package yamledit

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	jsonpatch "github.com/evanphx/json-patch/v5"
	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// --------------------------------------------------------------------------------------
// Internal state registered per root yaml.DocumentNode
// --------------------------------------------------------------------------------------

type docState struct {
	mu          sync.RWMutex
	doc         *yaml.Node              // back-reference to the root document
	indent      int                     // detected indent (2,3,4,...)
	indentSeq   bool                    // whether sequences under a key are indented
	ordered     gyaml.MapSlice          // current ordered mapping we edit (live view)
	comments    gyaml.CommentMap        // captured comments (for fallback encode)
	subPathByHN map[*yaml.Node][]string // mapping-handle -> YAML path segments from root

	// --- Byte-surgical indices ---
	original    []byte // original file bytes (exact)
	lineOffsets []int  // starting offset of each line in original
	origOrdered gyaml.MapSlice

	// Map-level index: information about each mapping path found in the original bytes
	mapIndex map[string]*mapInfo

	// Scalar value positions (original) keyed by path + key (we store all occurrences to handle dups)
	valueOccByPathKey map[string][]valueOcc

	seqIndex map[string]*seqInfo // sequence formatting & anchors by YAML path

	// explicit deletions requested (path\0key)
	toDelete    map[string]struct{}
	arraysDirty bool // set only when JSON Patch mutates arrays (seq nodes)
}

// Information about a sequence under a mapping path in the original YAML.
type seqItemInfo struct {
	name  string // value of "name" key if available
	start int    // byte offset at the beginning of the item's first line ("- " ...)
	end   int    // byte offset of the newline ending the last line of the item
}

type seqInfo struct {
	indent         int // spaces before '-' on the first line of an item
	itemKVIndent   int // spaces for subsequent key lines inside an item
	firstItemStart int // byte offset of the first item's line start
	lastItemEnd    int // byte offset of the newline ending the last item's last line
	hasAnyItem     bool
	originalPath   bool
	firstKeyInline bool          // whether first key appears on the same line as "- "
	keyOrder       []string      // preferred key order for items (captured from an existing item)
	items          []seqItemInfo // per-item positions and names
	gaps           [][]byte      // raw bytes between items; len = len(items)-1
	// header (key line) anchors for the sequence value (e.g., "externalSecretEnvs:")
	headerLineStart int // start offset of the key's line ("externalSecretEnvs:")
	headerLineEnd   int // end offset of that line (newline position)
}

func cloneSeqIndex(in map[string]*seqInfo) map[string]*seqInfo {
	out := make(map[string]*seqInfo, len(in))
	for k, v := range in {
		cp := *v
		cp.keyOrder = append([]string(nil), v.keyOrder...)
		if v.items != nil {
			cp.items = make([]seqItemInfo, len(v.items))
			copy(cp.items, v.items)
		}
		if v.gaps != nil {
			cp.gaps = make([][]byte, len(v.gaps))
			for i := range v.gaps {
				if v.gaps[i] != nil {
					cp.gaps[i] = append([]byte(nil), v.gaps[i]...)
				}
			}
		}
		out[k] = &cp
	}
	return out
}

// Information about a mapping block in the original YAML
type mapInfo struct {
	indent       int // indent (in spaces) of keys inside this mapping
	lastLineEnd  int // byte offset of the newline that ends the last key/value line in this mapping
	hasAnyKey    bool
	originalPath bool // mapping existed in the original bytes
}

// One occurrence of "key: value" in the original file
type valueOcc struct {
	keyLineStart int // start offset of the line where the key begins
	valStart     int // start offset of the value token
	valEnd       int // end offset (exclusive) of the value token
	lineEnd      int // offset of '\n' ending this line (or len(original)-1 if final line has no \n)
}

// Global registry so we can look up state by *yaml.Node (doc)
var (
	regMu sync.Mutex
	reg   = map[*yaml.Node]*docState{}
)

// findOwnerByMapNode safely finds the docState that knows about mapNode,
// without holding regMu while touching per-state fields.
func findOwnerByMapNode(mapNode *yaml.Node) (*docState, *yaml.Node, []string, bool) {
	// Snapshot states under regMu
	regMu.Lock()
	states := make([]*docState, 0, len(reg))
	for _, s := range reg {
		states = append(states, s)
	}
	regMu.Unlock()
	// Probe each state under its own RLock
	for _, s := range states {
		s.mu.RLock()
		if p, ok := s.subPathByHN[mapNode]; ok {
			base := append([]string(nil), p...)
			doc := s.doc
			s.mu.RUnlock()
			return s, doc, base, true
		}
		s.mu.RUnlock()
	}
	return nil, nil, nil, false
}

func register(doc *yaml.Node, st *docState) {
	regMu.Lock()
	reg[doc] = st
	regMu.Unlock()

	runtime.SetFinalizer(doc, func(d *yaml.Node) {
		regMu.Lock()
		delete(reg, d)
		regMu.Unlock()
	})
}

func lookup(doc *yaml.Node) (*docState, bool) {
	regMu.Lock()
	st, ok := reg[doc]
	regMu.Unlock()
	return st, ok
}

// --------------------------------------------------------------------------------------
// Public API
// --------------------------------------------------------------------------------------

// Parse reads YAML data and returns a yaml.Node, creating a minimal mapping document if empty.
func Parse(data []byte) (*yaml.Node, error) {
	doc := &yaml.Node{
		Kind:    yaml.DocumentNode,
		Content: []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}},
	}

	if len(data) > 0 {
		var tmp yaml.Node
		if err := yaml.Unmarshal(data, &tmp); err != nil {
			return nil, fmt.Errorf("yamledit: failed to parse YAML: %w", err)
		}
		if tmp.Kind != yaml.DocumentNode || len(tmp.Content) == 0 || tmp.Content[0].Kind != yaml.MappingNode {
			return nil, fmt.Errorf("yamledit: top-level YAML is not a mapping")
		}
		doc = &tmp
	}

	// Build shadow state using goccy/go-yaml (to preserve comments and ordered map for fallback)
	st := &docState{
		doc:               doc,
		comments:          gyaml.CommentMap{},
		ordered:           gyaml.MapSlice{},
		subPathByHN:       map[*yaml.Node][]string{},
		indent:            2,
		indentSeq:         true,
		original:          append([]byte(nil), data...),
		lineOffsets:       buildLineOffsets(data),
		mapIndex:          map[string]*mapInfo{},
		valueOccByPathKey: map[string][]valueOcc{},
		seqIndex:          map[string]*seqInfo{},
		toDelete:          map[string]struct{}{},
	}

	// Decode into ordered map and capture comments; detect indent and sequence style
	if len(data) > 0 {
		if err := gyaml.UnmarshalWithOptions(data, &st.ordered, gyaml.UseOrderedMap(), gyaml.CommentToMap(st.comments)); err == nil {
			ind, seq := detectIndentAndSequence(data)
			st.indent, st.indentSeq = ind, seq
		}
	}

	// Keep a snapshot of the original ordered map for diffing
	st.origOrdered = cloneMapSlice(st.ordered)

	// Index mapping handles (for path lookups later on)
	if doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode {
		st.subPathByHN[doc.Content[0]] = nil
		indexMappingHandles(st, doc.Content[0], nil)

		// Build byte-surgical indices off the original parsed tree
		if len(data) > 0 {
			indexPositions(st, doc.Content[0], nil)
		}
	}

	register(doc, st)
	return doc, nil
}

// indexSeqPositions indexes scalar positions for sequence items which are mapping nodes.
func indexSeqPositions(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Kind != yaml.SequenceNode {
		return
	}
	for idx, it := range seq.Content {
		if it == nil {
			continue
		}
		if it.Kind == yaml.MappingNode {
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				v := it.Content[j+1]
				if k.Kind != yaml.ScalarNode || v.Kind != yaml.ScalarNode {
					continue
				}
				valStart := offsetFor(st.lineOffsets, v.Line, v.Column)
				if valStart < 0 || valStart >= len(st.original) {
					continue
				}
				valEnd := findScalarEndOnLine(st.original, valStart)
				lineEnd := findLineEnd(st.original, valStart)
				pk := makeSeqPathKey(cur, idx, k.Value)
				st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
					keyLineStart: lineStartOffset(st.lineOffsets, k.Line),
					valStart:     valStart,
					valEnd:       valEnd,
					lineEnd:      lineEnd,
				})
			}
		} else if it.Kind == yaml.ScalarNode {
			// Scalar item in a sequence, e.g. "- 8080  # comment"
			valStart := offsetFor(st.lineOffsets, it.Line, it.Column)
			if valStart >= 0 && valStart < len(st.original) {
				valEnd := findScalarEndOnLine(st.original, valStart)
				lineStart := lineStartOffset(st.lineOffsets, it.Line)
				lineEnd := findLineEnd(st.original, valStart)
				pk := makeSeqPathKey(cur, idx, scalarItemKey)
				st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
					keyLineStart: lineStart,
					valStart:     valStart,
					valEnd:       valEnd,
					lineEnd:      lineEnd,
				})
			}
		}
	}
}

// indexSequenceAnchors captures indent/style and insertion anchors for sequences.
func indexSequenceAnchors(st *docState, seq *yaml.Node, cur []string, keyNode *yaml.Node) {
	mpath := joinPath(cur)
	si := st.seqIndex[mpath]
	if si == nil {
		si = &seqInfo{originalPath: true}
		st.seqIndex[mpath] = si
	}
	// Capture the header line for the mapping key that owns this sequence
	if keyNode != nil {
		si.headerLineStart = lineStartOffset(st.lineOffsets, keyNode.Line)
		si.headerLineEnd = findLineEnd(st.original, si.headerLineStart)
	}
	if len(seq.Content) == 0 {
		si.hasAnyItem = false
		return
	}
	si.hasAnyItem = true
	// First item start anchor
	first := seq.Content[0]
	if first.Kind == yaml.MappingNode && len(first.Content) >= 2 {
		fk := first.Content[0]
		si.firstItemStart = lineStartOffset(st.lineOffsets, fk.Line)
	} else {
		si.firstItemStart = lineStartOffset(st.lineOffsets, first.Line)
	}
	// Detect base indent from the first item's line even for scalar sequences.
	{
		ls := lineStartOffset(st.lineOffsets, first.Line)
		le := findLineEnd(st.original, ls)
		ln := st.original[ls:le]
		si.indent = leadingSpaces(ln)
	}
	// Per‑item boundaries and names
	si.items = si.items[:0]
	// Detect style/indent/key order from the FIRST mapping item we see (for stability).
	detectedStyle := false
	computeItemBounds := func(it *yaml.Node) (start int, end int, name string) {
		// start
		if it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
			fk := it.Content[0]
			start = lineStartOffset(st.lineOffsets, fk.Line)
		} else {
			start = lineStartOffset(st.lineOffsets, it.Line)
		}
		// end
		if it.Kind == yaml.MappingNode {
			maxEnd := 0
			for j := 0; j+1 < len(it.Content); j += 2 {
				if it.Content[j+1] == nil {
					continue
				}
				vs := offsetFor(st.lineOffsets, it.Content[j+1].Line, it.Content[j+1].Column)
				if vs >= 0 && vs < len(st.original) {
					le := findLineEnd(st.original, vs)
					if le > maxEnd {
						maxEnd = le
					}
				}
			}
			end = maxEnd
		} else {
			ls := lineStartOffset(st.lineOffsets, it.Line)
			end = findLineEnd(st.original, ls)
		}
		// name (best-effort)
		if it.Kind == yaml.MappingNode {
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				v := it.Content[j+1]
				if k.Kind == yaml.ScalarNode && k.Value == "name" && v.Kind == yaml.ScalarNode {
					name = v.Value
					break
				}
			}
		}
		// Detect style/indent/key order once from a mapping item
		if !detectedStyle && it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
			firstK := it.Content[0]
			ls := lineStartOffset(st.lineOffsets, firstK.Line)
			le := findLineEnd(st.original, ls)
			ln := st.original[ls:le]
			si.indent = leadingSpaces(ln)
			si.firstKeyInline = firstNonSpaceByte(ln) == '-'
			kvIndent := 0
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				ks := lineStartOffset(st.lineOffsets, k.Line)
				ke := findLineEnd(st.original, ks)
				kl := st.original[ks:ke]
				if firstNonSpaceByte(kl) == '-' {
					continue
				}
				sp := leadingSpaces(kl)
				if kvIndent == 0 || sp < kvIndent {
					kvIndent = sp
				}
			}
			if kvIndent == 0 {
				kvIndent = si.indent + st.indent
			}
			si.itemKVIndent = kvIndent
			order := make([]string, 0, len(it.Content)/2)
			for j := 0; j+1 < len(it.Content); j += 2 {
				if it.Content[j].Kind == yaml.ScalarNode {
					order = append(order, it.Content[j].Value)
				}
			}
			si.keyOrder = order
			detectedStyle = true
		}
		return
	}
	// First item start
	first = seq.Content[0]
	fs, _, _ := computeItemBounds(first)
	si.firstItemStart = fs
	// Items & last end
	lastEnd := 0
	si.items = make([]seqItemInfo, 0, len(seq.Content))
	for _, it := range seq.Content {
		s, e, nm := computeItemBounds(it)
		if e > lastEnd {
			lastEnd = e
		}
		si.items = append(si.items, seqItemInfo{name: nm, start: s, end: e})
	}
	si.lastItemEnd = lastEnd
	// Gaps between items (raw)
	if len(si.items) >= 2 {
		si.gaps = make([][]byte, len(si.items)-1)
		for i := 0; i < len(si.items)-1; i++ {
			gStart := si.items[i].end + 1
			gEnd := si.items[i+1].start
			if gStart >= 0 && gEnd >= gStart && gEnd <= len(st.original) {
				si.gaps[i] = append([]byte(nil), st.original[gStart:gEnd]...)
			} else {
				si.gaps[i] = nil
			}
		}
	} else {
		si.gaps = nil
	}
}

// Marshal encodes the YAML. Prefer byte-surgical patching when safe; otherwise fall back.
func Marshal(doc *yaml.Node) ([]byte, error) {
	st, ok := lookup(doc)
	if !ok {
		// Fallback if somehow not registered
		var buf bytes.Buffer
		enc := yaml.NewEncoder(&buf)
		enc.SetIndent(2)
		_ = enc.Encode(doc)
		_ = enc.Close()
		return buf.Bytes(), nil
	}

	st.mu.RLock()
	ordered := cloneMapSlice(st.ordered) // snapshot
	comments := st.comments
	indent := st.indent
	indentSeq := st.indentSeq
	original := st.original
	mapIdx := cloneMapIndex(st.mapIndex)
	valIdx := cloneValueIndex(st.valueOccByPathKey)
	origOrdered := cloneMapSlice(st.origOrdered)
	delSet := make(map[string]struct{}, len(st.toDelete))
	seqIdx := cloneSeqIndex(st.seqIndex)
	for k := range st.toDelete {
		delSet[k] = struct{}{}
	}
	arraysDirty := st.arraysDirty
	st.mu.RUnlock()

	// Attempt byte-surgical patching first (even if arraysDirty), with enhanced seq support.
	out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, indent, indentSeq, delSet)
	if okPatch {
		// clear the flag if we succeeded surgically
		if arraysDirty {
			if s, ok := lookup(doc); ok {
				s.mu.Lock()
				s.arraysDirty = false
				s.mu.Unlock()
			}
		}
		return out, nil
	}

	// Fallback: structured encode (still preserves comments/order/indent)
	var buf bytes.Buffer
	enc := gyaml.NewEncoder(
		&buf, gyaml.Indent(indent), gyaml.IndentSequence(indentSeq), gyaml.WithComment(comments),
	)
	if err := enc.Encode(ordered); err != nil {
		_ = enc.Close()
		return nil, err
	}
	_ = enc.Close()
	return buf.Bytes(), nil
}

// EnsurePath returns a mapping node for the nested keys (creates when missing).
// It now accepts either a root DocumentNode or a MappingNode as the starting point.
func EnsurePath(node *yaml.Node, first string, rest ...string) *yaml.Node {
	if node == nil {
		return nil
	}

	keys := append([]string{first}, rest...)

	// Resolve state + starting mapping node.
	var (
		st       *docState
		startMap *yaml.Node
		basePath []string // YAML path of startMap from the root (if known)
		ownsLock bool
	)

	switch node.Kind {
	case yaml.DocumentNode:
		// Start from document root mapping
		if len(node.Content) == 0 || node.Content[0].Kind != yaml.MappingNode {
			return nil
		}
		startMap = node.Content[0]
		if s, ok := lookup(node); ok {
			st = s
		}

	case yaml.MappingNode:
		// Start from a mapping node inside the doc
		startMap = node
		// Find the docState that knows this mapping handle
		if s, _, base, ok := findOwnerByMapNode(startMap); ok {
			st = s
			basePath = base
		}

	default:
		return nil
	}

	// Lock state if present
	if st != nil {
		st.mu.Lock()
		ownsLock = true
		defer func() {
			if ownsLock {
				st.mu.Unlock()
			}
		}()
	}

	// Walk/construct from startMap
	cur := startMap
	for _, k := range keys {
		var found *yaml.Node
		for i := 0; i+1 < len(cur.Content); i += 2 {
			if cur.Content[i].Kind == yaml.ScalarNode && cur.Content[i].Value == k {
				found = cur.Content[i+1]
				break
			}
		}
		if found == nil {
			key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}
			val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			cur.Content = append(cur.Content, key, val)
			found = val
		}
		if found.Kind != yaml.MappingNode {
			repl := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			repl.HeadComment, repl.LineComment, repl.FootComment = found.HeadComment, found.LineComment, found.FootComment
			repl.Anchor = found.Anchor
			*found = *repl
		}
		cur = found

		// Keep handle → path mapping up to date for new/converted nodes
		if st != nil {
			segPath := append(append([]string(nil), basePath...), k)
			st.subPathByHN[cur] = append([]string(nil), segPath...)
			basePath = segPath
		}
	}

	// Keep ordered (logical) view in sync
	if st != nil {
		fullPath := append([]string(nil), st.subPathByHN[startMap]...)
		fullPath = append(fullPath, keys...)
		st.ordered = ensureOrderedPath(st.ordered, fullPath...)
	}

	return cur
}

// SetScalarInt sets an integer value under the mapping node.
func SetScalarInt(mapNode *yaml.Node, key string, value int) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	var st *docState
	var docHN *yaml.Node
	regMu.Lock()
	for doc, s := range reg {
		if _, ok := s.subPathByHN[mapNode]; ok {
			st = s
			docHN = doc
			break
		}
	}
	regMu.Unlock()

	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	valStr := fmt.Sprintf("%d", value)
	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			v := mapNode.Content[i+1]
			head, line, foot := v.HeadComment, v.LineComment, v.FootComment
			v.Kind = yaml.ScalarNode
			v.Tag = "!!int"
			v.Value = valStr
			v.HeadComment, v.LineComment, v.FootComment = head, line, foot
			updated = true
			// NOTE: don't break; update all occurrences in the AST so any fallback that
			// happens to serialize from nodes won't leave mixed values.
		}
	}
	if !updated {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: valStr}
		mapNode.Content = append(mapNode.Content, keyNode, valNode)
	}

	if st == nil {
		return
	}

	// Ensure our logical ordered map is updated
	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	// Update the LAST occurrence in ordered map so "last wins" semantics hold.
	st.ordered = setIntAtPath(st.ordered, path, key, value)
	// if user had previously requested delete for this key, cancel it (last write wins)
	delete(st.toDelete, makePathKey(path, key))
}

// SetScalarString sets a string value under the mapping node.
func SetScalarString(mapNode *yaml.Node, key, value string) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	var st *docState
	var docHN *yaml.Node
	if s, doc, _, ok := findOwnerByMapNode(mapNode); ok {
		st = s
		docHN = doc
	}

	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			v := mapNode.Content[i+1]
			head, line, foot := v.HeadComment, v.LineComment, v.FootComment
			v.Kind = yaml.ScalarNode
			v.Tag = "!!str"
			v.Value = value
			v.HeadComment, v.LineComment, v.FootComment = head, line, foot
			updated = true
		}
	}
	if !updated {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: value}
		mapNode.Content = append(mapNode.Content, keyNode, valNode)
	}

	if st == nil {
		return
	}

	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	st.ordered = setStringAtPath(st.ordered, path, key, value)
	delete(st.toDelete, makePathKey(path, key)) // string write cancels pending deletion
}

// SetScalarBool sets a boolean value under the mapping node.
// Byte-surgical replacement writes canonical YAML booleans ("true"/"false").
func SetScalarBool(mapNode *yaml.Node, key string, value bool) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	var st *docState
	var docHN *yaml.Node
	regMu.Lock()
	for doc, s := range reg {
		if _, ok := s.subPathByHN[mapNode]; ok {
			st = s
			docHN = doc
			break
		}
	}
	regMu.Unlock()

	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	valStr := "false"
	if value {
		valStr = "true"
	}

	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			v := mapNode.Content[i+1]
			head, line, foot := v.HeadComment, v.LineComment, v.FootComment
			v.Kind = yaml.ScalarNode
			v.Tag = "!!bool"
			v.Value = valStr
			v.HeadComment, v.LineComment, v.FootComment = head, line, foot
			updated = true
		}
	}
	if !updated {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: valStr}
		mapNode.Content = append(mapNode.Content, keyNode, valNode)
	}

	if st == nil {
		return
	}

	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	st.ordered = setBoolAtPath(st.ordered, path, key, value)
	delete(st.toDelete, makePathKey(path, key)) // write cancels pending deletion
}

// SetScalarFloat sets a float value under the mapping node.
func SetScalarFloat(mapNode *yaml.Node, key string, value float64) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}
	valStr := strconv.FormatFloat(value, 'g', -1, 64)

	var st *docState
	var docHN *yaml.Node
	regMu.Lock()
	for doc, s := range reg {
		if _, ok := s.subPathByHN[mapNode]; ok {
			st = s
			docHN = doc
			break
		}
	}
	regMu.Unlock()

	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			v := mapNode.Content[i+1]
			head, line, foot := v.HeadComment, v.LineComment, v.FootComment
			v.Kind = yaml.ScalarNode
			v.Tag = "!!float"
			v.Value = valStr
			v.HeadComment, v.LineComment, v.FootComment = head, line, foot
			updated = true
		}
	}
	if !updated {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: valStr}
		mapNode.Content = append(mapNode.Content, keyNode, valNode)
	}

	if st == nil {
		return
	}
	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	// store as float64 in ordered view
	st.ordered = setFloatAtPath(st.ordered, path, key, value)
	delete(st.toDelete, makePathKey(path, key))
}

// SetScalarNull sets a null value (!!null) under the mapping node.
func SetScalarNull(mapNode *yaml.Node, key string) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}
	var st *docState
	var docHN *yaml.Node
	regMu.Lock()
	for doc, s := range reg {
		if _, ok := s.subPathByHN[mapNode]; ok {
			st = s
			docHN = doc
			break
		}
	}
	regMu.Unlock()
	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			v := mapNode.Content[i+1]
			head, line, foot := v.HeadComment, v.LineComment, v.FootComment
			v.Kind = yaml.ScalarNode
			v.Tag = "!!null"
			v.Value = "null"
			v.HeadComment, v.LineComment, v.FootComment = head, line, foot
			updated = true
		}
	}
	if !updated {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null", Value: "null"}
		mapNode.Content = append(mapNode.Content, keyNode, valNode)
	}
	if st == nil {
		return
	}
	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	st.ordered = setNullAtPath(st.ordered, path, key)
	delete(st.toDelete, makePathKey(path, key))
}

// DeleteKey removes all occurrences of 'key' under 'mapNode'.
// Surgical deletion removes the complete lines for the key’s occurrences.
// If surgery is unsafe/unavailable, Marshal() falls back to a structured re-encode.
func DeleteKey(mapNode *yaml.Node, key string) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	var st *docState
	var docHN *yaml.Node
	regMu.Lock()
	for doc, s := range reg {
		if _, ok := s.subPathByHN[mapNode]; ok {
			st = s
			docHN = doc
			break
		}
	}
	regMu.Unlock()

	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	// Remove all pairs from the AST for the mapping node.
	nc := make([]*yaml.Node, 0, len(mapNode.Content))
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		v := mapNode.Content[i+1]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			// drop the pair (k, v)
			_ = v
			continue
		}
		nc = append(nc, k, v)
	}
	mapNode.Content = nc

	if st == nil {
		return
	}

	// Ensure we have a path recorded for this handle
	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}

	// Update ordered map and mark deletion for surgery.
	st.ordered, _ = deleteKeyAtPath(st.ordered, path, key)
	st.toDelete[makePathKey(path, key)] = struct{}{}
}

// --------------------------------------------------------------------------------------
// Internal helpers (ordered-map + indices + byte surgery)
// --------------------------------------------------------------------------------------

func ensureOrderedPath(ms gyaml.MapSlice, keys ...string) gyaml.MapSlice {
	if len(keys) == 0 {
		return ms
	}
	k := keys[0]
	for i := range ms {
		if keyEquals(ms[i].Key, k) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = ensureOrderedPath(sub, keys[1:]...)
			ms[i].Value = sub
			return ms
		}
	}
	ms = append(ms, gyaml.MapItem{Key: k, Value: ensureOrderedPath(gyaml.MapSlice{}, keys[1:]...)})
	return ms
}

// Set the LAST occurrence if duplicates exist; else append.
func setIntAtPath(ms gyaml.MapSlice, path []string, key string, val int) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}

	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setIntAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setIntAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

// string version mirrors int semantics (last occurrence wins; append if missing)
func setStringAtPath(ms gyaml.MapSlice, path []string, key, val string) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setStringAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setStringAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setBoolAtPath(ms gyaml.MapSlice, path []string, key string, val bool) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setBoolAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setBoolAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setFloatAtPath(ms gyaml.MapSlice, path []string, key string, val float64) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setFloatAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setFloatAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setNullAtPath(ms gyaml.MapSlice, path []string, key string) gyaml.MapSlice {
	if len(path) == 0 {
		// store nil
		return setAnyAtPath(ms, path, key, nil)
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setNullAtPath(sub, path[1:], key)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setNullAtPath(gyaml.MapSlice{}, path[1:], key)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

// delete a key at path (remove all occurrences)
func deleteKeyAtPath(ms gyaml.MapSlice, path []string, key string) (gyaml.MapSlice, bool) {
	if len(path) == 0 {
		out := make(gyaml.MapSlice, 0, len(ms))
		removed := false
		for _, it := range ms {
			if keyEquals(it.Key, key) {
				removed = true
				continue
			}
			out = append(out, it)
		}
		return out, removed
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			if sub, ok := ms[i].Value.(gyaml.MapSlice); ok {
				newSub, rem := deleteKeyAtPath(sub, path[1:], key)
				ms[i].Value = newSub
				return ms, rem
			}
			return ms, false
		}
	}
	return ms, false
}

// setAnyAtPath sets arbitrary value at a path/key (last segment is a key).
func setAnyAtPath(ms gyaml.MapSlice, path []string, key string, val interface{}) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := range ms {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setAnyAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setAnyAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func keyEquals(k interface{}, want string) bool {
	switch vv := k.(type) {
	case string:
		return vv == want
	case fmt.Stringer:
		return vv.String() == want
	default:
		return false
	}
}

func indexMappingHandles(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode {
		return
	}
	st.subPathByHN[n] = append([]string(nil), cur...)
	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind == yaml.ScalarNode {
			seg := k.Value
			if v.Kind == yaml.MappingNode {
				indexMappingHandles(st, v, append(cur, seg))
			}
		}
	}
}

// ----- Byte indices from original parse -----

func indexPositions(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode {
		return
	}
	// The indent for keys inside this mapping is the Column-1 of any key under it.
	// We'll discover it while iterating keys below.
	mapPath := joinPath(cur)
	mi := st.mapIndex[mapPath]
	if mi == nil {
		mi = &mapInfo{indent: 0, lastLineEnd: 0, hasAnyKey: false, originalPath: true}
		st.mapIndex[mapPath] = mi
	}

	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind != yaml.ScalarNode {
			continue
		}
		key := k.Value

		if k.Column > 0 && mi.indent == 0 && !(len(cur) == 0 && k.Column-1 == 0) {
			// Record indent from the first seen key (except the very top where 0 is valid)
			mi.indent = k.Column - 1
		}
		if len(cur) == 0 {
			// top-level keys have indent 0
			mi.indent = 0
		}

		// For scalars, we can anchor at the value line.
		valStart := offsetFor(st.lineOffsets, v.Line, v.Column)
		if valStart >= 0 && valStart < len(st.original) {
			valEnd := findScalarEndOnLine(st.original, valStart)
			lineEnd := findLineEnd(st.original, valStart)

			pk := makePathKey(cur, key)
			st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
				keyLineStart: lineStartOffset(st.lineOffsets, k.Line),
				valStart:     valStart,
				valEnd:       valEnd,
				lineEnd:      lineEnd,
			})

			// Track last line in this mapping to attach future insertions
			if lineEnd > mi.lastLineEnd {
				mi.lastLineEnd = lineEnd
			}
			mi.hasAnyKey = true
		}

		// Recurse for nested mapping and extend the parent's lastLineEnd to the child's end.
		if v.Kind == yaml.MappingNode {
			childPath := append(cur, key)
			indexPositions(st, v, childPath)
			if childMi := st.mapIndex[joinPath(childPath)]; childMi != nil && childMi.lastLineEnd > mi.lastLineEnd {
				mi.lastLineEnd = childMi.lastLineEnd
			}
		} else if v.Kind == yaml.SequenceNode {
			seqPath := append(cur, key)
			// Index scalars inside sequence items (if they are mappings).
			indexSeqPositions(st, v, seqPath)
			// Capture anchors/indent for append surgery.
			indexSequenceAnchors(st, v, seqPath, k)
			// Note: we do not modify mapIndex.lastLineEnd for sequences.
		}
	}
}

// ----- Byte-surgical marshal -----

type patch struct {
	start int
	end   int
	data  []byte
	seq   int // stable order for equal start
}

// index segment for array items. MUST match makeSeqPathKey's "[%d]" form.
func indexSeg(i int) string { return fmt.Sprintf("[%d]", i) }

func marshalBySurgery(
	original []byte,
	current gyaml.MapSlice,
	originalOrdered gyaml.MapSlice,
	mapIdx map[string]*mapInfo,
	valIdx map[string][]valueOcc,
	seqIdx map[string]*seqInfo,
	baseIndent int,
	indentSeq bool,
	deletions map[string]struct{},
) ([]byte, bool) {
	if len(original) == 0 {
		// No original content to patch
		return nil, false
	}

	// If the logical shape changed (e.g., scalar -> mapping via EnsurePath), surgery is unsafe.
	if hasShapeChange(originalOrdered, current) {
		return nil, false
	}

	// Detect changes & build patches
	var patches []patch
	seq := 0
	for ok := range []int{0} {
		_ = ok                             // keep the block to allow early returns neatly
		mutableMI := cloneMapIndex(mapIdx) // local copy to advance insertion anchors
		// Replace entire sequence blocks when array "shape" changed (remove/add/reorder)
		seqReplOK, seqReplPatches, replacedSeqs := buildSeqReplaceBlockPatches(original, current, originalOrdered, seqIdx, baseIndent)
		if !seqReplOK {
			return nil, false
		}
		for _, p := range seqReplPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 1) Replace ints/strings/bools/floats/null that changed (and existed originally),
		//    including inside arrays of mappings.
		replaceOK, replPatches := buildReplacementPatches(original, current, valIdx, seqIdx, replacedSeqs)
		if !replaceOK {
			return nil, false
		}
		for _, p := range replPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 2) Remove duplicates in original (keep LAST occurrence), but ignore keys marked for deletion
		dupPatchesOK, dupPatches := buildDuplicateRemovalPatches(original, current, valIdx, deletions, replacedSeqs)
		if !dupPatchesOK {
			return nil, false
		}
		for _, p := range dupPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 3) Insert NEW keys (ints/strings) where safe
		insertOK, insertPatches := buildInsertPatches(original, current, originalOrdered, mutableMI, baseIndent, indentSeq)
		if !insertOK {
			return nil, false
		}
		for _, p := range insertPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 3b) Append NEW items to sequences (arrays) at the end (safe styles only).
		//     Skip sequences we fully replaced above.
		seqOK, seqPatches := buildSeqAppendPatches(original, current, originalOrdered, seqIdx, baseIndent, replacedSeqs)
		if !seqOK {
			return nil, false
		}
		for _, p := range seqPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 4) Explicit deletions (remove all occurrences)
		delOK, delPatches := buildDeletionPatches(original, deletions, valIdx)
		if !delOK {
			return nil, false
		}
		for _, p := range delPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}
	}

	if len(patches) == 0 {
		// If we couldn't produce surgical patches but the logical doc changed,
		// request a structured re‑encode (fallback). Otherwise keep original.
		if !logicalEqualOrdered(originalOrdered, current) {
			return nil, false
		}
		return original, true
	}

	// Ensure patches don't have bad overlaps (insertion at same point is OK)
	sort.SliceStable(patches, func(i, j int) bool {
		if patches[i].start == patches[j].start {
			if patches[i].end == patches[j].end {
				return patches[i].seq < patches[j].seq
			}
			return patches[i].end < patches[j].end
		}
		return patches[i].start < patches[j].start
	})
	for i := 1; i < len(patches); i++ {
		prev := patches[i-1]
		cur := patches[i]
		// overlapping destructive ranges not allowed
		if prev.end > cur.start {
			// If both are insertions at the same point (start==end), it's fine; else bail out
			if !(prev.start == prev.end && cur.start == cur.end && prev.start == cur.start) {
				return nil, false
			}
		}
	}

	// Apply patches
	var out bytes.Buffer
	cursor := 0
	for _, p := range patches {
		if p.start < cursor || p.end < p.start || p.end > len(original) {
			return nil, false
		}
		out.Write(original[cursor:p.start])
		out.Write(p.data)
		cursor = p.end
	}
	out.Write(original[cursor:])
	return out.Bytes(), true
}

// Compare logical structures (ignores scalar formatting). Used to decide fallback when
// no surgical patches were produced but the doc actually changed (e.g., array edits).
func logicalEqualOrdered(a, b gyaml.MapSlice) bool {
	return reflect.DeepEqual(toPlain(a), toPlain(b))
}

func toPlain(v interface{}) interface{} {
	switch t := v.(type) {
	case gyaml.MapSlice:
		m := map[string]interface{}{}
		for _, it := range t {
			k := fmt.Sprint(it.Key)
			m[k] = toPlain(it.Value)
		}
		return m
	case []interface{}:
		out := make([]interface{}, 0, len(t))
		for _, e := range t {
			out = append(out, toPlain(e))
		}
		return out
	default:
		return t
	}
}

// Build patches for appending new items to sequences (arrays) at the end.
// 'skipSeq' contains sequence paths (joinPath form) which are already replaced entirely.
func buildSeqAppendPatches(
	original []byte,
	current gyaml.MapSlice,
	originalOrdered gyaml.MapSlice,
	seqIdx map[string]*seqInfo,
	baseIndent int,
	skipSeq map[string]struct{},
) (bool, []patch) {
	var patches []patch

	var getArrAtPath func(ms gyaml.MapSlice, path []string, key string) ([]interface{}, bool)
	getArrAtPath = func(ms gyaml.MapSlice, path []string, key string) ([]interface{}, bool) {
		// navigate to mapping at path
		cur := ms
		for _, seg := range path {
			found := false
			for _, it := range cur {
				ks, ok := it.Key.(string)
				if ok && ks == seg {
					if sub, ok2 := it.Value.(gyaml.MapSlice); ok2 {
						cur = sub
						found = true
						break
					}
				}
			}
			if !found {
				return nil, false
			}
		}
		for _, it := range cur {
			ks, ok := it.Key.(string)
			if ok && ks == key {
				if arr, ok2 := it.Value.([]interface{}); ok2 {
					return arr, true
				}
				return nil, false
			}
		}
		return nil, false
	}

	var toMapSlice = func(v interface{}) (gyaml.MapSlice, bool) {
		switch t := v.(type) {
		case gyaml.MapSlice:
			return t, true
		case map[string]interface{}:
			ms := gyaml.MapSlice{}
			for k, vv := range t {
				ms = append(ms, gyaml.MapItem{Key: k, Value: jsonValueToOrdered(vv)})
			}
			return ms, true
		default:
			return gyaml.MapSlice{}, false
		}
	}

	renderScalar := func(v interface{}) string {
		switch vv := v.(type) {
		case int:
			return fmt.Sprintf("%d", vv)
		case float64:
			return strconv.FormatFloat(vv, 'g', -1, 64)
		case bool:
			if vv {
				return "true"
			}
			return "false"
		case string:
			if isSafeBareString(vv) {
				return vv
			}
			return quoteNewStringToken(vv)
		case nil:
			return "null"
		default:
			s := fmt.Sprint(vv)
			if isSafeBareString(s) {
				return s
			}
			return quoteNewStringToken(s)
		}
	}

	renderItem := func(si *seqInfo, ms gyaml.MapSlice) (string, bool) {
		// Build lookup and order
		vals := map[string]interface{}{}
		for _, it := range ms {
			if ks, ok := it.Key.(string); ok {
				vals[ks] = it.Value
			}
		}
		order := []string{}
		if len(si.keyOrder) > 0 {
			order = append(order, si.keyOrder...)
			for _, it := range ms {
				ks, _ := it.Key.(string)
				found := false
				for _, k := range order {
					if k == ks {
						found = true
						break
					}
				}
				if !found {
					order = append(order, ks)
				}
			}
		} else {
			for _, it := range ms {
				if ks, ok := it.Key.(string); ok {
					order = append(order, ks)
				}
			}
		}
		if len(order) == 0 {
			return "", false
		}
		kvIndent := si.itemKVIndent
		if kvIndent == 0 {
			kvIndent = si.indent + baseIndent
		}
		var sb strings.Builder
		first := order[0]
		fv, ok := vals[first]
		if !ok {
			return "", false
		}
		if si.firstKeyInline {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("- ")
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		} else {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("-\n")
			sb.WriteString(strings.Repeat(" ", kvIndent))
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		}
		for i := 1; i < len(order); i++ {
			k := order[i]
			v, ok := vals[k]
			if !ok {
				continue
			}
			sb.WriteString(strings.Repeat(" ", kvIndent))
			sb.WriteString(k)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(v))
			sb.WriteString("\n")
		}
		return sb.String(), true
	}

	var walk func(ms gyaml.MapSlice, path []string) bool
	walk = func(ms gyaml.MapSlice, path []string) bool {
		for _, it := range ms {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			switch v := it.Value.(type) {
			case gyaml.MapSlice:
				if !walk(v, append(path, k)) {
					return false
				}
			case []interface{}:
				mpath := joinPath(append(path, k))
				if _, skip := skipSeq[mpath]; skip {
					continue
				}
				origArr, ok := getArrAtPath(originalOrdered, path, k)
				if !ok {
					// New sequence path (no original anchor). Do not abort —
					// new sequences are handled by buildInsertPatches.
					continue
				}
				olen, nlen := len(origArr), len(v)
				if nlen < olen {
					return false
				} // deletions not handled surgically
				if nlen == olen {
					continue
				} // nothing appended
				// Only handle pure append at end.
				mpath = joinPath(append(path, k))
				si := seqIdx[mpath]
				if si == nil || !si.originalPath || !si.hasAnyItem {
					return false
				}
				insertPos := si.lastItemEnd + 1
				if insertPos < 0 || insertPos > len(original) {
					return false
				}
				var sb strings.Builder
				// If last item line had no newline at EOF, start with newline.
				if si.lastItemEnd >= len(original) || (si.lastItemEnd < len(original) && original[si.lastItemEnd] != '\n') {
					sb.WriteString("\n")
				}
				for i := olen; i < nlen; i++ {
					switch el := v[i].(type) {
					case gyaml.MapSlice, map[string]interface{}:
						// existing mapping rendering path
						msItem, ok := toMapSlice(v[i])
						if !ok {
							return false
						}
						txt, ok := renderItem(si, msItem)
						if !ok {
							return false
						}
						sb.WriteString(txt)
					default:
						// scalar append: "- <scalar>\n" honoring original indent
						sb.WriteString(strings.Repeat(" ", si.indent))
						sb.WriteString("- ")
						sb.WriteString(renderScalar(el))
						sb.WriteString("\n")
					}
					// advance anchor for chaining multiple appends in same sequence
					si.lastItemEnd = insertPos + len(sb.String()) - 1
				}
				patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(sb.String())})
			}
		}
		return true
	}
	if !walk(current, nil) {
		return false, nil
	}
	return true, patches
}

// buildReplacementPatches emits surgical scalar replacements (including inside seq items).
// If a sequence at some path was fully replaced, skip emitting replacements for its items.
func buildReplacementPatches(original []byte, current gyaml.MapSlice, valIdx map[string][]valueOcc, seqIdx map[string]*seqInfo, skipSeq map[string]struct{}) (bool, []patch) {
	var patches []patch

	// For sequence items, coalesce multiple scalar changes down to ONE patch,
	// chosen deterministically by the original key order captured in seqIdx.
	type keyPatch struct {
		key   string
		patch patch
	}
	perItem := map[string][]keyPatch{} // itemPath ("a\0b\0[1]") -> changed keys/patches

	isIndexSeg := func(s string) bool {
		return len(s) > 2 && s[0] == '[' && s[len(s)-1] == ']'
	}

	emit := func(p patch, path []string, key string) {
		if len(path) > 0 && isIndexSeg(path[len(path)-1]) {
			itemPath := joinPath(path) // includes the [n]
			// Skip if this item's sequence was fully replaced.
			seqPath := joinPath(path[:len(path)-1])
			if _, skip := skipSeq[seqPath]; skip {
				return
			}
			perItem[itemPath] = append(perItem[itemPath], keyPatch{key: key, patch: p})
			return
		}
		patches = append(patches, p) // non-sequence contexts are emitted as-is
	}

	var walkMap func(ms gyaml.MapSlice, path []string) bool
	var walkArr func(arr []interface{}, path []string) bool

	walkArr = func(arr []interface{}, path []string) bool {
		for i, el := range arr {
			seg := indexSeg(i)
			switch ev := el.(type) {
			case gyaml.MapSlice:
				if !walkMap(ev, append(path, seg)) {
					return false
				}
			// Arrays of scalars not supported surgically yet; fall through.
			default:
				// Handle arrays of scalars surgically: replace only the scalar token on its line.
				// Skip if this entire sequence was already marked as fully replaced.
				seqPath := joinPath(path)
				if _, skip := skipSeq[seqPath]; skip {
					continue
				}
				pk := makeSeqPathKey(path, i, scalarItemKey)
				occs := valIdx[pk]
				if len(occs) == 0 {
					// No original anchor for this index → probably an appended item.
					// Appends are handled by buildSeqAppendPatches.
					continue
				}
				last := occs[len(occs)-1]

				makeTok := func(oldTok []byte, v interface{}) []byte {
					switch t := v.(type) {
					case int:
						return []byte(fmt.Sprintf("%d", t))
					case float64:
						return []byte(strconv.FormatFloat(t, 'g', -1, 64))
					case bool:
						if t {
							return []byte("true")
						}
						return []byte("false")
					case string:
						return stringReplacementToken(oldTok, t)
					case nil:
						return []byte("null")
					default:
						// best-effort string
						return stringReplacementToken(oldTok, fmt.Sprint(t))
					}
				}

				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				newTok := makeTok(oldTok, ev)

				// Avoid churn if identical bytes
				if bytes.Equal(oldTok, newTok) {
					continue
				}
				patches = append(patches, patch{
					start: last.valStart,
					end:   last.valEnd,
					data:  newTok,
				})
			}
		}
		return true
	}

	walkMap = func(ms gyaml.MapSlice, path []string) bool {
		for _, it := range ms {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			switch v := it.Value.(type) {
			case gyaml.MapSlice:
				if !walkMap(v, append(path, k)) {
					return false
				}
			case []interface{}:
				if !walkArr(v, append(path, k)) {
					return false
				}
			case int:
				pk := makePathKey(path, k)
				occs := valIdx[pk]
				if len(occs) == 0 {
					// Key didn't exist originally at this path (it will be handled by insertion)
					continue
				}
				// Replace the LAST occurrence (YAML semantics: last wins)
				last := occs[len(occs)-1]
				newVal := []byte(fmt.Sprintf("%d", v))
				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				// Avoid churn if identical
				if bytes.Equal(oldTok, newVal) {
					continue
				}
				emit(patch{start: last.valStart, end: last.valEnd, data: newVal}, path, k)

			case string:
				pk := makePathKey(path, k)
				occs := valIdx[pk]
				if len(occs) == 0 {
					continue // new key; handled by insertion
				}
				last := occs[len(occs)-1]
				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				newTok := stringReplacementToken(oldTok, v)
				// Avoid churn if identical bytes
				if bytes.Equal(oldTok, newTok) {
					continue
				}
				emit(patch{start: last.valStart, end: last.valEnd, data: newTok}, path, k)

			case bool:
				pk := makePathKey(path, k)
				occs := valIdx[pk]
				if len(occs) == 0 {
					continue // new key; handled by insertion
				}
				last := occs[len(occs)-1]
				var newTok []byte
				if v {
					newTok = []byte("true")
				} else {
					newTok = []byte("false")
				}
				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				if bytes.Equal(oldTok, newTok) {
					continue
				}
				emit(patch{start: last.valStart, end: last.valEnd, data: newTok}, path, k)

			case float64:
				pk := makePathKey(path, k)
				occs := valIdx[pk]
				if len(occs) == 0 {
					continue
				}
				last := occs[len(occs)-1]
				newTok := []byte(strconv.FormatFloat(v, 'g', -1, 64))
				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				if bytes.Equal(oldTok, newTok) {
					continue
				}
				emit(patch{start: last.valStart, end: last.valEnd, data: newTok}, path, k)

			case nil:
				pk := makePathKey(path, k)
				occs := valIdx[pk]
				if len(occs) == 0 {
					continue
				}
				last := occs[len(occs)-1]
				newTok := []byte("null")
				oldTok := bytes.TrimSpace(original[last.valStart:last.valEnd])
				if bytes.Equal(oldTok, newTok) {
					continue
				}
				emit(patch{start: last.valStart, end: last.valEnd, data: newTok}, path, k)

			default:
				// We only byte-patch ints; anything else is left untouched by surgery
				continue
			}
		}
		return true
	}
	if !walkMap(current, nil) {
		return false, nil
	}
	// Flush selected changes per sequence item:
	// - If both "path" and "property" changed, emit BOTH (common entry-replace case).
	// - Otherwise, emit ONE patch chosen deterministically to keep minimal diffs.
	for itemPath, kvs := range perItem {
		// Determine the sequence path (without the trailing [n])
		var seqPath string
		{
			parts := strings.Split(itemPath, pathSep)
			if len(parts) > 0 && isIndexSeg(parts[len(parts)-1]) {
				seqPath = joinPath(parts[:len(parts)-1])
			} else {
				seqPath = joinPath(parts) // shouldn't happen, be safe
			}
		}
		si := seqIdx[seqPath]

		// Build key -> index map for this item's changed scalars
		idxByKey := make(map[string]int, len(kvs))
		for i, kp := range kvs {
			idxByKey[kp.key] = i
		}

		var picks []int
		// Prefer the common pair explicitly when both changed
		if i, ok := idxByKey["path"]; ok {
			picks = append(picks, i)
		}
		if i, ok := idxByKey["property"]; ok {
			picks = append(picks, i)
		}

		if len(picks) == 0 {
			// Minimal single-line change: choose the key that appears LAST
			// in the original key order (deterministic).
			if si != nil && len(si.keyOrder) > 0 {
				order := map[string]int{}
				for i, k := range si.keyOrder {
					order[k] = i
				}
				bestRank := -1
				bestIdx := -1
				for i, kp := range kvs {
					if r, ok := order[kp.key]; ok && r >= bestRank {
						bestRank = r
						bestIdx = i
					}
				}
				if bestIdx >= 0 {
					picks = []int{bestIdx}
				}
			}
		}

		if len(picks) == 0 {
			// Fallback: deterministically prefer "property" if present,
			// else choose the lexicographically greatest key.
			if i, ok := idxByKey["property"]; ok {
				picks = []int{i}
			} else {
				maxKey := ""
				maxIdx := 0
				for i, kp := range kvs {
					if kp.key >= maxKey {
						maxKey = kp.key
						maxIdx = i
					}
				}
				picks = []int{maxIdx}
			}
		}

		for _, i := range picks {
			patches = append(patches, kvs[i].patch)
		}
	}
	return true, patches
}

// Ignore duplicate-removal for keys that are explicitly deleted in this op (to avoid overlap).
// Also skip duplicates under sequences we fully replaced.
func buildDuplicateRemovalPatches(original []byte, current gyaml.MapSlice, valIdx map[string][]valueOcc, ignore map[string]struct{}, skipSeq map[string]struct{}) (bool, []patch) {
	var patches []patch
	// For each path+key that had duplicates originally, remove all but the last line
outer:
	for pk, occs := range valIdx {
		if _, skip := ignore[pk]; skip {
			continue
		}
		// Skip any pk under a replaced sequence (prefix: "<seqPath>\x00[")
		for sp := range skipSeq {
			prefix := sp + pathSep + "["
			if strings.HasPrefix(pk, prefix) {
				continue outer
			}
		}
		if len(occs) <= 1 {
			continue
		}
		for i := 0; i < len(occs)-1; i++ {
			o := occs[i]
			// Delete the whole line (from line start to line end + 1)
			start := o.keyLineStart
			end := o.lineEnd
			// If the file had a newline, include it in deletion so we don't leave blank lines
			if end < len(original) && original[end] == '\n' {
				end++
			}
			patches = append(patches, patch{start: start, end: end, data: []byte{}})
		}
	}
	return true, patches
}

// --- Sequence whole-block replacement when shape changed ---

func buildSeqReplaceBlockPatches(
	original []byte,
	current gyaml.MapSlice,
	originalOrdered gyaml.MapSlice,
	seqIdx map[string]*seqInfo,
	baseIndent int,
) (bool, []patch, map[string]struct{}) {
	var patches []patch
	replaced := map[string]struct{}{}

	// Helper: is every element in arr a scalar (non-map, non-array)?
	isArrayOfScalars := func(arr []interface{}) bool {
		for _, el := range arr {
			switch el.(type) {
			case gyaml.MapSlice, map[string]interface{}, []interface{}:
				return false
			default:
				// ints, float64, bool, string, nil → scalar
			}
		}
		return true
	}

	var getArrAtPath func(ms gyaml.MapSlice, path []string, key string) ([]interface{}, bool)
	getArrAtPath = func(ms gyaml.MapSlice, path []string, key string) ([]interface{}, bool) {
		cur := ms
		for _, seg := range path {
			found := false
			for _, it := range cur {
				ks, ok := it.Key.(string)
				if ok && ks == seg {
					if sub, ok2 := it.Value.(gyaml.MapSlice); ok2 {
						cur = sub
						found = true
						break
					}
				}
			}
			if !found {
				return nil, false
			}
		}
		for _, it := range cur {
			ks, ok := it.Key.(string)
			if ok && ks == key {
				if arr, ok2 := it.Value.([]interface{}); ok2 {
					return arr, true
				}
				return nil, false
			}
		}
		return nil, false
	}

	toMapSlice := func(v interface{}) (gyaml.MapSlice, bool) {
		switch t := v.(type) {
		case gyaml.MapSlice:
			return t, true
		case map[string]interface{}:
			ms := gyaml.MapSlice{}
			for k, vv := range t {
				ms = append(ms, gyaml.MapItem{Key: k, Value: jsonValueToOrdered(vv)})
			}
			return ms, true
		default:
			return gyaml.MapSlice{}, false
		}
	}

	namesOf := func(arr []interface{}) ([]string, bool) {
		out := make([]string, len(arr))
		for i, el := range arr {
			switch it := el.(type) {
			case gyaml.MapSlice:
				found := false
				for _, kv := range it {
					if ks, ok := kv.Key.(string); ok && ks == "name" {
						if sv, ok2 := kv.Value.(string); ok2 {
							out[i] = sv
							found = true
							break
						}
					}
				}
				if !found {
					return nil, false
				}
			case map[string]interface{}:
				if v, ok := it["name"].(string); ok {
					out[i] = v
				} else {
					return nil, false
				}
			default:
				return nil, false
			}
		}
		return out, true
	}

	getName := func(ms gyaml.MapSlice) string {
		for _, it := range ms {
			if ks, ok := it.Key.(string); ok && ks == "name" {
				if sv, ok2 := it.Value.(string); ok2 {
					return sv
				}
			}
		}
		return ""
	}

	renderScalar := func(v interface{}) string {
		switch vv := v.(type) {
		case int:
			return fmt.Sprintf("%d", vv)
		case float64:
			return strconv.FormatFloat(vv, 'g', -1, 64)
		case bool:
			if vv {
				return "true"
			}
			return "false"
		case string:
			if isSafeBareString(vv) {
				return vv
			}
			return quoteNewStringToken(vv)
		case nil:
			return "null"
		default:
			s := fmt.Sprint(vv)
			if isSafeBareString(s) {
				return s
			}
			return quoteNewStringToken(s)
		}
	}

	renderItem := func(si *seqInfo, ms gyaml.MapSlice) (string, bool) {
		vals := map[string]interface{}{}
		for _, it := range ms {
			if ks, ok := it.Key.(string); ok {
				vals[ks] = it.Value
			}
		}
		order := []string{}
		if len(si.keyOrder) > 0 {
			order = append(order, si.keyOrder...)
			for _, it := range ms {
				ks, _ := it.Key.(string)
				found := false
				for _, k := range order {
					if k == ks {
						found = true
						break
					}
				}
				if !found {
					order = append(order, ks)
				}
			}
		} else {
			for _, it := range ms {
				if ks, ok := it.Key.(string); ok {
					order = append(order, ks)
				}
			}
		}
		if len(order) == 0 {
			return "", false
		}
		kvIndent := si.itemKVIndent
		if kvIndent == 0 {
			kvIndent = si.indent + baseIndent
		}
		var sb strings.Builder
		first := order[0]
		fv, ok := vals[first]
		if !ok {
			return "", false
		}
		if si.firstKeyInline {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("- ")
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		} else {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("-\n")
			sb.WriteString(strings.Repeat(" ", kvIndent))
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		}
		for i := 1; i < len(order); i++ {
			k := order[i]
			v, ok := vals[k]
			if !ok {
				continue
			}
			sb.WriteString(strings.Repeat(" ", kvIndent))
			sb.WriteString(k)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(v))
			sb.WriteString("\n")
		}
		return sb.String(), true
	}

	shapeChanged := func(oldArr, newArr []interface{}) bool {
		if len(oldArr) != len(newArr) {
			return true
		}
		oldNames, ok1 := namesOf(oldArr)
		newNames, ok2 := namesOf(newArr)
		if !(ok1 && ok2) {
			// conservative: if we cannot match items by stable identity, treat as shape change
			return true
		}
		for i := range oldNames {
			if oldNames[i] != newNames[i] {
				return true
			}
		}
		return false
	}

	var walk func(ms gyaml.MapSlice, path []string) bool
	walk = func(ms gyaml.MapSlice, path []string) bool {
		for _, it := range ms {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			switch v := it.Value.(type) {
			case gyaml.MapSlice:
				if !walk(v, append(path, k)) {
					return false
				}
			case []interface{}:
				origArr, ok := getArrAtPath(originalOrdered, path, k)
				if !ok {
					// no original anchor to replace against → cannot perform surgical block replace
					continue
				}
				mpath := joinPath(append(path, k))
				si := seqIdx[mpath]
				if si == nil || !si.originalPath || !si.hasAnyItem || si.firstItemStart <= 0 || si.lastItemEnd <= 0 {
					continue
				}
				if isArrayOfScalars(origArr) && isArrayOfScalars(v) {
					// Let later passes (scalar replacements + appends) handle this surgically.
					// Do NOT mark as replaced and do NOT return failure.
					continue
				}
				if !shapeChanged(origArr, v) {
					continue
				}
				// Build "pre-gap" map: next item's name -> gap bytes that preceded it
				preGap := map[string][]byte{}
				if len(si.items) >= 2 && len(si.gaps) == len(si.items)-1 {
					for i := 0; i < len(si.items)-1; i++ {
						nextName := si.items[i+1].name
						if nextName == "" {
							continue
						}
						g := si.gaps[i]
						if len(g) > 0 {
							preGap[nextName] = g
						}
					}
				}
				// Render new block
				var sb strings.Builder
				for _, el := range v {
					msItem, ok := toMapSlice(el)
					if !ok {
						return false
					}
					if nm := getName(msItem); nm != "" {
						if g, ok := preGap[nm]; ok && len(g) > 0 {
							sb.Write(g)
						}
					}
					txt, ok := renderItem(si, msItem)
					if !ok {
						return false
					}
					sb.WriteString(txt)
				}
				start := si.firstItemStart
				end := si.lastItemEnd + 1 // include trailing newline
				if start < 0 || end < start || end > len(original) {
					return false
				}
				patches = append(patches, patch{start: start, end: end, data: []byte(sb.String())})
				replaced[mpath] = struct{}{}
			}
		}
		return true
	}
	if !walk(current, nil) {
		return false, nil, nil
	}
	return true, patches, replaced
}

func buildInsertPatches(
	original []byte,
	current gyaml.MapSlice,
	originalOrdered gyaml.MapSlice,
	mapIdx map[string]*mapInfo,
	baseIndent int,
	indentSeq bool,
) (bool, []patch) {
	var patches []patch

	// Build a quick set of original keys per path for "is new?" checks
	origKeys := map[string]map[string]struct{}{}
	var collect func(ms gyaml.MapSlice, path []string)
	collect = func(ms gyaml.MapSlice, path []string) {
		if origKeys[joinPath(path)] == nil {
			origKeys[joinPath(path)] = map[string]struct{}{}
		}
		for _, it := range ms {
			if k, ok := it.Key.(string); ok {
				origKeys[joinPath(path)][k] = struct{}{}
				if sub, ok2 := it.Value.(gyaml.MapSlice); ok2 {
					collect(sub, append(path, k))
				}
			}
		}
	}
	collect(originalOrdered, nil)

	// Walk current and insert new ints at the end of their mapping
	var walk func(ms gyaml.MapSlice, path []string) bool
	walk = func(ms gyaml.MapSlice, path []string) bool {
		mpath := joinPath(path)
		for _, it := range ms {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			switch v := it.Value.(type) {
			case gyaml.MapSlice:
				if !walk(v, append(path, k)) {
					return false
				}
			case []interface{}:
				// New sequence key insertion (surgical)
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						// No safe anchor to attach the new key bytes → bail to fallback.
						return false
					}
					keyIndent := mi.indent
					if keyIndent == 0 && len(path) > 0 {
						keyIndent = baseIndent * len(path)
					}
					// Where to insert
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}
					var sb strings.Builder
					// If the anchor ended without newline, start a new line.
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							sb.WriteString("\n")
						}
					}
					// Helper: render scalars like the rest of surgery does.
					renderScalar := func(val interface{}) string {
						switch vv := val.(type) {
						case int:
							return fmt.Sprintf("%d", vv)
						case float64:
							return strconv.FormatFloat(vv, 'g', -1, 64)
						case bool:
							if vv {
								return "true"
							}
							return "false"
						case string:
							if isSafeBareString(vv) {
								return vv
							}
							return quoteNewStringToken(vv)
						case nil:
							return "null"
						default:
							s := fmt.Sprint(vv)
							if isSafeBareString(s) {
								return s
							}
							return quoteNewStringToken(s)
						}
					}
					// Helper: stable order — prefer name, then path, property, then others lexicographically.
					orderKeys := func(ms gyaml.MapSlice) []string {
						pref := []string{"name", "path", "property"}
						have := map[string]bool{}
						for _, p := range pref {
							have[p] = false
						}
						keys := []string{}
						// collect presence
						seen := map[string]bool{}
						for _, it := range ms {
							if ks, ok := it.Key.(string); ok {
								seen[ks] = true
							}
						}
						for _, p := range pref {
							if seen[p] {
								keys = append(keys, p)
								have[p] = true
							}
						}
						rest := []string{}
						for _, it := range ms {
							if ks, ok := it.Key.(string); ok && !have[ks] {
								rest = append(rest, ks)
							}
						}
						sort.Strings(rest)
						return append(keys, rest...)
					}
					// Render the new sequence block.
					if len(v) == 0 {
						// Empty array → single line key: []
						sb.WriteString(strings.Repeat(" ", keyIndent))
						sb.WriteString(k)
						sb.WriteString(": []\n")
					} else {
						// Non-empty array → key line + items
						sb.WriteString(strings.Repeat(" ", keyIndent))
						sb.WriteString(k)
						sb.WriteString(":\n")
						itemIndent := keyIndent
						if indentSeq {
							itemIndent = keyIndent + baseIndent
						}
						for _, el := range v {
							switch ev := el.(type) {
							case gyaml.MapSlice:
								// Render IN INLINE style: "- name: …" on first line, then other keys.
								// Choose first key = "name" if present; else use stable ordered first.
								keys := orderKeys(ev)
								if len(keys) == 0 {
									continue
								}
								first := keys[0]
								var firstVal interface{}
								for _, kv := range ev {
									if ks, _ := kv.Key.(string); ks == first {
										firstVal = kv.Value
										break
									}
								}
								sb.WriteString(strings.Repeat(" ", itemIndent))
								sb.WriteString("- ")
								sb.WriteString(first)
								sb.WriteString(": ")
								sb.WriteString(renderScalar(firstVal))
								sb.WriteString("\n")
								kvIndent := itemIndent + baseIndent
								for _, k2 := range keys[1:] {
									// find value
									var v2 interface{}
									for _, kv := range ev {
										if ks, _ := kv.Key.(string); ks == k2 {
											v2 = kv.Value
											break
										}
									}
									sb.WriteString(strings.Repeat(" ", kvIndent))
									sb.WriteString(k2)
									sb.WriteString(": ")
									sb.WriteString(renderScalar(v2))
									sb.WriteString("\n")
								}

							case map[string]interface{}:
								// Convert to ordered MapSlice for stable rendering

								ms := gyaml.MapSlice{}
								for kk, vv := range ev {
									ms = append(ms, gyaml.MapItem{Key: kk, Value: vv})
								}
								keys := orderKeys(ms)
								if len(keys) == 0 {
									continue
								}
								var firstVal interface{}
								for _, kv := range ms {
									if ks, _ := kv.Key.(string); ks == keys[0] {
										firstVal = kv.Value
										break
									}
								}
								sb.WriteString(strings.Repeat(" ", itemIndent))
								sb.WriteString("- ")
								sb.WriteString(keys[0])
								sb.WriteString(": ")
								sb.WriteString(renderScalar(firstVal))
								sb.WriteString("\n")
								kvIndent := itemIndent + baseIndent
								for _, k2 := range keys[1:] {
									var v2 interface{}
									for _, kv := range ms {
										if ks, _ := kv.Key.(string); ks == k2 {
											v2 = kv.Value
											break
										}
									}
									sb.WriteString(strings.Repeat(" ", kvIndent))
									sb.WriteString(k2)
									sb.WriteString(": ")
									sb.WriteString(renderScalar(v2))
									sb.WriteString("\n")
								}

							default:
								// Scalar item
								sb.WriteString(strings.Repeat(" ", itemIndent))
								sb.WriteString("- ")
								sb.WriteString(renderScalar(ev))
								sb.WriteString("\n")
							}
						}
					}
					data := []byte(sb.String())
					patches = append(patches, patch{start: insertPos, end: insertPos, data: data})
					// Advance anchor for subsequent inserts into the same mapping.
					mi.lastLineEnd = insertPos + len(data) - 1
					mapIdx[mpath] = mi
				}
				// Recurse into sequence items is not needed for insertion phase.
				// Any nested new keys will be handled when editing those items later.
			case int:
				// New key?
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					// Need an existing mapping anchor line to attach insertions to
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						// No safe place to insert bytes → fall back
						return false
					}
					// Indent for keys inside this mapping.
					indent := mi.indent
					// If indent wasn't captured, approximate from depth * baseIndent
					if indent == 0 && len(path) > 0 {
						indent = baseIndent * len(path)
					}
					line := fmt.Sprintf("%s%s: %d\n", strings.Repeat(" ", indent), k, v)
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
					mi.lastLineEnd = insertPos + len(line) - 1
					mapIdx[mpath] = mi
				}
			case string:
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						return false
					}
					indent := mi.indent
					if indent == 0 && len(path) > 0 {
						indent = baseIndent * len(path)
					}
					valTok := quoteNewStringToken(v) // choose safe, stable quoting
					line := fmt.Sprintf("%s%s: %s\n", strings.Repeat(" ", indent), k, valTok)
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}

					// If the anchor line had no trailing newline (EOF case), ensure the new key starts on a new line.
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}

					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
					// Advance the local anchor so multiple insertions chain in order
					mi.lastLineEnd = insertPos + len(line) - 1
					mapIdx[mpath] = mi
				}
			case bool:
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						return false
					}
					indent := mi.indent
					if indent == 0 && len(path) > 0 {
						indent = baseIndent * len(path)
					}
					valTok := "false"
					if v {
						valTok = "true"
					}
					line := fmt.Sprintf("%s%s: %s\n", strings.Repeat(" ", indent), k, valTok)
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
					mi.lastLineEnd = insertPos + len(line) - 1
					mapIdx[mpath] = mi
				}
			case float64:
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						return false
					}
					indent := mi.indent
					if indent == 0 && len(path) > 0 {
						indent = baseIndent * len(path)
					}
					valTok := strconv.FormatFloat(v, 'g', -1, 64)
					line := fmt.Sprintf("%s%s: %s\n", strings.Repeat(" ", indent), k, valTok)
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
					mi.lastLineEnd = insertPos + len(line) - 1
					mapIdx[mpath] = mi
				}
			case nil:
				if _, existed := origKeys[mpath][k]; !existed {
					mi := mapIdx[mpath]
					if mi == nil || !mi.originalPath || !mi.hasAnyKey {
						return false
					}
					indent := mi.indent
					if indent == 0 && len(path) > 0 {
						indent = baseIndent * len(path)
					}
					line := fmt.Sprintf("%s%s: null\n", strings.Repeat(" ", indent), k)
					insertPos := mi.lastLineEnd + 1
					if insertPos < 0 || insertPos > len(original) {
						return false
					}
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
					mi.lastLineEnd = insertPos + len(line) - 1
					mapIdx[mpath] = mi
				}
			default:
				continue
			}
		}
		return true
	}
	if !walk(current, nil) {
		return false, nil
	}
	return true, patches
}

// explicit deletion patches for requested keys (remove whole lines for ALL occurrences)
func buildDeletionPatches(original []byte, deletions map[string]struct{}, valIdx map[string][]valueOcc) (bool, []patch) {
	if len(deletions) == 0 {
		return true, nil
	}
	var patches []patch
	for pk := range deletions {
		occs := valIdx[pk]
		if len(occs) == 0 {
			// No scalar line for this key. It might be a sequence or mapping value.
			// If it is a sequence we indexed, delete the whole block (header + items).
			// pk has the form "a\0b\0...<key>"
			parts := strings.Split(pk, pathSep)
			if len(parts) >= 1 {
				seqPath := joinPath(parts) // joinPath copies; we actually need the full path, not just parent
				// For sequences we indexed them with the full mapping path (parent + key).
				if si, ok := globalSeqLookupForDeletion(seqPath); ok {
					start := si.headerLineStart
					end := si.headerLineEnd
					if si.hasAnyItem && si.lastItemEnd >= end {
						end = si.lastItemEnd
					}
					// delete the newline after end if present
					if end < len(original) && original[end] == '\n' {
						end++
					} else {
						end++ // safe: Apply will clamp
					}
					if start >= 0 && end >= start && end <= len(original) {
						patches = append(patches, patch{start: start, end: end, data: []byte{}})
					}
					continue
				}
			}
			// Otherwise: no surgical deletion for this key; fallback will handle it.
			continue

		}
		for _, o := range occs {
			start := o.keyLineStart
			end := o.lineEnd
			if end < len(original) && original[end] == '\n' {
				end++
			}
			patches = append(patches, patch{start: start, end: end, data: []byte{}})
		}
	}
	return true, patches
}

// globalSeqLookupForDeletion provides access to seqIndex for deletion,
// by probing the registered docStates. We do not hold regMu while reading per-state maps.
func globalSeqLookupForDeletion(path string) (*seqInfo, bool) {
	regMu.Lock()
	states := make([]*docState, 0, len(reg))
	for _, s := range reg {
		states = append(states, s)
	}
	regMu.Unlock()
	for _, s := range states {
		s.mu.RLock()
		if si, ok := s.seqIndex[path]; ok && si != nil && si.originalPath {
			s.mu.RUnlock()
			return si, true
		}
		s.mu.RUnlock()
	}
	return nil, false
}

// ----- Small utilities for indices and scanning -----

func cloneMapSlice(ms gyaml.MapSlice) gyaml.MapSlice {
	out := make(gyaml.MapSlice, 0, len(ms))
	for _, it := range ms {
		var v interface{}
		switch vv := it.Value.(type) {
		case gyaml.MapSlice:
			v = cloneMapSlice(vv)
		case []interface{}:
			v = cloneSlice(vv)
		default:
			v = vv
		}
		out = append(out, gyaml.MapItem{Key: it.Key, Value: v})
	}
	return out
}

func cloneSlice(in []interface{}) []interface{} {
	out := make([]interface{}, len(in))
	for i, e := range in {
		switch tv := e.(type) {
		case gyaml.MapSlice:
			out[i] = cloneMapSlice(tv)
		case []interface{}:
			out[i] = cloneSlice(tv)
		default:
			out[i] = tv
		}
	}
	return out
}

func cloneMapIndex(in map[string]*mapInfo) map[string]*mapInfo {
	out := make(map[string]*mapInfo, len(in))
	for k, v := range in {
		cp := *v
		out[k] = &cp
	}
	return out
}

func cloneValueIndex(in map[string][]valueOcc) map[string][]valueOcc {
	out := make(map[string][]valueOcc, len(in))
	for k, v := range in {
		cp := make([]valueOcc, len(v))
		copy(cp, v)
		out[k] = cp
	}
	return out
}

const pathSep = "\x00p\x00"

// Sentinel key used to index scalar values that are direct items of a sequence ("- <scalar>")
const scalarItemKey = "\x00s\x00"

func joinPath(path []string) string {
	if len(path) == 0 {
		return ""
	}
	return strings.Join(path, pathSep)
}

func makePathKey(path []string, key string) string {
	if len(path) == 0 {
		return key
	}
	return strings.Join(append(append([]string{}, path...), key), pathSep)
}

func buildLineOffsets(b []byte) []int {
	offsets := []int{0}
	for i, c := range b {
		if c == '\n' {
			if i+1 < len(b) {
				offsets = append(offsets, i+1)
			}
		}
	}
	return offsets
}

func offsetFor(lineOffsets []int, line, col int) int {
	// yaml.v3 uses 1-based line/column
	if line <= 0 || col <= 0 || line > len(lineOffsets) {
		return -1
	}
	return lineOffsets[line-1] + (col - 1)
}

func lineStartOffset(lineOffsets []int, line int) int {
	if line <= 0 || line > len(lineOffsets) {
		return 0
	}
	return lineOffsets[line-1]
}

func findLineEnd(b []byte, from int) int {
	if from < 0 {
		return 0
	}
	for i := from; i < len(b); i++ {
		if b[i] == '\n' {
			return i
		}
	}
	// no newline; pretend the "end" sits at len-1 so 'end+1' is safe-checked by callers
	return len(b) - 1
}

// findScalarEndOnLine returns the end (exclusive) of the scalar token that starts at 'pos',
// scanning only within the current line. This is conservative and aims to handle:
//   - bare ints: -?[0-9_]+
//   - quoted scalars: '...' or "..." (we'll stop at the closing quote on this line)
//   - otherwise, we stop at the first '#' or end-of-line, trimming trailing spaces
func findScalarEndOnLine(b []byte, pos int) int {
	if pos < 0 || pos >= len(b) {
		return pos
	}
	i := pos
	// Determine line end
	le := findLineEnd(b, pos)
	if le < pos {
		le = len(b)
	}
	// If quoted
	if b[i] == '\'' {
		i++ // after opening '
		for i <= le {
			if i == le { // hit end of line
				return le
			}
			if b[i] == '\'' {
				// YAML single quotes escape as ''
				if i+1 <= le && b[i+1] == '\'' {
					i += 2
					continue
				}
				return i + 1 // include closing quote
			}
			i++
		}
		return le
	}
	if b[i] == '"' {
		i++ // after opening "
		esc := false
		for i <= le {
			if i == le {
				return le
			}
			if esc {
				esc = false
				i++
				continue
			}
			if b[i] == '\\' {
				esc = true
				i++
				continue
			}
			if b[i] == '"' {
				return i + 1
			}
			i++
		}
		return le
	}

	// Bare token: read until comment or newline
	j := pos
	for j < le {
		if b[j] == '#' {
			break
		}
		j++
	}
	// Trim trailing spaces before comment/hash
	k := j
	for k > pos && (b[k-1] == ' ' || b[k-1] == '\t') {
		k--
	}
	return k
}

// --------------------------------------------------------------------------------------
// Indent / sequence detection (unchanged)
// --------------------------------------------------------------------------------------

// detectIndentAndSequence returns the base indent, and whether sequences that are values
// of mapping keys are indented one level (true) or "indentless" (false).
func detectIndentAndSequence(b []byte) (int, bool) {
	indent := detectIndent(b)
	lines := bytes.Split(b, []byte("\n"))
	votes := 0 // >0 prefer indented seq, <0 prefer indentless

	for i := 0; i < len(lines); i++ {
		ln := lines[i]
		if isBlankOrComment(ln) {
			continue
		}
		if endsWithMappingKey(ln) {
			keyIndent := leadingSpaces(ln)
			// look ahead to the first non-blank, non-comment line
			for j := i + 1; j < len(lines); j++ {
				nxt := lines[j]
				if isBlankOrComment(nxt) {
					continue
				}
				lsp := leadingSpaces(nxt)
				trimmed := bytes.TrimLeft(nxt, " ")
				if len(trimmed) > 0 && trimmed[0] == '-' {
					if lsp == keyIndent+indent {
						votes++
					} else if lsp == keyIndent {
						votes--
					}
				}
				break
			}
		}
	}
	if votes > 0 {
		return indent, true
	}
	if votes < 0 {
		return indent, false
	}
	// default to indented sequences (common in K8s/Helm repos)
	return indent, true
}

func isBlankOrComment(ln []byte) bool {
	t := bytes.TrimSpace(ln)
	return len(t) == 0 || t[0] == '#'
}

// endsWithMappingKey returns true if the line is a block mapping key of the form "key:"
// possibly followed by spaces and/or a comment.
func endsWithMappingKey(ln []byte) bool {
	idx := bytes.IndexByte(ln, ':')
	if idx < 0 {
		return false
	}
	rest := bytes.TrimSpace(ln[idx+1:])
	return len(rest) == 0 || rest[0] == '#'
}

func detectIndent(b []byte) int {
	lines := bytes.Split(b, []byte("\n"))

	// Collect all non-zero indents from non-blank, non-comment lines
	indents := []int{}
	for _, ln := range lines {
		if len(bytes.TrimSpace(ln)) == 0 {
			continue
		}
		// Skip pure comment lines
		trimmed := bytes.TrimLeft(ln, " ")
		if len(trimmed) > 0 && trimmed[0] == '#' {
			continue
		}

		n := leadingSpaces(ln)
		if n > 0 {
			indents = append(indents, n)
		}
	}

	if len(indents) == 0 {
		return 2
	}

	// Find the GCD of all indents to get base indent
	result := indents[0]
	for i := 1; i < len(indents); i++ {
		result = gcd(result, indents[i])
		if result == 1 {
			break // Can't get smaller than 1
		}
	}

	if result > 0 && result <= 8 {
		return result
	}
	return 2
}

func gcd(a, b int) int {
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// makeSeqPathKey builds the index for a scalar key inside a mapping item located at a sequence under 'path'.
// The segment for the index is encoded as "[<idx>]" to avoid collisions with real keys.
func makeSeqPathKey(path []string, idx int, key string) string {
	segs := make([]string, 0, len(path)+2)
	segs = append(segs, path...)
	segs = append(segs, fmt.Sprintf("[%d]", idx))
	segs = append(segs, key)
	return strings.Join(segs, pathSep)
}

func leadingSpaces(line []byte) int {
	i := 0
	for i < len(line) && line[i] == ' ' {
		i++
	}
	return i
}

func firstNonSpaceByte(line []byte) byte {
	for _, b := range line {
		if b != ' ' && b != '\t' {
			return b
		}
	}
	return 0
}

// --------------------------------------------------------------------------------------
// Fallback helpers: shape-change detection + dedupe
// --------------------------------------------------------------------------------------

func hasShapeChange(originalOrdered, current gyaml.MapSlice) bool {
	om := lastMap(originalOrdered)
	cm := lastMap(current)
	for k, ov := range om {
		cv, ok := cm[k]
		if !ok {
			continue
		}
		_, oIsMap := ov.(gyaml.MapSlice)
		_, cIsMap := cv.(gyaml.MapSlice)
		if oIsMap != cIsMap {
			return true
		}
		if oIsMap && cIsMap {
			if hasShapeChange(ov.(gyaml.MapSlice), cv.(gyaml.MapSlice)) {
				return true
			}
		}
	}
	return false
}

func lastMap(ms gyaml.MapSlice) map[string]interface{} {
	m := make(map[string]interface{}, len(ms))
	for _, it := range ms {
		if k, ok := it.Key.(string); ok {
			m[k] = it.Value
		}
	}
	return m
}

// --------------------------------------------------------------------------------------
// string token helpers for surgical replacements/insertions
// --------------------------------------------------------------------------------------

var yamlBareDisallowed = map[string]struct{}{
	"true": {}, "false": {}, "True": {}, "False": {},
	"yes": {}, "no": {}, "Yes": {}, "No": {},
	"on": {}, "off": {}, "On": {}, "Off": {},
	"null": {}, "Null": {}, "NULL": {}, "~": {},
}

func isSafeBareString(s string) bool {
	if _, bad := yamlBareDisallowed[s]; bad {
		return false
	}
	if len(s) == 0 {
		return false
	}
	// Disallow whitespace or YAML special chars that frequently need quoting
	for _, r := range s {
		switch r {
		case ' ', '\t', '\n', ':', '#', '{', '}', '[', ']', ',', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`':
			return false
		}
	}
	return true
}

// Use existing quote style when replacing; if old token was bare but new is unsafe, add quotes.
func stringReplacementToken(oldTok []byte, newVal string) []byte {
	if len(oldTok) > 0 && oldTok[0] == '\'' {
		// single-quoted → escape by doubling single quotes
		return []byte("'" + strings.ReplaceAll(newVal, "'", "''") + "'")
	}
	if len(oldTok) > 0 && oldTok[0] == '"' {
		return []byte(`"` + escapeDoubleQuotes(newVal) + `"`)
	}
	// If the original token was bare and the value didn't change, keep it as-is.
	if string(oldTok) == newVal {
		return append([]byte(nil), oldTok...)
	}
	// Bare previously
	if isSafeBareString(newVal) {
		return []byte(newVal)
	}
	// default to double-quoted for safety
	return []byte(`"` + escapeDoubleQuotes(newVal) + `"`)
}

// For new insertions, prefer single quotes (no escapes) if possible; otherwise double-quote.
func quoteNewStringToken(s string) string {
	if !strings.Contains(s, "'") && !strings.ContainsAny(s, "\n\r\t") {
		return "'" + s + "'"
	}
	return `"` + escapeDoubleQuotes(s) + `"`
}

func escapeDoubleQuotes(s string) string {
	// Keep it simple: escape backslash and double quote; also encode newlines/tabs
	repl := strings.NewReplacer(
		`\\`, `\\`,
		`"`, `\"`,
		"\n", `\n`,
		"\r", `\r`,
		"\t", `\t`,
	)
	return repl.Replace(s)
}

// --------------------------------------------------------------------------------------
// JSON Patch (RFC-6902) public API
// --------------------------------------------------------------------------------------

// ApplyJSONPatchBytes applies a JSON Patch (as raw JSON) to a YAML node.
// Paths are resolved relative to 'node' (DocumentNode or MappingNode).
func ApplyJSONPatchBytes(node *yaml.Node, patchJSON []byte) error {
	return ApplyJSONPatchAtPathBytes(node, patchJSON, nil)
}

// ApplyJSONPatch applies a github.com/evanphx/json-patch/v5 Patch to a YAML node.
// Internally this marshals the patch back to JSON and delegates to ApplyJSONPatchBytes.
func ApplyJSONPatch(node *yaml.Node, patch jsonpatch.Patch) error {
	b, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("yamledit: cannot marshal jsonpatch.Patch; pass bytes instead: %w", err)
	}
	return ApplyJSONPatchBytes(node, b)
}

// ApplyJSONPatchAtPathBytes applies a JSON Patch, treating each op's path as relative
// to the given basePath (sequence of mapping keys).
func ApplyJSONPatchAtPathBytes(node *yaml.Node, patchJSON []byte, basePath []string) error {
	ops, err := decodePatchOps(patchJSON)
	if err != nil {
		return err
	}
	return applyDecodedPatch(node, ops, basePath)
}

// ApplyJSONPatchAtPath is a convenience wrapper for jsonpatch.Patch.
func ApplyJSONPatchAtPath(node *yaml.Node, patch jsonpatch.Patch, basePath []string) error {
	b, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("yamledit: cannot marshal jsonpatch.Patch; pass bytes instead: %w", err)
	}
	return ApplyJSONPatchAtPathBytes(node, b, basePath)
}

// --------------------------------------------------------------------------------------
// JSON Patch internals
// --------------------------------------------------------------------------------------

type patchOp struct {
	Op    string          `json:"op"`
	Path  string          `json:"path"`
	Value json.RawMessage `json:"value,omitempty"`
	From  string          `json:"from,omitempty"`
}

func decodePatchOps(b []byte) ([]patchOp, error) {
	var ops []patchOp
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&ops); err != nil {
		return nil, fmt.Errorf("yamledit: invalid JSON Patch: %w", err)
	}
	if len(ops) == 0 {
		return nil, errors.New("yamledit: empty JSON Patch")
	}
	return ops, nil
}

// ptrToken models one JSON Pointer segment: either a mapping key or an array index/append.
type ptrToken struct {
	key    string
	index  int
	isIdx  bool
	append bool // only valid for add into arrays
}

func parseJSONPointer(p string) ([]ptrToken, error) {
	if p == "" || p == "/" {
		// root pointer; empty token list means operate on 'node' itself
		if p == "/" {
			// split on leading '/', yields ["", ...], trim empty head
			return []ptrToken{}, nil
		}
		return []ptrToken{}, nil
	}
	if !strings.HasPrefix(p, "/") {
		return nil, fmt.Errorf("yamledit: JSON Pointer must start with '/': %q", p)
	}
	parts := strings.Split(p, "/")[1:]
	toks := make([]ptrToken, 0, len(parts))
	for _, s := range parts {
		seg := strings.ReplaceAll(strings.ReplaceAll(s, "~1", "/"), "~0", "~")
		if seg == "-" {
			toks = append(toks, ptrToken{isIdx: true, append: true})
			continue
		}
		// numeric?
		if i, err := strconv.Atoi(seg); err == nil {
			toks = append(toks, ptrToken{isIdx: true, index: i})
			continue
		}
		toks = append(toks, ptrToken{key: seg})
	}
	return toks, nil
}

// applyDecodedPatch executes ops in-order, relative to basePath.
func applyDecodedPatch(node *yaml.Node, ops []patchOp, basePath []string) error {
	if node == nil {
		return errors.New("yamledit: nil node")
	}

	// Identify starting mapping + doc state.
	startMap, baseFromRoot, st, docHN, err := resolveStart(node)
	if err != nil {
		return err
	}
	for _, op := range ops {
		segPath, err := parseJSONPointer(op.Path)
		if err != nil {
			return err
		}
		// Prepend basePath (mapping segments only).
		combined := make([]ptrToken, 0, len(basePath)+len(segPath))
		for _, k := range basePath {
			combined = append(combined, ptrToken{key: k})
		}
		combined = append(combined, segPath...)

		switch strings.ToLower(op.Op) {
		case "test":
			if err := opTest(startMap, combined, op.Value); err != nil {
				return err
			}
		case "add":
			if err := opAdd(startMap, st, docHN, baseFromRoot, combined, op.Value); err != nil {
				return err
			}
		case "remove":
			if err := opRemove(startMap, st, baseFromRoot, combined); err != nil {
				return err
			}
		case "replace":
			if err := opReplace(startMap, st, docHN, baseFromRoot, combined, op.Value); err != nil {
				return err
			}
		case "move":
			if err := opMove(startMap, st, docHN, baseFromRoot, op.From, op.Path); err != nil {
				return err
			}
		case "copy":
			if err := opCopy(startMap, st, docHN, baseFromRoot, op.From, op.Path); err != nil {
				return err
			}
		default:
			return fmt.Errorf("yamledit: unsupported op %q", op.Op)
		}
	}
	return nil
}

// resolveStart returns the mapping node to operate on, the YAML path from root,
// the docState and the root document handle.
func resolveStart(node *yaml.Node) (startMap *yaml.Node, pathFromRoot []string, st *docState, docHN *yaml.Node, err error) {
	switch node.Kind {
	case yaml.DocumentNode:
		if len(node.Content) == 0 || node.Content[0].Kind != yaml.MappingNode {
			return nil, nil, nil, nil, errors.New("yamledit: document root is not a mapping")
		}
		startMap = node.Content[0]
		if s, ok := lookup(node); ok {
			st = s
			docHN = node
			pathFromRoot = nil
		}
	case yaml.MappingNode:
		startMap = node
		if s, doc, base, ok := findOwnerByMapNode(startMap); ok {
			st = s
			docHN = doc
			pathFromRoot = base
		}
	default:
		return nil, nil, nil, nil, errors.New("yamledit: ApplyJSONPatch requires a DocumentNode or MappingNode")
	}
	return
}

// --- JSON → (ordered value, yaml.Node) helpers ---

func decodeJSONValue(raw json.RawMessage) (interface{}, error) {
	if raw == nil {
		return nil, errors.New("yamledit: missing 'value' for operation")
	}
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	var v interface{}
	if err := dec.Decode(&v); err != nil {
		return nil, fmt.Errorf("yamledit: invalid JSON value: %w", err)
	}
	return v, nil
}

func jsonValueToOrdered(v interface{}) interface{} {
	switch t := v.(type) {
	case json.Number:
		if strings.ContainsAny(string(t), ".eE") {
			f, _ := t.Float64()
			return f
		}
		// int
		i, err := t.Int64()
		if err != nil {
			// fallback
			f, _ := t.Float64()
			return f
		}
		return int(i)
	case float64, bool, string, nil:
		return t
	case []interface{}:
		out := make([]interface{}, 0, len(t))
		for _, e := range t {
			out = append(out, jsonValueToOrdered(e))
		}
		return out
	case map[string]interface{}:
		// order is not guaranteed in JSON; create a MapSlice in iteration order
		ms := gyaml.MapSlice{}
		for k, vv := range t {
			ms = append(ms, gyaml.MapItem{Key: k, Value: jsonValueToOrdered(vv)})
		}
		return ms
	default:
		return t
	}
}

func jsonValueToYAMLNode(v interface{}) *yaml.Node {
	switch t := v.(type) {
	case nil:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null", Value: "null"}
	case bool:
		if t {
			return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "true"}
		}
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "false"}
	case json.Number:
		if strings.ContainsAny(string(t), ".eE") {
			f, _ := t.Float64()
			return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: strconv.FormatFloat(f, 'g', -1, 64)}
		}
		i, err := t.Int64()
		if err != nil {
			// fallback to float
			f, _ := t.Float64()
			return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: strconv.FormatFloat(f, 'g', -1, 64)}
		}
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatInt(i, 10)}
	case float64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: strconv.FormatFloat(t, 'g', -1, 64)}
	case int:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.Itoa(t)}
	case int64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatInt(t, 10)}
	case string:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: t}
	case []interface{}:
		seq := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq"}
		for _, e := range t {
			seq.Content = append(seq.Content, jsonValueToYAMLNode(e))
		}
		return seq
	case map[string]interface{}:
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for k, vv := range t {
			mp.Content = append(mp.Content, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}, jsonValueToYAMLNode(vv))
		}
		return mp
	case gyaml.MapSlice:
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for _, it := range t {
			ks, _ := it.Key.(string)
			mp.Content = append(mp.Content, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: ks}, jsonValueToYAMLNode(it.Value))
		}
		return mp
	default:
		// best-effort string
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: fmt.Sprint(t)}
	}
}

// yamlNodeToInterface converts a YAML node to canonical Go types for comparison.
func yamlNodeToInterface(n *yaml.Node) interface{} {
	if n == nil {
		return nil
	}
	switch n.Kind {
	case yaml.ScalarNode:
		switch n.Tag {
		case "!!null":
			return nil
		case "!!bool":
			return strings.EqualFold(n.Value, "true")
		case "!!int":
			// best-effort parse
			if i, err := strconv.ParseInt(n.Value, 10, 64); err == nil {
				return int(i)
			}
			return n.Value
		case "!!float":
			if f, err := strconv.ParseFloat(n.Value, 64); err == nil {
				return f
			}
			return n.Value
		default:
			return n.Value
		}
	case yaml.MappingNode:
		m := map[string]interface{}{}
		for i := 0; i+1 < len(n.Content); i += 2 {
			if n.Content[i].Kind == yaml.ScalarNode {
				m[n.Content[i].Value] = yamlNodeToInterface(n.Content[i+1])
			}
		}
		return m
	case yaml.SequenceNode:
		arr := make([]interface{}, 0, len(n.Content))
		for _, c := range n.Content {
			arr = append(arr, yamlNodeToInterface(c))
		}
		return arr
	default:
		return nil
	}
}

// --- Path resolution on YAML AST ---

// resolveParent locates the parent node for the final token.
// If createForAdd is true, it will EnsurePath for missing mapping segments (not arrays).
func resolveParent(start *yaml.Node, tokens []ptrToken, createForAdd bool) (parent *yaml.Node, last ptrToken, err error) {
	if start == nil {
		return nil, ptrToken{}, errors.New("yamledit: nil start node")
	}
	// normalize to mapping start
	var cur *yaml.Node
	switch start.Kind {
	case yaml.DocumentNode:
		if len(start.Content) == 0 || start.Content[0].Kind != yaml.MappingNode {
			return nil, ptrToken{}, errors.New("yamledit: document has no mapping root")
		}
		cur = start.Content[0]
	case yaml.MappingNode:
		cur = start
	default:
		return nil, ptrToken{}, errors.New("yamledit: start node must be DocumentNode or MappingNode")
	}
	if len(tokens) == 0 {
		return cur, ptrToken{}, nil
	}

	// walk up to parent
	for i := 0; i < len(tokens)-1; i++ {
		t := tokens[i]
		if cur.Kind == yaml.MappingNode {
			if t.isIdx {
				return nil, ptrToken{}, fmt.Errorf("yamledit: cannot index into mapping at segment %d", i)
			}
			// find mapping key
			var child *yaml.Node
			for j := 0; j+1 < len(cur.Content); j += 2 {
				if cur.Content[j].Kind == yaml.ScalarNode && cur.Content[j].Value == t.key {
					child = cur.Content[j+1]
					break
				}
			}
			if child == nil {
				if !createForAdd {
					return nil, ptrToken{}, fmt.Errorf("yamledit: path not found at %q", t.key)
				}
				// create mapping
				key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: t.key}
				val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
				cur.Content = append(cur.Content, key, val)
				child = val
			}
			cur = child
		} else if cur.Kind == yaml.SequenceNode {
			if !t.isIdx {
				return nil, ptrToken{}, fmt.Errorf("yamledit: expected array index at segment %d", i)
			}
			if t.index < 0 || t.index >= len(cur.Content) {
				return nil, ptrToken{}, fmt.Errorf("yamledit: array index out of bounds at segment %d", i)
			}
			cur = cur.Content[t.index]
		} else {
			return nil, ptrToken{}, fmt.Errorf("yamledit: cannot traverse into node kind %v at segment %d", cur.Kind, i)
		}
	}
	return cur, tokens[len(tokens)-1], nil
}

// --- Operations ---

func opTest(start *yaml.Node, tokens []ptrToken, expectRaw json.RawMessage) error {
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	var target *yaml.Node
	if last.isIdx {
		if parent.Kind != yaml.SequenceNode {
			return errors.New("yamledit: test: parent is not an array")
		}
		if last.append {
			return errors.New("yamledit: test: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: test: index %d out of bounds", last.index)
		}
		target = parent.Content[last.index]
	} else {
		if parent.Kind != yaml.MappingNode {
			return errors.New("yamledit: test: parent is not a mapping")
		}
		for i := 0; i+1 < len(parent.Content); i += 2 {
			if parent.Content[i].Kind == yaml.ScalarNode && parent.Content[i].Value == last.key {
				target = parent.Content[i+1]
				break
			}
		}
		if target == nil {
			return fmt.Errorf("yamledit: test: key %q not found", last.key)
		}
	}

	got := yamlNodeToInterface(target)
	var want interface{}
	dec := json.NewDecoder(bytes.NewReader(expectRaw))
	dec.UseNumber()
	if err := dec.Decode(&want); err != nil {
		return fmt.Errorf("yamledit: test: invalid expected value: %w", err)
	}
	want = jsonValueToOrdered(want)
	if !deepEqual(got, want) {
		return fmt.Errorf("yamledit: test operation failed: expected %v, got %v", want, got)
	}
	return nil
}

func opAdd(start *yaml.Node, st *docState, docHN *yaml.Node, basePath []string, tokens []ptrToken, raw json.RawMessage) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: add: empty path not supported")
	}
	parent, last, err := resolveParent(start, tokens, true)
	if err != nil {
		return err
	}
	// decode value
	v, err := decodeJSONValue(raw)
	if err != nil {
		return err
	}
	orderedVal := jsonValueToOrdered(v)
	yval := jsonValueToYAMLNode(orderedVal)

	// Update ordered tree, AST, and set fallback when arrays/complex structures are involved.
	if last.isIdx {
		if parent.Kind != yaml.SequenceNode {
			return errors.New("yamledit: add: parent is not an array")
		}
		if last.append {
			// Append to end: update AST and ordered view
			parent.Content = append(parent.Content, yval)
			if st != nil {
				st.mu.Lock()
				absTokens := appendPathTokens(basePath, tokens)
				// Append in ordered view
				st.ordered, _ = orderedAddArray(st.ordered, absTokens, orderedVal, true)
				// rely on surgical append in Marshal
				st.mu.Unlock()
			}
			return nil
		} else {
			if last.index < 0 || last.index > len(parent.Content) {
				return fmt.Errorf("yamledit: add: index %d out of bounds", last.index)
			}
			parent.Content = append(parent.Content, nil)
			copy(parent.Content[last.index+1:], parent.Content[last.index:])
			parent.Content[last.index] = yval
		}
	}

	// mapping
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: add: parent is not a mapping")
	}

	// If scalar, prefer surgical setters
	switch vv := orderedVal.(type) {
	case int:
		SetScalarInt(parent, last.key, vv)
	case float64:
		SetScalarFloat(parent, last.key, vv)
	case bool:
		SetScalarBool(parent, last.key, vv)
	case string:
		SetScalarString(parent, last.key, vv)
	case nil:
		SetScalarNull(parent, last.key)
	default:
		// complex insert (map/array)
		// AST
		replaced := false
		for i := 0; i+1 < len(parent.Content); i += 2 {
			if parent.Content[i].Kind == yaml.ScalarNode && parent.Content[i].Value == last.key {
				parent.Content[i+1] = yval
				replaced = true
				break
			}
		}
		if !replaced {
			k := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: last.key}
			parent.Content = append(parent.Content, k, yval)
		}
		if st != nil {
			st.mu.Lock()
			if _, ok := st.subPathByHN[parent]; !ok && docHN != nil {
				indexMappingHandles(st, docHN.Content[0], nil)
			}
			path := st.subPathByHN[parent]
			st.ordered = setAnyAtPath(st.ordered, path, last.key, orderedVal)
			st.mu.Unlock()
		}
	}
	return nil
}

func opRemove(start *yaml.Node, st *docState, baseFromRoot []string, tokens []ptrToken) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: remove: empty path not supported")
	}
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	if last.isIdx {
		if parent.Kind != yaml.SequenceNode {
			return errors.New("yamledit: remove: parent is not an array")
		}
		if last.append {
			return errors.New("yamledit: remove: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: remove: index %d out of bounds", last.index)
		}
		parent.Content = append(parent.Content[:last.index], parent.Content[last.index+1:]...)
		if st != nil {
			st.mu.Lock()
			absTokens := appendPathTokens(baseFromRoot, tokens)
			st.ordered, _ = orderedRemoveArray(st.ordered, absTokens)
			st.arraysDirty = true
			st.mu.Unlock()
		}
		return nil
	}
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: remove: parent is not a mapping")
	}
	DeleteKey(parent, last.key)
	return nil
}

func opReplace(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []string, tokens []ptrToken, raw json.RawMessage) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: replace: empty path not supported")
	}
	// must exist
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	v, err := decodeJSONValue(raw)
	if err != nil {
		return err
	}
	orderedVal := jsonValueToOrdered(v)
	yval := jsonValueToYAMLNode(orderedVal)

	if last.isIdx {
		if parent.Kind != yaml.SequenceNode {
			return errors.New("yamledit: replace: parent is not an array")
		}
		if last.append {
			return errors.New("yamledit: replace: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: replace: index %d out of bounds", last.index)
		}
		parent.Content[last.index] = yval
		if st != nil {
			st.mu.Lock()
			absTokens := appendPathTokens(baseFromRoot, tokens)
			st.ordered, _ = orderedReplaceArray(st.ordered, absTokens, orderedVal)
			st.arraysDirty = true
			st.mu.Unlock()
		}
		return nil
	}
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: replace: parent is not a mapping")
	}
	// choose surgical replacements for scalars
	switch vv := orderedVal.(type) {
	case int:
		SetScalarInt(parent, last.key, vv)
	case float64:
		SetScalarFloat(parent, last.key, vv)
	case bool:
		SetScalarBool(parent, last.key, vv)
	case string:
		SetScalarString(parent, last.key, vv)
	case nil:
		SetScalarNull(parent, last.key)
	default:
		// complex (map/array)
		var oldChild *yaml.Node
		found := false
		for i := 0; i+1 < len(parent.Content); i += 2 {
			if parent.Content[i].Kind == yaml.ScalarNode && parent.Content[i].Value == last.key {
				// Remember previous value before we swap it out
				oldChild = parent.Content[i+1]
				parent.Content[i+1] = yval
				found = true
				break
			}
		}
		if !found {
			return fmt.Errorf("yamledit: replace: key %q not found", last.key)
		}
		if st != nil {
			st.mu.Lock()
			if _, ok := st.subPathByHN[parent]; !ok && docHN != nil {
				indexMappingHandles(st, docHN.Content[0], nil)
			}
			path := st.subPathByHN[parent]
			st.ordered = setAnyAtPath(st.ordered, path, last.key, orderedVal)
			// If we are replacing a sequence (array) value and its "shape" changed,
			// force structured re-encode to avoid byte-surgical scrambling.
			if yval.Kind == yaml.SequenceNode {
				shapeChanged := true // default to conservative
				if oldChild != nil && oldChild.Kind == yaml.SequenceNode {
					// length change → definitely shape change
					if len(oldChild.Content) == len(yval.Content) {
						// Try to compare item identities by their "name" field (if present)
						if oldNames, ok1 := seqItemNames(oldChild); ok1 {
							if newNames, ok2 := seqItemNames(yval); ok2 {
								shapeChanged = false
								for i := range oldNames {
									if oldNames[i] != newNames[i] {
										shapeChanged = true
										break
									}
								}
							}
						}
					}
				}
				if shapeChanged {
					st.arraysDirty = true
				}
			}
			st.mu.Unlock()
		}
	}
	// Ensure the ordered view also reflects scalar updates inside sequence items.
	// This handles cases where 'parent' is a mapping within an array and therefore
	// lacks a handle → path entry in subPathByHN.
	if st != nil {
		st.mu.Lock()
		absTokens := appendPathTokens(baseFromRoot, tokens)
		if nv, err := orderedSetAtPathTokens(st.ordered, absTokens, orderedVal); err == nil {
			st.ordered = nv
		}
		st.mu.Unlock()
	}
	return nil
}

func opMove(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []string, from, to string) error {
	fromToks, err := parseJSONPointer(from)
	if err != nil {
		return err
	}
	toToks, err := parseJSONPointer(to)
	if err != nil {
		return err
	}
	// read value at 'from'
	srcParent, srcLast, err := resolveParent(start, appendPathTokens(baseFromRoot, fromToks), false)
	if err != nil {
		return err
	}
	var src *yaml.Node
	if srcLast.isIdx {
		if srcParent.Kind != yaml.SequenceNode || srcLast.index < 0 || srcLast.index >= len(srcParent.Content) {
			return errors.New("yamledit: move: invalid 'from' index")
		}
		src = srcParent.Content[srcLast.index]
	} else {
		if srcParent.Kind != yaml.MappingNode {
			return errors.New("yamledit: move: invalid 'from' parent")
		}
		for i := 0; i+1 < len(srcParent.Content); i += 2 {
			if srcParent.Content[i].Kind == yaml.ScalarNode && srcParent.Content[i].Value == srcLast.key {
				src = srcParent.Content[i+1]
				break
			}
		}
		if src == nil {
			return fmt.Errorf("yamledit: move: key %q not found", srcLast.key)
		}
	}
	// clone
	cl := *src
	// add to 'to'
	if err := opAdd(start, st, docHN, baseFromRoot, toToks, mustMarshalJSON(yamlNodeToInterface(&cl))); err != nil {
		return err
	}
	// remove from 'from'
	return opRemove(start, st, baseFromRoot, fromToks)
}

func opCopy(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []string, from, to string) error {
	fromToks, err := parseJSONPointer(from)
	if err != nil {
		return err
	}
	toToks, err := parseJSONPointer(to)
	if err != nil {
		return err
	}
	// read value at 'from'
	srcParent, srcLast, err := resolveParent(start, appendPathTokens(baseFromRoot, fromToks), false)
	if err != nil {
		return err
	}
	var src *yaml.Node
	if srcLast.isIdx {
		if srcParent.Kind != yaml.SequenceNode || srcLast.index < 0 || srcLast.index >= len(srcParent.Content) {
			return errors.New("yamledit: copy: invalid 'from' index")
		}
		src = srcParent.Content[srcLast.index]
	} else {
		if srcParent.Kind != yaml.MappingNode {
			return errors.New("yamledit: copy: invalid 'from' parent")
		}
		for i := 0; i+1 < len(srcParent.Content); i += 2 {
			if srcParent.Content[i].Kind == yaml.ScalarNode && srcParent.Content[i].Value == srcLast.key {
				src = srcParent.Content[i+1]
				break
			}
		}
		if src == nil {
			return fmt.Errorf("yamledit: copy: key %q not found", srcLast.key)
		}
	}
	// add to 'to'
	return opAdd(start, st, docHN, baseFromRoot, toToks, mustMarshalJSON(yamlNodeToInterface(src)))
}

func mustMarshalJSON(v interface{}) json.RawMessage {
	b, _ := json.Marshal(v)
	return b
}

func deepEqual(a, b interface{}) bool {
	// simple reflect.DeepEqual would work; keep types aligned by our conversions
	return fmt.Sprintf("%#v", a) == fmt.Sprintf("%#v", b)
}

// --- Ordered updates for arrays (best-effort for fallback encoder) ---

func appendPathTokens(prefix []string, toks []ptrToken) []ptrToken {
	out := make([]ptrToken, 0, len(prefix)+len(toks))
	for _, k := range prefix {
		out = append(out, ptrToken{key: k})
	}
	out = append(out, toks...)
	return out
}

// Walk st.ordered and add into an array location.
func orderedAddArray(ms gyaml.MapSlice, path []ptrToken, val interface{}, appendMode bool) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)
	nv, err := orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		if appendMode {
			return append(cur, ov), nil
		}
		// find index from last token
		last := path[len(path)-1]
		if last.index < 0 || last.index > len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		cur = append(cur, nil)
		copy(cur[last.index+1:], cur[last.index:])
		cur[last.index] = ov
		return cur, nil
	})
	if err != nil {
		return ms, err
	}
	return nv, nil
}

func orderedReplaceArray(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)
	return orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		last := path[len(path)-1]
		if last.index < 0 || last.index >= len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		cur[last.index] = ov
		return cur, nil
	})
}

func orderedRemoveArray(ms gyaml.MapSlice, path []ptrToken) (gyaml.MapSlice, error) {
	return orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		last := path[len(path)-1]
		if last.index < 0 || last.index >= len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		return append(cur[:last.index], cur[last.index+1:]...), nil
	})
}

// orderedArrayEdit navigates to the []interface{} pointed by path (last segment is an index/appender)
// and applies 'edit', returning an updated MapSlice.
func orderedArrayEdit(ms gyaml.MapSlice, path []ptrToken, edit func([]interface{}) ([]interface{}, error)) (gyaml.MapSlice, error) {
	var recur func(cur interface{}, depth int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		if depth >= len(path) {
			return cur, nil
		}
		t := path[depth]
		switch v := cur.(type) {
		case gyaml.MapSlice:
			if t.isIdx {
				return nil, fmt.Errorf("expected key at segment %d", depth)
			}
			// locate key
			found := -1
			for i := range v {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("path key %q not found in ordered map", t.key)
			}
			next, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = next
			return v, nil
		case []interface{}:
			if !t.isIdx {
				return nil, fmt.Errorf("expected index at segment %d", depth)
			}
			if depth == len(path)-1 {
				// apply edit
				return edit(v)
			}
			if t.append {
				return nil, fmt.Errorf("'-' only valid at the last segment")
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("index %d out of bounds", t.index)
			}
			next, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = next
			return v, nil
		default:
			return nil, fmt.Errorf("unexpected type at segment %d", depth)
		}
	}
	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, _ := out.(gyaml.MapSlice)
	return res, nil
}

// orderedSetAtPathTokens sets a scalar value at the path indicated by tokens.
// The final token MUST be a mapping key (not an index). Intermediate segments
// may traverse through arrays (sequence indices) and mappings.
func orderedSetAtPathTokens(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)

	var recur func(cur interface{}, depth int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		if depth >= len(path) {
			return nil, fmt.Errorf("orderedSetAtPath: empty path at depth %d", depth)
		}
		t := path[depth]
		switch v := cur.(type) {
		case gyaml.MapSlice:
			if t.isIdx {
				return nil, fmt.Errorf("orderedSetAtPath: expected key at segment %d", depth)
			}
			// locate key
			found := -1
			for i := range v {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("orderedSetAtPath: path key %q not found", t.key)
			}
			if depth == len(path)-1 {
				// final segment is a key → set its scalar value
				v[found].Value = ov
				return v, nil
			}
			next, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = next
			return v, nil

		case map[string]interface{}:
			// Handle native map as well (can occur inside []interface{}).
			if t.isIdx {
				return nil, fmt.Errorf("orderedSetAtPath: expected key at segment %d", depth)
			}
			child, ok := v[t.key]
			if !ok {
				return nil, fmt.Errorf("orderedSetAtPath: path key %q not found", t.key)
			}
			if depth == len(path)-1 {
				v[t.key] = ov
				return v, nil
			}
			next, err := recur(child, depth+1)
			if err != nil {
				return nil, err
			}
			v[t.key] = next
			return v, nil

		case []interface{}:
			if !t.isIdx {
				return nil, fmt.Errorf("orderedSetAtPath: expected index at segment %d", depth)
			}
			if t.append {
				return nil, fmt.Errorf("orderedSetAtPath: '-' not valid for set")
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("orderedSetAtPath: index %d out of bounds", t.index)
			}
			if depth == len(path)-1 {
				// Not used for this test, but support setting entire element if addressed directly.
				v[t.index] = ov
				return v, nil
			}
			next, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = next
			return v, nil
		default:
			return nil, fmt.Errorf("orderedSetAtPath: unexpected type at segment %d (%T)", depth, v)
		}
	}
	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, _ := out.(gyaml.MapSlice)
	return res, nil
}

// seqItemNames extracts the "name" scalar from each mapping item in a sequence.
// Returns (names, true) only if every item is a mapping and has a string scalar "name".
func seqItemNames(seq *yaml.Node) ([]string, bool) {
	if seq == nil || seq.Kind != yaml.SequenceNode {
		return nil, false
	}
	out := make([]string, len(seq.Content))
	for i, it := range seq.Content {
		if it == nil || it.Kind != yaml.MappingNode {
			return nil, false
		}
		found := false
		for j := 0; j+1 < len(it.Content); j += 2 {
			k := it.Content[j]
			v := it.Content[j+1]
			if k.Kind == yaml.ScalarNode && k.Value == "name" && v.Kind == yaml.ScalarNode {
				out[i] = v.Value
				found = true
				break
			}
		}
		if !found {
			return nil, false
		}
	}
	return out, true
}
