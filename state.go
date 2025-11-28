package yamledit

import (
	"runtime"
	"sync"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// Internal state registered per root yaml.DocumentNode.
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
	// Also stores scalar sequence items keyed by path + [index].
	valueOccByPathKey map[string][]valueOcc

	// Key-Value boundaries for all types (scalar, mapping, sequence) for surgical deletion.
	boundsByPathKey map[string][]kvBounds

	seqIndex map[string]*seqInfo // sequence formatting & anchors by YAML path

	// explicit deletions requested (path\0key)
	toDelete        map[string]struct{}
	arraysDirty     bool // set only when JSON Patch mutates arrays (seq nodes)
	structuralDirty bool // when true, skip surgery and fall back to full encode
}

// Information about a sequence under a mapping path in the original YAML.
type seqItemInfo struct {
	name  string // identity: value of "name" key if mapping, or scalar value itself (for fallback matching)
	start int    // byte offset at the beginning of the item's first line ("- " ...)
	end   int    // byte offset of the newline ending the last line of the item
}

// Boundaries of a "key: value" block for deletion.
type kvBounds struct {
	start int // start offset of the line where the key begins (keyLineStart)
	end   int // exclusive end offset of the block (includes trailing newline if present)
}

type seqInfo struct {
	indent         int // spaces before '-' on the first line of an item
	itemKVIndent   int // spaces for subsequent key lines inside an item
	firstItemStart int // byte offset of the first item's line start
	lastItemEnd    int // byte offset of the newline ending the last item's last line
	hasAnyItem     bool
	originalPath   bool
	firstKeyInline bool          // whether first key (or scalar value) appears on the same line as "- "
	keyOrder       []string      // preferred key order for items (captured from an existing item)
	items          []seqItemInfo // per-item positions and names
	gaps           [][]byte      // raw bytes between items; len = len(items)-1
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

func cloneBoundsIndex(in map[string][]kvBounds) map[string][]kvBounds {
	out := make(map[string][]kvBounds, len(in))
	for k, v := range in {
		cp := make([]kvBounds, len(v))
		copy(cp, v)
		out[k] = cp
	}
	return out
}

// Information about a mapping block in the original YAML.
type mapInfo struct {
	indent       int // indent (in spaces) of keys inside this mapping
	lastLineEnd  int // byte offset of the newline that ends the last key/value line in this mapping
	hasAnyKey    bool
	originalPath bool // mapping existed in the original bytes
}

// One occurrence of "key: value" or "- value" in the original file.
type valueOcc struct {
	keyLineStart int // start offset of the line where the key/item begins
	valStart     int // start offset of the value token
	valEnd       int // end offset (exclusive) of the value token
	lineEnd      int // offset of '\n' ending this line (or len(original)-1 if final line has no \n)
}

// Global registry so we can look up state by *yaml.Node (doc).
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
