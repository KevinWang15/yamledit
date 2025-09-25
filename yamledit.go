package yamledit

import (
	"bytes"
	"fmt"
	"runtime"
	"sync"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

type docState struct {
	mu          sync.RWMutex
	doc         *yaml.Node              // back-reference to the root document
	indent      int                     // detected indent (2 or 4 spaces typically)
	indentSeq   bool                    // whether sequences under a key are indented
	ordered     gyaml.MapSlice          // ordered mapping we actually edit
	comments    gyaml.CommentMap        // captured comments
	subPathByHN map[*yaml.Node][]string // mapping-handle -> YAML path segments from root
}

var (
	regMu sync.Mutex
	reg   = map[*yaml.Node]*docState{}
)

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

	// Build shadow state using goccy/go-yaml
	st := &docState{
		doc:         doc,
		comments:    gyaml.CommentMap{},
		ordered:     gyaml.MapSlice{},
		subPathByHN: map[*yaml.Node][]string{},
		indent:      2,
		indentSeq:   true,
	}

	// Decode into ordered map and capture comments
	if len(data) > 0 {
		if err := gyaml.UnmarshalWithOptions(data, &st.ordered, gyaml.UseOrderedMap(), gyaml.CommentToMap(st.comments)); err == nil {
			ind, seq := detectIndentAndSequence(data)
			st.indent, st.indentSeq = ind, seq
		}
	}

	// Index mapping handles
	if doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode {
		st.subPathByHN[doc.Content[0]] = nil
		indexMappingHandles(st, doc.Content[0], nil)
	}

	register(doc, st)
	return doc, nil
}

// Marshal encodes the YAML preserving comments and formatting.
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
	ordered := st.ordered
	comments := st.comments
	indent := st.indent
	indentSeq := st.indentSeq
	st.mu.RUnlock()

	var buf bytes.Buffer
	enc := gyaml.NewEncoder(
		&buf, gyaml.Indent(indent), gyaml.IndentSequence(indentSeq), gyaml.WithComment(comments),
	)
	if err := enc.Encode(ordered); err != nil {
		return nil, err
	}
	_ = enc.Close()

	return buf.Bytes(), nil
}

// EnsurePath returns a mapping node for the nested keys (creates when missing).
func EnsurePath(doc *yaml.Node, first string, rest ...string) *yaml.Node {
	if doc == nil || doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 {
		return nil
	}

	st, _ := lookup(doc)
	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	cur := doc.Content[0]
	keys := append([]string{first}, rest...)

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
	}

	if st != nil {
		st.ordered = ensureOrderedPath(st.ordered, keys...)
		st.subPathByHN[cur] = append([]string(nil), keys...)
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
			break
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

	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}
	st.ordered = setIntAtPath(st.ordered, path, key, value)
}

// Internal helpers

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

func setIntAtPath(ms gyaml.MapSlice, path []string, key string, val int) gyaml.MapSlice {
	if len(path) == 0 {
		for i := range ms {
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
	// no evidence either way: default to indented sequences (common in K8s/Helm repos)
	return indent, true
}

func isBlankOrComment(ln []byte) bool {
	t := bytes.TrimSpace(ln)
	return len(t) == 0 || t[0] == '#'
}

// endsWithMappingKey returns true if the line is a block mapping key of the form "key:" possibly
// followed by spaces and/or a comment.
func endsWithMappingKey(ln []byte) bool {
	// ignore flow/inline cases; we just need the common block "key:" form
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

func leadingSpaces(line []byte) int {
	i := 0
	for i < len(line) && line[i] == ' ' {
		i++
	}
	return i
}
