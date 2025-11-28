package yamledit

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"sort"
	"strconv"
	"strings"

	jsonpatch "github.com/evanphx/json-patch/v5"
	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

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
		// order is not guaranteed in JSON; create a stable MapSlice (sorted keys)
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)

		ms := gyaml.MapSlice{}
		for _, k := range keys {
			ms = append(ms, gyaml.MapItem{Key: k, Value: jsonValueToOrdered(t[k])})
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
				old := parent.Content[i+1]
				parent.Content[i+1] = yval
				// If we replaced a scalar with a complex value, move its inline comment onto the key line
				if old != nil && old.Kind == yaml.ScalarNode && (yval.Kind == yaml.MappingNode || yval.Kind == yaml.SequenceNode) {
					if c := strings.TrimSpace(old.LineComment); c != "" {
						if parent.Content[i].LineComment == "" {
							parent.Content[i].LineComment = old.LineComment
						}
						old.LineComment = ""
					}
				}
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
				// If old value was scalar and new is complex, keep the inline comment on the *key* line
				if oldChild != nil && oldChild.Kind == yaml.ScalarNode && (yval.Kind == yaml.MappingNode || yval.Kind == yaml.SequenceNode) {
					if c := strings.TrimSpace(oldChild.LineComment); c != "" {
						if parent.Content[i].LineComment == "" {
							parent.Content[i].LineComment = oldChild.LineComment
						}
						oldChild.LineComment = ""
					}
				}
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
	// This function is used by opReplace (in the original file) to check shape change for mapping arrays.
	// We keep its original behavior (only checks mappings) as the new hybrid surgery logic handles scalars separately.
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
