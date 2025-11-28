package yamledit

import (
	"fmt"
	"strconv"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

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
		var keyNode *yaml.Node
		for i := 0; i+1 < len(cur.Content); i += 2 {
			if cur.Content[i].Kind == yaml.ScalarNode && cur.Content[i].Value == k {
				keyNode = cur.Content[i]
				found = cur.Content[i+1]
				break
			}
		}

		if found == nil {
			key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}
			val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			cur.Content = append(cur.Content, key, val)
			keyNode = key
			found = val
		}
		if found.Kind != yaml.MappingNode {
			// Preserve comments, but keep the old inline comment on the *key* line
			oldHead, oldLine, oldFoot, oldAnchor := found.HeadComment, found.LineComment, found.FootComment, found.Anchor
			repl := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			repl.HeadComment, repl.FootComment, repl.Anchor = oldHead, oldFoot, oldAnchor
			// Clear the inline comment on the value; attach to key instead
			if keyNode != nil && oldLine != "" {
				// Only assign if the key doesn't already have an inline comment
				if keyNode.LineComment == "" {
					keyNode.LineComment = oldLine
				}
			}
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

// stateForMapNode finds the docState and owning document for a mapping node.
func stateForMapNode(mapNode *yaml.Node) (*docState, *yaml.Node) {
	if mapNode == nil {
		return nil, nil
	}
	if st, doc, _, ok := findOwnerByMapNode(mapNode); ok {
		return st, doc
	}
	regMu.Lock()
	defer regMu.Unlock()
	for doc, st := range reg {
		if len(doc.Content) > 0 && doc.Content[0] == mapNode {
			return st, doc
		}
	}
	return nil, nil
}

// setScalarNode updates a scalar node while preserving existing comments.
func setScalarNode(n *yaml.Node, tag, val string) {
	head, line, foot := n.HeadComment, n.LineComment, n.FootComment
	n.Kind = yaml.ScalarNode
	n.Tag = tag
	n.Value = val
	n.HeadComment, n.LineComment, n.FootComment = head, line, foot
}

// upsertScalarKey rewrites existing scalar values for key (all occurrences) or appends a new pair.
func upsertScalarKey(mapNode *yaml.Node, key, tag, val string) {
	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if k.Kind == yaml.ScalarNode && k.Value == key {
			setScalarNode(mapNode.Content[i+1], tag, val)
			updated = true
		}
	}
	if updated {
		return
	}
	keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
	valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: val}
	mapNode.Content = append(mapNode.Content, keyNode, valNode)
}

// setScalarValue centralizes scalar writes, keeping docState/ordered map in sync.
func setScalarValue(
	mapNode *yaml.Node,
	key string,
	tag string,
	val string,
	updateOrdered func(ms gyaml.MapSlice, path []string, key string) gyaml.MapSlice,
) {
	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	st, docHN := stateForMapNode(mapNode)
	if st != nil {
		st.mu.Lock()
		defer st.mu.Unlock()
	}

	upsertScalarKey(mapNode, key, tag, val)

	if st == nil {
		return
	}

	if _, ok := st.subPathByHN[mapNode]; !ok && docHN != nil && len(docHN.Content) > 0 {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	path, ok := st.subPathByHN[mapNode]
	if !ok {
		return
	}

	st.ordered = updateOrdered(st.ordered, path, key)
	delete(st.toDelete, makePathKey(path, key))
}

// SetScalarInt sets an integer value under the mapping node.
func SetScalarInt(mapNode *yaml.Node, key string, value int) {
	valStr := fmt.Sprintf("%d", value)
	setScalarValue(mapNode, key, "!!int", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setIntAtPath(ms, path, k, value)
	})
}

// SetScalarString sets a string value under the mapping node.
func SetScalarString(mapNode *yaml.Node, key, value string) {
	setScalarValue(mapNode, key, "!!str", value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setStringAtPath(ms, path, k, value)
	})
}

// SetScalarBool sets a boolean value under the mapping node.
// Byte-surgical replacement writes canonical YAML booleans ("true"/"false").
func SetScalarBool(mapNode *yaml.Node, key string, value bool) {
	valStr := "false"
	if value {
		valStr = "true"
	}

	setScalarValue(mapNode, key, "!!bool", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setBoolAtPath(ms, path, k, value)
	})
}

// SetScalarFloat sets a float value under the mapping node.
func SetScalarFloat(mapNode *yaml.Node, key string, value float64) {
	valStr := strconv.FormatFloat(value, 'g', -1, 64)
	setScalarValue(mapNode, key, "!!float", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setFloatAtPath(ms, path, k, value)
	})
}

// SetScalarNull sets a null value (!!null) under the mapping node.
func SetScalarNull(mapNode *yaml.Node, key string) {
	setScalarValue(mapNode, key, "!!null", "null", func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setNullAtPath(ms, path, k)
	})
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

	if len(mapNode.Content) == 0 {
		st.structuralDirty = true
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

// Ordered-map helpers shared by the setter helpers.
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
