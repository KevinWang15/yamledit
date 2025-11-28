package yamledit

import (
	"bytes"

	"gopkg.in/yaml.v3"
)

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
	indent := st.indent
	original := st.original
	mapIdx := cloneMapIndex(st.mapIndex)
	valIdx := cloneValueIndex(st.valueOccByPathKey)
	boundsIdx := cloneBoundsIndex(st.boundsByPathKey) // Clone new index
	origOrdered := cloneMapSlice(st.origOrdered)
	delSet := make(map[string]struct{}, len(st.toDelete))
	seqIdx := cloneSeqIndex(st.seqIndex)
	for k := range st.toDelete {
		delSet[k] = struct{}{}
	}
	arraysDirty := st.arraysDirty
	structuralDirty := st.structuralDirty
	st.mu.RUnlock()

	// If we know the structure has changed in ways that byte surgery can't
	// safely represent (e.g. "envs:" -> "envs: {}"), skip surgery and fall
	// back to a full yaml.v3 encode.
	if !structuralDirty {
		// Attempt byte-surgical patching first (even if arraysDirty), with enhanced seq support.
		out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, indent, delSet)
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
	}

	// Fallback: structured encode (still preserves comments/order/indent)
	// Fallback: encode from the yaml.v3 AST to preserve original quoting/comment styles
	var buf bytes.Buffer
	encV3 := yaml.NewEncoder(&buf)
	encV3.SetIndent(indent)
	if err := encV3.Encode(doc); err != nil {
		_ = encV3.Close()
		return nil, err
	}
	_ = encV3.Close()
	return buf.Bytes(), nil
}
