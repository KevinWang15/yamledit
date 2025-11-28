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

	// Attempt byte-surgical patching first (even if arraysDirty), with enhanced seq support.
	if !structuralDirty {
		out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, indent, delSet)
		if okPatch {
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

	// Structured encode fallback (v2: isolated to cases we cannot safely patch)
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
