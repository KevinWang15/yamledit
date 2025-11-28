package yamledit

import (
	"bytes"
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	gyaml "github.com/goccy/go-yaml"
)

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
	boundsIdx map[string][]kvBounds, // NEW argument
	baseIndent int,
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

		// Replace entire sequence blocks when array "shape" changed (remove/add/reorder/value change in scalar array).
		// We pass valIdx to allow microsurgery during block regeneration for scalar arrays.
		seqReplOK, seqReplPatches, replacedSeqs := buildSeqReplaceBlockPatches(original, current, originalOrdered, seqIdx, baseIndent, valIdx)
		if !seqReplOK {
			return nil, false
		}
		for _, p := range seqReplPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 1) Replace ints/strings/bools/floats/null that changed (and existed originally),
		//    including inside arrays of mappings. (Scalar arrays handled above now).
		replaceOK, replPatches := buildReplacementPatches(original, current, originalOrdered, valIdx, seqIdx, replacedSeqs)
		if !replaceOK {
			return nil, false
		}
		for _, p := range replPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 2) Remove duplicates in original (keep LAST occurrence), but ignore keys marked for deletion
		// MODIFIED: Use boundsIdx instead of valIdx
		dupPatchesOK, dupPatches := buildDuplicateRemovalPatches(original, boundsIdx, deletions, replacedSeqs)
		if !dupPatchesOK {
			return nil, false
		}
		for _, p := range dupPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 3) Insert NEW keys (ints/strings) where safe
		insertOK, insertPatches := buildInsertPatches(original, current, originalOrdered, mutableMI, baseIndent)
		if !insertOK {
			return nil, false
		}
		for _, p := range insertPatches {
			p.seq = seq
			seq++
			patches = append(patches, p)
		}

		// 3b) Append NEW items to sequences (arrays) at the end (safe styles only).
		//     Skip sequences we fully replaced above. (This is now redundant if buildSeqReplaceBlockPatches handles appends).
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
		// MODIFIED: Use boundsIdx instead of valIdx
		delOK, delPatches := buildDeletionPatches(original, deletions, boundsIdx)
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
			// Check for valid range, allowing insertion at the end (p.start == len(original))
			if !(p.start == len(original) && p.end == len(original) && p.start >= cursor) {
				return nil, false
			}
		}
		if p.start > len(original) {
			// Should have been caught above
			return nil, false
		}

		out.Write(original[cursor:p.start])
		out.Write(p.data)
		cursor = p.end
	}
	if cursor < len(original) {
		out.Write(original[cursor:])
	}
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

		// Helper to render one "key: value" pair, handling nested scalar lists.
		writeField := func(indent int, key string, v interface{}) {
			switch vv := v.(type) {
			case []interface{}:
				// Treat as a block-style sequence if all elements are simple scalars.
				allScalar := true
				for _, e := range vv {
					if !isScalarValue(e) {
						allScalar = false
						break
					}
				}
				if allScalar {
					sb.WriteString(strings.Repeat(" ", indent))
					sb.WriteString(key)
					sb.WriteString(":\n")
					for _, e := range vv {
						sb.WriteString(strings.Repeat(" ", indent+baseIndent))
						sb.WriteString("- ")
						sb.WriteString(renderScalar(e))
						sb.WriteString("\n")
					}
					return
				}
				// Fall back to scalar-style rendering for complex sequences.
				sb.WriteString(strings.Repeat(" ", indent))
				sb.WriteString(key)
				sb.WriteString(": ")
				sb.WriteString(renderScalar(v))
				sb.WriteString("\n")
			default:
				sb.WriteString(strings.Repeat(" ", indent))
				sb.WriteString(key)
				sb.WriteString(": ")
				sb.WriteString(renderScalar(v))
				sb.WriteString("\n")
			}
		}

		first := order[0]
		fv, ok := vals[first]
		if !ok {
			return "", false
		}

		if si.firstKeyInline && isScalarValue(fv) {
			// Standard inline form: "- key: value"
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("- ")
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		} else {
			// Either originally non-inline, or first value is now complex (e.g. a nested list).
			// Render as:
			//   -
			//     key: ...
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("-\n")
			writeField(kvIndent, first, fv)
		}

		for i := 1; i < len(order); i++ {
			k := order[i]
			v, ok := vals[k]
			if !ok {
				continue
			}
			writeField(kvIndent, k, v)
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
					// This is a brand-new sequence (no original anchor). We don't try
					// to surgically append into it here; insertion of the entire key
					// will be handled (or not) by buildInsertPatches.
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
func buildReplacementPatches(
	original []byte,
	current gyaml.MapSlice,
	originalOrdered gyaml.MapSlice,
	valIdx map[string][]valueOcc,
	seqIdx map[string]*seqInfo,
	skipSeq map[string]struct{},
) (bool, []patch) {
	// Helper: get original string value for (path, key) from originalOrdered.
	// path is a slice of mapping keys and possibly "[idx]" segments for array items.
	isIndexSeg := func(s string) bool {
		return len(s) > 2 && s[0] == '[' && s[len(s)-1] == ']'
	}

	lookupOrigString := func(path []string, key string) (string, bool) {
		var recur func(cur interface{}, depth int) (interface{}, bool)
		recur = func(cur interface{}, depth int) (interface{}, bool) {
			if depth == len(path) {
				switch m := cur.(type) {
				case gyaml.MapSlice:
					for i := len(m) - 1; i >= 0; i-- {
						if keyEquals(m[i].Key, key) {
							return m[i].Value, true
						}
					}
				case map[string]interface{}:
					if v, ok := m[key]; ok {
						return v, true
					}
				}
				return nil, false
			}

			seg := path[depth]
			if isIndexSeg(seg) {
				// "[N]" → array index
				idxStr := seg[1 : len(seg)-1]
				idx, err := strconv.Atoi(idxStr)
				if err != nil {
					return nil, false
				}
				switch arr := cur.(type) {
				case []interface{}:
					if idx < 0 || idx >= len(arr) {
						return nil, false
					}
					return recur(arr[idx], depth+1)
				default:
					return nil, false
				}
			}

			// mapping segment
			switch m := cur.(type) {
			case gyaml.MapSlice:
				for _, it := range m {
					if keyEquals(it.Key, seg) {
						return recur(it.Value, depth+1)
					}
				}
			case map[string]interface{}:
				if v, ok := m[seg]; ok {
					return recur(v, depth+1)
				}
			}
			return nil, false
		}

		if v, ok := recur(originalOrdered, 0); ok {
			if s, ok2 := v.(string); ok2 {
				return s, true
			}
		}
		return "", false
	}

	var patches []patch

	// For sequence items, coalesce multiple scalar changes down to ONE patch,
	// chosen deterministically by the original key order captured in seqIdx.
	type keyPatch struct {
		key   string
		patch patch
	}
	perItem := map[string][]keyPatch{} // itemPath ("a\0b\0[1]") -> changed keys/patches

	isIndexSeg = func(s string) bool {
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

				// --- Block scalar handling (| / >) ---
				// If the scalar is represented in the YAML as a block scalar, we treat the
				// whole block as opaque for surgery:
				//   • If the logical value hasn't changed, leave bytes exactly as-is.
				//   • If the value DID change, we cannot safely patch → abort surgery
				//     and let Marshal() fall back to structured encode.
				if len(oldTok) > 0 && (oldTok[0] == '|' || oldTok[0] == '>') {
					if orig, ok := lookupOrigString(path, k); ok && orig == v {
						// Value is identical → keep block scalar bytes untouched.
						continue
					}
					// Underlying value changed for a block scalar (or we couldn't
					// find the original value). We can't do safe byte-surgery here.
					return false
				}

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
func buildDuplicateRemovalPatches(original []byte, boundsIdx map[string][]kvBounds, ignore map[string]struct{}, skipSeq map[string]struct{}) (bool, []patch) {
	var patches []patch
	// For each path+key that had duplicates originally, remove all but the last occurrence
outer:
	for pk, boundsList := range boundsIdx {
		if _, skip := ignore[pk]; skip {
			continue
		}
		// Skip any pk under a replaced sequence (prefix: "<seqPath>\x00[")
		// This applies to duplicates inside array items (which are indexed this way).
		for sp := range skipSeq {
			prefix := sp + pathSep + "["
			if strings.HasPrefix(pk, prefix) {
				continue outer
			}
		}
		if len(boundsList) <= 1 {
			continue
		}
		// Remove all but the last occurrence (which is the semantically winning one)
		for i := 0; i < len(boundsList)-1; i++ {
			b := boundsList[i]

			// Sanity check boundaries
			if b.start < 0 || b.end > len(original) || b.end < b.start {
				// Invalid bounds recorded, cannot perform surgery safely.
				return false, nil
			}

			// Delete the whole structure defined by the bounds
			patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
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
	valIdx map[string][]valueOcc, // Added valIdx for hybrid surgery
) (bool, []patch, map[string]struct{}) {
	var patches []patch
	replaced := map[string]struct{}{}

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
	// Helper to convert scalar interface{} to string for identity matching.
	// Must be consistent with how yaml.v3 parses values into Node.Value during indexing.
	scalarToString := func(v interface{}) (string, bool) {
		switch vv := v.(type) {
		case string:
			return vv, true
		case int:
			return strconv.Itoa(vv), true
		case int64:
			return strconv.FormatInt(vv, 10), true
		case float64:
			return strconv.FormatFloat(vv, 'g', -1, 64), true
		case bool:
			return strconv.FormatBool(vv), true
		case nil:
			// YAML null can be represented as "null" or "~" or empty. We use "null" for canonical identity.
			return "null", true
		default:
			return "", false
		}
	}

	// Extracts identity ("name" field or scalar value) from array items.
	namesOf := func(arr []interface{}) ([]string, bool) {
		out := make([]string, len(arr))
		for i, el := range arr {
			switch it := el.(type) {
			case gyaml.MapSlice:
				found := false
				for _, kv := range it {
					if ks, ok := kv.Key.(string); ok && ks == "name" {
						// Use scalarToString for consistency
						if sv, ok2 := scalarToString(kv.Value); ok2 {
							out[i] = sv
							found = true
							break
						}
					}
				}
				if !found {
					// If we cannot establish identity for a mapping item (e.g. no "name" field or "name" is complex), bail out.
					return nil, false
				}
			case map[string]interface{}:
				if v, ok := it["name"]; ok {
					if sv, ok2 := scalarToString(v); ok2 {
						out[i] = sv
					} else {
						return nil, false
					}
				} else {
					return nil, false
				}
			// Handle scalars
			default:
				if sv, ok := scalarToString(it); ok {
					out[i] = sv
				} else {
					// Complex type (e.g. nested array) or unknown type.
					return nil, false
				}
			}
		}
		return out, true
	}

	getName := func(ms gyaml.MapSlice) string {
		for _, it := range ms {
			if ks, ok := it.Key.(string); ok && ks == "name" {
				if sv, ok2 := scalarToString(it.Value); ok2 {
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

		writeField := func(indent int, key string, v interface{}) {
			switch vv := v.(type) {
			case []interface{}:
				// Render nested scalar lists in block style:
				//   key:
				//     - ...
				allScalar := true
				for _, e := range vv {
					if !isScalarValue(e) {
						allScalar = false
						break
					}
				}
				if allScalar {
					sb.WriteString(strings.Repeat(" ", indent))
					sb.WriteString(key)
					sb.WriteString(":\n")
					for _, e := range vv {
						sb.WriteString(strings.Repeat(" ", indent+baseIndent))
						sb.WriteString("- ")
						sb.WriteString(renderScalar(e))
						sb.WriteString("\n")
					}
					return
				}
				// Fallback for complex sequences (rare in current use cases).
				sb.WriteString(strings.Repeat(" ", indent))
				sb.WriteString(key)
				sb.WriteString(": ")
				sb.WriteString(renderScalar(v))
				sb.WriteString("\n")
			default:
				sb.WriteString(strings.Repeat(" ", indent))
				sb.WriteString(key)
				sb.WriteString(": ")
				sb.WriteString(renderScalar(v))
				sb.WriteString("\n")
			}
		}

		first := order[0]
		fv, ok := vals[first]
		if !ok {
			return "", false
		}

		if si.firstKeyInline && isScalarValue(fv) {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("- ")
			sb.WriteString(first)
			sb.WriteString(": ")
			sb.WriteString(renderScalar(fv))
			sb.WriteString("\n")
		} else {
			sb.WriteString(strings.Repeat(" ", si.indent))
			sb.WriteString("-\n")
			writeField(kvIndent, first, fv)
		}

		for i := 1; i < len(order); i++ {
			k := order[i]
			v, ok := vals[k]
			if !ok {
				continue
			}
			writeField(kvIndent, k, v)
		}

		return sb.String(), true
	}

	// shapeChanged reports whether the "shape" of a sequence is different:
	//   • length change
	//   • identity / order change when we can derive stable identities
	//   • deep value change as a final fallback.
	//
	// Previously, when namesOf() couldn't derive stable identities
	// (e.g. sequences of mappings without a "name" field like:
	//
	//   routes:
	//     - host: app.example.com
	//       paths:
	//         - /
	//
	// ), we conservatively returned true and rewrote the entire block.
	// The re-rendering path only understood scalar values, so nested
	// lists like "paths" were flattened into flow-style strings:
	//   paths: '[/]'
	//
	// By falling back to a deep logical comparison when we *don't*
	// have identities, we avoid touching sequences whose contents
	// haven't actually changed, so their original YAML (including
	// nested lists) is preserved byte-for-byte.
	shapeChanged := func(oldArr, newArr []interface{}) bool {
		if len(oldArr) != len(newArr) {
			return true
		}

		// Fast path: if we can derive stable identities for items,
		// use those to detect reordering / additions / deletions.
		if oldNames, ok1 := namesOf(oldArr); ok1 {
			if newNames, ok2 := namesOf(newArr); ok2 {
				if len(oldNames) != len(newNames) {
					return true
				}
				for i := range oldNames {
					if oldNames[i] != newNames[i] {
						return true
					}
				}
				// Same identities in the same order ⇒ no shape change.
				// Any scalar field edits are handled by buildReplacementPatches.
				return false
			}
		}

		// Fallback: we don't have stable identities (e.g. routes without "name").
		// Compare the logical contents; if they are identical, we MUST NOT
		// rewrite the block, or we risk corrupting nested structures like
		// "paths" lists.
		return !reflect.DeepEqual(toPlain(oldArr), toPlain(newArr))
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
					// New array; cannot perform surgical block replace as we don't have anchors.
					continue
				}
				mpath := joinPath(append(path, k))
				si := seqIdx[mpath]
				// Ensure we have valid anchors from the original parse.
				if si == nil || !si.originalPath || !si.hasAnyItem || si.firstItemStart < 0 || si.lastItemEnd < 0 {
					continue
				}

				// Check if the structure or order changed.
				// We also treat value changes in scalar arrays as "shape change" here (since value is identity) to trigger hybrid surgery.
				if !shapeChanged(origArr, v) {
					// If shape (identities/order) didn't change, rely on buildReplacementPatches for mapping updates.
					// For scalars, if shape didn't change, values (identities) are the same, so nothing to do.
					continue
				}

				// If we are here, the array changed (length, order, or content/identity).

				// --- Block Replacement Logic (Hybrid Approach) ---
				O := len(origArr)
				seqPath := append(append([]string{}, path...), k)

				// Build map of original item info by identity for preservation logic.
				type origItemContext struct {
					index int
					info  seqItemInfo
					data  interface{} // The logical data (gyaml.MapSlice or scalar)
				}
				// Store a list of contexts for each identity to handle potential duplicates.
				origItemsByIdentity := make(map[string][]origItemContext)

				// Populate the map, ensuring we have the necessary info from seqInfo (si).
				// We rely on si.items having the correct length and names captured during indexing.
				if len(si.items) == O {
					for i := 0; i < O; i++ {
						identity := si.items[i].name
						if identity != "" {
							ctx := origItemContext{index: i, info: si.items[i], data: origArr[i]}
							origItemsByIdentity[identity] = append(origItemsByIdentity[identity], ctx)
						}
					}
				}

				// Build "pre-gap" map for fallback rendering if surgery isn't possible for an item.
				preGap := map[string][]byte{}
				if len(si.items) >= 2 && len(si.gaps) == len(si.items)-1 {
					for i := 0; i < len(si.items)-1; i++ {
						nextName := si.items[i+1].name
						if nextName == "" {
							continue
						}
						g := si.gaps[i]
						if len(g) > 0 {
							// Associate gap with the identity of the item that followed it.
							if _, exists := preGap[nextName]; !exists {
								preGap[nextName] = g
							}
						}
					}
				}

				// Helper for fallback identity extraction
				getItemIdentity := func(item interface{}) string {
					if ms, ok := toMapSlice(item); ok {
						return getName(ms)
					}
					if sv, ok := scalarToString(item); ok {
						return sv
					}
					return ""
				}

				// Render new block
				var sb strings.Builder
				// Keep track of used original items by index.
				usedOriginalItems := make(map[int]bool)

				for i, el := range v {

					// Preservation Logic for Existing, Unchanged Items (Identity-Based).
					// If an item existed and hasn't changed content, reuse its original bytes to prevent churn.
					identity := getItemIdentity(el)
					if identity != "" {
						// Check if there are available original occurrences for this identity.
						if contexts, found := origItemsByIdentity[identity]; found && len(contexts) > 0 {
							// Try to find an unused context that matches the content.
							foundMatch := false
							for _, ctx := range contexts {
								if !usedOriginalItems[ctx.index] {
									// Check if the logical content is identical (order-independent for maps).
									if reflect.DeepEqual(toPlain(ctx.data), toPlain(el)) {
										// Found an unused, identical original item. Reuse original bytes.

										// 1. Preserve preceding Gap using preGap map.
										// preGap stores the gap for the first occurrence of an identity.
										if g, ok := preGap[identity]; ok && len(g) > 0 {
											sb.Write(g)
											// Consume gap if used (only once per identity).
											delete(preGap, identity)
										}

										// 2. Write the original item bytes.
										start := ctx.info.start
										// ctx.info.end points to the newline char or EOF-1. Add 1 to include it.
										end := ctx.info.end + 1
										if end > len(original) {
											end = len(original)
										}

										// Boundary checks
										if start >= 0 && end >= start && end <= len(original) {
											sb.Write(original[start:end])
											usedOriginalItems[ctx.index] = true
											foundMatch = true
											break // Found a match, move to the next item in the new array.
										}
									}
								}
							}
							if foundMatch {
								continue // Done: preserved original bytes.
							}
						}
					}
					// END NEW Preservation Logic.

					// NEW: For *appended* items (indexes >= original length), make sure
					// they start on a fresh line. Some preserved items' spans may not
					// include a trailing newline, which would otherwise cause the next
					// "- path: ..." to be glued onto the last line.
					if i >= O && sb.Len() > 0 {
						s := sb.String()
						if len(s) > 0 && s[len(s)-1] != '\n' {
							sb.WriteByte('\n')
						}
					}

					// --- Hybrid Surgical Replacement (Index Alignment) ---
					// Try surgical replacement if the index existed originally AND the item is still a scalar.
					if i < O && i < len(si.items) {
						// Check if the new item is a scalar.
						isScalar := false
						switch el.(type) {
						case string, int, int64, float64, bool, nil:
							isScalar = true
						}

						if isScalar {
							// Check if we have index information for a scalar at this position (indexed by indexScalarSeqPositions).
							pk := makeSeqItemPathKey(seqPath, i)
							occs := valIdx[pk]

							if len(occs) > 0 {
								last := occs[len(occs)-1]
								itemInfo := si.items[i]

								// Perform surgical replacement.
								start := itemInfo.start
								valStart := last.valStart
								valEnd := last.valEnd
								// itemInfo.end points to the newline char or EOF-1. Add 1 to include it.
								end := itemInfo.end + 1
								if end > len(original) {
									end = len(original)
								}

								// Boundary checks
								if start >= 0 && valStart >= start && valEnd >= valStart && end >= valEnd && end <= len(original) {

									// 1. Preserve Gap at this index position (from original gaps).
									if i > 0 && i-1 < len(si.gaps) {
										if gap := si.gaps[i-1]; len(gap) > 0 {
											sb.Write(gap)
										}
									}

									// 2. Write prefix (indent, "- ")
									sb.Write(original[start:valStart])

									// 3. Write new value.
									oldTok := bytes.TrimSpace(original[valStart:valEnd])
									var newValBytes []byte

									if sval, ok := el.(string); ok {
										// Respect original quoting style if possible.
										newValBytes = stringReplacementToken(oldTok, sval)
									} else {
										// Use canonical rendering for non-strings.
										newValBytes = []byte(renderScalar(el))
									}
									sb.Write(newValBytes)

									// 4. Write suffix (whitespace, inline comment, newline)
									sb.Write(original[valEnd:end])
									continue // Done surgically
								}
							}
						}
					}
					// --------------------------------------------------------------------

					// Fallback rendering (for appends, mappings, or when surgery failed/not applicable).

					// Try to preserve gaps using the identity-based preGap map (useful if reordering occurred).
					nm := getItemIdentity(el)
					if nm != "" {
						if g, ok := preGap[nm]; ok && len(g) > 0 {
							sb.Write(g)
							// Consume gap if used.
							delete(preGap, nm)
						}
					}

					// Re-render the item.
					if msItem, okMap := toMapSlice(el); okMap {
						// Render mapping item
						txt, ok := renderItem(si, msItem)
						if !ok {
							return false
						}
						sb.WriteString(txt)
					} else {
						// Render scalar item (Fallback rendering)
						sb.WriteString(strings.Repeat(" ", si.indent))
						sb.WriteString("- ")
						sb.WriteString(renderScalar(el))
						sb.WriteString("\n")
					}
				} // end loop

				start := si.firstItemStart
				end := si.lastItemEnd + 1 // include trailing newline (or extends to EOF)

				if start < 0 || end < start {
					return false
				}
				if end > len(original) {
					end = len(original)
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

	// Walk current and insert new scalars at the end of their mapping
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
					// If the anchor line had no trailing newline (EOF case), ensure the new key
					// starts on a new line. NOTE: we *do not* update mi.lastLineEnd here; all
					// insert positions are expressed in the original coordinate space.
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
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
					if mi.lastLineEnd >= 0 {
						if mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n' {
							line = "\n" + line
						}
					}
					patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(line)})
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
				}
			case []interface{}:
				// New sequence key?
				if _, existed := origKeys[mpath][k]; existed {
					// If the key already existed in the original, we don't handle
					// it as a "new key" insertion. Apps/changes to its items are
					// handled via the sequence surgery helpers.
					continue
				}

				mi := mapIdx[mpath]
				if mi == nil || !mi.originalPath || !mi.hasAnyKey {
					// No stable anchor inside this mapping to attach the new block.
					// We can't safely insert bytes here → bail out to fallback.
					return false
				}

				// Compute indent for the key line
				indent := mi.indent
				if indent == 0 && len(path) > 0 {
					indent = baseIndent * len(path)
				}

				var sb strings.Builder

				// Key line: "  externalSecretEnvs:\n"
				sb.WriteString(strings.Repeat(" ", indent))
				sb.WriteString(k)
				sb.WriteString(":\n")

				// Indentation for "- ..." lines and nested keys.
				// We can use the library-wide baseIndent as the step.
				seqIndent := indent + baseIndent       // for "- ..."
				itemKVIndent := seqIndent + baseIndent // for "name:", "path:", ...

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

				for _, el := range v {
					switch item := el.(type) {
					case gyaml.MapSlice:
						if len(item) == 0 {
							// "- {}" style (unlikely here, but safe)
							sb.WriteString(strings.Repeat(" ", seqIndent))
							sb.WriteString("- {}\n")
							continue
						}

						// Inline the first field: "- name: S"
						firstKey := ""
						firstVal := interface{}(nil)
						for _, kv := range item {
							if ks, ok := kv.Key.(string); ok {
								firstKey = ks
								firstVal = kv.Value
								break
							}
						}
						if firstKey == "" {
							// fallback: scalar-ish toString
							sb.WriteString(strings.Repeat(" ", seqIndent))
							sb.WriteString("- ")
							sb.WriteString(renderScalar(item))
							sb.WriteString("\n")
							continue
						}

						sb.WriteString(strings.Repeat(" ", seqIndent))
						sb.WriteString("- ")
						sb.WriteString(firstKey)
						sb.WriteString(": ")
						sb.WriteString(renderScalar(firstVal))
						sb.WriteString("\n")

						// Remaining fields on their own lines
						for _, kv := range item {
							ks, ok := kv.Key.(string)
							if !ok || ks == firstKey {
								continue
							}
							sb.WriteString(strings.Repeat(" ", itemKVIndent))
							sb.WriteString(ks)
							sb.WriteString(": ")
							sb.WriteString(renderScalar(kv.Value))
							sb.WriteString("\n")
						}

					default:
						// Scalar array item: "- 8080", "- 'foo'" etc.
						sb.WriteString(strings.Repeat(" ", seqIndent))
						sb.WriteString("- ")
						sb.WriteString(renderScalar(el))
						sb.WriteString("\n")
					}
				}

				insertPos := mi.lastLineEnd + 1
				if insertPos < 0 || insertPos > len(original) {
					return false
				}

				// If the last key had no trailing newline, make sure we start on a new line.
				line := sb.String()
				if mi.lastLineEnd >= 0 && (mi.lastLineEnd >= len(original) || original[mi.lastLineEnd] != '\n') {
					line = "\n" + line
				}

				patches = append(patches, patch{
					start: insertPos,
					end:   insertPos,
					data:  []byte(line),
				})

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

// explicit deletion patches for requested keys (remove whole lines/blocks for ALL occurrences)
func buildDeletionPatches(original []byte, deletions map[string]struct{}, boundsIdx map[string][]kvBounds) (bool, []patch) {
	if len(deletions) == 0 {
		return true, nil
	}
	var patches []patch
	for pk := range deletions {
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			// Key didn’t exist in original → no surgical deletion to make.
			// Not an error: fallback encoder will already have removed from the logical map.
			continue
		}
		for _, b := range bounds {
			// Sanity check boundaries.
			if b.start < 0 || b.end > len(original) || b.end < b.start {
				// Invalid boundary indexed, potentially unsafe surgery. Fallback.
				return false, nil
			}
			// The kvBounds struct already defines the exact start and exclusive end of the block.
			patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
		}
	}
	return true, patches
}

// ----- Small utilities for indices and scanning -----
