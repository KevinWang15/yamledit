package yamledit

import (
	"bytes"
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	gyaml "github.com/goccy/go-yaml"
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

	out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, indent, delSet)
	if okPatch && !structuralDirty {
		if arraysDirty {
			if s, ok := lookup(doc); ok {
				s.mu.Lock()
				s.arraysDirty = false
				s.mu.Unlock()
			}
		}
		return out, nil
	}

	if patched, ok := structuralRewrite(original, ordered, origOrdered, boundsIdx, indent, delSet); ok {
		return patched, nil
	}

	return nil, fmt.Errorf("yamledit: surgical edit unsupported; no safe structural rewrite")
}

// structuralRewrite surgically re-encodes individual key regions using boundsIdx.
func structuralRewrite(original []byte, ordered gyaml.MapSlice, origOrdered gyaml.MapSlice, boundsIdx map[string][]kvBounds, baseIndent int, delSet map[string]struct{}) ([]byte, bool) {
	var patches []patch
	patched := map[string]struct{}{}

	// Deletions: remove key ranges for explicit deletions.
	for pk := range delSet {
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			continue
		}
		b := bounds[len(bounds)-1]
		patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
		patched[pk] = struct{}{}
	}

	changed := collectChangedKeys(origOrdered, ordered, nil)
	for _, pk := range changed {
		if _, skip := patched[pk]; skip {
			continue
		}
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			continue
		}
		path, key := splitPathKey(pk)
		val, ok := orderedValueAt(ordered, path, key)
		if !ok {
			continue
		}
		b := bounds[len(bounds)-1]
		if isSequence(val) {
			seqText, okSeq := renderSequenceValue(original, key, val, b, baseIndent)
			if !okSeq {
				return nil, false
			}
			if bytes.Equal(original[b.start:b.end], []byte(seqText)) {
				continue
			}
			patches = append(patches, patch{start: b.start, end: b.end, data: []byte(seqText)})
			continue
		}

		txt, ok := renderKeyValue(original, key, val, b, baseIndent)
		if !ok {
			continue
		}
		if bytes.Equal(original[b.start:b.end], []byte(txt)) {
			continue
		}
		patches = append(patches, patch{start: b.start, end: b.end, data: []byte(txt)})
	}

	if len(patches) == 0 {
		return nil, false
	}

	sort.SliceStable(patches, func(i, j int) bool {
		if patches[i].start == patches[j].start {
			return patches[i].end < patches[j].end
		}
		return patches[i].start < patches[j].start
	})

	var filtered []patch
	for _, p := range patches {
		if len(filtered) == 0 {
			filtered = append(filtered, p)
			continue
		}
		last := &filtered[len(filtered)-1]
		if p.start < last.end {
			// Overlap: keep earlier (outer) patch, skip this one.
			continue
		}
		filtered = append(filtered, p)
	}

	var buf bytes.Buffer
	cursor := 0
	for _, p := range filtered {
		if p.start < cursor || p.end < p.start || p.end > len(original) {
			return nil, false
		}
		buf.Write(original[cursor:p.start])
		buf.Write(p.data)
		cursor = p.end
	}
	if cursor < len(original) {
		buf.Write(original[cursor:])
	}
	return buf.Bytes(), true
}

func splitPathKey(pk string) ([]string, string) {
	parts := strings.Split(pk, pathSep)
	if len(parts) == 0 {
		return nil, ""
	}
	return parts[:len(parts)-1], parts[len(parts)-1]
}

func orderedValueAt(ms gyaml.MapSlice, path []string, key string) (interface{}, bool) {
	cur := ms
	for _, seg := range path {
		found := false
		for _, it := range cur {
			if keyEquals(it.Key, seg) {
				if sub, ok := it.Value.(gyaml.MapSlice); ok {
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
		if keyEquals(it.Key, key) {
			return it.Value, true
		}
	}
	return nil, false
}

func renderKeyValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int) (string, bool) {
	plain := toPlain(val)

	var tmp bytes.Buffer
	enc := yaml.NewEncoder(&tmp)
	enc.SetIndent(baseIndent)
	if err := enc.Encode(map[string]interface{}{key: plain}); err != nil {
		_ = enc.Close()
		return "", false
	}
	_ = enc.Close()

	lines := strings.Split(strings.TrimRight(tmp.String(), "\n"), "\n")
	indentSpaces := currentIndent(original, b.start)
	prefix := strings.Repeat(" ", indentSpaces)
	comment := inlineComment(original, b.start)

	for i := range lines {
		if i == 0 && comment != "" {
			lines[i] = prefix + lines[i] + " " + comment
		} else {
			lines[i] = prefix + lines[i]
		}
	}
	out := strings.Join(lines, "\n")
	if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
		out += "\n"
	}
	return out, true
}

func currentIndent(original []byte, start int) int {
	i := start
	for i > 0 && original[i-1] != '\n' {
		i--
	}
	end := findLineEnd(original, i)
	if end >= len(original) {
		end = len(original)
	}
	return leadingSpaces(original[i:end])
}

func inlineComment(original []byte, start int) string {
	i := start
	for i > 0 && original[i-1] != '\n' {
		i--
	}
	end := findLineEnd(original, i)
	if end >= len(original) {
		end = len(original) - 1
	}
	line := original[i : end+1]
	if idx := bytes.IndexByte(line, '#'); idx >= 0 {
		return strings.TrimSpace(string(line[idx:]))
	}
	return ""
}

func collectChangedKeys(orig gyaml.MapSlice, cur gyaml.MapSlice, path []string) []string {
	var out []string
	for _, it := range cur {
		k, ok := it.Key.(string)
		if !ok {
			continue
		}
		ov, okOrig := findLast(orig, k)
		cv := it.Value
		diff := !okOrig || !reflect.DeepEqual(toPlain(ov), toPlain(cv))
		if subCur, ok := cv.(gyaml.MapSlice); ok {
			if diff {
				if ovMs, okMs := ov.(gyaml.MapSlice); !okMs || len(subCur) == 0 || len(ovMs) == 0 {
					out = append(out, makePathKey(path, k))
				}
			}
			var subOrig gyaml.MapSlice
			if ovMs, ok := ov.(gyaml.MapSlice); ok {
				subOrig = ovMs
			}
			out = append(out, collectChangedKeys(subOrig, subCur, append(path, k))...)
			continue
		}
		if diff {
			out = append(out, makePathKey(path, k))
		}
	}
	return out
}

func findLast(ms gyaml.MapSlice, key string) (interface{}, bool) {
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, key) {
			return ms[i].Value, true
		}
	}
	return nil, false
}

func isSequence(v interface{}) bool {
	switch v.(type) {
	case []interface{}:
		return true
	default:
		return false
	}
}

func renderSequenceValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int) (string, bool) {
	arr, ok := val.([]interface{})
	if !ok {
		return "", false
	}
	indentSpaces := currentIndent(original, b.start)

	var sb strings.Builder
	sb.WriteString(strings.Repeat(" ", indentSpaces))
	sb.WriteString(key)
	if len(arr) == 0 {
		sb.WriteString(": []")
		if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
			sb.WriteString("\n")
		}
		return sb.String(), true
	}
	sb.WriteString(":\n")
	for _, el := range arr {
		line := renderScalarLine(el)
		sb.WriteString(strings.Repeat(" ", indentSpaces+baseIndent))
		sb.WriteString("- ")
		sb.WriteString(line)
		sb.WriteString("\n")
	}
	// Trim trailing newline if original region had none.
	if b.end <= len(original) && b.end > b.start && original[b.end-1] != '\n' {
		out := sb.String()
		out = strings.TrimSuffix(out, "\n")
		return out, true
	}
	return sb.String(), true
}

func renderScalarLine(v interface{}) string {
	switch t := v.(type) {
	case string:
		if isSafeBareString(t) {
			return t
		}
		return quoteNewStringToken(t)
	case int:
		return fmt.Sprintf("%d", t)
	case float64:
		return strconv.FormatFloat(t, 'g', -1, 64)
	case bool:
		if t {
			return "true"
		}
		return "false"
	default:
		b, err := yaml.Marshal(v)
		if err != nil {
			return fmt.Sprint(v)
		}
		return strings.TrimSpace(string(b))
	}
}
