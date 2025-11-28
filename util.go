package yamledit

import (
	"bytes"
	"fmt"
	"strings"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

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

// makeSeqItemPathKey builds the index key for a scalar item at a sequence index.
// Format: path\x00[idx]
func makeSeqItemPathKey(path []string, idx int) string {
	segs := make([]string, 0, len(path)+1)
	segs = append(segs, path...)
	segs = append(segs, fmt.Sprintf("[%d]", idx))
	return strings.Join(segs, pathSep)
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
	// Determine line end (inclusive index: '\n' or len(b)-1)
	le := findLineEnd(b, pos)

	// Calculate exclusive end of line content (scanLimit).
	// If le points to '\n', scanLimit is le.
	// If le points to last char (EOF), scanLimit is le + 1 (len(b)).

	// Since pos < len(b), we know len(b) > 0 and le is a valid index.

	scanLimit := le
	// If the character at le is NOT '\n', it must be the EOF case (last char).
	if b[le] != '\n' {
		scanLimit = le + 1
	}

	// If quoted
	if b[i] == '\'' {
		i++ // after opening '
		// Use scanLimit (exclusive)
		for i < scanLimit {
			if b[i] == '\'' {
				// YAML single quotes escape as ''
				if i+1 < scanLimit && b[i+1] == '\'' {
					i += 2
					continue
				}
				return i + 1 // include closing quote
			}
			i++
		}
		return scanLimit // Unterminated quote ends at end of line.
	}
	if b[i] == '"' {
		i++ // after opening "
		esc := false
		for i < scanLimit {
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
		return scanLimit
	}

	// Bare token: read until comment or newline (scanLimit)
	j := pos
	for j < scanLimit {
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
			// key was removed entirely; we don't treat that as a shape change here
			// because DeleteKey is handled surgically via boundsByPathKey.
			continue
		}

		// Mapping vs non-mapping transitions (scalar -> map, map -> scalar)
		if oMap, okMap := ov.(gyaml.MapSlice); okMap {
			cMap, cOk := cv.(gyaml.MapSlice)
			if !cOk {
				return true
			}
			if len(oMap) > 0 && len(cMap) > 0 {
				if hasShapeChange(oMap, cMap) {
					return true
				}
			}
			continue
		} else if _, cIsMap := cv.(gyaml.MapSlice); cIsMap {
			// scalar/sequence -> map
			return true
		}

		// Sequence transitions
		oSlice, oIsSlice := ov.([]interface{})
		cSlice, cIsSlice := cv.([]interface{})
		if oIsSlice && cIsSlice {
			// We treat "non-empty -> empty" as a structural change; this is
			// what drives fallback for cases like deleting all array items and
			// wanting "externalSecretEnvs: []".
			if len(oSlice) > 0 && len(cSlice) == 0 {
				return true
			}
			continue
		}
		if oIsSlice != cIsSlice {
			return true
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

// isScalarValue reports whether v is a "simple" scalar that we can safely render
// with renderScalar (i.e. not a nested list/map).
func isScalarValue(v interface{}) bool {
	switch v.(type) {
	case int, int64, float64, bool, string, nil:
		return true
	default:
		return false
	}
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
// maxLineEndForNode returns the maximum line-end offset (index of '\n' or len-1)
// for the given node and all of its descendants, based on yaml.v3 position info.
func maxLineEndForNode(st *docState, n *yaml.Node) int {
	if n == nil {
		return 0
	}
	maxEnd := 0
	var walk func(*yaml.Node)
	walk = func(n *yaml.Node) {
		if n == nil {
			return
		}
		if n.Line > 0 && n.Column > 0 {
			vs := offsetFor(st.lineOffsets, n.Line, n.Column)
			if vs >= 0 && vs < len(st.original) {
				le := findLineEnd(st.original, vs)
				if le > maxEnd {
					maxEnd = le
				}
			}
		}
		for _, c := range n.Content {
			walk(c)
		}
	}
	walk(n)
	return maxEnd
}

// extendScalarBlockEnd walks forward from the scalar's line and includes
// any following lines that are part of the same scalar block.
// A continuation line is blank, or more-indented than the key's indent.
func extendScalarBlockEnd(b []byte, lineOffsets []int, scalarLine int, keyIndent int) int {
	lastEnd := findLineEnd(b, lineStartOffset(lineOffsets, scalarLine))

	for li := scalarLine + 1; li <= len(lineOffsets); li++ {
		start := lineStartOffset(lineOffsets, li)
		if start >= len(b) {
			break
		}
		end := findLineEnd(b, start)
		line := b[start:end]
		trimmed := bytes.TrimSpace(line)
		if len(trimmed) == 0 {
			// blank line → still part of block
			lastEnd = end
			continue
		}
		indent := leadingSpaces(line)
		if indent > keyIndent {
			// more-indented than key → still part of this scalar block
			lastEnd = end
			continue
		}
		// indentation <= keyIndent → new sibling key / mapping
		break
	}
	return lastEnd
}
