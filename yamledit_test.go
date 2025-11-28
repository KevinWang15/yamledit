package yamledit

import (
	"bytes"
	"encoding/json"
	"os"
	"sort"
	"strings"
	"testing"

	jsonpatch "github.com/evanphx/json-patch/v5"
	"github.com/pmezard/go-difflib/difflib"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestParseErrorsOnNonMappingTopLevel(t *testing.T) {
	in := []byte("- 1\n- 2\n")
	if _, err := Parse(in); err == nil {
		t.Fatalf("expected error for non-mapping top-level, got nil")
	}
}

func TestEnsurePathAndSetScalarIntOnExistingNestedMap(t *testing.T) {
	in := []byte("a:\n  b:\n    c: 1\n")
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	// Locate the nested mapping node for "b" directly
	bNode := findMapNode(doc.Content[0], "a", "b")
	if bNode == nil {
		t.Fatalf("failed to find mapping node for a.b")
	}

	SetScalarInt(bNode, "c", 42)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}
	if !strings.Contains(string(out), "c: 42") {
		t.Fatalf("expected c: 42 in output, got:\n%s", string(out))
	}
}

func TestEnsurePathConvertsScalarToMapping(t *testing.T) {
	in := []byte("x: 1\n")
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}
	// Convert x (scalar) -> mapping
	m := EnsurePath(doc, "x")
	if m == nil || m.Kind != yaml.MappingNode {
		t.Fatalf("EnsurePath did not produce a mapping for 'x'")
	}

	// Write and ensure shape is mapping
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}
	var round yaml.Node
	if err := yaml.Unmarshal(out, &round); err != nil {
		t.Fatalf("unmarshal roundtrip: %v", err)
	}
	x := findMapNode(round.Content[0], "x")
	if x == nil || x.Kind != yaml.MappingNode {
		t.Fatalf("after write, 'x' is not a mapping")
	}
}

func TestConcurrentSetScalarIntOnSameMapIsSafe(t *testing.T) {
	in := []byte("root: {}\n")
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}
	root := EnsurePath(doc, "root")

	done := make(chan struct{})
	go func() {
		SetScalarInt(root, "x", 1)
		done <- struct{}{}
	}()
	go func() {
		SetScalarInt(root, "y", 2)
		done <- struct{}{}
	}()

	<-done
	<-done

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Verify both keys present after roundtrip.
	type M map[string]any
	var top struct {
		Root M `yaml:"root"`
	}
	if err := yaml.Unmarshal(out, &top); err != nil {
		t.Fatalf("yaml unmarshal: %v\n%s", err, string(out))
	}
	if _, ok := top.Root["x"]; !ok {
		t.Fatalf("missing key x")
	}
	if _, ok := top.Root["y"]; !ok {
		t.Fatalf("missing key y")
	}
}

func TestEmptyDataCreatesEmptyDoc(t *testing.T) {
	doc, err := Parse([]byte{})
	if err != nil {
		t.Fatalf("Parse empty should succeed, got error: %v", err)
	}
	if doc == nil || doc.Kind != yaml.DocumentNode {
		t.Fatalf("expected valid document node for empty data")
	}
}

func TestPreservesCommentsAndIndent(t *testing.T) {
	// Test with 4-space indent
	in := []byte(`# file header comment
resources:
    # cpu comment
    cpu: 100
    # memory comment
    memory: 256
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	js := EnsurePath(doc, "resources")
	SetScalarInt(js, "cpu", 150)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Comments preserved
	if !bytes.Contains(out, []byte("# cpu comment")) || !bytes.Contains(out, []byte("# memory comment")) {
		t.Fatalf("expected comments to be preserved; got:\n%s", string(out))
	}

	// Must preserve exact 4-space indent
	if !bytes.Contains(out, []byte("    cpu: 150")) {
		t.Fatalf("expected 4-space indent for cpu to be preserved; got:\n%s", string(out))
	}
}

func TestApplyJSONPatchArrayReplaceMinimalDiff(t *testing.T) {
	original := `service:
  envs:
    FEATURE_FLAG: 'true'
    SERVICE_URL: "https://example.internal"
  externalSecretEnvs:
    - name: Z_SECRET
      path: secrets/apps/prod
      property: z-val
    - name: A_SECRET
      path: secrets/apps/prod
      property: a-val
    - name: M_SECRET
      path: secrets/apps/prod
      property: m-val
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	patch := mustDecodePatch(t, `[
		{"op":"replace","path":"","value":[
			{"name":"Z_SECRET","path":"secrets/apps/prod","property":"z-val"},
			{"name":"A_SECRET","path":"secrets/apps/prod","property":"a-val-new"},
			{"name":"M_SECRET","path":"secrets/apps/prod","property":"m-val"}
		]}
	]`)

	if err := ApplyJSONPatchAtPath(doc, patch, []string{"service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPath: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	adds, removes := diffStats(diff)
	if adds > 1 || removes > 1 {
		t.Fatalf("expected single-line change, got %d additions / %d removals:\n%s", adds, removes, diff)
	}
}

// --- helpers for tests ---

// findMapNode walks a mapping node by a sequence of scalar keys and returns the final mapping value node.
func findMapNode(n *yaml.Node, path ...string) *yaml.Node {
	if n == nil || n.Kind != yaml.MappingNode {
		return nil
	}
	cur := n
	for _, k := range path {
		var found *yaml.Node
		for i := 0; i+1 < len(cur.Content); i += 2 {
			if cur.Content[i].Kind == yaml.ScalarNode && cur.Content[i].Value == k {
				found = cur.Content[i+1]
				break
			}
		}
		if found == nil {
			return nil
		}
		if found.Kind != yaml.MappingNode {
			return found // return non-mapping if so (some tests expect to see this)
		}
		cur = found
	}
	return cur
}

func mustDecodePatch(t *testing.T, s string) jsonpatch.Patch {
	t.Helper()
	patch, err := jsonpatch.DecodePatch([]byte(s))
	if err != nil {
		t.Fatalf("jsonpatch decode error: %v", err)
	}
	return patch
}

func unifiedDiff(before, after string) string {
	diff, err := difflib.GetUnifiedDiffString(difflib.UnifiedDiff{
		A:        difflib.SplitLines(before),
		B:        difflib.SplitLines(after),
		FromFile: "before",
		ToFile:   "after",
		Context:  2,
	})
	if err != nil {
		return err.Error()
	}
	return diff
}

func diffStats(diff string) (adds, removes int) {
	for _, line := range strings.Split(diff, "\n") {
		if len(line) == 0 {
			continue
		}
		switch line[0] {
		case '+':
			if !strings.HasPrefix(line, "+++") {
				adds++
			}
		case '-':
			if !strings.HasPrefix(line, "---") {
				removes++
			}
		}
	}
	return
}

func cloneRecords(in map[string]map[string]any) map[string]map[string]any {
	out := make(map[string]map[string]any, len(in))
	for k, v := range in {
		c := make(map[string]any, len(v))
		for fk, fv := range v {
			c[fk] = fv
		}
		out[k] = c
	}
	return out
}

func extractArrayOrder(doc *yaml.Node, path []string, keyField string) []string {
	if len(path) == 0 || doc == nil {
		return nil
	}
	cur := doc
	if cur.Kind == yaml.DocumentNode && len(cur.Content) > 0 {
		cur = cur.Content[0]
	}
	for _, segment := range path[:len(path)-1] {
		if cur.Kind != yaml.MappingNode {
			return nil
		}
		var next *yaml.Node
		for i := 0; i+1 < len(cur.Content); i += 2 {
			if cur.Content[i].Kind == yaml.ScalarNode && cur.Content[i].Value == segment {
				next = cur.Content[i+1]
				break
			}
		}
		if next == nil {
			return nil
		}
		cur = next
	}
	final := path[len(path)-1]
	if cur.Kind != yaml.MappingNode {
		return nil
	}
	var seq *yaml.Node
	for i := 0; i+1 < len(cur.Content); i += 2 {
		if cur.Content[i].Kind == yaml.ScalarNode && cur.Content[i].Value == final {
			seq = cur.Content[i+1]
			break
		}
	}
	if seq == nil || seq.Kind != yaml.SequenceNode {
		return nil
	}
	order := make([]string, 0, len(seq.Content))
	for _, item := range seq.Content {
		if item.Kind != yaml.MappingNode {
			continue
		}
		for i := 0; i+1 < len(item.Content); i += 2 {
			if item.Content[i].Kind == yaml.ScalarNode && item.Content[i].Value == keyField {
				if item.Content[i+1].Kind == yaml.ScalarNode {
					order = append(order, item.Content[i+1].Value)
				}
				break
			}
		}
	}
	return order
}

func buildArrayJSON(records map[string]map[string]any, existingOrder []string, keyField string, fields []string) ([]byte, error) {
	seen := make(map[string]bool, len(existingOrder))
	keys := make([]string, 0, len(records))
	for _, k := range existingOrder {
		if _, ok := records[k]; ok && !seen[k] {
			keys = append(keys, k)
			seen[k] = true
		}
	}
	var extras []string
	for k := range records {
		if !seen[k] {
			extras = append(extras, k)
		}
	}
	sort.Strings(extras)
	keys = append(keys, extras...)

	buf := bytes.NewBufferString("[")
	for i, key := range keys {
		if i > 0 {
			buf.WriteByte(',')
		}
		buf.WriteByte('{')
		first := true
		if err := writeJSONField(buf, keyField, key, &first); err != nil {
			return nil, err
		}
		for _, f := range fields {
			if val, ok := records[key][f]; ok {
				if err := writeJSONField(buf, f, val, &first); err != nil {
					return nil, err
				}
			}
		}
		for fk, fv := range records[key] {
			if fk == keyField {
				continue
			}
			found := false
			for _, f := range fields {
				if f == fk {
					found = true
					break
				}
			}
			if !found {
				if err := writeJSONField(buf, fk, fv, &first); err != nil {
					return nil, err
				}
			}
		}
		buf.WriteByte('}')
	}
	buf.WriteByte(']')
	return buf.Bytes(), nil
}

func writeJSONField(buf *bytes.Buffer, name string, value any, first *bool) error {
	if !*first {
		buf.WriteByte(',')
	}
	*first = false

	nameJSON, err := json.Marshal(name)
	if err != nil {
		return err
	}
	buf.Write(nameJSON)
	buf.WriteByte(':')

	valJSON, err := json.Marshal(value)
	if err != nil {
		return err
	}
	buf.Write(valJSON)
	return nil
}

func applySequencePatch(doc *yaml.Node, path []string, op string, value []byte) error {
	type patchOp struct {
		Op    string          `json:"op"`
		Path  string          `json:"path"`
		Value json.RawMessage `json:"value,omitempty"`
	}
	payload, err := json.Marshal([]patchOp{{Op: op, Path: "", Value: json.RawMessage(value)}})
	if err != nil {
		return err
	}
	return ApplyJSONPatchAtPathBytes(doc, payload, path)
}

func TestPreserves2SpaceIndent(t *testing.T) {
	in := []byte(`root:
  child1: value1
  child2:
    nested: value2
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	// Make a change
	child2 := EnsurePath(doc, "root", "child2")
	SetScalarInt(child2, "newkey", 42)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Must preserve 2-space indent
	if !bytes.Contains(out, []byte("  child1:")) {
		t.Errorf("Expected 2-space indent for child1, got:\n%s", out)
	}
	if !bytes.Contains(out, []byte("    nested:")) {
		t.Errorf("Expected 4-space indent for nested (2 levels), got:\n%s", out)
	}
	if !bytes.Contains(out, []byte("    newkey: 42")) {
		t.Errorf("Expected 4-space indent for newkey (2 levels), got:\n%s", out)
	}
}

func TestPreserves4SpaceIndent(t *testing.T) {
	in := []byte(`root:
    child1: value1
    child2:
        nested: value2
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	// Make a change
	child2 := EnsurePath(doc, "root", "child2")
	SetScalarInt(child2, "newkey", 42)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Must preserve 4-space indent
	if !bytes.Contains(out, []byte("    child1:")) {
		t.Errorf("Expected 4-space indent for child1, got:\n%s", out)
	}
	if !bytes.Contains(out, []byte("        nested:")) {
		t.Errorf("Expected 8-space indent for nested (2 levels), got:\n%s", out)
	}
	if !bytes.Contains(out, []byte("        newkey: 42")) {
		t.Errorf("Expected 8-space indent for newkey (2 levels), got:\n%s", out)
	}
}

func TestPreserves3SpaceIndent(t *testing.T) {
	in := []byte(`root:
   child: value
   nested:
      deep: value2
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Must preserve 3-space indent
	if !bytes.Contains(out, []byte("   child:")) {
		t.Errorf("Expected 3-space indent for child, got:\n%s", out)
	}
	if !bytes.Contains(out, []byte("      deep:")) {
		t.Errorf("Expected 6-space indent for deep (2 levels), got:\n%s", out)
	}
}

func TestIndentDetection(t *testing.T) {
	tests := []struct {
		name     string
		input    []byte
		expected int
	}{
		{
			name: "2 spaces",
			input: []byte(`root:
  child: value`),
			expected: 2,
		},
		{
			name: "4 spaces",
			input: []byte(`root:
    child: value`),
			expected: 4,
		},
		{
			name: "3 spaces",
			input: []byte(`root:
   child: value`),
			expected: 3,
		},
		{
			name: "mixed but consistent levels",
			input: []byte(`root:
  child:
    deep:
      deeper: value`),
			expected: 2,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			detected := detectIndent(tt.input)
			if detected != tt.expected {
				t.Errorf("detectIndent() = %d, want %d for input:\n%s", detected, tt.expected, tt.input)
			}
		})
	}
}

func TestComplexIndentPreservation(t *testing.T) {
	in := []byte(`# Header comment
services:
    web:
        # Web config
        port: 8080
        replicas: 3
    db:
        # Database config
        host: localhost
        port: 5432
`)

	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	// Modify values
	web := EnsurePath(doc, "services", "web")
	SetScalarInt(web, "replicas", 5)

	db := EnsurePath(doc, "services", "db")
	SetScalarInt(db, "port", 5433)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	// Verify exact indentation
	lines := bytes.Split(out, []byte("\n"))
	for _, line := range lines {
		if bytes.Contains(line, []byte("web:")) {
			if !bytes.HasPrefix(line, []byte("    web:")) {
				t.Errorf("Expected 4-space indent for 'web:', got: %q", line)
			}
		}
		if bytes.Contains(line, []byte("port:")) && bytes.Contains(line, []byte("8080")) {
			if !bytes.HasPrefix(line, []byte("        port:")) {
				t.Errorf("Expected 8-space indent for 'port: 8080', got: %q", line)
			}
		}
		if bytes.Contains(line, []byte("replicas:")) {
			if !bytes.HasPrefix(line, []byte("        replicas:")) {
				t.Errorf("Expected 8-space indent for 'replicas:', got: %q", line)
			}
		}
	}

	// Should still have 4-space base indent
	if !bytes.Contains(out, []byte("    web:")) {
		t.Errorf("Lost 4-space indent for web")
	}
	if !bytes.Contains(out, []byte("    db:")) {
		t.Errorf("Lost 4-space indent for db")
	}
}

func TestIndentPreservationIsExact(t *testing.T) {
	tests := []struct {
		name  string
		input []byte
	}{
		{
			name: "2-space indent",
			input: []byte(`app:
  name: test
  config:
    port: 8080
    nested:
      deep: value
`),
		},
		{
			name: "4-space indent",
			input: []byte(`app:
    name: test
    config:
        port: 8080
        nested:
            deep: value
`),
		},
		{
			name: "3-space indent",
			input: []byte(`app:
   name: test
   config:
      port: 8080
      nested:
         deep: value
`),
		},
		{
			name: "mixed with comments",
			input: []byte(`# Root comment
services:
    # Web service
    web:
        port: 80  # HTTP port
        # Security settings
        ssl:
            enabled: true
    # Database
    database:
        host: localhost
`),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Parse
			doc, err := Parse(tt.input)
			if err != nil {
				t.Fatalf("Parse error: %v", err)
			}

			// Make some changes
			if tt.name == "mixed with comments" {
				web := EnsurePath(doc, "services", "web")
				SetScalarInt(web, "port", 443)
			} else {
				app := EnsurePath(doc, "app")
				SetScalarInt(app, "version", 2)
			}

			// Marshal back
			out, err := Marshal(doc)
			if err != nil {
				t.Fatalf("Marshal error: %v", err)
			}

			// Compare line by line for indent consistency
			inLines := bytes.Split(tt.input, []byte("\n"))
			outLines := bytes.Split(out, []byte("\n"))

			for i := range inLines {
				if i >= len(outLines) {
					break
				}

				// Skip blank lines
				if len(bytes.TrimSpace(inLines[i])) == 0 {
					continue
				}

				inSpaces := countLeadingSpaces(inLines[i])
				outSpaces := countLeadingSpaces(outLines[i])

				// For unchanged lines, indent must be identical
				if bytes.Contains(inLines[i], []byte("name:")) && bytes.Contains(outLines[i], []byte("name:")) {
					if inSpaces != outSpaces {
						t.Errorf("Line %d: indent changed from %d to %d spaces\nOriginal: %q\nOutput:   %q",
							i, inSpaces, outSpaces, inLines[i], outLines[i])
					}
				}
			}
		})
	}
}

func countLeadingSpaces(line []byte) int {
	count := 0
	for _, b := range line {
		if b == ' ' {
			count++
		} else {
			break
		}
	}
	return count
}

func TestPreservesKeyOrder(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{
			name: "simple order",
			input: `zebra: 1
apple: 2
middle: 3
`,
		},
		{
			name: "nested order",
			input: `third: 3
first:
  zulu: z
  alpha: a
  bravo: b
second: 2
`,
		},
		{
			name: "complex order with comments",
			input: `# Header
zoo: animals
bar: drinks
foo: food
nested:
  last: 100
  middle: 50
  first: 1
`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			if err != nil {
				t.Fatalf("Parse error: %v", err)
			}

			// Make a change
			root := doc.Content[0]
			SetScalarInt(root, "newkey", 999)

			out, err := Marshal(doc)
			if err != nil {
				t.Fatalf("Marshal error: %v", err)
			}

			t.Logf("Input:\n%s", tt.input)
			t.Logf("Output:\n%s", out)

			// Check that original keys appear in the same order
			inputLines := strings.Split(tt.input, "\n")
			outputLines := strings.Split(string(out), "\n")

			var inputKeys []string
			for _, line := range inputLines {
				if strings.Contains(line, ":") && !strings.HasPrefix(strings.TrimSpace(line), "#") {
					parts := strings.Split(line, ":")
					key := strings.TrimSpace(parts[0])
					if key != "" {
						inputKeys = append(inputKeys, key)
					}
				}
			}

			var outputKeys []string
			for _, line := range outputLines {
				if strings.Contains(line, ":") && !strings.HasPrefix(strings.TrimSpace(line), "#") {
					parts := strings.Split(line, ":")
					key := strings.TrimSpace(parts[0])
					if key != "" && key != "newkey" { // Exclude the new key we added
						outputKeys = append(outputKeys, key)
					}
				}
			}

			// Check that the order is preserved
			if len(inputKeys) != len(outputKeys) {
				t.Errorf("Key count mismatch: input had %d keys, output has %d keys", len(inputKeys), len(outputKeys))
			}

			for i := 0; i < len(inputKeys) && i < len(outputKeys); i++ {
				if inputKeys[i] != outputKeys[i] {
					t.Errorf("Key order not preserved at position %d: expected %q, got %q", i, inputKeys[i], outputKeys[i])
				}
			}
		})
	}
}

func TestNewKeysAppendedAtEnd(t *testing.T) {
	input := `first: 1
second: 2
third: 3
`
	doc, err := Parse([]byte(input))
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	root := doc.Content[0]
	SetScalarInt(root, "fourth", 4)
	SetScalarInt(root, "fifth", 5)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	lines := strings.Split(string(out), "\n")

	// Find positions of keys
	positions := make(map[string]int)
	for i, line := range lines {
		if strings.Contains(line, ":") {
			parts := strings.Split(line, ":")
			key := strings.TrimSpace(parts[0])
			positions[key] = i
		}
	}

	// Check order
	if positions["first"] > positions["second"] {
		t.Errorf("first should come before second")
	}
	if positions["second"] > positions["third"] {
		t.Errorf("second should come before third")
	}
	if positions["third"] > positions["fourth"] {
		t.Errorf("third should come before fourth (new keys append)")
	}
	if positions["fourth"] > positions["fifth"] {
		t.Errorf("fourth should come before fifth (maintain add order)")
	}
}

func TestModifyingExistingKeysPreservesOrder(t *testing.T) {
	input := `gamma: 3
alpha: 1
beta: 2
delta: 4
`
	doc, err := Parse([]byte(input))
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	root := doc.Content[0]
	// Modify existing keys
	SetScalarInt(root, "alpha", 100)
	SetScalarInt(root, "delta", 400)
	SetScalarInt(root, "beta", 200)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	expected := `gamma: 3
alpha: 100
beta: 200
delta: 400
`

	if string(out) != expected {
		t.Errorf("Order not preserved.\nExpected:\n%s\nGot:\n%s", expected, out)
	}
}

func TestPreserveSingleQuotedScalar_UnrelatedChange(t *testing.T) {
	in := []byte(`# header
env:
  HTTP_CORS_ALLOWED_ORIGINS: '*'
  METRICS_ENABLED: "true"
  port: 8080
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	svc := EnsurePath(doc, "env")
	SetScalarInt(svc, "port", 9090)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if !bytes.Contains(out, []byte(`HTTP_CORS_ALLOWED_ORIGINS: '*'`)) {
		t.Fatalf("single-quoted value should be preserved; got:\n%s", out)
	}

	before := getLineContaining(string(in), "HTTP_CORS_ALLOWED_ORIGINS:")
	after := getLineContaining(string(out), "HTTP_CORS_ALLOWED_ORIGINS:")
	if before != after {
		t.Fatalf("unrelated line changed:\nBEFORE: %q\nAFTER:  %q", before, after)
	}
}

func TestPreserveDoubleQuotedScalar_UnrelatedChange(t *testing.T) {
	in := []byte(`svc:
  GREETING: "hello"
  port: 8080
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	svc := EnsurePath(doc, "svc")
	SetScalarInt(svc, "port", 9090)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	line := getLineContaining(string(out), "GREETING:")
	if line != `  GREETING: "hello"` {
		t.Fatalf("expected GREETING line unchanged (double quotes), got: %q", line)
	}
}

func TestInlineCommentPreservedOnUpdatedInt(t *testing.T) {
	in := []byte(`svc:
  port: 8080  # http
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	svc := EnsurePath(doc, "svc")
	SetScalarInt(svc, "port", 9090)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	want := `  port: 9090  # http`
	got := getLineContaining(string(out), "port:")
	if got != want {
		t.Fatalf("inline comment or spacing lost.\nwant: %q\ngot:  %q\nfull:\n%s", want, got, out)
	}
}

func TestSingleLineDiffOnIntegerUpdate(t *testing.T) {
	in := []byte(`# header
cfg:
  a: 1
  b: "x"
  cors: '*'
  c: 2
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	cfg := EnsurePath(doc, "cfg")
	SetScalarInt(cfg, "a", 10)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	diff := countDifferentLines(string(in), string(out))
	if diff != 1 {
		t.Fatalf("expected exactly 1 line to change, got %d\n--- before ---\n%s\n--- after ---\n%s", diff, in, out)
	}
	// And the single-quoted cors stays single-quoted.
	if !bytes.Contains(out, []byte(`cors: '*'`)) {
		t.Fatalf("expected cors line to remain single-quoted; got:\n%s", out)
	}
}

func TestInsertNewIntegerKeyPreservesIndent(t *testing.T) {
	in := []byte(`svc:
    name: api
    port: 8080
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	svc := EnsurePath(doc, "svc")
	SetScalarInt(svc, "timeout", 30) // NEW key

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// Existing line stays identical
	before := getLineContaining(string(in), "name:")
	after := getLineContaining(string(out), "name:")
	if before != after {
		t.Fatalf("unchanged line churned:\nBEFORE: %q\nAFTER:  %q", before, after)
	}

	// New key appears at 4-space indent, appended
	if !bytes.Contains(out, []byte("    timeout: 30")) {
		t.Fatalf("expected 4-space indent for newly inserted key; got:\n%s", out)
	}
	posPort := lineIndexContaining(string(out), "port:")
	posTimeout := lineIndexContaining(string(out), "timeout:")
	if !(posTimeout > posPort) {
		t.Fatalf("new key should be appended after existing ones; port line idx=%d, timeout idx=%d", posPort, posTimeout)
	}
}

func TestTopLevelInsertAppendsWithoutTouchingHeader(t *testing.T) {
	in := []byte(`# header
alpha: 1
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	root := doc.Content[0]
	SetScalarInt(root, "beta", 2)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// header intact
	if getLineContaining(string(out), "# header") != "# header" {
		t.Fatalf("header changed: %q", getLineContaining(string(out), "# header"))
	}
	// ordering: alpha before beta
	iAlpha := lineIndexContaining(string(out), "alpha:")
	iBeta := lineIndexContaining(string(out), "beta:")
	if !(iAlpha >= 0 && iBeta > iAlpha) {
		t.Fatalf("beta should be appended after alpha; alpha=%d beta=%d\n%s", iAlpha, iBeta, out)
	}
}

func TestShapeChangeFallbackDoesNotChurnOtherQuotes(t *testing.T) {
	in := []byte(`x: 1
note: "*"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	// Force shape change: x (scalar) -> mapping
	_ = EnsurePath(doc, "x")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// x is a mapping now
	var round yaml.Node
	if err := yaml.Unmarshal(out, &round); err != nil {
		t.Fatalf("unmarshal round: %v\n%s", err, out)
	}
	x := findMapNode(round.Content[0], "x")
	if x == nil || x.Kind != yaml.MappingNode {
		t.Fatalf("'x' should be mapping after write; got kind=%v", x)
	}

	// note's double quotes remain double quotes
	if getLineContaining(string(out), "note:") != `note: "*"` {
		t.Fatalf("expected note line to stay double-quoted; got: %q\nfull:\n%s",
			getLineContaining(string(out), "note:"), out)
	}
}

func TestIndentlessSequenceUnchangedOnUnrelatedChange(t *testing.T) {
	in := []byte(`items:
- a
- b
settings:
  port: 8080
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	settings := EnsurePath(doc, "settings")
	SetScalarInt(settings, "port", 8081)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	if getLineContaining(string(out), "- a") != "- a" || getLineContaining(string(out), "- b") != "- b" {
		t.Fatalf("indentless sequence should be untouched; got:\n%s", out)
	}
}

func TestFinalNewlinePreserved(t *testing.T) {
	in := []byte("svc:\n  port: 8080\n") // ends with newline
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	svc := EnsurePath(doc, "svc")
	SetScalarInt(svc, "port", 9090)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if len(out) == 0 || out[len(out)-1] != '\n' {
		t.Fatalf("final newline should be preserved; got bytes: %v", out)
	}
}

func TestGoldenPreservesUnchangedBytes(t *testing.T) {
	orig, err := os.ReadFile("golden_testdata.yaml")
	require.NoError(t, err)

	doc, err := Parse(orig)
	require.NoError(t, err)

	// mutate a value; unrelated lines should stay byte-identical
	svc := EnsurePath(doc, "svc")
	SetScalarInt(svc, "port", 9090)

	out, err := Marshal(doc)
	require.NoError(t, err)

	if bytes.Contains(out, []byte("\r")) {
		t.Fatalf("unexpected CR in output")
	}

	beforeLines := strings.Split(string(orig), "\n")
	afterLines := strings.Split(string(out), "\n")
	if len(beforeLines) != len(afterLines) {
		t.Fatalf("line count changed: before=%d after=%d", len(beforeLines), len(afterLines))
	}
	// header and name line should be identical
	if beforeLines[0] != afterLines[0] {
		t.Fatalf("header line churned:\nbefore: %q\nafter:  %q", beforeLines[0], afterLines[0])
	}
	if beforeLines[1] != afterLines[1] {
		t.Fatalf("svc name line churned:\nbefore: %q\nafter:  %q", beforeLines[1], afterLines[1])
	}
	// notes block should remain unchanged
	for i := range beforeLines {
		if strings.Contains(beforeLines[i], "notes: |") {
			for j := 0; j <= 2; j++ { // notes line plus two content lines
				if beforeLines[i+j] != afterLines[i+j] {
					t.Fatalf("notes block changed at line %d:\nbefore: %q\nafter:  %q", i+j, beforeLines[i+j], afterLines[i+j])
				}
			}
			break
		}
	}
	// port line should reflect change and preserve inline comment spacing
	portLine := getLineContaining(string(out), "port:")
	if portLine != "  port: 9090  # inline" {
		t.Fatalf("port line incorrect:\n%s", portLine)
	}
}

func TestInsertNewKeyAtEOF_NoFinalNewline_SeparatesLine(t *testing.T) {
	// No newline at EOF; last line is the nested mapping's last line.
	in := []byte(`deploy:
  serviceAccount:
    create: "true"`)

	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	js := EnsurePath(doc, "deploy")

	// Insert a new top-level key under "config"
	SetScalarInt(js, "replicas", 5)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	s := string(out)

	// Must NOT be appended to the same line as 'create: "true"'
	if strings.Contains(s, `create: "true" replicas:`) {
		t.Fatalf("new key appended to same line; got:\n%s", s)
	}

	// The new key should appear on its own line with the correct (2-space) indent
	if !strings.Contains(s, "\n  replicas: 5\n") && !strings.HasSuffix(s, "\n  replicas: 5") {
		t.Fatalf("expected '  replicas: 5' on a new line; got:\n%s", s)
	}

	// Ensure the order is correct: 'replicas' comes after 'serviceAccount' block
	iCreate := strings.Index(s, `create: "true"`)
	iRep := strings.Index(s, "replicas: 5")
	if !(iCreate >= 0 && iRep > iCreate) {
		t.Fatalf("expected replicas to be appended after serviceAccount; create=%d replicas=%d\n%s", iCreate, iRep, s)
	}
}

func TestSetScalarString_UpdatePreservesQuotes_Double(t *testing.T) {
	in := []byte(`env:
  GREETING: "hello"
  port: 8080
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	SetScalarString(env, "GREETING", "hi")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	got := getLineContaining(string(out), "GREETING:")
	want := `  GREETING: "hi"`
	if got != want {
		t.Fatalf("double-quote style should be preserved\nwant: %q\ngot:  %q\nfull:\n%s", want, got, out)
	}
}

func TestSetScalarString_UpdatePreservesQuotes_Single_WithEscapes(t *testing.T) {
	in := []byte(`env:
  NOTE: 'it works'
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	SetScalarString(env, "NOTE", "it's fine") // must escape as it''s

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	got := getLineContaining(string(out), "NOTE:")
	want := `  NOTE: 'it''s fine'`
	if got != want {
		t.Fatalf("single-quote style/escaping not preserved\nwant: %q\ngot:  %q\nfull:\n%s", want, got, out)
	}
}

func TestSetScalarString_InsertNew_AppendsWithIndentAndQuotes(t *testing.T) {
	in := []byte(`env:
    A: 1
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	SetScalarString(env, "NEW", "v1")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// Unchanged line should remain byte-identical
	before := getLineContaining(string(in), "A:")
	after := getLineContaining(string(out), "A:")
	if before != after {
		t.Fatalf("unchanged line churned:\nBEFORE: %q\nAFTER:  %q", before, after)
	}

	// New key appended with 4-space indent; value quoted (either 'v1' or "v1")
	newLine := getLineContaining(string(out), "NEW:")
	if !(newLine == `    NEW: 'v1'` || newLine == `    NEW: "v1"`) {
		t.Fatalf("unexpected formatting for inserted string key; got: %q", newLine)
	}

	posA := lineIndexContaining(string(out), "A:")
	posN := lineIndexContaining(string(out), "NEW:")
	if !(posN > posA) {
		t.Fatalf("NEW should be appended after A; A=%d NEW=%d\n%s", posA, posN, out)
	}
}

func TestSetScalarBool_UpdateBare_PreservesOtherLines(t *testing.T) {
	in := []byte(`cfg:
  enabled: false  # feature gate
  name: "svc"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	cfg := EnsurePath(doc, "cfg")
	SetScalarBool(cfg, "enabled", true)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	// Updated line keeps inline comment and base spacing; token becomes bare true
	want := `  enabled: true  # feature gate`
	got := getLineContaining(string(out), "enabled:")
	if got != want {
		t.Fatalf("bool update lost formatting/comment\nwant: %q\ngot:  %q\nfull:\n%s", want, got, out)
	}
	// Unrelated quoted string unchanged
	if getLineContaining(string(out), `name:`) != `  name: "svc"` {
		t.Fatalf("unrelated line churned:\n%s", out)
	}
}

func TestSetScalarBool_InsertNew_AppendsWithIndent(t *testing.T) {
	in := []byte(`cfg:
    a: 1
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	cfg := EnsurePath(doc, "cfg")
	SetScalarBool(cfg, "enabled", true)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	// New key at 4-space indent
	if getLineContaining(string(out), "enabled:") != `    enabled: true` {
		t.Fatalf("expected 4-space indent for inserted bool; got:\n%s", out)
	}
	// a: 1 remains identical
	before := getLineContaining(string(in), "a:")
	after := getLineContaining(string(out), "a:")
	if before != after {
		t.Fatalf("unchanged line churned:\nBEFORE: %q\nAFTER:  %q", before, after)
	}
}

func TestSetScalarBool_QuotedOldBecomesBareBool(t *testing.T) {
	in := []byte(`env:
  FLAG: "true"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	SetScalarBool(env, "FLAG", false)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	// We normalize to bare YAML booleans for the edited key
	if getLineContaining(string(out), "FLAG:") != `  FLAG: false` {
		t.Fatalf("expected bare YAML boolean; got:\n%s", out)
	}
}

func TestPlainStringsWithSpacesStayUnquotedOnUnrelatedChange(t *testing.T) {
	in := []byte(`service:
  envs:
    SERVICE_URI_LIST: http://node-1.example.net:8081,http://node-2.example.net:8081,http://node-3.example.net:8081
    JVM_FLAGS: -Xms2048m -Xmx2048m
  replicas: 3
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	// Change an unrelated integer field under the same mapping.
	svc := EnsurePath(doc, "service")
	SetScalarInt(svc, "replicas", 4)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// Ensure the previously bare strings remain unquoted.
	if got := getLineContaining(string(out), "SERVICE_URI_LIST:"); got != "    SERVICE_URI_LIST: http://node-1.example.net:8081,http://node-2.example.net:8081,http://node-3.example.net:8081" {
		t.Fatalf("SERVICE_URI_LIST line changed:\n%s", out)
	}
	if got := getLineContaining(string(out), "JVM_FLAGS:"); got != "    JVM_FLAGS: -Xms2048m -Xmx2048m" {
		t.Fatalf("JVM_FLAGS line changed:\n%s", out)
	}
	// And the edited field reflects the new value.
	if getLineContaining(string(out), "replicas:") != "  replicas: 4" {
		t.Fatalf("replicas not updated correctly:\n%s", out)
	}
}

func TestDeleteKey_RemovesOnlyThatKey_Surgically(t *testing.T) {
	in := []byte(`# header
env:
  A: "1"
  B: "2"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	DeleteKey(env, "A")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// header intact
	if getLineContaining(string(out), "# header") != "# header" {
		t.Fatalf("header changed")
	}
	if strings.Contains(string(out), "A:") {
		t.Fatalf("A should be deleted; got:\n%s", out)
	}
	// B unchanged
	if getLineContaining(string(out), "B:") != `  B: "2"` {
		t.Fatalf("B line changed:\n%s", out)
	}
}

func TestDeleteKey_RemovesAllDuplicates(t *testing.T) {
	in := []byte(`env:
  A: "x"
  A: "y"
  B: "z"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	DeleteKey(env, "A")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if strings.Contains(string(out), "A:") {
		t.Fatalf("expected all A entries removed; got:\n%s", out)
	}
	if getLineContaining(string(out), "B:") != `  B: "z"` {
		t.Fatalf("B should remain; got:\n%s", out)
	}
}

func TestDeleteKey_Missing_NoChange(t *testing.T) {
	in := []byte(`env:
  X: "1"
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	env := EnsurePath(doc, "env")
	DeleteKey(env, "Y") // not present

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if string(out) != string(in) {
		t.Fatalf("deleting non-existent key should not change output\nbefore:\n%s\nafter:\n%s", in, out)
	}
}

func TestA(t *testing.T) {
	in := []byte(`deploy:
  envs:
    KEEP_THIS: keep_value
    REMOVE_THIS: remove_value
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	js := EnsurePath(doc, "deploy")
	envs := EnsurePath(js, "envs")
	DeleteKey(envs, "REMOVE_THIS")
	output, err := Marshal(doc)

	print(output, err)
}
func TestInsertNewEnvVarUnderNestedMapping(t *testing.T) {
	in := []byte(`deploy:
  envs:
    EXISTING_KEY: existing_value
  replicas: 3
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	// ✅ Call EnsurePath from the document root for the full path.
	envs := EnsurePath(doc, "deploy", "envs")
	SetScalarString(envs, "NEW_ENV", "new_value")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	s := string(out)

	// Existing lines unchanged.
	if getLineContaining(s, "EXISTING_KEY:") != "    EXISTING_KEY: existing_value" {
		t.Fatalf("EXISTING_KEY line changed:\n%s", s)
	}
	if getLineContaining(s, "replicas:") != "  replicas: 3" {
		t.Fatalf("replicas line changed:\n%s", s)
	}

	// New env var appended with correct indent and quoting.
	newLine := getLineContaining(s, "NEW_ENV:")
	if !(newLine == "    NEW_ENV: 'new_value'" || newLine == `    NEW_ENV: "new_value"`) {
		t.Fatalf("unexpected formatting for inserted env var; got: %q\nfull:\n%s", newLine, s)
	}

	// Ordering: EXISTING_KEY before NEW_ENV; envs block before replicas.
	posExisting := lineIndexContaining(s, "EXISTING_KEY:")
	posNew := lineIndexContaining(s, "NEW_ENV:")
	posReplicas := lineIndexContaining(s, "replicas:")
	if !(posExisting >= 0 && posNew > posExisting) {
		t.Fatalf("NEW_ENV should be appended after EXISTING_KEY; EXISTING_KEY=%d NEW_ENV=%d\n%s", posExisting, posNew, s)
	}
	if !(posReplicas > posNew) {
		t.Fatalf("envs section should appear before replicas; NEW_ENV=%d replicas=%d\n%s", posNew, posReplicas, s)
	}
}

func TestEnsurePathFromMapping_AllowsChainedCalls(t *testing.T) {
	in := []byte(`deploy:
  envs:
    EXISTING_KEY: existing_value
  replicas: 3
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	// First from doc → "deploy", then from that mapping → "envs"
	deploy := EnsurePath(doc, "deploy")
	envs := EnsurePath(deploy, "envs")
	if envs == nil || envs.Kind != yaml.MappingNode {
		t.Fatalf("expected mapping node for deploy.envs")
	}

	SetScalarString(envs, "NEW_ENV", "new_value")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	s := string(out)

	// Existing lines unchanged
	if getLineContaining(s, "EXISTING_KEY:") != "    EXISTING_KEY: existing_value" {
		t.Fatalf("EXISTING_KEY line changed:\n%s", s)
	}
	if getLineContaining(s, "replicas:") != "  replicas: 3" {
		t.Fatalf("replicas line changed:\n%s", s)
	}

	// NEW_ENV present with correct indent & quoting
	nl := getLineContaining(s, "NEW_ENV:")
	if !(nl == "    NEW_ENV: 'new_value'" || nl == `    NEW_ENV: "new_value"`) {
		t.Fatalf("NEW_ENV not inserted as expected; got: %q\nfull:\n%s", nl, s)
	}
}

// --- small helpers ---

func getLineContaining(s, substr string) string {
	for _, ln := range strings.Split(s, "\n") {
		if strings.Contains(ln, substr) {
			return ln
		}
	}
	return ""
}

func lineIndexContaining(s, substr string) int {
	lines := strings.Split(s, "\n")
	for i, ln := range lines {
		if strings.Contains(ln, substr) {
			return i
		}
	}
	return -1
}

func countDifferentLines(a, b string) int {
	as := strings.Split(a, "\n")
	bs := strings.Split(b, "\n")
	n := max(len(as), len(bs))
	diff := 0
	for i := 0; i < n; i++ {
		var la, lb string
		if i < len(as) {
			la = as[i]
		}
		if i < len(bs) {
			lb = bs[i]
		}
		if la != lb {
			diff++
		}
	}
	return diff
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

// ---------------------------
// JSON Patch tests
// ---------------------------

func TestJSONPatch_AddEnvVarAtBasePath(t *testing.T) {
	in := []byte(`java-service:
  envs:
    EXISTING_KEY: existing_value
  replicas: 3
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}
	patch := []byte(`[{"op":"add","path":"/NEW_KEY","value":"new_value"}]`)
	if err := ApplyJSONPatchAtPathBytes(doc, patch, []string{"java-service", "envs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	s := string(out)
	if getLineContaining(s, "EXISTING_KEY:") != "    EXISTING_KEY: existing_value" {
		t.Fatalf("existing line churned:\n%s", s)
	}
	nl := getLineContaining(s, "NEW_KEY:")
	if !(nl == "    NEW_KEY: 'new_value'" || nl == `    NEW_KEY: "new_value"`) {
		t.Fatalf("NEW_KEY not appended with quoting; got: %q\nfull:\n%s", nl, s)
	}
}

func TestJSONPatch_ReplaceInt(t *testing.T) {
	in := []byte(`java-service:
  replicas: 3
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	target := EnsurePath(doc, "java-service")
	patch := []byte(`[{"op":"replace","path":"/replicas","value":5}]`)
	if err := ApplyJSONPatchBytes(target, patch); err != nil {
		t.Fatalf("apply: %v", err)
	}
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if getLineContaining(string(out), "replicas:") != "  replicas: 5" {
		t.Fatalf("replicas not replaced, got:\n%s", out)
	}
}

func TestJSONPatch_RemoveKey(t *testing.T) {
	in := []byte(`svc:
  A: "1"
  B: "2"
`)
	doc, _ := Parse(in)
	target := EnsurePath(doc, "svc")
	patch := []byte(`[{"op":"remove","path":"/A"}]`)
	if err := ApplyJSONPatchBytes(target, patch); err != nil {
		t.Fatalf("apply: %v", err)
	}
	out, _ := Marshal(doc)
	if strings.Contains(string(out), "A:") {
		t.Fatalf("A should be removed:\n%s", out)
	}
	if getLineContaining(string(out), "B:") != `  B: "2"` {
		t.Fatalf("B changed:\n%s", out)
	}
}

func TestJSONPatch_TestOp(t *testing.T) {
	in := []byte(`cfg:
  enabled: false
`)
	doc, _ := Parse(in)
	target := EnsurePath(doc, "cfg")
	ok := []byte(`[{"op":"test","path":"/enabled","value":false}]`)
	if err := ApplyJSONPatchBytes(target, ok); err != nil {
		t.Fatalf("test should pass, got: %v", err)
	}
	bad := []byte(`[{"op":"test","path":"/enabled","value":true}]`)
	if err := ApplyJSONPatchBytes(target, bad); err == nil {
		t.Fatalf("test should fail")
	}
}

func TestJSONPatch_ArrayAddTriggersFallback(t *testing.T) {
	in := []byte(`items:
- a
- b
`)
	doc, _ := Parse(in)
	patch := []byte(`[{"op":"add","path":"/items/-","value":"c"}]`)
	if err := ApplyJSONPatchBytes(doc, patch); err != nil {
		t.Fatalf("apply: %v", err)
	}
	out, _ := Marshal(doc)
	s := string(out)
	if !strings.Contains(s, "- c") {
		t.Fatalf("expected array append, got:\n%s", s)
	}
}

func TestJSONPatch_WrappersWithDecodePatch(t *testing.T) {
	in := []byte(`svc:
  port: 8080
`)
	doc, _ := Parse(in)
	pb := []byte(`[{"op":"replace","path":"/port","value":9090}]`)
	var arr []map[string]any
	_ = json.Unmarshal(pb, &arr) // ensure valid

	// Use jsonpatch.Patch wrapper (if available)
	p, err := jsonpatch.DecodePatch(pb)
	if err != nil {
		t.Fatalf("DecodePatch: %v", err)
	}
	if err := ApplyJSONPatch(EnsurePath(doc, "svc"), p); err != nil {
		t.Fatalf("ApplyJSONPatch: %v", err)
	}
	out, _ := Marshal(doc)
	if getLineContaining(string(out), "port:") != "  port: 9090" {
		t.Fatalf("replace failed:\n%s", out)
	}
}

func TestJSONPatch_ConcurrentMarshalNoDeadlock(t *testing.T) {
	in := []byte(`svc:
  port: 8080
  name: "api"
`)
	doc, _ := Parse(in)
	svc := EnsurePath(doc, "svc")

	done := make(chan struct{})

	go func() {
		defer close(done)
		patch := []byte(`[{"op":"replace","path":"/port","value":9090}]`)
		if err := ApplyJSONPatchBytes(svc, patch); err != nil {
			t.Errorf("patch: %v", err)
		}
	}()

	// Concurrent marshal while patch is applying
	for i := 0; i < 1000; i++ {
		if _, err := Marshal(doc); err != nil {
			t.Fatalf("marshal: %v", err)
		}
	}
	<-done
}

func TestApplyJSONPatchArrayAddMinimalDiff(t *testing.T) {
	original := `service:
  envs:
    FEATURE_FLAG: 'true'
    SERVICE_URL: "https://example.internal/"
  externalSecretEnvs:
    - name: PRIMARY_PASSWORD
      path: data/apps/prod/service
      property: primary-password
    - name: CACHE_PASSWORD
      path: data/apps/prod/service
      property: cache-password
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	patch := mustDecodePatch(t, `[
{"op":"add","path":"/-","value":{"name":"EXTRA_SECRET","path":"data/shared/prod","property":"extra"}}
]`)

	if err := ApplyJSONPatchAtPath(doc, patch, []string{"service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPath: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	adds, removes := diffStats(diff)
	if adds > 3 || removes > 3 {
		t.Fatalf("expected localized change, got %d additions / %d removals:\n%s", adds, removes, diff)
	}
	if !strings.Contains(string(out), "name: EXTRA_SECRET") {
		t.Fatalf("new secret missing:\n%s", string(out))
	}
	if !strings.Contains(string(out), "SERVICE_URL: \"https://example.internal/\"") {
		t.Fatalf("env block modified:\n%s", string(out))
	}
}

func TestApplyJSONPatchArrayReplaceEntry(t *testing.T) {
	original := `service:
  envs:
    FEATURE_FLAG: "true"
  externalSecretEnvs:
    - name: TARGET
      path: data/apps/prod-old
      property: target-old
    - name: OTHER
      path: data/apps/prod
      property: other
  notes: keep-me
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	records := map[string]map[string]any{
		"TARGET": {"path": "data/apps/prod-old", "property": "target-old"},
		"OTHER":  {"path": "data/apps/prod", "property": "other"},
	}

	next := cloneRecords(records)
	next["TARGET"] = map[string]any{"path": "data/apps/prod", "property": "target-new"}

	order := extractArrayOrder(doc, []string{"service", "externalSecretEnvs"}, "name")
	arrayJSON, err := buildArrayJSON(next, order, "name", []string{"path", "property"})
	if err != nil {
		t.Fatalf("buildArrayJSON: %v", err)
	}
	if err := applySequencePatch(doc, []string{"service", "externalSecretEnvs"}, "replace", arrayJSON); err != nil {
		t.Fatalf("applySequencePatch: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	adds, removes := diffStats(diff)
	if adds > 2 || removes > 2 {
		t.Fatalf("expected targeted change, got %d additions / %d removals:\n%s", adds, removes, diff)
	}
	if !strings.Contains(string(out), "property: target-new") {
		t.Fatalf("replacement missing:\n%s", string(out))
	}
	if !strings.Contains(string(out), "path: data/apps/prod") || strings.Contains(string(out), "path: data/apps/prod-old") {
		t.Fatalf("path not updated correctly:\n%s", string(out))
	}
	if !strings.Contains(string(out), "notes: keep-me") {
		t.Fatalf("unrelated sections changed:\n%s", string(out))
	}
}

func TestArrayItemAttributeEdit_ByIndex(t *testing.T) {
	original := `service:
  envs:
    FEATURE_FLAG: "true"
  externalSecretEnvs:
    - name: TARGET
      path: data/apps/prod-old
      property: target-old
    - name: OTHER
      path: data/apps/prod
      property: other
  notes: keep-me
`
	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Replace ONLY the 'property' field of item at index 0 (TARGET)
	base := []string{"service", "externalSecretEnvs"}
	patch := []byte(`[{"op":"replace","path":"/0/property","value":"target-new"}]`)
	if err := ApplyJSONPatchAtPathBytes(doc, patch, base); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	adds, removes := diffStats(diff)

	// Single-line, targeted change expected
	if adds > 1 || removes > 1 {
		t.Fatalf("expected single-line change, got %d additions / %d removals:\n%s", adds, removes, diff)
	}
	if !strings.Contains(string(out), "property: target-new") {
		t.Fatalf("property not updated:\n%s", string(out))
	}
	// Make sure unrelated fields & quoting are untouched
	if getLineContaining(string(out), "FEATURE_FLAG:") != `    FEATURE_FLAG: "true"` {
		t.Fatalf("unrelated env changed:\n%s", string(out))
	}
	if !strings.Contains(string(out), "path: data/apps/prod-old") {
		t.Fatalf("path should remain old in this test:\n%s", string(out))
	}
	if !strings.Contains(string(out), "notes: keep-me") {
		t.Fatalf("unrelated section changed:\n%s", string(out))
	}
}

func TestArrayDeleteEntry_ByIndex_FallbackNoChurn(t *testing.T) {
	original := `service:
  envs:
    FEATURE_FLAG: "true"
  externalSecretEnvs:
    - name: TARGET
      path: data/apps/prod
      property: target
    - name: OTHER
      path: data/apps/prod
      property: other
  notes: keep-me
`
	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Remove the first array item (index 0). This triggers array fallback encode.
	base := []string{"service", "externalSecretEnvs"}
	patch := []byte(`[{"op":"remove","path":"/0"}]`)
	if err := ApplyJSONPatchAtPathBytes(doc, patch, base); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	s := string(out)
	// TARGET entry should be gone; OTHER should remain
	if strings.Contains(s, "name: TARGET") {
		t.Fatalf("TARGET should be removed:\n%s", s)
	}
	if !strings.Contains(s, "name: OTHER") {
		t.Fatalf("OTHER should remain:\n%s", s)
	}
	// Unrelated sections should remain byte-stable (esp. envs + notes)
	if getLineContaining(s, "FEATURE_FLAG:") != `    FEATURE_FLAG: "true"` {
		t.Fatalf("envs block churned:\n%s", s)
	}
	if !strings.Contains(s, "notes: keep-me") {
		t.Fatalf("notes section changed:\n%s", s)
	}

	diff := unifiedDiff(original, s)
	adds, removes := diffStats(diff)
	// Removing one 3-line item usually yields 0 additions and >=3 removals.
	if adds != 0 || removes < 3 {
		t.Fatalf("expected only removals for array deletion; got %d additions / %d removals:\n%s", adds, removes, diff)
	}
}

func TestInlineCommentWhitespacePreservedOnUnrelatedChange(t *testing.T) {
	in := []byte(`java-service:
  someField: 'value'  # this comment has 2 spaces before it
  anotherField: 'test'
  externalSecretEnvs:
    - name: EXISTING_VAR
      path: secret/path
      property: EXISTING_PROPERTY
`)
	doc, err := Parse(in)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}

	// Make a change to externalSecretEnvs (unrelated to someField)
	patch := mustDecodePatch(t, `[
		{"op":"add","path":"/-","value":{"name":"A","path":"ab","property":"a"}},
		{"op":"add","path":"/-","value":{"name":"B","path":"c","property":"c"}}
	]`)

	if err := ApplyJSONPatchAtPath(doc, patch, []string{"java-service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPath: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}

	// Verify the unrelated field's inline comment whitespace is preserved exactly
	before := getLineContaining(string(in), "someField:")
	after := getLineContaining(string(out), "someField:")
	if before != after {
		t.Fatalf("inline comment whitespace changed on unrelated field:\nBEFORE: %q\nAFTER:  %q\nfull output:\n%s", before, after, string(out))
	}

	// Also verify the comment still has 2 spaces (more explicit check)
	if after != "  someField: 'value'  # this comment has 2 spaces before it" {
		t.Fatalf("expected exact preservation of 2-space inline comment, got: %q\nfull output:\n%s", after, string(out))
	}
}

func TestMapDeleteEntry_Surgical(t *testing.T) {
	original := `service:
  config:
    timeout: 30  # seconds
    retries: 3 # attempts
  port: 8080
`
	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Delete a nested map key surgically.
	cfg := EnsurePath(doc, "service", "config")
	DeleteKey(cfg, "timeout")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	s := string(out)
	// timeout line should be gone, retries & port untouched
	if strings.Contains(s, "timeout:") {
		t.Fatalf("'timeout' should be removed:\n%s", s)
	}
	if getLineContaining(s, "retries:") != "    retries: 3 # attempts" {
		t.Fatalf("retries changed:\n%s", s)
	}
	if getLineContaining(s, "port:") != "  port: 8080" {
		t.Fatalf("port changed:\n%s", s)
	}

	diff := unifiedDiff(original, s)
	adds, removes := diffStats(diff)
	if adds != 0 || removes != 1 {
		t.Fatalf("expected a single-line surgical removal, got %d additions / %d removals:\n%s", adds, removes, diff)
	}
}

// TestArrayReplaceWithMultipleOps reproduces production issue: values get scrambled
// when we replace one entry, remove another, and add a new one
func TestArrayReplaceWithMultipleOps(t *testing.T) {
	original := `java-service:
  envs:
    ENABLE_CORE_TRANSACTION_CONSUMER: 'true'
    KAFKA_BROKERS: example.com:1234
  externalSecretEnvs:
    - name: POSTGRES_10_PASSWD
      path: test/app/prod/hk
      property: POSTGRES_10_PASSWD
    - name: POSTGRES_RO_PASSWORD
      path: test/app/prod/hk
      property: POSTGRES_RO_PASSWORD
    - name: LAUNCHDARKLY_KEY
      path: data/launchdarkly/prod
      property: CONTAINER
    - name: SECRET_TEMPORAL_CERT
      path: data/common
      property: TEMPORAL_CERT
    - name: KAFKA_CORE_BANKING_USER_PASSWORD
      path: data/kafka/user/prod
      property: core-banking_pwd
    - name: KAFKA_CORE_BANKING_USERNAME
      path: data/kafka/user/prod
      property: core-banking_user
    - name: TRUST_STORE_PASSWORD
      path: data/kafka/ssl/prod
      property: TRUSTSTORE_PASSWORD
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Simulate the operations from the production request:
	// 1. Replace KAFKA_CORE_BANKING_USERNAME
	// 2. Remove LAUNCHDARKLY_KEY
	// 3. Add A
	records := map[string]map[string]any{
		"POSTGRES_10_PASSWD":               {"path": "test/app/prod/hk", "property": "POSTGRES_10_PASSWD"},
		"POSTGRES_RO_PASSWORD":             {"path": "test/app/prod/hk", "property": "POSTGRES_RO_PASSWORD"},
		"SECRET_TEMPORAL_CERT":             {"path": "data/common", "property": "TEMPORAL_CERT"},
		"KAFKA_CORE_BANKING_USER_PASSWORD": {"path": "data/kafka/user/prod", "property": "core-banking_pwd"},
		"KAFKA_CORE_BANKING_USERNAME":      {"path": "data/kafka/user/pro", "property": "core-banking_use"}, // REPLACED
		"TRUST_STORE_PASSWORD":             {"path": "data/kafka/ssl/prod", "property": "TRUSTSTORE_PASSWORD"},
		"A":                                {"path": "A", "property": "A"}, // ADDED
		// LAUNCHDARKLY_KEY is REMOVED (not in map)
	}

	order := extractArrayOrder(doc, []string{"java-service", "externalSecretEnvs"}, "name")
	t.Logf("Original order: %v", order)

	arrayJSON, err := buildArrayJSON(records, order, "name", []string{"path", "property"})
	if err != nil {
		t.Fatalf("buildArrayJSON: %v", err)
	}
	t.Logf("Built JSON: %s", string(arrayJSON))

	if err := applySequencePatch(doc, []string{"java-service", "externalSecretEnvs"}, "replace", arrayJSON); err != nil {
		t.Fatalf("applySequencePatch: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	t.Logf("Diff:\n%s", diff)
	t.Logf("\n=== OUTPUT ===\n%s\n=== END ===", string(out))

	// Parse the output to verify correctness
	var result struct {
		JavaService struct {
			ExternalSecretEnvs []map[string]string `yaml:"externalSecretEnvs"`
		} `yaml:"java-service"`
	}
	if err := yaml.Unmarshal(out, &result); err != nil {
		t.Fatalf("unmarshal result: %v", err)
	}

	// Build a map for easier verification
	resultMap := make(map[string]map[string]string)
	for _, item := range result.JavaService.ExternalSecretEnvs {
		name := item["name"]
		resultMap[name] = item
	}

	t.Logf("Result map: %v", resultMap)

	// Verify KAFKA_CORE_BANKING_USERNAME was updated correctly
	if entry, ok := resultMap["KAFKA_CORE_BANKING_USERNAME"]; ok {
		if entry["path"] != "data/kafka/user/pro" {
			t.Errorf("KAFKA_CORE_BANKING_USERNAME path: expected 'data/kafka/user/pro', got '%s'", entry["path"])
		}
		if entry["property"] != "core-banking_use" {
			t.Errorf("KAFKA_CORE_BANKING_USERNAME property: expected 'core-banking_use', got '%s'", entry["property"])
		}
	} else {
		t.Errorf("KAFKA_CORE_BANKING_USERNAME not found in result")
	}

	// Verify LAUNCHDARKLY_KEY was removed
	if _, exists := resultMap["LAUNCHDARKLY_KEY"]; exists {
		t.Errorf("LAUNCHDARKLY_KEY should have been removed, but still exists: %v", resultMap["LAUNCHDARKLY_KEY"])
	}

	// Verify A was added
	if entry, ok := resultMap["A"]; ok {
		if entry["path"] != "A" {
			t.Errorf("A path: expected 'A', got '%s'", entry["path"])
		}
		if entry["property"] != "A" {
			t.Errorf("A property: expected 'A', got '%s'", entry["property"])
		}
	} else {
		t.Errorf("A not found in result")
	}

	// Verify other entries are unchanged
	expectedUnchanged := map[string]map[string]string{
		"POSTGRES_10_PASSWD":               {"path": "test/app/prod/hk", "property": "POSTGRES_10_PASSWD"},
		"POSTGRES_RO_PASSWORD":             {"path": "test/app/prod/hk", "property": "POSTGRES_RO_PASSWORD"},
		"SECRET_TEMPORAL_CERT":             {"path": "data/common", "property": "TEMPORAL_CERT"},
		"KAFKA_CORE_BANKING_USER_PASSWORD": {"path": "data/kafka/user/prod", "property": "core-banking_pwd"},
		"TRUST_STORE_PASSWORD":             {"path": "data/kafka/ssl/prod", "property": "TRUSTSTORE_PASSWORD"},
	}

	for name, expected := range expectedUnchanged {
		if entry, ok := resultMap[name]; ok {
			if entry["path"] != expected["path"] {
				t.Errorf("%s path: expected '%s', got '%s'", name, expected["path"], entry["path"])
			}
			if entry["property"] != expected["property"] {
				t.Errorf("%s property: expected '%s', got '%s'", name, expected["property"], entry["property"])
			}
		} else {
			t.Errorf("%s not found in result", name)
		}
	}

	// Verify total count
	expectedCount := 7 // 7 original - 1 removed (LAUNCHDARKLY) + 1 added (A)
	if len(resultMap) != expectedCount {
		t.Errorf("Expected %d entries, got %d. Entries: %v", expectedCount, len(resultMap), getMapKeys(resultMap))
	}
}

func getMapKeys(m map[string]map[string]string) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}

// TestArrayReplacePreservesInlineComments reproduces the failing comment preservation test
// Checks if inline comments between array items are preserved when replacing array
func TestArrayReplacePreservesInlineComments(t *testing.T) {
	original := `# top comment
java-service:
  # external secrets comment
  externalSecretEnvs:
    - name: BAR
      path: bar/path
      property: BAR_PROP
    # mid comment
    - name: FOO
      path: foo/path
      property: FOO_PROP
  otherField: untouched
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Simulate the operations:
	// 1. Replace FOO/path with "foo/updated"
	// 2. Add NEW
	records := map[string]map[string]any{
		"BAR": {"path": "bar/path", "property": "BAR_PROP"},
		"FOO": {"path": "foo/updated", "property": "FOO_PROP"}, // REPLACED
		"NEW": {"path": "new/path", "property": "NEW_PROP"},    // ADDED
	}

	order := extractArrayOrder(doc, []string{"java-service", "externalSecretEnvs"}, "name")
	t.Logf("Original order: %v", order)

	arrayJSON, err := buildArrayJSON(records, order, "name", []string{"path", "property"})
	if err != nil {
		t.Fatalf("buildArrayJSON: %v", err)
	}
	t.Logf("Built JSON: %s", string(arrayJSON))

	if err := applySequencePatch(doc, []string{"java-service", "externalSecretEnvs"}, "replace", arrayJSON); err != nil {
		t.Fatalf("applySequencePatch: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	diff := unifiedDiff(original, string(out))
	t.Logf("Diff:\n%s", diff)
	t.Logf("\n=== OUTPUT ===\n%s\n=== END ===", string(out))

	updatedStr := string(out)

	// Verify top-level comment is preserved
	if !strings.Contains(updatedStr, "# top comment") {
		t.Errorf("top-level comment lost:\n%s", updatedStr)
	}

	// Verify array leading comment is preserved
	if !strings.Contains(updatedStr, "# external secrets comment") {
		t.Errorf("array leading comment lost:\n%s", updatedStr)
	}

	// Verify inline array comment is preserved (THIS IS THE FAILING CHECK)
	if !strings.Contains(updatedStr, "# mid comment") {
		t.Errorf("inline array comment lost:\n%s", updatedStr)
	}

	// Verify unrelated field is untouched
	if !strings.Contains(updatedStr, "otherField: untouched") {
		t.Errorf("unrelated fields altered:\n%s", updatedStr)
	}

	// Verify new record was added
	if !strings.Contains(updatedStr, "name: NEW") {
		t.Errorf("new record not present:\n%s", updatedStr)
	}
}

// TestArrayOfScalars_EditPreserveCommentsMinimalDiff
// Expects surgical behavior & comment preservation on a sequence of scalars.
func TestArrayOfScalars_EditPreserveCommentsMinimalDiff(t *testing.T) {
	original := `service:
  ports:
    - 8080  # public
    - 9090  # admin
    - 10000
  note: "keep me"
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Replace the whole array value at basePath "service/ports":
	//  - change 9090 -> 9091
	//  - keep 8080 and 10000
	//  - append 11000
	base := []string{"service", "ports"}
	patch := []byte(`[
		{"op":"replace","path":"","value":[8080,9091,10000,11000]}
	]`)
	if err := ApplyJSONPatchAtPathBytes(doc, patch, base); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	s := string(out)

	// Expectation (DESIGNED TO FAIL CURRENTLY):
	// 1) Inter-item comments should be preserved
	if !strings.Contains(s, "# public") || !strings.Contains(s, "# admin") {
		t.Fatalf("expected inter-item comments to be preserved; got:\n%s", s)
	}
	// 2) Minimal churn: a couple of lines max (one changed for 9091 + one added for 11000)
	diff := unifiedDiff(original, s)
	adds, removes := diffStats(diff)
	if adds > 2 || removes > 1 {
		t.Fatalf("expected minimal diff for scalar array update; got %d additions / %d removals:\n%s", adds, removes, diff)
	}
	// 3) Unrelated fields untouched
	if getLineContaining(s, `note:`) != `  note: "keep me"` {
		t.Fatalf("unrelated field churned:\n%s", s)
	}
}

func TestScalarToMapping_FallbackMinimalChurn(t *testing.T) {
	original := `cfg:
  timeout: 30  # seconds
  name: app
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	cfg := EnsurePath(doc, "cfg")
	timeoutMap := EnsurePath(cfg, "timeout") // scalar -> mapping (shape change)
	SetScalarInt(timeoutMap, "hard", 60)

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	s := string(out)

	// 1) Semantics: timeout is now a mapping with hard: 60
	var round struct {
		Cfg struct {
			Timeout struct {
				Hard int `yaml:"hard"`
			} `yaml:"timeout"`
			Name string `yaml:"name"`
		} `yaml:"cfg"`
	}
	if err := yaml.Unmarshal(out, &round); err != nil {
		t.Fatalf("unmarshal: %v\n%s", err, s)
	}
	if round.Cfg.Timeout.Hard != 60 {
		t.Fatalf("timeout.hard = %d, want 60\n%s", round.Cfg.Timeout.Hard, s)
	}

	// 2) Comment preserved on the timeout key line
	timeoutLine := getLineContaining(s, "timeout:")
	if !strings.Contains(timeoutLine, "# seconds") {
		t.Fatalf("inline comment lost on timeout line:\n%s", s)
	}

	// 3) Unrelated line unchanged byte-for-byte
	if getLineContaining(s, "name:") != "  name: app" {
		t.Fatalf("unrelated line churned:\n%s", s)
	}

	// (Optional) 4) Diff is localized (don’t require single-line)
	diff := unifiedDiff(original, s)
	adds, removes := diffStats(diff)
	if adds < 1 || removes < 1 {
		t.Fatalf("expected at least one add and one removal due to shape change; got +%d/-%d\n%s", adds, removes, diff)
	}
}

// TestArrayReplacePreservesDoubleQuotedUnrelatedFields tests that replacing an array
// does not remove double quotes from unrelated string fields in sibling mappings.
// This reproduces a bug where instrumentation.instanceOverride: "value" loses its quotes
// when externalSecretEnvs array is replaced.
func TestArrayReplacePreservesDoubleQuotedUnrelatedFields(t *testing.T) {
	original := `java-service:
  cpu: 800
  memory: 4096
  kafkaSslTrustStore: true
  useKafkaCredentials: true
  instrumentation:
    instanceOverride: "my-instrumentation-1-32-0"
  externalSecretEnvs:
    - name: EXISTING_SECRET
      path: secret/existing
      property: EXISTING_PROP
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Add a new secret to the externalSecretEnvs array
	records := map[string]map[string]any{
		"EXISTING_SECRET": {"path": "secret/existing", "property": "EXISTING_PROP"},
		"NEW_SECRET":      {"path": "secret/new", "property": "NEW_PROP"},
	}

	order := extractArrayOrder(doc, []string{"java-service", "externalSecretEnvs"}, "name")
	arrayJSON, err := buildArrayJSON(records, order, "name", []string{"path", "property"})
	if err != nil {
		t.Fatalf("buildArrayJSON: %v", err)
	}

	if err := applySequencePatch(doc, []string{"java-service", "externalSecretEnvs"}, "replace", arrayJSON); err != nil {
		t.Fatalf("applySequencePatch: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	updatedStr := string(out)
	t.Logf("Updated YAML:\n%s", updatedStr)

	// The critical check: instrumentation.instanceOverride should still be double-quoted
	instanceOverrideLine := getLineContaining(updatedStr, "instanceOverride:")
	t.Logf("instanceOverride line: %q", instanceOverrideLine)

	if !strings.Contains(instanceOverrideLine, `"my-instrumentation-1-32-0"`) {
		t.Errorf("Expected instanceOverride to remain double-quoted as \"my-instrumentation-1-32-0\", but got: %q", instanceOverrideLine)
		t.Errorf("Full updated YAML:\n%s", updatedStr)
	}

	// Verify the array change was applied
	if !strings.Contains(updatedStr, "name: NEW_SECRET") {
		t.Errorf("Expected NEW_SECRET to be added")
	}

	// Verify other unrelated fields are unchanged
	if !strings.Contains(updatedStr, "cpu: 800") {
		t.Errorf("cpu field changed unexpectedly")
	}
	if !strings.Contains(updatedStr, "kafkaSslTrustStore: true") {
		t.Errorf("kafkaSslTrustStore field changed unexpectedly")
	}
}

// TestParseMarshalPreservesDoubleQuotedStrings is a minimal test that just parses
// and marshals without any changes. This tests if yamledit preserves double quotes
// during a basic parse/marshal cycle.
func TestParseMarshalPreservesDoubleQuotedStrings(t *testing.T) {
	original := `java-service:
  cpu: 800
  memory: 4096
  instrumentation:
    instanceOverride: "my-instrumentation-1-32-0"
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	updatedStr := string(out)
	t.Logf("After Parse/Marshal:\n%s", updatedStr)

	// Check if double quotes are preserved on the instanceOverride field
	instanceOverrideLine := getLineContaining(updatedStr, "instanceOverride:")
	t.Logf("instanceOverride line: %q", instanceOverrideLine)

	if !strings.Contains(instanceOverrideLine, `"my-instrumentation-1-32-0"`) {
		t.Errorf("Expected instanceOverride to remain double-quoted as \"my-instrumentation-1-32-0\", but got: %q", instanceOverrideLine)
		t.Errorf("Full YAML after parse/marshal:\n%s", updatedStr)
	}
}

// TestApplyJSONPatchAtPathBytesPreservesDoubleQuotes tests if ApplyJSONPatchAtPathBytes
// preserves double quotes in unrelated fields when applying a patch to an array.
func TestApplyJSONPatchAtPathBytesPreservesDoubleQuotes(t *testing.T) {
	original := `java-service:
  cpu: 800
  memory: 4096
  instrumentation:
    instanceOverride: "my-instrumentation-1-32-0"
  externalSecretEnvs:
    - name: EXISTING_SECRET
      path: secret/existing
      property: EXISTING_PROP
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Apply a JSON patch to replace the entire array
	patch := []byte(`[
		{
			"op":"replace",
			"path":"",
			"value":[
				{"name":"EXISTING_SECRET","path":"secret/existing","property":"EXISTING_PROP"},
				{"name":"NEW_SECRET","path":"secret/new","property":"NEW_PROP"}
			]
		}
	]`)

	if err := ApplyJSONPatchAtPathBytes(doc, patch, []string{"java-service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	updatedStr := string(out)
	t.Logf("After applying patch:\n%s", updatedStr)

	// The critical check: instrumentation.instanceOverride should still be double-quoted
	instanceOverrideLine := getLineContaining(updatedStr, "instanceOverride:")
	t.Logf("instanceOverride line: %q", instanceOverrideLine)

	if !strings.Contains(instanceOverrideLine, `"my-instrumentation-1-32-0"`) {
		t.Errorf("Expected instanceOverride to remain double-quoted as \"my-instrumentation-1-32-0\", but got: %q", instanceOverrideLine)
		t.Errorf("Full updated YAML:\n%s", updatedStr)
	}

	// Verify the patch was applied
	if !strings.Contains(updatedStr, "name: NEW_SECRET") {
		t.Errorf("Expected NEW_SECRET to be added")
	}
}

// TestCreateArrayThenAddItemPreservesQuotes mimics the exact flow of the accessor:
// 1. Start with YAML that has no externalSecretEnvs array
// 2. Create an empty array
// 3. Add an item to the array
// This should preserve quotes in unrelated fields.
func TestCreateArrayThenAddItemPreservesQuotes(t *testing.T) {
	original := `java-service:
  cpu: 800
  memory: 4096
  instrumentation:
    instanceOverride: "my-instrumentation-1-32-0"
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Step 1: Create empty array (like the accessor does)
	parentNode := EnsurePath(doc, "java-service")
	emptyArrayPatch := []byte(`[{"op":"add","path":"/externalSecretEnvs","value":[]}]`)
	if err := ApplyJSONPatchBytes(parentNode, emptyArrayPatch); err != nil {
		t.Fatalf("Create empty array: %v", err)
	}

	// Step 2: Add an item to the array
	addItemPatch := []byte(`[{"op":"add","path":"/-","value":{"name":"MY_SECRET","path":"secret/path","property":"MY_PROPERTY"}}]`)
	if err := ApplyJSONPatchAtPathBytes(doc, addItemPatch, []string{"java-service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("Add item: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	updatedStr := string(out)
	t.Logf("After creating array and adding item:\n%s", updatedStr)

	// The critical check: instrumentation.instanceOverride should still be double-quoted
	instanceOverrideLine := getLineContaining(updatedStr, "instanceOverride:")
	t.Logf("instanceOverride line: %q", instanceOverrideLine)

	if !strings.Contains(instanceOverrideLine, `"my-instrumentation-1-32-0"`) {
		t.Errorf("Expected instanceOverride to remain double-quoted as \"my-instrumentation-1-32-0\", but got: %q", instanceOverrideLine)
		t.Errorf("Full updated YAML:\n%s", updatedStr)
	}

	// Verify the array was created and item was added
	if !strings.Contains(updatedStr, "externalSecretEnvs:") {
		t.Errorf("Expected externalSecretEnvs array to be created")
	}
	if !strings.Contains(updatedStr, "name: MY_SECRET") {
		t.Errorf("Expected MY_SECRET to be added")
	}
}

// TestArrayItemFormatting_DashOnSameLineAsFirstField verifies that when yamledit
// creates new array items via JSON patch, the dash "-" is on the same line as the
// first field, not on a separate line. This is the standard YAML formatting style.
//
// Expected format:
//
//   - name: VALUE
//     path: VALUE
//
// NOT:
//
//	-
//	  name: VALUE
//	  path: VALUE
func TestArrayItemFormatting_DashOnSameLineAsFirstField(t *testing.T) {
	// Initial YAML WITHOUT array (will be added fresh)
	original := `java-service:
  periodSeconds: 3
  port: 8080
  successThreshold: 1
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Apply a JSON patch to create an array with one item using ApplyJSONPatchAtPathBytes
	// This mimics how the accessor creates arrays
	arrayJSON := []byte(`[{"name":"A","path":"A","property":"A"}]`)
	patchOp := []struct {
		Op    string          `json:"op"`
		Path  string          `json:"path"`
		Value json.RawMessage `json:"value,omitempty"`
	}{
		{Op: "add", Path: "", Value: json.RawMessage(arrayJSON)},
	}
	patchBytes, err := json.Marshal(patchOp)
	if err != nil {
		t.Fatalf("Marshal patch: %v", err)
	}

	// Ensure parent path exists
	EnsurePath(doc, "java-service")

	// Apply the patch at the array path (will create the field)
	if err := ApplyJSONPatchAtPathBytes(doc, patchBytes, []string{"java-service", "externalSecretEnvs"}); err != nil {
		t.Fatalf("ApplyJSONPatchAtPathBytes: %v", err)
	}

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	updatedStr := string(out)
	t.Logf("Updated YAML:\n%s", updatedStr)

	// Check that the array item uses inline format (dash on same line as first field)
	// Expected: "  - <field>: <value>" (where <field> could be any field like path, property, name)
	// NOT: "  -" on one line followed by "    <field>: <value>" on the next line
	lines := strings.Split(updatedStr, "\n")

	var foundInlineArrayItem bool
	var foundBadFormatting bool
	var dashLineIdx int

	for i, line := range lines {
		trimmed := strings.TrimLeft(line, " \t")
		if trimmed == "-" {
			// Found a standalone dash - this is bad formatting
			foundBadFormatting = true
			dashLineIdx = i
			t.Logf("Found standalone dash at line %d: %q", i+1, line)
		}
		// Check for dash followed by any field (generic pattern: "- <word>:")
		if strings.Contains(line, "-") && strings.Contains(line, ":") {
			// Verify it's in the format "- <field>:" not just any line with both - and :
			dashIdx := strings.Index(line, "-")
			if dashIdx >= 0 && dashIdx < len(line)-1 {
				afterDash := line[dashIdx+1:]
				// After the dash, we should have whitespace then a field name followed by colon
				if len(afterDash) > 0 && afterDash[0] == ' ' {
					colonIdx := strings.Index(afterDash, ":")
					if colonIdx > 0 {
						foundInlineArrayItem = true
						t.Logf("Found correct inline format at line %d: %q", i+1, line)
					}
				}
			}
		}
	}

	if foundBadFormatting {
		t.Errorf("YAML array item has dash on separate line (bad formatting)")
		t.Errorf("Line %d: %q", dashLineIdx+1, lines[dashLineIdx])
		if dashLineIdx+1 < len(lines) {
			t.Errorf("Line %d: %q", dashLineIdx+2, lines[dashLineIdx+1])
		}
		t.Errorf("Expected format: '  - <field>: <value>' (dash and field on same line)")
		t.Errorf("Got format: '  -' followed by '    <field>: <value>' (dash on separate line)")
	}

	if !foundInlineArrayItem && !foundBadFormatting {
		t.Errorf("Could not find inline array item in output YAML")
		t.Errorf("Full YAML:\n%s", updatedStr)
	}

	if !foundBadFormatting && foundInlineArrayItem {
		t.Logf("✓ Array formatting is correct (dash on same line as first field)")
	}
}

// TestArrayDeletion_RemovesAllLines verifies that when deleting an array field
// using DeleteKey, ALL lines of the array are removed, not just some.
//
// This reproduces a bug where deleting array fields leaves orphaned lines:
//   - The array field key and first item's dash may be deleted
//   - But subsequent field lines (path:, property:) remain as orphaned content
//
// Expected: All array content should be removed
// Bug: Only partial deletion, leaving malformed YAML
func TestArrayDeletion_RemovesAllLines(t *testing.T) {
	// Initial YAML WITH an array containing multiple items
	original := `java-service:
  periodSeconds: 3
  port: 8080
  successThreshold: 1
  externalSecretEnvs:
    - name: POSTGRES_10_PASSWD
      path: applications/data/myapp/staging/us
      property: POSTGRES_PASSWORD
    - name: POSTGRES_RO_PASSWORD
      path: applications/data/myapp/staging/us
      property: POSTGRES_RO_PASSWORD
  otherField: value
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Navigate to java-service node and delete the externalSecretEnvs field
	javaServiceNode := EnsurePath(doc, "java-service")
	DeleteKey(javaServiceNode, "externalSecretEnvs")

	// Marshal back to YAML
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	outputStr := string(out)
	t.Logf("Output YAML after deletion:\n%s", outputStr)

	// Check that externalSecretEnvs is completely gone
	if strings.Contains(outputStr, "externalSecretEnvs") {
		t.Errorf("Field 'externalSecretEnvs' should be completely deleted, but still appears in output")
	}

	// Check that NO orphaned array content remains
	lines := strings.Split(outputStr, "\n")
	for i, line := range lines {
		trimmed := strings.TrimLeft(line, " \t")

		// These should NOT appear (they were part of the deleted array)
		if strings.Contains(trimmed, "name: POSTGRES_10_PASSWD") {
			t.Errorf("Line %d: Found orphaned 'name: POSTGRES_10_PASSWD' after deleting externalSecretEnvs: %q", i+1, line)
		}
		if strings.Contains(trimmed, "name: POSTGRES_RO_PASSWORD") {
			t.Errorf("Line %d: Found orphaned 'name: POSTGRES_RO_PASSWORD' after deleting externalSecretEnvs: %q", i+1, line)
		}
		if strings.Contains(trimmed, "path: applications/data/") {
			t.Errorf("Line %d: Found orphaned 'path:' field after deleting externalSecretEnvs: %q", i+1, line)
		}
		if strings.Contains(trimmed, "property: POSTGRES_") {
			t.Errorf("Line %d: Found orphaned 'property:' field after deleting externalSecretEnvs: %q", i+1, line)
		}
	}

	// Verify other fields are preserved
	if !strings.Contains(outputStr, "periodSeconds: 3") {
		t.Errorf("Expected 'periodSeconds: 3' to be preserved")
	}
	if !strings.Contains(outputStr, "otherField: value") {
		t.Errorf("Expected 'otherField: value' to be preserved")
	}

	t.Logf("✓ Array deletion test complete")
}

// TestDeleteKey_PreservesInlineCommentWhitespace verifies that DeleteKey + Marshal
// preserves the exact whitespace before inline comments in unrelated fields.
// This reproduces a bug where deleting one field normalizes comment whitespace in other fields.
func TestDeleteKey_PreservesInlineCommentWhitespace(t *testing.T) {
	// YAML with a field that has 2 spaces before its inline comment
	original := `service:
  config:
    field1: 'value1'
    field2: 'value2'  # this comment has 2 spaces before the hash
    field3: 'value3'
  arrayField:
    - item1
    - item2
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Delete arrayField (simulates cascade deletion scenario)
	serviceNode := EnsurePath(doc, "service")
	DeleteKey(serviceNode, "arrayField")

	// Marshal back
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	outputStr := string(out)
	t.Logf("Output YAML:\n%s", outputStr)

	// Check if original bytes are preserved (byte surgery succeeded)
	if strings.Contains(string(out), "'value2'  #") {
		t.Logf("✓ Byte surgery succeeded - whitespace preserved")
	} else {
		t.Logf("✗ Fell back to yaml encoder - whitespace normalized")
	}

	// Find the line with field2
	lines := strings.Split(outputStr, "\n")
	var field2Line string
	for _, line := range lines {
		if strings.Contains(line, "field2") {
			field2Line = line
			break
		}
	}

	if field2Line == "" {
		t.Fatalf("Could not find field2 line in output")
	}

	t.Logf("field2 line: %q", field2Line)

	// Check that there are still 2 spaces before the # comment
	if !strings.Contains(field2Line, "'value2'  #") {
		t.Errorf("Expected 2 spaces before '#' in comment, but got: %q", field2Line)

		// Count spaces to report
		if strings.Contains(field2Line, "'value2' #") {
			t.Errorf("Comment whitespace was normalized from 2 spaces to 1 space")
		}
	}
}

// TestDeleteKey_PreservesInlineCommentWhitespace2 verifies that DeleteKey + Marshal
// preserves the exact whitespace before inline comments in unrelated fields.
// This reproduces a bug where deleting one field normalizes comment whitespace in other fields.
func TestDeleteKey_PreservesInlineCommentWhitespace2(t *testing.T) {
	// YAML with a field that has 2 spaces before its inline comment
	original := `service:
  config:
    field1: 'value1'
    field2: 'value2'  # this comment has 2 spaces before the hash
    field3: 'value3'
  arrayField:
    - item1
    - item2
`

	doc, err := Parse([]byte(original))
	if err != nil {
		t.Fatalf("Parse: %v", err)
	}

	// Delete arrayField
	patch, err := jsonpatch.DecodePatch([]byte(`[
		{"op":"remove","path":"/arrayField"}
	]`))
	if err != nil {
		t.Fatalf("decode patch: %v", err)
	}
	if err := ApplyJSONPatchAtPath(doc, patch, []string{"service"}); err != nil {
		t.Fatalf("PatchData error: %v", err)
	}

	// Marshal back
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}

	outputStr := string(out)
	t.Logf("Output YAML:\n%s", outputStr)

	// Check if original bytes are preserved (byte surgery succeeded)
	if strings.Contains(string(out), "'value2'  #") {
		t.Logf("✓ Byte surgery succeeded - whitespace preserved")
	} else {
		t.Logf("✗ Fell back to yaml encoder - whitespace normalized")
	}

	// Find the line with field2
	lines := strings.Split(outputStr, "\n")
	var field2Line string
	for _, line := range lines {
		if strings.Contains(line, "field2") {
			field2Line = line
			break
		}
	}

	if field2Line == "" {
		t.Fatalf("Could not find field2 line in output")
	}

	t.Logf("field2 line: %q", field2Line)

	// Check that there are still 2 spaces before the # comment
	if !strings.Contains(field2Line, "'value2'  #") {
		t.Errorf("Expected 2 spaces before '#' in comment, but got: %q", field2Line)

		// Count spaces to report
		if strings.Contains(field2Line, "'value2' #") {
			t.Errorf("Comment whitespace was normalized from 2 spaces to 1 space")
		}
	}
}

// TestNoTrailingNewlineCharacterDuplication reproduces a bug where Parse + Marshal
// duplicates the last character when the input YAML has no trailing newline.
//
// Bug: When input ends without '\n', the last character gets duplicated:
//
//	Input:  "property: SOME_PASSWORD" (no trailing newline, ends with 'D')
//	Output: "property: SOME_PASSWORDD" (extra 'D' appended!)
//
// This causes git diffs to show unintended modifications to the last line.
func TestNoTrailingNewlineCharacterDuplication(t *testing.T) {
	// YAML WITHOUT trailing newline - last char is 'D' from PASSWORD
	yamlWithoutNewline := []byte(`service:
  envs:
    FOO: bar
  externalSecretEnvs:
    - name: SECRET_A
      path: secret/path/a
      property: SOME_PASSWORD`)

	// Verify no trailing newline
	if len(yamlWithoutNewline) > 0 && yamlWithoutNewline[len(yamlWithoutNewline)-1] == '\n' {
		t.Fatalf("Test setup error: input should not have trailing newline")
	}
	lastChar := yamlWithoutNewline[len(yamlWithoutNewline)-1]
	t.Logf("Input size: %d bytes, last char: %q", len(yamlWithoutNewline), lastChar)

	// Parse the YAML
	doc, err := Parse(yamlWithoutNewline)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	// Add a new field (e.g., replicas: 2) to the service node
	serviceNode := EnsurePath(doc, "service")
	SetScalarInt(serviceNode, "replicas", 2)

	// Marshal back
	output, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	outputStr := string(output)
	t.Logf("Output YAML:\n%s", outputStr)

	// BUG CHECK: Verify the last character is NOT duplicated
	buggyText := "property: SOME_PASSWORD" + string(lastChar) // Would be "SOME_PASSWORDD"
	if strings.Contains(outputStr, buggyText) {
		t.Errorf("BUG REPRODUCED: Last character %q was duplicated!", lastChar)
		t.Errorf("Expected: 'property: SOME_PASSWORD'")
		t.Errorf("Found:    'property: SOME_PASSWORD%c'", lastChar)
		t.Errorf("This causes git diff to incorrectly show the last line as modified")
	}

	// Verify the new field was added
	if !strings.Contains(outputStr, "replicas: 2") {
		t.Errorf("Expected 'replicas: 2' to be added")
	}

	// Verify YAML is valid
	var check map[string]any
	if err := yaml.Unmarshal(output, &check); err != nil {
		t.Errorf("Output is not valid YAML: %v", err)
	}
}

// deleting a folded scalar currently leaves dangling lines that break YAML parsing.
func TestDeleteKey_FoldedScalarLeavesValidYaml(t *testing.T) {
	input := []byte(`app:
  envs:
    FOLDED_VALUE: >
      line-one,
      line-two
    KEEP_ME: "ok"
`)

	doc, err := Parse(input)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	envs := EnsurePath(doc, "app", "envs")
	DeleteKey(envs, "FOLDED_VALUE")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	var parsed map[string]any
	if err := yaml.Unmarshal(out, &parsed); err != nil {
		t.Fatalf("YAML became invalid after DeleteKey: %v\ncontent:\n%s", err, string(out))
	}
	if strings.Contains(string(out), "FOLDED_VALUE") {
		t.Fatalf("folded key should be removed:\n%s", string(out))
	}
	envsMap, _ := parsed["app"].(map[string]any)["envs"].(map[string]any)
	if _, ok := envsMap["KEEP_ME"]; !ok {
		t.Fatalf("KEEP_ME should remain, got: %v", envsMap)
	}
}

// adding an unrelated key leaves dangling lines that break YAML parsing.
func TestAddUnrelatedKey_FoldedScalarLeavesValidYaml(t *testing.T) {
	input := []byte(`app:
  envs:
    FOLDED_VALUE: >
      line-one,
      line-two
    KEEP_ME: "ok"
`)

	doc, err := Parse(input)
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	envs := EnsurePath(doc, "app", "envs")
	SetScalarString(envs, "NEW_VALUE", "new")

	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal error: %v", err)
	}

	var parsed map[string]any
	if err := yaml.Unmarshal(out, &parsed); err != nil {
		t.Fatalf("YAML became invalid after DeleteKey: %v\ncontent:\n%s", err, string(out))
	}
}

func TestReproMapReplacementCorruption(t *testing.T) {
	// This input simulates the structure where a map (envs) is followed by a list (externalSecretEnvs).
	// The indentation levels are key here.
	input := `java-service:
  envs:
    OLD_KEY: old_val
  externalSecretEnvs:
    - name: SECRET_1
      path: secret/path/1
    - name: SECRET_2
      path: secret/path/2
`

	// Payload to replace 'envs' with.
	// We add enough keys to change the size significantly.
	newEnvs := map[string]string{
		"NEW_KEY_1": "val1",
		"NEW_KEY_2": "val2",
		"NEW_KEY_3": "val3",
		"NEW_KEY_4": "val4",
		"NEW_KEY_5": "val5",
	}

	mapJSON, err := json.Marshal(newEnvs)
	require.NoError(t, err)

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	// Target path: /java-service/envs
	path := []string{"java-service", "envs"}

	// Construct a JSON Patch to REPLACE the 'envs' node
	type patchOp struct {
		Op    string          `json:"op"`
		Path  string          `json:"path"`
		Value json.RawMessage `json:"value,omitempty"`
	}
	ops := []patchOp{{Op: "replace", Path: "", Value: json.RawMessage(mapJSON)}}
	payload, _ := json.Marshal(ops)

	// Apply the patch
	err = ApplyJSONPatchAtPathBytes(doc, payload, path)
	require.NoError(t, err)

	// Marshal back to YAML
	output, err := Marshal(doc)
	require.NoError(t, err)

	t.Logf("Output YAML:\n%s", string(output))

	// Validation: The output should be valid YAML
	var data map[string]any
	err = yaml.Unmarshal(output, &data)
	assert.NoError(t, err, "Resulting YAML should be valid")

	// Validation: Check if externalSecretEnvs is intact
	js, ok := data["java-service"].(map[string]any)
	require.True(t, ok)

	_, hasSecrets := js["externalSecretEnvs"]
	assert.True(t, hasSecrets, "externalSecretEnvs should still exist")

	secrets, isList := js["externalSecretEnvs"].([]any)
	assert.True(t, isList, "externalSecretEnvs should be a list")
	assert.Equal(t, 2, len(secrets), "externalSecretEnvs should have 2 items")
}

// Regression: replacing an array (records accessor style) should not rewrite
// existing items when appending a new one. Currently this produces a diff with
// removals/rewrites (field order churn + misplaced comments).
func TestArrayReplaceAppendDoesNotChurnExistingItems(t *testing.T) {
	original := `app-chart:
  externalSecretEnvs:
    - path: path/alpha
      property: SECRET_ALPHA
      name: KEY_ALPHA
    - name: KEY_BETA
      property: SECRET_BETA
      # intentionally missing path to mimic partial data
    # region separator between clusters
    - name: KEY_GAMMA
      property: SECRET_GAMMA
      path: path/gamma
`

	doc, err := Parse([]byte(original))
	require.NoError(t, err)

	records := map[string]map[string]any{
		"KEY_ALPHA": {"property": "SECRET_ALPHA", "path": "path/alpha"},
		"KEY_BETA":  {"property": "SECRET_BETA"},
		"KEY_GAMMA": {"property": "SECRET_GAMMA", "path": "path/gamma"},
		// New item being appended
		"NEW_KEY": {"property": "NEW_SECRET", "path": "path/new"},
	}

	order := extractArrayOrder(doc, []string{"app-chart", "externalSecretEnvs"}, "name")
	arrayJSON, err := buildArrayJSON(records, order, "name", []string{"path", "property"})
	require.NoError(t, err)

	err = applySequencePatch(doc, []string{"app-chart", "externalSecretEnvs"}, "replace", arrayJSON)
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)

	diff := unifiedDiff(original, string(out))
	adds, removes := diffStats(diff)

	// Ideal: only the new item's lines are added (no deletions).
	if removes > 0 || adds > 6 { // allow a couple lines for blank/comment preservation
		t.Fatalf("array replace churned existing items (+%d/-%d):\n%s", adds, removes, diff)
	}
}

func TestFoldedScalarPreservedWhenAddingSiblingSequence(t *testing.T) {
	input := `app-chart:
  envs:
    FOO: >
        line1
        line2
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"add","path":"/externalSecretEnvs","value":[{"name":"S","path":"S"}]}
	]`)
	err = ApplyJSONPatchAtPathBytes(doc, patch, []string{"app-chart"})
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)

	expected := `app-chart:
  envs:
    FOO: >
        line1
        line2
  externalSecretEnvs:
    - name: S
      path: S
`

	if string(out) == string(input) {
		t.Fatalf("no change produced; test input should gain an externalSecretEnvs block")
	}
	assert.Equal(t, expected, string(out), "folded scalar should keep its line breaks when adding a sibling array")

	var round map[string]any
	require.NoError(t, yaml.Unmarshal(out, &round), "output should remain valid YAML")
}

func TestDeletingAllEnvKeysLeavesEmptyMap(t *testing.T) {
	input := `app-chart:
  cpu: 100
  envs:
    KAFKA_CDC_TOPIC: topic
    REGION: HK
  externalSecretEnvs:
    - name: A
      path: p1
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	envs := EnsurePath(doc, "app-chart", "envs")
	for _, k := range []string{
		"KAFKA_CDC_TOPIC",
		"REGION",
	} {
		DeleteKey(envs, k)
	}

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	var parsed map[string]any
	require.NoError(t, yaml.Unmarshal(out, &parsed))

	appChart, ok := parsed["app-chart"].(map[string]any)
	require.True(t, ok, "app-chart should be a map")

	envsVal, hasEnvs := appChart["envs"]
	require.True(t, hasEnvs, "envs key should remain present")
	if envsVal == nil {
		t.Fatalf("envs rendered as null/bare key; expected empty map. YAML:\n%s", s)
	}

	envsMap, ok := envsVal.(map[string]any)
	if !ok {
		t.Fatalf("envs should remain a mapping (empty map), got %T (%v)", envsVal, envsVal)
	}
	if len(envsMap) != 0 {
		t.Fatalf("envs should be empty after deleting all children; got %v", envsMap)
	}

	if strings.Contains(s, "envs:\n  externalSecretEnvs") {
		t.Fatalf("envs rendered as bare key with no value (invalid/ambiguous YAML):\n%s", s)
	}
	if !strings.Contains(s, "envs: {}") {
		t.Fatalf("expected YAML to render envs as empty mapping (envs: {}), got:\n%s", s)
	}
}

func TestRemovingAllArrayItemsLeavesEmptyArray(t *testing.T) {
	input := `app-chart:
  envs:
    REGION: HK
  externalSecretEnvs:
    - name: A
      path: p1
    - name: B
      path: p2
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"remove","path":"/0"},
		{"op":"remove","path":"/0"}
	]`)
	err = ApplyJSONPatchAtPathBytes(doc, patch, []string{"app-chart", "externalSecretEnvs"})
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	var parsed map[string]any
	require.NoError(t, yaml.Unmarshal(out, &parsed))

	appChart, ok := parsed["app-chart"].(map[string]any)
	require.True(t, ok)

	arrVal, hasArr := appChart["externalSecretEnvs"]
	require.True(t, hasArr, "externalSecretEnvs should remain present")
	if arrVal == nil {
		t.Fatalf("externalSecretEnvs rendered as null/bare key; expected empty array. YAML:\n%s", s)
	}
	arr, ok := arrVal.([]any)
	if !ok {
		t.Fatalf("externalSecretEnvs should remain a sequence (empty array), got %T (%v)", arrVal, arrVal)
	}
	if len(arr) != 0 {
		t.Fatalf("externalSecretEnvs should be empty after deleting all items; got %v", arr)
	}
	if strings.Contains(s, "externalSecretEnvs:\n  envs:") || strings.Contains(s, "externalSecretEnvs:\n  ") {
		t.Fatalf("externalSecretEnvs rendered as bare key with no value:\n%s", s)
	}
	if !strings.Contains(s, "externalSecretEnvs: []") {
		t.Fatalf("expected YAML to render externalSecretEnvs as empty array (externalSecretEnvs: []), got:\n%s", s)
	}
}

func TestEmptyMapThenDeleteSiblingSequenceDoesNotBecomeNull(t *testing.T) {
	input := `app-chart:
  envs:
    A: 1
    B: 2
  externalSecretEnvs:
    - name: A
      path: p1
    - name: B
      path: p2
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	envs := EnsurePath(doc, "app-chart", "envs")
	DeleteKey(envs, "A")
	DeleteKey(envs, "B")

	app := EnsurePath(doc, "app-chart")
	DeleteKey(app, "externalSecretEnvs")

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	var parsed map[string]any
	require.NoError(t, yaml.Unmarshal(out, &parsed))
	appChart, ok := parsed["app-chart"].(map[string]any)
	require.True(t, ok)

	envsVal, hasEnvs := appChart["envs"]
	require.True(t, hasEnvs, "envs key should remain present")
	if envsVal == nil {
		t.Fatalf("envs became null after deleting sibling sequence; expected empty map. YAML:\n%s", s)
	}
	envsMap, ok := envsVal.(map[string]any)
	if !ok {
		t.Fatalf("envs should be a map, got %T (%v)", envsVal, envsVal)
	}
	if len(envsMap) != 0 {
		t.Fatalf("envs should be empty, got %v", envsMap)
	}
	if strings.Contains(s, "envs:\n") && !strings.Contains(s, "envs: {}") {
		t.Fatalf("envs rendered as bare key instead of empty map:\n%s", s)
	}
	if strings.Contains(s, "envs: null") {
		t.Fatalf("envs became null after deleting sibling sequence:\n%s", s)
	}
	if strings.Contains(s, "externalSecretEnvs") {
		t.Fatalf("externalSecretEnvs should be deleted:\n%s", s)
	}
}

func TestEmptyEnvMapRoundTripDoesNotBecomeNull(t *testing.T) {
	input := `app-chart:
  envs:
    A: 1
    B: 2
  externalSecretEnvs:
    - name: A
      path: p1
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	envs := EnsurePath(doc, "app-chart", "envs")
	DeleteKey(envs, "A")
	DeleteKey(envs, "B")
	app := EnsurePath(doc, "app-chart")
	DeleteKey(app, "externalSecretEnvs")

	first, err := Marshal(doc)
	require.NoError(t, err)
	s1 := string(first)
	if strings.Contains(s1, "envs:\n") && !strings.Contains(s1, "envs: {}") {
		t.Fatalf("first marshal rendered bare envs key instead of empty map:\n%s", s1)
	}

	// Round-trip through Parse → Marshal (simulates a second run) should not turn envs into null.
	doc2, err := Parse(first)
	require.NoError(t, err)
	second, err := Marshal(doc2)
	require.NoError(t, err)
	s2 := string(second)
	if strings.Contains(s2, "envs: null") || strings.Contains(s2, "envs:\n") {
		t.Fatalf("empty envs map turned into null/bare after round-trip:\nFIRST:\n%s\nSECOND:\n%s", s1, s2)
	}
	if !strings.Contains(s2, "envs: {}") {
		t.Fatalf("expected envs to remain empty map after round-trip; got:\n%s", s2)
	}
}

func TestEmptyEnvMapDoesNotSerializeAsNull(t *testing.T) {
	input := `app-chart:
  envs:
`
	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	if strings.Contains(s, "envs:null") || strings.Contains(s, "envs: null") {
		t.Fatalf("empty env map serialized as null (envs:null):\n%s", s)
	}
	if !strings.Contains(s, "envs: {}") {
		t.Fatalf("expected empty env map to render as envs: {}, got:\n%s", s)
	}
}

func TestCommentBetweenKeysDiscardedWhenAllChildrenDeleted(t *testing.T) {
	input := `app-chart:
  envs:
    FOO: foo
    # note
    BAR: bar
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	envs := EnsurePath(doc, "app-chart", "envs")
	DeleteKey(envs, "FOO")
	DeleteKey(envs, "BAR")

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	// No stray comment left behind; envs should be an explicit empty map.
	if strings.Contains(s, "# note") {
		t.Fatalf("comment between deleted keys should be dropped when map becomes empty:\n%s", s)
	}
	if !strings.Contains(s, "envs: {}") {
		t.Fatalf("expected envs to render as empty map after deletions; got:\n%s", s)
	}
}

func TestArrayOfObjectsKeepsInnerCommentOnUpdate(t *testing.T) {
	input := `items:
  - name: A
    # inside
    value: 1
  - name: B
    value: 2
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"replace","path":"/0/value","value":10}
	]`)
	require.NoError(t, ApplyJSONPatchAtPathBytes(doc, patch, []string{"items"}))

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	if !strings.Contains(s, "# inside") {
		t.Fatalf("comment inside array item was lost on update:\n%s", s)
	}
	if !strings.Contains(s, "value: 10") {
		t.Fatalf("updated value missing:\n%s", s)
	}
}

func TestArrayOfObjectsDropsInnerCommentWhenItemDeleted(t *testing.T) {
	input := `items:
  - name: A
    # inside
    value: 1
  - name: B
    value: 2
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"remove","path":"/0"}
	]`)
	require.NoError(t, ApplyJSONPatchAtPathBytes(doc, patch, []string{"items"}))

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	if strings.Contains(s, "# inside") {
		t.Fatalf("comment belonging to deleted array item should not linger:\n%s", s)
	}
	if !strings.Contains(s, "- name: B") {
		t.Fatalf("remaining item missing:\n%s", s)
	}
}

func TestScalarArrayKeepsInlineCommentsOnReplace(t *testing.T) {
	input := `list:
  - one # a
  - two # b
  - three # c
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"replace","path":"/1","value":"TWO"}
	]`)
	require.NoError(t, ApplyJSONPatchAtPathBytes(doc, patch, []string{"list"}))

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	// Inline comments on untouched lines should remain
	if !strings.Contains(s, "one # a") || !strings.Contains(s, "three # c") {
		t.Fatalf("inline comments on untouched scalars lost:\n%s", s)
	}
	// Changed line keeps its comment
	if !strings.Contains(s, "TWO # b") {
		t.Fatalf("inline comment on replaced scalar lost:\n%s", s)
	}
}

// TestNestedListsConvertedToStringsWhenAddingField reproduces a bug where
// adding a new scalar field to a document corrupts nested list structures
// by converting them to flow-style string representations.
//
// Bug: When document contains nested lists like:
//
//	routes:
//	  - host: app.example.com
//	    paths:
//	      - /
//
// And we add a scalar field (e.g., replicas: 5), yamledit converts the nested
// paths list to a string:
//
//	paths: '[/]'
//
// Expected behavior: Lists should remain as block-style lists after modification.
func TestNestedListsConvertedToStringsWhenAddingField(t *testing.T) {
	input := `service:
  enabled: true
  routes:
    - host: app.example.com
      paths:
        - /
    - host: api.example.com
      paths:
        - /api
        - /v1
`

	doc, err := Parse([]byte(input))
	require.NoError(t, err)

	// Add a new scalar field "replicas: 5" to the service section
	// This simulates the real-world scenario where adding replicas corrupts lists
	serviceNode := EnsurePath(doc, "service")
	SetScalarInt(serviceNode, "replicas", 5)

	out, err := Marshal(doc)
	require.NoError(t, err)
	s := string(out)

	t.Logf("Output YAML:\n%s", s)

	// BUG CHECK: Verify paths lists are NOT converted to string representations
	if strings.Contains(s, "paths: '[/]'") || strings.Contains(s, `paths: "[/]"`) {
		t.Errorf("BUG REPRODUCED: paths list was converted to string '[/]'!")
		t.Errorf("Expected:\n  paths:\n    - /")
		t.Errorf("Found: paths: '[/]' (incorrect flow-style string)")
	}

	if strings.Contains(s, "paths: '[/api, /v1]'") || strings.Contains(s, `paths: "[/api, /v1]"`) {
		t.Errorf("BUG REPRODUCED: multi-item paths list was converted to string!")
		t.Errorf("Expected:\n  paths:\n    - /api\n    - /v1")
	}

	// Verify the list structure is preserved (should contain "- /" or "- /api")
	if !strings.Contains(s, "- /") {
		t.Errorf("Expected paths to remain as block-style list with '- /' format")
	}

	// Verify replicas was added correctly
	if !strings.Contains(s, "replicas: 5") {
		t.Errorf("Expected 'replicas: 5' to be added")
	}

	// Verify the output is valid YAML with correct types
	var parsed map[string]interface{}
	err = yaml.Unmarshal(out, &parsed)
	require.NoError(t, err, "Output should be valid YAML")

	// Navigate to service
	service, ok := parsed["service"].(map[string]interface{})
	require.True(t, ok, "service should be a map")

	// Verify replicas was set
	replicas, ok := service["replicas"].(int)
	require.True(t, ok, "replicas should be an int")
	assert.Equal(t, 5, replicas, "replicas should be 5")

	// Verify routes structure
	routes, ok := service["routes"].([]interface{})
	require.True(t, ok, "routes should be a list, got %T", service["routes"])
	require.Greater(t, len(routes), 0, "routes should have at least one item")

	// Verify first route has paths as a list (not string)
	route1, ok := routes[0].(map[string]interface{})
	require.True(t, ok, "route should be a map")

	paths, ok := route1["paths"]
	require.True(t, ok, "paths field should exist in route")

	// This is the critical check - paths should be a list, not a string
	pathsList, ok := paths.([]interface{})
	if !ok {
		t.Errorf("BUG CONFIRMED: paths is %T instead of []interface{}", paths)
		t.Errorf("paths value: %v", paths)
		t.Errorf("This means yamledit converted the list to a string representation")
		t.FailNow()
	}

	require.Greater(t, len(pathsList), 0, "paths list should have items")
	assert.Equal(t, "/", pathsList[0], "first path should be '/'")

	// Verify second route with multiple paths
	if len(routes) > 1 {
		route2, ok := routes[1].(map[string]interface{})
		require.True(t, ok, "second route should be a map")

		paths2, ok := route2["paths"]
		require.True(t, ok, "paths field should exist in second route")

		pathsList2, ok := paths2.([]interface{})
		if !ok {
			t.Errorf("BUG CONFIRMED: second route paths is %T instead of []interface{}", paths2)
			t.FailNow()
		}

		assert.Equal(t, 2, len(pathsList2), "second route should have 2 paths")
		assert.Equal(t, "/api", pathsList2[0], "first path should be '/api'")
		assert.Equal(t, "/v1", pathsList2[1], "second path should be '/v1'")
	}
}
