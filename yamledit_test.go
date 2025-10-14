package yamledit

import (
	"bytes"
	"strings"
	"testing"

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
