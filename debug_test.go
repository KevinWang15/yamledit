package yamledit

import (
	"testing"

	"gopkg.in/yaml.v3"
)

// TestDebugNodeStructure helps understand where list corruption happens
func TestDebugNodeStructure(t *testing.T) {
	input := `service:
  enabled: true
  routes:
    - host: app.example.com
      paths:
        - /
`

	doc, err := Parse([]byte(input))
	if err != nil {
		t.Fatalf("Parse failed: %v", err)
	}

	// Print initial structure
	t.Log("=== INITIAL STRUCTURE ===")
	printNode(t, doc.Content[0], 0)

	// Check the ordered MapSlice before modification
	st, _ := lookup(doc)
	if st != nil {
		st.mu.RLock()
		t.Logf("\n=== INITIAL ORDERED MAPSLICE ===\n%#v", st.ordered)
		st.mu.RUnlock()
	}

	// Add replicas
	serviceNode := EnsurePath(doc, "service")
	SetScalarInt(serviceNode, "replicas", 5)

	// Print structure after modification
	t.Log("\n=== AFTER ADDING REPLICAS ===")
	printNode(t, doc.Content[0], 0)

	// Check the ordered MapSlice after modification
	if st != nil {
		st.mu.RLock()
		t.Logf("\n=== AFTER MODIFICATION ORDERED MAPSLICE ===\n%#v", st.ordered)
		st.mu.RUnlock()
	}

	// Check if surgery succeeded or fell back
	t.Log("\n=== ATTEMPTING MARSHAL ===")

	// Marshal and check
	out, err := Marshal(doc)
	if err != nil {
		t.Fatalf("Marshal failed: %v", err)
	}

	t.Logf("\n=== MARSHALED OUTPUT ===\n%s", string(out))

	// Check if paths are still sequences
	var parsed map[string]interface{}
	if err := yaml.Unmarshal(out, &parsed); err != nil {
		t.Fatalf("Unmarshal failed: %v", err)
	}

	service := parsed["service"].(map[string]interface{})
	routes := service["routes"].([]interface{})
	route := routes[0].(map[string]interface{})

	t.Logf("paths type: %T", route["paths"])
	t.Logf("paths value: %v", route["paths"])
}

func printNode(t *testing.T, n *yaml.Node, indent int) {
	if n == nil {
		return
	}
	prefix := ""
	for i := 0; i < indent; i++ {
		prefix += "  "
	}

	kindStr := ""
	switch n.Kind {
	case yaml.DocumentNode:
		kindStr = "Document"
	case yaml.MappingNode:
		kindStr = "Mapping"
	case yaml.SequenceNode:
		kindStr = "Sequence"
	case yaml.ScalarNode:
		kindStr = "Scalar"
	case yaml.AliasNode:
		kindStr = "Alias"
	}

	if n.Kind == yaml.ScalarNode {
		t.Logf("%s%s: %q (tag=%s)", prefix, kindStr, n.Value, n.Tag)
	} else {
		t.Logf("%s%s (tag=%s, len=%d)", prefix, kindStr, n.Tag, len(n.Content))
	}

	for i, child := range n.Content {
		t.Logf("%s[%d]:", prefix, i)
		printNode(t, child, indent+1)
	}
}
