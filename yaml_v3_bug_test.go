package yamledit

import (
	"bytes"
	"testing"

	"gopkg.in/yaml.v3"
)

// TestYamlV3EncoderBug tests if gopkg.in/yaml.v3 encoder has a bug
// where modifying a mapping node causes nested sequences to be corrupted
func TestYamlV3EncoderBug(t *testing.T) {
	input := `service:
  enabled: true
  routes:
    - host: app.example.com
      paths:
        - /
`

	// Parse with yaml.v3
	var doc yaml.Node
	if err := yaml.Unmarshal([]byte(input), &doc); err != nil {
		t.Fatalf("Unmarshal failed: %v", err)
	}

	// Navigate to service mapping
	serviceMap := doc.Content[0]  // root mapping
	if serviceMap.Kind != yaml.MappingNode {
		t.Fatalf("Expected mapping node")
	}

	// Find the "service" key
	var serviceValue *yaml.Node
	for i := 0; i+1 < len(serviceMap.Content); i += 2 {
		key := serviceMap.Content[i]
		if key.Value == "service" {
			serviceValue = serviceMap.Content[i+1]
			break
		}
	}

	if serviceValue == nil || serviceValue.Kind != yaml.MappingNode {
		t.Fatalf("service not found or not a mapping")
	}

	// Add replicas: 5 to the service mapping
	keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "replicas"}
	valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: "5"}
	serviceValue.Content = append(serviceValue.Content, keyNode, valNode)

	// Encode back with yaml.v3
	var buf bytes.Buffer
	enc := yaml.NewEncoder(&buf)
	enc.SetIndent(2)
	if err := enc.Encode(&doc); err != nil {
		t.Fatalf("Encode failed: %v", err)
	}
	enc.Close()

	output := buf.String()
	t.Logf("Output:\n%s", output)

	// Check if paths are corrupted
	if bytes.Contains(buf.Bytes(), []byte("paths: '[/]'")) || bytes.Contains(buf.Bytes(), []byte(`paths: "[/]"`)) {
		t.Errorf("BUG CONFIRMED IN YAML.V3: paths list was converted to string '[/]'!")
	}

	// Verify it's valid and has correct types
	var parsed map[string]interface{}
	if err := yaml.Unmarshal(buf.Bytes(), &parsed); err != nil {
		t.Fatalf("Unmarshal output failed: %v", err)
	}

	service := parsed["service"].(map[string]interface{})
	routes := service["routes"].([]interface{})
	route := routes[0].(map[string]interface{})

	t.Logf("paths type: %T", route["paths"])
	if _, ok := route["paths"].([]interface{}); !ok {
		t.Errorf("paths should be a list, got %T: %v", route["paths"], route["paths"])
	}
}
