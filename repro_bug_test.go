package yamledit

import (
	"encoding/json"
	"testing"

	"strings"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

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
