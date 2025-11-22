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
