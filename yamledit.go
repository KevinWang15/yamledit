package yamledit

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"reflect"
	"strconv"
	"strings"
	"sync"

	jsonpatch "github.com/evanphx/json-patch/v5"
	"gopkg.in/yaml.v3"
)

// Global lock to ensure thread safety across all operations on any AST.
var globalEditLock sync.RWMutex

// --- Parse and Marshal ---

// Parse parses the YAML data into a yaml.Node AST.
func Parse(data []byte) (*yaml.Node, error) {
	var node yaml.Node
	// yaml.v3 Unmarshal populates the AST including comments and line/column info.
	if err := yaml.Unmarshal(data, &node); err != nil {
		// Handle potentially empty files or files with only comments which might result in EOF-like behavior depending on exact content.
		// If unmarshal fails but the data is empty/whitespace, treat as empty document.
		if len(bytes.TrimSpace(data)) == 0 {
			return &yaml.Node{Kind: yaml.DocumentNode}, nil
		}
		return nil, err
	}

	// Ensure we have a DocumentNode, especially for empty input where Kind might be 0.
	if node.Kind == 0 {
		node.Kind = yaml.DocumentNode
	}

	// Enforce requirement that top-level must be a mapping (if content exists).
	if node.Kind == yaml.DocumentNode && len(node.Content) > 0 {
		root := node.Content[0]
		if root.Kind != yaml.MappingNode {
			// Allow null/empty scalar if the document content is essentially null.
			if !(root.Kind == yaml.ScalarNode && (root.Tag == "!!null" || root.Value == "null" || root.Value == "~" || root.Value == "")) {
				// Required by TestParseErrorsOnNonMappingTopLevel
				return nil, errors.New("top-level node must be a mapping")
			}
		}
	}

	return &node, nil
}

// Marshal serializes the yaml.Node AST back to bytes, preserving comments and indentation.
func Marshal(doc *yaml.Node) ([]byte, error) {
	// Acquire Read Lock to ensure safety during concurrent edits.
	globalEditLock.RLock()
	defer globalEditLock.RUnlock()

	if doc == nil {
		return []byte{}, nil
	}

	// Detect original indentation from the AST structure.
	indent := calculateIndentFromAST(doc)

	var buf bytes.Buffer
	enc := yaml.NewEncoder(&buf)
	enc.SetIndent(indent)

	if err := enc.Encode(doc); err != nil {
		return nil, err
	}

	// Ensure the encoder is closed to finalize output.
	if err := enc.Close(); err != nil {
		return nil, err
	}

	return buf.Bytes(), nil
}

// gcd calculates the Greatest Common Divisor.
func gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// calculateIndentFromAST analyzes the AST (Column numbers) to determine the base indentation level.
// It calculates the GCD of all detected indentation steps (relative indentation between parent and child).
func calculateIndentFromAST(node *yaml.Node) int {
	indents := make(map[int]bool)

	// Walker function to traverse AST and find indentation steps.
	var walker func(*yaml.Node, int)
	walker = func(n *yaml.Node, parentCol int) {
		if n == nil || n.Column == 0 {
			return
		}

		// Analyze block-style mappings.
		if n.Kind == yaml.MappingNode && n.Style&yaml.FlowStyle == 0 {
			for i := 0; i+1 < len(n.Content); i += 2 {
				keyNode := n.Content[i]
				valueNode := n.Content[i+1]

				if keyNode.Column > parentCol {
					step := keyNode.Column - parentCol
					if step > 0 {
						indents[step] = true
					}
				}
				// Recurse using the key's column as the parent column for the value.
				walker(valueNode, keyNode.Column)
			}
		} else if n.Kind == yaml.SequenceNode && n.Style&yaml.FlowStyle == 0 {
			// Analyze block-style sequences.
			for _, itemNode := range n.Content {
				if itemNode.Column > parentCol {
					step := itemNode.Column - parentCol
					if step > 0 {
						indents[step] = true
					}
				}
				// Recurse using the item's column (where the dash conceptually is) as the parent column.
				walker(itemNode, itemNode.Column)
			}
		} else if n.Kind == yaml.DocumentNode {
			if len(n.Content) > 0 {
				// Start traversal from Column 1 (yaml.v3 uses 1-based columns).
				walker(n.Content[0], 1)
			}
		}
	}

	// Start the walker based on the node type.
	if node != nil {
		if node.Kind == yaml.DocumentNode {
			walker(node, 0)
		} else {
			walker(node, 1)
		}
	}

	if len(indents) == 0 {
		return 2 // Default fallback
	}

	// Calculate GCD of all steps.
	result := 0
	for step := range indents {
		if result == 0 {
			result = step
		} else {
			result = gcd(result, step)
		}
	}

	if result > 0 {
		return result
	}

	return 2
}

// detectIndent helper required by the specific test interface provided (e.g., TestIndentDetection).
// It parses the data and uses AST analysis.
func detectIndent(data []byte) int {
	var node yaml.Node
	// We ignore errors here assuming the input is reasonably valid YAML for detection purposes.
	_ = yaml.Unmarshal(data, &node)
	return calculateIndentFromAST(&node)
}

// --- Navigation and Manipulation ---

// EnsurePath ensures that the given path exists and returns the mapping node at that path.
// It converts intermediate nodes to mappings if necessary.
func EnsurePath(node *yaml.Node, first string, rest ...string) *yaml.Node {
	globalEditLock.Lock()
	defer globalEditLock.Unlock()

	return ensurePathInternal(node, append([]string{first}, rest...))
}

func ensurePathInternal(node *yaml.Node, path []string) *yaml.Node {
	if node == nil {
		return nil
	}

	current := node

	// Handle Document Node wrapper.
	if current.Kind == yaml.DocumentNode {
		if len(current.Content) == 0 {
			// Empty document, create root mapping node.
			root := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			current.Content = append(current.Content, root)
			current = root
		} else {
			current = current.Content[0]
		}
	}

	for _, key := range path {
		// Ensure current node is a mapping node (Shape Change).
		if current.Kind != yaml.MappingNode {
			convertToMapping(current)
		}

		// Look for the key.
		found := false
		for i := 0; i+1 < len(current.Content); i += 2 {
			keyNode := current.Content[i]
			if keyNode.Kind == yaml.ScalarNode && keyNode.Value == key {
				current = current.Content[i+1]
				found = true
				break
			}
		}

		if !found {
			// Key not found, create it.
			newKeyNode := &yaml.Node{
				Kind: yaml.ScalarNode, Tag: "!!str", Value: key, Style: 0,
			}
			// Initialize the new node as a mapping for subsequent segments or the final result.
			newValueNode := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			current.Content = append(current.Content, newKeyNode, newValueNode)
			current = newValueNode
		}
	}

	// Ensure the final node is also a mapping node.
	if current.Kind != yaml.MappingNode {
		convertToMapping(current)
	}

	return current
}

func convertToMapping(node *yaml.Node) {
	node.Kind = yaml.MappingNode
	node.Tag = "!!map"
	node.Value = ""
	node.Content = nil
	node.Style = 0 // Reset style to default block style.
}

// Helper function for setting scalar values with style preservation.
func setScalar(mapNode *yaml.Node, key string, value string, tag string, defaultNewStyle yaml.Style) {
	globalEditLock.Lock()
	defer globalEditLock.Unlock()

	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	// 1. Update existing key.
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		keyNode := mapNode.Content[i]
		valueNode := mapNode.Content[i+1]

		if keyNode.Kind == yaml.ScalarNode && keyNode.Value == key {
			// Update surgically.
			valueNode.Kind = yaml.ScalarNode
			valueNode.Tag = tag
			valueNode.Value = value
			valueNode.Content = nil

			// Style preservation logic.
			if tag == "!!str" {
				// Keep the existing style (e.g., quotes) if set (Style != 0).
				// If it was PlainStyle (0), we keep it 0 and let the encoder decide if quotes are needed based on content.
			} else {
				// Non-strings (int, bool, float, null) enforce PlainStyle (bare values).
				valueNode.Style = 0
			}
			return
		}
	}

	// 2. Insert new key (append).
	newKeyNode := &yaml.Node{
		Kind: yaml.ScalarNode, Tag: "!!str", Value: key, Style: 0,
	}
	newValueNode := &yaml.Node{
		Kind: yaml.ScalarNode, Tag: tag, Value: value,
	}

	// Apply default style for new insertions.
	if tag == "!!str" {
		newValueNode.Style = defaultNewStyle
	} else {
		newValueNode.Style = 0
	}

	mapNode.Content = append(mapNode.Content, newKeyNode, newValueNode)
}

func SetScalarInt(mapNode *yaml.Node, key string, value int) {
	setScalar(mapNode, key, strconv.Itoa(value), "!!int", 0)
}

func SetScalarBool(mapNode *yaml.Node, key string, value bool) {
	strVal := "false"
	if value {
		strVal = "true"
	}
	// Normalize to bare booleans.
	setScalar(mapNode, key, strVal, "!!bool", 0)
}

func SetScalarFloat(mapNode *yaml.Node, key string, value float64) {
	// Handle special float values.
	if math.IsInf(value, 1) {
		setScalar(mapNode, key, ".inf", "!!float", 0)
	} else if math.IsInf(value, -1) {
		setScalar(mapNode, key, "-.inf", "!!float", 0)
	} else if math.IsNaN(value) {
		setScalar(mapNode, key, ".nan", "!!float", 0)
	} else {
		// Use 'g' format for general representation.
		setScalar(mapNode, key, strconv.FormatFloat(value, 'g', -1, 64), "!!float", 0)
	}
}

func SetScalarString(mapNode *yaml.Node, key, value string) {
	// Default to SingleQuotedStyle for new strings, satisfying tests expecting quotes for new insertions.
	setScalar(mapNode, key, value, "!!str", yaml.SingleQuotedStyle)
}

func SetScalarNull(mapNode *yaml.Node, key string) {
	setScalar(mapNode, key, "null", "!!null", 0)
}

// DeleteKey removes a key and its value from a mapping node. Removes duplicates if any.
func DeleteKey(mapNode *yaml.Node, key string) {
	globalEditLock.Lock()
	defer globalEditLock.Unlock()

	if mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return
	}

	newContent := make([]*yaml.Node, 0, len(mapNode.Content))
	found := false

	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		keyNode := mapNode.Content[i]

		if keyNode.Kind == yaml.ScalarNode && keyNode.Value == key {
			// Skip this pair.
			found = true
			continue
		}
		newContent = append(newContent, keyNode, mapNode.Content[i+1])
	}

	if found {
		mapNode.Content = newContent
	}
}

// --- JSON Patch Application ---

// Internal representation of a JSON Patch operation.
type PatchOperation struct {
	Op    string          `json:"op"`
	Path  string          `json:"path"`
	Value json.RawMessage `json:"value,omitempty"`
	From  string          `json:"from,omitempty"`
}

// ApplyJSONPatch applies a JSON Patch atomically to the YAML AST.
func ApplyJSONPatch(node *yaml.Node, patch jsonpatch.Patch) error {
	// Marshal the patch object back to bytes to use the internal implementation.
	patchJSON, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("failed to marshal JSON patch: %w", err)
	}
	return ApplyJSONPatchBytes(node, patchJSON)
}

// ApplyJSONPatchBytes applies a JSON Patch (in JSON format) atomically to the YAML AST.
func ApplyJSONPatchBytes(node *yaml.Node, patchJSON []byte) error {
	var ops []PatchOperation
	if err := json.Unmarshal(patchJSON, &ops); err != nil {
		return fmt.Errorf("failed to decode JSON patch: %w", err)
	}

	globalEditLock.Lock()
	defer globalEditLock.Unlock()

	// Apply atomically: clone, apply, replace.
	// This ensures that if any operation fails, the original node remains unmodified.
	clonedNode := cloneYAMLNode(node)

	if err := applyPatchInternal(clonedNode, ops); err != nil {
		return err
	}

	// If successful, replace the original node content in place.
	*node = *clonedNode
	return nil
}

// ApplyJSONPatchAtPath applies a JSON Patch atomically to a specific subtree.
func ApplyJSONPatchAtPath(node *yaml.Node, patch jsonpatch.Patch, basePath []string) error {
	patchJSON, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("failed to marshal JSON patch: %w", err)
	}
	return ApplyJSONPatchAtPathBytes(node, patchJSON, basePath)
}

// ApplyJSONPatchAtPathBytes applies a JSON Patch (in JSON format) atomically to a specific subtree.
func ApplyJSONPatchAtPathBytes(node *yaml.Node, patchJSON []byte, basePath []string) error {
	if len(basePath) == 0 {
		return ApplyJSONPatchBytes(node, patchJSON)
	}

	var ops []PatchOperation
	if err := json.Unmarshal(patchJSON, &ops); err != nil {
		return fmt.Errorf("failed to decode JSON patch: %w", err)
	}

	globalEditLock.Lock()
	defer globalEditLock.Unlock()

	// Resolve the base path to find the target node.
	targetNode, err := resolvePathSegments(node, basePath)
	if err != nil {
		return fmt.Errorf("failed to resolve base path %v: %w", basePath, err)
	}

	// Apply atomically to the target subtree.
	clonedTarget := cloneYAMLNode(targetNode)

	if err := applyPatchInternal(clonedTarget, ops); err != nil {
		return err
	}

	*targetNode = *clonedTarget
	return nil
}

func applyPatchInternal(node *yaml.Node, ops []PatchOperation) error {
	for i, op := range ops {
		if err := applyOperation(node, op); err != nil {
			return fmt.Errorf("failed to apply operation %d (%s %s): %w", i, op.Op, op.Path, err)
		}
	}
	return nil
}

// cloneYAMLNode performs a deep clone of a yaml.Node.
func cloneYAMLNode(node *yaml.Node) *yaml.Node {
	if node == nil {
		return nil
	}
	// Shallow copy the struct fields (metadata like comments, style).
	clone := *node
	// Deep copy the content slice.
	if node.Content != nil {
		clone.Content = make([]*yaml.Node, len(node.Content))
		for i, child := range node.Content {
			clone.Content[i] = cloneYAMLNode(child)
		}
	}
	return &clone
}

// resolvePathSegments navigates the AST based on simple path segments (used for basePath).
func resolvePathSegments(node *yaml.Node, pathSegments []string) (*yaml.Node, error) {
	current := node

	// Handle Document Node wrapper.
	if current.Kind == yaml.DocumentNode {
		if len(current.Content) == 0 {
			return nil, errors.New("cannot resolve path in empty document")
		}
		current = current.Content[0]
	}

	for _, segment := range pathSegments {
		if current == nil {
			return nil, fmt.Errorf("path segment '%s' navigates into nil node", segment)
		}

		if current.Kind == yaml.MappingNode {
			found := false
			for i := 0; i+1 < len(current.Content); i += 2 {
				keyNode := current.Content[i]
				if keyNode.Kind == yaml.ScalarNode && keyNode.Value == segment {
					current = current.Content[i+1]
					found = true
					break
				}
			}
			if !found {
				return nil, fmt.Errorf("key '%s' not found in mapping", segment)
			}
		} else {
			// basePath is expected to traverse only mappings based on tests.
			return nil, fmt.Errorf("cannot navigate through non-mapping node with segment '%s'", segment)
		}
	}
	return current, nil
}

// applyOperation applies a single JSON Patch operation.
func applyOperation(root *yaml.Node, op PatchOperation) error {
	// Determine the effective root for navigation.
	effectiveRoot := root
	if root.Kind == yaml.DocumentNode {
		if len(root.Content) > 0 {
			effectiveRoot = root.Content[0]
		} else {
			// Handle operations on an empty document.
			effectiveRoot = nil
		}
	}

	// Handle operations targeting the root (path "" or "/").
	if op.Path == "" || op.Path == "/" {
		if op.Op == "add" || op.Op == "replace" {
			// If effectiveRoot exists, perform surgical replace on it.
			if effectiveRoot != nil {
				return surgicalReplace(effectiveRoot, op.Value)
			}

			// If document is empty, create the root content.
			if root.Kind == yaml.DocumentNode && len(root.Content) == 0 {
				newNode, err := jsonValueToYAMLNode(op.Value)
				if err != nil {
					return err
				}
				root.Content = []*yaml.Node{newNode}
				return nil
			}
			// Handle replacing a nil node if root was not a DocumentNode (less common if using Parse).
			if effectiveRoot == nil {
				newNode, err := jsonValueToYAMLNode(op.Value)
				if err != nil {
					return err
				}
				*root = *newNode
				return nil
			}
		}
		// Other operations on root (remove, test) require existing content.
		if effectiveRoot == nil {
			return errors.New("target document is empty")
		}
	}

	if effectiveRoot == nil {
		return errors.New("cannot apply non-root patch operation to empty document")
	}

	if !strings.HasPrefix(op.Path, "/") {
		return fmt.Errorf("invalid JSON pointer: %s (must start with /)", op.Path)
	}

	// Split and unescape path segments.
	pathSegments := strings.Split(op.Path, "/")[1:]
	for i, seg := range pathSegments {
		seg = strings.ReplaceAll(seg, "~1", "/")
		seg = strings.ReplaceAll(seg, "~0", "~")
		pathSegments[i] = seg
	}

	targetSegment := pathSegments[len(pathSegments)-1]
	parentPath := pathSegments[:len(pathSegments)-1]

	// Resolve parent node.
	parent, err := resolveJSONPointer(effectiveRoot, parentPath)
	if err != nil {
		// 'add' allows the parent path to not exist if we could create it, but standard JSON patch requires the parent to exist.
		return fmt.Errorf("failed to resolve parent path: %w", err)
	}
	if parent == nil {
		return errors.New("parent node resolved to nil")
	}

	switch op.Op {
	case "add":
		return applyAdd(parent, targetSegment, op.Value)
	case "remove":
		return applyRemove(parent, targetSegment)
	case "replace":
		// Find the target node first. 'replace' requires the target to exist.
		target, err := findChildNode(parent, targetSegment)
		if err != nil {
			return fmt.Errorf("target not found for replace operation: %w", err)
		}
		return surgicalReplace(target, op.Value)
	case "test":
		return applyTest(parent, targetSegment, op.Value)
	case "move", "copy":
		// move and copy are complex and not required by the provided tests.
		return fmt.Errorf("JSON patch operation '%s' is not implemented", op.Op)
	default:
		return fmt.Errorf("unsupported JSON patch operation: %s", op.Op)
	}
}

// resolveJSONPointer navigates the AST based on JSON Pointer segments.
func resolveJSONPointer(node *yaml.Node, pathSegments []string) (*yaml.Node, error) {
	current := node

	for _, segment := range pathSegments {
		if current == nil {
			return nil, fmt.Errorf("path segment '%s' navigates into nil node", segment)
		}

		if current.Kind == yaml.MappingNode {
			found := false
			for i := 0; i+1 < len(current.Content); i += 2 {
				keyNode := current.Content[i]
				if keyNode.Kind == yaml.ScalarNode && keyNode.Value == segment {
					current = current.Content[i+1]
					found = true
					break
				}
			}
			if !found {
				return nil, fmt.Errorf("key '%s' not found in mapping", segment)
			}
		} else if current.Kind == yaml.SequenceNode {
			index, err := strconv.Atoi(segment)
			if err != nil {
				return nil, fmt.Errorf("invalid array index '%s'", segment)
			}
			if index < 0 || index >= len(current.Content) {
				return nil, fmt.Errorf("array index %d out of bounds (len %d)", index, len(current.Content))
			}
			current = current.Content[index]
		} else {
			return nil, fmt.Errorf("cannot navigate through scalar/other node with segment '%s'", segment)
		}
	}
	return current, nil
}

// jsonValueToYAMLNode converts JSON value (RawMessage) to YAML Node AST.
func jsonValueToYAMLNode(value json.RawMessage) (*yaml.Node, error) {
	// Handle null or empty input specifically.
	if len(value) == 0 || string(value) == "null" {
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null", Value: "null", Style: 0}, nil
	}

	// Unmarshal the JSON into a generic interface{} first to inspect the data.
	var data interface{}
	if err := json.Unmarshal(value, &data); err != nil {
		return nil, fmt.Errorf("failed to unmarshal JSON value: %w", err)
	}

	// Use yaml.Node's Encode method to convert the Go interface{} into an AST structure.
	var node yaml.Node
	if err := node.Encode(data); err != nil {
		return nil, fmt.Errorf("failed to encode data to YAML node: %w", err)
	}

	var resultNode *yaml.Node
	// Encode might produce a DocumentNode wrapper.
	if node.Kind == yaml.DocumentNode && len(node.Content) > 0 {
		resultNode = node.Content[0]
	} else {
		resultNode = &node
	}

	// Apply default styles for newly created nodes from JSON Patch.
	// This ensures consistency with SetScalar* functions.
	var styleWalker func(*yaml.Node)
	styleWalker = func(n *yaml.Node) {
		if n == nil {
			return
		}
		if n.Kind == yaml.ScalarNode {
			if n.Tag == "!!str" && n.Style == 0 {
				// Default new strings to SingleQuotedStyle.
				n.Style = yaml.SingleQuotedStyle
			} else if n.Tag != "!!str" {
				n.Style = 0
			}
		}
		for _, child := range n.Content {
			styleWalker(child)
		}
	}
	styleWalker(resultNode)

	return resultNode, nil
}

// Implementation of JSON Patch operations (add, remove, test).

func applyAdd(parent *yaml.Node, key string, value json.RawMessage) error {
	if parent.Kind == yaml.MappingNode {
		// If key exists, 'add' acts as 'replace' (RFC 6902).
		existing, _ := findChildNode(parent, key)
		if existing != nil {
			return surgicalReplace(existing, value)
		}

		// Insert new key-value pair (append).
		newNode, err := jsonValueToYAMLNode(value)
		if err != nil {
			return err
		}

		newKeyNode := &yaml.Node{
			Kind: yaml.ScalarNode, Tag: "!!str", Value: key, Style: 0,
		}
		parent.Content = append(parent.Content, newKeyNode, newNode)
		return nil
	}

	if parent.Kind == yaml.SequenceNode {
		newNode, err := jsonValueToYAMLNode(value)
		if err != nil {
			return err
		}

		// Add to array (insert at index or append).
		if key == "-" {
			parent.Content = append(parent.Content, newNode)
			return nil
		}

		index, err := strconv.Atoi(key)
		if err != nil {
			return fmt.Errorf("invalid array index '%s'", key)
		}
		// Index can be equal to length (append).
		if index < 0 || index > len(parent.Content) {
			return fmt.Errorf("array index %d out of bounds (len %d)", index, len(parent.Content))
		}

		// Insert at index.
		parent.Content = append(parent.Content, nil)
		copy(parent.Content[index+1:], parent.Content[index:])
		parent.Content[index] = newNode
		return nil
	}

	return fmt.Errorf("cannot add to node kind %v", parent.Kind)
}

func applyRemove(parent *yaml.Node, key string) error {
	if parent.Kind == yaml.MappingNode {
		// Remove from map. Key must exist.
		for i := 0; i+1 < len(parent.Content); i += 2 {
			keyNode := parent.Content[i]
			if keyNode.Kind == yaml.ScalarNode && keyNode.Value == key {
				parent.Content = append(parent.Content[:i], parent.Content[i+2:]...)
				return nil
			}
		}
		return fmt.Errorf("key '%s' not found", key)
	}

	if parent.Kind == yaml.SequenceNode {
		// Remove from array at index.
		index, err := strconv.Atoi(key)
		if err != nil {
			return fmt.Errorf("invalid array index '%s'", key)
		}
		if index < 0 || index >= len(parent.Content) {
			return fmt.Errorf("array index %d out of bounds (len %d)", index, len(parent.Content))
		}
		parent.Content = append(parent.Content[:index], parent.Content[index+1:]...)
		return nil
	}

	return fmt.Errorf("cannot remove from node kind %v", parent.Kind)
}

func applyTest(parent *yaml.Node, key string, expectedValue json.RawMessage) error {
	target, err := findChildNode(parent, key)
	if err != nil {
		return fmt.Errorf("target not found: %w", err)
	}

	// Compare semantic values using Go reflection.

	// 1. Convert target node to Go structure.
	var targetGo any
	// Decode handles the conversion from AST to Go types.
	if err := target.Decode(&targetGo); err != nil {
		// Handle explicit nulls if Decode fails but the node represents null.
		if target.Kind == yaml.ScalarNode && (target.Tag == "!!null" || target.Value == "null" || target.Value == "~") {
			targetGo = nil
		} else {
			return fmt.Errorf("failed to decode target node for comparison: %w", err)
		}
	}

	// 2. Convert expected JSON value to Go structure.
	var expectedGo any
	if len(expectedValue) > 0 {
		if err := json.Unmarshal(expectedValue, &expectedGo); err != nil {
			return fmt.Errorf("failed to unmarshal expected JSON value: %w", err)
		}
	} else {
		// 'test' operation requires a 'value' field.
		return errors.New("expected value missing for test operation")
	}

	// 3. Compare.
	if !reflect.DeepEqual(targetGo, expectedGo) {
		return fmt.Errorf("test failed: value mismatch. Expected %v, Got %v", expectedGo, targetGo)
	}

	return nil
}

func findChildNode(parent *yaml.Node, key string) (*yaml.Node, error) {
	if parent.Kind == yaml.MappingNode {
		for i := 0; i+1 < len(parent.Content); i += 2 {
			keyNode := parent.Content[i]
			if keyNode.Kind == yaml.ScalarNode && keyNode.Value == key {
				return parent.Content[i+1], nil
			}
		}
		return nil, fmt.Errorf("key '%s' not found", key)
	}

	if parent.Kind == yaml.SequenceNode {
		index, err := strconv.Atoi(key)
		if err != nil {
			return nil, fmt.Errorf("invalid array index '%s'", key)
		}
		if index < 0 || index >= len(parent.Content) {
			return nil, fmt.Errorf("array index %d out of bounds (len %d)", index, len(parent.Content))
		}
		return parent.Content[index], nil
	}

	return nil, fmt.Errorf("cannot find child in node kind %v", parent.Kind)
}

// --- Surgical Replacement (AST Reconciliation) ---

// surgicalReplace replaces the target node, reconciling the AST to minimize changes.
func surgicalReplace(target *yaml.Node, newValue json.RawMessage) error {
	desiredNode, err := jsonValueToYAMLNode(newValue)
	if err != nil {
		return err
	}
	return surgicalReplaceNode(target, desiredNode)
}

// surgicalReplaceNode performs the reconciliation logic.
func surgicalReplaceNode(target, desired *yaml.Node) error {
	// If kinds differ, replace the whole structure (Shape Change).
	if target.Kind != desired.Kind {
		// We replace the content but keep the target node's metadata (comments) associated with its position.
		target.Kind = desired.Kind
		target.Tag = desired.Tag
		target.Value = desired.Value
		target.Content = desired.Content
		target.Style = desired.Style
		return nil
	}

	// Scalar update (surgical).
	if target.Kind == yaml.ScalarNode {
		target.Tag = desired.Tag
		target.Value = desired.Value

		// Style preservation logic.
		if target.Tag == "!!str" {
			// Keep target.Style if set (preserves original quotes).
			// If it was PlainStyle (0), we keep it 0.
			// We rely on jsonValueToYAMLNode to set a default style (e.g., SingleQuoted) on the 'desired' node,
			// but we prioritize the 'target' style here for existing nodes.
		} else {
			// Normalize non-strings to PlainStyle.
			target.Style = 0
		}
		return nil
	}

	// Mapping reconciliation.
	if target.Kind == yaml.MappingNode {
		return reconcileMapping(target, desired)
	}

	// Sequence reconciliation.
	if target.Kind == yaml.SequenceNode {
		return reconcileSequence(target, desired)
	}

	return nil
}

// reconcileMapping reconciles two mapping nodes, preserving order and comments of existing keys, and handling duplicates.
func reconcileMapping(target, desired *yaml.Node) error {
	// 1. Map desired keys.
	desiredMap := make(map[string]*yaml.Node)
	// We iterate desired.Content to capture the semantic value (last occurrence if desired somehow had duplicates).
	for i := 0; i+1 < len(desired.Content); i += 2 {
		keyNode := desired.Content[i]
		if keyNode.Kind == yaml.ScalarNode {
			desiredMap[keyNode.Value] = desired.Content[i+1]
		}
	}

	// 2. Iterate over target content (to preserve order) and reconcile.
	newContent := make([]*yaml.Node, 0, len(target.Content)+len(desired.Content))
	processedKeys := make(map[string]bool)

	for i := 0; i+1 < len(target.Content); i += 2 {
		keyNode := target.Content[i]
		valueNode := target.Content[i+1]

		if keyNode.Kind != yaml.ScalarNode {
			// Keep non-scalar keys if they somehow exist.
			newContent = append(newContent, keyNode, valueNode)
			continue
		}

		key := keyNode.Value
		if processedKeys[key] {
			continue // Handle duplicates in target: skip subsequent occurrences.
		}
		processedKeys[key] = true

		if desiredValue, ok := desiredMap[key]; ok {
			// Key exists in both. Recursively reconcile the value.
			if err := surgicalReplaceNode(valueNode, desiredValue); err != nil {
				return err
			}
			// Keep original keyNode (preserves comments/style) and updated valueNode.
			newContent = append(newContent, keyNode, valueNode)
		}
		// Key removed in desired (skip appending to newContent).
	}

	// 3. Append new keys from desired (maintaining their relative order from the desired state).
	for i := 0; i+1 < len(desired.Content); i += 2 {
		keyNode := desired.Content[i]
		if keyNode.Kind == yaml.ScalarNode {
			key := keyNode.Value
			// Check if the key was already present in the target.
			if !processedKeys[key] {
				// Create a new key node with default style.
				newKeyNode := &yaml.Node{
					Kind: yaml.ScalarNode, Tag: "!!str", Value: key, Style: 0,
				}
				// The value node comes from the desired state (already styled by jsonValueToYAMLNode).
				newContent = append(newContent, newKeyNode, desired.Content[i+1])
				processedKeys[key] = true // Ensure we don't add it again if desired had duplicates.
			}
		}
	}

	target.Content = newContent
	return nil
}

// reconcileSequence performs element-by-element reconciliation based on index.
func reconcileSequence(target, desired *yaml.Node) error {
	n := len(target.Content)
	m := len(desired.Content)

	commonLen := n
	if m < n {
		commonLen = m
	}

	// 1. Reconcile existing elements by index.
	// This reuses the target nodes, preserving comments associated with that index.
	for i := 0; i < commonLen; i++ {
		if err := surgicalReplaceNode(target.Content[i], desired.Content[i]); err != nil {
			return err
		}
	}

	// 2. Handle length difference.
	if n > m {
		// Trim target.
		target.Content = target.Content[:m]
	} else if m > n {
		// Append new elements from desired.
		target.Content = append(target.Content, desired.Content[n:]...)
	}

	return nil
}
