# yamledit

A minimal Go package for **precise YAML editing** that preserves comments, formatting, and structure — now with **byte-surgical editing** to avoid noisy diffs.

## Features

* **Byte-Surgical Editing (No Churn)** – Only the bytes for values you actually change are touched. Unrelated lines remain byte-for-byte identical (quotes, spaces, inline comments, etc.).
* **Preserves Comments** – All `# …` comments and inline comments are maintained.
* **Preserves Formatting** – Maintains original indentation (auto-detected, including indentless sequences).
* **Preserves Key Order** – Original key order is maintained; **new keys are appended** to their mapping.
* **Thread-Safe** – Concurrent edits are safe.
* **Minimal API** – Just 4 functions for all operations.

## Installation

```bash
go get github.com/kevinwang15/yamledit
```

## API

The package provides just 4 functions:

* `Parse(data []byte) (*yaml.Node, error)` – Parse YAML from bytes (top-level must be a mapping).
* `Marshal(doc *yaml.Node) ([]byte, error)` – Serialize back to bytes (surgical when safe, falls back if needed).
* `EnsurePath(doc *yaml.Node, keys ...string) *yaml.Node` – Navigate/create nested paths (always returns a mapping node).
* `SetScalarInt(mapNode *yaml.Node, key string, value int)` – Set integer values under a mapping node.

### Example: no quote churn

Input:

```yaml
env:
  HTTP_CORS_ALLOWED_ORIGINS: '*'
  METRICS_ENABLED: "true"
  port: 8080
```

Code:

```go
svc := yamledit.EnsurePath(doc, "env")
yamledit.SetScalarInt(svc, "port", 9090)
out, _ := yamledit.Marshal(doc)
```

Output (only one line changed; quotes preserved):

```yaml
env:
  HTTP_CORS_ALLOWED_ORIGINS: '*'
  METRICS_ENABLED: "true"
  port: 9090
```

## Usage

```go
package main

import (
    "fmt"
    "os"
    "github.com/kevinwang15/yamledit"
)

func main() {
    // Read your YAML file
    data, _ := os.ReadFile("config.yaml")

    // Parse YAML
    doc, err := yamledit.Parse(data)
    if err != nil {
        panic(err)
    }

    // Navigate to nested paths (creates if missing)
    settings := yamledit.EnsurePath(doc, "app", "settings")

    // Set values while preserving comments & formatting
    yamledit.SetScalarInt(settings, "port", 8080)
    yamledit.SetScalarInt(settings, "timeout", 30)

    // Marshal back to YAML (byte-surgical where possible)
    output, _ := yamledit.Marshal(doc)

    // Write back to file
    if err := os.WriteFile("config.yaml", output, 0o644); err != nil {
        panic(err)
    }

    fmt.Println("Updated config.yaml")
}
```

## Example

Input YAML:

```yaml
# Application config
app:
  name: myapp
  # Settings section
  settings:
    debug: false  # Debug mode
```

After running the code above:

```yaml
# Application config
app:
  name: myapp
  # Settings section
  settings:
    debug: false  # Debug mode
    port: 8080
    timeout: 30
```

**Notice how:**

* All comments are preserved.
* Original indentation is maintained (including 2/3/4-space and indentless sequences).
* New keys are appended without disrupting structure.
* Unrelated lines (including their quoting style) are unchanged.

## Behavior & Limitations

* **Top-level must be a mapping.** `Parse` returns an error otherwise.
* **Supported write ops:** setting integers and creating nested mappings (`EnsurePath`).
  (String/boolean setters may be added in the future; today, only integers are mutated.)
* **Duplicate keys:** **undefined behavior** (subject to change). Do not rely on how duplicates are handled.
* **Fallbacks:** On shape changes or when surgery is unsafe, `Marshal` falls back to a structured re-encode that still preserves comments, order, and indent.

## Tests

The test suite includes cases for:

* Preserving single/double quotes on unrelated lines.
* Keeping inline comments when updating integers.
* Ensuring only the edited line changes when possible.
* Appending new integer keys with the mapping’s original indent.
* Fallback on shape change (scalar → mapping) without churning unrelated lines.
* Preserving indentless sequences and the final newline.

Run:

```bash
go test ./...
```

## Requirements

* Go 1.21 or higher

## License

MIT