# yamledit

A minimal Go package for precise YAML editing that preserves comments, formatting, and structure.

## Features

- **Preserves Comments** - All comments in your YAML are maintained
- **Preserves Formatting** - Maintains original indentation (auto-detected)
- **Preserves Key Order** - Original key order is maintained, new keys are appended
- **Thread-Safe** - Concurrent edits are safe
- **Minimal API** - Just 4 functions for all operations

## Installation

```bash
go get github.com/kevinwang15/yamledit
```

## API

The package provides just 4 functions:

- `Parse(data []byte) (*yaml.Node, error)` - Parse YAML from bytes
- `Marshal(doc *yaml.Node) ([]byte, error)` - Serialize back to bytes
- `EnsurePath(doc *yaml.Node, keys ...string) *yaml.Node` - Navigate/create nested paths
- `SetScalarInt(mapNode *yaml.Node, key string, value int)` - Set integer values

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

    // Set values while preserving comments
    yamledit.SetScalarInt(settings, "port", 8080)
    yamledit.SetScalarInt(settings, "timeout", 30)

    // Marshal back to YAML
    output, _ := yamledit.Marshal(doc)

    // Write back to file
    os.WriteFile("config.yaml", output, 0644)
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

Notice how:
- All comments are preserved
- Original indentation is maintained
- New keys are added without disrupting structure

## Requirements

- Go 1.21 or higher

## License

MIT