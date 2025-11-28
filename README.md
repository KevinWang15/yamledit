# yamledit

A Go package for **surgical YAML edits** that preserves comments, formatting, key order, and minimizes diffs.
Think: *change exactly the bytes you mean to - leave everything else untouched.*

- **Zero‑churn scalars.** Update ints/strings/bools/floats/null in place, keeping quote style, spaces, and inline
  comments.
- **Append without reflow.** Insert new keys/items at the _right_ indent and position.
- **JSON Patch built‑in.** Apply RFC‑6902 patches (optionally at a base path) with minimal diffs when safe.
- **Thread‑safe.** Concurrent edits are safe.

> **Why not parse & re‑encode?** Re‑encoding churns quotes, spaces, and comment whitespace. `yamledit` indexes exact
> byte positions so unrelated lines are **byte‑for‑byte identical**.

---

## Installation

```bash
go get github.com/kevinwang15/yamledit
````

Go 1.21+

---

## Quick start

```go
package main

import (
	"fmt"
	"os"

	"github.com/kevinwang15/yamledit"
	"gopkg.in/yaml.v3"
)

func main() {
	// 1) Read and parse (top-level must be a mapping; empty is okay)
	data, _ := os.ReadFile("config.yaml")
	doc, err := yamledit.Parse(data)
	if err != nil {
		panic(err)
	}

	// 2) Navigate/create nested mappings
	env := yamledit.EnsurePath(doc, "service", "env")

	// 3) Surgical scalar updates (quotes & inline comments on other lines preserved)
	yamledit.SetScalarInt(env, "PORT", 9090)
	yamledit.SetScalarBool(env, "METRICS_ENABLED", true)
	yamledit.SetScalarString(env, "GREETING", "hi") // keeps prior quote style if it existed
	yamledit.SetScalarNull(env, "DEPRECATED")       // !!null

	// 4) Delete keys surgically (removes full blocks, including arrays)
	yamledit.DeleteKey(env, "OLD_FLAG")

	// 5) Marshal back (surgery when safe; structured fallback when needed)
	out, err := yamledit.Marshal(doc)
	if err != nil {
		panic(err)
	}

	if err := os.WriteFile("config.yaml", out, 0o644); err != nil {
		panic(err)
	}
	fmt.Println("Updated config.yaml")
	_ = yaml.Node{} // just to show the import, not required further
}
```

**No quote churn example**

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

---

## API overview

> All functions are in `github.com/kevinwang15/yamledit`.

### Core

* `Parse(data []byte) (*yaml.Node, error)`
  Parse bytes into a `yaml.Node`. Top‑level **must** be a mapping (empty input creates an empty mapping document).

* `Marshal(doc *yaml.Node) ([]byte, error)`
  Serialize back to bytes. Performs **byte‑surgical** edits when safe, and **falls back** to AST encode when structure
  changes—still preserving comments, indent, and key order.

* `EnsurePath(node *yaml.Node, first string, rest ...string) *yaml.Node`
  Navigate/create nested mappings, starting from a `DocumentNode` **or** an inner `MappingNode`. Returns the mapping
  node at that path.

### Scalar setters (surgical updates)

* `SetScalarInt(mapNode *yaml.Node, key string, value int)`
* `SetScalarString(mapNode *yaml.Node, key, value string)`
* `SetScalarBool(mapNode *yaml.Node, key string, value bool)` → **canonicalizes to bare** `true`/`false`
* `SetScalarFloat(mapNode *yaml.Node, key string, value float64)`
* `SetScalarNull(mapNode *yaml.Node, key string)` → `!!null`

> Behavior: If the key exists, we replace only the value token (preserving spacing and inline comment).
> If it’s new, it’s appended at the mapping’s indent; strings are safely quoted on insertion.

### Deletion (surgical)

* `DeleteKey(mapNode *yaml.Node, key string)`
  Removes **all occurrences** of the key under that mapping. Deletion uses pre‑indexed start/end byte boundaries to
  remove the entire block (scalars, mappings, or arrays). If surgery isn’t possible, fallback marshal still removes the
  key without churning unrelated lines.

### JSON Patch (RFC‑6902)

* `ApplyJSONPatchBytes(node *yaml.Node, patchJSON []byte) error`
* `ApplyJSONPatch(node *yaml.Node, patch jsonpatch.Patch) error`
* `ApplyJSONPatchAtPathBytes(node *yaml.Node, patchJSON []byte, basePath []string) error`
* `ApplyJSONPatchAtPath(node *yaml.Node, patch jsonpatch.Patch, basePath []string) error`

**Notes**

* `basePath` lets you interpret each op’s pointer **relative** to a mapping path (e.g. `[]string{"service","envs"}`).
* Arrays: targeted edits (`/0/property`, `/-` appends) often remain **surgical**. Whole‑array replaces may fall back.

**Example: replace a field inside an array item (single‑line diff)**

```go
patch := []byte(`[{"op":"replace","path":"/0/property","value":"target-new"}]`)
if err := yamledit.ApplyJSONPatchAtPathBytes(doc, patch, []string{"service", "externalSecretEnvs"}); err != nil { /* ... */ }
out, _ := yamledit.Marshal(doc)
```

**Example: append a new array item**

```go
patch := []byte(`[{"op":"add","path":"/-","value":{"name":"EXTRA","path":"data/shared","property":"extra"}}]`)
_ = yamledit.ApplyJSONPatchAtPathBytes(doc, patch, []string{"service", "externalSecretEnvs"})
out, _ := yamledit.Marshal(doc)
```

---

## Guarantees & design choices

* **Comments preserved.** Header, foot, and inline (`# ...`) comments are preserved; unrelated lines are byte‑stable.
* **Indent preserved.** Base indent auto‑detected (2/3/4/…); indentless sequences supported; new content matches
  original style.
* **Key order preserved.** Original order is maintained; **new keys are appended** to their mapping.
* **Duplicates deduped on write.** If the original contained duplicate keys, only the **last** occurrence remains after
  marshal (YAML semantics: last wins). This changes bytes but not meaning.
* **Booleans normalize on edit.** A key you edit with `SetScalarBool` (or via JSON Patch) will render as bare `true`/
  `false` even if previously quoted. Unrelated booleans remain untouched.
* **No global re‑encode.** If surgery and scoped rewrites are not possible, `Marshal` returns an error instead of
  reformatting the whole document. All rewrites are per‑key/sequence, using recorded bounds.
* **Sequence append/delete supported.** Scalar arrays can be appended to or truncated surgically; complex reorders may
  still be unsupported and will error rather than churn bytes.

---

## Arrays (sequences)

* **Arrays of mappings**

    * In‑place updates (e.g. change `property` of item `0`) are typically **single‑line** surgical diffs.
    * Appends render using the item’s captured style:

      ```
      - name: FOO
        path: ...
        property: ...
      ```
* **Arrays of scalars**

    * Index‑based replacements can be surgical.
    * **Whole‑array replace** may fall back and can drop inter‑item comments. If you need minimal diffs & comment
      preservation, prefer targeted index edits and `/-` appends instead of replacing the entire list.

---

## Testing

The suite covers:

* quote preservation (single/double), inline comments, final newline,
* exact indent (2/3/4‑space, indentless),
* new key insertion & append order,
* JSON Patch on scalars, maps, arrays,
* duplicate removal, deletions (including arrays),
* concurrency safety.

Run:

```bash
go test ./...
```

## Performance

Edits run in O(changes), indexing is O(file). Memory footprint scales with the size of the original buffer and indices 
(line offsets, map/sequence metadata).

---

## License

MIT
