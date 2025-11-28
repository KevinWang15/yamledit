# yamledit v1 Review & Evolution Plan Toward v2

## 1. Purpose & Audience

This document is for the **current yamledit v1 engineering team**.

Goals:

* Give a **clear review** of v1: what’s good, what’s problematic.
* Describe the **target v2 behavior and architecture** (the “surgical editing” design).
* Propose a **gradual, low‑risk plan** to evolve v1 into v2, **without breaking the existing public API**.
* Allow two efforts to proceed in parallel:

  * Clean‑room v2 implementation.
  * Controlled refactor of v1 converging on the same design.

The idea is: if both succeed, we can pick the better one, or merge ideas. If only one succeeds, we still get a good v2.

---

## 2. v1 – What Works Today

Even though we want to replace/improve v1, it already has several valuable pieces:

1. **Public API and CLI**

   * The v1 interface is already wired into internal usage and tooling.
   * Callers know how to express operations (paths, set/delete behavior, etc.).
   * This is a big asset: we want **v2 to be a drop‑in replacement**.

2. **Concept of “surgical editing”**

   * v1 already tries to modify YAML **in place**, without completely re‑encoding the file.
   * It attempts to preserve comments and formatting in many cases.
   * The “surgical” idea is correct; we want to keep and formalize it.

3. **Use of `goccy/go-yaml` or similar**

   * v1 already depends on modern YAML tooling.
   * This library gives an AST with positions, which is exactly what we need for principled surgical edits.

4. **Unit tests and fixtures**

   * v1 already has tests that capture current behavior and edge cases.
   * These tests are useful as:

     * Regression protection,
     * Documentation of expectations,
     * A way to check that refactors don’t break semantics.

---

## 3. v1 – Key Problems to Address

The motivation for v2 is that v1’s **internals and behavior are fragile**. Main issues:

### 3.1 Fallback Behavior (Biggest Problem)

* v1 attempts a surgical edit.
* If something looks “hard” or “unsafe”, v1 sometimes **falls back to re‑encoding the whole document**.
* This fallback is often:

  * **Silent or unexpected**
  * Potentially destructive for formatting and comments
* Result: users see surprise reformats, moved or lost comments, and hard‑to‑debug diffs.

**New requirement:**

> “We’d rather it error out than fallback.”

So we want to **remove this fallback behavior entirely** and replace it with **explicit errors** for unsupported operations.

### 3.2 Weak / Ad‑hoc Shape Detection

* v1 uses some notion of “shape change detection” to decide when surgeries are allowed.
* This logic is:

  * Hard to understand,
  * Not clearly documented,
  * Often too conservative or too inconsistent.
* It sometimes blocks operations that are actually feasible, or pushes them into fallback.

In v2, we want:

* Clear, **principled rules** for what is supported.
* A simple model: **“If the operation can be done by rewriting one contiguous subtree, we do it. Otherwise we error.”**

### 3.3 Messy Internals & Coupling

From the description:

* Parsing, path resolution, planning, patching, and CLI logic tend to be **mixed together**.
* Hard to reason about:

  * Where exactly the AST is interpreted,
  * Where text offsets are computed,
  * Where formatting decisions are made.
* This makes it difficult to:

  * Fix bugs,
  * Extend behavior,
  * Add new tests that target specific layers.

We’d like to gradually refactor toward a **pipeline**:

> Parse → Resolve Paths → Plan Edits → Render Snippets → Apply Patches

Each phase should be as independent as possible.

### 3.4 Over‑ or Under‑Preserving Formatting

v1 behavior around formatting/comments is inconsistent:

* Sometimes it destroys large amounts of formatting due to fallback.
* Sometimes it refuses operations because it’s scared of “shape change”.
* Sometimes it gets indentation wrong.

We want strong guarantees:

* **Unchanged parts of the document stay byte‑for‑byte identical.**
* Only the **minimal edited subtree** is re‑encoded.
* Indentation for new content is consistent with the existing file.

---

## 4. Target v2 Behavior (Short Summary)

This summarizes the separate “surgical editing design” document in v2 terms, so the v1 team knows where we’re going.

### 4.1 Public API

* The **public API and CLI must stay the same**, including:

  * Exported Go types & functions,
  * CLI flags and semantics.
* v2 is explicitly a **drop‑in replacement**.

### 4.2 Core Rules

1. **Surgical editing as default and only mode.**
   No full‑document re‑encode behind the scenes.

2. **Minimal subtree re‑encoding.**
   For a set operation on path `a.b`:

   ```yaml
   a: # this is a
     b: 1
   ```

   Setting `a.b` to `{c: d}` behaves like:

   ```yaml
   a: # this is a
     b:
       c: d
   ```

   * We keep `a: # this is a` exactly as‑is.
   * We replace only the `b` subtree.
   * It is allowed to use YAML marshal for the new `b` value, then inject it with correct indent.

3. **No fallback.**
   If we cannot perform a safe surgical edit that touches only the necessary region, we:

   * Return an error,
   * Do not modify the file.

4. **Best‑effort preservation of comments and formatting.**

   * Unchanged subtrees are preserved byte‑for‑byte.
   * Comments on the **parent lines** of edited nodes are preserved where reasonable.
   * Comments inside re‑encoded subtrees may be lost.

5. **Deterministic behavior with a clear internal pipeline.**

---

## 5. Strategy: Evolve v1 Incrementally

We don’t want a “big bang” rewrite inside v1. Instead, we’ll progressively reshape v1 into the v2 architecture, **keeping it buildable and shippable at every step**.

High‑level phases:

1. **Lock down API and behavior contracts.**
2. **Add observability and toggles.**
3. **Refactor into a clear pipeline (parse → plan → patch).**
4. **Introduce minimal‑subtree re‑encoding logic.**
5. **Replace fallback with hard errors.**
6. **Align with clean‑room v2 behavior and remove old paths.**

Below is a more detailed plan.

---

## 6. Phase 1 – Establish Contracts & Safety Net

**Goal:** Make it safe to refactor v1 without breaking users.

### 6.1 Freeze Public API

* Document the current exported Go surface and CLI behavior.
* Agree that **no breaking changes** (signature changes, removed flags) will be made during the v1→v2 evolution.

### 6.2 Strengthen Tests

Add/expand tests that will guard behavior during refactors:

1. **Golden tests for formatting preservation**

   * Take real‑world YAML files and operations.
   * Assert that:

     * Data semantics after editing are correct.
     * Diff is small and localized to expected regions.

2. **Comment preservation tests**

   * Especially around examples like:

     ```yaml
     a: # this is a
       b: 1
     ```

   * Changing `b` should not touch the comment on `a`.

3. **Failure‑mode tests**

   * For operations that v1 currently cannot handle surgically.
   * For now we assert “whatever v1 does today,” but we’ll later shift expectations to “returns error” instead of fallback.

4. **Round‑trip semantic tests**

   * Parse original → apply operations in memory → marshal → parse.
   * Parse output from v1.
   * Compare data semantics (must match).

This test suite will be the **safety net** for refactoring.

---

## 7. Phase 2 – Add Observability & Feature Flags

**Goal:** See what v1 is actually doing in the wild and enable gradual behavior changes.

### 7.1 Instrument Fallback Paths

* Wherever v1 currently:

  * Detects “shape change” and decides to fallback,
  * Or re‑encodes the entire document,
* Add logging or counters (depending on environment), e.g.:

  * “Fallback: reason=ShapeChanged path=…”
  * “Fallback: reason=UnsupportedAnchor path=…”

This helps answer:

* How often do fallbacks happen?
* Which code paths are most problematic?

### 7.2 Add Internal Feature Flags

Introduce feature flags (environment variables or configuration) such as:

* `YAMLEDIT_EXPERIMENTAL_SURGICAL_ONLY=true`
* `YAMLEDIT_DISABLE_FALLBACK=true`

Initially:

* Default: legacy behavior (fallback still enabled).
* CI / experimental binaries: enable new behavior progressively.

Later, as confidence grows, flip defaults.

---

## 8. Phase 3 – Refactor Toward a Clean Pipeline

**Goal:** Make v1 internals look structurally like the v2 design, while keeping behavior mostly the same.

### 8.1 Introduce Internal Modules

Without changing public API, refactor internal code into logical components:

* `parser`

  * Wraps `goccy/go-yaml`.
  * Exposes AST + positions.

* `path`

  * Knows how to interpret the existing path syntax and find nodes.

* `layout`

  * Deals with byte offsets, indentation, line endings.
  * Maps AST nodes to `[start, end)` byte ranges in the original YAML.

* `planner`

  * Given operations, AST and layout, produces an **edit plan**:

    * Which nodes to change,
    * What their new logical values are,
    * What byte ranges will be affected.

* `patch`

  * Applies text replacements to the original bytes.

These modules can be pure internal packages; public API just calls into them.

### 8.2 Keep Behavior Intact (for Now)

During this phase:

* Where v1 currently falls back to full re‑encode, keep doing so.
* Focus on **moving logic** into the new structured modules, not changing outcomes.

The payoff:

* Once the pipeline structure is in place, we can **swap out fallback** for better logic, without touching CLI and public surface.

---

## 9. Phase 4 – Introduce Explicit Minimal‑Subtree Re‑encoding

**Goal:** Replace ad‑hoc shape checks with a principled notion: “one contiguous subtree = one text region.”

### 9.1 Define the Edit Unit

In `layout` / `planner`, formalize:

* The edit unit is:

  * A **mapping entry** (key + value subtree), or
  * A **sequence item**, or
  * A top‑level document node.

For each operation, we want to be able to compute:

* A **single contiguous region** in the original bytes that contains the entire subtree to be replaced.

If we cannot find such a region, we consider this operation “not surgically supported” (to be turned into an error later).

### 9.2 Implement Subtree Re‑encoding

For each operation:

1. Use `planner` to:

   * Resolve path → AST node,
   * Determine region `[start, end)` to replace.

2. Create the new logical value in memory (using the current v1 mechanisms).

3. Use YAML marshal (e.g. `yaml.Marshal`) to encode **only that value** into a snippet.

4. In `layout`:

   * Adjust indentation based on parent context.
   * Honor line endings.

5. In `patch`:

   * Replace `[start, end)` with the new snippet.

Initially, keep fallback in place for cases where we cannot compute such a region. But for cases we can, this new logic **should replace existing surgical code**, which may be messy.

### 9.3 Gate With Feature Flag

Enable this new subtree re‑encode logic behind an internal flag:

* When disabled: v1 behavior.
* When enabled: use the new logic for those operations.

Run tests and real workloads with the flag on to shake out bugs.

---

## 10. Phase 5 – Remove Fallback in Favor of Hard Errors

**Goal:** Remove the “full re‑encode” escape hatch, per product requirement.

Once subtree re‑encoding works and tests are solid:

1. Change behavior of fallback sites:

   * Instead of “full re‑encode whole document,”
   * Return a **clear error** like:

     > `surgical edit unsupported for this node; would require rewriting unrelated parts of the document`

2. Update tests:

   * For scenarios where v1 used to fallback and reformat the whole document, adjust expectations:

     * Now, those operations should fail with error.
   * Ensure these errors are consistent and descriptive.

3. Treat this as a **breaking change only in behavior**, not API:

   * The same operations may now fail instead of succeeding with heavy reformat.
   * This is intentional and desired:

     * “We’d rather it error out than fallback.”

4. Use flags to roll out:

   * For a transition period:

     * `YAMLEDIT_ALLOW_FALLBACK` can keep old behavior in some environments.
   * Eventually, default becomes **“no fallback, only error”**.

---

## 11. Phase 6 – Align Fully With the Clean‑Room v2 Design

By this stage, v1 internals should be very close in spirit to the clean‑room v2 design:

* Same pipeline: parse → resolve → plan → render → patch.
* Same minimal‑subtree re‑encoding semantics.
* Same “no fallback” rule.

At this point:

1. Compare v1‑refactored vs clean‑room v2:

   * Run a large suite of tests (real configs, kubernetes manifests, CI YAMLs).
   * For each:

     * Operations: apply via both implementations.
     * Compare:

       * Parsed data semantics,
       * Diff size,
       * Comment preservation.

2. Choose one of these paths (or merge):

   * If v1‑refactored is stable and clean enough, it can **be the v2**.
   * If the clean‑room implementation is cleaner and more maintainable, we can:

     * Replace internal code in the v1 repo with the clean‑room implementation.
     * Keep the v1 API but with the new core.

In both paths, the **public API remains the same**, and we end up with a v2 that is principled and maintainable.

---

## 12. Summary for the v1 Team

* v1 has valuable assets: **API, test cases, and the initial surgical concept**.
* The main pain points are:

  * **Fallback to full re‑encode** (surprise, formatting destruction),
  * **Ad‑hoc shape detection**,
  * **Messy internal structure**.

The target v2 is:

* A **surgical YAML editor** that:

  * Only re‑encodes the minimal necessary subtree,
  * Never silently falls back to full re‑encode,
  * Preserves comments and formatting outside edited regions,
  * Keeps the existing public API and CLI.

The proposed plan lets the v1 team:

* Reshape v1 into this architecture **step by step**,
* While a completely separate clean‑room implementation is built in parallel.

By the end, we’ll have:

* A principled, well‑structured codebase,
* Clear internal layers (parser, path, layout, planner, patch),
* Strong tests,
* And an implementation we can confidently publish and rely on as a common YAML editing library.
