package yamledit

import (
	"fmt"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// normalizeEmptyEnvMap converts "envs:" (parsed as !!null) into an empty mapping
// in the yaml.v3 AST and in the ordered logical view, and marks the doc as
// structurally dirty so Marshal() will fall back to a full re-encode.
func normalizeEmptyEnvMap(doc *yaml.Node, st *docState) {
	if doc == nil || st == nil {
		return
	}
	if doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 {
		return
	}
	root := doc.Content[0]
	if root == nil || root.Kind != yaml.MappingNode {
		return
	}

	var walk func(n *yaml.Node, path []string)
	walk = func(n *yaml.Node, path []string) {
		if n == nil {
			return
		}
		switch n.Kind {
		case yaml.MappingNode:
			for i := 0; i+1 < len(n.Content); i += 2 {
				k := n.Content[i]
				v := n.Content[i+1]
				if k.Kind != yaml.ScalarNode {
					continue
				}
				key := k.Value
				if key == "envs" && v.Kind == yaml.ScalarNode && v.Tag == "!!null" {
					// Replace scalar null with an empty !!map in the AST.
					m := &yaml.Node{
						Kind:        yaml.MappingNode,
						Tag:         "!!map",
						HeadComment: v.HeadComment,
						LineComment: v.LineComment,
						FootComment: v.FootComment,
						Anchor:      v.Anchor,
						Line:        v.Line,
						Column:      v.Column,
					}
					n.Content[i+1] = m
					// Update the logical ordered view: envs becomes an empty map.
					st.ordered = setAnyAtPath(st.ordered, path, key, gyaml.MapSlice{})
					st.structuralDirty = true
					continue
				}
				// Recurse into children so we catch nested envs maps as well.
				switch v.Kind {
				case yaml.MappingNode:
					walk(v, append(path, key))
				case yaml.SequenceNode:
					walk(v, append(path, key))
				}
			}
		case yaml.SequenceNode:
			for _, c := range n.Content {
				walk(c, path)
			}
		}
	}
	walk(root, nil)
}

// Parse reads YAML data and returns a yaml.Node, creating a minimal mapping document if empty.
func Parse(data []byte) (*yaml.Node, error) {
	doc := &yaml.Node{
		Kind:    yaml.DocumentNode,
		Content: []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}},
	}

	if len(data) > 0 {
		var tmp yaml.Node
		if err := yaml.Unmarshal(data, &tmp); err != nil {
			return nil, fmt.Errorf("yamledit: failed to parse YAML: %w", err)
		}
		if tmp.Kind != yaml.DocumentNode || len(tmp.Content) == 0 || tmp.Content[0].Kind != yaml.MappingNode {
			return nil, fmt.Errorf("yamledit: top-level YAML is not a mapping")
		}
		doc = &tmp
	}

	// Build shadow state using goccy/go-yaml (to preserve comments and ordered map for fallback)
	st := &docState{
		doc:               doc,
		comments:          gyaml.CommentMap{},
		ordered:           gyaml.MapSlice{},
		subPathByHN:       map[*yaml.Node][]string{},
		indent:            2,
		indentSeq:         true,
		original:          append([]byte(nil), data...),
		lineOffsets:       buildLineOffsets(data),
		mapIndex:          map[string]*mapInfo{},
		valueOccByPathKey: map[string][]valueOcc{},
		boundsByPathKey:   map[string][]kvBounds{}, // Initialize new map
		seqIndex:          map[string]*seqInfo{},
		toDelete:          map[string]struct{}{},
	}

	// Decode into ordered map and capture comments; detect indent and sequence style
	if len(data) > 0 {
		if err := gyaml.UnmarshalWithOptions(data, &st.ordered, gyaml.UseOrderedMap(), gyaml.CommentToMap(st.comments)); err == nil {
			ind, seq := detectIndentAndSequence(data)
			st.indent, st.indentSeq = ind, seq
		}
	}

	// Keep a snapshot of the original ordered map for diffing
	st.origOrdered = cloneMapSlice(st.ordered)

	// Normalize pathological shapes (e.g. "envs:" parsed as !!null) into an
	// empty mapping in the AST and logical view. This is marked as a structural
	// change so Marshal() will fall back to full encode, producing "envs: {}".
	if doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode {
		normalizeEmptyEnvMap(doc, st)
	}

	// Index mapping handles (for path lookups later on)
	if doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode {
		st.subPathByHN[doc.Content[0]] = nil
		indexMappingHandles(st, doc.Content[0], nil)

		// Build byte-surgical indices off the original parsed tree
		if len(data) > 0 {
			indexPositions(st, doc.Content[0], nil)
		}
	}

	register(doc, st)
	return doc, nil
}

// indexSeqPositions indexes scalar positions for sequence items which are mapping nodes.
func indexSeqPositions(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Kind != yaml.SequenceNode {
		return
	}
	for idx, it := range seq.Content {
		if it == nil {
			continue
		}
		if it.Kind == yaml.MappingNode {
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				v := it.Content[j+1]
				if k.Kind != yaml.ScalarNode || v.Kind != yaml.ScalarNode {
					continue
				}
				valStart := offsetFor(st.lineOffsets, v.Line, v.Column)
				if valStart < 0 || valStart >= len(st.original) {
					continue
				}
				valEnd := findScalarEndOnLine(st.original, valStart)
				lineEnd := findLineEnd(st.original, valStart)
				pk := makeSeqPathKey(cur, idx, k.Value)
				st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
					keyLineStart: lineStartOffset(st.lineOffsets, k.Line),
					valStart:     valStart,
					valEnd:       valEnd,
					lineEnd:      lineEnd,
				})
			}
		}
	}
}

// indexScalarSeqPositions indexes positions for sequence items which are scalar nodes.
func indexScalarSeqPositions(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Kind != yaml.SequenceNode {
		return
	}

	// Optimization/Safety: Only process if it appears to be primarily a sequence of scalars.
	// Mixed sequences (scalars and mappings) are complex; we prioritize mapping indexing.
	isScalarSeq := true
	for _, it := range seq.Content {
		if it != nil && it.Kind != yaml.ScalarNode {
			// If we find a non-scalar, we rely on indexSeqPositions (for mappings)
			// or indexSequenceAnchors (for structure) but skip scalar indexing here
			// to avoid conflicts if structure is complex.
			isScalarSeq = false
			break
		}
	}
	if !isScalarSeq {
		return
	}

	for idx, it := range seq.Content {
		if it == nil {
			continue
		}

		// We have a scalar item. Index its value position.
		valStart := offsetFor(st.lineOffsets, it.Line, it.Column)
		if valStart < 0 || valStart >= len(st.original) {
			continue
		}
		valEnd := findScalarEndOnLine(st.original, valStart)
		lineEnd := findLineEnd(st.original, valStart)

		// We use the index path key format: path\x00[idx].
		pk := makeSeqItemPathKey(cur, idx)
		st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
			keyLineStart: lineStartOffset(st.lineOffsets, it.Line),
			valStart:     valStart,
			valEnd:       valEnd,
			lineEnd:      lineEnd,
		})
	}
}

// indexSequenceAnchors captures indent/style and insertion anchors for sequences (both scalars and mappings).
func indexSequenceAnchors(st *docState, seq *yaml.Node, cur []string) {
	mpath := joinPath(cur)
	si := st.seqIndex[mpath]
	if si == nil {
		si = &seqInfo{originalPath: true}
		st.seqIndex[mpath] = si
	}
	if len(seq.Content) == 0 {
		si.hasAnyItem = false
		si.items = nil
		si.gaps = nil
		return
	}
	si.hasAnyItem = true

	// Per‑item boundaries and identities (name or scalar value)
	si.items = si.items[:0]

	// Detect style/indent/key order from the FIRST item we see (for stability).
	detectedStyle := false

	computeItemBounds := func(it *yaml.Node) (start int, end int, name string) {
		if it == nil {
			return
		}
		// start (beginning of the first line of the item)
		if it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
			fk := it.Content[0]
			start = lineStartOffset(st.lineOffsets, fk.Line)
		} else {
			start = lineStartOffset(st.lineOffsets, it.Line)
		}

		// end (newline ending the last line of the item)
		if it.Kind == yaml.MappingNode {
			maxEnd := 0
			for j := 0; j+1 < len(it.Content); j += 2 {
				v := it.Content[j+1]
				if v == nil {
					continue
				}
				le := maxLineEndForNode(st, v)
				if le > maxEnd {
					maxEnd = le
				}
			}
			if maxEnd == 0 {
				end = findLineEnd(st.original, start)
			} else {
				end = maxEnd
			}
		} else {
			end = findLineEnd(st.original, start)
		}

		// name (best-effort identity: "name" field value or scalar value)
		if it.Kind == yaml.MappingNode {
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				v := it.Content[j+1]
				if k.Kind == yaml.ScalarNode && k.Value == "name" && v.Kind == yaml.ScalarNode {
					name = v.Value
					break
				}
			}
		} else if it.Kind == yaml.ScalarNode {
			name = it.Value
		}

		if !detectedStyle {
			le := findLineEnd(st.original, start)
			if start < 0 || start >= len(st.original) {
				return
			}
			lnEnd := le
			if le < len(st.original) && st.original[le] == '\n' {
			} else if le == len(st.original)-1 {
				lnEnd = len(st.original)
			}
			if start >= lnEnd {
				return
			}
			ln := st.original[start:lnEnd]
			si.indent = leadingSpaces(ln)
			si.firstKeyInline = firstNonSpaceByte(ln) == '-'

			if it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
				kvIndent := 0
				for j := 0; j+1 < len(it.Content); j += 2 {
					k := it.Content[j]
					ks := lineStartOffset(st.lineOffsets, k.Line)
					ke := findLineEnd(st.original, ks)
					if ks < 0 || ks >= len(st.original) {
						continue
					}
					klEnd := ke
					if ke < len(st.original) && st.original[ke] == '\n' {
					} else if ke == len(st.original)-1 {
						klEnd = len(st.original)
					}
					if ks >= klEnd {
						continue
					}
					kl := st.original[ks:klEnd]
					if firstNonSpaceByte(kl) == '-' {
						continue
					}
					sp := leadingSpaces(kl)
					if kvIndent == 0 || (sp > 0 && sp < kvIndent) {
						kvIndent = sp
					}
				}

				if kvIndent == 0 {
					kvIndent = si.indent + st.indent
				}
				si.itemKVIndent = kvIndent

				order := make([]string, 0, len(it.Content)/2)
				for j := 0; j+1 < len(it.Content); j += 2 {
					if it.Content[j].Kind == yaml.ScalarNode {
						order = append(order, it.Content[j].Value)
					}
				}
				si.keyOrder = order
			} else {
				si.itemKVIndent = si.indent + st.indent
				si.keyOrder = nil
			}
			detectedStyle = true
		}
		return
	}

	first := seq.Content[0]
	if first == nil {
		return
	}

	fs, fe, nm := computeItemBounds(first)
	si.firstItemStart = fs

	lastEnd := fe
	si.items = make([]seqItemInfo, 0, len(seq.Content))
	si.items = append(si.items, seqItemInfo{name: nm, start: fs, end: fe})

	for _, it := range seq.Content[1:] {
		s, e, nm2 := computeItemBounds(it)
		if e > lastEnd {
			lastEnd = e
		}
		si.items = append(si.items, seqItemInfo{name: nm2, start: s, end: e})
	}
	si.lastItemEnd = lastEnd

	if len(si.items) >= 2 {
		si.gaps = make([][]byte, len(si.items)-1)
		for i := 0; i < len(si.items)-1; i++ {
			gStart := si.items[i].end + 1
			gEnd := si.items[i+1].start
			if gStart >= 0 && gEnd >= gStart && gEnd <= len(st.original) {
				si.gaps[i] = append([]byte(nil), st.original[gStart:gEnd]...)
			} else {
				si.gaps[i] = nil
			}
		}
	} else {
		si.gaps = nil
	}
}

func indexMappingHandles(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode {
		return
	}
	st.subPathByHN[n] = append([]string(nil), cur...)
	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind == yaml.ScalarNode {
			seg := k.Value
			if v.Kind == yaml.MappingNode {
				indexMappingHandles(st, v, append(cur, seg))
			}
		}
	}
}

// indexPositions populates indices for surgical edits: mapIndex, valueOccByPathKey, seqIndex, and boundsByPathKey.
func indexPositions(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode {
		return
	}
	mapPath := joinPath(cur)
	mi := st.mapIndex[mapPath]
	if mi == nil {
		mi = &mapInfo{indent: 0, lastLineEnd: 0, hasAnyKey: false, originalPath: true}
		st.mapIndex[mapPath] = mi
	}

	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind != yaml.ScalarNode {
			continue
		}
		key := k.Value
		pk := makePathKey(cur, key)

		if k.Column > 0 && mi.indent == 0 && !(len(cur) == 0 && k.Column-1 == 0) {
			mi.indent = k.Column - 1
		}
		if len(cur) == 0 {
			mi.indent = 0
		}

		keyLineStart := lineStartOffset(st.lineOffsets, k.Line)
		valStart := offsetFor(st.lineOffsets, v.Line, v.Column)

		var lineEnd int
		if valStart >= 0 && valStart < len(st.original) {
			lineEnd = findLineEnd(st.original, valStart)
			mi.hasAnyKey = true
		} else {
			lineEnd = findLineEnd(st.original, keyLineStart)
			mi.hasAnyKey = true
		}

		if v.Kind == yaml.ScalarNode && valStart >= 0 && valStart < len(st.original) {
			if valStart < len(st.original) {
				ch := st.original[valStart]
				if ch == '|' || ch == '>' {
					keyIndent := 0
					if k.Column > 0 {
						keyIndent = k.Column - 1
					}
					lineEnd = extendScalarBlockEnd(st.original, st.lineOffsets, v.Line, keyIndent)
				}
			}
		}

		if v.Kind == yaml.MappingNode {
			childPath := append(cur, key)
			indexPositions(st, v, childPath)
			if childMi := st.mapIndex[joinPath(childPath)]; childMi != nil && childMi.lastLineEnd > lineEnd {
				lineEnd = childMi.lastLineEnd
			}
		} else if v.Kind == yaml.SequenceNode {
			seqPath := append(cur, key)
			indexSeqPositions(st, v, seqPath)
			indexScalarSeqPositions(st, v, seqPath)
			indexSequenceAnchors(st, v, seqPath)
			if seqInfo := st.seqIndex[joinPath(seqPath)]; seqInfo != nil && seqInfo.lastItemEnd > lineEnd {
				lineEnd = seqInfo.lastItemEnd
			}
		}

		if v.Kind == yaml.ScalarNode && valStart >= 0 && valStart < len(st.original) {
			valEnd := findScalarEndOnLine(st.original, valStart)
			scalarLineEnd := findLineEnd(st.original, valStart)

			st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
				keyLineStart: keyLineStart,
				valStart:     valStart,
				valEnd:       valEnd,
				lineEnd:      scalarLineEnd,
			})
		}

		blockEnd := lineEnd
		if blockEnd >= 0 {
			if blockEnd < len(st.original) && st.original[blockEnd] == '\n' {
				blockEnd++
			} else if blockEnd == len(st.original)-1 {
				blockEnd = len(st.original)
			}
		}

		if keyLineStart >= 0 && keyLineStart <= len(st.original) && blockEnd >= keyLineStart && blockEnd <= len(st.original) {
			st.boundsByPathKey[pk] = append(st.boundsByPathKey[pk], kvBounds{
				start: keyLineStart,
				end:   blockEnd,
			})
		}

		if lineEnd > mi.lastLineEnd {
			mi.lastLineEnd = lineEnd
		}
	}
}
