// definitions.go — the chapter's definitional layer: the one-point
// compactification of a space, on the optional values of its type.
// `none` is the point at infinity and `some` carries the space in; the
// open sets are the images of the open sets of the space, and the
// complements of its closed compact sets with the new point added.

package compactification

import (
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_image"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

// OnePointCompactificationDef — `one_point_compactification(T)`: the
// topology on `insert(none, image(some, ⋃T))` whose open sets are the
// images of the open sets of T and the sets `insert(none, image(some,
// ⋃T ∖ k))` for k closed and compact in T. The space is carried on the
// optional values of its own type, so the new point is never one of its
// points, whatever its carrier — the line's carrier is all of ℝ.
var OnePointCompactificationDef = onePointCompactificationDefThm{family.Define(registry.DefEntry{
	Name:  "OnePointCompactificationDef",
	Key:   "prop_aedfb56246f7345e",
	Const: "one_point_compactification",
	Type:  "set(set(A)) → set(set(option(A)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    one_point_compactification(T) = " +
			"    {v:set(option(A)) | " +
			"        (∃u:set(A). u ∈ T ∧ v = image(some, u)) ∨ " +
			"        (∃k:set(A). closed_in(T, k) ∧ compact_in(T, k) ∧ v = insert(none, image(some, ⋃T ∖ k)))}",
	},
})}
