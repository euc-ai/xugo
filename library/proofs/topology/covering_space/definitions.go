// definitions.go — the chapter's definitional layer: an open set evenly
// covered by a map, and a covering map, continuous with every point of the
// base in an evenly covered open set. The covering space is T and the base
// S, as continuous_map names a map's two spaces.

package covering_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

// EvenlyCoveredDef — `evenly_covered(T, S, p, u)`: u is open in the base,
// and the part of the covering space p carries into u is the union of
// pairwise disjoint open sets, the sheets, each carried homeomorphically
// onto u.
var EvenlyCoveredDef = evenlyCoveredDefThm{family.Define(registry.DefEntry{
	Name:  "EvenlyCoveredDef",
	Key:   "prop_d4d9850ac4b88835",
	Const: "evenly_covered",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → set(B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀u:set(B). " +
			"    evenly_covered(T, S, p, u) ⇔ " +
			"    u ∈ S ∧ " +
			"    ∃v:set(set(A)). " +
			"        v ⊆ T ∧ " +
			"        ⋃v = preimage_on(⋃T, p, u) ∧ " +
			"        (∀w w':set(A). w ∈ v ∧ w' ∈ v ∧ w ≠ w' ⇒ w ∩ w' = ∅) ∧ " +
			"        (∀w:set(A). w ∈ v ⇒ homeomorphic_map(subtopology(T, w), subtopology(S, u), p))",
	},
	Reading: "There may be no sheet at all: an open set nothing is carried into is evenly covered.",
})}

// CoveringMapDef — `covering_map(T, S, p)`: p is continuous and every point
// of the base lies in an evenly covered open set. p is not asked to be
// onto.
var CoveringMapDef = coveringMapDefThm{family.Define(registry.DefEntry{
	Name:  "CoveringMapDef",
	Key:   "prop_400bd7d2b89c823f",
	Const: "covering_map",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). " +
			"    covering_map(T, S, p) ⇔ " +
			"    continuous_map(T, S, p) ∧ ∀b:B. b ∈ ⋃S ⇒ ∃u:set(B). b ∈ u ∧ evenly_covered(T, S, p, u)",
	},
	Reading: "The lifting theorems never use that p is onto. When S is a " +
		"topology the points of the base p reaches form an open and closed set; " +
		"for an arbitrary family they and the rest are unions of members of S.",
	Deps: []registry.EntryLike{EvenlyCoveredDef},
})}
