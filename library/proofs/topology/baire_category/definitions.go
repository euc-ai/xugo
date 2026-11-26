// definitions.go — the chapter's definitional layer: a nowhere dense set,
// a meager set, a set with the Baire property and a Baire space, all read
// inside one topology.

package baire_category

import (
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// NowhereDenseDef — A subset of the carrier whose closure has empty interior.
var NowhereDenseDef = nowhereDenseDefThm{family.Define(registry.DefEntry{
	Name:     "NowhereDenseDef",
	Key:      "prop_dd0e98016c76474f",
	Const:    "nowhere_dense",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). nowhere_dense(T, s) ⇔ s ⊆ ⋃T ∧ interior(T, closure(T, s)) = ∅",
	},
	Reading: "Read inside the space: the set lies in the carrier and its closure, " +
		"taken in T, has no interior point. The empty set is nowhere dense in every space.",
})}

// MeagerDef — A subset of a countable union of nowhere dense sets.
var MeagerDef = meagerDefThm{family.Define(registry.DefEntry{
	Name:     "MeagerDef",
	Key:      "prop_2f16b2e76545e1f4",
	Const:    "meager",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). " +
			"    meager(T, s) ⇔ ∃a:(num → set(A)). (∀n:num. nowhere_dense(T, a(n))) ∧ s ⊆ ⋃image(a, 𝕌)",
	},
	Deps: []registry.EntryLike{NowhereDenseDef},
	Reading: "A subset of a meager set is meager by the definition, and a meager set " +
		"lies in the carrier. A countable union of meager sets is meager (MeagerCountableUnion).",
})}

// BairePropertyDef — Differs from an open set by a meager set.
var BairePropertyDef = bairePropertyDefThm{family.Define(registry.DefEntry{
	Name:     "BairePropertyDef",
	Key:      "prop_c0238e493a4cd6d2",
	Const:    "baire_property",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). " +
			"    baire_property(T, s) ⇔ s ⊆ ⋃T ∧ (∃u:set(A). u ∈ T ∧ meager(T, (s ∖ u) ∪ (u ∖ s)))",
	},
	Deps: []registry.EntryLike{MeagerDef},
	Reading: "The witness is an open set of T; the symmetric difference is " +
		"meager. Every open set and every meager subset of the carrier has the property.",
})}

// BaireSpaceDef — No nonempty open set is meager.
var BaireSpaceDef = baireSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "BaireSpaceDef",
	Key:   "prop_8c25eb69951104db",
	Const: "baire_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). baire_space(T) ⇔ is_topology(T) ∧ (∀u:set(A). u ∈ T ∧ meager(T, u) ⇒ u = ∅)",
	},
	Deps: []registry.EntryLike{MeagerDef},
	Reading: "Equivalent to the density of every countable " +
		"intersection of dense open sets. The empty space is a Baire space.",
})}
