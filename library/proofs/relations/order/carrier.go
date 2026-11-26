// carrier.go — preorders on a set, their guarded axioms, and the
// whole-type order views obtained by taking the carrier to be Universe.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PreorderOn — a preorder on c asks for reflexivity and transitivity
// only among points of c. The relation is unrestricted outside c.
var PreorderOn = preorderOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "PreorderOn",
	Key:     "prop_22c2672cee58afa5",
	Const:   "preorder_on",
	Subject: "c",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). " +
			"    preorder_on(c, R) ⇔ " +
			"    (∀x:A. x ∈ c ⇒ R(x, x)) ∧ (∀x y z:A. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ R(x, y) ∧ R(y, z) ⇒ R(x, z))",
	},
})}

// ReflexiveOn — a point of the carrier is below itself.
var ReflexiveOn = reflexiveOnThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveOn",
	Key:  "prop_59bd4489c243a9a8",
	Build: PreorderOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "R(x, x)",
	}),
})}

// TransitiveOn — two steps within the carrier compose to one.
var TransitiveOn = transitiveOnThm{family.Add(registry.ProofEntry{
	Name: "TransitiveOn",
	Key:  "prop_e06ad7e48770067c",
	Build: PreorderOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"z ∈ c",
			"R(x, y)",
			"R(y, z)",
		},
		Conclusion: "R(x, z)",
	}),
})}

// PreorderOnUniverse — a preorder on the whole type is a preorder:
// membership in Universe discharges every guard in the carrier axioms.
var PreorderOnUniverse = preorderOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "PreorderOnUniverse",
	Key:  "prop_1ed5390a34286fb7",
	Build: family.Theorem("∀R:(A → A → bool). preorder(R) ⇔ preorder_on(𝕌, R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Show(
				"every point lies in Universe, so both predicates state the same two properties",
				Unfold(Preorder),
				Unfold(equivalence.ReflexiveDef),
				Unfold(equivalence.TransitiveDef),
				Unfold(PreorderOn),
				Simp(Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// PreorderAtUniverse — whole-type laws read the carrier laws at Universe.
var PreorderAtUniverse = Preorder.AtUniverse(
	PreorderOn, PreorderOnUniverse, set_basic.InUniv, set_order.SubsetUniv)

// PartialOrderOnUniverse — a partial order on the whole type is a
// partial order on Universe: the preorder bridge and universal
// membership identify their two defining properties.
var PartialOrderOnUniverse = partialOrderOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "PartialOrderOnUniverse",
	Key:  "prop_d286426c2c614320",
	Build: family.Theorem("∀R:(A → A → bool). partial_order(R) ⇔ partial_order_on(𝕌, R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Show(
				"the preorder bridge and universal membership identify the defining properties",
				Unfold(PartialOrder),
				Unfold(AntisymmetricDef),
				Unfold(PartialOrderOn),
				Simp(Fwd(PreorderOnUniverse), Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// PartialOrderAtUniverse — whole-type partial-order laws read the
// carrier laws at Universe.
var PartialOrderAtUniverse = PartialOrder.AtUniverse(
	PartialOrderOn, PartialOrderOnUniverse, set_basic.InUniv, set_order.SubsetUniv)
