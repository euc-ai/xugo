// abelian_group.go — whole-type and carrier groups whose product commutes.

package abelian_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AbelianGroup — G's operation is a whole-type group operation and
// commutes on the whole type. The record supplies G.mul, G.one and
// G.inv; the predicate does not constrain G.carrier. Group is its
// group projection, and x * y means G.mul(x, y).
var AbelianGroup = abelianGroupThm{family.DefineStructure(registry.DefEntry{
	Name:    "AbelianGroup",
	Key:     "prop_3fb6712154a94c08",
	Const:   "abelian_group",
	Subject: "G",
	Type:    "group_ops(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). abelian_group(G) ⇔ group(G) ∧ (∀x y:A. G.mul(x, y) = G.mul(y, x))",
	},
})}

// AbelianGroupOn — G is a group and its product commutes on its carrier.
var AbelianGroupOn = abelianGroupOnThm{family.DefineStructure(registry.DefEntry{
	Name: "AbelianGroupOn",
	Key:  "prop_47d61c0c43a38c97",

	Const:   "abelian_group_on",
	Subject: "G",
	Type:    "group_ops(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"    abelian_group_on(G) ⇔ " +
			"    group_on(G) ∧ (∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ G.mul(x, y) = G.mul(y, x))",
	},
})}

// AbelianGroupOnUniverse — an abelian group on the whole type is an
// abelian group: the group on 𝕌 is the group, and every membership in 𝕌
// holds.
var AbelianGroupOnUniverse = abelianGroupOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "AbelianGroupOnUniverse",
	Key:  "prop_81441fa473ac4311",
	Build: family.Theorem("∀G:group_ops(A). abelian_group(G) ⇔ abelian_group_on(restrict_group(G, 𝕌))",
		func(a *Argument, G *Expr[GroupOps[A]]) {
			a.Show(
				"the group conjunct is the group on 𝕌, and the commutative law loses its guards",
				Unfold(AbelianGroup),
				Unfold(AbelianGroupOn),
				Simp(Fwd(group.GroupOnUniverse), Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// AbelianGroupAtUniverse — the whole-type abelian group is the abelian
// group on 𝕌: a law is proved once on the carrier set, and the
// whole-type member is its view through this door.
var AbelianGroupAtUniverse = AbelianGroup.AtUniverseRecord(
	AbelianGroupOn, AbelianGroupOnUniverse, "restrict_group(G, 𝕌)", set_basic.InUniv)

// Group — the abelian group is a group: the sub-structure at which the
// group chapter's laws apply.
var Group = groupThm{family.Add(registry.ProofEntry{
	Name:  "Group",
	Key:   "prop_c0b2c7bbe88bf3ee",
	Build: AbelianGroup.Axiom("group(G)"),
})}

// GroupOn — the abelian group on c is a group on c: the sub-structure at
// which the group chapter's carrier laws apply.
var GroupOn = groupOnThm{family.Add(registry.ProofEntry{
	Name: "GroupOn",
	Key:  "prop_b719aef2546e6131",

	Build: AbelianGroupOn.Axiom("group_on(G)"),
})}

// CommOn — the operation commutes on the carrier.
var CommOn = commOnThm{family.Add(registry.ProofEntry{
	Name: "CommOn",
	Key:  "prop_c3c35f1b543f0774",

	Build: AbelianGroupOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "x * y = y * x",
	}),
})}

// Comm — CommOn on the whole type.
var Comm = commThm{family.Add(registry.ProofEntry{
	Name:  "Comm",
	Key:   "prop_a14a41f02a368273",
	Build: AbelianGroupAtUniverse.Law("∀x y:A. x * y = y * x", CommOn),
})}

// Monoid — the operation and its identity form a commutative monoid: the
// monoid's three axioms are commutativity and the group's associativity
// and left identity.
var Monoid = monoidThm{family.Add(registry.ProofEntry{
	Name: "Monoid",
	Key:  "prop_52afd8dfecf08a92",
	Build: AbelianGroup.Law("comm_monoid(G.mul, G.one)",
		func(a *Argument, abelian Fact) {
			additive := Read(Group, abelian)
			a.Do(Unfold(comm_monoid.CommMonoid), SplitConjAll(
				Case(
					"the operation commutes",
					By(Comm, abelian)),
				Case(
					"it associates, being a group's",
					By(Read(group.Assoc, additive))),
				Case(
					"zero is its left identity, being the group's",
					By(Read(group.LeftIdentity, additive))),
			))
		}),
})}

// MonoidOn — the operation and its identity form a commutative monoid on
// the carrier: the monoid's closure and its three axioms are the group's
// on c and commutativity.
var MonoidOn = monoidOnThm{family.Add(registry.ProofEntry{
	Name: "MonoidOn",
	Key:  "prop_b6d723f1d01c350c",

	Build: AbelianGroupOn.Law("comm_monoid_on(G.carrier, G.mul, G.one)",
		func(a *Argument, abelian AbelianGroupFact[on.G]) {
			additive := Read(GroupOn, abelian)
			a.Do(Unfold(comm_monoid.CommMonoidOn), SplitConjAll(
				Case(
					"the identity lies in G.carrier, being the group's identity",
					By(group.OneIn.Read(additive))),
				Case(
					"G.carrier is closed under the product, being the group's carrier",
					By(group.MulIn.Read(additive))),
				Case(
					"the operation commutes",
					By(CommOn, abelian)),
				Case(
					"it associates, being a group's",
					By(group.AssocOn.Read(additive))),
				Case(
					"the identity is its left identity, being the group's",
					By(group.LeftIdentityOn.Read(additive))),
			))
		}),
})}

// NegAddOn — the inverse of a product is the sum of the inverses. In any
// group it is the sum of the inverses in the OTHER order
// (group.InvMulOn); here the order does not matter.
var NegAddOn = negAddOnThm{family.Add(registry.ProofEntry{
	Name: "NegAddOn",
	Key:  "prop_d671488071126a60",

	Build: AbelianGroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "G.inv(x * y) = G.inv(x) * G.inv(y)",
	},
		func(a *Argument, abelian AbelianGroupFact[on.G], x, y *Member[A, on.G]) {
			additive := a.Have(
				"the abelian group on G.carrier is a group on G.carrier",
				"group_on(G)",
				By(GroupOn, abelian))
			a.Show(
				"the inverse of a product is the other order's product of inverses, and the order does not matter",
				CalcEq(
					Leg(
						a.TermAs[A]("G.inv(y) * G.inv(x)"),
						"the group's inverse of a product",
						By(group.InvMulOn.Read(additive), x, y)),
					FinalLeg(
						"and the product commutes",
						By(CommOn, abelian, x, y, additive, group.InvIn)),
				))
		}),
})}

// NegAdd — NegAddOn on the whole type.
var NegAdd = negAddThm{family.Add(registry.ProofEntry{
	Name:  "NegAdd",
	Key:   "prop_c71d709727d56008",
	Build: AbelianGroupAtUniverse.Law("∀x y:A. G.inv(x * y) = G.inv(x) * G.inv(y)", NegAddOn),
})}
