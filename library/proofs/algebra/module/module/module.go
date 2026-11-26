// module.go — the chapter: a module over a commutative ring on a carrier
// set, its axioms, and the first laws they give.
//
// Two parts, marked by banners: the structure and its axioms; the zero
// laws. A module is two values: the ring's six operations and its
// carrier in one value R of the record `ring_ops(A)`, the vectors'
// addition, zero, negation, scaling and carrier in one value M of the
// record `module_ops(A, B)` (module_record). The additive structure is a
// group on M's carrier whose addition commutes there, an abelian group
// on the carrier, so every law of the group and abelian group chapters'
// carrier forms reads at it, written additively. There is no whole-type
// module, so a law here carries no `On` suffix; the members that do are
// named after the predicates they state.

package module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// ringFact and groupFact are the two sub-structure facts a module
// states: the scalars R are a commutative ring on their carrier, and the
// vectors of M a group on theirs under the vector addition.
const ringFact = "comm_ring_on(R)"
const groupFact = "group_on(module_additive_group(M))"

// ModuleOn — `module_on(R, M)`: the vectors of M, of a type B, are a
// module over the commutative ring R of scalars, of a type A. R holds
// the ring's six operations and its carrier, M the vector addition,
// zero, negation, the scalar action and the set of vectors. M is a group
// on its carrier under the vector addition, the addition commutes, the
// carrier is closed under scaling, and scaling distributes over both
// additions, associates with the ring's product and fixes a vector at
// the ring's one — each law for the members of M's carrier.
//
// The carrier is a part of the record because a module's submodules and
// quotients are modules on sets (constitution §Structures, "One proof
// per law"); the n-vectors over a ring are such a module
// (`vec_space.ModuleOn`). The ring's addition and the vectors' share
// `+`, read at their operands' types; the scaling is `c • u`.
var ModuleOn = moduleOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "ModuleOn",
	Key:   "prop_e8c7a6f5b4c43055",
	Const: "module_on",
	Type:  "ring_ops(A) → module_ops(A, B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). module_on(R, M) ⇔ " +
			ringFact + " ∧ " + groupFact + " ∧ " +
			"(∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ u + v = v + u) ∧ " +
			"(∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ c • u ∈ M.carrier) ∧ " +
			"(∀c:A. ∀u v:B. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ M.carrier ⇒ c • (u + v) = c • u + c • v) ∧ " +
			"(∀c d:A. ∀u:B. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ M.carrier ⇒ (c + d) • u = c • u + d • u) ∧ " +
			"(∀c d:A. ∀u:B. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ M.carrier ⇒ (c * d) • u = c • (d • u)) ∧ " +
			"(∀u:B. u ∈ M.carrier ⇒ R.one • u = u)",
	},
})}

// RingOn — the scalars are a commutative ring on their carrier: the
// sub-structure at which every law of the commutative ring chapter
// reads.
var RingOn = ringOnThm{family.Add(registry.ProofEntry{
	Name:  "RingOn",
	Key:   "prop_a16c2550150d56de",
	Build: ModuleOn.Axiom("comm_ring_on(R)"),
})}

// AddGroupOn — the vectors are a group on their carrier under the
// vector addition: the sub-structure at which every law of the group
// chapter's carrier form reads.
var AddGroupOn = addGroupOnThm{family.Add(registry.ProofEntry{
	Name:  "AddGroupOn",
	Key:   "prop_3f0cab1d675b8867",
	Build: ModuleOn.Axiom("group_on(module_additive_group(M))"),
})}

// AddComm — the vector addition commutes on the carrier.
var AddComm = addCommThm{family.Add(registry.ProofEntry{
	Name: "AddComm",
	Key:  "prop_2813de213e21fc69",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀u v:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "u + v = v + u",
	}),
})}

// AddAbelianGroupOn — the vectors are an abelian group on their carrier
// under the vector addition: the abelian group on a set unfolded, its
// group is AddGroupOn and its commutativity AddComm. It is the
// sub-structure at which every law of the abelian group chapter's
// carrier form reads.
var AddAbelianGroupOn = addAbelianGroupOnThm{family.Add(registry.ProofEntry{
	Name: "AddAbelianGroupOn",
	Key:  "prop_9324617df9502877",
	Build: ModuleOn.Law("abelian_group_on(module_additive_group(M))",
		func(a *Argument, module ModuleFact[on.R, on.M]) {
			a.Do(Unfold(abelian_group.AbelianGroupOn), SplitConjAll(
				Case(
					"the vectors are a group on their carrier under +",
					By(AddGroupOn, module)),
				Case(
					"and their addition commutes there",
					By(AddComm, module)),
			))
		}),
})}

// AddMonoidOn — the vectors are a commutative monoid on their carrier
// under the vector addition and the zero: the abelian group's own
// monoid, stated once at the module, the sub-structure at which every
// law of the commutative monoid chapter's carrier form reads.
var AddMonoidOn = addMonoidOnThm{family.Add(registry.ProofEntry{
	Name: "AddMonoidOn",
	Key:  "prop_8345a0bd532a1921",
	Build: ModuleOn.Law("comm_monoid_on(M.carrier, M.add, M.zero)",
		func(a *Argument, module ModuleFact[on.R, on.M]) {
			a.Show(
				"the additive abelian group's monoid",
				By(abelian_group.MonoidOn.Read(AddAbelianGroupOn.Read(module))))
		}),
})}

// SmulIn — the carrier is closed under scaling.
var SmulIn = smulInThm{family.Add(registry.ProofEntry{
	Name: "SmulIn",
	Key:  "prop_bafc1b05fa9f207e",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀c:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "c • u ∈ M.carrier",
	}),
})}

// SmulAddLeft — a scalar distributes over a sum of vectors.
var SmulAddLeft = smulAddLeftThm{family.Add(registry.ProofEntry{
	Name: "SmulAddLeft",
	Key:  "prop_9859c13fd51d4cab",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀c:A. ∀u v:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ M.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "c • (u + v) = c • u + c • v",
	}),
})}

// SmulAddRight — a sum of scalars distributes over a vector.
var SmulAddRight = smulAddRightThm{family.Add(registry.ProofEntry{
	Name: "SmulAddRight",
	Key:  "prop_671eb2273ea9e195",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀c d:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"d ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "(c + d) • u = c • u + d • u",
	}),
})}

// SmulMul — scaling by a product is scaling twice.
var SmulMul = smulMulThm{family.Add(registry.ProofEntry{
	Name: "SmulMul",
	Key:  "prop_5afd59b0b76b6fae",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀c d:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"d ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "c * d • u = c • d • u",
	}),
})}

// SmulOne — the ring's one fixes every vector.
var SmulOne = smulOneThm{family.Add(registry.ProofEntry{
	Name: "SmulOne",
	Key:  "prop_d5f19c2923f5a813",
	Build: ModuleOn.Axiom(Statement{
		Binders: "∀u:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
		},
		Conclusion: "R.one • u = u",
	}),
})}

// RegularModuleOn — a commutative ring on a set is a module over
// itself: the scalars are the ring packed as one record, the vectors its
// members, added by the ring's sum and scaled by its product. Each module
// axiom is a ring axiom: the vectors' group is the ring's additive group,
// the two distributive laws are the ring's, and the scaling associates
// and fixes a vector at one because the product is a monoid on the
// carrier. The proof unfolds the predicate, whose parts of the two
// packed values the unfolding states, and closes one Case per conjunct
// in the definition's order.
var RegularModuleOn = regularModuleOnThm{family.Add(registry.ProofEntry{
	Name: "RegularModuleOn",
	Key:  "prop_3e6454fc1a024186",
	Build: comm_ring.CommRingOn.Law("module_on(R, regular_module(R))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			additive := comm_ring.AddGroupOn.Read(ring)
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			a.Do(Unfold(ModuleOn),
				SplitConjAll(
					Case(
						"the scalars are the ring itself",
						By(ring)),
					Case(
						"the vectors are the ring's additive group",
						Simp(
							Fwd(module_record.ModuleAdditiveGroupDef),
							Fwd(module_record.ModAddDef),
							Fwd(module_record.ModZeroDef),
							Fwd(module_record.ModNegDef),
							Fwd(module_record.ModCarrierDef),
							Rev(module_record.AdditiveGroupDef)),
						By(abelian_group.GroupOn.Read(additive))),
					Case(
						"addition commutes",
						By(abelian_group.CommOn, additive)),
					Case(
						"the carrier is closed under the product",
						By(comm_ring.MulIn, ring)),
					Case(
						"the product distributes over a sum on the right",
						By(comm_ring.LeftDistribOn, ring)),
					Case(
						"and on the left",
						By(comm_ring.RightDistribOn, ring)),
					Case(
						"the product associates",
						By(comm_monoid.AssocOn, mulMonoid)),
					Case(
						"and one is a left identity",
						By(comm_monoid.LeftIdentityOn, mulMonoid)),
				))
		}),
})}

// RegularModuleOverSubring — a commutative ring is a module over each of
// its subrings, the subring scaling by the ring's product: the ring is a
// module over itself, and those scalars restrict to S.
var RegularModuleOverSubring = regularModuleOverSubringThm{family.Add(registry.ProofEntry{
	Name: "RegularModuleOverSubring",
	Key:  "prop_72589b00f4bd04b9",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(A).",
		Hypotheses: []string{
			"subring(R, S)",
		},
		Conclusion: "module_on(restrict_ring(R, S), regular_module(R))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], S *Expr[Set[A]], given Fact) {
			a.Show(
				"R is a module over itself, and its scalars restrict to S",
				By(given, ModuleRestrictScalars.Read(RegularModuleOn.Read(ring)).At(S)))
		}),
})}

// ---------------------------------------------------------------------------
// The zero laws
// ---------------------------------------------------------------------------
//
// Each zero is the one element of the additive group that is its own
// double: the scaled zero equals its own sum through a distributive law,
// and the group's IdempotentIsOneOn, read at the vectors, makes it the
// vectors' zero.

// ModuleRestrictScalars — a module over R is a module over every subring S
// of R, the scalars restricted to S: each law of the action holds at
// the members of S, which are scalars of R.
var ModuleRestrictScalars = moduleRestrictScalarsThm{family.Add(registry.ProofEntry{
	Name: "ModuleRestrictScalars",
	Key:  "prop_e9055b91740b2bbb",
	Build: ModuleOn.Law(Statement{
		Binders: "∀S:set(A).",
		Hypotheses: []string{
			"subring(R, S)",
		},
		Conclusion: "module_on(restrict_ring(R, S), M)",
	},
		func(a *Argument, ambient ModuleFact[on.R, on.M], S *Expr[Set[A]], given Fact) {
			scalars := a.Unfolded(a.Have(
				"S lies in R's carrier",
				"S ⊆ R.carrier",
				By(comm_ring.SubringSubset.Read(given))), set_basic.SubsetDef)
			scaled := a.Have(
				"a member of S scales a vector into M's carrier, being a scalar of R",
				"∀c:A. ∀u:B. c ∈ S ∧ u ∈ M.carrier ⇒ c • u ∈ M.carrier",
				By(SmulIn.Read(ambient), scalars))
			distributes := a.Have(
				"a member of S distributes over a sum of vectors",
				"∀c:A. ∀u v:B. c ∈ S ∧ u ∈ M.carrier ∧ v ∈ M.carrier ⇒ c • (u + v) = c • u + c • v",
				By(SmulAddLeft.Read(ambient), scalars))
			sumOfScalars := a.Have(
				"a sum of members of S distributes over a vector",
				"∀c d:A. ∀u:B. c ∈ S ∧ d ∈ S ∧ u ∈ M.carrier ⇒ (c + d) • u = c • u + d • u",
				By(SmulAddRight.Read(ambient), scalars))
			productOfScalars := a.Have(
				"a product of members of S scales a vector in turn",
				"∀c d:A. ∀u:B. c ∈ S ∧ d ∈ S ∧ u ∈ M.carrier ⇒ (c * d) • u = c • (d • u)",
				By(SmulMul.Read(ambient), scalars))
			a.Show(
				"S's ring, M's group and commuting addition, and "+
					"the four laws of the action make M a module over S",
				By(
					given,
					comm_ring.SubringRingOn.Read(RingOn.Read(ambient)).At(S),
					AddGroupOn.Read(ambient),
					AddComm.Read(ambient),
					scaled,
					distributes,
					sumOfScalars,
					productOfScalars,
					SmulOne.Read(ambient),
					ModuleOn))
		}),
})}

// ZeroSmul — the ring's zero scales every vector to the zero vector:
// R.zero • u is (R.zero + R.zero) • u, which is R.zero • u + R.zero • u.
var ZeroSmul = zeroSmulThm{family.Add(registry.ProofEntry{
	Name: "ZeroSmul",
	Key:  "prop_255790849ed6e4f6",
	Build: ModuleOn.Law(Statement{
		Binders: "∀u:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
		},
		Conclusion: "R.zero • u = M.zero",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], u *Member[B, on.M]) {
			ring := RingOn.Read(module)
			zeroIn := comm_ring.ZeroIn.Read(ring)
			double := a.Have(
				"zero • u is its own double",
				"R.zero • u + R.zero • u = R.zero • u",
				CalcEq(
					Leg(
						a.TermAs[B]("(R.zero + R.zero) • u"),
						"a sum of scalars distributes over u",
						By(SmulAddRight, module, zeroIn, u)),
					FinalLeg(
						"and zero + zero is zero",
						Simp(Fwd(comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring))), Fwd(zeroIn)),
						Basic()),
				))
			a.Show(
				"an element of a group that is its own double is the identity",
				By(double, group.IdempotentIsOneOn.Read(AddGroupOn.Read(module)), module, zeroIn, u, SmulIn))
		}),
})}

// SmulZero — every scalar scales the zero vector to itself: c • M.zero
// is c • (M.zero + M.zero), which is c • M.zero + c • M.zero.
var SmulZero = smulZeroThm{family.Add(registry.ProofEntry{
	Name: "SmulZero",
	Key:  "prop_5e1d9f2298b0955c",
	Build: ModuleOn.Law(Statement{
		Binders: "∀c:A.",
		Hypotheses: []string{
			"c ∈ R.carrier",
		},
		Conclusion: "c • M.zero = M.zero",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], c *Member[A, on.R]) {
			additive := AddGroupOn.Read(module)
			zeroIn := group.OneIn.Read(additive)
			double := a.Have(
				"c • zero is its own double",
				"c • M.zero + c • M.zero = c • M.zero",
				CalcEq(
					Leg(
						a.TermAs[B]("c • (M.zero + M.zero)"),
						"c distributes over a sum of vectors",
						By(SmulAddLeft, module, c, zeroIn)),
					FinalLeg(
						"and zero + zero is zero",
						Simp(Fwd(group.LeftIdentityOn.Read(additive)), Fwd(zeroIn)),
						Basic()),
				))
			a.Show(
				"an element of a group that is its own double is the identity",
				By(double, group.IdempotentIsOneOn.Read(additive), module, c, zeroIn, SmulIn))
		}),
})}

// SmulNeg — a scalar passes through a negation: c • (−u) + c • u is
// c • (−u + u) = c • M.zero = M.zero, so c • (−u) is the inverse of c • u
// in the additive group.
var SmulNeg = smulNegThm{family.Add(registry.ProofEntry{
	Name: "SmulNeg",
	Key:  "prop_d0db96afc6de8137",
	Build: ModuleOn.Law(Statement{
		Binders: "∀c:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "c • -u = -(c • u)",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], c *Member[A, on.R], u *Member[B, on.M]) {
			additive := AddGroupOn.Read(module)
			negU := group.InvIn.Read(additive).At(u)
			cancel := a.Have(
				"the two scalings cancel",
				"c • -u + c • u = M.zero",
				CalcEq(
					Leg(
						a.TermAs[B]("c • (-u + u)"),
						"c distributes over a sum of vectors",
						By(SmulAddLeft.Read(module).At(c, negU, u))),
					Leg(
						a.TermAs[B]("c • M.zero"),
						"and -u + u is the vectors' zero",
						Simp(Fwd(group.LeftInverseOn.Read(additive))),
						Basic()),
					FinalLeg(
						"which c scales to M.zero",
						By(SmulZero.Read(module).At(c))),
				))
			a.Show(
				"a summand that cancels c • u is its inverse",
				By(
					cancel,
					group.InvUniqueOn.Read(additive).At(SmulIn.Read(module).At(c, negU), SmulIn.Read(module).At(c, u))))
		}),
})}

// NegSmul — scaling by a negated scalar negates: (−c) • u + c • u is
// (−c + c) • u, the scaling by R.zero, which is M.zero; so (−c) • u is
// the inverse of c • u in the additive group.
var NegSmul = negSmulThm{family.Add(registry.ProofEntry{
	Name: "NegSmul",
	Key:  "prop_5a6ac81d64534493",
	Build: ModuleOn.Law(Statement{
		Binders: "∀c:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "-c • u = -(c • u)",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], c *Member[A, on.R], u *Member[B, on.M]) {
			ring := RingOn.Read(module)
			negC := comm_ring.NegIn.Read(ring).At(c)
			cancel := a.Have(
				"the two scalings cancel",
				"-c • u + c • u = M.zero",
				CalcEq(
					Leg(
						a.TermAs[B]("(-c + c) • u"),
						"a sum of scalars distributes over u",
						By(SmulAddRight.Read(module).At(negC, c, u))),
					Leg(
						a.TermAs[B]("R.zero • u"),
						"and -c + c is the ring's zero",
						Simp(Fwd(group.LeftInverseOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))))),
						Basic()),
					FinalLeg(
						"which scales u to M.zero",
						By(ZeroSmul.Read(module).At(u))),
				))
			a.Show(
				"a summand that cancels c • u is its inverse",
				By(
					cancel,
					group.InvUniqueOn.Read(AddGroupOn.Read(module)).At(
						SmulIn.Read(module).At(negC, u), SmulIn.Read(module).At(c, u))))
		}),
})}

// NegOneSmul — the negated one negates every vector: (−R.one) • u is
// −(R.one • u) by NegSmul, and R.one fixes u.
var NegOneSmul = negOneSmulThm{family.Add(registry.ProofEntry{
	Name: "NegOneSmul",
	Key:  "prop_a1fac42c3afb09f1",
	Build: ModuleOn.Law(Statement{
		Binders: "∀u:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
		},
		Conclusion: "-R.one • u = -u",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], u *Member[B, on.M]) {
			oneIn := comm_ring.OneIn.Read(RingOn.Read(module))
			a.Show(
				"-R.one scales u to the negative of u",
				CalcEq(
					Leg(
						a.TermAs[B]("-(R.one • u)"),
						"scaling by a negated scalar negates",
						By(NegSmul, module, oneIn, u)),
					FinalLeg(
						"R.one fixes u",
						Simp(Fwd(SmulOne.Read(module))),
						Basic()),
				))
		}),
})}
