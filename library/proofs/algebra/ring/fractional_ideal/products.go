// products.go — the module algebra of fractional ideals: the field as a
// module over a subring S, a fractional ideal holding the finite sums of
// its members; the product M · N, the colon of a fractional
// ideal by a subset of the field and the inverse (S : M) as S-submodules
// of it; the product's universal property and the laws it obeys; and
// (S : M) as the one fractional ideal whose product with M is S when
// there is one.

package fractional_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The field as a module over a subring
// ---------------------------------------------------------------------------

// FieldModuleOn — the field is a module over each of its subrings, the
// subring acting by the field's product. Unfolding module_on, the ring of
// scalars is the hypothesis on S; the vectors' group and the commutativity
// of their sum are the field's additive group; and each axiom where a
// scalar meets a vector — closure, the two distributive laws, the
// associativity of scaling — is a law of the field's ring read at a scalar
// of S as a member of L, since S lies in L, while one fixes every vector as
// the identity of the field's product.
var FieldModuleOn = fieldModuleOnThm{family.Add(registry.ProofEntry{
	Name: "FieldModuleOn",
	Key:  "prop_45dadaa44e2bd868",
	Reading: "S ⊆ L.carrier is what keeps a scaled member inside the carrier; " +
		"every module law is a ring law of the field read at members of L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "module_on(«wfScalars», «wfField»)",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
			ringL := field.RingOn.Read(L)
			scalarsInL := a.Unfolded(a.Have(
				"S lies in the field",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring))), set_basic.SubsetDef)
			additive := comm_ring.AddGroupOn.Read(ringL)
			multiplicative := comm_ring.MulMonoidOn.Read(ringL)
			a.Show(
				"so L is a module over S, its scalars' ring the "+
					"hypothesis on S and every other axiom a law of the field",
				Unfold(module.ModuleOn),
				SplitConjAll(
					Case(
						"the scalars form a ring, S being a subring",
						By(subring, comm_ring.SubringRingOn.Read(ringL).At(S))),
					Case(
						"L is a group under the field's sum, the additive group of its ring",
						Simp(Fwd(module_record.ModuleAdditiveGroupDef)),
						By(abelian_group.GroupOn.Read(additive), module_record.AdditiveGroupDef)),
					Case(
						"whose sum commutes",
						By(abelian_group.CommOn.Read(additive))),
					Case(
						"a scalar of S lies in L, so its product with a vector of L does",
						By(scalarsInL, comm_ring.MulIn.Read(ringL))),
					Case(
						"a scalar distributes over a sum of vectors, by distributivity in L",
						By(scalarsInL, comm_ring.LeftDistribOn.Read(ringL))),
					Case(
						"a sum of scalars distributes over a vector, likewise",
						By(scalarsInL, comm_ring.RightDistribOn.Read(ringL))),
					Case(
						"scaling by a product is scaling twice, the field's product associating",
						By(scalarsInL, comm_monoid.AssocOn.Read(multiplicative))),
					Case(
						"and one fixes every vector, being the identity of the field's product",
						By(comm_monoid.LeftIdentityOn.Read(multiplicative))),
				))
		}),
})}

// SubringSubmodule — a subring of the field is a fractional ideal of
// itself: S is an S-submodule of L. Under the field's addition S is a
// group inside L, so an additive subgroup of it, and the product of two
// members of S stays in S.
var SubringSubmodule = subringSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "SubringSubmodule",
	Key:  "prop_98ffa1df2d11c91c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "«wfFractional»(S)",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
			ring := a.Have(
				"S is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			additive := a.Have(
				"a group under the field's addition inside L, S is an additive subgroup of L",
				"subgroup(additive_group(field_ring(L)), S)",
				By(
					group.SubgroupGroupOn.Read(
						abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(field.RingOn.Read(L)))).At(
						S),
					comm_ring.SubringSubset.Read(subring),
					abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring)),
					group.RestrictGroupDef,
					module_record.AdditiveGroupDef))
			a.Show(
				"closed under the product by its own members, it is an S-submodule of the field",
				Simp(Fwd(submodule.SubmoduleDef), Fwd(module_record.ModuleAdditiveGroupDef)),
				By(additive, module_record.AdditiveGroupDef, comm_ring.MulIn.Read(ring)))
		}),
})}

// IntegralIdealFractional — integral ideals are precisely the fractional
// submodules contained in the scalar ring: both directions read their closure laws.
var IntegralIdealFractional = integralIdealFractionalThm{family.Add(registry.ProofEntry{
	Name: "IntegralIdealFractional",
	Key:  "prop_98e4ad8e6100f68b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "ring_ideal(restrict_ring(field_ring(L), S), I) ⇔ " +
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), I) ∧ I ⊆ S",
	},
		func(a *Argument, L field.FieldFact[on.L], S, I *Expr[Set[A]], h Fact) {
			r := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			a.Iff()
			a.Forward(
				"an ideal is an S-submodule contained in S",
				func(b *Argument, ideal Fact) {
					contained := b.Have(
						"the ideal lies in S",
						"I ⊆ S",
						By(ideal, ring_ideal.IdealSubset.At(r, I)))
					inField := b.Have(
						"so it lies in L",
						"I ⊆ L.carrier",
						BySets(contained, comm_ring.SubringSubset.Read(h)))
					fractional := b.Have(
						"the ideal laws give the submodule criterion",
						"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), I)",
						By(
							ideal,
							inField,
							h,
							FieldModuleOn.Read(L).At(S),
							ring_ideal.RingIdealDef.At(r, I),
							submodule.SubmoduleCriterion.At(r, vectors, I)))
					b.Show(
						"the ideal is fractional and integral",
						By(fractional, contained))
				})
			a.Backward(
				"an S-submodule contained in S obeys the ideal laws",
				func(b *Argument, integral Fact) {
					b.Show(
						"the submodule laws are the ideal laws on S",
						By(
							integral,
							submodule.SubmoduleZero.At(r, vectors, I),
							At(submodule.SubmoduleAdd, r, vectors, I),
							At(submodule.SubmoduleSmul, r, vectors, I),
							ring_ideal.RingIdealDef.At(r, I)))
				})
		}),
})}

// FractionalSumIn — a finite sum of members of a fractional ideal lies in
// it: a fractional ideal P is an S-submodule of the field, so an S-module
// under the field's operations, and a module holds the finite sums of its
// members.
var FractionalSumIn = fractionalSumInThm{family.Add(registry.ProofEntry{
	Name: "FractionalSumIn",
	Key:  "prop_27422ad744108b60",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S P:set(A). ∀n:num. ∀F:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfFractional»(P)",
			"∀i:num. i < n ⇒ F(i) ∈ P",
		},
		Conclusion: "module_sum(L.add, L.zero, {i:num | i < n}, F) ∈ P",
		Abbrev: Abbrev{
			{Name: "fieldModuleOn", Text: "restrict_module(regular_module(field_ring(L)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, P *Expr[Set[A]],
			n *Expr[Nat],
			F *Arrow[Nat, A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"S is a subring of the field",
				"P is a fractional ideal",
				"and holds every F(i)")
			subring, fractional, terms := parts[0], parts[1], parts[2]
			fieldModule := a.Have(
				"the field is an S-module",
				"module_on(«wfScalars», «wfField»)",
				By(FieldModuleOn.Read(L).At(S), subring))
			pModule := a.Have(
				"so P is an S-module under the field's operations",
				"module_on(«wfScalars», «fieldModuleOn»(P))",
				By(
					fractional,
					submodule.SubmoduleModuleOn.Read(fieldModule).At(P),
					module_record.RestrictModuleDef.At(a.TermAs[module_record.ModuleOps[A, A]]("«wfField»"), P)))
			finiteBelow := a.Have(
				"the indices below n are finitely many",
				"finite({i:num | i < n})",
				Cite(num_segment.FiniteBelowStrict))
			a.Show(
				"a module holds the finite sums of its members",
				By(
					finiteBelow,
					terms,
					module.ModuleSumIn.Read(pModule).At(a.TermAs[Set[Nat]]("{i:num | i < n}"), F)))
		}),
})}

// SpanHoldingOne — a subset X of the subring S holding one spans S: the
// S-submodule of L that X spans is S itself. S is an S-submodule of L
// holding X (SubringSubmodule), so the span lies in S; and every
// S-submodule holding X holds one, so every r = r · one of S, which puts
// S in the span, the meet of those submodules.
var SpanHoldingOne = spanHoldingOneThm{family.Add(registry.ProofEntry{
	Name: "SpanHoldingOne",
	Key:  "prop_7e80223c8ce45e18",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"X ⊆ S",
			"L.one ∈ X",
		},
		Conclusion: "«wfSpan»(X) = S",
	},
		func(a *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"X lies in S",
				"and holds one")
			subring, inS, oneIn := parts[0], parts[1], parts[2]
			ring := a.Have(
				"S is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			within := a.Have(
				"the span of X lies in S, a submodule holding X",
				"«wfSpan»(X) ⊆ S",
				By(submodule.SpanLeast, SubringSubmodule.Read(L).At(S), subring, inS))
			everySubmodule := a.Have(
				"a submodule holding X holds L.one, so every r = r · L.one of S",
				"∀N:set(A). «wfFractional»(N) ∧ X ⊆ N ⇒ S ⊆ N",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					holding := b.Conjuncts(
						b.Assume(),
						"N is an S-submodule of the field",
						"holding X")
					oneInN := b.Have(
						"so N holds one",
						"L.one ∈ N",
						By(holding[1], oneIn, set_basic.SubsetDef))
					b.Do(Unfold(set_basic.SubsetDef))
					b.FixAs[A]("r")
					rIn := b.Assume()
					scaled := b.Have(
						"N, an S-submodule, holds r · one",
						"r * L.one ∈ N",
						By(submodule.SubmoduleSmul.Read(holding[0]), rIn, oneInN))
					b.Show(
						"so it holds r",
						By(Normalized, scaled, comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)), rIn))
				}))
			spanning := a.Have(
				"so S lies in their meet, the span of X",
				"S ⊆ «wfSpan»(X)",
				Unfold(submodule.ModuleSpanDef),
				BySets(everySubmodule))
			a.Show(
				"the span of X lies in S and holds it, so it is S",
				By(within, spanning, set_order.SubsetAntisym))
		}),
})}

// SpanHoldingUnit — a subset X of a subring S of the field that holds a
// unit u of S spans S: the S-submodule of L that X spans holds u, so it
// holds v · u = one for the inverse v of u, and a submodule of S holding
// one is S (SpanHoldingOne, read at the span itself).
var SpanHoldingUnit = spanHoldingUnitThm{family.Add(registry.ProofEntry{
	Name: "SpanHoldingUnit",
	Key:  "prop_39616096d966a70d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X:set(A). ∀u v:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"X ⊆ S",
			"u ∈ X",
			"v ∈ S",
			"u * v = L.one",
		},
		Conclusion: "«wfSpan»(X) = S",
	},
		func(a *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], u, v *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"S is a subring of L",
				"X lies in S",
				"u lies in X",
				"v lies in S",
				"and u · v = one")
			subring, xInS, uInX, vInS, unit := parts[0], parts[1], parts[2], parts[3], parts[4]
			ring := a.Have(
				"S is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			spanned := a.TermAs[Set[A]]("«wfSpan»(X)")
			module := a.Have(
				"L is a module over S",
				"module_on(«wfScalars», «wfField»)",
				By(subring, FieldModuleOn.Read(L).At(S)))
			spanSubmodule := a.Have(
				"the span of X, a subset of L, is an S-submodule of L",
				"«wfFractional»(«wfSpan»(X))",
				By(
					comm_ring.SubringSubset.Read(subring),
					xInS,
					submodule.SpanSubmodule.Read(module).At(X),
					set_order.SubsetTrans))
			uInSpan := a.Have(
				"u lies in X, so in its span",
				"u ∈ «wfSpan»(X)",
				BySets(uInX, submodule.SubsetSpan.At(scalars, vectors, X)))
			uInS := a.Have(
				"and in S",
				"u ∈ S",
				BySets(uInX, xInS))
			inverse := a.Have(
				"v · u = u · v = one in the commutative ring S",
				"v * u = L.one",
				By(
					Normalized,
					unit,
					comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(
						proof.MemberOf(v, vInS), proof.MemberOf(u, uInS))))
			oneInSpan := a.Have(
				"so the span, an S-submodule holding u, holds v · u = one",
				"L.one ∈ «wfSpan»(X)",
				By(
					inverse,
					submodule.SubmoduleSmul.Read(spanSubmodule).At(
						proof.MemberOf(v, vInS), proof.MemberOf(u, uInSpan))))
			within := a.Have(
				"the span lies in S, an S-submodule of L holding X",
				"«wfSpan»(X) ⊆ S",
				By(subring, xInS, SubringSubmodule.Read(L).At(S), submodule.SpanLeast.At(scalars, vectors, X, S)))
			a.Show(
				"the span is its own span, and a subset of S holding one spans S",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfSpan»(«wfSpan»(X))"),
						"a submodule is its own span",
						By(spanSubmodule, submodule.SpanOfSubmodule.At(scalars, vectors, spanned))),
					FinalLeg(
						"the span lies in S and holds one",
						By(subring, within, oneInSpan, SpanHoldingOne.Read(L).At(S, spanned)))))
		}),
})}

// SpanInSubringIsIdealSpan — a subset of the subring spans, inside the
// field, the ideal it generates in the subring: the S-submodule of L that
// X spans is the ideal of S generated by X. S is an S-submodule of L holding
// X, so the module span lies in S, where a submodule is an ideal; holding X,
// it contains the ideal span. Conversely an ideal of S is an S-submodule of
// L, so the ideal span, holding X, contains the module span.
var SpanInSubringIsIdealSpan = spanInSubringIsIdealSpanThm{family.Add(registry.ProofEntry{
	Name: "SpanInSubringIsIdealSpan",
	Key:  "prop_683c1b79a2ae4fca",
	Reading: "X ⊆ S is load-bearing: a member of X outside S would make the span " +
		"leave S, and the ideal span is then ⋂∅ = 𝕌. At X = ∅ both sides are {L.zero}.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"X ⊆ S",
		},
		Conclusion: "«wfSpan»(X) = ideal_span(restrict_ring(field_ring(L), S), X)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of L",
				"X lies in S")
			subring, xInS := parts[0], parts[1]
			scalars := a.TermAs[RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			span := a.TermAs[Set[A]]("«wfSpan»(X)")
			idealSpan := a.TermAs[Set[A]]("ideal_span(«wfScalars», X)")
			ringS := a.Have(
				"S is a commutative ring under the field's operations",
				"comm_ring_on(«wfScalars»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			spanInS := a.Have(
				"S is an S-submodule of L holding X, so the module span lies in S by minimality",
				"«wfSpan»(X) ⊆ S",
				By(subring, SubringSubmodule.Read(L).At(S), xInS, submodule.SpanLeast.At(scalars, vectors, X, S)))
			spanSubmodule := a.Have(
				"X lies in L, a module over S, so the module span is an S-submodule of L",
				"«wfFractional»(«wfSpan»(X))",
				BySets(
					subring,
					FieldModuleOn.Read(L).At(S),
					xInS,
					comm_ring.SubringSubset.Read(subring),
					submodule.SpanSubmodule.At(scalars, vectors, X)))
			spanIdeal := a.Have(
				"contained in S, the module span is an ideal of S",
				"«wfIdeal»(«wfSpan»(X))",
				By(subring, spanSubmodule, spanInS, IntegralIdealFractional.Read(L).At(S, span)))
			idealInSpan := a.Have(
				"the module span holds X, so minimality puts the ideal span inside it",
				"ideal_span(«wfScalars», X) ⊆ «wfSpan»(X)",
				By(spanIdeal, submodule.SubsetSpan, ring_ideal.SpanLeast.At(scalars, X, span)))
			idealSpanSubmodule := a.Have(
				"the ideal span, an ideal of S, is an S-submodule of L",
				"«wfFractional»(ideal_span(«wfScalars», X))",
				By(
					subring,
					xInS,
					ring_ideal.SpanIdeal.Read(ringS).At(X),
					IntegralIdealFractional.Read(L).At(S, idealSpan)))
			spanInIdeal := a.Have(
				"the ideal span holds X, so minimality puts the module span inside it",
				"«wfSpan»(X) ⊆ ideal_span(«wfScalars», X)",
				By(
					idealSpanSubmodule,
					ring_ideal.SpanContains,
					submodule.SpanLeast.At(scalars, vectors, X, idealSpan)))
			a.Show(
				"the two spans are equal by inclusion in both directions",
				By(idealInSpan, spanInIdeal, set_order.SubsetAntisym))
		}),
})}

// SubringTowerSpan — spanning sets multiply over a tower of rings inside
// the field, the subring form of field_extension.TowerSpan: B spanning S
// over R and C spanning I over S give the products b * c spanning I over
// R. Multiplication by c is R-linear, so it carries S, the R-span of B,
// onto the R-span of the multiples c * b, which are products; a member of
// I is an S-combination of members of C, each term s * c one of those
// multiples, and the R-span of the products is closed under sums. The
// products lie in I, an S-submodule, so their span does too.
var SubringTowerSpan = subringTowerSpanThm{family.Add(registry.ProofEntry{
	Name: "SubringTowerSpan",
	Key:  "prop_4427ec88bd5ba6b2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀R S I B C:set(A).",
		Hypotheses: []string{
			"R ⊆ S",
			"subring(field_ring(L), R)",
			"subring(field_ring(L), S)",
			"C ⊆ L.carrier",
			"module_span(«ringOn»(R), «moduleOn»(S), B) = S",
			"module_span(«wfScalars», «wfField», C) = I",
		},
		Conclusion: "«subringTowerSpanned» = I",
		Abbrev: Abbrev{
			{Name: "ringOn", Text: "restrict_ring(field_ring(L))"},
			{Name: "moduleOn", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "subringTowerProducts", Text: "{b * c | b:A, c:A | b ∈ B ∧ c ∈ C}"},
			{Name: "subringTowerSpanned", Text: "module_span(«ringOn»(R), «wfField», «subringTowerProducts»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], R, S, I, B, C *Expr[Set[A]], tower Fact) {
			h := a.Conjuncts(
				tower,
				"R lies in S",
				"R is a subring of L",
				"and so is S",
				"C lies in L",
				"B spans S over R",
				"C spans I over S")
			rInS, subringR, subringS, cInL, spanB, spanC := h[0], h[1], h[2], h[3], h[4], h[5]
			carrier := a.TermAs[Set[A]]("L.carrier")
			scalars := a.TermAs[module_record.RingOps[A]]("«ringOn»(R)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			products, spanned :=
				a.TermAs[Set[A]]("«subringTowerProducts»"), a.TermAs[Set[A]]("«subringTowerSpanned»")
			ringL := field.RingOn.Read(L)

			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringS)))
			overS := a.Have(
				"L is a module over S",
				"module_on(«wfScalars», «wfField»)",
				By(subringS, FieldModuleOn.Read(L).At(S)))
			overR := a.Have(
				"and over R",
				"module_on(«ringOn»(R), «wfField»)",
				By(subringR, FieldModuleOn.Read(L).At(R)))
			sOverS := a.Have(
				"S is an S-submodule of L",
				"«wfFractional»(S)",
				By(subringS, SubringSubmodule.Read(L).At(S)))
			spansInL := a.Conjuncts(
				a.Have(
					"S is an R-submodule, R lying in S, so B, spanning "+
						"it over R inside S, lies in S and spans it inside L",
					"B ⊆ S ∧ module_span(«ringOn»(R), «wfField», B) = S",
					By(
						rInS,
						submodule.SubmoduleRestrictScalars.Read(sOverS).At(scalars),
						spanB,
						linear_independence.SpanningRestrict.Read(overR).At(S, B),
						module_record.RestrictModuleDef.At(vectors, S))),
				"B lies in S",
				"B spans S over R inside L")
			bInS, spanInL := spansInL[0], spansInL[1]
			bInL := a.Have(
				"so B lies in L",
				"B ⊆ L.carrier",
				By(bInS, sInL, set_order.SubsetTrans.At(B, S, carrier)))

			iOverS := a.Have(
				"I, the S-span of C, is an S-submodule of L",
				"«wfFractional»(I)",
				spanC.RwRev(),
				By(cInL, submodule.SpanSubmodule.Read(overS).At(C)))
			cInI := a.Have(
				"C lies in every submodule holding it, so in their meet I",
				"C ⊆ I",
				BySets(a.Unfolded(spanC, submodule.ModuleSpanDef)))
			closedI := a.Have(
				"I is closed under multiplication by S",
				"∀x y:A. x ∈ S ∧ y ∈ I ⇒ x * y ∈ I",
				By(submodule.SubmoduleSmul.Read(iOverS)))
			productsInI := a.Have(
				"the products lie in I",
				"«subringTowerProducts» ⊆ I",
				BySets(bInS, cInI, closedI))
			productsInL := a.Have(
				"and so in L",
				"«subringTowerProducts» ⊆ L.carrier",
				By(
					productsInI,
					submodule.SubmoduleSubset.Read(iOverS),
					set_order.SubsetTrans.At(products, I, carrier)))

			multiples := a.Have(
				"for c in C, the multiples of S by c lie in the R-span of the products",
				"∀c:A. c ∈ C ⇒ image(L.mul(c), S) ⊆ «subringTowerSpanned»",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cInC := b.Assume()
					cm := b.MemberOf[on.L](c, b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(cInC, cInL)))
					scale := b.TermAs[Fun[A, A]]("L.mul(c)")
					image := b.Have(
						"multiplication by c is R-linear, so it carries S, the "+
							"R-span of B, onto the R-span of the multiples c * b",
						"image(L.mul(c), S) = module_span(«ringOn»(R), «wfField», image(L.mul(c), B))",
						spanInL.RwRev(),
						By(
							subringR,
							field_extension.ScaleLinear.Read(L).At(R, cm),
							bInL,
							linear_independence.HomSpan.At(scalars, vectors, vectors, scale, B)))
					commuting := b.Have(
						"each multiple c * x of a member x of B is the product x * c",
						"∀x:A. x ∈ B ⇒ c * x ∈ «subringTowerProducts»",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							xInB := d.Assume()
							xm := d.MemberOf[on.L](x, d.Have(
								"x lies in L",
								"x ∈ L.carrier",
								BySets(xInB, bInL)))
							swap := d.Have(
								"the field's product commutes",
								"c * x = x * c",
								By(comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ringL)).At(cm, xm)))
							d.Show(
								"so c * x is the product x * c",
								swap.Rw(),
								BySets(xInB, cInC))
						}))
					within := b.Have(
						"so the multiples of B by c are products",
						"image(L.mul(c), B) ⊆ «subringTowerProducts»",
						Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
						By(commuting))
					b.Show(
						"so the multiples of S lie in the span of the products",
						image.Rw(),
						By(
							within,
							submodule.SpanMono.At(scalars, vectors, b.TermAs[Set[A]]("image(L.mul(c), B)"), products)))
				}))

			everyMember := a.Have(
				"a member of I is an S-combination of members of C, each term in the span of the products",
				"∀v:A. v ∈ I ⇒ v ∈ «subringTowerSpanned»",
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					inI := b.Assume()
					T, _, expansion := b.Obtain2As[Set[A], Fun[A, A]](
						"v is an S-combination of finitely many members of C",
						"∃T:set(A). ∃s:(A → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ C ∧ "+
							"    (∀x:A. x ∈ T ⇒ s(x) ∈ S) ∧ "+
							"    v = module_sum(L.add, L.zero, T, λx:A. s(x) * x)",
						By(inI, spanC, cInL, linear_independence.SpanMembership.Read(overS).At(C, v)))
					overC := b.Conjuncts(
						expansion,
						"T is finite",
						"T lies in C",
						"the coefficients s(x) lie in S",
						"v is their combination")
					terms := b.Have(
						"each term s(x) * x lies in the span of the products",
						"∀x:A. x ∈ T ⇒ s(x) * x ∈ «subringTowerSpanned»",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							inT := d.Assume()
							parts := d.Have(
								"x lies in C and in L, and s(x) in S and in L",
								"x ∈ C ∧ x ∈ L.carrier ∧ s(x) ∈ S ∧ s(x) ∈ L.carrier",
								BySets(inT, overC[1], overC[2], cInL, sInL))
							inSpan := d.Have(
								"x * s(x), a multiple of a member of S by x, lies in the span of the products",
								"x * s(x) ∈ «subringTowerSpanned»",
								By(
									parts,
									set_image.FunInImage.At(d.TermAs[Fun[A, A]]("L.mul(x)"), S, d.TermAs[A]("s(x)")),
									multiples.At(x),
									set_basic.SubsetDef))
							swap := d.Have(
								"the field's product commutes",
								"s(x) * x = x * s(x)",
								ByArith(ringL, parts))
							d.Show(
								"and so does s(x) * x",
								swap.Rw(),
								By(inSpan))
						}))
					sum := b.Have(
						"the span, an R-submodule, holds their sum",
						"module_sum(L.add, L.zero, T, λx:A. s(x) * x) ∈ «subringTowerSpanned»",
						By(
							overC[0],
							terms,
							productsInL,
							submodule.SpanSubmodule.Read(overR).At(products),
							submodule.SubmoduleModuleSum.Read(overR).At(spanned, T, b.TermAs[Fun[A, A]]("λx:A. s(x) * x"))))
					b.Show(
						"which is v",
						overC[3].Rw(),
						By(sum))
				}))
			within := a.Have(
				"the span of the products lies in I, an R-submodule holding them",
				"«subringTowerSpanned» ⊆ I",
				By(
					rInS,
					submodule.SubmoduleRestrictScalars.Read(iOverS).At(scalars),
					productsInI,
					submodule.SpanLeast.At(scalars, vectors, products, I)))
			a.Show(
				"so the products span I over R",
				By(within, everyMember, set_basic.SubsetDef, set_order.SubsetAntisym.At(spanned, I)))
		}),
})}

// FractionalMulSubmodule — the product of two subsets of the field is a
// fractional ideal. M · N is the span of the products m * n in the field
// as an S-module, and those products lie in L, which is closed under the
// product: the span of a subset of a module is a submodule.
var FractionalMulSubmodule = fractionalMulSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulSubmodule",
	Key:  "prop_2b9921ad215fff95",
	Reading: "M and N need not be submodules. M ⊆ L.carrier and N ⊆ L.carrier " +
		"keep the products inside the carrier: a set outside L lies in no submodule " +
		"of L, and its span is then the intersection of nothing, the whole type.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfFractional»(«wfMul»(M, N))",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M lies in the field",
				"and so does N")
			subring, mInL, nInL := parts[0], parts[1], parts[2]
			module := a.Have(
				"the field is an S-module, S acting by the field's product",
				"module_on(«wfScalars», «wfField»)",
				By(FieldModuleOn.Read(L).At(S), subring))
			products := a.Have(
				"a member of M times a member of N lies in L, which is closed under the product",
				"{m * n | m:A, n:A | m ∈ M ∧ n ∈ N} ⊆ L.carrier",
				BySets(mInL, nInL, comm_ring.MulIn.Read(field.RingOn.Read(L))))
			a.Show(
				"so M · N, the span of those products, is an S-submodule of the field",
				Unfold(FractionalMulDef),
				By(submodule.SpanSubmodule.Read(module), products))
		}),
})}

// ColonSubmodule — the colon (P : N) of a fractional ideal P by a subset N
// of the field, the members y of L with y * n ∈ P for every n in N, is a
// fractional ideal. It holds zero, as zero * n = zero; and it is closed
// under sums, negatives and S-multiples because the product by each n
// distributes over sums, takes -x to -(x * n) and (c * u) * n to
// c * (u * n), while P is closed under each.
var ColonSubmodule = colonSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ColonSubmodule",
	Key:  "prop_552f6d1bfd6c1ae5",
	Reading: "N ⊆ L.carrier is what the field's laws need: L.zero * n = L.zero and " +
		"(x + y) * n = x * n + y * n hold at members n of L. S ⊆ L.carrier keeps c * u " +
		"in L for c ∈ S; that S is a ring is not used. At N = ∅ the colon is all of L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S P N:set(A).",
		Hypotheses: []string{
			"S ⊆ L.carrier",
			"«wfFractional»(P)",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfFractional»({y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ y * n ∈ P)})",
	},
		func(a *Argument, L field.FieldFact[on.L], S, P, N *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S lies in the field",
				"P is a fractional ideal",
				"and N lies in the field")
			inField, ideal, nInL := parts[0], parts[1], parts[2]
			ring := field.RingOn.Read(L)
			zero := a.Have(
				"zero lies in L, and zero times each n of N is zero, which lies in P",
				"L.zero ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ L.zero * n ∈ P)",
				Derive(func(b *Argument) {
					products := b.Have(
						"L.zero * n = L.zero lies in P for each n of N",
						"∀n:A. n ∈ N ⇒ L.zero * n ∈ P",
						Derive(func(c *Argument) {
							n := c.FixAs[A]()
							nIn := c.Assume()
							nm := c.MemberOf[on.L](n, c.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(nInL, nIn)))
							vanish := c.Have(
								"zero absorbs in L",
								"L.zero * n = L.zero",
								By(comm_ring.MulLeftZeroOn.Read(ring).At(nm)))
							c.Show(
								"so zero * n is zero, a member of P",
								vanish.Rw(),
								By(submodule.SubmoduleZero.Read(ideal)))
						}))
					b.Show(
						"and zero lies in L",
						By(comm_ring.ZeroIn.Read(ring), products))
				}))
			sums := a.Have(
				"sums stay in the colon, the product by each n of N distributing over them",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ L.carrier",
						"∀n:A. n ∈ N ⇒ x * n ∈ P",
						"y ∈ L.carrier",
						"∀n:A. n ∈ N ⇒ y * n ∈ P",
					},
					Conclusion: "x + y ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ (x + y) * n ∈ P)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A](), b.FixAs[A]()
					in := b.Conjuncts(
						b.Assume(),
						"x lies in L",
						"with x * n in P for n in N",
						"y lies in L",
						"with y * n in P for n in N")
					xm, ym := b.MemberOf[on.L](x, in[0]), b.MemberOf[on.L](y, in[2])
					products := b.Have(
						"each (x + y) * n is the sum x * n + y * n of two members of P",
						"∀n:A. n ∈ N ⇒ (x + y) * n ∈ P",
						Derive(func(c *Argument) {
							n := c.FixAs[A]()
							nIn := c.Assume()
							nm := c.MemberOf[on.L](n, c.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(nInL, nIn)))
							distribute := c.Have(
								"the product by n distributes over x + y",
								"(x + y) * n = x * n + y * n",
								By(comm_ring.RightDistribOn.Read(ring).At(xm, ym, nm)))
							c.Show(
								"a sum of two members of P",
								distribute.Rw(),
								By(submodule.SubmoduleAdd.Read(ideal), in[1].At(n), in[3].At(n), nIn))
						}))
					b.Show(
						"x + y lies in L, and so in the colon",
						By(comm_ring.AddIn.Read(ring).At(xm, ym), products))
				}))
			negatives := a.Have(
				"negatives stay in the colon, as -x * n = -(x * n)",
				"∀x:A. x ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ x * n ∈ P) ⇒ -x ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ -x * n ∈ P)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					in := b.Conjuncts(
						b.Assume(),
						"x lies in L",
						"with x * n in P for n in N")
					xm := b.MemberOf[on.L](x, in[0])
					products := b.Have(
						"each -x * n is the negative of a member of P",
						"∀n:A. n ∈ N ⇒ -x * n ∈ P",
						Derive(func(c *Argument) {
							n := c.FixAs[A]()
							nIn := c.Assume()
							nm := c.MemberOf[on.L](n, c.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(nInL, nIn)))
							sign := c.Have(
								"-x times n is the negative of x * n",
								"-x * n = -(x * n)",
								By(comm_ring.MulLeftNegOn.Read(ring).At(xm, nm)))
							c.Show(
								"the negative of a member of P",
								sign.Rw(),
								By(submodule.SubmoduleNeg.Read(ideal), in[1].At(n), nIn))
						}))
					b.Show(
						"-x lies in L, and so in the colon",
						By(comm_ring.NegIn.Read(ring).At(xm), products))
				}))
			multiples := a.Have(
				"S-multiples stay in the colon, as (c * u) * n = c * (u * n)",
				Statement{
					Binders: "∀c u:A.",
					Hypotheses: []string{
						"c ∈ S",
						"u ∈ L.carrier",
						"∀n:A. n ∈ N ⇒ u * n ∈ P",
					},
					Conclusion: "c * u ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ c * u * n ∈ P)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A](), b.FixAs[A]()
					in := b.Conjuncts(
						b.Assume(),
						"c lies in S",
						"u lies in L",
						"with u * n in P for n in N")
					cm := b.MemberOf[on.L](c, b.Have(
						"c lies in L, as S does",
						"c ∈ L.carrier",
						BySets(inField, in[0])))
					um := b.MemberOf[on.L](u, in[1])
					products := b.Have(
						"each (c * u) * n is the S-multiple c * (u * n) of a member of P",
						"∀n:A. n ∈ N ⇒ (c * u) * n ∈ P",
						Derive(func(d *Argument) {
							n := d.FixAs[A]()
							nIn := d.Assume()
							nm := d.MemberOf[on.L](n, d.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(nInL, nIn)))
							regroup := d.Have(
								"the field's product associates",
								"(c * u) * n = c * (u * n)",
								By(comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(cm, um, nm)))
							d.Show(
								"an S-multiple of a member of P",
								regroup.Rw(),
								By(submodule.SubmoduleSmul.Read(ideal), in[0], in[2].At(n), nIn))
						}))
					b.Show(
						"c * u lies in L, and so in the colon",
						By(comm_ring.MulIn.Read(ring).At(cm, um), products))
				}))
			a.Show(
				"so the colon is an additive subgroup of L closed under S-multiples: a fractional ideal",
				Simp(Fwd(submodule.SubmoduleDef), Fwd(group.SubgroupDef)),
				BySets(zero, sums, negatives, multiples))
		}),
})}

// FractionalInverseSubset — the inverse (S : M) lies in the field: it is
// defined as a set of members of L.
var FractionalInverseSubset = fractionalInverseSubsetThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseSubset",
	Key:  "prop_6bc79ad255c4f008",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S M:set(A).",
		Conclusion: "«wfInverse»(M) ⊆ L.carrier",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]]) {
			a.Show(
				"(S : M) is a set of members of L",
				Unfold(FractionalInverseDef),
				BySets())
		}),
})}

// FractionalInverseSubmodule — the inverse (S : M) of a subset M of the
// field is a fractional ideal: it is the colon of S, a fractional ideal of
// itself, by M.
var FractionalInverseSubmodule = fractionalInverseSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseSubmodule",
	Key:  "prop_aea1d074985c1807",
	Reading: "(S : M) is all of L when M is ∅ or {L.zero}. M ⊆ L.carrier " +
		"is load-bearing: the product distributes over a sum of members of L " +
		"only at a second member of L, and L.zero * m = L.zero only there.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"M ⊆ L.carrier",
		},
		Conclusion: "«wfFractional»(«wfInverse»(M))",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M lies in the field")
			isSubring, mInL := parts[0], parts[1]
			a.Show(
				"unfolded, (S : M) is the colon of the fractional ideal S by M",
				Unfold(FractionalInverseDef),
				By(
					ColonSubmodule.Read(L).At(S, S, M),
					comm_ring.SubringSubset.Read(isSubring),
					SubringSubmodule.Read(L).At(S),
					isSubring,
					mInL))
		}),
})}

// ---------------------------------------------------------------------------
// The laws of the product
// ---------------------------------------------------------------------------

// FractionalMulHolds — the product holds the products it is spanned by:
// m * n lies in M · N for m in M and n in N, a span holding the set it
// spans.
var FractionalMulHolds = fractionalMulHoldsThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulHolds",
	Key:  "prop_668f7bd3dfad76d",
	Reading: "No hypothesis on S, M or N: a span holds the set it " +
		"spans, the span of a set no submodule holds being the whole type.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A). ∀m n:A.",
		Hypotheses: []string{
			"m ∈ M",
			"n ∈ N",
		},
		Conclusion: "m * n ∈ «wfMul»(M, N)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], m, n *Expr[A], members Fact) {
			a.Show(
				"M · N is the span of the products m * n, which holds each of them",
				Simp(Fwd(FractionalMulDef)),
				BySets(members, submodule.SubsetSpan))
		}),
})}

// FractionalMulLeast — M · N lies in every fractional ideal holding the
// products m * n, the span of a set lying in every submodule that holds
// the set.
var FractionalMulLeast = fractionalMulLeastThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulLeast",
	Key:  "prop_43d814d33ad805ac",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N P:set(A).",
		Hypotheses: []string{
			"«wfFractional»(P)",
			"∀m n:A. m ∈ M ∧ n ∈ N ⇒ m * n ∈ P",
		},
		Conclusion: "«wfMul»(M, N) ⊆ P",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N, P *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"P is a fractional ideal",
				"holding each product m * n")
			ideal, holding := parts[0], parts[1]
			products := a.Have(
				"the products of M with N lie in P",
				"{m * n | m:A, n:A | m ∈ M ∧ n ∈ N} ⊆ P",
				BySets(holding))
			a.Show(
				"so does their span, M · N",
				Simp(Fwd(FractionalMulDef)),
				By(submodule.SpanLeast, ideal, products))
		}),
})}

// FractionalMulMono — the product grows with its factors: M ⊆ M' and
// N ⊆ N' give M · N ⊆ M' · N', the products of M with N being among those
// of M' with N' and the span monotone.
var FractionalMulMono = fractionalMulMonoThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulMono",
	Key:  "prop_a00128023e7784dd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M M' N N':set(A).",
		Hypotheses: []string{
			"M ⊆ M'",
			"N ⊆ N'",
		},
		Conclusion: "«wfMul»(M, N) ⊆ «wfMul»(M', N')",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, Mp, N, Np *Expr[Set[A]], inclusions Fact) {
			fewer := a.Have(
				"the products of M with N are among those of M' with N'",
				"{m * n | m:A, n:A | m ∈ M ∧ n ∈ N} ⊆ {m * n | m:A, n:A | m ∈ M' ∧ n ∈ N'}",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					product := b.Assume()
					_, _, factors := b.Obtain2As[A, A](
						"x is a product m * n with m in M and n in N",
						"∃m n:A. m ∈ M ∧ n ∈ N ∧ x = m * n",
						BySets(product))
					b.Show(
						"and m lies in M', n in N', so x is one of their products",
						BySets(inclusions, factors))
				}))
			a.Show(
				"so their span lies in the span of the larger set",
				Simp(Fwd(FractionalMulDef)),
				By(fewer, submodule.SpanMono))
		}),
})}

// FractionalMulSpan — the product reads its left factor only through its
// span: span(M) · N = M · N. M lies in span(M), so M · N lies in
// span(M) · N. Conversely the colon (M · N : N) is a fractional ideal
// holding M, hence span(M); so every product of span(M) with N lies in
// M · N, and so does their span.
var FractionalMulSpan = fractionalMulSpanThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulSpan",
	Key:  "prop_7129d40b31429e83",
	Reading: "With FractionalMulComm the same holds on the right, so a " +
		"product of fractional ideals is computed on generators. M ⊆ L.carrier is " +
		"load-bearing: the span of a set with a member outside L is the whole type.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfMul»(«wfSpan»(M), N) = «wfMul»(M, N)",
		Abbrev: Abbrev{
			// The colon (M · N : N): the members y of L with y * n in M · N for every n in N.
			{Name: "colon", Text: "{y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ N ⇒ y * n ∈ «wfMul»(M, N))}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"M lies in the field",
				"and so does N")
			subring, mInL, nInL := parts[0], parts[1], parts[2]
			span, product := a.TermAs[Set[A]]("«wfSpan»(M)"), a.TermAs[Set[A]]("«wfMul»(M, N)")
			fractional := a.Have(
				"M · N is a fractional ideal",
				"«wfFractional»(«wfMul»(M, N))",
				By(FractionalMulSubmodule.Read(L).At(S, M, N), subring, mInL, nInL))
			colonIdeal := a.Have(
				"so is the colon (M · N : N), the members y of L with y * n in M · N for every n in N",
				"«wfFractional»(«colon»)",
				By(
					ColonSubmodule.Read(L).At(S, product, N),
					comm_ring.SubringSubset.Read(subring),
					fractional,
					nInL))
			holdsM := a.Have(
				"each m of M lies in L with m * n in M · N, so the colon holds M",
				"M ⊆ «colon»",
				BySets(mInL, FractionalMulHolds.Read(L)))
			holdsSpan := a.Have(
				"so it holds span(M)",
				"«wfSpan»(M) ⊆ «colon»",
				By(colonIdeal, holdsM, submodule.SpanLeast))
			spanProducts := a.Have(
				"so every product of span(M) with N lies in M · N",
				"∀z n:A. z ∈ «wfSpan»(M) ∧ n ∈ N ⇒ z * n ∈ «wfMul»(M, N)",
				BySets(holdsSpan))
			within := a.Have(
				"span(M) · N lies in M · N, a fractional ideal holding those products",
				"«wfMul»(«wfSpan»(M), N) ⊆ «wfMul»(M, N)",
				By(FractionalMulLeast.Read(L).At(S, span, N, product), fractional, spanProducts))
			spanHoldsM := a.Have(
				"M lies in its span",
				"M ⊆ «wfSpan»(M)",
				Cite(submodule.SubsetSpan))
			covering := a.Have(
				"so M · N lies in span(M) · N",
				"«wfMul»(M, N) ⊆ «wfMul»(«wfSpan»(M), N)",
				By(FractionalMulMono.Read(L).At(S, M, span, N, N), spanHoldsM, set_order.SubsetRefl.At(N)))
			a.Show(
				"the two inclusions are the equation",
				By(within, covering, set_order.SubsetAntisym))
		}),
})}

// FractionalMulSpanRight — the product reads its right factor only through
// its span: M · span(N) = M · N. span(N), a fractional ideal, lies in L;
// commuting the factors puts it on the left, where FractionalMulSpan reads
// it through N, and the factors commute back.
var FractionalMulSpanRight = fractionalMulSpanRightThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulSpanRight",
	Key:  "prop_6b40013c089ac33d",
	Reading: "With FractionalMulSpan a product of fractional ideals is computed on " +
		"generators on either side. N ⊆ L.carrier is load-bearing, as M ⊆ L.carrier is " +
		"there: the span of a set with a member outside L is the whole type.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfMul»(M, «wfSpan»(N)) = «wfMul»(M, N)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"M lies in the field",
				"and so does N")
			subring, mInL, nInL := parts[0], parts[1], parts[2]
			fieldModule := a.Have(
				"L is a module over S",
				"module_on(«wfScalars», «wfField»)",
				By(subring, FieldModuleOn.Read(L).At(S)))
			spanFractional := a.Have(
				"span(N) is a fractional ideal",
				"«wfFractional»(«wfSpan»(N))",
				By(nInL, submodule.SpanSubmodule.Read(fieldModule).At(N)))
			span := a.TermAs[Set[A]]("«wfSpan»(N)")
			a.Show(
				"commute span(N) to the left, read it through N there, and commute back",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfMul»(«wfSpan»(N), M)"),
						"commute the factors",
						By(mInL, submodule.SubmoduleSubset.Read(spanFractional), FractionalMulComm.Read(L).At(S, M, span))),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(N, M)"),
						"the left factor is read through its span",
						By(subring, nInL, mInL, FractionalMulSpan.Read(L).At(S, N, M))),
					FinalLeg(
						"commute back",
						By(nInL, mInL, FractionalMulComm.Read(L).At(S, N, M)))))
		}),
})}

// FractionalMulAssoc — fractional products associate: replacing the spanned
// factors by their generators leaves the same triple products, by
// associativity and commutativity in the ambient field.
var FractionalMulAssoc = fractionalMulAssocThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulAssoc",
	Key:  "prop_ee433634cd1e9915",
	Reading: "Stated for any three subsets of L; they are kept inside L because " +
		"a product with a member outside the carrier is a value nothing is said about.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N P:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
			"P ⊆ L.carrier",
		},
		Conclusion: "«wfMul»(«wfMul»(M, N), P) = «wfMul»(M, «wfMul»(N, P))",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N, P *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"M lies in the field",
				"and so does N",
				"and so does P")
			subring, mInL, nInL, pInL := parts[0], parts[1], parts[2], parts[3]
			ringL := field.RingOn.Read(L)
			U, definedU := a.LetAs[Set[A]]("U", "{m * n | m:A, n:A | m ∈ M ∧ n ∈ N}")
			V, definedV := a.LetAs[Set[A]]("V", "{n * p | n:A, p:A | n ∈ N ∧ p ∈ P}")
			uInL := a.Have(
				"the products generating M · N lie in the field",
				"U ⊆ L.carrier",
				BySets(definedU, mInL, nInL, comm_ring.MulIn.Read(ringL)))
			vInL := a.Have(
				"and so do the products generating N · P",
				"V ⊆ L.carrier",
				BySets(definedV, nInL, pInL, comm_ring.MulIn.Read(ringL)))
			regroup := a.Have(
				"three field members associate and commute",
				"∀m n p:A. m ∈ M ∧ n ∈ N ∧ p ∈ P ⇒ (m * n) * p = (n * p) * m",
				Derive(func(b *Argument) {
					b.FixAs[A]("m")
					b.FixAs[A]("n")
					b.FixAs[A]("p")
					factors := b.Assume()
					inL := b.Have(
						"the three factors lie in the field",
						"m ∈ L.carrier ∧ n ∈ L.carrier ∧ p ∈ L.carrier",
						BySets(factors, mInL, nInL, pInL))
					b.Show(
						"the field's product associates and commutes",
						ByArith(ringL, inL))
				}))
			generators := a.Have(
				"both associated products have the same triple generators",
				"{u * p | u:A, p:A | u ∈ U ∧ p ∈ P} = {v * m | v:A, m:A | v ∈ V ∧ m ∈ M}",
				definedU.Rw(),
				definedV.Rw(),
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("{(m * n) * p | m:A, n:A, p:A | m ∈ M ∧ n ∈ N ∧ p ∈ P}"),
						"flatten a generator of U and a member of P",
						BySets()),
					Leg(
						a.TermAs[Set[A]]("{(n * p) * m | m:A, n:A, p:A | m ∈ M ∧ n ∈ N ∧ p ∈ P}"),
						"regroup the triple products",
						BySets(regroup)),
					Leg(
						a.TermAs[Set[A]]("{(n * p) * m | n:A, p:A, m:A | n ∈ N ∧ p ∈ P ∧ m ∈ M}"),
						"list the same triples starting with N and P",
						BySets()),
					FinalLeg(
						"collect n * p into a generator of V",
						Derive(func(b *Argument) {
							b.Do(Simp(Fwd(set_basic.Extension)))
							b.FixAs[A]("x")
							b.Iff()
							b.Forward(
								"each triple is a product of a generator of V and a member of M",
								func(c *Argument, triple Fact) {
									c.Show(
										"collect the first two factors",
										BySets(triple))
								})
							b.Backward(
								"each product with a generator of V comes from a triple",
								func(c *Argument, product Fact) {
									c.Show(
										"expand the generator into its two factors",
										BySets(product))
								})
						}))))
			mnSpan := a.Have(
				"M · N is the span of U",
				"«wfMul»(M, N) = «wfSpan»(U)",
				Simp(Fwd(FractionalMulDef)),
				definedU.Rw(),
				Basic())
			npSpan := a.Have(
				"N · P is the span of V",
				"«wfMul»(N, P) = «wfSpan»(V)",
				Simp(Fwd(FractionalMulDef)),
				definedV.Rw(),
				Basic())
			left := a.Have(
				"the left associated product is computed on U",
				"«wfMul»(«wfMul»(M, N), P) = «wfMul»(U, P)",
				mnSpan.Rw(),
				By(subring, uInL, pInL, FractionalMulSpan.Read(L).At(S, U, P)))
			right := a.Have(
				"the product of N · P with M is computed on V",
				"«wfMul»(«wfMul»(N, P), M) = «wfMul»(V, M)",
				npSpan.Rw(),
				By(subring, vInL, mInL, FractionalMulSpan.Read(L).At(S, V, M)))
			npModule := a.Have(
				"N · P is a fractional ideal",
				"«wfFractional»(«wfMul»(N, P))",
				By(subring, nInL, pInL, FractionalMulSubmodule.Read(L).At(S, N, P)))
			sameProduct := a.Have(
				"the spans of the equal generator sets agree",
				"«wfMul»(U, P) = «wfMul»(V, M)",
				Simp(Fwd(FractionalMulDef)),
				By(generators))
			commute := a.Have(
				"commute the outer factors on the right",
				"«wfMul»(M, «wfMul»(N, P)) = «wfMul»(«wfMul»(N, P), M)",
				By(
					mInL,
					submodule.SubmoduleSubset.Read(npModule),
					FractionalMulComm.Read(L).At(S, M, a.TermAs[Set[A]]("«wfMul»(N, P)"))))
			a.Show(
				"the two associations are the span of the same triple products",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfMul»(U, P)"),
						"compute the left factor on generators",
						By(left)),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(V, M)"),
						"use the equal triple generator sets",
						By(sameProduct)),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(«wfMul»(N, P), M)"),
						"restore the spanned factor",
						By(right)),
					FinalLeg(
						"commute the outer factors back",
						By(commute))))
		}),
})}

// FractionalMulComm — the product of fractional ideals is commutative.
// M · N and N · M are spans of the products m * n and n * m, and these
// are one set, as the product commutes on L, where M and N lie.
var FractionalMulComm = fractionalMulCommThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulComm",
	Key:  "prop_2e81ce1a47808b82",
	Reading: "No hypothesis on S: both sides are spans over the same " +
		"scalars of one set of products. M ⊆ L.carrier and N ⊆ L.carrier are " +
		"there only for the commutativity of the product, which holds on L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfMul»(M, N) = «wfMul»(N, M)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], inclusions Fact) {
			commute := a.Have(
				"a member of M and a member of N lie in L, where the product commutes",
				"∀m n:A. m ∈ M ∧ n ∈ N ⇒ m * n = n * m",
				BySets(inclusions, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L)))))
			products := a.Have(
				"so the products of M with N are the products of N with M",
				"{m * n | m:A, n:A | m ∈ M ∧ n ∈ N} = {n * m | n:A, m:A | n ∈ N ∧ m ∈ M}",
				BySets(commute))
			a.Show(
				"M · N and N · M are the spans of that one set",
				Simp(Fwd(FractionalMulDef)),
				By(products))
		}),
})}

// FractionalMulOne — S is the unit of the product: S · M = M for a
// fractional ideal M. Each product s · m lies in M, an S-submodule, and
// each m of M is the product one · m with one ∈ S, so the products are
// the members of M, whose span is M.
var FractionalMulOne = fractionalMulOneThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulOne",
	Key:  "prop_2c2ab10c28bb055f",
	Reading: "L.one ∈ S, from comm_ring_on(restrict_ring(field_ring(L), S)), puts M among " +
		"the products; for a subset M of L that is not a submodule, S · M is the span of M.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfFractional»(M)",
		},
		Conclusion: "«wfMul»(S, M) = M",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M is an S-submodule of the field")
			subring, fractional := parts[0], parts[1]
			products := a.Have(
				"the products s · m are the members of M: each lies "+
					"in the S-submodule M, and each m of M is one · m",
				"{s * m | s:A, m:A | s ∈ S ∧ m ∈ M} = M",
				BySets(
					submodule.SubmoduleSmul.Read(fractional),
					comm_ring.SubringOne.Read(subring),
					submodule.SubmoduleSubset.Read(fractional),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L)))))
			a.Show(
				"so S · M is the span of M, a submodule, which is M",
				Simp(Fwd(FractionalMulDef)),
				products.Rw(),
				By(submodule.SpanOfSubmodule.Read(fractional)))
		}),
})}

// FractionalIdealsCommMonoid — the S-submodules of a field form a
// commutative monoid under fractional-ideal multiplication, with S as
// identity. Submodules lie in the field, so the product laws apply;
// products are submodules, and multiplication by S fixes each one.
var FractionalIdealsCommMonoid = fractionalIdealsCommMonoidThm{family.Add(registry.ProofEntry{
	Name: "FractionalIdealsCommMonoid",
	Key:  "prop_1a360fde1149555",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "comm_monoid_on({M:set(A) | «wfFractional»(M)}, «wfMul», S)",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
			fractionalsInL := a.Have(
				"every fractional ideal lies in the field",
				"∀M:set(A). «wfFractional»(M) ⇒ M ⊆ L.carrier",
				By(submodule.SubmoduleSubset))
			a.Show(
				"the product laws and closure give the commutative monoid",
				Unfold(comm_monoid.CommMonoidOn),
				SplitConjAll(
					Case(
						"S is a fractional ideal of itself",
						By(subring, SubringSubmodule.Read(L).At(S))),
					Case(
						"the product of fractional ideals is a fractional ideal",
						By(subring, fractionalsInL, At(FractionalMulSubmodule.Read(L), S))),
					Case(
						"the product commutes",
						By(fractionalsInL, At(FractionalMulComm.Read(L), S))),
					Case(
						"the product associates",
						By(subring, fractionalsInL, At(FractionalMulAssoc.Read(L), S))),
					Case(
						"S is the product's identity",
						By(subring, At(FractionalMulOne.Read(L), S))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The inverse
// ---------------------------------------------------------------------------

// FractionalInverseUnique — a fractional ideal N with M · N = S is
// (S : M), and M is then invertible. Each n * m = m * n is one of the
// products spanning M · N = S, so N lies in (S : M). Conversely, for p in
// (S : M) the colon (N : {p}) is a fractional ideal holding every m * n,
// since (m * n) * p = (p * m) * n with p * m in S; so it holds their span
// M · N = S, and one with it: one * p = p lies in N.
var FractionalInverseUnique = fractionalInverseUniqueThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseUnique",
	Key:  "prop_5068ff631f9d4172",
	Reading: "This is the usual criterion: M is invertible as soon as some " +
		"fractional ideal has product S with it. N must be a submodule: a set " +
		"N whose product with M is S has its span, not itself, as (S : M).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfFractional»(M)",
			"«wfFractional»(N)",
			"«wfMul»(M, N) = S",
		},
		Conclusion: "«wfInvertible»(M) ∧ «wfInverse»(M) = N",
		Abbrev: Abbrev{
			// The colon (N : {p}) at a member p of (S : M) the proof fixes: the members y of L with y * p in N.
			{Name: "colon", Text: "{y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ {p} ⇒ y * n ∈ N)}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"S is a subring of the field",
				"M is a fractional ideal",
				"and so is N",
				"whose product is S")
			subring, mSub, nSub, product := parts[0], parts[1], parts[2], parts[3]
			fieldRing := field.RingOn.Read(L)
			mInL := a.Have(
				"a fractional ideal lies in the field",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(mSub)))
			nInL := a.Have(
				"and so does N",
				"N ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(nSub)))

			nInInverse := a.Have(
				"N lies in (S : M): for n in N and m in M, n * m = m * n lies in M · N = S",
				"N ⊆ «wfInverse»(M)",
				Derive(func(b *Argument) {
					intoS := b.Have(
						"each n * m with n in N and m in M lies in S",
						"∀n m:A. n ∈ N ∧ m ∈ M ⇒ n * m ∈ S",
						Derive(func(c *Argument) {
							n, m := c.FixAs[A]("n"), c.FixAs[A]("m")
							in := c.Conjuncts(
								c.Assume(),
								"n lies in N",
								"m lies in M")
							inL := c.Have(
								"n and m lie in L",
								"n ∈ L.carrier ∧ m ∈ L.carrier",
								BySets(nInL, mInL, in[0], in[1]))
							commute := c.Have(
								"where the product commutes",
								"n * m = m * n",
								ByArith(fieldRing, inL))
							held := c.Have(
								"m * n is one of the products spanning M · N",
								"m * n ∈ «wfMul»(M, N)",
								By(FractionalMulHolds.Read(L).At(S, M, N, m, n), in[1], in[0]))
							c.Show(
								"and M · N is S",
								commute.Rw(),
								By(Normalized, held, product))
						}))
					b.Show(
						"so each n of N, a member of L, lies in (S : M)",
						Unfold(FractionalInverseDef),
						BySets(nInL, intoS))
				}))

			inverseInN := a.Have(
				"each p of (S : M) lies in N: the colon(N : {p}) holds M · N = S, and L.one with it",
				"∀p:A. p ∈ «wfInverse»(M) ⇒ p ∈ N",
				Derive(func(b *Argument) {
					p := b.FixAs[A]("p")
					pIn := b.Assume()
					member := b.Have(
						"p lies in L and multiplies M into S",
						"p ∈ L.carrier ∧ (∀m:A. m ∈ M ⇒ p * m ∈ S)",
						BySets(b.Unfolded(pIn, FractionalInverseDef)))
					opened := b.Conjuncts(
						member,
						"p lies in L",
						"and multiplies M into S")
					pInL, scales := opened[0], opened[1]
					pm := b.MemberOf[on.L](p, pInL)
					colonIdeal := b.Have(
						"the members y of L with y * p in N form a fractional ideal, the colon (N : {p})",
						"«wfFractional»(«colon»)",
						By(
							ColonSubmodule.Read(L).At(S, N, b.TermAs[Set[A]]("{p}")),
							comm_ring.SubringSubset.Read(subring),
							nSub,
							pInL,
							set_order.SingSubset))
					holds := b.Have(
						"it holds each m * n: (m * n) * p = (p * m) * n is a multiple of n in N by p * m in S",
						"∀m n:A. m ∈ M ∧ n ∈ N ⇒ m * n ∈ «colon»",
						Derive(func(c *Argument) {
							m := c.FixAs[A]("m")
							c.FixAs[A]("n")
							in := c.Conjuncts(
								c.Assume(),
								"m lies in M",
								"n lies in N")
							inL := c.Have(
								"m and n lie in L",
								"m ∈ L.carrier ∧ n ∈ L.carrier",
								BySets(mInL, nInL, in[0], in[1]))
							regroup := c.Have(
								"the field's product associates and commutes",
								"m * n * p = p * m * n",
								ByArith(fieldRing, inL, pInL))
							multiple := c.Have(
								"so (m * n) * p, a multiple of n by p * m, lies in N",
								"m * n * p ∈ N",
								regroup.Rw(),
								By(submodule.SubmoduleSmul.Read(nSub), scales.At(m), in[0], in[1]))
							c.Show(
								"m * n lies in L, and its product with p lies in N",
								BySets(inL, comm_ring.MulIn.Read(fieldRing), multiple))
						}))
					spanned := b.Have(
						"so it holds their span M · N",
						"«wfMul»(M, N) ⊆ «colon»",
						By(FractionalMulLeast.Read(L).At(S, M, N, b.TermAs[Set[A]]("«colon»")), colonIdeal, holds))
					oneIn := b.Have(
						"M · N is S, which holds one",
						"L.one ∈ «wfMul»(M, N)",
						product.Rw(),
						By(comm_ring.SubringOne.Read(subring)))
					unit := b.Have(
						"so one lies in the colon: one * p lies in N",
						"L.one * p ∈ N",
						BySets(spanned, oneIn))
					b.Show(
						"L.one * p = p, so p lies in N",
						By(Normalized, unit, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(fieldRing)).At(pm)))
				}))

			equal := a.Have(
				"the two inclusions make (S : M) = N",
				"«wfInverse»(M) = N",
				BySets(inverseInN, nInInverse))
			a.Show(
				"then M · (S : M) = M · N = S, so M is invertible",
				By(InvertibleFractionalDef, mSub, equal, product))
		}),
})}
