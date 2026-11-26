// field_pairs.go — lattice pairs inside a field: the field as their
// container and the rings of the datum, scaling by a member of the field,
// chartwise products, the invertible pairs and their inverses, the
// sections of N · M⁻¹, and the maps from an invertible pair into any
// lattice pair, each multiplication by a member of the field.
//
// The statements stand in a field L holding the biaffine datum: the
// overlap A₀₁ ⊆ L is a ring with the field's operations, A₀ and A₁ its
// charts, t ∈ A₀ with inverse inv(t) ∈ A₁. A lattice pair here is one in
// the container L over the ring A₀₁.
//
// The abbreviations of these statements are named wb…, as those of the
// statements over a ring record R are named wa…: «wbRing»(S) is the
// field's ring read on S, «wbVectors»(S) its regular module read on S,
// «wbField» the container, and the other wb… names spell the lattice
// pairs in it over the overlap's ring (wbPair, wbInvertible), their
// ambients and the operations on them (wbMul, wbInverse, …).

package invertible_lattice_pair

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The field and the datum
// ---------------------------------------------------------------------------

// ChartRingsInField — the biaffine datum in the field puts both charts
// inside the overlap, so inside L, and the overlap and both charts are
// rings under the field's operations: the datum says so of the charts'
// rings read inside the overlap's ring, which are the charts' rings read
// inside L.
var ChartRingsInField = chartRingsInFieldThm{family.Add(registry.ProofEntry{
	Name: "ChartRingsInField",
	Key:  "prop_730e427377f16e76",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
		},
		Conclusion: "A₀ ⊆ A₀₁ ∧ " +
			"A₁ ⊆ A₀₁ ∧ " +
			"subring(field_ring(L), A₀₁) ∧ " +
			"subring(field_ring(L), A₀) ∧ " +
			"subring(field_ring(L), A₁)",
	},
		func(arg *Argument, L field.FieldFact[on.L], A0, A1, A01 *Expr[Set[A]], t *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)")
			overlapInL, datum := parts[0], parts[1]
			charts := arg.Conjuncts(
				arg.Unfolded(datum, lattice_pair.BiaffineDef),
				"the overlap is a ring under the field's operations",
				"A₀ is a subring of the overlap",
				"and so is A₁",
				"t lies in A₀",
				"inv(t) lies in A₁",
				"t · inv(t) = one",
				"the overlap is A₀ with t inverted",
				"and A₁ with inv(t) inverted")
			overlapRing, sub0, sub1 := charts[0], charts[1], charts[2]
			carrier := arg.TermAs[Set[A]]("L.carrier")
			fieldOps, overlapOps :=
				arg.TermAs[RingOps[A]]("field_ring(L)"), arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			fieldRing := field.RingOn.Read(L)
			inOverlap := arg.Conjuncts(
				arg.Have(
					"a subring of the overlap's ring lies in its carrier, the overlap",
					"A₀ ⊆ A₀₁ ∧ A₁ ⊆ A₀₁",
					By(
						comm_ring.SubringSubset.Read(sub0),
						comm_ring.SubringSubset.Read(sub1),
						module_record.RestrictRingDef.At(fieldOps, A01))),
				"A₀ lies in the overlap",
				"and so does A₁")
			// A chart's ring read inside the overlap's ring is the chart's ring read inside L.
			ring0 := arg.Have(
				"A₀ is a ring under the overlap's operations, which are L's",
				"comm_ring_on(«wbRing»(A₀))",
				By(
					sub0,
					comm_ring.SubringRingOn.Read(overlapRing).At(A0),
					module_record.RestrictRingDef.At(overlapOps, A0),
					module_record.RestrictRingDef.At(fieldOps, A0)))
			ring1 := arg.Have(
				"and so is A₁",
				"comm_ring_on(«wbRing»(A₁))",
				By(
					sub1,
					comm_ring.SubringRingOn.Read(overlapRing).At(A1),
					module_record.RestrictRingDef.At(overlapOps, A1),
					module_record.RestrictRingDef.At(fieldOps, A1)))
			overlapSubring := arg.Have(
				"the overlap lies in L and is a ring under its operations: a subring of L",
				"subring(field_ring(L), A₀₁)",
				By(overlapInL, overlapRing, comm_ring.SubringRingOn.Read(fieldRing).At(A01)))
			subring0 := arg.Have(
				"so is A₀, inside the overlap",
				"subring(field_ring(L), A₀)",
				By(
					inOverlap[0],
					overlapInL,
					set_order.SubsetTrans.At(A0, A01, carrier),
					ring0,
					comm_ring.SubringRingOn.Read(fieldRing).At(A0)))
			subring1 := arg.Have(
				"and A₁",
				"subring(field_ring(L), A₁)",
				By(
					inOverlap[1],
					overlapInL,
					set_order.SubsetTrans.At(A1, A01, carrier),
					ring1,
					comm_ring.SubringRingOn.Read(fieldRing).At(A1)))
			arg.Show(
				"both charts lie in the overlap, and the overlap and both charts are subrings of L",
				By(inOverlap[0], inOverlap[1], overlapSubring, subring0, subring1))
		}),
})}

// ---------------------------------------------------------------------------
// Scaling
// ---------------------------------------------------------------------------

// ScaleOne — scaling by one leaves a pair with its charts in the field as
// it is: one · X = X for each chart X (fractional_ideal.ScaleOne).
var ScaleOne = scaleOneThm{family.Add(registry.ProofEntry{
	Name: "ScaleOne",
	Key:  "prop_c74a56b0d6b587fe",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
		},
		Conclusion: "lattice_pair_scale(L.one, M) = M",
	},
		func(a *Argument, L field.FieldFact[on.L], M *Expr[Prod[Set[A], Set[A]]], given Fact) {
			charts := a.Conjuncts(
				given,
				"the first chart of M lies in L",
				"and so does its second")
			a.Show(
				"one fixes each chart, a subset of L, so one · M = M",
				Unfold(LatticePairScaleDef),
				By(
					charts[0],
					charts[1],
					fractional_ideal.ScaleOne.Read(L).At(a.TermAs[Set[A]]("fst(M)")),
					fractional_ideal.ScaleOne.Read(L).At(a.TermAs[Set[A]]("snd(M)")),
					pairs.PairEta))
		}),
})}

// ScaleScale — scaling by a and then by b is scaling by b · a, for a and b
// in the field and a pair with its charts in it: b · (a · X) = (b · a) · X
// for each chart X (fractional_ideal.ScaleScale).
var ScaleScale = scaleScaleThm{family.Add(registry.ProofEntry{
	Name: "ScaleScale",
	Key:  "prop_ea90ece5d9b16be1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀a b:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"a ∈ L.carrier",
			"b ∈ L.carrier",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
		},
		Conclusion: "lattice_pair_scale(b, lattice_pair_scale(a, M)) = lattice_pair_scale(b * a, M)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			a, b *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"a lies in L",
				"and so does b",
				"the first chart of M lies in L",
				"and so does its second")
			am, bm := arg.MemberOf[on.L](a, parts[0]), arg.MemberOf[on.L](b, parts[1])
			arg.Show(
				"scaling each chart by a and then by b is scaling it by b · a, so b · (a · M) = (b · a) · M",
				Unfold(LatticePairScaleDef),
				By(
					parts[2],
					parts[3],
					fractional_ideal.ScaleScale.Read(L).At(arg.TermAs[Set[A]]("fst(M)"), am, bm),
					fractional_ideal.ScaleScale.Read(L).At(arg.TermAs[Set[A]]("snd(M)"), am, bm),
					pairs.Fst,
					pairs.Snd))
		}),
})}

// ScaleCancel — dividing by a nonzero member a of the field undoes scaling
// by it: inv(a) · (a · M) = M for a pair M with its charts in the field,
// chart by chart (fractional_ideal.ScaleCancel).
var ScaleCancel = scaleCancelThm{family.Add(registry.ProofEntry{
	Name: "ScaleCancel",
	Key:  "prop_6d6bdab0bbf46c46",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
		},
		Conclusion: "lattice_pair_scale(L.inv(a), lattice_pair_scale(a, M)) = M",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"a lies in L",
				"a is not zero",
				"the first chart of M lies in L",
				"and so does its second")
			am := arg.MemberOf[on.L](a, parts[0])
			arg.Show(
				"dividing a · fst(M) and a · snd(M) by a gives fst(M) and snd(M) back, so inv(a) · (a · M) = M",
				Unfold(LatticePairScaleDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					parts[1],
					parts[2],
					parts[3],
					fractional_ideal.ScaleCancel.Read(L).At(arg.TermAs[Set[A]]("fst(M)"), am),
					fractional_ideal.ScaleCancel.Read(L).At(arg.TermAs[Set[A]]("snd(M)"), am),
					pairs.PairEta.At(M)))
		}),
})}

// AmbientOfScale — the ambient of a · M is a times the ambient of M.
// Multiplication by a is A₀₁-linear on L (ScaleLinear), so it carries what
// fst(M) spans onto what a · fst(M) spans (HomSpan), and a · fst(M) is the
// first chart of a · M.
var AmbientOfScale = ambientOfScaleThm{family.Add(registry.ProofEntry{
	Name: "AmbientOfScale",
	Key:  "prop_b19a097354f0fcd4",
	Reading: "Of the datum only the overlap being a subring of L is asked, and of M only fst(M) ⊆ L: " +
		"the ambient is the A₀₁-span of the first chart, and the statement holds of any subset of the " +
		"field in that place, so it serves the second chart through the pair (snd(M), fst(M)). a = zero " +
		"is allowed: both sides are {zero}, the span of {zero} and of ∅ alike being the zero submodule.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀₁:set(A). ∀a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀₁)",
			"a ∈ L.carrier",
			"fst(M) ⊆ L.carrier",
		},
		Conclusion: "«wbAmbient»(lattice_pair_scale(a, M)) = image(L.mul(a), «wbAmbient»(M))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A01 *Expr[Set[A]],
			a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"the overlap is a subring of L",
				"a lies in L",
				"and so does fst(M)")
			overlapSubring, aInL, fstMInL := parts[0], parts[1], parts[2]
			am := arg.MemberOf[on.L](a, aInL)
			overlap, vectors :=
				arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)"), arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			byA, first := arg.TermAs[Fun[A, A]]("L.mul(a)"), arg.TermAs[Set[A]]("fst(M)")
			spanFirst := arg.Have(
				"so it carries what fst(M) spans onto what a · fst(M) spans",
				"image(L.mul(a), «wbSpan»(fst(M))) = «wbSpan»(image(L.mul(a), fst(M)))",
				By(
					linear_independence.HomSpan.At(overlap, vectors, vectors, byA, first),
					field_extension.ScaleLinear.Read(L).At(A01, am),
					overlapSubring,
					fstMInL))
			arg.Show(
				"a · fst(M), the first chart of a · M, spans its ambient",
				Unfold(lattice_pair.LatticePairAmbientDef),
				Unfold(LatticePairScaleDef),
				Simp(Fwd(pairs.Fst)),
				By(spanFirst))
		}),
})}

// ScaleIsLattice — scaling by a nonzero member of the field keeps and
// reflects being a lattice pair. A multiple a · M of a lattice pair is one
// for every a in the field: multiplication by a carries an A₀- or
// A₁-submodule of L to one (ScaleSubmodule), and, being A₀₁-linear on L
// (ScaleLinear), carries what each chart spans onto what its multiple spans
// (HomSpan), so a · fst(M) and a · snd(M) span one submodule. Conversely M
// is inv(a) · (a · M), a multiple of the lattice pair a · M, since dividing
// by a undoes the multiple chart by chart (ScaleCancel).
var ScaleIsLattice = scaleIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "ScaleIsLattice",
	Key:  "prop_3c3797e65ea5f738",
	Reading: "a ≠ zero is load-bearing for ⇒: zero · M = ({zero}, {zero}) is a lattice pair " +
		"for every M with non-empty charts. The charts of M lie in the field so that inv(a) · " +
		"(a · M) = M; off the carrier the product is unspecified and a · M says nothing of M.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
		},
		Conclusion: "«wbPair»(lattice_pair_scale(a, M)) ⇔ «wbPair»(M)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			scaled := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
				Hypotheses: []string{
					"A₀₁ ⊆ L.carrier",
					"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
					"a ∈ L.carrier",
					"«wbPair»(M)",
				},
				Conclusion: "«wbPair»(lattice_pair_scale(a, M))",
			},
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					A0, A1, A01 *Expr[Set[A]],
					t, a *Expr[A],
					M *Expr[Prod[Set[A], Set[A]]],
					given Fact,
				) {
					parts := arg.Conjuncts(
						given,
						"A₀₁ lies in L",
						"with A₀ and A₁ its charts at t and inv(t)",
						"a lies in L",
						"and M is a lattice pair")
					aInL, pair := parts[2], parts[3]
					am := arg.MemberOf[on.L](a, aInL)
					rings := arg.Conjuncts(
						GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
						"A₀ lies in the overlap",
						"and so does A₁",
						"the overlap is a subring of L",
						"and so is A₀",
						"and so is A₁")
					overlapSubring, subring0, subring1 := rings[2], rings[3], rings[4]
					// A chart's ring read inside the overlap's ring is the chart's ring read inside L.
					fieldOps, overlapOps :=
						arg.TermAs[RingOps[A]]("field_ring(L)"), arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
					in0, in0L :=
						module_record.RestrictRingDef.At(overlapOps, A0), module_record.RestrictRingDef.At(fieldOps, A0)
					in1, in1L :=
						module_record.RestrictRingDef.At(overlapOps, A1), module_record.RestrictRingDef.At(fieldOps, A1)
					lattice := arg.Conjuncts(
						arg.Unfolded(pair, lattice_pair.LatticePairDef),
						"L is an A₀₁-module",
						"fst(M) is an A₀-submodule of L",
						"snd(M) is an A₁-submodule of L",
						"and the two span the same A₀₁-submodule")
					first, second := arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("snd(M)")
					scaledFirst := arg.Have(
						"a · fst(M) is an A₀-submodule of L",
						"submodule(«wbRing»(A₀), «wbField», image(L.mul(a), fst(M)))",
						By(fractional_ideal.ScaleSubmodule.Read(L).At(A0, first, am), subring0, lattice[1], in0, in0L))
					scaledSecond := arg.Have(
						"a · snd(M) is an A₁-submodule of L",
						"submodule(«wbRing»(A₁), «wbField», image(L.mul(a), snd(M)))",
						By(fractional_ideal.ScaleSubmodule.Read(L).At(A1, second, am), subring1, lattice[2], in1, in1L))
					chartsInL := arg.Conjuncts(
						GroupPremises(parts[3], LatticePairChartsInField.Read(L).At(A0, A1, A01, M)),
						"fst(M) lies in L",
						"and so does snd(M)")
					fstMInL, sndMInL := chartsInL[0], chartsInL[1]
					linear := arg.Have(
						"multiplication by a is A₀₁-linear on L",
						"module_homomorphism(«wbRing»(A₀₁), «wbField», «wbField», L.mul(a))",
						By(field_extension.ScaleLinear.Read(L).At(A01, am), overlapSubring))
					overlap, vectors :=
						arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)"), arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
					byA := arg.TermAs[Fun[A, A]]("L.mul(a)")
					spanFirst := arg.Have(
						"so it carries what fst(M) spans onto what a · fst(M) spans",
						"image(L.mul(a), «wbSpan»(fst(M))) = «wbSpan»(image(L.mul(a), fst(M)))",
						By(linear_independence.HomSpan.At(overlap, vectors, vectors, byA, first), linear, fstMInL))
					spanSecond := arg.Have(
						"and what snd(M) spans onto what a · snd(M) spans",
						"image(L.mul(a), «wbSpan»(snd(M))) = «wbSpan»(image(L.mul(a), snd(M)))",
						By(linear_independence.HomSpan.At(overlap, vectors, vectors, byA, second), linear, sndMInL))
					spans := arg.Have(
						"so a · fst(M) and a · snd(M) span the same A₀₁-submodule",
						"«wbSpan»(image(L.mul(a), fst(M))) = «wbSpan»(image(L.mul(a), snd(M)))",
						CalcEq(
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(a), «wbSpan»(fst(M)))"),
								"a · fst(M) spans a times what fst(M) spans",
								By(spanFirst)),
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(a), «wbSpan»(snd(M)))"),
								"fst(M) and snd(M) span the same submodule",
								By(lattice[3])),
							FinalLeg(
								"which is what a · snd(M) spans",
								By(spanSecond))))
					arg.Show(
						"so a · M, with charts a · fst(M) and a · snd(M) in the A₀₁-module L, is a lattice pair",
						Unfold(lattice_pair.LatticePairDef),
						Unfold(LatticePairScaleDef),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						By(lattice[0], scaledFirst, scaledSecond, spans, in0, in0L, in1, in1L))
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					A0, A1, A01 *Expr[Set[A]],
					t, a *Expr[A],
					M *Expr[Prod[Set[A], Set[A]]],
					given Fact,
				) {
					parts := arg.Conjuncts(
						given,
						"A₀₁ lies in L",
						"with A₀ and A₁ its charts at t and inv(t)",
						"a lies in L",
						"a is not zero",
						"fst(M) lies in L",
						"and so does snd(M)")
					overlapInL, datum, aInL, nonzero, fstMInL, sndMInL :=
						parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
					am := arg.MemberOf[on.L](a, aInL)
					arg.Iff()
					arg.Forward(
						"M is inv(a) · (a · M), a multiple of the lattice pair a · M",
						func(b *Argument, scaledPair Fact) {
							divided := b.Have(
								"inv(a) · (a · M) is a lattice pair",
								"«wbPair»(lattice_pair_scale(L.inv(a), lattice_pair_scale(a, M)))",
								By(L, overlapInL, datum, field.InvIn.Read(L).At(am), scaledPair, scaled))
							b.Show(
								"dividing a · M by a, a being nonzero, gives M back, so M is a lattice pair",
								By(Normalized, nonzero, fstMInL, sndMInL, ScaleCancel.Read(L).At(am, M), divided))
						})
					arg.Backward(
						"a multiple of a lattice pair is a lattice pair",
						func(b *Argument, pair Fact) {
							b.Show(
								"so a · M is one",
								By(L, overlapInL, datum, aInL, pair, scaled))
						})
				})
		}),
})}

// ScaleOnAmbient — multiplication by a member a of the field on the ambient of
// a lattice pair M, zero off it, is an A₀₁-linear map of the ambient into L
// carrying each chart of M onto its multiple by a. The ambient is an
// A₀₁-submodule of L holding both charts (lattice_pair.AmbientContains); on it
// the map is x ↦ a * x, which is A₀₁-linear on L (ScaleLinear) and so on the
// ambient, and off it the map is zero, so it lies in hom_set. Agreeing with
// multiplication by a on each chart, it carries the chart onto a times it.
var ScaleOnAmbient = scaleOnAmbientThm{family.Add(registry.ProofEntry{
	Name: "ScaleOnAmbient",
	Key:  "prop_65ffbf3ffaeca572",
	Reading: "a may be zero: the map is then zero, and the statement reads zero · fst(M) and " +
		"zero · snd(M) as the images. lattice_pair(M) is load-bearing: it makes the ambient an " +
		"A₀₁-submodule of L, so a module the map can be linear on, and puts both charts inside it.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"a ∈ L.carrier",
			"«wbPair»(M)",
		},
		Conclusion: "(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)) ∈ " +
			"hom_set(«wbRing»(A₀₁), restrict_module(«wbField», «wbAmbient»(M)), «wbField») ∧ " +
			"image(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero), fst(M)) = image(L.mul(a), fst(M)) ∧ " +
			"image(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero), snd(M)) = image(L.mul(a), snd(M))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t, a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)",
				"a lies in L",
				"and M is a lattice pair")
			aInL := parts[2]
			am := arg.MemberOf[on.L](a, aInL)
			overlap, vectors :=
				arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)"), arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			onAmbient := arg.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«wbField», «wbAmbient»(M))")
			ambient, first, second :=
				arg.TermAs[Set[A]]("«wbAmbient»(M)"), arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("snd(M)")
			times, byA :=
				arg.TermAs[Fun[A, A]]("λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)"),
				arg.TermAs[Fun[A, A]]("L.mul(a)")
			overlapSubring := arg.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")[2]
			contains := arg.Conjuncts(
				GroupPremises(parts[3], lattice_pair.AmbientContains.At(overlap, A0, A1, vectors, M)),
				"the ambient of M is an A₀₁-submodule of L",
				"holding fst(M)",
				"and snd(M)")
			submoduleAmbient, firstIn, secondIn := contains[0], contains[1], contains[2]

			agrees := arg.Have(
				"on the ambient the map multiplies by a",
				"∀x:A. x ∈ «wbAmbient»(M) ⇒ COND(x ∈ «wbAmbient»(M), a * x, L.zero) = a * x",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Show(
						"x lies in the ambient, so the map takes it to a * x",
						By(b.Assume()))
				}))
			vanishes := arg.Have(
				"and off the ambient it is zero",
				"∀u:A. u ∉ «wbAmbient»(M) ⇒ COND(u ∈ «wbAmbient»(M), a * u, L.zero) = L.zero",
				Derive(func(b *Argument) {
					b.FixAs[A]("u")
					b.Show(
						"u lies off the ambient, so the map takes it to zero",
						By(b.Assume()))
				}))

			linear := arg.Have(
				"multiplication by a is A₀₁-linear on L, so on the ambient, an A₀₁-submodule of L",
				"module_homomorphism(«wbRing»(A₀₁), "+
					"    restrict_module(«wbField», «wbAmbient»(M)), "+
					"    «wbField», "+
					"    L.mul(a))",
				By(
					module_homomorphism.HomRestrictSource.At(overlap, vectors, vectors, byA, ambient),
					field_extension.ScaleLinear.Read(L).At(A01, am),
					overlapSubring,
					submoduleAmbient))
			homomorphism := arg.Have(
				"so is the map, which agrees with it there",
				"module_homomorphism(«wbRing»(A₀₁), "+
					"    restrict_module(«wbField», «wbAmbient»(M)), "+
					"    «wbField», "+
					"    λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero))",
				By(module_homomorphism.HomCongruence.At(overlap, onAmbient, vectors, byA, times), linear, agrees))
			inHomSet := arg.Have(
				"being zero off the ambient, the map lies in hom_set",
				"(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)) ∈ "+
					"hom_set(«wbRing»(A₀₁), restrict_module(«wbField», «wbAmbient»(M)), «wbField»)",
				By(hom_module.InHomSet.At(overlap, onAmbient, vectors, times), homomorphism, vanishes))

			imageFirst := arg.Have(
				"fst(M) lies in the ambient, so the map carries it onto a · fst(M)",
				"image(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero), fst(M)) = image(L.mul(a), fst(M))",
				By(set_image.ImageCongruence.At(times, byA, first), agrees, firstIn, set_basic.SubsetDef))
			imageSecond := arg.Have(
				"and snd(M) onto a · snd(M)",
				"image(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero), snd(M)) = image(L.mul(a), snd(M))",
				By(set_image.ImageCongruence.At(times, byA, second), agrees, secondIn, set_basic.SubsetDef))
			arg.Show(
				"so the map lies in hom_set and carries each chart onto its multiple by a",
				By(inHomSet, imageFirst, imageSecond))
		}),
})}

// ScaleIsomorphism — multiplication by a nonzero member of the field is an
// isomorphism of lattice pairs from M onto a · M. On the ambient of M, and
// zero off it, multiplication by a is an A₀₁-linear map carrying each chart
// onto its multiple by a, the chart of a · M (ScaleOnAmbient); and
// a * x = a * y gives x = y, a nonzero member of a field cancelling.
var ScaleIsomorphism = scaleIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ScaleIsomorphism",
	Key:  "prop_86859ff4b45f6f6",
	Reading: "a ≠ zero is load-bearing for injectivity alone: at a = zero " +
		"the map is zero, which still carries each chart of M onto the chart of " +
		"zero · M = ({zero}, {zero}), but is one-to-one only on a zero ambient.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"«wbPair»(M)",
		},
		Conclusion: "lattice_pair_isomorphism(«wbRing»(A₀₁), " +
			"    «wbField», " +
			"    M, " +
			"    «wbField», " +
			"    lattice_pair_scale(a, M), " +
			"    λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t, a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)",
				"a lies in L",
				"a is not zero",
				"and M is a lattice pair")
			aInL, nonzero := parts[2], parts[3]
			am := arg.MemberOf[on.L](a, aInL)
			overlap, vectors :=
				arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)"), arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			scaling := arg.Conjuncts(
				GroupPremises(parts[0], parts[1], parts[4], ScaleOnAmbient.Read(L).At(A0, A1, A01, t, am, M)),
				"multiplication by a on the ambient, zero off it, lies in hom_set",
				"carries fst(M) onto a · fst(M)",
				"and snd(M) onto a · snd(M)")
			submoduleAmbient := arg.Conjuncts(
				GroupPremises(parts[4], lattice_pair.AmbientContains.At(overlap, A0, A1, vectors, M)),
				"the ambient of M is an A₀₁-submodule of L",
				"holding fst(M)",
				"and snd(M)")[0]

			ambientInL := arg.Have(
				"the ambient lies in L, a submodule of it",
				"«wbAmbient»(M) ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(submoduleAmbient)))
			injective := arg.Have(
				"a being nonzero, the map is one-to-one on the ambient",
				"injective_on(«wbAmbient»(M), λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero))",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in the ambient",
						"so does y",
						"and the map takes them to one point")
					products := b.Have(
						"that is, a * x = a * y",
						"a * x = a * y",
						By(points[0], points[1], points[2]))
					xm := b.MemberOf[on.L](x, b.Have(
						"x lies in L, as the ambient does",
						"x ∈ L.carrier",
						BySets(ambientInL, points[0])))
					ym := b.MemberOf[on.L](y, b.Have(
						"and so does y",
						"y ∈ L.carrier",
						BySets(ambientInL, points[1])))
					b.Show(
						"a nonzero member of the field cancels: x = y",
						By(
							integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L)).At(am, xm, ym),
							nonzero,
							products))
				}))

			arg.Show(
				"so the map is an isomorphism of M onto a · M, whose charts are a · fst(M) and a · snd(M)",
				Simp(
					Fwd(lattice_pair_map.LatticePairIsomorphismDef),
					Fwd(lattice_pair_map.LatticePairMapsDef),
					Fwd(LatticePairScaleDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				BySets(scaling[0], injective, scaling[1], scaling[2]))
		}),
})}

// ---------------------------------------------------------------------------
// Products
// ---------------------------------------------------------------------------

// AmbientOfMul — the ambient of M · N is the product of the ambients, as
// fractional ideals of the overlap: an ambient is the overlap span of the
// first chart, the first chart of M · N is the product over chart 0 of the
// first charts, and extending along A₀ ⊆ A₀₁ takes that product to the
// product of the extensions (subring_localization.ExtensionOfProduct).
var AmbientOfMul = ambientOfMulThm{family.Add(registry.ProofEntry{
	Name: "AmbientOfMul",
	Key:  "prop_f5c4d84d448a7187",
	Reading: "The product on the right is over A₀₁, on the left over A₀ and then spanned " +
		"over A₀₁; A₀ ⊆ A₀₁ is what lets the inner span be absorbed. Only the first charts " +
		"enter, and only as subsets of L: neither pair need be a lattice pair and no datum is " +
		"asked, so read at A₁ with the charts of both pairs exchanged it gives the second chart.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀₁)",
			"A₀ ⊆ A₀₁",
			"fst(M) ⊆ L.carrier",
			"fst(N) ⊆ L.carrier",
		},
		Conclusion: "«wbAmbient»(«wbMul»(M, N)) = " +
			"fractional_mul(field_ring(L), A₀₁, «wbAmbient»(M), «wbAmbient»(N))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M, N *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap is a subring of L",
				"chart 0 lies in the overlap",
				"the first chart of M lies in L",
				"and so does the first chart of N")
			a.Show(
				"the ambients are the overlap spans of the first charts, and "+
					"the first chart of the product is their product over chart 0",
				Unfold(lattice_pair.LatticePairAmbientDef),
				Simp(Fwd(LatticePairMulDef), Fwd(pairs.Fst)),
				By(
					parts[0],
					parts[1],
					parts[2],
					parts[3],
					subring_localization.ExtensionOfProduct.Read(L).At(
						A0, A01, a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("fst(N)"))))
		}),
})}

// MulIsLattice — the chartwise product of two lattice pairs is a lattice
// pair. Each product chart is a fractional product over its chart ring,
// a subring of L, so a submodule of L (FractionalMulSubmodule). The first
// spans the product of the two ambients over the overlap (AmbientOfMul).
// So does the second: it is the first chart of the product of the two
// pairs with their charts exchanged, and exchanging a pair's charts keeps
// its ambient, the two charts spanning one module.
var MulIsLattice = mulIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "MulIsLattice",
	Key:  "prop_29c16da0328cee3e",
	Reading: "No invertibility is asked. Of the lattice pairs only their " +
		"charts lying in L and spanning one module over the overlap enter, and " +
		"of the datum only its charts being subrings of L inside the overlap.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
			"«wbPair»(N)",
		},
		Conclusion: "«wbPair»(«wbMul»(M, N))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the two charts form the biaffine datum",
				"M is a lattice pair in L",
				"and so is N")
			latticeM := a.Conjuncts(
				a.Unfolded(parts[2], lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is a submodule over chart 0",
				"snd(M) is a submodule over chart 1",
				"the charts span the same module over the overlap")
			unfoldedN := a.Unfolded(parts[3], lattice_pair.LatticePairDef)
			chartsMInL := a.Conjuncts(
				GroupPremises(parts[2], LatticePairChartsInField.Read(L).At(A0, A1, A01, M)),
				"the first chart of M lies in L",
				"and so does its second chart")
			chartsNInL := a.Conjuncts(
				GroupPremises(parts[3], LatticePairChartsInField.Read(L).At(A0, A1, A01, N)),
				"the first chart of N lies in L",
				"and so does its second chart")
			fstMInL, sndMInL := chartsMInL[0], chartsMInL[1]
			fstNInL, sndNInL := chartsNInL[0], chartsNInL[1]
			rings := a.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")
			inOverlap0, inOverlap1, overlapSubring, subring0, subring1 :=
				rings[0], rings[1], rings[2], rings[3], rings[4]
			fstM, sndM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			fstN, sndN := a.TermAs[Set[A]]("fst(N)"), a.TermAs[Set[A]]("snd(N)")
			product0 := a.Have(
				"the product on chart 0 is an A₀-submodule of L",
				"submodule(«wbRing»(A₀), «wbField», fractional_mul(field_ring(L), A₀, fst(M), fst(N)))",
				By(subring0, fstMInL, fstNInL, fractional_ideal.FractionalMulSubmodule.Read(L).At(A0, fstM, fstN)))
			product1 := a.Have(
				"and the product on chart 1 an A₁-submodule of L",
				"submodule(«wbRing»(A₁), «wbField», fractional_mul(field_ring(L), A₁, snd(M), snd(N)))",
				By(subring1, sndMInL, sndNInL, fractional_ideal.FractionalMulSubmodule.Read(L).At(A1, sndM, sndN)))

			// Exchanging the charts of a lattice pair keeps its ambient, the two charts spanning one module.
			exchangedM := a.TermAs[Prod[Set[A], Set[A]]]("(snd(M), fst(M))")
			exchangedN := a.TermAs[Prod[Set[A], Set[A]]]("(snd(N), fst(N))")
			exchangedAmbientM := a.Have(
				"M with its charts exchanged has M's ambient",
				"«wbAmbient»((snd(M), fst(M))) = «wbAmbient»(M)",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef), Fwd(pairs.Fst)),
				By(latticeM[3]))
			exchangedAmbientN := a.Have(
				"and N with its charts exchanged has N's ambient",
				"«wbAmbient»((snd(N), fst(N))) = «wbAmbient»(N)",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef), Fwd(pairs.Fst)),
				By(unfoldedN))
			ambient0 := a.Have(
				"the first product chart spans the product of the original ambients",
				"«wbAmbient»(«wbMul»(M, N)) = fractional_mul(field_ring(L), A₀₁, «wbAmbient»(M), «wbAmbient»(N))",
				By(overlapSubring, inOverlap0, fstMInL, fstNInL, AmbientOfMul.Read(L).At(A0, A1, A01, M, N)))
			ambient1 := a.Have(
				"and so does the first product chart after exchanging the charts",
				"«wbAmbient»(lattice_pair_mul(field_ring(L), A₁, A₀, (snd(M), fst(M)), (snd(N), fst(N)))) = "+
					"fractional_mul(field_ring(L), A₀₁, «wbAmbient»(M), «wbAmbient»(N))",
				By(
					overlapSubring,
					inOverlap1,
					sndMInL,
					sndNInL,
					exchangedAmbientM,
					exchangedAmbientN,
					pairs.Fst,
					AmbientOfMul.Read(L).At(A1, A0, A01, exchangedM, exchangedN)))
			spans := a.Have(
				"both product charts span that same overlap product",
				"module_span(«wbRing»(A₀₁), «wbField», fractional_mul(field_ring(L), A₀, fst(M), fst(N))) = "+
					"module_span(«wbRing»(A₀₁), «wbField», fractional_mul(field_ring(L), A₁, snd(M), snd(N)))",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wbAmbient»(«wbMul»(M, N))"),
						"the first product chart spans the product pair's ambient",
						Simp(Fwd(lattice_pair.LatticePairAmbientDef), Fwd(LatticePairMulDef), Fwd(pairs.Fst)),
						Basic()),
					Leg(
						a.TermAs[Set[A]]("fractional_mul(field_ring(L), A₀₁, «wbAmbient»(M), «wbAmbient»(N))"),
						"which is the product of the original ambients",
						By(ambient0)),
					Leg(
						a.TermAs[Set[A]](
							"«wbAmbient»(lattice_pair_mul(field_ring(L), A₁, A₀, (snd(M), fst(M)), (snd(N), fst(N))))"),
						"and the exchanged product has that ambient too",
						By(ambient1)),
					FinalLeg(
						"its first chart is the original product's second chart",
						Simp(
							Fwd(lattice_pair.LatticePairAmbientDef),
							Fwd(LatticePairMulDef),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						Basic())))
			// Restricting the overlap's ring to a chart keeps the field's operations.
			fieldOps, overlapOps := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			in0, in0L :=
				module_record.RestrictRingDef.At(overlapOps, A0), module_record.RestrictRingDef.At(fieldOps, A0)
			in1, in1L :=
				module_record.RestrictRingDef.At(overlapOps, A1), module_record.RestrictRingDef.At(fieldOps, A1)
			a.Show(
				"the two product submodules have one overlap span, so form a lattice pair",
				Unfold(lattice_pair.LatticePairDef),
				Simp(Fwd(LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(latticeM[0], product0, product1, spans, in0, in0L, in1, in1L))
		}),
})}

// MulAssoc — the product of pairs is associative. It is taken chart by
// chart, and on each chart a fractional product of three subsets of L over
// a subring of L associates (FractionalMulAssoc), each side being the span
// of the triple products m · n · q.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_2db0aa3f1cb4ea0d",
	Reading: "Neither pair need be a lattice pair and no datum is asked. The charts of " +
		"the three pairs lie in L, where the field's product is associative, a product with a " +
		"member outside L being a value nothing is said about; the chart rings are subrings " +
		"of L, over which a product of spans is the span of the products (FractionalMulAssoc).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁:set(A). ∀M N Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀)",
			"subring(field_ring(L), A₁)",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
			"fst(N) ⊆ L.carrier",
			"snd(N) ⊆ L.carrier",
			"fst(Q) ⊆ L.carrier",
			"snd(Q) ⊆ L.carrier",
		},
		Conclusion: "«wbMul»(«wbMul»(M, N), Q) = «wbMul»(M, «wbMul»(N, Q))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1 *Expr[Set[A]],
			M, N, Q *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"chart 0 is a subring of L",
				"and so is chart 1",
				"the first chart of M lies in L",
				"and so does its second",
				"the first chart of N lies in L",
				"and so does its second",
				"the first chart of Q lies in L",
				"and so does its second")
			subring0, subring1 := parts[0], parts[1]
			fstMInL, sndMInL, fstNInL, sndNInL, fstQInL, sndQInL :=
				parts[2], parts[3], parts[4], parts[5], parts[6], parts[7]
			fstM, sndM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			fstN, sndN := a.TermAs[Set[A]]("fst(N)"), a.TermAs[Set[A]]("snd(N)")
			fstQ, sndQ := a.TermAs[Set[A]]("fst(Q)"), a.TermAs[Set[A]]("snd(Q)")
			chart0 := a.Have(
				"the products on chart 0 associate",
				"fractional_mul(field_ring(L), A₀, fractional_mul(field_ring(L), A₀, fst(M), fst(N)), fst(Q)) = "+
					"fractional_mul(field_ring(L), A₀, fst(M), fractional_mul(field_ring(L), A₀, fst(N), fst(Q)))",
				By(
					subring0,
					fstMInL,
					fstNInL,
					fstQInL,
					fractional_ideal.FractionalMulAssoc.Read(L).At(A0, fstM, fstN, fstQ)))
			chart1 := a.Have(
				"and so do the products on chart 1",
				"fractional_mul(field_ring(L), A₁, fractional_mul(field_ring(L), A₁, snd(M), snd(N)), snd(Q)) = "+
					"fractional_mul(field_ring(L), A₁, snd(M), fractional_mul(field_ring(L), A₁, snd(N), snd(Q)))",
				By(
					subring1,
					sndMInL,
					sndNInL,
					sndQInL,
					fractional_ideal.FractionalMulAssoc.Read(L).At(A1, sndM, sndN, sndQ)))
			a.Show(
				"the chartwise product of pairs therefore associates",
				Simp(Fwd(LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(chart0, chart1))
		}),
})}

// MulComm — the product of pairs is commutative: each chart lies in the
// field, where its fractional-ideal product commutes (FractionalMulComm).
var MulComm = mulCommThm{family.Add(registry.ProofEntry{
	Name: "MulComm",
	Key:  "prop_e9462bd3cd4e75bb",
	Reading: "Neither pair need be a lattice pair and nothing is asked of the chart rings: " +
		"fractional products of subsets of L commute over any set of scalars. The charts of M " +
		"and N lie in L only for the commutativity of the field's product, which holds on L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁:set(A). ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
			"fst(N) ⊆ L.carrier",
			"snd(N) ⊆ L.carrier",
		},
		Conclusion: "«wbMul»(M, N) = «wbMul»(N, M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1 *Expr[Set[A]],
			M, N *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the first chart of M lies in L",
				"and so does its second",
				"the first chart of N lies in L",
				"and so does its second")
			fstMInL, sndMInL, fstNInL, sndNInL := parts[0], parts[1], parts[2], parts[3]
			fstM, sndM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			fstN, sndN := a.TermAs[Set[A]]("fst(N)"), a.TermAs[Set[A]]("snd(N)")
			chart0 := a.Have(
				"the products on chart 0 commute",
				"fractional_mul(field_ring(L), A₀, fst(M), fst(N)) = "+
					"fractional_mul(field_ring(L), A₀, fst(N), fst(M))",
				By(fstMInL, fstNInL, fractional_ideal.FractionalMulComm.Read(L).At(A0, fstM, fstN)))
			chart1 := a.Have(
				"and so do the products on chart 1",
				"fractional_mul(field_ring(L), A₁, snd(M), snd(N)) = "+
					"fractional_mul(field_ring(L), A₁, snd(N), snd(M))",
				By(sndMInL, sndNInL, fractional_ideal.FractionalMulComm.Read(L).At(A1, sndM, sndN)))
			a.Show(
				"the chartwise product of pairs therefore commutes",
				Simp(Fwd(LatticePairMulDef)),
				By(chart0, chart1))
		}),
})}

// MulOne — the structure pair (A₀, A₁) is the unit of the product. The
// product is taken chart by chart, and on each chart a subring of L times
// a submodule over it is that submodule (FractionalMulOne): the products
// c * m with c in the chart lie in the submodule, and every m is one * m.
// The datum puts each chart inside L as a ring under the field's
// operations, and the lattice pair makes fst(M) an A₀-submodule and snd(M)
// an A₁-submodule of L.
var MulOne = mulOneThm{family.Add(registry.ProofEntry{
	Name: "MulOne",
	Key:  "prop_1c9e07986b93a947",
	Reading: "The lattice-pair hypothesis is needed: for a chart that " +
		"is no submodule, (A₀, A₁) · M is the pair of spans of M's charts.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
		},
		Conclusion: "«wbMul»((A₀, A₁), M) = M",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)",
				"and M is a lattice pair")
			pair := parts[2]
			rings := a.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"A₀ lies in the overlap",
				"and so does A₁",
				"the overlap is a subring of L",
				"and so is A₀",
				"and so is A₁")
			subring0, subring1 := rings[3], rings[4]
			// A chart's ring read inside the overlap's ring is the chart's ring read inside L.
			fieldOps, overlapOps := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			in0, in0L :=
				module_record.RestrictRingDef.At(overlapOps, A0), module_record.RestrictRingDef.At(fieldOps, A0)
			in1, in1L :=
				module_record.RestrictRingDef.At(overlapOps, A1), module_record.RestrictRingDef.At(fieldOps, A1)
			lattice := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"L is an A₀₁-module",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"and the two span the same A₀₁-submodule")
			first, second := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			onFirst := a.Have(
				"chart 0 times its submodule fst(M) is fst(M)",
				"fractional_mul(field_ring(L), A₀, A₀, fst(M)) = fst(M)",
				By(fractional_ideal.FractionalMulOne.Read(L).At(A0, first), subring0, lattice[1], in0, in0L))
			onSecond := a.Have(
				"and chart 1 times its submodule snd(M) is snd(M)",
				"fractional_mul(field_ring(L), A₁, A₁, snd(M)) = snd(M)",
				By(fractional_ideal.FractionalMulOne.Read(L).At(A1, second), subring1, lattice[2], in1, in1L))
			a.Show(
				"the product of pairs is taken chart by chart, so (A₀, A₁) · M is (fst(M), snd(M)), which is M",
				Simp(Fwd(LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(Normalized, onFirst, onSecond, pairs.PairEta.At(M)))
		}),
})}

// ScaleMulAssoc — scaling commutes with the product of pairs: (a · M) · N
// = a · (M · N) = M · (a · N). Both are read chart by chart. On one chart
// ring S, a subring of L, a multiple comes out of the left factor of a
// product of fractional ideals (FractionalMulScale), and out of the right
// one because the product commutes: X · (a · Y) = (a · Y) · X =
// a · (Y · X) = a · (X · Y). The datum puts both charts inside the
// overlap, so inside L, as rings under the field's operations.
var ScaleMulAssoc = scaleMulAssocThm{family.Add(registry.ProofEntry{
	Name: "ScaleMulAssoc",
	Key:  "prop_4e042868aed872f9",
	Reading: "What is asked is the datum in L, whose charts are the rings the " +
		"products are taken over, a ∈ L, and the charts of M and N inside L, a member " +
		"outside L making a product a value nothing is said about: neither pair need be " +
		"a lattice pair or invertible, and a = zero is allowed — then all three sides " +
		"are ({zero}, {zero}), the span of ∅ or of {zero} being the zero submodule.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"a ∈ L.carrier",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
			"fst(N) ⊆ L.carrier",
			"snd(N) ⊆ L.carrier",
		},
		Conclusion: "«wbMul»(lattice_pair_scale(a, M), N) = lattice_pair_scale(a, «wbMul»(M, N)) ∧ " +
			"«wbMul»(M, lattice_pair_scale(a, N)) = lattice_pair_scale(a, «wbMul»(M, N))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			chart := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀S X Y:set(A). ∀a:A.",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"a ∈ L.carrier",
					"X ⊆ L.carrier",
					"Y ⊆ L.carrier",
				},
				Conclusion: "fractional_mul(field_ring(L), S, image(L.mul(a), X), Y) = " +
					"image(L.mul(a), fractional_mul(field_ring(L), S, X, Y)) ∧ " +
					"fractional_mul(field_ring(L), S, X, image(L.mul(a), Y)) = " +
					"image(L.mul(a), fractional_mul(field_ring(L), S, X, Y))",
			},
				func(arg *Argument, L field.FieldFact[on.L], S, X, Y *Expr[Set[A]], a *Expr[A], given Fact) {
					parts := arg.Conjuncts(
						given,
						"S is a subring of L",
						"a lies in L",
						"X lies in L",
						"and so does Y")
					subring, aInL, xInL, yInL := parts[0], parts[1], parts[2], parts[3]
					am := arg.MemberOf[on.L](a, aInL)
					scaledY := arg.TermAs[Set[A]]("image(L.mul(a), Y)")
					scaledInL := arg.Have(
						"a · Y lies in L",
						"image(L.mul(a), Y) ⊆ L.carrier",
						BySets(aInL, yInL, comm_ring.MulIn.Read(field.RingOn.Read(L))))
					left := arg.Have(
						"a comes out of the left factor",
						"fractional_mul(field_ring(L), S, image(L.mul(a), X), Y) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), S, X, Y))",
						By(fractional_ideal.FractionalMulScale.Read(L).At(S, X, Y, am), subring, xInL, yInL))
					right := arg.Have(
						"and out of the right one, the product commuting",
						"fractional_mul(field_ring(L), S, X, image(L.mul(a), Y)) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), S, X, Y))",
						CalcEq(
							Leg(
								arg.TermAs[Set[A]]("fractional_mul(field_ring(L), S, image(L.mul(a), Y), X)"),
								"the product commutes",
								By(fractional_ideal.FractionalMulComm.Read(L).At(S, X, scaledY), xInL, scaledInL)),
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(a), fractional_mul(field_ring(L), S, Y, X))"),
								"a comes out of the left factor",
								By(fractional_ideal.FractionalMulScale.Read(L).At(S, Y, X, am), subring, yInL, xInL)),
							FinalLeg(
								"the product inside commutes",
								By(Normalized, fractional_ideal.FractionalMulComm.Read(L).At(S, Y, X), yInL, xInL))))
					arg.Show(
						"so a comes out of either factor",
						By(left, right))
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					A0, A1, A01 *Expr[Set[A]],
					t, a *Expr[A],
					M, N *Expr[Prod[Set[A], Set[A]]],
					given Fact,
				) {
					parts := arg.Conjuncts(
						given,
						"the overlap lies in L",
						"the charts and the overlap are a biaffine datum",
						"a lies in L",
						"the first chart of M lies in L",
						"and so does its second",
						"the first chart of N lies in L",
						"and so does its second")
					aInL := parts[2]
					fstMInL, sndMInL, fstNInL, sndNInL := parts[3], parts[4], parts[5], parts[6]
					rings := arg.Conjuncts(
						GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
						"A₀ lies in the overlap",
						"and so does A₁",
						"the overlap is a subring of L",
						"and so is A₀",
						"and so is A₁")
					subring0, subring1 := rings[3], rings[4]
					onFirst := arg.Have(
						"on chart 0, a comes out of either factor of fst(M) · fst(N)",
						"fractional_mul(field_ring(L), A₀, image(L.mul(a), fst(M)), fst(N)) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), A₀, fst(M), fst(N))) ∧ "+
							"fractional_mul(field_ring(L), A₀, fst(M), image(L.mul(a), fst(N))) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), A₀, fst(M), fst(N)))",
						By(L, subring0, aInL, fstMInL, fstNInL, chart))
					onSecond := arg.Have(
						"on chart 1, of snd(M) · snd(N)",
						"fractional_mul(field_ring(L), A₁, image(L.mul(a), snd(M)), snd(N)) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), A₁, snd(M), snd(N))) ∧ "+
							"fractional_mul(field_ring(L), A₁, snd(M), image(L.mul(a), snd(N))) = "+
							"image(L.mul(a), fractional_mul(field_ring(L), A₁, snd(M), snd(N)))",
						By(L, subring1, aInL, sndMInL, sndNInL, chart))
					arg.Show(
						"products and multiples of pairs are taken chart by chart",
						Simp(Fwd(LatticePairMulDef), Fwd(LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						By(onFirst, onSecond))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Invertible pairs
// ---------------------------------------------------------------------------

// LatticePairChartsInField — the charts of a lattice pair in the field lie
// in the field: each is a submodule of L over its chart ring, and a
// submodule lies in its module's carrier, L's.
var LatticePairChartsInField = latticePairChartsInFieldThm{family.Add(registry.ProofEntry{
	Name: "LatticePairChartsInField",
	Key:  "prop_165b663e9a9054e7",
	Reading: "The field hypothesis is not load-bearing: it is the chapter's setting. Of " +
		"the lattice pair only its charts being submodules of L enter, not their common span.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wbPair»(M)",
		},
		Conclusion: "fst(M) ⊆ L.carrier ∧ snd(M) ⊆ L.carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M *Expr[Prod[Set[A], Set[A]]],
			pair Fact,
		) {
			lattice := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"L is a module over A₀₁",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"and the two span the same A₀₁-submodule")
			a.Show(
				"a submodule lies in its module's carrier, here L",
				By(submodule.SubmoduleSubset.Read(lattice[1]), submodule.SubmoduleSubset.Read(lattice[2])))
		}),
})}

// InvertibleChartsInField — the charts of an invertible pair lie in the
// field: each is an invertible fractional ideal of its chart ring, so a
// submodule of L over it, and a submodule lies in its module's carrier.
var InvertibleChartsInField = invertibleChartsInFieldThm{family.Add(registry.ProofEntry{
	Name:    "InvertibleChartsInField",
	Key:     "prop_f87b6df58cc793c",
	Reading: "The field hypothesis is not load-bearing: it is the chapter's setting.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wbInvertible»(M)",
		},
		Conclusion: "fst(M) ⊆ L.carrier ∧ snd(M) ⊆ L.carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M *Expr[Prod[Set[A], Set[A]]],
			invertible Fact,
		) {
			charts := a.Conjuncts(
				a.Unfolded(invertible, InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) one of A₁",
				"M is a lattice pair over A₀₁")
			first := a.Conjuncts(
				a.Unfolded(charts[0], fractional_ideal.InvertibleFractionalDef),
				"so fst(M) is an A₀-submodule of L",
				"with A₀ its product with its inverse")
			second := a.Conjuncts(
				a.Unfolded(charts[1], fractional_ideal.InvertibleFractionalDef),
				"and snd(M) an A₁-submodule of L",
				"with A₁ its product with its inverse")
			a.Show(
				"a submodule lies in its module's carrier, here L",
				By(submodule.SubmoduleSubset.Read(first[0]), submodule.SubmoduleSubset.Read(second[0])))
		}),
})}

// InvertiblePairSwap — exchanging the charts of an invertible pair gives
// an invertible pair over the exchanged charts, with the same ambient:
// the definitions are symmetric in the charts but for the ambient, the
// span of chart 0, and the two charts span one submodule.
var InvertiblePairSwap = invertiblePairSwapThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePairSwap",
	Key:  "prop_a18f13f8b31d3ee8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wbInvertible»(M)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), A₁, A₀, A₀₁, (snd(M), fst(M))) ∧ " +
			"«wbAmbient»((snd(M), fst(M))) = «wbAmbient»(M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M *Expr[Prod[Set[A], Set[A]]],
			invertible Fact,
		) {
			charts := a.Conjuncts(
				a.Unfolded(invertible, InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"M is a lattice pair over the overlap")
			lattice := a.Conjuncts(
				a.Unfolded(charts[2], lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"the two charts span one submodule")
			swapped := a.Have(
				"with its charts exchanged M is a lattice pair over chart 1 and chart 0",
				"lattice_pair(«wbRing»(A₀₁), A₁, A₀, «wbField», (snd(M), fst(M)))",
				Unfold(lattice_pair.LatticePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(lattice[0], lattice[2], lattice[1], lattice[3]))
			ambient := a.Have(
				"its ambient is the span of snd(M), which is the span of fst(M)",
				"«wbAmbient»((snd(M), fst(M))) = «wbAmbient»(M)",
				Unfold(lattice_pair.LatticePairAmbientDef),
				Simp(Fwd(pairs.Fst)),
				By(lattice[3]))
			a.Show(
				"so it is invertible, with the ambient of M",
				Unfold(InvertibleLatticePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(charts[1], charts[0], swapped, ambient))
		}),
})}

// StructurePairInvertible — the structure pair (A₀, A₁) is an invertible
// lattice pair: each chart is a subring of the field, so an invertible
// fractional ideal of itself and a submodule of the field over itself;
// each lies in the subring A₀₁ and holds one, so its A₀₁-span is A₀₁,
// and the two charts span the same A₀₁-module.
var StructurePairInvertible = structurePairInvertibleThm{family.Add(registry.ProofEntry{
	Name: "StructurePairInvertible",
	Key:  "prop_66164043b707f87",
	Reading: "The inverse keeps only members of L, so no element " +
		"outside the field, where products are unspecified, enters (A₀ : A₀).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
		},
		Conclusion: "«wbInvertible»((A₀, A₁))",
	},
		func(a *Argument, L field.FieldFact[on.L], A0, A1, A01 *Expr[Set[A]], t *Expr[A], datum Fact) {
			rings := a.Conjuncts(
				GroupPremises(datum, ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"and so is chart 0",
				"and so is chart 1")
			inOverlap0, inOverlap1, overlapSubring, subring0, subring1 :=
				rings[0], rings[1], rings[2], rings[3], rings[4]
			// A chart's ring read inside the overlap's ring is the chart's ring read inside L.
			fieldOps, overlapOps := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			in0, in0L :=
				module_record.RestrictRingDef.At(overlapOps, A0), module_record.RestrictRingDef.At(fieldOps, A0)
			in1, in1L :=
				module_record.RestrictRingDef.At(overlapOps, A1), module_record.RestrictRingDef.At(fieldOps, A1)

			span0 := a.Have(
				"chart 0 lies in the subring A₀₁ and holds one, so it spans A₀₁",
				"module_span(«wbRing»(A₀₁), «wbField», A₀) = A₀₁",
				By(
					fractional_ideal.SpanHoldingOne.Read(L).At(A01, A0),
					overlapSubring,
					inOverlap0,
					comm_ring.SubringOne.Read(subring0)))
			span1 := a.Have(
				"so does chart 1",
				"module_span(«wbRing»(A₀₁), «wbField», A₁) = A₀₁",
				By(
					fractional_ideal.SpanHoldingOne.Read(L).At(A01, A1),
					overlapSubring,
					inOverlap1,
					comm_ring.SubringOne.Read(subring1)))
			lattice := a.Have(
				"each chart a submodule over its own ring, both spanning A₀₁: the structure pair is a lattice pair",
				"«wbPair»((A₀, A₁))",
				Unfold(lattice_pair.LatticePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					fractional_ideal.FieldModuleOn.Read(L).At(A01),
					overlapSubring,
					fractional_ideal.SubringSubmodule.Read(L).At(A0),
					subring0,
					fractional_ideal.SubringSubmodule.Read(L).At(A1),
					subring1,
					span0,
					span1,
					in0,
					in0L,
					in1,
					in1L))
			a.Show(
				"each chart is invertible over itself, and the pair is a lattice pair over the overlap",
				Unfold(InvertibleLatticePairDef),
				By(
					fractional_ideal.SubringInvertible.Read(L).At(A0),
					subring0,
					fractional_ideal.SubringInvertible.Read(L).At(A1),
					subring1,
					lattice,
					pairs.Fst,
					pairs.Snd))
		}),
})}

// AmbientInvertible — the ambient of a pair whose first chart is an
// invertible fractional ideal of chart 0 is an invertible fractional ideal
// of the overlap, whose inverse is the ambient of the inverse pair. The two
// ambients are the A₀₁-spans of X = fst(M) and of its inverse (A₀ : X), the
// first chart of the inverse pair, and extending along the subrings A₀ ⊆ A₀₁
// keeps X invertible with that inverse (subring_localization.ExtensionOfInvertible).
var AmbientInvertible = ambientInvertibleThm{family.Add(registry.ProofEntry{
	Name: "AmbientInvertible",
	Key:  "prop_f03a0af42527ce01",
	Reading: "Only chart 0 enters: the ambient is the A₀₁-span of fst(M), and what is " +
		"load-bearing is fst(M) invertible over the subring A₀, which holds one and lies in " +
		"A₀₁. M need not be a lattice pair, and neither snd(M), A₁ nor a datum enters, so " +
		"read at A₁ with the charts of M exchanged it gives the ambient of the second chart. " +
		"Finite generation does not enter, and L need not be the fraction field of A₀₁.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀₁)",
			"A₀ ⊆ A₀₁",
			"subring(field_ring(L), A₀)",
			"invertible_fractional(field_ring(L), A₀, fst(M))",
		},
		Conclusion: "invertible_fractional(field_ring(L), A₀₁, «wbAmbient»(M)) ∧ " +
			"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M)) = «wbAmbient»(«wbInverse»(M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap is a subring of L",
				"chart 0 lies in the overlap",
				"and is a subring of L",
				"on which fst(M) is an invertible fractional ideal")
			a.Show(
				"the ambients are the overlap spans of fst(M) and of "+
					"its inverse over chart 0, which extension keeps inverse",
				Unfold(lattice_pair.LatticePairAmbientDef),
				Simp(Fwd(LatticePairInverseDef), Fwd(pairs.Fst)),
				By(
					parts[0],
					parts[1],
					parts[2],
					parts[3],
					subring_localization.ExtensionOfInvertible.Read(L).At(A0, A01, a.TermAs[Set[A]]("fst(M)"))))
		}),
})}

// InvertibleLatticeProduct — the product of two invertible pairs is
// invertible. On each chart, a subring of L by the datum, the product of
// two invertible fractional ideals is invertible (InvertibleProduct), and
// the product pair is a lattice pair, as any product of lattice pairs is
// (MulIsLattice).
var InvertibleLatticeProduct = invertibleLatticeProductThm{family.Add(registry.ProofEntry{
	Name: "InvertibleLatticeProduct",
	Key:  "prop_a40485fad1650cd1",
	Reading: "Only the invertibility of M · N is stated; that its inverse is " +
		"M⁻¹ · N⁻¹ is fractional_ideal.InvertibleProduct's, chart by chart. Of " +
		"the datum only its charts being subrings of L inside the overlap enter.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
			"«wbInvertible»(N)",
		},
		Conclusion: "«wbInvertible»(«wbMul»(M, N))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the charts form the biaffine datum",
				"M is invertible",
				"and so is N")
			overlapInL, datum := parts[0], parts[1]
			ownM := a.Conjuncts(
				a.Unfolded(parts[2], InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"and M is a lattice pair over the overlap")
			ownN := a.Conjuncts(
				a.Unfolded(parts[3], InvertibleLatticePairDef),
				"fst(N) is an invertible fractional ideal of A₀",
				"snd(N) is one of A₁",
				"and N is a lattice pair over the overlap")
			rings := a.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")
			subring0, subring1 := rings[3], rings[4]
			fstM, sndM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			fstN, sndN := a.TermAs[Set[A]]("fst(N)"), a.TermAs[Set[A]]("snd(N)")
			product0 := a.Have(
				"the product on chart 0 is invertible",
				"invertible_fractional(field_ring(L), A₀, fractional_mul(field_ring(L), A₀, fst(M), fst(N)))",
				By(subring0, ownM[0], ownN[0], fractional_ideal.InvertibleProduct.Read(L).At(A0, fstM, fstN)))
			product1 := a.Have(
				"and so is the product on chart 1",
				"invertible_fractional(field_ring(L), A₁, fractional_mul(field_ring(L), A₁, snd(M), snd(N)))",
				By(subring1, ownM[1], ownN[1], fractional_ideal.InvertibleProduct.Read(L).At(A1, sndM, sndN)))
			productPair := a.Have(
				"the chartwise product is a lattice pair over the overlap",
				"«wbPair»(«wbMul»(M, N))",
				By(overlapInL, datum, ownM[2], ownN[2], MulIsLattice.Read(L).At(A0, A1, A01, t, M, N)))
			a.Show(
				"the product is a lattice pair whose two charts are invertible",
				Unfold(InvertibleLatticePairDef),
				Simp(Fwd(LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					product0,
					product1,
					productPair,
					LatticePairMulDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, M, N)))
		}),
})}

// InvertiblePairsCommMonoid — the invertible pairs form a commutative
// monoid under multiplication, with the structure pair as its unit.
var InvertiblePairsCommMonoid = invertiblePairsCommMonoidThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePairsCommMonoid",
	Key:  "prop_93f7642a844a2793",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
		},
		Conclusion: "comm_monoid_on({M:prod(set(A), set(A)) | «wbInvertible»(M)}, «wbMul», (A₀, A₁))",
	},
		func(a *Argument, L field.FieldFact[on.L], A0, A1, A01 *Expr[Set[A]], t *Expr[A], datum Fact) {
			parts := a.Conjuncts(
				datum,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)")
			inL, biaffine := parts[0], parts[1]
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			lattices := a.Have(
				"an invertible pair is a lattice pair in the field",
				"∀M:prod(set(A), set(A)). «wbInvertible»(M) ⇒ «wbPair»(M)",
				Derive(func(b *Argument) {
					M := b.FixAs[Prod[Set[A], Set[A]]]("M")
					b.Show(
						"the third conjunct of invertibility",
						By(b.Assume(), InvertibleLatticePairDef.At(ring, A0, A1, A01, M)))
				}))
			a.Show(
				"the unit and the products stay invertible, and the product laws hold at lattice pairs",
				Unfold(comm_monoid.CommMonoidOn),
				SplitConjAll(
					Case(
						"the structure pair is invertible",
						By(inL, biaffine, StructurePairInvertible.Read(L).At(A0, A1, A01, t))),
					// Read at the datum or the charts alone, the product laws keep their pairs quantified, as the comm_monoid_on clauses do.
					Case(
						"the product of invertible pairs is invertible",
						By(inL, biaffine, At(InvertibleLatticeProduct.Read(L), A0, A1, A01, t))),
					Case(
						"the product commutes, the charts of invertible pairs lying in L",
						By(At(InvertibleChartsInField.Read(L), A0, A1, A01), At(MulComm.Read(L), A0, A1))),
					Case(
						"the product associates, the chart rings being subrings of L as well",
						By(
							inL,
							biaffine,
							ChartRingsInField.Read(L).At(A0, A1, A01, t),
							At(InvertibleChartsInField.Read(L), A0, A1, A01),
							At(MulAssoc.Read(L), A0, A1))),
					Case(
						"the structure pair is the product's unit",
						By(inL, biaffine, lattices, At(MulOne.Read(L), A0, A1, A01, t))),
				))
		}),
})}

// InvertibleLatticeInverse — the inverse of an invertible pair is
// invertible, its product with the pair is the structure pair, and its
// inverse is the pair again. Chart by chart, the inverse of an invertible
// fractional ideal is invertible with the ideal as its inverse, and an
// invertible ideal times its inverse is the chart ring. The two charts of
// M⁻¹ span one A₀₁-module, (A₀₁ : ambient(M)): the first chart by
// AmbientInvertible, the second by AmbientInvertible read at chart 1 with
// the charts of M exchanged, the exchanged pair having the ambient of M
// (InvertiblePairSwap).
var InvertibleLatticeInverse = invertibleLatticeInverseThm{family.Add(registry.ProofEntry{
	Name: "InvertibleLatticeInverse",
	Key:  "prop_903266f2a5c078e1",
	Reading: "The first conjunct asks M⁻¹ to be a lattice pair, its two charts " +
		"spanning one A₀₁-module, and that is where the datum enters. The second is " +
		"the definition of invertibility read chart by chart. The third needs only " +
		"that each chart is invertible: (A₀ : (A₀ : X)) = X for an invertible X.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
		},
		Conclusion: "«wbInvertible»(«wbInverse»(M)) ∧ " +
			"«wbMul»(M, «wbInverse»(M)) = (A₀, A₁) ∧ " +
			"«wbInverse»(«wbInverse»(M)) = M",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)",
				"and M is invertible")
			invertible := parts[2]
			first, second := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			rings := a.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"A₀ lies in the overlap",
				"and so does A₁",
				"the overlap is a subring of L",
				"and so is A₀",
				"and so is A₁")
			inOverlap0, inOverlap1, overlapSubring, subring0, subring1 :=
				rings[0], rings[1], rings[2], rings[3], rings[4]
			// A chart's ring read inside the overlap's ring is the chart's ring read inside L.
			fieldOps, overlapOps := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			in0, in0L :=
				module_record.RestrictRingDef.At(overlapOps, A0), module_record.RestrictRingDef.At(fieldOps, A0)
			in1, in1L :=
				module_record.RestrictRingDef.At(overlapOps, A1), module_record.RestrictRingDef.At(fieldOps, A1)
			own := a.Conjuncts(
				a.Unfolded(invertible, InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"and M is a lattice pair over the overlap")
			lattice := a.Conjuncts(
				a.Unfolded(own[2], lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"the two charts span one submodule")
			own0 := a.Conjuncts(
				a.Unfolded(own[0], fractional_ideal.InvertibleFractionalDef),
				"fst(M) is a fractional ideal of A₀",
				"whose product with (A₀ : fst(M)) is A₀")
			own1 := a.Conjuncts(
				a.Unfolded(own[1], fractional_ideal.InvertibleFractionalDef),
				"snd(M) is a fractional ideal of A₁",
				"whose product with (A₁ : snd(M)) is A₁")

			inverse0 := a.Conjuncts(
				a.Have(
					"the inverse of an invertible fractional ideal is "+
						"invertible, with the ideal as its inverse: chart 0",
					"invertible_fractional(field_ring(L), A₀, fractional_inverse(field_ring(L), A₀, fst(M))) ∧ "+
						"fractional_inverse(field_ring(L), A₀, fractional_inverse(field_ring(L), A₀, fst(M))) = fst(M)",
					By(fractional_ideal.InvertibleInverse.Read(L).At(A0, first), subring0, own[0])),
				"(A₀ : fst(M)) is an invertible fractional ideal of A₀",
				"whose inverse is fst(M)")
			inverse1 := a.Conjuncts(
				a.Have(
					"and chart 1",
					"invertible_fractional(field_ring(L), A₁, fractional_inverse(field_ring(L), A₁, snd(M))) ∧ "+
						"fractional_inverse(field_ring(L), A₁, fractional_inverse(field_ring(L), A₁, snd(M))) = snd(M)",
					By(fractional_ideal.InvertibleInverse.Read(L).At(A1, second), subring1, own[1])),
				"(A₁ : snd(M)) is one of A₁",
				"whose inverse is snd(M)")
			inverseSubmodule0 := a.Conjuncts(
				a.Unfolded(inverse0[0], fractional_ideal.InvertibleFractionalDef),
				"so (A₀ : fst(M)) is an A₀-submodule of L",
				"whose product with its own inverse is A₀")
			inverseSubmodule1 := a.Conjuncts(
				a.Unfolded(inverse1[0], fractional_ideal.InvertibleFractionalDef),
				"and (A₁ : snd(M)) an A₁-submodule of L",
				"whose product with its own inverse is A₁")

			exchangedPair := a.TermAs[Prod[Set[A], Set[A]]]("(snd(M), fst(M))")
			exchanged := a.Conjuncts(
				GroupPremises(parts[2], InvertiblePairSwap.Read(L).At(A0, A1, A01, M)),
				"with its charts exchanged M is invertible over chart 1 and chart 0",
				"and keeps its ambient")[1]

			ambientInverse := a.Have(
				"the ambient of M⁻¹ is (A₀₁ : ambient(M))",
				"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M)) = «wbAmbient»(«wbInverse»(M))",
				By(AmbientInvertible.Read(L).At(A0, A1, A01, M), overlapSubring, inOverlap0, subring0, own[0]))
			exchangedAmbientInverse := a.Have(
				"and so is the ambient of the inverse of the exchanged pair, read at chart 1",
				"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M)) = "+
					"«wbAmbient»(lattice_pair_inverse(field_ring(L), A₁, A₀, (snd(M), fst(M))))",
				By(
					AmbientInvertible.Read(L).At(A1, A0, A01, exchangedPair),
					overlapSubring,
					inOverlap1,
					subring1,
					own[1],
					exchanged,
					pairs.Fst))
			spans := a.Have(
				"so the two charts of M⁻¹ span one A₀₁-submodule of L",
				"«wbSpan»(fractional_inverse(field_ring(L), A₀, fst(M))) = "+
					"«wbSpan»(fractional_inverse(field_ring(L), A₁, snd(M)))",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wbAmbient»(«wbInverse»(M))"),
						"the first chart of M⁻¹ spans its ambient",
						Simp(Fwd(lattice_pair.LatticePairAmbientDef), Fwd(LatticePairInverseDef), Fwd(pairs.Fst)),
						Basic()),
					Leg(
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M))"),
						"which is (A₀₁ : ambient(M))",
						By(ambientInverse)),
					Leg(
						a.TermAs[Set[A]]("«wbAmbient»(lattice_pair_inverse(field_ring(L), A₁, A₀, (snd(M), fst(M))))"),
						"which is the ambient of the inverse of the exchanged pair",
						By(exchangedAmbientInverse)),
					FinalLeg(
						"which is the span of that inverse's first chart, the second chart of M⁻¹",
						Simp(
							Fwd(lattice_pair.LatticePairAmbientDef),
							Fwd(LatticePairInverseDef),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						Basic())))

			inversePair := a.Have(
				"each a submodule over its chart and the two spanning one A₀₁-module, "+
					"the inverses of the charts form a lattice pair over the overlap",
				"«wbPair»((fractional_inverse(field_ring(L), A₀, fst(M)), "+
					"        fractional_inverse(field_ring(L), A₁, snd(M))))",
				Unfold(lattice_pair.LatticePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(lattice[0], inverseSubmodule0[0], inverseSubmodule1[0], spans, in0, in0L, in1, in1L))
			invertibleInverse := a.Have(
				"so M⁻¹ is invertible",
				"«wbInvertible»(«wbInverse»(M))",
				Unfold(InvertibleLatticePairDef),
				Simp(Fwd(LatticePairInverseDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(inverse0[0], inverse1[0], inversePair))
			product := a.Have(
				"each chart times its inverse is the chart's ring, so M · M⁻¹ is (A₀, A₁)",
				"«wbMul»(M, «wbInverse»(M)) = (A₀, A₁)",
				Simp(Fwd(LatticePairMulDef), Fwd(LatticePairInverseDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(Normalized, own0[1], own1[1]))
			inverseTwice := a.Have(
				"and each chart is the inverse of its inverse, so (M⁻¹)⁻¹ is M",
				"«wbInverse»(«wbInverse»(M)) = M",
				Simp(Fwd(LatticePairInverseDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(inverse0[1], inverse1[1], pairs.PairEta.At(M)))
			a.Show(
				"M⁻¹ is invertible, the inverse of M in the product, and has M as its inverse",
				By(invertibleInverse, product, inverseTwice))
		}),
})}

// InvertiblePairsGroup — the invertible pairs over a biaffine datum are an
// abelian group: the commutative monoid under the product, each pair M having
// M⁻¹ as its inverse, on the left because the product commutes.
var InvertiblePairsGroup = invertiblePairsGroupThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePairsGroup",
	Key:  "prop_57f6143eeb9dde64",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wbRing»(A₀₁), A₀, A₁, t, L.inv(t))",
		},
		Conclusion: "abelian_group_on(mk_group(«wbMul», (A₀, A₁), «wbInverse», «invertibles»))",
		Abbrev: Abbrev{
			{Name: "invertibles", Text: "{N:prod(set(A), set(A)) | «wbInvertible»(N)}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], A0, A1, A01 *Expr[Set[A]], t *Expr[A], datum Fact) {
			parts := a.Conjuncts(
				datum,
				"A₀₁ lies in L",
				"with A₀ and A₁ its charts at t and inv(t)")
			inL, biaffine := parts[0], parts[1]
			monoid := a.Have(
				"the invertible pairs are a commutative monoid under the product",
				"comm_monoid_on(«invertibles», «wbMul», (A₀, A₁))",
				By(inL, biaffine, InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t)))
			a.Show(
				"the monoid's laws are the group's, and M⁻¹ is the inverse",
				Unfold(abelian_group.AbelianGroupOn),
				Unfold(group.GroupOn),
				SplitConjAll(
					Case(
						"the structure pair is invertible",
						By(comm_monoid.IdentityIn.Read(monoid))),
					Case(
						"the product of invertible pairs is invertible",
						By(comm_monoid.OpIn.Read(monoid))),
					Case(
						"the inverse of an invertible pair is invertible",
						By(inL, biaffine, At(InvertibleLatticeInverse.Read(L), A0, A1, A01, t))),
					Case(
						"the product associates",
						By(comm_monoid.AssocOn.Read(monoid))),
					Case(
						"the structure pair is its left identity",
						By(comm_monoid.LeftIdentityOn.Read(monoid))),
					Case(
						"M⁻¹ is a left inverse of M: a right one, and the product commutes",
						By(
							inL,
							biaffine,
							At(InvertibleLatticeInverse.Read(L), A0, A1, A01, t),
							comm_monoid.CommOn.Read(monoid))),
					Case(
						"the product commutes",
						By(comm_monoid.CommOn.Read(monoid))),
				))
		}),
})}

// InvertibleLatticeScale — scaling by a nonzero member of the field keeps
// and reflects invertibility. On each chart, a subring of L by the datum,
// a nonzero multiple of a subset of L is an invertible fractional ideal
// exactly when the subset is (InvertibleScale), and the multiple of the
// pair is a lattice pair exactly when the pair is (ScaleIsLattice).
var InvertibleLatticeScale = invertibleLatticeScaleThm{family.Add(registry.ProofEntry{
	Name: "InvertibleLatticeScale",
	Key:  "prop_25f153e8a5944fdb",
	Reading: "a ≠ zero is load-bearing for ⇐: zero · M = ({zero}, {zero}) is invertible " +
		"for no M. The charts of M lie in L so that a · M determines M, as in ScaleIsLattice.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"fst(M) ⊆ L.carrier",
			"snd(M) ⊆ L.carrier",
		},
		Conclusion: "«wbInvertible»(lattice_pair_scale(a, M)) ⇔ «wbInvertible»(M)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t, a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"the overlap lies in L",
				"the charts form the biaffine datum",
				"a lies in L",
				"a is nonzero",
				"fst(M) lies in L",
				"and so does snd(M)")
			overlapInL, datum, aInL, nonzero, fstMInL, sndMInL :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			am := arg.MemberOf[on.L](a, aInL)
			rings := arg.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")
			subring0, subring1 := rings[3], rings[4]
			first, second := arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("snd(M)")
			scaled0 := arg.Have(
				"scaling keeps and reflects invertibility on chart 0",
				"invertible_fractional(field_ring(L), A₀, image(L.mul(a), fst(M))) ⇔ "+
					"invertible_fractional(field_ring(L), A₀, fst(M))",
				By(subring0, nonzero, fstMInL, fractional_ideal.InvertibleScale.Read(L).At(A0, first, am)))
			scaled1 := arg.Have(
				"and likewise on chart 1",
				"invertible_fractional(field_ring(L), A₁, image(L.mul(a), snd(M))) ⇔ "+
					"invertible_fractional(field_ring(L), A₁, snd(M))",
				By(subring1, nonzero, sndMInL, fractional_ideal.InvertibleScale.Read(L).At(A1, second, am)))
			scaledPair := arg.Have(
				"scaling also keeps and reflects the lattice-pair condition",
				"«wbPair»(lattice_pair_scale(a, M)) ⇔ «wbPair»(M)",
				By(overlapInL, datum, nonzero, fstMInL, sndMInL, ScaleIsLattice.Read(L).At(A0, A1, A01, t, am, M)))
			arg.Show(
				"the two chart equivalences and the lattice-pair equivalence give invertibility in both directions",
				Unfold(InvertibleLatticePairDef),
				Simp(Fwd(LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(scaled0, scaled1, scaledPair, LatticePairScaleDef.At(arg.TermAs[Op[A]]("L.mul"), a, M)))
		}),
})}

// ---------------------------------------------------------------------------
// Maps out of an invertible pair
// ---------------------------------------------------------------------------

// H0MulInverse — the sections of N · M⁻¹, for M invertible, are the
// members a of L carrying each chart of M into the same chart of N: H⁰ is
// the meet of the two charts of N · M⁻¹, and on each chart dividing by the
// invertible chart of M is taking the colon
// (invertible_fractional_ideal.MulInverseIsColon).
var H0MulInverse = h0MulInverseThm{family.Add(registry.ProofEntry{
	Name: "H0MulInverse",
	Key:  "prop_cacf194e88ed8e09",
	Reading: "Only M is asked to be invertible, chart by chart; N is any lattice pair in the " +
		"field, whose charts, fractional ideals of A₀ and A₁, are what each colon is taken into.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
			"«wbPair»(N)",
		},
		Conclusion: "lattice_pair_h0(«wbField», «wbMul»(N, «wbInverse»(M))).carrier = " +
			"{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N))} ∩ " +
			"{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N))}",
		Abbrev: Abbrev{
			{Name: "product0", Text: "fractional_mul(field_ring(L), " +
				"    A₀, " +
				"    fst(N), " +
				"    fractional_inverse(field_ring(L), A₀, fst(M)))"},
			{Name: "product1", Text: "fractional_mul(field_ring(L), " +
				"    A₁, " +
				"    snd(N), " +
				"    fractional_inverse(field_ring(L), A₁, snd(M)))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			const (
				colonFirst  = "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N))}"
				colonSecond = "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N))}"
			)
			parts := arg.Conjuncts(
				given,
				"A₀₁ lies in L",
				"with charts A₀ and A₁ at t and inv(t)",
				"M is invertible",
				"and N is a lattice pair")
			invertible, pairN := parts[2], parts[3]
			fieldOps, overlapOps :=
				arg.TermAs[RingOps[A]]("field_ring(L)"), arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			first, second := arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("snd(M)")
			firstN, secondN := arg.TermAs[Set[A]]("fst(N)"), arg.TermAs[Set[A]]("snd(N)")

			rings := arg.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"A₀ lies in the overlap",
				"and so does A₁",
				"the overlap is a subring of L",
				"and so is A₀",
				"and so is A₁")
			chart0Subring, chart1Subring := rings[3], rings[4]
			mCharts := arg.Conjuncts(
				arg.Unfolded(invertible, InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) one of A₁",
				"M is a lattice pair in L's regular module")
			nCharts := arg.Conjuncts(
				arg.Have(
					"the charts of N are fractional ideals of A₀ and A₁",
					"submodule(restrict_ring(field_ring(L), A₀), «wbField», fst(N)) ∧ "+
						"submodule(restrict_ring(field_ring(L), A₁), «wbField», snd(N))",
					By(
						arg.Unfolded(pairN, lattice_pair.LatticePairDef),
						module_record.RestrictRingDef.At(overlapOps, A0),
						module_record.RestrictRingDef.At(fieldOps, A0),
						module_record.RestrictRingDef.At(overlapOps, A1),
						module_record.RestrictRingDef.At(fieldOps, A1))),
				"fst(N) is a fractional ideal of A₀",
				"snd(N) one of A₁")

			colon0 := arg.Have(
				"dividing by the invertible fst(M) is the colon (fst(N) : fst(M))",
				"«product0» = «colonFirst»",
				By(
					invertible_fractional_ideal.MulInverseIsColon.Read(L).At(A0, first, firstN),
					chart0Subring,
					mCharts[0],
					nCharts[0]))
			colon1 := arg.Have(
				"and dividing by snd(M) the colon (snd(N) : snd(M))",
				"«product1» = «colonSecond»",
				By(
					invertible_fractional_ideal.MulInverseIsColon.Read(L).At(A1, second, secondN),
					chart1Subring,
					mCharts[1],
					nCharts[1]))
			h0 := arg.Have(
				"H⁰ is the meet of the two charts of N · M⁻¹, the products "+
					"of the charts of N with the inverses of those of M",
				"lattice_pair_h0(«wbField», «wbMul»(N, «wbInverse»(M))).carrier = «product0» ∩ «product1»",
				Simp(
					Fwd(lattice_pair.LatticePairH0Def),
					Fwd(LatticePairMulDef),
					Fwd(LatticePairInverseDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				Basic())
			arg.Show(
				"so it is the meet of the two colons",
				h0.Rw(),
				colon0.Rw(),
				colon1.Rw(),
				Basic())
		}),
})}

// InvertibleHomIsScale — the maps of lattice pairs out of an invertible M
// into N are the multiplications by the members of H⁰(N · M⁻¹), each on
// the ambient of M: Hom(M, N) = H⁰(N ⊗ M⁻¹) for line bundles. A section of
// N · M⁻¹ is a member a of L with a · fst(M) ⊆ fst(N) and
// a · snd(M) ⊆ snd(N) (H0MulInverse), and multiplication by such an a is a
// map of pairs (ScaleOnAmbient). Conversely an A₀₁-linear map g of the
// ambient of M into L is multiplication by a = Σ y(i) * g(x(i)), with
// one = Σ x(i) * y(i) a partition of unity of fst(M): each v of the
// ambient multiplies y(i) into A₀₁, (A₀ : fst(M)) lying in the inverse
// (A₀₁ : ambient) of the ambient (AmbientInvertible), so A₀₁-linearity at
// the scalars x(i) * y(i) and v * y(i) gives
// (g(v) * x(i)) * y(i) = v * (y(i) * g(x(i))), and summing over i, the
// partition expanding g(v) (invertible_fractional_ideal.PartitionOfUnityExpansion),
// g(v) = a * v.
var InvertibleHomIsScale = invertibleHomIsScaleThm{family.Add(registry.ProofEntry{
	Name: "InvertibleHomIsScale",
	Key:  "prop_eab29199fe28a8d1",
	Reading: "Only M is asked to be invertible; N may be any lattice pair in the " +
		"field. The maps are zero off the ambient of M (hom_set), whence the COND.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
			"«wbPair»(N)",
		},
		Conclusion: "lattice_pair_maps(«wbRing»(A₀₁), «wbField», M, «wbField», N) = " +
			"{λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero) | " +
			"a:A | " +
			"a ∈ lattice_pair_h0(«wbField», «wbMul»(N, «wbInverse»(M))).carrier}",
		Abbrev: Abbrev{
			// The maps of pairs from M to N, and the sections of N · M⁻¹ they are the multiplications by.
			{Name: "maps", Text: "lattice_pair_maps(«wbRing»(A₀₁), «wbField», M, «wbField», N)"},
			{Name: "sections", Text: "lattice_pair_h0(«wbField», «wbMul»(N, «wbInverse»(M))).carrier"},
			// The sum over the indices of the partition of unity one = Σ x(i) * y(i), i < n, that the lemma unpacks.
			{Name: "partitionSum", Text: "module_sum(L.add, L.zero, {i:num | i < n})"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// An A₀₁-linear map of the ambient of an invertible M into L is
			// multiplication by a member of L.
			multiplication := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)). ∀g:(A → A).",
				Hypotheses: []string{
					"A₀₁ ⊆ L.carrier",
					"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
					"«wbInvertible»(M)",
					"module_homomorphism(«wbRing»(A₀₁), restrict_module(«wbField», «wbAmbient»(M)), «wbField», g)",
				},
				Conclusion: "∃a:A. a ∈ L.carrier ∧ (∀v:A. v ∈ «wbAmbient»(M) ⇒ g(v) = a * v)",
			},
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					A0, A1, A01 *Expr[Set[A]],
					t *Expr[A],
					M *Expr[Prod[Set[A], Set[A]]],
					g *Arrow[A, A],
					given Fact,
				) {
					parts := arg.Conjuncts(
						given,
						"A₀₁ lies in L",
						"with charts A₀ and A₁ at t and inv(t)",
						"M is invertible",
						"and g is A₀₁-linear on the ambient of M")
					invertible, linear := parts[2], parts[3]
					fieldRing := field.RingOn.Read(L)
					regularModule := module.RegularModuleOn.Read(fieldRing)
					overlapOps := arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
					vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
					first, inverse0Set := arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("«ambientInvertibleInverse»")

					mCharts := arg.Conjuncts(
						arg.Unfolded(invertible, InvertibleLatticePairDef),
						"fst(M) is an invertible fractional ideal of A₀",
						"snd(M) one of A₁",
						"M is a lattice pair in L's regular module")
					contains := arg.Conjuncts(
						arg.Have(
							"so its ambient is an A₀₁-submodule of L holding both charts",
							"submodule(«wbRing»(A₀₁), «wbField», «wbAmbient»(M)) ∧ "+
								"fst(M) ⊆ «wbAmbient»(M) ∧ "+
								"snd(M) ⊆ «wbAmbient»(M)",
							By(lattice_pair.AmbientContains.At(overlapOps, A0, A1, vectors, M), mCharts[2])),
						"the ambient of M is an A₀₁-submodule of L",
						"holding fst(M)",
						"and snd(M)")
					ambientInL := arg.Have(
						"the ambient lies in L, a submodule of it",
						"«wbAmbient»(M) ⊆ L.carrier",
						By(submodule.SubmoduleSubset.Read(contains[0])))
					fstMInL := arg.Conjuncts(
						GroupPremises(parts[2], InvertibleChartsInField.Read(L).At(A0, A1, A01, M)),
						"fst(M) lies in L",
						"and so does snd(M)")[0]
					rings := arg.Conjuncts(
						GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
						"A₀ lies in the overlap",
						"and so does A₁",
						"the overlap is a subring of L",
						"and so is A₀",
						"and so is A₁")
					inOverlap0, overlapSubring, subring0 := rings[0], rings[2], rings[3]

					// (A₀ : fst(M)) lies in its A₀₁-span, the ambient of M⁻¹, which is
					// the inverse (A₀₁ : ambient) of the ambient of M over A₀₁.
					inverseAmbient := arg.Have(
						"the inverse of the ambient of M over A₀₁ is the ambient "+
							"of M⁻¹, fst(M) being invertible over the subring A₀ ⊆ A₀₁",
						"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M)) = «wbAmbient»(«wbInverse»(M))",
						By(AmbientInvertible.Read(L).At(A0, A1, A01, M), overlapSubring, inOverlap0, subring0, mCharts[0]))
					inSpan := arg.Have(
						"so (A₀ : fst(M)) lies in (A₀₁ : ambient)",
						"«ambientInvertibleInverse» ⊆ fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M))",
						inverseAmbient.Rw(),
						Unfold(lattice_pair.LatticePairAmbientDef),
						Simp(Fwd(LatticePairInverseDef), Fwd(pairs.Fst)),
						Cite(submodule.SubsetSpan, overlapOps, vectors, inverse0Set))
					ambientProducts := arg.Have(
						"a member v of the ambient and w of (A₀ : fst(M)) have v * w ∈ A₀₁",
						"∀v w:A. v ∈ «wbAmbient»(M) ∧ w ∈ «ambientInvertibleInverse» ⇒ v * w ∈ A₀₁",
						Derive(func(b *Argument) {
							b.FixAs[A]("v")
							b.FixAs[A]("w")
							in := b.Conjuncts(
								b.Assume(),
								"v lies in the ambient",
								"w lies in (A₀ : fst(M))")
							inColon := b.Have(
								"w lies in (A₀₁ : ambient)",
								"w ∈ fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M))",
								BySets(inSpan, in[1]))
							colon := b.Have(
								"so w lies in L and multiplies the ambient into A₀₁",
								"w ∈ L.carrier ∧ (∀u:A. u ∈ «wbAmbient»(M) ⇒ w * u ∈ A₀₁)",
								BySets(b.Unfolded(inColon, fractional_ideal.FractionalInverseDef)))
							vInL := b.Have(
								"v lies in L",
								"v ∈ L.carrier",
								BySets(in[0], ambientInL))
							commute := b.Have(
								"the field's product commutes",
								"v * w = w * v",
								ByArith(fieldRing, vInL, colon))
							b.Show(
								"w * v lies in A₀₁",
								commute.Rw(),
								BySets(colon, in[0]))
						}))

					// A partition of unity of the first chart, one = Σ x(i) * y(i).
					n, x, y, partition := arg.Unpack3As[Nat, Fun[Nat, A], Fun[Nat, A]](
						GroupPremises(
							rings[3], mCharts[0], invertible_fractional_ideal.InvertiblePartitionOfUnity.Read(L).At(A0, first)),
						"n",
						"x",
						"y")
					split := arg.Conjuncts(
						partition,
						"each x(i) lies in fst(M) and each y(i) in (A₀ : fst(M))",
						"and one is the sum of the products x(i) * y(i)")
					onRange, sumOne := split[0], split[1]
					below := arg.TermAs[Set[Nat]]("{i:num | i < n}")
					finiteBelow := arg.Have(
						"the indices below n are finitely many",
						"finite({i:num | i < n})",
						Cite(num_segment.FiniteBelowStrict))
					members := arg.Have(
						"each x(i) and each y(i) lies in the field",
						"∀i:num. i < n ⇒ x(i) ∈ L.carrier ∧ y(i) ∈ L.carrier",
						BySets(onRange, fstMInL, fractional_ideal.FractionalInverseSubset.Read(L).At(A0, first)))
					xInAmbient := arg.Have(
						"each x(i) lies in the ambient",
						"∀i:num. i < n ⇒ x(i) ∈ «wbAmbient»(M)",
						BySets(onRange, contains[1]))

					// The multiplier a = Σ y(i) * g(x(i)), a member of L.
					gIn := arg.Have(
						"g carries the ambient into L",
						"∀v:A. v ∈ «wbAmbient»(M) ⇒ g(v) ∈ L.carrier",
						By(module_homomorphism.HomIn.Read(linear)))
					summands := arg.Have(
						"each y(i) * g(x(i)) lies in L",
						"∀i:num. i < n ⇒ y(i) * g(x(i)) ∈ L.carrier",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							inRange := b.Assume()
							image := b.Have(
								"g(x(i)) lies in L, x(i) lying in the ambient",
								"g(x(i)) ∈ L.carrier",
								By(gIn, xInAmbient.At(i), inRange))
							b.Show(
								"a product of two members of L",
								By(
									comm_ring.MulIn.Read(fieldRing).AsFact().At(b.TermAs[A]("y(i)"), b.TermAs[A]("g(x(i))")),
									members.At(i),
									inRange,
									image))
						}))
					summand := arg.TermAs[Fun[Nat, A]]("λi:num. y(i) * g(x(i))")
					multiplier := arg.TermAs[A]("«partitionSum»(λi:num. y(i) * g(x(i)))")
					arg.Take(multiplier)
					defined := arg.Let("a", multiplier)
					aInL := arg.Have(
						"a lies in L, a finite sum of members of L",
						"a ∈ L.carrier",
						defined.Rw(),
						By(finiteBelow, summands, module.ModuleSumIn.Read(regularModule).At(below, summand)))

					scaling := arg.Have(
						"on the ambient g multiplies by a",
						"∀v:A. v ∈ «wbAmbient»(M) ⇒ g(v) = a * v",
						Derive(func(b *Argument) {
							v := b.FixAs[A]("v")
							vIn := b.Assume()
							vInL := b.Have(
								"v lies in L",
								"v ∈ L.carrier",
								BySets(vIn, ambientInL))
							gv := b.TermAs[A]("g(v)")
							gvInL := b.Have(
								"and so does g(v)",
								"g(v) ∈ L.carrier",
								By(gIn, vIn))
							termwise := b.Have(
								"termwise, g(v) * x(i) * y(i) = v * (y(i) * g(x(i))), "+
									"by A₀₁-linearity at x(i) * y(i) and at v * y(i)",
								"∀i:num. i < n ⇒ g(v) * x(i) * y(i) = v * (y(i) * g(x(i)))",
								Derive(func(c *Argument) {
									i := c.FixAs[Nat]("i")
									inRange := c.Assume()
									xi, yi := c.TermAs[A]("x(i)"), c.TermAs[A]("y(i)")
									xInAmb := c.Have(
										"x(i) lies in the ambient",
										"x(i) ∈ «wbAmbient»(M)",
										By(xInAmbient.At(i), inRange))
									yInverse := c.Have(
										"y(i) lies in (A₀ : fst(M))",
										"y(i) ∈ «ambientInvertibleInverse»",
										By(onRange.At(i), inRange))
									unit := c.Have(
										"x(i) * y(i) lies in A₀₁",
										"x(i) * y(i) ∈ A₀₁",
										By(ambientProducts.At(xi, yi), xInAmb, yInverse))
									scalar := c.Have(
										"and so does v * y(i)",
										"v * y(i) ∈ A₀₁",
										By(ambientProducts.At(v, yi), vIn, yInverse))
									atUnit := c.Have(
										"A₀₁-linearity at the scalar x(i) * y(i)",
										"g(x(i) * y(i) * v) = x(i) * y(i) * g(v)",
										By(module_homomorphism.HomSmul.Read(linear).AsFact().At(c.TermAs[A]("x(i) * y(i)"), v), unit, vIn))
									atScalar := c.Have(
										"and at the scalar v * y(i)",
										"g(v * y(i) * x(i)) = v * y(i) * g(x(i))",
										By(
											module_homomorphism.HomSmul.Read(linear).AsFact().At(c.TermAs[A]("v * y(i)"), xi),
											scalar,
											xInAmb))
									regroup := c.Have(
										"the two arguments are one member of L",
										"x(i) * y(i) * v = v * y(i) * x(i)",
										ByArith(fieldRing, members.At(i), inRange, vInL))
									c.Show(
										"so the two scalings agree",
										CalcEq(
											Leg(
												c.TermAs[A]("x(i) * y(i) * g(v)"),
												"the product commutes",
												ByArith(fieldRing, gvInL, members.At(i), inRange)),
											Leg(
												c.TermAs[A]("g(x(i) * y(i) * v)"),
												"A₀₁-linearity at x(i) * y(i)",
												By(atUnit)),
											Leg(
												c.TermAs[A]("g(v * y(i) * x(i))"),
												"the arguments regroup",
												By(regroup)),
											Leg(
												c.TermAs[A]("v * y(i) * g(x(i))"),
												"A₀₁-linearity at v * y(i)",
												By(atScalar)),
											FinalLeg(
												"the product regroups",
												ByArith(fieldRing, vInL, members.At(i), inRange, gIn, xInAmb)),
										))
								}))
							passOut := b.Have(
								"v passes into the sum defining a",
								"v * «partitionSum»(λi:num. y(i) * g(x(i))) = «partitionSum»(λi:num. v * (y(i) * g(x(i))))",
								By(
									finiteBelow,
									summands,
									module.ModuleSumSmul.Read(regularModule).At(below, b.MemberOf[on.L](v, vInL), summand)))
							b.Show(
								"so g(v) = a * v",
								CalcEq(
									Leg(
										b.TermAs[A]("«partitionSum»(λi:num. g(v) * x(i) * y(i))"),
										"the partition of unity expands g(v)",
										By(
											invertible_fractional_ideal.PartitionOfUnityExpansion.Read(L).At(
												b.MemberOf[on.L](gv, gvInL), n, x, y),
											members,
											sumOne)),
									Leg(
										b.TermAs[A]("«partitionSum»(λi:num. v * (y(i) * g(x(i))))"),
										"term by term",
										By(termwise, module.ModuleSumCongruence)),
									Leg(
										b.TermAs[A]("v * «partitionSum»(λi:num. y(i) * g(x(i)))"),
										"v comes out of the sum",
										By(passOut)),
									Leg(
										b.TermAs[A]("v * a"),
										"the sum is a",
										By(defined)),
									FinalLeg(
										"the product commutes",
										ByArith(fieldRing, vInL, aInL)),
								))
						}))
					arg.Show(
						"so g multiplies by a, a member of L",
						By(aInL, scaling))
				})

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					A0, A1, A01 *Expr[Set[A]],
					t *Expr[A],
					M, N *Expr[Prod[Set[A], Set[A]]],
					given Fact,
				) {
					const (
						colonFirst  = "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N))}"
						colonSecond = "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N))}"
					)
					parts := arg.Conjuncts(
						given,
						"A₀₁ lies in L",
						"with charts A₀ and A₁ at t and inv(t)",
						"M is invertible",
						"and N is a lattice pair")
					overlapInL, datum, invertible, pairN := parts[0], parts[1], parts[2], parts[3]
					overlapOps, vectors :=
						arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)"), arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
					onAmbient := arg.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«wbField», «wbAmbient»(M))")

					mCharts := arg.Conjuncts(
						arg.Unfolded(invertible, InvertibleLatticePairDef),
						"fst(M) is an invertible fractional ideal of A₀",
						"snd(M) one of A₁",
						"M is a lattice pair in L's regular module")
					charts := arg.Conjuncts(
						arg.Have(
							"its charts lie in its ambient",
							"fst(M) ⊆ «wbAmbient»(M) ∧ snd(M) ⊆ «wbAmbient»(M)",
							By(lattice_pair.AmbientContains.At(overlapOps, A0, A1, vectors, M), mCharts[2])),
						"fst(M) lies in the ambient",
						"and so does snd(M)")
					firstIn, secondIn := charts[0], charts[1]
					sectionsEq := arg.Have(
						"a section of N · M⁻¹ is a member of L carrying each chart of M into the same chart of N",
						"«sections» = «colonFirst» ∩ «colonSecond»",
						By(H0MulInverse.Read(L).At(A0, A1, A01, t, M, N), overlapInL, datum, invertible, pairN))

					scales := arg.Have(
						"multiplication by a section of N · M⁻¹, on the ambient and zero off it, is a map of pairs",
						"∀a:A. a ∈ «sections» ⇒ (λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)) ∈ «maps»",
						Derive(func(b *Argument) {
							a := b.FixAs[A]("a")
							inColons := b.Simplified(b.Assume(), Fwd(sectionsEq))
							aParts := b.Conjuncts(
								b.Have(
									"a lies in L and carries each chart of M into the same chart of N",
									"a ∈ L.carrier ∧ (∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N)) ∧ (∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N))",
									BySets(inColons)),
								"a lies in L",
								"a · fst(M) lies in fst(N)",
								"a · snd(M) lies in snd(N)")
							aInL, into0, into1 := aParts[0], aParts[1], aParts[2]
							b.Show(
								"multiplication by a, on the ambient and zero off it, lies in hom_set "+
									"and carries each chart of M onto a times it, inside the chart of N",
								Simp(Fwd(lattice_pair_map.LatticePairMapsDef)),
								BySets(
									ScaleOnAmbient.Read(L).At(A0, A1, A01, t, b.MemberOf[on.L](a, aInL), M),
									overlapInL,
									datum,
									mCharts[2],
									into0,
									into1))
						}))

					mapsIff := arg.Have(
						"a map of pairs from M to N is multiplication by a "+
							"section of N · M⁻¹ on the ambient of M, zero off it",
						"∀g:A → A. "+
							"    g ∈ «maps» ⇔ (∃a:A. a ∈ «sections» ∧ g = (λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)))",
						Derive(func(b *Argument) {
							g := b.FixAs[Fun[A, A]]("g")
							b.Iff()
							b.Forward(
								"a map g of pairs is multiplication by a member a "+
									"of L, which carries each chart of M into that of N",
								func(c *Argument, pairMap Fact) {
									opened := c.Simplified(
										pairMap,
										Fwd(lattice_pair_map.LatticePairMapsDef),
										Fwd(set_image.ImageSubsetIff))
									parts := c.Conjuncts(
										opened,
										"g is an A₀₁-linear map of the ambient of M into L, zero off it",
										"g carries fst(M) into fst(N)",
										"and snd(M) into snd(N)")
									zeroOff := c.Have(
										"and zero off it",
										"∀u:A. u ∉ «wbAmbient»(M) ⇒ g(u) = L.zero",
										By(parts[0], hom_module.InHomSet.At(overlapOps, onAmbient, vectors, g)))
									a, multiplier := c.ObtainAs[A](
										"so g multiplies by a member a of L on the ambient",
										"∃a:A. a ∈ L.carrier ∧ (∀v:A. v ∈ «wbAmbient»(M) ⇒ g(v) = a * v)",
										By(
											L,
											overlapInL,
											datum,
											invertible,
											parts[0],
											hom_module.InHomSet.At(overlapOps, onAmbient, vectors, g),
											multiplication))
									multiplies := c.Conjuncts(
										multiplier,
										"a lies in L",
										"and g multiplies by a on the ambient")
									aInL, scaling := multiplies[0], multiplies[1]
									into0 := c.Have(
										"a carries fst(M) into fst(N), a * m being g(m)",
										"∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N)",
										Derive(func(d *Argument) {
											m := d.FixAs[A]("m")
											mIn := d.Assume()
											mInAmbient := d.Have(
												"m lies in the ambient",
												"m ∈ «wbAmbient»(M)",
												BySets(mIn, firstIn))
											atM := d.Have(
												"where g multiplies by a",
												"g(m) = a * m",
												By(scaling.At(m), mInAmbient))
											d.Show(
												"so a * m = g(m) lies in fst(N)",
												atM.RwRev(),
												By(parts[1].At(m), mIn))
										}))
									into1 := c.Have(
										"and snd(M) into snd(N)",
										"∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N)",
										Derive(func(d *Argument) {
											m := d.FixAs[A]("m")
											mIn := d.Assume()
											mInAmbient := d.Have(
												"m lies in the ambient",
												"m ∈ «wbAmbient»(M)",
												BySets(mIn, secondIn))
											atM := d.Have(
												"where g multiplies by a",
												"g(m) = a * m",
												By(scaling.At(m), mInAmbient))
											d.Show(
												"so a * m = g(m) lies in snd(N)",
												atM.RwRev(),
												By(parts[2].At(m), mIn))
										}))
									section := c.Have(
										"so a is a section of N · M⁻¹, lying in both colons",
										"a ∈ «sections»",
										sectionsEq.Rw(),
										BySets(aInL, into0, into1))
									agrees := c.Have(
										"and g is multiplication by a on the ambient, zero off it",
										"g = λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)",
										Derive(func(d *Argument) {
											d.Do(Funext())
											v := d.FixAs[A]("v")
											d.Cases(d.Term("v ∈ «wbAmbient»(M)"))
											d.When(
												"on the ambient g multiplies by a",
												func(e *Argument, vIn Fact) {
													e.Show(
														"g(v) = a * v",
														By(scaling.At(v), vIn))
												})
											d.Otherwise(
												"off the ambient g is zero",
												func(e *Argument, vOut Fact) {
													e.Show(
														"g(v) = zero",
														By(zeroOff.At(v), vOut))
												})
										}))
									c.Take(a)
									c.Show(
										"a is the section g multiplies by",
										By(section, agrees))
								})
							b.Backward(
								"multiplication by a section of N · M⁻¹ is a map of pairs",
								func(c *Argument, scaled Fact) {
									a, written := c.UnpackAs[A](scaled, "a")
									pieces := c.Conjuncts(
										written,
										"a is a section of N · M⁻¹",
										"g is multiplication by a")
									section := c.Simplified(pieces[0], Fwd(lattice_pair.LatticePairH0Def))
									c.Show(
										"so g, multiplication by the section a, is a map of pairs",
										pieces[1].Rw(),
										By(scales.At(a), section))
								})
						}))
					comprehension := arg.Have(
						"a member of the set of multiplications is multiplication by a section",
						"∀g:A → A. "+
							"    g ∈ {(λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)) | a:A | a ∈ «sections»} ⇔ "+
							"    (∃a:A. a ∈ «sections» ∧ g = (λx:A. COND(x ∈ «wbAmbient»(M), a * x, L.zero)))",
						BySets())
					arg.Show(
						"so the maps of pairs are the multiplications by the sections of N · M⁻¹",
						Simp(Fwd(set_basic.Extension), Fwd(mapsIff), Fwd(comprehension)),
						Basic())
				})
		}),
})}

// SectionsAreMaps — Hom(M, N) ≅ H⁰(N · M⁻¹): for an invertible pair M, any
// lattice pair N in the field and a subring S of both charts,
// a ↦ (z ↦ a·z on the ambient of M, zero off it) is an S-isomorphism of the
// sections of N · M⁻¹ onto the maps of lattice pairs from M into N. The maps
// are those multiplications (InvertibleHomIsScale), the assignment is S-linear
// pointwise, and it is one-to-one because chart 0 of M holds a nonzero member,
// at which two equal maps agree.
var SectionsAreMaps = sectionsAreMapsThm{family.Add(registry.ProofEntry{
	Name: "SectionsAreMaps",
	Key:  "prop_5c76a1231013d884",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁ S:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wbRing»(A₀₁), A₀, A₁, t, L.inv(t))",
			"subring(«wbRing»(A₀₁), S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"«wbPair»(N)",
		},
		Conclusion: "module_isomorphism(«sectionsAreMapsScalars», " +
			"    lattice_pair_h0(«wbField», «sectionsAreMapsQuotient»), " +
			"    lattice_pair_hom(«wbRing»(A₀₁), «wbField», M, «wbField», N), " +
			"    «sectionsAreMapsMultiplication»)",
		Abbrev: Abbrev{
			{Name: "sectionsAreMapsScalars", Text: "restrict_ring(«wbRing»(A₀₁), S)"},
			{Name: "sectionsAreMapsQuotient", Text: "lattice_pair_mul(field_ring(L), " +
				"    A₀, " +
				"    A₁, " +
				"    N, " +
				"    «wbInverse»(M))"},
			{Name: "sectionsAreMapsSections", Text: "fst(«sectionsAreMapsQuotient») ∩ " +
				"snd(«sectionsAreMapsQuotient»)"},
			{Name: "sectionsAreMapsMaps", Text: "lattice_pair_maps(«wbRing»(A₀₁), «wbField», M, «wbField», N)"},
			{Name: "sectionsAreMapsMultiplication", Text: "λa:A. λz:A. " +
				"    COND(z ∈ «wbAmbient»(M), a * z, L.zero)"},
			{Name: "sectionsAreMapsColon", Text: "fractional_inverse(field_ring(L), A₀, fst(M))"},
			{Name: "sectionsAreMapsProduct", Text: "fractional_mul(field_ring(L), " +
				"    A₀, " +
				"    fst(M), " +
				"    «sectionsAreMapsColon»)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01, S *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[Prod[Set[A], Set[A]]],
			inField, biaffine, subringS, s0, s1, invertible, pairN Fact,
		) {
			overlapRing := arg.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			fieldModule := arg.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			inverse, quotient :=
				arg.TermAs[Prod[Set[A], Set[A]]]("«wbInverse»(M)"),
				arg.TermAs[Prod[Set[A], Set[A]]]("«sectionsAreMapsQuotient»")
			sections := arg.TermAs[Set[A]]("«sectionsAreMapsSections»")
			multiplication := arg.TermAs[Fun[A, Fun[A, A]]]("«sectionsAreMapsMultiplication»")

			// M, N · M⁻¹ as lattice pairs over the overlap.
			unfolded := arg.Conjuncts(
				arg.Unfolded(invertible, InvertibleLatticePairDef),
				"chart 0 of M is invertible over A₀",
				"chart 1 of M is invertible over A₁",
				"M is a lattice pair over the overlap")
			chartInvertible, pairM := unfolded[0], unfolded[2]
			inverseInvertible := arg.Have(
				"M⁻¹ is invertible",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «wbInverse»(M))",
				By(inField, biaffine, invertible, InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, M)))
			pairInverse := arg.Have(
				"so it is a lattice pair",
				"«wbPair»(«wbInverse»(M))",
				By(arg.Unfolded(inverseInvertible, InvertibleLatticePairDef)))
			pairQuotient := arg.Have(
				"and so is N · M⁻¹",
				"«wbPair»(«sectionsAreMapsQuotient»)",
				By(inField, biaffine, pairN, pairInverse, MulIsLattice.Read(L).At(A0, A1, A01, t, N, inverse)))

			// The maps M → N are the multiplications by the members of H⁰(N · M⁻¹).
			scale := arg.Have(
				"the maps M → N are the multiplications by the sections of N · M⁻¹",
				"«sectionsAreMapsMaps» = "+
					"{λz:A. COND(z ∈ «wbAmbient»(M), a * z, L.zero) | a:A | a ∈ «sectionsAreMapsSections»}",
				By(inField, biaffine, invertible, pairN, InvertibleHomIsScale.Read(L).At(A0, A1, A01, t, M, N)))
			image := arg.Have(
				"so they are the image of H⁰(N · M⁻¹) under multiplication",
				"image(«sectionsAreMapsMultiplication», «sectionsAreMapsSections») = «sectionsAreMapsMaps»",
				BySets(scale))

			// Both sides are S-modules.
			rings := arg.Conjuncts(
				GroupPremises(inField, biaffine, ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"and so is chart 0",
				"and so is chart 1")
			overlapModule := arg.Have(
				"L is a module over the overlap",
				"module_on(«wbRing»(A₀₁), «wbField»)",
				By(arg.Unfolded(pairM, lattice_pair.LatticePairDef)))
			sInOverlap := arg.Have(
				"S lies in the overlap, as chart 0 does",
				"S ⊆ A₀₁",
				BySets(s0, rings[0]))
			moduleS := arg.Have(
				"so L is a module over S",
				"module_on(«sectionsAreMapsScalars», «wbField»)",
				By(subringS, module.ModuleRestrictScalars.Read(overlapModule).At(S)))
			h0Submodule := arg.Have(
				"H⁰(N · M⁻¹) is an S-submodule of L",
				"submodule(«sectionsAreMapsScalars», «wbField», «sectionsAreMapsSections»)",
				By(
					s0,
					s1,
					pairQuotient,
					lattice_pair.H0Submodule.At(overlapRing, A0, A1, S, fieldModule, quotient)))
			h0Module := arg.Have(
				"so an S-module",
				"module_on(«sectionsAreMapsScalars», lattice_pair_h0(«wbField», «sectionsAreMapsQuotient»))",
				By(
					h0Submodule,
					submodule.SubmoduleModuleOn.Read(moduleS).At(sections),
					lattice_pair.LatticePairH0Def.At(fieldModule, quotient)))
			mapsModule := arg.Have(
				"and so are the maps M → N",
				"module_on(«sectionsAreMapsScalars», lattice_pair_hom(«wbRing»(A₀₁), «wbField», M, «wbField», N))",
				By(
					biaffine,
					subringS,
					s0,
					s1,
					pairM,
					pairN,
					lattice_pair_map.PairMapsLinearSpace.At(overlapRing, A0, A1, S, fieldModule, fieldModule, M, N)))
			sectionsInL := arg.Have(
				"H⁰(N · M⁻¹) lies in L",
				"«sectionsAreMapsSections» ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(h0Submodule)))
			ambient := arg.Conjuncts(
				GroupPremises(unfolded[2], lattice_pair.AmbientContains.At(overlapRing, A0, A1, fieldModule, M)),
				"the ambient of M is a submodule of L",
				"chart 0 of M lies in it",
				"chart 1 of M lies in it")
			ambientInL := arg.Have(
				"the ambient of M lies in L",
				"«wbAmbient»(M) ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(ambient[0])))

			// a ↦ (z ↦ a·z) is an S-linear map of H⁰(N · M⁻¹) into the maps M → N.
			into := arg.Have(
				"multiplication by a section is a map M → N",
				Statement{
					Binders: "∀u:A.",
					Hypotheses: []string{
						"u ∈ «sectionsAreMapsSections»",
					},
					Conclusion: "(λz:A. COND(z ∈ «wbAmbient»(M), u * z, L.zero)) ∈ «sectionsAreMapsMaps»",
				},
				Derive(func(c *Argument) {
					u := c.FixAs[A]("u")
					section := c.Assume()
					c.Show(
						"it is the image of u",
						By(image, section, set_image.FunInImage.At(multiplication, sections, u)))
				}))
			additive := arg.Have(
				"multiplication by u + v is the sum of the two multiplications",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ «sectionsAreMapsSections»",
						"v ∈ «sectionsAreMapsSections»",
					},
					Conclusion: "(λz:A. COND(z ∈ «wbAmbient»(M), (u + v) * z, L.zero)) = " +
						"fun_add(λz:A. COND(z ∈ «wbAmbient»(M), u * z, L.zero), " +
						"    λz:A. COND(z ∈ «wbAmbient»(M), v * z, L.zero))",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.FixAs[A]("v")
					members := c.Have(
						"u and v lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier",
						BySets(c.Assume(), sectionsInL))
					pointwise := c.Have(
						"at each point both maps take the same value",
						"∀z:A. "+
							"    COND(z ∈ «wbAmbient»(M), (u + v) * z, L.zero) = "+
							"    COND(z ∈ «wbAmbient»(M), u * z, L.zero) + COND(z ∈ «wbAmbient»(M), v * z, L.zero)",
						Derive(func(d *Argument) {
							d.FixAs[A]("z")
							d.Cases(d.Term("z ∈ «wbAmbient»(M)"))
							d.When(
								"on the ambient the product distributes over the sum",
								func(e *Argument, onAmbient Fact) {
									point := e.Have(
										"z lies in L",
										"z ∈ L.carrier",
										BySets(onAmbient, ambientInL))
									e.Show(
										"(u + v)·z = u·z + v·z",
										ByArith(field.RingOn.Read(L), point, onAmbient, members))
								})
							d.Otherwise(
								"off the ambient both sides are zero",
								func(e *Argument, offAmbient Fact) {
									e.Show(
										"zero is zero plus zero",
										ByArith(field.RingOn.Read(L), offAmbient))
								})
						}))
					c.Show(
						"so the two maps are one function",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						By(pointwise))
				}))
			homogeneous := arg.Have(
				"multiplication by c·u is c times the multiplication by u",
				Statement{
					Binders: "∀c u:A.",
					Hypotheses: []string{
						"c ∈ S",
						"u ∈ «sectionsAreMapsSections»",
					},
					Conclusion: "(λz:A. COND(z ∈ «wbAmbient»(M), c * u * z, L.zero)) = " +
						"fun_smul(c, λz:A. COND(z ∈ «wbAmbient»(M), u * z, L.zero))",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("c")
					c.FixAs[A]("u")
					members := c.Have(
						"c and u lie in L",
						"c ∈ L.carrier ∧ u ∈ L.carrier",
						BySets(c.Assume(), sInOverlap, inField, sectionsInL))
					pointwise := c.Have(
						"at each point both maps take the same value",
						"∀z:A. COND(z ∈ «wbAmbient»(M), c * u * z, L.zero) = c * COND(z ∈ «wbAmbient»(M), u * z, L.zero)",
						Derive(func(d *Argument) {
							d.FixAs[A]("z")
							d.Cases(d.Term("z ∈ «wbAmbient»(M)"))
							d.When(
								"on the ambient the product is associative",
								func(e *Argument, onAmbient Fact) {
									point := e.Have(
										"z lies in L",
										"z ∈ L.carrier",
										BySets(onAmbient, ambientInL))
									e.Show(
										"(c·u)·z = c·(u·z)",
										ByArith(field.RingOn.Read(L), point, onAmbient, members))
								})
							d.Otherwise(
								"off the ambient both sides are zero",
								func(e *Argument, offAmbient Fact) {
									e.Show(
										"zero is c times zero",
										ByArith(field.RingOn.Read(L), offAmbient, members))
								})
						}))
					c.Show(
						"so the two maps are one function",
						Funext(),
						Simp(Fwd(function_module.FunSmulDef)),
						By(pointwise))
				}))
			linear := arg.Have(
				"so a ↦ (z ↦ a·z) is S-linear from H⁰(N · M⁻¹) into the maps M → N",
				"module_homomorphism(«sectionsAreMapsScalars», "+
					"    lattice_pair_h0(«wbField», «sectionsAreMapsQuotient»), "+
					"    lattice_pair_hom(«wbRing»(A₀₁), «wbField», M, «wbField», N), "+
					"    «sectionsAreMapsMultiplication»)",
				By(
					h0Module,
					mapsModule,
					into,
					additive,
					homogeneous,
					lattice_pair_map.LatticePairHomDef.At(overlapRing, fieldModule, M, fieldModule, N),
					module_homomorphism.ModuleHomomorphismDef))

			// Chart 0 of M holds a nonzero member w: otherwise every product with
			// (A₀ : fst(M)) would vanish, and so would their span A₀, which holds one.
			chartSubring0 := rings[3]
			w, nonzero := arg.ObtainAs[A](
				"chart 0 of M holds a nonzero member",
				"∃w:A. w ∈ fst(M) ∧ w ≠ L.zero",
				Derive(func(c *Argument) {
					none := c.SupposeNot()
					vanish := c.Have(
						"then every product of a member of fst(M) with one of (A₀ : fst(M)) is zero",
						"∀p q:A. p ∈ fst(M) ∧ q ∈ «sectionsAreMapsColon» ⇒ p * q ∈ {L.zero}",
						BySets(
							none,
							fractional_ideal.FractionalInverseDef,
							comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(L))))
					overChart := c.Have(
						"L is a module over chart 0",
						"module_on(restrict_ring(field_ring(L), A₀), «wbField»)",
						By(chartSubring0, fractional_ideal.FieldModuleOn.Read(L).At(A0)))
					productZero := c.Have(
						"so fst(M) · (A₀ : fst(M)) lies in {zero}",
						"«sectionsAreMapsProduct» ⊆ {L.zero}",
						By(
							vanish,
							submodule.ZeroSubmodule.Read(overChart),
							fractional_ideal.FractionalMulLeast.Read(L).At(
								A0,
								c.TermAs[Set[A]]("fst(M)"),
								c.TermAs[Set[A]]("«sectionsAreMapsColon»"),
								c.TermAs[Set[A]]("{L.zero}"))))
					product := c.Conjuncts(
						c.Unfolded(chartInvertible, fractional_ideal.InvertibleFractionalDef),
						"fst(M) is a fractional ideal of A₀",
						"whose product with (A₀ : fst(M)) is A₀")
					oneIn := c.Have(
						"but that product is A₀, which holds one",
						"L.one ∈ «sectionsAreMapsProduct»",
						product[1].Rw(),
						By(comm_ring.SubringOne.Read(chartSubring0)))
					c.Show(
						"so one = zero, which it is not",
						BySets(productZero, oneIn, field.OneNotZeroOn.Read(L)))
				}))
			nonzeroParts := arg.Conjuncts(
				nonzero,
				"w lies in chart 0 of M",
				"w is not zero")
			wAmbient := arg.Have(
				"so w lies in the ambient of M",
				"w ∈ «wbAmbient»(M)",
				BySets(ambient[1], nonzeroParts[0]))
			wInL := arg.Have(
				"and in L",
				"w ∈ L.carrier",
				BySets(wAmbient, ambientInL))

			// Two sections with one multiplication agree at w, so they are equal.
			injective := arg.Have(
				"distinct sections give distinct maps, read at w",
				"injective_on(«sectionsAreMapsSections», «sectionsAreMapsMultiplication»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(c *Argument) {
					u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
					parts := c.Conjuncts(
						c.Assume(),
						"u is a section of N · M⁻¹",
						"so is v",
						"and the two multiplications agree")
					atW := c.Have(
						"read at w, u·w = v·w",
						"u * w = v * w",
						By(parts[2], wAmbient))
					members := c.Have(
						"u, v and w lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier ∧ w ∈ L.carrier",
						BySets(parts[0], parts[1], sectionsInL, wInL))
					commuted := c.Have(
						"so w·u = w·v",
						"w * u = w * v",
						ByArith(field.RingOn.Read(L), members, atW))
					c.Show(
						"w is not zero, so u = v",
						By(
							commuted,
							nonzeroParts[1],
							members,
							integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L)).AsFact().At(
								w, u, v)))
				}))
			arg.Show(
				"so a ↦ (z ↦ a·z) is an S-isomorphism of H⁰(N · M⁻¹) onto the maps M → N",
				By(
					linear,
					injective,
					image,
					lattice_pair_map.LatticePairHomDef.At(overlapRing, fieldModule, M, fieldModule, N),
					module_homomorphism.ModuleIsomorphismDef))
		}),
})}

// InvertibleIsoIffScale — an invertible pair M is isomorphic to N exactly
// when N is a nonzero multiple of M.
var InvertibleIsoIffScale = invertibleIsoIffScaleThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIsoIffScale",
	Key:  "prop_28328e5d6c99515c",
	Reading: "Nothing is asked of N: a pair isomorphic to an invertible one is " +
		"a multiple of it, hence invertible. The multiple is nonzero because an " +
		"isomorphism is one-to-one on the ambient of M, which holds a nonzero member.",
	Deps: []registry.EntryLike{
		InvertibleHomIsScale,
		ScaleIsomorphism,
		lattice_pair_map.LatticePairIsomorphismDef,
		lattice_pair_map.LatticePairMapsDef,
		LatticePairScaleDef,
		lattice_pair.LatticePairDef,
		InvertibleLatticePairDef,
		fractional_ideal.InvertibleFractionalDef,
		hom_module.HomSetDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
		},
		Conclusion: "(∃f:(A → A). " +
			"    lattice_pair_isomorphism(«wbRing»(A₀₁), «wbField», M, «wbField», N, f)) ⇔ " +
			"∃a:A. a ∈ L.carrier ∧ a ≠ L.zero ∧ N = lattice_pair_scale(a, M)",
	},
		"⇐ by ScaleIsomorphism; ⇒: N is a lattice pair, each chart the image of M's under "+
			"a map A₀₁-linear on the ambient of M, both spanning the image of that ambient; "+
			"so InvertibleHomIsScale makes the isomorphism multiplication by some a on the "+
			"ambient, and each chart of N, the image of the same chart of M, is a times it; "+
			"fst(M) ≠ {zero} since {zero} · X = {zero} ≠ A₀, so injectivity forces a ≠ zero"),
})}

// SectionInclusion — a nonzero section a of M embeds the structure pair in
// M by multiplication by a: a · (A₀, A₁) is an invertible pair inside M
// chart by chart. The structure pair is invertible
// (StructurePairInvertible), so its nonzero multiple is
// (InvertibleLatticeScale); and a lies in both charts of M, each a
// submodule over its chart ring, so a times each chart lies in that chart
// of M.
var SectionInclusion = sectionInclusionThm{family.Add(registry.ProofEntry{
	Name: "SectionInclusion",
	Key:  "prop_ca44d78c25011c31",
	Reading: "The theorem needs M only a lattice pair; a ≠ zero is " +
		"load-bearing for invertibility, since zero · (A₀, A₁) = ({zero}, {zero}).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
			"a ∈ lattice_pair_h0(«wbField», M).carrier",
			"a ≠ L.zero",
		},
		Conclusion: "«wbInvertible»(lattice_pair_scale(a, (A₀, A₁))) ∧ " +
			"image(L.mul(a), A₀) ⊆ fst(M) ∧ " +
			"image(L.mul(a), A₁) ⊆ snd(M)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t, a *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"the overlap lies in L",
				"the charts form the biaffine datum",
				"M is a lattice pair",
				"a is a section of M",
				"a is nonzero")
			overlapInL, datum, nonzero := parts[0], parts[1], parts[4]
			lattice := arg.Conjuncts(
				arg.Unfolded(parts[2], lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"the charts span the same module over the overlap")
			section := arg.Unfolded(parts[3], lattice_pair.LatticePairH0Def)
			inCharts := arg.Conjuncts(
				arg.Have(
					"a section lies in both charts",
					"a ∈ fst(M) ∧ a ∈ snd(M)",
					BySets(section)),
				"a lies in fst(M)",
				"and in snd(M)")
			fstMInL := arg.Conjuncts(
				GroupPremises(parts[2], LatticePairChartsInField.Read(L).At(A0, A1, A01, M)),
				"fst(M) lies in L",
				"and so does snd(M)")[0]
			aInL := arg.Have(
				"the section therefore lies in L",
				"a ∈ L.carrier",
				BySets(inCharts[0], fstMInL))
			am := arg.MemberOf[on.L](a, aInL)
			rings := arg.Conjuncts(
				GroupPremises(parts[0], parts[1], ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")
			chart0InL := arg.Have(
				"chart 0 lies in L",
				"A₀ ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(rings[3])))
			chart1InL := arg.Have(
				"and so does chart 1",
				"A₁ ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(rings[4])))
			structure := arg.TermAs[Prod[Set[A], Set[A]]]("(A₀, A₁)")
			structureInvertible := arg.Have(
				"the structure pair is invertible",
				"«wbInvertible»((A₀, A₁))",
				By(overlapInL, datum, StructurePairInvertible.Read(L).At(A0, A1, A01, t)))
			scaledStructure := arg.Have(
				"its nonzero multiple by a is invertible",
				"«wbInvertible»(lattice_pair_scale(a, (A₀, A₁)))",
				By(
					overlapInL,
					datum,
					nonzero,
					chart0InL,
					chart1InL,
					structureInvertible,
					InvertibleLatticeScale.Read(L).At(A0, A1, A01, t, am, structure),
					pairs.Fst.At(A0, A1),
					pairs.Snd.At(A0, A1)))
			commute := comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L)))
			aFirst, aSecond := proof.MemberOf(a, inCharts[0]), proof.MemberOf(a, inCharts[1])
			first, second := arg.TermAs[Set[A]]("fst(M)"), arg.TermAs[Set[A]]("snd(M)")
			byA := arg.TermAs[Fun[A, A]]("L.mul(a)")
			multiples0 := arg.Have(
				"multiplying a by each scalar in chart 0 stays in fst(M)",
				"∀c:A. c ∈ A₀ ⇒ a * c ∈ fst(M)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					cInL := b.Have(
						"c lies in L, as chart 0 does",
						"c ∈ L.carrier",
						BySets(cIn, chart0InL))
					b.Show(
						"commutativity identifies a * c with c * a",
						By(
							Normalized,
							submodule.SubmoduleSmul.Read(lattice[1]).At(proof.MemberOf(c, cIn), aFirst),
							commute.At(am, b.MemberOf[on.L](c, cInL))))
				}))
			multiples1 := arg.Have(
				"multiplying a by each scalar in chart 1 stays in snd(M)",
				"∀c:A. c ∈ A₁ ⇒ a * c ∈ snd(M)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					cInL := b.Have(
						"c lies in L, as chart 1 does",
						"c ∈ L.carrier",
						BySets(cIn, chart1InL))
					b.Show(
						"commutativity identifies a * c with c * a",
						By(
							Normalized,
							submodule.SubmoduleSmul.Read(lattice[2]).At(proof.MemberOf(c, cIn), aSecond),
							commute.At(am, b.MemberOf[on.L](c, cInL))))
				}))
			arg.Show(
				"the nonzero section gives an invertible pair contained in M chart by chart",
				By(
					scaledStructure,
					multiples0,
					set_image.ImageSubsetIff.At(byA, A0, first),
					multiples1,
					set_image.ImageSubsetIff.At(byA, A1, second)))
		}),
})}

// InverseHoldsOne — one is a section of the inverse of a pair inside the structure
// pair: on each chart, the pair's chart lies in the chart, and one lies in its inverse
// there (fractional_ideal.FractionalInverseHoldsOne).
var InverseHoldsOne = inverseHoldsOneThm{family.Add(registry.ProofEntry{
	Name: "InverseHoldsOne",
	Key:  "prop_170daf005866f585",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁:set(A). ∀J:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀)",
			"subring(field_ring(L), A₁)",
			"fst(J) ⊆ A₀",
			"snd(J) ⊆ A₁",
		},
		Conclusion: "L.one ∈ lattice_pair_h0(«wbField», «wbInverse»(J)).carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1 *Expr[Set[A]],
			J *Expr[Prod[Set[A], Set[A]]],
			subring0, subring1, inside0, inside1 Fact,
		) {
			firstJ, secondJ := a.TermAs[Set[A]]("fst(J)"), a.TermAs[Set[A]]("snd(J)")
			both := a.Have(
				"one lies in the inverse of each chart",
				"L.one ∈ fractional_inverse(field_ring(L), A₀, fst(J)) ∧ "+
					"L.one ∈ fractional_inverse(field_ring(L), A₁, snd(J))",
				By(
					L,
					subring0,
					subring1,
					inside0,
					inside1,
					fractional_ideal.FractionalInverseHoldsOne.Read(L).At(A0, firstJ),
					fractional_ideal.FractionalInverseHoldsOne.Read(L).At(A1, secondJ)))
			a.Do(Simp(
				Fwd(lattice_pair.LatticePairH0Def),
				Fwd(LatticePairInverseDef),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd)))
			a.Show(
				"so it is a section of the inverse",
				BySets(both))
		}),
})}
