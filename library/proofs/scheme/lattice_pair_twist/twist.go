// twist.go — twisting at a point. M(P) is M multiplied by the inverse of
// an invertible ideal pair P, the sections allowed a simple pole at P when
// P is a point. The algebra of twisting is the product's; at a regular
// point each chart and the overlap gain the point's colength, so the Euler
// characteristic rises by one and the sections by at most one.
//
// The statements stand in a field L holding the biaffine datum, as those
// of invertible_lattice_pair do, and spell its wb… abbreviations.

package lattice_pair_twist

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The algebra of twisting
// ---------------------------------------------------------------------------

// TwistIsLattice — twisting a lattice pair by an invertible ideal pair gives a
// lattice pair. M(P) is P⁻¹ · M; P⁻¹ is invertible
// (invertible_lattice_pair.InvertibleLatticeInverse), so a lattice pair, and a
// product of lattice pairs is one (invertible_lattice_pair.MulIsLattice).
var TwistIsLattice = twistIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "TwistIsLattice",
	Key:  "prop_36f49ee3c62a6a90",
	Reading: "P need only be invertible, which a regular point's ideal " +
		"pair is by its definition (BiaffineRegularPointDef); M need not be.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
			"«wbInvertible»(P)",
		},
		Conclusion: "«wbPair»(«wbTwist»(M, P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the two charts form the biaffine datum",
				"M is a lattice pair in L",
				"P is invertible")
			overlapInL, datum, pairM, invertibleP := parts[0], parts[1], parts[2], parts[3]
			inverseP := a.TermAs[Prod[Set[A], Set[A]]]("«wbInverse»(P)")
			inverseInvertible := a.Have(
				"the inverse of P is invertible",
				"«wbInvertible»(«wbInverse»(P))",
				By(
					overlapInL,
					datum,
					invertibleP,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P)))
			inverseCharts := a.Conjuncts(
				a.Unfolded(inverseInvertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"the first chart of P⁻¹ is an invertible fractional ideal of A₀",
				"its second chart one of A₁",
				"and P⁻¹ is a lattice pair over the overlap")
			productPair := a.Have(
				"multiplying the inverse of P by M gives a lattice pair",
				"«wbPair»(«wbMul»(«wbInverse»(P), M))",
				By(
					overlapInL,
					datum,
					inverseCharts[2],
					pairM,
					invertible_lattice_pair.MulIsLattice.Read(L).At(A0, A1, A01, t, inverseP, M)))
			a.Show(
				"this product is the twist M(P)",
				Simp(Fwd(LatticePairTwistDef)),
				By(productPair))
		}),
})}

// TwistInvertible — twisting an invertible pair by an invertible ideal pair
// gives an invertible pair. M(P) is P⁻¹ · M, a product of two invertible pairs
// (invertible_lattice_pair.InvertibleLatticeInverse,
// invertible_lattice_pair.InvertibleLatticeProduct).
var TwistInvertible = twistInvertibleThm{family.Add(registry.ProofEntry{
	Name: "TwistInvertible",
	Key:  "prop_b5a35333939ff260",
	Reading: "P need only be invertible, which a regular point's " +
		"ideal pair is by its definition (BiaffineRegularPointDef).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbInvertible»(M)",
			"«wbInvertible»(P)",
		},
		Conclusion: "«wbInvertible»(«wbTwist»(M, P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the two charts form the biaffine datum",
				"M is invertible",
				"P is invertible")
			overlapInL, datum, invertibleM, invertibleP := parts[0], parts[1], parts[2], parts[3]
			inverseP := a.TermAs[Prod[Set[A], Set[A]]]("«wbInverse»(P)")
			inverseInvertible := a.Have(
				"the inverse of P is invertible",
				"«wbInvertible»(«wbInverse»(P))",
				By(
					overlapInL,
					datum,
					invertibleP,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P)))
			productInvertible := a.Have(
				"multiplying the inverse of P by M gives an invertible pair",
				"«wbInvertible»(«wbMul»(«wbInverse»(P), M))",
				By(
					overlapInL,
					datum,
					inverseInvertible,
					invertibleM,
					invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, inverseP, M)))
			a.Show(
				"this product is the twist M(P)",
				Simp(Fwd(LatticePairTwistDef)),
				By(productInvertible))
		}),
})}

// TwistCommute — twists at two ideal pairs commute: M(P)(Q) = M(Q)(P).
var TwistCommute = twistCommuteThm{family.Add(registry.ProofEntry{
	Name: "TwistCommute",
	Key:  "prop_1254cc35000fe1f0",
	Reading: "P and Q need only be invertible, so that their inverses " +
		"are lattice pairs and the product's associativity applies.",
	Deps: []registry.EntryLike{
		LatticePairTwistDef,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticePairDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
			"«wbInvertible»(P)",
			"«wbInvertible»(Q)",
		},
		Conclusion: "«wbTwist»(«wbTwist»(M, P), Q) = «wbTwist»(«wbTwist»(M, Q), P)",
	},
		"Q⁻¹ · (P⁻¹ · M) = (Q⁻¹ · P⁻¹) · M = (P⁻¹ · Q⁻¹) · M = P⁻¹ · (Q⁻¹ · M) by "+
			"MulAssoc and MulComm, P⁻¹ and Q⁻¹ being lattice pairs (InvertibleLatticeInverse)"),
})}

// TwistInverseTwist — twisting at P and multiplying by P undo each
// other: M(P) · P = M and (M · P)(P) = M.
var TwistInverseTwist = twistInverseTwistThm{family.Add(registry.ProofEntry{
	Name:    "TwistInverseTwist",
	Key:     "prop_392d8836e72caf8a",
	Reading: "P need only be invertible; M need only be a lattice pair, which (A₀, A₁) · M = M asks.",
	Deps: []registry.EntryLike{
		LatticePairTwistDef,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticePairDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"«wbPair»(M)",
			"«wbInvertible»(P)",
		},
		Conclusion: "«wbMul»(«wbTwist»(M, P), P) = M ∧ «wbTwist»(«wbMul»(M, P), P) = M",
	},
		"(P⁻¹ · M) · P = (P · P⁻¹) · M and P⁻¹ · (M · P) = (P · P⁻¹) · M by MulAssoc "+
			"and MulComm; P · P⁻¹ = (A₀, A₁) (InvertibleLatticeInverse) and MulOne"),
})}

// ---------------------------------------------------------------------------
// Twisting at a regular point
// ---------------------------------------------------------------------------

// RationalPointColengthsInField — the colengths of a rational point, read in
// the field: over a subfield k inside both charts, a chart modulo the point's
// ideal, a quotient of the field's regular module restricted to the chart, has
// dimension one where the point lies on that chart and zero where it does not,
// and the overlap modulo the ideal the point generates has dimension one
// exactly where the point lies on both. This is
// biaffine_rational_point.RationalPointColengths at the overlap's ring, under
// whose operations k is a field (field.SubfieldRingSubfield): the overlap's
// regular module restricted to a set, and its ring restricted to k, are the
// field's.
var RationalPointColengthsInField = rationalPointColengthsInFieldThm{family.Add(registry.ProofEntry{
	Name: "RationalPointColengthsInField",
	Key:  "prop_912f2157a378c08b",
	Reading: "A₀₁ need not lie in L: the overlap's ring, its regular module " +
		"and their restrictions keep L's operations whatever their carrier.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(«wbRing»(A₀₁), A₀, A₁, t, L.inv(t))",
			"subfield(L, k)",
			"k ⊆ A₀ ∩ A₁",
			"biaffine_rational_point(«wbRing»(A₀₁), k, A₀, A₁, P)",
		},
		Conclusion: "finite_dimensional(«wbRing»(k), «pointQ₀») ∧ " +
			"finite_dimensional(«wbRing»(k), «pointQ₁») ∧ " +
			"finite_dimensional(«wbRing»(k), «pointQ₀₁») ∧ " +
			"module_dim(«wbRing»(k), «pointQ₀») = COND(fst(P) = A₀, 0, 1) ∧ " +
			"module_dim(«wbRing»(k), «pointQ₁») = COND(snd(P) = A₁, 0, 1) ∧ " +
			"module_dim(«wbRing»(k), «pointQ₀₁») = COND(fst(P) ≠ A₀ ∧ snd(P) ≠ A₁, 1, 0)",
		Abbrev: Abbrev{
			{Name: "pointQ₀", Text: "quotient_module(«wbVectors»(A₀), fst(P))"},
			{Name: "pointQ₁", Text: "quotient_module(«wbVectors»(A₁), snd(P))"},
			{Name: "pointQ₀₁", Text: "quotient_module(«wbVectors»(A₀₁), ideal_span(«wbRing»(A₀₁), fst(P)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"A₀ and A₁ are the overlap's charts at t and inv(t)",
				"k is a subfield of L",
				"inside both charts",
				"and P is a rational point over k")
			datum, subfield, kInCharts, rational := parts[0], parts[1], parts[2], parts[3]
			fieldOps, overlapOps := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			kIn := a.Have(
				"k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			// The overlap's regular module, restricted to a set, is the field's.
			overlapModules := a.Have(
				"the overlap's regular module restricted to a set is the field's",
				"∀S:set(A). restrict_module(regular_module(«wbRing»(A₀₁)), S) = «wbVectors»(S)",
				Simp(
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RegularModuleDef),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
			overlapCarrier := a.Have(
				"the overlap's ring has carrier A₀₁",
				"«wbRing»(A₀₁).carrier = A₀₁",
				Simp(Fwd(module_record.RestrictRingDef)),
				Basic())
			a.Show(
				"the colengths of the rational point over the overlap's ring, read in the field",
				By(
					datum,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					kIn,
					rational,
					module_record.RestrictRingTwice.At(fieldOps, A01, k),
					overlapCarrier,
					overlapModules.At(A0),
					overlapModules.At(A1),
					overlapModules.At(A01),
					biaffine_rational_point.RationalPointColengths.At(
						overlapOps, A0, A1, t, a.TermAs[A]("L.inv(t)"), k, inverse, P)))
		}),
})}

// TwistQuotientDim — twisting an invertible pair M at a regular point P
// enlarges each chart and the ambient, and each quotient of the twisted one by
// M's is finite over k, of the dimension of the point's quotient in that ring:
// chart 0 modulo fst(P), chart 1 modulo snd(P), the overlap modulo the ideal
// fst(P) generates. On each chart and on the overlap this is
// InvertibleColengthQuotient, read at the twist: a chart of M(P) is the inverse
// of the point's chart times that chart of M; on the overlap ambient(M(P)) =
// ambient(P)⁻¹ · ambient(M) (invertible_lattice_pair.AmbientOfMul,
// invertible_lattice_pair.AmbientInvertible); and ambient(P) = ideal_span(A₀₁,
// fst(P)), fst(P) lying in A₀₁.
var TwistQuotientDim = twistQuotientDimThm{family.Add(registry.ProofEntry{
	Name: "TwistQuotientDim",
	Key:  "prop_bc881ed329d4829c",
	Reading: "M must be invertible: twisting ({zero}, {zero}) leaves it unchanged, and " +
		"the quotients are then zero whatever the point. Where the point lies off chart 0, " +
		"fst(P) = A₀ and the first quotient is zero on both sides. The dimensions on the " +
		"right are the point's colengths, one on a ring the point lies on and zero off it " +
		"(RationalPointColengthsInField); the statement leaves them as dimensions.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"subfield(L, k)",
			"k ⊆ A₀ ∩ A₁",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "fst(M) ⊆ fst(«twisted») ∧ " +
			"snd(M) ⊆ snd(«twisted») ∧ " +
			"«wbAmbient»(M) ⊆ «wbAmbient»(«twisted») ∧ " +
			"finite_dimensional(«wbRing»(k), «twistQ₀») ∧ " +
			"module_dim(«wbRing»(k), «twistQ₀») = module_dim(«wbRing»(k), «pointQ₀») ∧ " +
			"finite_dimensional(«wbRing»(k), «twistQ₁») ∧ " +
			"module_dim(«wbRing»(k), «twistQ₁») = module_dim(«wbRing»(k), «pointQ₁») ∧ " +
			"finite_dimensional(«wbRing»(k), «twistQ₀₁») ∧ " +
			"module_dim(«wbRing»(k), «twistQ₀₁») = module_dim(«wbRing»(k), «pointQ₀₁»)",
		Abbrev: Abbrev{
			{Name: "twisted", Text: "«wbTwist»(M, P)"},
			{Name: "inverseP", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁, P)"},
			{Name: "pointIdeal", Text: "ideal_span(«wbRing»(A₀₁), fst(P))"},
			{Name: "pointQ₀", Text: "quotient_module(«wbVectors»(A₀), fst(P))"},
			{Name: "pointQ₁", Text: "quotient_module(«wbVectors»(A₁), snd(P))"},
			{Name: "pointQ₀₁", Text: "quotient_module(«wbVectors»(A₀₁), «pointIdeal»)"},
			{Name: "twistQ₀", Text: "quotient_module(«wbVectors»(fst(«twisted»)), fst(M))"},
			{Name: "twistQ₁", Text: "quotient_module(«wbVectors»(snd(«twisted»)), snd(M))"},
			{Name: "twistQ₀₁", Text: "quotient_module(«wbVectors»(«wbAmbient»(«twisted»)), «wbAmbient»(M))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"with the two charts as a biaffine datum",
				"k is a subfield",
				"inside both charts",
				"M is invertible",
				"P is a regular point")
			datum, subfieldK, kInCharts, invertibleM, regularP :=
				parts[1], parts[2], parts[3], parts[4], parts[5]
			point := a.Conjuncts(
				a.Unfolded(regularP, BiaffineRegularPointDef),
				"P is rational over k",
				"and its ideal pair is invertible")
			rational, invertibleP := point[0], point[1]
			mCharts := a.Conjuncts(
				a.Unfolded(invertibleM, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"and M is a lattice pair over the overlap")
			pCharts := a.Conjuncts(
				a.Unfolded(invertibleP, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(P) is an invertible fractional ideal of A₀",
				"snd(P) is one of A₁",
				"and P is a lattice pair over the overlap")
			rings := a.Conjuncts(
				GroupPremises(
					parts[0], parts[1], invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"and so is chart 1")
			inOverlap0, overlapSubring, subring0, subring1 := rings[0], rings[2], rings[3], rings[4]
			scalars := a.Have(
				"k lies in both charts and in the overlap",
				"k ⊆ A₀ ∧ k ⊆ A₁ ∧ k ⊆ A₀₁",
				BySets(kInCharts, inOverlap0))
			fieldOps := a.TermAs[RingOps[A]]("field_ring(L)")
			ringStructures := a.Have(
				"the chart rings and the overlap's are rings under L's operations",
				"comm_ring_on(«wbRing»(A₀)) ∧ comm_ring_on(«wbRing»(A₁)) ∧ comm_ring_on(«wbRing»(A₀₁))",
				By(
					subring0,
					subring1,
					overlapSubring,
					field.RingOn.Read(L),
					comm_ring.SubringRingOn.At(fieldOps, A0),
					comm_ring.SubringRingOn.At(fieldOps, A1),
					comm_ring.SubringRingOn.At(fieldOps, A01)))
			restrictionRings := a.Have(
				"restricting through the overlap gives the same chart rings",
				"restrict_ring(«wbRing»(A₀₁), A₀) = «wbRing»(A₀) ∧ restrict_ring(«wbRing»(A₀₁), A₁) = «wbRing»(A₁)",
				By(
					module_record.RestrictRingTwice.At(fieldOps, A01, A0),
					module_record.RestrictRingTwice.At(fieldOps, A01, A1)))
			overlapOps := a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			chart0Ops := a.TermAs[RingOps[A]]("«wbRing»(A₀)")
			// The regular point supplies chart ideals and finite residue quotients.
			pointIdeals := a.Have(
				"fst(P) and snd(P) are ideals of their charts, the whole chart where P lies off it",
				"ring_ideal(«wbRing»(A₀), fst(P)) ∧ ring_ideal(«wbRing»(A₁), snd(P))",
				By(
					Normalized,
					datum,
					rational,
					restrictionRings,
					biaffine_rational_point.RationalPointChartIdeals.At(
						overlapOps, A0, A1, t, a.TermAs[A]("L.inv(t)"), k, P)))
			pointColengths := a.Have(
				"P has finite colength on both charts and on the overlap",
				"finite_dimensional(«wbRing»(k), «pointQ₀») ∧ "+
					"finite_dimensional(«wbRing»(k), «pointQ₁») ∧ "+
					"finite_dimensional(«wbRing»(k), «pointQ₀₁»)",
				By(
					datum,
					subfieldK,
					kInCharts,
					rational,
					RationalPointColengthsInField.Read(L).At(k, A0, A1, A01, t, P)))
			overlapCarrier := a.Have(
				"the overlap's ring has carrier A₀₁",
				"«wbRing»(A₀₁).carrier = A₀₁",
				Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
				Basic())

			// On each chart, InvertibleColengthQuotient read at the twist.
			twistCharts := a.Have(
				"each chart of M(P) is that chart of P inverted times that chart of M",
				"fst(«twisted») = "+
					"fractional_mul(field_ring(L), A₀, fractional_inverse(field_ring(L), A₀, fst(P)), fst(M)) ∧ "+
					"snd(«twisted») = "+
					"fractional_mul(field_ring(L), A₁, fractional_inverse(field_ring(L), A₁, snd(P)), snd(M))",
				Simp(
					Fwd(LatticePairTwistDef),
					Fwd(invertible_lattice_pair.LatticePairMulDef),
					Fwd(invertible_lattice_pair.LatticePairInverseDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				Basic())
			firstM, secondM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			firstP, secondP := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			chart0 := a.Have(
				"chart 0 of M lies in that of M(P), the quotient of the dimension of A₀ modulo fst(P)",
				"fst(M) ⊆ fst(«twisted») ∧ "+
					"finite_dimensional(«wbRing»(k), «twistQ₀») ∧ "+
					"module_dim(«wbRing»(k), «twistQ₀») = module_dim(«wbRing»(k), «pointQ₀»)",
				By(
					subfieldK,
					subring0,
					scalars,
					pointIdeals,
					mCharts[0],
					pCharts[0],
					pointColengths,
					twistCharts,
					ideal_colength.InvertibleColengthQuotient.Read(L).At(k, A0, firstM, firstP)))
			chart1 := a.Have(
				"and chart 1 of M lies in that of M(P), the quotient of the dimension of A₁ modulo snd(P)",
				"snd(M) ⊆ snd(«twisted») ∧ "+
					"finite_dimensional(«wbRing»(k), «twistQ₁») ∧ "+
					"module_dim(«wbRing»(k), «twistQ₁») = module_dim(«wbRing»(k), «pointQ₁»)",
				By(
					subfieldK,
					subring1,
					scalars,
					pointIdeals,
					mCharts[1],
					pCharts[1],
					pointColengths,
					twistCharts,
					ideal_colength.InvertibleColengthQuotient.Read(L).At(k, A1, secondM, secondP)))

			// On the overlap, the same read at the ambients, the ambient of P being the ideal fst(P) generates.
			ambientM := a.Have(
				"the ambient of M is an invertible fractional ideal of the overlap, its inverse the ambient of M⁻¹",
				"invertible_fractional(field_ring(L), A₀₁, «wbAmbient»(M)) ∧ "+
					"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(M)) = "+
					"«wbAmbient»(lattice_pair_inverse(field_ring(L), A₀, A₁, M))",
				By(
					overlapSubring,
					inOverlap0,
					subring0,
					mCharts[0],
					invertible_lattice_pair.AmbientInvertible.Read(L).At(A0, A1, A01, M)))
			ambientP := a.Have(
				"and so is the ambient of P, its inverse the ambient of P⁻¹",
				"invertible_fractional(field_ring(L), A₀₁, «wbAmbient»(P)) ∧ "+
					"fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(P)) = «wbAmbient»(«inverseP»)",
				By(
					overlapSubring,
					inOverlap0,
					subring0,
					pCharts[0],
					invertible_lattice_pair.AmbientInvertible.Read(L).At(A0, A1, A01, P)))
			firstCharts := a.Have(
				"fst(P⁻¹) and fst(M) lie in L",
				"fst(«inverseP») ⊆ L.carrier ∧ fst(M) ⊆ L.carrier",
				Simp(Fwd(invertible_lattice_pair.LatticePairInverseDef), Fwd(pairs.Fst)),
				By(
					invertibleM,
					fractional_ideal.FractionalInverseSubset.Read(L).At(A0, firstP),
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M)))
			inverseP := a.TermAs[Prod[Set[A], Set[A]]]("«inverseP»")
			twistAmbient := a.Have(
				"the ambient of M(P) is the inverse of the ambient of P times the ambient of M",
				"«wbAmbient»(«twisted») = "+
					"fractional_mul(field_ring(L), "+
					"    A₀₁, "+
					"    fractional_inverse(field_ring(L), A₀₁, «wbAmbient»(P)), "+
					"    «wbAmbient»(M))",
				By(
					overlapSubring,
					inOverlap0,
					firstCharts,
					ambientP,
					invertible_lattice_pair.AmbientOfMul.Read(L).At(A0, A1, A01, inverseP, M),
					LatticePairTwistDef.At(fieldOps, A0, A1, M, P)))
			pointInChart := a.Have(
				"fst(P) lies in chart 0",
				"fst(P) ⊆ A₀",
				By(
					pointIdeals,
					ring_ideal.IdealSubset.At(chart0Ops, firstP),
					module_record.RestrictRingDef.At(fieldOps, A0),
					module_record.RingCarrierDef))
			pointInOverlap := a.Have(
				"therefore it lies in the overlap",
				"fst(P) ⊆ A₀₁",
				BySets(pointInChart, inOverlap0))
			containerVectors := a.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			pointAmbient := a.Have(
				"the ambient of P is the ideal of the overlap fst(P) generates",
				"«wbAmbient»(P) = «pointIdeal»",
				By(
					overlapSubring,
					pointInOverlap,
					fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(A01, firstP),
					lattice_pair.LatticePairAmbientDef.At(overlapOps, containerVectors, P)))
			overlapIdeal := a.Have(
				"so the ambient of P is an ideal of the overlap",
				"ring_ideal(«wbRing»(A₀₁), «wbAmbient»(P))",
				By(
					ringStructures,
					pointInOverlap,
					overlapCarrier,
					pointAmbient,
					ring_ideal.SpanIdeal.At(overlapOps, firstP)))
			ambientMSet, ambientPSet := a.TermAs[Set[A]]("«wbAmbient»(M)"), a.TermAs[Set[A]]("«wbAmbient»(P)")
			overlapColength := a.Have(
				"the ambient of M lies in that of M(P), the quotient of "+
					"the dimension of A₀₁ modulo the ideal fst(P) generates",
				"«wbAmbient»(M) ⊆ «wbAmbient»(«twisted») ∧ "+
					"finite_dimensional(«wbRing»(k), «twistQ₀₁») ∧ "+
					"module_dim(«wbRing»(k), «twistQ₀₁») = module_dim(«wbRing»(k), «pointQ₀₁»)",
				By(
					subfieldK,
					overlapSubring,
					scalars,
					overlapIdeal,
					ambientM,
					ambientP,
					pointAmbient,
					pointColengths,
					twistAmbient,
					ideal_colength.InvertibleColengthQuotient.Read(L).At(k, A01, ambientMSet, ambientPSet)))
			a.Show(
				"the chart and overlap comparisons give all inclusions and dimensions",
				By(chart0, chart1, overlapColength))
		}),
})}

// TwistEuler — twisting a finite invertible pair at a regular point keeps it
// finite and raises its Euler characteristic by one. M lies in M(P) chart by
// chart, each quotient finite of the point's colength d₀, d₁ or d₀₁
// (TwistQuotientDim), so M(P) is finite with χ(M(P)) − χ(M) = d₀ + d₁ − d₀₁
// (lattice_pair_sequence.EulerAdditive). The colengths are one on a ring the
// point lies on and zero off it (RationalPointColengthsInField), and the point
// lies on at least one chart, so the sum is one in each of the three cases.
var TwistEuler = twistEulerThm{family.Add(registry.ProofEntry{
	Name: "TwistEuler",
	Key:  "prop_97ee2718ee5f422e",
	Reading: "The one is the point's degree: a point on both charts adds 1 + 1 − 1 " +
		"(each chart and the overlap gain one dimension), a point on one chart adds 1 + 0 − " +
		"0. M invertible is load-bearing through TwistQuotientDim; finiteness of M is " +
		"needed for χ(M) to be a determined number. No point lies on neither chart — the " +
		"definition excludes fst(P) = A₀ ∧ snd(P) = A₁ — so d₀ + d₁ = d₀₁ + 1 in every " +
		"case; the Euler difference is taken in int, where its subtraction does not truncate.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"subfield(L, k)",
			"k ⊆ A₀ ∩ A₁",
			"«wbInvertible»(M)",
			"«wbFinite»(M)",
			"«wbPoint»(P)",
		},
		Conclusion: "«wbFinite»(«wbTwist»(M, P)) ∧ «wbEuler»(«wbTwist»(M, P)) = «wbEuler»(M) + &1",
		Abbrev: Abbrev{
			{Name: "wbPoint", Text: "biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁)"},
			{Name: "wbFinite", Text: "lattice_pair_finite(«wbRing»(A₀₁), k, «wbField»)"},
			{Name: "wbEuler", Text: "lattice_pair_euler(«wbRing»(A₀₁), k, «wbField»)"},
			{Name: "pointQ₀", Text: "quotient_module(«wbVectors»(A₀), fst(P))"},
			{Name: "pointQ₁", Text: "quotient_module(«wbVectors»(A₁), snd(P))"},
			{Name: "pointQ₀₁", Text: "quotient_module(«wbVectors»(A₀₁), ideal_span(«wbRing»(A₀₁), fst(P)))"},
			{Name: "twistQ₀", Text: "quotient_module(«wbVectors»(fst(«wbTwist»(M, P))), fst(M))"},
			{Name: "twistQ₁", Text: "quotient_module(«wbVectors»(snd(«wbTwist»(M, P))), snd(M))"},
			{Name: "twistQ₀₁", Text: "quotient_module(«wbVectors»(«wbAmbient»(«wbTwist»(M, P))), " +
				"    «wbAmbient»(M))"},
			{Name: "pointDim₀", Text: "module_dim(«wbRing»(k), «pointQ₀»)"},
			{Name: "pointDim₁", Text: "module_dim(«wbRing»(k), «pointQ₁»)"},
			{Name: "pointDim₀₁", Text: "module_dim(«wbRing»(k), «pointQ₀₁»)"},
			{Name: "twistDim₀", Text: "module_dim(«wbRing»(k), «twistQ₀»)"},
			{Name: "twistDim₁", Text: "module_dim(«wbRing»(k), «twistQ₁»)"},
			{Name: "twistDim₀₁", Text: "module_dim(«wbRing»(k), «twistQ₀₁»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the charts form the biaffine datum",
				"k is a subfield of L",
				"k lies in both charts",
				"M is invertible",
				"M has finite cohomology",
				"P is a regular rational point")
			overlapInL, datum, subfieldK, kInCharts := parts[0], parts[1], parts[2], parts[3]
			invertibleM, finiteM, point := parts[4], parts[5], parts[6]
			pointParts := a.Conjuncts(
				a.Unfolded(point, BiaffineRegularPointDef),
				"P is rational over k",
				"and its ideal pair is invertible")
			rational, invertibleP := pointParts[0], pointParts[1]
			fieldOps := a.TermAs[RingOps[A]]("field_ring(L)")
			overlapOps := a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			twist := a.TermAs[Prod[Set[A], Set[A]]]("«wbTwist»(M, P)")
			invT := a.TermAs[A]("L.inv(t)")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			mCharts := a.Conjuncts(
				a.Unfolded(invertibleM, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"and M is a lattice pair over the overlap")
			pairTwist := a.Have(
				"so is the twist at P",
				"«wbPair»(«wbTwist»(M, P))",
				By(overlapInL, datum, mCharts[2], invertibleP, TwistIsLattice.Read(L).At(A0, A1, A01, t, M, P)))
			kParts := a.Conjuncts(
				a.Have(
					"k lies in each chart",
					"k ⊆ A₀ ∧ k ⊆ A₁",
					BySets(kInCharts)),
				"k lies in chart 0",
				"and in chart 1")
			kIn0, kIn1 := kParts[0], kParts[1]
			twistQuotients := a.Conjuncts(
				GroupPremises(
					parts[0],
					parts[1],
					parts[2],
					parts[3],
					parts[4],
					parts[6],
					TwistQuotientDim.Read(L).At(k, A0, A1, A01, t, M, P)),
				"chart 0 of M lies in the twisted chart",
				"and so does chart 1",
				"the ambient of M lies in the twisted ambient",
				"the chart 0 quotient is finite over k",
				"its dimension is the point's chart 0 colength",
				"the chart 1 quotient is finite over k",
				"its dimension is the point's chart 1 colength",
				"the ambient quotient is finite over k",
				"its dimension is the point's overlap colength")
			inclusion0, inclusion1 := twistQuotients[0], twistQuotients[1]
			finite0, finite1 := twistQuotients[3], twistQuotients[5]
			dimension0, dimension1, dimensionAmbient := twistQuotients[4], twistQuotients[6], twistQuotients[8]
			pointDimensions := a.Conjuncts(
				a.Have(
					"a chart contributes one where P lies on it, and the overlap one where P lies on both",
					"«pointDim₀» = COND(fst(P) = A₀, 0, 1) ∧ "+
						"«pointDim₁» = COND(snd(P) = A₁, 0, 1) ∧ "+
						"«pointDim₀₁» = COND(fst(P) ≠ A₀ ∧ snd(P) ≠ A₁, 1, 0)",
					By(
						datum,
						subfieldK,
						kInCharts,
						rational,
						RationalPointColengthsInField.Read(L).At(k, A0, A1, A01, t, P))),
				"the point's chart 0 colength",
				"its chart 1 colength",
				"and its overlap colength")
			euler := a.Conjuncts(
				a.Have(
					"the finite subpair formula gives finiteness and the signed Euler difference",
					"«wbFinite»(«wbTwist»(M, P)) ∧ "+
						"«wbEuler»(«wbTwist»(M, P)) - «wbEuler»(M) = &«twistDim₀» + &«twistDim₁» - &«twistDim₀₁»",
					Derive(func(b *Argument) {
						b.Show(
							"apply Euler additivity to M inside its twist",
							By(
								datum,
								subfieldK,
								field.SubfieldRingSubfield.Read(L).At(k, A01),
								kIn0,
								kIn1,
								pairTwist,
								mCharts[2],
								inclusion0,
								inclusion1,
								finite0,
								finite1,
								finiteM,
								module_record.RestrictRingTwice.At(fieldOps, A01, k),
								lattice_pair_sequence.EulerAdditive.At(overlapOps, A0, A1, t, invT, k, inverse, vectors, twist, M)))
					})),
				"the twist has finite cohomology",
				"its Euler difference is the signed sum of relative dimensions")
			notBoth := a.Have(
				"the point lies on at least one chart",
				"¬(fst(P) = A₀ ∧ snd(P) = A₁)",
				By(rational, biaffine_rational_point.BiaffineRationalPointDef.At(overlapOps, k, A0, A1, P)))
			correction := a.Have(
				"the point's two chart colengths add up to its overlap colength and one",
				"«pointDim₀» + «pointDim₁» = «pointDim₀₁» + 1",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"P lies only on chart 1: zero plus one is zero plus one",
						func(c *Argument, off0 Fact) {
							on1 := c.Have(
								"P must lie on chart 1",
								"snd(P) ≠ A₁",
								By(Normalized, notBoth, off0))
							c.Show(
								"the chart 1 colength contributes one",
								ByArith(pointDimensions[0], pointDimensions[1], pointDimensions[2], off0, on1))
						})
					b.Otherwise(
						"P lies on chart 0",
						func(c *Argument, on0 Fact) {
							c.Cases(c.TermAs[Bool]("snd(P) = A₁"))
							c.When(
								"P lies only on chart 0: one plus zero is zero plus one",
								func(d *Argument, off1 Fact) {
									d.Show(
										"the chart 0 colength contributes one",
										ByArith(pointDimensions[0], pointDimensions[1], pointDimensions[2], on0, off1))
								})
							c.Otherwise(
								"P lies on both charts: one plus one is one plus one",
								func(d *Argument, on1 Fact) {
									d.Show(
										"the overlap counts one of the two chart contributions",
										ByArith(pointDimensions[0], pointDimensions[1], pointDimensions[2], on0, on1))
								})
						})
				}))
			eulerRise := a.Have(
				"substitute the three colengths into the signed Euler difference",
				"«wbEuler»(«wbTwist»(M, P)) = «wbEuler»(M) + &1",
				ByArith(euler[1], dimension0, dimension1, dimensionAmbient, correction))
			a.Show(
				"twisting at P keeps finiteness and raises Euler characteristic by one",
				By(euler[0], eulerRise))
		}),
})}

// TwistH0Step — twisting an invertible pair with finite cohomology at a
// regular rational point raises the dimension of its sections by at most
// one: the Euler characteristic rises by exactly one (TwistEuler), and the
// first cohomology can only shrink, since the six-term sequence maps H¹ of
// the pair onto H¹ of its twist.
var TwistH0Step = twistH0StepThm{family.Add(registry.ProofEntry{
	Name: "TwistH0Step",
	Key:  "prop_34fa255c951024f5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wbRing»(A₀₁), A₀, A₁, t, L.inv(t))",
			"subfield(L, k)",
			"k ⊆ A₀ ∩ A₁",
			"«wbInvertible»(M)",
			"«wbFinite»(M)",
			"«wbPoint»(P)",
		},
		Conclusion: "«wbH0Dim»(«wbTwist»(M, P)) ≤ «wbH0Dim»(M) + 1",
		Abbrev: Abbrev{
			{Name: "wbPoint", Text: "biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁)"},
			{Name: "wbFinite", Text: "lattice_pair_finite(«wbRing»(A₀₁), k, «wbField»)"},
			{Name: "wbH0Dim", Text: "lattice_pair_h0_dim(«wbRing»(A₀₁), k, «wbField»)"},
			{Name: "wbH1Dim", Text: "lattice_pair_h1_dim(«wbRing»(A₀₁), k, «wbField»)"},
			{Name: "wbH1", Text: "lattice_pair_h1(«wbRing»(A₀₁), «wbField»)"},
			{Name: "toTwist", Text: "λx:set(A). " +
				"    set_mul(«wbField».add, " +
				"        x, " +
				"        set_mul(«wbField».add, fst(«wbTwist»(M, P)), snd(«wbTwist»(M, P))))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the overlap lies in L",
				"the charts form the biaffine datum",
				"k is a subfield of L",
				"k lies in both charts",
				"M is invertible",
				"M has finite cohomology",
				"P is a regular rational point")
			overlapInL, datum, subfieldK, kInCharts := parts[0], parts[1], parts[2], parts[3]
			invertibleM, finiteM, point := parts[4], parts[5], parts[6]
			fieldOps := a.TermAs[RingOps[A]]("field_ring(L)")
			overlapOps := a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			scalars := a.TermAs[RingOps[A]]("restrict_ring(«wbRing»(A₀₁), k)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			twist := a.TermAs[Prod[Set[A], Set[A]]]("«wbTwist»(M, P)")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			euler := a.Conjuncts(
				GroupPremises(
					overlapInL,
					datum,
					subfieldK,
					kInCharts,
					invertibleM,
					finiteM,
					point,
					TwistEuler.Read(L).At(k, A0, A1, A01, t, M, P)),
				"the twist has finite cohomology",
				"and Euler characteristic one more than M's")
			pairs := a.Conjuncts(
				a.Unfolded(invertibleM, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"M is a lattice pair over the overlap")
			pointParts := a.Conjuncts(
				a.Unfolded(point, BiaffineRegularPointDef),
				"P is rational over k",
				"and its ideal pair is invertible")
			kParts := a.Conjuncts(
				a.Have(
					"k lies in each chart",
					"k ⊆ A₀ ∧ k ⊆ A₁",
					BySets(kInCharts)),
				"k lies in chart 0",
				"and in chart 1")
			pairTwist := a.Have(
				"the twist is a lattice pair",
				"«wbPair»(«wbTwist»(M, P))",
				By(overlapInL, datum, pairs[2], pointParts[1], TwistIsLattice.Read(L).At(A0, A1, A01, t, M, P)))
			quotients := a.Conjuncts(
				GroupPremises(
					overlapInL,
					datum,
					subfieldK,
					kInCharts,
					invertibleM,
					point,
					TwistQuotientDim.Read(L).At(k, A0, A1, A01, t, M, P)),
				"chart 0 of M lies in the twisted chart",
				"and so does chart 1",
				"the ambient of M lies in the twisted ambient",
				"the chart 0 quotient is finite over k",
				"its dimension is the point's chart 0 colength",
				"the chart 1 quotient is finite over k",
				"its dimension is the point's chart 1 colength",
				"the ambient quotient is finite over k",
				"its dimension is the point's overlap colength")
			finiteQuotients := a.Have(
				"the two chart quotients are finite over k, read on the overlap",
				"finite_dimensional(restrict_ring(«wbRing»(A₀₁), k), "+
					"    quotient_module(restrict_module(«wbField», fst(«wbTwist»(M, P))), fst(M))) ∧ "+
					"finite_dimensional(restrict_ring(«wbRing»(A₀₁), k), "+
					"    quotient_module(restrict_module(«wbField», snd(«wbTwist»(M, P))), snd(M)))",
				By(quotients[3], quotients[5], module_record.RestrictRingTwice.At(fieldOps, A01, k)))
			overlapField := a.Have(
				"k is a field of scalars of the overlap",
				"ring_subfield(«wbRing»(A₀₁), L.inv, k)",
				By(subfieldK, field.SubfieldRingSubfield.Read(L).At(k, A01)))
			sequence := a.Conjuncts(
				GroupPremises(
					datum,
					overlapField,
					kParts[0],
					kParts[1],
					pairTwist,
					pairs[2],
					quotients[0],
					quotients[1],
					finiteQuotients,
					lattice_pair_sequence.SixTermSequence.At(
						overlapOps, A0, A1, t, a.TermAs[A]("L.inv(t)"), k, inverse, vectors, twist, M)),
				"H⁰ of the twist maps to the quotient kernel",
				"the connecting map is linear",
				"H¹ of M maps to H¹ of the twist",
				"the quotient kernel is finite over k",
				"H⁰ of M is the kernel of the first map",
				"the connecting map's kernel is the image of H⁰",
				"the third map's kernel is the image of the connecting map",
				"the third map is onto")
			scalarField := a.Have(
				"k is a field of scalars on the overlap's restriction to k",
				"ring_subfield(restrict_ring(«wbRing»(A₀₁), k), L.inv, k)",
				By(
					Normalized,
					subfieldK,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					module_record.RestrictRingTwice.At(fieldOps, A01, k)))
			h1Finite := a.Conjuncts(
				a.Unfolded(finiteM, lattice_pair.LatticePairFiniteDef),
				"H⁰ of M is finite over k",
				"H¹ of M is finite over k")
			image := a.Have(
				"the image of H¹ of M has dimension at most that of H¹ of M",
				"module_dim(restrict_ring(«wbRing»(A₀₁), k), "+
					"    restrict_module(«wbH1»(«wbTwist»(M, P)), image(«toTwist», «wbH1»(M).carrier))) ≤ "+
					"module_dim(restrict_ring(«wbRing»(A₀₁), k), «wbH1»(M))",
				By(
					h1Finite[1],
					scalarField,
					sequence[2],
					module_dimension.ImageDim.At(
						scalars,
						inverse,
						a.TermAs[module_record.ModuleOps[A, Set[A]]]("«wbH1»(M)"),
						a.TermAs[module_record.ModuleOps[A, Set[A]]]("«wbH1»(«wbTwist»(M, P))"),
						a.TermAs[Fun[Set[A], Set[A]]]("«toTwist»"))))
			h1Bound := a.Have(
				"so H¹ can only shrink under the twist",
				"«wbH1Dim»(«wbTwist»(M, P)) ≤ «wbH1Dim»(M)",
				By(
					a.Simplified(image, Fwd(sequence[7])),
					lattice_pair.LatticePairH1DimDef.At(overlapOps, k, vectors, M),
					lattice_pair.LatticePairH1DimDef.At(overlapOps, k, vectors, twist)))
			h0Twist := a.TermAs[Nat]("«wbH0Dim»(«wbTwist»(M, P))")
			h0M := a.TermAs[Nat]("«wbH0Dim»(M)")
			integral := a.Have(
				"the Euler characteristic rises by one while H¹ does not grow",
				"int_of_num(«wbH0Dim»(«wbTwist»(M, P))) ≤ int_of_num(«wbH0Dim»(M)) + 1",
				ByArith(
					h1Bound,
					euler[1],
					lattice_pair.LatticePairEulerDef.At(overlapOps, k, vectors, M),
					lattice_pair.LatticePairEulerDef.At(overlapOps, k, vectors, twist)))
			a.Show(
				"read in num",
				By(
					integral,
					int_embed.OfNumLe.At(h0Twist, a.TermAs[Nat]("«wbH0Dim»(M) + 1")),
					int_embed.OfNumAdd.At(h0M, a.TermAs[Nat]("1"))))
		}),
})}

// PairBelowContraction — a lattice pair under the first component of P lies under
// the second, where that component is chart 1 inside the ideal the first generates
// on the overlap: the pair's two components span one module of the overlap, so its
// second component lies in the span of its first, inside the span of fst(P), which
// is that ideal.
var PairBelowContraction = pairBelowContractionThm{family.Add(registry.ProofEntry{
	Name: "PairBelowContraction",
	Key:  "prop_8e7374212bedcf6a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀J P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀₁)",
			"«wbPair»(J)",
			"snd(J) ⊆ A₁",
			"fst(P) ⊆ A₀₁",
			"snd(P) = A₁ ∩ ideal_span(«wbRing»(A₀₁), fst(P))",
			"fst(J) ⊆ fst(P)",
		},
		Conclusion: "snd(J) ⊆ snd(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			J, P *Expr[Prod[Set[A], Set[A]]],
			subring, pair, inChart, inOverlap, contraction, below Fact,
		) {
			overlap := a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wbField»")
			firstJ, secondJ := a.TermAs[Set[A]]("fst(J)"), a.TermAs[Set[A]]("snd(J)")
			firstP := a.TermAs[Set[A]]("fst(P)")
			spans := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"the field is a module over the overlap",
				"fst(J) is a module over chart 0",
				"snd(J) is a module over chart 1",
				"they span one module of the overlap")[3]
			extended := a.Have(
				"inside the overlap the span of fst(P) is the ideal it generates",
				"«wbSpan»(fst(P)) = ideal_span(«wbRing»(A₀₁), fst(P))",
				By(subring, inOverlap, fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(A01, firstP)))
			a.Show(
				"snd(J) lies in its span, which is the span of fst(J), inside that of fst(P)",
				BySets(
					contraction,
					inChart,
					extended,
					spans,
					below,
					submodule.SubsetSpan.At(overlap, vectors, secondJ),
					submodule.SpanMono.At(overlap, vectors, firstJ, firstP)))
		}),
})}

// TwistInsidePoints — an invertible pair J inside a regular point P of a biaffine datum
// in L: its twist at P lies in the structure pair, and in every other regular point J
// lies inside. Each chart of the twist is P⁻¹J on that chart, which
// invertible_fractional_ideal.InverseMulInside places in the chart, and in another point's ideal
// where that is proper: it is prime there, and does not hold P's ideal by
// biaffine_rational_point.RationalPointsSeparate.
var TwistInsidePoints = twistInsidePointsThm{family.Add(registry.ProofEntry{
	Name: "TwistInsidePoints",
	Key:  "prop_34eab3f62a500e2c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀J P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
			"subfield(L, k)",
			"k ⊆ A₀ ∩ A₁",
			"«wbInvertible»(J)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
			"fst(J) ⊆ fst(P)",
			"snd(J) ⊆ snd(P)",
		},
		Conclusion: "fst(«twisted») ⊆ A₀ ∧ " +
			"snd(«twisted») ⊆ A₁ ∧ " +
			"(∀Q:prod(set(A), set(A)). " +
			"    biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, Q) ∧ " +
			"    Q ≠ P ∧ " +
			"    fst(J) ⊆ fst(Q) ∧ " +
			"    snd(J) ⊆ snd(Q) ⇒ " +
			"    fst(«twisted») ⊆ fst(Q) ∧ snd(«twisted») ⊆ snd(Q))",
		Abbrev: Abbrev{
			{Name: "twisted", Text: "«wbTwist»(J, P)"},
			{Name: "divided₀", Text: "fractional_mul(field_ring(L), " +
				"    A₀, " +
				"    fractional_inverse(field_ring(L), A₀, fst(P)), " +
				"    fst(J))"},
			{Name: "divided₁", Text: "fractional_mul(field_ring(L), " +
				"    A₁, " +
				"    fractional_inverse(field_ring(L), A₁, snd(P)), " +
				"    snd(J))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			J, P *Expr[Prod[Set[A], Set[A]]],
			overlapInField, biaffine, subfieldK, constantsInCharts, invertibleJ, point, insideFirst, insideSecond Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("«wbRing»(A₀₁)")
			chart0 := a.TermAs[RingOps[A]]("«wbRing»(A₀)")
			chart1 := a.TermAs[RingOps[A]]("«wbRing»(A₁)")
			inverseT := a.TermAs[A]("L.inv(t)")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			firstJ, secondJ := a.TermAs[Set[A]]("fst(J)"), a.TermAs[Set[A]]("snd(J)")
			firstP, secondP := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			charts := a.Have(
				"the charts are subrings of L",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(overlapInField, biaffine, invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)))
			constants := a.Have(
				"the constants are a field under the overlap's operations, inside both charts",
				"ring_subfield(«wbRing»(A₀₁), L.inv, k) ∧ k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(subfieldK, constantsInCharts, field.SubfieldRingSubfield.Read(L).At(k, A01)))
			invertiblesJ := a.Have(
				"each chart of J is invertible",
				"invertible_fractional(field_ring(L), A₀, fst(J)) ∧ "+
					"invertible_fractional(field_ring(L), A₁, snd(J))",
				By(invertibleJ, invertible_lattice_pair.InvertibleLatticePairDef.At(ring, A0, A1, A01, J)))
			clausesP := a.Have(
				"P is a rational point with invertible charts",
				"biaffine_rational_point(«wbRing»(A₀₁), k, A₀, A₁, P) ∧ "+
					"invertible_fractional(field_ring(L), A₀, fst(P)) ∧ "+
					"invertible_fractional(field_ring(L), A₁, snd(P))",
				By(
					point,
					BiaffineRegularPointDef.At(ring, k, A0, A1, A01, P),
					invertible_lattice_pair.InvertibleLatticePairDef.At(ring, A0, A1, A01, P)))
			inCharts := a.Have(
				"P lies in the structure pair",
				"fst(P) ⊆ A₀ ∧ snd(P) ⊆ A₁",
				By(
					biaffine,
					clausesP,
					biaffine_rational_point.PointIdealLattice.At(overlap, A0, A1, t, inverseT, k, P)))
			modules := a.Have(
				"each chart of J is a module over its chart ring",
				"submodule(«wbRing»(A₀), «wbField», fst(J)) ∧ submodule(«wbRing»(A₁), «wbField», snd(J))",
				By(
					invertiblesJ,
					fractional_ideal.InvertibleFractionalDef.At(ring, A0, firstJ),
					fractional_ideal.InvertibleFractionalDef.At(ring, A1, secondJ)))
			components := a.Have(
				"each chart of the twist is P⁻¹J on that chart",
				"fst(«twisted») = «divided₀» ∧ snd(«twisted») = «divided₁»",
				Simp(
					Fwd(LatticePairTwistDef),
					Fwd(invertible_lattice_pair.LatticePairMulDef),
					Fwd(invertible_lattice_pair.LatticePairInverseDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				Basic())
			onFirst := a.Conjuncts(
				a.Have(
					"on chart 0 the quotient lies in the chart, and in a prime holding fst(J) and not fst(P)",
					"«divided₀» ⊆ A₀ ∧ "+
						"(∀Z:set(A). prime_ideal(«wbRing»(A₀), Z) ∧ fst(J) ⊆ Z ∧ ¬(fst(P) ⊆ Z) ⇒ «divided₀» ⊆ Z)",
					By(
						L,
						charts,
						clausesP,
						inCharts,
						modules,
						insideFirst,
						invertible_fractional_ideal.InverseMulInside.Read(L).At(A0, firstP, firstJ))),
				"on chart 0 the quotient lies in the chart",
				"and in a prime holding fst(J) and not fst(P)")
			onSecond := a.Conjuncts(
				a.Have(
					"on chart 1 the quotient lies in the chart, and in a prime holding snd(J) and not snd(P)",
					"«divided₁» ⊆ A₁ ∧ "+
						"(∀Z:set(A). prime_ideal(«wbRing»(A₁), Z) ∧ snd(J) ⊆ Z ∧ ¬(snd(P) ⊆ Z) ⇒ «divided₁» ⊆ Z)",
					By(
						L,
						charts,
						clausesP,
						inCharts,
						modules,
						insideSecond,
						invertible_fractional_ideal.InverseMulInside.Read(L).At(A1, secondP, secondJ))),
				"on chart 1 the quotient lies in the chart",
				"and in a prime holding snd(J) and not snd(P)")
			others := a.Have(
				"the twist lies in every other point J lies inside",
				Statement{
					Binders: "∀Q:prod(set(A), set(A)).",
					Hypotheses: []string{
						"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, Q)",
						"Q ≠ P",
						"fst(J) ⊆ fst(Q)",
						"snd(J) ⊆ snd(Q)",
					},
					Conclusion: "fst(«twisted») ⊆ fst(Q) ∧ snd(«twisted») ⊆ snd(Q)",
				},
				Derive(func(b *Argument) {
					Q := b.FixAs[Prod[Set[A], Set[A]]]("Q")
					assumed := b.Conjuncts(
						b.Assume(),
						"Q is a regular point",
						"another point",
						"holding fst(J)",
						"and snd(J)")
					pointQ, distinct, holdsFirst, holdsSecond := assumed[0], assumed[1], assumed[2], assumed[3]
					firstQ, secondQ := b.TermAs[Set[A]]("fst(Q)"), b.TermAs[Set[A]]("snd(Q)")
					rationalQ := b.Have(
						"Q is a rational point",
						"biaffine_rational_point(«wbRing»(A₀₁), k, A₀, A₁, Q)",
						By(pointQ, BiaffineRegularPointDef.At(ring, k, A0, A1, A01, Q)))
					separated := b.Have(
						"P's ideal lies in Q's on no chart where Q is proper",
						"(fst(Q) ≠ A₀ ⇒ ¬(fst(P) ⊆ fst(Q))) ∧ (snd(Q) ≠ A₁ ⇒ ¬(snd(P) ⊆ snd(Q)))",
						By(
							distinct,
							biaffine,
							constants,
							clausesP,
							rationalQ,
							biaffine_rational_point.RationalPointsSeparate.At(overlap, A0, A1, t, inverseT, k, inverse, Q, P)))
					maximalQ := b.Have(
						"Q's ideal is maximal on a chart where it is proper",
						"(fst(Q) ≠ A₀ ⇒ maximal_ideal(«wbRing»(A₀), fst(Q))) ∧ "+
							"(snd(Q) ≠ A₁ ⇒ maximal_ideal(«wbRing»(A₁), snd(Q)))",
						By(
							Normalized,
							biaffine,
							constants,
							rationalQ,
							biaffine_rational_point.RationalPointMaximal.At(overlap, A0, A1, t, inverseT, k, inverse, Q),
							module_record.RestrictRingTwice.At(ring, A01, A0),
							module_record.RestrictRingTwice.At(ring, A01, A1)))
					rings := b.Have(
						"the charts are commutative rings",
						"comm_ring_on(«wbRing»(A₀)) ∧ comm_ring_on(«wbRing»(A₁))",
						By(
							charts,
							comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A0),
							comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A1)))
					firstInside := b.Have(
						"chart 0 of the twist lies in Q",
						"«divided₀» ⊆ fst(Q)",
						By(
							holdsFirst,
							separated,
							maximalQ,
							rings,
							onFirst[0],
							onFirst[1].At(firstQ),
							ring_ideal.MaximalIsPrime.At(chart0, firstQ)))
					secondInside := b.Have(
						"chart 1 of the twist lies in Q",
						"«divided₁» ⊆ snd(Q)",
						By(
							holdsSecond,
							separated,
							maximalQ,
							rings,
							onSecond[0],
							onSecond[1].At(secondQ),
							ring_ideal.MaximalIsPrime.At(chart1, secondQ)))
					b.Show(
						"so the twist lies in Q on both charts",
						By(components, firstInside, secondInside))
				}))
			a.Show(
				"the twist lies in the structure pair, and in the other points",
				By(components, onFirst[0], onSecond[0], others))
		}),
})}
