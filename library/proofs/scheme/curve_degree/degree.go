// degree.go — the degree of an invertible pair, deg M = χ(M) − χ(O), and
// what it measures: it is unchanged by scaling and isomorphism, rises by
// one at a twist by a regular point, adds over products, and bounds the
// sections — a nonzero section forces deg M ≥ 0, at degree zero or one
// it pins M down to a multiple of O or of O(P), and in negative degree
// there are none; and χ(M) = deg M + 1 − g. Then the divisors: integer
// multiplicities on finitely many regular points, their pairs O(D) and
// their degrees.

package curve_degree

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"

	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The degree
// ---------------------------------------------------------------------------

// CurveDegreeDef — `curve_degree(L, k, A₀, A₁, A₀₁, M)`, written deg M:
// χ(M) − χ(O), the Euler characteristic of M over k measured from that of
// the structure pair (A₀, A₁), an integer.
var CurveDegreeDef = curveDegreeDefThm{family.Define(registry.DefEntry{
	Name:     "CurveDegreeDef",
	Key:      "prop_d67c9eb36d9fd0d7",
	Const:    "curve_degree",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → int",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "χ is an integer difference of two dimensions, determined only " +
		"where both are finite: for an invertible pair of a curve they are " +
		"(InvertibleFinite), and elsewhere the degree is a number nothing is said about.",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀M:prod(set(A), set(A)). " +
			"    curve_degree(R, k, A₀, A₁, A₀₁, M) = " +
			"    lattice_pair_euler(restrict_ring(R, A₀₁), k, regular_module(R), M) - " +
			"    lattice_pair_euler(restrict_ring(R, A₀₁), k, regular_module(R), (A₀, A₁))",
	},
})}

// DegreeStructure — the structure pair has degree zero: its Euler
// characteristic is subtracted from itself.
var DegreeStructure = degreeStructureThm{family.Add(registry.ProofEntry{
	Name: "DegreeStructure",
	Key:  "prop_d67cf33ae304e72c",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A).",
		Conclusion: "«wdDegree»((A₀, A₁)) = &0",
	}, func(a *Argument) {
		a.Show(
			"the Euler characteristic of the structure pair less itself is zero",
			Unfold(CurveDegreeDef),
			Simp(Fwd(int_real_lift.SubRefl)),
			Basic())
	}),
})}

// DegreeIso — a pair isomorphic to an invertible pair has its degree.
var DegreeIso = degreeIsoThm{family.Add(registry.ProofEntry{
	Name: "DegreeIso",
	Key:  "prop_92b8020a390b7c7a",
	Reading: "Nothing is asked of N beyond the isomorphism: an isomorphism of lattice " +
		"pairs carries the finite cohomology of M to N, dimensions and all " +
		"(IsomorphismSameEuler), so χ(N) = χ(M). M's invertibility is used only to make M " +
		"a lattice pair with finite cohomology (InvertibleLatticePairDef, InvertibleFinite).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)). ∀f:(A → A).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"lattice_pair_isomorphism(«wcOverlap», «wcField», M, «wcField», N, f)",
		},
		Conclusion: "«wdDegree»(N) = «wdDegree»(M)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[_LatticePair],
			f *Arrow[A, A],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"the curve datum",
				"M is invertible",
				"f identifies M with N")
			curve, invertible, isomorphism := parts[0], parts[1], parts[2]
			data := arg.Conjuncts(
				GroupPremises(parts[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			biaffine, subfield, kInCharts := data[1], data[2], data[7]
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
			overlap := arg.TermAs[RingOps[A]]("«wcOverlap»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			inverseT := arg.TermAs[A]("L.inv(t)")
			inv := arg.TermAs[Fun[A, A]]("L.inv")
			kInEachChart := arg.Have(
				"k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			finite := arg.Have(
				"the invertible pair has finite cohomology",
				"lattice_pair_finite(«wcOverlap», k, «wcField», M)",
				By(curve, invertible, algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M)))
			euler := arg.Have(
				"isomorphic pairs have the same Euler characteristic",
				"«wdEuler»(M) = «wdEuler»(N)",
				By(
					biaffine,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					kInEachChart,
					finite,
					invertible,
					invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, M),
					isomorphism,
					lattice_pair_map.IsomorphismSameEuler.At(
						overlap, A0, A1, t, inverseT, k, inv, vectors, vectors, M, N, f)))
			arg.Show(
				"subtract the Euler characteristic of the structure pair",
				Unfold(CurveDegreeDef),
				euler.Rw(),
				Basic())
		}),
})}

// DegreeScale — a nonzero multiple of an invertible pair has its degree.
var DegreeScale = degreeScaleThm{family.Add(registry.ProofEntry{
	Name: "DegreeScale",
	Key:  "prop_24820306f813355e",
	Reading: "a ≠ zero is load-bearing: zero · M = ({zero}, {zero}), whose H¹ " +
		"is zero and H⁰ is {zero}, so χ = 0 and its degree is g − 1 whatever M is.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"a ∈ L.carrier",
			"a ≠ L.zero",
		},
		Conclusion: "«wdDegree»(lattice_pair_scale(a, M)) = «wdDegree»(M)",
		Abbrev: Abbrev{
			{Name: "scaleMap", Text: "λx:A. COND(x ∈ «ambientOnCurve», a * x, L.zero)"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t, a *Expr[A],
		M *Expr[_LatticePair],
		h Fact,
	) {
		hypotheses := arg.Conjuncts(
			h,
			"the curve datum",
			"M is invertible",
			"a lies in L",
			"a is nonzero")
		scalar := arg.MemberOf[on.L](a, hypotheses[2])
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		scaled := arg.TermAs[_LatticePair]("lattice_pair_scale(a, M)")
		multiply := arg.TermAs[Fun[A, A]]("«scaleMap»")
		data := arg.Conjuncts(
			GroupPremises(hypotheses[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
			"the overlap lies in the field",
			"the charts and their overlap are a biaffine datum",
			"k is a subfield",
			"the structure pair is a lattice pair",
			"its ambient is the overlap",
			"the structure pair is invertible",
			"the constants form a field under L's operations",
			"the constants lie in both charts")
		overlapInField, biaffine := data[0], data[1]
		isomorphism := arg.Have(
			"nonzero multiplication identifies M with its multiple",
			"lattice_pair_isomorphism(«wcOverlap», "+
				"    «wcField», "+
				"    M, "+
				"    «wcField», "+
				"    lattice_pair_scale(a, M), "+
				"    «scaleMap»)",
			By(
				overlapInField,
				biaffine,
				hypotheses[3],
				h,
				invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, M),
				invertible_lattice_pair.ScaleIsomorphism.Read(L).At(A0, A1, A01, t, scalar, M)),
		)
		arg.Show(
			"a pair isomorphic to M has its degree",
			By(h, isomorphism, DegreeIso.Read(L).At(k, A0, A1, A01, t, M, scaled, multiply)),
		)
	}),
})}

// DegreeTwist — twisting an invertible pair at a regular point raises its
// degree by one.
var DegreeTwist = degreeTwistThm{family.Add(registry.ProofEntry{
	Name: "DegreeTwist",
	Key:  "prop_5eb495812fbd1135",
	Reading: "The point must be regular: TwistEuler, whose count of the point's colengths " +
		"on the two charts and the overlap raises the Euler characteristic of the finite pair M " +
		"by one, needs the point's ideals invertible. At a cusp the twist is not even invertible.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"«wdPoint»(P)",
		},
		Conclusion: "«wdDegree»(«wdTwist»(M, P)) = «wdDegree»(M) + &1",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, P *Expr[_LatticePair],
			h Fact,
		) {
			data := a.Conjuncts(
				GroupPremises(h, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, subfield, kInCharts := data[0], data[1], data[2], data[7]
			finite := a.Have(
				"an invertible pair has finite cohomology",
				"lattice_pair_finite(«wcOverlap», k, «wcField», M)",
				By(h, algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M)))
			euler := a.Have(
				"twisting at the regular point raises the Euler characteristic by one",
				"«wdEuler»(«wdTwist»(M, P)) = «wdEuler»(M) + &1",
				By(
					overlapInField,
					biaffine,
					subfield,
					kInCharts,
					h,
					finite,
					lattice_pair_twist.TwistEuler.Read(L).At(k, A0, A1, A01, t, M, P)))
			a.Show(
				"subtracting the structure pair's Euler characteristic raises the degree by one",
				Unfold(CurveDegreeDef),
				ByArith(euler))
		}),
})}

// SectionDegreeNonneg — an invertible pair with a nonzero section has
// degree at least zero.
var SectionDegreeNonneg = sectionDegreeNonnegThm{family.Add(registry.ProofEntry{
	Name: "SectionDegreeNonneg",
	Key:  "prop_2de4a7783224e958",
	Reading: "The section a embeds O in M as a · O (SectionInclusion), and deg M = deg(a · O) " +
		"+ d₀ + d₁ − d₀₁ for the three quotients of M by a · O; d₀₁ ≤ d₀ (QuotientDimLocalizes), " +
		"so deg M ≥ d₁ ≥ 0. a ≠ zero is load-bearing: zero is a section of every pair.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"a ∈ lattice_pair_h0(«wcField», M).carrier",
			"a ≠ L.zero",
		},
		Conclusion: "&0 ≤ «wdDegree»(M)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, a *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
			overlap := arg.TermAs[RingOps[A]]("«wcOverlap»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			chartZeroScalars := arg.TermAs[RingOps[A]]("restrict_ring(«wcOverlap», A₀)")
			structure := arg.TermAs[_LatticePair]("(A₀, A₁)")
			scaled := arg.TermAs[_LatticePair]("lattice_pair_scale(a, (A₀, A₁))")
			M0 := arg.TermAs[Set[A]]("fst(M)")
			scaled0 := arg.TermAs[Set[A]]("fst(lattice_pair_scale(a, (A₀, A₁)))")
			inverseT := arg.TermAs[A]("L.inv(t)")
			inv := arg.TermAs[Fun[A, A]]("L.inv")
			data := arg.Conjuncts(
				GroupPremises(given, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, subfield, structureInvertible, kInCharts :=
				data[0], data[1], data[2], data[5], data[7]
			subfieldK := arg.Have(
				"k, a subfield of L, is a field under the overlap's operations",
				"ring_subfield(«wcOverlap», L.inv, k)",
				By(subfield, field.SubfieldRingSubfield.Read(L).At(k, A01)))
			pair := arg.Have(
				"M is a lattice pair",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
				By(given, invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, M)))
			pairData := arg.Unfolded(pair, lattice_pair.LatticePairDef)
			inField := arg.Have(
				"the section lies in L",
				"a ∈ L.carrier",
				BySets(
					pairData,
					given,
					lattice_pair.LatticePairH0Def.At(vectors, M),
					submodule.SubmoduleSubset.At(chartZeroScalars, vectors, M0)))
			section := arg.MemberOf[on.L](a, inField)
			sectionOnCharts := arg.Have(
				"a is a section on both charts",
				"a ∈ fst(M) ∩ snd(M)",
				By(
					given,
					lattice_pair.LatticePairH0Def.At(vectors, M),
					module_record.RestrictModuleDef.At(vectors, arg.TermAs[Set[A]]("fst(M) ∩ snd(M)"))))
			sectionPair := arg.Conjuncts(
				arg.Have(
					"multiplication by the section embeds the structure pair in M as an invertible pair",
					"«wdInvertible»(lattice_pair_scale(a, (A₀, A₁))) ∧ "+
						"image(L.mul(a), A₀) ⊆ fst(M) ∧ "+
						"image(L.mul(a), A₁) ⊆ snd(M)",
					By(
						sectionOnCharts,
						overlapInField,
						biaffine,
						given,
						pair,
						invertible_lattice_pair.SectionInclusion.Read(L).At(A0, A1, A01, t, a, M))),
				"a · O is invertible",
				"a · A₀ lies in fst(M)",
				"a · A₁ lies in snd(M)")
			scaledInvertible := sectionPair[0]
			inside := arg.Have(
				"so the scaled structure pair lies in M chartwise",
				"fst(lattice_pair_scale(a, (A₀, A₁))) ⊆ fst(M) ∧ snd(lattice_pair_scale(a, (A₀, A₁))) ⊆ snd(M)",
				Simp(Fwd(invertible_lattice_pair.LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(sectionPair[1], sectionPair[2]))
			finiteQuotients := arg.Have(
				"the two chart quotients are finite over k",
				"finite_dimensional(«wdScalars», "+
					"    quotient_module(«wcVectors»(fst(M)), fst(lattice_pair_scale(a, (A₀, A₁))))) ∧ "+
					"finite_dimensional(«wdScalars», "+
					"    quotient_module(«wcVectors»(snd(M)), snd(lattice_pair_scale(a, (A₀, A₁)))))",
				Simp(Fwd(module_record.RestrictRingTwice)),
				By(
					inside,
					given,
					scaledInvertible,
					algebraic_curve.InvertibleQuotientFinite.Read(L).At(k, A0, A1, A01, t, scaled, M)))
			scaledFinite := arg.Have(
				"the scaled subpair has finite cohomology",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», lattice_pair_scale(a, (A₀, A₁))) ∧ "+
					"lattice_pair_finite(«wcOverlap», k, «wcField», lattice_pair_scale(a, (A₀, A₁)))",
				By(
					given,
					scaledInvertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, scaled),
					invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, scaled)))
			kInEachChart := arg.Have(
				"so k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			_, d0Def := arg.LetAs[Nat](
				"d_0",
				"module_dim(«wdScalars», "+
					"    quotient_module(«wcVectors»(fst(M)), fst(lattice_pair_scale(a, (A₀, A₁)))))")
			_, d1Def := arg.LetAs[Nat](
				"d_1",
				"module_dim(«wdScalars», "+
					"    quotient_module(«wcVectors»(snd(M)), snd(lattice_pair_scale(a, (A₀, A₁)))))")
			_, d01Def := arg.LetAs[Nat](
				"d_01",
				"module_dim(«wdScalars», "+
					"    quotient_module(«wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», M)), "+
					"        lattice_pair_ambient(«wcOverlap», «wcField», lattice_pair_scale(a, (A₀, A₁)))))")
			eulerDifference := arg.Have(
				"Euler difference is the alternating sum of quotient dimensions",
				"«wdEuler»(M) - «wdEuler»(lattice_pair_scale(a, (A₀, A₁))) = &d₀ + &d₁ - &d₀₁",
				Simp(Fwd(d0Def), Fwd(d1Def), Fwd(d01Def)),
				By(
					finiteQuotients,
					inside,
					subfieldK,
					kInEachChart,
					biaffine,
					scaledFinite,
					pair,
					lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverseT, k, inv, vectors, M, scaled)))
			scaledData := arg.Unfolded(scaledFinite, lattice_pair.LatticePairDef)
			dimensionBound := arg.Have(
				"the overlap quotient is no larger than the chart-zero quotient",
				"d₀₁ ≤ d₀",
				Simp(Fwd(d01Def), Fwd(d0Def), Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					finiteQuotients,
					inside,
					subfieldK,
					kInEachChart,
					biaffine,
					pairData,
					scaledData,
					lattice_pair.QuotientDimLocalizes.At(overlap, A0, A1, t, inverseT, k, inv, vectors, M0, scaled0)))
			scaledDegree := arg.Have(
				"the scaled structure pair has degree zero",
				"«wdDegree»(lattice_pair_scale(a, (A₀, A₁))) = &0",
				By(
					structureInvertible,
					given,
					DegreeScale.Read(L).At(k, A0, A1, A01, t, section, structure),
					DegreeStructure.Read(L).At(k, A0, A1, A01)))
			sameEuler := arg.Unfolded(scaledDegree, CurveDegreeDef)
			arg.Show(
				"the degree is d₀ + d₁ − d₀₁, with d₀₁ ≤ d₀ and d₁ nonnegative",
				Simp(Fwd(CurveDegreeDef)),
				ByArith(dimensionBound, eulerDifference, sameEuler))
		}),
})}

// DegreeZeroSectionTrivial — an invertible pair of degree zero with a
// nonzero section a is a · O.
var DegreeZeroSectionTrivial = degreeZeroSectionTrivialThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroSectionTrivial",
	Key:  "prop_291411ef042569bb",
	Reading: "deg M = (d₀ − d₀₁) + d₁ = (d₁ − d₀₁) + d₀ with both brackets nonnegative " +
		"(QuotientDimLocalizes at each chart), so degree zero forces d₀ = d₁ = 0: the chart " +
		"quotients of M by a · O vanish and M is a · O. Without the section the conclusion fails: " +
		"a pair of degree zero need not be trivial, the points of an elliptic curve giving O(P − O).",
	Deps: []registry.EntryLike{
		SectionDegreeNonneg,
		CurveDegreeDef,
		DegreeScale,
		DegreeStructure,
		algebraic_curve.InvertibleFinite,
		algebraic_curve.InvertibleQuotientFinite,
		invertible_lattice_pair.SectionInclusion,
		lattice_pair_sequence.EulerAdditive,
		lattice_pair.QuotientDimLocalizes,
		invertible_lattice_pair.LatticePairScaleDef,
		module_dimension.DimZero,
		submodule.QuotientModuleDef,
		lattice_pair.BiaffineSwap,
		algebraic_curve.CurveLatticeData,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"a ∈ lattice_pair_h0(«wcField», M).carrier",
			"a ≠ L.zero",
			"«wdDegree»(M) = &0",
		},
		Conclusion: "M = lattice_pair_scale(a, (A₀, A₁))",
	},
		"as in SectionDegreeNonneg, deg M = d₀ + d₁ − d₀₁ for the quotients of M by a · O "+
			"(SectionInclusion, EulerAdditive, DegreeScale), and d₀₁ ≤ d₀, d₀₁ ≤ d₁ (QuotientDimLocalizes "+
			"at both charts, the second at the exchanged datum); so d₀ = d₁ = 0, and a finite-dimensional "+
			"quotient of dimension zero is the zero module (DimZero), its submodule the whole: fst(M) = "+
			"image(mul(a), A₀), snd(M) = image(mul(a), A₁), which is a · O (LatticePairScaleDef)"),
})}

// LargeDegreeHasSection — an invertible pair of degree at least the genus
// has a nonzero section: its Euler characteristic forces H⁰ to have
// positive dimension.
var LargeDegreeHasSection = largeDegreeHasSectionThm{family.Add(registry.ProofEntry{
	Name: "LargeDegreeHasSection",
	Key:  "prop_a560d5f90af8e226",
	Reading: "χ(M) = deg M + 1 − g ≥ 1, and ℓ(M) ≥ χ(M) since dim H¹(M) ≥ 0, so " +
		"H⁰(M) is not {zero}. No rational point is asked for: the bound comes from the " +
		"Euler characteristic alone. H⁰(M) is finite-dimensional (InvertibleFinite), " +
		"so ℓ(M) ≥ 1 is a true dimension and gives a nonzero section.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"«wdGenus» ≤ «wdDegree»(M)",
		},
		Conclusion: "∃a:A. a ∈ lattice_pair_h0(«wcField», M).carrier ∧ a ≠ L.zero",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		M *Expr[_LatticePair],
		given Fact,
	) {
		finitePair := a.Have(
			"an invertible pair has finite cohomology",
			"lattice_pair_finite(«wcOverlap», k, «wcField», M)",
			By(given, algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M)))
		finiteCohomology := a.Unfolded(finitePair, lattice_pair.LatticePairFiniteDef)
		hypotheses := a.Conjuncts(
			given,
			"the curve datum",
			"M is invertible",
			"the degree is at least the genus")
		curve, invertible, degreeBound := hypotheses[0], hypotheses[1], hypotheses[2]
		finiteH0 := a.Conjuncts(
			finiteCohomology,
			"H⁰ has finite dimension",
			"H¹ has finite dimension")[0]
		euler := a.Have(
			"Riemann–Roch gives the Euler characteristic",
			"«wdEuler»(M) = «wdDegree»(M) + &1 - «wdGenus»",
			By(curve, RiemannRochEuler.Read(L).At(k, A0, A1, A01, t, M)))
		dimensions := a.Unfolded(
			a.Unfolded(euler, lattice_pair.LatticePairEulerDef), lattice_pair.LatticePairH0DimDef)
		dimH0 := a.TermAs[Nat]("module_dim(«wdScalars», lattice_pair_h0(«wcField», M))")
		positive := a.Have(
			"the degree bound makes the dimension of H⁰ positive",
			"0 < module_dim(«wdScalars», lattice_pair_h0(«wcField», M))",
			Derive(func(b *Argument) {
				positiveInteger := b.Have(
					"the Euler characteristic is positive and the dimension of H¹ is nonnegative",
					"&0 < int_of_num(module_dim(«wdScalars», lattice_pair_h0(«wcField», M)))",
					ByArith(dimensions, degreeBound))
				b.Show(
					"the integer embedding preserves strict order",
					By(positiveInteger, int_embed.OfNumLt.At(b.TermAs[Nat]("0"), dimH0)))
			}))
		data := a.Conjuncts(
			GroupPremises(hypotheses[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
			"the overlap lies in the field",
			"the charts and their overlap are a biaffine datum",
			"k is a subfield",
			"the structure pair is a lattice pair",
			"its ambient is the overlap",
			"the structure pair is invertible",
			"the constants form a field under L's operations",
			"the constants lie in both charts")
		subfield, kInCharts := data[2], data[7]
		pair := a.Conjuncts(
			a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
			"fst(M) is invertible over A₀",
			"snd(M) is invertible over A₁",
			"M is a lattice pair")[2]
		overlap := a.TermAs[RingOps[A]]("«wcOverlap»")
		ambient := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
		h0Submodule := a.Have(
			"the intersection of the two charts is a submodule over k",
			"submodule(«wdScalars», «wcField», fst(M) ∩ snd(M))",
			By(
				pair,
				kInCharts,
				set_order.SubsetInter.At(k, A0, A1),
				lattice_pair.H0Submodule.At(overlap, A0, A1, k, ambient, M)))
		h0On := a.Have(
			"H⁰ is a module over k",
			"module_on(«wdScalars», lattice_pair_h0(«wcField», M))",
			Derive(func(b *Argument) {
				b.Do(Unfold(lattice_pair.LatticePairH0Def))
				ambientOverK := b.Have(
					"the function field is a module over its subfield k",
					"module_on(«wdScalars», «wcField»)",
					Simp(Fwd(module_record.RestrictRingTwice)),
					By(
						subfield,
						field.SubfieldSubring.Read(L).At(k),
						module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(k)))
				b.Show(
					"restricting to the intersection gives the section module",
					By(
						h0Submodule,
						submodule.SubmoduleModuleOn.Read(ambientOverK).At(b.TermAs[Set[A]]("fst(M) ∩ snd(M)"))))
			}))
		zeroCriterion := a.Have(
			"a finite dimensional section module has dimension zero exactly when it contains only zero",
			"module_dim(«wdScalars», lattice_pair_h0(«wcField», M)) = 0 ⇔ "+
				"lattice_pair_h0(«wcField», M).carrier = {L.zero}",
			By(
				finiteH0,
				subfield,
				field.SubfieldRingSubfield.Read(L).At(k, A01),
				field.RingSubfieldRestrict.At(overlap, k, a.TermAs[Fun[A, A]]("L.inv"), k),
				module_dimension.DimZero.Read(h0On).At(a.TermAs[Fun[A, A]]("L.inv"))))
		nonzeroDimension := a.Have(
			"positive dimension excludes dimension zero",
			"module_dim(«wdScalars», lattice_pair_h0(«wcField», M)) ≠ 0",
			ByArith(positive))
		zeroSection := a.Have(
			"zero belongs to the section module",
			"L.zero ∈ lattice_pair_h0(«wcField», M).carrier",
			By(group.OneIn.Read(module.AddGroupOn.Read(h0On))))
		a.Show(
			"H⁰ contains more than zero, so it has a nonzero section",
			BySets(nonzeroDimension, zeroCriterion, zeroSection))
	}),
})}

// ProductQuotientDimensions — for invertible pairs M and N and a lattice
// pair K inside M with finite chart quotients, multiplying by N keeps the
// two chart quotients and the overlap quotient finite and preserves the
// three dimensions. Each comparison is InvertibleFractionalQuotientDim, at a
// chart ring for the chart quotients and at the overlap ring for their
// ambients.
var ProductQuotientDimensions = productQuotientDimensionsThm{family.Add(registry.ProofEntry{
	Name: "ProductQuotientDimensions",
	Key:  "prop_12ea4cb5631a1c1e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N K:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"«wdInvertible»(N)",
			"lattice_pair(«wcOverlap», A₀, A₁, «wcField», K)",
			"fst(K) ⊆ fst(M)",
			"snd(K) ⊆ snd(M)",
			"finite_dimensional(«wcRing»(k), «qZero»)",
			"finite_dimensional(«wcRing»(k), «qOne»)",
		},
		Conclusion: "finite_dimensional(«wcRing»(k), «pZero») ∧ " +
			"finite_dimensional(«wcRing»(k), «pOne») ∧ " +
			"finite_dimensional(«wcRing»(k), «pOverlap») ∧ " +
			"module_dim(«wcRing»(k), «pZero») = module_dim(«wcRing»(k), «qZero») ∧ " +
			"module_dim(«wcRing»(k), «pOne») = module_dim(«wcRing»(k), «qOne») ∧ " +
			"module_dim(«wcRing»(k), «pOverlap») = module_dim(«wcRing»(k), «qOverlap»)",
		Abbrev: Abbrev{
			{Name: "productM", Text: "«wdMul»(M, N)"},
			{Name: "productK", Text: "«wdMul»(K, N)"},
			{Name: "qZero", Text: "quotient_module(«wcVectors»(fst(M)), fst(K))"},
			{Name: "qOne", Text: "quotient_module(«wcVectors»(snd(M)), snd(K))"},
			{Name: "qOverlap", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», M)), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», K))"},
			{Name: "pZero", Text: "quotient_module(«wcVectors»(fst(«productM»)), fst(«productK»))"},
			{Name: "pOne", Text: "quotient_module(«wcVectors»(snd(«productM»)), snd(«productK»))"},
			{Name: "pOverlap", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», «productM»)), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», «productK»))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N, K *Expr[_LatticePair],
			given Fact,
		) {
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
			overlap := arg.TermAs[RingOps[A]]("«wcOverlap»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			inverseT := arg.TermAs[A]("L.inv(t)")
			inv := arg.TermAs[Fun[A, A]]("L.inv")
			parts := arg.Conjuncts(
				given,
				"the curve datum",
				"M is invertible",
				"N is invertible",
				"K is a lattice pair",
				"K lies in M on chart zero",
				"K lies in M on chart one",
				"the chart-zero quotient is finite",
				"the chart-one quotient is finite")
			curve, MInvertible, NInvertible, KPair := parts[0], parts[1], parts[2], parts[3]
			inside0, inside1, finite0, finite1 := parts[4], parts[5], parts[6], parts[7]
			data := arg.Conjuncts(
				GroupPremises(parts[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			biaffine, subfield, kInCharts := data[1], data[2], data[7]
			subrings := arg.Have(
				"the charts and their overlap are subrings of L, chart zero inside the overlap",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ subring(field_ring(L), A₀₁) ∧ A₀ ⊆ A₀₁",
				By(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			constants := arg.Have(
				"k lies in each of the three rings",
				"k ⊆ A₀ ∧ k ⊆ A₁ ∧ k ⊆ A₀₁",
				BySets(kInCharts, subrings))
			fractions := arg.Have(
				"L is the fraction field of each of the three rings",
				"fraction_field_carrier(field_ring(L), A₀) ∧ "+
					"fraction_field_carrier(field_ring(L), A₁) ∧ "+
					"fraction_field_carrier(field_ring(L), A₀₁)",
				By(curve, algebraic_curve.FractionFieldBothCharts.Read(L).At(k, A0, A1, A01, t)))
			MData := arg.Unfolded(MInvertible, invertible_lattice_pair.InvertibleLatticePairDef)
			NData := arg.Unfolded(NInvertible, invertible_lattice_pair.InvertibleLatticePairDef)
			KData := arg.Unfolded(KPair, lattice_pair.LatticePairDef)
			KChartModules := arg.Have(
				"K's chart modules use the field's restricted scalar rings",
				"submodule(«wcRing»(A₀), «wcField», fst(K)) ∧ submodule(«wcRing»(A₁), «wcField», snd(K))",
				By(
					Normalized,
					KData,
					module_record.RestrictRingTwice.At(fieldRing, A01, A0),
					module_record.RestrictRingTwice.At(fieldRing, A01, A1)))
			firstM := arg.TermAs[Set[A]]("fst(M)")
			firstK := arg.TermAs[Set[A]]("fst(K)")
			firstN := arg.TermAs[Set[A]]("fst(N)")
			secondM := arg.TermAs[Set[A]]("snd(M)")
			secondK := arg.TermAs[Set[A]]("snd(K)")
			secondN := arg.TermAs[Set[A]]("snd(N)")
			chartZero := arg.Have(
				"chart zero: multiplication preserves quotient finiteness and dimension",
				"finite_dimensional(«wcRing»(k), «pZero») ∧ "+
					"module_dim(«wcRing»(k), «pZero») = module_dim(«wcRing»(k), «qZero»)",
				Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Fst)),
				By(
					ideal_colength.InvertibleFractionalQuotientDim.Read(L).At(k, A0, firstM, firstK, firstN),
					fractions,
					constants,
					subrings,
					subfield,
					KChartModules,
					MData,
					NData,
					inside0,
					finite0))
			chartOne := arg.Have(
				"chart one: multiplication preserves quotient finiteness and dimension",
				"finite_dimensional(«wcRing»(k), «pOne») ∧ "+
					"module_dim(«wcRing»(k), «pOne») = module_dim(«wcRing»(k), «qOne»)",
				Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Snd)),
				By(
					ideal_colength.InvertibleFractionalQuotientDim.Read(L).At(k, A1, secondM, secondK, secondN),
					fractions,
					constants,
					subrings,
					subfield,
					KChartModules,
					MData,
					NData,
					inside1,
					finite1))
			ambientM := arg.TermAs[Set[A]]("lattice_pair_ambient(«wcOverlap», «wcField», M)")
			ambientN := arg.TermAs[Set[A]]("lattice_pair_ambient(«wcOverlap», «wcField», N)")
			ambientK := arg.TermAs[Set[A]]("lattice_pair_ambient(«wcOverlap», «wcField», K)")
			ambientInvertible := arg.Have(
				"the ambients of M and N are invertible over the overlap",
				"invertible_fractional(field_ring(L), A₀₁, lattice_pair_ambient(«wcOverlap», «wcField», M)) ∧ "+
					"invertible_fractional(field_ring(L), A₀₁, lattice_pair_ambient(«wcOverlap», «wcField», N))",
				By(
					subrings,
					MData,
					NData,
					invertible_lattice_pair.AmbientInvertible.Read(L).At(A0, A1, A01, M),
					invertible_lattice_pair.AmbientInvertible.Read(L).At(A0, A1, A01, N)))
			ambientSubmodule := arg.Have(
				"the ambient of K is a submodule over the overlap",
				"submodule(«wcOverlap», «wcField», lattice_pair_ambient(«wcOverlap», «wcField», K))",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					KData,
					KChartModules,
					submodule.SubmoduleSubset.At(arg.TermAs[RingOps[A]]("«wcRing»(A₀)"), vectors, firstK),
					submodule.SpanSubmodule.At(overlap, vectors, firstK)))
			ambientInclusion := arg.Have(
				"the inclusion K into M extends to their ambients",
				"lattice_pair_ambient(«wcOverlap», «wcField», K) ⊆ lattice_pair_ambient(«wcOverlap», «wcField», M)",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(inside0, submodule.SpanMono.At(overlap, vectors, firstK, firstM)))
			MModules := arg.Unfolded(MData, lattice_pair.LatticePairDef)
			rawOverlapFinite := arg.Have(
				"the finite chart-zero quotient makes the ambient quotient finite",
				"finite_dimensional(«wdScalars», «qOverlap»)",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					finite0,
					inside0,
					constants,
					KData,
					biaffine,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					MModules,
					lattice_pair.QuotientDimLocalizes.At(overlap, A0, A1, t, inverseT, k, inv, vectors, firstM, firstK),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			overlapFinite := arg.Simplified(rawOverlapFinite, Fwd(module_record.RestrictRingTwice))
			productAmbientM := arg.Have(
				"multiplication of M and N multiplies their ambients",
				"lattice_pair_ambient(«wcOverlap», «wcField», «productM») = "+
					"fractional_mul(field_ring(L), "+
					"    A₀₁, "+
					"    lattice_pair_ambient(«wcOverlap», «wcField», M), "+
					"    lattice_pair_ambient(«wcOverlap», «wcField», N))",
				By(
					subrings,
					MInvertible,
					NInvertible,
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M),
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, N),
					invertible_lattice_pair.AmbientOfMul.Read(L).At(A0, A1, A01, M, N)))
			productAmbientK := arg.Have(
				"multiplication of K and N multiplies their ambients",
				"lattice_pair_ambient(«wcOverlap», «wcField», «productK») = "+
					"fractional_mul(field_ring(L), "+
					"    A₀₁, "+
					"    lattice_pair_ambient(«wcOverlap», «wcField», K), "+
					"    lattice_pair_ambient(«wcOverlap», «wcField», N))",
				By(
					subrings,
					NInvertible,
					KChartModules,
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, N),
					submodule.SubmoduleSubset.At(arg.TermAs[RingOps[A]]("«wcRing»(A₀)"), vectors, firstK),
					invertible_lattice_pair.AmbientOfMul.Read(L).At(A0, A1, A01, K, N)))
			overlapComparison := arg.Have(
				"overlap: multiplication preserves the dimension of the ambient quotient",
				"finite_dimensional(«wcRing»(k), «pOverlap») ∧ "+
					"module_dim(«wcRing»(k), «pOverlap») = module_dim(«wcRing»(k), «qOverlap»)",
				Simp(Fwd(productAmbientK), Fwd(productAmbientM)),
				By(
					ideal_colength.InvertibleFractionalQuotientDim.Read(L).At(k, A01, ambientM, ambientK, ambientN),
					fractions,
					constants,
					subrings,
					subfield,
					overlapFinite,
					ambientInclusion,
					ambientSubmodule,
					ambientInvertible))
			arg.Show(
				"all three product quotients are finite and their dimensions are preserved",
				By(chartZero, chartOne, overlapComparison))
		}),
})}

// DegreeAdditive — the degree of a product of invertible pairs is the sum
// of their degrees.
var DegreeAdditive = degreeAdditiveThm{family.Add(registry.ProofEntry{
	Name: "DegreeAdditive",
	Key:  "prop_4399d0aa9f5ffa7d",
	Reading: "Compare M and O with their meet K. Multiplication by the " +
		"invertible N preserves the three quotient dimensions in both " +
		"comparisons; subtracting their Euler differences cancels K and K times N.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"«wdInvertible»(N)",
		},
		Conclusion: "«wdDegree»(«wdMul»(M, N)) = «wdDegree»(M) + «wdDegree»(N)",
		Abbrev: Abbrev{
			{Name: "qMK0", Text: "quotient_module(«wcVectors»(fst(M)), fst(K))"},
			{Name: "qMK1", Text: "quotient_module(«wcVectors»(snd(M)), snd(K))"},
			{Name: "qMK01", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», M)), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», K))"},
			{Name: "qOK0", Text: "quotient_module(«wcVectors»(A₀), fst(K))"},
			{Name: "qOK1", Text: "quotient_module(«wcVectors»(A₁), snd(K))"},
			{Name: "qOK01", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», (A₀, A₁))), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», K))"},
			{Name: "qMNKN0", Text: "quotient_module(«wcVectors»(fst(«wdMul»(M, N))), fst(«wdMul»(K, N)))"},
			{Name: "qMNKN1", Text: "quotient_module(«wcVectors»(snd(«wdMul»(M, N))), snd(«wdMul»(K, N)))"},
			{Name: "qMNKN01", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», «wdMul»(M, N))), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», «wdMul»(K, N)))"},
			{Name: "qONKN0", Text: "quotient_module(«wcVectors»(fst(«wdMul»((A₀, A₁), N))), " +
				"    fst(«wdMul»(K, N)))"},
			{Name: "qONKN1", Text: "quotient_module(«wcVectors»(snd(«wdMul»((A₀, A₁), N))), " +
				"    snd(«wdMul»(K, N)))"},
			{Name: "qONKN01", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», «wdMul»((A₀, A₁), N))), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», «wdMul»(K, N)))"},
			{Name: "qNKN0", Text: "quotient_module(«wcVectors»(fst(N)), fst(«wdMul»(K, N)))"},
			{Name: "qNKN1", Text: "quotient_module(«wcVectors»(snd(N)), snd(«wdMul»(K, N)))"},
			{Name: "qNKN01", Text: "quotient_module( " +
				"    «wcVectors»(lattice_pair_ambient(«wcOverlap», «wcField», N)), " +
				"    lattice_pair_ambient(«wcOverlap», «wcField», «wdMul»(K, N)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[_LatticePair],
			given Fact,
		) {
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("«wcOverlap»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			inverseT := a.TermAs[A]("L.inv(t)")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			structure := a.TermAs[_LatticePair]("(A₀, A₁)")
			K, meetDef := a.LetAs[_LatticePair]("K", "(fst(M) ∩ A₀, snd(M) ∩ A₁)")
			MN := a.TermAs[_LatticePair]("«wdMul»(M, N)")
			KN := a.TermAs[_LatticePair]("«wdMul»(K, N)")
			data := a.Conjuncts(
				GroupPremises(given, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, subfield, structurePair, structureInvertible, kInCharts :=
				data[0], data[1], data[2], data[3], data[5], data[7]
			subfieldK := a.Have(
				"k, a subfield of L, is a field under the overlap's operations",
				"ring_subfield(«wcOverlap», L.inv, k)",
				By(subfield, field.SubfieldRingSubfield.Read(L).At(k, A01)))
			meet := a.Have(
				"the meet is a lattice pair with finite chart quotients in M and O",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», K) ∧ "+
					"finite_dimensional(«wcRing»(k), «qMK0») ∧ "+
					"finite_dimensional(«wcRing»(k), «qMK1») ∧ "+
					"finite_dimensional(«wcRing»(k), «qOK0») ∧ "+
					"finite_dimensional(«wcRing»(k), «qOK1»)",
				By(
					Normalized,
					meetDef,
					given,
					algebraic_curve.InvertibleMeetStructure.Read(L).At(k, A0, A1, A01, t, M),
					pairs.Fst,
					pairs.Snd))
			inside := a.Have(
				"the meet lies in M and O chartwise",
				"fst(K) ⊆ fst(M) ∧ snd(K) ⊆ snd(M) ∧ fst(K) ⊆ A₀ ∧ snd(K) ⊆ A₁",
				Simp(Fwd(meetDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				BySets())
			productM := a.Have(
				"multiplication by N preserves M/K on both charts and on the overlap",
				"finite_dimensional(«wcRing»(k), «qMNKN0») ∧ "+
					"finite_dimensional(«wcRing»(k), «qMNKN1») ∧ "+
					"module_dim(«wcRing»(k), «qMNKN0») = module_dim(«wcRing»(k), «qMK0») ∧ "+
					"module_dim(«wcRing»(k), «qMNKN1») = module_dim(«wcRing»(k), «qMK1») ∧ "+
					"module_dim(«wcRing»(k), «qMNKN01») = module_dim(«wcRing»(k), «qMK01»)",
				By(given, meet, inside, ProductQuotientDimensions.Read(L).At(k, A0, A1, A01, t, M, N, K)))
			productO := a.Have(
				"multiplication by N preserves O/K on both charts and on the overlap",
				"finite_dimensional(«wcRing»(k), «qONKN0») ∧ "+
					"finite_dimensional(«wcRing»(k), «qONKN1») ∧ "+
					"module_dim(«wcRing»(k), «qONKN0») = module_dim(«wcRing»(k), «qOK0») ∧ "+
					"module_dim(«wcRing»(k), «qONKN1») = module_dim(«wcRing»(k), «qOK1») ∧ "+
					"module_dim(«wcRing»(k), «qONKN01») = module_dim(«wcRing»(k), «qOK01»)",
				By(
					given,
					structureInvertible,
					meet,
					inside,
					ProductQuotientDimensions.Read(L).At(k, A0, A1, A01, t, structure, N, K),
					pairs.Fst,
					pairs.Snd))
			pairData := a.Have(
				"M and N are lattice pairs",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M) ∧ lattice_pair(«wcOverlap», A₀, A₁, «wcField», N)",
				By(
					given,
					invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, M),
					invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, N)))
			productMeet := a.Have(
				"K times N is a lattice pair",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», «wdMul»(K, N))",
				By(
					overlapInField,
					biaffine,
					meet,
					pairData,
					invertible_lattice_pair.MulIsLattice.Read(L).At(A0, A1, A01, t, K, N)))
			productInvertible := a.Have(
				"M times N is invertible",
				"«wdInvertible»(«wdMul»(M, N))",
				By(
					overlapInField,
					biaffine,
					given,
					invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, M, N)))
			unit := a.Have(
				"the structure pair times N is N",
				"«wdMul»((A₀, A₁), N) = N",
				By(
					overlapInField,
					biaffine,
					pairData,
					invertible_lattice_pair.MulOne.Read(L).At(A0, A1, A01, t, N)))
			quotientsOfN := a.Simplified(productO, Fwd(unit))
			finiteProducts := a.Have(
				"M and its invertible product have finite cohomology",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», «wdMul»(M, N)) ∧ "+
					"lattice_pair_finite(«wcOverlap», k, «wcField», M) ∧ "+
					"lattice_pair_finite(«wcOverlap», k, «wcField», «wdMul»(M, N))",
				By(
					given,
					productInvertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M),
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, MN),
					invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, MN)))
			K0, K1 := a.TermAs[Set[A]]("fst(K)"), a.TermAs[Set[A]]("snd(K)")
			M0, M1 := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			N0, N1 := a.TermAs[Set[A]]("fst(N)"), a.TermAs[Set[A]]("snd(N)")
			productInside := a.Have(
				"multiplication preserves the two chartwise inclusions",
				"fst(«wdMul»(K, N)) ⊆ fst(«wdMul»(M, N)) ∧ "+
					"snd(«wdMul»(K, N)) ⊆ snd(«wdMul»(M, N)) ∧ "+
					"fst(«wdMul»(K, N)) ⊆ fst(«wdMul»((A₀, A₁), N)) ∧ "+
					"snd(«wdMul»(K, N)) ⊆ snd(«wdMul»((A₀, A₁), N))",
				Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					inside,
					fractional_ideal.FractionalMulMono.Read(L).At(A0, K0, M0, N0, N0),
					fractional_ideal.FractionalMulMono.Read(L).At(A0, K0, A0, N0, N0),
					fractional_ideal.FractionalMulMono.Read(L).At(A1, K1, M1, N1, N1),
					fractional_ideal.FractionalMulMono.Read(L).At(A1, K1, A1, N1, N1),
					set_order.SubsetRefl.At(N0),
					set_order.SubsetRefl.At(N1)))
			productInsideN := a.Simplified(productInside, Fwd(unit))
			kInEachChart := a.Have(
				"so k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			finiteMeet := a.Have(
				"finite chart quotients transfer finite cohomology from M to its meet",
				"lattice_pair_finite(«wcOverlap», k, «wcField», K)",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					inside,
					meet,
					pairData,
					finiteProducts,
					lattice_pair_sequence.EulerSubpairFinite.At(overlap, A0, A1, t, inverseT, k, inv, vectors, M, K),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			finiteProductMeet := a.Have(
				"the finite product quotients transfer finite cohomology to K times N",
				"lattice_pair_finite(«wcOverlap», k, «wcField», «wdMul»(K, N))",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					productInsideN,
					productM,
					finiteProducts,
					productMeet,
					lattice_pair_sequence.EulerSubpairFinite.At(overlap, A0, A1, t, inverseT, k, inv, vectors, MN, KN),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			eulerMK := a.Have(
				"M exceeds its meet in Euler characteristic by the alternating sum of the quotient dimensions",
				"«wdEuler»(M) - «wdEuler»(K) = "+
					"&module_dim(«wcRing»(k), «qMK0») + "+
					"&module_dim(«wcRing»(k), «qMK1») - "+
					"&module_dim(«wcRing»(k), «qMK01»)",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					pairData,
					meet,
					inside,
					finiteMeet,
					lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverseT, k, inv, vectors, M, K),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			eulerMNKN := a.Have(
				"M times N exceeds K times N by the alternating sum of its quotient dimensions",
				"«wdEuler»(«wdMul»(M, N)) - «wdEuler»(«wdMul»(K, N)) = "+
					"&module_dim(«wcRing»(k), «qMNKN0») + "+
					"&module_dim(«wcRing»(k), «qMNKN1») - "+
					"&module_dim(«wcRing»(k), «qMNKN01»)",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					finiteProducts,
					productMeet,
					productInsideN,
					productM,
					finiteProductMeet,
					lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverseT, k, inv, vectors, MN, KN),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			eulerM := a.Have(
				"the two Euler differences for M/K agree after multiplication",
				"«wdEuler»(«wdMul»(M, N)) - «wdEuler»(«wdMul»(K, N)) = «wdEuler»(M) - «wdEuler»(K)",
				ByArith(eulerMK, eulerMNKN, productM))
			eulerOK := a.Have(
				"the structure pair exceeds the meet by the alternating sum of the quotient dimensions",
				"«wdEuler»((A₀, A₁)) - «wdEuler»(K) = "+
					"&module_dim(«wcRing»(k), «qOK0») + "+
					"&module_dim(«wcRing»(k), «qOK1») - "+
					"&module_dim(«wcRing»(k), «qOK01»)",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					structurePair,
					meet,
					inside,
					finiteMeet,
					lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverseT, k, inv, vectors, structure, K),
					module_record.RestrictRingTwice.At(fieldRing, A01, k),
					pairs.Fst,
					pairs.Snd))
			eulerNKN := a.Have(
				"N exceeds K times N by the alternating sum of its quotient dimensions",
				"«wdEuler»(N) - «wdEuler»(«wdMul»(K, N)) = "+
					"&module_dim(«wcRing»(k), «qNKN0») + "+
					"&module_dim(«wcRing»(k), «qNKN1») - "+
					"&module_dim(«wcRing»(k), «qNKN01»)",
				By(
					biaffine,
					subfieldK,
					kInEachChart,
					pairData,
					productMeet,
					productInsideN,
					quotientsOfN,
					finiteProductMeet,
					lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverseT, k, inv, vectors, N, KN),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			eulerO := a.Have(
				"the two Euler differences for O/K agree after multiplication",
				"«wdEuler»(N) - «wdEuler»(«wdMul»(K, N)) = «wdEuler»((A₀, A₁)) - «wdEuler»(K)",
				ByArith(eulerOK, eulerNKN, quotientsOfN))
			a.Show(
				"subtracting cancels both meet terms and gives additivity of degree",
				Simp(Fwd(CurveDegreeDef)),
				ByArith(eulerO, eulerM))
		}),
})}

// DegreeInverse — the inverse of an invertible pair has the opposite
// degree: their product is the structure pair, whose degree is zero.
var DegreeInverse = degreeInverseThm{family.Add(registry.ProofEntry{
	Name: "DegreeInverse",
	Key:  "prop_31abd8781163a056",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
		},
		Conclusion: "«wdDegree»(«wdInverse»(M)) = -«wdDegree»(M)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		M *Expr[_LatticePair],
		given Fact,
	) {
		data := a.Conjuncts(
			GroupPremises(given, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
			"the overlap lies in the field",
			"the charts and their overlap are a biaffine datum",
			"k is a subfield",
			"the structure pair is a lattice pair",
			"its ambient is the overlap",
			"the structure pair is invertible",
			"the constants form a field under L's operations",
			"the constants lie in both charts")
		overlapInField, biaffine := data[0], data[1]
		inverseFacts := a.Have(
			"the inverse is invertible and its product with M is the structure pair",
			"«wdInvertible»(«wdInverse»(M)) ∧ «wdMul»(M, «wdInverse»(M)) = (A₀, A₁)",
			By(
				overlapInField,
				biaffine,
				given,
				invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, M)))
		inverseParts := a.Conjuncts(
			inverseFacts,
			"the inverse of M is invertible",
			"M times its inverse is the structure pair")
		inverse := a.TermAs[_LatticePair]("«wdInverse»(M)")
		additive := a.Have(
			"the degree of the product is the sum of the degrees",
			"«wdDegree»(«wdMul»(M, «wdInverse»(M))) = «wdDegree»(M) + «wdDegree»(«wdInverse»(M))",
			By(given, inverseParts[0], DegreeAdditive.Read(L).At(k, A0, A1, A01, t, M, inverse)))
		a.Show(
			"the sum is the structure pair's degree, so the two degrees are opposite",
			ByArith(additive, inverseParts[1], DegreeStructure.Read(L).At(k, A0, A1, A01)))
	}),
})}

// InvertibleInsidePointsDegree — an invertible pair J inside the structure pair
// and inside each of a finite set S of regular points has degree at most
// -card(S). By induction on S, for every such pair: with no points, one is a
// nonzero section of J⁻¹ (invertible_lattice_pair.InverseHoldsOne), whose
// degree is -deg J; a further point X raises the degree by one under the twist
// of J at X, which stays inside the structure pair and the points of S
// (lattice_pair_twist.TwistInsidePoints).
var InvertibleInsidePointsDegree = invertibleInsidePointsDegreeThm{family.Add(registry.ProofEntry{
	Name: "InvertibleInsidePointsDegree",
	Key:  "prop_2abbb38d63188c08",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀S:set(prod(set(A), set(A))). " +
			"∀J:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"finite(S)",
			"∀Q:prod(set(A), set(A)). Q ∈ S ⇒ «wdPoint»(Q)",
			"«wdInvertible»(J)",
			"fst(J) ⊆ A₀",
			"snd(J) ⊆ A₁",
			"∀Q:prod(set(A), set(A)). Q ∈ S ⇒ fst(J) ⊆ fst(Q) ∧ snd(J) ⊆ snd(Q)",
		},
		Conclusion: "«wdDegree»(J) + int_of_num(card(S)) ≤ &0",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			S *Expr[Set[_LatticePair]],
			curve, finiteS, points Fact,
		) {
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, subfield, kInCharts := data[0], data[1], data[2], data[7]
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			a.Show(
				"by induction on the finite set of points",
				ByInduction(finite_set.FiniteInductFreshOn, finiteS, points,
					Case(
						"with no points, one is a section of the inverse, so the degree is at most zero",
						Derive(func(b *Argument) {
							J := b.FixAs[_LatticePair]("J")
							assumed := b.Conjuncts(
								b.Assume(),
								"J is invertible",
								"J lies in chart 0",
								"and in chart 1",
								"J lies inside every point of the empty set")
							invertibleJ, in0, in1 := assumed[0], assumed[1], assumed[2]
							inverse := b.TermAs[_LatticePair]("«wdInverse»(J)")
							one := b.TermAs[A]("L.one")
							inverted := b.Have(
								"the inverse of J is invertible",
								"«wdInvertible»(«wdInverse»(J))",
								By(
									overlapInField,
									biaffine,
									invertibleJ,
									invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, J)))
							section := b.Have(
								"one is a section of it",
								"L.one ∈ lattice_pair_h0(«wcField», «wdInverse»(J)).carrier",
								By(
									L,
									in0,
									in1,
									overlapInField,
									biaffine,
									invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t),
									invertible_lattice_pair.InverseHoldsOne.Read(L).At(A0, A1, J)))
							nonnegative := b.Have(
								"so the inverse has nonnegative degree",
								"&0 ≤ «wdDegree»(«wdInverse»(J))",
								By(
									curve,
									inverted,
									section,
									field.OneNotZeroOn.Read(L),
									SectionDegreeNonneg.Read(L).At(k, A0, A1, A01, t, one, inverse)))
							negated := b.Have(
								"which is minus the degree of J",
								"«wdDegree»(«wdInverse»(J)) = -«wdDegree»(J)",
								By(curve, invertibleJ, DegreeInverse.Read(L).At(k, A0, A1, A01, t, J)))
							b.Do(Simp(Fwd(cardinality.CardClauses)))
							b.Show(
								"hence the bound",
								ByArith(nonnegative, negated))
						})),
					Case(
						"a further point: the twist at it has one more degree and one point fewer to lie in",
						Derive(func(b *Argument) {
							X := b.FixAs[_LatticePair]("X")
							T := b.FixAs[Set[_LatticePair]]("T")
							carried := b.Conjuncts(
								b.Assume(),
								"the bound holds along T",
								"X is a new point",
								"T is finite",
								"X is a regular point",
								"so is every point of T")
							ih, fresh, finiteT, pointX, pointsT := carried[0], carried[1], carried[2], carried[3], carried[4]
							J := b.FixAs[_LatticePair]("J")
							assumed := b.Conjuncts(
								b.Assume(),
								"J is invertible",
								"J lies in chart 0",
								"and in chart 1",
								"J lies inside every point of insert(X, T)")
							invertibleJ, inside := assumed[0], assumed[3]
							holds := b.TermAs[Set[_LatticePair]]("λQ:prod(set(A), set(A)). fst(J) ⊆ fst(Q) ∧ snd(J) ⊆ snd(Q)")
							insideAll := b.Have(
								"J lies inside X and inside every point of T",
								"fst(J) ⊆ fst(X) ∧ "+
									"snd(J) ⊆ snd(X) ∧ "+
									"(∀Q:prod(set(A), set(A)). Q ∈ T ⇒ fst(J) ⊆ fst(Q) ∧ snd(J) ⊆ snd(Q))",
								By(inside, set_basic.ForallInInsert.At(holds, X, T)))
							invertibleX := b.Have(
								"X is invertible",
								"«wdInvertible»(X)",
								By(pointX, lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, X)))
							inverseX := b.TermAs[_LatticePair]("«wdInverse»(X)")
							twisted := b.TermAs[_LatticePair]("«wdTwist»(J, X)")
							invertibleTwist := b.Have(
								"the twist of J at X is invertible, a product of two",
								"«wdInvertible»(«wdTwist»(J, X))",
								By(
									overlapInField,
									biaffine,
									invertibleX,
									invertibleJ,
									invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, X),
									invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, inverseX, J),
									lattice_pair_twist.LatticePairTwistDef.At(ring, A0, A1, J, X)))
							raised := b.Have(
								"it has one more degree",
								"«wdDegree»(«wdTwist»(J, X)) = «wdDegree»(J) + &1",
								By(curve, invertibleJ, pointX, DegreeTwist.Read(L).At(k, A0, A1, A01, t, J, X)))
							reading := b.Have(
								"it lies in the structure pair, and in the other points J lies inside",
								"fst(«wdTwist»(J, X)) ⊆ A₀ ∧ "+
									"snd(«wdTwist»(J, X)) ⊆ A₁ ∧ "+
									"(∀Q:prod(set(A), set(A)). "+
									"    «wdPoint»(Q) ∧ Q ≠ X ∧ fst(J) ⊆ fst(Q) ∧ snd(J) ⊆ snd(Q) ⇒ "+
									"    fst(«wdTwist»(J, X)) ⊆ fst(Q) ∧ snd(«wdTwist»(J, X)) ⊆ snd(Q))",
								By(
									L,
									overlapInField,
									biaffine,
									subfield,
									kInCharts,
									pointX,
									invertibleJ,
									insideAll,
									lattice_pair_twist.TwistInsidePoints.Read(L).At(k, A0, A1, A01, t, J, X)))
							onT := b.Have(
								"so in every point of T, none of which is X",
								"∀Q:prod(set(A), set(A)). Q ∈ T ⇒ fst(«wdTwist»(J, X)) ⊆ fst(Q) ∧ snd(«wdTwist»(J, X)) ⊆ snd(Q)",
								Derive(func(c *Argument) {
									c.FixAs[_LatticePair]("Q")
									member := c.Assume()
									c.Show(
										"Q is a regular point of T, so not X, and J lies inside it",
										By(fresh, member, insideAll, reading, pointsT))
								}))
							induced := b.Have(
								"the induction hypothesis reads at the twist",
								"«wdDegree»(«wdTwist»(J, X)) + int_of_num(card(T)) ≤ &0",
								By(ih.At(twisted), invertibleTwist, reading, onT))
							counted := b.Have(
								"X counts one point more",
								"card(insert(X, T)) = suc(card(T))",
								By(finiteT, fresh, cardinality.InsertCountsOneMore.At(T, X)))
							b.Show(
								"which is the bound at J",
								ByArith(induced, raised, counted, int_embed.OfNumSuc.At(b.TermAs[Nat]("card(T)"))))
						}))))
		}),
})}

// DegreeOneSectionIsPoint — an invertible pair of degree one with a
// nonzero section a is a · O(P) for a regular point P: the point where
// the section's divisor of zeros lies.
var DegreeOneSectionIsPoint = degreeOneSectionIsPointThm{family.Add(registry.ProofEntry{
	Name: "DegreeOneSectionIsPoint",
	Key:  "prop_de99310e228905d8",
	Reading: "With a · O ⊆ M and quotient dimensions d₀, d₁, d₀₁: d₀ ≥ d₀₁ ≤ d₁ and d₀ + d₁ − " +
		"d₀₁ = 1 leave (1, 0, 0), (0, 1, 0) and (1, 1, 1) — a point on chart 0 only, on chart 1 " +
		"only, or on both. P is the inverse of the pair a⁻¹ · M ⊇ O; its chart ideals have colength " +
		"d₀ and d₁ (InvertibleColengthQuotient), so colength one or the whole chart, residue field " +
		"k, and it is invertible: regular. The point is found without asking the curve to be smooth: " +
		"invertibility of M is what makes P's ideals invertible. So no singular point arises: an " +
		"invertible ideal of colength one there would make the maximal ideal locally principal.",
	Deps: []registry.EntryLike{
		DegreeZeroSectionTrivial,
		SectionDegreeNonneg,
		CurveDegreeDef,
		DegreeScale,
		algebraic_curve.InvertibleFinite,
		algebraic_curve.InvertibleQuotientFinite,
		algebraic_curve.CurveLatticeData,
		invertible_lattice_pair.SectionInclusion,
		lattice_pair_sequence.EulerAdditive,
		lattice_pair.QuotientDimLocalizes,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticeScale,
		invertible_lattice_pair.AmbientInvertible,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.MulComm,
		lattice_pair_twist.LatticePairTwistDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		biaffine_rational_point.BiaffineRationalPointDef,
		ideal_colength.InvertibleColengthQuotient,
		ring_ideal.IdealSpanDef,
		module_dimension.DimZero,
		module_dimension.DimBasis,
		fractional_ideal.SpanInSubringIsIdealSpan,
		invertible_lattice_pair.AmbientOfMul,
		lattice_pair.BiaffineSwap,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t a:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"a ∈ lattice_pair_h0(«wcField», M).carrier",
			"a ≠ L.zero",
			"«wdDegree»(M) = &1",
		},
		Conclusion: "∃P:prod(set(A), set(A)). " +
			"    «wdPoint»(P) ∧ M = lattice_pair_scale(a, «wdTwist»((A₀, A₁), P))",
	},
		"N = inv(a) · M is invertible (InvertibleLatticeScale), holds O chart by chart and has "+
			"degree one (DegreeScale); take P = N⁻¹, invertible with P⁻¹ = N "+
			"(InvertibleLatticeInverse), and P ⊆ O since one ∈ N, with finite chart quotients "+
			"(InvertibleQuotientFinite); the quotients of N by O have d₀ + d₁ − d₀₁ = 1 "+
			"(EulerAdditive) with d₀₁ ≤ d₀, d₀₁ ≤ d₁ (QuotientDimLocalizes), and dim(A₀/fst(P)) = d₀, "+
			"dim(A₁/snd(P)) = d₁, dim(A₀₁/ideal_span(A₀₁, fst(P))) = d₀₁ (InvertibleColengthQuotient "+
			"on each chart and on the overlap, AmbientInvertible); a chart ideal of colength one holds "+
			"every member modulo the class of one, residue field k, and of colength zero is the chart "+
			"(DimZero, DimBasis); the two charts' ideals span one ideal of A₀₁ (P is a lattice pair), "+
			"proper exactly at (1, 1, 1): so P is a rational point (BiaffineRationalPointDef), regular "+
			"as it is invertible; and M = a · N = a · (P⁻¹ · O) (MulComm, MulOne, LatticePairTwistDef)"),
})}

// RiemannRochEuler — χ(M) = deg M + 1 − g: the degree is χ(M) − χ(O) by
// definition, and χ(O) = 1 − g.
var RiemannRochEuler = riemannRochEulerThm{family.Add(registry.ProofEntry{
	Name: "RiemannRochEuler",
	Key:  "prop_13474e94a740d4e3",
	Reading: "An identity of integers for every pair M: the degree is χ measured " +
		"from χ(O), and χ(O) = 1 − g. It says something about M only where χ(M) is a " +
		"determined number, as it is for an invertible pair (InvertibleFinite).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "«wdEuler»(M) = «wdDegree»(M) + &1 - «wdGenus»",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			curve Fact,
		) {
			structure := a.Have(
				"the structure pair has Euler characteristic one minus the genus",
				"lattice_pair_euler(«wcOverlap», k, «wcField», (A₀, A₁)) = &1 - «wdGenus»",
				By(curve, algebraic_curve.StructureEuler.Read(L).At(k, A0, A1, A01, t)))
			a.Show(
				"deg M is χ(M) − χ(O), so χ(M) = deg M + χ(O) = deg M + 1 − g",
				Unfold(CurveDegreeDef),
				ByArith(structure))
		}),
})}

// NegativeDegreeNoSections — an invertible pair of negative degree has no
// sections: ℓ(X) = 0. A nonzero section would make the degree nonnegative
// (SectionDegreeNonneg), so H⁰(X) is {0}, and a finite-dimensional module
// that is zero alone has dimension zero.
var NegativeDegreeNoSections = negativeDegreeNoSectionsThm{family.Add(registry.ProofEntry{
	Name: "NegativeDegreeNoSections",
	Key:  "prop_25893ab587c4a444",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, X)",
			"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, X) < &0",
		},
		Conclusion: "lattice_pair_h0_dim(«overlap», k, «fieldModule», X) = 0",
		Abbrev: Abbrev{
			{Name: "overlap", Text: "restrict_ring(field_ring(L), A₀₁)"},
			{Name: "fieldModule", Text: "regular_module(field_ring(L))"},
			{Name: "scalars", Text: "restrict_ring(«overlap», k)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[Prod[Set[A], Set[A]]],
			curve, invertible, negative Fact,
		) {
			fieldOps := a.TermAs[FieldOps[A]]("L")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«fieldModule»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			latticeData := algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)
			finite := a.Have(
				"an invertible pair has finite-dimensional sections",
				"finite_dimensional(«scalars», lattice_pair_h0(«fieldModule», X))",
				By(
					curve,
					invertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, X),
					lattice_pair.LatticePairFiniteDef.At(overlap, k, vectors, X)))
			subfield := a.Have(
				"k is a subfield of L",
				"subfield(L, k)",
				By(curve, latticeData))
			sectionsSubmodule := a.Have(
				"the intersection of the two charts is a submodule over k",
				"submodule(«scalars», «fieldModule», fst(X) ∩ snd(X))",
				By(
					curve,
					invertible,
					latticeData,
					invertible_lattice_pair.InvertibleLatticePairDef.At(
						a.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, A01, X),
					set_order.SubsetInter.At(k, A0, A1),
					lattice_pair.H0Submodule.At(overlap, A0, A1, k, vectors, X)))
			fieldOverK := a.Have(
				"the function field is a module over its subfield k",
				"module_on(«scalars», «fieldModule»)",
				Simp(Fwd(module_record.RestrictRingTwice)),
				By(
					subfield,
					field.SubfieldSubring.Read(L).At(k),
					module.ModuleRestrictScalars.Read(module.RegularModuleOn.Read(field.RingOn.Read(L))).At(k)))
			sectionsModule := a.Have(
				"H⁰ is a module over k",
				"module_on(«scalars», lattice_pair_h0(«fieldModule», X))",
				By(
					sectionsSubmodule,
					submodule.SubmoduleModuleOn.Read(fieldOverK).At(a.TermAs[Set[A]]("fst(X) ∩ snd(X)")),
					lattice_pair.LatticePairH0Def.At(vectors, X)))
			// The dimension is measured over k as a field under L's operations, with L's inverse.
			criterion := a.Have(
				"a finite-dimensional H⁰ has dimension zero exactly when it is zero alone",
				"module_dim(«scalars», lattice_pair_h0(«fieldModule», X)) = 0 ⇔ "+
					"lattice_pair_h0(«fieldModule», X).carrier = {L.zero}",
				By(
					finite,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					field.RingSubfieldRestrict.At(overlap, k, inv, k),
					module_dimension.DimZero.Read(sectionsModule).At(inv)))
			zeroSection := a.Have(
				"zero is a section",
				"L.zero ∈ lattice_pair_h0(«fieldModule», X).carrier",
				By(group.OneIn.Read(module.AddGroupOn.Read(sectionsModule))))
			carrier := a.Have(
				"the sections are the points of the two charts",
				"lattice_pair_h0(«fieldModule», X).carrier = fst(X) ∩ snd(X)",
				Simp(Fwd(lattice_pair.LatticePairH0Def)),
				Basic())
			notNonnegative := a.Have(
				"the degree of X is not nonnegative",
				"¬(&0 ≤ curve_degree(field_ring(L), k, A₀, A₁, A₀₁, X))",
				ByArith(negative))
			onlyZero := a.Have(
				"so no section of X is nonzero",
				"∀s:A. s ∈ fst(X) ∩ snd(X) ⇒ s = L.zero",
				a.ForEach(func(s *Expr[A]) Action {
					return By(
						L,
						curve,
						invertible,
						notNonnegative,
						SectionDegreeNonneg.At(fieldOps, k, A0, A1, A01, t, s, X))
				}))
			zeroAlone := a.Have(
				"H⁰ is zero alone",
				"lattice_pair_h0(«fieldModule», X).carrier = {L.zero}",
				BySets(onlyZero, carrier, zeroSection))
			a.Show(
				"so ℓ(X) = 0",
				By(criterion, zeroAlone, lattice_pair.LatticePairH0DimDef.At(overlap, k, vectors, X)))
		}),
})}

// ---------------------------------------------------------------------------
// Divisors
// ---------------------------------------------------------------------------

// CurveDivisorDef — `curve_divisor(L, k, A₀, A₁, A₀₁, D)`: D is a divisor
// of the curve, an integer multiplicity at every pair of subsets of the
// field, nonzero at finitely many pairs and only at regular points.
var CurveDivisorDef = curveDivisorDefThm{family.Define(registry.DefEntry{
	Name:     "CurveDivisorDef",
	Key:      "prop_7330d3b89bfd7e79",
	Const:    "curve_divisor",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "A point is its ideal pair, so a divisor is a function on pairs of subsets; " +
		"at every pair that is not a regular point it is zero. Points that are rational but " +
		"not regular — the cusp of k[u², u³] — carry no multiplicity: their ideals are not " +
		"invertible, so a twist there leaves the invertible pairs and P · P⁻¹ is not O.",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀k:set(A). " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀A₀₁:set(A). " +
			"∀D:(prod(set(A), set(A)) → int). " +
			"    curve_divisor(R, k, A₀, A₁, A₀₁, D) ⇔ " +
			"    finite(fun_support(int_of_num(0), D)) ∧ " +
			"    (∀P:prod(set(A), set(A)). D(P) ≠ &0 ⇒ biaffine_regular_point(R, k, A₀, A₁, A₀₁, P))",
	},
})}

// CurveDivisorDegreeDef — `curve_divisor_degree(D)`, written deg D: the
// sum of the multiplicities of D over its support.
var CurveDivisorDegreeDef = curveDivisorDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "CurveDivisorDegreeDef",
	Key:   "prop_8c1105a946c38751",
	Const: "curve_divisor_degree",
	Type:  "(prod(set(A), set(A)) → int) → int",
	Equations: []string{
		"∀D:(prod(set(A), set(A)) → int). " +
			"    curve_divisor_degree(D) = int_sum(fun_support(int_of_num(0), D), D)",
	},
})}

// CurveDivisorPairDef — `curve_divisor_pair(L, A₀, A₁, A₀₁, D)`, written
// O(D): the product over the support of D of the powers P^(−D(P)) of its
// points' ideal pairs, P⁻¹ = O(P) taken D(P) times where D(P) > 0 and P
// itself −D(P) times where D(P) < 0, starting from the structure pair. The
// product is a fold over the support, each step multiplying by the power
// at one pair; a pair that is not invertible leaves the product alone, so
// the steps commute on invertible pairs and the fold does not depend on
// an order.
var CurveDivisorPairDef = curveDivisorPairDefThm{family.Define(registry.DefEntry{
	Name:  "CurveDivisorPairDef",
	Key:   "prop_a467d70aa1c02779",
	Const: "curve_divisor_pair",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"(prod(set(A), set(A)) → int) → " +
		"prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "The fold is determined because its steps commute on the invertible pairs, a " +
		"set holding the structure pair and closed under every step (FiniteRecursionWithin): at an " +
		"invertible P the step multiplies by an invertible power, and products of lattice pairs " +
		"commute and associate. A divisor's support is regular points, where the guard holds. They " +
		"commute only at a curve datum, which MulAssoc and MulComm need; the guard makes a " +
		"non-invertible pair a neutral step, so the steps at any two distinct pairs commute.",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀D:(prod(set(A), set(A)) → int). " +
			"    curve_divisor_pair(R, A₀, A₁, A₀₁, D) = " +
			"    set_fold(λP:prod(set(A), set(A)). λN:prod(set(A), set(A)). " +
			"            COND(invertible_lattice_pair(R, A₀, A₁, A₀₁, P), " +
			"                lattice_pair_mul(R, " +
			"                    A₀, " +
			"                    A₁, " +
			"                    COND(&0 ≤ D(P), " +
			"                        monoid_pow((λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
			"                                lattice_pair_mul(R, A₀, A₁, X, Y)), " +
			"                            (A₀, A₁), " +
			"                            lattice_pair_inverse(R, A₀, A₁, P), " +
			"                            num_of_int(D(P))), " +
			"                        monoid_pow((λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
			"                                lattice_pair_mul(R, A₀, A₁, X, Y)), " +
			"                            (A₀, A₁), " +
			"                            P, " +
			"                            num_of_int(-D(P)))), " +
			"                    N), " +
			"                N), " +
			"        fun_support(int_of_num(0), D), " +
			"        (A₀, A₁))",
	},
})}

// DivisorFoldRecursion — the fold that builds a divisor's pair, over any
// finite set of pairs, starts at O, takes a new pair by its step, and is
// invertible: the steps keep the invertible pairs and commute there.
var DivisorFoldRecursion = divisorFoldRecursionThm{family.Add(registry.ProofEntry{
	Name: "DivisorFoldRecursion",
	Key:  "prop_ee108a14ef41a908",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "set_fold(«divisorStep», ∅, (A₀, A₁)) = (A₀, A₁) ∧ " +
			"(∀P:prod(set(A), set(A)). ∀s:set(prod(set(A), set(A))). " +
			"    finite(s) ∧ P ∉ s ⇒ " +
			"    set_fold(«divisorStep», insert(P, s), (A₀, A₁)) = " +
			"    «divisorStep»(P, set_fold(«divisorStep», s, (A₀, A₁)))) ∧ " +
			"(∀s:set(prod(set(A), set(A))). finite(s) ⇒ «wdInvertible»(set_fold(«divisorStep», s, (A₀, A₁))))",
		Abbrev: Abbrev{
			{Name: "divisorStep", Text: "λP:prod(set(A), set(A)). λN:prod(set(A), set(A)). " +
				"    COND(«wdInvertible»(P), " +
				"        «wdMul»(COND(&0 ≤ D(P), " +
				"                monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
				"                        lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), " +
				"                    (A₀, A₁), " +
				"                    «wdInverse»(P), " +
				"                    num_of_int(D(P))), " +
				"                monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
				"                        lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), " +
				"                    (A₀, A₁), " +
				"                    P, " +
				"                    num_of_int(-D(P)))), " +
				"            N), " +
				"        N)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			datum Fact,
		) {
			data := a.Conjuncts(
				GroupPremises(datum, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, structureInvertible := data[0], data[1], data[5]
			O, structure := a.LetAs[_LatticePair]("O", "(A₀, A₁)")
			_, multiplication := a.LetAs[Op[_LatticePair]](
				"mul", "λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). «wdMul»(X, Y)")

			monoid := a.Have(
				"the invertible pairs form a commutative monoid under the product, with O its unit",
				"comm_monoid_on({N:prod(set(A), set(A)) | «wdInvertible»(N)}, mul, O)",
				By(
					multiplication,
					structure,
					overlapInField,
					biaffine,
					invertible_lattice_pair.InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t)))

			_, signedPower := a.LetAs[Fun[_LatticePair, _LatticePair]](
				"power",
				"λP:prod(set(A), set(A)). "+
					"    COND(&0 ≤ D(P), "+
					"        monoid_pow(mul, O, «wdInverse»(P), num_of_int(D(P))), "+
					"        monoid_pow(mul, O, P, num_of_int(-D(P))))")
			signedPowers := a.Have(
				"the signed power at an invertible pair is invertible",
				"∀P:prod(set(A), set(A)). «wdInvertible»(P) ⇒ «wdInvertible»(power(P))",
				Derive(func(b *Argument) {
					P := b.FixAs[_LatticePair]("P")
					invertible := b.Assume()
					b.Cases(b.TermAs[Bool]("&0 ≤ D(P)"))
					b.When(
						"a nonnegative multiplicity uses a power of the inverse pair",
						func(c *Argument, nonnegative Fact) {
							c.Show(
								"the inverse pair and all its powers are invertible",
								Simp(Fwd(signedPower)),
								By(
									comm_monoid.PowIn.Read(monoid).AsFact().At(
										c.TermAs[_LatticePair]("«wdInverse»(P)"), c.TermAs[Nat]("num_of_int(D(P))")),
									overlapInField,
									biaffine,
									invertible,
									invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P)))
						})
					b.Otherwise(
						"a negative multiplicity uses a power of the pair itself",
						func(c *Argument, negative Fact) {
							c.Show(
								"this natural power is invertible",
								Simp(Fwd(signedPower)),
								By(comm_monoid.PowIn.Read(monoid).AsFact().At(P, c.TermAs[Nat]("num_of_int(-D(P))")), invertible))
						})
				}))

			step, divisorStep := a.LetAs[Op[_LatticePair]](
				"step",
				"λP:prod(set(A), set(A)). λN:prod(set(A), set(A)). COND(«wdInvertible»(P), mul(power(P), N), N)")
			invertibles, invertiblePairs := a.LetAs[Set[_LatticePair]](
				"invertibles", "{N:prod(set(A), set(A)) | «wdInvertible»(N)}")
			preserves := a.Have(
				"each divisor step preserves the invertible pairs",
				"∀P N:prod(set(A), set(A)). N ∈ invertibles ⇒ step(P, N) ∈ invertibles",
				Derive(func(b *Argument) {
					P, N := b.FixAs[_LatticePair]("P"), b.FixAs[_LatticePair]("N")
					inInvertibles := b.Assume()
					b.Cases(b.TermAs[Bool]("«wdInvertible»(P)"))
					b.When(
						"an invertible P contributes an invertible factor",
						func(c *Argument, invertible Fact) {
							c.Show(
								"the product stays among the invertible pairs",
								Simp(Fwd(invertiblePairs), Fwd(divisorStep)),
								invertiblePairs.Rw(),
								BySets(
									Normalized,
									signedPowers.At(P),
									inInvertibles,
									invertible,
									comm_monoid.OpIn.Read(monoid).AsFact().At(c.TermAs[_LatticePair]("power(P)"), N)))
						})
					b.Otherwise(
						"a noninvertible P has the identity step",
						func(c *Argument, noninvertible Fact) {
							c.Show(
								"the pair stays among the invertible pairs",
								Simp(Fwd(divisorStep)),
								By(inInvertibles))
						})
				}))
			commutes := a.Have(
				"any two divisor steps commute on the invertible pairs",
				"∀P Q N:prod(set(A), set(A)). N ∈ invertibles ⇒ step(P, step(Q, N)) = step(Q, step(P, N))",
				Derive(func(b *Argument) {
					P, Q, N := b.FixAs[_LatticePair]("P"), b.FixAs[_LatticePair]("Q"), b.FixAs[_LatticePair]("N")
					inInvertibles := b.Assume()
					b.Do(invertiblePairs.Rw(), Simp(Fwd(divisorStep)))
					pInvertible := b.Assuming(
						b.Term("«wdInvertible»(P)"),
						"a noninvertible P acts as the identity",
						Derive(func(c *Argument) {
							c.Show(
								"the two orders agree",
								By(c.Hyp("¬«wdInvertible»(P)")))
						}))
					qInvertible := b.Assuming(
						b.Term("«wdInvertible»(Q)"),
						"a noninvertible Q acts as the identity",
						Derive(func(c *Argument) {
							c.Show(
								"the two orders agree",
								By(c.Hyp("¬«wdInvertible»(Q)")))
						}))
					b.Show(
						"the two invertible signed powers interchange",
						BySets(
							Normalized,
							comm_monoid.LeftCommOn.Read(monoid).AsFact().At(
								b.TermAs[_LatticePair]("power(P)"), b.TermAs[_LatticePair]("power(Q)"), N),
							signedPowers.At(P),
							signedPowers.At(Q),
							inInvertibles,
							pInvertible,
							qInvertible))
				}))
			base := a.Have(
				"the structure pair lies in the invertible pairs",
				"O ∈ invertibles",
				invertiblePairs.Rw(),
				BySets(structureInvertible))
			recursion := a.Have(
				"closure and commutation give the finite recursion equations",
				"set_fold(step, ∅, O) = O ∧ "+
					"(∀P:prod(set(A), set(A)). ∀s:set(prod(set(A), set(A))). "+
					"    finite(s) ⇒ "+
					"    set_fold(step, insert(P, s), O) = "+
					"    COND(P ∈ s, set_fold(step, s, O), step(P, set_fold(step, s, O))))",
				By(commutes, preserves, base, cardinality.FiniteRecursionWithin.At(step, O, invertibles)))
			folds := a.Have(
				"every finite fold lies among the invertible pairs",
				"∀s:set(prod(set(A), set(A))). finite(s) ⇒ set_fold(step, s, O) ∈ invertibles",
				Derive(func(b *Argument) {
					b.FixAs[Set[_LatticePair]]("s")
					finite := b.Assume()
					b.Show(
						"induct over the finite set by adjoining a fresh point",
						ByInduction(finite_set.FiniteInductFresh, finite,
							Case(
								"the empty fold is the invertible structure pair",
								Simp(Fwd(recursion)),
								By(base)),
							Case(
								"adjoining a fresh point preserves the invariant",
								Derive(func(c *Argument) {
									P := c.FixAs[_LatticePair]("P")
									c.FixAs[Set[_LatticePair]]("u")
									fresh := c.Assume()
									c.Show(
										"apply the step to the inductively invertible fold",
										Simp(Fwd(recursion)),
										By(preserves.At(P, c.TermAs[_LatticePair]("set_fold(step, u, O)")), fresh))
								}))))
				}))
			a.Show(
				"the fold of the divisor steps starts at O, takes a new pair by its step, and stays invertible",
				Simp(Rev(multiplication), Rev(signedPower), Rev(divisorStep)),
				invertiblePairs.Rw(),
				BySets(Normalized, recursion, folds))
		}),
})}

// DivisorLatticeInvertible — the pair of a divisor is an invertible pair.
var DivisorLatticeInvertible = divisorLatticeInvertibleThm{family.Add(registry.ProofEntry{
	Name: "DivisorLatticeInvertible",
	Key:  "prop_a040adc45cea588e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdDivisor»(D)",
		},
		Conclusion: "«wdInvertible»(«wdDivisorPair»(D))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve datum",
				"D is a divisor")
			support := a.TermAs[Set[_LatticePair]]("fun_support(int_of_num(0), D)")
			fold := a.Conjuncts(
				GroupPremises(given[0], DivisorFoldRecursion.Read(L).At(k, A0, A1, A01, t, D)),
				"the empty fold is O",
				"a new pair applies its step to the fold before it",
				"every finite fold is invertible")
			a.Show(
				"O(D) is the fold over the finite support, so it is invertible",
				Unfold(CurveDivisorPairDef),
				By(
					given[1],
					CurveDivisorDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), k, A0, A1, A01, D),
					fold[2].At(support)))
		}),
})}

// DivisorLatticeDegree — the pair of a divisor has the divisor's degree.
var DivisorLatticeDegree = divisorLatticeDegreeThm{family.Add(registry.ProofEntry{
	Name: "DivisorLatticeDegree",
	Key:  "prop_1723202762a2d797",
	Reading: "A point counts with degree one because its ideal pair is invertible " +
		"with residue field k: deg O(P) = deg O + 1 (DegreeTwist), so deg P = −1 and " +
		"deg P^(−n) = n by additivity. At a point of higher residue degree the count " +
		"would be that degree; the divisors here are on rational points.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdDivisor»(D)",
		},
		Conclusion: "«wdDegree»(«wdDivisorPair»(D)) = curve_divisor_degree(D)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve datum",
				"D is a divisor")
			data := a.Conjuncts(
				GroupPremises(given[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine, structureInvertible := data[0], data[1], data[5]
			O, structure := a.LetAs[_LatticePair]("O", "(A₀, A₁)")
			_, multiplication := a.LetAs[Op[_LatticePair]](
				"mul", "λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). «wdMul»(X, Y)")

			monoid := a.Have(
				"the invertible pairs form a commutative monoid under the product, with O its unit",
				"comm_monoid_on({N:prod(set(A), set(A)) | «wdInvertible»(N)}, mul, O)",
				By(
					multiplication,
					structure,
					overlapInField,
					biaffine,
					invertible_lattice_pair.InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t)))

			powers := a.Have(
				"the degree of a natural power of an invertible pair is the exponent times its degree",
				Statement{
					Binders:    "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{"«wdInvertible»(P)"},
					Conclusion: "∀n:num. «wdDegree»(monoid_pow(mul, O, P, n)) = int_of_num(n) * «wdDegree»(P)",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_LatticePair]("P")
					invertible := b.Assume()
					n := b.FixAs[Nat]("n")
					b.Induct(n)
					b.Base(
						"the zeroth power is O, of degree zero",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ByArith(structure, DegreeStructure.Read(L).At(k, A0, A1, A01)))
					b.Step(
						"adjoin one invertible factor and add its degree",
						func(c *Argument, ih Fact) {
							naturalPower := c.TermAs[_LatticePair]("monoid_pow(mul, O, P, n)")
							degree := c.TermAs[Int]("«wdDegree»(P)")
							powerInvertible := c.Have(
								"the power is invertible, a power in the monoid of invertible pairs",
								"«wdInvertible»(monoid_pow(mul, O, P, n))",
								By(comm_monoid.PowIn.Read(monoid).AsFact().At(P, c.TermAs[Nat]("n")), invertible))
							c.Show(
								"the successor's degree is the degree of P plus that of the power",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								ByArith(
									multiplication,
									invertible,
									powerInvertible,
									ih,
									given[0],
									DegreeAdditive.Read(L).At(k, A0, A1, A01, t, P, naturalPower),
									int_embed.OfNumSuc.At(c.TermAs[Nat]("n")),
									int_real_lift.RightDistrib.At(c.TermAs[Int]("n"), c.TermAs[Int]("&1"), degree)))
						})
				}))

			pointDegrees := a.Have(
				"a regular point has degree minus one and its inverse has degree one",
				Statement{
					Binders:    "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{"«wdPoint»(P)"},
					Conclusion: "«wdInvertible»(P) ∧ " +
						"«wdInvertible»(«wdInverse»(P)) ∧ " +
						"«wdDegree»(P) = -&1 ∧ " +
						"«wdDegree»(«wdInverse»(P)) = &1",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_LatticePair]("P")
					regular := b.Assume()
					ring := b.TermAs[RingOps[A]]("field_ring(L)")
					invertible := b.Have(
						"the regular point is invertible",
						"«wdInvertible»(P)",
						By(regular, lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, P)))
					inverse := b.TermAs[_LatticePair]("«wdInverse»(P)")
					inverseInvertible := b.Have(
						"its inverse is invertible",
						"«wdInvertible»(«wdInverse»(P))",
						By(
							overlapInField,
							biaffine,
							invertible,
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P)))
					inverseDegree := b.Have(
						"twisting O shows that the inverse point has degree one",
						"«wdDegree»(«wdInverse»(P)) = &1",
						Derive(func(c *Argument) {
							twist := c.Have(
								"the product of the inverse point with O raises degree by one",
								"«wdDegree»(«wdMul»(«wdInverse»(P), O)) = «wdDegree»(O) + &1",
								By(
									given[0],
									structureInvertible,
									regular,
									DegreeTwist.Read(L).At(k, A0, A1, A01, t, O, P),
									lattice_pair_twist.LatticePairTwistDef.At(ring, A0, A1, O, P)))
							c.Show(
								"cancel the degree of O from product additivity",
								ByArith(
									twist,
									given[0],
									structureInvertible,
									inverseInvertible,
									DegreeAdditive.Read(L).At(k, A0, A1, A01, t, inverse, O)))
						}))
					degree := b.Have(
						"the point's degree is the negative of its inverse's",
						"«wdDegree»(P) = -&1",
						ByArith(inverseDegree, given[0], invertible, DegreeInverse.Read(L).At(k, A0, A1, A01, t, P)))
					b.Show(
						"both degree values and invertibility statements hold",
						By(invertible, inverseInvertible, degree, inverseDegree))
				}))

			_, signedPower := a.LetAs[Fun[_LatticePair, _LatticePair]](
				"power",
				"λP:prod(set(A), set(A)). "+
					"    COND(&0 ≤ D(P), "+
					"        monoid_pow(mul, O, «wdInverse»(P), num_of_int(D(P))), "+
					"        monoid_pow(mul, O, P, num_of_int(-D(P))))")
			signedDegrees := a.Have(
				"the signed factor at a regular point is invertible and has its multiplicity as degree",
				"∀P:prod(set(A), set(A)). «wdPoint»(P) ⇒ «wdInvertible»(power(P)) ∧ «wdDegree»(power(P)) = D(P)",
				Derive(func(b *Argument) {
					P := b.FixAs[_LatticePair]("P")
					regular := b.Assume()
					b.Cases(b.TermAs[Bool]("&0 ≤ D(P)"))
					b.When(
						"a nonnegative multiplicity uses the inverse point",
						func(c *Argument, nonnegative Fact) {
							c.Show(
								"a power of the invertible, degree-one inverse is invertible and has degree D(P)",
								Simp(Fwd(signedPower)),
								ByArith(
									powers.At(c.TermAs[_LatticePair]("«wdInverse»(P)"), c.TermAs[Nat]("num_of_int(D(P))")),
									comm_monoid.PowIn.Read(monoid).AsFact().At(
										c.TermAs[_LatticePair]("«wdInverse»(P)"), c.TermAs[Nat]("num_of_int(D(P))")),
									pointDegrees.At(P),
									regular,
									nonnegative,
									int_embed.NumOfIntSection.At(c.TermAs[Int]("D(P)"))))
						})
					b.Otherwise(
						"a negative multiplicity uses the point itself",
						func(c *Argument, negative Fact) {
							nonnegative := c.Have(
								"the negated multiplicity is nonnegative",
								"&0 ≤ -D(P)",
								ByArith(negative))
							c.Show(
								"the power is invertible, and the degree minus one cancels the sign of the exponent",
								Simp(Fwd(signedPower)),
								ByArith(
									powers.At(P, c.TermAs[Nat]("num_of_int(-D(P))")),
									comm_monoid.PowIn.Read(monoid).AsFact().At(P, c.TermAs[Nat]("num_of_int(-D(P))")),
									pointDegrees.At(P),
									regular,
									nonnegative,
									int_embed.NumOfIntSection.At(c.TermAs[Int]("-D(P)"))))
						})
				}))

			_, divisorStep := a.LetAs[Op[_LatticePair]](
				"step",
				"λP:prod(set(A), set(A)). λN:prod(set(A), set(A)). COND(«wdInvertible»(P), mul(power(P), N), N)")
			fold := a.Conjuncts(
				a.Have(
					"the fold of the steps starts at O, takes a new pair by its step, and stays invertible",
					"set_fold(step, ∅, O) = O ∧ "+
						"(∀P:prod(set(A), set(A)). ∀s:set(prod(set(A), set(A))). "+
						"    finite(s) ∧ P ∉ s ⇒ set_fold(step, insert(P, s), O) = step(P, set_fold(step, s, O))) ∧ "+
						"(∀s:set(prod(set(A), set(A))). finite(s) ⇒ «wdInvertible»(set_fold(step, s, O)))",
					Simp(Fwd(divisorStep), Fwd(signedPower), Fwd(multiplication), Fwd(structure)),
					By(given[0], DivisorFoldRecursion.Read(L).At(k, A0, A1, A01, t, D))),
				"the empty fold is O",
				"a new pair applies its step to the fold before it",
				"every finite fold is invertible")
			support, supportSet := a.LetAs[Set[_LatticePair]]("support", "fun_support(int_of_num(0), D)")
			supportData := a.Have(
				"the divisor has finite support consisting of regular points",
				"finite(support) ∧ (∀P:prod(set(A), set(A)). P ∈ support ⇒ «wdPoint»(P))",
				BySets(
					Normalized,
					supportSet,
					given[1],
					CurveDivisorDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), k, A0, A1, A01, D)))
			degrees := a.Have(
				"a fold over part of the support has degree the sum of its multiplicities",
				Statement{
					Binders:    "∀s:set(prod(set(A), set(A))).",
					Hypotheses: []string{"finite(s)"},
					Conclusion: "s ⊆ support ⇒ «wdDegree»(set_fold(step, s, O)) = sum(s, D)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[_LatticePair]]("s")
					finite := b.Assume()
					b.Show(
						"induct by adjoining a fresh support point",
						ByInduction(finite_set.FiniteInductFresh, finite,
							Case(
								"the empty fold is O and the empty sum is zero",
								Derive(func(c *Argument) {
									c.Assume()
									c.Show(
										"the empty fold has degree zero",
										Simp(Fwd(fold[0]), Fwd(int_sum.IntSumClauses)),
										By(Normalized, structure, DegreeStructure.Read(L).At(k, A0, A1, A01)))
								})),
							Case(
								"adjoining a fresh point adds its multiplicity to the degree",
								Derive(func(c *Argument) {
									P := c.FixAs[_LatticePair]("P")
									u := c.FixAs[Set[_LatticePair]]("u")
									fresh := c.Assume()
									included := c.Assume()
									inSupport := c.Have(
										"the previous set and the new point lie in the support",
										"u ⊆ support ∧ P ∈ support",
										BySets(included))
									previous := c.Have(
										"the induction hypothesis applies to the previous support subset",
										"«wdDegree»(set_fold(step, u, O)) = sum(u, D)",
										By(fresh, inSupport))
									points := c.Conjuncts(
										supportData,
										"the support is finite",
										"every support point is regular")
									factor := c.Have(
										"the new factor is invertible and has degree D(P)",
										"«wdInvertible»(P) ∧ «wdInvertible»(power(P)) ∧ «wdDegree»(power(P)) = D(P)",
										By(inSupport, points[1].At(P), pointDegrees.At(P), signedDegrees.At(P)))
									oldFold := c.TermAs[_LatticePair]("set_fold(step, u, O)")
									oldInvertible := c.Have(
										"the previous fold is invertible",
										"«wdInvertible»(set_fold(step, u, O))",
										By(fresh, fold[2].At(u)))
									stepDegree := c.Have(
										"the new step adds D(P) to the previous degree",
										"«wdDegree»(step(P, set_fold(step, u, O))) = D(P) + sum(u, D)",
										Derive(func(d *Argument) {
											active := d.Have(
												"the guard is true at this support point",
												"step(P, set_fold(step, u, O)) = mul(power(P), set_fold(step, u, O))",
												By(Normalized, divisorStep, factor))
											product := d.Have(
												"product additivity computes the new degree",
												"«wdDegree»(mul(power(P), set_fold(step, u, O))) = D(P) + sum(u, D)",
												ByArith(
													Normalized,
													multiplication,
													given[0],
													factor,
													oldInvertible,
													previous,
													DegreeAdditive.Read(L).At(k, A0, A1, A01, t, d.TermAs[_LatticePair]("power(P)"), oldFold)))
											d.Show(
												"replace the guarded step by its active product",
												By(Normalized, active, product))
										}))
									c.Show(
										"the fresh insertion adds D(P) to the degree",
										Simp(Fwd(fold[1]), Fwd(int_sum.IntSumClauses)),
										By(stepDegree, fresh))
								}))))
				}))
			degree := a.Have(
				"the fold over the whole support has the required degree",
				"«wdDegree»(set_fold(step, support, O)) = sum(support, D)",
				By(supportData, degrees.At(support), set_order.SubsetRefl.At(support)))
			pair := a.Have(
				"the divisor pair is the guarded fold over its support",
				"«wdDivisorPair»(D) = set_fold(step, support, O)",
				By(
					multiplication,
					signedPower,
					divisorStep,
					supportSet,
					structure,
					CurveDivisorPairDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, A01, D)))
			divisorDegree := a.Have(
				"the divisor degree is the sum over the same support",
				"curve_divisor_degree(D) = sum(support, D)",
				By(supportSet, CurveDivisorDegreeDef.At(D)))
			a.Show(
				"the divisor pair and divisor have the same degree",
				By(Normalized, pair, divisorDegree, degree))
		}),
})}

// DivisorLatticeAdd — the sum of two divisors is a divisor, and its pair
// is the product of their pairs.
var DivisorLatticeAdd = divisorLatticeAddThm{family.Add(registry.ProofEntry{
	Name: "DivisorLatticeAdd",
	Key:  "prop_554d34b0eb56ec1e",
	Reading: "The support of D + E may be smaller than the union of the " +
		"supports, where multiplicities cancel; there the two powers P^(−a) " +
		"and P^a multiply to O (InvertibleLatticeInverse), which is why the " +
		"product is computed over the union and the cancelled points drop out.",
	Deps: []registry.EntryLike{
		CurveDivisorPairDef,
		CurveDivisorDef,
		DivisorLatticeInvertible,
		cardinality.FiniteRecursionWithin,
		cardinality.FoldOfAgreeingStepsWithin,
		finite_set.FiniteInductFresh,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticePairDef,
		invertible_lattice_pair.InvertibleLatticeProduct,
		algebraic_curve.CurveLatticeData,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdDivisor»(D)",
			"«wdDivisor»(E)",
		},
		Conclusion: "«wdDivisor»(λP:prod(set(A), set(A)). D(P) + E(P)) ∧ " +
			"«wdDivisorPair»(λP:prod(set(A), set(A)). D(P) + E(P)) = " +
			"«wdMul»(«wdDivisorPair»(D), «wdDivisorPair»(E))",
	},
		"the support of D + E lies in the union of the supports, finite and of regular points "+
			"(CurveDivisorDef); at an invertible P the integer powers add, P^(−a) · P^(−b) = P^(−(a + "+
			"b)), by MulAssoc, MulComm, MulOne and P · P⁻¹ = O (InvertibleLatticeInverse); so each fold "+
			"may be taken over the union of the supports, a pair outside a divisor's support contributing "+
			"P⁰ = O (FoldOfAgreeingStepsWithin, MulOne), and induction over the union (FiniteInductFresh, "+
			"FiniteRecursionWithin) splits the fold of the sum into the product of the two folds"),
})}

// DivisorLatticePoint — the divisor of one regular point P with
// multiplicity n has degree n, and its pair is O(P) at n = 1 and P at
// n = −1.
var DivisorLatticePoint = divisorLatticePointThm{family.Add(registry.ProofEntry{
	Name: "DivisorLatticePoint",
	Key:  "prop_b33d080fcbe8bbf7",
	Reading: "The fold over the one-point support is one step: O(P) = P⁻¹ " +
		"· O, which is the twist of O at P, and O(−P) = P · O = P. n = 0 is " +
		"allowed: the divisor is zero, its support empty, and its degree &0.",
	Deps: []registry.EntryLike{
		CurveDivisorPairDef,
		CurveDivisorDef,
		CurveDivisorDegreeDef,
		algebraic_curve.CurveLatticeData,
		cardinality.FiniteRecursionWithin,
		int_sum.IntSumClauses,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.InvertibleLatticePairDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticeProduct,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:int.",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdPoint»(P)",
		},
		Conclusion: "«wdDivisor»(λQ:prod(set(A), set(A)). COND(Q = P, n, int_of_num(0))) ∧ " +
			"curve_divisor_degree(λQ:prod(set(A), set(A)). COND(Q = P, n, int_of_num(0))) = n ∧ " +
			"«wdDivisorPair»(λQ:prod(set(A), set(A)). COND(Q = P, int_of_num(1), int_of_num(0))) = " +
			"«wdTwist»((A₀, A₁), P) ∧ " +
			"«wdDivisorPair»(λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), int_of_num(0))) = P",
	},
		"the support is {P} for n ≠ &0 and ∅ at n = &0, finite and regular (CurveDivisorDef), and the "+
			"sum over it is n (IntSumClauses); the fold over {P} is one step (FiniteRecursionWithin, its "+
			"set the invertible pairs as in DivisorLatticeInvertible): at n = &1 it is P⁻¹ · O = "+
			"lattice_pair_twist(O, P) (LatticePairTwistDef), at n = -&1 it is P · O = P (MulComm, MulOne; "+
			"P is invertible by BiaffineRegularPointDef), the first power being the base times the unit"),
})}

// PrincipalDivisorDegree — a divisor whose pair is a nonzero multiple of
// the structure pair has degree zero: principal divisors have degree zero.
// The degree of D is that of its pair a · O, scaling by a nonzero a does
// not change the degree of the invertible O, and O has degree zero.
var PrincipalDivisorDegree = principalDivisorDegreeThm{family.Add(registry.ProofEntry{
	Name: "PrincipalDivisorDegree",
	Key:  "prop_73e7f373e5d6d00c",
	Reading: "O(D) = a · O says D is the divisor of inv(a): its sections are the " +
		"multiples of a, the functions with poles bounded by D. The divisor of a function " +
		"is not formed here, so principality is stated through the pair. The hypothesis a " +
		"≠ zero is implied by the others — O(D) is invertible (DivisorLatticeInvertible) " +
		"and zero · O = ({zero}, {zero}) is not — and is stated because DegreeScale asks it.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int). ∀a:A.",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdDivisor»(D)",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"«wdDivisorPair»(D) = lattice_pair_scale(a, (A₀, A₁))",
		},
		Conclusion: "curve_divisor_degree(D) = &0",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			a *Expr[A],
			h Fact,
		) {
			given := arg.Conjuncts(
				h,
				"the curve datum",
				"D is a divisor",
				"a lies in L",
				"a is nonzero",
				"the pair of D is a times O")
			curve, divisor, nonzero, principal := given[0], given[1], given[3], given[4]
			scalar := arg.MemberOf[on.L](a, given[2])
			structure := arg.TermAs[_LatticePair]("(A₀, A₁)")
			arg.Show(
				"D has degree zero",
				CalcEq(
					Leg(
						arg.TermAs[Int]("«wdDegree»(«wdDivisorPair»(D))"),
						"a divisor has the degree of its pair",
						By(curve, divisor, DivisorLatticeDegree.Read(L).At(k, A0, A1, A01, t, D))),
					Leg(
						arg.TermAs[Int]("«wdDegree»(lattice_pair_scale(a, (A₀, A₁)))"),
						"the pair of D is a times O",
						By(Normalized, principal)),
					Leg(
						arg.TermAs[Int]("«wdDegree»((A₀, A₁))"),
						"a nonzero multiple of the invertible structure pair has its degree",
						By(
							curve,
							nonzero,
							algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
							DegreeScale.Read(L).At(k, A0, A1, A01, t, scalar, structure))),
					FinalLeg(
						"the structure pair has degree zero",
						Cite(DegreeStructure.Read(L))),
				))
		}),
})}
