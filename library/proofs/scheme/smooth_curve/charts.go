package smooth_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothCurveSwap — a smooth curve read from its other chart: the coordinate
// inverted and the charts exchanged, it is the same smooth curve. CurveSwap
// exchanges the curve datum, the two normality clauses trade places, and the
// rest names no chart.
var SmoothCurveSwap = smoothCurveSwapThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveSwap",
	Key:  "prop_5b493bb70b6a987e",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"the curve swaps its charts, and with them the two normality clauses",
				Simp(Fwd(SmoothFiniteFieldCurveDef)),
				By(
					curve,
					SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					SmoothCurveFiniteConstants.Read(curve),
					SmoothCurveChartZeroNormal.Read(curve),
					SmoothCurveChartOneNormal.Read(curve),
					algebraic_curve.CurveSwap.Read(L).At(k, A0, A1, A01, t)))
		}),
})}

// SmoothCurveOverLine — what a smooth curve over L gives first: its charts make
// a curve over the line of t.
var SmoothCurveOverLine = smoothCurveOverLineThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveOverLine",
	Key:  "prop_d71cc3819dbeec1c",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "curve_over_line(L, k, t, A₀, A₁, A₀₁)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"the curve is a clause of the smooth curve",
				By(a.Unfolded(curve, SmoothFiniteFieldCurveDef)))
		}),
})}

// SmoothCurveFiniteConstants — the constants k of a smooth curve are finite.
var SmoothCurveFiniteConstants = smoothCurveFiniteConstantsThm{family.Add(registry.ProofEntry{
	Name:  "SmoothCurveFiniteConstants",
	Key:   "prop_a0507d8c2cb20b17",
	Build: SmoothFiniteFieldCurveDef.Entry().Conjunct("finite(k)"),
})}

// SmoothCurveChartZeroNormal — the chart A₀ of a smooth curve is integrally
// closed in its function field.
var SmoothCurveChartZeroNormal = smoothCurveChartZeroNormalThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveChartZeroNormal",
	Key:  "prop_665337129f6890c6",
	Build: SmoothFiniteFieldCurveDef.Entry().Conjunct(
		"integrally_closed_in(restrict_ring(field_ring(R), A₀), R.carrier)"),
})}

// SmoothCurveChartOneNormal — the chart A₁ of a smooth curve is integrally
// closed in its function field.
var SmoothCurveChartOneNormal = smoothCurveChartOneNormalThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveChartOneNormal",
	Key:  "prop_b0ff6e31c288a385",
	Build: SmoothFiniteFieldCurveDef.Entry().Conjunct(
		"integrally_closed_in(restrict_ring(field_ring(R), A₁), R.carrier)"),
})}

// ChartCommRing — a chart of a smooth curve is a ring under L's operations: it
// is a subring of L.
var ChartCommRing = chartCommRingThm{family.Add(registry.ProofEntry{
	Name: "ChartCommRing",
	Key:  "prop_3060349e423af61c",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "comm_ring_on(restrict_ring(field_ring(L), A₀))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"as a subring of L, the chart is a ring",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t),
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A0)))
		}),
})}

// OverlapCommRing — the overlap of a smooth curve is a ring under L's
// operations: it is a subring of L.
var OverlapCommRing = overlapCommRingThm{family.Add(registry.ProofEntry{
	Name: "OverlapCommRing",
	Key:  "prop_967763cdf020392",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "comm_ring_on(restrict_ring(field_ring(L), A₀₁))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"as a subring of L, the overlap is a ring",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t),
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
		}),
})}

// ChartSubring — a chart of a smooth curve: the constants are a subfield of L
// lying in the chart, and the chart is a subring of L. Each is a clause of the
// curve over the line.
var ChartSubring = chartSubringThm{family.Add(registry.ProofEntry{
	Name: "ChartSubring",
	Key:  "prop_78c36818844f03d6",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "subfield(L, k) ∧ k ⊆ A₀ ∧ subring(field_ring(L), A₀)",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			line := a.Have(
				"the constants are a subfield inside the polynomials, inside the chart, a subring of L",
				"subfield(L, k) ∧ subring(field_ring(L), A₀) ∧ k ⊆ «polynomials» ∧ «polynomials» ⊆ A₀",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			a.Show(
				"the constants lie in the polynomials, which lie in the chart",
				BySets(line))
		}),
})}

// NormalChartsRegular — a curve over the projective line over a finite field
// k whose two charts are integrally closed in L has a function field regular
// over k. L is finite over k(t), so it is regular over its field of constants,
// the elements of L algebraic over k. Such an element is integral over k,
// which both charts hold, so it lies in either chart, and the charts meet in
// k: the constants are k itself.
var NormalChartsRegular = normalChartsRegularThm{family.Add(registry.ProofEntry{
	Name: "NormalChartsRegular",
	Key:  "prop_c4e1c637a01ea498",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"finite(k)",
			"integrally_closed_in(restrict_ring(field_ring(L), A₀), L.carrier)",
			"integrally_closed_in(restrict_ring(field_ring(L), A₁), L.carrier)",
		},
		Conclusion: "regular_function_field(L, k, L.carrier)",
		Abbrev: Abbrev{
			{Name: "constants", Text: "{x:A | x ∈ L.carrier ∧ algebraic_over(L, k, x)}"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve, finiteK, normalZero, normalOne Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("L")
		ring := a.TermAs[RingOps[A]]("field_ring(L)")
		chartZero := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)")
		chartOne := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₁)")
		carrier := a.TermAs[Set[A]]("L.carrier")
		datum := a.Have(
			"k is a subfield of L, t lies in L and is transcendental over k, and the charts meet in k",
			"subfield(L, k) ∧ t ∈ L.carrier ∧ ¬algebraic_over(L, k, t) ∧ A₀ ∩ A₁ = k",
			By(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
		inCharts := a.Have(
			"so k lies in both charts",
			"k ⊆ A₀ ∧ k ⊆ A₁",
			BySets(datum))
		exact := a.Have(
			"an element of L algebraic over k lies in k",
			"∀x:A. x ∈ L.carrier ∧ algebraic_over(L, k, x) ⇒ x ∈ k",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in L",
					"x is algebraic over k")
				xm := b.MemberOf[on.L](x, given[0])
				integral := b.Have(
					"x, algebraic over k, is integral over k",
					"integral_over(restrict_ring(field_ring(L), k), x)",
					By(datum, given[1], integral_element.AlgebraicIntegral.Read(L).At(k, xm)))
				inBoth := b.Have(
					"so x is integral over either chart, which holds k, "+
						"and lies in it, the chart being integrally closed in L",
					"x ∈ A₀ ∧ x ∈ A₁",
					By(
						integral,
						given[0],
						inCharts,
						normalZero,
						normalOne,
						integral_element.IntegralOverMono.At(ring, k, A0, x),
						integral_element.IntegralOverMono.At(ring, k, A1, x),
						integral_element.IntegrallyClosedDef.At(chartZero, carrier),
						integral_element.IntegrallyClosedDef.At(chartOne, carrier)))
				b.Show(
					"x lies in the meet of the charts, which is k",
					BySets(inBoth, datum))
			}))
		constants := a.Have(
			"the constants of L over k are k itself: an element of k is algebraic over k and lies in L",
			"«constants» = k",
			BySets(exact, datum, algebraic_element.MemberAlgebraic.Read(L), field.SubfieldSubset.At(ops, k)))
		regular := a.Have(
			"L is finite over k(t), so it is regular over its field of constants",
			"regular_function_field(L, «constants», L.carrier)",
			By(
				datum,
				curve,
				finiteK,
				field.CarrierSubfield.Read(L),
				field.SubfieldSubset.At(ops, k),
				algebraic_curve.FiniteOverRationalFunctions.Read(L).At(k, A0, A1, A01, t),
				function_field.ExactConstantFieldFinite.Read(L).At(k, carrier, t)))
		a.Show(
			"and those constants are k",
			By(constants, regular))
	}),
})}

// ColengthCosetCount — an ideal of colength d over a finite subfield of q
// elements has q^d cosets: the quotient is a d-dimensional space over a finite
// field, and such a space has q^d elements.
var ColengthCosetCount = colengthCosetCountThm{family.Add(registry.ProofEntry{
	Name: "ColengthCosetCount",
	Key:  "prop_863e2d2ae1bd4d09",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S H:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"ring_ideal(restrict_ring(field_ring(M), S), H)",
			"finite_dimensional(restrict_ring(field_ring(M), k), «quotient»)",
		},
		Conclusion: "has_size(left_cosets(M.add, S, H), " +
			"    card(k) ^ module_dim(restrict_ring(field_ring(M), k), «quotient»))",
		Abbrev: Abbrev{
			{Name: "quotient", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), H)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, S, H *Expr[Set[A]],
			inField, finiteK, subring, kInS, ideal, colength Fact,
		) {
			record := a.TermAs[FieldOps[A]]("M")
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			chart := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), S)")
			scalarField := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
			quotient := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«quotient»")
			chartModule := a.Have(
				"the regular module of S is M's restricted to S",
				"regular_module(restrict_ring(field_ring(M), S)) = "+
					"restrict_module(regular_module(field_ring(M)), S)",
				Simp(
					Fwd(module_record.RegularModuleDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RestrictModuleDef)),
				Refl())
			space := a.Have(
				"the quotient is a vector space over k",
				"module_on(restrict_ring(field_ring(M), k), «quotient»)",
				By(
					Normalized,
					subring,
					inField,
					kInS,
					ideal,
					chartModule,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S),
					field.SubfieldRingSubfield.Read(M).At(k, S),
					module_dimension.IdealQuotientModuleOn.At(chart, k, a.TermAs[Fun[A, A]]("M.inv"), H),
					module_record.RestrictRingTwice.At(ring, S, k)))
			finiteField := a.Have(
				"k is a finite field",
				"finite_field(restrict_field(M, k))",
				By(
					inField,
					finiteK,
					field.SubfieldFieldOn.Read(M).At(k),
					finite_field.FiniteFieldDef.At(scalarField),
					field.RestrictFieldDef.At(record, k)))
			a.Show(
				"a finite-dimensional space over a finite field has q^d elements, here the cosets",
				By(
					Normalized,
					finiteField,
					space,
					colength,
					finite_field.FiniteDimensionalSpaceSize.At(scalarField, quotient),
					field.RestrictFieldRing.At(record, k),
					finite_field.FieldSizeDef.At(scalarField),
					field.RestrictFieldDef.At(record, k),
					submodule.QuotientModuleDef,
					module_record.RestrictModuleDef))
		}),
})}

// ChartIdealFiniteQuotient — a nonzero ideal of a chart of a smooth curve has
// finite colength over the constants and finitely many cosets: the colength is
// finite on any curve over the line, and over the finite field k a quotient of
// dimension d has q^d elements.
var ChartIdealFiniteQuotient = chartIdealFiniteQuotientThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealFiniteQuotient",
	Key:  "prop_30dc3441d802901b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"ring_ideal(«chart», H)",
			"H ≠ {L.zero}",
		},
		Conclusion: "finite_dimensional(«scalars», quotient_module(«chartVectors», H)) ∧ " +
			"finite(left_cosets(L.add, A₀, H))",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
			{Name: "chartVectors", Text: "restrict_module(«vectors», A₀)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H *Expr[Set[A]],
			curve, ideal, nonzero Fact,
		) {
			read := a.Conjuncts(
				GroupPremises(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)),
				"the constants are a subfield of L",
				"the constants lie in the chart",
				"the chart is a subring of L")
			constants, kInChart, subring := read[0], read[1], read[2]
			quotient := a.Have(
				"a nonzero ideal of a chart of a curve over the line has finite colength over k",
				"finite_dimensional(«scalars», quotient_module(«chartVectors», H))",
				By(
					curve,
					SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					ideal,
					nonzero,
					algebraic_curve.NonzeroIdealFiniteColength.Read(L).At(k, A0, A1, A01, t, H)))
			a.Show(
				"over the finite field k, finite colength means finitely many cosets",
				By(
					quotient,
					constants,
					SmoothCurveFiniteConstants.Read(curve),
					subring,
					kInChart,
					ideal,
					ColengthCosetCount.Read(L).At(k, A0, H),
					cardinality.HasSizeDef))
		}),
})}

// ChartMaximalNonzero — the zero ideal is not maximal in a chart of a smooth
// curve: were it maximal, the nonzero coordinate t would be a unit of A₀, so
// its inverse would lie in both charts, hence in the constants, and the
// inverse coordinate would be algebraic.
var ChartMaximalNonzero = chartMaximalNonzeroThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalNonzero",
	Key:  "prop_955ca36b2e5af1e1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"maximal_ideal(restrict_ring(field_ring(L), A₀), m)",
		},
		Conclusion: "m ≠ {L.zero}",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Set[A]],
			curve, maximal Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			inverse := a.TermAs[A]("L.inv(t)")
			line := a.Have(
				"t is a nonzero element of A₀ whose inverse lies in A₁ and is transcendental over A₀ ∩ A₁ = k",
				"subfield(L, k) ∧ "+
					"t ∈ A₀ ∧ "+
					"t ≠ L.zero ∧ "+
					"L.inv(t) ∈ A₁ ∧ "+
					"A₀ ∩ A₁ = k ∧ "+
					"¬algebraic_over(L, k, L.inv(t))",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			chartRing := a.Have(
				"the chart is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), A₀))",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			zero := a.SupposeNot()
			outside := a.Have(
				"t is outside the zero ideal",
				"t ∉ m",
				BySets(zero, line))
			v, unitModulo := a.ObtainAs[A](
				"a maximal ideal inverts what lies outside it",
				"∃v:A. v ∈ A₀ ∧ v * t - L.one ∈ m",
				By(maximal, line, outside, At(ring_ideal.MaximalUnitModulo.Read(chartRing), m, t)))
			vanishing := a.Have(
				"modulo the zero ideal, v * t - 1 is zero",
				"v * t - L.one = L.zero",
				BySets(unitModulo, zero))
			unit := a.Have(
				"so v inverts t in the chart",
				"v * t = L.one",
				ByArith(chartRing, unitModulo, vanishing, line))
			identified := a.Have(
				"so v is the inverse of t in L",
				"L.inv(t) = v",
				By(
					unit,
					unitModulo,
					line,
					subring,
					comm_ring.SubringSubset.At(ring, A0),
					At(field.InvLeftUniqueOn.Read(L), v, t),
					set_basic.SubsetDef))
			constant := a.Have(
				"so the inverse of t lies in both charts, hence in the constants",
				"L.inv(t) ∈ k",
				BySets(identified, unitModulo, line))
			a.Show(
				"a constant is algebraic, and the inverse coordinate is not",
				By(constant, line, algebraic_element.MemberAlgebraic.Read(L).At(k, inverse)))
		}),
})}

// ChartIdealInvertible — every nonzero ideal of a chart of a smooth curve is
// invertible: nonzero ideals have finitely many cosets, hence finite height,
// and the chart is integrally closed, so its nonzero maximal ideals are
// invertible, and the factorization theory reaches every nonzero ideal.
var ChartIdealInvertible = chartIdealInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealInvertible",
	Key:  "prop_198b6d8d3cc4d758",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"ring_ideal(restrict_ring(field_ring(L), A₀), H)",
			"H ≠ {L.zero}",
		},
		Conclusion: "invertible_fractional(field_ring(L), A₀, H)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H *Expr[Set[A]],
			curve, ideal, nonzero Fact,
		) {
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(
					curve,
					SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			cosets := a.Have(
				"every nonzero ideal of the chart has finitely many cosets",
				"∀J:set(A). ring_ideal(«chart», J) ∧ J ≠ {L.zero} ⇒ finite(left_cosets(L.add, A₀, J))",
				a.ForEach(func(J *Expr[Set[A]]) Action {
					return By(curve, ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, J))
				}))
			chartRing := a.Have(
				"the chart is a ring under L's operations",
				"comm_ring_on(«chart»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A0)))
			heights := a.Have(
				"and finitely many cosets give finite height",
				"∀J:set(A). ring_ideal(«chart», J) ∧ J ≠ {L.zero} ⇒ finite_ideal_height(«chart», J)",
				a.ForEach(func(J *Expr[Set[A]]) Action {
					return By(cosets.At(J), ideal_factorization.FiniteQuotientIdealHeight.Read(chartRing).At(J))
				}))
			maximalInvertible := a.Have(
				"and, the chart being normal, its nonzero maximal ideals are invertible",
				"∀m:set(A). maximal_ideal(«chart», m) ∧ m ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), A₀, m)",
				By(
					cosets,
					subring,
					SmoothCurveChartZeroNormal.Read(curve),
					ideal_factorization.NonzeroMaximalInvertible.Read(L)))
			a.Show(
				"so a nonzero ideal factors into invertible maximal ideals",
				By(
					subring,
					heights,
					maximalInvertible,
					ideal,
					nonzero,
					ideal_factorization.NonzeroIdealInvertible.Read(L).At(A0, H)))
		}),
})}
