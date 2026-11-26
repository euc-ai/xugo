// extended_curve.go — the curve after a constant extension. The function field
// of a smooth curve is regular over k in any field holding it; the charts
// spanned over the field l of q^r constants form a curve over the line,
// integrally closed in the composite K(l) by the normality mechanism, so a
// smooth curve over l; and the extended curve counts at degree m what the curve
// counts at degree r·m.

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_splitting"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothCurveRegular — the function field of a smooth curve is regular over
// its constants read in any field holding it, the constants lie in it, and so
// does the coordinate: inside K the regularity is that of a curve with normal
// charts over a finite field, and it carries up through K ⊆ M.
var SmoothCurveRegular = smoothCurveRegularThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveRegular",
	Key:  "prop_9877f1ec804e9a8a",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"subfield(M, K)", "«ambientCurve»"},
		Conclusion: "regular_function_field(M, k, K) ∧ k ⊆ K ∧ t ∈ K",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			inField, curve Fact,
		) {
			ambient := a.TermAs[FieldOps[A]]("M")
			functionField := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			functionFieldOn := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			smooth := a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)
			regularInK := a.Have(
				"the charts are normal over the finite field k, so K is regular over k",
				"regular_function_field(restrict_field(M, K), k, K)",
				By(smooth, smooth_curve.NormalChartsRegular.Read(functionFieldOn).At(k, A0, A1, A01, t)))
			a.Show(
				"regularity over K carries up to M, and its clause k ⊆ K and the curve's t ∈ K stand",
				By(
					inField,
					regularInK,
					smooth,
					function_field.RegularFunctionFieldInAmbient.Read(M).At(k, K),
					function_field.RegularFunctionFieldDef.At(ambient, k, K),
					algebraic_curve.CurveOverLineDef.At(functionField, k, t, A0, A1, A01)))
		}),
})}

// ConstantChartLine — a chart of a curve after a constant extension: the chart
// of A₀ and the chart of the overlap are subrings, the first holding l, t and
// l[t], which is the chart of k[t], the overlap's chart is the first with t
// inverted, and a finite basis of A₀ over k[t] is one of its chart over l[t].
// The clauses of A₀ read in M are CurveOverLineFirstChart, K being a subfield of
// M as its regularity states.
var ConstantChartLine = constantChartLineThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartLine",
	Key:  "prop_528ff8f183bc0c51",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "over", Text: "λX:set(A). polynomial_image(field_ring(M), X, t)"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "subring(field_ring(M), «chart»(A₀)) ∧ " +
			"subring(field_ring(M), «chart»(A₀₁)) ∧ " +
			"l ⊆ «chart»(A₀) ∧ " +
			"t ∈ «chart»(A₀) ∧ " +
			"«chart»(A₀) ⊆ «chart»(A₀₁) ∧ " +
			"«over»(l) ⊆ «chart»(A₀) ∧ " +
			"«chart»(A₀₁) = ring_away(«scalars»(«chart»(A₀₁)), «chart»(A₀), t) ∧ " +
			"(∃B:set(A). finite(B) ∧ module_basis(«scalars»(«over»(l)), «vectors»(«chart»(A₀)), B))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			regular, curve, lSubfield, kInL, finiteExtension Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			polynomials := a.TermAs[Set[A]]("«over»(k)")
			chart0, chart01 := a.TermAs[Set[A]]("«chart»(A₀)"), a.TermAs[Set[A]]("«chart»(A₀₁)")
			fields := a.Conjuncts(
				a.Have(
					"k and K are subfields of M",
					"subfield(M, k) ∧ subfield(M, K)",
					By(a.Unfolded(regular, function_field.RegularFunctionFieldDef))),
				"k is a subfield of M",
				"so is K")
			kSubfield, inField := fields[0], fields[1]
			chart := a.Conjuncts(
				GroupPremises(inField, curve, CurveOverLineFirstChart.Read(M).At(K, k, A0, A1, A01, t)),
				"A₀ is a subring of M",
				"so is the overlap",
				"A₀ lies in K",
				"so does the overlap",
				"A₀ holds k",
				"the overlap holds A₀",
				"A₀ holds t",
				"a power of t carries each member of the overlap into A₀",
				"k[t] is a subring of M",
				"A₀ holds k[t]",
				"A₀ is free of finite rank over k[t]",
				"K is the field of fractions of A₀")
			subring0, subring01, A0InK, A01InK, kInA0 := chart[0], chart[1], chart[2], chart[3], chart[4]
			A0InA01, tInA0, clears, polynomialRing, polynomialsInA0, freeChart :=
				chart[5], chart[6], chart[7], chart[8], chart[9], chart[10]
			inM := a.Have(
				"so the chart and the overlap lie in M",
				"A₀ ⊆ M.carrier ∧ A₀₁ ⊆ M.carrier",
				BySets(A0InK, A01InK, inField, field.SubfieldSubset.At(ops, K)))
			tInK := a.Have(
				"t lies in K, as A₀ does",
				"t ∈ K",
				BySets(tInA0, A0InK))
			tInField := a.MemberOf[on.M](t, a.Have(
				"t lies in M",
				"t ∈ M.carrier",
				BySets(tInA0, inM)))
			kInPolynomials := a.Have(
				"k[t] holds k",
				"k ⊆ «over»(k)",
				By(kSubfield, algebraic_element.PolynomialImageRing.Read(M).At(k, tInField)))
			polynomialsInK := a.Have(
				"k[t] lies in K, as A₀ does",
				"«over»(k) ⊆ K",
				BySets(polynomialsInA0, A0InK))
			overlapHoldsK := a.Have(
				"the overlap holds k",
				"k ⊆ A₀₁",
				BySets(kInA0, A0InA01))
			ring0 := a.Conjuncts(
				GroupPremises(
					regular,
					subring0,
					M,
					lSubfield,
					kInL,
					finiteExtension,
					A0InK,
					kInA0,
					constant_field_extension.ConstantChartRing.At(ops, K, k, l, A0)),
				"the chart of A₀ is a subring",
				"it holds l",
				"it holds A₀",
				"it carries ideals to ideals")
			ring01 := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subring01,
					A01InK,
					overlapHoldsK,
					constant_field_extension.ConstantChartRing.At(ops, K, k, l, A01)),
				"the chart of the overlap is a subring",
				"it holds l",
				"it holds the overlap",
				"it carries ideals to ideals")
			chartSubmodules := a.Have(
				"both charts are submodules over l",
				"submodule(«scalars»(l), regular_module(field_ring(M)), «chart»(A₀)) ∧ "+
					"submodule(«scalars»(l), regular_module(field_ring(M)), «chart»(A₀₁))",
				By(
					M,
					lSubfield,
					inM,
					constant_field_extension.ConstantChartSubmodule.At(ops, l, A0),
					constant_field_extension.ConstantChartSubmodule.At(ops, l, A01)))
			A0InChart01 := a.Have(
				"the chart of the overlap holds A₀",
				"A₀ ⊆ «chart»(A₀₁)",
				BySets(A0InA01, ring01[2]))
			chart0InChart01 := a.Have(
				"so it holds the chart of A₀",
				"«chart»(A₀) ⊆ «chart»(A₀₁)",
				By(
					chartSubmodules,
					A0InChart01,
					constant_field_extension.ConstantChartLeast.At(fieldRing, l, A0, chart01)))
			polynomialsInChart := a.Have(
				"the chart of A₀ holds k[t]",
				"«over»(k) ⊆ «chart»(A₀)",
				BySets(polynomialsInA0, ring0[2]))
			same := a.Have(
				"l[t] is the chart of k[t]",
				"«over»(l) = «chart»(«over»(k))",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					tInK,
					constant_field_extension.ConstantPolynomialChart.At(ops, K, k, l, t)))
			overLInChart := a.Have(
				"so the chart of A₀ holds l[t]",
				"«over»(l) ⊆ «chart»(A₀)",
				same.Rw(),
				By(
					chartSubmodules,
					polynomialsInChart,
					constant_field_extension.ConstantChartLeast.At(fieldRing, l, polynomials, chart0)))
			tInChart := a.Have(
				"it holds t",
				"t ∈ «chart»(A₀)",
				BySets(tInA0, ring0[2]))
			away := a.Have(
				"the chart of the overlap is the chart of A₀ with t inverted",
				"«chart»(A₀₁) = ring_away(«scalars»(«chart»(A₀₁)), «chart»(A₀), t)",
				By(
					M,
					ring0[0],
					ring0[1],
					ring0[2],
					tInChart,
					inM,
					clears,
					constant_field_extension.ConstantChartAway.At(ops, l, A0, A01, t)))
			B, basisData := a.UnpackAs[Set[A]](freeChart, "B")
			basisParts := a.Conjuncts(
				basisData,
				"B is finite",
				"B is a basis of A₀ over k[t]")
			moduleOverPolynomials := a.Have(
				"A₀ is a submodule over k[t]",
				"submodule(«scalars»(«over»(k)), regular_module(field_ring(M)), A₀)",
				By(
					M,
					subring0,
					polynomialsInA0,
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, polynomials, A0)))
			lifted := a.Have(
				"so B is a basis of the chart of A₀ over the chart of k[t]",
				"module_basis(«scalars»(«chart»(«over»(k))), «vectors»(«chart»(A₀)), B)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					polynomialRing,
					polynomialsInK,
					kInPolynomials,
					moduleOverPolynomials,
					A0InK,
					basisParts[1],
					constant_field_extension.ConstantChartBasis.At(ops, K, k, l, polynomials, A0, B)))
			free := a.Have(
				"and over l[t], which is that chart",
				"∃B:set(A). finite(B) ∧ module_basis(«scalars»(«over»(l)), «vectors»(«chart»(A₀)), B)",
				same.Rw(),
				Witness(B),
				By(basisParts[0], lifted))
			a.Show(
				"the clauses of the chart",
				By(ring0[0], ring01[0], ring0[1], tInChart, chart0InChart01, overLInChart, away, free))
		}),
})}

// ConstantChartCurve — the charts of a constant extension form a curve over
// the line: over l, in the composite K(l), with coordinate t, the charts of
// A₀, A₁ and the overlap are the datum of a curve. Each chart's clauses are
// ConstantChartLine, read a second time through the swap; t stays
// transcendental, the charts meet in the chart of the constants, which is l,
// and the fractions of A₀ fill K, so those of its chart fill the composite.
var ConstantChartCurve = constantChartCurveThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartCurve",
	Key:  "prop_b035b05cf1e1a934",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "curve_over_line(restrict_field(M, constant_composite(M, K, l)), " +
			"    l, " +
			"    t, " +
			"    «chart»(A₀), " +
			"    «chart»(A₁), " +
			"    «chart»(A₀₁))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			regular, curve, lSubfield, kInL, finiteExtension Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			ringM := field.RingOn.Read(M)
			inverse := a.TermAs[A]("M.inv(t)")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
			chart0, chart1 := a.TermAs[Set[A]]("«chart»(A₀)"), a.TermAs[Set[A]]("«chart»(A₁)")
			chart01 := a.TermAs[Set[A]]("«chart»(A₀₁)")
			overlapRing := a.TermAs[RingOps[A]]("«scalars»(«chart»(A₀₁))")
			fields := a.Conjuncts(
				a.Have(
					"k and K are subfields of M",
					"subfield(M, k) ∧ subfield(M, K)",
					By(a.Unfolded(regular, function_field.RegularFunctionFieldDef))),
				"k is a subfield of M",
				"so is K")
			kSubfield, inField := fields[0], fields[1]
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			first := a.Simplified(GroupPremises(
				M,
				regular,
				curve,
				lSubfield,
				kInL,
				finiteExtension,
				ConstantChartLine.At(ops, K, k, l, A0, A1, A01, t)))
			otherChart := a.Have(
				"read from its other chart, the curve is a curve in the inverse of t",
				"curve_over_line(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(curve, algebraic_curve.CurveSwap.Read(functionField).At(k, A0, A1, A01, t)))
			second := a.Simplified(GroupPremises(
				M,
				regular,
				lSubfield,
				kInL,
				finiteExtension,
				otherChart,
				ConstantChartLine.At(ops, K, k, l, A1, A0, A01, inverse)))
			charts := a.Conjuncts(
				GroupPremises(inField, curve, CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t)),
				"A₀ is a subring of M",
				"so is A₁",
				"so is the overlap",
				"k lies in A₀",
				"and in A₁",
				"and in the overlap",
				"A₀ lies in K",
				"so does A₁",
				"so does the overlap",
				"t lies in A₀")
			tInK := a.Have(
				"t lies in K, as A₀ does",
				"t ∈ K",
				BySets(charts[9], charts[6]))
			clauses := a.Conjuncts(
				a.Have(
					"the curve's meet, transcendence and fractions",
					"A₀ ∩ A₁ = k ∧ "+
						"¬algebraic_over(restrict_field(M, K), k, t) ∧ "+
						"fraction_field_carrier(field_ring(restrict_field(M, K)), A₀)",
					By(a.Unfolded(curve, algebraic_curve.CurveOverLineDef))),
				"the charts meet in k",
				"t is transcendental over k",
				"K is the fraction field of A₀")
			subspaces := a.Have(
				"the charts and the overlap are k-subspaces of K",
				"submodule(«scalars»(k), «vectors»(K), A₀) ∧ "+
					"submodule(«scalars»(k), «vectors»(K), A₁) ∧ "+
					"submodule(«scalars»(k), «vectors»(K), A₀₁)",
				By(
					GroupPremises(
						charts[0],
						charts[3],
						charts[6],
						constant_field_extension.ConstantRingSubspace.Read(M).At(K, k, A0)),
					GroupPremises(
						charts[1],
						charts[4],
						charts[7],
						constant_field_extension.ConstantRingSubspace.Read(M).At(K, k, A1)),
					GroupPremises(
						charts[2],
						charts[5],
						charts[8],
						constant_field_extension.ConstantRingSubspace.Read(M).At(K, k, A01))))
			compositeFractions := a.Have(
				"so the fractions of its chart fill the composite",
				"fraction_field_carrier(field_ring(restrict_field(M, constant_composite(M, K, l))), «chart»(A₀))",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					charts[0],
					charts[6],
					charts[3],
					clauses[2],
					constant_field_extension.ConstantChartFractions.At(ops, K, k, l, A0)))
			meetCharts := a.Have(
				"the charts meet in the chart of A₀ ∩ A₁",
				"«chart»(A₀ ∩ A₁) = «chart»(A₀) ∩ «chart»(A₁)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subspaces,
					constant_field_extension.ConstantChartMeet.At(ops, K, k, l, A0, A1)))
			chartsMeet := a.Have(
				"which is the chart of the constants, l",
				"«chart»(A₀) ∩ «chart»(A₁) = l",
				meetCharts.RwRev(),
				clauses[0].Rw(),
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					constant_field_extension.ConstantChartOfConstants.At(ops, K, k, l)))
			compositeData := a.Conjuncts(
				GroupPremises(M, inField, lSubfield, constant_composite.ConstantCompositeSubfield.At(ops, K, l)),
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			lInComposite := a.Have(
				"l is a subfield of the composite",
				"subfield(restrict_field(M, constant_composite(M, K, l)), l)",
				By(lSubfield, compositeData[2], field.SubfieldRestrict.At(ops, composite, l)))
			tInComposite := a.Have(
				"t lies in the composite, as K does",
				"t ∈ constant_composite(M, K, l)",
				BySets(tInK, compositeData[1]))
			tInField := a.MemberOf[on.M](t, a.Have(
				"so t lies in M",
				"t ∈ M.carrier",
				BySets(tInK, inField, field.SubfieldSubset.At(ops, K))))
			overlapInComposite := a.Have(
				"the chart of the overlap lies in the composite",
				"«chart»(A₀₁) ⊆ constant_composite(M, K, l)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subspaces,
					constant_field_extension.ConstantChartContract.At(ops, K, k, l, A01)))
			readK := a.Conjuncts(
				algebraic_element.RestrictFieldReadings.At(ops, K, k, t),
				"k[t] is read in M",
				"and so is algebraicity over k")
			transcendentalOverK := a.Have(
				"t is transcendental over k in M",
				"¬algebraic_over(M, k, t)",
				By(clauses[1], readK[1]))
			transcendental := a.Have(
				"so it is transcendental over l",
				"¬algebraic_over(M, l, t)",
				By(
					M,
					kSubfield,
					lSubfield,
					kInL,
					finiteExtension,
					tInField,
					transcendentalOverK,
					algebraic_element.ConstantTranscendental.At(ops, k, l, t)))
			nonzero := a.Conjuncts(
				GroupPremises(
					kSubfield, transcendentalOverK, algebraic_element.TranscendentalInverse.Read(M).At(k, tInField)),
				"t is not zero",
				"inv(t) lies in M",
				"inv(t) is transcendental over k")[0]
			overlapIsRing := a.Have(
				"the chart of the overlap is a ring under M's operations",
				"comm_ring_on(«scalars»(«chart»(A₀₁)))",
				By(first, comm_ring.SubringRingOn.Read(ringM).At(chart01)))
			subring0 := a.Have(
				"the first chart is a subring of it",
				"subring(«scalars»(«chart»(A₀₁)), «chart»(A₀))",
				By(
					first,
					comm_ring.SubringRingOn.Read(ringM).At(chart0),
					comm_ring.SubringRingOn.Read(overlapIsRing).At(chart0),
					module_record.RestrictRingTwice.At(fieldRing, chart01, chart0)))
			subring1 := a.Have(
				"and so is the second",
				"subring(«scalars»(«chart»(A₀₁)), «chart»(A₁))",
				By(
					second,
					comm_ring.SubringRingOn.Read(ringM).At(chart1),
					comm_ring.SubringRingOn.Read(overlapIsRing).At(chart1),
					module_record.RestrictRingTwice.At(fieldRing, chart01, chart1)))
			biaffine := a.Have(
				"the charts and the overlap are a biaffine datum",
				"biaffine(«scalars»(«chart»(A₀₁)), «chart»(A₀), «chart»(A₁), t, M.inv(t))",
				By(
					overlapIsRing,
					subring0,
					subring1,
					first,
					second,
					nonzero,
					field.MulRightInverseOn.Read(M).At(tInField),
					lattice_pair.BiaffineDef.At(overlapRing, chart0, chart1, t, inverse),
					module_record.RestrictRingDef.At(fieldRing, chart01)))
			a.Show(
				"read at the composite, whose operations are M's, each clause of the datum is one of these",
				Simp(
					Fwd(algebraic_curve.CurveOverLineDef),
					Fwd(field.RestrictFieldRecords),
					Fwd(algebraic_element.RestrictFieldReadings)),
				By(
					lInComposite,
					tInComposite,
					transcendental,
					overlapInComposite,
					biaffine,
					first,
					second,
					chartsMeet,
					compositeFractions))
		}),
})}

// SmoothCurveConstantExtension — extending the constants of a smooth curve to
// the field with q^r elements gives a smooth curve over that field: the charts
// over l are a curve over the line, l is finite, and the charts stay
// integrally closed in the composite, the second through the swap.
var SmoothCurveConstantExtension = smoothCurveConstantExtensionThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveConstantExtension",
	Key:  "prop_328c70f4b01683a1",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), «constants», X)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < r",
		},
		Conclusion: "smooth_finite_curve(restrict_field(M, «composite»), " +
			"    «constants», " +
			"    t, " +
			"    «chart»(A₀), " +
			"    «chart»(A₁), " +
			"    «chart»(A₀₁))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			r *Expr[Nat],
			closed, inField, curve, positive Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			constants := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			chart0, chart1 := a.TermAs[Set[A]]("«chart»(A₀)"), a.TermAs[Set[A]]("«chart»(A₁)")
			inverse := a.TermAs[A]("M.inv(t)")
			regular := a.Have(
				"the function field is regular over k in M",
				"regular_function_field(M, k, K)",
				By(inField, curve, SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t)))
			smooth := a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)
			data := a.Have(
				"l is a finite subfield of M holding k, of finite degree, and the composite is a subfield",
				"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite(«constants») ∧ "+
					"finite_extension(M, k, «constants») ∧ "+
					"subfield(M, «composite»)",
				By(
					closed,
					regular,
					smooth_curve.SmoothCurveFiniteConstants.Read(curve),
					positive,
					constant_galois.ConstantCompositeData.Read(M).At(K, k, r)))
			finiteL := a.Have(
				"so l is finite",
				"finite(«constants»)",
				By(data))
			over := a.Have(
				"the charts over l are a curve over the line",
				"curve_over_line(restrict_field(M, «composite»), "+
					"    «constants», "+
					"    t, "+
					"    «chart»(A₀), "+
					"    «chart»(A₁), "+
					"    «chart»(A₀₁))",
				By(regular, smooth, data, ConstantChartCurve.Read(M).At(K, k, constants, A0, A1, A01, t)))
			closed0 := a.Have(
				"the first chart over l is integrally closed in the composite",
				"integrally_closed_in(restrict_ring(field_ring(M), «chart»(A₀)), «composite»)",
				By(
					closed,
					inField,
					curve,
					positive,
					ConstantChartIntegrallyClosed.Read(M).At(K, k, A0, A1, A01, t, r)))
			closed1 := a.Have(
				"so is the second, reading the curve from its other chart",
				"integrally_closed_in(restrict_ring(field_ring(M), «chart»(A₁)), «composite»)",
				By(
					closed,
					inField,
					curve,
					positive,
					CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t),
					ConstantChartIntegrallyClosed.Read(M).At(K, k, A1, A0, A01, inverse, r)))
			a.Show(
				"the clauses of a smooth curve stand at the extended datum",
				Unfold(smooth_curve.SmoothFiniteFieldCurveDef),
				By(
					over,
					finiteL,
					closed0,
					closed1,
					field.RestrictFieldRecords.At(ops, composite, chart0),
					field.RestrictFieldRecords.At(ops, composite, chart1)))
		}),
})}

// ConstantChartOverLine — the chart of A₀ over l is finite over k[t]: A₀ is
// free of finite rank over k[t], and its chart is generated over A₀ by a
// k-basis E of l.
var ConstantChartOverLine = constantChartOverLineThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartOverLine",
	Key:  "prop_5d83cd1587ae03a4",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, A₀)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"«ambientCurve»",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
		},
		Conclusion: "subring(field_ring(M), «polynomials») ∧ " +
			"subring(field_ring(M), «chart») ∧ " +
			"«polynomials» ⊆ «chart» ∧ " +
			"l ⊆ «chart» ∧ " +
			"module_finitely_generated(«scalars»(«polynomials»), «vectors»(«chart»))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			inField, curve, lSubfield, kInL, finiteE, basis Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			chart := a.TermAs[Set[A]]("«chart»")
			polynomials := a.TermAs[Set[A]]("«polynomials»")
			regularData := a.Conjuncts(
				GroupPremises(M, inField, curve, SmoothCurveRegular.At(m, K, k, A0, A1, A01, t)),
				"K is regular over k",
				"k lies in K",
				"t lies in K")
			regular := regularData[0]
			line := a.Conjuncts(
				GroupPremises(
					M,
					inField,
					a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
					CurveOverLineFirstChart.At(m, K, k, A0, A1, A01, t)),
				"the chart is a subring",
				"the overlap is a subring",
				"the chart lies in K",
				"the overlap lies in K",
				"k lies in the chart",
				"the chart lies in the overlap",
				"t lies in the chart",
				"a power of t carries the overlap into the chart",
				"k[t] is a subring",
				"k[t] lies in the chart",
				"the chart is free of finite rank over k[t]",
				"K is the field of fractions of the chart")
			subA0, A0InK, kInA0, subPolynomials, polynomialsInA0, freeA0 :=
				line[0], line[2], line[4], line[8], line[9], line[10]
			kSubfield := a.Have(
				"k is a subfield",
				"subfield(M, k)",
				By(regular, function_field.RegularFunctionFieldDef.At(m, k, K)))
			basisDegree := a.Conjuncts(
				GroupPremises(
					M, kSubfield, lSubfield, kInL, finiteE, basis, field_extension.BasisDegree.At(m, k, l, E)),
				"l is finite over k",
				"of degree the size of E")
			ringData := a.Conjuncts(
				GroupPremises(
					regularData[0],
					line[0],
					M,
					lSubfield,
					kInL,
					line[2],
					line[4],
					basisDegree[0],
					constant_field_extension.ConstantChartRing.At(m, K, k, l, A0)),
				"the chart of A₀ is a subring",
				"it holds l",
				"it holds A₀",
				"the charts of ideals are ideals")
			subChart, lInChart, A0InChart := ringData[0], ringData[1], ringData[2]
			finiteChart := a.Have(
				"the chart is finite over A₀",
				"module_finitely_generated(«scalars»(A₀), «vectors»(«chart»))",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteE,
					basis,
					subA0,
					A0InK,
					kInA0,
					constant_field_extension.ConstantChartFinite.At(m, K, k, l, E, A0)))
			overA0 := a.Have(
				"the chart is a submodule over A₀",
				"submodule(«scalars»(A₀), regular_module(field_ring(M)), «chart»)",
				By(M, subChart, A0InChart, principal_ideal_domain.ConstantSubringSubmodule.At(m, A0, chart)))
			polynomialScalars := a.TermAs[RingOps[A]]("«scalars»(«polynomials»)")
			vectorsA0 := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(A₀)")
			finiteOverPolynomials := a.Have(
				"so the chart is finite over k[t]",
				"module_finitely_generated(«scalars»(«polynomials»), «vectors»(«chart»))",
				By(
					M,
					polynomialsInA0,
					subPolynomials,
					subA0,
					overA0,
					freeA0,
					principal_ideal_domain.FiniteBasisFinitelyGenerated.At(polynomialScalars, vectorsA0),
					finiteChart,
					principal_ideal_domain.FiniteModuleTower.At(m, polynomials, A0, chart)))
			polynomialsInChart := a.Have(
				"the chart holds k[t]",
				"«polynomials» ⊆ «chart»",
				BySets(polynomialsInA0, A0InChart))
			a.Show(
				"k[t] and the chart, finite over it",
				By(subPolynomials, subChart, polynomialsInChart, lInChart, finiteOverPolynomials))
		}),
})}

// ConstantChartIntegrallyClosed — a constant extension keeps a chart normal. An
// element x of the composite integral over the chart of A₀ is integral over
// k[t], the chart being finite over k[t]. So is d(e) * x for d the dual family
// of a k-basis E of l, and so is the sum of its conjugates, which is the
// coordinate of x at e. That coordinate lies in K, integral over A₀, so it lies
// in A₀; and an element of the composite with its coordinates in A₀ lies in the
// chart of A₀.
var ConstantChartIntegrallyClosed = constantChartIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartIntegrallyClosed",
	Key:  "prop_cbfcb876e9bdea03",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», A₀)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "group", Text: "field_automorphisms(M, K, «composite»)"},
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, M.zero, «group», λg:permutation(A). permutation_map(g, b))"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(«composite»), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < r",
		},
		Conclusion: "integrally_closed_in(«scalars»(«chart»), «composite»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			r *Expr[Nat],
			closed, inField, curve, positive Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			l := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			chart := a.TermAs[Set[A]]("«chart»")
			polynomials := a.TermAs[Set[A]]("«polynomials»")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«constants»)")
			regular := a.Conjuncts(
				GroupPremises(M, inField, curve, SmoothCurveRegular.At(m, K, k, A0, A1, A01, t)),
				"K is regular over k",
				"k lies in K",
				"t lies in K")[0]
			finiteK := a.Simplified(smooth_curve.SmoothCurveFiniteConstants.Read(curve).AsFact())
			line := a.Conjuncts(
				a.Have(
					"read in M, the chart is a subring lying in K and holding k and k[t]",
					"subring(field_ring(M), A₀) ∧ A₀ ⊆ K ∧ k ⊆ A₀ ∧ «polynomials» ⊆ A₀",
					By(
						M,
						inField,
						a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
						CurveOverLineFirstChart.At(m, K, k, A0, A1, A01, t))),
				"the chart is a subring",
				"it lies in K",
				"it holds k",
				"it holds k[t]")
			subA0, A0InK, kInA0, polynomialsInA0 := line[0], line[1], line[2], line[3]
			data := a.Conjuncts(
				a.Have(
					"the field of constants sits over k, inside the composite",
					"subfield(M, k) ∧ "+
						"subfield(M, «constants») ∧ "+
						"k ⊆ «constants» ∧ "+
						"finite_extension(M, k, «constants») ∧ "+
						"subfield(M, «composite») ∧ "+
						"K ⊆ «composite» ∧ "+
						"«constants» ⊆ «composite»",
					By(M, closed, regular, finiteK, positive, constant_galois.ConstantCompositeData.At(m, K, k, r))),
				"k is a subfield",
				"l is a subfield",
				"l holds k",
				"l is finite over k",
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			lSubfield, kInL, finiteExtension := data[1], data[2], data[3]
			compositeSubfield, KInC, lInComposite := data[4], data[5], data[6]
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(«constants»), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			finiteE, basis := basisParts[0], basisParts[1]
			over := a.Conjuncts(
				GroupPremises(
					M,
					inField,
					curve,
					data[1],
					data[2],
					basisParts[0],
					basisParts[1],
					ConstantChartOverLine.At(m, K, k, l, E, A0, A1, A01, t)),
				"k[t] is a subring",
				"the chart of A₀ is a subring",
				"it holds k[t]",
				"it holds l",
				"it is finite over k[t]")
			subPolynomials, subChart := over[0], over[1]
			polynomialsInChart, lInChart, finiteOverPolynomials := over[2], over[3], over[4]
			polynomialsInK := a.Have(
				"K holds k[t]",
				"«polynomials» ⊆ K",
				BySets(polynomialsInA0, A0InK))
			_, dual := a.UnpackAs[Fun[A, A]](
				GroupPremises(
					M,
					closed,
					regular,
					finiteK,
					positive,
					basisParts[0],
					basisParts[1],
					constant_galois.ConstantTraceDual.At(m, K, k, E, r)),
				"d")
			dualParts := a.Conjuncts(
				dual,
				"d lands in l",
				"d reads the coordinates")
			form := a.Conjuncts(
				GroupPremises(
					M, closed, regular, finiteK, positive, constant_galois.ConstantTraceForm.At(m, K, k, r)),
				"the group is finite",
				"the composite is Galois over K",
				"the sum of the conjugates is K-linear",
				"and a k-linear form on l")
			linear := form[2]
			normal := a.Have(
				"A₀ is normal in K, read under M's operations",
				"integrally_closed_in(«scalars»(A₀), K)",
				By(
					Normalized,
					smooth_curve.SmoothCurveChartZeroNormal.Read(curve),
					field.RestrictFieldRecords.At(m, K, A0)))
			a.Do(Simp(Fwd(integral_element.IntegrallyClosedDef)))
			x := a.FixAs[A]("x")
			members := a.Conjuncts(
				a.Assume(),
				"x lies in the composite",
				"x is integral over the chart")
			xIn, integralChart := members[0], members[1]
			xInField := a.Have(
				"x lies in M",
				"x ∈ M.carrier",
				BySets(xIn, compositeSubfield, field.SubfieldSubset.At(m, composite)))
			integralLine := a.Have(
				"x is integral over k[t]",
				"integral_over(«scalars»(«polynomials»), x)",
				By(
					M,
					subPolynomials,
					subChart,
					polynomialsInChart,
					finiteOverPolynomials,
					xInField,
					integralChart,
					principal_ideal_domain.IntegralTowerOverPrincipal.At(m, polynomials, chart, x)))
			inA0 := a.Have(
				"each coordinate of x lies in A₀",
				"∀e:A. e ∈ E ⇒ «coordinate»(x, e) ∈ A₀",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					de := b.TermAs[A]("d(e)")
					product := b.TermAs[A]("d(e) * x")
					value := b.TermAs[A]("«trace»(d(e) * x)")
					points := b.Have(
						"d(e) lies in the chart, in the composite and in M",
						"d(e) ∈ «chart» ∧ d(e) ∈ «composite» ∧ d(e) ∈ M.carrier",
						BySets(inE, dualParts[0].At(e), lInChart, lInComposite, lSubfield, field.SubfieldSubset.At(m, l)))
					integralPoint := b.Have(
						"d(e) is integral over k[t], the chart being finite",
						"integral_over(«scalars»(«polynomials»), d(e))",
						By(
							M,
							subPolynomials,
							subChart,
							polynomialsInChart,
							finiteOverPolynomials,
							points,
							principal_ideal_domain.FiniteSubringIntegral.At(m, polynomials, chart, de)))
					integralProduct := b.Have(
						"so is d(e) * x",
						"integral_over(«scalars»(«polynomials»), d(e) * x)",
						By(
							M,
							subPolynomials,
							points,
							xInField,
							integralPoint,
							integralLine,
							integral_element.IntegralAddNegMul.At(m, polynomials, de, x)))
					productIn := b.Have(
						"d(e) * x lies in the composite",
						"d(e) * x ∈ «composite»",
						By(points, xIn, compositeSubfield, field.SubfieldMul.At(m, composite, de, x)))
					integralValue := b.Have(
						"so does the sum of the conjugates of d(e) * x",
						"integral_over(«scalars»(«polynomials»), «trace»(d(e) * x))",
						By(
							M,
							inField,
							compositeSubfield,
							KInC,
							form[0],
							subPolynomials,
							polynomialsInK,
							productIn,
							integralProduct,
							field_automorphism.GaloisTraceIntegral.At(m, K, composite, polynomials, product)))
					inFunctionField := b.Have(
						"the coordinate lies in K",
						"«trace»(d(e) * x) ∈ K",
						By(productIn, module_homomorphism.HomIn.Read(linear)))
					overA0 := b.Have(
						"it is integral over A₀",
						"integral_over(«scalars»(A₀), «trace»(d(e) * x))",
						By(
							polynomialsInA0,
							integralValue,
							integral_element.IntegralOverMono.At(fieldRing, polynomials, A0, value)))
					b.Show(
						"A₀ is normal in K",
						By(
							inE,
							xIn,
							dualParts[1].At(e, x),
							inFunctionField,
							overA0,
							normal,
							integral_element.IntegrallyClosedDef.At(a.TermAs[RingOps[A]]("«scalars»(A₀)"), K)))
				}))
			subspace := a.Have(
				"A₀ is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), A₀)",
				By(M, subA0, kInA0, A0InK, constant_field_extension.ConstantRingSubspace.At(m, K, k, A0)))
			a.Show(
				"an element of the composite with coordinates in A₀ lies in the chart of A₀",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteE,
					basis,
					xIn,
					inA0,
					subspace,
					constant_field_extension.ConstantChartCoordinates.At(m, K, k, l, E, A0, x)))
		}),
})}

// ExtensionCountBaseChange — the count of a curve over the field l with q^r
// elements at degree m is its count over k at degree r·m. Both count in the
// field T with q^(r·m) elements, and each chart over l has as many points as
// its chart over k (constant_splitting.ConstantChartPointCount).
var ExtensionCountBaseChange = extensionCountBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "ExtensionCountBaseChange",
	Key:  "prop_ea2a9862f92dad20",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "target", Text: "finite_constants(field_ring(M), card(k), r * m)"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), «constants», X)"},
			{Name: "above", Text: "λX:set(A). " +
				"    algebra_points(«scalars»(«chart»(X)), «scalars»(«target»), «constants», λx:A. x)"},
			{Name: "below", Text: "λX:set(A). algebra_points(«scalars»(X), «scalars»(«target»), k, λx:A. x)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < r",
			"0 < m",
		},
		Conclusion: "curve_extension_count(field_ring(M), " +
			"    «constants», " +
			"    «chart»(A₀), " +
			"    «chart»(A₁), " +
			"    «chart»(A₀₁), " +
			"    m) = " +
			"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, r * m)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			r, m *Expr[Nat],
			closed, subfieldK, curve, rPositive, mPositive Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			constants := a.TermAs[Set[A]]("«constants»")
			target := a.TermAs[Set[A]]("«target»")
			q := a.TermAs[Nat]("card(k)")
			degree := a.TermAs[Nat]("r * m")
			regular := a.Conjuncts(
				GroupPremises(subfieldK, curve, SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t)),
				"K is regular over k",
				"k lies in K",
				"t lies in K")[0]
			smooth := a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)
			finiteK := a.Simplified(smooth_curve.SmoothCurveFiniteConstants.Read(curve).AsFact())
			constantData := a.Conjuncts(
				a.Have(
					"k is a subfield, and l is a subfield holding it, finite over it",
					"subfield(M, k) ∧ subfield(M, «constants») ∧ k ⊆ «constants» ∧ finite_extension(M, k, «constants»)",
					By(
						M,
						closed,
						regular,
						finiteK,
						rPositive,
						constant_galois.ConstantCompositeData.At(fieldM, K, k, r))),
				"k is a subfield",
				"l is a subfield",
				"l holds k",
				"l is finite over k")
			kSubfield, lSubfield, kInL, finiteExtension :=
				constantData[0], constantData[1], constantData[2], constantData[3]
			nonzero := a.Conjuncts(
				a.Have(
					"the degrees are not zero",
					"0 < r * m ∧ m ≠ 0 ∧ r * m ≠ 0",
					ByArith(rPositive, mPositive, nat_arith.MulEqZero.At(r, m))),
				"r·m is positive",
				"m is not zero",
				"r·m is not zero")
			targetData := a.Conjuncts(
				GroupPremises(
					closed,
					constantData[0],
					finiteK,
					nonzero[0],
					finite_field.FiniteConstantsSubfield.Read(M).At(k, degree)),
				"T is a subfield",
				"k lies in T",
				"T has q^(r·m) elements")
			TSubfield := targetData[0]
			sizeOfL := a.Have(
				"l has q^r elements",
				"card(«constants») = card(k) ^ r",
				By(
					M,
					closed,
					kSubfield,
					finiteK,
					rPositive,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, r),
					cardinality.HasSizeDef.At(constants, a.TermAs[Nat]("card(k) ^ r"))))
			finiteT := a.Have(
				"T is finite",
				"finite(«target»)",
				By(targetData[2], cardinality.HasSizeDef.At(target, a.TermAs[Nat]("card(k) ^ (r * m)"))))
			sameField := a.Have(
				"degree m over l is degree r·m over k",
				"finite_constants(field_ring(M), card(«constants»), m) = «target»",
				sizeOfL.Rw(),
				Simp(Fwd(finite_field.FiniteConstantsDef), Rev(nat_arith.PowPow)),
				Basic())
			lInT := a.Have(
				"T holds l, as r divides r·m",
				"«constants» ⊆ «target»",
				By(
					finite_field.FiniteConstantsMono.Read(field.RingOn.Read(M)).At(q, r, degree),
					nat_divides.DividesOwnMultiple.At(r, m)))
			finitePoints := a.Conjuncts(
				a.Have(
					"the charts and the overlap have finitely many points in T",
					"finite(«below»(A₀)) ∧ finite(«below»(A₁)) ∧ finite(«below»(A₀₁))",
					By(M, subfieldK, smooth, finiteT, CurvePointSetsFinite.At(fieldM, K, k, A0, A1, A01, t, target))),
				"the first chart has finitely many points in T",
				"so has the second",
				"so has the overlap")
			charts := a.Conjuncts(
				GroupPremises(subfieldK, smooth, CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t)),
				"the first chart is a subring",
				"so is the second",
				"so is the overlap",
				"k lies in the first chart",
				"and in the second",
				"and in the overlap",
				"the first chart lies in K",
				"so does the second",
				"so does the overlap",
				"t lies in the first chart")
			zero := a.Conjuncts(
				GroupPremises(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					charts[0],
					charts[3],
					charts[6],
					TSubfield,
					lInT,
					finitePoints[0],
					constant_splitting.ConstantChartPointCount.Read(M).At(K, k, constants, A0, target)),
				"the first chart over l has finitely many points",
				"as many as the first chart")[1]
			one := a.Conjuncts(
				GroupPremises(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					charts[1],
					charts[4],
					charts[7],
					TSubfield,
					lInT,
					finitePoints[1],
					constant_splitting.ConstantChartPointCount.Read(M).At(K, k, constants, A1, target)),
				"so has the second chart over l",
				"as many as the second chart")[1]
			overlap := a.Conjuncts(
				GroupPremises(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					charts[2],
					charts[5],
					charts[8],
					TSubfield,
					lInT,
					finitePoints[2],
					constant_splitting.ConstantChartPointCount.Read(M).At(K, k, constants, A01, target)),
				"and the overlap over l",
				"as many as the overlap")[1]
			left := a.Have(
				"over l at degree m the count is taken in T",
				"curve_extension_count(field_ring(M), «constants», «chart»(A₀), «chart»(A₁), «chart»(A₀₁), m) = "+
					"curve_rational_point_count(field_ring(M), "+
					"    «constants», "+
					"    «target», "+
					"    «chart»(A₀), "+
					"    «chart»(A₁), "+
					"    «chart»(A₀₁))",
				By(
					nonzero[1],
					sameField,
					CurveExtensionCountDef.At(
						fieldRing,
						constants,
						a.TermAs[Set[A]]("«chart»(A₀)"),
						a.TermAs[Set[A]]("«chart»(A₁)"),
						a.TermAs[Set[A]]("«chart»(A₀₁)"),
						m)))
			right := a.Have(
				"over k at degree r·m it is taken in T",
				"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, r * m) = "+
					"curve_rational_point_count(field_ring(M), k, «target», A₀, A₁, A₀₁)",
				By(nonzero[2], CurveExtensionCountDef.At(fieldRing, k, A0, A1, A01, degree)))
			a.Show(
				"the three counts agree",
				left.Rw(),
				right.Rw(),
				Unfold(CurveRationalPointCountDef),
				By(zero, one, overlap))
		}),
})}
