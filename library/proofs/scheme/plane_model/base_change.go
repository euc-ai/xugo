package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneModelBaseChange — a plane model after extending its constants to a
// finite extension l of k: the charts spanned over l are a curve over the line
// over l inside the composite, of the genus of the model, and the powers of z
// below deg F stay a basis of the extended first chart over l[t]. The model's
// charts are a curve over the line with that power basis
// (PlaneEquationBiaffineCurve), and K is regular over k, so the extended curve
// and its genus are the constant extension's (curve_point_count.ConstantChartCurve,
// ConstantChartGenus). Read in M, the first chart is a subring lying in K and
// holding k[t] (CurveOverLineFirstChart), so a k[t]-submodule of K, and its
// basis stays a basis of its chart over the chart of k[t] (ConstantChartBasis),
// which is l[t] (ConstantPolynomialChart).
var PlaneModelBaseChange = planeModelBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelBaseChange",
	Key:  "prop_e47bbba9fe30a74f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "curve_over_line(«pmExtendedField», " +
			"    l, " +
			"    t, " +
			"    «pmExtendedChart0», " +
			"    «pmExtendedChart1», " +
			"    «pmExtendedOverlap») ∧ " +
			"curve_genus(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
			"    l, " +
			"    «pmExtendedChart0», " +
			"    «pmExtendedChart1», " +
			"    «pmExtendedOverlap») = " +
			"curve_genus(«pmRing», k, «pmChart0», «pmChart1», «pmOverlap») ∧ " +
			"module_basis(restrict_ring(field_ring(M), polynomial_image(field_ring(M), l, t)), " +
			"    restrict_module(regular_module(field_ring(M)), «pmExtendedChart0»), " +
			"    «pmPowersZ»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			l *Expr[Set[A]],
			subfieldK, model, subfieldL, kInL, finiteExtension Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			chart := a.TermAs[Set[A]]("«pmChart0»")
			second := a.TermAs[Set[A]]("«pmChart1»")
			overlap := a.TermAs[Set[A]]("«pmOverlap»")
			polynomials := a.TermAs[Set[A]]("«pmPolynomials»")
			ambient := a.Conjuncts(
				a.Have(
					"read in M, K is regular over k, k is a subfield, and t lies in K and in M",
					"regular_function_field(M, k, K) ∧ subfield(M, k) ∧ t ∈ K ∧ t ∈ M.carrier",
					By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
				"K is regular over k read in M",
				"k is a subfield of M",
				"t lies in K",
				"t lies in M")
			regular, kSubfield, tInK := ambient[0], ambient[1], ambient[2]
			tm := a.MemberOf[on.M](t, ambient[3])
			plane := a.Conjuncts(
				GroupPremises(subfieldK, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)),
				"the charts of the model are a curve over the line",
				"the powers of z below deg F are a finite basis of the first chart over k[t]")
			curve := plane[0]
			E, basisData := a.UnpackAs[Set[A]](plane[1], "E")
			chartData := a.Conjuncts(
				a.Have(
					"read in M, the first chart is a subring lying in K and holding k[t]",
					"subring(field_ring(M), «pmChart0») ∧ «pmChart0» ⊆ K ∧ «pmPolynomials» ⊆ «pmChart0»",
					By(
						subfieldK,
						curve,
						curve_point_count.CurveOverLineFirstChart.Read(M).At(K, k, chart, second, overlap, t))),
				"the first chart is a subring of M",
				"it lies in K",
				"it holds k[t]")
			chartRing, chartInK, lineInChart := chartData[0], chartData[1], chartData[2]
			line := a.Conjuncts(
				GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
				"k[t] is a subring of M",
				"it holds k",
				"it holds t",
				"it lies in k(t)")
			lineInK := a.Have(
				"k[t] lies in K, as the first chart does",
				"«pmPolynomials» ⊆ K",
				BySets(chartInK, lineInChart))
			overLine := a.Have(
				"the first chart is a submodule over k[t]",
				"submodule(restrict_ring(field_ring(M), «pmPolynomials»), "+
					"    regular_module(field_ring(M)), "+
					"    «pmChart0»)",
				By(
					M,
					chartRing,
					lineInChart,
					principal_ideal_domain.ConstantSubringSubmodule.At(fieldM, polynomials, chart)))
			a.Show(
				"the extended charts and the extended power basis",
				SplitConj(
					Case(
						"the charts spanned over l are a curve over the line of the same genus",
						By(
							M,
							regular,
							curve,
							subfieldL,
							kInL,
							finiteExtension,
							curve_point_count.ConstantChartCurve.At(fieldM, K, k, l, chart, second, overlap, t),
							curve_point_count.ConstantChartGenus.At(fieldM, K, k, l, chart, second, overlap, t))),
					Case(
						"a basis of the first chart, a k[t]-submodule of K, stays "+
							"a basis of its chart over the chart of k[t], which is l[t]",
						By(
							M,
							regular,
							subfieldL,
							kInL,
							finiteExtension,
							line[0],
							line[1],
							lineInK,
							chartInK,
							tInK,
							overLine,
							basisData,
							constant_field_extension.ConstantChartBasis.At(fieldM, K, k, l, polynomials, chart, E),
							constant_field_extension.ConstantPolynomialChart.At(fieldM, K, k, l, t)))))
		}),
})}
