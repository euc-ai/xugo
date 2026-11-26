// point_bounds.go — what the points of a plane model in a finite field cost:
// boundedly many over each value of t and at infinity, so the rational count is
// the number of points of the first chart up to deg F; over a finite constant
// field the points of the extended first chart where a(t) survives fall short of
// the count by at most d(deg a + 1); and a curve over the line through t agrees
// with the model's charts off the zeros of one polynomial and counts alike up to
// a fixed bound.

package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_splitting"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneChartFibreBound — the first chart of a plane model has at most deg F points
// in a subfield over each value of t: z is a root of the monic equation F over k[t]
// (PlaneModelRelation).
var PlaneChartFibreBound = planeChartFibreBoundThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartFibreBound",
	Key:  "prop_215f33c146f22dbc",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k l:set(A). ∀t z:A. ∀F:(num → A). ∀b:num. ∀y:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
		},
		Conclusion: "finite(«fibre») ∧ card(«fibre») ≤ polynomial_degree(F)",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "{e:A → A | e ∈ «pmPoints»(«pmChart0») ∧ e(t) = y}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			y *Expr[A],
			subfieldK, model, subfieldL Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			chartIs := a.Conjuncts(
				PlaneChartsInAmbient.At(fieldM, K, k, t, z, b),
				"the first chart is k[t][z]",
				"the second chart is k[1/t][t^(-b) z]")
			a.Show(
				"z is a root of the monic equation over k[t]",
				chartIs[0].Rw(),
				By(
					M,
					subfieldK,
					model,
					subfieldL,
					PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b),
					PlaneModelRelation.Read(M).At(K, k, t, z, F, b),
					algebra_point_bounds.PointsOverValueBound.At(fieldM, k, l, t, z, F, y)))
		}),
})}

// PlaneCountNearChart — the rational point count of a plane model is the number of
// points of its first chart, up to deg F: the count is those points and the points
// at infinity (curve_point_count.CurveCountAtInfinity), and a point at infinity of the
// second chart k[1/t][w], w = t^(-b) z, kills t⁻¹, so it lies over 0 under the monic
// equation of w (ScaledMonicEquation), of degree deg F.
var PlaneCountNearChart = planeCountNearChartThm{family.Add(registry.ProofEntry{
	Name: "PlaneCountNearChart",
	Key:  "prop_71ad3e65e5141af2",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
			"finite(l)",
		},
		Conclusion: "card(«pmPoints»(«pmChart0»)) ≤ «pmCount» ∧ " +
			"«pmCount» ≤ card(«pmPoints»(«pmChart0»)) + polynomial_degree(F)",
		Abbrev: Abbrev{
			{Name: "atInfinity", Text: "{ψ:A → A | ψ ∈ «pmPoints»(«pmChart1») ∧ ψ(M.inv(t)) = M.zero}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			l *Expr[Set[A]],
			subfieldK, model, subfieldL, finiteL Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			inverse := a.TermAs[A]("M.inv(t)")
			chart := a.TermAs[Set[A]]("«pmChart0»")
			second := a.TermAs[Set[A]]("«pmChart1»")
			overlap := a.TermAs[Set[A]]("«pmOverlap»")
			scaled := a.TermAs[Fun[Nat, A]]("«pmScaled»")
			generator := a.TermAs[A]("«pmGenerator»")
			ambient := a.Conjuncts(
				a.Have(
					"read in M, k is a subfield, and t and t^(-b) z lie in M",
					"subfield(M, k) ∧ t ∈ M.carrier ∧ «pmGenerator» ∈ M.carrier",
					By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
				"k is a subfield of M",
				"t lies in M",
				"t^(-b) z lies in M")
			inverseIn := a.Have(
				"t⁻¹ lies in M",
				"M.inv(t) ∈ M.carrier",
				By(ambient[1], field.InvIn.Read(M)))
			overLine := a.Have(
				"the charts of the model make a curve",
				"curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap»)",
				By(subfieldK, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)))
			counted := a.Conjuncts(
				GroupPremises(
					M,
					subfieldK,
					subfieldL,
					finiteL,
					overLine,
					curve_point_count.CurveCountAtInfinity.At(fieldM, K, k, chart, second, overlap, t, l)),
				"there are finitely many points at infinity",
				"the count is the points of the first chart and those at infinity")
			equation := a.Conjuncts(
				GroupPremises(M, subfieldK, model, ScaledMonicEquation.At(fieldM, K, k, t, z, F, b)),
				"the scaled equation is a polynomial over k[1/t]",
				"it is monic",
				"it vanishes at t^(-b) z",
				"its degree is deg F")
			chartIs := a.Conjuncts(
				PlaneChartsInAmbient.At(fieldM, K, k, t, z, b),
				"the first chart is k[t][z]",
				"the second chart is k[1/t][t^(-b) z]")
			infinity := a.Have(
				"a point at infinity sends t⁻¹ to 0, and t^(-b) z "+
					"is a root of the monic scaled equation over k[1/t]",
				"card(«atInfinity») ≤ polynomial_degree(«pmScaled»)",
				chartIs[1].Rw(),
				By(
					M,
					ambient[0],
					subfieldL,
					inverseIn,
					ambient[2],
					chartIs[1],
					equation[0],
					equation[1],
					equation[2],
					algebra_point_bounds.PointsOverValueBound.At(fieldM, k, l, inverse, generator, scaled, zero)))
			a.Show(
				"the count exceeds the points of the first chart by the points at infinity",
				ByArith(counted[1], infinity, equation[3]))
		}),
})}

// PlaneGoodOpenUniformBadPointBound — over a finite field l of constants, the
// points of the extended first chart at which a(t) survives are at most the
// rational point count, and fall short of it by at most d(deg a + 1), d the
// degree of F. Extending the constants to l keeps the number of points of each
// chart (constant_splitting.ConstantChartPointCount), so the count over l is the count
// over k, which exceeds the points of the first chart by at most d
// (PlaneCountNearChart). Restriction to the first chart takes the points killing
// a(t) one to one to points of the chart killing a(t), and these send t to a
// root of a, at most d over each (KilledPointsBound, PlaneChartFibreBound).
var PlaneGoodOpenUniformBadPointBound = planeGoodOpenUniformBadPointBoundThm{family.Add(registry.ProofEntry{
	Name: "PlaneGoodOpenUniformBadPointBound",
	Key:  "prop_896a59fda71f2148",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀K k:set(A). " +
			"∀t z:A. " +
			"∀F:(num → A). " +
			"∀b:num. " +
			"∀l:set(A). " +
			"∀a U V:(num → A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
			"finite(l)",
			"k ⊆ l",
			"plane_good_certificate(«pmRing», k, t, F, a, U, V)",
		},
		Conclusion: "card(«good») ≤ «extendedCount» ∧ " +
			"«extendedCount» ≤ card(«good») + polynomial_degree(F) * (polynomial_degree(a) + 1)",
		Abbrev: Abbrev{
			{Name: "extendedPoints", Text: "λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), l, λx:A. x)"},
			{Name: "good", Text: "{φ:A → A | " +
				"    φ ∈ «extendedPoints»(«pmExtendedChart0») ∧ φ(polynomial_eval(a, t)) ≠ M.zero}"},
			{Name: "killed", Text: "{φ:A → A | " +
				"    φ ∈ «extendedPoints»(«pmExtendedChart0») ∧ φ(polynomial_eval(a, t)) = M.zero}"},
			{Name: "killedBelow", Text: "{ψ:A → A | " +
				"    ψ ∈ «pmPoints»(«pmChart0») ∧ ψ(polynomial_eval(a, t)) = M.zero}"},
			{Name: "restriction", Text: "λX:set(A). λψ:A → A. λx:A. COND(x ∈ X, ψ(x), M.zero)"},
			{Name: "extendedCount", Text: "curve_rational_point_count(field_ring(M), " +
				"    l, " +
				"    l, " +
				"    «pmExtendedChart0», " +
				"    «pmExtendedChart1», " +
				"    «pmExtendedOverlap»)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			l *Expr[Set[A]],
			a, U, V *Arrow[Nat, A],
			subfieldK, model, subfieldL, finiteL, kInL, certificate Fact,
		) {
			ops := arg.TermAs[FieldOps[A]]("M")
			functionRing := arg.TermAs[RingOps[A]]("«pmRing»")
			chart := arg.TermAs[Set[A]]("«pmChart0»")
			second := arg.TermAs[Set[A]]("«pmChart1»")
			overlap := arg.TermAs[Set[A]]("«pmOverlap»")
			chartPoints := arg.TermAs[Set[Fun[A, A]]]("«extendedPoints»(«pmExtendedChart0»)")
			good := arg.TermAs[Set[Fun[A, A]]]("«good»")
			killed := arg.TermAs[Set[Fun[A, A]]]("«killed»")
			killedBelow := arg.TermAs[Set[Fun[A, A]]]("«killedBelow»")
			restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»(«pmChart0»)")
			degree := arg.TermAs[Nat]("polynomial_degree(F)")

			// The model's charts are a curve over k whose constants l extends finitely.
			regular := arg.Have(
				"K is regular over k read in M",
				"regular_function_field(M, k, K)",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b)))
			finiteOverK := arg.Have(
				"l is finite over k, a finite subfield holding it",
				"finite_extension(M, k, l)",
				By(
					regular,
					subfieldL,
					kInL,
					finiteL,
					function_field.RegularFunctionFieldDef.At(ops, k, K),
					finite_field.FiniteSubfieldSize.Read(M).At(k, l)))
			curve := arg.Have(
				"the charts of the model are a curve over the line",
				"curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap»)",
				By(subfieldK, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)))
			charts := arg.Have(
				"so the charts and the overlap are subrings of M between k and K, and t lies in the first chart",
				"subring(field_ring(M), «pmChart0») ∧ "+
					"subring(field_ring(M), «pmChart1») ∧ "+
					"subring(field_ring(M), «pmOverlap») ∧ "+
					"k ⊆ «pmChart0» ∧ "+
					"k ⊆ «pmChart1» ∧ "+
					"k ⊆ «pmOverlap» ∧ "+
					"«pmChart0» ⊆ K ∧ "+
					"«pmChart1» ⊆ K ∧ "+
					"«pmOverlap» ⊆ K ∧ "+
					"t ∈ «pmChart0»",
				By(
					subfieldK,
					curve,
					curve_point_count.CurveOverLineChartsInField.Read(M).At(K, k, chart, second, overlap, t)))
			finitePoints := arg.Conjuncts(
				GroupPremises(
					subfieldK,
					curve,
					finiteL,
					curve_point_count.CurvePointSetsFinite.Read(M).At(K, k, chart, second, overlap, t, l)),
				"the first chart has finitely many points in l",
				"so has the second",
				"so has the overlap")

			// Each chart extended to l has as many points over l as it has over k.
			lInL := set_order.SubsetRefl.At(l)
			chartCount := arg.Conjuncts(
				arg.Have(
					"the extended first chart has finitely many points over l, as many as the first chart over k",
					"finite(«extendedPoints»(«pmExtendedChart0»)) ∧ "+
						"card(«extendedPoints»(«pmExtendedChart0»)) = card(«pmPoints»(«pmChart0»))",
					By(
						regular,
						subfieldL,
						kInL,
						finiteOverK,
						charts,
						finitePoints[0],
						lInL,
						constant_splitting.ConstantChartPointCount.Read(M).At(K, k, l, chart, l))),
				"the extended first chart has finitely many points",
				"as many as the first chart")
			secondCount := arg.Have(
				"so does the second chart",
				"card(«extendedPoints»(«pmExtendedChart1»)) = card(«pmPoints»(«pmChart1»))",
				By(
					regular,
					subfieldL,
					kInL,
					finiteOverK,
					charts,
					finitePoints[1],
					lInL,
					constant_splitting.ConstantChartPointCount.Read(M).At(K, k, l, second, l)))
			overlapCount := arg.Have(
				"and so does the overlap",
				"card(«extendedPoints»(«pmExtendedOverlap»)) = card(«pmPoints»(«pmOverlap»))",
				By(
					regular,
					subfieldL,
					kInL,
					finiteOverK,
					charts,
					finitePoints[2],
					lInL,
					constant_splitting.ConstantChartPointCount.Read(M).At(K, k, l, overlap, l)))
			sameCount := arg.Have(
				"so the count over l is the count over k",
				"«extendedCount» = «pmCount»",
				Unfold(curve_point_count.CurveRationalPointCountDef),
				By(chartCount[1], secondCount, overlapCount))

			// The points of the extended chart killing a(t) restrict to points of the chart killing it.
			descent := arg.Conjuncts(
				arg.Have(
					"restriction takes the points of the extended first chart one to one onto those of the first chart",
					"injective_on(«extendedPoints»(«pmExtendedChart0»), «restriction»(«pmChart0»)) ∧ "+
						"image(«restriction»(«pmChart0»), «extendedPoints»(«pmExtendedChart0»)) = «pmPoints»(«pmChart0»)",
					By(
						M,
						regular,
						subfieldL,
						kInL,
						finiteOverK,
						charts,
						lInL,
						constant_splitting.ConstantChartPoints.Read(M).At(K, k, l, chart, l))),
				"restriction is injective on the points of the extended chart",
				"its image is the points of the first chart")
			killedInto := arg.Have(
				"a point of the extended chart killing a(t) restricts to a point of the first chart killing it",
				"image(«restriction»(«pmChart0»), «killed») ⊆ «killedBelow»",
				Simp(Fwd(set_image.ImageSubsetIff)),
				Derive(func(c *Argument) {
					φ := c.FixAs[Fun[A, A]]("φ")
					parts := c.Conjuncts(
						c.Have(
							"φ is a point of the extended chart killing a(t)",
							"φ ∈ «extendedPoints»(«pmExtendedChart0») ∧ φ(polynomial_eval(a, t)) = M.zero",
							By(c.Assume())),
						"φ is a point of the extended chart",
						"φ kills a(t)")
					restricted := c.Have(
						"its restriction is a point of the first chart",
						"«restriction»(«pmChart0», φ) ∈ «pmPoints»(«pmChart0»)",
						By(parts[0], descent[1], set_image.FunInImage.At(restriction, chartPoints, φ)))
					c.Show(
						"which kills a(t) as φ does, a(t) lying in the chart or the restriction being zero there",
						BySets(restricted, parts[1]))
				}))
			killedPoints := arg.Have(
				"the killed points are points of the extended chart",
				"«killed» ⊆ «extendedPoints»(«pmExtendedChart0»)",
				BySets())
			killedInjective := arg.Have(
				"restriction stays injective on the killed points, finitely many as the points are",
				"injective_on(«killed», «restriction»(«pmChart0»)) ∧ finite(«killed»)",
				By(
					descent[0],
					chartCount[0],
					killedPoints,
					functions.InjectiveOnSubset.At(restriction, killed, chartPoints),
					finite_set.FiniteSubset.At(killed, chartPoints)))

			// Points of the chart killing a(t) send t to a root of a, at most deg F over each.
			fibres := arg.Have(
				"at most deg F points of the first chart lie over each value of t",
				"∀y:A. "+
					"    finite({e:A → A | e ∈ «pmPoints»(«pmChart0») ∧ e(t) = y}) ∧ "+
					"    card({e:A → A | e ∈ «pmPoints»(«pmChart0») ∧ e(t) = y}) ≤ polynomial_degree(F)",
				arg.ForEach(func(y *Expr[A]) Action {
					return By(subfieldK, model, subfieldL, PlaneChartFibreBound.Read(M).At(K, k, l, t, z, F, b, y))
				}))
			killedBound := arg.Have(
				"a being a nonzero polynomial over k by the certificate, "+
					"at most deg a · deg F points of the first chart kill a(t)",
				"finite(«killedBelow») ∧ card(«killedBelow») ≤ polynomial_degree(a) * polynomial_degree(F)",
				By(
					charts,
					subfieldL,
					certificate,
					PlaneGoodCertificateDef.At(functionRing, k, t, F, a, U, V),
					fibres,
					algebra_point_bounds.KilledPointsBound.Read(M).At(chart, k, l, t, a, degree)))
			killedCount := arg.Have(
				"and the killed points of the extended chart are no more",
				"card(«killed») ≤ card(«killedBelow»)",
				By(
					killedInjective,
					killedInto,
					killedBound,
					cardinality.CardImageInj.At(restriction, killed),
					cardinality.CardSubset.At(
						arg.TermAs[Set[Fun[A, A]]]("image(«restriction»(«pmChart0»), «killed»)"), killedBelow)))

			// The extended chart's points are the good ones and the killed ones.
			partition := arg.Have(
				"a point of the extended chart either keeps a(t) or kills it",
				"«good» ∪ «killed» = «extendedPoints»(«pmExtendedChart0») ∧ «good» ∩ «killed» = ∅",
				BySets())
			split := arg.Have(
				"so the points of the extended chart are the good ones and the killed ones",
				"card(«extendedPoints»(«pmExtendedChart0»)) = card(«good») + card(«killed»)",
				By(chartCount[0], partition, cardinality.CardOfDisjointParts.At(good, killed, chartPoints)))
			near := arg.Have(
				"the count over k exceeds the points of the first chart by at most deg F",
				"card(«pmPoints»(«pmChart0»)) ≤ «pmCount» ∧ "+
					"«pmCount» ≤ card(«pmPoints»(«pmChart0»)) + polynomial_degree(F)",
				By(subfieldK, model, subfieldL, finiteL, PlaneCountNearChart.Read(M).At(K, k, t, z, F, b, l)))
			arg.Show(
				"the good points, the chart and the count in turn",
				SplitConj(
					Case(
						"the good points are among those of the extended chart, which the count bounds",
						ByArith(sameCount, split, chartCount[1], near)),
					Case(
						"the count exceeds the good points by the killed ones and deg F, at most deg a · deg F + deg F",
						ByArith(sameCount, split, chartCount[1], near, killedCount, killedBound))))
		}),
})}

// FunctionFieldModelsAgreeOffFiniteSet — a curve over the line through t and the
// charts of an integral plane model at the same t, in the function field K over
// k, agree once the value at t of one nonzero polynomial a over k is inverted,
// and their rational point counts lie within a fixed B of each other over every
// finite subfield. The plane charts are a curve over the line at t
// (PlaneEquationBiaffineCurve); both first charts are subrings of M lying in K,
// with fraction field K, holding k[t] and free of finite rank over it
// (curve_point_count.CurveOverLineFirstChart), so finitely generated over it
// (principal_ideal_domain.FiniteBasisFinitelyGenerated); one nonzero d in k[t]
// makes them agree (good_localization.ModelsAgreeInSubfield), and d is a(t). The
// counts are those of two curves over the line in K
// (curve_point_count.BirationalBiaffinePointCountBound).
var FunctionFieldModelsAgreeOffFiniteSet = functionFieldModelsAgreeOffFiniteSetThm{family.Add(registry.ProofEntry{
	Name: "FunctionFieldModelsAgreeOffFiniteSet",
	Key:  "prop_9a9bf1204930dc4d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "∃a:(num → A). ∃B:num. " +
			"    polynomial_over(k, a) ∧ " +
			"    a ≠ vec_zero ∧ " +
			"    ring_away(«pmRing», A₀, polynomial_eval(a, t)) = " +
			"    ring_away(«pmRing», «pmChart0», polynomial_eval(a, t)) ∧ " +
			"    (∀l:set(A). " +
			"        subfield(M, l) ∧ finite(l) ⇒ " +
			"        dist((curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁), " +
			"                curve_rational_point_count(field_ring(M), " +
			"                    k, " +
			"                    l, " +
			"                    «pmChart0», " +
			"                    «pmChart1», " +
			"                    «pmOverlap»))) ≤ " +
			"        B)",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			inField, curve, model Fact,
		) {
			ops := arg.TermAs[FieldOps[A]]("M")
			ring := arg.TermAs[RingOps[A]]("field_ring(M)")
			ambient := arg.TermAs[RingOps[A]]("«pmRing»")
			polynomials := arg.TermAs[Set[A]]("«pmPolynomials»")
			scalars := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «pmPolynomials»)")
			chart := arg.TermAs[Set[A]]("«pmChart0»")
			second := arg.TermAs[Set[A]]("«pmChart1»")
			overlap := arg.TermAs[Set[A]]("«pmOverlap»")
			planeCurve := arg.Have(
				"the charts of the plane model are a curve over the line at t",
				"curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap»)",
				By(inField, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)))
			bound, counts := arg.ObtainAs[Nat](
				"two curves over the line in K count alike up to a fixed B over every finite subfield",
				"∃B:num. ∀l:set(A). "+
					"    subfield(M, l) ∧ finite(l) ⇒ "+
					"    dist((curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁), "+
					"            curve_rational_point_count(field_ring(M), "+
					"                k, "+
					"                l, "+
					"                «pmChart0», "+
					"                «pmChart1», "+
					"                «pmOverlap»))) ≤ "+
					"    B",
				By(
					inField,
					curve,
					planeCurve,
					curve_point_count.BirationalBiaffinePointCountBound.Read(M).At(
						K, k, A0, A1, A01, t, chart, second, overlap, t)))
			vectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), A₀)")
			chartVectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), «pmChart0»)")
			d, found := arg.ObtainAs[A](
				"both first charts are finitely generated subrings over k[t] "+
					"with fraction field K, so one nonzero d in k[t] makes them agree",
				"∃d:A. "+
					"    d ∈ «pmPolynomials» ∧ "+
					"    d ≠ M.zero ∧ "+
					"    ring_away(field_ring(M), A₀, d) = ring_away(field_ring(M), «pmChart0», d)",
				By(
					M,
					inField,
					curve,
					planeCurve,
					curve_point_count.CurveOverLineFirstChart.Read(M).At(K, k, A0, A1, A01, t),
					curve_point_count.CurveOverLineFirstChart.Read(M).At(K, k, chart, second, overlap, t),
					principal_ideal_domain.FiniteBasisFinitelyGenerated.At(scalars, vectors),
					principal_ideal_domain.FiniteBasisFinitelyGenerated.At(scalars, chartVectors),
					good_localization.ModelsAgreeInSubfield.Read(M).At(K, polynomials, A0, chart)))
			parts := arg.Conjuncts(
				found,
				"d lies in k[t]",
				"d is not zero",
				"inverting d makes the charts agree in M")
			poly, valued := arg.ObtainAs[Fun[Nat, A]](
				"d is the value at t of a polynomial a over k",
				"∃a:(num → A). polynomial_over(k, a) ∧ polynomial_eval(a, t) = d",
				BySets(parts[0], algebraic_element.PolynomialImageDef.At(ring, k, t)))
			polyParts := arg.Conjuncts(
				valued,
				"a lies over k",
				"its value at t is d")
			tIn := arg.Have(
				"t lies in the chart, inside K, so in M",
				"t ∈ M.carrier",
				BySets(
					M,
					inField,
					curve,
					curve_point_count.CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t),
					field.SubfieldSubset.At(ops, K)))
			nonzero := arg.Have(
				"a is not the zero polynomial, whose value at t is zero while d is not",
				"a ≠ vec_zero",
				By(
					Normalized,
					parts[1],
					polyParts[1],
					polynomial_evaluation.EvalVecZero.Read(field.RingOn.Read(M)).At(arg.MemberOf[on.M](t, tIn))))
			agree := arg.Have(
				"read in the ring of K, whose elements lie in M, the charts with d inverted still agree",
				"ring_away(«pmRing», A₀, d) = ring_away(«pmRing», «pmChart0», d)",
				BySets(
					parts[2],
					inField,
					field.SubfieldSubset.At(ops, K),
					ring_away.RingAwayDef.At(ambient, A0, d),
					ring_away.RingAwayDef.At(ambient, chart, d),
					ring_away.RingAwayDef.At(ring, A0, d),
					ring_away.RingAwayDef.At(ring, chart, d)))
			arg.Take(poly)
			arg.Take(bound)
			arg.Show(
				"a and B are the polynomial and the bound",
				By(polyParts[0], nonzero, polyParts[1], agree, counts))
		}),
})}
