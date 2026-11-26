// extension_count.go — the points of the curve over the field with q^m elements
// counted by closed points. A point of a chart in that field has a maximal
// kernel, so it lies over a closed point whose degree divides m, and over a
// closed point of degree d dividing m lie exactly d such points. Counting the
// evaluation points fibre by fibre gives the sum of the degrees.

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/residue_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedPointAtInfinity — a maximal ideal of A₁ holding the inverse of t is the
// second component of the closed point with first component A₀. It is the first
// component of a closed point read from A₁, and the inverse of t lying in it
// rules out a proper component on the other side.
var ClosedPointAtInfinity = closedPointAtInfinityThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointAtInfinity",
	Key:  "prop_c57b901dbd6d9a78",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"«ambientCurve»",
			"maximal_ideal(restrict_ring(field_ring(M), A₁), n)",
			"M.inv(t) ∈ n",
		},
		Conclusion: "«ambientPoint»((A₀, n))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Set[A]],
			inField, curve, maximal, holdsInverse Fact,
		) {
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			inverse := a.TermAs[A]("M.inv(t)")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			otherChart := a.Have(
				"the other chart is a subring of M",
				"subfield(M, k) ∧ k ⊆ A₁ ∧ subring(field_ring(M), A₁)",
				By(inField, otherCurve, CurveChartsInField.Read(M).At(K, k, A1, A0, A01, inverse)))
			Q, over := a.ObtainAs[Prod[Set[A], Set[A]]](
				"from A₁ the ideal n is the first component of a closed point",
				"∃Q:prod(set(A), set(A)). curve_closed_point(«ambientRing», A₁, A₀, A₀₁, Q) ∧ fst(Q) = n",
				By(
					otherCurve,
					maximal,
					a.Simplified(
						smooth_curve.ChartMaximalClosedPoint.Read(functionField).At(k, A1, A0, A01, inverse, n),
						InAmbient)))
			swapped := a.TermAs[Prod[Set[A], Set[A]]]("(snd(Q), n)")
			point := a.Have(
				"read from A₀ it has second component n",
				"«ambientPoint»((snd(Q), n))",
				By(
					over,
					smooth_curve.ClosedPointSwap.At(a.TermAs[RingOps[A]]("«ambientRing»"), A0, A1, A01, swapped),
					pairs.Fst,
					pairs.Snd,
					pairs.PairEta.At(Q)))
			proper := a.Have(
				"n is not all of A₁",
				"n ≠ A₁",
				By(
					otherChart,
					maximal,
					ring_ideal.MaximalIdealNotWhole.At(a.TermAs[RingOps[A]]("field_ring(M)"), A1, n)))
			whole := a.Have(
				"a point proper on both sides would avoid the inverse of t, so its first component is A₀",
				"snd(Q) = A₀",
				By(
					point,
					proper,
					holdsInverse,
					curve,
					a.Simplified(
						smooth_curve.ClosedPointContraction.Read(functionField).At(k, A0, A1, A01, t, swapped),
						InAmbient),
					pairs.Fst,
					pairs.Snd))
			a.Show(
				"so the point is (A₀, n)",
				By(Normalized, point, whole))
		}),
})}

// EvaluationFibreSize — over a closed point P of degree d dividing m lie exactly
// d evaluation points. They carry the tag of the chart P is proper in, and their
// values are the points of that chart in the constants with kernel the ideal of
// P; a point at infinity vanishes at the inverse of t because P holds it.
var EvaluationFibreSize = evaluationFibreSizeThm{family.Add(registry.ProofEntry{
	Name: "EvaluationFibreSize",
	Key:  "prop_832280451afc1d3e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:num. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < m",
			"«ambientPoint»(P)",
			"«ambientPointDegree»(P) ∣ m",
		},
		Conclusion: "has_size({p:prod(bool, A → A) | p ∈ «evaluation» ∧ «scOver»(p, P)}, " +
			"    «ambientPointDegree»(P))",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "evaluation", Text: "curve_evaluation_points(M, k, «constants», t, A₀, A₁)"},
			{Name: "pointsOf", Text: "λS:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), S), " +
				"        restrict_ring(field_ring(M), «constants»), " +
				"        k, " +
				"        λx:A. x)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module( " +
				"    restrict_module(regular_module(field_ring(M)), point_chart(A₀, A₁, P)), point_ideal(A₀, P))"},
			{Name: "fibre", Text: "{φ:A → A | " +
				"    φ ∈ «pointsOf»(point_chart(A₀, A₁, P)) ∧ " +
				"    ring_kernel(M.zero, point_chart(A₀, A₁, P), φ) = point_ideal(A₀, P)}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Nat],
			P *Expr[Prod[Set[A], Set[A]]],
			closed, inField, curve, positive, point, divides Fact,
		) {
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			record := a.TermAs[FieldOps[A]]("M")
			inverse := a.TermAs[A]("M.inv(t)")
			zero := a.TermAs[A]("M.zero")
			constants := a.TermAs[Set[A]]("«constants»")
			properChart := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)")
			ideal := a.TermAs[Set[A]]("point_ideal(A₀, P)")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			firstChart := a.Have(
				"A₀ is a subring of M holding k",
				"subfield(M, k) ∧ k ⊆ A₀ ∧ subring(field_ring(M), A₀)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			secondChart := a.Have(
				"and so is A₁",
				"subfield(M, k) ∧ k ⊆ A₁ ∧ subring(field_ring(M), A₁)",
				By(inField, otherCurve, CurveChartsInField.Read(M).At(K, k, A1, A0, A01, inverse)))
			inChart := a.Have(
				"the chart P is proper in is either of them",
				"subring(field_ring(M), point_chart(A₀, A₁, P)) ∧ k ⊆ point_chart(A₀, A₁, P)",
				Simp(Fwd(biaffine_rational_point.PointChartDef)),
				By(firstChart, secondChart))
			maximal := a.Have(
				"the ideal of P is maximal in that chart",
				"maximal_ideal(restrict_ring(field_ring(M), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(
					point,
					smooth_curve.ClosedPointMaximal.At(a.TermAs[RingOps[A]]("«ambientRing»"), A0, A1, A01, P),
					module_record.RestrictRingTwice))
			residues := a.Have(
				"with finite residues over k",
				"finite_dimensional(«scalars», «residues»)",
				By(
					curve,
					point,
					a.Simplified(
						smooth_curve.ClosedPointResidue.Read(functionField).At(k, A0, A1, A01, t, P),
						InAmbient)))
			sized := a.Have(
				"so the points of the chart with that kernel number the degree of P, the dimension of the residues",
				"has_size(«fibre», «ambientPointDegree»(P))",
				By(
					M,
					closed,
					firstChart,
					curve,
					smooth_curve.SmoothFiniteFieldCurveDef,
					positive,
					inChart,
					maximal,
					residues,
					divides,
					smooth_curve.ClosedPointDegreeInField.At(record, K, k, A0, A1, P),
					residue_points.ConstantPointsWithKernel.Read(M).At(k, properChart, ideal, m)))
			atInfinity := a.Have(
				"a point in the second chart alone holds the inverse of t",
				"fst(P) = A₀ ⇒ M.inv(t) ∈ snd(P)",
				By(
					curve,
					point,
					a.Simplified(
						smooth_curve.ClosedPointContraction.Read(functionField).At(k, A0, A1, A01, t, P),
						InAmbient)))
			described := a.Have(
				"an evaluation point over P has the tag of its chart and a value in that fibre, and conversely",
				"∀p:prod(bool, A → A). "+
					"    (p ∈ «evaluation» ∧ «scOver»(p, P)) ⇔ (fst(p) ⇔ fst(P) = A₀) ∧ snd(p) ∈ «fibre»",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(biaffine_rational_point.PointChartDef), Fwd(biaffine_rational_point.PointIdealDef)))
					b.FixAs[Prod[Bool, Fun[A, A]]]("p")
					member := b.Have(
						"the evaluation points are the points of A₀ and the points of A₁ at the inverse of t",
						"p ∈ «evaluation» ⇔ "+
							"(¬fst(p) ∧ snd(p) ∈ «pointsOf»(A₀)) ∨ "+
							"(fst(p) ∧ snd(p) ∈ «pointsOf»(A₁) ∧ snd(p, M.inv(t)) = M.zero)",
						BySets(CurveEvaluationPointsDef.At(record, k, constants, A0, A1, t)))
					b.Iff()
					b.Forward(
						"a point over P has the tag and value it needs",
						func(c *Argument, over Fact) {
							c.Show(
								"its clauses are those of the membership",
								By(member, over))
						})
					b.Backward(
						"and such a pair is an evaluation point over P",
						func(c *Argument, tagged Fact) {
							vanishing := c.Have(
								"when P lies at infinity the value of p vanishes at the inverse of t",
								"fst(P) = A₀ ⇒ snd(p, M.inv(t)) = M.zero",
								Derive(func(d *Argument) {
									whole := d.Assume()
									value := d.TermAs[Fun[A, A]]("snd(p)")
									kernel := d.Have(
										"the chart being A₁, snd(P) is the kernel of the value",
										"ring_kernel(M.zero, A₁, snd(p)) = snd(P)",
										By(Normalized, tagged, whole))
									d.Show(
										"and it holds the inverse of t",
										BySets(kernel, atInfinity, whole, ring_homomorphism.RingKernelDef.At(zero, A1, value)))
								}))
							c.Show(
								"the clauses of the membership stand",
								By(member, vanishing, tagged))
						})
				}))
			same := a.Have(
				"the fibre over P is the tagged copy of the fibre of the chart",
				"{p:prod(bool, A → A) | p ∈ «evaluation» ∧ «scOver»(p, P)} = "+
					"{p:prod(bool, A → A) | (fst(p) ⇔ fst(P) = A₀) ∧ snd(p) ∈ «fibre»}",
				BySets(described))
			a.Show(
				"and the tagged copy has the same size",
				By(
					same,
					sized,
					cardinality.TaggedCopySize.At(
						a.TermAs[Bool]("fst(P) = A₀"),
						a.TermAs[Set[Fun[A, A]]]("«fibre»"),
						a.TermAs[Nat]("«ambientPointDegree»(P)"))))
		}),
})}

// EvaluationPointLiesOver — every evaluation point lies over exactly one closed
// point of degree dividing m. A point of a chart in the constants has a maximal
// kernel of degree dividing m. In A₀ that kernel is the first component of one
// closed point; in A₁ it holds the inverse of t, so it is the second component
// of a closed point proper in A₁ alone.
var EvaluationPointLiesOver = evaluationPointLiesOverThm{family.Add(registry.ProofEntry{
	Name: "EvaluationPointLiesOver",
	Key:  "prop_fc65f5f27f686fd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:num. ∀p:prod(bool, A → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < m",
			"p ∈ «evaluation»",
		},
		Conclusion: "∃!P:prod(set(A), set(A)). P ∈ «closedPoints» ∧ «scOver»(p, P)",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "evaluation", Text: "curve_evaluation_points(M, k, «constants», t, A₀, A₁)"},
			{Name: "closedPoints", Text: "{P:prod(set(A), set(A)) | " +
				"    «ambientPoint»(P) ∧ «ambientPointDegree»(P) ∣ m}"},
			{Name: "pointsOf", Text: "λS:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), S), " +
				"        restrict_ring(field_ring(M), «constants»), " +
				"        k, " +
				"        λx:A. x)"},
			{Name: "residueDegree", Text: "λS:set(A). λI:set(A). " +
				"    module_dim(restrict_ring(field_ring(M), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(M)), S), I))"},
			{Name: "kernel", Text: "λS:set(A). ring_kernel(M.zero, S, snd(p))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Nat],
			p *Expr[Prod[Bool, Fun[A, A]]],
			closed, inField, curve, positive, evaluated Fact,
		) {
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			record := a.TermAs[FieldOps[A]]("M")
			inverse := a.TermAs[A]("M.inv(t)")
			zero := a.TermAs[A]("M.zero")
			constants := a.TermAs[Set[A]]("«constants»")
			value := a.TermAs[Fun[A, A]]("snd(p)")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			firstChart := a.Have(
				"A₀ is a subring of M holding k",
				"subfield(M, k) ∧ k ⊆ A₀ ∧ subring(field_ring(M), A₀)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			secondChart := a.Have(
				"and so is A₁",
				"subfield(M, k) ∧ k ⊆ A₁ ∧ subring(field_ring(M), A₁)",
				By(inField, otherCurve, CurveChartsInField.Read(M).At(K, k, A1, A0, A01, inverse)))
			finiteK := a.Have(
				"k is finite",
				"finite(k)",
				By(curve, smooth_curve.SmoothFiniteFieldCurveDef))
			constantsField := a.Have(
				"the constants are a finite subfield of M",
				"subfield(M, «constants») ∧ k ⊆ «constants» ∧ finite(«constants»)",
				By(
					closed,
					positive,
					firstChart,
					finiteK,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
					cardinality.HasSizeDef))
			chartPoint := a.Have(
				"a point of a subring in the constants has a maximal kernel of degree dividing m",
				Statement{
					Binders:    "∀S:set(A). ∀φ:(A → A).",
					Hypotheses: []string{"subring(field_ring(M), S)", "k ⊆ S", "φ ∈ «pointsOf»(S)"},
					Conclusion: "maximal_ideal(restrict_ring(field_ring(M), S), ring_kernel(M.zero, S, φ)) ∧ " +
						"«residueDegree»(S, ring_kernel(M.zero, S, φ)) ∣ m",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					φ := b.FixAs[Fun[A, A]]("φ")
					given := b.Assume()
					ownKernel := b.TermAs[Set[A]]("ring_kernel(M.zero, S, φ)")
					residues := b.Have(
						"the kernel is maximal with finite residues",
						"maximal_ideal(restrict_ring(field_ring(M), S), ring_kernel(M.zero, S, φ)) ∧ "+
							"finite_dimensional(restrict_ring(field_ring(M), k), "+
							"    quotient_module(restrict_module(regular_module(field_ring(M)), S), "+
							"        ring_kernel(M.zero, S, φ)))",
						By(
							M,
							given,
							firstChart,
							constantsField,
							residue_points.PointKernelMaximal.Read(M).At(k, S, constants, φ)))
					b.Show(
						"and φ itself is a point with that kernel, so the degree divides m",
						By(
							M,
							closed,
							finiteK,
							positive,
							given,
							firstChart,
							residues,
							residue_points.ConstantPointsWithKernel.Read(M).At(k, S, ownKernel, m)))
				}))
			member := a.Have(
				"p is a point of A₀, or a point of A₁ vanishing at the inverse of t",
				"(¬fst(p) ∧ snd(p) ∈ «pointsOf»(A₀)) ∨ "+
					"(fst(p) ∧ snd(p) ∈ «pointsOf»(A₁) ∧ snd(p, M.inv(t)) = M.zero)",
				BySets(evaluated, CurveEvaluationPointsDef.At(record, k, constants, A0, A1, t)))
			a.Cases(a.Term("fst(p)"))
			a.When(
				"a point of A₁ lies over the closed point with first component A₀",
				func(b *Argument, tagged Fact) {
					kernel := b.TermAs[Set[A]]("«kernel»(A₁)")
					Q := b.TermAs[Prod[Set[A], Set[A]]]("(A₀, «kernel»(A₁))")
					inSecond := b.Conjuncts(
						b.Have(
							"its value is a point of A₁ vanishing at the inverse of t",
							"snd(p) ∈ «pointsOf»(A₁) ∧ snd(p, M.inv(t)) = M.zero",
							By(member, tagged)),
						"its value is a point of A₁",
						"which vanishes at the inverse of t")
					read := b.Have(
						"its kernel is maximal of degree dividing m",
						"maximal_ideal(restrict_ring(field_ring(M), A₁), «kernel»(A₁)) ∧ "+
							"«residueDegree»(A₁, «kernel»(A₁)) ∣ m",
						By(chartPoint.At(A1, value), inSecond[0], secondChart))
					holdsInverse := b.Have(
						"and it holds the inverse of t",
						"M.inv(t) ∈ «kernel»(A₁)",
						BySets(
							inSecond[1],
							inField,
							b.Unfolded(otherCurve, smooth_curve.SmoothFiniteFieldCurveDef),
							CurveOverLineFirstChart.Read(M).At(K, k, A1, A0, A01, inverse),
							ring_homomorphism.RingKernelDef.At(zero, A1, value)))
					point := b.Have(
						"so the pair is a closed point",
						"«ambientPoint»((A₀, «kernel»(A₁)))",
						By(
							inField,
							curve,
							read,
							holdsInverse,
							ClosedPointAtInfinity.Read(M).At(K, k, A0, A1, A01, t, kernel)))
					components := b.Have(
						"with those components",
						"fst((A₀, «kernel»(A₁))) = A₀ ∧ snd((A₀, «kernel»(A₁))) = «kernel»(A₁)",
						By(pairs.Fst, pairs.Snd))
					degree := b.Have(
						"and its degree is that of the kernel",
						"«ambientPointDegree»((A₀, «kernel»(A₁))) = «residueDegree»(A₁, «kernel»(A₁))",
						By(
							components,
							smooth_curve.ClosedPointDegreeInField.At(record, K, k, A0, A1, Q),
							biaffine_rational_point.PointOffChartZero.At(A0, A1, Q)))
					b.Take(Q)
					b.Do(SplitConj(
						Case(
							"the pair is one of the closed points, and p lies over it",
							Simp(Fwd(biaffine_rational_point.PointChartDef), Fwd(biaffine_rational_point.PointIdealDef)),
							By(tagged, degree, read, components, point)),
						Case(
							"a closed point under p has those components",
							Derive(func(c *Argument) {
								y := c.FixAs[Prod[Set[A], Set[A]]]("y")
								under := c.Assume()
								whole := c.Have(
									"the tag says its first component is A₀",
									"fst(y) = A₀",
									By(tagged, under))
								second := c.Have(
									"so its second is the kernel",
									"snd(y) = «kernel»(A₁)",
									By(Normalized, whole, under, biaffine_rational_point.PointOffChartZero.At(A0, A1, y)))
								c.Show(
									"and a pair is its components",
									By(Normalized, whole, second, pairs.PairEta.At(y)))
							}))))
				})
			a.Otherwise(
				"a point of A₀ lies over the closed point with first component its kernel",
				func(b *Argument, untagged Fact) {
					kernel := b.TermAs[Set[A]]("«kernel»(A₀)")
					read := b.Have(
						"its value is a point of A₀, so its kernel is maximal of degree dividing m",
						"maximal_ideal(restrict_ring(field_ring(M), A₀), «kernel»(A₀)) ∧ "+
							"«residueDegree»(A₀, «kernel»(A₀)) ∣ m",
						By(chartPoint.At(A0, value), member, untagged, firstChart))
					proper := b.Have(
						"so it is proper",
						"«kernel»(A₀) ≠ A₀",
						By(
							firstChart,
							read,
							ring_ideal.MaximalIdealNotWhole.At(b.TermAs[RingOps[A]]("field_ring(M)"), A0, kernel)))
					Q, atKernel := b.ObtainAs[Prod[Set[A], Set[A]]](
						"it is the first component of exactly one closed point",
						"∃Q:prod(set(A), set(A)). "+
							"    «ambientPoint»(Q) ∧ "+
							"    fst(Q) = «kernel»(A₀) ∧ "+
							"    (∀P:prod(set(A), set(A)). «ambientPoint»(P) ∧ fst(P) = «kernel»(A₀) ⇒ P = Q)",
						By(
							curve,
							read,
							b.Simplified(
								smooth_curve.ChartMaximalClosedPoint.Read(functionField).At(k, A0, A1, A01, t, kernel),
								InAmbient)))
					parts := b.Conjuncts(
						atKernel,
						"Q is a closed point",
						"its first component is the kernel",
						"no other closed point has it")
					properQ := b.Have(
						"Q is proper in A₀",
						"fst(Q) ≠ A₀",
						By(Normalized, parts[1], proper))
					degree := b.Have(
						"so its degree is that of the kernel",
						"«ambientPointDegree»(Q) = «residueDegree»(A₀, «kernel»(A₀))",
						By(
							properQ,
							parts[1],
							smooth_curve.ClosedPointDegreeInField.At(record, K, k, A0, A1, Q),
							biaffine_rational_point.PointOnChartZero.At(A0, A1, Q)))
					lyingOver := b.Have(
						"lying over a proper point is having no tag and that point's first component for kernel",
						"∀P:prod(set(A), set(A)). fst(P) ≠ A₀ ⇒ («scOver»(p, P) ⇔ ¬fst(p) ∧ «kernel»(A₀) = fst(P))",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(biaffine_rational_point.PointChartDef), Fwd(biaffine_rational_point.PointIdealDef)))
							c.FixAs[Prod[Set[A], Set[A]]]("P")
							properP := c.Assume()
							c.Show(
								"its conditionals read the first chart",
								By(Normalized, properP))
						}))
					b.Take(Q)
					b.Do(SplitConj(
						Case(
							"Q is one of the closed points, and p lies over it",
							By(untagged, properQ, lyingOver.At(Q), parts[0], parts[1], degree, read)),
						Case(
							"a closed point under p is Q",
							Derive(func(c *Argument) {
								y := c.FixAs[Prod[Set[A], Set[A]]]("y")
								under := c.Assume()
								properY := c.Have(
									"the tag says it is proper in A₀",
									"fst(y) ≠ A₀",
									By(Normalized, untagged, under))
								c.Show(
									"so its first component is the kernel",
									By(lyingOver.At(y), parts[2].At(y), untagged, under, properY))
							}))))
				})
		}),
})}

// ExtensionCountClosedPoints — the point count of the curve over the field with
// q^m elements is the sum of the degrees of the closed points whose degree
// divides m: that count is the number of evaluation points, and these fall into
// the fibres over those closed points, each as large as the degree.
var ExtensionCountClosedPoints = extensionCountClosedPointsThm{family.Add(registry.ProofEntry{
	Name: "ExtensionCountClosedPoints",
	Key:  "prop_da9d5962ab63dd51",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < m",
		},
		Conclusion: "curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m) = " +
			"nat_sum(«closedPoints», «ambientPointDegree»)",
		Abbrev: Abbrev{
			{Name: "closedPoints", Text: "{P:prod(set(A), set(A)) | " +
				"    «ambientPoint»(P) ∧ «ambientPointDegree»(P) ∣ m}"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "evaluation", Text: "curve_evaluation_points(M, k, «constants», t, A₀, A₁)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Nat],
			closed, inField, curve, positive Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			constants := a.TermAs[Set[A]]("«constants»")
			evaluation := a.TermAs[Set[Prod[Bool, Fun[A, A]]]]("«evaluation»")
			closedPoints := a.TermAs[Set[Prod[Set[A], Set[A]]]]("«closedPoints»")
			over := a.TermAs[Fun[Prod[Bool, Fun[A, A]], Fun[Prod[Set[A], Set[A]], Bool]]]("«scOver»")
			degree := a.TermAs[Fun[Prod[Set[A], Set[A]], Nat]]("«ambientPointDegree»")
			firstChart := a.Have(
				"k is a subfield of M, and A₀ a subring of M holding it",
				"subfield(M, k) ∧ k ⊆ A₀ ∧ subring(field_ring(M), A₀)",
				By(inField, curve, CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			data := a.Have(
				"the curve lies over the line and k is finite",
				"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁) ∧ finite(k)",
				By(curve, smooth_curve.SmoothFiniteFieldCurveDef))
			constantsField := a.Have(
				"the constants are a finite subfield of M holding k",
				"subfield(M, «constants») ∧ k ⊆ «constants» ∧ finite(«constants»)",
				By(
					closed,
					positive,
					firstChart,
					data,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
					cardinality.HasSizeDef))
			count := a.Have(
				"at positive m the count is the rational point count over the constants",
				"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m) = "+
					"curve_rational_point_count(field_ring(M), k, «constants», A₀, A₁, A₀₁)",
				ByArith(positive, CurveExtensionCountDef.At(ring, k, A0, A1, A01, m)))
			evaluations := a.Have(
				"which is the number of evaluation points",
				"finite(«evaluation») ∧ "+
					"card(«evaluation») = curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m)",
				By(
					M,
					inField,
					constantsField,
					data,
					curve,
					count,
					EvaluationPointsCount.Read(M).At(K, k, A0, A1, A01, t, constants)))
			under := a.Have(
				"each evaluation point lies over exactly one of these closed points",
				Statement{
					Binders: "∀p:prod(bool, A → A).",
					Hypotheses: []string{
						"p ∈ «evaluation»",
					},
					Conclusion: "∃!P:prod(set(A), set(A)). P ∈ «closedPoints» ∧ «scOver»(p, P)",
				},
				a.ForEach(func(p *Expr[Prod[Bool, Fun[A, A]]]) Action {
					return By(
						closed,
						inField,
						curve,
						positive,
						EvaluationPointLiesOver.Read(M).At(K, k, A0, A1, A01, t, m, p))
				}))
			sizes := a.Have(
				"and over each of them lie as many evaluation points as its degree",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"P ∈ «closedPoints»",
					},
					Conclusion: "has_size({p:prod(bool, A → A) | p ∈ «evaluation» ∧ «scOver»(p, P)}, " +
						"    «ambientPointDegree»(P))",
				},
				a.ForEach(func(P *Expr[Prod[Set[A], Set[A]]]) Action {
					return By(
						closed,
						inField,
						curve,
						positive,
						EvaluationFibreSize.Read(M).At(K, k, A0, A1, A01, t, m, P))
				}))
			a.Show(
				"so the count is the sum of the degrees",
				By(evaluations, under, sizes, nat_sum.CardByFibres.At(evaluation, closedPoints, over, degree)))
		}),
})}
