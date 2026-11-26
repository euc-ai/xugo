// evaluation_points.go — the evaluation points of a curve counted. A ring
// finitely generated over k has finitely many points in a finite ring, so each
// chart has, and a point of the overlap is a point of the second chart making
// t⁻¹ a unit. The evaluation points are the points of the first chart beside
// the points at infinity of the second, and their number is the rational point
// count.

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartPointsFinite — a chart of a curve has finitely many points in a finite
// ring: it is generated over k by t and a finite basis over k[t], since a
// subring of the chart holding k and t holds k[t], so is a k[t]-submodule, and
// holding the basis it holds the span.
var ChartPointsFinite = chartPointsFiniteThm{family.Add(registry.ProofEntry{
	Name: "ChartPointsFinite",
	Key:  "prop_9a1ad672c3d82424",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀T:ring_ops(B). ∀i:(A → B).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"finite(T.carrier)",
		},
		Conclusion: "finite(algebra_points(«chart», T, k, i))",
		Abbrev: Abbrev{
			{Name: "chart", Text: "restrict_ring(field_ring(L), A₀)"},
			{Name: "polynomials", Text: "restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t))"},
			{Name: "chartVectors", Text: "restrict_module(regular_module(field_ring(L)), A₀)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			T *Expr[RingOps[B]],
			i *Arrow[A, B],
			curve, finiteT Fact,
		) {
			data := a.Conjuncts(
				a.Have(
					"the chart holds k and t, and has a finite basis over k[t]",
					"k ⊆ A₀ ∧ "+
						"t ∈ A₀ ∧ "+
						"subring(field_ring(L), A₀) ∧ "+
						"(∃E:set(A). finite(E) ∧ module_basis(«polynomials», «chartVectors», E))",
					BySets(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"k lies in the chart",
				"so does t",
				"the chart is a subring of L",
				"it has a finite basis over k[t]")
			kInChart, tInChart, chartSubring := data[0], data[1], data[2]
			E, basisData := a.UnpackAs[Set[A]](data[3], "E")
			basis := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a basis")
			finiteE := basis[0]
			basisClauses := a.Unfolded(basis[1], linear_independence.ModuleBasisDef)
			independenceClauses := a.Unfolded(basisClauses, linear_independence.ModuleIndependentDef)
			spans := a.Have(
				"E lies in the chart and spans it",
				"E ⊆ A₀ ∧ module_span(«polynomials», «chartVectors», E) = A₀",
				By(independenceClauses, basisClauses))
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			chartRing := a.TermAs[RingOps[A]]("«chart»")
			polynomials := a.TermAs[RingOps[A]]("«polynomials»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«chartVectors»")
			generated := a.Have(
				"a subring of the chart holding k, t and E is the chart",
				"∀C:set(A). subring(«chart», C) ∧ k ⊆ C ∧ t ∈ C ∧ E ⊆ C ⇒ A₀ ⊆ C",
				Derive(func(b *Argument) {
					C := b.FixAs[Set[A]]("C")
					assumed := b.Conjuncts(
						b.Assume(),
						"C is a subring of the chart",
						"C holds k",
						"C holds t",
						"C holds E")
					subringC, kInC, tInC, eInC := assumed[0], assumed[1], assumed[2], assumed[3]
					subringOfL := b.Have(
						"C is a subring of L",
						"subring(field_ring(L), C)",
						BySets(
							chartSubring,
							subringC,
							comm_ring.SubringDef.At(fieldRing, C),
							comm_ring.SubringDef.At(chartRing, C),
							comm_ring.SubringDef.At(fieldRing, A0)))
					polynomialsInC := b.Have(
						"so C holds k[t], the least ring holding k and t",
						"polynomial_image(field_ring(L), k, t) ⊆ C",
						By(
							subringOfL,
							kInC,
							tInC,
							comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(C),
							algebraic_element.PolynomialImageLeast.Read(L).At(k, C, t)))
					submoduleC := b.Have(
						"so C is a k[t]-submodule of the chart",
						"submodule(«polynomials», «chartVectors», C)",
						Unfold(submodule.SubmoduleDef),
						Unfold(group.SubgroupDef),
						BySets(subringC, polynomialsInC, comm_ring.SubringDef.At(chartRing, C)))
					b.Show(
						"holding E, it holds the span of E, which is the chart",
						By(Normalized, eInC, spans, submoduleC, submodule.SpanLeast.At(polynomials, vectors, E, C)))
				}))
			conditions := a.Have(
				"t and E are finitely many generators of the chart over k",
				"insert(t, E) ⊆ A₀ ∧ "+
					"finite(insert(t, E)) ∧ "+
					"(∀C:set(A). subring(«chart», C) ∧ k ⊆ C ∧ insert(t, E) ⊆ C ⇒ A₀ ⊆ C)",
				BySets(finiteE, generated, tInChart, spans, finite_set.FiniteInsert.At(t, E)))
			a.Show(
				"a ring finitely generated over k has finitely many points",
				By(
					conditions,
					finiteT,
					kInChart,
					algebra_point_bounds.AlgebraPointsGeneratedFinite.At(
						chartRing, T, k, a.TermAs[Set[A]]("insert(t, E)"), i)))
		}),
})}

// OverlapPointsAway — restriction to the second chart takes the points of the
// overlap one to one onto the points of that chart at which t⁻¹ is a unit: the
// overlap is the chart with t⁻¹ inverted.
var OverlapPointsAway = overlapPointsAwayThm{family.Add(registry.ProofEntry{
	Name: "OverlapPointsAway",
	Key:  "prop_be6355012170dc24",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "targetRing", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "overlap", Text: "restrict_ring(field_ring(M), A₀₁)"},
			{Name: "points", Text: "λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), «targetRing», k, λx:A. x)"},
			{Name: "restriction", Text: "λφ:(A → A). λx:A. COND(x ∈ A₁, φ(x), «targetRing».zero)"},
			{Name: "away", Text: "{ψ:A → A | ψ ∈ «points»(A₁) ∧ ring_unit(«targetRing», ψ(M.inv(t)))}"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "injective_on(«points»(A₀₁), «restriction») ∧ " +
			"image(«restriction», «points»(A₀₁)) = «away»",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Expr[Set[A]],
			subfieldK, curve Fact,
		) {
			functionFieldOn := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			charts := a.Conjuncts(
				a.Have(
					"read in M, the second chart holds k and t⁻¹ and the charts are biaffine in the overlap",
					"k ⊆ A₁ ∧ M.inv(t) ∈ A₁ ∧ biaffine(«overlap», A₀, A₁, t, M.inv(t))",
					BySets(a.Simplified(
						GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(functionFieldOn).At(k, A0, A1, A01, t)),
						Fwd(field.RestrictFieldRecords)))),
				"k lies in the second chart",
				"so does t⁻¹",
				"the charts are biaffine")
			kInOne, inverseInOne, biaffine := charts[0], charts[1], charts[2]
			overlapRing := a.TermAs[RingOps[A]]("«overlap»")
			inverseT := a.TermAs[A]("M.inv(t)")
			localization := a.Have(
				"the overlap is the second chart with t⁻¹ inverted",
				"is_localization_on(restrict_ring(«overlap», A₁), "+
					"    monoid_powers(«overlap».mul, «overlap».one, M.inv(t)), "+
					"    «overlap», "+
					"    λx:A. x)",
				By(biaffine, lattice_pair.BiaffineChartLocalization.At(overlapRing, A0, A1, t, inverseT)))
			chartInOverlap := a.Have(
				"the second chart reads the same inside the overlap",
				"restrict_ring(«overlap», A₁) = restrict_ring(field_ring(M), A₁)",
				By(module_record.RestrictRingTwice.At(a.TermAs[RingOps[A]]("field_ring(M)"), A01, A1)))
			a.Show(
				"a point of a ring with an element inverted is a point making it a unit",
				chartInOverlap.RwRev(),
				By(
					kInOne,
					inverseInOne,
					localization,
					algebra_point_bounds.AlgebraPointsAway.At(
						overlapRing,
						a.TermAs[RingOps[A]]("«targetRing»"),
						A1,
						k,
						a.TermAs[Fun[A, A]]("λx:A. x"),
						inverseT)))
		}),
})}

// CurvePointSetsFinite — the two charts and the overlap of a curve have
// finitely many points in a finite set: the charts by their finite generation,
// and the points of the overlap inject into those of the second chart, the
// overlap being that chart with t⁻¹ inverted.
var CurvePointSetsFinite = curvePointSetsFiniteThm{family.Add(registry.ProofEntry{
	Name: "CurvePointSetsFinite",
	Key:  "prop_5e44c3587b515140",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "targetRing", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "overlap", Text: "restrict_ring(field_ring(M), A₀₁)"},
			{Name: "points", Text: "λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), «targetRing», k, λx:A. x)"},
			{Name: "restriction", Text: "λφ:(A → A). λx:A. COND(x ∈ A₁, φ(x), «targetRing».zero)"},
			{Name: "away", Text: "{ψ:A → A | ψ ∈ «points»(A₁) ∧ ring_unit(«targetRing», ψ(M.inv(t)))}"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"finite(l)",
		},
		Conclusion: "finite(«points»(A₀)) ∧ finite(«points»(A₁)) ∧ finite(«points»(A₀₁))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Expr[Set[A]],
			subfieldK, curve, finiteL Fact,
		) {
			targetRing := a.TermAs[RingOps[A]]("«targetRing»")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			pointsOne := a.TermAs[Set[Fun[A, A]]]("«points»(A₁)")
			pointsOverlap := a.TermAs[Set[Fun[A, A]]]("«points»(A₀₁)")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			functionFieldOn := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			finiteZero := a.Simplified(
				GroupPremises(
					curve,
					finiteL,
					ChartPointsFinite.Read(functionFieldOn).At(k, A0, A1, A01, t, targetRing, identity)),
				Fwd(field.RestrictFieldRecords))
			finiteOne := a.Have(
				"so has the second, read through the swap",
				"finite(«points»(A₁))",
				By(
					finiteL,
					curve,
					algebraic_curve.CurveSwap.Read(functionFieldOn).At(k, A0, A1, A01, t),
					a.Simplified(
						ChartPointsFinite.Read(functionFieldOn).At(
							k, A1, A0, A01, a.TermAs[A]("restrict_field(M, K).inv(t)"), targetRing, identity),
						Fwd(field.RestrictFieldRecords))))
			bijection := a.Conjuncts(
				a.Have(
					"points of the overlap are the points of the second chart making t⁻¹ a unit",
					"injective_on(«points»(A₀₁), «restriction») ∧ image(«restriction», «points»(A₀₁)) = «away»",
					By(subfieldK, curve, OverlapPointsAway.Read(M).At(K, k, A0, A1, A01, t, l))),
				"restriction is injective on the points of the overlap",
				"its image is the points making t⁻¹ a unit")
			injective, image := bijection[0], bijection[1]
			finiteImage := a.Have(
				"the image is finite, inside the points of the second chart",
				"finite(image(«restriction», «points»(A₀₁)))",
				image.Rw(),
				By(
					finiteOne,
					finite_set.FiniteRestrict.At(
						pointsOne, a.TermAs[Set[Fun[A, A]]]("λψ:(A → A). ring_unit(«targetRing», ψ(M.inv(t)))"))))
			a.Show(
				"so the overlap has finitely many points",
				By(
					finiteZero,
					finiteOne,
					finiteImage,
					injective,
					finite_set.FiniteImageInjEq.At(restriction, pointsOverlap)))
		}),
})}

// EvaluationPointsCount — the normalized evaluation maps on the two charts,
// each point at infinity taken from the second chart, are finite in number
// and counted by the two charts less their overlap. A point of the overlap
// restricts to a point of the second chart at which t⁻¹ is a unit, and every
// such point arises once (OverlapPointsAway), so the second chart is its
// points at infinity beside a copy of the overlap's points.
var EvaluationPointsCount = evaluationPointsCountThm{family.Add(registry.ProofEntry{
	Name: "EvaluationPointsCount",
	Key:  "prop_dbef7aa7de42581b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"finite(l)",
		},
		Conclusion: "finite(curve_evaluation_points(M, k, l, t, A₀, A₁)) ∧ " +
			"card(curve_evaluation_points(M, k, l, t, A₀, A₁)) = " +
			"curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁)",
		Abbrev: Abbrev{
			{Name: "targetRing", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "overlap", Text: "restrict_ring(field_ring(M), A₀₁)"},
			{Name: "pointsZero", Text: "algebra_points(restrict_ring(field_ring(M), A₀), " +
				"    «targetRing», " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "pointsOne", Text: "algebra_points(restrict_ring(field_ring(M), A₁), " +
				"    «targetRing», " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "pointsOverlap", Text: "algebra_points(«overlap», «targetRing», k, λx:A. x)"},
			{Name: "restriction", Text: "λφ:(A → A). λx:A. COND(x ∈ A₁, φ(x), «targetRing».zero)"},
			{Name: "atInfinity", Text: "{ψ:A → A | ψ ∈ «pointsOne» ∧ ψ(M.inv(t)) = M.zero}"},
			{Name: "away", Text: "{ψ:A → A | ψ ∈ «pointsOne» ∧ ring_unit(«targetRing», ψ(M.inv(t)))}"},
			{Name: "tagged", Text: "{p:prod(bool, A → A) | " +
				"    (¬fst(p) ∧ snd(p) ∈ «pointsZero») ∨ (fst(p) ∧ snd(p) ∈ «atInfinity»)}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Expr[Set[A]],
			subfieldK, curve, subfieldL, finiteL Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			targetRing := a.TermAs[RingOps[A]]("«targetRing»")
			secondChart := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), A₁)")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			inverseT := a.TermAs[A]("M.inv(t)")
			pointsOne := a.TermAs[Set[Fun[A, A]]]("«pointsOne»")
			pointsOverlap := a.TermAs[Set[Fun[A, A]]]("«pointsOverlap»")
			atInfinity := a.TermAs[Set[Fun[A, A]]]("«atInfinity»")
			away := a.TermAs[Set[Fun[A, A]]]("«away»")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			finitePoints := a.Conjuncts(
				a.Have(
					"the charts and the overlap have finitely many points in l",
					"finite(«pointsZero») ∧ finite(«pointsOne») ∧ finite(«pointsOverlap»)",
					By(subfieldK, curve, finiteL, CurvePointSetsFinite.Read(M).At(K, k, A0, A1, A01, t, l))),
				"the first chart has finitely many points",
				"so has the second",
				"so has the overlap")
			finiteZero, finiteOne, finiteOverlap := finitePoints[0], finitePoints[1], finitePoints[2]
			bijection := a.Conjuncts(
				a.Have(
					"points of the overlap are the points of the second chart making t⁻¹ a unit",
					"injective_on(«pointsOverlap», «restriction») ∧ image(«restriction», «pointsOverlap») = «away»",
					By(subfieldK, curve, OverlapPointsAway.Read(M).At(K, k, A0, A1, A01, t, l))),
				"restriction is injective on the points of the overlap",
				"its image is the points making t⁻¹ a unit")
			injective, image := bijection[0], bijection[1]
			functionFieldOn := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			inverseInOne := a.Have(
				"the second chart holds t⁻¹",
				"M.inv(t) ∈ A₁",
				By(curve, algebraic_curve.CurveOverItsLine.Read(functionFieldOn).At(k, A0, A1, A01, t)))
			units := a.Have(
				"the units of l are its nonzero elements",
				"∀x:A. x ∈ l ⇒ (ring_unit(«targetRing», x) ⇔ x ≠ M.zero)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inL := b.Assume()
					b.Iff()
					b.Forward(
						"a unit is not zero, zero having no inverse",
						func(c *Argument, unit Fact) {
							y, inverse := c.ObtainAs[A](
								"x has an inverse in l",
								"∃y:A. y ∈ l ∧ x * y = M.one",
								By(unit, ring_ideal.RingUnitDef.At(targetRing, x)))
							c.Show(
								"were x zero, one would be zero",
								By(
									subfieldL,
									inverse,
									field.SubfieldSubset.At(fieldM, l),
									set_basic.SubsetDef,
									field.OneNotZeroOn.Read(M),
									comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(M)).AsFact().At(y)))
						})
					b.Backward(
						"a nonzero element of l has its inverse in l",
						func(c *Argument, nonzero Fact) {
							inverted := c.Have(
								"M inverts x inside l",
								"∃y:A. y ∈ l ∧ x * y = M.one",
								Witness(c.TermAs[A]("M.inv(x)")),
								By(
									nonzero,
									inL,
									subfieldL,
									field.SubfieldInv.At(fieldM, l, x),
									field.SubfieldSubset.At(fieldM, l),
									set_basic.SubsetDef,
									field.MulRightInverseOn.Read(M).AsFact().At(x)))
							c.Show(
								"so x is a unit of l",
								By(inL, inverted, ring_ideal.RingUnitDef.At(targetRing, x)))
						})
				}))
			values := a.Have(
				"a point of the second chart sends t⁻¹ into l",
				"∀ψ:(A → A). ψ ∈ «pointsOne» ⇒ ψ(M.inv(t)) ∈ l",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]("ψ")
					point := b.Assume()
					ringMap := b.Have(
						"it is a ring map from the second chart to l",
						"ring_homomorphism(restrict_ring(field_ring(M), A₁), «targetRing», ψ)",
						By(point, algebra_points.AlgebraPointsMember.At(secondChart, targetRing, k, identity, ψ)))
					b.Show(
						"and t⁻¹ lies in the second chart",
						By(inverseInOne, ring_homomorphism.MapIn.Read(ringMap).AsFact().At(inverseT)))
				}))
			partition := a.Have(
				"a point of the second chart vanishes at t⁻¹ or makes it a unit, and not both",
				"«atInfinity» ∪ «away» = «pointsOne» ∧ «atInfinity» ∩ «away» = ∅",
				BySets(units, values))
			finiteInfinity := a.Have(
				"the points at infinity are finite",
				"finite(«atInfinity»)",
				By(
					finiteOne,
					finite_set.FiniteRestrict.At(
						pointsOne, a.TermAs[Set[Fun[A, A]]]("λψ:(A → A). ψ(M.inv(t)) = M.zero"))))
			overlapCount := a.Have(
				"and as many as there are points away from infinity",
				"card(«away») = card(«pointsOverlap»)",
				image.RwRev(),
				By(finiteOverlap, injective, cardinality.CardImageInj.At(restriction, pointsOverlap)))
			chartCount := a.Have(
				"the second chart counts its two parts",
				"card(«pointsOne») = card(«atInfinity») + card(«away»)",
				By(finiteOne, partition, cardinality.CardOfDisjointParts.At(atInfinity, away, pointsOne)))
			evaluation := a.Have(
				"the evaluation points are the first chart's points beside the points at infinity",
				"curve_evaluation_points(M, k, l, t, A₀, A₁) = «tagged»",
				Unfold(CurveEvaluationPointsDef),
				BySets())
			taggedParts := a.Conjuncts(
				a.Have(
					"tagging the two finite sets adds their sizes",
					"finite(«tagged») ∧ card(«tagged») = card(«pointsZero») + card(«atInfinity»)",
					By(
						finiteZero,
						finiteInfinity,
						cardinality.TaggedUnionCount.At(a.TermAs[Set[Fun[A, A]]]("«pointsZero»"), atInfinity))),
				"the tagged set is finite",
				"its size is the sum")
			finiteTagged, taggedCount := taggedParts[0], taggedParts[1]
			count := a.Have(
				"the overlap cancels against the points away from infinity",
				"card(«tagged») = card(«pointsZero») + card(«pointsOne») - card(«pointsOverlap»)",
				ByArith(overlapCount, chartCount, taggedCount))
			a.Show(
				"the evaluation points are finite and so counted",
				Unfold(CurveRationalPointCountDef),
				evaluation.Rw(),
				By(finiteTagged, count))
		}),
})}

// CurveCountAtInfinity — the rational point count of a curve is the number of
// points of the first chart and the points of the second chart that kill t⁻¹:
// these two sets, tagged apart, are the evaluation points (EvaluationPointsCount).
var CurveCountAtInfinity = curveCountAtInfinityThm{family.Add(registry.ProofEntry{
	Name: "CurveCountAtInfinity",
	Key:  "prop_408d12f5e21c8d67",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"finite(l)",
		},
		Conclusion: "finite(«atInfinity») ∧ " +
			"curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁) = " +
			"card(«pointsZero») + card(«atInfinity»)",
		Abbrev: Abbrev{
			{Name: "targetRing", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "pointsZero", Text: "algebra_points(restrict_ring(field_ring(M), A₀), " +
				"    «targetRing», " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "pointsOne", Text: "algebra_points(restrict_ring(field_ring(M), A₁), " +
				"    «targetRing», " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "pointsOverlap", Text: "algebra_points(restrict_ring(field_ring(M), A₀₁), " +
				"    «targetRing», " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "atInfinity", Text: "{ψ:A → A | ψ ∈ «pointsOne» ∧ ψ(M.inv(t)) = M.zero}"},
			{Name: "tagged", Text: "{p:prod(bool, A → A) | " +
				"    (¬fst(p) ∧ snd(p) ∈ «pointsZero») ∨ (fst(p) ∧ snd(p) ∈ «atInfinity»)}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Expr[Set[A]],
			subfieldK, curve, subfieldL, finiteL Fact,
		) {
			finitePoints := a.Conjuncts(
				a.Have(
					"the charts have finitely many points in l",
					"finite(«pointsZero») ∧ finite(«pointsOne») ∧ finite(«pointsOverlap»)",
					By(subfieldK, curve, finiteL, CurvePointSetsFinite.Read(M).At(K, k, A0, A1, A01, t, l))),
				"the first chart has finitely many points",
				"so has the second",
				"so has the overlap")
			finiteZero, finiteOne := finitePoints[0], finitePoints[1]
			finiteInfinity := a.Have(
				"so has the part of the second chart at infinity",
				"finite(«atInfinity»)",
				By(
					finiteOne,
					finite_set.FiniteRestrict.At(
						a.TermAs[Set[Fun[A, A]]]("«pointsOne»"),
						a.TermAs[Set[Fun[A, A]]]("λψ:(A → A). ψ(M.inv(t)) = M.zero"))))
			evaluation := a.Have(
				"the evaluation points are the first chart's points beside the points at infinity",
				"curve_evaluation_points(M, k, l, t, A₀, A₁) = «tagged»",
				Unfold(CurveEvaluationPointsDef),
				BySets())
			counted := a.Have(
				"the rational points are the evaluation points",
				"card(«tagged») = curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁)",
				evaluation.RwRev(),
				By(subfieldK, curve, subfieldL, finiteL, EvaluationPointsCount.Read(M).At(K, k, A0, A1, A01, t, l)))
			a.Show(
				"tagging the two finite sets adds their sizes",
				By(
					finiteZero,
					finiteInfinity,
					counted,
					cardinality.TaggedUnionCount.At(
						a.TermAs[Set[Fun[A, A]]]("«pointsZero»"), a.TermAs[Set[Fun[A, A]]]("«atInfinity»"))))
		}),
})}
