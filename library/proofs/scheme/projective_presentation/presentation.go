// presentation.go — the finite presentation of a smooth projective equation
// curve over a finite field: the charts of F = Xⱼ^r and of a second form G of
// degree r with no zero in common with F on the curve make a smooth finite
// curve inside M, with the curve's Hilbert genus and its points over every
// finite extension.

package projective_presentation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_chart"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_generic_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothProjectiveBiaffinePresentation — a smooth projective equation curve
// over a finite field has a smooth finite two-chart presentation inside M
// with its Hilbert genus and its points over every finite extension: a
// generic point x generates the function field K
// (projective_generic_point.GenericPointExists), with x(j) = one for some j;
// the zeros of Xⱼ on the curve lie over one finite field
// (projective_form_pair.FormZerosRational), where a form H of some degree r
// has no zero but the origin (projective_form_pair.AnisotropicForm).
// F = Xⱼ^r and G = H, or G = H + F where H vanishes at x, are then two forms
// of degree r with no common zero on the curve, and their charts are the
// presentation (projective_form_chart.FormChartsAreCurve,
// projective_form_chart.FormChartIntegrallyClosed,
// ProjectiveGenusIsCurveGenus, PointsMatchCharts).
var SmoothProjectiveBiaffinePresentation = smoothProjectiveBiaffinePresentationThm{family.Add(registry.ProofEntry{
	Name: "SmoothProjectiveBiaffinePresentation",
	Key:  "prop_9be59ec6898866e",
	Reading: "The statement keeps of the presentation what " +
		"weil_curve.FullWeilProjectiveEquationCurves reads: the field, the smooth curve, " +
		"the genus and the points. It does not state the generic field or separability " +
		"over k(t); t = G(x)/x(j)^r is not a separating parameter and need not be. The " +
		"point of M transcendental over k is a hypothesis the presentation itself needs.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"∃u:A. u ∈ M.carrier ∧ ¬algebraic_over(M, k, u)",
			"smooth_projective_equation_curve(M, k, n, E)",
		},
		Conclusion: "∃K A₀ A₁ A₀₁:set(A). ∃t:A. " +
			"    subfield(M, K) ∧ " +
			"    smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁) ∧ " +
			"    curve_genus(restrict_ring(field_ring(M), K), k, A₀, A₁, A₀₁) = " +
			"    projective_equation_genus(field_ring(M), k, n, E) ∧ " +
			"    (∀m:num. " +
			"        0 < m ⇒ " +
			"        ∃f:((num → A) → prod(bool, A → A)). " +
			"            injective_on(«points»(m), f) ∧ " +
			"            image(f, «points»(m)) = " +
			"            curve_evaluation_points(M, " +
			"                k, " +
			"                finite_constants(field_ring(M), card(k), m), " +
			"                t, " +
			"                A₀, " +
			"                A₁))",
		Abbrev: Abbrev{
			// Xⱼ^e for e positive, spelled Xⱼ·Xⱼ^(e−1): it is
			// homogeneous_polynomial.MixedMonomialForm's X_i·X_j^(r−1) at i = j, which
			// gives its degree and its value.
			{Name: "power", Text: "λj:num. λe:num. " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"            polynomial_algebra_one(«hilbertCoefficients»), " +
				"            polynomial_algebra_var(«hilbertCoefficients», j), " +
				"            e - 1))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			closed, transcendental, curve Fact,
		) {
			ring := field.RingOn.Read(M)
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			carrier := a.TermAs[Set[A]]("M.carrier")
			// closed is not listed: the law is read at M, and the hypothesis M is
			// read from states M's closedness, the law's first hypothesis, so the
			// discharge refuses closed listed a second time.
			K, generic := a.UnpackAs[Set[A]](
				GroupPremises(
					transcendental,
					curve,
					projective_generic_point.GenericPointExists.Read(M).At(k, n, E)),
				"K")
			genericParts := a.Conjuncts(
				generic,
				"K is a subfield of M",
				"the field a generic point of the curve generates",
				"regular over k")
			subfieldK := genericParts[0]
			x, point := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(genericParts[1], projective_curve.ProjectiveGenericFieldDef), "x")
			pointParts := a.Conjuncts(
				point,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"at which a form vanishes exactly when it lies in the ideal")
			xInK := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(pointParts[0], projective_curve.PointCoordinatesIn))
			j, first := a.UnpackAs[Nat](
				GroupPremises(pointParts[0], projective_curve.PointLeadingOne.At(fieldRing, k, K, n, E, x)), "j")
			firstParts := a.Conjuncts(
				first,
				"j is at most n",
				"x(j) is one",
				"the coordinates before it are zero")
			kSub := projective_curve.CurveConstantsSubfield.Read(curve)
			finite := projective_curve.CurveConstantsFinite.Read(curve)
			xInM := a.Have(
				"the coordinates of x lie in M, as K does",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(xInK, subfieldK, field.SubfieldSubset))
			onePositive := a.Have(
				"one is positive",
				"0 < 1",
				ByArith())
			degreeOne := a.TermAs[Nat]("1")
			powers := a.Have(
				"Xⱼ^e is a form of degree e, vanishing at a point of M exactly where its j-th coordinate does",
				Statement{
					Binders: "∀y:(num → A). ∀e:num.",
					Hypotheses: []string{
						"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
						"0 < e",
					},
					Conclusion: "homogeneous_polynomial(«hilbertCoefficients», n, e, «power»(j, e)) ∧ " +
						"(«valueAt»(y, «power»(j, e)) = M.zero ⇔ y(j) = M.zero)",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[Fun[Nat, A]]("y")
					e := b.FixAs[Nat]("e")
					guard := b.Conjuncts(
						b.Assume(),
						"the coordinates of y lie in M",
						"e is positive")
					yj := b.MemberOf[on.M](b.TermAs[A]("y(j)"), GroupPremises(firstParts[0], guard[0].At(j)))
					lower := b.TermAs[Nat]("e - 1")
					lowerPower := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(yj, lower)
					b.Show(
						"its value y(j)·y(j)^(e−1) is zero exactly with y(j), M having no zero divisors",
						By(
							kSub,
							guard[0],
							guard[1],
							firstParts[0],
							homogeneous_polynomial.MixedMonomialForm.Read(M).At(k, n, e, j, j, y),
							field.MulEqZeroOn.Read(M).At(yj, lowerPower),
							field.PowEqZeroOn.Read(M).At(yj, lower),
							comm_ring.MulLeftZeroOn.Read(ring).At(lowerPower)))
				}))
			linear := a.Conjuncts(
				GroupPremises(xInM, onePositive, powers.At(x, degreeOne)),
				"Xⱼ is a form of degree one",
				"vanishing at x exactly where x(j) does")
			coordinateForm := a.TermAs[Fun[Fun[Nat, Nat], A]]("«power»(j, 1)")
			outside := a.Have(
				"Xⱼ does not vanish at x, where x(j) is one, so it lies outside the ideal",
				"«power»(j, 1) ∉ ideal_span(«polynomials», E)",
				By(
					linear[0],
					linear[1],
					firstParts[1],
					field.OneNotZeroOn.Read(M),
					pointParts[2].At(coordinateForm)))
			s, rational := a.UnpackAs[Nat](
				GroupPremises(
					curve,
					linear[0],
					outside,
					projective_form_pair.FormZerosRational.Read(M).At(k, n, degreeOne, E, coordinateForm)),
				"s")
			rationalParts := a.Conjuncts(
				rational,
				"s is positive",
				"the zeros of Xⱼ on the curve have their coordinates in the field of q^s elements")
			r, H, anisotropic := a.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](
				GroupPremises(
					kSub, finite, rationalParts[0], projective_form_pair.AnisotropicForm.Read(M).At(k, n, s)),
				"r",
				"H")
			anisotropicParts := a.Conjuncts(
				anisotropic,
				"r is positive",
				"H is a form of degree r",
				"H has no zero over the field of q^s elements but the origin")
			positive := anisotropicParts[0]
			F, fDef := a.LetAs[Fun[Fun[Nat, Nat], A]]("F", "«power»(j, r)")
			fFacts := a.Have(
				"F = Xⱼ^r is a form of degree r, not vanishing at x",
				"homogeneous_polynomial(«hilbertCoefficients», n, r, F) ∧ «at»(F) ≠ M.zero",
				By(Normalized, fDef, xInM, positive, firstParts[1], field.OneNotZeroOn.Read(M), powers.At(x, r)))
			fParts := a.Conjuncts(
				fFacts,
				"F is a form of degree r",
				"F does not vanish at x")
			avoid := a.Have(
				"where F vanishes on the curve, so does Xⱼ: the point lies "+
					"over the field of q^s elements, and H does not vanish there",
				Statement{
					Binders: "∀z:(num → A).",
					Hypotheses: []string{
						"z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
						"«valueAt»(z, F) = M.zero",
					},
					Conclusion: "«valueAt»(z, H) ≠ M.zero",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]("z")
					assumed := b.Conjuncts(
						b.Assume(),
						"z is a point of the curve over M",
						"F vanishes at z")
					onCurve, fZero := assumed[0], assumed[1]
					zInM := b.Have(
						"the coordinates of z up to n lie in M",
						"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
						By(onCurve, projective_curve.PointCoordinatesIn))
					zLeading := b.Have(
						"a first nonzero coordinate is one",
						"∃p:num. p ≤ n ∧ z(p) = M.one ∧ (∀i:num. i < p ⇒ z(i) = M.zero)",
						By(onCurve, projective_curve.PointLeadingOne.At(fieldRing, k, carrier, n, E, z)))
					jZero := b.Have(
						"F vanishes at z, so z(j) = 0",
						"z(j) = M.zero",
						By(Normalized, zInM, positive, fZero, fDef, powers.At(z, r)))
					over := b.Have(
						"so Xⱼ vanishes at z, whose coordinates then lie in the field of q^s elements",
						"∀i:num. z(i) ∈ finite_constants(field_ring(M), card(k), s)",
						By(onCurve, zInM, onePositive, jZero, powers.At(z, degreeOne), rationalParts[1].At(z)))
					b.Show(
						"a coordinate of z is one, so z is no zero of H",
						By(over, zLeading, field.OneNotZeroOn.Read(M), anisotropicParts[2].At(z)))
				}))
			G, pair := a.ObtainAs[Fun[Fun[Nat, Nat], A]](
				"a second form G of degree r, not vanishing at x, with no zero in common with F on the curve",
				"∃G:((num → num) → A). "+
					"    homogeneous_polynomial(«hilbertCoefficients», n, r, G) ∧ "+
					"    «at»(G) ≠ M.zero ∧ "+
					"    (∀z:(num → A). "+
					"        z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E) ⇒ "+
					"        «valueAt»(z, F) ≠ M.zero ∨ «valueAt»(z, G) ≠ M.zero)",
				Derive(func(b *Argument) {
					vanishes := b.Assuming(
						b.TermAs[Bool]("«at»(H) = M.zero"),
						"where H does not vanish at x, G = H will do",
						Given(func(c *Argument, nonzero Fact) {
							c.Take(H)
							c.Show(
								"H is a form of degree r, not zero at x nor where F vanishes on the curve",
								By(anisotropicParts[1], nonzero, avoid))
						}))
					coefficients := b.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
					identity := b.TermAs[Fun[A, A]]("λa:A. a")
					inclusion := b.Have(
						"the inclusion of k into M is a ring map",
						"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
						By(
							kSub,
							field.SubfieldSubring.Read(M).At(k),
							ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
					indices := b.TermAs[Set[Nat]]("{i:num | i ≤ n}")
					sum := b.Have(
						"at a point y of M, (H + F)(y) = H(y) + F(y), both values lying in M",
						Statement{
							Binders:    "∀y:(num → A).",
							Hypotheses: []string{"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier"},
							Conclusion: "«valueAt»(y, fun_add(H, F)) = «valueAt»(y, H) + «valueAt»(y, F) ∧ " +
								"«valueAt»(y, H) ∈ M.carrier ∧ " +
								"«valueAt»(y, F) ∈ M.carrier",
						},
						Derive(func(d *Argument) {
							y := d.FixAs[Fun[Nat, A]]("y")
							coordinatesY := d.Assume()
							d.Show(
								"a form is a polynomial over k, so evaluation adds on H and F, with values in M",
								By(
									inclusion,
									coordinatesY,
									homogeneous_polynomial.FormPolynomial.Read(anisotropicParts[1]),
									homogeneous_polynomial.FormPolynomial.Read(fParts[0]),
									polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(
										coefficients, fieldRing, identity, y, indices, H, F),
									polynomial_algebra_evaluation.PolynomialAlgebraEvalIn.At(
										coefficients, fieldRing, identity, y, indices, H),
									polynomial_algebra_evaluation.PolynomialAlgebraEvalIn.At(
										coefficients, fieldRing, identity, y, indices, F)))
						}))
					additive := comm_ring.AddMonoidOn.Read(ring)
					b.Take(b.TermAs[Fun[Fun[Nat, Nat], A]]("fun_add(H, F)"))
					form := b.Have(
						"H + F is a form of degree r",
						"homogeneous_polynomial(«hilbertCoefficients», n, r, fun_add(H, F))",
						By(
							anisotropicParts[1],
							fParts[0],
							ring_homomorphism.Source.Read(inclusion),
							homogeneous_polynomial.FormSum.At(coefficients, n, r, H, F)))
					atX := b.Have(
						"at x it takes 0 + F(x) = F(x), which is not zero",
						"«at»(fun_add(H, F)) ≠ M.zero",
						By(
							fParts[1],
							xInM,
							vanishes,
							sum.At(x),
							comm_monoid.LeftIdentityOn.Read(additive).AsFact().At(b.TermAs[A]("«at»(F)"))))
					apart := b.Have(
						"where F vanishes on the curve, H + F takes the value of H, which is not zero",
						Statement{
							Binders:    "∀z:(num → A).",
							Hypotheses: []string{"z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)"},
							Conclusion: "«valueAt»(z, F) ≠ M.zero ∨ «valueAt»(z, fun_add(H, F)) ≠ M.zero",
						},
						Derive(func(d *Argument) {
							z := d.FixAs[Fun[Nat, A]]("z")
							onCurve := d.Assume()
							zInM := d.Have(
								"the coordinates of z up to n lie in M",
								"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
								By(onCurve, projective_curve.PointCoordinatesIn))
							d.Show(
								"(H + F)(z) = H(z) + 0 where F(z) is zero",
								By(
									onCurve,
									zInM,
									sum.At(z),
									avoid.At(z),
									comm_monoid.RightIdentityOn.Read(additive).AsFact().At(d.TermAs[A]("«valueAt»(z, H)"))))
						}))
					b.Show(
						"where H vanishes at x, H + F is the second form",
						By(form, atX, apart))
				}))
			charts := a.Have(
				"the charts of F and G, glued along t = G(x)/F(x), are a curve over the line",
				"curve_over_line(restrict_field(M, K), k, «parameter», «chart»(F), «chart»(G), «overlap»)",
				By(
					closed,
					curve,
					subfieldK,
					point,
					positive,
					fFacts,
					pair,
					projective_form_chart.FormChartsAreCurve.Read(M).At(k, K, n, r, E, x, F, G)))
			normal := a.Have(
				"both charts are integrally closed in K",
				"integrally_closed_in(restrict_ring(field_ring(M), «chart»(F)), K) ∧ "+
					"integrally_closed_in(restrict_ring(field_ring(M), «chart»(G)), K)",
				By(
					closed,
					curve,
					subfieldK,
					point,
					positive,
					fFacts,
					pair,
					projective_form_chart.FormChartIntegrallyClosed.Read(M).At(k, K, n, r, E, x, F),
					projective_form_chart.FormChartIntegrallyClosed.Read(M).At(k, K, n, r, E, x, G)))
			chartF, chartG := a.TermAs[Set[A]]("«chart»(F)"), a.TermAs[Set[A]]("«chart»(G)")
			smooth := a.Have(
				"K's ring over each chart is M's ring over it, so with k finite "+
					"and both charts integrally closed they make a smooth curve",
				"smooth_finite_curve(restrict_field(M, K), k, «parameter», «chart»(F), «chart»(G), «overlap»)",
				By(
					charts,
					finite,
					normal,
					smooth_curve.SmoothFiniteFieldCurveDef,
					field.RestrictFieldRecords.At(fieldM, K, chartF),
					field.RestrictFieldRecords.At(fieldM, K, chartG)))
			genus := a.Have(
				"its Čech genus is the Hilbert genus of the equations",
				"curve_genus(restrict_ring(field_ring(M), K), k, «chart»(F), «chart»(G), «overlap») = "+
					"projective_equation_genus(field_ring(M), k, n, E)",
				By(
					closed,
					curve,
					subfieldK,
					point,
					positive,
					fFacts,
					pair,
					ProjectiveGenusIsCurveGenus.Read(M).At(k, K, n, r, E, x, F, G)))
			points := a.Have(
				"over each field of q^m elements the points of the curve match the evaluation points of the charts",
				Statement{
					Binders:    "∀m:num.",
					Hypotheses: []string{"0 < m"},
					Conclusion: "∃f:((num → A) → prod(bool, A → A)). " +
						"    injective_on(«points»(m), f) ∧ " +
						"    image(f, «points»(m)) = " +
						"    curve_evaluation_points(M, " +
						"        k, " +
						"        finite_constants(field_ring(M), card(k), m), " +
						"        «parameter», " +
						"        «chart»(F), " +
						"        «chart»(G))",
				},
				a.ForEach(func(m *Expr[Nat]) Action {
					return By(
						closed,
						curve,
						subfieldK,
						point,
						positive,
						fFacts,
						pair,
						PointsMatchCharts.Read(M).At(k, K, n, r, m, E, x, F, G))
				}))
			a.Take(K)
			a.Take(chartF)
			a.Take(chartG)
			a.Take(a.TermAs[Set[A]]("«overlap»"))
			a.Take(a.TermAs[A]("«parameter»"))
			a.Show(
				"K with the charts of F and G, glued along t, is the presentation",
				By(subfieldK, smooth, genus, points))
		}),
})}
