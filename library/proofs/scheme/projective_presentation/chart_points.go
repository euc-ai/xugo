// chart_points.go — the points of the curve over a finite field are the
// evaluation points of its two form charts. Four lemmas on forms of
// projective_curve carry the computations: the numerators P·H^d + Q·H^c and
// P·Q of the sum and the product of P/H^c and Q/H^d (FormNumerators), the
// ratio P/H^a unchanged by scaling the point (FormRatioScaling), evaluation
// commuting with a ring map that fixes k (EvaluationNatural), and the forms
// X_i·X_j^(r−1) (MixedMonomialForm). A point z of the curve over a subfield l where a form H
// does not vanish evaluates the chart of H, P(x)/H(x)^a ↦ P(z)/H(z)^a
// (ChartEvaluation); every point of the chart with values in l is such an
// evaluation (ChartPointFromMap); a point of the chart is fixed by the
// quotients (ChartPointsDetermined) and a point of the curve by its ratios
// (FormRatiosDetermine). Over the field of qᵐ elements the points then match
// the evaluation points of the charts of F and G (PointsMatchCharts).

package projective_presentation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_chart"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartEvaluation — a point z with coordinates in l, at which every form
// vanishing at x vanishes, evaluates the chart of H where H(z) is not zero:
// the value P(x)/H(x)^a of a form P of degree r·a goes to P(z)/H(z)^a. A
// member y of the chart is represented by forms P of degree r·c with
// y·H(x)^c = P(x), and two representations give one value at z, since
// P·H^d − Q·H^c vanishes at x and so at z; the numerators of sums and
// products make the value a ring map, the constants fix k, and set to zero
// off the chart it is a point of the chart.
var ChartEvaluation = chartEvaluationThm{family.Add(registry.ProofEntry{
	Name: "ChartEvaluation",
	Key:  "prop_141b560d86a4fef0",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K l:set(A). ∀n r:num. ∀x z:(num → A). ∀H:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"subfield(M, l)",
			"k ⊆ K",
			"k ⊆ l",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"∀i:num. i ≤ n ⇒ z(i) ∈ l",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
			"«at»(H) ≠ M.zero",
			"«valueAt»(z, H) ≠ M.zero",
			"∀P:((num → num) → A). " +
				"    (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ∧ «at»(P) = M.zero ⇒ " +
				"    «valueAt»(z, P) = M.zero",
		},
		Conclusion: "∃φ:(A → A). " +
			"    φ ∈ " +
			"    algebra_points(restrict_ring(field_ring(M), «chart»(H)), " +
			"        restrict_ring(field_ring(M), l), " +
			"        k, " +
			"        λa:A. a) ∧ " +
			"    (∀a:num. ∀P:((num → num) → A). " +
			"        homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ⇒ " +
			"        φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
			"        «valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), a))",
		Abbrev: Abbrev{
			{Name: "represents", Text: "λy:A. λv:A. λc:num. λP:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, r * c, P) ∧ " +
				"    y * monoid_pow(M.mul, M.one, «at»(H), c) = «at»(P) ∧ " +
				"    v * monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = «valueAt»(z, P)"},
			{Name: "power", Text: "λe:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        H, " +
				"        e)"},
			// P·H^d + Q·H^c, the numerator of P/H^c + Q/H^d, and P·H^d − Q·H^c.
			{Name: "sum", Text: "λP:((num → num) → A). λc:num. λQ:((num → num) → A). λd:num. " +
				"    fun_add(polynomial_algebra_mul(«hilbertCoefficients», P, «power»(d)), " +
				"        polynomial_algebra_mul(«hilbertCoefficients», Q, «power»(c)))"},
			{Name: "difference", Text: "λP:((num → num) → A). λc:num. λQ:((num → num) → A). λd:num. " +
				"    «sum»(P, c, fun_neg(Q), d)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			n, r *Expr[Nat],
			x, z *Arrow[Nat, A],
			H *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, lSub, kInK, kInL, xCoordinates, zCoordinates, form, xNonzero, zNonzero, specialization Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldOps := arg.TermAs[FieldOps[A]]("M")
			fieldRing := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
			coefficients := arg.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			identity := arg.TermAs[Fun[A, A]]("λa:A. a")
			chart := arg.TermAs[Set[A]]("«chart»(H)")
			chartRing := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «chart»(H))")
			lRing := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), l)")
			hx := arg.TermAs[A]("«at»(H)")
			hz := arg.TermAs[A]("«valueAt»(z, H)")
			ix := arg.TermAs[A]("M.inv(«at»(H))")
			iz := arg.TermAs[A]("M.inv(«valueAt»(z, H))")
			zero := arg.TermAs[Nat]("0")
			inclusion := arg.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			coefficientRing := ring_homomorphism.Source.Read(inclusion)
			KInM := arg.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			lInM := arg.Have(
				"and so does l",
				"l ⊆ M.carrier",
				By(lSub, field.SubfieldSubset))
			xInM := arg.Have(
				"the coordinates of x lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(xCoordinates, KInM))
			zInM := arg.Have(
				"and so do those of z",
				"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
				BySets(zCoordinates, lInM))
			atX := arg.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, xCoordinates, Read(projective_curve.PointEvaluation, M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			atZ := arg.Conjuncts(
				GroupPremises(
					kSub, lSub, kInL, zCoordinates, Read(projective_curve.PointEvaluation, M).At(k, l, n, z)),
				"evaluation at z is a ring map",
				"with values in l")
			hzInL := arg.Have(
				"H(z) lies in l",
				"«valueAt»(z, H) ∈ l",
				By(homogeneous_polynomial.FormPolynomial.Read(form), atZ[1]))
			izInL := arg.Have(
				"and so does its inverse, l being a subfield",
				"M.inv(«valueAt»(z, H)) ∈ l",
				By(lSub, hzInL, field.SubfieldInv.At(fieldOps, l, hz)))
			values := arg.Conjuncts(
				arg.Have(
					"H(x), H(z) and their inverses lie in M",
					"«at»(H) ∈ M.carrier ∧ "+
						"M.inv(«at»(H)) ∈ M.carrier ∧ "+
						"«valueAt»(z, H) ∈ M.carrier ∧ "+
						"M.inv(«valueAt»(z, H)) ∈ M.carrier",
					BySets(
						homogeneous_polynomial.FormPolynomial.Read(form),
						atX[1],
						KInM,
						hzInL,
						lInM,
						field.InvIn.Read(M))),
				"H(x) lies in M",
				"so does its inverse",
				"so does H(z)",
				"and its inverse")
			units := arg.Have(
				"the powers of H(x) and of H(z) are units, H(x) and H(z) being nonzero",
				"∀c:num. "+
					"    monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) * monoid_pow(M.mul, M.one, «at»(H), c) = "+
					"    M.one ∧ "+
					"    monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
					"    monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = "+
					"    M.one",
				Derive(func(b *Argument) {
					c := b.FixAs[Nat]("c")
					b.Show(
						"a power of a unit times the power of its inverse",
						By(
							values[0],
							values[1],
							values[2],
							values[3],
							b.Have(
								"H(x)^(−1)·H(x) = 1",
								"M.inv(«at»(H)) * «at»(H) = M.one",
								By(xNonzero, values[0], field.MulLeftInverseOn.Read(M))),
							b.Have(
								"H(z)^(−1)·H(z) = 1",
								"M.inv(«valueAt»(z, H)) * «valueAt»(z, H) = M.one",
								By(zNonzero, values[2], field.MulLeftInverseOn.Read(M))),
							comm_monoid.PowInverseOn.Read(monoid).AsFact().At(ix, hx, c),
							comm_monoid.PowInverseOn.Read(monoid).AsFact().At(iz, hz, c)))
				}))
			cancels := arg.Have(
				"dividing by a power of H(x), or of H(z), and multiplying back changes nothing",
				Statement{
					Binders: "∀c:num. ∀p:A.",
					Hypotheses: []string{
						"p ∈ M.carrier",
					},
					Conclusion: "p * " +
						"monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) * " +
						"monoid_pow(M.mul, M.one, «at»(H), c) = " +
						"p ∧ " +
						"p * " +
						"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * " +
						"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = " +
						"p",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[Nat]("c")
					b.FixAs[A]("p")
					pIn := b.Assume()
					unit := b.Conjuncts(
						units.At(c),
						"H(x)^(−c)·H(x)^c = 1",
						"H(z)^(−c)·H(z)^c = 1")
					powers := b.Have(
						"the powers of H(x), H(z) and their inverses lie in M",
						"monoid_pow(M.mul, M.one, «at»(H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) ∈ M.carrier",
						By(values[0], values[1], values[2], values[3], powIn))
					regroup := b.Conjuncts(
						b.Have(
							"regroup the factors",
							"p * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) * monoid_pow(M.mul, M.one, «at»(H), c) = "+
								"p * (monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) * monoid_pow(M.mul, M.one, «at»(H), c)) ∧ "+
								"p * "+
								"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
								"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = "+
								"p * "+
								"(monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
								"    monoid_pow(M.mul, M.one, «valueAt»(z, H), c))",
							ByArith(M, pIn, powers)),
						"at x",
						"and at z")
					b.Show(
						"regroup, and the power of the inverse times the power is one",
						regroup[0].Rw(),
						regroup[1].Rw(),
						unit[0].Rw(),
						unit[1].Rw(),
						ByArith(M, pIn))
				}))
			formValues := arg.Have(
				"a form takes values in M at x and at z",
				Statement{
					Binders: "∀c:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, c, P)",
					},
					Conclusion: "«at»(P) ∈ M.carrier ∧ «valueAt»(z, P) ∈ M.carrier",
				},
				BySets(homogeneous_polynomial.FormPolynomial, atX[1], atZ[1], KInM, lInM))
			chartParts := arg.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, xInM, form, Read(projective_curve.ChartSubring, M).At(k, K, n, r, x, H)),
				"the chart is a subring of M",
				"holding k")
			chartInM := arg.Have(
				"the chart lies in K, inside M",
				"«chart»(H) ⊆ M.carrier",
				BySets(KInM))
			unique := arg.Have(
				"two representations of y give one value at z: P·H^d − Q·H^c vanishes at x, so at z",
				"∀y v w:A. ∀c d:num. ∀P Q:((num → num) → A). "+
					"    «represents»(y, v, c, P) ⇒ "+
					"    «represents»(y, w, d, Q) ⇒ "+
					"    y ∈ M.carrier ⇒ "+
					"    v ∈ M.carrier ⇒ "+
					"    w ∈ M.carrier ⇒ "+
					"    v = w",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					v := b.FixAs[A]("v")
					w := b.FixAs[A]("w")
					c := b.FixAs[Nat]("c")
					d := b.FixAs[Nat]("d")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					Q := b.FixAs[Fun[Fun[Nat, Nat], A]]("Q")
					first := b.Conjuncts(
						b.Assume(),
						"P is a form of degree r·c",
						"y·H(x)^c = P(x)",
						"v·H(z)^c = P(z)")
					second := b.Conjuncts(
						b.Assume(),
						"Q is a form of degree r·d",
						"y·H(x)^d = Q(x)",
						"w·H(z)^d = Q(z)")
					yIn := b.Assume()
					vIn := b.Assume()
					wIn := b.Assume()
					negQ := b.TermAs[Fun[Fun[Nat, Nat], A]]("fun_neg(Q)")
					negForm := b.Have(
						"−Q is a form of degree r·d",
						"homogeneous_polynomial(«hilbertCoefficients», n, r * d, fun_neg(Q))",
						By(
							coefficientRing,
							second[0],
							At(homogeneous_polynomial.FormNeg, coefficients, n, b.TermAs[Nat]("r * d"), Q)))
					difference := b.TermAs[Fun[Fun[Nat, Nat], A]]("«difference»(P, c, Q, d)")
					numerator := b.Conjuncts(
						GroupPremises(
							kSub,
							xInM,
							form,
							first[0],
							negForm,
							Read(homogeneous_polynomial.FormNumerators, M).At(k, n, r, c, d, x, H, P, negQ)),
						"P·H^d − Q·H^c is a form of degree r·(c + d)",
						"and so is P·(−Q)",
						"its value at x is P(x)·H(x)^d − Q(x)·H(x)^c",
						"and that of P·(−Q) is P(x)·(−Q)(x)")
					atZValue := b.Have(
						"its value at z is P(z)·H(z)^d − Q(z)·H(z)^c",
						"«valueAt»(z, «difference»(P, c, Q, d)) = "+
							"«valueAt»(z, P) * monoid_pow(M.mul, M.one, «valueAt»(z, H), d) + "+
							"«valueAt»(z, fun_neg(Q)) * monoid_pow(M.mul, M.one, «valueAt»(z, H), c)",
						By(
							kSub,
							zInM,
							form,
							first[0],
							negForm,
							Read(homogeneous_polynomial.FormNumerators, M).At(k, n, r, c, d, z, H, P, negQ)))
					qPolynomial := b.Have(
						"Q is a polynomial over k",
						"Q ∈ «polynomials».carrier",
						By(homogeneous_polynomial.FormPolynomial.Read(second[0])))
					negX := b.Have(
						"the value of −Q at x is −Q(x)",
						"«at»(fun_neg(Q)) = -«at»(Q)",
						By(
							qPolynomial,
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.MapNeg.Read(atX[0]).AsFact().At(Q)))
					negZ := b.Have(
						"and at z it is −Q(z)",
						"«valueAt»(z, fun_neg(Q)) = -«valueAt»(z, Q)",
						By(
							qPolynomial,
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.MapNeg.Read(atZ[0]).AsFact().At(Q)))
					powersX := b.Have(
						"the powers of H(x) lie in M",
						"monoid_pow(M.mul, M.one, «at»(H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(H), d) ∈ M.carrier",
						By(values[0], powIn))
					atXZero := b.Have(
						"the difference vanishes at x: P(x)·H(x)^d = y·H(x)^c·H(x)^d = Q(x)·H(x)^c",
						"«at»(«difference»(P, c, Q, d)) = M.zero",
						numerator[2].Rw(),
						negX.Rw(),
						first[1].RwRev(),
						second[1].RwRev(),
						ByArith(M, yIn, powersX))
					atZZero := b.Have(
						"so it vanishes at z",
						"«valueAt»(z, «difference»(P, c, Q, d)) = M.zero",
						By(numerator[0], atXZero, specialization.At(difference)))
					zValues := b.Conjuncts(
						b.Have(
							"P(z), Q(z) and the powers of H(z) and of its inverse lie in M",
							"«valueAt»(z, P) ∈ M.carrier ∧ "+
								"«valueAt»(z, Q) ∈ M.carrier ∧ "+
								"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) ∈ M.carrier ∧ "+
								"monoid_pow(M.mul, M.one, «valueAt»(z, H), d) ∈ M.carrier ∧ "+
								"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) ∈ M.carrier ∧ "+
								"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), d) ∈ M.carrier",
							By(first[0], second[0], formValues, values[2], values[3], powIn)),
						"P(z) lies in M",
						"so does Q(z)",
						"so does H(z)^c",
						"so does H(z)^d",
						"so does H(z)^(−c)",
						"and H(z)^(−d)")
					relation := b.Have(
						"so v·H(z)^c·H(z)^d = w·H(z)^d·H(z)^c",
						"v * "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) * "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), d) = "+
							"w * monoid_pow(M.mul, M.one, «valueAt»(z, H), d) * monoid_pow(M.mul, M.one, «valueAt»(z, H), c)",
						first[2].Rw(),
						second[2].Rw(),
						ByArith(M, atZZero, atZValue, negZ, zValues[0], zValues[1], zValues[2], zValues[3]))
					unitC := b.Conjuncts(
						units.At(c),
						"H(x)^c is a unit",
						"and so is H(z)^c")
					unitD := b.Conjuncts(
						units.At(d),
						"H(x)^d is a unit",
						"and so is H(z)^d")
					b.Show(
						"cancel H(z)^c·H(z)^d, a unit",
						ByArith(
							M,
							vIn,
							wIn,
							zValues[2],
							zValues[3],
							zValues[4],
							zValues[5],
							Scaled(
								b.TermAs[A](
									"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
										"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), d)"),
								relation),
							Scaled(
								b.TermAs[A](
									"v * "+
										"monoid_pow(M.mul, M.one, «valueAt»(z, H), d) * "+
										"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), d)"),
								unitC[1]),
							Scaled(v, unitD[1]),
							Scaled(
								b.TermAs[A](
									"w * "+
										"monoid_pow(M.mul, M.one, «valueAt»(z, H), d) * "+
										"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), d)"),
								unitC[1]),
							Scaled(w, unitD[1])))
				}))
			represented := arg.Have(
				"each member y of the chart, y·H(x)^c = P(x), is represented with the value P(z)/H(z)^c, in l",
				"∀y:A. y ∈ «chart»(H) ⇒ ∃v:A. v ∈ l ∧ (∃c:num. ∃P:((num → num) → A). «represents»(y, v, c, P))",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					yParts := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·H(x)^c is the value of a form of degree r·c")
					c, P, yForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yParts[1], "c", "P")
					yData := b.Conjuncts(
						yForm,
						"P is a form of degree r·c",
						"y·H(x)^c = P(x)")
					pz := b.TermAs[A]("«valueAt»(z, P)")
					izc := b.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c)")
					pzInL := b.Have(
						"P(z) lies in l",
						"«valueAt»(z, P) ∈ l",
						By(homogeneous_polynomial.FormPolynomial.Read(yData[0]), atZ[1]))
					b.Take(b.TermAs[A]("«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c)"))
					b.Show(
						"P(z)·H(z)^(−c) lies in l, and times H(z)^c it is P(z)",
						By(
							yData[0],
							yData[1],
							b.Have(
								"it lies in l, a subfield",
								"«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) ∈ l",
								By(
									lSub,
									pzInL,
									izInL,
									field.SubfieldPowerIn.Read(M).AsFact().At(l, iz, c),
									field.SubfieldMul.At(fieldOps, l, pz, izc))),
							b.Have(
								"and times H(z)^c it is P(z)",
								"«valueAt»(z, P) * "+
									"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
									"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = "+
									"«valueAt»(z, P)",
								By(GroupPremises(yData[0], formValues.At(b.TermAs[Nat]("r * c"), P)), cancels.At(c, pz)))))
				}))
			psi, psiDef := arg.LetAs[Fun[A, A]](
				"ψ",
				"λy:A. εv:A. v ∈ l ∧ (∃c:num. ∃P:((num → num) → A). «represents»(y, v, c, P))")
			chosen := arg.Have(
				"so ψ(y), a value chosen for each member y of the chart, "+
					"lies in l and is the value at z of a representation of y",
				"∀y:A. y ∈ «chart»(H) ⇒ ψ(y) ∈ l ∧ (∃c:num. ∃P:((num → num) → A). «represents»(y, ψ(y), c, P))",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					b.Show(
						"the chosen value is one",
						psiDef.Rw(),
						By(GroupPremises(yIn, represented.At(y))))
				}))
			value := arg.Have(
				"ψ(y) is the value at z of every representation of y",
				"∀y v:A. ∀c:num. ∀P:((num → num) → A). "+
					"    y ∈ «chart»(H) ⇒ v ∈ M.carrier ⇒ «represents»(y, v, c, P) ⇒ ψ(y) = v",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					v := b.FixAs[A]("v")
					c := b.FixAs[Nat]("c")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					yIn := b.Assume()
					vIn := b.Assume()
					given := b.Assume()
					yChosen := b.Conjuncts(
						GroupPremises(yIn, chosen.At(y)),
						"ψ(y) lies in l",
						"and is the value of a representation of y")
					d, Q, other := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yChosen[1], "d", "Q")
					b.Show(
						"the two representations give one value",
						By(
							other,
							given,
							vIn,
							b.Have(
								"y and ψ(y) lie in M",
								"y ∈ M.carrier ∧ ψ(y) ∈ M.carrier",
								BySets(yIn, yChosen[0], chartInM, lInM)),
							unique.At(y, b.TermAs[A]("ψ(y)"), v, d, c, Q, P)))
				}))
			closed := arg.Have(
				"ψ keeps sums and products: the numerators P·H^d + Q·H^c and P·Q represent them",
				Statement{
					Binders: "∀y₁ y₂:A.",
					Hypotheses: []string{
						"y₁ ∈ «chart»(H)",
						"y₂ ∈ «chart»(H)",
					},
					Conclusion: "ψ(y₁ + y₂) = ψ(y₁) + ψ(y₂) ∧ ψ(y₁ * y₂) = ψ(y₁) * ψ(y₂)",
				},
				Derive(func(b *Argument) {
					y1 := b.FixAs[A]("y₁")
					y2 := b.FixAs[A]("y₂")
					members := b.Conjuncts(
						b.Assume(),
						"y₁ lies in the chart",
						"so does y₂")
					firstChosen := b.Conjuncts(
						GroupPremises(members[0], chosen.At(y1)),
						"ψ(y₁) lies in l",
						"and is the value of a representation of y₁")
					c, P, firstRep := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](firstChosen[1], "c", "P")
					first := b.Conjuncts(
						firstRep,
						"P is a form of degree r·c",
						"y₁·H(x)^c = P(x)",
						"ψ(y₁)·H(z)^c = P(z)")
					secondChosen := b.Conjuncts(
						GroupPremises(members[1], chosen.At(y2)),
						"ψ(y₂) lies in l",
						"and is the value of a representation of y₂")
					d, Q, secondRep := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](secondChosen[1], "d", "Q")
					second := b.Conjuncts(
						secondRep,
						"Q is a form of degree r·d",
						"y₂·H(x)^d = Q(x)",
						"ψ(y₂)·H(z)^d = Q(z)")
					numerators := b.Conjuncts(
						GroupPremises(
							kSub,
							xInM,
							form,
							first[0],
							second[0],
							Read(homogeneous_polynomial.FormNumerators, M).At(k, n, r, c, d, x, H, P, Q)),
						"P·H^d + Q·H^c is a form of degree r·(c + d)",
						"and so is P·Q",
						"the value of the first at x",
						"and of the second")
					atZValues := b.Conjuncts(
						b.Have(
							"and their values at z",
							"«valueAt»(z, «sum»(P, c, Q, d)) = "+
								"«valueAt»(z, P) * monoid_pow(M.mul, M.one, «valueAt»(z, H), d) + "+
								"«valueAt»(z, Q) * monoid_pow(M.mul, M.one, «valueAt»(z, H), c) ∧ "+
								"«valueAt»(z, polynomial_algebra_mul(«hilbertCoefficients», P, Q)) = "+
								"«valueAt»(z, P) * «valueAt»(z, Q)",
							By(
								kSub,
								zInM,
								form,
								first[0],
								second[0],
								Read(homogeneous_polynomial.FormNumerators, M).At(k, n, r, c, d, z, H, P, Q))),
						"the value of the first at z",
						"and of the second")
					inM := b.Have(
						"y₁, y₂, ψ(y₁) and ψ(y₂) lie in M",
						"y₁ ∈ M.carrier ∧ y₂ ∈ M.carrier ∧ ψ(y₁) ∈ M.carrier ∧ ψ(y₂) ∈ M.carrier",
						BySets(members[0], members[1], firstChosen[0], secondChosen[0], chartInM, lInM))
					powers := b.Have(
						"and so do the powers of H(x) and H(z)",
						"monoid_pow(M.mul, M.one, «at»(H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(H), d) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), d) ∈ M.carrier",
						By(values[0], values[2], powIn))
					splitX := GroupPremises(values[0], comm_monoid.PowAddOn.Read(monoid).AsFact().At(hx, c, d))
					splitZ := GroupPremises(values[2], comm_monoid.PowAddOn.Read(monoid).AsFact().At(hz, c, d))
					sumX := b.Have(
						"(y₁ + y₂)·H(x)^(c+d) is the value at x of P·H^d + Q·H^c",
						"(y₁ + y₂) * monoid_pow(M.mul, M.one, «at»(H), c + d) = «at»(«sum»(P, c, Q, d))",
						numerators[2].Rw(),
						first[1].RwRev(),
						second[1].RwRev(),
						splitX.Rw(),
						ByArith(M, inM, powers))
					sumZ := b.Have(
						"and (ψ(y₁) + ψ(y₂))·H(z)^(c+d) its value at z",
						"(ψ(y₁) + ψ(y₂)) * monoid_pow(M.mul, M.one, «valueAt»(z, H), c + d) = "+
							"«valueAt»(z, «sum»(P, c, Q, d))",
						atZValues[0].Rw(),
						first[2].RwRev(),
						second[2].RwRev(),
						splitZ.Rw(),
						ByArith(M, inM, powers))
					productX := b.Have(
						"y₁·y₂·H(x)^(c+d) is the value at x of P·Q",
						"(y₁ * y₂) * monoid_pow(M.mul, M.one, «at»(H), c + d) = "+
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», P, Q))",
						numerators[3].Rw(),
						first[1].RwRev(),
						second[1].RwRev(),
						splitX.Rw(),
						ByArith(M, inM, powers))
					productZ := b.Have(
						"and ψ(y₁)·ψ(y₂)·H(z)^(c+d) its value at z",
						"(ψ(y₁) * ψ(y₂)) * monoid_pow(M.mul, M.one, «valueAt»(z, H), c + d) = "+
							"«valueAt»(z, polynomial_algebra_mul(«hilbertCoefficients», P, Q))",
						atZValues[1].Rw(),
						first[2].RwRev(),
						second[2].RwRev(),
						splitZ.Rw(),
						ByArith(M, inM, powers))
					chartClosed := b.Have(
						"y₁ + y₂ and y₁·y₂ lie in the chart, a subring",
						"y₁ + y₂ ∈ «chart»(H) ∧ y₁ * y₂ ∈ «chart»(H)",
						By(
							members[0],
							members[1],
							comm_ring.SubringAdd.Read(chartParts[0]),
							comm_ring.SubringMul.Read(chartParts[0])))
					b.Show(
						"ψ of the sum and the product are the values of their numerators",
						By(
							chartClosed,
							inM,
							numerators[0],
							numerators[1],
							sumX,
							sumZ,
							productX,
							productZ,
							value.At(
								b.TermAs[A]("y₁ + y₂"),
								b.TermAs[A]("ψ(y₁) + ψ(y₂)"),
								b.TermAs[Nat]("c + d"),
								b.TermAs[Fun[Fun[Nat, Nat], A]]("«sum»(P, c, Q, d)")),
							value.At(
								b.TermAs[A]("y₁ * y₂"),
								b.TermAs[A]("ψ(y₁) * ψ(y₂)"),
								b.TermAs[Nat]("c + d"),
								b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», P, Q)")),
							comm_ring.AddIn.Read(ring),
							comm_ring.MulIn.Read(ring)))
				}))
			fixes := arg.Have(
				"ψ fixes k: a constant c is represented by the constant form c of degree r·0, with value c at z",
				"∀c:A. c ∈ k ⇒ ψ(c) = c",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					constant := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_const(«hilbertCoefficients», c)")
					constantForm := b.Have(
						"the constant c is a form of degree r·0",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    r * 0, "+
							"    polynomial_algebra_const(«hilbertCoefficients», c))",
						By(
							Normalized,
							cIn,
							coefficientRing,
							nat_arith.MulZero.At(r),
							At(homogeneous_polynomial.FormConstant, coefficients, n, c)))
					evaluated := b.Conjuncts(
						b.Have(
							"it evaluates to c at x and at z, c lying in M",
							"«at»(polynomial_algebra_const(«hilbertCoefficients», c)) = c ∧ "+
								"«valueAt»(z, polynomial_algebra_const(«hilbertCoefficients», c)) = c ∧ "+
								"c ∈ M.carrier",
							BySets(
								cIn,
								inclusion,
								b.Have(
									"k lies in M",
									"k ⊆ M.carrier",
									By(kSub, field.SubfieldSubset)),
								At(
									polynomial_algebra_evaluation.PolynomialAlgebraEvalConst, coefficients, fieldRing, identity, x, c),
								At(
									polynomial_algebra_evaluation.PolynomialAlgebraEvalConst,
									coefficients,
									fieldRing,
									identity,
									z,
									c))),
						"the constant evaluates to c at x",
						"and at z",
						"c lies in M")
					b.Show(
						"c·H(x)^0 = c and c·H(z)^0 = c: the constant represents c with value c",
						By(
							cIn,
							evaluated[2],
							constantForm,
							b.Have(
								"c lies in the chart",
								"c ∈ «chart»(H)",
								BySets(cIn, chartParts[1])),
							b.Have(
								"c·H(x)^0 = c and c·H(z)^0 = c",
								"c * monoid_pow(M.mul, M.one, «at»(H), 0) = "+
									"«at»(polynomial_algebra_const(«hilbertCoefficients», c)) ∧ "+
									"c * monoid_pow(M.mul, M.one, «valueAt»(z, H), 0) = "+
									"«valueAt»(z, polynomial_algebra_const(«hilbertCoefficients», c))",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								evaluated[0].Rw(),
								evaluated[1].Rw(),
								ByArith(M, evaluated[2])),
							value.At(c, c, zero, constant)))
				}))
			mapping := arg.Have(
				"so ψ is a ring map from the chart into l",
				"ring_homomorphism(restrict_ring(field_ring(M), «chart»(H)), restrict_ring(field_ring(M), l), ψ)",
				Simp(Fwd(ring_homomorphism.RingHomomorphism)),
				By(
					arg.Have(
						"the chart is a ring under the operations of M",
						"comm_ring_on(restrict_ring(field_ring(M), «chart»(H)))",
						By(chartParts[0], comm_ring.SubringRingOn.Read(ring).At(chart))),
					arg.Have(
						"and so is l",
						"comm_ring_on(restrict_ring(field_ring(M), l))",
						By(lSub, field.SubfieldCommRing.Read(M).At(l))),
					chosen,
					closed,
					GroupPremises(
						arg.Have(
							"one lies in k",
							"M.one ∈ k",
							By(kSub, field.SubfieldOne)),
						fixes.At(arg.TermAs[A]("M.one")))))
			point := arg.Conjuncts(
				GroupPremises(
					mapping,
					chartParts[1],
					fixes,
					algebra_points.AlgebraPointsOfRingMap.At(chartRing, lRing, k, identity, psi)),
				"ψ set to zero off the chart is a point of the chart",
				"agreeing with ψ on the chart")
			quotients := arg.Have(
				"ψ takes P(x)/H(x)^a to P(z)/H(z)^a: P represents the quotient with that value",
				Statement{
					Binders: "∀c:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, r * c, P)",
					},
					Conclusion: "«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) ∈ «chart»(H) ∧ " +
						"ψ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c)) = " +
						"«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[Nat]("c")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					pForm := b.Assume()
					quotient := b.TermAs[A]("«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c)")
					target := b.TermAs[A]("«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c)")
					inChart := b.Have(
						"P(x)/H(x)^c lies in the chart",
						"«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) ∈ «chart»(H)",
						By(
							kSub,
							KSub,
							kInK,
							xCoordinates,
							form,
							xNonzero,
							pForm,
							Read(projective_curve.ChartQuotient, M).At(k, K, n, r, c, x, H, P)))
					pValues := b.Conjuncts(
						GroupPremises(pForm, formValues.At(b.TermAs[Nat]("r * c"), P)),
						"P(x) lies in M",
						"and so does P(z)")
					powers := b.Have(
						"the powers of H(x), H(z) and their inverses lie in M",
						"monoid_pow(M.mul, M.one, «at»(H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) ∈ M.carrier",
						By(values[0], values[1], values[2], values[3], powIn))
					b.Show(
						"by the representation (c, P)",
						By(
							inChart,
							pForm,
							b.Have(
								"the quotient times H(x)^c is P(x)",
								"«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), c) * monoid_pow(M.mul, M.one, «at»(H), c) = "+
									"«at»(P)",
								By(pValues[0], cancels.At(c, b.TermAs[A]("«at»(P)")))),
							b.Have(
								"and P(z)/H(z)^c times H(z)^c is P(z)",
								"«valueAt»(z, P) * "+
									"monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) * "+
									"monoid_pow(M.mul, M.one, «valueAt»(z, H), c) = "+
									"«valueAt»(z, P)",
								By(pValues[1], cancels.At(c, b.TermAs[A]("«valueAt»(z, P)")))),
							b.Have(
								"P(z)/H(z)^c lies in M",
								"«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), c) ∈ M.carrier",
								By(pValues[1], powers, comm_ring.MulIn.Read(ring))),
							value.At(quotient, target, c, P)))
				}))
			phi, phiDef := arg.LetAs[Fun[A, A]](
				"φ",
				"λy:A. COND(y ∈ «chart»(H), ψ(y), M.zero)")
			evaluates := arg.Have(
				"so φ takes P(x)/H(x)^a to P(z)/H(z)^a, agreeing with ψ on the chart",
				Statement{
					Binders: "∀a:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)",
					},
					Conclusion: "φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
						"«valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), a)",
				},
				Derive(func(b *Argument) {
					a := b.FixAs[Nat]("a")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					parts := b.Conjuncts(
						GroupPremises(b.Assume(), quotients.At(a, P)),
						"the quotient lies in the chart",
						"where ψ takes it to P(z)/H(z)^a")
					b.Show(
						"φ is ψ there",
						phiDef.Rw(),
						By(
							parts[1],
							GroupPremises(
								parts[0], point[1].At(b.TermAs[A]("«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)")))))
				}))
			arg.Show(
				"φ is the point",
				Witness(phi),
				By(
					arg.Have(
						"φ is a point of the chart",
						"φ ∈ "+
							"algebra_points(restrict_ring(field_ring(M), «chart»(H)), "+
							"    restrict_ring(field_ring(M), l), "+
							"    k, "+
							"    λa:A. a)",
						phiDef.Rw(),
						By(point[0])),
					evaluates))
		}),
})}

// ChartPointFromMap — every point φ of the chart of H with values in l is the
// evaluation at a point z of the curve over l at which H does not vanish.
// The quotients x(i)^r/H(x) generate the unit ideal of the chart, so φ does
// not kill the one at some i₀; with s = x(i₀)^(r−1)/H(x) the points x(j)·s
// lie in the chart, φ commutes with evaluating forms there, and w = φ(x(·)·s)
// is a zero of E at which every ratio P/H^a is φ(P(x)/H(x)^a). Scaled by the
// inverse of its first nonzero coordinate, w is the point z.
var ChartPointFromMap = chartPointFromMapThm{family.Add(registry.ProofEntry{
	Name: "ChartPointFromMap",
	Key:  "prop_ce67c39c6c6f4f12",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K l:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀H:((num → num) → A). " +
			"∀φ:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"subfield(M, l)",
			"k ⊆ K",
			"x ∈ projective_equation_points(field_ring(M), k, K, n, E)",
			"∀P:((num → num) → A). P ∈ E ⇒ ∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
			"0 < r",
			"«at»(H) ≠ M.zero",
			"φ ∈ " +
				"algebra_points(restrict_ring(field_ring(M), «chart»(H)), " +
				"    restrict_ring(field_ring(M), l), " +
				"    k, " +
				"    λa:A. a)",
		},
		Conclusion: "∃z:(num → A). " +
			"    z ∈ projective_equation_points(field_ring(M), k, l, n, E) ∧ " +
			"    «valueAt»(z, H) ≠ M.zero ∧ " +
			"    (∀a:num. ∀P:((num → num) → A). " +
			"        homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ⇒ " +
			"        φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
			"        «valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), a))",
		Abbrev: Abbrev{
			{Name: "quotients", Text: "{monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(H)) | i:num | i ≤ n}"},
			{Name: "mixed", Text: "λi:num. λj:num. " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», i), " +
				"        monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"            polynomial_algebra_one(«hilbertCoefficients»), " +
				"            polynomial_algebra_var(«hilbertCoefficients», j), " +
				"            r - 1))"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			H *Arrow[Fun[Nat, Nat], A],
			φ *Arrow[A, A],
			kSub, KSub, lSub, kInK, xPoint, forms, form, positive, nonzero, point Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldRing := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
			coefficients := arg.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			identity := arg.TermAs[Fun[A, A]]("λa:A. a")
			chart := arg.TermAs[Set[A]]("«chart»(H)")
			chartRing := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «chart»(H))")
			lRing := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), l)")
			variables := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			one := arg.TermAs[Nat]("1")
			lower := arg.TermAs[Nat]("r - 1")
			h := arg.TermAs[A]("«at»(H)")
			ih := arg.TermAs[A]("M.inv(«at»(H))")
			xParts := arg.Conjuncts(
				arg.Unfolded(xPoint, projective_curve.ProjectiveEquationPointsDef),
				"the coordinates of x up to n lie in K",
				"those past n are zero",
				"the first nonzero one is one",
				"and the equations vanish at x")
			KInM := arg.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			lInM := arg.Have(
				"and so does l",
				"l ⊆ M.carrier",
				By(lSub, field.SubfieldSubset))
			xInM := arg.Have(
				"the coordinates of x lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(xParts[0], KInM))
			atX := arg.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, xParts[0], Read(projective_curve.PointEvaluation, M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			hParts := arg.Conjuncts(
				arg.Have(
					"H(x) and its inverse lie in M",
					"«at»(H) ∈ M.carrier ∧ M.inv(«at»(H)) ∈ M.carrier",
					BySets(homogeneous_polynomial.FormPolynomial.Read(form), atX[1], KInM, field.InvIn.Read(M))),
				"H(x) lies in M",
				"and so does its inverse")
			inclusion := arg.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			chartParts := arg.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, xInM, form, Read(projective_curve.ChartSubring, M).At(k, K, n, r, x, H)),
				"the chart is a subring of M",
				"holding k")
			chartRingOn := arg.Have(
				"the chart is a ring under the operations of M",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(H)))",
				By(chartParts[0], comm_ring.SubringRingOn.Read(ring).At(chart)))
			mapping := arg.Conjuncts(
				arg.Have(
					"φ is a ring map from the chart into l fixing k",
					"ring_homomorphism(restrict_ring(field_ring(M), «chart»(H)), "+
						"    restrict_ring(field_ring(M), l), "+
						"    φ) ∧ "+
						"(∀c:A. c ∈ k ⇒ φ(c) = c)",
					By(point, algebra_points.AlgebraPointsMember.At(chartRing, lRing, k, identity, φ))),
				"φ is a ring map from the chart into l",
				"fixing k")
			intoM := arg.Have(
				"so φ is a ring map from the chart into M",
				"ring_homomorphism(restrict_ring(field_ring(M), «chart»(H)), field_ring(M), φ)",
				By(mapping[0], lInM, ring, ring_homomorphism.RingHomExtendTarget.At(chartRing, fieldRing, φ, l)))

			i0, i0Data := arg.ObtainAs[Nat](
				"φ does not kill every quotient x(i)^r/H(x): they "+
					"generate the unit ideal of the chart, and φ keeps one",
				"∃i₀:num. i₀ ≤ n ∧ φ(monoid_pow(M.mul, M.one, x(i₀), r) * M.inv(«at»(H))) ≠ M.zero",
				Derive(func(b *Argument) {
					generate := b.Conjuncts(
						GroupPremises(
							kSub,
							KSub,
							kInK,
							xParts[0],
							form,
							positive,
							nonzero,
							Read(projective_form_chart.ChartQuotientsGenerate, M).At(k, K, n, r, x, H)),
						"the quotients x(i)^r/H(x) lie in the chart",
						"and generate its unit ideal")
					killed := b.Have(
						"suppose φ kills every quotient",
						"∀y:A. y ∈ «quotients» ⇒ φ(y) = M.zero",
						BySets(b.SupposeNot()))
					spanIn := b.Have(
						"then its kernel holds their span",
						"ideal_span(restrict_ring(field_ring(M), «chart»(H)), «quotients») ⊆ "+
							"ring_kernel(M.zero, «chart»(H), φ)",
						By(
							generate[0],
							killed,
							ring_homomorphism.IdealSpanInKernel.Read(mapping[0]).At(b.TermAs[Set[A]]("«quotients»"))))
					b.Show(
						"and one, which φ takes to one",
						By(
							b.Have(
								"φ kills one, which lies in the span",
								"φ(M.one) = M.zero",
								BySets(generate[1], spanIn, ring_homomorphism.RingKernelDef.At(b.TermAs[A]("M.zero"), chart, φ))),
							ring_homomorphism.MapOne.Read(mapping[0]),
							field.OneNotZeroOn.Read(M)))
				}))
			i0Parts := arg.Conjuncts(
				i0Data,
				"i₀ is at most n",
				"φ does not kill x(i₀)^r/H(x)")

			s, sDef := arg.LetAs[A]("s", "monoid_pow(M.mul, M.one, x(i₀), r - 1) * M.inv(«at»(H))")
			x0 := arg.TermAs[A]("x(i₀)")
			x0In := arg.Have(
				"x(i₀) lies in M",
				"x(i₀) ∈ M.carrier",
				By(i0Parts[0], xInM.At(i0)))
			x0Lower := arg.Have(
				"and so does x(i₀)^(r−1)",
				"monoid_pow(M.mul, M.one, x(i₀), r - 1) ∈ M.carrier",
				By(x0In, powIn.AsFact().At(x0, lower)))
			sIn := arg.Have(
				"so s = x(i₀)^(r−1)/H(x) lies in M",
				"s ∈ M.carrier",
				sDef.Rw(),
				By(x0Lower, hParts[1], comm_ring.MulIn.Read(ring)))
			mixedForms := arg.Have(
				"for j up to n, X_j·X_i₀^(r−1) is a form of degree r·1 whose value over H(x) is x(j)·s",
				Statement{
					Binders:    "∀j:num.",
					Hypotheses: []string{"j ≤ n"},
					Conclusion: "homogeneous_polynomial(«hilbertCoefficients», n, r * 1, «mixed»(j, i₀)) ∧ " +
						"«at»(«mixed»(j, i₀)) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), 1) = x(j) * s",
				},
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					jIn := b.Assume()
					parts := b.Conjuncts(
						GroupPremises(
							kSub,
							positive,
							jIn,
							i0Parts[0],
							xInM,
							Read(homogeneous_polynomial.MixedMonomialForm, M).At(k, n, r, j, i0, x)),
						"X_j·X_i₀^(r−1) is a form of degree r",
						"with value x(j)·x(i₀)^(r−1) at x")
					value := b.Have(
						"its value over H(x)^1 is x(j)·x(i₀)^(r−1)·H(x)^(−1) = x(j)·s",
						"«at»(«mixed»(j, i₀)) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), 1) = x(j) * s",
						sDef.Rw(),
						parts[1].Rw(),
						GroupPremises(hParts[1], comm_monoid.PowOneOn.Read(monoid).AsFact().At(ih)).Rw(),
						ByArith(
							M,
							b.Have(
								"x(j) lies in M",
								"x(j) ∈ M.carrier",
								By(jIn, xInM.At(j))),
							x0Lower,
							hParts[1]))
					b.Show(
						"of degree r·1, with that value",
						By(parts[0], nat_arith.MulOne.At(r), value))
				}))
			inChart := arg.Have(
				"so each x(j)·s lies in the chart",
				"∀j:num. j ≤ n ⇒ x(j) * s ∈ «chart»(H)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					mixed := b.Conjuncts(
						GroupPremises(b.Assume(), mixedForms.At(j)),
						"X_j·X_i₀^(r−1) is a form of degree r·1",
						"whose value over H(x) is x(j)·s")
					b.Show(
						"the value of a form of degree r over H(x) lies in the chart",
						mixed[1].RwRev(),
						By(
							kSub,
							KSub,
							kInK,
							xParts[0],
							form,
							nonzero,
							mixed[0],
							Read(projective_curve.ChartQuotient, M).At(
								k, K, n, r, one, x, H, b.TermAs[Fun[Fun[Nat, Nat], A]]("«mixed»(j, i₀)"))))
				}))

			θ := arg.TermAs[Fun[Nat, A]]("λj:num. x(j) * s")
			w := arg.TermAs[Fun[Nat, A]]("λj:num. φ(x(j) * s)")
			commutes := arg.Have(
				"φ commutes with evaluating the forms over k at the points x(j)·s of the chart",
				Statement{
					Binders: "∀d:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "φ(«valueAt»(λj:num. x(j) * s, P)) = «valueAt»(λj:num. φ(x(j) * s), P)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("d")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					polynomial := b.Have(
						"a form is a polynomial over k",
						"P ∈ «polynomials».carrier",
						By(homogeneous_polynomial.FormPolynomial.Read(b.Assume())))
					b.Show(
						"by the naturality of evaluation",
						By(GroupPremises(
							kSub,
							chartParts[0],
							chartParts[1],
							inChart,
							intoM,
							mapping[1],
							polynomial,
							Read(projective_curve.EvaluationNatural, M).At(k, chart, n, θ, φ, P))))
				}))
			wIn := arg.Have(
				"the coordinates of w = φ(x(·)·s) up to n lie in l, φ taking the chart into l",
				"∀j:num. j ≤ n ⇒ φ(x(j) * s) ∈ l",
				By(inChart, ring_homomorphism.MapIn.Read(mapping[0])))
			wInM := arg.Have(
				"and so in M",
				"∀j:num. j ≤ n ⇒ φ(x(j) * s) ∈ M.carrier",
				BySets(wIn, lInM))
			wPast := arg.Have(
				"past n they are zero, x being zero there",
				"∀j:num. n < j ⇒ φ(x(j) * s) = M.zero",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					beyond := b.Assume()
					b.Show(
						"φ(0·s) = φ(0) = 0",
						GroupPremises(beyond, xParts[1].At(j)).Rw(),
						By(
							ring_homomorphism.MapZero.Read(intoM),
							b.Have(
								"0·s = 0",
								"M.zero * s = M.zero",
								ByArith(M, sIn))))
				}))
			wZeros := arg.Have(
				"w is a zero of E: P(w) = φ(P(x·s)) = φ(s^d·P(x)) = φ(0)",
				"∀P:((num → num) → A). P ∈ E ⇒ «valueAt»(λj:num. φ(x(j) * s), P) = M.zero",
				Derive(func(b *Argument) {
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					inE := b.Assume()
					d, pForm := b.UnpackAs[Nat](GroupPremises(inE, forms.At(P)), "d")
					scaled := b.Have(
						"P(x·s) = s^d·P(x), P being a form of degree d",
						"«valueAt»(λj:num. x(j) * s, P) = monoid_pow(M.mul, M.one, s, d) * «at»(P)",
						By(
							inclusion,
							pForm,
							xInM,
							sIn,
							At(homogeneous_polynomial.FormScaling, coefficients, fieldRing, identity, n, d, x, s, P)))
					vanishes := b.Have(
						"so P(x·s) = 0, P(x) being zero",
						"«valueAt»(λj:num. x(j) * s, P) = M.zero",
						scaled.Rw(),
						GroupPremises(inE, xParts[3].At(P)).Rw(),
						ByArith(M, GroupPremises(sIn, powIn.AsFact().At(s, d))))
					b.Show(
						"and φ keeps zero",
						By(vanishes, GroupPremises(pForm, commutes.At(d, P)), ring_homomorphism.MapZero.Read(intoM)))
				}))

			transport := arg.Have(
				"the ratio of P to H^a is carried from x to x·s and, by φ, to w: φ(P(x)/H(x)^a)·H(w)^a = P(w)",
				Statement{
					Binders:    "∀a:num. ∀P:((num → num) → A).",
					Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)"},
					Conclusion: "φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) ∈ M.carrier ∧ " +
						"φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) * " +
						"monoid_pow(M.mul, M.one, «valueAt»(λj:num. φ(x(j) * s), H), a) = " +
						"«valueAt»(λj:num. φ(x(j) * s), P)",
				},
				Derive(func(b *Argument) {
					a := b.FixAs[Nat]("a")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					pForm := b.Assume()
					q := b.TermAs[A]("«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)")
					qIn := b.Have(
						"P(x)/H(x)^a lies in the chart",
						"«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) ∈ «chart»(H)",
						By(
							kSub,
							KSub,
							kInK,
							xParts[0],
							form,
							nonzero,
							pForm,
							Read(projective_curve.ChartQuotient, M).At(k, K, n, r, a, x, H, P)))
					pValue := b.Have(
						"P(x) lies in M",
						"«at»(P) ∈ M.carrier",
						BySets(homogeneous_polynomial.FormPolynomial.Read(pForm), atX[1], KInM))
					unit := b.Have(
						"H(x)^(−a)·H(x)^a = 1, H(x) being nonzero",
						"monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) * monoid_pow(M.mul, M.one, «at»(H), a) = M.one",
						By(
							hParts[0],
							hParts[1],
							b.Have(
								"H(x)^(−1)·H(x) = 1",
								"M.inv(«at»(H)) * «at»(H) = M.one",
								By(nonzero, hParts[0], field.MulLeftInverseOn.Read(M))),
							comm_monoid.PowInverseOn.Read(monoid).AsFact().At(ih, h, a)))
					back := b.Have(
						"P(x)/H(x)^a times H(x)^a is P(x)",
						"«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) * monoid_pow(M.mul, M.one, «at»(H), a) = "+
							"«at»(P)",
						ByArith(
							M,
							pValue,
							GroupPremises(hParts[0], powIn.AsFact().At(h, a)),
							GroupPremises(hParts[1], powIn.AsFact().At(ih, a)),
							Scaled(b.TermAs[A]("«at»(P)"), unit)))
					atθ := b.Have(
						"so P(x)/H(x)^a·H(x·s)^a = P(x·s), the ratio not changing with the scale s",
						"«at»(P) * "+
							"monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) * "+
							"monoid_pow(M.mul, M.one, «valueAt»(λj:num. x(j) * s, H), a) = "+
							"«valueAt»(λj:num. x(j) * s, P)",
						By(GroupPremises(
							kSub,
							form,
							pForm,
							xInM,
							sIn,
							b.Have(
								"P(x)/H(x)^a lies in M",
								"«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) ∈ M.carrier",
								BySets(qIn, KInM)),
							back,
							Read(homogeneous_polynomial.FormRatioScaling, M).At(k, n, r, a, x, s, q, H, P))))
					hθ := b.TermAs[A]("«valueAt»(λj:num. x(j) * s, H)")
					hθIn := b.Have(
						"H(x·s) lies in the chart, a subring holding k and the x(j)·s",
						"«valueAt»(λj:num. x(j) * s, H) ∈ «chart»(H)",
						By(GroupPremises(
							inclusion,
							chartParts[0],
							b.Have(
								"the constants lie in the chart",
								"∀c:A. c ∈ «hilbertCoefficients».carrier ⇒ c ∈ «chart»(H)",
								BySets(chartParts[1])),
							b.Have(
								"and so do the points x(j)·s",
								"∀j:num. j ∈ {i:num | i ≤ n} ⇒ x(j) * s ∈ «chart»(H)",
								BySets(inChart)),
							b.Have(
								"H is a polynomial in the variables up to n",
								"H ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
								By(homogeneous_polynomial.FormPolynomial.Read(form))),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring.At(
								coefficients, fieldRing, identity, θ, variables, chart, H))))
					hθPower := b.TermAs[A]("monoid_pow(M.mul, M.one, «valueAt»(λj:num. x(j) * s, H), a)")
					image := b.Have(
						"φ takes P(x·s) to φ(P(x)/H(x)^a)·φ(H(x·s))^a",
						"φ(«valueAt»(λj:num. x(j) * s, P)) = "+
							"φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) * "+
							"monoid_pow(M.mul, M.one, φ(«valueAt»(λj:num. x(j) * s, H)), a)",
						atθ.RwRev(),
						By(
							qIn,
							hθIn,
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRingOn)).AsFact().At(hθ, a),
							ring_homomorphism.MapMul.Read(intoM).AsFact().At(q, hθPower),
							ring_homomorphism.RingMapPower.Read(intoM).AsFact().At(a, hθ)))
					b.Show(
						"φ(P(x)/H(x)^a) lies in M, and φ(P(x·s)) = P(w), φ(H(x·s)) = H(w)",
						By(
							b.Have(
								"φ(P(x)/H(x)^a) lies in M",
								"φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) ∈ M.carrier",
								By(GroupPremises(qIn, ring_homomorphism.MapIn.Read(intoM).AsFact().At(q)))),
							b.Have(
								"and times H(w)^a = φ(H(x·s))^a it is φ(P(x·s)) = P(w)",
								"φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) * "+
									"monoid_pow(M.mul, M.one, «valueAt»(λj:num. φ(x(j) * s), H), a) = "+
									"«valueAt»(λj:num. φ(x(j) * s), P)",
								GroupPremises(form, commutes.At(r, H)).RwRev(),
								GroupPremises(pForm, commutes.At(b.TermAs[Nat]("r * a"), P)).RwRev(),
								By(image))))
				}))

			w0 := arg.TermAs[A]("φ(x(i₀) * s)")
			w0Nonzero := arg.Have(
				"w(i₀) = φ(x(i₀)^r/H(x)) is not zero",
				"φ(x(i₀) * s) ≠ M.zero",
				By(
					i0Parts[1],
					arg.Have(
						"x(i₀)·s = x(i₀)^r/H(x), x(i₀)^r being x(i₀)·x(i₀)^(r−1)",
						"x(i₀) * s = monoid_pow(M.mul, M.one, x(i₀), r) * M.inv(«at»(H))",
						sDef.Rw(),
						arg.Have(
							"x(i₀)^r = x(i₀)·x(i₀)^(r−1), r being positive",
							"monoid_pow(M.mul, M.one, x(i₀), r) = x(i₀) * monoid_pow(M.mul, M.one, x(i₀), r - 1)",
							By(
								x0In,
								arg.Have(
									"1 + (r − 1) = r",
									"1 + (r - 1) = r",
									ByArith(positive)),
								comm_monoid.PowAddOn.Read(monoid).AsFact().At(x0, one, lower),
								comm_monoid.PowOneOn.Read(monoid).AsFact().At(x0))).Rw(),
						ByArith(M, x0In, x0Lower, hParts[1]))))
			hw := arg.TermAs[A]("«valueAt»(λj:num. φ(x(j) * s), H)")
			hwIn := arg.Have(
				"H(w) lies in M",
				"«valueAt»(λj:num. φ(x(j) * s), H) ∈ M.carrier",
				By(
					homogeneous_polynomial.FormPolynomial.Read(form),
					ring_homomorphism.MapIn.Read(arg.Have(
						"evaluation at w is a ring map into M",
						"ring_homomorphism(«polynomials», "+
							"    field_ring(M), "+
							"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, λj:num. φ(x(j) * s)))",
						By(wInM, inclusion, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom)))))
			w0Lower := arg.TermAs[A]("monoid_pow(M.mul, M.one, φ(x(i₀) * s), r - 1)")
			hwNonzero := arg.Have(
				"H does not vanish at w: read at X_i₀·X_i₀^(r−1), the transport "+
					"gives w(i₀)·H(w) = w(i₀)·w(i₀)^(r−1), and w(i₀) is not zero",
				"«valueAt»(λj:num. φ(x(j) * s), H) ≠ M.zero",
				Derive(func(b *Argument) {
					w0In := b.Have(
						"w(i₀) lies in M",
						"φ(x(i₀) * s) ∈ M.carrier",
						By(i0Parts[0], wInM.At(i0)))
					mixedAt := b.Conjuncts(
						GroupPremises(i0Parts[0], mixedForms.At(i0)),
						"X_i₀·X_i₀^(r−1) is a form of degree r·1",
						"whose value over H(x) is x(i₀)·s")
					read := b.Conjuncts(
						GroupPremises(mixedAt[0], transport.At(one, b.TermAs[Fun[Fun[Nat, Nat], A]]("«mixed»(i₀, i₀)"))),
						"φ(x(i₀)·s) lies in M",
						"and times H(w) it is the value of X_i₀·X_i₀^(r−1) at w")
					identity0 := b.Have(
						"so w(i₀)·H(w) = w(i₀)·w(i₀)^(r−1)",
						"φ(x(i₀) * s) * «valueAt»(λj:num. φ(x(j) * s), H) = "+
							"φ(x(i₀) * s) * monoid_pow(M.mul, M.one, φ(x(i₀) * s), r - 1)",
						By(
							read[1],
							mixedAt[1],
							GroupPremises(hwIn, comm_monoid.PowOneOn.Read(monoid).AsFact().At(hw)),
							GroupPremises(
								kSub,
								positive,
								i0Parts[0],
								wInM,
								Read(homogeneous_polynomial.MixedMonomialForm, M).At(k, n, r, i0, i0, w))))
					vanishing := b.SupposeNot()
					product := b.Have(
						"w(i₀)·w(i₀)^(r−1) = w(i₀)·H(w) = 0",
						"φ(x(i₀) * s) * monoid_pow(M.mul, M.one, φ(x(i₀) * s), r - 1) = M.zero",
						identity0.RwRev(),
						ByArith(M, w0In, hwIn, vanishing))
					b.Show(
						"so w(i₀) = 0, a contradiction",
						By(
							product,
							w0Nonzero,
							w0In,
							GroupPremises(w0In, powIn.AsFact().At(w0, lower)),
							field.MulEqZeroOn.Read(M).AsFact().At(w0, w0Lower),
							field.PowEqZeroOn.Read(M).AsFact().At(w0, lower)))
				}))

			c, cData := arg.ObtainAs[A](
				"scaled by the inverse of its first nonzero coordinate, w is a point of the curve over l",
				"∃c:A. "+
					"    c ∈ l ∧ "+
					"    c ≠ M.zero ∧ "+
					"    (λi:num. φ(x(i) * s) * c) ∈ projective_equation_points(field_ring(M), k, l, n, E)",
				By(GroupPremises(
					kSub,
					lSub,
					forms,
					wIn,
					wPast,
					i0Parts[0],
					w0Nonzero,
					wZeros,
					Read(projective_curve.PointNormalization, M).At(k, l, n, i0, E, w))))
			cParts := arg.Conjuncts(
				cData,
				"c lies in l",
				"c is not zero",
				"and z = w·c is a point of the curve over l")
			cIn := arg.Have(
				"c lies in M",
				"c ∈ M.carrier",
				BySets(cParts[0], lInM))
			cr := arg.TermAs[A]("monoid_pow(M.mul, M.one, c, r)")
			hzScaled := arg.Have(
				"H(z) = c^r·H(w)",
				"«valueAt»(λi:num. φ(x(i) * s) * c, H) = "+
					"monoid_pow(M.mul, M.one, c, r) * «valueAt»(λj:num. φ(x(j) * s), H)",
				By(
					inclusion,
					form,
					wInM,
					cIn,
					At(homogeneous_polynomial.FormScaling, coefficients, fieldRing, identity, n, r, w, c, H)))
			crIn := arg.Have(
				"c^r lies in M",
				"monoid_pow(M.mul, M.one, c, r) ∈ M.carrier",
				By(cIn, powIn.AsFact().At(c, r)))
			hz := arg.TermAs[A]("«valueAt»(λi:num. φ(x(i) * s) * c, H)")
			ihz := arg.TermAs[A]("M.inv(«valueAt»(λi:num. φ(x(i) * s) * c, H))")
			hzIn := arg.Have(
				"H(z) lies in M",
				"«valueAt»(λi:num. φ(x(i) * s) * c, H) ∈ M.carrier",
				hzScaled.Rw(),
				By(crIn, hwIn, comm_ring.MulIn.Read(ring)))
			hzNonzero := arg.Have(
				"H(z) is not zero, neither c^r nor H(w) being zero",
				"«valueAt»(λi:num. φ(x(i) * s) * c, H) ≠ M.zero",
				hzScaled.Rw(),
				By(
					hwNonzero,
					cParts[1],
					crIn,
					hwIn,
					cIn,
					field.MulEqZeroOn.Read(M).AsFact().At(cr, hw),
					field.PowEqZeroOn.Read(M).AsFact().At(c, r)))
			ihzIn := arg.Have(
				"and so does its inverse",
				"M.inv(«valueAt»(λi:num. φ(x(i) * s) * c, H)) ∈ M.carrier",
				By(hzIn, field.InvIn.Read(M)))
			evaluates := arg.Have(
				"φ takes P(x)/H(x)^a to P(z)/H(z)^a",
				Statement{
					Binders: "∀a:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)",
					},
					Conclusion: "φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
						"«valueAt»(λi:num. φ(x(i) * s) * c, P) * " +
						"monoid_pow(M.mul, M.one, M.inv(«valueAt»(λi:num. φ(x(i) * s) * c, H)), a)",
				},
				Derive(func(b *Argument) {
					a := b.FixAs[Nat]("a")
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					pForm := b.Assume()
					v := b.TermAs[A]("φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a))")
					ratioAtW := b.Conjuncts(
						GroupPremises(pForm, transport.At(a, P)),
						"φ(P(x)/H(x)^a) lies in M",
						"and times H(w)^a it is P(w)")
					ratioAtZ := b.Have(
						"so times H(z)^a it is P(z), the ratio not changing with the scale c",
						"φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) * "+
							"monoid_pow(M.mul, M.one, «valueAt»(λi:num. φ(x(i) * s) * c, H), a) = "+
							"«valueAt»(λi:num. φ(x(i) * s) * c, P)",
						By(GroupPremises(
							kSub,
							form,
							pForm,
							wInM,
							cIn,
							ratioAtW[0],
							ratioAtW[1],
							Read(homogeneous_polynomial.FormRatioScaling, M).At(k, n, r, a, w, c, v, H, P))))
					unit := b.Have(
						"H(z)^a·H(z)^(−a) = 1",
						"monoid_pow(M.mul, M.one, «valueAt»(λi:num. φ(x(i) * s) * c, H), a) * "+
							"monoid_pow(M.mul, M.one, M.inv(«valueAt»(λi:num. φ(x(i) * s) * c, H)), a) = "+
							"M.one",
						By(
							hzIn,
							ihzIn,
							b.Have(
								"H(z)·H(z)^(−1) = 1",
								"«valueAt»(λi:num. φ(x(i) * s) * c, H) * M.inv(«valueAt»(λi:num. φ(x(i) * s) * c, H)) = M.one",
								By(hzNonzero, hzIn, field.MulRightInverseOn.Read(M))),
							comm_monoid.PowInverseOn.Read(monoid).AsFact().At(hz, ihz, a)))
					b.Show(
						"divide by H(z)^a",
						ratioAtZ.RwRev(),
						ByArith(
							M,
							ratioAtW[0],
							GroupPremises(hzIn, powIn.AsFact().At(hz, a)),
							GroupPremises(ihzIn, powIn.AsFact().At(ihz, a)),
							Scaled(v, unit)))
				}))
			arg.Show(
				"z = w·c is the point",
				Witness(arg.TermAs[Fun[Nat, A]]("λi:num. φ(x(i) * s) * c")),
				By(cParts[2], hzNonzero, evaluates))
		}),
})}

// ChartPointsDetermined — two points of the chart of H that agree on the
// quotients P(x)/H(x)^a are equal: a member y of the chart has
// y·H(x)^a = P(x) for a form P of degree r·a, so it is the quotient
// P(x)/H(x)^a, H(x) being nonzero, and off the chart both points vanish.
var ChartPointsDetermined = chartPointsDeterminedThm{family.Add(registry.ProofEntry{
	Name: "ChartPointsDetermined",
	Key:  "prop_8de7916635ff0827",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K l:set(A). " +
			"∀n r:num. " +
			"∀x:(num → A). " +
			"∀H:((num → num) → A). " +
			"∀φ ψ:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
			"«at»(H) ≠ M.zero",
			"φ ∈ " +
				"algebra_points(restrict_ring(field_ring(M), «chart»(H)), " +
				"    restrict_ring(field_ring(M), l), " +
				"    k, " +
				"    λa:A. a)",
			"ψ ∈ " +
				"algebra_points(restrict_ring(field_ring(M), «chart»(H)), " +
				"    restrict_ring(field_ring(M), l), " +
				"    k, " +
				"    λa:A. a)",
			"∀a:num. ∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ⇒ " +
				"    φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
				"    ψ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a))",
		},
		Conclusion: "φ = ψ",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			H *Arrow[Fun[Nat, Nat], A],
			φ, ψ *Arrow[A, A],
			kSub, KSub, kInK, coordinates, form, nonzero, φPoint, ψPoint, agree Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			chartRing := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «chart»(H))")
			values := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), l)")
			identity := arg.TermAs[Fun[A, A]]("λa:A. a")
			h := arg.TermAs[A]("«at»(H)")
			offChart := arg.Have(
				"both points vanish off the chart",
				"∀y:A. y ∉ «chart»(H) ⇒ φ(y) = M.zero ∧ ψ(y) = M.zero",
				By(
					φPoint,
					ψPoint,
					algebra_points.AlgebraPointsMember.At(chartRing, values, k, identity, φ),
					algebra_points.AlgebraPointsMember.At(chartRing, values, k, identity, ψ)))
			atX := arg.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, Read(projective_curve.PointEvaluation, M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			KInM := arg.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			hParts := arg.Conjuncts(
				arg.Have(
					"H(x) and its inverse lie in M",
					"«at»(H) ∈ M.carrier ∧ M.inv(«at»(H)) ∈ M.carrier",
					BySets(homogeneous_polynomial.FormPolynomial.Read(form), atX[1], KInM, field.InvIn.Read(M))),
				"H(x) lies in M",
				"and so does its inverse")
			onChart := arg.Have(
				"on the chart they agree: a member of it is a quotient P(x)/H(x)^a",
				"∀y:A. y ∈ «chart»(H) ⇒ φ(y) = ψ(y)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yParts := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·H(x)^a is the value of a form of degree r·a")
					a, P, yForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yParts[1], "a", "P")
					yData := b.Conjuncts(
						yForm,
						"P is a form of degree r·a",
						"y·H(x)^a = P(x)")
					powers := b.Have(
						"H(x)^a·H(x)^(−a) = 1, H(x) being nonzero",
						"monoid_pow(M.mul, M.one, «at»(H), a) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a) = M.one",
						By(
							hParts[0],
							hParts[1],
							b.Have(
								"H(x)·H(x)^(−1) = 1",
								"«at»(H) * M.inv(«at»(H)) = M.one",
								By(nonzero, hParts[0], field.MulRightInverseOn.Read(M))),
							comm_monoid.PowInverseOn.Read(monoid).AsFact().At(h, b.TermAs[A]("M.inv(«at»(H))"), a)))
					quotient := b.Have(
						"so y = P(x)/H(x)^a",
						"y = «at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)",
						yData[1].RwRev(),
						ByArith(
							M,
							b.Have(
								"y lies in M",
								"y ∈ M.carrier",
								BySets(yParts[0], KInM)),
							hParts[0],
							hParts[1],
							comm_monoid.PowIn.Read(monoid).AsFact().At(h, a),
							comm_monoid.PowIn.Read(monoid).AsFact().At(b.TermAs[A]("M.inv(«at»(H))"), a),
							Scaled(y, powers)))
					b.Show(
						"φ and ψ agree on the quotient",
						quotient.Rw(),
						By(yData[0], agree.At(a, P)))
				}))
			arg.Show(
				"so they agree everywhere",
				Funext(),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					b.Cases(b.TermAs[Bool]("y ∈ «chart»(H)"))
					b.When(
						"on the chart",
						func(c *Argument, inside Fact) {
							c.Show(
								"they agree there",
								By(inside, onChart.At(y)))
						})
					b.Otherwise(
						"off the chart both vanish",
						func(c *Argument, outside Fact) {
							c.Show(
								"both are zero",
								By(outside, offChart.At(y)))
						})
				}))
		}),
})}

// FormRatiosDetermine — two points of the curve over M at which every form P
// of degree r·a has the same ratio P/H^a, H nonzero at both, are equal: read
// at the forms X_i·X_j^(r−1), the first nonzero coordinate of each point is
// nonzero at the other, so both are one at the same index p, where H(z) and
// H(w) agree; the forms X_i·X_p^(r−1) then give z(i) = w(i).
var FormRatiosDetermine = formRatiosDetermineThm{family.Add(registry.ProofEntry{
	Name: "FormRatiosDetermine",
	Key:  "prop_28395fc16ef4bbe",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀z w:(num → A). " +
			"∀H:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"0 < r",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
			"z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"w ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"«valueAt»(z, H) ≠ M.zero",
			"«valueAt»(w, H) ≠ M.zero",
			"∀a:num. ∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ⇒ " +
				"    «valueAt»(z, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(z, H)), a) = " +
				"    «valueAt»(w, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(w, H)), a)",
		},
		Conclusion: "z = w",
		Abbrev: Abbrev{
			{Name: "ratio", Text: "λy:(num → A). λi:num. λj:num. " +
				"    y(i) * monoid_pow(M.mul, M.one, y(j), r - 1) * M.inv(«valueAt»(y, H))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			z, w *Arrow[Nat, A],
			H *Arrow[Fun[Nat, Nat], A],
			kSub, positive, form, zIn, wIn, zNonzero, wNonzero, ratios Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			carrier := a.TermAs[Set[A]]("M.carrier")
			one := a.TermAs[Nat]("1")
			lower := a.TermAs[Nat]("r - 1")
			zero := a.TermAs[A]("M.zero")
			hz := a.TermAs[A]("«valueAt»(z, H)")
			hw := a.TermAs[A]("«valueAt»(w, H)")
			cz := a.TermAs[A]("M.inv(«valueAt»(z, H))")
			cw := a.TermAs[A]("M.inv(«valueAt»(w, H))")
			zParts := a.Conjuncts(
				a.Unfolded(zIn, projective_curve.ProjectiveEquationPointsDef),
				"the coordinates of z up to n lie in M",
				"those past n are zero",
				"the first nonzero one is one",
				"and the equations vanish at z")
			wParts := a.Conjuncts(
				a.Unfolded(wIn, projective_curve.ProjectiveEquationPointsDef),
				"the coordinates of w up to n lie in M",
				"those past n are zero",
				"the first nonzero one is one",
				"and the equations vanish at w")
			kInM := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(kSub, field.SubfieldSubset))
			whole := a.Have(
				"M is a subfield of itself",
				"subfield(M, M.carrier)",
				By(field.CarrierSubfield.Read(M)))
			atZ := a.Conjuncts(
				GroupPremises(
					kSub, whole, kInM, zParts[0], Read(projective_curve.PointEvaluation, M).At(k, carrier, n, z)),
				"evaluation at z is a ring map",
				"with values in M")
			atW := a.Conjuncts(
				GroupPremises(
					kSub, whole, kInM, wParts[0], Read(projective_curve.PointEvaluation, M).At(k, carrier, n, w)),
				"evaluation at w is a ring map",
				"with values in M")
			values := a.Conjuncts(
				a.Have(
					"H(z), H(w) and their inverses lie in M",
					"«valueAt»(z, H) ∈ M.carrier ∧ "+
						"«valueAt»(w, H) ∈ M.carrier ∧ "+
						"M.inv(«valueAt»(z, H)) ∈ M.carrier ∧ "+
						"M.inv(«valueAt»(w, H)) ∈ M.carrier",
					BySets(homogeneous_polynomial.FormPolynomial.Read(form), atZ[1], atW[1], field.InvIn.Read(M))),
				"H(z) lies in M",
				"so does H(w)",
				"and the inverse of H(z)",
				"and that of H(w)")
			ratio := a.Have(
				"read at the forms X_i·X_j^(r−1) of degree r, the "+
					"ratios give z(i)·z(j)^(r−1)/H(z) = w(i)·w(j)^(r−1)/H(w)",
				"∀i j:num. i ≤ n ∧ j ≤ n ⇒ «ratio»(z, i, j) = «ratio»(w, i, j)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					j := b.FixAs[Nat]("j")
					indices := b.Conjuncts(
						b.Assume(),
						"i is at most n",
						"so is j")
					mixedAtZ := b.Conjuncts(
						GroupPremises(
							kSub,
							positive,
							indices[0],
							indices[1],
							zParts[0],
							Read(homogeneous_polynomial.MixedMonomialForm, M).At(k, n, r, i, j, z)),
						"X_i·X_j^(r−1) is a form of degree r",
						"with value z(i)·z(j)^(r−1) at z")
					mixedAtW := b.Have(
						"and with value w(i)·w(j)^(r−1) at w",
						"polynomial_algebra_eval(«hilbertCoefficients», "+
							"    field_ring(M), "+
							"    λa:A. a, "+
							"    w, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», "+
							"        polynomial_algebra_var(«hilbertCoefficients», i), "+
							"        monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), "+
							"            polynomial_algebra_one(«hilbertCoefficients»), "+
							"            polynomial_algebra_var(«hilbertCoefficients», j), "+
							"            r - 1))) = "+
							"w(i) * monoid_pow(M.mul, M.one, w(j), r - 1)",
						By(
							kSub,
							positive,
							indices[0],
							indices[1],
							wParts[0],
							Read(homogeneous_polynomial.MixedMonomialForm, M).At(k, n, r, i, j, w)))
					mixed := b.TermAs[Fun[Fun[Nat, Nat], A]](
						"polynomial_algebra_mul(«hilbertCoefficients», " +
							"    polynomial_algebra_var(«hilbertCoefficients», i), " +
							"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
							"        polynomial_algebra_one(«hilbertCoefficients»), " +
							"        polynomial_algebra_var(«hilbertCoefficients», j), " +
							"        r - 1))")
					b.Show(
						"the ratio of X_i·X_j^(r−1) to H",
						By(
							b.Have(
								"X_i·X_j^(r−1) is a form of degree r·1",
								"homogeneous_polynomial(«hilbertCoefficients», "+
									"    n, "+
									"    r * 1, "+
									"    polynomial_algebra_mul(«hilbertCoefficients», "+
									"        polynomial_algebra_var(«hilbertCoefficients», i), "+
									"        monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), "+
									"            polynomial_algebra_one(«hilbertCoefficients»), "+
									"            polynomial_algebra_var(«hilbertCoefficients», j), "+
									"            r - 1)))",
								By(mixedAtZ[0], nat_arith.MulOne.At(r))),
							ratios.At(one, mixed),
							mixedAtZ[1],
							mixedAtW,
							values[2],
							values[3],
							comm_monoid.PowOneOn.Read(monoid).AsFact().At(cz),
							comm_monoid.PowOneOn.Read(monoid).AsFact().At(cw)))
				}))
			p, zFirst := a.UnpackAs[Nat](zParts[2], "p")
			zIndex := a.Conjuncts(
				zFirst,
				"p is at most n",
				"z(p) is one",
				"and z vanishes before p")
			q, wFirst := a.UnpackAs[Nat](wParts[2], "q")
			wIndex := a.Conjuncts(
				wFirst,
				"q is at most n",
				"w(q) is one",
				"and w vanishes before q")
			identityPower := comm_monoid.IdentityPowOn.Read(monoid).AsFact().At(lower)
			atP := a.Have(
				"at i = j = p the ratio at z is H(z)^(−1), z(p) being one",
				"«ratio»(z, p, p) = M.inv(«valueAt»(z, H))",
				zIndex[1].Rw(),
				ByArith(M, values[2], identityPower))
			atQ := a.Have(
				"and at i = j = q the ratio at w is H(w)^(−1)",
				"«ratio»(w, q, q) = M.inv(«valueAt»(w, H))",
				wIndex[1].Rw(),
				ByArith(M, values[3], identityPower))
			zeroPower := comm_monoid.PowIn.Read(monoid).AsFact().At(zero, lower)
			wAtP := a.Have(
				"w(p) is not zero: the ratio at w would vanish at (p, p), where at z it is H(z)^(−1) ≠ zero",
				"w(p) ≠ M.zero",
				By(
					atP,
					GroupPremises(zIndex[0], ratio.At(p, p)),
					a.Have(
						"H(z)^(−1) is not zero",
						"M.inv(«valueAt»(z, H)) ≠ M.zero",
						By(zNonzero, values[0], field.InvEqZeroOn.Read(M).AsFact().At(hz))),
					a.Have(
						"a ratio at w vanishes where its first coordinate does",
						"w(p) = M.zero ⇒ «ratio»(w, p, p) = M.zero",
						Derive(func(b *Argument) {
							b.Show(
								"zero times anything is zero",
								b.Assume().Rw(),
								ByArith(M, values[3], comm_ring.ZeroIn.Read(ring), zeroPower))
						}))))
			zAtQ := a.Have(
				"and z(q) is not zero, likewise",
				"z(q) ≠ M.zero",
				By(
					atQ,
					GroupPremises(wIndex[0], ratio.At(q, q)),
					a.Have(
						"H(w)^(−1) is not zero",
						"M.inv(«valueAt»(w, H)) ≠ M.zero",
						By(wNonzero, values[1], field.InvEqZeroOn.Read(M).AsFact().At(hw))),
					a.Have(
						"a ratio at z vanishes where its first coordinate does",
						"z(q) = M.zero ⇒ «ratio»(z, q, q) = M.zero",
						Derive(func(b *Argument) {
							b.Show(
								"zero times anything is zero",
								b.Assume().Rw(),
								ByArith(M, values[2], comm_ring.ZeroIn.Read(ring), zeroPower))
						}))))
			same := a.Have(
				"so the two normalizations sit at one index: p is not before q, where w vanishes, nor q before p",
				"p = q",
				ByArith(
					a.Have(
						"p is not before q",
						"¬(p < q)",
						By(wAtP, wIndex[2])),
					a.Have(
						"q is not before p",
						"¬(q < p)",
						By(zAtQ, zIndex[2]))))
			wOne := a.Have(
				"so w(p) is one",
				"w(p) = M.one",
				By(Normalized, same, wIndex[1]))
			inverses := a.Have(
				"and there the ratios give H(z)^(−1) = H(w)^(−1)",
				"M.inv(«valueAt»(z, H)) = M.inv(«valueAt»(w, H))",
				By(atP, atQ, same, GroupPremises(zIndex[0], ratio.At(p, p))))
			agree := a.Have(
				"z and w agree up to n: the ratios at (i, p) are z(i)·H(z)^(−1) and w(i)·H(w)^(−1)",
				"∀i:num. i ≤ n ⇒ z(i) = w(i)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					inRange := b.Assume()
					coordinates := b.Conjuncts(
						b.Have(
							"z(i) and w(i) lie in M",
							"z(i) ∈ M.carrier ∧ w(i) ∈ M.carrier",
							By(inRange, zParts[0], wParts[0])),
						"z(i) lies in M",
						"and so does w(i)")
					atI := b.Have(
						"z(i)·H(z)^(−1) = w(i)·H(w)^(−1), the ratio at (i, p), z(p) and w(p) being one",
						"z(i) * M.inv(«valueAt»(z, H)) = w(i) * M.inv(«valueAt»(w, H))",
						By(
							GroupPremises(inRange, zIndex[0], ratio.At(b.TermAs[Nat]("i"), p)),
							b.Have(
								"the ratio at z is z(i)·H(z)^(−1)",
								"«ratio»(z, i, p) = z(i) * M.inv(«valueAt»(z, H))",
								zIndex[1].Rw(),
								ByArith(M, identityPower, coordinates[0], values[2])),
							b.Have(
								"and the ratio at w is w(i)·H(w)^(−1)",
								"«ratio»(w, i, p) = w(i) * M.inv(«valueAt»(w, H))",
								wOne.Rw(),
								ByArith(M, identityPower, coordinates[1], values[3]))))
					cancel := b.Have(
						"H(z)·H(z)^(−1) = 1, H(z) being nonzero",
						"«valueAt»(z, H) * M.inv(«valueAt»(z, H)) = M.one",
						By(zNonzero, values[0], field.MulRightInverseOn.Read(M)))
					b.Show(
						"cancel H(z)^(−1), equal to H(w)^(−1)",
						ByArith(
							M,
							coordinates[0],
							coordinates[1],
							values[0],
							values[2],
							values[3],
							Scaled(b.TermAs[A]("z(i)"), cancel),
							Scaled(b.TermAs[A]("w(i)"), cancel),
							Scaled(hz, atI),
							Scaled(b.TermAs[A]("«valueAt»(z, H) * w(i)"), inverses)))
				}))
			a.Show(
				"so z = w, both vanishing past n",
				Funext(),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i ≤ n"))
					b.When(
						"up to n they agree",
						func(c *Argument, inRange Fact) {
							c.Show(
								"by the ratios",
								By(inRange, agree.At(i)))
						})
					b.Otherwise(
						"past n both vanish",
						func(c *Argument, outside Fact) {
							c.Show(
								"both are zero",
								By(
									Normalized,
									c.Have(
										"n < i",
										"n < i",
										ByArith(outside)),
									zParts[1],
									wParts[1]))
						})
				}))
		}),
})}

// PointsMatchCharts — the points of a smooth projective equation curve with
// coordinates in the field of q^m elements correspond one to one with the
// evaluation points of the two charts of F and G: a point where F does not
// vanish goes to its evaluation of the chart of F, flagged chart 0, a point
// where F vanishes to its evaluation of the chart of G, flagged chart 1,
// which kills 1/t = F(x)/G(x). Two points with one evaluation are one point
// (FormRatiosDetermine), and every point of a chart is the evaluation at a
// point of the curve (ChartPointFromMap), one evaluation of the chart at a
// point being the only one (ChartPointsDetermined).
var PointsMatchCharts = pointsMatchChartsThm{family.Add(registry.ProofEntry{
	Name: "PointsMatchCharts",
	Key:  "prop_99942559c975a13f",
	Reading: "A point where neither F nor G vanishes goes to the chart of F alone, the chart " +
		"of G being read only where 1/t vanishes, so no point is counted twice; that F and G have " +
		"no common zero on the curve is what makes every point land somewhere, and the generic " +
		"clause is what makes evaluation at a point of the curve well defined on the chart.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r m:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
			"0 < m",
		},
		Conclusion: "∃f:((num → A) → prod(bool, A → A)). " +
			"    injective_on(«points»(m), f) ∧ " +
			"    image(f, «points»(m)) = " +
			"    curve_evaluation_points(M, " +
			"        k, " +
			"        finite_constants(field_ring(M), card(k), m), " +
			"        «parameter», " +
			"        «chart»(F), " +
			"        «chart»(G))",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "chartPoints", Text: "λH:((num → num) → A). " +
				"    algebra_points(restrict_ring(field_ring(M), «chart»(H)), " +
				"        restrict_ring(field_ring(M), «constants»), " +
				"        k, " +
				"        (λa:A. a))"},
			{Name: "evaluates", Text: "λφ:(A → A). " +
				"λw:(num → A). " +
				"λH:((num → num) → A). " +
				"∀a:num. " +
				"∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ⇒ " +
				"    φ(«at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(H)), a)) = " +
				"    «valueAt»(w, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(w, H)), a)"},
			{Name: "evaluationPoints", Text: "curve_evaluation_points(M, " +
				"    k, " +
				"    «constants», " +
				"    «parameter», " +
				"    «chart»(F), " +
				"    «chart»(G))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r, m *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, gNonzero, noCommonZero, mPositive Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			constants := a.TermAs[Set[A]]("«constants»")
			points := a.TermAs[Set[Fun[Nat, A]]]("«points»(m)")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			evaluationPoints := a.TermAs[Set[Prod[Bool, Fun[A, A]]]]("«evaluationPoints»")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			equations := projective_curve.CurveEquationsForms.Read(curve)
			lField := a.Conjuncts(
				GroupPremises(
					closed,
					kSub,
					projective_curve.CurveConstantsFinite.Read(curve),
					mPositive,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, m)),
				"the field l of q^m elements is a subfield of M",
				"holding k",
				"with q^m elements")
			point := a.Conjuncts(
				generic,
				"x is a point of the curve with coordinates in K",
				"whose coordinates generate K over k",
				"at which a form vanishes exactly when it lies in the ideal")
			xInK := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates of x generate over k",
				"k ⊆ K",
				By(
					point[1],
					a.Have(
						"k lies in M",
						"k ⊆ M.carrier",
						By(kSub, field.SubfieldSubset)),
					a.Have(
						"and so do the coordinates of x",
						"{x(i) | i:num | i ≤ n} ⊆ M.carrier",
						BySets(xInK, KInM)),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			lInM := a.Have(
				"l lies in M",
				"«constants» ⊆ M.carrier",
				By(lField[0], field.SubfieldSubset))
			overM := a.Have(
				"a point of the curve over l is one over M, l lying in M",
				"∀z:(num → A). z ∈ «points»(m) ⇒ z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
				BySets(
					lInM,
					projective_curve.ProjectiveEquationPointsMono.At(
						fieldRing,
						k,
						constants,
						a.TermAs[Set[A]]("M.carrier"),
						n,
						E)))
			evaluationAt := a.Have(
				"evaluation at a point of the curve over l is a ring "+
					"map out of the polynomials over k, with values in l",
				Statement{
					Binders: "∀z:(num → A).",
					Hypotheses: []string{
						"z ∈ «points»(m)",
					},
					Conclusion: "ring_homomorphism(«polynomials», " +
						"    field_ring(M), " +
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z)) ∧ " +
						"(∀P:((num → num) → A). P ∈ «polynomials».carrier ⇒ «valueAt»(z, P) ∈ «constants»)",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]("z")
					zInL := b.Have(
						"the coordinates of z up to n lie in l",
						"∀i:num. i ≤ n ⇒ z(i) ∈ «constants»",
						By(b.Assume(), projective_curve.PointCoordinatesIn))
					b.Show(
						"the coordinates of z lie in l, a subfield holding k",
						By(
							kSub,
							lField[0],
							lField[1],
							zInL,
							Read(projective_curve.PointEvaluation, M).At(k, constants, n, z)))
				}))
			formValues := a.Have(
				"F and G take values in M at the points over l",
				"∀z:(num → A). z ∈ «points»(m) ⇒ «valueAt»(z, F) ∈ M.carrier ∧ «valueAt»(z, G) ∈ M.carrier",
				BySets(
					evaluationAt,
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm),
					lInM))
			specialized := a.Have(
				"every point of the curve over l is a specialization of x: a form "+
					"vanishing at x lies in the ideal of E, which evaluation at the point kills",
				"∀z:(num → A). "+
					"    z ∈ «points»(m) ⇒ "+
					"    ∀P:((num → num) → A). "+
					"        (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ∧ «at»(P) = M.zero ⇒ "+
					"        «valueAt»(z, P) = M.zero",
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]("z")
					zIn := b.Assume()
					evaluation := b.Conjuncts(
						GroupPremises(zIn, evaluationAt.At(z)),
						"evaluation at z is a ring map",
						"with values in l")
					killsE := b.Have(
						"the equations vanish at z",
						"∀P:((num → num) → A). P ∈ E ⇒ «valueAt»(z, P) = M.zero",
						By(zIn, At(projective_curve.PointEquationsVanish, fieldRing, k, constants, n, E, z)))
					killed := b.Have(
						"evaluation at z kills the ideal of E: the equations are polynomials vanishing at z",
						"ideal_span(«polynomials», E) ⊆ "+
							"ring_kernel(M.zero, "+
							"    «polynomials».carrier, "+
							"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z))",
						BySets(
							b.Have(
								"the equations are polynomials, being forms",
								"∀P:((num → num) → A). P ∈ E ⇒ P ∈ «polynomials».carrier",
								Derive(func(c *Argument) {
									P := c.FixAs[Fun[Fun[Nat, Nat], A]]("P")
									inE := c.Assume()
									_, form := c.UnpackAs[Nat](equations.At(c.MemberOf[on.Any](P, inE)), "d")
									c.Show(
										"a form is a polynomial",
										By(homogeneous_polynomial.FormPolynomial.Read(form)))
								})),
							killsE,
							ring_homomorphism.IdealSpanInKernel.Read(evaluation[0]).At(E)))
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					vanishing := b.Conjuncts(
						b.Assume(),
						"P is a form",
						"vanishing at x")
					b.Show(
						"P lies in the ideal of E, so z kills it",
						BySets(
							b.Have(
								"P lies in the ideal of E",
								"P ∈ ideal_span(«polynomials», E)",
								By(vanishing[0], vanishing[1], point[2].At(P))),
							killed,
							ring_homomorphism.RingKernelDef.At(
								b.TermAs[A]("M.zero"),
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«polynomials».carrier"),
								b.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]](
									"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z)"))))
				}))
			chosen := a.Have(
				"for a form H of degree r nonzero at x, choose a point of its chart "+
					"evaluating it at each point of the curve over l where H does not vanish",
				Statement{
					Binders: "∀H:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
						"«at»(H) ≠ M.zero",
					},
					Conclusion: "∃e:((num → A) → A → A). ∀z:(num → A). " +
						"    z ∈ «points»(m) ∧ «valueAt»(z, H) ≠ M.zero ⇒ " +
						"    e(z) ∈ «chartPoints»(H) ∧ «evaluates»(e(z), z, H)",
				},
				Derive(func(b *Argument) {
					H := b.FixAs[Fun[Fun[Nat, Nat], A]]("H")
					form := b.Conjuncts(
						b.Assume(),
						"H is a form of degree r",
						"nonzero at x")
					each := b.Have(
						"each such point evaluates the chart of H, being a specialization of x",
						Statement{
							Binders: "∀z:(num → A).",
							Hypotheses: []string{
								"z ∈ «points»(m)",
								"«valueAt»(z, H) ≠ M.zero",
							},
							Conclusion: "∃φ:(A → A). φ ∈ «chartPoints»(H) ∧ «evaluates»(φ, z, H)",
						},
						Derive(func(c *Argument) {
							z := c.FixAs[Fun[Nat, A]]("z")
							zParts := c.Conjuncts(
								c.Assume(),
								"z is a point of the curve over l",
								"where H does not vanish")
							zInL := c.Have(
								"the coordinates of z up to n lie in l",
								"∀i:num. i ≤ n ⇒ z(i) ∈ «constants»",
								By(zParts[0], projective_curve.PointCoordinatesIn))
							c.Show(
								"evaluation at z",
								By(
									kSub,
									KSub,
									lField[0],
									kInK,
									lField[1],
									xInK,
									zInL,
									form[0],
									form[1],
									zParts[1],
									zParts[0],
									specialized.At(z),
									Read(ChartEvaluation, M).At(k, K, constants, n, r, x, z, H)))
						}))
					b.Show(
						"choose one at each point",
						Witness(b.Term("λz:(num → A). εφ:(A → A). φ ∈ «chartPoints»(H) ∧ «evaluates»(φ, z, H)")),
						By(HilbertDenoted, each))
				}))
			_, fChosen := a.ObtainAs[Fun[Fun[Nat, A], Fun[A, A]]](
				"so a point e₀(z) of the chart of F is chosen at each "+
					"point z of the curve over l where F does not vanish",
				"∃e₀:((num → A) → A → A). ∀z:(num → A). "+
					"    z ∈ «points»(m) ∧ «valueAt»(z, F) ≠ M.zero ⇒ "+
					"    e₀(z) ∈ «chartPoints»(F) ∧ «evaluates»(e₀(z), z, F)",
				By(fForm, fNonzero, chosen.At(F)))
			_, gChosen := a.ObtainAs[Fun[Fun[Nat, A], Fun[A, A]]](
				"and a point e₁(z) of the chart of G at each point z where G does not vanish",
				"∃e₁:((num → A) → A → A). ∀z:(num → A). "+
					"    z ∈ «points»(m) ∧ «valueAt»(z, G) ≠ M.zero ⇒ "+
					"    e₁(z) ∈ «chartPoints»(G) ∧ «evaluates»(e₁(z), z, G)",
				By(gForm, gNonzero, chosen.At(G)))
			f, fDef := a.LetAs[Fun[Fun[Nat, A], Prod[Bool, Fun[A, A]]]](
				"f",
				"λz:(num → A). COND(«valueAt»(z, F) = M.zero, (⊤, e₁(z)), (⊥, e₀(z)))")
			atFirst := a.Have(
				"where F does not vanish, f(z) is e₀(z), flagged as the chart of F",
				"∀z:(num → A). «valueAt»(z, F) ≠ M.zero ⇒ f(z) = (⊥, e₀(z))",
				By(fDef))
			atSecond := a.Have(
				"where F vanishes, f(z) is e₁(z), flagged as the chart of G",
				"∀z:(num → A). «valueAt»(z, F) = M.zero ⇒ f(z) = (⊤, e₁(z))",
				By(fDef))
			gThere := a.Have(
				"where F vanishes on the curve over l, G does not, the two having no common zero",
				"∀z:(num → A). z ∈ «points»(m) ∧ «valueAt»(z, F) = M.zero ⇒ «valueAt»(z, G) ≠ M.zero",
				By(noCommonZero, overM))
			oneEvaluation := a.Have(
				"two points over l where a form H of degree r does not vanish, "+
					"at which one point of the chart of H evaluates, are equal",
				Statement{
					Binders: "∀H:((num → num) → A). ∀u v:(num → A). ∀φ ψ:(A → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, r, H)",
						"u ∈ «points»(m)",
						"v ∈ «points»(m)",
						"«valueAt»(u, H) ≠ M.zero",
						"«valueAt»(v, H) ≠ M.zero",
						"«evaluates»(φ, u, H)",
						"«evaluates»(ψ, v, H)",
						"φ = ψ",
					},
					Conclusion: "u = v",
				},
				Derive(func(b *Argument) {
					H := b.FixAs[Fun[Fun[Nat, Nat], A]]("H")
					u := b.FixAs[Fun[Nat, A]]("u")
					v := b.FixAs[Fun[Nat, A]]("v")
					b.FixAs[Fun[A, A]]("φ")
					b.FixAs[Fun[A, A]]("ψ")
					given := b.Conjuncts(
						b.Assume(),
						"H is a form of degree r",
						"u is a point over l",
						"so is v",
						"H does not vanish at u",
						"nor at v",
						"φ evaluates the chart of H at u",
						"ψ evaluates it at v",
						"and φ = ψ")
					b.Show(
						"every form of degree r·a has one ratio to H^a at u and at v",
						By(
							kSub,
							positive,
							given[0],
							GroupPremises(given[1], overM.At(u)),
							GroupPremises(given[2], overM.At(v)),
							given[3],
							given[4],
							b.Have(
								"the ratios at u and v are the values of φ = ψ at the quotients",
								Statement{
									Binders: "∀a:num. ∀P:((num → num) → A).",
									Hypotheses: []string{
										"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)",
									},
									Conclusion: "«valueAt»(u, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(u, H)), a) = " +
										"«valueAt»(v, P) * monoid_pow(M.mul, M.one, M.inv(«valueAt»(v, H)), a)",
								},
								By(given[5], given[6], given[7])),
							Read(FormRatiosDetermine, M).At(k, n, r, E, u, v, H)))
				}))
			top := a.TermAs[Bool]("⊤")
			bottom := a.TermAs[Bool]("⊥")
			injective := a.Have(
				"f is one-to-one on the points over l",
				"injective_on(«points»(m), f)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[Nat, A]]("u")
					v := b.FixAs[Fun[Nat, A]]("v")
					given := b.Conjuncts(
						b.Assume(),
						"u is a point over l",
						"so is v",
						"and f(u) = f(v)")
					b.Cases(b.TermAs[Bool]("«valueAt»(u, F) = M.zero"))
					b.When(
						"F vanishes at u",
						func(c *Argument, uZero Fact) {
							c.Cases(c.TermAs[Bool]("«valueAt»(v, F) = M.zero"))
							c.When(
								"and at v: f(u) and f(v) are the points e₁(u), e₁(v) of the chart of G, which agree",
								func(d *Argument, vZero Fact) {
									uG := d.Have(
										"G does not vanish at u",
										"«valueAt»(u, G) ≠ M.zero",
										By(given[0], uZero, gThere))
									vG := d.Have(
										"nor at v",
										"«valueAt»(v, G) ≠ M.zero",
										By(given[1], vZero, gThere))
									d.Show(
										"one point of the chart of G evaluates it at u and at v",
										By(
											gForm,
											given[0],
											given[1],
											uG,
											vG,
											gChosen.At(u),
											gChosen.At(v),
											d.Have(
												"e₁(u) = e₁(v), f(u) and f(v) being (⊤, e₁(u)) and (⊤, e₁(v))",
												"e₁(u) = e₁(v)",
												By(
													given[2],
													atSecond.At(u),
													atSecond.At(v),
													uZero,
													vZero,
													pairs.PairEq.At(top, d.TermAs[Fun[A, A]]("e₁(u)"), top, d.TermAs[Fun[A, A]]("e₁(v)")))),
											oneEvaluation.At(G, u, v, d.TermAs[Fun[A, A]]("e₁(u)"), d.TermAs[Fun[A, A]]("e₁(v)"))))
								})
							c.Otherwise(
								"but not at v: f(u) is flagged ⊤ and f(v) ⊥, which cannot be",
								func(d *Argument, vNonzero Fact) {
									d.Show(
										"the flags differ",
										By(
											given[2],
											atSecond.At(u),
											atFirst.At(v),
											uZero,
											vNonzero,
											pairs.PairEq.At(top, d.TermAs[Fun[A, A]]("e₁(u)"), bottom, d.TermAs[Fun[A, A]]("e₀(v)"))))
								})
						})
					b.Otherwise(
						"F does not vanish at u",
						func(c *Argument, uNonzero Fact) {
							c.Cases(c.TermAs[Bool]("«valueAt»(v, F) = M.zero"))
							c.When(
								"but vanishes at v: f(u) is flagged ⊥ and f(v) ⊤, which cannot be",
								func(d *Argument, vZero Fact) {
									d.Show(
										"the flags differ",
										By(
											given[2],
											atFirst.At(u),
											atSecond.At(v),
											uNonzero,
											vZero,
											pairs.PairEq.At(bottom, d.TermAs[Fun[A, A]]("e₀(u)"), top, d.TermAs[Fun[A, A]]("e₁(v)"))))
								})
							c.Otherwise(
								"nor at v: f(u) and f(v) are the points e₀(u), e₀(v) of the chart of F, which agree",
								func(d *Argument, vNonzero Fact) {
									d.Show(
										"one point of the chart of F evaluates it at u and at v",
										By(
											fForm,
											given[0],
											given[1],
											uNonzero,
											vNonzero,
											fChosen.At(u),
											fChosen.At(v),
											d.Have(
												"e₀(u) = e₀(v), f(u) and f(v) being (⊥, e₀(u)) and (⊥, e₀(v))",
												"e₀(u) = e₀(v)",
												By(
													given[2],
													atFirst.At(u),
													atFirst.At(v),
													uNonzero,
													vNonzero,
													pairs.PairEq.At(bottom, d.TermAs[Fun[A, A]]("e₀(u)"), bottom, d.TermAs[Fun[A, A]]("e₀(v)")))),
											oneEvaluation.At(F, u, v, d.TermAs[Fun[A, A]]("e₀(u)"), d.TermAs[Fun[A, A]]("e₀(v)"))))
								})
						})
				}))
			gValue := a.MemberOf[on.M](
				a.TermAs[A]("«at»(G)"),
				a.Have(
					"G(x) lies in M, evaluation at x taking the polynomials over k into K",
					"«at»(G) ∈ M.carrier",
					BySets(
						homogeneous_polynomial.FormPolynomial.Read(gForm),
						KInM,
						GroupPremises(kSub, KSub, kInK, xInK, Read(projective_curve.PointEvaluation, M).At(k, K, n, x)))))
			inverseT := a.Have(
				"1/t is F(x)/G(x), the value of the form F of degree r·1 over G(x)",
				"M.inv(«parameter») = «at»(F) * monoid_pow(M.mul, M.one, M.inv(«at»(G)), 1)",
				By(
					GroupPremises(
						kSub,
						KSub,
						kInK,
						xInK,
						fForm,
						gForm,
						projective_form_chart.ParameterInverse.Read(M).At(k, K, n, r, x, F, G)),
					comm_monoid.PowOneOn.Read(monoid).At(field.InvIn.Read(M).At(gValue))))
			atInverse := a.Have(
				"a point of the chart of G evaluating it at a point z over l takes 1/t to F(z)/G(z)",
				Statement{
					Binders: "∀φ:(A → A). ∀z:(num → A).",
					Hypotheses: []string{
						"z ∈ «points»(m)",
						"«evaluates»(φ, z, G)",
					},
					Conclusion: "φ(M.inv(«parameter»)) = «valueAt»(z, F) * M.inv(«valueAt»(z, G))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, A]]("φ")
					z := b.FixAs[Fun[Nat, A]]("z")
					given := b.Conjuncts(
						b.Assume(),
						"z is a point over l",
						"where φ evaluates the chart of G")
					zValues := b.Conjuncts(
						GroupPremises(given[0], formValues.At(z)),
						"F(z) lies in M",
						"and so does G(z)")
					b.Show(
						"its value at F(x)/G(x), F being a form of degree r·1",
						inverseT.Rw(),
						By(
							given[1],
							b.Have(
								"F is a form of degree r·1",
								"homogeneous_polynomial(«hilbertCoefficients», n, r * 1, F)",
								By(Normalized, fForm, nat_arith.MulOne.At(r))),
							zValues[1],
							field.InvIn.Read(M),
							comm_monoid.PowOneOn.Read(monoid).AsFact().At(b.TermAs[A]("M.inv(«valueAt»(z, G))"))))
				}))
			chartF := a.TermAs[Set[A]]("«chart»(F)")
			chartG := a.TermAs[Set[A]]("«chart»(G)")
			flagged := a.Have(
				"a pair flagged ⊥ is an evaluation point when its map is a point of "+
					"the first chart, one flagged ⊤ when it is one of the second killing 1/t",
				"∀B₀ B₁:set(A). ∀φ:(A → A). "+
					"    (φ ∈ "+
					"        algebra_points(restrict_ring(field_ring(M), B₀), "+
					"            restrict_ring(field_ring(M), «constants»), "+
					"            k, "+
					"            λa:A. a) ⇒ "+
					"        (⊥, φ) ∈ curve_evaluation_points(M, k, «constants», «parameter», B₀, B₁)) ∧ "+
					"    (φ ∈ "+
					"        algebra_points(restrict_ring(field_ring(M), B₁), "+
					"            restrict_ring(field_ring(M), «constants»), "+
					"            k, "+
					"            λa:A. a) ∧ "+
					"        φ(M.inv(«parameter»)) = M.zero ⇒ "+
					"        (⊤, φ) ∈ curve_evaluation_points(M, k, «constants», «parameter», B₀, B₁))",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("B₀")
					b.FixAs[Set[A]]("B₁")
					φ := b.FixAs[Fun[A, A]]("φ")
					b.Show(
						"the flag picks the disjunct of the definition",
						Unfold(curve_point_count.CurveEvaluationPointsDef),
						BySets(
							pairs.Fst.At(bottom, φ),
							pairs.Snd.At(bottom, φ),
							pairs.Fst.At(top, φ),
							pairs.Snd.At(top, φ)))
				}))
			flagRead := a.Have(
				"and the map of an evaluation point is a point of the "+
					"chart its flag names, killing 1/t when that is the second",
				Statement{
					Binders:    "∀B₀ B₁:set(A). ∀p:prod(bool, A → A).",
					Hypotheses: []string{"p ∈ curve_evaluation_points(M, k, «constants», «parameter», B₀, B₁)"},
					Conclusion: "(fst(p) ⇒ " +
						"    snd(p) ∈ " +
						"    algebra_points(restrict_ring(field_ring(M), B₁), " +
						"        restrict_ring(field_ring(M), «constants»), " +
						"        k, " +
						"        (λa:A. a)) ∧ " +
						"    snd(p, M.inv(«parameter»)) = M.zero) ∧ " +
						"(¬fst(p) ⇒ " +
						"    snd(p) ∈ " +
						"    algebra_points(restrict_ring(field_ring(M), B₀), " +
						"        restrict_ring(field_ring(M), «constants»), " +
						"        k, " +
						"        (λa:A. a)))",
				},
				BySets(curve_point_count.CurveEvaluationPointsDef))
			into := a.Have(
				"f takes the points over l into the evaluation points",
				"∀z:(num → A). z ∈ «points»(m) ⇒ f(z) ∈ «evaluationPoints»",
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]("z")
					zIn := b.Assume()
					b.Cases(b.TermAs[Bool]("«valueAt»(z, F) = M.zero"))
					b.When(
						"F vanishes at z: e₁(z) is a point of the chart of G killing 1/t",
						func(c *Argument, zero Fact) {
							gz := c.Have(
								"G does not vanish at z",
								"«valueAt»(z, G) ≠ M.zero",
								By(zIn, zero, gThere))
							chart := c.Conjuncts(
								GroupPremises(zIn, gz, gChosen.At(z)),
								"e₁(z) is a point of the chart of G",
								"evaluating it at z")
							c.Show(
								"so f(z) = (⊤, e₁(z)) is an evaluation point",
								GroupPremises(zero, atSecond.At(z)).Rw(),
								By(
									flagged.At(chartF, chartG, c.TermAs[Fun[A, A]]("e₁(z)")),
									chart[0],
									c.Have(
										"e₁(z) kills 1/t, F vanishing at z",
										"e₁(z, M.inv(«parameter»)) = M.zero",
										GroupPremises(zIn, chart[1], atInverse.At(c.TermAs[Fun[A, A]]("e₁(z)"), z)).Rw(),
										zero.Rw(),
										ByArith(M, GroupPremises(zIn, formValues.At(z)), field.InvIn.Read(M)))))
						})
					b.Otherwise(
						"F does not vanish at z: e₀(z) is a point of the chart of F",
						func(c *Argument, nonzero Fact) {
							c.Show(
								"so f(z) = (⊥, e₀(z)) is an evaluation point",
								GroupPremises(nonzero, atFirst.At(z)).Rw(),
								By(flagged.At(chartF, chartG, c.TermAs[Fun[A, A]]("e₀(z)")), zIn, nonzero, fChosen.At(z)))
						})
				}))
			onto := a.Have(
				"every evaluation point is f at a point over l",
				"∀p:prod(bool, A → A). p ∈ «evaluationPoints» ⇒ ∃z:(num → A). z ∈ «points»(m) ∧ f(z) = p",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Bool, Fun[A, A]]]("p")
					pIn := b.Assume()
					b.Cases(b.TermAs[Bool]("fst(p)"))
					b.When(
						"p is flagged as the chart of G: snd(p) is a point of it killing 1/t",
						func(c *Argument, flag Fact) {
							parts := c.Conjuncts(
								c.Have(
									"snd(p) is a point of the chart of G killing 1/t",
									"snd(p) ∈ «chartPoints»(G) ∧ snd(p, M.inv(«parameter»)) = M.zero",
									By(pIn, flag, flagRead.At(chartF, chartG, p))),
								"snd(p) is a point of the chart of G",
								"killing 1/t")
							z, zData := c.ObtainAs[Fun[Nat, A]](
								"snd(p) is the evaluation at a point z of the curve over l where G does not vanish",
								"∃z:(num → A). z ∈ «points»(m) ∧ «valueAt»(z, G) ≠ M.zero ∧ «evaluates»(snd(p), z, G)",
								By(
									kSub,
									KSub,
									lField[0],
									kInK,
									point[0],
									equations,
									gForm,
									positive,
									gNonzero,
									parts[0],
									Read(ChartPointFromMap, M).At(k, K, constants, n, r, E, x, G, c.TermAs[Fun[A, A]]("snd(p)"))))
							zParts := c.Conjuncts(
								zData,
								"z is a point of the curve over l",
								"where G does not vanish",
								"and snd(p) evaluates the chart of G there")
							zValues := c.Conjuncts(
								GroupPremises(zParts[0], formValues.At(z)),
								"F(z) lies in M",
								"and so does G(z)")
							zero := c.Have(
								"F vanishes at z: snd(p) kills 1/t, which it takes to F(z)/G(z), and G(z) is not zero",
								"«valueAt»(z, F) = M.zero",
								By(
									parts[1],
									GroupPremises(zParts[0], zParts[2], atInverse.At(c.TermAs[Fun[A, A]]("snd(p)"), z)),
									zParts[1],
									zValues[0],
									zValues[1],
									field.InvIn.Read(M),
									field.InvEqZeroOn.Read(M).AsFact().At(c.TermAs[A]("«valueAt»(z, G)")),
									field.MulEqZeroOn.Read(M).AsFact().At(
										c.TermAs[A]("«valueAt»(z, F)"), c.TermAs[A]("M.inv(«valueAt»(z, G))"))))
							chosenAt := c.Conjuncts(
								GroupPremises(zParts[0], zParts[1], gChosen.At(z)),
								"e₁(z) is a point of the chart of G",
								"evaluating it at z")
							same := c.Have(
								"e₁(z) = snd(p), two points of the chart of G evaluating it at z",
								"e₁(z) = snd(p)",
								By(
									kSub,
									KSub,
									kInK,
									xInK,
									gForm,
									gNonzero,
									chosenAt[0],
									parts[0],
									c.Have(
										"they agree on the quotients, both taking P(x)/G(x)^a to P(z)/G(z)^a",
										Statement{
											Binders: "∀a:num. ∀P:((num → num) → A).",
											Hypotheses: []string{
												"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)",
											},
											Conclusion: "e₁(z, «at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(G)), a)) = " +
												"snd(p, «at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(G)), a))",
										},
										By(chosenAt[1], zParts[2])),
									Read(ChartPointsDetermined, M).At(
										k, K, constants, n, r, x, G, c.TermAs[Fun[A, A]]("e₁(z)"), c.TermAs[Fun[A, A]]("snd(p)"))))
							c.Show(
								"so f(z) = (⊤, e₁(z)) is p",
								Witness(z),
								By(zParts[0], atSecond.At(z), zero, flag, same, pairs.PairEta.At(p)))
						})
					b.Otherwise(
						"p is flagged as the chart of F: snd(p) is a point of it",
						func(c *Argument, flag Fact) {
							chartPoint := c.Have(
								"snd(p) is a point of the chart of F",
								"snd(p) ∈ «chartPoints»(F)",
								By(pIn, flag, flagRead.At(chartF, chartG, p)))
							z, zData := c.ObtainAs[Fun[Nat, A]](
								"snd(p) is the evaluation at a point z of the curve over l where F does not vanish",
								"∃z:(num → A). z ∈ «points»(m) ∧ «valueAt»(z, F) ≠ M.zero ∧ «evaluates»(snd(p), z, F)",
								By(
									kSub,
									KSub,
									lField[0],
									kInK,
									point[0],
									equations,
									fForm,
									positive,
									fNonzero,
									chartPoint,
									Read(ChartPointFromMap, M).At(k, K, constants, n, r, E, x, F, c.TermAs[Fun[A, A]]("snd(p)"))))
							zParts := c.Conjuncts(
								zData,
								"z is a point of the curve over l",
								"where F does not vanish",
								"and snd(p) evaluates the chart of F there")
							chosenAt := c.Conjuncts(
								GroupPremises(zParts[0], zParts[1], fChosen.At(z)),
								"e₀(z) is a point of the chart of F",
								"evaluating it at z")
							same := c.Have(
								"e₀(z) = snd(p), two points of the chart of F evaluating it at z",
								"e₀(z) = snd(p)",
								By(
									kSub,
									KSub,
									kInK,
									xInK,
									fForm,
									fNonzero,
									chosenAt[0],
									chartPoint,
									c.Have(
										"they agree on the quotients, both taking P(x)/F(x)^a to P(z)/F(z)^a",
										Statement{
											Binders: "∀a:num. ∀P:((num → num) → A).",
											Hypotheses: []string{
												"homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)",
											},
											Conclusion: "e₀(z, «at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(F)), a)) = " +
												"snd(p, «at»(P) * monoid_pow(M.mul, M.one, M.inv(«at»(F)), a))",
										},
										By(chosenAt[1], zParts[2])),
									Read(ChartPointsDetermined, M).At(
										k, K, constants, n, r, x, F, c.TermAs[Fun[A, A]]("e₀(z)"), c.TermAs[Fun[A, A]]("snd(p)"))))
							c.Show(
								"so f(z) = (⊥, e₀(z)) is p",
								Witness(z),
								By(zParts[0], atFirst.At(z), zParts[1], flag, same, pairs.PairEta.At(p)))
						})
				}))
			a.Show(
				"f is one-to-one, and its image is the evaluation points",
				Witness(f),
				By(
					injective,
					a.Have(
						"the image of f lies among the evaluation points",
						"image(f, «points»(m)) ⊆ «evaluationPoints»",
						By(into, set_image.ImageSubsetIff.At(f, points, evaluationPoints))),
					a.Have(
						"and holds every one of them",
						"«evaluationPoints» ⊆ image(f, «points»(m))",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(b *Argument) {
							p := b.FixAs[Prod[Bool, Fun[A, A]]]("p")
							_, source := b.UnpackAs[Fun[Nat, A]](GroupPremises(b.Assume(), onto.At(p)), "z")
							b.Show(
								"p is f at a point z over l",
								By(source, set_basic.InImage.At(f, points, p)))
						})),
					set_order.SubsetAntisym.At(
						a.TermAs[Set[Prod[Bool, Fun[A, A]]]]("image(f, «points»(m))"), evaluationPoints)))
		}),
})}
