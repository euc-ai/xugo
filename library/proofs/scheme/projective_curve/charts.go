// charts.go — the chart of a form: evaluation at a point is a ring map, the
// quotients of forms over powers of F(x) lie in the chart, and the chart is a
// subring of M holding k.

package projective_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartSubring — the values P(x)/F(x)^a of the forms P of degree r·a, for F
// a form of degree r over k, are a subring of M holding k: a constant c is
// c·F(x)^0, P(x)/F(x)^a + Q(x)/F(x)^b is (P·F^b + Q·F^a)(x)/F(x)^(a+b), the
// product is (P·Q)(x)/F(x)^(a+b) (FormNumerators), and the negative is
// (−P)(x)/F(x)^a, each numerator a form of the matching degree.
var ChartSubring = chartSubringThm{family.Add(registry.ProofEntry{
	Name: "ChartSubring",
	Key:  "prop_23a173bc3f5ac908",
	Reading: "The chart is cut out of K, a subfield, so its members lie in M; no hypothesis " +
		"asks F(x) ≠ zero, and at F(x) = zero the chart is all of K, a subring holding k too.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
		},
		Conclusion: "subring(field_ring(M), «chart»(F)) ∧ k ⊆ «chart»(F)",
		Abbrev: Abbrev{
			{Name: "power", Text: "λb:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        F, " +
				"        b)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, form Fact,
		) {
			ring := field.RingOn.Read(M)
			fieldOps := a.TermAs[FieldOps[A]]("M")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			evaluation := a.Have(
				"evaluation at x is a ring map from the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
				By(kSub, coordinates, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, x)))
			coefficientRing := ring_homomorphism.Source.Read(inclusion)
			kInM := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(kSub, field.SubfieldSubset))
			KInM := a.Have(
				"and so does K",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			valueF := a.Have(
				"F(x) lies in M",
				"«at»(F) ∈ M.carrier",
				By(homogeneous_polynomial.FormPolynomial.Read(form), ring_homomorphism.MapIn.Read(evaluation)))
			constants := a.Have(
				"a constant c of k is c·F(x)^0, the value of the constant form c of degree r·0",
				"∀c:A. c ∈ k ⇒ c ∈ «chart»(F)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					constant := b.Have(
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
							"it evaluates to c, which lies in M",
							"«at»(polynomial_algebra_const(«hilbertCoefficients», c)) = c ∧ c ∈ M.carrier",
							BySets(
								cIn,
								inclusion,
								kInM,
								At(
									polynomial_algebra_evaluation.PolynomialAlgebraEvalConst,
									coefficients,
									a.TermAs[RingOps[A]]("field_ring(M)"),
									identity,
									x,
									c))),
						"the constant evaluates to c",
						"c lies in M")
					value := b.Have(
						"so c·F(x)^0 = c is its value",
						"c * monoid_pow(M.mul, M.one, «at»(F), 0) = "+
							"«at»(polynomial_algebra_const(«hilbertCoefficients», c))",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						evaluated[0].Rw(),
						ByArith(M, evaluated[1]))
					b.Show(
						"c lies in K, k lying in K",
						BySets(cIn, kInK, constant, value))
				}))
			closed := a.Have(
				"the sum and the product of two members of the chart lie in it",
				"∀y z:A. y ∈ «chart»(F) ∧ z ∈ «chart»(F) ⇒ y + z ∈ «chart»(F) ∧ y * z ∈ «chart»(F)",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					b.FixAs[A]("z")
					members := b.Conjuncts(
						b.Assume(),
						"y lies in the chart",
						"so does z")
					yParts := b.Conjuncts(
						members[0],
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					zParts := b.Conjuncts(
						members[1],
						"z lies in K",
						"z·F(x)^b is the value of a form of degree r·b")
					ya, P, yForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yParts[1], "a", "P")
					zb, Q, zForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](zParts[1], "b", "Q")
					yData := b.Conjuncts(
						yForm,
						"P is a form of degree r·a",
						"y·F(x)^a = P(x)")
					zData := b.Conjuncts(
						zForm,
						"Q is a form of degree r·b",
						"z·F(x)^b = Q(x)")
					inM := b.Have(
						"y and z lie in M",
						"y ∈ M.carrier ∧ z ∈ M.carrier",
						BySets(yParts[0], zParts[0], KInM))
					numerators := b.Conjuncts(
						GroupPremises(
							kSub,
							coordinates,
							form,
							yData[0],
							zData[0],
							homogeneous_polynomial.FormNumerators.Read(M).At(k, n, r, ya, zb, x, F, P, Q)),
						"P·F^b + Q·F^a is a form of degree r·(a + b)",
						"and so is P·Q",
						"the value of P·F^b + Q·F^a is P(x)·F(x)^b + Q(x)·F(x)^a",
						"and that of P·Q is P(x)·Q(x)")
					split := GroupPremises(
						valueF,
						comm_monoid.PowAddOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(
							b.TermAs[A]("«at»(F)"), ya, zb))
					valuesIn := b.Have(
						"P(x), Q(x) and the powers of F(x) lie in M",
						"«at»(P) ∈ M.carrier ∧ "+
							"«at»(Q) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(F), a) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(F), b) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(F), a + b) ∈ M.carrier",
						By(
							homogeneous_polynomial.FormPolynomial.Read(yData[0]),
							homogeneous_polynomial.FormPolynomial.Read(zData[0]),
							valueF,
							ring_homomorphism.MapIn.Read(evaluation),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
					sum := b.Have(
						"so (y + z)·F(x)^(a+b) is the value of P·F^b + Q·F^a",
						"(y + z) * monoid_pow(M.mul, M.one, «at»(F), a + b) = "+
							"«at»(fun_add(polynomial_algebra_mul(«hilbertCoefficients», P, «power»(b)), "+
							"        polynomial_algebra_mul(«hilbertCoefficients», Q, «power»(a))))",
						numerators[2].Rw(),
						yData[1].RwRev(),
						zData[1].RwRev(),
						split.Rw(),
						ByArith(M, inM, valuesIn))
					product := b.Have(
						"and y·z·F(x)^(a+b) is the value of P·Q",
						"(y * z) * monoid_pow(M.mul, M.one, «at»(F), a + b) = "+
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», P, Q))",
						numerators[3].Rw(),
						yData[1].RwRev(),
						zData[1].RwRev(),
						split.Rw(),
						ByArith(M, inM, valuesIn))
					b.Show(
						"y + z and y·z lie in K, a subfield, with those forms",
						BySets(
							yParts[0],
							zParts[0],
							KSub,
							field.SubfieldAdd.At(fieldOps, K, b.TermAs[A]("y"), b.TermAs[A]("z")),
							field.SubfieldMul.At(fieldOps, K, b.TermAs[A]("y"), b.TermAs[A]("z")),
							numerators[0],
							sum,
							numerators[1],
							product))
				}))
			negated := a.Have(
				"the negative of a member of the chart lies in it",
				"∀y:A. y ∈ «chart»(F) ⇒ -y ∈ «chart»(F)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yParts := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					_, P, yForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yParts[1], "a", "P")
					yData := b.Conjuncts(
						yForm,
						"P is a form of degree r·a",
						"y·F(x)^a = P(x)")
					negForm := b.Have(
						"−P is a form of degree r·a",
						"homogeneous_polynomial(«hilbertCoefficients», n, r * a, fun_neg(«hilbertCoefficients».neg, P))",
						By(
							coefficientRing,
							yData[0],
							At(homogeneous_polynomial.FormNeg, coefficients, n, b.TermAs[Nat]("r * a"), P)))
					pPolynomial := homogeneous_polynomial.FormPolynomial.Read(yData[0])
					negValue := b.Have(
						"whose value is −P(x)",
						"«at»(fun_neg(«hilbertCoefficients».neg, P)) = -«at»(P)",
						By(
							pPolynomial,
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.MapNeg.Read(evaluation).AsFact().At(P)))
					inM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(yParts[0], KInM))
					valuesIn := b.Have(
						"P(x) and F(x)^a lie in M",
						"«at»(P) ∈ M.carrier ∧ monoid_pow(M.mul, M.one, «at»(F), a) ∈ M.carrier",
						By(
							pPolynomial,
							valueF,
							ring_homomorphism.MapIn.Read(evaluation),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
					value := b.Have(
						"so (−y)·F(x)^a is the value of −P",
						"-y * monoid_pow(M.mul, M.one, «at»(F), a) = «at»(fun_neg(«hilbertCoefficients».neg, P))",
						negValue.Rw(),
						yData[1].RwRev(),
						ByArith(M, inM, valuesIn))
					b.Show(
						"−y lies in K, a subfield, with that form",
						BySets(yParts[0], field.SubfieldNeg.At(fieldOps, K, y), KSub, negForm, value))
				}))
			inside := a.Have(
				"the chart lies in K, inside M",
				"«chart»(F) ⊆ M.carrier",
				BySets(KInM))
			holdsK := a.Have(
				"it holds k",
				"k ⊆ «chart»(F)",
				BySets(constants))
			units := a.Have(
				"so it holds zero and one, which k holds",
				"M.zero ∈ «chart»(F) ∧ M.one ∈ «chart»(F)",
				By(kSub, holdsK, field.SubfieldZero, field.SubfieldOne, set_basic.SubsetDef))
			a.Show(
				"a subset of M holding zero and one and closed under the operations, holding k",
				Simp(Fwd(comm_ring.SubringDef)),
				By(inside, units, closed, negated, holdsK))
		}),
})}

// ProjectiveEquationPointsMono — a point of the curve over K is a point over
// any L containing K: its coordinates up to n lie in K, so in L, and the
// other conditions do not read the set of values.
var ProjectiveEquationPointsMono = projectiveEquationPointsMonoThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveEquationPointsMono",
	Key:  "prop_691d02fe58b97be6",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀k K L:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{"K ⊆ L"},
		Conclusion: "projective_equation_points(R, k, K, n, E) ⊆ projective_equation_points(R, k, L, n, E)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, K, L *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			within Fact,
		) {
			a.Show(
				"the coordinates up to n, lying in K, lie in L",
				Simp(Fwd(ProjectiveEquationPointsDef)),
				BySets(within))
		}),
})}

// PointEvaluation — evaluation at a point x with coordinates in a subfield K
// holding k is a ring map from the polynomials over k into M with values in
// K: the inclusion of k is a ring map, and a polynomial's value is built
// from coefficients in k and coordinates in K by the operations of K.
var PointEvaluation = pointEvaluationThm{family.Add(registry.ProofEntry{
	Name: "PointEvaluation",
	Key:  "prop_7f259c35bf30d47d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n:num. ∀x:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
		},
		Conclusion: "ring_homomorphism(«polynomials», " +
			"    field_ring(M), " +
			"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x)) ∧ " +
			"(∀P:((num → num) → A). P ∈ «polynomials».carrier ⇒ «at»(P) ∈ K)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n *Expr[Nat],
			x *Arrow[Nat, A],
			kSub, KSub, kInK, coordinates Fact,
		) {
			ring := field.RingOn.Read(M)
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			inM := a.Have(
				"so the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			evaluation := GroupPremises(
				kSub, inM, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, x))
			values := a.Have(
				"and its values lie in K, a subring holding k and the coordinates",
				"∀P:((num → num) → A). P ∈ «polynomials».carrier ⇒ «at»(P) ∈ K",
				Derive(func(b *Argument) {
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					b.Show(
						"evaluation lands in the subring K",
						By(
							b.Assume(),
							inclusion,
							kInK,
							coordinates,
							polynomial_algebra.PolynomialAlgebraRingDef,
							field.SubfieldSubring.Read(M).AsFact().At(K),
							KSub,
							set_basic.SubsetDef,
							At(
								polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring,
								b.TermAs[RingOps[A]]("«hilbertCoefficients»"),
								fieldRing,
								identity,
								x,
								b.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
								K,
								P)))
				}))
			a.Show(
				"both",
				By(evaluation, values))
		}),
})}

// ChartQuotient — the value of a form G of degree r·b over F(x)^b lies in
// the chart of F: it lies in K, and times F(x)^b it is G(x).
var ChartQuotient = chartQuotientThm{family.Add(registry.ProofEntry{
	Name: "ChartQuotient",
	Key:  "prop_a3198eb4cee4e788",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r b:num. ∀x:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"«at»(F) ≠ M.zero",
			"homogeneous_polynomial(«hilbertCoefficients», n, r * b, G)",
		},
		Conclusion: "«at»(G) * monoid_pow(M.mul, M.one, M.inv(«at»(F)), b) ∈ «chart»(F)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r, b *Expr[Nat],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, fForm, nonzero, gForm Fact,
		) {
			evaluation := a.Conjuncts(
				GroupPremises(kSub, KSub, kInK, coordinates, Read(PointEvaluation, M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			values := a.Have(
				"F(x) and G(x) lie in K",
				"«at»(F) ∈ K ∧ «at»(G) ∈ K",
				By(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm),
					evaluation[1]))
			parts := a.Conjuncts(
				values,
				"F(x) lies in K",
				"and so does G(x)")
			fieldOps := a.TermAs[FieldOps[A]]("M")
			inverse := field.SubfieldInv.At(fieldOps, K, a.TermAs[A]("«at»(F)"))
			power := field.SubfieldPowerIn.Read(M).AsFact().At(K, a.TermAs[A]("M.inv(«at»(F))"), b)
			quotientInK := a.Have(
				"G(x)·F(x)^(−b) lies in K, a subfield",
				"«at»(G) * monoid_pow(M.mul, M.one, M.inv(«at»(F)), b) ∈ K",
				By(
					KSub,
					parts[0],
					parts[1],
					inverse,
					power,
					field.SubfieldMul.At(
						fieldOps, K, a.TermAs[A]("«at»(G)"), a.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«at»(F)), b)"))))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			inM := a.Have(
				"F(x), its inverse and G(x) lie in M",
				"«at»(F) ∈ M.carrier ∧ M.inv(«at»(F)) ∈ M.carrier ∧ «at»(G) ∈ M.carrier",
				BySets(parts[0], parts[1], KInM, field.InvIn.Read(M)))
			members := a.Conjuncts(
				inM,
				"F(x) lies in M",
				"its inverse lies in M",
				"G(x) lies in M")
			cancel := a.Have(
				"F(x)^(−1)·F(x) = 1, F(x) being nonzero",
				"M.inv(«at»(F)) * «at»(F) = M.one",
				By(nonzero, members[0], field.MulLeftInverseOn.Read(M)))
			powers := a.Have(
				"so F(x)^(−b)·F(x)^b = 1",
				"monoid_pow(M.mul, M.one, M.inv(«at»(F)), b) * monoid_pow(M.mul, M.one, «at»(F), b) = M.one",
				By(
					cancel,
					members[0],
					members[1],
					comm_monoid.PowInverseOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M)))))
			value := a.Have(
				"times F(x)^b the quotient is G(x)",
				"«at»(G) * monoid_pow(M.mul, M.one, M.inv(«at»(F)), b) * monoid_pow(M.mul, M.one, «at»(F), b) = "+
					"«at»(G)",
				ByArith(
					M,
					members[0],
					members[1],
					members[2],
					Scaled(a.TermAs[A]("«at»(G)"), powers),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))).AsFact().At(
						a.TermAs[A]("M.inv(«at»(F))"), b),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))).AsFact().At(
						a.TermAs[A]("«at»(F)"), b)))
			a.Show(
				"so it lies in the chart, G having degree r·b",
				BySets(quotientInK, gForm, value))
		}),
})}
