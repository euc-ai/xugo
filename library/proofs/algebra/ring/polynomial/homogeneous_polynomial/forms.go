// forms.go — the forms of one degree over a ring and over k: a form of
// degree d in the variables up to n is a polynomial of degree at most d in
// the variables below n + 1, a monomial times a coefficient is a form of the
// monomial's degree, the constants are forms of degree zero, sums and
// negatives of forms of one degree are forms of that degree, the product of
// forms of degrees d and e is a form of degree d + e, and a power of a form
// of degree d is one of degree d times the exponent.
// A form's coefficients carried along a ring homomorphism make a form of the
// same degree. The part of degree s of a polynomial, its coefficients at the monomials of
// degree s, is a form of degree s, and multiplying by a form of degree e
// moves the parts up by e, leaving none below e. A form of degree d,
// evaluated where every value is scaled by c, scales by c to the d-th power,
// so a form vanishing at a point vanishes at its multiples, and a ratio P/H^a
// of forms does not change with the point's scale. Evaluating the polynomials
// over k at a point of M is a ring homomorphism into M. The numerators of the
// sum and the product of P/H^c and Q/H^d are forms of degree r·(c + d), and
// X_i·X_j^(r−1) is a form of degree r, each with its value at a point. The
// partials of a form of degree d are forms of degree d − 1, and Euler's
// identity Σ xᵢ·∂ᵢP(x) = d·P(x) holds over any commutative ring. The gradient
// at a point of M of a polynomial over k is a coordinate vector; that of a
// form of degree d scales by c^(d − 1) with the point, at a zero b of the
// form it lies in the kernel of v ↦ Σᵢ b(i)·v(i), and that of X_j − 1 is the
// coordinate vector of j.

package homogeneous_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FormBound — a form of degree d in the variables up to n is a polynomial of degree at most d in
// the n + 1 variables below n + 1: it is a polynomial in the variables up to n, and every monomial
// where it is nonzero has degree d (PolynomialBoundUpTo).
var FormBound = formBoundThm{family.Add(registry.ProofEntry{
	Name: "FormBound",
	Key:  "prop_564082b097b75cab",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"homogeneous_polynomial(R, n, d, p)",
		},
		Conclusion: "polynomial_bound(R, n + 1, d, p)",
	},
		func(a *Argument, R *Expr[RingOps[A]], n, d *Expr[Nat], p *Arrow[Fun[Nat, Nat], A], form Fact) {
			degree := a.Have(
				"every monomial where p is not zero has degree d, so at most d",
				"∀m:(num → num). p(m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) ≤ d",
				ByArith(FormDegree.Read(form)))
			a.Show(
				"and p is a polynomial in the variables up to n, so "+
					"it has degree at most d in the variables below n + 1",
				By(FormPolynomial.Read(form), degree, PolynomialBoundUpTo.At(R, n, d, p)))
		}),
})}

// FormMonomial — a coefficient c at one monomial m of the variables up to n
// is a form whose degree is the sum of the exponents of m: it is a
// polynomial, nonzero at most at m, and m is its only monomial.
var FormMonomial = formMonomialThm{family.Add(registry.ProofEntry{
	Name: "FormMonomial",
	Key:  "prop_b6729a565067b65d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀c:A. ∀m:(num → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c ∈ R.carrier",
			"m ∈ monomials({i:num | i ≤ n})",
		},
		Conclusion: "homogeneous_polynomial(R, n, sum({i:num | i ≤ n}, m), delta_at(R.zero, c, m))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n *Expr[Nat],
			c *Expr[A],
			m *Expr[Fun[Nat, Nat]],
			ring, cIn, monomial Fact,
		) {
			monomials := a.TermAs[Set[Fun[Nat, Nat]]]("monomials({i:num | i ≤ n})")
			isPolynomial := a.Have(
				"the polynomials in the variables up to n are the free module on "+
					"their monomials, which holds the coefficient c at the monomial m",
				"delta_at(R.zero, c, m) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				Unfold(polynomial_algebra.PolynomialAlgebraDef),
				By(cIn, monomial, free_module.DeltaAtCoefficientIn.Read(ring).AsFact().At(monomials, c, m)))
			degree := a.Have(
				"its one monomial is m, of the degree of m",
				Statement{
					Binders: "∀u:(num → num).",
					Hypotheses: []string{
						"delta_at(R.zero, c, m, u) ≠ R.zero",
					},
					Conclusion: "sum({i:num | i ≤ n}, u) = sum({i:num | i ≤ n}, m)",
				},
				Simp(Fwd(free_module.DeltaAtDef)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Nat]]("u")
					b.Show(
						"a coefficient that is not zero sits at m",
						By(b.Assume()))
				}))
			a.Show(
				"a polynomial whose monomials all have the degree of m",
				Unfold(HomogeneousPolynomialDef),
				By(isPolynomial, degree))
		}),
})}

// FormConstant — a constant of the carrier is a form of degree zero: it is
// the coefficient at the monomial of the constants, whose exponents sum to
// zero.
var FormConstant = formConstantThm{family.Add(registry.ProofEntry{
	Name: "FormConstant",
	Key:  "prop_8d4da69dd7d1efdf",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀c:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c ∈ R.carrier",
		},
		Conclusion: "homogeneous_polynomial(R, n, 0, polynomial_algebra_const(R, c))",
	},
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], c *Expr[A], ring, cIn Fact) {
			constants := a.TermAs[Fun[Nat, Nat]]("λy:num. 0")
			monomial := a.Have(
				"the exponent zero at every variable is a monomial of the variables up to n",
				"(λy:num. 0) ∈ monomials({i:num | i ≤ n})",
				Simp(Fwd(polynomial_algebra.MonomialsMember)),
				Unfold(functions.FunSupportDef),
				BySets(finite_set.FiniteRules))
			degree := a.Have(
				"and its exponents sum to zero",
				"sum({i:num | i ≤ n}, λy:num. 0) = 0",
				By(
					nat_sum.EqZero.At(a.TermAs[Set[Nat]]("{i:num | i ≤ n}"), constants),
					num_segment.FiniteBelow.At(n)))
			a.Show(
				"a constant is the coefficient at that monomial",
				Simp(Fwd(polynomial_algebra.PolynomialAlgebraConstDef)),
				By(ring, cIn, monomial, degree, At(FormMonomial, R, n, c, constants)))
		}),
})}

// FormVariable — the variable i, for i up to n, is a form of degree one:
// it is the coefficient one at the monomial of i, whose exponents sum to one
// (VariableMonomialDegree).
var FormVariable = formVariableThm{family.Add(registry.ProofEntry{
	Name: "FormVariable",
	Key:  "prop_3961e00006728157",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n i:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"i ≤ n",
		},
		Conclusion: "homogeneous_polynomial(R, n, 1, polynomial_algebra_var(R, i))",
	},
		func(a *Argument, R *Expr[RingOps[A]], n, i *Expr[Nat], ring, inRange Fact) {
			exponent := a.TermAs[Fun[Nat, Nat]]("monomial_var(i)")
			oneNonzero := a.Have(
				"one is not zero",
				"1 ≠ 0",
				ByArith())
			support := a.Have(
				"the exponent one at i and zero elsewhere is nonzero at i alone",
				"fun_support(0, λy:num. monomial_var(i, y)) = {i}",
				Simp(Fwd(polynomial_algebra.MonomialVarDef), Fwd(free_module.DeltaAtDef)),
				BySets(oneNonzero))
			finite := a.Have(
				"so it is finitely supported",
				"finite_support(0, monomial_var(i))",
				Unfold(function_module.FiniteSupportDef),
				support.Rw(),
				By(finite_set.FiniteSing.At(i)))
			monomial := a.Have(
				"a monomial of the variables up to n, i being one of them",
				"monomial_var(i) ∈ monomials({j:num | j ≤ n})",
				Unfold(polynomial_algebra.MonomialsDef),
				BySets(finite, support, inRange))
			a.Show(
				"the variable is the coefficient one at that monomial, of degree one",
				Simp(Fwd(polynomial_algebra.PolynomialAlgebraVarDef)),
				By(
					ring,
					monomial,
					inRange,
					VariableMonomialDegree.At(n, i),
					comm_ring.OneIn.Read(ring),
					At(FormMonomial, R, n, a.TermAs[A]("R.one"), exponent)))
		}),
})}

// FormSum — the sum of two forms of degree d is a form of degree d: it is a
// polynomial, and where it is nonzero one of the two summands is, a sum of
// zeros being zero.
var FormSum = formSumThm{family.Add(registry.ProofEntry{
	Name: "FormSum",
	Key:  "prop_bc864ad94aab84b2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num. ∀P Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, d, P)",
			"homogeneous_polynomial(R, n, d, Q)",
		},
		Conclusion: "homogeneous_polynomial(R, n, d, fun_add(P, Q))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d *Expr[Nat],
			P, Q *Arrow[Fun[Nat, Nat], A],
			ring, pForm, qForm Fact,
		) {
			polynomials := a.Have(
				"the polynomials in the variables up to n are a ring",
				"comm_ring_on(polynomial_algebra_ring(R, {i:num | i ≤ n}))",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
			isPolynomial := a.Have(
				"so the sum is a polynomial",
				"fun_add(P, Q) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				By(FormPolynomial.Read(pForm), FormPolynomial.Read(qForm), comm_ring.AddIn.Read(polynomials)))
			degree := a.Have(
				"where the sum is nonzero one summand is, and both have degree d there",
				"∀m:(num → num). fun_add(P, Q, m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) = d",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					b.Show(
						"zero plus zero is zero",
						By(
							b.Assume(),
							FormDegree.Read(pForm).At(m),
							FormDegree.Read(qForm).At(m),
							function_module.FunAddDef.At(b.TermAs[Op[A]]("R.add"), P, Q, m),
							comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								b.TermAs[A]("R.zero")),
							comm_ring.ZeroIn.Read(ring)))
				}))
			a.Show(
				"a polynomial whose monomials have degree d",
				Unfold(HomogeneousPolynomialDef),
				By(isPolynomial, degree))
		}),
})}

// FormNeg — the negative of a form of degree d is a form of degree d: it is
// a polynomial, nonzero exactly where the form is, the negative of zero
// being zero.
var FormNeg = formNegThm{family.Add(registry.ProofEntry{
	Name: "FormNeg",
	Key:  "prop_861e4410a2d55b09",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num. ∀P:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, d, P)",
		},
		Conclusion: "homogeneous_polynomial(R, n, d, fun_neg(P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			ring, form Fact,
		) {
			polynomials := a.Have(
				"the polynomials in the variables up to n are a ring",
				"comm_ring_on(polynomial_algebra_ring(R, {i:num | i ≤ n}))",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
			isPolynomial := a.Have(
				"so the negative is a polynomial",
				"fun_neg(P) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				By(FormPolynomial.Read(form), comm_ring.NegIn.Read(polynomials)))
			degree := a.Have(
				"where the negative is nonzero so is P, of degree d there",
				"∀m:(num → num). fun_neg(P, m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) = d",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					b.Show(
						"the negative of zero is zero",
						By(
							b.Assume(),
							FormDegree.Read(form).At(m),
							function_module.FunNegDef.At(b.TermAs[Fun[A, A]]("R.neg"), P, m),
							group.InvOneOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring)))))
				}))
			a.Show(
				"a polynomial whose monomials have degree d",
				Unfold(HomogeneousPolynomialDef),
				By(isPolynomial, degree))
		}),
})}

// FormProduct — the product of a form of degree d and one of degree e is a
// form of degree d + e: it is a polynomial, and a monomial m where it is
// nonzero splits as m₁ + (m − m₁) with P nonzero at m₁ and Q at m − m₁, so
// its degree is d + e.
var FormProduct = formProductThm{family.Add(registry.ProofEntry{
	Name: "FormProduct",
	Key:  "prop_29b679cda06bffbe",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d e:num. ∀P Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, d, P)",
			"homogeneous_polynomial(R, n, e, Q)",
		},
		Conclusion: "homogeneous_polynomial(R, n, d + e, polynomial_algebra_mul(R, P, Q))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, e *Expr[Nat],
			P, Q *Arrow[Fun[Nat, Nat], A],
			ring, pForm, qForm Fact,
		) {
			pPolynomial, qPolynomial := FormPolynomial.Read(pForm), FormPolynomial.Read(qForm)
			isPolynomial := a.Have(
				"the product is a polynomial in the variables up to n",
				"polynomial_algebra_mul(R, P, Q) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				By(ring, pPolynomial, qPolynomial, polynomial_algebra.PolynomialAlgebraMulIn))
			pCoefficients := a.Conjuncts(
				a.Simplified(pPolynomial.AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"P is nonzero at finitely many monomials",
				"every monomial where P is nonzero is a monomial of the variables up to n",
				"every coefficient of P lies in the carrier")
			qCoefficients := a.Conjuncts(
				a.Simplified(qPolynomial.AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"Q is nonzero at finitely many monomials",
				"every monomial where Q is nonzero is a monomial of the variables up to n",
				"every coefficient of Q lies in the carrier")
			degree := a.Have(
				"a monomial where the product is nonzero splits into one of degree d and one of degree e",
				"∀m:(num → num). polynomial_algebra_mul(R, P, Q, m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) = d + e",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					nonzero := b.Assume()
					split := b.Conjuncts(
						GroupPremises(
							ring,
							pCoefficients[2],
							qCoefficients[2],
							nonzero,
							At(polynomial_algebra.PolynomialAlgebraMulSupport, R, P, Q, m)),
						"m is finitely supported",
						"some m₁ below m has P(m₁) and Q(m − m₁) nonzero")
					m1, term := b.UnpackAs[Fun[Nat, Nat]](split[1], "m₁")
					pieces := b.Conjuncts(
						term,
						"m₁ lies below m",
						"P is nonzero at m₁",
						"Q is nonzero at m − m₁")
					rest := b.TermAs[Fun[Nat, Nat]]("λy:num. m(y) - m₁(y)")
					exponents := b.Have(
						"exponent by exponent, m is m₁ plus m − m₁",
						"(λy:num. m₁(y) + (m(y) - m₁(y))) = m",
						Funext(),
						ByArith(pieces[0]))
					b.Show(
						"so the degree of m is that of m₁ plus that of m − m₁",
						By(
							pieces[1],
							pieces[2],
							FormDegree.Read(pForm).At(m1),
							FormDegree.Read(qForm).At(rest),
							exponents,
							nat_sum.Add.At(m1, rest, b.TermAs[Set[Nat]]("{i:num | i ≤ n}")),
							num_segment.FiniteBelow.At(n)))
				}))
			a.Show(
				"a polynomial whose monomials have degree d + e",
				Unfold(HomogeneousPolynomialDef),
				By(isPolynomial, degree))
		}),
})}

// FormPower — the j-th power of a form of degree d is a form of degree d·j:
// the zeroth power is the one polynomial, a constant, and each further power
// multiplies by the form, adding d to the degree.
var FormPower = formPowerThm{family.Add(registry.ProofEntry{
	Name: "FormPower",
	Key:  "prop_eb9dbfda842a96fa",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num. ∀P:((num → num) → A). ∀j:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, d, P)",
		},
		Conclusion: "homogeneous_polynomial(R, " +
			"    n, " +
			"    d * j, " +
			"    monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), P, j))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			ring, form Fact,
		) {
			a.Induct("j")
			a.Base(
				"the zeroth power is the one polynomial, the constant one, of degree zero",
				func(b *Argument) {
					one := b.Simplified(
						GroupPremises(ring, comm_ring.OneIn.Read(ring), At(FormConstant, R, n, b.TermAs[A]("R.one"))),
						Fwd(polynomial_algebra.PolynomialAlgebraConstDef))
					b.Show(
						"the one polynomial is the constant one",
						Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(polynomial_algebra.PolynomialAlgebraOneDef)),
						By(Normalized, one, nat_arith.MulZero.At(d)))
				})
			a.Step(
				"one more factor P adds d to the degree",
				func(b *Argument, power Fact) {
					b.Show(
						"P times a form of degree d·j has degree d + d·j",
						Simp(Fwd(nat_arith.MulSuc), Fwd(comm_monoid.MonoidPowDef)),
						By(ring, form, power, FormProduct))
				})
		}),
})}

// CarriedForm — carrying the coefficients of a form of degree d along a ring
// homomorphism φ gives a form of degree d: φ keeps zero, so the carried
// polynomial is supported where the form is, and its coefficients φ(P(m)) lie
// in T; where it is nonzero so is the form, of degree d there.
var CarriedForm = carriedFormThm{family.Add(registry.ProofEntry{
	Name: "CarriedForm",
	Key:  "prop_67082bed09024493",
	Reading: "φ need not be one to one: a coefficient it sends to zero drops out " +
		"of the carried polynomial, which is still of degree d, the zero polynomial " +
		"being a form of every degree. Neither ring needs to be commutative.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀φ:(A → B). ∀n d:num. ∀P:((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
			"homogeneous_polynomial(R, n, d, P)",
		},
		Conclusion: "homogeneous_polynomial(T, n, d, λm:(num → num). φ(P(m)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			form Fact,
		) {
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			carried := a.TermAs[Fun[Fun[Nat, Nat], B]]("λm:(num → num). φ(P(m))")
			support := a.Have(
				"φ keeps zero, so the carried polynomial is supported where P is",
				"fun_support(T.zero, λm:(num → num). φ(P(m))) ⊆ fun_support(R.zero, P)",
				BySets(hom, ring_homomorphism.MapZero))
			isPolynomial := a.Have(
				"so it is finitely supported on the monomials of the "+
					"variables up to n, its coefficients φ(P(m)) lying in T",
				"(λm:(num → num). φ(P(m))) ∈ polynomial_algebra(T, {i:num | i ≤ n})",
				By(
					FormPolynomial.Read(form),
					support,
					ring_homomorphism.MapIn.Read(hom),
					polynomial_algebra.PolynomialAlgebraMember.At(R, variables, P),
					polynomial_algebra.PolynomialAlgebraMember.At(T, variables, carried),
					finite_set.FiniteSubset,
					set_order.SubsetTrans))
			degree := a.Have(
				"where φ(P(m)) is nonzero so is P(m), φ keeping zero, and m has degree d",
				"∀m:(num → num). φ(P(m)) ≠ T.zero ⇒ sum({i:num | i ≤ n}, m) = d",
				a.ForEach(func(m *Expr[Fun[Nat, Nat]]) Action {
					return By(FormDegree.Read(form).At(m), ring_homomorphism.MapZero.Read(hom))
				}))
			a.Show(
				"a polynomial whose monomials have degree d",
				Unfold(HomogeneousPolynomialDef),
				By(isPolynomial, degree))
		}),
})}

// FormPart — the part of degree s of a polynomial in the variables up to n,
// its coefficients at the monomials of degree s, is a form of degree s: it is
// nonzero only where the polynomial is, and only in degree s.
var FormPart = formPartThm{family.Add(registry.ProofEntry{
	Name: "FormPart",
	Key:  "prop_e90cf8cd0d2f52dc",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n s:num. ∀Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"Q ∈ polynomial_algebra(R, {i:num | i ≤ n})",
		},
		Conclusion: "homogeneous_polynomial(R, n, s, «part»(s, Q))",
		Abbrev: Abbrev{
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), R.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, s *Expr[Nat],
			Q *Arrow[Fun[Nat, Nat], A],
			ring, polynomial Fact,
		) {
			coefficients := a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember))
			support := a.Have(
				"the part is nonzero only where Q is",
				"fun_support(R.zero, λm:(num → num). «part»(s, Q, m)) ⊆ fun_support(R.zero, Q)",
				BySets())
			inAlgebra := a.Have(
				"so it is a polynomial in the variables up to n, its coefficients those of Q or zero",
				"«part»(s, Q) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				Simp(Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				By(
					coefficients,
					support,
					finite_set.FiniteSubset,
					set_order.SubsetTrans,
					comm_ring.ZeroIn.Read(ring)))
			a.Show(
				"whose monomials all have degree s",
				Unfold(HomogeneousPolynomialDef),
				By(inAlgebra))
		}),
})}

// FormOwnPart — a form of degree s is its own part of degree s: its
// coefficient at a monomial is nonzero only when the monomial has degree s,
// so the part of degree s keeps every coefficient.
var FormOwnPart = formOwnPartThm{family.Add(registry.ProofEntry{
	Name: "FormOwnPart",
	Key:  "prop_640995461795ba35",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n s:num. ∀Q:((num → num) → A).",
		Hypotheses: []string{
			"homogeneous_polynomial(R, n, s, Q)",
		},
		Conclusion: "«part»(s, Q) = Q",
		Abbrev: Abbrev{
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), R.zero)"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], n, s *Expr[Nat], Q *Arrow[Fun[Nat, Nat], A], form Fact) {
			a.Do(Funext())
			m := a.FixAs[Fun[Nat, Nat]]("m")
			a.Show(
				"a monomial at which Q is not zero has degree s, and elsewhere Q is zero as the part is",
				By(form, FormDegree.At(R, n, s, Q, m)))
		}),
})}

// FormTimesPart — multiplying a polynomial Q by a form F of degree e moves
// its parts up by e: the part of degree s + e of F·Q is F times the part of
// degree s of Q. At a monomial m of degree s + e the coefficient of F·Q is
// the sum over m₁ ≤ m of F(m₁)·Q(m − m₁), and where F(m₁) is not zero m₁ has
// degree e, so m − m₁ has degree s; off degree s + e both sides vanish, F
// times a form of degree s being a form of degree e + s.
var FormTimesPart = formTimesPartThm{family.Add(registry.ProofEntry{
	Name: "FormTimesPart",
	Key:  "prop_3cb7f9c6865f0348",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n e s:num. ∀F Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, e, F)",
			"Q ∈ polynomial_algebra(R, {i:num | i ≤ n})",
		},
		Conclusion: "«part»(s + e, polynomial_algebra_mul(R, F, Q)) = " +
			"polynomial_algebra_mul(R, F, «part»(s, Q))",
		Abbrev: Abbrev{
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), R.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, e, s *Expr[Nat],
			F, Q *Arrow[Fun[Nat, Nat], A],
			ring, form, polynomial Fact,
		) {
			type monomial = Fun[Nat, Nat]
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			product := a.Have(
				"F times the part of degree s of Q is a form of degree e + s",
				"homogeneous_polynomial(R, n, e + s, polynomial_algebra_mul(R, F, «part»(s, Q)))",
				By(
					ring,
					polynomial,
					form,
					At(FormPart, R, n, s, Q),
					FormProduct.At(R, n, e, s, F, a.TermAs[Fun[monomial, A]]("«part»(s, Q)"))))
			qCoefficients := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"Q is nonzero at finitely many monomials",
				"every monomial where Q is nonzero is a monomial of the variables up to n",
				"every coefficient of Q lies in the carrier")
			split := a.Have(
				"a monomial below m and its complement have degrees adding up to that of m",
				Statement{
					Binders:    "∀m u:(num → num).",
					Hypotheses: []string{"∀x:num. u(x) ≤ m(x)"},
					Conclusion: "sum({i:num | i ≤ n}, u) + sum({i:num | i ≤ n}, λx:num. m(x) - u(x)) = " +
						"sum({i:num | i ≤ n}, m)",
				},
				Derive(func(b *Argument) {
					b.FixAs[monomial]("m")
					u := b.FixAs[monomial]("u")
					below := b.Assume()
					exponents := b.Have(
						"exponent by exponent, m is u plus m − u",
						"(λy:num. u(y) + (m(y) - u(y))) = m",
						Funext(),
						ByArith(below))
					b.Show(
						"so their degrees add up",
						By(
							exponents,
							nat_sum.Add.At(u, b.TermAs[monomial]("λx:num. m(x) - u(x)"), variables),
							num_segment.FiniteBelow.At(n)))
				}))
			a.Show(
				"at a monomial of degree s + e only the terms of F "+
					"of degree e count, against the part of degree s of Q",
				Funext(),
				Derive(func(b *Argument) {
					m := b.FixAs[monomial]("m")
					b.Cases(b.TermAs[Bool]("sum({i:num | i ≤ n}, m) = s + e"))
					b.When(
						"in degree s + e both sides are sums over the monomials below m",
						func(c *Argument, degree Fact) {
							termwise := c.Have(
								"term by term, Q at m − u may be read through its part of degree s",
								Statement{
									Binders:    "∀u:(num → num).",
									Hypotheses: []string{"∀x:num. u(x) ≤ m(x)"},
									Conclusion: "F(u) * Q(λx:num. m(x) - u(x)) = F(u) * «part»(s, Q, λx:num. m(x) - u(x))",
								},
								Derive(func(d *Argument) {
									u := d.FixAs[monomial]("u")
									below := d.Assume()
									rest := d.TermAs[monomial]("λx:num. m(x) - u(x)")
									d.Cases(d.TermAs[Bool]("sum({i:num | i ≤ n}, λx:num. m(x) - u(x)) = s"))
									d.When(
										"where m − u has degree s the part of degree s of Q is Q itself",
										func(f *Argument, same Fact) {
											f.Show(
												"so the two terms agree",
												By(same))
										})
									d.Otherwise(
										"elsewhere u is not of degree e, and F vanishes at u",
										func(f *Argument, other Fact) {
											vanishes := f.Have(
												"F is zero at u",
												"F(u) = R.zero",
												ByArith(other, degree, below, split.At(m, u), form, FormDegree.At(R, n, e, F, u)))
											f.Show(
												"so both terms are zero",
												By(
													other,
													vanishes,
													qCoefficients[2].At(rest),
													comm_ring.MulLeftZeroOn.Read(ring),
													comm_ring.ZeroIn.Read(ring)))
										})
								}))
							c.Show(
								"so the two sums agree term by term",
								Simp(Fwd(polynomial_algebra.PolynomialAlgebraMulDef)),
								By(
									termwise,
									module.ModuleSumCongruence.At(
										c.TermAs[Op[A]]("R.add"),
										c.TermAs[A]("R.zero"),
										c.TermAs[Set[monomial]]("{m₁:(num → num) | ∀x:num. m₁(x) ≤ m(x)}"),
										c.TermAs[Fun[monomial, A]]("λm₁:(num → num). F(m₁) * Q(λx:num. m(x) - m₁(x))"),
										c.TermAs[Fun[monomial, A]]("λm₁:(num → num). F(m₁) * «part»(s, Q, λx:num. m(x) - m₁(x))"))))
						})
					b.Otherwise(
						"off degree s + e the part is zero, and so is a form of degree e + s",
						func(c *Argument, other Fact) {
							c.Show(
								"the product of F with the part of degree s of Q vanishes at m",
								By(other, FormDegree.Read(product), nat_arith.AddSym))
						})
				}))
		}),
})}

// FormTimesLowPart — the product of a polynomial Q with a form F of degree e
// has no part below degree e: a monomial m where F·Q is not zero splits as
// m₁ + (m − m₁) with F nonzero at m₁, which then has degree e.
var FormTimesLowPart = formTimesLowPartThm{family.Add(registry.ProofEntry{
	Name: "FormTimesLowPart",
	Key:  "prop_53ff9408ff606946",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n e s:num. ∀F Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, e, F)",
			"Q ∈ polynomial_algebra(R, {i:num | i ≤ n})",
			"s < e",
		},
		Conclusion: "«part»(s, polynomial_algebra_mul(R, F, Q)) = fun_zero",
		Abbrev: Abbrev{
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), R.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, e, s *Expr[Nat],
			F, Q *Arrow[Fun[Nat, Nat], A],
			ring, form, polynomial, low Fact,
		) {
			type monomial = Fun[Nat, Nat]
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			fCoefficients := a.Conjuncts(
				a.Simplified(FormPolynomial.Read(form).AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"F is nonzero at finitely many monomials",
				"every monomial where F is nonzero is a monomial of the variables up to n",
				"every coefficient of F lies in the carrier")
			qCoefficients := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"Q is nonzero at finitely many monomials",
				"every monomial where Q is nonzero is a monomial of the variables up to n",
				"every coefficient of Q lies in the carrier")
			vanishes := a.Have(
				"F·Q has no monomial of degree below e",
				"∀m:(num → num). sum({i:num | i ≤ n}, m) < e ⇒ polynomial_algebra_mul(R, F, Q, m) = R.zero",
				Derive(func(b *Argument) {
					m := b.FixAs[monomial]("m")
					below := b.Assume()
					nonzero := b.SupposeNot()
					split := b.Conjuncts(
						GroupPremises(
							ring,
							fCoefficients[2],
							qCoefficients[2],
							nonzero,
							At(polynomial_algebra.PolynomialAlgebraMulSupport, R, F, Q, m)),
						"m is finitely supported",
						"some m₁ below m has F(m₁) and Q(m − m₁) nonzero")
					m1, term := b.UnpackAs[monomial](split[1], "m₁")
					pieces := b.Conjuncts(
						term,
						"m₁ lies below m",
						"F is nonzero at m₁",
						"Q is nonzero at m − m₁")
					exponents := b.Have(
						"exponent by exponent, m is m₁ plus m − m₁",
						"(λy:num. m₁(y) + (m(y) - m₁(y))) = m",
						Funext(),
						ByArith(pieces[0]))
					b.Show(
						"so the degree of m is at least that of m₁, which is e",
						ByArith(
							below,
							pieces[1],
							FormDegree.Read(form).At(m1),
							exponents,
							nat_sum.Add.At(m1, b.TermAs[monomial]("λx:num. m(x) - m₁(x)"), variables),
							num_segment.FiniteBelow.At(n)))
				}))
			a.Show(
				"so the part of degree s < e is zero",
				Funext(),
				By(low, vanishes, function_module.FunZeroDef))
		}),
})}

// FormTimesTruncation — multiplying a polynomial Q by a form F of degree e,
// the part of degree at most b of F·Q is F times the terms of Q whose degree
// plus e is at most b. At a monomial m of degree at most b the coefficient
// of F·Q is the sum over m₁ ≤ m of F(m₁)·Q(m − m₁), and where F(m₁) is not
// zero m₁ has degree e, so m − m₁ is a term the truncation of Q keeps; above
// degree b a nonzero term F(m₁)·Q(m − m₁) of F times the truncation would
// give m degree e plus at most b − e.
var FormTimesTruncation = formTimesTruncationThm{family.Add(registry.ProofEntry{
	Name: "FormTimesTruncation",
	Key:  "prop_8bc207e8be00b091",
	Reading: "No e ≤ b is assumed: when e exceeds b the truncation of Q is zero, and " +
		"so is the part of F·Q of degree at most b, F·Q having no part below degree e.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n e b:num. ∀F Q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, e, F)",
			"Q ∈ polynomial_algebra(R, {i:num | i ≤ n})",
		},
		Conclusion: "«upTo»(b, polynomial_algebra_mul(R, F, Q)) = " +
			"polynomial_algebra_mul(R, F, «truncation»)",
		Abbrev: Abbrev{
			{Name: "upTo", Text: "λd:num. λf:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) ≤ d, f(m), R.zero)"},
			{Name: "truncation", Text: "λu:(num → num). COND(sum({i:num | i ≤ n}, u) + e ≤ b, Q(u), R.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, e, b *Expr[Nat],
			F, Q *Arrow[Fun[Nat, Nat], A],
			ring, form, polynomial Fact,
		) {
			type monomial = Fun[Nat, Nat]
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			truncation := a.TermAs[Fun[monomial, A]]("«truncation»")
			fCoefficients := a.Conjuncts(
				a.Simplified(FormPolynomial.Read(form).AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"F is nonzero at finitely many monomials",
				"every monomial where F is nonzero is a monomial of the variables up to n",
				"every coefficient of F lies in the carrier")
			qCoefficients := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"Q is nonzero at finitely many monomials",
				"every monomial where Q is nonzero is a monomial of the variables up to n",
				"every coefficient of Q lies in the carrier")
			truncated := a.Have(
				"the coefficients of the truncation of Q lie in the carrier",
				"∀u:(num → num). «truncation»(u) ∈ R.carrier",
				By(qCoefficients[2], comm_ring.ZeroIn.Read(ring)))
			split := a.Have(
				"a monomial below m and its complement have degrees adding up to that of m",
				Statement{
					Binders:    "∀m u:(num → num).",
					Hypotheses: []string{"∀x:num. u(x) ≤ m(x)"},
					Conclusion: "sum({i:num | i ≤ n}, u) + sum({i:num | i ≤ n}, λx:num. m(x) - u(x)) = " +
						"sum({i:num | i ≤ n}, m)",
				},
				Derive(func(c *Argument) {
					c.FixAs[monomial]("m")
					u := c.FixAs[monomial]("u")
					below := c.Assume()
					exponents := c.Have(
						"exponent by exponent, m is u plus m − u",
						"(λy:num. u(y) + (m(y) - u(y))) = m",
						Funext(),
						ByArith(below))
					c.Show(
						"so their degrees add up",
						By(
							exponents,
							nat_sum.Add.At(u, c.TermAs[monomial]("λx:num. m(x) - u(x)"), variables),
							num_segment.FiniteBelow.At(n)))
				}))
			a.Show(
				"monomial by monomial, up to degree b the terms of F·Q are "+
					"those of F times the truncation, and above b both vanish",
				Funext(),
				Derive(func(c *Argument) {
					m := c.FixAs[monomial]("m")
					c.Cases(c.TermAs[Bool]("sum({i:num | i ≤ n}, m) ≤ b"))
					c.When(
						"up to degree b both sides are sums over the monomials below m",
						func(d *Argument, low Fact) {
							termwise := d.Have(
								"term by term, Q at m − u may be read through its truncation",
								Statement{
									Binders:    "∀u:(num → num).",
									Hypotheses: []string{"∀x:num. u(x) ≤ m(x)"},
									Conclusion: "F(u) * Q(λx:num. m(x) - u(x)) = F(u) * «truncation»(λx:num. m(x) - u(x))",
								},
								Derive(func(f *Argument) {
									u := f.FixAs[monomial]("u")
									below := f.Assume()
									rest := f.TermAs[monomial]("λx:num. m(x) - u(x)")
									f.Cases(f.TermAs[Bool]("sum({i:num | i ≤ n}, λx:num. m(x) - u(x)) + e ≤ b"))
									f.When(
										"where m − u has degree at most b − e the truncation keeps Q's coefficient",
										func(g *Argument, kept Fact) {
											g.Show(
												"so the two terms agree",
												By(kept))
										})
									f.Otherwise(
										"elsewhere u is not of degree e, and F vanishes at u",
										func(g *Argument, dropped Fact) {
											vanishes := g.Have(
												"F is zero at u",
												"F(u) = R.zero",
												ByArith(dropped, low, below, split.At(m, u), form, FormDegree.At(R, n, e, F, u)))
											g.Show(
												"so both terms are zero",
												By(
													dropped,
													vanishes,
													qCoefficients[2].At(rest),
													comm_ring.MulLeftZeroOn.Read(ring),
													comm_ring.ZeroIn.Read(ring)))
										})
								}))
							d.Show(
								"so the two sums agree term by term",
								Simp(Fwd(polynomial_algebra.PolynomialAlgebraMulDef)),
								By(
									termwise,
									module.ModuleSumCongruence.At(
										d.TermAs[Op[A]]("R.add"),
										d.TermAs[A]("R.zero"),
										d.TermAs[Set[monomial]]("{m₁:(num → num) | ∀x:num. m₁(x) ≤ m(x)}"),
										d.TermAs[Fun[monomial, A]]("λm₁:(num → num). F(m₁) * Q(λx:num. m(x) - m₁(x))"),
										d.TermAs[Fun[monomial, A]]("λm₁:(num → num). F(m₁) * «truncation»(λx:num. m(x) - m₁(x))"))))
						})
					c.Otherwise(
						"above degree b the part of F·Q is zero, and so is F times the truncation of Q",
						func(d *Argument, high Fact) {
							vanishes := d.Have(
								"F times the truncation of Q vanishes at m",
								"polynomial_algebra_mul(R, F, «truncation», m) = R.zero",
								Derive(func(f *Argument) {
									nonzero := f.SupposeNot()
									support := f.Conjuncts(
										GroupPremises(
											ring,
											fCoefficients[2],
											truncated,
											nonzero,
											At(polynomial_algebra.PolynomialAlgebraMulSupport, R, F, truncation, m)),
										"m is finitely supported",
										"some m₁ below m has F(m₁) and the truncation at m − m₁ nonzero")
									m1, term := f.UnpackAs[monomial](support[1], "m₁")
									pieces := f.Conjuncts(
										term,
										"m₁ lies below m",
										"F is nonzero at m₁",
										"the truncation of Q is nonzero at m − m₁")
									kept := f.Have(
										"so the truncation keeps m − m₁",
										"sum({i:num | i ≤ n}, λx:num. m(x) - m₁(x)) + e ≤ b",
										By(pieces[2]))
									f.Show(
										"then m has degree e plus at most b − e",
										ByArith(high, pieces[1], kept, pieces[0], form, FormDegree.At(R, n, e, F, m1), split.At(m, m1)))
								}))
							d.Show(
								"so both sides vanish at m",
								By(high, vanishes))
						})
				}))
		}),
})}

// FormScaling — a form of degree d, evaluated where every value is scaled by
// c, scales by c^d: each monomial m of the form has degree d, so its value
// scales by c^d (MonomialEvalScale), and c^d passes out of the finite sum
// over the monomials.
var FormScaling = formScalingThm{family.Add(registry.ProofEntry{
	Name: "FormScaling",
	Key:  "prop_9b7a78c04ec6d6f4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀T:ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀n d:num. " +
			"∀θ:(num → B). " +
			"∀c:B. " +
			"∀P:((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
			"homogeneous_polynomial(R, n, d, P)",
			"∀i:num. i ≤ n ⇒ θ(i) ∈ T.carrier",
			"c ∈ T.carrier",
		},
		Conclusion: "polynomial_algebra_eval(R, T, φ, λi:num. T.mul(θ(i), c), P) = " +
			"T.mul(monoid_pow(T.mul, T.one, c, d), polynomial_algebra_eval(R, T, φ, θ, P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			n, d *Expr[Nat],
			θ *Arrow[Nat, B],
			c *Expr[B],
			P *Arrow[Fun[Nat, Nat], A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			form, values, cIn Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			mapIn := ring_homomorphism.MapIn.Read(hom)
			coefficients := a.Conjuncts(
				a.Simplified(FormPolynomial.Read(form).AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"P is nonzero at finitely many monomials",
				"every monomial where P is nonzero is a monomial of the variables up to n",
				"every coefficient of P lies in the carrier")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			powerIn := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(target)).AsFact().At(c, d)
			termwise := a.Have(
				"at a monomial m of P the term scales by c^d, m having degree d",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(R.zero, P)"},
					Conclusion: "T.mul(φ(P(m)), monomial_eval(T, λi:num. T.mul(θ(i), c), m)) = " +
						"T.mul(monoid_pow(T.mul, T.one, c, d), T.mul(φ(P(m)), monomial_eval(T, θ, m)))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					inSupport := b.Assume()
					monomial := b.Have(
						"m is a monomial of the variables up to n, P being nonzero there",
						"m ∈ monomials({i:num | i ≤ n}) ∧ P(m) ≠ R.zero",
						BySets(coefficients[1], inSupport))
					pieces := b.Conjuncts(
						monomial,
						"m is a monomial",
						"P is nonzero at m")
					onVariables := b.Have(
						"the support of m lies among the variables up to n, and m is zero off it",
						"fun_support(0, m) ⊆ {i:num | i ≤ n} ∧ "+
							"(∀y:num. y ∈ {i:num | i ≤ n} ∧ y ∉ fun_support(0, m) ⇒ m(y) = 0)",
						BySets(pieces[0], polynomial_algebra.MonomialsMember.At(variables, m)))
					degree := b.Have(
						"the exponents of m sum to d over its support",
						"sum(fun_support(0, m), m) = d",
						By(
							pieces[1],
							FormDegree.Read(form).At(m),
							onVariables,
							nat_sum.Superset.At(b.TermAs[Set[Nat]]("fun_support(0, m)"), variables, m)))
					scaled := b.Have(
						"so the value of m scales by c^d, and the value of m lies in the carrier",
						"monomial_eval(T, λi:num. T.mul(θ(i), c), m) = "+
							"T.mul(monomial_eval(T, θ, m), monoid_pow(T.mul, T.one, c, d)) ∧ "+
							"monomial_eval(T, θ, m) ∈ T.carrier",
						By(
							target,
							values,
							degree,
							cIn,
							pieces[0],
							At(polynomial_algebra_evaluation.MonomialEvalScale, T, variables, θ, c, m),
							At(polynomial_algebra_evaluation.MonomialEvalIn, T, variables, θ, m)))
					scaledParts := b.Conjuncts(
						scaled,
						"the value of m scales by c^d",
						"and lies in the carrier")
					coefficient := b.Have(
						"the coefficient of m and c^d lie in the carrier",
						"φ(P(m)) ∈ T.carrier ∧ monoid_pow(T.mul, T.one, c, d) ∈ T.carrier",
						By(cIn, mapIn.AsFact().At(b.TermAs[A]("P(m)")), coefficients[2].At(m), powerIn))
					b.Show(
						"c^d commutes past the coefficient",
						scaledParts[0].Rw(),
						ByArith(target, scaledParts[1], coefficient))
				}))
			terms := a.Have(
				"P has finitely many monomials, and each term of its value lies in the carrier",
				"finite(fun_support(R.zero, P)) ∧ "+
					"(∀m:(num → num). m ∈ fun_support(R.zero, P) ⇒ T.mul(φ(P(m)), monomial_eval(T, θ, m)) ∈ T.carrier)",
				Derive(func(b *Argument) {
					member := b.Have(
						"each term is a product of members of the carrier",
						"∀m:(num → num). m ∈ fun_support(R.zero, P) ⇒ T.mul(φ(P(m)), monomial_eval(T, θ, m)) ∈ T.carrier",
						Derive(func(e *Argument) {
							m := e.FixAs[Fun[Nat, Nat]]("m")
							inSupport := e.Assume()
							monomial := e.Have(
								"m is a monomial of the variables up to n, and φ(P(m)) lies in T",
								"m ∈ monomials({i:num | i ≤ n}) ∧ φ(P(m)) ∈ T.carrier",
								BySets(coefficients[1], inSupport, mapIn.AsFact().At(e.TermAs[A]("P(m)")), coefficients[2].At(m)))
							e.Show(
								"a coefficient times a monomial's value",
								By(
									target,
									values,
									monomial,
									comm_ring.MulIn.Read(target),
									At(polynomial_algebra_evaluation.MonomialEvalIn, T, variables, θ, m)))
						}))
					b.Show(
						"both",
						By(coefficients[0], member))
				}))
			a.Show(
				"so c^d passes out of the finite sum over the monomials of P",
				Simp(Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef)),
				By(
					termwise,
					cIn,
					terms,
					At(
						module.ModuleSumCongruence,
						a.TermAs[Op[B]]("T.add"),
						a.TermAs[B]("T.zero"),
						a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(R.zero, P)"),
						a.TermAs[Fun[Fun[Nat, Nat], B]](
							"λm:(num → num). T.mul(φ(P(m)), monomial_eval(T, λi:num. T.mul(θ(i), c), m))"),
						a.TermAs[Fun[Fun[Nat, Nat], B]](
							"λm:(num → num). T.mul(monoid_pow(T.mul, T.one, c, d), T.mul(φ(P(m)), monomial_eval(T, θ, m)))")),
					module.ModuleSumSmul.Read(module.RegularModuleOn.Read(target)).AsFact().At(
						a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(R.zero, P)"),
						a.TermAs[B]("monoid_pow(T.mul, T.one, c, d)"),
						a.TermAs[Fun[Fun[Nat, Nat], B]]("λm:(num → num). T.mul(φ(P(m)), monomial_eval(T, θ, m))")),
					powerIn))
		}),
})}

// FormZeroScaling — a form vanishing at a point θ vanishes at θ scaled by
// any c: its value there is c^d times its value at θ (FormScaling), and c^d
// times zero is zero.
var FormZeroScaling = formZeroScalingThm{family.Add(registry.ProofEntry{
	Name: "FormZeroScaling",
	Key:  "prop_106b8c7ceafd3424",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀T:ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀n d:num. " +
			"∀θ:(num → B). " +
			"∀c:B. " +
			"∀P:((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
			"homogeneous_polynomial(R, n, d, P)",
			"∀i:num. i ≤ n ⇒ θ(i) ∈ T.carrier",
			"c ∈ T.carrier",
			"polynomial_algebra_eval(R, T, φ, θ, P) = T.zero",
		},
		Conclusion: "polynomial_algebra_eval(R, T, φ, λi:num. T.mul(θ(i), c), P) = T.zero",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			n, d *Expr[Nat],
			θ *Arrow[Nat, B],
			c *Expr[B],
			P *Arrow[Fun[Nat, Nat], A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			form, values, cIn, vanishes Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			a.Show(
				"the value at θ·c is c^d times the value at θ, which is zero",
				By(
					hom,
					form,
					values,
					cIn,
					vanishes,
					FormScaling.At(R, T, φ, n, d, θ, c, P),
					comm_ring.MulRightZeroOn.Read(target).AsFact().At(a.TermAs[B]("monoid_pow(T.mul, T.one, c, d)")),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(target)).AsFact().At(c, d)))
		}),
})}

// FormRatioScaling — the ratio of a form P of degree r·a to the a-th power of
// a form H of degree r does not change when the point is scaled: a value v
// with v·H(y)^a = P(y) has v·H(y·c)^a = P(y·c), both sides scaling by
// c^(r·a) (FormScaling).
var FormRatioScaling = formRatioScalingThm{family.Add(registry.ProofEntry{
	Name: "FormRatioScaling",
	Key:  "prop_df2d00f6458bf35f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r a:num. ∀y:(num → A). ∀c v:A. ∀H P:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«scalars», n, r, H)",
			"homogeneous_polynomial(«scalars», n, r * a, P)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
			"c ∈ M.carrier",
			"v ∈ M.carrier",
			"v * monoid_pow(M.mul, M.one, «valueAt»(y, H), a) = «valueAt»(y, P)",
		},
		Conclusion: "v * monoid_pow(M.mul, M.one, «valueAt»(λi:num. y(i) * c, H), a) = " +
			"«valueAt»(λi:num. y(i) * c, P)",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, r, a *Expr[Nat],
			y *Arrow[Nat, A],
			c, v *Expr[A],
			H, P *Arrow[Fun[Nat, Nat], A],
			kSub, hForm, pForm, coordinates, cIn, vIn, represents Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
			coefficients := arg.TermAs[RingOps[A]]("«scalars»")
			identity := arg.TermAs[Fun[A, A]]("λa:A. a")
			hy := arg.TermAs[A]("«valueAt»(y, H)")
			inclusion := arg.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			evaluation := arg.Have(
				"so evaluation at y is a ring map out of the polynomials over k",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«scalars», field_ring(M), λa:A. a, y))",
				By(coordinates, inclusion, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			hValue := arg.Have(
				"H(y) lies in M",
				"«valueAt»(y, H) ∈ M.carrier",
				By(
					FormPolynomial.Read(hForm),
					polynomial_algebra.PolynomialAlgebraRingDef,
					ring_homomorphism.MapIn.Read(evaluation)))
			scaledH := arg.Have(
				"H(y·c) = c^r·H(y)",
				"«valueAt»(λi:num. y(i) * c, H) = monoid_pow(M.mul, M.one, c, r) * «valueAt»(y, H)",
				By(
					inclusion,
					hForm,
					coordinates,
					cIn,
					At(FormScaling, coefficients, fieldRing, identity, n, r, y, c, H)))
			scaledP := arg.Have(
				"and P(y·c) = c^(r·a)·P(y)",
				"«valueAt»(λi:num. y(i) * c, P) = monoid_pow(M.mul, M.one, c, r * a) * «valueAt»(y, P)",
				By(
					inclusion,
					pForm,
					coordinates,
					cIn,
					At(FormScaling, coefficients, fieldRing, identity, n, arg.TermAs[Nat]("r * a"), y, c, P)))
			cr := arg.TermAs[A]("monoid_pow(M.mul, M.one, c, r)")
			power := arg.Have(
				"so H(y·c)^a = (c^r)^a·H(y)^a = c^(r·a)·H(y)^a",
				"monoid_pow(M.mul, M.one, «valueAt»(λi:num. y(i) * c, H), a) = "+
					"monoid_pow(M.mul, M.one, c, r * a) * monoid_pow(M.mul, M.one, «valueAt»(y, H), a)",
				By(
					scaledH,
					cIn,
					hValue,
					comm_monoid.MulPowOn.Read(monoid).AsFact().At(cr, hy, a),
					comm_monoid.PowPowOn.Read(monoid).AsFact().At(c, r, a),
					powIn.AsFact().At(c, r)))
			arg.Show(
				"both sides scale by c^(r·a)",
				power.Rw(),
				scaledP.Rw(),
				represents.RwRev(),
				ByArith(
					M,
					vIn,
					GroupPremises(hValue, powIn.AsFact().At(hy, a)),
					GroupPremises(cIn, powIn.AsFact().At(c, arg.TermAs[Nat]("r * a")))))
		}),
})}

// EvaluationRingHom — evaluation at a point x of M, its coordinates up to n
// in M, is a ring homomorphism from the polynomials over k: the inclusion
// of k is one, and a ring homomorphism extends to the polynomials.
var EvaluationRingHom = evaluationRingHomThm{family.Add(registry.ProofEntry{
	Name: "EvaluationRingHom",
	Key:  "prop_a1c087d5f3bfa7e6",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀x:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
		},
		Conclusion: "ring_homomorphism(«polynomials», field_ring(M), «at»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			x *Arrow[Nat, A],
			subfieldK, coordinates Fact,
		) {
			inclusion := a.Have(
				"the inclusion of k into M is a ring homomorphism",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					subfieldK,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			a.Show(
				"so is evaluation at x, its coordinates lying in M",
				By(inclusion, coordinates, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
		}),
})}

// FormNumerators — for H of degree r, P of degree r·c and Q of degree r·d,
// P·H^d + Q·H^c and P·Q are forms of degree r·(c + d), and at a point y of
// M they take the values P(y)·H(y)^d + Q(y)·H(y)^c and P(y)·Q(y): the
// numerators of the sum and of the product of P/H^c and Q/H^d.
var FormNumerators = formNumeratorsThm{family.Add(registry.ProofEntry{
	Name: "FormNumerators",
	Key:  "prop_d2331b35dc3d8e02",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r c d:num. ∀y:(num → A). ∀H P Q:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
			"homogeneous_polynomial(«scalars», n, r, H)",
			"homogeneous_polynomial(«scalars», n, r * c, P)",
			"homogeneous_polynomial(«scalars», n, r * d, Q)",
		},
		Conclusion: "homogeneous_polynomial(«scalars», n, r * (c + d), «sum») ∧ " +
			"homogeneous_polynomial(«scalars», n, r * (c + d), «product») ∧ " +
			"«valueAt»(y, «sum») = " +
			"«valueAt»(y, P) * monoid_pow(M.mul, M.one, «valueAt»(y, H), d) + " +
			"«valueAt»(y, Q) * monoid_pow(M.mul, M.one, «valueAt»(y, H), c) ∧ " +
			"«valueAt»(y, «product») = «valueAt»(y, P) * «valueAt»(y, Q)",
		Abbrev: Abbrev{
			{Name: "power", Text: "λe:num. " +
				"    monoid_pow(polynomial_algebra_mul(«scalars»), polynomial_algebra_one(«scalars»), H, e)"},
			{Name: "sum", Text: "fun_add(«scalars».add, " +
				"    polynomial_algebra_mul(«scalars», P, «power»(d)), " +
				"    polynomial_algebra_mul(«scalars», Q, «power»(c)))"},
			{Name: "product", Text: "polynomial_algebra_mul(«scalars», P, Q)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, r, c, d *Expr[Nat],
			y *Arrow[Nat, A],
			H, P, Q *Arrow[Fun[Nat, Nat], A],
			kSub, coordinates, hForm, pForm, qForm Fact,
		) {
			coefficients := a.TermAs[RingOps[A]]("«scalars»")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			coefficientRing := ring_homomorphism.Source.Read(inclusion)
			evaluation := a.Have(
				"evaluation at y is a ring map from the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«scalars», field_ring(M), λa:A. a, y))",
				By(kSub, coordinates, Read(EvaluationRingHom, M).At(k, n, y)))
			powers := a.Have(
				"the powers of H are forms of degree r·e, evaluating to the powers of H(y)",
				"∀e:num. "+
					"    homogeneous_polynomial(«scalars», n, r * e, «power»(e)) ∧ "+
					"    «valueAt»(y, «power»(e)) = monoid_pow(M.mul, M.one, «valueAt»(y, H), e)",
				Derive(func(b *Argument) {
					exponent := b.FixAs[Nat]("e")
					degree := b.Have(
						"H^e is a form of degree r·e",
						"homogeneous_polynomial(«scalars», n, r * e, «power»(e))",
						By(coefficientRing, hForm, At(FormPower, coefficients, n, r, H, exponent)))
					value := b.Have(
						"and evaluates to H(y)^e, evaluation keeping powers",
						"«valueAt»(y, «power»(e)) = monoid_pow(M.mul, M.one, «valueAt»(y, H), e)",
						By(
							FormPolynomial.Read(hForm),
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.RingMapPower.Read(evaluation)))
					b.Show(
						"both",
						By(degree, value))
				}))
			rc := a.TermAs[Nat]("r * c")
			rd := a.TermAs[Nat]("r * d")
			powerC := a.TermAs[Fun[Fun[Nat, Nat], A]]("«power»(c)")
			powerD := a.TermAs[Fun[Fun[Nat, Nat], A]]("«power»(d)")
			first := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«scalars», P, «power»(d))")
			second := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«scalars», Q, «power»(c))")
			distributed := nat_arith.LeftAddDistrib.At(r, c, d)
			pf := a.Have(
				"P·H^d is a form of degree r·c + r·d = r·(c + d)",
				"homogeneous_polynomial(«scalars», "+
					"    n, "+
					"    r * (c + d), "+
					"    polynomial_algebra_mul(«scalars», P, «power»(d)))",
				By(
					coefficientRing,
					pForm,
					powers.At(d),
					distributed,
					At(FormProduct, coefficients, n, rc, rd, P, powerD)))
			qf := a.Have(
				"and so is Q·H^c, of degree r·d + r·c",
				"homogeneous_polynomial(«scalars», "+
					"    n, "+
					"    r * (c + d), "+
					"    polynomial_algebra_mul(«scalars», Q, «power»(c)))",
				By(
					coefficientRing,
					qForm,
					powers.At(c),
					distributed,
					nat_arith.AddSym.At(rd, rc),
					At(FormProduct, coefficients, n, rd, rc, Q, powerC)))
			sumForm := a.Have(
				"so P·H^d + Q·H^c is a form of degree r·(c + d)",
				"homogeneous_polynomial(«scalars», n, r * (c + d), «sum»)",
				By(
					coefficientRing,
					pf,
					qf,
					At(FormSum, coefficients, n, a.TermAs[Nat]("r * (c + d)"), first, second)))
			productForm := a.Have(
				"and P·Q is one of degree r·c + r·d = r·(c + d)",
				"homogeneous_polynomial(«scalars», n, r * (c + d), «product»)",
				By(
					Normalized,
					coefficientRing,
					pForm,
					qForm,
					distributed,
					At(FormProduct, coefficients, n, rc, rd, P, Q)))
			polynomials := a.Have(
				"P and Q are polynomials over k",
				"P ∈ «polynomials».carrier ∧ Q ∈ «polynomials».carrier",
				By(FormPolynomial.Read(pForm), FormPolynomial.Read(qForm)))
			factors := a.Have(
				"P·H^d, Q·H^c and the powers of H are polynomials over k",
				"polynomial_algebra_mul(«scalars», P, «power»(d)) ∈ «polynomials».carrier ∧ "+
					"polynomial_algebra_mul(«scalars», Q, «power»(c)) ∈ «polynomials».carrier ∧ "+
					"«power»(c) ∈ «polynomials».carrier ∧ "+
					"«power»(d) ∈ «polynomials».carrier",
				By(pf, qf, powers.At(c), powers.At(d), FormPolynomial))
			products := a.Have(
				"the value of P·H^d is P(y)·H(y)^d, and that of Q·H^c is Q(y)·H(y)^c",
				"«valueAt»(y, polynomial_algebra_mul(«scalars», P, «power»(d))) = "+
					"«valueAt»(y, P) * monoid_pow(M.mul, M.one, «valueAt»(y, H), d) ∧ "+
					"«valueAt»(y, polynomial_algebra_mul(«scalars», Q, «power»(c))) = "+
					"«valueAt»(y, Q) * monoid_pow(M.mul, M.one, «valueAt»(y, H), c)",
				By(
					polynomials,
					factors,
					powers.At(c),
					powers.At(d),
					polynomial_algebra.PolynomialAlgebraRingDef,
					ring_homomorphism.MapMul.Read(evaluation).AsFact().At(P, powerD),
					ring_homomorphism.MapMul.Read(evaluation).AsFact().At(Q, powerC)))
			a.Show(
				"both forms, the values of a sum and a product being the sum and the product of the values",
				By(
					sumForm,
					productForm,
					factors,
					products,
					polynomials,
					polynomial_algebra.PolynomialAlgebraRingDef,
					ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(first, second),
					ring_homomorphism.MapMul.Read(evaluation).AsFact().At(P, Q)))
		}),
})}

// MixedMonomialForm — for i, j up to n and r positive, X_i·X_j^(r−1) is a
// form of degree r over k, and its value at a point y of M is
// y(i)·y(j)^(r−1): evaluation keeps products and powers and takes each
// variable to its coordinate.
var MixedMonomialForm = mixedMonomialFormThm{family.Add(registry.ProofEntry{
	Name: "MixedMonomialForm",
	Key:  "prop_a9d15f205a6685f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r i j:num. ∀y:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"0 < r",
			"i ≤ n",
			"j ≤ n",
			"∀m:num. m ≤ n ⇒ y(m) ∈ M.carrier",
		},
		Conclusion: "homogeneous_polynomial(«scalars», n, r, «mixed») ∧ " +
			"«valueAt»(y, «mixed») = y(i) * monoid_pow(M.mul, M.one, y(j), r - 1)",
		Abbrev: Abbrev{
			{Name: "mixed", Text: "polynomial_algebra_mul(«scalars», " +
				"    polynomial_algebra_var(«scalars», i), " +
				"    monoid_pow(polynomial_algebra_mul(«scalars»), " +
				"        polynomial_algebra_one(«scalars»), " +
				"        polynomial_algebra_var(«scalars», j), " +
				"        r - 1))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, r, i, j *Expr[Nat],
			y *Arrow[Nat, A],
			kSub, positive, iInRange, jInRange, coordinates Fact,
		) {
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			coefficients := a.TermAs[RingOps[A]]("«scalars»")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			one := a.TermAs[Nat]("1")
			lower := a.TermAs[Nat]("r - 1")
			varI := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«scalars», i)")
			varJ := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«scalars», j)")
			power := a.TermAs[Fun[Fun[Nat, Nat], A]](
				"monoid_pow(polynomial_algebra_mul(«scalars»), " +
					"    polynomial_algebra_one(«scalars»), " +
					"    polynomial_algebra_var(«scalars», j), " +
					"    r - 1)")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			coefficientRing := ring_homomorphism.Source.Read(inclusion)
			evaluation := a.Have(
				"evaluation at y is a ring map from the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«scalars», field_ring(M), λa:A. a, y))",
				By(kSub, coordinates, Read(EvaluationRingHom, M).At(k, n, y)))
			varIForm := a.Have(
				"X_i is a form of degree 1",
				"homogeneous_polynomial(«scalars», n, 1, polynomial_algebra_var(«scalars», i))",
				By(iInRange, coefficientRing, At(FormVariable, coefficients, n, i)))
			varJForm := a.Have(
				"and so is X_j",
				"homogeneous_polynomial(«scalars», n, 1, polynomial_algebra_var(«scalars», j))",
				By(jInRange, coefficientRing, At(FormVariable, coefficients, n, j)))
			powerForm := a.Have(
				"X_j^(r−1) is a form of degree 1·(r − 1)",
				"homogeneous_polynomial(«scalars», "+
					"    n, "+
					"    1 * (r - 1), "+
					"    monoid_pow(polynomial_algebra_mul(«scalars»), "+
					"        polynomial_algebra_one(«scalars»), "+
					"        polynomial_algebra_var(«scalars», j), "+
					"        r - 1))",
				By(coefficientRing, varJForm, At(FormPower, coefficients, n, one, varJ, lower)))
			degree := a.Have(
				"1 + 1·(r − 1) = r·1, r being positive",
				"1 + 1 * (r - 1) = r * 1",
				ByArith(positive))
			productForm := a.Have(
				"so X_i·X_j^(r−1) is a form of degree r·1",
				"homogeneous_polynomial(«scalars», n, r * 1, «mixed»)",
				degree.RwRev(),
				By(
					coefficientRing,
					varIForm,
					powerForm,
					At(FormProduct, coefficients, n, one, a.TermAs[Nat]("1 * (r - 1)"), varI, power)))
			values := a.Conjuncts(
				a.Have(
					"y(i) and y(j) lie in M",
					"y(i) ∈ M.carrier ∧ y(j) ∈ M.carrier",
					By(iInRange, jInRange, coordinates)),
				"y(i) lies in M",
				"and so does y(j)")
			varJValue := a.Have(
				"X_j evaluates to y(j)",
				"polynomial_algebra_eval(«scalars», "+
					"    field_ring(M), "+
					"    λa:A. a, "+
					"    y, "+
					"    polynomial_algebra_var(«scalars», j)) = "+
					"y(j)",
				By(
					inclusion,
					values[1],
					polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, fieldRing, identity, y, j)))
			a.Show(
				"of degree r, with value y(i)·y(j)^(r−1), evaluation keeping products and powers",
				By(
					Normalized,
					productForm,
					nat_arith.MulOne.At(r),
					a.Have(
						"X_i evaluates to y(i)",
						"polynomial_algebra_eval(«scalars», "+
							"    field_ring(M), "+
							"    λa:A. a, "+
							"    y, "+
							"    polynomial_algebra_var(«scalars», i)) = "+
							"y(i)",
						By(
							inclusion,
							values[0],
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(
								coefficients, fieldRing, identity, y, i))),
					a.Have(
						"X_j^(r−1) evaluates to y(j)^(r−1)",
						"polynomial_algebra_eval(«scalars», "+
							"    field_ring(M), "+
							"    λa:A. a, "+
							"    y, "+
							"    monoid_pow(polynomial_algebra_mul(«scalars»), "+
							"        polynomial_algebra_one(«scalars»), "+
							"        polynomial_algebra_var(«scalars», j), "+
							"        r - 1)) = "+
							"monoid_pow(M.mul, M.one, y(j), r - 1)",
						By(
							FormPolynomial.Read(varJForm),
							varJValue,
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.RingMapPower.Read(evaluation))),
					FormPolynomial.Read(varIForm),
					FormPolynomial.Read(powerForm),
					polynomial_algebra.PolynomialAlgebraRingDef,
					ring_homomorphism.MapMul.Read(evaluation)))
		}),
})}

// VariableMonomialDegree — the monomial of the variable i, for i up to n,
// has degree one over the variables up to n: its only nonzero exponent is
// the one at i, which is one.
var VariableMonomialDegree = variableMonomialDegreeThm{family.Add(registry.ProofEntry{
	Name: "VariableMonomialDegree",
	Key:  "prop_acb9c82e9706cbbd",
	Build: family.Theorem(Statement{
		Binders:    "∀n i:num.",
		Hypotheses: []string{"i ≤ n"},
		Conclusion: "sum({j:num | j ≤ n}, monomial_var(i)) = 1",
	},
		func(a *Argument, n, i *Expr[Nat], inRange Fact) {
			exponent := a.TermAs[Fun[Nat, Nat]]("monomial_var(i)")
			single := a.TermAs[Set[Nat]]("{i}")
			variables := a.TermAs[Set[Nat]]("{j:num | j ≤ n}")
			atI := a.Have(
				"over {i} the exponents sum to the exponent at i, one",
				"sum({i}, monomial_var(i)) = 1",
				Simp(Fwd(nat_sum.NatSumDef), Fwd(polynomial_algebra.MonomialVarDef), Fwd(free_module.DeltaAtDef)),
				By(
					nat_sum.MonoidalNatAdd,
					monoidal.Sing.At(
						a.TermAs[Op[Nat]]("(+)"), a.TermAs[Fun[Nat, Nat]]("λy:num. COND(y = i, 1, 0)"), i)))
			offI := a.Have(
				"the exponents vanish off i, which lies among the variables up to n",
				"{i} ⊆ {j:num | j ≤ n} ∧ (∀y:num. y ∈ {j:num | j ≤ n} ∧ y ∉ {i} ⇒ monomial_var(i, y) = 0)",
				BySets(inRange, polynomial_algebra.MonomialVarDef, free_module.DeltaAtDef))
			a.Show(
				"so they sum to one over the variables up to n",
				By(offI, atI, nat_sum.Superset.At(single, variables, exponent)))
		}),
	Reading: "i ≤ n is load-bearing: past n the exponent of the " +
		"variable i is not among those summed, and the sum is zero.",
})}

// PartialOfForm — the partial derivative of a form of degree d is a form
// of degree d − 1: it is a polynomial in the variables up to n, and a
// monomial m where it is nonzero has P nonzero at m raised at i, which is
// then a monomial of the variables up to n, so i ≤ n, and of degree d, one
// more than the degree of m.
var PartialOfForm = partialOfFormThm{family.Add(registry.ProofEntry{
	Name: "PartialOfForm",
	Key:  "prop_7658dfd4c172963f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d i:num. ∀P:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homogeneous_polynomial(R, n, d, P)",
		},
		Conclusion: "homogeneous_polynomial(R, n, d - 1, polynomial_algebra_partial(R, i, P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, i *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			ring, form Fact,
		) {
			variables := a.TermAs[Set[Nat]]("{j:num | j ≤ n}")
			pPolynomial := FormPolynomial.Read(form)
			degree := a.Have(
				"a monomial where the derivative is nonzero has degree d − 1",
				"∀m:(num → num). polynomial_algebra_partial(R, i, P, m) ≠ R.zero ⇒ sum({j:num | j ≤ n}, m) = d - 1",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					nonzero := b.Assume()
					raised := b.TermAs[Fun[Nat, Nat]]("λy:num. m(y) + monomial_var(i, y)")
					atRaised := b.Have(
						"P is nonzero at m raised at i, the derivative there being a numeral times that coefficient",
						"P(λy:num. m(y) + monomial_var(i, y)) ≠ R.zero",
						By(
							nonzero,
							partial_derivative.PolynomialAlgebraPartialDef,
							comm_ring.OneIn.Read(ring),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
							comm_ring.MulRightZeroOn.Read(ring)))
					// Unpacked inside this Derive, where the rewrite of the
					// fact stays local: the closing Show reads pPolynomial
					// whole.
					coefficients := b.Conjuncts(
						b.Simplified(pPolynomial.AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
						"P is nonzero at finitely many monomials",
						"every monomial where P is nonzero is a monomial of the variables up to n",
						"every coefficient of P lies in the carrier")
					monomial := b.Have(
						"so m raised at i is a monomial of the variables up to n",
						"(λy:num. m(y) + monomial_var(i, y)) ∈ monomials({j:num | j ≤ n})",
						By(atRaised, b.Unfolded(coefficients[1], set_basic.SubsetDef).At(raised)))
					inRange := b.Have(
						"so i is among the variables up to n, the exponent of m raised being positive there",
						"i ≤ n",
						By(
							b.Unfolded(monomial, polynomial_algebra.MonomialsDef),
							polynomial_algebra.MonomialVarValues.At(i),
							nat_arith.AddEqZero,
							nat_arith.OneNotZero))
					b.Show(
						"m raised at i has degree d, one more than the degree of m",
						ByArith(
							atRaised,
							FormDegree.Read(form).At(raised),
							inRange,
							At(VariableMonomialDegree, n, i),
							num_segment.FiniteBelow.At(n),
							nat_sum.Add.At(m, b.TermAs[Fun[Nat, Nat]]("monomial_var(i)"), variables)))
				}))
			// The goal is opened by Simp, not Unfold: an Unfold would rewrite
			// the form the readings above are read at.
			a.Show(
				"a polynomial in the variables up to n whose monomials have degree d − 1",
				Simp(Fwd(HomogeneousPolynomialDef)),
				By(ring, pPolynomial, degree, partial_derivative.PolynomialPartialIn.At(R, variables, i, P)))
		}),
	Reading: "The degree is truncated: at d = 0 the derivative is zero, and 0 − " +
		"1 = 0 in num. At a variable i past n the derivative is the zero polynomial.",
})}

// FormsAdditive — the forms of degree d contain zero and are closed under
// sums (FormSum), so they are a submonoid of the additive monoid of the
// polynomials.
var FormsAdditive = formsAdditiveThm{family.Add(registry.ProofEntry{
	Name: "FormsAdditive",
	Key:  "prop_9db1bb334ff3a502",
	Build: family.Theorem(
		"∀R:comm_ring_on(A). ∀n d:num. "+
			"    comm_monoid_on({P:((num → num) → A) | homogeneous_polynomial(R, n, d, P)}, fun_add, fun_zero)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n, d *Expr[Nat]) {
			polynomials := a.Have(
				"the polynomials in the variables up to n are a commutative ring",
				"comm_ring_on(polynomial_algebra_ring(R, {i:num | i ≤ n}))",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
			sums := a.Have(
				"a sum of two forms of degree d is one",
				Statement{
					Binders: "∀P Q:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(R, n, d, P)",
						"homogeneous_polynomial(R, n, d, Q)",
					},
					Conclusion: "homogeneous_polynomial(R, n, d, fun_add(P, Q))",
				},
				By(ring, FormSum))
			zero := a.Have(
				"the zero polynomial has no nonzero coefficient",
				"homogeneous_polynomial(R, n, d, fun_zero)",
				By(HomogeneousPolynomialDef, comm_ring.ZeroIn.Read(polynomials), function_module.FunZeroDef))
			additive := comm_ring.AddMonoidOn.Read(polynomials)
			a.Show(
				"the monoid laws hold on the polynomials, the forms among them",
				Simp(Fwd(comm_monoid.CommMonoidOn)),
				By(
					sums,
					FormPolynomial,
					zero,
					comm_monoid.CommOn.Read(additive),
					comm_monoid.AssocOn.Read(additive),
					comm_monoid.LeftIdentityOn.Read(additive)))
		}),
})}

// HomogenizedForm — a polynomial f of degree m over R, homogenized at two
// forms F and G of degree d, is a form of degree d·m: it is the sum of the
// terms G^(m−i)·f(i)·F^i for i up to m, each a form of degree d·(m − i) + d·i.
var HomogenizedForm = homogenizedFormThm{family.Add(registry.ProofEntry{
	Name: "HomogenizedForm",
	Key:  "prop_8f127d6356821606",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀n d:num. ∀f:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"homogeneous_polynomial(R, n, d, F)",
			"homogeneous_polynomial(R, n, d, G)",
		},
		Conclusion: "homogeneous_polynomial(R, " +
			"    n, " +
			"    d * polynomial_degree(f), " +
			"    polynomial_eval(fun_add, " +
			"        fun_zero, " +
			"        polynomial_algebra_mul(R), " +
			"        polynomial_algebra_one(R), " +
			"        «homogenized», " +
			"        F))",
		Abbrev: Abbrev{
			{Name: "homogenized", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(f), " +
				"        polynomial_algebra_mul(R, " +
				"            monoid_pow(polynomial_algebra_mul(R), " +
				"                polynomial_algebra_one(R), " +
				"                G, " +
				"                polynomial_degree(f) - i), " +
				"            polynomial_algebra_const(R, f(i))), " +
				"        fun_zero)"},
		},
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n, d *Expr[Nat],
			f *Arrow[Nat, A],
			F, G *Expr[Fun[Fun[Nat, Nat], A]],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"f is a polynomial over R",
				"F is a form of degree d",
				"G is a form of degree d")
			fOver, fForm, gForm := parts[0], parts[1], parts[2]
			terms := a.Have(
				"the term G^(m−i)·f(i)·F^i, for i up to m, is a form of degree d·m",
				Statement{
					Binders:    "∀i:num.",
					Hypotheses: []string{"i ≤ polynomial_degree(f)"},
					Conclusion: "homogeneous_polynomial(R, " +
						"    n, " +
						"    d * polynomial_degree(f), " +
						"    polynomial_algebra_mul(R, " +
						"        polynomial_algebra_mul(R, " +
						"            monoid_pow(polynomial_algebra_mul(R), " +
						"                polynomial_algebra_one(R), " +
						"                G, " +
						"                polynomial_degree(f) - i), " +
						"            polynomial_algebra_const(R, f(i))), " +
						"        monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), F, i)))",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					complement := b.TermAs[Nat]("polynomial_degree(f) - i")
					rest := b.Have(
						"i is at most m",
						"polynomial_degree(f) - i + i = polynomial_degree(f)",
						ByArith(below))
					degree := b.Have(
						"so the degrees d·(m − i) and d·i add up to d·m",
						"d * (polynomial_degree(f) - i) + 0 + d * i = d * polynomial_degree(f)",
						ByArith(rest, nat_arith.LeftAddDistrib.At(d, complement, i)))
					coefficient := b.Have(
						"f(i) lies in R",
						"f(i) ∈ R.carrier",
						By(fOver, polynomial.PolynomialOverDef))
					power := b.TermAs[Fun[Fun[Nat, Nat], A]](
						"monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), G, polynomial_degree(f) - i)")
					constant := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_const(R, f(i))")
					leading := b.Have(
						"G^(m−i)·f(i) is a form of degree d·(m − i) + 0",
						"homogeneous_polynomial(R, "+
							"    n, "+
							"    d * (polynomial_degree(f) - i) + 0, "+
							"    polynomial_algebra_mul(R, "+
							"        monoid_pow(polynomial_algebra_mul(R), "+
							"            polynomial_algebra_one(R), "+
							"            G, "+
							"            polynomial_degree(f) - i), "+
							"        polynomial_algebra_const(R, f(i))))",
						By(
							ring,
							coefficient,
							gForm,
							At(
								FormProduct,
								b.Term("R"),
								n,
								b.TermAs[Nat]("d * (polynomial_degree(f) - i)"),
								b.TermAs[Nat]("0"),
								power,
								constant),
							At(FormPower, b.Term("R"), n, d, G, complement),
							At(FormConstant, b.Term("R"), n, f.Apply(i))))
					product := b.Have(
						"and its product with F^i one of degree d·(m − i) + 0 + d·i",
						"homogeneous_polynomial(R, "+
							"    n, "+
							"    d * (polynomial_degree(f) - i) + 0 + d * i, "+
							"    polynomial_algebra_mul(R, "+
							"        polynomial_algebra_mul(R, "+
							"            monoid_pow(polynomial_algebra_mul(R), "+
							"                polynomial_algebra_one(R), "+
							"                G, "+
							"                polynomial_degree(f) - i), "+
							"            polynomial_algebra_const(R, f(i))), "+
							"        monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), F, i)))",
						By(
							ring,
							fForm,
							leading,
							At(FormProduct, b.Term("R"),
								n,
								b.TermAs[Nat]("d * (polynomial_degree(f) - i) + 0"),
								b.TermAs[Nat]("d * i"),
								b.TermAs[Fun[Fun[Nat, Nat], A]](
									"polynomial_algebra_mul(R, "+
										"    monoid_pow(polynomial_algebra_mul(R), "+
										"        polynomial_algebra_one(R), "+
										"        G, "+
										"        polynomial_degree(f) - i), "+
										"    polynomial_algebra_const(R, f(i)))"),
								b.TermAs[Fun[Fun[Nat, Nat], A]](
									"monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), F, i)")),
							At(FormPower, b.Term("R"), n, d, F, i)))
					b.Show(
						"which is d·m",
						By(degree, product))
				}))
			monoid := a.Have(
				"the forms of degree d·m are closed under sums",
				"comm_monoid_on( "+
					"    {P:((num → num) → A) | homogeneous_polynomial(R, n, d * polynomial_degree(f), P)}, "+
					"    fun_add, "+
					"    fun_zero)",
				By(ring, Read(FormsAdditive, ring)))
			support := a.TermAs[Set[Nat]]("fun_support(fun_zero, «homogenized»)")
			within := a.Have(
				"the homogenized coefficients vanish past m",
				"fun_support(fun_zero, «homogenized») ⊆ {i:num | i ≤ polynomial_degree(f)}",
				BySets())
			finite := a.Have(
				"so they are nonzero at finitely many indices",
				"finite(fun_support(fun_zero, «homogenized»))",
				By(
					within,
					num_segment.FiniteBelow.At(a.TermAs[Nat]("polynomial_degree(f)")),
					finite_set.FiniteSubset))
			summands := a.Have(
				"each nonzero term of the value at F is a form of degree d·m",
				Statement{
					Binders:    "∀i:num.",
					Hypotheses: []string{"i ∈ fun_support(fun_zero, «homogenized»)"},
					Conclusion: "homogeneous_polynomial(R, " +
						"    n, " +
						"    d * polynomial_degree(f), " +
						"    polynomial_algebra_mul(R, " +
						"        «homogenized»(i), " +
						"        monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), F, i)))",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					nonzero := b.Simplified(b.Assume(), Fwd(functions.InFunSupport))
					b.Cases(b.TermAs[Bool]("i ≤ polynomial_degree(f)"))
					b.When(
						"up to m the coefficient is G^(m−i)·f(i)",
						func(c *Argument, le Fact) {
							c.Show(
								"and the term is a form of degree d·m",
								By(terms.At(i), le))
						})
					b.Otherwise(
						"past m the coefficient is zero",
						func(c *Argument, gt Fact) {
							c.Show(
								"against its being nonzero",
								By(gt, nonzero))
						})
				}))
			a.Show(
				"the value at F is the sum of its nonzero terms, all forms of degree d·m",
				Simp(Fwd(polynomial_evaluation.PolynomialEvalDef)),
				By(
					finite,
					summands,
					module.ModuleSumInMonoid.Read(monoid).At(
						support,
						a.TermAs[Fun[Nat, Fun[Fun[Nat, Nat], A]]](
							"λi:num. "+
								"    polynomial_algebra_mul(R, "+
								"        «homogenized»(i), "+
								"        monoid_pow(polynomial_algebra_mul(R), polynomial_algebra_one(R), F, i))"))))
		}),
})}

// EulerIdentity — a form P of degree d over a subset k of a commutative
// ring R satisfies Σ xᵢ·∂P/∂Xᵢ(x) = d·P(x) at every point x of R:
// xᵢ·∂ᵢP(x) is the sum over the monomials m of P of
// m(i)·P(m)·x^m, the sums over i and over m swap, and for each m the
// numerals m(i) add up to the numeral of the degree of m, which is d.
var EulerIdentity = eulerIdentityThm{family.Add(registry.ProofEntry{
	Name: "EulerIdentity",
	Reading: "Homogeneity makes every monomial's exponents sum to d; the coordinates up " +
		"to n must lie in R's carrier for the arithmetic, and those past n are not read. " +
		"Nothing is divided: k need only lie in R's carrier, and R need not be a field.",
	Key: "prop_f2a1e74b7257b18b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀n d:num. ∀P:((num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"k ⊆ R.carrier",
			"homogeneous_polynomial(restrict_ring(R, k), n, d, P)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ R.carrier",
		},
		Conclusion: "module_sum(R.add, " +
			"    R.zero, " +
			"    {i:num | i ≤ n}, " +
			"    λi:num. " +
			"        x(i) * " +
			"        polynomial_algebra_eval(restrict_ring(R, k), " +
			"            R, " +
			"            (λa:A. a), " +
			"            x, " +
			"            polynomial_algebra_partial(restrict_ring(R, k), i, P))) = " +
			"monoid_pow(R.add, R.zero, R.one, d) * " +
			"polynomial_algebra_eval(restrict_ring(R, k), R, (λa:A. a), x, P)",
		Abbrev: Abbrev{
			{Name: "term", Text: "λm:(num → num). P(m) * monomial_eval(R, x, m)"},
			{Name: "weighted", Text: "λi:num. λm:(num → num). " +
				"    monoid_pow(R.add, R.zero, R.one, m(i)) * «term»(m)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			x *Arrow[Nat, A],
			coefficients, homogeneous, coordinates Fact,
		) {
			regular := module.RegularModuleOn.Read(ring)
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			support := a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(R.zero, P)")
			term := a.TermAs[Fun[Fun[Nat, Nat], A]]("«term»")
			add := a.TermAs[Op[A]]("R.add")
			zero := a.TermAs[A]("R.zero")
			degree := a.TermAs[A]("monoid_pow(R.add, R.zero, R.one, d)")
			variablesFinite := num_segment.FiniteBelow.At(n)
			isPolynomial := FormPolynomial.Read(homogeneous)
			perVariable := a.Have(
				"xᵢ times ∂ᵢP at x is the sum over the monomials m of P of m(i) · P(m) · x^m",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ≤ n",
					},
					Conclusion: "x(i) * " +
						"polynomial_algebra_eval(restrict_ring(R, k), " +
						"    R, " +
						"    λa:A. a, " +
						"    x, " +
						"    polynomial_algebra_partial(restrict_ring(R, k), i, P)) = " +
						"module_sum(R.add, R.zero, fun_support(R.zero, P), «weighted»(i))",
				},
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(
						ring,
						coefficients,
						isPolynomial,
						coordinates,
						At(partial_derivative.PartialEvalTimesVar, R, k, variables, P, x, i))
				}))
			parts := a.Conjuncts(
				a.Simplified(isPolynomial.AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"P is nonzero at finitely many monomials",
				"every monomial where P is nonzero is a monomial of the variables up to n",
				"every coefficient of P lies in k")
			inclusion := a.Unfolded(coefficients, set_basic.SubsetDef)
			terms := a.Have(
				"at a monomial where P is nonzero its term lies in R",
				"∀m:(num → num). m ∈ fun_support(R.zero, P) ⇒ P(m) * monomial_eval(R, x, m) ∈ R.carrier",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					nonzero := b.Assume()
					monomial := b.Have(
						"P vanishing off the monomials of the variables up to n, m is one",
						"m ∈ monomials({i:num | i ≤ n})",
						By(nonzero, b.Unfolded(parts[1], set_basic.SubsetDef).At(m)))
					b.Show(
						"so m evaluates in R, and P(m) lies in k",
						By(
							ring,
							coordinates,
							inclusion,
							parts[2],
							At(polynomial_algebra_evaluation.MonomialEvalIn, R, variables, x, m),
							monomial,
							comm_ring.MulIn.Read(ring)))
				}))
			numerals := a.Have(
				"every numeral lies in R",
				"∀j:num. monoid_pow(R.add, R.zero, R.one, j) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
			degrees := a.Have(
				"the numerals of the exponents of a monomial of P add up to the numeral of d",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"P(m) ≠ R.zero"},
					Conclusion: "module_sum(R.add, " +
						"    R.zero, " +
						"    {i:num | i ≤ n}, " +
						"    λi:num. monoid_pow(R.add, R.zero, R.one, m(i))) = " +
						"monoid_pow(R.add, R.zero, R.one, d)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					nonzero := b.Assume()
					b.Show(
						"the exponents of m add up to d, and the numeral of a finite sum is the sum of the numerals",
						By(
							nonzero,
							FormDegree.Read(homogeneous).At(m),
							variablesFinite,
							Read(module.NatSumNumeral, ring).At(variables, m)))
				}))
			perMonomial := a.Have(
				"at each monomial of P the weighted terms add up over the variables to d · P(m) · x^m",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(R.zero, P)"},
					Conclusion: "module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. «weighted»(i, m)) = " +
						"monoid_pow(R.add, R.zero, R.one, d) * «term»(m)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					inSupport := b.Assume()
					b.Show(
						"the term factors out of the sum, leaving the numerals of the exponents",
						By(
							inSupport,
							degrees.At(m),
							terms.At(m),
							numerals,
							variablesFinite,
							module.ModuleSumSmulRight.Read(regular).AsFact().At(
								variables,
								b.TermAs[Fun[Nat, A]]("λi:num. monoid_pow(R.add, R.zero, R.one, m(i))"),
								b.TermAs[A]("«term»(m)"))))
				}))
			weightedIn := a.Have(
				"the weighted terms lie in R",
				Statement{
					Binders: "∀i:num. ∀m:(num → num).",
					Hypotheses: []string{
						"i ∈ {i:num | i ≤ n}",
						"m ∈ fun_support(R.zero, P)",
					},
					Conclusion: "«weighted»(i, m) ∈ R.carrier",
				},
				By(numerals, terms, comm_ring.MulIn.Read(ring)))
			a.Show(
				"so the sum of xᵢ · ∂ᵢP(x) is d · P(x)",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i ≤ n}, "+
								"    λi:num. module_sum(R.add, R.zero, fun_support(R.zero, P), «weighted»(i)))"),
						"each xᵢ · ∂ᵢP(x) is its sum over the monomials of P",
						By(
							perVariable,
							module.ModuleSumCongruence.At(
								add,
								zero,
								variables,
								a.TermAs[Fun[Nat, A]](
									"λi:num. "+
										"    x(i) * "+
										"    polynomial_algebra_eval(restrict_ring(R, k), "+
										"        R, "+
										"        (λa:A. a), "+
										"        x, "+
										"        polynomial_algebra_partial(restrict_ring(R, k), i, P))"),
								a.TermAs[Fun[Nat, A]](
									"λi:num. module_sum(R.add, R.zero, fun_support(R.zero, P), «weighted»(i))")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    fun_support(R.zero, P), "+
								"    λm:(num → num). module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. «weighted»(i, m)))"),
						"the two finite sums swap",
						By(
							variablesFinite,
							parts[0],
							weightedIn,
							module.ModuleSumSwap.Read(regular).At(
								variables, support, a.TermAs[Fun2[Nat, Fun[Nat, Nat], A]]("«weighted»")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    fun_support(R.zero, P), "+
								"    λm:(num → num). monoid_pow(R.add, R.zero, R.one, d) * «term»(m))"),
						"at each monomial the exponents add up to the degree d",
						By(
							perMonomial,
							module.ModuleSumCongruence.At(
								add,
								zero,
								support,
								a.TermAs[Fun[Fun[Nat, Nat], A]](
									"λm:(num → num). module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. «weighted»(i, m))"),
								a.TermAs[Fun[Fun[Nat, Nat], A]](
									"λm:(num → num). monoid_pow(R.add, R.zero, R.one, d) * «term»(m)")))),
					Leg(
						a.TermAs[A](
							"monoid_pow(R.add, R.zero, R.one, d) * module_sum(R.add, R.zero, fun_support(R.zero, P), «term»)"),
						"the numeral of d factors out of the finite sum",
						By(
							parts[0],
							numerals,
							terms,
							module.ModuleSumSmul.Read(regular).AsFact().At(support, degree, term))),
					FinalLeg(
						"and the sum over the monomials of P is its value at x",
						By(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef.At(
							a.TermAs[RingOps[A]]("restrict_ring(R, k)"),
							R,
							a.TermAs[Fun[A, A]]("λa:A. a"),
							x,
							P)))))
		}),
})}

// GradientCoordinateVector — the gradient of a polynomial P over k at a
// point y of M, the values at y of the partials of P up to n and zero past
// n, is a coordinate vector: each partial is a polynomial over k, so its
// value at y lies in M, and the gradient is zero off the finitely many
// indices up to n.
var GradientCoordinateVector = gradientCoordinateVectorThm{family.Add(registry.ProofEntry{
	Name: "GradientCoordinateVector",
	Key:  "prop_9fd79b27b8a00576",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀P:((num → num) → A). ∀y:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"P ∈ polynomial_algebra(«scalars», {i:num | i ≤ n})",
			"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
		},
		Conclusion: "«gradient»(y, P) ∈ free_module_record(field_ring(M), {i:num | i ≤ n}).carrier",
		Abbrev: Abbrev{
			{Name: "gradient", Text: "λy:(num → A). λP:((num → num) → A). λi:num. " +
				"    COND(i ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», i, P)), M.zero)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			y *Arrow[Nat, A],
			subK, polynomial, coordinates Fact,
		) {
			indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			evaluation := a.Have(
				"evaluation at y is a ring map from the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«scalars», field_ring(M), (λa:A. a), y))",
				By(subK, coordinates, EvaluationRingHom.Read(M).At(k, n, y)))
			partialValues := a.Have(
				"so the partials of P take their values in M",
				"∀i:num. «valueAt»(y, polynomial_algebra_partial(«scalars», i, P)) ∈ M.carrier",
				By(
					polynomial,
					subK,
					field.SubfieldCommRing.Read(M).At(k),
					ring_homomorphism.MapIn.Read(evaluation),
					partial_derivative.PolynomialPartialIn,
					polynomial_algebra.PolynomialAlgebraRingDef))
			pastN := a.Have(
				"a coordinate past n is zero",
				"fun_support(M.zero, "+
					"    λl:num. COND(l ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», l, P)), M.zero)) ⊆ "+
					"{i:num | i ≤ n}",
				BySets())
			supported := a.Have(
				"so the gradient is supported on finitely many coordinates, those up to n, with values in M",
				"finite(fun_support(M.zero, "+
					"        λl:num. "+
					"            COND(l ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», l, P)), M.zero))) ∧ "+
					"fun_support(M.zero, "+
					"    λl:num. COND(l ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», l, P)), M.zero)) ⊆ "+
					"{i:num | i ≤ n} ∧ "+
					"(∀l:num. "+
					"    COND(l ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», l, P)), M.zero) ∈ M.carrier)",
				By(
					partialValues,
					pastN,
					num_segment.FiniteBelow.At(n),
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Nat]](
							"fun_support(M.zero, "+
								"    λl:num. COND(l ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», l, P)), M.zero))"),
						indices),
					comm_ring.ZeroIn.Read(field.RingOn.Read(M))))
			a.Show(
				"so it is a coordinate vector",
				By(
					supported,
					function_module.FiniteSuppMember.At(
						a.TermAs[A]("M.zero"),
						a.TermAs[Set[A]]("M.carrier"),
						indices,
						a.TermAs[Fun[Nat, A]]("«gradient»(y, P)"))))
		}),
})}

// GradientScaling — the gradient of a form P of degree d at y scaled by c
// is c^(d − 1) times its gradient at y: each partial of P is a form of
// degree d − 1 (PartialOfForm), so its value scales by c^(d − 1)
// (FormScaling), and past n both gradients are zero.
var GradientScaling = gradientScalingThm{family.Add(registry.ProofEntry{
	Name: "GradientScaling",
	Key:  "prop_d0d0b33e70d2d1aa",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num. ∀P:((num → num) → A). ∀y:(num → A). ∀c:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«scalars», n, d, P)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
			"c ∈ M.carrier",
		},
		Conclusion: "«gradient»(λi:num. y(i) * c, P) = " +
			"fun_smul(monoid_pow(M.mul, M.one, c, d - 1), «gradient»(y, P))",
		Abbrev: Abbrev{
			{Name: "gradient", Text: "λy:(num → A). λP:((num → num) → A). λi:num. " +
				"    COND(i ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», i, P)), M.zero)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			y *Arrow[Nat, A],
			c *Expr[A],
			subK, form, coordinates, cIn Fact,
		) {
			ring := field.RingOn.Read(M)
			coefficients := a.TermAs[RingOps[A]]("«scalars»")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			lowered := a.TermAs[Nat]("d - 1")
			inclusion := a.Have(
				"k includes into M as a ring map",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					subK,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			partials := a.Have(
				"each partial of P is a form of degree d − 1, so its value scales by c^(d − 1)",
				"∀i:num. "+
					"    «valueAt»(λl:num. y(l) * c, polynomial_algebra_partial(«scalars», i, P)) = "+
					"    monoid_pow(M.mul, M.one, c, d - 1) * "+
					"    «valueAt»(y, polynomial_algebra_partial(«scalars», i, P))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"∂ᵢP is a form of degree d − 1",
						By(
							form,
							inclusion,
							coordinates,
							cIn,
							ring_homomorphism.Source.Read(inclusion),
							FormScaling.At(
								coefficients,
								fieldRing,
								identity,
								n,
								lowered,
								y,
								c,
								b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_partial(«scalars», i, P)")),
							PartialOfForm.At(coefficients, n, d, i, P)))
				}))
			a.Show(
				"so the gradient at y·c is c^(d − 1) times the gradient at y, past n both being zero",
				Funext(),
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(
						partials.At(i),
						cIn,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(c, lowered),
						comm_ring.MulRightZeroOn.Read(ring).AsFact().At(a.TermAs[A]("monoid_pow(M.mul, M.one, c, d - 1)")),
						function_module.FunSmulDef)
				}))
		}),
})}

// EulerGradientKernel — at a zero b of a form P, the gradient of P lies in
// the kernel of the linear form v ↦ Σᵢ b(i)·v(i): that form at the gradient
// is the sum Σᵢ b(i)·∂ᵢP(b) over the indices up to n, which is d·P(b) by
// Euler's identity, and P(b) = 0.
var EulerGradientKernel = eulerGradientKernelThm{family.Add(registry.ProofEntry{
	Name: "EulerGradientKernel",
	Key:  "prop_82095223f7a6c6fb",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num. ∀P:((num → num) → A). ∀b:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«scalars», n, d, P)",
			"∀i:num. i ≤ n ⇒ b(i) ∈ M.carrier",
			"«valueAt»(b, P) = M.zero",
		},
		Conclusion: "free_lift(M.zero, M.add, M.zero, M.mul, b, «gradient»(b, P)) = M.zero",
		Abbrev: Abbrev{
			{Name: "gradient", Text: "λy:(num → A). λP:((num → num) → A). λi:num. " +
				"    COND(i ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», i, P)), M.zero)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			P *Arrow[Fun[Nat, Nat], A],
			b *Arrow[Nat, A],
			subK, form, coordinates, vanishes Fact,
		) {
			ring := field.RingOn.Read(M)
			regular := module.RegularModuleOn.Read(ring)
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			rowFacts := a.Conjuncts(
				a.Have(
					"the gradient is a coordinate vector: supported on "+
						"finitely many coordinates, those up to n, with values in M",
					"finite(fun_support(M.zero, "+
						"        λl:num. "+
						"            COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero))) ∧ "+
						"fun_support(M.zero, "+
						"    λl:num. COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero)) ⊆ "+
						"{i:num | i ≤ n} ∧ "+
						"(∀l:num. "+
						"    COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero) ∈ M.carrier)",
					By(
						subK,
						FormPolynomial.Read(form),
						coordinates,
						GradientCoordinateVector.Read(M).At(k, n, P, b),
						function_module.FiniteSuppMember)),
				"the support is finite",
				"it lies among the coordinates up to n",
				"the entries lie in M")
			expand := a.Have(
				"so the form at the gradient is the sum over the coordinates up to n of its entries times b",
				"free_lift(M.zero, M.add, M.zero, M.mul, b, «gradient»(b, P)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    {i:num | i ≤ n}, "+
					"    λl:num. "+
					"        COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero) * b(l))",
				By(
					num_segment.FiniteBelow.At(n),
					rowFacts[1],
					rowFacts[2],
					coordinates,
					free_module.FreeLiftOver.Read(regular).At(indices, b, a.TermAs[Fun[Nat, A]]("«gradient»(b, P)")),
					module_record.RegularModuleDef))
			termwise := a.Have(
				"term by term, the entry and b(l) commuting",
				Statement{
					Binders:    "∀l:num.",
					Hypotheses: []string{"l ∈ {i:num | i ≤ n}"},
					Conclusion: "COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero) * " +
						"b(l) = " +
						"b(l) * «valueAt»(b, polynomial_algebra_partial(«scalars», l, P))",
				},
				Derive(func(c *Argument) {
					l := c.FixAs[Nat]("l")
					lIn := c.Assume()
					entry := c.TermAs[A]("«valueAt»(b, polynomial_algebra_partial(«scalars», l, P))")
					c.Show(
						"up to n the entry is the partial's value",
						By(
							lIn,
							rowFacts[2].At(l),
							coordinates.At(l),
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(entry, b.Apply(l))))
				}))
			reorder := a.Have(
				"which is Euler's sum Σᵢ b(i)·∂ᵢP(b)",
				"module_sum(M.add, "+
					"    M.zero, "+
					"    {i:num | i ≤ n}, "+
					"    λl:num. "+
					"        COND(l ≤ n, «valueAt»(b, polynomial_algebra_partial(«scalars», l, P)), M.zero) * "+
					"        b(l)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    {i:num | i ≤ n}, "+
					"    λi:num. b(i) * «valueAt»(b, polynomial_algebra_partial(«scalars», i, P)))",
				By(termwise, module.ModuleSumCongruence))
			eulerSum := a.Have(
				"Euler's identity: the sum is d times P(b), which is zero",
				"module_sum(M.add, "+
					"    M.zero, "+
					"    {i:num | i ≤ n}, "+
					"    λi:num. b(i) * «valueAt»(b, polynomial_algebra_partial(«scalars», i, P))) = "+
					"M.zero",
				By(
					ring,
					subK,
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("M"), k),
					form,
					coordinates,
					vanishes,
					EulerIdentity.At(fieldRing, k, n, d, P, b),
					comm_ring.MulRightZeroOn.Read(ring).AsFact().At(a.TermAs[A]("monoid_pow(M.add, M.zero, M.one, d)")),
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(a.TermAs[A]("M.one"), d),
					comm_ring.OneIn.Read(ring)))
			a.Show(
				"so the gradient lies in the kernel",
				By(expand, reorder, eulerSum))
		}),
})}

// VariableMinusOneGradient — the gradient of X_j − 1, for j up to n, at a
// point y of M is the coordinate vector of j: the partial of X_j − 1 in X_i
// is the constant δᵢⱼ minus the zero polynomial, whose value at y is δᵢⱼ.
var VariableMinusOneGradient = variableMinusOneGradientThm{family.Add(registry.ProofEntry{
	Name: "VariableMinusOneGradient",
	Key:  "prop_3d6735a232c11544",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n j:num. ∀y:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"j ≤ n",
			"∀i:num. i ≤ n ⇒ y(i) ∈ M.carrier",
		},
		Conclusion: "«gradient»(y, «relation») = delta_at(j)",
		Abbrev: Abbrev{
			{Name: "gradient", Text: "λy:(num → A). λP:((num → num) → A). λi:num. " +
				"    COND(i ≤ n, «valueAt»(y, polynomial_algebra_partial(«scalars», i, P)), M.zero)"},
			{Name: "relation", Text: "«polynomials».sub(polynomial_algebra_var(«scalars», j), " +
				"    polynomial_algebra_const(«scalars», M.one))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n, j *Expr[Nat],
			y *Arrow[Nat, A],
			subK, jIndex, coordinates Fact,
		) {
			ring := field.RingOn.Read(M)
			coefficients := a.TermAs[RingOps[A]]("«scalars»")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			one := a.TermAs[A]("M.one")
			variableJ := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«scalars», j)")
			constantOne := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_const(«scalars», M.one)")
			inclusion := a.Have(
				"k includes into M as a ring map",
				"ring_homomorphism(«scalars», field_ring(M), λa:A. a)",
				By(
					subK,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			coefficientsRing := ring_homomorphism.Source.Read(inclusion)
			_, relationDef := a.LetAs[Fun[Fun[Nat, Nat], A]]("Q", "«relation»")
			oneInK := a.Have(
				"one lies in k",
				"M.one ∈ k",
				By(subK, field.SubfieldOne))
			constants := a.Have(
				"the constants are polynomials",
				"ring_homomorphism(«scalars», «polynomials», polynomial_algebra_const(«scalars»))",
				By(coefficientsRing, polynomial_algebra.PolynomialAlgebraConstHom))
			generatorsIn := a.Have(
				"X_j and one are polynomials over k",
				"polynomial_algebra_var(«scalars», j) ∈ polynomial_algebra(«scalars», {i:num | i ≤ n}) ∧ "+
					"polynomial_algebra_const(«scalars», M.one) ∈ polynomial_algebra(«scalars», {i:num | i ≤ n})",
				By(
					coefficientsRing,
					jIndex,
					oneInK,
					polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, indices, j),
					ring_homomorphism.MapIn.Read(constants).AsFact().At(one),
					polynomial_algebra.PolynomialAlgebraRingDef))
			evaluation := a.Have(
				"evaluation at y is a ring map",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«scalars», field_ring(M), (λa:A. a), y))",
				By(subK, coordinates, EvaluationRingHom.Read(M).At(k, n, y)))
			derivative := a.Have(
				"the partial of X_j − 1 in X_i is the constant δᵢⱼ minus zero",
				"∀i:num. "+
					"    polynomial_algebra_partial(«scalars», i, Q) = "+
					"    «polynomials».sub(polynomial_algebra_const(«scalars», COND(i = j, M.one, M.zero)), fun_zero)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					difference := b.Have(
						"the partial of the difference is the difference of the partials",
						"polynomial_algebra_partial(«scalars», i, «relation») = "+
							"«polynomials».sub( "+
							"    polynomial_algebra_partial(«scalars», i, polynomial_algebra_var(«scalars», j)), "+
							"    polynomial_algebra_partial(«scalars», i, polynomial_algebra_const(«scalars», M.one)))",
						By(
							coefficientsRing,
							generatorsIn,
							At(partial_derivative.PolynomialPartialLinear, coefficients, indices, i, variableJ, constantOne)))
					parts := b.Have(
						"the variable's partial is the constant δᵢⱼ and the constant's is zero",
						"polynomial_algebra_partial(«scalars», i, polynomial_algebra_var(«scalars», j)) = "+
							"polynomial_algebra_const(«scalars», COND(i = j, M.one, M.zero)) ∧ "+
							"polynomial_algebra_partial(«scalars», i, polynomial_algebra_const(«scalars», M.one)) = fun_zero",
						By(
							coefficientsRing,
							oneInK,
							At(partial_derivative.PolynomialPartialVar, coefficients, i, j),
							At(partial_derivative.PolynomialPartialConst, coefficients, i, one)))
					b.Show(
						"so the partial is δᵢⱼ minus zero",
						By(relationDef, difference, parts))
				}))
			polynomialsRing := a.Have(
				"the polynomials over k are a commutative ring",
				"comm_ring_on(«polynomials»)",
				By(coefficientsRing, polynomial_algebra.PolynomialAlgebraCommRingOn))
			zeroPolynomial := a.Have(
				"the zero polynomial is a polynomial, evaluating to zero",
				"fun_zero ∈ «polynomials».carrier ∧ «valueAt»(y, fun_zero) = M.zero",
				By(
					comm_ring.ZeroIn.Read(polynomialsRing),
					ring_homomorphism.MapZero.Read(evaluation),
					polynomial_algebra.PolynomialAlgebraRingDef))
			subtractZero := a.Have(
				"subtracting zero changes nothing",
				"∀z:A. z ∈ M.carrier ⇒ z - M.zero = z",
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					zIn := b.Assume()
					b.Show(
						"a ring identity",
						ByArith(M, zIn))
				}))
			values := a.Have(
				"so the value at y of the partial in X_i is δᵢⱼ",
				"∀i:num. «valueAt»(y, polynomial_algebra_partial(«scalars», i, Q)) = COND(i = j, M.one, M.zero)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					coefficient := b.TermAs[A]("COND(i = j, M.one, M.zero)")
					constant := b.TermAs[Fun[Fun[Nat, Nat], A]](
						"polynomial_algebra_const(«scalars», COND(i = j, M.one, M.zero))")
					coefficientIn := b.Have(
						"δᵢⱼ lies in k",
						"COND(i = j, M.one, M.zero) ∈ k",
						By(oneInK, subK, field.SubfieldZero))
					split := b.Have(
						"the value of the partial is the value of the constant minus that of zero",
						"«valueAt»(y, polynomial_algebra_partial(«scalars», i, Q)) = "+
							"«valueAt»(y, polynomial_algebra_const(«scalars», COND(i = j, M.one, M.zero))) - "+
							"«valueAt»(y, fun_zero)",
						By(
							derivative.At(i),
							coefficientIn,
							ring_homomorphism.MapIn.Read(constants).AsFact().At(coefficient),
							zeroPolynomial,
							ring_homomorphism.MapSub.Read(evaluation).AsFact().At(
								constant, b.TermAs[Fun[Fun[Nat, Nat], A]]("fun_zero"))))
					value := b.Have(
						"a constant evaluates to itself",
						"«valueAt»(y, polynomial_algebra_const(«scalars», COND(i = j, M.one, M.zero))) = "+
							"COND(i = j, M.one, M.zero)",
						By(
							inclusion,
							coefficientIn,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
								coefficients, fieldRing, identity, y, coefficient)))
					b.Show(
						"so it is δᵢⱼ",
						By(
							split,
							value,
							zeroPolynomial,
							subtractZero.At(coefficient),
							b.Have(
								"δᵢⱼ lies in M",
								"COND(i = j, M.one, M.zero) ∈ M.carrier",
								By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))))
				}))
			a.Show(
				"so the gradient is one at j and zero elsewhere, the coordinate vector of j",
				Funext(),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i = j"))
					b.When(
						"at j both are one",
						func(c *Argument, same Fact) {
							c.Show(
								"i is j, at most n, where both are one",
								By(
									same,
									c.Have(
										"so i ≤ n",
										"i ≤ n",
										ByArith(same, jIndex)),
									values.At(i),
									free_module.DeltaAtDef.At(c.TermAs[A]("M.zero"), c.TermAs[A]("M.one"), j, i)))
						})
					b.Otherwise(
						"elsewhere both are zero",
						func(c *Argument, other Fact) {
							c.Show(
								"the gradient's entry is zero",
								By(
									other,
									values.At(i),
									free_module.DeltaAtDef.At(c.TermAs[A]("M.zero"), c.TermAs[A]("M.one"), j, i)))
						})
				}))
		}),
})}
