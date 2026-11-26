// multiplicity.go — the multiplicity of a root: over a domain a root a of
// a nonzero polynomial splits off x − a to its full power, leaving a
// cofactor that no longer vanishes at a; and the derivative of a power of
// x − a times a cofactor, which keeps all but one of the factors x − a.

package polynomial_roots

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RootMultiplicity — over a domain, a root a of a nonzero polynomial p
// splits off the factor x − a to its full multiplicity: p is (x − a)^(m+1)
// times a polynomial s that does not vanish at a, and the roots of p are a
// with the roots of s. Strong induction on the degree: RootFactorization
// splits off one factor, and a quotient that still vanishes at a has lower
// degree, so the hypothesis splits off the rest.
var RootMultiplicity = rootMultiplicityThm{family.Add(registry.ProofEntry{
	Name: "RootMultiplicity",
	Key:  "prop_b2e1180f7c6aa238",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p:(num → A). ∀a:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"p ≠ vec_zero",
			"a ∈ R.carrier",
			"polynomial_eval(p, a) = R.zero",
		},
		Conclusion: "∃m:num. ∃s:(num → A). " +
			"    polynomial_over(R.carrier, s) ∧ " +
			"    polynomial_eval(s, a) ≠ R.zero ∧ " +
			"    p = polynomial_mul(polynomial_pow(«linear»(a), suc(m)), s) ∧ " +
			"    polynomial_roots(R.carrier, p) = insert(a, polynomial_roots(R.carrier, s))",
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		p *Arrow[Nat, A],
		a *Member[A, on.R],
		over, nonzero, root Fact,
	) {
		ring := integral_domain.Ring.Read(domain)
		products := comm_ring.MulMonoidOn.Read(polynomial.PolynomialRingOn.Read(ring))
		linear := arg.TermAs[Fun[Nat, A]]("«linear»(a)")
		line := LinearFactor.Read(ring).At(a)
		split := arg.TermAs[Set[Nat]](
			"λn:num. ∀f:(num → A). " +
				"    polynomial_over(R.carrier, f) ∧ " +
				"    f ≠ vec_zero ∧ " +
				"    polynomial_degree(f) = n ∧ " +
				"    polynomial_eval(f, a) = R.zero ⇒ " +
				"    ∃m:num. ∃s:(num → A). " +
				"        polynomial_over(R.carrier, s) ∧ " +
				"        polynomial_eval(s, a) ≠ R.zero ∧ " +
				"        f = polynomial_mul(polynomial_pow(«linear»(a), suc(m)), s) ∧ " +
				"        polynomial_roots(R.carrier, f) = insert(a, polynomial_roots(R.carrier, s))")
		arg.Show(
			"strong induction on the degree splits x − a off "+
				"every nonzero polynomial vanishing at a, p among them",
			ByInduction(nat_order.StrongInduction.At(
				split, arg.TermAs[Nat]("polynomial_degree(p)")), over, nonzero, root,
				Case(
					"granted the split below degree n, a nonzero polynomial of degree n vanishing at a splits",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						smaller := b.Assume()
						f := b.FixAs[Fun[Nat, A]]("f")
						given := b.Conjuncts(
							b.Assume(),
							"f is over the domain",
							"f is nonzero",
							"f has degree n",
							"f vanishes at a")
						q, reduced := b.UnpackAs[Fun[Nat, A]](
							GroupPremises(given[0], given[1], given[3], RootFactorization.Read(domain).At(f, a)), "q")
						quotient := b.Conjuncts(
							reduced,
							"q is over the domain",
							"q is nonzero",
							"f is x − a times q",
							"the degree drops by one",
							"a is inserted into the roots of q")
						qOver, qNonzero, factor, degreeStep, rootsStep :=
							quotient[0], quotient[1], quotient[2], quotient[3], quotient[4]
						b.Cases(b.TermAs[Bool]("polynomial_eval(q, a) = R.zero"))
						b.When(
							"q still vanishes at a: the split below n takes x − a off q, and one more factor joins the power",
							func(c *Argument, qRoot Fact) {
								lower := c.Have(
									"q has degree below n",
									"polynomial_degree(q) < n",
									ByArith(given[2], degreeStep))
								_, s, deeper := c.Obtain2As[Nat, Fun[Nat, A]](
									"the split below n gives q = (x − a)^(k+1)·s with s not vanishing at a",
									"∃k:num. ∃s:(num → A). "+
										"    polynomial_over(R.carrier, s) ∧ "+
										"    polynomial_eval(s, a) ≠ R.zero ∧ "+
										"    q = polynomial_mul(polynomial_pow(«linear»(a), suc(k)), s) ∧ "+
										"    polynomial_roots(R.carrier, q) = insert(a, polynomial_roots(R.carrier, s))",
									By(smaller.At(c.TermAs[Nat]("polynomial_degree(q)"), q), lower, qOver, qNonzero, qRoot))
								cofactor := c.Conjuncts(
									deeper,
									"s is over the domain",
									"s does not vanish at a",
									"q is (x − a)^(k+1) times s",
									"a is inserted into the roots of s")
								sOver := cofactor[0]
								c.Take(c.TermAs[Nat]("suc(k)"))
								c.Take(s)
								power := c.Have(
									"so f = (x − a)·((x − a)^(k+1)·s) = (x − a)^(k+2)·s",
									"f = polynomial_mul(polynomial_pow(«linear»(a), suc(suc(k))), s)",
									By(
										factor,
										cofactor[2],
										sOver,
										a,
										polynomial.PolynomialPowSuc.Read(ring).At(c.TermAs[Nat]("suc(k)"), linear),
										comm_monoid.AssocOn.Read(products).AsFact().At(
											linear, c.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(a), suc(k))"), s),
										line,
										polynomial.PolynomialPowOver.Read(ring)))
								roots := c.Have(
									"and inserting a into the roots of q, which already hold a, inserts it once",
									"polynomial_roots(R.carrier, f) = insert(a, polynomial_roots(R.carrier, s))",
									By(
										rootsStep,
										cofactor[3],
										set_algebra.InsertInsert.At(c.TermAs[Set[A]]("polynomial_roots(R.carrier, s)"), a)))
								c.Show(
									"s serves, with the exponent one higher",
									By(sOver, cofactor[1], power, roots))
							})
						b.Otherwise(
							"q does not vanish at a: x − a divides f exactly once",
							func(c *Argument, qNotRoot Fact) {
								c.Take(c.TermAs[Nat]("0"))
								c.Take(q)
								once := c.Have(
									"the first power of x − a is x − a",
									"f = polynomial_mul(polynomial_pow(«linear»(a), suc(0)), q)",
									By(
										factor,
										a,
										polynomial.PolynomialPowSuc.Read(ring).At(c.TermAs[Nat]("0"), linear),
										polynomial.PolynomialPowZero.Read(ring).At(linear),
										comm_monoid.RightIdentityOn.Read(products).AsFact().At(linear),
										line))
								c.Show(
									"q serves, with exponent zero",
									By(qOver, qNotRoot, once, rootsStep))
							})
					}))))
	}),
})}

// LinearFactorDerivative — the derivative of x − a is the one polynomial:
// the derivative's coefficient at n is n + 1 times the coefficient of
// x − a at n + 1, which is one at n = 0 and zero past it.
var LinearFactorDerivative = linearFactorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LinearFactorDerivative",
	Key:  "prop_61e18f8e00b7659",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀a:A.",
		Hypotheses: []string{"a ∈ R.carrier"},
		Conclusion: "polynomial_derivative(«linear»(a)) = basis_vector(0)",
	}, func(arg *Argument, ring comm_ring.CommRingFact[on.R], a *Member[A, on.R]) {
		arg.Do(Funext())
		arg.FixAs[Nat]("n")
		arg.Do(Simp(
			Fwd(polynomial.PolynomialDerivativeDef),
			Fwd(vec_space.VecSubDef),
			Fwd(vec_space.VecScalarMulDef),
			Fwd(vec_space.BasisVectorDef)))
		arg.Cases(arg.TermAs[Bool]("n = 0"))
		arg.When(
			"the constant coefficient of the derivative is one times the coefficient one of x",
			func(c *Argument, zero Fact) {
				c.Show(
					"one times one is one",
					zero.Subst(),
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					ByArith(ring, a))
			})
		arg.Otherwise(
			"past the constant coefficient the derivative vanishes",
			func(c *Argument, later Fact) {
				c.Show(
					"x − a has no coefficient past the first",
					ByArith(ring, later, a))
			})
	}),
})}

// LinearPowerDerivative — the derivative of (x − a)^(m+1)·g is
// (x − a)^m·((m + 1)·g + (x − a)·g'): the product rule, then the power rule
// with (x − a)' = 1, and ring arithmetic among polynomials once the multiple
// (m + 1)·h is read as h times the constant polynomial m + 1.
var LinearPowerDerivative = linearPowerDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LinearPowerDerivative",
	Key:  "prop_26652823f96fabf1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:num. ∀a:A. ∀g:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(a), suc(m)), g)) = " +
			"polynomial_mul(polynomial_pow(«linear»(a), m), " +
			"    monoid_pow(R.add, R.zero, R.one, suc(m)) • g + " +
			"    polynomial_mul(«linear»(a), polynomial_derivative(g)))",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "{p:(num → A) | polynomial_over(R.carrier, p)}"},
		},
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		m *Expr[Nat],
		a *Member[A, on.R],
		g *Arrow[Nat, A],
		gOver Fact,
	) {
		linear := arg.TermAs[Fun[Nat, A]]("«linear»(a)")
		line := LinearFactor.Read(ring).At(a)
		powerOver := polynomial.PolynomialPowOver.Read(ring)
		productRule := arg.Have(
			"by the product rule",
			"polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(a), suc(m)), g)) = "+
				"polynomial_mul(polynomial_derivative(polynomial_pow(«linear»(a), suc(m))), g) + "+
				"polynomial_mul(polynomial_pow(«linear»(a), suc(m)), polynomial_derivative(g))",
			By(
				a,
				gOver,
				polynomial.DerivativeMul.Read(ring).At(
					arg.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(a), suc(m))"), g),
				powerOver.At(arg.TermAs[Nat]("suc(m)"), linear),
				line,
				polynomial.PolynomialOverDef))
		powerRule := arg.Have(
			"by the power rule, x − a having derivative one",
			"polynomial_derivative(polynomial_pow(«linear»(a), suc(m))) = "+
				"monoid_pow(R.add, R.zero, R.one, suc(m)) • "+
				"polynomial_mul(polynomial_pow(«linear»(a), m), basis_vector(0))",
			By(
				LinearFactorDerivative.Read(ring).At(a),
				polynomial.DerivativePow.Read(ring).At(m, linear),
				line))
		multiple := comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).At(
			arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring)), arg.TermAs[Nat]("suc(m)"))
		constant := arg.Conjuncts(
			arg.Have(
				"a multiple (m + 1)·h is h times the constant polynomial m + 1",
				"monoid_pow(R.add, R.zero, R.one, suc(m)) • "+
					"polynomial_mul(polynomial_pow(«linear»(a), m), basis_vector(0)) = "+
					"polynomial_mul(polynomial_mul(polynomial_pow(«linear»(a), m), basis_vector(0)), "+
					"    monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0)) ∧ "+
					"monoid_pow(R.add, R.zero, R.one, suc(m)) • g = "+
					"polynomial_mul(g, monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0))",
				By(
					a,
					multiple,
					gOver,
					polynomial.PolynomialMulConstant.Read(ring).AsFact().At(
						arg.TermAs[A]("monoid_pow(R.add, R.zero, R.one, suc(m))"),
						arg.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_pow(«linear»(a), m), basis_vector(0))")),
					polynomial.PolynomialMulConstant.Read(ring).AsFact().At(
						arg.TermAs[A]("monoid_pow(R.add, R.zero, R.one, suc(m))"), g),
					polynomial.PolynomialMulOver.Read(ring).At(
						arg.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(a), m)"),
						arg.TermAs[Fun[Nat, A]]("basis_vector(0)")),
					powerOver.At(m, linear),
					line,
					polynomial.BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("0")))),
			"for the multiple of (x − a)^m",
			"for the multiple of g")
		members := arg.Have(
			"x, a, x − a, (x − a)^m, the constants and g and g' lie in the polynomial ring",
			"basis_vector(1) ∈ «polynomials» ∧ "+
				"a • basis_vector(0) ∈ «polynomials» ∧ "+
				"«linear»(a) ∈ «polynomials» ∧ "+
				"polynomial_pow(«linear»(a), m) ∈ «polynomials» ∧ "+
				"basis_vector(0) ∈ «polynomials» ∧ "+
				"monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0) ∈ «polynomials» ∧ "+
				"g ∈ «polynomials» ∧ "+
				"polynomial_derivative(g) ∈ «polynomials»",
			BySets(
				a,
				multiple,
				gOver,
				line,
				powerOver.At(m, linear),
				polynomial.BasisVectorOver.Read(ring),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
				polynomial.DerivativeOverCarrier.Read(ring).At(g)))
		arg.Show(
			"so the derivative is (x − a)^m times (m + 1)·g + (x − a)·g', by ring arithmetic among polynomials",
			productRule.Rw(),
			powerRule.Rw(),
			constant[0].Rw(),
			constant[1].Rw(),
			polynomial.PolynomialPowSuc.Read(ring).At(m, linear).Rw(),
			ByArith(polynomial.PolynomialRingOn.Read(ring), members))
	}),
})}

// LinearPowersDerivative — the derivative of (x − a)^(m+1)·(x − b)^(n+1)·s
// keeps the factor (x − a)^m·(x − b)^n, with the cofactor
// (m + 1)·(x − b)·s + (x − a)·((n + 1)·s + (x − b)·s'): LinearPowerDerivative
// at a and then at b, and ring arithmetic among polynomials once the
// multiples by m + 1 are read as products with the constant polynomial.
var LinearPowersDerivative = linearPowersDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LinearPowersDerivative",
	Key:  "prop_ad58aaa66e5fcdc8",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m n:num. ∀a b:A. ∀s:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"polynomial_over(R.carrier, s)",
		},
		Conclusion: "polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(a), suc(m)), " +
			"        polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s))) = " +
			"polynomial_mul(polynomial_pow(«linear»(a), m), " +
			"    polynomial_mul(polynomial_pow(«linear»(b), n), " +
			"        monoid_pow(R.add, R.zero, R.one, suc(m)) • polynomial_mul(«linear»(b), s) + " +
			"        polynomial_mul(«linear»(a), " +
			"            monoid_pow(R.add, R.zero, R.one, suc(n)) • s + " +
			"            polynomial_mul(«linear»(b), polynomial_derivative(s)))))",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "{p:(num → A) | polynomial_over(R.carrier, p)}"},
		},
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		m, n *Expr[Nat],
		a, b *Member[A, on.R],
		s *Arrow[Nat, A],
		sOver Fact,
	) {
		lineA := LinearFactor.Read(ring).At(a)
		lineB := LinearFactor.Read(ring).At(b)
		linearA := arg.TermAs[Fun[Nat, A]]("«linear»(a)")
		linearB := arg.TermAs[Fun[Nat, A]]("«linear»(b)")
		powerOver := polynomial.PolynomialPowOver.Read(ring)
		inner := arg.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s)")
		outer := arg.Have(
			"x − a comes off first, the cofactor being (x − b)^(n+1)·s",
			"polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(a), suc(m)), "+
				"        polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s))) = "+
				"polynomial_mul(polynomial_pow(«linear»(a), m), "+
				"    monoid_pow(R.add, R.zero, R.one, suc(m)) • "+
				"    polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s) + "+
				"    polynomial_mul(«linear»(a), "+
				"        polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s))))",
			By(
				LinearPowerDerivative.Read(ring).At(m, a, inner),
				polynomial.PolynomialMulOver.Read(ring).At(
					arg.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(b), suc(n))"), s),
				powerOver.At(arg.TermAs[Nat]("suc(n)"), linearB),
				lineB,
				sOver))
		next := arg.Have(
			"then x − b comes off the derivative of (x − b)^(n+1)·s",
			"polynomial_derivative(polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s)) = "+
				"polynomial_mul(polynomial_pow(«linear»(b), n), "+
				"    monoid_pow(R.add, R.zero, R.one, suc(n)) • s + "+
				"    polynomial_mul(«linear»(b), polynomial_derivative(s)))",
			By(sOver, LinearPowerDerivative.Read(ring).At(n, b, s)))
		one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
		additive := comm_ring.AddMonoidOn.Read(ring)
		multipleM := comm_monoid.PowIn.Read(additive).At(one, arg.TermAs[Nat]("suc(m)"))
		multipleN := comm_monoid.PowIn.Read(additive).At(one, arg.TermAs[Nat]("suc(n)"))
		constant := arg.Conjuncts(
			arg.Have(
				"a multiple by m + 1 is a product with the constant polynomial m + 1",
				"monoid_pow(R.add, R.zero, R.one, suc(m)) • "+
					"polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s) = "+
					"polynomial_mul(polynomial_mul(polynomial_pow(«linear»(b), suc(n)), s), "+
					"    monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0)) ∧ "+
					"monoid_pow(R.add, R.zero, R.one, suc(m)) • polynomial_mul(«linear»(b), s) = "+
					"polynomial_mul(polynomial_mul(«linear»(b), s), "+
					"    monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0))",
				By(
					b,
					multipleM,
					sOver,
					polynomial.PolynomialMulConstant.Read(ring).AsFact().At(
						arg.TermAs[A]("monoid_pow(R.add, R.zero, R.one, suc(m))"), inner),
					polynomial.PolynomialMulConstant.Read(ring).AsFact().At(
						arg.TermAs[A]("monoid_pow(R.add, R.zero, R.one, suc(m))"),
						arg.TermAs[Fun[Nat, A]]("polynomial_mul(«linear»(b), s)")),
					polynomial.PolynomialMulOver.Read(ring),
					powerOver.At(arg.TermAs[Nat]("suc(n)"), linearB),
					lineB)),
			"for the multiple of (x − b)^(n+1)·s",
			"for the multiple of (x − b)·s")
		members := arg.Have(
			"x, the constants and the factors, s and s' lie in the polynomial ring",
			"basis_vector(1) ∈ «polynomials» ∧ "+
				"a • basis_vector(0) ∈ «polynomials» ∧ "+
				"b • basis_vector(0) ∈ «polynomials» ∧ "+
				"«linear»(a) ∈ «polynomials» ∧ "+
				"«linear»(b) ∈ «polynomials» ∧ "+
				"polynomial_pow(«linear»(a), m) ∈ «polynomials» ∧ "+
				"polynomial_pow(«linear»(b), n) ∈ «polynomials» ∧ "+
				"s ∈ «polynomials» ∧ "+
				"polynomial_derivative(s) ∈ «polynomials» ∧ "+
				"monoid_pow(R.add, R.zero, R.one, suc(m)) • basis_vector(0) ∈ «polynomials» ∧ "+
				"monoid_pow(R.add, R.zero, R.one, suc(n)) • s ∈ «polynomials»",
			BySets(
				a,
				b,
				multipleM,
				multipleN,
				sOver,
				lineA,
				lineB,
				powerOver.At(m, linearA),
				powerOver.At(n, linearB),
				polynomial.BasisVectorOver.Read(ring),
				polynomial.DerivativeOverCarrier.Read(ring).At(s),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
		arg.Show(
			"(x − b)^(n+1) is (x − b)·(x − b)^n, and ring "+
				"arithmetic among polynomials gathers (x − a)^m·(x − b)^n",
			outer.Rw(),
			next.Rw(),
			constant[0].Rw(),
			constant[1].Rw(),
			polynomial.PolynomialPowSuc.Read(ring).At(n, linearB).Rw(),
			ByArith(polynomial.PolynomialRingOn.Read(ring), members))
	}),
})}
