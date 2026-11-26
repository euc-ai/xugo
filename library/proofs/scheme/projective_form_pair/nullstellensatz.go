// nullstellensatz.go — the graded Nullstellensatz: subspaces X(d) of the
// forms of degree d over k, from some degree on closed under multiplication
// by the variables, of bounded codimension and with no common zero in
// projective space over an algebraically closed M, hold every form of large
// degree. When every variable has a power in X, those powers generate every
// form of large degree. When some variable has none, a prime of the
// polynomials over k holds the ideal X generates, whose forms of large degree
// are the X(d), and misses that variable; the codimension bound makes the
// prime's generic point algebraic over k, and its image in M is a common
// zero.

package projective_form_pair

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_generic_point"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// VariablePowersGenerate — subspaces X(d) of the forms of degree d over k,
// from degree N₀ on closed under multiplication by the variables, in which
// every variable up to n has a power, hold every form of large degree. The
// powers raise to one common exponent e, the sum of the exponents found; a
// monomial of degree at least (n + 1)·e has an exponent at least e somewhere,
// so it is a power Xᵢ^e raised by variables one at a time and lies in X; and a
// form is the sum of its coefficients times its monomials.
var VariablePowersGenerate = variablePowersGenerateThm{family.Add(registry.ProofEntry{
	Name: "VariablePowersGenerate",
	Key:  "prop_10350500c592dc61",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n N₀:num. ∀X:(num → set((num → num) → A)).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀d:num. N₀ ≤ d ⇒ submodule(«hilbertCoefficients», «formSpace»(d), X(d))",
			"∀d i:num. ∀P:((num → num) → A). " +
				"    N₀ ≤ d ∧ i ≤ n ∧ P ∈ X(d) ⇒ " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», i), " +
				"        P) ∈ " +
				"    X(d + 1)",
			"∀i:num. i ≤ n ⇒ ∃a:num. N₀ ≤ a ∧ «power»(i, a) ∈ X(a)",
		},
		Conclusion: "∃N:num. ∀d:num. N ≤ d ⇒ «forms»(d) ⊆ X(d)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "power", Text: "λl:num. λs:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», l), " +
				"        s)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, N0 *Expr[Nat],
		X *Arrow2[Nat, _Polynomial, Bool],
		subK, subspace, closure, powers Fact,
	) {
		type monomial = Fun[Nat, Nat]
		K := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		variables := a.TermAs[Set[Nat]]("{j:num | j ≤ n}")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		unit := a.Have(
			"the exponent monomial_var(l) is zero off l",
			"∀l x:num. x = l ∨ monomial_var(l, x) = 0",
			By(polynomial_algebra.MonomialVarValues))
		shift := a.Have(
			"raising the exponent of the variable l by one multiplies the monomial by X_l",
			Statement{
				Binders:    "∀w:(num → num). ∀l:num.",
				Hypotheses: []string{"finite_support(0, w)"},
				Conclusion: "delta_at(λx:num. w(x) + monomial_var(l, x)) = " +
					"polynomial_algebra_mul(«hilbertCoefficients», " +
					"    polynomial_algebra_var(«hilbertCoefficients», l), " +
					"    delta_at(w))",
			},
			Derive(func(b *Argument) {
				w := b.FixAs[monomial]("w")
				l := b.FixAs[Nat]("l")
				finite := b.Assume()
				variableFinite := b.Have(
					"the exponent of X_l, a monomial of the variables, is finitely supported",
					"finite_support(0, monomial_var(l))",
					BySets(
						polynomial_algebra.MonomialsDef,
						polynomial_algebra.MonomialVarIn.At(b.TermAs[Set[Nat]]("𝕌⟨A:num⟩"), l)))
				swap := b.Have(
					"exponents add in either order",
					"(λx:num. monomial_var(l, x) + w(x)) = (λx:num. w(x) + monomial_var(l, x))",
					Funext(),
					ByArith())
				b.Show(
					"X_l is the generator at the exponent of X_l, and generators multiply by adding their exponents",
					Simp(Fwd(polynomial_algebra.PolynomialAlgebraVarDef)),
					By(
						scalars,
						finite,
						variableFinite,
						swap,
						polynomial_algebra.PolynomialAlgebraGeneratorMul.At(K, b.TermAs[monomial]("monomial_var(l)"), w)))
			}))
		powerMonomial := a.Have(
			"the power X_i^t is the monomial with exponent t at i",
			"∀i t:num. «power»(i, t) = delta_at(λx:num. t * monomial_var(i, x))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Induct("t")
				b.Base(
					"X_i^0 is the polynomial one, the monomial with no exponent",
					Simp(
						Fwd(nat_arith.MulLeftZeroClause),
						Fwd(comm_monoid.MonoidPowDef),
						Fwd(polynomial_algebra.PolynomialAlgebraOneDef)),
					Refl())
				b.Step(
					"X_i^(t + 1) is X_i times X_i^t, which raises the exponent at i by one",
					func(c *Argument, ih Fact) {
						exponent := c.TermAs[monomial]("λx:num. t * monomial_var(i, x)")
						atI := c.Have(
							"t·monomial_var(i) is nonzero only at i",
							"fun_support(0, λx:num. t * monomial_var(i, x)) ⊆ {i}",
							Derive(func(d *Argument) {
								pointwise := d.Have(
									"off i the exponent is t·0",
									"∀x:num. t * monomial_var(i, x) ≠ 0 ⇒ x = i",
									Derive(func(f *Argument) {
										x := f.FixAs[Nat]("x")
										f.Show(
											"monomial_var(i, x) is zero unless x is i",
											By(unit.At(i, x), nat_arith.MulZero))
									}))
								d.Show(
									"so its support lies in {i}",
									BySets(pointwise))
							}))
						finite := c.Have(
							"so it is finitely supported",
							"finite_support(0, λx:num. t * monomial_var(i, x))",
							By(
								atI,
								function_module.FiniteSupportDef,
								finite_set.FiniteSing.At(i),
								finite_set.FiniteSubset.At(
									c.TermAs[Set[Nat]]("fun_support(0, λx:num. t * monomial_var(i, x))"), c.TermAs[Set[Nat]]("{i}"))))
						c.Show(
							"one more factor X_i raises the exponent t at i to t + 1",
							Simp(Fwd(nat_arith.Mul), Fwd(comm_monoid.MonoidPowDef)),
							By(ih, finite, shift.At(exponent, i)))
					})
			}))
		_, exponents := a.ObtainAs[monomial](
			"choose for each variable up to n an exponent p(i) with X_i^p(i) in X",
			"∃p:(num → num). ∀i:num. i ≤ n ⇒ N₀ ≤ p(i) ∧ «power»(i, p(i)) ∈ X(p(i))",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[monomial]("λi:num. εa:num. N₀ ≤ a ∧ «power»(i, a) ∈ X(a)"))
				b.Show(
					"the chosen exponent has the property each variable's power has",
					By(powers))
			}))
		raise := a.Have(
			"a power of X_i in X stays in X when raised: X(c) ∋ X_i^c gives X(t) ∋ X_i^t for t ≥ c",
			"∀t i c:num. i ≤ n ∧ N₀ ≤ c ∧ c ≤ t ∧ «power»(i, c) ∈ X(c) ⇒ «power»(i, t) ∈ X(t)",
			Derive(func(b *Argument) {
				b.Induct("t")
				b.Base(
					"c ≤ 0 makes c zero",
					By(Normalized, nat_order.LessEq))
				b.Step(
					"from t to t + 1 one more factor X_i is a variable times a member of X(t)",
					func(c *Argument, ih Fact) {
						i := c.FixAs[Nat]("i")
						base := c.FixAs[Nat]("c")
						t := c.TermAs[Nat]("t")
						given := c.Assume()
						c.Cases(c.TermAs[Bool]("c ≤ t"))
						c.When(
							"with c ≤ t, X_i^t lies in X(t) and X_i^(t + 1) is X_i times it",
							func(d *Argument, below Fact) {
								d.Show(
									"a variable times a member of X(t) lies in X(t + 1)",
									By(
										below,
										given,
										ih.At(i, base),
										closure.At(t, i, d.TermAs[_Polynomial]("«power»(i, t)")),
										comm_monoid.MonoidPowDef,
										nat_arith.Add1.At(t),
										nat_order.LessEqTrans.At(N0, base, t)))
							})
						c.Otherwise(
							"otherwise c is t + 1 itself",
							func(d *Argument, notBelow Fact) {
								d.Show(
									"and X_i^(t + 1) is the power given",
									By(Normalized, notBelow, given, nat_order.LessEq))
							})
					})
			}))
		e, eDef := a.LetAs[Nat]("e", "sum({j:num | j ≤ n}, p)")
		bounded := a.Have(
			"each chosen exponent is at most their sum e",
			"∀i:num. i ≤ n ⇒ p(i) ≤ e",
			By(eDef, At(nat_sum.TermLeSum, a.TermAs[monomial]("p"), variables), num_segment.FiniteBelow.At(n)))
		zero := a.TermAs[Nat]("0")
		past := a.Have(
			"e is at least the exponent of X₀, which is at least N₀",
			"N₀ ≤ e",
			ByArith(bounded.At(zero), exponents.At(zero)))
		common := a.Have(
			"so every variable up to n has its e-th power in X",
			"∀i:num. i ≤ n ⇒ «power»(i, e) ∈ X(e)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inRange := b.Assume()
				b.Show(
					"X_i^p(i) raises to X_i^e, p(i) being at most e",
					By(inRange, bounded.At(i), exponents.At(i), raise.At(e, i, b.TermAs[Nat]("p(i)"))))
			}))
		finitelySupported := a.Have(
			"an exponent vanishing past n is finitely supported",
			"∀u:(num → num). (∀x:num. n < x ⇒ u(x) = 0) ⇒ finite_support(0, u)",
			Derive(func(b *Argument) {
				b.FixAs[monomial]("u")
				vanishes := b.Assume()
				within := b.Have(
					"its support lies among the variables up to n",
					"fun_support(0, u) ⊆ {x:num | x ≤ n}",
					BySets(vanishes, nat_order.NotLessEq))
				b.Show(
					"which are finitely many",
					By(
						within,
						function_module.FiniteSupportDef,
						num_segment.FiniteBelow.At(n),
						finite_set.FiniteSubset.At(
							b.TermAs[Set[Nat]]("fun_support(0, u)"), b.TermAs[Set[Nat]]("{x:num | x ≤ n}"))))
			}))
		degreeShift := a.Have(
			"adding c to the exponent at l, l ≤ n, adds c to the degree",
			Statement{
				Binders:    "∀f:(num → num). ∀c l:num.",
				Hypotheses: []string{"l ≤ n"},
				Conclusion: "sum({j:num | j ≤ n}, λx:num. f(x) + c * monomial_var(l, x)) = " +
					"sum({j:num | j ≤ n}, f) + c",
			},
			Derive(func(b *Argument) {
				f := b.FixAs[monomial]("f")
				c := b.FixAs[Nat]("c")
				l := b.FixAs[Nat]("l")
				inRange := b.Assume()
				b.Show(
					"the sum splits, and c·monomial_var(l) sums to c",
					By(
						inRange,
						homogeneous_polynomial.VariableMonomialDegree.At(n, l),
						num_segment.FiniteBelow.At(n),
						nat_sum.Add.At(f, b.TermAs[monomial]("λx:num. c * monomial_var(l, x)"), variables),
						nat_sum.ScalarLeft.At(c, b.TermAs[monomial]("monomial_var(l)"), variables),
						nat_arith.MulOne.At(c)))
			}))
		raisedMonomials := a.Have(
			"a monomial of degree s times X_i^e lies in X(e + s)",
			Statement{
				Binders: "∀s:num. ∀v:(num → num). ∀i:num.",
				Hypotheses: []string{
					"∀x:num. n < x ⇒ v(x) = 0",
					"sum({j:num | j ≤ n}, v) = s",
					"i ≤ n",
				},
				Conclusion: "delta_at(λx:num. v(x) + e * monomial_var(i, x)) ∈ X(e + s)",
			},
			Derive(func(b *Argument) {
				b.Induct("s")
				b.Base(
					"in degree zero the monomial is X_i^e itself",
					func(c *Argument) {
						v := c.FixAs[monomial]("v")
						i := c.FixAs[Nat]("i")
						given := c.Assume()
						vanishing := c.Have(
							"a monomial of degree zero vanishing past n is zero",
							"∀x:num. v(x) = 0",
							Derive(func(d *Argument) {
								d.FixAs[Nat]("x")
								d.Cases(d.TermAs[Bool]("x ≤ n"))
								d.When(
									"up to n its exponents sum to zero",
									func(f *Argument, below Fact) {
										f.Show(
											"so each is zero",
											By(below, given, num_segment.FiniteBelow.At(n), nat_sum.EqZero.At(variables, v)))
									})
								d.Otherwise(
									"past n it vanishes",
									func(f *Argument, beyond Fact) {
										f.Show(
											"by hypothesis",
											By(beyond, given, nat_order.NotLessEq))
									})
							}))
						exponent := c.Have(
							"so the exponent is e at i and zero elsewhere",
							"(λx:num. v(x) + e * monomial_var(i, x)) = (λx:num. e * monomial_var(i, x))",
							Funext(),
							By(vanishing, nat_arith.AddLeftZeroClause))
						c.Do(exponent.Rw())
						c.Show(
							"which is X_i^e, in X(e)",
							By(common, given, powerMonomial.At(i, e), nat_arith.AddZero))
					})
				b.Step(
					"a monomial of degree s + 1 is X_l times one of degree s, for some l with a positive exponent",
					func(c *Argument, ih Fact) {
						v := c.FixAs[monomial]("v")
						i := c.FixAs[Nat]("i")
						s := c.TermAs[Nat]("s")
						given := c.Assume()
						l, positive := c.ObtainAs[Nat](
							"some exponent of v up to n is positive",
							"∃l:num. l ≤ n ∧ v(l) ≠ 0",
							By(given, num_segment.FiniteBelow.At(n), nat_sum.EqZero.At(variables, v), peano.SucNotZero.At(s)))
						restore := c.Have(
							"lowering the exponent at l by one and raising it again restores v",
							"∀x:num. v(x) - monomial_var(l, x) + 1 * monomial_var(l, x) = v(x)",
							ByArith(positive, polynomial_algebra.MonomialLowerRaise.At(v, l, c.TermAs[Nat]("1"))))
						lowered := c.TermAs[monomial]("λx:num. v(x) - monomial_var(l, x)")
						loweredDegree := c.Have(
							"the lowered monomial has degree one less",
							"sum({j:num | j ≤ n}, λx:num. v(x) - monomial_var(l, x)) + 1 = sum({j:num | j ≤ n}, v)",
							By(
								positive,
								restore,
								degreeShift.At(lowered, c.TermAs[Nat]("1"), l),
								nat_sum.Congruence.At(
									variables, c.TermAs[monomial]("λx:num. v(x) - monomial_var(l, x) + 1 * monomial_var(l, x)"), v)))
						degree := c.Have(
							"which is s",
							"sum({j:num | j ≤ n}, λx:num. v(x) - monomial_var(l, x)) = s",
							ByArith(loweredDegree, given))
						loweredVanishes := c.Have(
							"the lowered monomial vanishes past n",
							"∀x:num. n < x ⇒ v(x) - monomial_var(l, x) = 0",
							ByArith(given))
						shifted := c.TermAs[monomial]("λx:num. v(x) - monomial_var(l, x) + e * monomial_var(i, x)")
						shiftedVanishes := c.Have(
							"and so does its product with X_i^e",
							"∀x:num. n < x ⇒ v(x) - monomial_var(l, x) + e * monomial_var(i, x) = 0",
							Derive(func(d *Argument) {
								x := d.FixAs[Nat]("x")
								past := d.Assume()
								d.Show(
									"past n the exponent of v is zero and x is not i",
									ByArith(past, given, unit.At(i, x), polynomial_algebra.MonomialVarValues.At(i)))
							}))
						together := c.Have(
							"raising the lowered exponent at l again gives the exponent of v times X_i^e",
							"(λx:num. v(x) - monomial_var(l, x) + e * monomial_var(i, x) + monomial_var(l, x)) = "+
								"(λx:num. v(x) + e * monomial_var(i, x))",
							Funext(),
							Derive(func(d *Argument) {
								x := d.FixAs[Nat]("x")
								d.Show(
									"the exponents add up at every variable",
									ByArith(restore.At(x)))
							}))
						lowerProduct := c.TermAs[_Polynomial](
							"delta_at(λx:num. v(x) - monomial_var(l, x) + e * monomial_var(i, x))")
						c.Do(together.RwRev())
						c.Show(
							"X_l times a member of X(e + s) lies in X(e + s + 1)",
							By(
								given,
								positive,
								past,
								degree,
								loweredVanishes,
								shiftedVanishes,
								ih.At(lowered, i),
								finitelySupported.At(shifted),
								shift.At(shifted, l),
								closure.At(c.TermAs[Nat]("e + s"), l, lowerProduct),
								nat_arith.AddSuc.At(e, s),
								nat_arith.Add1.At(c.TermAs[Nat]("e + s")),
								nat_order.LessEqAdd.At(e, s),
								nat_order.LessEqTrans.At(N0, e, c.TermAs[Nat]("e + s"))))
					})
			}))
		pigeonhole := a.Have(
			"a monomial of degree at least (n + 1)·e has an exponent at least e",
			"∀u:(num → num). (n + 1) * e ≤ sum({j:num | j ≤ n}, u) ⇒ ∃i:num. i ≤ n ∧ e ≤ u(i)",
			Derive(func(b *Argument) {
				u := b.FixAs[monomial]("u")
				large := b.Assume()
				smaller := b.SupposeNot()
				complement := b.TermAs[monomial]("λx:num. e - u(x)")
				filled := b.Have(
					"each exponent tops up to e",
					"∀x:num. x ∈ {j:num | j ≤ n} ⇒ u(x) + (e - u(x)) = e * 1",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("x")
						inRange := c.Assume()
						c.Show(
							"the exponent is below e",
							ByArith(smaller, inRange))
					}))
				count := b.Have(
					"there are n + 1 variables",
					"sum({j:num | j ≤ n}, λx:num. 1) = n + 1",
					By(num_segment.HasSizeBelow.At(n), cardinality.HasSizeDef, nat_sum.SumOfOnes.At(variables)))
				total := b.Have(
					"so the exponents and their top-ups sum to (n + 1)·e",
					"sum({j:num | j ≤ n}, u) + sum({j:num | j ≤ n}, λx:num. e - u(x)) = e * (n + 1)",
					By(
						filled,
						count,
						num_segment.FiniteBelow.At(n),
						nat_sum.Add.At(u, complement, variables),
						nat_sum.Congruence.At(
							variables, b.TermAs[monomial]("λx:num. u(x) + (e - u(x))"), b.TermAs[monomial]("λx:num. e * 1")),
						nat_sum.ScalarLeft.At(e, b.TermAs[monomial]("λx:num. 1"), variables)))
				topUp := b.Have(
					"the top-up at the variable 0 is part of their sum",
					"e - u(0) ≤ sum({j:num | j ≤ n}, λx:num. e - u(x))",
					By(
						num_segment.FiniteBelow.At(n),
						nat_order.ZeroLessEq.At(n),
						nat_sum.TermLeSum.At(complement, variables, b.TermAs[Nat]("0"))))
				b.Show(
					"and it is positive, so the degree is below (n + 1)·e",
					ByArith(smaller, large, topUp, total, nat_order.ZeroLessEq.At(n)))
			}))
		monomialsIn := a.Have(
			"every monomial of degree d ≥ (n + 1)·e lies in X(d)",
			Statement{
				Binders: "∀d:num. ∀m:(num → num).",
				Hypotheses: []string{
					"(n + 1) * e ≤ d",
					"m ∈ monomials({j:num | j ≤ n})",
					"sum({j:num | j ≤ n}, m) = d",
				},
				Conclusion: "delta_at(m) ∈ X(d)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				m := b.FixAs[monomial]("m")
				given := b.Conjuncts(
					b.Assume(),
					"the degree d is at least (n + 1)·e",
					"m is a monomial in the variables up to n",
					"of degree d")
				i, large := b.ObtainAs[Nat](
					"some exponent of m is at least e",
					"∃i:num. i ≤ n ∧ e ≤ m(i)",
					By(given[0], given[2], pigeonhole.At(m)))
				// Taking e from the exponent at i and giving it back restores m,
				// the exponent at i being at least e.
				restore := polynomial_algebra.MonomialLowerRaise.At(m, i, e)
				support := b.Unfolded(given[1], polynomial_algebra.MonomialsDef)
				vanishes := b.Have(
					"the lowered monomial vanishes past n",
					"∀x:num. n < x ⇒ m(x) - e * monomial_var(i, x) = 0",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("x")
						outside := c.Assume()
						vanishing := c.Have(
							"m vanishes past n",
							"m(x) = 0",
							BySets(outside, support, nat_order.NotLessEq))
						c.Show(
							"so does what is taken from it",
							ByArith(vanishing))
					}))
				lowered := b.TermAs[monomial]("λx:num. m(x) - e * monomial_var(i, x)")
				loweredDegree := b.Have(
					"the lowered monomial has degree d − e",
					"sum({j:num | j ≤ n}, λx:num. m(x) - e * monomial_var(i, x)) + e = d",
					By(large, given[2], restore, degreeShift.At(lowered, e, i)))
				degrees := b.Have(
					"so e + (d − e) is d",
					"e + (d - e) = d ∧ sum({j:num | j ≤ n}, λx:num. m(x) - e * monomial_var(i, x)) = d - e",
					ByArith(loweredDegree, given[0]))
				b.Show(
					"which lies in X(e + (d − e)) = X(d), m being the lowered monomial times X_i^e",
					By(vanishes, restore, large, degrees, raisedMonomials.At(b.TermAs[Nat]("d - e"), lowered, i)))
			}))
		a.Take(a.TermAs[Nat]("(n + 1) * e"))
		a.Show(
			"from degree (n + 1)·e on, a form is the sum of its coefficients times its monomials, each in X",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				large := b.Assume()
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				P := b.FixAs[_Polynomial]("P")
				formP := b.Assume()
				facts := b.Have(
					"P is a finitely supported function on the monomials into k, nonzero only in degree d",
					"P ∈ finite_supp(M.zero, k, monomials({j:num | j ≤ n})) ∧ "+
						"(∀m:(num → num). P(m) ≠ M.zero ⇒ sum({j:num | j ≤ n}, m) = d)",
					BySets(
						formP,
						homogeneous_polynomial.FormPolynomial,
						homogeneous_polynomial.FormDegree,
						polynomial_algebra.PolynomialAlgebraDef))
				expansion := b.Have(
					"P is the sum of its coefficients times its monomials",
					"P = "+
						"module_sum(fun_add, "+
						"    fun_zero, "+
						"    fun_support(M.zero, P), "+
						"    λm:(num → num). fun_smul(P(m), delta_at(m)))",
					By(
						scalars,
						facts,
						free_module.FreeModuleExpand.At(K, b.TermAs[Set[Fun[Nat, Nat]]]("monomials({j:num | j ≤ n})"), P)))
				beyond := b.Have(
					"d is past N₀",
					"N₀ ≤ d",
					ByArith(past, large))
				space := b.Have(
					"X(d) is a subspace of the forms of degree d",
					"submodule(«hilbertCoefficients», «formSpace»(d), X(d))",
					By(beyond, subspace.At(d)))
				terms := b.Have(
					"each coefficient times its monomial lies in X(d)",
					"∀m:(num → num). m ∈ fun_support(M.zero, P) ⇒ fun_smul(P(m), delta_at(m)) ∈ X(d)",
					Derive(func(c *Argument) {
						m := c.FixAs[monomial]("m")
						nonzero := c.Assume()
						term := c.Have(
							"m is a monomial of degree d with its coefficient in k",
							"m ∈ monomials({j:num | j ≤ n}) ∧ sum({j:num | j ≤ n}, m) = d ∧ P(m) ∈ k",
							By(nonzero, facts, function_module.FiniteSuppMember, set_basic.SubsetDef))
						c.Do(Simp(Fwd(function_module.FunSmulDef)))
						c.Show(
							"a scalar multiple of a member of the subspace X(d)",
							By(
								large,
								term,
								space,
								monomialsIn.At(d, m),
								submodule.SubmoduleSmul.At(
									K,
									c.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
									c.TermAs[Set[_Polynomial]]("X(d)"),
									c.TermAs[A]("P(m)"),
									c.TermAs[_Polynomial]("delta_at(m)"))))
					}))
				module := b.Have(
					"the forms of degree d are a vector space over k",
					"module_on(«hilbertCoefficients», «formSpace»(d))",
					By(subK, Read(projective_curve.FormsSubspace, M).At(k, n, d)))
				finite := b.Have(
					"P has finitely many monomials",
					"finite(fun_support(M.zero, P))",
					By(facts, function_module.FiniteSuppMember))
				b.Show(
					"so the sum lies in X(d)",
					By(
						terms,
						expansion,
						module,
						finite,
						space,
						submodule.SubmoduleModuleSum.At(
							K,
							b.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
							b.TermAs[Set[_Polynomial]]("X(d)"),
							b.TermAs[Set[Fun[Nat, Nat]]]("fun_support(M.zero, P)"),
							b.TermAs[Fun[Fun[Nat, Nat], _Polynomial]]("λm:(num → num). fun_smul(P(m), delta_at(m))"))))
			}))
	}),
})}

// GeneratedIdealForms — subspaces X(d) of the forms of degree d over a
// subfield k, from degree N₀ on closed under multiplication by the variables,
// are the forms of their degree in the ideal they generate: a form of degree
// t ≥ N₀ in that ideal lies in X(t). The polynomials Y whose parts below
// degree N₀ vanish and whose part of each degree d ≥ N₀ lies in X(d) are an
// ideal: the parts of a sum are the sums of the parts, a constant keeps each
// part in its degree and a variable moves it up one
// (homogeneous_polynomial.FormTimesPart, homogeneous_polynomial.FormTimesLowPart), X
// being a subspace closed under the variables, and every polynomial is built
// from constants and variables (polynomial_algebra.PolynomialInduction). Y
// holds the generators, so it holds the ideal they generate, and a form of
// degree t is its own part of degree t.
var GeneratedIdealForms = generatedIdealFormsThm{family.Add(registry.ProofEntry{
	Name: "GeneratedIdealForms",
	Key:  "prop_c87c12c6af739aee",
	Reading: "N₀ ≤ t is load-bearing: nothing is asked of X below N₀, and there the ideal's " +
		"forms need not lie in X(t). The closure under the variables is what keeps the span's " +
		"forms of degree t inside X(t); without it the ideal holds every multiple of every X(d).",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n N₀ t:num. ∀X:(num → set((num → num) → A)).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀d:num. N₀ ≤ d ⇒ submodule(«hilbertCoefficients», «formSpace»(d), X(d))",
			"∀d j:num. ∀P:((num → num) → A). " +
				"    N₀ ≤ d ∧ j ≤ n ∧ P ∈ X(d) ⇒ " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        P) ∈ " +
				"    X(d + 1)",
			"N₀ ≤ t",
		},
		Conclusion: "«forms»(t) ∩ ideal_span(«polynomials», «generators») = X(t)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "generators", Text: "{P:((num → num) → A) | ∃d:num. N₀ ≤ d ∧ P ∈ X(d)}"},
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), M.zero)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, N0, t *Expr[Nat],
		X *Arrow2[Nat, _Polynomial, Bool],
		subK, subspace, closure, large Fact,
	) {
		K := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		polynomialRing := a.TermAs[module_record.RingOps[_Polynomial]]("«polynomials»")
		generators := a.TermAs[Set[_Polynomial]]("«generators»")
		zeroDegree := a.TermAs[Nat]("0")
		one := a.TermAs[Nat]("1")
		zeroPolynomial := a.TermAs[_Polynomial]("fun_zero")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		// The ring of polynomials over k with its operations written out, the
		// sums coefficientwise and the product the convolution: the ring the
		// laws below are read in and the identities computed in.
		arithmetic := a.Simplified(
			GroupPremises(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn.At(K, variables)),
			Fwd(polynomial_algebra.PolynomialAlgebraRingDef))
		timesZero := comm_ring.MulRightZeroOn.Read(arithmetic)
		zeroSum := a.Have(
			"zero plus zero is zero",
			"M.zero + M.zero = M.zero",
			ByArith(M))
		zeroIn := a.Have(
			"from N₀ on each X(d) holds the zero polynomial",
			"∀d:num. N₀ ≤ d ⇒ fun_zero ∈ X(d)",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				past := b.Assume()
				b.Show(
					"a subspace holds zero",
					By(
						past,
						subspace.At(d),
						submodule.SubmoduleZero.At(
							K,
							b.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
							b.TermAs[Set[_Polynomial]]("X(d)"))))
			}))
		inForms := a.Have(
			"a member of X(d), d ≥ N₀, is a form of degree d",
			Statement{
				Binders:    "∀d:num. ∀P:((num → num) → A).",
				Hypotheses: []string{"N₀ ≤ d", "P ∈ X(d)"},
				Conclusion: "homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				b.FixAs[_Polynomial]("P")
				given := b.Assume()
				b.Show(
					"X(d) lies among the forms of degree d",
					BySets(
						given,
						subspace.At(d),
						submodule.SubmoduleSubset.At(
							K,
							b.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
							b.TermAs[Set[_Polynomial]]("X(d)"))))
			}))
		ownPart := a.Have(
			"a form of degree d is its own part of degree d",
			Statement{
				Binders:    "∀d:num. ∀P:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
				Conclusion: "«part»(d, P) = P",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				b.FixAs[_Polynomial]("P")
				form := b.Assume()
				b.Show(
					"where P is not zero its monomial has degree d",
					Funext(),
					By(homogeneous_polynomial.FormDegree.Read(form)))
			}))
		otherParts := a.Have(
			"and has no part of another degree",
			Statement{
				Binders:    "∀d e:num. ∀P:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)", "e ≠ d"},
				Conclusion: "«part»(e, P) = fun_zero",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				b.FixAs[Nat]("e")
				P := b.FixAs[_Polynomial]("P")
				given := b.Assume()
				b.Show(
					"at a monomial of degree e, not d, P is zero",
					Funext(),
					By(given, At(homogeneous_polynomial.FormDegree, K, n, d, P), function_module.FunZeroDef))
			}))
		graded, gradedDef := a.LetAs[Set[_Polynomial]](
			"Y",
			"{Q:((num → num) → A) | "+
				"    Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
				"    (∀d:num. d < N₀ ⇒ «part»(d, Q) = fun_zero) ∧ "+
				"    (∀d:num. N₀ ≤ d ⇒ «part»(d, Q) ∈ X(d))}")
		members := a.Have(
			"a member of Y is a polynomial over k with no part below "+
				"degree N₀ and its part of each degree d ≥ N₀ in X(d)",
			Statement{
				Binders:    "∀Q:((num → num) → A).",
				Hypotheses: []string{"Q ∈ Y"},
				Conclusion: "Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ " +
					"(∀d:num. d < N₀ ⇒ «part»(d, Q) = fun_zero) ∧ " +
					"(∀d:num. N₀ ≤ d ⇒ «part»(d, Q) ∈ X(d))",
			},
			BySets(gradedDef))
		gathered := a.Have(
			"and every such polynomial lies in Y",
			Statement{
				Binders: "∀Q:((num → num) → A).",
				Hypotheses: []string{
					"Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					"∀d:num. d < N₀ ⇒ «part»(d, Q) = fun_zero",
					"∀d:num. N₀ ≤ d ⇒ «part»(d, Q) ∈ X(d)",
				},
				Conclusion: "Q ∈ Y",
			},
			BySets(gradedDef))
		zeroParts := a.Have(
			"every part of the zero polynomial is zero",
			"∀d:num. «part»(d, fun_zero) = fun_zero",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				b.Show(
					"zero in degree d and zero elsewhere",
					Funext(),
					By(function_module.FunZeroDef))
			}))
		zeroHigh := a.Have(
			"from N₀ on they lie in X",
			"∀d:num. N₀ ≤ d ⇒ «part»(d, fun_zero) ∈ X(d)",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				past := b.Assume()
				b.Show(
					"zero lies in X(d)",
					By(past, zeroParts.At(d), zeroIn.At(d)))
			}))
		zeroGraded := a.Have(
			"so the zero polynomial lies in Y",
			"fun_zero ∈ Y",
			By(comm_ring.ZeroIn.Read(arithmetic), zeroParts, zeroHigh, gathered.At(zeroPolynomial)))
		sums := a.Have(
			"Y is closed under sums: a part of a sum is the sum of the parts",
			"∀P Q:((num → num) → A). P ∈ Y ∧ Q ∈ Y ⇒ fun_add(P, Q) ∈ Y",
			Derive(func(b *Argument) {
				P := b.FixAs[_Polynomial]("P")
				Q := b.FixAs[_Polynomial]("Q")
				given := b.Conjuncts(
					b.Assume(),
					"P lies in Y",
					"so does Q")
				p := b.Conjuncts(
					GroupPremises(given[0], members.At(P)),
					"P is a polynomial over k",
					"P has no part below degree N₀",
					"from N₀ on the parts of P lie in X")
				q := b.Conjuncts(
					GroupPremises(given[1], members.At(Q)),
					"Q is a polynomial over k",
					"Q has no part below degree N₀",
					"from N₀ on the parts of Q lie in X")
				partSum := b.Have(
					"the part of degree d of P + Q is the sum of their parts",
					"∀d:num. «part»(d, fun_add(P, Q)) = fun_add(«part»(d, P), «part»(d, Q))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("d")
						c.Show(
							"off degree d both sides are zero",
							Funext(),
							Simp(Fwd(function_module.FunAddDef)),
							By(zeroSum))
					}))
				low := b.Have(
					"below N₀ the parts of P + Q vanish",
					"∀d:num. d < N₀ ⇒ «part»(d, fun_add(P, Q)) = fun_zero",
					Derive(func(c *Argument) {
						d := c.FixAs[Nat]("d")
						below := c.Assume()
						c.Show(
							"zero plus zero is zero",
							By(
								below,
								partSum.At(d),
								p[1].At(d),
								q[1].At(d),
								comm_ring.ZeroIn.Read(arithmetic),
								comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(arithmetic)).AsFact().At(
									zeroPolynomial)))
					}))
				high := b.Have(
					"from N₀ on they lie in X, a sum of members of a subspace",
					"∀d:num. N₀ ≤ d ⇒ «part»(d, fun_add(P, Q)) ∈ X(d)",
					Derive(func(c *Argument) {
						d := c.FixAs[Nat]("d")
						past := c.Assume()
						c.Show(
							"the sum of the parts of P and Q, both in X(d)",
							By(
								past,
								partSum.At(d),
								p[2].At(d),
								q[2].At(d),
								subspace.At(d),
								submodule.SubmoduleAdd.At(
									K,
									c.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
									c.TermAs[Set[_Polynomial]]("X(d)"),
									c.TermAs[_Polynomial]("«part»(d, P)"),
									c.TermAs[_Polynomial]("«part»(d, Q)"))))
					}))
				b.Show(
					"so P + Q is a polynomial over k in Y",
					By(
						p[0],
						q[0],
						comm_ring.AddIn.Read(arithmetic),
						low,
						high,
						gathered.At(b.TermAs[_Polynomial]("fun_add(P, Q)"))))
			}))
		scaled := a.Have(
			"Y is closed under multiplication by a constant c of k, "+
				"a form of degree zero that keeps each part in its degree",
			Statement{
				Binders:    "∀c:A. ∀Q:((num → num) → A).",
				Hypotheses: []string{"c ∈ k", "Q ∈ Y"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», " +
					"    polynomial_algebra_const(«hilbertCoefficients», c), " +
					"    Q) ∈ " +
					"Y",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				Q := b.FixAs[_Polynomial]("Q")
				given := b.Conjuncts(
					b.Assume(),
					"c lies in k",
					"Q lies in Y")
				q := b.Conjuncts(
					GroupPremises(given[1], members.At(Q)),
					"Q is a polynomial over k",
					"Q has no part below degree N₀",
					"from N₀ on the parts of Q lie in X")
				constant := b.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», c)")
				constantForm := b.Have(
					"the constant c is a form of degree zero",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    0, "+
						"    polynomial_algebra_const(«hilbertCoefficients», c))",
					By(scalars, given[0], homogeneous_polynomial.FormConstant.At(K, n, c)))
				constantIn := b.Have(
					"so it is a polynomial over k",
					"polynomial_algebra_const(«hilbertCoefficients», c) ∈ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(homogeneous_polynomial.FormPolynomial.Read(constantForm)))
				kept := b.Have(
					"the constant keeps each part of Q in its degree",
					"∀d:num. "+
						"    «part»(d, "+
						"        polynomial_algebra_mul(«hilbertCoefficients», "+
						"            polynomial_algebra_const(«hilbertCoefficients», c), "+
						"            Q)) = "+
						"    polynomial_algebra_mul(«hilbertCoefficients», "+
						"        polynomial_algebra_const(«hilbertCoefficients», c), "+
						"        «part»(d, Q))",
					Derive(func(e *Argument) {
						d := e.FixAs[Nat]("d")
						e.Show(
							"a form of degree zero moves the parts by zero",
							By(
								scalars,
								constantForm,
								q[0],
								At(homogeneous_polynomial.FormTimesPart, K, n, zeroDegree, d, constant, Q),
								nat_arith.AddZero.At(d)))
					}))
				low := b.Have(
					"below N₀ the parts of c·Q vanish, c times zero being zero",
					Statement{
						Binders:    "∀d:num.",
						Hypotheses: []string{"d < N₀"},
						Conclusion: "«part»(d, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», " +
							"        polynomial_algebra_const(«hilbertCoefficients», c), " +
							"        Q)) = " +
							"fun_zero",
					},
					Derive(func(e *Argument) {
						d := e.FixAs[Nat]("d")
						below := e.Assume()
						e.Show(
							"the constant times the zero part of Q",
							By(below, kept.At(d), q[1].At(d), constantIn, timesZero))
					}))
				high := b.Have(
					"from N₀ on they are c times the parts of Q, in the subspaces X",
					Statement{
						Binders:    "∀d:num.",
						Hypotheses: []string{"N₀ ≤ d"},
						Conclusion: "«part»(d, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», " +
							"        polynomial_algebra_const(«hilbertCoefficients», c), " +
							"        Q)) ∈ " +
							"X(d)",
					},
					Derive(func(e *Argument) {
						d := e.FixAs[Nat]("d")
						past := e.Assume()
						part := e.TermAs[_Polynomial]("«part»(d, Q)")
						partIn := e.Have(
							"the part of degree d of Q is a polynomial over k",
							"«part»(d, Q) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
							By(
								scalars,
								q[0],
								At(homogeneous_polynomial.FormPart, K, n, d, Q),
								homogeneous_polynomial.FormPolynomial,
								polynomial_algebra.PolynomialAlgebraRingDef))
						e.Show(
							"c times a member of the subspace X(d)",
							By(
								past,
								kept.At(d),
								q[2].At(d),
								scalars,
								given[0],
								partIn,
								polynomial_algebra.PolynomialAlgebraConstMul.At(K, variables, c, part),
								subspace.At(d),
								submodule.SubmoduleSmul.At(
									K,
									e.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
									e.TermAs[Set[_Polynomial]]("X(d)"),
									c,
									part)))
					}))
				product := b.TermAs[_Polynomial](
					"polynomial_algebra_mul(«hilbertCoefficients», " +
						"    polynomial_algebra_const(«hilbertCoefficients», c), " +
						"    Q)")
				b.Show(
					"so c·Q is a polynomial over k in Y",
					By(
						scalars,
						constantIn,
						q[0],
						polynomial_algebra.PolynomialAlgebraMulIn.At(K, variables, constant, Q),
						low,
						high,
						gathered.At(product)))
			}))
		raisedByVariable := a.Have(
			"Y is closed under multiplication by a variable X_j, "+
				"a form of degree one that moves each part up a degree",
			Statement{
				Binders:    "∀j:num. ∀Q:((num → num) → A).",
				Hypotheses: []string{"j ≤ n", "Q ∈ Y"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», " +
					"    polynomial_algebra_var(«hilbertCoefficients», j), " +
					"    Q) ∈ " +
					"Y",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				Q := b.FixAs[_Polynomial]("Q")
				given := b.Conjuncts(
					b.Assume(),
					"j is at most n",
					"Q lies in Y")
				q := b.Conjuncts(
					GroupPremises(given[1], members.At(Q)),
					"Q is a polynomial over k",
					"Q has no part below degree N₀",
					"from N₀ on the parts of Q lie in X")
				variable := b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», j)")
				variableForm := b.Have(
					"X_j is a form of degree one",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    1, "+
						"    polynomial_algebra_var(«hilbertCoefficients», j))",
					By(scalars, given[0], homogeneous_polynomial.FormVariable.At(K, n, j)))
				variableIn := b.Have(
					"so it is a polynomial over k",
					"polynomial_algebra_var(«hilbertCoefficients», j) ∈ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(homogeneous_polynomial.FormPolynomial.Read(variableForm)))
				lowest := b.Have(
					"X_j·Q has no part of degree zero",
					"«part»(0, "+
						"    polynomial_algebra_mul(«hilbertCoefficients», "+
						"        polynomial_algebra_var(«hilbertCoefficients», j), "+
						"        Q)) = "+
						"fun_zero",
					By(
						scalars,
						variableForm,
						q[0],
						At(homogeneous_polynomial.FormTimesLowPart, K, n, one, zeroDegree, variable, Q)))
				raised := b.Have(
					"and its part of degree d + 1 is X_j times the part of degree d of Q",
					"∀d:num. "+
						"    «part»(d + 1, "+
						"        polynomial_algebra_mul(«hilbertCoefficients», "+
						"            polynomial_algebra_var(«hilbertCoefficients», j), "+
						"            Q)) = "+
						"    polynomial_algebra_mul(«hilbertCoefficients», "+
						"        polynomial_algebra_var(«hilbertCoefficients», j), "+
						"        «part»(d, Q))",
					Derive(func(e *Argument) {
						d := e.FixAs[Nat]("d")
						e.Show(
							"a form of degree one moves the parts up by one",
							By(
								scalars,
								variableForm,
								q[0],
								At(homogeneous_polynomial.FormTimesPart, K, n, one, d, variable, Q)))
					}))
				low := b.Have(
					"below N₀ the parts of X_j·Q vanish",
					Statement{
						Binders:    "∀d:num.",
						Hypotheses: []string{"d < N₀"},
						Conclusion: "«part»(d, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», " +
							"        polynomial_algebra_var(«hilbertCoefficients», j), " +
							"        Q)) = " +
							"fun_zero",
					},
					Derive(func(e *Argument) {
						e.Induct("d")
						e.Base(
							"the part of degree zero is zero",
							By(lowest))
						e.Step(
							"the part of degree d + 1 is X_j times the zero part of degree d of Q",
							func(f *Argument, _ Fact) {
								d := f.TermAs[Nat]("d")
								below := f.Assume()
								smaller := f.Have(
									"d is below N₀ too",
									"d < N₀",
									ByArith(below))
								f.Show(
									"X_j times zero is zero",
									By(smaller, raised.At(d), q[1].At(d), variableIn, timesZero, nat_arith.Add1.At(d)))
							})
					}))
				high := b.Have(
					"from N₀ on they lie in X, which X_j maps into the next degree",
					Statement{
						Binders:    "∀d:num.",
						Hypotheses: []string{"N₀ ≤ d"},
						Conclusion: "«part»(d, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», " +
							"        polynomial_algebra_var(«hilbertCoefficients», j), " +
							"        Q)) ∈ " +
							"X(d)",
					},
					Derive(func(e *Argument) {
						e.Induct("d")
						e.Base(
							"N₀ is zero, and the part of degree zero is zero, in X(0)",
							By(lowest, zeroIn.At(zeroDegree)))
						e.Step(
							"the part of degree d + 1 is X_j times the part of degree d of Q",
							func(f *Argument, _ Fact) {
								d := f.TermAs[Nat]("d")
								past := f.Assume()
								part := f.TermAs[_Polynomial]("«part»(d, Q)")
								f.Cases(f.TermAs[Bool]("N₀ ≤ d"))
								f.When(
									"from N₀ on, X_j maps X(d) into X(d + 1)",
									func(g *Argument, above Fact) {
										g.Show(
											"X_j times a member of X(d)",
											By(above, given[0], raised.At(d), q[2].At(d), closure.At(d, j, part), nat_arith.Add1.At(d)))
									})
								f.Otherwise(
									"below N₀ the part of degree d of Q is zero",
									func(g *Argument, below Fact) {
										smaller := g.Have(
											"d is below N₀",
											"d < N₀",
											ByArith(below))
										g.Show(
											"and X_j times zero is zero, in X(d + 1)",
											By(
												past,
												smaller,
												raised.At(d),
												q[1].At(d),
												variableIn,
												timesZero,
												zeroIn.At(f.TermAs[Nat]("d + 1")),
												nat_arith.Add1.At(d)))
									})
							})
					}))
				product := b.TermAs[_Polynomial](
					"polynomial_algebra_mul(«hilbertCoefficients», " +
						"    polynomial_algebra_var(«hilbertCoefficients», j), " +
						"    Q)")
				b.Show(
					"so X_j·Q is a polynomial over k in Y",
					By(
						scalars,
						variableIn,
						q[0],
						polynomial_algebra.PolynomialAlgebraMulIn.At(K, variables, variable, Q),
						low,
						high,
						gathered.At(product)))
			}))
		multiples := a.Have(
			"Y is closed under multiplication by every polynomial over "+
				"k, built from constants and variables by sums and products",
			Statement{
				Binders:    "∀Q G:((num → num) → A).",
				Hypotheses: []string{"Q ∈ Y", "G ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», G, Q) ∈ Y",
			},
			Derive(func(b *Argument) {
				Q := b.FixAs[_Polynomial]("Q")
				b.FixAs[_Polynomial]("G")
				given := b.Conjuncts(
					b.Assume(),
					"Q lies in Y",
					"G is a polynomial over k")
				qIn := b.Have(
					"Q is a polynomial over k",
					"Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(given[0], members.At(Q)))
				multipliers, multipliersDef := b.LetAs[Set[_Polynomial]](
					"C",
					"{G:((num → num) → A) | "+
						"    G ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
						"    polynomial_algebra_mul(«hilbertCoefficients», G, Q) ∈ Y}")
				constants := b.Have(
					"the constants of k multiply Q into Y",
					"∀c:A. c ∈ k ⇒ polynomial_algebra_const(«hilbertCoefficients», c) ∈ C",
					Derive(func(c *Argument) {
						constant := c.FixAs[A]("c")
						cIn := c.Assume()
						c.Show(
							"a constant is a polynomial over k, and c·Q lies in Y",
							BySets(
								multipliersDef,
								cIn,
								scalars,
								homogeneous_polynomial.FormConstant.At(K, n, constant),
								homogeneous_polynomial.FormPolynomial,
								given[0],
								scaled.At(constant, Q)))
					}))
				sumsOf := b.Have(
					"so does a sum of two such multipliers, the product distributing over it",
					"∀f g:((num → num) → A). f ∈ C ∧ g ∈ C ⇒ fun_add(f, g) ∈ C",
					Derive(func(c *Argument) {
						c.FixAs[_Polynomial]("f")
						c.FixAs[_Polynomial]("g")
						both := c.Assume()
						parts := c.Have(
							"f and g are polynomials over k multiplying Q into Y",
							"f ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
								"polynomial_algebra_mul(«hilbertCoefficients», f, Q) ∈ Y ∧ "+
								"g ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
								"polynomial_algebra_mul(«hilbertCoefficients», g, Q) ∈ Y",
							BySets(both, multipliersDef))
						factors := c.Conjuncts(
							parts,
							"f is a polynomial over k",
							"f·Q lies in Y",
							"g is a polynomial over k",
							"g·Q lies in Y")
						distribute := c.Have(
							"(f + g)·Q = f·Q + g·Q",
							"polynomial_algebra_mul(«hilbertCoefficients», fun_add(f, g), Q) = "+
								"fun_add(polynomial_algebra_mul(«hilbertCoefficients», f, Q), "+
								"    polynomial_algebra_mul(«hilbertCoefficients», g, Q))",
							ByArith(arithmetic, factors[0], factors[2], qIn))
						sum := c.Have(
							"so (f + g)·Q is the sum of two members of Y",
							"polynomial_algebra_mul(«hilbertCoefficients», fun_add(f, g), Q) ∈ Y",
							By(
								distribute,
								factors[1],
								factors[3],
								sums.At(
									c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», f, Q)"),
									c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», g, Q)"))))
						c.Show(
							"and f + g is a polynomial over k",
							BySets(multipliersDef, factors[0], factors[2], comm_ring.AddIn.Read(arithmetic), sum))
					}))
				variablesOf := b.Have(
					"and so does a variable times such a multiplier, the product being associative",
					Statement{
						Binders:    "∀x:num. ∀f:((num → num) → A).",
						Hypotheses: []string{"x ∈ {i:num | i ≤ n}", "f ∈ C"},
						Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», " +
							"    polynomial_algebra_var(«hilbertCoefficients», x), " +
							"    f) ∈ " +
							"C",
					},
					Derive(func(c *Argument) {
						x := c.FixAs[Nat]("x")
						f := c.FixAs[_Polynomial]("f")
						either := c.Conjuncts(
							c.Assume(),
							"x is one of the variables up to n",
							"f multiplies Q into Y")
						factors := c.Conjuncts(
							c.Have(
								"f is a polynomial over k multiplying Q into Y",
								"f ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
									"polynomial_algebra_mul(«hilbertCoefficients», f, Q) ∈ Y",
								BySets(either[1], multipliersDef)),
							"f is a polynomial over k",
							"f·Q lies in Y")
						variable := c.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», x)")
						variableIn := c.Have(
							"X_x is a polynomial over k",
							"polynomial_algebra_var(«hilbertCoefficients», x) ∈ "+
								"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
							By(
								scalars,
								either[0],
								homogeneous_polynomial.FormVariable.At(K, n, x),
								homogeneous_polynomial.FormPolynomial,
								polynomial_algebra.PolynomialAlgebraRingDef))
						associate := c.Have(
							"(X_x·f)·Q = X_x·(f·Q)",
							"polynomial_algebra_mul(«hilbertCoefficients», "+
								"    polynomial_algebra_mul(«hilbertCoefficients», "+
								"        polynomial_algebra_var(«hilbertCoefficients», x), "+
								"        f), "+
								"    Q) = "+
								"polynomial_algebra_mul(«hilbertCoefficients», "+
								"    polynomial_algebra_var(«hilbertCoefficients», x), "+
								"    polynomial_algebra_mul(«hilbertCoefficients», f, Q))",
							ByArith(arithmetic, variableIn, factors[0], qIn))
						product := c.Have(
							"so (X_x·f)·Q is X_x times a member of Y",
							"polynomial_algebra_mul(«hilbertCoefficients», "+
								"    polynomial_algebra_mul(«hilbertCoefficients», "+
								"        polynomial_algebra_var(«hilbertCoefficients», x), "+
								"        f), "+
								"    Q) ∈ "+
								"Y",
							By(
								associate,
								either[0],
								factors[1],
								raisedByVariable.At(
									x, c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», f, Q)"))))
						c.Show(
							"and X_x·f is a polynomial over k",
							BySets(
								multipliersDef,
								scalars,
								variableIn,
								factors[0],
								polynomial_algebra.PolynomialAlgebraMulIn.At(K, variables, variable, f),
								product))
					}))
				covered := b.Have(
					"so every polynomial over k multiplies Q into Y",
					"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ⊆ C",
					By(
						scalars,
						constants,
						sumsOf,
						variablesOf,
						At(polynomial_algebra.PolynomialInduction, K, variables, multipliers)))
				b.Show(
					"and G is one of them",
					BySets(given[1], covered, multipliersDef))
			}))
		ideal := a.Have(
			"so Y is an ideal of the polynomials over k",
			"ring_ideal(«polynomials», Y)",
			Simp(Fwd(ring_ideal.RingIdealDef), Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
			By(zeroGraded, sums, multiples, members, set_basic.SubsetDef))
		generatorsIn := a.Have(
			"Y holds the generators: a member of X(d), d ≥ N₀, is its own part of degree d and has no other",
			"«generators» ⊆ Y",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				P := b.FixAs[_Polynomial]("P")
				d, member := b.UnpackAs[Nat](b.Assume(), "d")
				parts := b.Conjuncts(
					member,
					"d is at least N₀",
					"P lies in X(d)")
				form := b.Have(
					"P is a form of degree d",
					"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					By(parts[0], parts[1], inForms.At(d, P)))
				polynomial := b.Have(
					"so a polynomial over k",
					"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(homogeneous_polynomial.FormPolynomial.Read(form)))
				low := b.Have(
					"its parts below N₀ vanish, d being at least N₀",
					"∀e:num. e < N₀ ⇒ «part»(e, P) = fun_zero",
					Derive(func(c *Argument) {
						e := c.FixAs[Nat]("e")
						below := c.Assume()
						other := c.Have(
							"e is not d",
							"e ≠ d",
							ByArith(below, parts[0]))
						c.Show(
							"a part of another degree",
							By(form, other, otherParts.At(d, e, P)))
					}))
				high := b.Have(
					"and from N₀ on its parts lie in X: P itself in degree d, zero elsewhere",
					"∀e:num. N₀ ≤ e ⇒ «part»(e, P) ∈ X(e)",
					Derive(func(c *Argument) {
						e := c.FixAs[Nat]("e")
						past := c.Assume()
						c.Cases(c.TermAs[Bool]("e = d"))
						c.When(
							"in degree d the part is P",
							func(f *Argument, same Fact) {
								f.Do(same.Rw())
								f.Show(
									"which lies in X(d)",
									By(form, parts[1], ownPart.At(d, P)))
							})
						c.Otherwise(
							"in another degree the part is zero",
							func(f *Argument, other Fact) {
								f.Show(
									"which lies in X(e)",
									By(past, other, form, otherParts.At(d, e, P), zeroIn.At(e)))
							})
					}))
				b.Show(
					"so P lies in Y",
					By(polynomial, low, high, gathered.At(P)))
			}))
		spanIn := a.Have(
			"so Y holds the ideal the X(d) generate",
			"ideal_span(«polynomials», «generators») ⊆ Y",
			By(ideal, generatorsIn, ring_ideal.SpanLeast.At(polynomialRing, generators, graded)))
		pointwise := a.Have(
			"a polynomial is a form of degree t in the ideal exactly when it lies in X(t)",
			"∀P:((num → num) → A). P ∈ «forms»(t) ∩ ideal_span(«polynomials», «generators») ⇔ P ∈ X(t)",
			Derive(func(b *Argument) {
				P := b.FixAs[_Polynomial]("P")
				b.Iff()
				b.Forward(
					"a form of degree t in the ideal lies in Y, and is its own part of degree t",
					func(c *Argument, both Fact) {
						given := c.Conjuncts(
							c.Simplified(both, Fwd(set_basic.InInter)),
							"P is a form of degree t",
							"P lies in the ideal")
						inY := c.Have(
							"so P lies in Y",
							"P ∈ Y",
							By(given[1], spanIn, set_basic.SubsetDef))
						parts := c.Conjuncts(
							GroupPremises(inY, members.At(P)),
							"P is a polynomial over k",
							"P has no part below degree N₀",
							"from N₀ on the parts of P lie in X")
						c.Show(
							"its part of degree t ≥ N₀ lies in X(t)",
							By(large, given[0], ownPart.At(t, P), parts[2].At(t)))
					})
				b.Backward(
					"a member of X(t) is a form of degree t and a generator, so in the ideal",
					func(c *Argument, member Fact) {
						generator := c.Have(
							"P is a generator, t being at least N₀",
							"P ∈ «generators»",
							By(member, large))
						c.Show(
							"the generators lie in the ideal they generate",
							BySets(
								member,
								large,
								generator,
								inForms.At(t, P),
								ring_ideal.SpanContains.At(polynomialRing, generators)))
					})
			}))
		a.Show(
			"so the forms of degree t in the ideal are exactly X(t)",
			By(pointwise, set_basic.Extension))
	}),
})}

// CommonZeroWithoutPower — subspaces X(d) of the forms of degree d over a
// subfield k of an algebraically closed field M, from degree N₀ on closed
// under multiplication by the variables and of codimension at most b, in
// which some variable Xᵢ has no power, have a common zero in projective space
// over M: the point the projective Nullstellensatz finds off the hyperplane
// Xᵢ = 0. The forms of large degree in the ideal the X(d) generate over k are
// the X(d) (GeneratedIdealForms), so it holds no power of Xᵢ, and a prime p of
// the polynomials over k holds it and misses Xᵢ
// (ring_ideal.PrimeAvoidingPowers). Its generic point y, normalized at i, has
// every coordinate algebraic over k: a transcendental one would give more
// than b independent values of forms of degree N₀ + b
// (projective_curve.TranscendentalCoordinateBound), while X(N₀ + b) ⊆ p
// bounds the Hilbert function of p there by b
// (projective_curve.HilbertFunctionBelowCodimension). So y has an image x in
// M with the same vanishing polynomials
// (projective_generic_point.AlgebraicPointIntoAmbient), a zero of every
// member of X with xᵢ = 1, and divided by its first nonzero coordinate it
// lies in projective space (projective_curve.PointNormalization).
var CommonZeroWithoutPower = commonZeroWithoutPowerThm{family.Add(registry.ProofEntry{
	Name: "CommonZeroWithoutPower",
	Key:  "prop_1459c388c9d77ad4",
	Reading: "The codimension bound makes every coordinate of the generic point of a prime " +
		"above X algebraic over k, and an algebraic point has an image in the closed M. At n = 0 " +
		"the forms of degree d are the multiples of X₀^d, so X(d) is zero and the point 1 is a zero.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n b N₀ i:num. ∀X:(num → set((num → num) → A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"∀d:num. N₀ ≤ d ⇒ submodule(«hilbertCoefficients», «formSpace»(d), X(d))",
			"∀d j:num. ∀P:((num → num) → A). " +
				"    N₀ ≤ d ∧ j ≤ n ∧ P ∈ X(d) ⇒ " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        P) ∈ " +
				"    X(d + 1)",
			"∀d:num. N₀ ≤ d ⇒ module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), X(d))) ≤ b",
			"i ≤ n",
			"∀a:num. N₀ ≤ a ⇒ «power»(i, a) ∉ X(a)",
		},
		Conclusion: "∃z:(num → A). " +
			"    z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, ∅) ∧ " +
			"    (∀d:num. ∀P:((num → num) → A). " +
			"        N₀ ≤ d ∧ P ∈ X(d) ⇒ " +
			"        polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, P) = M.zero)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add(M.add), " +
				"        fun_zero(M.zero), " +
				"        fun_neg(M.neg), " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "power", Text: "λl:num. λs:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», l), " +
				"        s)"},
			{Name: "generators", Text: "{P:((num → num) → A) | ∃d:num. N₀ ≤ d ∧ P ∈ X(d)}"},
			{Name: "fractions", Text: "fraction_field_record(ideal_quotient_ring(«polynomials», p))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, b, N0, i *Expr[Nat],
		X *Arrow2[Nat, _Polynomial, Bool],
		closed, subK, subspace, closure, bound, iIn, missing Fact,
	) {
		m := a.TermAs[FieldOps[A]]("M")
		K := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		polynomialRing := a.TermAs[module_record.RingOps[_Polynomial]]("«polynomials»")
		generators := a.TermAs[Set[_Polynomial]]("«generators»")
		variable := a.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», i)")
		one := a.TermAs[Nat]("1")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		polynomials := a.Have(
			"and so are the polynomials over k",
			"comm_ring_on(«polynomials»)",
			By(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn))
		inForms := a.Have(
			"a member of X(d), d ≥ N₀, is a form of degree d",
			Statement{
				Binders:    "∀d:num. ∀P:((num → num) → A).",
				Hypotheses: []string{"N₀ ≤ d", "P ∈ X(d)"},
				Conclusion: "homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
			},
			Derive(func(c *Argument) {
				d := c.FixAs[Nat]("d")
				c.FixAs[_Polynomial]("P")
				given := c.Assume()
				c.Show(
					"X(d) lies among the forms of degree d",
					BySets(
						given,
						subspace.At(d),
						submodule.SubmoduleSubset.At(
							K,
							c.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)"),
							c.TermAs[Set[_Polynomial]]("X(d)"))))
			}))
		generatorsIn := a.Have(
			"the members of the X(d) are polynomials over k",
			"«generators» ⊆ «polynomials».carrier",
			Unfold(set_basic.SubsetDef),
			Derive(func(c *Argument) {
				c.FixAs[_Polynomial]("P")
				_, member := c.UnpackAs[Nat](c.Assume(), "d")
				c.Show(
					"a form is a polynomial over k",
					By(
						member,
						inForms,
						homogeneous_polynomial.FormPolynomial,
						polynomial_algebra.PolynomialAlgebraRingDef))
			}))
		variableIn := a.Have(
			"Xᵢ is a polynomial over k",
			"polynomial_algebra_var(«hilbertCoefficients», i) ∈ «polynomials».carrier",
			By(
				scalars,
				iIn,
				polynomial_algebra.PolynomialAlgebraVarIn,
				polynomial_algebra.PolynomialAlgebraRingDef))
		inRing := a.Have(
			"the powers of Xᵢ over k are its powers in the ring of polynomials",
			"∀s:num. "+
				"    «power»(i, s) = "+
				"    monoid_pow(«polynomials».mul, "+
				"        «polynomials».one, "+
				"        polynomial_algebra_var(«hilbertCoefficients», i), "+
				"        s)",
			Simp(Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
			Basic())
		spanIdeal := a.Have(
			"the X(d) generate an ideal of the polynomials over k",
			"ring_ideal(«polynomials», ideal_span(«polynomials», «generators»))",
			By(generatorsIn, ring_ideal.SpanIdeal.Read(polynomials)))
		multiplicative := comm_ring.MulMonoidOn.Read(polynomials)
		noPower := a.Have(
			"no power of Xᵢ lies in that ideal",
			"∀s:num. «power»(i, s) ∉ ideal_span(«polynomials», «generators»)",
			Derive(func(c *Argument) {
				s := c.FixAs[Nat]("s")
				inSpan := c.SupposeNot()
				raised := c.TermAs[Nat]("N₀ + s")
				higher := c.Have(
					"then so does Xᵢ^(N₀ + s), which is Xᵢ^N₀ times Xᵢ^s",
					"«power»(i, N₀ + s) ∈ ideal_span(«polynomials», «generators»)",
					By(
						inSpan,
						spanIdeal,
						variableIn,
						inRing.At(raised),
						inRing.At(N0),
						inRing.At(s),
						comm_monoid.PowAddOn.Read(multiplicative).AsFact().At(variable, N0, s),
						comm_monoid.PowIn.Read(multiplicative).AsFact().At(variable, N0),
						ring_ideal.IdealMul.Read(spanIdeal)))
				form := c.Have(
					"Xᵢ^(N₀ + s) is a form of degree N₀ + s",
					"homogeneous_polynomial(«hilbertCoefficients», n, N₀ + s, «power»(i, N₀ + s))",
					By(
						scalars,
						iIn,
						At(homogeneous_polynomial.FormPower, K, n, one, variable, raised),
						At(homogeneous_polynomial.FormVariable, K, n, i),
						nat_arith.OneMul))
				past := c.Have(
					"N₀ + s is at least N₀",
					"N₀ ≤ N₀ + s",
					ByArith())
				graded := c.Have(
					"the forms of degree N₀ + s in the ideal are X(N₀ + s)",
					"«forms»(N₀ + s) ∩ ideal_span(«polynomials», «generators») = X(N₀ + s)",
					By(subK, subspace, closure, past, Read(GeneratedIdealForms, M).At(k, n, N0, raised, X)))
				c.Show(
					"so Xᵢ^(N₀ + s) lies in X(N₀ + s), which holds no power of Xᵢ",
					By(higher, form, past, graded, missing.At(raised), set_basic.InInter))
			}))
		p, primeFacts := a.ObtainAs[Set[_Polynomial]](
			"a prime ideal p of the polynomials over k holds the ideal and misses Xᵢ",
			"∃p:set((num → num) → A). "+
				"    prime_ideal(«polynomials», p) ∧ "+
				"    ideal_span(«polynomials», «generators») ⊆ p ∧ "+
				"    polynomial_algebra_var(«hilbertCoefficients», i) ∉ p",
			By(spanIdeal, variableIn, inRing, noPower, ring_ideal.PrimeAvoidingPowers.Read(polynomials)),
			Named("p"))
		prime := a.Conjuncts(
			primeFacts,
			"p is prime",
			"p holds the ideal the X(d) generate",
			"Xᵢ lies outside p")
		pIdeal := a.Have(
			"p is an ideal",
			"ring_ideal(«polynomials», p)",
			By(prime[0], ring_ideal.PrimeIdealIdeal))
		inP := a.Have(
			"every X(d), d ≥ N₀, lies in p",
			"∀d:num. ∀P:((num → num) → A). N₀ ≤ d ∧ P ∈ X(d) ⇒ P ∈ p",
			Derive(func(c *Argument) {
				c.FixAs[Nat]("d")
				c.FixAs[_Polynomial]("P")
				given := c.Assume()
				c.Show(
					"a member of X(d) is a generator, in the ideal, in p",
					By(given, prime[1], ring_ideal.SpanContains.At(polynomialRing, generators), set_basic.SubsetDef))
			}))
		generic := a.Conjuncts(
			a.Have(
				"p has a generic point y in the fraction field of the polynomials modulo p, normalized at i",
				"field_on(«fractions») ∧ "+
					"(∃σ:(A → set(prod(set((num → num) → A), set((num → num) → A)))). "+
					"∃y:(num → set(prod(set((num → num) → A), set((num → num) → A)))). "+
					"    ring_homomorphism(«hilbertCoefficients», field_ring(«fractions»), σ) ∧ "+
					"    (∀j:num. y(j) ∈ «fractions».carrier) ∧ "+
					"    y(i) = «fractions».one ∧ "+
					"    (∀j:num. "+
					"        j ≤ n ⇒ "+
					"        (y(j) = «fractions».zero ⇔ polynomial_algebra_var(«hilbertCoefficients», j) ∈ p)) ∧ "+
					"    (∀j:num. n < j ⇒ y(j) = «fractions».zero) ∧ "+
					"    (∀P:((num → num) → A). "+
					"        (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ⇒ "+
					"        (polynomial_algebra_eval(«hilbertCoefficients», field_ring(«fractions»), σ, y, P) = "+
					"            «fractions».zero ⇔ "+
					"            P ∈ p)))",
				By(
					scalars,
					prime[0],
					iIn,
					prime[2],
					At(projective_generic_point.PrimeIdealGenericPoint, K, n, i, p))),
			"the fraction field is a field",
			"it holds the generic point of p")
		L, _ := a.LetAs[FieldOps[_Fraction]]("L", "«fractions»")
		σ, y, atY := a.Unpack2As[Fun[A, _Fraction], Fun[Nat, _Fraction]](generic[1], "σ", "y")
		ofY := a.Conjuncts(
			atY,
			"σ is a ring homomorphism from k",
			"y lies in L",
			"y(i) is one",
			"up to n, y(j) is zero exactly when Xⱼ lies in p",
			"its coordinates past n are zero",
			"a form over k vanishes at y exactly when it lies in p")
		D := a.TermAs[Nat]("N₀ + b")
		xD := a.TermAs[Set[_Polynomial]]("X(N₀ + b)")
		pastD := a.Have(
			"N₀ + b is at least N₀ and at least b",
			"N₀ ≤ N₀ + b ∧ b ≤ N₀ + b",
			ByArith())
		pInside := a.Have(
			"p lies among the polynomials over k",
			"p ⊆ «polynomials».carrier",
			By(pIdeal, ring_ideal.IdealSubset))
		spanP := a.Have(
			"the ideal p generates is p",
			"ideal_span(«polynomials», p) = p",
			By(pIdeal, ring_ideal.SpanOfIdeal))
		xInP := a.Have(
			"X(N₀ + b) lies in it",
			"X(N₀ + b) ⊆ ideal_span(«polynomials», p)",
			spanP.Rw(),
			BySets(pastD, inP))
		codimension := a.Have(
			"so the Hilbert function of p at N₀ + b is at most the codimension of X(N₀ + b)",
			"projective_hilbert_function(field_ring(M), k, n, p, N₀ + b) ≤ "+
				"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(N₀ + b), X(N₀ + b)))",
			By(
				subK,
				pInside,
				pastD,
				subspace.At(D),
				xInP,
				Read(projective_curve.HilbertFunctionBelowCodimension, M).At(k, n, D, p, xD)))
		hilbert := a.Have(
			"which is at most b",
			"projective_hilbert_function(field_ring(M), k, n, p, N₀ + b) ≤ b",
			ByArith(codimension, pastD, bound.At(D)))
		formsAtY := a.Have(
			"a form of degree N₀ + b vanishes at y exactly when it lies in the ideal p generates, p itself",
			Statement{
				Binders: "∀P:((num → num) → A).",
				Hypotheses: []string{
					"homogeneous_polynomial(«hilbertCoefficients», n, N₀ + b, P)",
				},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero ⇔ " +
					"P ∈ ideal_span(«polynomials», p)",
			},
			By(ofY[5], pIdeal, ring_ideal.SpanOfIdeal))
		algebraic := a.Have(
			"every coordinate of y is algebraic over σ(k): a transcendental "+
				"one would give b + 1 independent values of forms of degree N₀ + b",
			"∀r:num. r ≤ n ⇒ algebraic_over(L, image(σ, k), y(r))",
			Derive(func(c *Argument) {
				r := c.FixAs[Nat]("r")
				rIn := c.Assume()
				transcendental := c.SupposeNot()
				many := c.Have(
					"then b + 1 is at most the Hilbert function of p at N₀ + b",
					"b + 1 ≤ projective_hilbert_function(field_ring(M), k, n, p, N₀ + b)",
					By(
						M,
						generic[0],
						subK,
						ofY[0],
						ofY[1],
						formsAtY,
						iIn,
						ofY[2],
						rIn,
						transcendental,
						pastD,
						At(projective_curve.TranscendentalCoordinateBound, m, L, k, n, D, p, σ, y, i, r, b)))
				c.Show(
					"which is at most b",
					ByArith(many, hilbert))
			}))
		x, image := a.UnpackAs[Fun[Nat, A]](
			GroupPremises(
				M,
				generic[0],
				closed,
				subK,
				ofY[0],
				ofY[1],
				ofY[4],
				algebraic,
				At(projective_generic_point.AlgebraicPointIntoAmbient, m, L, k, n, σ, y)),
			"x")
		ofX := a.Conjuncts(
			image,
			"x lies in M",
			"x is zero where y is",
			"x is one where y is",
			"a polynomial over k vanishes at x exactly when it vanishes at y")
		vanishing := a.Have(
			"every member of the X(d), d ≥ N₀, vanishes at x: it lies in p, so vanishes at y",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ «generators»"},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λc:A. c, x, P) = M.zero",
			},
			Derive(func(c *Argument) {
				P := c.FixAs[_Polynomial]("P")
				member := c.Assume()
				_, inX := c.UnpackAs[Nat](member, "d")
				c.Show(
					"a form in p vanishes at y, and so at x",
					By(
						inX,
						inForms,
						inP,
						ofY[5].At(P),
						ofX[3].At(P),
						homogeneous_polynomial.FormPolynomial,
						polynomial_algebra.PolynomialAlgebraRingDef))
			}))
		xOne := a.Have(
			"x(i) is one, so not zero",
			"x(i) ≠ M.zero",
			By(Normalized, ofY[2], ofX[2], field.OneNotZeroOn.Read(M)))
		beyond := a.Have(
			"the coordinates of x past n are zero",
			"∀j:num. n < j ⇒ x(j) = M.zero",
			By(ofY[4], ofX[1]))
		formsE := a.Have(
			"the members of the X(d) are forms",
			Statement{
				Binders: "∀P:((num → num) → A).",
				Hypotheses: []string{
					"P ∈ «generators»",
				},
				Conclusion: "∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
			},
			Derive(func(c *Argument) {
				c.FixAs[_Polynomial]("P")
				member := c.Assume()
				d, inX := c.UnpackAs[Nat](member, "d")
				c.Take(d)
				c.Show(
					"a member of X(d) is a form of degree d",
					By(inX, inForms))
			}))
		_, normalized := a.ObtainAs[A](
			"dividing x by its first nonzero coordinate puts it in projective space, still a zero of the X(d)",
			"∃c:A. "+
				"    c ∈ M.carrier ∧ "+
				"    c ≠ M.zero ∧ "+
				"    (λj:num. x(j) * c) ∈ projective_equation_points(field_ring(M), k, M.carrier, n, «generators»)",
			By(
				M,
				subK,
				field.CarrierSubfield.Read(M),
				formsE,
				ofX[0],
				beyond,
				iIn,
				xOne,
				vanishing,
				At(projective_curve.PointNormalization, m, k, a.TermAs[Set[A]]("M.carrier"), n, i, generators, x)),
			Named("c"))
		pointParts := a.Conjuncts(
			normalized,
			"c lies in M",
			"c is not zero",
			"x·c lies in projective space and kills the X(d)")
		scaledPoint := a.Conjuncts(
			a.Unfolded(pointParts[2], projective_curve.ProjectiveEquationPointsDef),
			"the coordinates of x·c up to n lie in M",
			"those past n are zero",
			"its first nonzero coordinate is one",
			"every member of the X(d) vanishes there")
		a.Show(
			"x·c is the common zero",
			Witness(a.TermAs[Fun[Nat, A]]("λj:num. x(j) * c")),
			SplitConj(
				Case(
					"a point of projective space over M",
					Unfold(projective_curve.ProjectiveEquationPointsDef),
					BySets(scaledPoint[0], scaledPoint[1], scaledPoint[2])),
				Case(
					"at which every member of X(d), d ≥ N₀, vanishes",
					BySets(scaledPoint[3]))))
	}),
})}

// GradedNullstellensatz — the projective Nullstellensatz for a homogeneous
// ideal given by its graded pieces: subspaces X(d) of the forms of degree d
// over a subfield k of an algebraically closed field M, from degree N₀ on
// closed under multiplication by the variables and of codimension at most b,
// with no point of projective space over M at which every one of them
// vanishes, hold every form of large degree. Either every variable has a
// power in X, and those powers generate every form of large degree
// (VariablePowersGenerate), or some variable has none, and X has a common
// zero (CommonZeroWithoutPower), which the last hypothesis rules out.
var GradedNullstellensatz = gradedNullstellensatzThm{family.Add(registry.ProofEntry{
	Name: "GradedNullstellensatz",
	Key:  "prop_94224dc50ccf640b",
	Reading: "The codimension bound b is what the proof reads in place of a Noetherian " +
		"hypothesis, and only where a variable Xᵢ has no power in X: there a prime of the " +
		"polynomials over k holds X and misses Xᵢ, the bound makes every coordinate of the prime's " +
		"generic point algebraic over k, and that algebraic point has an image in the closed M, a " +
		"common zero of X (CommonZeroWithoutPower). Without the last hypothesis it fails at a common " +
		"zero z, where every member of X vanishes and the power of a variable nonzero at z does not.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n b N₀:num. ∀X:(num → set((num → num) → A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"∀d:num. N₀ ≤ d ⇒ submodule(«hilbertCoefficients», «formSpace»(d), X(d))",
			"∀d i:num. ∀P:((num → num) → A). " +
				"    N₀ ≤ d ∧ i ≤ n ∧ P ∈ X(d) ⇒ " +
				"    polynomial_algebra_mul(«hilbertCoefficients», " +
				"        polynomial_algebra_var(«hilbertCoefficients», i), " +
				"        P) ∈ " +
				"    X(d + 1)",
			"∀d:num. N₀ ≤ d ⇒ module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), X(d))) ≤ b",
			"∀z:(num → A). " +
				"    z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, ∅) ⇒ " +
				"    ∃d:num. ∃P:((num → num) → A). " +
				"        N₀ ≤ d ∧ " +
				"        P ∈ X(d) ∧ " +
				"        polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, P) ≠ M.zero",
		},
		Conclusion: "∃N:num. ∀d:num. N ≤ d ⇒ «forms»(d) ⊆ X(d)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "power", Text: "λl:num. λs:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», l), " +
				"        s)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, b, N0 *Expr[Nat],
		X *Arrow2[Nat, _Polynomial, Bool],
		closed, subK, subspace, closure, bound, noZero Fact,
	) {
		a.Cases(a.TermAs[Bool]("∀i:num. i ≤ n ⇒ ∃a:num. N₀ ≤ a ∧ «power»(i, a) ∈ X(a)"))
		a.When(
			"every variable has a power in X",
			func(c *Argument, powers Fact) {
				c.Show(
					"and those powers generate every form of large degree",
					By(subK, subspace, closure, powers, Read(VariablePowersGenerate, M).At(k, n, N0, X)))
			})
		a.Otherwise(
			"some variable has no power in X",
			func(c *Argument, notAll Fact) {
				i, missing := c.ObtainAs[Nat](
					"a variable Xᵢ, i ≤ n, none of whose powers lies in X",
					"∃i:num. i ≤ n ∧ (∀a:num. N₀ ≤ a ⇒ «power»(i, a) ∉ X(a))",
					By(notAll))
				z, zero := c.ObtainAs[Fun[Nat, A]](
					"then X has a common zero z in projective space over M",
					"∃z:(num → A). "+
						"    z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, ∅) ∧ "+
						"    (∀d:num. ∀P:((num → num) → A). "+
						"        N₀ ≤ d ∧ P ∈ X(d) ⇒ "+
						"        polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, P) = M.zero)",
					By(
						closed,
						subK,
						subspace,
						closure,
						bound,
						missing,
						Read(CommonZeroWithoutPower, M).At(k, n, b, N0, i, X)))
				c.Show(
					"which the last hypothesis rules out: some member of X does not vanish at z",
					By(zero, noZero.At(z)))
			})
	}),
})}
