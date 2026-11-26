// polynomial_partial.go — the partial derivative on the polynomial model
// itself: it keeps the polynomials of a set of variables, is additive and
// subtractive, kills the constants, takes a variable to one or zero, and
// is nonzero in only finitely many variables, all of them in the set.
// These are the laws the free algebra's derivative reads through its
// injection, stated where the coefficients are read directly. Beside them
// stand the Leibniz rule at a variable, the derivative's commuting with
// carrying the coefficients along a ring homomorphism, and, by induction
// over the polynomials, the first-order expansion of a polynomial modulo the
// square of an ideal.

package partial_derivative

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialPartialIn — the partial derivative of a polynomial of S is a
// polynomial of S: its coefficients are numerals times coefficients of f,
// in R; where it is nonzero, f is nonzero at the monomial raised at x, a
// monomial of S, and so the monomial itself is a monomial of S too; and
// its support lies in the preimage of the finite support of f under
// raising, which is one-to-one.
var PolynomialPartialIn = polynomialPartialInThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialIn",
	Key:  "prop_7495ead37c257c5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀x:D. ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_partial(R, x, f) ∈ polynomial_algebra(R, S)",
		Abbrev: Abbrev{
			{Name: "raise", Text: "λm:(D → num). λy:D. m(y) + monomial_var(x, y)"},
			{Name: "partialSupport", Text: "fun_support(R.zero, " +
				"    λm:(D → num). polynomial_algebra_partial(R, x, f, m))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			x *Expr[D],
			f *Arrow[Fun[D, Nat], A],
			ring, polynomial Fact,
		) {
			raise := a.TermAs[Fun[Fun[D, Nat], Fun[D, Nat]]]("«raise»")
			support := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)")
			partialSupport := a.TermAs[Set[Fun[D, Nat]]]("«partialSupport»")
			preimage := a.TermAs[Set[Fun[D, Nat]]]("preimage_on(𝕌, «raise», fun_support(R.zero, f))")
			parts := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in R")
			numerals := a.Have(
				"every numeral lies in R",
				"∀j:num. monoid_pow(R.add, R.zero, R.one, j) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
			coefficients := a.Have(
				"the coefficients of the derivative lie in R, each a numeral times a coefficient of f",
				"∀m:(D → num). polynomial_algebra_partial(R, x, f, m) ∈ R.carrier",
				By(numerals, parts[2], PolynomialAlgebraPartialDef, comm_ring.MulIn.Read(ring)))
			raisedNonzero := a.Have(
				"where the derivative is nonzero, f is nonzero at the raised monomial",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"polynomial_algebra_partial(R, x, f, m) ≠ R.zero"},
					Conclusion: "f(λy:D. m(y) + monomial_var(x, y)) ≠ R.zero",
				},
				By(numerals, PolynomialAlgebraPartialDef, comm_ring.MulRightZeroOn.Read(ring)))
			lowering := a.Have(
				"a monomial of S raised at x was a monomial of S",
				"∀m:(D → num). (λy:D. m(y) + monomial_var(x, y)) ∈ monomials(S) ⇒ m ∈ monomials(S)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m")
					raised := b.Conjuncts(
						b.Unfolded(b.Assume(), polynomial_algebra.MonomialsDef),
						"m raised at x is finitely supported",
						"and its variables lie in S")
					pointwise := b.Have(
						"an exponent of m that is not zero stays so when raised",
						"∀y:D. m(y) ≠ 0 ⇒ m(y) + monomial_var(x, y) ≠ 0",
						ByArith())
					smaller := b.Have(
						"so the support of m lies in that of m raised",
						"fun_support(0, m) ⊆ fun_support(0, λy:D. m(y) + monomial_var(x, y))",
						BySets(pointwise))
					finite := b.Have(
						"so m is finitely supported",
						"finite_support(0, m)",
						Unfold(function_module.FiniteSupportDef),
						By(
							b.Unfolded(raised[0], function_module.FiniteSupportDef),
							smaller,
							finite_set.FiniteSubset.At(
								b.TermAs[Set[D]]("fun_support(0, m)"),
								b.TermAs[Set[D]]("fun_support(0, λy:D. m(y) + monomial_var(x, y))"))))
					b.Show(
						"and its variables lie in S, being variables of m raised",
						Unfold(polynomial_algebra.MonomialsDef),
						By(finite, raised[1], pointwise))
				}))
			onMonomials := a.Have(
				"every monomial where the derivative is nonzero is a monomial of S, f being nonzero at it raised",
				"«partialSupport» ⊆ monomials(S)",
				BySets(raisedNonzero, parts[1], lowering))
			injective := a.Have(
				"raising the exponent of x is one-to-one",
				"injective_on(𝕌, «raise»)",
				Unfold(functions.InjectiveOnDef),
				By(nat_arith.AddEqLCancel, nat_arith.AddSym))
			covered := a.Have(
				"the support of the derivative lies in the preimage of the support of f under raising",
				"«partialSupport» ⊆ preimage_on(𝕌, «raise», fun_support(R.zero, f))",
				BySets(raisedNonzero))
			finite := a.Have(
				"so the derivative is nonzero at finitely many monomials",
				"finite(«partialSupport»)",
				By(
					parts[0],
					injective,
					covered,
					finite_set.FiniteImageInjGeneral.At(raise, a.TermAs[Set[Fun[D, Nat]]]("𝕌"), support),
					finite_set.FiniteSubset.At(partialSupport, preimage)))
			a.Show(
				"a polynomial of S: nonzero at finitely many monomials, "+
					"all of them monomials of S, with coefficients in R",
				Simp(Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				By(finite, onMonomials, coefficients))
		}),
	Reading: "At a variable x outside S every m + x has x in its support, off the monomials " +
		"of S, so the derivative is the zero polynomial, a polynomial of S. comm_ring_on(R) " +
		"keeps the numeral m(x) + 1, and its product with a coefficient of f, in R's carrier.",
})}

// PolynomialPartialSupportFinite — a polynomial of S has a nonzero partial
// derivative in only finitely many variables, all of them in S: a nonzero
// derivative in x has a nonzero coefficient at some monomial m, so f is
// nonzero at m with the exponent of x raised by one, a monomial with x
// among its variables. The variables with a nonzero derivative are thus
// among the variables of the monomials where f is nonzero — finitely many
// monomials of S, each with finitely many variables, all of them in S.
var PolynomialPartialSupportFinite = polynomialPartialSupportFiniteThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialSupportFinite",
	Key:  "prop_1996b63dac4c7a5a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "finite(«partialVariables») ∧ «partialVariables» ⊆ S",
		Abbrev: Abbrev{
			{Name: "partialVariables", Text: "fun_support(fun_zero, " +
				"    λx:D. polynomial_algebra_partial(R, x, f))"},
			{Name: "supportVariables", Text: "{y | " +
				"    m:(D → num), " +
				"    y:D | " +
				"    m ∈ fun_support(R.zero, f) ∧ y ∈ fun_support(0, m)}"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			f *Arrow[Fun[D, Nat], A],
			ring, polynomial Fact,
		) {
			parts := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in R")
			raisedNonzero := a.Have(
				"where the derivative in x is nonzero at m, f is nonzero at m raised at x",
				Statement{
					Binders:    "∀x:D. ∀m:(D → num).",
					Hypotheses: []string{"polynomial_algebra_partial(R, x, f, m) ≠ R.zero"},
					Conclusion: "f(λy:D. m(y) + monomial_var(x, y)) ≠ R.zero",
				},
				By(
					comm_ring.OneIn.Read(ring),
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
					comm_ring.MulRightZeroOn.Read(ring),
					PolynomialAlgebraPartialDef))
			witnessed := a.Have(
				"a variable with a nonzero derivative is a variable of a monomial where f is nonzero",
				"∀x:D. polynomial_algebra_partial(R, x, f) ≠ fun_zero ⇒ ∃n:(D → num). f(n) ≠ R.zero ∧ n(x) ≠ 0",
				Derive(func(b *Argument) {
					x := b.FixAs[D]("x")
					nonzero := b.Assume()
					m, coefficient := b.ObtainAs[Fun[D, Nat]](
						"the derivative has a nonzero coefficient at some monomial m",
						"∃m:(D → num). polynomial_algebra_partial(R, x, f, m) ≠ R.zero",
						By(nonzero, function_module.FunZeroDef))
					b.Take(b.TermAs[Fun[D, Nat]]("λy:D. m(y) + monomial_var(x, y)"))
					b.Show(
						"f is nonzero at m raised at x, whose exponent at x is m(x) + 1",
						ByArith(coefficient, raisedNonzero.At(x, m), polynomial_algebra.MonomialVarValues.At(x)))
				}))
			covered := a.Have(
				"so the variables with a nonzero derivative are among "+
					"the variables of the monomials where f is nonzero",
				"«partialVariables» ⊆ «supportVariables»",
				BySets(witnessed))
			monomialVariables := a.Have(
				"a monomial where f is nonzero is a monomial of S: finitely many variables, all of them in S",
				"∀m:(D → num). m ∈ fun_support(R.zero, f) ⇒ finite(fun_support(0, m)) ∧ (∀y:D. m(y) ≠ 0 ⇒ y ∈ S)",
				By(parts[1], set_basic.SubsetDef, polynomial_algebra.MonomialSupport))
			finite := a.Have(
				"finitely many monomials with finitely many variables each have finitely many variables in all",
				"finite(«supportVariables»)",
				By(
					parts[0],
					monomialVariables,
					finite_set.FiniteProductDependent.At(
						a.TermAs[Fun2[Fun[D, Nat], D, D]]("λm:(D → num). λy:D. y"),
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
						a.TermAs[Fun2[Fun[D, Nat], D, Bool]]("λm:(D → num). fun_support(0, m)"))))
			inS := a.Have(
				"and all of them lie in S",
				"«supportVariables» ⊆ S",
				BySets(monomialVariables))
			a.Show(
				"the variables with a nonzero derivative lie among finitely many variables of S",
				SplitConj(
					Case(
						"finitely many variables have a nonzero derivative: a subset of a finite set",
						By(finite, covered, finite_set.FiniteSubset)),
					Case(
						"all of them lie in S: a subset of a subset of S",
						By(covered, inS, set_order.SubsetTrans))))
		}),
})}

// PolynomialPartialLinear — the partial derivative of a sum, and of a
// difference, of two polynomials of S is the sum, and the difference, of
// their derivatives: coefficient by coefficient, the numeral m(x) + 1
// distributes over the sum and the difference of the coefficients of f and
// g at the raised monomial, which lie in R.
var PolynomialPartialLinear = polynomialPartialLinearThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialLinear",
	Key:  "prop_b2ba47b4fbf5cc85",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀x:D. ∀f g:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_partial(R, x, polynomial_algebra_ring(R, S).add(f, g)) = " +
			"polynomial_algebra_ring(R, S).add(polynomial_algebra_partial(R, x, f), " +
			"    polynomial_algebra_partial(R, x, g)) ∧ " +
			"polynomial_algebra_partial(R, x, polynomial_algebra_ring(R, S).sub(f, g)) = " +
			"polynomial_algebra_ring(R, S).sub(polynomial_algebra_partial(R, x, f), " +
			"    polynomial_algebra_partial(R, x, g))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			x *Expr[D],
			f, g *Arrow[Fun[D, Nat], A],
			ring, fIn, gIn Fact,
		) {
			fParts := a.Conjuncts(
				a.Simplified(fIn, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in R")
			gParts := a.Conjuncts(
				a.Simplified(gIn, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"g is nonzero at finitely many monomials",
				"every monomial where g is nonzero is a monomial of S",
				"every coefficient of g lies in R")
			numeral := comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))
			sum := a.Have(
				"the derivative of the sum is the sum of the derivatives",
				"polynomial_algebra_partial(R, x, polynomial_algebra_ring(R, S).add(f, g)) = "+
					"polynomial_algebra_ring(R, S).add(polynomial_algebra_partial(R, x, f), "+
					"    polynomial_algebra_partial(R, x, g))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Fun[D, Nat]]("m")
					raised := b.TermAs[Fun[D, Nat]]("λy:D. m(y) + monomial_var(x, y)")
					b.Show(
						"at m the numeral m(x) + 1 distributes over the two coefficients at m raised",
						Simp(
							Fwd(PolynomialAlgebraPartialDef),
							Fwd(polynomial_algebra.PolynomialAlgebraRingDef),
							Fwd(function_module.FunAddDef)),
						ByArith(
							ring,
							comm_ring.OneIn.Read(ring),
							numeral.AsFact().At(b.TermAs[A]("R.one"), b.TermAs[Nat]("m(x) + 1")),
							fParts[2].At(raised),
							gParts[2].At(raised)))
				}))
			difference := a.Have(
				"and the derivative of the difference is the difference of the derivatives",
				"polynomial_algebra_partial(R, x, polynomial_algebra_ring(R, S).sub(f, g)) = "+
					"polynomial_algebra_ring(R, S).sub(polynomial_algebra_partial(R, x, f), "+
					"    polynomial_algebra_partial(R, x, g))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Fun[D, Nat]]("m")
					raised := b.TermAs[Fun[D, Nat]]("λy:D. m(y) + monomial_var(x, y)")
					b.Show(
						"at m the numeral m(x) + 1 distributes over the difference of the two coefficients at m raised",
						Simp(Fwd(PolynomialAlgebraPartialDef), Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
						ByArith(
							ring,
							comm_ring.OneIn.Read(ring),
							numeral.AsFact().At(b.TermAs[A]("R.one"), b.TermAs[Nat]("m(x) + 1")),
							fParts[2].At(raised),
							gParts[2].At(raised)))
				}))
			a.Show(
				"the derivative keeps both the sum and the difference",
				By(sum, difference))
		}),
	Reading: "The polynomials f and g are read only for their coefficients lying in " +
		"R's carrier, where the numeral distributes; the ring's sum and difference on " +
		"the polynomials of S act coefficient by coefficient, so S itself plays no part.",
})}

// PolynomialPartialVarMul — the Leibniz rule at a variable: the partial
// derivative in x of X_y·f is X_y times the derivative of f, plus f itself
// when x = y. Multiplying by a variable v shifts the coefficients, X_v
// being the term R.one at the monomial of v (PolynomialAlgebraTermMul): at
// a monomial w the coefficient of X_v·g is g at w lowered by v where w(v)
// is positive, and zero where w(v) is zero, a w of infinite support
// lowering to one where g vanishes. So at x ≠ y both sides are zero where
// m(y) = 0, m raised at x having no exponent at y either, and elsewhere
// both are (m(x) + 1)·f at m raised at x and lowered at y, the two moves
// commuting; at x = y the left side is (m(x) + 1)·f(m), and the right is
// m(x)·f(m) + f(m).
var PolynomialPartialVarMul = polynomialPartialVarMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialVarMul",
	Key:  "prop_cbeeb9904273df7d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀x y:D. ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_partial(R, " +
			"    x, " +
			"    polynomial_algebra_mul(R, polynomial_algebra_var(R, y), f)) = " +
			"fun_add(polynomial_algebra_mul(R, " +
			"        polynomial_algebra_var(R, y), " +
			"        polynomial_algebra_partial(R, x, f)), " +
			"    COND(x = y, f, fun_zero))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			x, y *Expr[D],
			f *Arrow[Fun[D, Nat], A],
			ring, polynomial Fact,
		) {
			shift := a.Have(
				"multiplying by the variable v shifts the coefficients up by the monomial of v",
				Statement{
					Binders:    "∀v:D. ∀g:((D → num) → A). ∀w:(D → num).",
					Hypotheses: []string{"g ∈ polynomial_algebra(R, S)"},
					Conclusion: "polynomial_algebra_mul(R, polynomial_algebra_var(R, v), g, w) = " +
						"COND(w(v) = 0, R.zero, g(λz:D. w(z) - monomial_var(v, z)))",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[D]("v")
					b.FixAs[Fun[Fun[D, Nat], A]]("g")
					b.FixAs[Fun[D, Nat]]("w")
					gParts := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
						"g is nonzero at finitely many monomials",
						"every monomial where g is nonzero is a monomial of S",
						"every coefficient of g lies in R")
					unit := b.Conjuncts(
						polynomial_algebra.MonomialVarValues.At(v),
						"the monomial of v is one at v",
						"and zero at every other variable")
					lowered := b.TermAs[Fun[D, Nat]]("λz:D. w(z) - monomial_var(v, z)")
					b.Do(Simp(
						Fwd(polynomial_algebra.PolynomialAlgebraVarDef),
						Fwd(polynomial_algebra.PolynomialAlgebraTermMul),
						Fwd(comm_ring.OneIn.Read(ring)),
						Fwd(gParts[2])))
					finite := b.Assuming(
						b.Term("finite_support(0, w)"),
						"at a w of infinite support the product is zero, and "+
							"so is g at w lowered, which has infinite support too",
						Given(func(c *Argument, infinite Fact) {
							pointwise := c.Have(
								"an exponent of w that is not zero stays so when lowered at v, except at v",
								"∀z:D. w(z) ≠ 0 ⇒ w(z) - monomial_var(v, z) ≠ 0 ∨ z = v",
								ByArith(polynomial_algebra.MonomialVarValues.At(v)))
							covered := c.Have(
								"so the support of w lies in that of w lowered, with v inserted",
								"fun_support(0, w) ⊆ insert(v, fun_support(0, λz:D. w(z) - monomial_var(v, z)))",
								BySets(pointwise))
							loweredInfinite := c.Have(
								"so w lowered has infinite support",
								"¬finite_support(0, λz:D. w(z) - monomial_var(v, z))",
								BySets(
									infinite,
									covered,
									function_module.FiniteSupportDef,
									finite_set.FiniteInsert,
									finite_set.FiniteSubset.At(
										c.TermAs[Set[D]]("fun_support(0, w)"),
										c.TermAs[Set[D]]("insert(v, fun_support(0, λz:D. w(z) - monomial_var(v, z)))"))))
							vanishes := c.Have(
								"so it is no monomial of S, and g vanishes there",
								"g(λz:D. w(z) - monomial_var(v, z)) = R.zero",
								BySets(loweredInfinite, gParts[1], polynomial_algebra.MonomialsDef))
							c.Show(
								"both sides are zero",
								By(infinite, vanishes))
						}))
					b.Cases(b.TermAs[Bool]("w(v) = 0"))
					b.When(
						"where w(v) = 0 the monomial of v, one at v, is not below w, and both sides are zero",
						func(c *Argument, zeroAt Fact) {
							c.Show(
								"one does not lie below zero",
								By(finite, zeroAt, unit[0], nat_arith.OneNotZero, nat_order.LessEqZeroClause))
						})
					b.Otherwise(
						"where w(v) is positive the monomial of v lies below "+
							"w, and the coefficient is one times g at w lowered by v",
						func(c *Argument, positive Fact) {
							isBelow := c.Have(
								"the monomial of v lies below w",
								"∀z:D. monomial_var(v, z) ≤ w(z)",
								Derive(func(d *Argument) {
									z := d.FixAs[D]("z")
									d.Cases(d.TermAs[Bool]("z = v"))
									d.When(
										"at v the exponent of w is positive",
										func(e *Argument, same Fact) {
											e.Do(same.Rw())
											e.Show(
												"so it is at least one",
												ByArith(positive, unit[0]))
										})
									d.Otherwise(
										"elsewhere the monomial of v is zero",
										func(e *Argument, other Fact) {
											e.Show(
												"and zero lies below every exponent",
												ByArith(other, unit[1].At(z)))
										})
								}))
							c.Show(
								"which is g at w lowered by v",
								By(
									finite,
									positive,
									isBelow,
									gParts[2].At(lowered),
									comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
						})
				}))
			partialIn := a.Have(
				"the derivative of f is a polynomial of S",
				"polynomial_algebra_partial(R, x, f) ∈ polynomial_algebra(R, S)",
				By(ring, polynomial, PolynomialPartialIn))
			unitX := a.Conjuncts(
				polynomial_algebra.MonomialVarValues.At(x),
				"the monomial of x is one at x",
				"and zero at every other variable")
			a.Do(Funext())
			m := a.FixAs[Fun[D, Nat]]("m")
			coefficient := a.Have(
				"at m, the products by X_y written by the shift: (m(x) "+
					"+ 1)·(X_y·f)(m raised at x) = (X_y·∂ₓf)(m) + δₓᵧ·f(m)",
				"monoid_pow(R.add, R.zero, R.one, m(x) + 1) * "+
					"COND(m(y) + monomial_var(x, y) = 0, "+
					"    R.zero, "+
					"    f(λz:D. m(z) + monomial_var(x, z) - monomial_var(y, z))) = "+
					"COND(m(y) = 0, "+
					"    R.zero, "+
					"    monoid_pow(R.add, R.zero, R.one, m(x) - monomial_var(y, x) + 1) * "+
					"    f(λz:D. m(z) - monomial_var(y, z) + monomial_var(x, z))) + "+
					"COND(x = y, f(m), R.zero)",
				Derive(func(b *Argument) {
					// Unpacked inside this Derive: the unpack rewrites polynomial in
					// place, and the rewrite stays in this branch, so the closing
					// Show still reads the membership.
					coefficients := b.Conjuncts(
						b.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
						"f is nonzero at finitely many monomials",
						"every monomial where f is nonzero is a monomial of S",
						"every coefficient of f lies in R")[2]
					b.Cases(b.TermAs[Bool]("x = y"))
					b.When(
						"in its own variable the derivative of X_x·f picks up f itself",
						func(c *Argument, same Fact) {
							c.Do(same.RwRev())
							lowerRaise := c.Have(
								"lowering at x undoes raising at x",
								"(λz:D. m(z) + monomial_var(x, z) - monomial_var(x, z)) = m",
								Funext(),
								ByArith())
							raisedNonzero := c.Have(
								"the exponent of x in m raised at x is positive",
								"m(x) + monomial_var(x, x) ≠ 0",
								ByArith(unitX[0]))
							c.Do(lowerRaise.Rw())
							c.Cases(c.TermAs[Bool]("m(x) = 0"))
							c.When(
								"where m(x) = 0 the numeral is one, and X_x times the derivative contributes nothing at m",
								func(d *Argument, zeroAt Fact) {
									d.Show(
										"one times f(m) is f(m)",
										ByArith(ring, zeroAt, unitX[0], coefficients.At(m)))
								})
							c.Otherwise(
								"where m(x) is positive, the numeral m(x) + 1 is m(x) plus one",
								func(d *Argument, positive Fact) {
									exponent := d.Have(
										"the lowered exponent of x plus one is m(x)",
										"m(x) - monomial_var(x, x) + 1 = m(x)",
										ByArith(positive, unitX[0]))
									additive := comm_ring.AddMonoidOn.Read(ring)
									numeral := d.Have(
										"the numeral m(x) + 1 is the numeral m(x) plus one",
										"monoid_pow(R.add, R.zero, R.one, m(x) + 1) = monoid_pow(R.add, R.zero, R.one, m(x)) + R.one",
										By(
											ring,
											comm_ring.OneIn.Read(ring),
											comm_monoid.PowOneOn.Read(additive),
											comm_monoid.PowAddOn.Read(additive).AsFact().At(
												d.TermAs[A]("R.one"), d.TermAs[Nat]("m(x)"), d.TermAs[Nat]("1"))))
									raiseLower := d.Have(
										"lowering the exponent at x by one and raising it again restores m, m(x) being positive",
										"(λz:D. m(z) - monomial_var(x, z) + monomial_var(x, z)) = m",
										ByArith(positive, polynomial_algebra.MonomialLowerRaise.At(m, x, d.TermAs[Nat]("1"))))
									d.Do(raiseLower.Rw(), exponent.Rw(), numeral.Rw())
									d.Show(
										"(m(x) + 1)·f(m) is m(x)·f(m) plus f(m)",
										ByArith(
											ring,
											positive,
											raisedNonzero,
											coefficients.At(m),
											comm_ring.OneIn.Read(ring),
											comm_monoid.PowIn.Read(additive).AsFact().At(d.TermAs[A]("R.one"), d.TermAs[Nat]("m(x)"))))
								})
						})
					b.Otherwise(
						"in another variable X_y passes through the derivative",
						func(c *Argument, other Fact) {
							unitY := c.Conjuncts(
								polynomial_algebra.MonomialVarValues.At(y),
								"the monomial of y is one at y",
								"and zero at every other variable")
							disjoint := c.Have(
								"no variable carries both monomials",
								"∀z:D. monomial_var(x, z) = 0 ∨ monomial_var(y, z) = 0",
								By(Normalized, other, unitX[1], unitY[1]))
							swap := c.Have(
								"raising at x and lowering at y commute",
								"(λz:D. m(z) + monomial_var(x, z) - monomial_var(y, z)) = "+
									"(λz:D. m(z) - monomial_var(y, z) + monomial_var(x, z))",
								Funext(),
								c.ForEach(func(z *Expr[D]) Action { return ByArith(disjoint.At(z)) }))
							c.Do(swap.Rw())
							raised := c.TermAs[Fun[D, Nat]]("λz:D. m(z) - monomial_var(y, z) + monomial_var(x, z)")
							c.Cases(c.TermAs[Bool]("m(y) = 0"))
							c.When(
								"where m(y) = 0 both sides are zero",
								func(d *Argument, zeroAt Fact) {
									d.Show(
										"a numeral times zero is zero",
										ByArith(ring, other, zeroAt, unitX[1].At(y)))
								})
							c.Otherwise(
								"where m(y) is positive both sides are (m(x) + 1)·f at m raised at x and lowered at y",
								func(d *Argument, positive Fact) {
									d.Show(
										"the lowered exponent of x is m(x)",
										ByArith(ring, other, positive, coefficients.At(raised), unitX[1].At(y), unitY[1].At(x)))
								})
						})
				}))
			a.Show(
				"unfolding the derivative and the shift, the claim at m is that equation",
				Simp(Fwd(function_module.FunAddDef), Fwd(function_module.FunZeroDef), Fwd(shift), Fwd(partialIn)),
				Simp(Fwd(PolynomialAlgebraPartialDef), Fwd(shift), Fwd(polynomial)),
				By(coefficient))
		}),
})}

// TaylorModuloSquare — the first-order Taylor expansion of a polynomial over
// a subring k modulo the square of an ideal: when every x(i) − y(i) lies in
// the ideal I of a subring T holding k and both points, P(x) − P(y) −
// Σ_{i ≤ n} ∂ᵢP(x)·(x(i) − y(i)) lies in I². By induction over the
// polynomials, carrying with the expansion that P(x) − P(y) lies in I: a
// constant has equal values and no derivative; values, derivatives and the
// linear term are additive; and for X_j·f the Leibniz rule at a variable
// (PolynomialPartialVarMul) makes the linear term x(j) times that of f plus
// f(x)·(x(j) − y(j)), so the remainder of X_j·f is x(j) times that of f less
// (x(j) − y(j))·(f(x) − f(y)), a product of two members of I.
var TaylorModuloSquare = taylorModuloSquareThm{family.Add(registry.ProofEntry{
	Name: "TaylorModuloSquare",
	Key:  "prop_cda41a9814834175",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀k T I:set(A). ∀n:num. ∀x y:(num → A). ∀P:((num → num) → A).",
		Hypotheses: []string{
			"subring(R, k)",
			"subring(R, T)",
			"k ⊆ T",
			"ring_ideal(restrict_ring(R, T), I)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ T ∧ y(i) ∈ T ∧ x(i) - y(i) ∈ I",
			"P ∈ «polynomials»",
		},
		Conclusion: "«valueAt»(x, P) - " +
			"«valueAt»(y, P) - " +
			"module_sum(R.add, " +
			"    R.zero, " +
			"    {i:num | i ≤ n}, " +
			"    λi:num. «valueAt»(x, «partial»(i, P)) * (x(i) - y(i))) ∈ " +
			"«square»",
		Abbrev: Abbrev{
			{Name: "valueAt", Text: "λz:(num → A). λF:((num → num) → A). " +
				"    polynomial_algebra_eval(restrict_ring(R, k), R, (λa:A. a), z, F)"},
			{Name: "polynomials", Text: "polynomial_algebra(restrict_ring(R, k), {i:num | i ≤ n})"},
			{Name: "partial", Text: "λi:num. λF:((num → num) → A). " +
				"    polynomial_algebra_partial(restrict_ring(R, k), i, F)"},
			{Name: "timesVariable", Text: "λj:num. λF:((num → num) → A). " +
				"    polynomial_algebra_mul(restrict_ring(R, k), " +
				"        polynomial_algebra_var(restrict_ring(R, k), j), " +
				"        F)"},
			{Name: "summand", Text: "λF:((num → num) → A). λi:num. " +
				"    «valueAt»(x, «partial»(i, F)) * (x(i) - y(i))"},
			{Name: "linear", Text: "λF:((num → num) → A). " +
				"    module_sum(R.add, R.zero, {i:num | i ≤ n}, «summand»(F))"},
			{Name: "difference", Text: "λF:((num → num) → A). «valueAt»(x, F) - «valueAt»(y, F)"},
			{Name: "remainder", Text: "λF:((num → num) → A). «difference»(F) - «linear»(F)"},
			{Name: "square", Text: "ideal_mul(restrict_ring(R, T), I, I)"},
			{Name: "expanding", Text: "{F:((num → num) → A) | " +
				"    F ∈ «polynomials» ∧ «difference»(F) ∈ I ∧ «remainder»(F) ∈ «square»}"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		k, T, I *Expr[Set[A]],
		n *Expr[Nat],
		x, y *Arrow[Nat, A],
		P *Arrow[Fun[Nat, Nat], A],
		subK, subT, kInT, ideal, points, polynomial Fact,
	) {
		type poly = Fun[Fun[Nat, Nat], A]
		ring := a.TermAs[RingOps[A]]("R")
		coefficients := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
		ringT := a.TermAs[RingOps[A]]("restrict_ring(R, T)")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		square := a.TermAs[Set[A]]("«square»")
		regular := module.RegularModuleOn.Read(R)
		inclusion := a.Have(
			"k includes into R as a ring map",
			"ring_homomorphism(restrict_ring(R, k), R, λa:A. a)",
			By(
				subK,
				ring_homomorphism.RingHomIdentity.Read(R),
				ring_homomorphism.RingHomRestrictSource.At(ring, ring, identity, k)))
		rings := a.Conjuncts(
			a.Have(
				"k and T are rings under the operations of R",
				"comm_ring_on(restrict_ring(R, k)) ∧ comm_ring_on(restrict_ring(R, T))",
				By(subK, subT, comm_ring.SubringRingOn.Read(R))),
			"k is a ring",
			"T is a ring")
		// The record unfolded: the ring's sum then reads as fun_add, the sum the induction closes under.
		polynomialRing := a.Simplified(
			GroupPremises(rings[0], polynomial_algebra.PolynomialAlgebraCommRingOn.At(coefficients, indices)),
			Fwd(polynomial_algebra.PolynomialAlgebraRingDef))
		ideals := a.Have(
			"I² is an ideal of T, and I lies in T, which lies in R",
			"ring_ideal(restrict_ring(R, T), «square») ∧ I ⊆ T ∧ T ⊆ R.carrier",
			By(
				ideal,
				subT,
				ring_ideal.IdealSubset,
				comm_ring.SubringSubset,
				ring_ideal.IdealMulIdeal.Read(rings[1]).At(I, I)))
		coordinates := a.Conjuncts(
			a.Have(
				"the coordinates of both points, and their differences, lie in R",
				"(∀i:num. i ≤ n ⇒ x(i) ∈ R.carrier) ∧ "+
					"(∀i:num. i ≤ n ⇒ y(i) ∈ R.carrier) ∧ "+
					"(∀i:num. i ≤ n ⇒ x(i) - y(i) ∈ R.carrier)",
				BySets(points, ideals)),
			"the coordinates of x lie in R",
			"so do those of y",
			"and so do their differences")
		xInR, yInR, differences := coordinates[0], coordinates[1], coordinates[2]
		values := a.Have(
			"the values of a polynomial at x and at y lie in T, and so in R",
			Statement{
				Binders:    "∀F:((num → num) → A).",
				Hypotheses: []string{"F ∈ «polynomials»"},
				Conclusion: "«valueAt»(x, F) ∈ T ∧ " +
					"«valueAt»(y, F) ∈ T ∧ " +
					"«valueAt»(x, F) ∈ R.carrier ∧ " +
					"«valueAt»(y, F) ∈ R.carrier",
			},
			a.ForEach(func(F *Expr[poly]) Action {
				return BySets(
					inclusion,
					subT,
					kInT,
					points,
					ideals,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring.At(
						coefficients, ring, identity, x, indices, T, F),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring.At(
						coefficients, ring, identity, y, indices, T, F))
			}))
		linearIn := a.Have(
			"the linear term of a polynomial and each of its summands lie in R",
			Statement{
				Binders:    "∀F:((num → num) → A).",
				Hypotheses: []string{"F ∈ «polynomials»"},
				Conclusion: "(∀i:num. i ≤ n ⇒ «summand»(F, i) ∈ R.carrier) ∧ «linear»(F) ∈ R.carrier",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[poly]("F")
				FIn := b.Assume()
				summands := b.Have(
					"each summand is a value of a derivative times a coordinate difference",
					"∀i:num. i ≤ n ⇒ «summand»(F, i) ∈ R.carrier",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iIn := c.Assume()
						c.Show(
							"a value of a polynomial times a member of R",
							By(
								R,
								iIn,
								FIn,
								rings[0],
								differences.At(i),
								values.At(c.TermAs[poly]("«partial»(i, F)")),
								PolynomialPartialIn.At(coefficients, indices, i, F),
								comm_ring.MulIn.Read(R)))
					}))
				b.Show(
					"a finite sum of members of R lies in R",
					By(
						summands,
						num_segment.FiniteBelow,
						module.ModuleSumIn.Read(regular).At(indices, b.TermAs[Fun[Nat, A]]("«summand»(F)"))))
			}))
		// The record unfolded likewise: the zero evaluation keeps then reads as fun_zero(R.zero).
		evaluation := a.Simplified(
			GroupPremises(
				inclusion,
				xInR,
				polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
					coefficients, ring, identity, x, indices)),
			Fwd(polynomial_algebra.PolynomialAlgebraRingDef))
		zero := a.Have(
			"the zero polynomial is a polynomial and evaluates to zero at x",
			"fun_zero ∈ «polynomials» ∧ «valueAt»(x, fun_zero) = R.zero",
			By(comm_ring.ZeroIn.Read(polynomialRing), ring_homomorphism.MapZero.Read(evaluation)))

		constants := a.Have(
			"a constant has equal values at x and y and no derivative, so its expansion is zero",
			"∀c:A. c ∈ k ⇒ polynomial_algebra_const(restrict_ring(R, k), c) ∈ «expanding»",
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				cIn := b.Assume()
				isConstant := b.Have(
					"the constant c is a polynomial, with value c at x and at y",
					"polynomial_algebra_const(restrict_ring(R, k), c) ∈ «polynomials» ∧ "+
						"«valueAt»(x, polynomial_algebra_const(restrict_ring(R, k), c)) = c ∧ "+
						"«valueAt»(y, polynomial_algebra_const(restrict_ring(R, k), c)) = c",
					By(
						cIn,
						inclusion,
						ring_homomorphism.MapIn.Read(b.Have(
							"taking constants is a ring map from k into the polynomials",
							"ring_homomorphism(restrict_ring(R, k), "+
								"    polynomial_algebra_ring(restrict_ring(R, k), {i:num | i ≤ n}), "+
								"    polynomial_algebra_const(restrict_ring(R, k)))",
							By(rings[0], polynomial_algebra.PolynomialAlgebraConstHom.At(coefficients, indices)))),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(coefficients, ring, identity, x, c),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(coefficients, ring, identity, y, c)))
				vanishing := b.Have(
					"each term of its linear term is zero, the derivative being the zero polynomial",
					"∀i:num. i ≤ n ⇒ «summand»(polynomial_algebra_const(restrict_ring(R, k), c), i) = R.zero",
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						iIn := d.Assume()
						d.Do(Simp(Fwd(PolynomialPartialConst)))
						d.Show(
							"zero times the coordinate difference is zero",
							By(R, iIn, zero, differences.At(i), comm_ring.MulLeftZeroOn.Read(R)))
					}))
				flat := b.Have(
					"so its linear term is zero",
					"«linear»(polynomial_algebra_const(restrict_ring(R, k), c)) = R.zero",
					By(
						vanishing,
						num_segment.FiniteBelow,
						module.ModuleSumZero.Read(regular).At(
							indices, b.TermAs[Fun[Nat, A]]("«summand»(polynomial_algebra_const(restrict_ring(R, k), c))"))))
				cInR := b.Have(
					"c lies in R",
					"c ∈ R.carrier",
					BySets(cIn, kInT, ideals))
				b.Show(
					"c − c and c − c − 0 are zero, which lies in I and in I²",
					By(
						isConstant,
						flat,
						ideal,
						ideals,
						b.Have(
							"c − c is zero",
							"c - c = R.zero ∧ c - c - R.zero = R.zero",
							ByArith(R, cInR)),
						ring_ideal.IdealZero.At(ringT, I),
						ring_ideal.IdealZero.At(ringT, square)))
			}))

		sums := a.Have(
			"expansions add: the values, the derivatives and so the linear term of a sum are sums",
			"∀f g:((num → num) → A). f ∈ «expanding» ∧ g ∈ «expanding» ⇒ fun_add(f, g) ∈ «expanding»",
			Derive(func(b *Argument) {
				f := b.FixAs[poly]("f")
				g := b.FixAs[poly]("g")
				given := b.Conjuncts(
					b.Assume(),
					"f has its expansion",
					"and so has g")
				fHas := b.Conjuncts(
					given[0],
					"f is a polynomial",
					"f(x) − f(y) lies in I",
					"and the remainder of f lies in I²")
				gHas := b.Conjuncts(
					given[1],
					"g is a polynomial",
					"g(x) − g(y) lies in I",
					"and the remainder of g lies in I²")
				sumIn := b.Have(
					"f + g is a polynomial",
					"fun_add(f, g) ∈ «polynomials»",
					By(polynomialRing, fHas[0], gHas[0], comm_ring.AddIn.Read(polynomialRing)))
				sumValues := b.Have(
					"its values are the sums of the values",
					"«valueAt»(x, fun_add(f, g)) = «valueAt»(x, f) + «valueAt»(x, g) ∧ "+
						"«valueAt»(y, fun_add(f, g)) = «valueAt»(y, f) + «valueAt»(y, g)",
					By(
						inclusion,
						xInR,
						yInR,
						fHas[0],
						gHas[0],
						polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(
							coefficients, ring, identity, x, indices, f, g),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(
							coefficients, ring, identity, y, indices, f, g)))
				termwise := b.Have(
					"term by term the linear term of f + g is the sum of those of f and g",
					"∀i:num. i ≤ n ⇒ «summand»(fun_add(f, g), i) = «summand»(f, i) + «summand»(g, i)",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iIn := c.Assume()
						partialF := c.TermAs[poly]("«partial»(i, f)")
						partialG := c.TermAs[poly]("«partial»(i, g)")
						derivatives := c.Have(
							"the derivatives of f and g are polynomials",
							"«partial»(i, f) ∈ «polynomials» ∧ «partial»(i, g) ∈ «polynomials»",
							By(
								rings[0],
								fHas[0],
								gHas[0],
								PolynomialPartialIn.At(coefficients, indices, i, f),
								PolynomialPartialIn.At(coefficients, indices, i, g)))
						c.Show(
							"the derivative of f + g is the sum of the derivatives, and so is its value at x",
							CalcEq(
								Leg(
									c.TermAs[A]("«valueAt»(x, fun_add(«partial»(i, f), «partial»(i, g))) * (x(i) - y(i))"),
									"the derivative is additive",
									By(rings[0], fHas[0], gHas[0], PolynomialPartialLinear.At(coefficients, indices, i, f, g))),
								Leg(
									c.TermAs[A]("(«valueAt»(x, «partial»(i, f)) + «valueAt»(x, «partial»(i, g))) * (x(i) - y(i))"),
									"and so is evaluation",
									By(
										inclusion,
										xInR,
										derivatives,
										polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(
											coefficients, ring, identity, x, indices, partialF, partialG))),
								FinalLeg(
									"the coordinate difference distributes over the sum",
									ByArith(R, iIn, derivatives, xInR.At(i), yInR.At(i), values.At(partialF), values.At(partialG)))))
					}))
				fLinear := linearIn.At(f)
				gLinear := linearIn.At(g)
				linear := b.Have(
					"so the linear term of f + g is the sum of those of f and g",
					"«linear»(fun_add(f, g)) = «linear»(f) + «linear»(g)",
					By(
						termwise,
						fHas[0],
						gHas[0],
						fLinear,
						gLinear,
						num_segment.FiniteBelow,
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("R.add"),
							b.TermAs[A]("R.zero"),
							indices,
							b.TermAs[Fun[Nat, A]]("«summand»(fun_add(f, g))"),
							b.TermAs[Fun[Nat, A]]("λi:num. «summand»(f, i) + «summand»(g, i)")),
						module.ModuleSumAdd.Read(regular).At(
							indices,
							b.TermAs[Fun[Nat, A]]("«summand»(f)"),
							b.TermAs[Fun[Nat, A]]("«summand»(g)"))))
				members := b.Have(
					"the values and linear terms of f and g lie in R",
					"«valueAt»(x, f) ∈ R.carrier ∧ "+
						"«valueAt»(y, f) ∈ R.carrier ∧ "+
						"«valueAt»(x, g) ∈ R.carrier ∧ "+
						"«valueAt»(y, g) ∈ R.carrier ∧ "+
						"«linear»(f) ∈ R.carrier ∧ "+
						"«linear»(g) ∈ R.carrier",
					By(fHas[0], gHas[0], values.At(f), values.At(g), fLinear, gLinear))
				regrouped := b.Have(
					"the difference and the remainder of f + g are the sums of those of f and g",
					"«valueAt»(x, f) + «valueAt»(x, g) - («valueAt»(y, f) + «valueAt»(y, g)) = "+
						"«difference»(f) + «difference»(g) ∧ "+
						"«valueAt»(x, f) + "+
						"«valueAt»(x, g) - "+
						"(«valueAt»(y, f) + «valueAt»(y, g)) - "+
						"(«linear»(f) + «linear»(g)) = "+
						"«remainder»(f) + «remainder»(g)",
					ByArith(R, members))
				difference := b.Have(
					"the difference of f + g lies in I, a sum of two members of I",
					"«valueAt»(x, f) + «valueAt»(x, g) - («valueAt»(y, f) + «valueAt»(y, g)) ∈ I",
					By(
						regrouped,
						fHas[1],
						gHas[1],
						ideal,
						ring_ideal.IdealAdd.At(ringT, I, b.TermAs[A]("«difference»(f)"), b.TermAs[A]("«difference»(g)"))))
				remainder := b.Have(
					"and its remainder lies in I², a sum of two members of I²",
					"«valueAt»(x, f) + "+
						"«valueAt»(x, g) - "+
						"(«valueAt»(y, f) + «valueAt»(y, g)) - "+
						"(«linear»(f) + «linear»(g)) ∈ "+
						"«square»",
					By(
						regrouped,
						fHas[2],
						gHas[2],
						ideals,
						ring_ideal.IdealAdd.At(
							ringT, square, b.TermAs[A]("«remainder»(f)"), b.TermAs[A]("«remainder»(g)"))))
				b.Show(
					"f + g is a polynomial whose values and linear term are the sums",
					By(sumIn, sumValues, linear, difference, remainder))
			}))

		variables := a.Have(
			"multiplying by a variable keeps the expansion: by the Leibniz rule "+
				"the remainder of X_j·f is x(j) times that of f less a product in I²",
			"∀j:num. ∀f:((num → num) → A). j ≤ n ∧ f ∈ «expanding» ⇒ «timesVariable»(j, f) ∈ «expanding»",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				f := b.FixAs[poly]("f")
				given := b.Conjuncts(
					b.Assume(),
					"j is at most n",
					"f has its expansion")
				jIn := given[0]
				fHas := b.Conjuncts(
					given[1],
					"f is a polynomial",
					"f(x) − f(y) lies in I",
					"and the remainder of f lies in I²")
				variable := b.TermAs[poly]("polynomial_algebra_var(restrict_ring(R, k), j)")
				varIn := b.Have(
					"X_j is a polynomial",
					"polynomial_algebra_var(restrict_ring(R, k), j) ∈ «polynomials»",
					By(rings[0], jIn, polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, indices, j)))
				productIn := b.Have(
					"and so is X_j·f",
					"«timesVariable»(j, f) ∈ «polynomials»",
					By(
						rings[0],
						varIn,
						fHas[0],
						polynomial_algebra.PolynomialAlgebraMulIn.At(coefficients, indices, variable, f)))
				productValues := b.Have(
					"the values of X_j·f are x(j)·f(x) and y(j)·f(y)",
					"«valueAt»(x, «timesVariable»(j, f)) = x(j) * «valueAt»(x, f) ∧ "+
						"«valueAt»(y, «timesVariable»(j, f)) = y(j) * «valueAt»(y, f)",
					By(
						inclusion,
						xInR,
						yInR,
						jIn,
						varIn,
						fHas[0],
						polynomial_algebra_evaluation.PolynomialAlgebraEvalMul.At(
							coefficients, ring, identity, x, indices, variable, f),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalMul.At(
							coefficients, ring, identity, y, indices, variable, f),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, ring, identity, x, j),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, ring, identity, y, j)))
				fValues := values.At(f)
				fLinear := linearIn.At(f)
				termwise := b.Have(
					"term by term, by the Leibniz rule at X_j, the linear term "+
						"of X_j·f is x(j) times that of f plus f(x)·(x(j) − y(j)) at j",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i ≤ n"},
						Conclusion: "«summand»(«timesVariable»(j, f), i) = " +
							"x(j) * «summand»(f, i) + COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iIn := c.Assume()
						partialF := c.TermAs[poly]("«partial»(i, f)")
						shiftedProduct := c.TermAs[poly]("«timesVariable»(j, «partial»(i, f))")
						choice := c.TermAs[poly]("COND(i = j, f, fun_zero)")
						derivativeIn := c.Have(
							"the derivative of f in X_i is a polynomial, and so is X_j times it",
							"«partial»(i, f) ∈ «polynomials» ∧ «timesVariable»(j, «partial»(i, f)) ∈ «polynomials»",
							By(
								rings[0],
								fHas[0],
								varIn,
								PolynomialPartialIn.At(coefficients, indices, i, f),
								polynomial_algebra.PolynomialAlgebraMulIn.At(coefficients, indices, variable, partialF)))
						shifted := c.Have(
							"X_j times the derivative has value x(j) times that of the derivative",
							"«valueAt»(x, «timesVariable»(j, «partial»(i, f))) = x(j) * «valueAt»(x, «partial»(i, f))",
							By(
								inclusion,
								xInR,
								jIn,
								varIn,
								derivativeIn,
								polynomial_algebra_evaluation.PolynomialAlgebraEvalMul.At(
									coefficients, ring, identity, x, indices, variable, partialF),
								polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, ring, identity, x, j)))
						picked := c.Conjuncts(
							c.Have(
								"f where i = j and the zero polynomial elsewhere is a "+
									"polynomial, with value f(x) where i = j and zero elsewhere",
								"COND(i = j, f, fun_zero) ∈ «polynomials» ∧ "+
									"«valueAt»(x, COND(i = j, f, fun_zero)) = COND(i = j, «valueAt»(x, f), R.zero)",
								Derive(func(d *Argument) {
									d.Cases(d.TermAs[Bool]("i = j"))
									d.When(
										"at i = j it is f",
										func(e *Argument, same Fact) {
											e.Show(
												"f is a polynomial",
												By(same, fHas[0]))
										})
									d.Otherwise(
										"elsewhere it is the zero polynomial",
										func(e *Argument, other Fact) {
											e.Show(
												"which is a polynomial with value zero",
												By(other, zero))
										})
								})),
							"it is a polynomial",
							"with value f(x) or zero")
						members := c.Have(
							"the values in play lie in R",
							"x(j) ∈ R.carrier ∧ "+
								"«valueAt»(x, f) ∈ R.carrier ∧ "+
								"«valueAt»(x, «partial»(i, f)) ∈ R.carrier ∧ "+
								"x(i) ∈ R.carrier ∧ "+
								"y(i) ∈ R.carrier",
							By(jIn, iIn, fHas[0], xInR, yInR, fValues, derivativeIn, values.At(partialF)))
						c.Show(
							"∂_i(X_j·f)(x) is x(j)·∂_i f(x), plus f(x) when i = j",
							CalcEq(
								Leg(
									c.TermAs[A](
										"«valueAt»(x, fun_add(«timesVariable»(j, «partial»(i, f)), COND(i = j, f, fun_zero))) * "+
											"(x(i) - y(i))"),
									"the Leibniz rule at X_j",
									By(rings[0], fHas[0], PolynomialPartialVarMul.At(coefficients, indices, i, j, f))),
								Leg(
									c.TermAs[A](
										"(x(j) * «valueAt»(x, «partial»(i, f)) + COND(i = j, «valueAt»(x, f), R.zero)) * (x(i) - y(i))"),
									"evaluation is additive, and X_j evaluates to x(j)",
									By(
										inclusion,
										xInR,
										derivativeIn,
										picked[0],
										picked[1],
										shifted,
										polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(
											coefficients, ring, identity, x, indices, shiftedProduct, choice))),
								FinalLeg(
									"the coordinate difference distributes, the term of f(x) surviving at j alone",
									Derive(func(d *Argument) {
										d.Cases(d.TermAs[Bool]("i = j"))
										d.When(
											"at j the term of f(x) is there",
											func(e *Argument, same Fact) {
												e.Show(
													"both sides are x(j)·∂_j f(x)·(x(j) − y(j)) + f(x)·(x(j) − y(j))",
													Simp(Rev(same)),
													ByArith(R, members))
											})
										d.Otherwise(
											"elsewhere it is zero",
											func(e *Argument, other Fact) {
												e.Show(
													"both sides are x(j)·∂_i f(x)·(x(i) − y(i))",
													Simp(Fwd(other)),
													ByArith(R, members))
											})
									}))))
					}))
				fTerms := b.TermAs[Fun[Nat, A]]("«summand»(f)")
				scaled := b.Have(
					"x(j) times each summand of the linear term of f lies in R",
					"∀i:num. i ≤ n ⇒ x(j) * «summand»(f, i) ∈ R.carrier",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						iIn := c.Assume()
						c.Show(
							"a product of members of R",
							By(R, iIn, jIn, fHas[0], fLinear, xInR.At(j), comm_ring.MulIn.Read(R)))
					}))
				atJ := b.TermAs[Fun[Nat, A]]("λi:num. COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero)")
				chosen := b.Have(
					"so does f(x)·(x(i) − y(i)) at i = j, and zero elsewhere",
					"∀i:num. i ≤ n ⇒ COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero) ∈ R.carrier",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iIn := c.Assume()
						c.Show(
							"a product of members of R, or zero",
							By(R, iIn, fHas[0], fValues, differences.At(i), comm_ring.MulIn.Read(R), comm_ring.ZeroIn.Read(R)))
					}))
				vanishesOff := b.Have(
					"and is zero off j",
					"∀i:num. i ≤ n ∧ i ≠ j ⇒ COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero) = R.zero",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						off := c.Conjuncts(
							c.Assume(),
							"i is at most n",
							"and is not j")
						c.Show(
							"the condition fails",
							By(off[1]))
					}))
				linear := b.Have(
					"so the linear term of X_j·f is x(j) times that of f plus f(x)·(x(j) − y(j))",
					"«linear»(«timesVariable»(j, f)) = x(j) * «linear»(f) + «valueAt»(x, f) * (x(j) - y(j))",
					CalcEq(
						Leg(
							b.TermAs[A](
								"module_sum(R.add, "+
									"    R.zero, "+
									"    {i:num | i ≤ n}, "+
									"    λi:num. x(j) * «summand»(f, i) + COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero))"),
							"term by term",
							By(
								termwise,
								module.ModuleSumCongruence.At(
									b.TermAs[Op[A]]("R.add"),
									b.TermAs[A]("R.zero"),
									indices,
									b.TermAs[Fun[Nat, A]]("«summand»(«timesVariable»(j, f))"),
									b.TermAs[Fun[Nat, A]](
										"λi:num. x(j) * «summand»(f, i) + COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero)")))),
						Leg(
							b.TermAs[A](
								"module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. x(j) * «summand»(f, i)) + "+
									"module_sum(R.add, "+
									"    R.zero, "+
									"    {i:num | i ≤ n}, "+
									"    λi:num. COND(i = j, «valueAt»(x, f) * (x(i) - y(i)), R.zero))"),
							"the sum splits",
							By(
								scaled,
								chosen,
								num_segment.FiniteBelow,
								module.ModuleSumAdd.Read(regular).At(
									indices,
									b.TermAs[Fun[Nat, A]]("λi:num. x(j) * «summand»(f, i)"),
									atJ))),
						FinalLeg(
							"x(j) comes out of the first sum, and the second has its one nonzero term at j",
							By(
								jIn,
								fHas[0],
								fLinear,
								chosen,
								vanishesOff,
								xInR,
								num_segment.FiniteBelow,
								module.ModuleSumSmul.Read(regular).AsFact().At(indices, x.Apply(j), fTerms),
								module.ModuleSumSingle.Read(regular).At(indices, j, atJ)))))
				members := b.Have(
					"the values, coordinates and linear term in play lie in R",
					"x(j) ∈ R.carrier ∧ "+
						"y(j) ∈ R.carrier ∧ "+
						"«valueAt»(x, f) ∈ R.carrier ∧ "+
						"«valueAt»(y, f) ∈ R.carrier ∧ "+
						"«linear»(f) ∈ R.carrier",
					By(jIn, fHas[0], xInR, yInR, fValues, fLinear))
				regrouped := b.Have(
					"the difference of X_j·f regroups around that of f, and its remainder around the remainder of f",
					"x(j) * «valueAt»(x, f) - y(j) * «valueAt»(y, f) = "+
						"x(j) * «difference»(f) + «valueAt»(y, f) * (x(j) - y(j)) ∧ "+
						"x(j) * «valueAt»(x, f) - "+
						"y(j) * «valueAt»(y, f) - "+
						"(x(j) * «linear»(f) + «valueAt»(x, f) * (x(j) - y(j))) = "+
						"x(j) * «remainder»(f) + -((x(j) - y(j)) * «difference»(f))",
					ByArith(R, members))
				inT := b.Have(
					"x(j) and f(y) lie in T, and x(j) − y(j) in I",
					"x(j) ∈ T ∧ «valueAt»(y, f) ∈ T ∧ x(j) - y(j) ∈ I",
					By(jIn, points, fHas[0], fValues))
				dx := b.TermAs[A]("x(j) - y(j)")
				df := b.TermAs[A]("«difference»(f)")
				remainder := b.TermAs[A]("«remainder»(f)")
				difference := b.Have(
					"I absorbs the difference of X_j·f",
					"x(j) * «valueAt»(x, f) - y(j) * «valueAt»(y, f) ∈ I",
					By(
						regrouped,
						inT,
						fHas[1],
						ideal,
						ring_ideal.IdealMul.At(ringT, I, x.Apply(j), df),
						ring_ideal.IdealMul.At(ringT, I, b.TermAs[A]("«valueAt»(y, f)"), dx),
						ring_ideal.IdealAdd.At(
							ringT, I, b.TermAs[A]("x(j) * «difference»(f)"), b.TermAs[A]("«valueAt»(y, f) * (x(j) - y(j))"))))
				product := b.TermAs[A]("(x(j) - y(j)) * «difference»(f)")
				remainderIn := b.Have(
					"and I² its remainder: x(j) times the remainder of f, less a product of two members of I",
					"x(j) * «valueAt»(x, f) - "+
						"y(j) * «valueAt»(y, f) - "+
						"(x(j) * «linear»(f) + «valueAt»(x, f) * (x(j) - y(j))) ∈ "+
						"«square»",
					By(
						regrouped,
						inT,
						fHas[1],
						fHas[2],
						ideals,
						ring_ideal.IdealMul.At(ringT, square, x.Apply(j), remainder),
						ring_ideal.IdealMulHolds.At(ringT, I, I, dx, df),
						ring_ideal.IdealSub.Read(rings[1]).At(square, b.TermAs[A]("x(j) * «remainder»(f)"), product)))
				b.Show(
					"X_j·f is a polynomial whose expansion follows from that of f",
					By(productIn, productValues, linear, difference, remainderIn))
			}))

		expansion := a.Have(
			"every polynomial has its expansion, by induction over the polynomials",
			"«polynomials» ⊆ «expanding»",
			By(
				rings[0],
				constants,
				sums,
				variables,
				polynomial_algebra.PolynomialInduction.At(
					coefficients, indices, a.TermAs[Set[poly]]("«expanding»"))))
		a.Show(
			"P is a polynomial, so its remainder lies in I²",
			BySets(polynomial, expansion))
	}),
})}

// PolynomialPartialConst — a constant has partial derivative zero: the
// constant vanishes off the zero monomial, raising the exponent of x never
// gives the zero monomial, and a numeral times zero is zero.
var PolynomialPartialConst = polynomialPartialConstThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialConst",
	Key:  "prop_af1e99153afedcd4",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀x:D. ∀a:A.",
		Hypotheses: []string{"comm_ring_on(R)"},
		Conclusion: "polynomial_algebra_partial(R, x, polynomial_algebra_const(R, a)) = fun_zero",
	},
		func(arg *Argument, R *Expr[RingOps[A]], x *Expr[D], a *Expr[A], ring Fact) {
			raised := arg.Have(
				"raising the exponent of x never gives the zero monomial, the exponent at x being positive",
				"∀m:(D → num). (λy:D. m(y) + monomial_var(x, y)) ≠ (λy:D. 0)",
				By(polynomial_algebra.MonomialVarValues.At(x), nat_arith.AddEqZero, nat_arith.OneNotZero))
			arg.Do(Funext())
			m := arg.FixAs[Fun[D, Nat]]("m")
			arg.Show(
				"the constant is zero at m raised, and a numeral times zero is zero",
				Simp(
					Fwd(PolynomialAlgebraPartialDef),
					Fwd(polynomial_algebra.PolynomialAlgebraConstDef),
					Fwd(free_module.DeltaAtDef),
					Fwd(function_module.FunZeroDef)),
				By(
					raised.At(m),
					comm_ring.OneIn.Read(ring),
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
					comm_ring.MulRightZeroOn.Read(ring)))
		}),
	Reading: "Nothing is asked of a: the constant is R.zero at every monomial but the zero one, " +
		"which no raised monomial m + x is, so the derivative of any constant vanishes, a value " +
		"outside R's carrier included. comm_ring_on(R) makes a numeral times R.zero equal to R.zero.",
})}

// PolynomialPartialVar — the partial derivative of the variable y in the
// variable x is the constant one when x = y and the constant zero
// otherwise: the variable y is one at the monomial of y alone, and m
// raised at x is that monomial exactly when x = y and m is the zero
// monomial, where the numeral is 0 + 1, one.
var PolynomialPartialVar = polynomialPartialVarThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialVar",
	Key:  "prop_403f6e605c1f0b8c",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀x y:D.",
		Hypotheses: []string{"comm_ring_on(R)"},
		Conclusion: "polynomial_algebra_partial(R, x, polynomial_algebra_var(R, y)) = " +
			"polynomial_algebra_const(R, COND(x = y, R.one, R.zero))",
	},
		func(a *Argument, R *Expr[RingOps[A]], x, y *Expr[D], ring Fact) {
			a.Cases(a.TermAs[Bool]("x = y"))
			a.When(
				"in its own variable the derivative is the constant one",
				func(b *Argument, same Fact) {
					b.Do(same.RwRev())
					raised := b.Have(
						"m raised at x is the monomial of x exactly when m is the zero monomial",
						"∀m:(D → num). (λz:D. m(z) + monomial_var(x, z)) = monomial_var(x) ⇔ m = (λz:D. 0)",
						By(nat_arith.AddEqSelfRight))
					b.Do(Funext())
					m := b.FixAs[Fun[D, Nat]]("m")
					b.Cases(b.TermAs[Bool]("m = (λz:D. 0)"))
					b.When(
						"at the zero monomial the numeral is 0 + 1 and the coefficient one",
						func(c *Argument, zero Fact) {
							c.Do(zero.Rw())
							c.Show(
								"one times one is one",
								Simp(
									Fwd(PolynomialAlgebraPartialDef),
									Fwd(polynomial_algebra.PolynomialAlgebraVarDef),
									Fwd(polynomial_algebra.PolynomialAlgebraConstDef),
									Fwd(free_module.DeltaAtDef),
									Fwd(nat_arith.AddLeftZeroClause)),
								By(
									Normalized,
									comm_ring.OneIn.Read(ring),
									comm_monoid.PowOneOn.Read(comm_ring.AddMonoidOn.Read(ring)),
									comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
						})
					b.Otherwise(
						"at any other monomial m raised is not the monomial of x, and both sides are zero",
						func(c *Argument, nonzero Fact) {
							c.Show(
								"a numeral times zero is zero",
								Simp(
									Fwd(PolynomialAlgebraPartialDef),
									Fwd(polynomial_algebra.PolynomialAlgebraVarDef),
									Fwd(polynomial_algebra.PolynomialAlgebraConstDef),
									Fwd(free_module.DeltaAtDef)),
								By(
									ring,
									nonzero,
									raised.At(m),
									comm_ring.OneIn.Read(ring),
									comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
									comm_ring.MulRightZeroOn.Read(ring)))
						})
				})
			a.Otherwise(
				"in another variable it is the constant zero",
				func(b *Argument, other Fact) {
					raised := b.Have(
						"m raised at x is never the monomial of y, its exponent at x being positive",
						"∀m:(D → num). (λz:D. m(z) + monomial_var(x, z)) ≠ monomial_var(y)",
						By(
							other,
							polynomial_algebra.MonomialVarValues.At(x),
							polynomial_algebra.MonomialVarValues.At(y),
							nat_arith.AddEqZero,
							nat_arith.OneNotZero))
					b.Do(Funext())
					m := b.FixAs[Fun[D, Nat]]("m")
					b.Show(
						"so the variable y is zero at m raised, and a numeral times zero is zero",
						Simp(
							Fwd(PolynomialAlgebraPartialDef),
							Fwd(polynomial_algebra.PolynomialAlgebraVarDef),
							Fwd(polynomial_algebra.PolynomialAlgebraConstDef),
							Fwd(free_module.DeltaAtDef)),
						By(
							ring,
							raised.At(m),
							comm_ring.OneIn.Read(ring),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
							comm_ring.MulRightZeroOn.Read(ring)))
				})
		}),
	Reading: "At x ≠ y the derivative is the constant zero, the zero " +
		"polynomial; at x = y it is the constant one. comm_ring_on(R) is what makes " +
		"the numeral 0 + 1 equal to R.one and a numeral times R.zero equal to R.zero.",
})}

// PolynomialPartialMap — a partial derivative commutes with carrying the
// coefficients along a ring homomorphism f: the derivative in x of the
// carried polynomial is the carried derivative. At a monomial m both sides
// are the numeral m(x) + 1 times the coefficient at m raised at x, and f
// keeps the numerals and the product of two members of R.
var PolynomialPartialMap = polynomialPartialMapThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartialMap",
	Key:  "prop_d5fcf9ab324c9cc3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀x:D. ∀p:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"∀m:(D → num). p(m) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_partial(T, x, λm:(D → num). f(p(m))) = " +
			"(λm:(D → num). f(polynomial_algebra_partial(R, x, p, m)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			f *Arrow[A, B],
			x *Expr[D],
			p *Arrow[Fun[D, Nat], A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			coefficients Fact,
		) {
			source := ring_homomorphism.Source.Read(hom)
			a.Do(Funext())
			a.FixAs[Fun[D, Nat]]("m")
			a.Show(
				"f keeps the numeral m(x) + 1 and the product of two members of R",
				Simp(Fwd(PolynomialAlgebraPartialDef)),
				By(
					coefficients,
					ring_homomorphism.MapMul.Read(hom),
					ring_homomorphism.RingMapNumeral.Read(hom),
					comm_ring.OneIn.Read(source),
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(source))))
		}),
})}
