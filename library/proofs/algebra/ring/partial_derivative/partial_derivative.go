// partial_derivative.go — the partial derivative of a polynomial in one
// of its variables, read on the polynomial model and carried along the
// host's injection to the free algebra, and its laws: it keeps the
// algebra on a set of variables, is additive, kills the constants,
// takes a variable to one or zero and obeys the Leibniz rule, and only
// finitely many variables of a member have a nonzero derivative.
// Then the derivations of an algebra into a module over it, the maps
// that are additive, obey the Leibniz rule and vanish on the constants:
// on a free algebra one is fixed by its values at the variables, which
// gives the chain rule for an algebra map, and the derivative of a map
// that sends some variables to the coefficients and renames the rest;
// any values at the variables are those of one derivation. Then the
// conormal maps of a ring map, the linear maps on its kernel, among them
// the restrictions of derivations.
// Last, the corpus's polynomials in one variable: their formal
// derivative is the partial derivative of the algebra on that variable.

package partial_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The partial derivative
// ---------------------------------------------------------------------------

// PolynomialAlgebraPartialDef — `polynomial_algebra_partial(R, x, f)`:
// the partial derivative of the polynomial f in the variable x, its
// coefficient at a monomial m the coefficient of f at m with the
// exponent of x raised by one, times the numeral m(x) + 1.
var PolynomialAlgebraPartialDef = polynomialAlgebraPartialDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraPartialDef",
	Key:   "prop_42ce401667c6a1c2",
	Const: "polynomial_algebra_partial",
	Type:  "ring_ops(A) → D → ((D → num) → A) → (D → num) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀x:D. ∀f:((D → num) → A). ∀m:(D → num). " +
			"    polynomial_algebra_partial(R, x, f, m) = " +
			"    R.mul(monoid_pow(R.add, R.zero, R.one, m(x) + 1), f(λy:D. m(y) + monomial_var(x, y)))",
	},
	Reading: "The numeral m(x) + 1 is R.one added to itself m(x) + 1 times, zero where " +
		"the characteristic divides it. On a polynomial of S the value is a polynomial of S: " +
		"m plus the monomial of x is finitely supported only when m is, and is a monomial of " +
		"S exactly when m is one and x ∈ S, so off the monomials of S every coefficient is a " +
		"product with R.zero, and at a variable x outside S the derivative is the zero " +
		"polynomial. On a function that is not a polynomial no such reading holds.",
})}

// PartialEvalTimesVar — θ(x) times the value at θ of the derivative of P
// in x is the sum over the monomials m of P of m(x) · P(m) · θ^m: with eₓ
// the monomial of x, the coefficient of ∂ₓP at m is (m(x) + 1) · P(m + eₓ)
// and θ(x) · θ^m is θ^(m + eₓ) (MonomialEvalShift), so the sum is
// reindexed by m′ = m + eₓ, which runs over the monomials of P with a
// positive exponent at x — lowering them by eₓ is one-to-one and reaches
// every m where ∂ₓP is nonzero — and the monomials of P with exponent
// zero at x add nothing.
var PartialEvalTimesVar = partialEvalTimesVarThm{family.Add(registry.ProofEntry{
	Name: "PartialEvalTimesVar",
	Key:  "prop_87a12c81e831337b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀S:set(D). ∀P:((D → num) → A). ∀θ:(D → A). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"k ⊆ R.carrier",
			"P ∈ polynomial_algebra(restrict_ring(R, k), S)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"θ(x) ∈ R.carrier",
		},
		Conclusion: "θ(x) * " +
			"polynomial_algebra_eval(restrict_ring(R, k), " +
			"    R, " +
			"    (λa:A. a), " +
			"    θ, " +
			"    polynomial_algebra_partial(restrict_ring(R, k), x, P)) = " +
			"module_sum(R.add, " +
			"    R.zero, " +
			"    fun_support(R.zero, P), " +
			"    λm:(D → num). monoid_pow(R.add, R.zero, R.one, m(x)) * (P(m) * monomial_eval(R, θ, m)))",
		Abbrev: Abbrev{
			{Name: "partial", Text: "polynomial_algebra_partial(restrict_ring(R, k), x, P)"},
			{Name: "raisedSupport", Text: "{m:(D → num) | P(m) ≠ R.zero ∧ m(x) ≠ 0}"},
			{Name: "lower", Text: "λm:(D → num). λy:D. m(y) - monomial_var(x, y)"},
			{Name: "lowered", Text: "image(«lower», «raisedSupport»)"},
			{Name: "partialSupport", Text: "fun_support(R.zero, λm:(D → num). «partial»(m))"},
			{Name: "scaled", Text: "λm:(D → num). θ(x) * («partial»(m) * monomial_eval(R, θ, m))"},
			{Name: "weighted", Text: "λm:(D → num). " +
				"    monoid_pow(R.add, R.zero, R.one, m(x)) * (P(m) * monomial_eval(R, θ, m))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			S *Expr[Set[D]],
			P *Arrow[Fun[D, Nat], A],
			θ *Arrow[D, A],
			x *Expr[D],
			ring, coefficients, polynomial, values, xValue Fact,
		) {
			regular := module.RegularModuleOn.Read(ring)
			coefficientRing := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			support := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, P)")
			raised := a.TermAs[Set[Fun[D, Nat]]]("«raisedSupport»")
			lower := a.TermAs[Fun[Fun[D, Nat], Fun[D, Nat]]]("«lower»")
			lowered := a.TermAs[Set[Fun[D, Nat]]]("«lowered»")
			partialSupport := a.TermAs[Set[Fun[D, Nat]]]("«partialSupport»")
			scaled := a.TermAs[Fun[Fun[D, Nat], A]]("«scaled»")
			weighted := a.TermAs[Fun[Fun[D, Nat], A]]("«weighted»")
			unit := a.Conjuncts(
				polynomial_algebra.MonomialVarValues.At(x),
				"the monomial of x is one at x",
				"and zero at every other variable")
			parts := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"P is nonzero at finitely many monomials",
				"every monomial where P is nonzero is a monomial of S",
				"every coefficient of P lies in k")
			inR := a.Have(
				"the coefficients of P lie in R",
				"∀m:(D → num). P(m) ∈ R.carrier",
				By(a.Unfolded(coefficients, set_basic.SubsetDef), parts[2]))
			monomialsFinite := a.Have(
				"a monomial where P is nonzero is a monomial of S, and so finitely supported",
				"∀m:(D → num). P(m) ≠ R.zero ⇒ finite_support(0, m)",
				BySets(parts[1], polynomial_algebra.MonomialsDef))
			numerals := a.Have(
				"every numeral lies in R",
				"∀j:num. monoid_pow(R.add, R.zero, R.one, j) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
			lowerRaise := a.Have(
				"lowering the exponent of x undoes raising it",
				"∀m:(D → num). (λy:D. m(y) + monomial_var(x, y) - monomial_var(x, y)) = m",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m")
					b.Do(Funext())
					b.Show(
						"exponent by exponent, adding and taking away the same number",
						ByArith())
				}))
			raiseLower := a.Have(
				"raising the exponent of x undoes lowering it where that exponent is positive",
				"∀m:(D → num). m(x) ≠ 0 ⇒ (λy:D. m(y) - monomial_var(x, y) + monomial_var(x, y)) = m",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					positive := b.Assume()
					b.Show(
						"one is at most the positive m(x), so lowering by one and raising again restores m",
						ByArith(positive, polynomial_algebra.MonomialLowerRaise.At(m, x, b.TermAs[Nat]("1"))))
				}))
			lowerMonomial := a.Have(
				"lowering a monomial where P is nonzero leaves a monomial of S",
				"∀m:(D → num). P(m) ≠ R.zero ⇒ (λy:D. m(y) - monomial_var(x, y)) ∈ monomials(S)",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					nonzero := b.Assume()
					finite := b.Unfolded(
						GroupPremises(nonzero, monomialsFinite.At(m)), function_module.FiniteSupportDef)
					pointwise := b.Have(
						"a lowered exponent is nonzero only where the exponent is, zero minus anything being zero",
						"∀y:D. m(y) - monomial_var(x, y) ≠ 0 ⇒ m(y) ≠ 0",
						ByArith())
					smaller := b.Have(
						"so the support of the lowering lies in that of m",
						"fun_support(0, λy:D. m(y) - monomial_var(x, y)) ⊆ fun_support(0, m)",
						BySets(pointwise))
					finiteLowered := b.Have(
						"so the lowering is finitely supported",
						"finite_support(0, λy:D. m(y) - monomial_var(x, y))",
						Unfold(function_module.FiniteSupportDef),
						By(
							finite,
							smaller,
							finite_set.FiniteSubset.At(
								b.TermAs[Set[D]]("fun_support(0, λy:D. m(y) - monomial_var(x, y))"),
								b.TermAs[Set[D]]("fun_support(0, m)"))))
					b.Show(
						"with its variables among those of m, which lie in S",
						BySets(finiteLowered, pointwise, nonzero, parts[1], polynomial_algebra.MonomialsDef))
				}))
			lowerIn := a.Have(
				"so its value at θ lies in R",
				"∀m:(D → num). P(m) ≠ R.zero ⇒ monomial_eval(R, θ, λy:D. m(y) - monomial_var(x, y)) ∈ R.carrier",
				By(lowerMonomial, ring, values, At(polynomial_algebra_evaluation.MonomialEvalIn, R, S)))
			raisedNonzero := a.Have(
				"where the derivative is nonzero, P is nonzero at the raised monomial",
				"∀m:(D → num). «partial»(m) ≠ R.zero ⇒ P(λy:D. m(y) + monomial_var(x, y)) ≠ R.zero",
				By(numerals, PolynomialAlgebraPartialDef, comm_ring.MulRightZeroOn.Read(ring)))
			covered := a.Have(
				"every monomial where the derivative is nonzero is the "+
					"lowering of a monomial of P with a positive exponent at x",
				"«partialSupport» ⊆ «lowered»",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					m := b.FixAs[Fun[D, Nat]]("m")
					nonzero := b.Simplified(b.Assume(), Fwd(functions.InFunSupport))
					raisedM := b.TermAs[Fun[D, Nat]]("λy:D. m(y) + monomial_var(x, y)")
					b.Show(
						"m is the lowering of m raised at x, where P is nonzero and the exponent of x positive",
						By(
							nonzero,
							raisedNonzero.At(m),
							lowerRaise.At(m),
							unit[0],
							nat_arith.AddEqZero,
							nat_arith.OneNotZero,
							set_image.FunInImage.At(lower, raised, raisedM)))
				}))
			raisedFinite := a.Have(
				"the monomials of P with a positive exponent at x are finitely many",
				"finite(«raisedSupport»)",
				BySets(
					parts[0],
					finite_set.FiniteRestrict.At(support, a.TermAs[Set[Fun[D, Nat]]]("λm:(D → num). m(x) ≠ 0"))))
			loweredFinite := a.Have(
				"and so are their lowerings",
				"finite(«lowered»)",
				By(raisedFinite, finite_set.FiniteImage.At(lower, raised)))
			partialFinite := a.Have(
				"so the derivative is nonzero at finitely many monomials",
				"finite(«partialSupport»)",
				By(loweredFinite, covered, finite_set.FiniteSubset.At(partialSupport, lowered)))
			partialIn := a.Have(
				"the coefficients of the derivative lie in R",
				"∀m:(D → num). «partial»(m) ∈ R.carrier",
				By(numerals, inR, PolynomialAlgebraPartialDef, comm_ring.MulIn.Read(ring)))
			injective := a.Have(
				"lowering is one-to-one on the monomials of P with a positive exponent at x",
				"injective_on(«raisedSupport», «lower»)",
				Unfold(functions.InjectiveOnDef),
				By(raiseLower))
			termsIn := a.Have(
				"at the lowering of a monomial of P with a positive exponent at x the scaled term lies in R",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"m ∈ «raisedSupport»"},
					Conclusion: "θ(x) * " +
						"(«partial»(λy:D. m(y) - monomial_var(x, y)) * " +
						"    monomial_eval(R, θ, λy:D. m(y) - monomial_var(x, y))) ∈ " +
						"R.carrier",
				},
				By(xValue, partialIn, lowerIn, comm_ring.MulIn.Read(ring)))
			loweredEval := a.Have(
				"the lowerings evaluate at θ in R",
				"∀m:(D → num). m ∈ «lowered» ⇒ monomial_eval(R, θ, m) ∈ R.carrier",
				By(
					lowerIn,
					set_image.ForallInImage.At(
						lower, raised, a.TermAs[Set[Fun[D, Nat]]]("λm:(D → num). monomial_eval(R, θ, m) ∈ R.carrier"))))
			scaledIn := a.Have(
				"so over the lowerings the scaled terms lie in R",
				"∀m:(D → num). m ∈ «lowered» ⇒ «scaled»(m) ∈ R.carrier",
				By(xValue, partialIn, loweredEval, comm_ring.MulIn.Read(ring)))
			scaledVanish := a.Have(
				"and vanish where the derivative does",
				"∀m:(D → num). m ∈ «lowered» ∧ m ∉ «partialSupport» ⇒ «scaled»(m) = R.zero",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					where := b.Simplified(b.Assume(), Fwd(functions.InFunSupport))
					b.Show(
						"the derivative's coefficient is zero there, and θ(x) times zero times a member of R is zero",
						By(
							where,
							xValue,
							loweredEval.At(m),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(b.TermAs[A]("monomial_eval(R, θ, m)")),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(θ.Apply(x))))
				}))
			productsIn := a.Have(
				"where the derivative is nonzero its terms lie in R",
				"∀m:(D → num). m ∈ «partialSupport» ⇒ «partial»(m) * monomial_eval(R, θ, m) ∈ R.carrier",
				By(a.Unfolded(covered, set_basic.SubsetDef), loweredEval, partialIn, comm_ring.MulIn.Read(ring)))
			supportEval := a.Have(
				"the monomials of P evaluate at θ in R",
				"∀m:(D → num). P(m) ≠ R.zero ⇒ monomial_eval(R, θ, m) ∈ R.carrier",
				BySets(parts[1], ring, values, At(polynomial_algebra_evaluation.MonomialEvalIn, R, S)))
			raisedInSupport := a.Have(
				"the monomials of P with a positive exponent at x are monomials of P",
				"«raisedSupport» ⊆ fun_support(R.zero, P)",
				BySets())
			weightedIn := a.Have(
				"over the monomials of P the weighted terms lie in R",
				"∀m:(D → num). m ∈ fun_support(R.zero, P) ⇒ «weighted»(m) ∈ R.carrier",
				BySets(numerals, inR, supportEval, comm_ring.MulIn.Read(ring)))
			weightedVanish := a.Have(
				"and vanish at those with exponent zero at x, whose numeral is zero",
				"∀m:(D → num). m ∈ fun_support(R.zero, P) ∧ m ∉ «raisedSupport» ⇒ «weighted»(m) = R.zero",
				BySets(
					inR,
					supportEval,
					comm_monoid.MonoidPowDef,
					comm_ring.MulIn.Read(ring),
					comm_ring.MulLeftZeroOn.Read(ring)))
			reindexed := a.Have(
				"at the lowering of a monomial m of P with a positive "+
					"exponent at x the scaled term is m(x) · P(m) · θ^m",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"m ∈ «raisedSupport»"},
					Conclusion: "θ(x) * " +
						"(«partial»(λy:D. m(y) - monomial_var(x, y)) * " +
						"    monomial_eval(R, θ, λy:D. m(y) - monomial_var(x, y))) = " +
						"monoid_pow(R.add, R.zero, R.one, m(x)) * (P(m) * monomial_eval(R, θ, m))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					member := b.Conjuncts(
						b.Assume(),
						"P is nonzero at m",
						"and the exponent of x is positive")
					loweredM := b.TermAs[Fun[D, Nat]]("λy:D. m(y) - monomial_var(x, y)")
					exponent := b.Have(
						"the lowered exponent of x plus one is m(x)",
						"m(x) - monomial_var(x, x) + 1 = m(x)",
						ByArith(member[1], unit[0]))
					coefficient := b.Have(
						"the derivative's coefficient at the lowering is m(x) · P(m)",
						"«partial»(λy:D. m(y) - monomial_var(x, y)) = monoid_pow(R.add, R.zero, R.one, m(x)) * P(m)",
						By(
							exponent,
							member[1],
							raiseLower.At(m),
							PolynomialAlgebraPartialDef.At(coefficientRing, x, P, loweredM)))
					xIn := b.Have(
						"x is a variable of m, a monomial of S, so it lies in S",
						"x ∈ S",
						BySets(member[1], parts[1], member[0], polynomial_algebra.MonomialsDef))
					shifted := b.Have(
						"and θ(x) times the lowered monomial is the monomial",
						"monomial_eval(R, θ, m) = θ(x) * monomial_eval(R, θ, λy:D. m(y) - monomial_var(x, y))",
						By(
							member[0],
							member[1],
							raiseLower.At(m),
							ring,
							values,
							xIn,
							lowerMonomial.At(m),
							polynomial_algebra_evaluation.MonomialEvalShift.At(R, S, θ, loweredM, x)))
					b.Do(coefficient.Rw(), shifted.Rw())
					b.Show(
						"the two products regroup the same four factors",
						ByArith(ring, member[0], xValue, numerals.At(b.TermAs[Nat]("m(x)")), inR.At(m), lowerIn.At(m)))
				}))
			a.Do(Unfold(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef))
			a.Show(
				"so the sum reindexes from the lowerings to the monomials of P",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, «partialSupport», «scaled»)"),
						"θ(x) multiplies through the finite sum",
						By(
							partialFinite,
							xValue,
							productsIn,
							module.ModuleSumSmul.Read(regular).AsFact().At(
								partialSupport,
								θ.Apply(x),
								a.TermAs[Fun[Fun[D, Nat], A]]("λm:(D → num). «partial»(m) * monomial_eval(R, θ, m)")))),
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, «lowered», «scaled»)"),
						"the sum extends to the lowerings, where the added terms are zero",
						By(
							loweredFinite,
							covered,
							scaledIn,
							scaledVanish,
							module.ModuleSumSupport.Read(regular).At(lowered, partialSupport, scaled))),
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, «raisedSupport», λm:(D → num). «scaled»(«lower»(m)))"),
						"lowering is one-to-one, so the sum over the lowerings is the sum over the monomials they lower",
						By(
							raisedFinite,
							injective,
							termsIn,
							module.ModuleSumImage.Read(regular).At(raised, lower, scaled))),
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, «raisedSupport», «weighted»)"),
						"term by term the scaled term at a lowering is the weighted term",
						By(
							reindexed,
							module.ModuleSumCongruence.At(
								a.TermAs[Op[A]]("R.add"),
								a.TermAs[A]("R.zero"),
								raised,
								a.TermAs[Fun[Fun[D, Nat], A]]("λm:(D → num). «scaled»(«lower»(m))"),
								weighted))),
					FinalLeg(
						"and the monomials of P with exponent zero at x add nothing",
						By(
							parts[0],
							raisedInSupport,
							weightedIn,
							weightedVanish,
							module.ModuleSumSupport.Read(regular).At(support, raised, weighted)))))
		}),
})}

// FreeAlgebraPartialDef — `free_algebra_partial(ι, R, x, u)`: the
// partial derivative in the variable x of the member u of the host, the
// derivative of its polynomial — the preimage chosen among all
// polynomials — carried back along ι.
var FreeAlgebraPartialDef = freeAlgebraPartialDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraPartialDef",
	Key:   "prop_ded1f6430a157827",
	Const: "free_algebra_partial",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → D → E → E",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D. ∀u:E. " +
			"    free_algebra_partial(ι, R, x, u) = " +
			"    ι(polynomial_algebra_partial(R, x, inverse_on(polynomial_algebra(R, 𝕌), ι, u)))",
	},
	Reading: "The member is read through the preimage among the polynomials in every variable, " +
		"as free_algebra_eval reads it, so the derivative is one function of the host whatever set of " +
		"variables u is taken in. With ι an embedding and R a commutative ring it carries the algebra " +
		"on S into itself and is zero at a variable outside S; off the algebra on 𝕌 the chosen " +
		"preimage is unspecified, so a statement reads the derivative of a member of the algebra.",
	Deps: []registry.EntryLike{PolynomialAlgebraPartialDef},
})}

// ---------------------------------------------------------------------------
// The laws of the partial derivative
// ---------------------------------------------------------------------------

// PartialIn — the partial derivative of a member of the algebra on S is
// a member of the algebra on S: it is ι of the derivative of the member's
// preimage chosen among all polynomials, which the embedding reads back
// as a polynomial of S, and the derivative of a polynomial of S is one
// (PolynomialPartialIn).
var PartialIn = partialInThm{family.Add(registry.ProofEntry{
	Name: "PartialIn",
	Key:  "prop_20d7643e25fa2364",
	Reading: "x need not lie in S: for x ∉ S no monomial of S has " +
		"an exponent at x, so the derivative is the algebra's zero.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀x:D. ∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_partial(ι, R, x, u) ∈ free_algebra(ι, R, S)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			x *Expr[D],
			u *Expr[E],
			embedding, ring, member Fact,
		) {
			decoded := a.Have(
				"the embedding reads u back to a polynomial of S",
				"inverse_on(polynomial_algebra(R, 𝕌), ι, u) ∈ polynomial_algebra(R, S)",
				By(embedding, member, free_algebra.FreeAlgebraEmbeddingDecode.At(ι, R)))
			a.Show(
				"so the derivative of u is ι of the derivative of that polynomial, which is a polynomial of S",
				By(
					ring,
					decoded,
					free_algebra.FreeAlgebraDef.At(ι, R, S),
					FreeAlgebraPartialDef.At(ι, R, x, u),
					PolynomialPartialIn.At(
						R, S, x, a.TermAs[Fun[Fun[D, Nat], A]]("inverse_on(polynomial_algebra(R, 𝕌), ι, u)")),
					set_image.FunInImage.At(
						ι,
						a.TermAs[Set[Fun[Fun[D, Nat], A]]]("polynomial_algebra(R, S)"),
						a.TermAs[Fun[Fun[D, Nat], A]](
							"polynomial_algebra_partial(R, x, inverse_on(polynomial_algebra(R, 𝕌), ι, u))"))))
		}),
})}

// PartialAdd — the partial derivative of a sum is the sum of the
// partial derivatives.
var PartialAdd = partialAddThm{family.Add(registry.ProofEntry{
	Name: "PartialAdd",
	Key:  "prop_35837654abefbd7a",
	Deps: []registry.EntryLike{
		FreeAlgebraPartialDef,
		PolynomialAlgebraPartialDef,
		PartialIn,
		free_algebra.FreeAlgebraRingDef,
		polynomial_algebra.PolynomialAlgebraRingDef,
		free_algebra.FreeAlgebraDef,
		function_module.FunAddDef,
		free_algebra.FreeAlgebraEmbeddingDecode,
		comm_ring.LeftDistribOn,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀x:D. ∀u v:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"u ∈ free_algebra(ι, R, S)",
			"v ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_partial(ι, R, x, free_algebra_ring(ι, R, S).add(u, v)) = " +
			"free_algebra_ring(ι, R, S).add(free_algebra_partial(ι, R, x, u), " +
			"    free_algebra_partial(ι, R, x, v))",
	},
		"the host's sum of ι(f) and ι(g) is ι of the pointwise sum f + g (the transported operation at "+
			"the preimages, FreeAlgebraEmbeddingDecode); the coefficient of the derivative of f + g at m is "+
			"the numeral times f(m') + g(m'), split by LeftDistribOn, and the two derivatives are "+
			"polynomials (PartialIn), so their host sum is ι of the pointwise sum again (the free algebra's "+
			"FreeAlgebraOpsIndependentOfVariables reads the sum of the algebra on S as the one on 𝕌)"),
})}

// PartialConst — the partial derivative of a constant is zero.
var PartialConst = partialConstThm{family.Add(registry.ProofEntry{
	Name: "PartialConst",
	Key:  "prop_a325776b7300292b",
	Deps: []registry.EntryLike{
		FreeAlgebraPartialDef,
		PolynomialAlgebraPartialDef,
		free_algebra.FreeAlgebraConstDef,
		polynomial_algebra.PolynomialAlgebraConstDef,
		free_algebra.FreeAlgebraRingDef,
		polynomial_algebra.PolynomialAlgebraRingDef,
		free_algebra.FreeAlgebraEmbeddingDecode,
		free_module.DeltaAtDef,
		function_module.FunZeroDef,
		comm_ring.MulRightZeroOn,
		comm_monoid.PowIn,
		free_algebra.FreeAlgebraConstHom,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D. ∀a:A.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"a ∈ R.carrier",
		},
		Conclusion: "free_algebra_partial(ι, R, x, free_algebra_const(ι, R, a)) = " +
			"free_algebra_ring(ι, R, 𝕌).zero",
	},
		"the constant is ι of the generator at the monomial of the constants with value a, a "+
			"polynomial since a ∈ R.carrier, so it is its own preimage "+
			"(FreeAlgebraEmbeddingDecode); m plus the monomial of x is never the monomial of the "+
			"constants, so every coefficient of the derivative is the numeral times R.zero, R.zero "+
			"by MulRightZeroOn, and ι of the zero polynomial is the host's zero (the transported "+
			"ring's zero; FreeAlgebraConstHom of the free algebra puts the constant in the algebra)"),
	Reading: "a ∈ R.carrier is load-bearing: a constant off the carrier is no polynomial " +
		"over R, its preimage is chosen arbitrarily and its derivative is unspecified.",
})}

// PartialVar — the partial derivative of the variable y in the variable
// x is one when x = y and zero otherwise: the variable is ι of the
// polynomial y, which lies among the polynomials in every variable and is
// so its own preimage; its derivative is the constant polynomial of R.one
// or R.zero (PolynomialPartialVar), and the constants, a ring map into the
// polynomials, carry those to the polynomials' one and zero, which ι
// carries to the host's.
var PartialVar = partialVarThm{family.Add(registry.ProofEntry{
	Name: "PartialVar",
	Key:  "prop_6ddd6a1f61df597a",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x y:D.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
		},
		Conclusion: "free_algebra_partial(ι, R, x, free_algebra_var(ι, R, y)) = " +
			"COND(x = y, free_algebra_ring(ι, R, 𝕌).one, free_algebra_ring(ι, R, 𝕌).zero)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			x, y *Expr[D],
			embedding, ring Fact,
		) {
			allVariables := a.TermAs[Set[D]]("𝕌")
			readback := a.Have(
				"the variable is ι of the polynomial y, a polynomial in "+
					"every variable, which the embedding reads back from its image",
				"inverse_on(polynomial_algebra(R, 𝕌), ι, free_algebra_var(ι, R, y)) = polynomial_algebra_var(R, y)",
				Unfold(free_algebra.FreeAlgebraVarDef),
				By(
					ring,
					embedding,
					free_algebra.FreeAlgebraEmbeddingDecode.At(ι, R),
					polynomial_algebra.PolynomialAlgebraVarIn.At(R, allVariables, y),
					set_basic.InUniv.At(y)))
			derivative := a.Have(
				"so the derivative is ι of the derivative of the polynomial y, the constant one or zero",
				"free_algebra_partial(ι, R, x, free_algebra_var(ι, R, y)) = "+
					"ι(polynomial_algebra_const(R, COND(x = y, R.one, R.zero)))",
				By(
					ring,
					readback,
					FreeAlgebraPartialDef.At(ι, R, x, a.TermAs[E]("free_algebra_var(ι, R, y)")),
					PolynomialPartialVar.At(R, x, y)))
			constants := a.Have(
				"the constants are a ring map into the polynomials in every variable",
				"ring_homomorphism(R, polynomial_algebra_ring(R, 𝕌⟨A:D⟩), polynomial_algebra_const(R))",
				By(ring, polynomial_algebra.PolynomialAlgebraConstHom.At(R, allVariables)))
			a.Show(
				"they carry R.one and R.zero to the polynomials' one and zero, and ι carries those to the host's",
				Unfold(free_algebra.FreeAlgebraRingDef),
				By(derivative, ring_homomorphism.MapOne.Read(constants), ring_homomorphism.MapZero.Read(constants)))
		}),
	Reading: "Over the zero ring the host's one is its zero, and both branches agree.",
})}

// PartialLeibniz — the partial derivative of a product obeys the Leibniz
// rule ∂(u * v) = u * ∂v + v * ∂u.
var PartialLeibniz = partialLeibnizThm{family.Add(registry.ProofEntry{
	Name: "PartialLeibniz",
	Key:  "prop_30e8186cddd39677",
	Reading: "Only the splitting of the numeral m(x) + 1 into two numerals is read, and numerals " +
		"add in every ring, so the rule holds over every commutative ring, characteristic p included.",
	Deps: []registry.EntryLike{
		FreeAlgebraPartialDef,
		PolynomialAlgebraPartialDef,
		PartialIn,
		PartialAdd,
		free_algebra.FreeAlgebraRingDef,
		polynomial_algebra.PolynomialAlgebraRingDef,
		polynomial_algebra.PolynomialAlgebraMulDef,
		polynomial_algebra.MonomialVarDef,
		free_algebra.FreeAlgebraEmbeddingDecode,
		module.RegularModuleOn,
		module.ModuleSumAdd,
		module.ModuleSumSupport,
		module.ModuleSumCongruence,
		comm_ring.LeftDistribOn,
		comm_ring.RightDistribOn,
		free_algebra.FreeAlgebraRingIsomorphism,
		polynomial_algebra.PolynomialAlgebraMulIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀x:D. ∀u v:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"u ∈ free_algebra(ι, R, S)",
			"v ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_partial(ι, R, x, free_algebra_ring(ι, R, S).mul(u, v)) = " +
			"free_algebra_ring(ι, R, S).add( " +
			"    free_algebra_ring(ι, R, S).mul(u, free_algebra_partial(ι, R, x, v)), " +
			"    free_algebra_ring(ι, R, S).mul(v, free_algebra_partial(ι, R, x, u)))",
	},
		"on the polynomials f, g, the coefficient at m of the derivative of the convolution is (m(x) "+
			"+ 1) Σ_{m₁ ≤ m + x} f(m₁) g(m + x - m₁); split m(x) + 1 as (m₁(x)) + (m(x) + 1 - m₁(x)) and "+
			"reindex each half by moving the extra x onto the other factor, giving the coefficients of f "+
			"* ∂g and g * ∂f (sums in the ring as a module over itself, RegularModuleOn, ModuleSumAdd, "+
			"ModuleSumSupport). The free algebra's FreeAlgebraRingIsomorphism and PolynomialAlgebraMulIn "+
			"carry the identity to the host, the host product of ι(f) and ι(g) being ι(f * g)"),
})}

// PartialSupportFinite — only finitely many variables have a nonzero
// partial derivative of a member of the algebra on S, all of them in S:
// its derivative in x is by definition ι of the derivative of its
// preimage f chosen among all polynomials, which ι carries to the host's
// zero where that derivative is zero, so u has a nonzero derivative only
// where f has; the embedding reads f as a polynomial of S, and those
// variables are finitely many, all in S (PolynomialPartialSupportFinite).
var PartialSupportFinite = partialSupportFiniteThm{family.Add(registry.ProofEntry{
	Name: "PartialSupportFinite",
	Key:  "prop_d1558bfdf40dad60",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "finite( " +
			"    fun_support(free_algebra_ring(ι, R, S).zero, λx:D. free_algebra_partial(ι, R, x, u))) ∧ " +
			"fun_support(free_algebra_ring(ι, R, S).zero, λx:D. free_algebra_partial(ι, R, x, u)) ⊆ S",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			u *Expr[E],
			embedding, ring, member Fact,
		) {
			decoded := a.Have(
				"the embedding reads u back to a polynomial of S",
				"inverse_on(polynomial_algebra(R, 𝕌), ι, u) ∈ polynomial_algebra(R, S)",
				By(embedding, member, free_algebra.FreeAlgebraEmbeddingDecode.At(ι, R)))
			inclusion := a.Have(
				"the derivative of u in x is ι of the polynomial's, the host's zero "+
					"where that one is zero, so it is nonzero only where the polynomial's is",
				"fun_support(free_algebra_ring(ι, R, S).zero, λx:D. free_algebra_partial(ι, R, x, u)) ⊆ "+
					"fun_support(fun_zero, "+
					"    λx:D. polynomial_algebra_partial(R, x, inverse_on(polynomial_algebra(R, 𝕌), ι, u)))",
				Unfold(FreeAlgebraPartialDef),
				BySets())
			model := a.Conjuncts(
				GroupPremises(
					ring,
					decoded,
					PolynomialPartialSupportFinite.At(
						R, S, a.TermAs[Fun[Fun[D, Nat], A]]("inverse_on(polynomial_algebra(R, 𝕌), ι, u)"))),
				"that polynomial has a nonzero derivative in finitely many variables",
				"all of them in S")
			a.Show(
				"so u has a nonzero derivative in finitely many variables, all of them in S",
				SplitConj(
					Case(
						"finitely many variables have a nonzero derivative: a subset of a finite set",
						By(inclusion, model[0], finite_set.FiniteSubset)),
					Case(
						"all of them lie in S: a subset of a subset of S",
						By(inclusion, model[1], set_order.SubsetTrans))))
		}),
})}

// ---------------------------------------------------------------------------
// Derivations
// ---------------------------------------------------------------------------

// DerivationOn — `derivation_on(R, S, f, N, D)`: D is a derivation of
// the algebra S over R, its structure map the ring map f, into the
// module N over S — D carries S's carrier into N's, is additive, obeys
// the Leibniz rule D(u * v) = u • D(v) + v • D(u), and is zero on the
// constants f(a).
var DerivationOn = derivationOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "DerivationOn",
	Key:     "prop_7995db87a5149559",
	Const:   "derivation_on",
	Type:    "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, C) → (B → C) → bool",
	Subject: "D",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, C). ∀D:(B → C). " +
			"    derivation_on(R, S, f, N, D) ⇔ " +
			"    ring_homomorphism(R, S, f) ∧ " +
			"    module_on(S, N) ∧ " +
			"    (∀u:B. u ∈ S.carrier ⇒ D(u) ∈ N.carrier) ∧ " +
			"    (∀u v:B. u ∈ S.carrier ∧ v ∈ S.carrier ⇒ D(S.add(u, v)) = N.add(D(u), D(v))) ∧ " +
			"    (∀u v:B. " +
			"        u ∈ S.carrier ∧ v ∈ S.carrier ⇒ " +
			"        D(S.mul(u, v)) = N.add(N.smul(u, D(v)), N.smul(v, D(u)))) ∧ " +
			"    (∀a:A. a ∈ R.carrier ⇒ D(f(a)) = N.zero)",
	},
	Reading: "The predicate conjoins the ring map that makes S an algebra over R and the module " +
		"structure of N over S, so it is false of anything that is not one. Zero on the constants " +
		"with the Leibniz rule makes D linear over R, D(f(a) * u) = f(a) • D(u). A derivation along a " +
		"ring map ψ from S into a module over another ring is a derivation into that module " +
		"restricted along ψ, mk_module(N.add, N.zero, N.neg, λu v. N.smul(ψ(u), v), N.carrier).",
})}

// DerivationUniqueOnGenerators — two derivations of the algebra on S
// over its constants into one module that agree at the variables of S
// agree on the whole algebra.
var DerivationUniqueOnGenerators = derivationUniqueOnGeneratorsThm{family.Add(registry.ProofEntry{
	Name: "DerivationUniqueOnGenerators",
	Key:  "prop_8b62a5a2f2fe249",
	Deps: []registry.EntryLike{
		DerivationOn,
		free_algebra.FreeAlgebraDef,
		free_algebra.FreeAlgebraRingDef,
		free_algebra.FreeAlgebraConstDef,
		free_algebra.FreeAlgebraVarDef,
		free_algebra.FreeAlgebraEmbeddingDef,
		free_module.FreeModuleExpand,
		module.ModuleSumCongruence,
		finite_set.FiniteInduct,
		polynomial_algebra_evaluation.MonomialAsProduct,
		free_algebra.FreeAlgebraRingIsomorphism,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		ring_homomorphism.Source,
		module.ModuleSumInsertMonoid,
		module.ModuleSumEmpty,
		comm_ring.MulMonoidOn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀N:module_ops(E, C). " +
			"∀d d':(E → C). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"derivation_on(R, free_algebra_ring(ι, R, S), free_algebra_const(ι, R), N, d)",
			"derivation_on(R, free_algebra_ring(ι, R, S), free_algebra_const(ι, R), N, d')",
			"∀s:D. s ∈ S ⇒ d(free_algebra_var(ι, R, s)) = d'(free_algebra_var(ι, R, s))",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "d(u) = d'(u)",
	},
		"every member of the algebra is a finite sum of constants times products of variables of S "+
			"(FreeModuleExpand carried along ι, with the free algebra's MonomialAsProduct, "+
			"FreeAlgebraRingIsomorphism, FreeAlgebraConstHom and FreeAlgebraVarIn); both maps are "+
			"additive, vanish on the constants and so take const(a) * w to const(a) • d(w), and by the "+
			"Leibniz rule agree on a product of variables by induction on its degree (FiniteInduct on the "+
			"support of the exponent, the product peeled by ModuleSumInsertMonoid at the algebra's "+
			"multiplicative monoid, MulMonoidOn), the empty product being the constant one (ModuleSumEmpty)"),
	Reading: "The ring hypothesis on R is carried by the derivations themselves: each conjoins the " +
		"ring map from R to the algebra on S. The two derivations go into one module; a derivation " +
		"along an algebra map is one into the target restricted along the map, as derivation_on reads " +
		"it. At S = ∅ the algebra is the constants and both derivations vanish on it.",
})}

// FreeAlgebraDerivationDef — `free_algebra_derivation(ι, R, S, ε, N, v,
// u)`: the derivation of the algebra on S into the module N along ε with
// the value v(s) at the variable of s — at a member u of the algebra the
// sum Σ_s ε(∂_s u) • v(s) over the variables s of S where the derivative
// of u is nonzero, and N.zero off the algebra.
var FreeAlgebraDerivationDef = freeAlgebraDerivationDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraDerivationDef",
	Key:   "prop_cad88602aebc327b",
	Const: "free_algebra_derivation",
	Type: "(((D → num) → A) → E) → " +
		"ring_ops(A) → " +
		"set(D) → " +
		"(E → F) → " +
		"module_ops(F, G) → " +
		"(D → G) → " +
		"E → " +
		"G",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀ε:(E → F). " +
			"∀N:module_ops(F, G). " +
			"∀v:(D → G). " +
			"∀u:E. " +
			"    free_algebra_derivation(ι, R, S, ε, N, v, u) = " +
			"    COND(u ∈ free_algebra(ι, R, S), " +
			"        module_sum(N.add, " +
			"            N.zero, " +
			"            {s:D | " +
			"                s ∈ S ∧ ¬(free_algebra_partial(ι, R, s, u) = free_algebra_ring(ι, R, S).zero)}, " +
			"            λs:D. N.smul(ε(free_algebra_partial(ι, R, s, u)), v(s))), " +
			"        N.zero)",
	},
	Reading: "v is read on S only and the value is N.zero off the algebra on S, so the " +
		"derivation is fixed as one function of the host by its values at the variables. The " +
		"sum is finite for ι an embedding and R a commutative ring (PartialSupportFinite), " +
		"and ε reads each derivative, a member of the algebra (PartialIn). At S = ∅ every " +
		"member is a constant, the index set is empty and the derivation is zero.",
	Deps: []registry.EntryLike{FreeAlgebraPartialDef},
})}

// FreeAlgebraDerivationFromValues — values v(s) in N at the variables of
// S make free_algebra_derivation a derivation of the algebra on S over
// its constants into N along a ring map ε, with the value v(s) at the
// variable of s.
var FreeAlgebraDerivationFromValues = freeAlgebraDerivationFromValuesThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraDerivationFromValues",
	Key:  "prop_6e0a832c9ca1cd9c",
	Reading: "v is asked to lie in N's carrier on S only; its values elsewhere are not read. N " +
		"is a module over the algebra only through ε, as derivation_on reads a derivation along a " +
		"ring map. ε a ring map is load-bearing: it makes N a module over the algebra, it splits " +
		"ε(u * ∂v + v * ∂u) into ε(u) ε(∂v) + ε(v) ε(∂u) for the Leibniz rule, and ε(one) = K.one " +
		"gives the value at var s. Over the zero ring R the index set at var s is empty, and the " +
		"same equation forces K, and so N, to be zero, so v(s) = N.zero agrees with the empty sum.",
	Deps: []registry.EntryLike{
		FreeAlgebraDerivationDef,
		DerivationOn,
		PartialIn,
		PartialAdd,
		PartialConst,
		PartialVar,
		PartialLeibniz,
		PartialSupportFinite,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleOn,
		module.ModuleSumIn,
		module.ModuleSumSupport,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.ModuleSumInsert,
		module.ModuleSumEmpty,
		module.SmulAddRight,
		module.SmulMul,
		module.SmulOne,
		module.ZeroSmul,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀K:ring_ops(F). " +
			"∀ε:(E → F). " +
			"∀N:module_ops(F, G). " +
			"∀v:(D → G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"ring_homomorphism(free_algebra_ring(ι, R, S), K, ε)",
			"module_on(K, N)",
			"∀s:D. s ∈ S ⇒ v(s) ∈ N.carrier",
		},
		Conclusion: "derivation_on(R, " +
			"    free_algebra_ring(ι, R, S), " +
			"    free_algebra_const(ι, R), " +
			"    scalar_restriction(ε, N), " +
			"    free_algebra_derivation(ι, R, S, ε, N, v)) ∧ " +
			"(∀s:D. s ∈ S ⇒ free_algebra_derivation(ι, R, S, ε, N, v, free_algebra_var(ι, R, s)) = v(s))",
	},
		"the constants are a ring map into the algebra (FreeAlgebraConstHom), and N through ε is a "+
			"module over it, each law of module_on(K, N) read at ε's values (ModuleOn, RingHomomorphism). "+
			"At a member u the sum is finite (PartialSupportFinite) and lies in N's carrier (ModuleSumIn, "+
			"the scalars ε of members of the algebra by PartialIn and MapIn). Additivity: PartialAdd, ε "+
			"additive and SmulAddRight, both sides read over the union of the two supports "+
			"(ModuleSumSupport, ModuleSumAdd). Leibniz: PartialLeibniz, ε keeping sums and products, "+
			"SmulMul and ModuleSumSmul pull ε(u) and ε(v) out of the two sums. A constant has no nonzero "+
			"derivative (PartialConst), so its index set is empty (ModuleSumEmpty). At var s split on the "+
			"host's one being its zero: if not, the index set is {s} (PartialVar) and ε(one) • v(s) = "+
			"v(s) (MapOne, SmulOne, ModuleSumInsert); if so, it is empty, and ε(one) = K.one and ε(zero) "+
			"= K.zero make v(s) = K.zero • v(s) = N.zero (AdditiveHomomorphism, ZeroSmul)"),
})}

// FreeAlgebraDerivationRepresentation — every derivation d of the
// algebra on S over its constants into N along ε is free_algebra_derivation
// at its own values at the variables.
var FreeAlgebraDerivationRepresentation = freeAlgebraDerivationRepresentationThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraDerivationRepresentation",
	Key:  "prop_fc3cdc7534b0c444",
	Reading: "The equation holds on the algebra only: d is " +
		"unconstrained off it, where free_algebra_derivation is N.zero.",
	Deps: []registry.EntryLike{
		FreeAlgebraDerivationFromValues,
		DerivationUniqueOnGenerators,
		DerivationOn,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀K:ring_ops(F). " +
			"∀ε:(E → F). " +
			"∀N:module_ops(F, G). " +
			"∀d:(E → G). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"ring_homomorphism(free_algebra_ring(ι, R, S), K, ε)",
			"module_on(K, N)",
			"derivation_on(R, " +
				"    free_algebra_ring(ι, R, S), " +
				"    free_algebra_const(ι, R), " +
				"    scalar_restriction(ε, N), " +
				"    d)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_derivation(ι, R, S, ε, N, λs:D. d(free_algebra_var(ι, R, s)), u) = d(u)",
	},
		"the values d(var s) lie in N's carrier, var s being in the algebra "+
			"(FreeAlgebraVarIn, DerivationOn), so FreeAlgebraDerivationFromValues "+
			"makes free_algebra_derivation at them a derivation into the same module "+
			"with the same values at the variables; DerivationUniqueOnGenerators"),
})}

// ChainRule — the partial derivative of the image of u under an algebra
// map Φ over φ: ∂_t Φ(u) = Σ_s Φ(∂_s u) * ∂_t Φ(var s), over the
// finitely many variables s of S where u's derivative is nonzero.
var ChainRule = chainRuleThm{family.Add(registry.ProofEntry{
	Name: "ChainRule",
	Key:  "prop_facadd601f0a113d",
	Deps: []registry.EntryLike{
		DerivationUniqueOnGenerators,
		DerivationOn,
		PartialIn,
		PartialAdd,
		PartialConst,
		PartialVar,
		PartialLeibniz,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.RegularModuleOn,
		module.ModuleSumSupport,
		module.ModuleSumAdd,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀t:I. " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_partial(ι', R', t, Φ(u)) = " +
			"module_sum(free_algebra_ring(ι', R', T).add, " +
			"    free_algebra_ring(ι', R', T).zero, " +
			"    {s:D | s ∈ S ∧ ¬(free_algebra_partial(ι, R, s, u) = free_algebra_ring(ι, R, S).zero)}, " +
			"    λs:D. " +
			"        free_algebra_ring(ι', R', T).mul(Φ(free_algebra_partial(ι, R, s, u)), " +
			"            free_algebra_partial(ι', R', t, Φ(free_algebra_var(ι, R, s)))))",
	},
		"both sides, as maps of u, are derivations of the algebra on S over its constants into "+
			"the algebra on T made a module through Φ, mk_module(T.add, T.zero, T.neg, λa b. Φ(a) * "+
			"b, free_algebra(ι', R', T)) (RegularModuleOn restricted along the ring map Φ): the left "+
			"by PartialAdd, PartialLeibniz and PartialConst at T, Φ(const a) being const'(φ(a)) with "+
			"φ(a) in the carrier of R' (FreeAlgebraHomomorphismDef); the right term by term, its "+
			"index sets for u, v and u + v all inside a finite set where the other terms vanish "+
			"(PartialSupportFinite, ModuleSumSupport). At var s₀ the right side is the one term "+
			"Φ(one) * ∂_t Φ(var s₀) (PartialVar, MapOne), so DerivationUniqueOnGenerators closes; "+
			"the algebras are rings by the free algebra's FreeAlgebraCommRingOn, the constants a "+
			"ring map into them by FreeAlgebraConstHom, the variables members by FreeAlgebraVarIn"),
	Reading: "Φ is an algebra map over φ, so it carries the constants to constants, " +
		"whose derivatives vanish; without that the constants' images would contribute. " +
		"The sum runs over the finitely many s of S where the derivative of u is nonzero, " +
		"the sum of the host ring of T. t need not lie in T: at t ∉ T both sides are zero.",
})}

// PartialBaseChange — an algebra map that sends the variables of X to
// constants and renames the variables of Y by h commutes with the
// partial derivatives: the derivative of the image in t is the sum of
// the images of the derivatives in the variables y of Y with h(y) = t.
var PartialBaseChange = partialBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "PartialBaseChange",
	Key:  "prop_4c651feab56aca88",
	Deps: []registry.EntryLike{
		ChainRule,
		PartialConst,
		PartialVar,
		PartialSupportFinite,
		PartialIn,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.MapOne,
		ring_homomorphism.AdditiveHomomorphism,
		module.RegularModuleOn,
		module.ModuleSumSupport,
		module.ModuleSumCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀X Y:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀h:(D → I). " +
			"∀t:I. " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, X ∪ Y, T, Φ)",
			"∀x:D. x ∈ X ⇒ ∃b:B. b ∈ R'.carrier ∧ Φ(free_algebra_var(ι, R, x)) = free_algebra_const(ι', R', b)",
			"∀y:D. y ∈ Y ⇒ Φ(free_algebra_var(ι, R, y)) = free_algebra_var(ι', R', h(y))",
			"u ∈ free_algebra(ι, R, X ∪ Y)",
		},
		Conclusion: "free_algebra_partial(ι', R', t, Φ(u)) = " +
			"module_sum(free_algebra_ring(ι', R', T).add, " +
			"    free_algebra_ring(ι', R', T).zero, " +
			"    {y:D | " +
			"        y ∈ Y ∧ " +
			"        h(y) = t ∧ " +
			"        ¬(free_algebra_partial(ι, R, y, u) = free_algebra_ring(ι, R, X ∪ Y).zero)}, " +
			"    λy:D. Φ(free_algebra_partial(ι, R, y, u)))",
	},
		"ChainRule at u: a term at x ∈ X carries the derivative of a constant, zero by "+
			"PartialConst; a term at y ∈ Y carries ∂_t var'(h(y)), one when h(y) = t and zero "+
			"otherwise (PartialVar), so the sum drops to the y with h(y) = t (ModuleSumSupport). "+
			"The horizontal augmentation of a relative resolution is such a map: the variables "+
			"of the base's resolution go to coefficients, the rest are renamed"),
	Reading: "The variables of X go to the coefficients: each is sent to a constant of the " +
		"algebra on T. The variables of Y are renamed by h, which need not be injective: the " +
		"variable t collects the derivatives of every y of Y with h(y) = t — u = var y₁ · var y₂ " +
		"with y₁ ≠ y₂ and h(y₁) = h(y₂) = t gives 2 · var t on both sides — and for h injective on Y " +
		"and t = h(y₀) the sum is the one term Φ(∂_{y₀} u). A variable in both X and Y forces a " +
		"constant to equal a variable, which happens only over the zero ring, where both sides vanish.",
})}

// ---------------------------------------------------------------------------
// Conormal maps
// ---------------------------------------------------------------------------

// ConormalHom — `conormal_hom(P, S, ε, N, γ)`: γ is a conormal map of the
// ring map ε from P to S into the module N over S — on the kernel I of ε
// it takes values in N, is additive and linear over P through ε,
// γ(u * x) = ε(u) • γ(x), and it is N.zero off I.
var ConormalHom = conormalHomThm{family.DefineStructure(registry.DefEntry{
	Name:    "ConormalHom",
	Key:     "prop_83e615bc033a29b3",
	Const:   "conormal_hom",
	Type:    "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, C) → (A → C) → bool",
	Subject: "γ",
	Equations: []string{
		"∀P:ring_ops(A). ∀S:ring_ops(B). ∀ε:(A → B). ∀N:module_ops(B, C). ∀γ:(A → C). " +
			"    conormal_hom(P, S, ε, N, γ) ⇔ " +
			"    (∀x:A. x ∈ ring_kernel(S.zero, P.carrier, ε) ⇒ γ(x) ∈ N.carrier) ∧ " +
			"    (∀x y:A. " +
			"        x ∈ ring_kernel(S.zero, P.carrier, ε) ∧ y ∈ ring_kernel(S.zero, P.carrier, ε) ⇒ " +
			"        γ(P.add(x, y)) = N.add(γ(x), γ(y))) ∧ " +
			"    (∀u x:A. " +
			"        u ∈ P.carrier ∧ x ∈ ring_kernel(S.zero, P.carrier, ε) ⇒ " +
			"        γ(P.mul(u, x)) = N.smul(ε(u), γ(x))) ∧ " +
			"    (∀x:A. x ∉ ring_kernel(S.zero, P.carrier, ε) ⇒ γ(x) = N.zero)",
	},
	Reading: "No ring hypothesis is conjoined: the predicate reads P's sum and product on the " +
		"kernel and ε's values there. With ε a ring map and N a module over S it is a homomorphism of " +
		"modules over P from I to N, N made one through ε; it kills I², a product of two members x, y " +
		"of I going to ε(x) • γ(y) = S.zero • γ(y), and linearity over a ring that P is an algebra " +
		"over is the case u a constant. The value off I is fixed as N.zero, so two conormal maps that " +
		"agree on I are one function. No quotient I/I² is formed: a conormal map is read on I itself.",
})}

// DerivationRestrictionConormal — a derivation of P into N along ε,
// restricted to the kernel of ε and N.zero off it, is a conormal map.
var DerivationRestrictionConormal = derivationRestrictionConormalThm{family.Add(registry.ProofEntry{
	Name: "DerivationRestrictionConormal",
	Key:  "prop_a7b21553f3d0e1b1",
	Reading: "P is any algebra over R through h, ε any ring map out of it; " +
		"nothing asks ε to be onto or P to be free. The kernel is what kills the " +
		"second Leibniz term, d(u * x) = ε(u) • d(x) + ε(x) • d(u) with ε(x) = S.zero.",
	Deps: []registry.EntryLike{
		ConormalHom,
		DerivationOn,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.KernelIdeal,
		module.ZeroSmul,
		module.AddGroupOn,
		module.SmulIn,
		module.ModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(E). " +
			"∀h:(A → E). " +
			"∀S:ring_ops(B). " +
			"∀ε:(E → B). " +
			"∀N:module_ops(B, C). " +
			"∀d:(E → C).",
		Hypotheses: []string{
			"ring_homomorphism(P, S, ε)",
			"module_on(S, N)",
			"derivation_on(R, P, h, scalar_restriction(ε, N), d)",
		},
		Conclusion: "conormal_hom(P, " +
			"    S, " +
			"    ε, " +
			"    N, " +
			"    λx:E. COND(x ∈ ring_kernel(S.zero, P.carrier, ε), d(x), N.zero))",
	},
		"unfold conormal_hom (ConormalHom): the kernel is an ideal of P (KernelIdeal, "+
			"RingKernelDef), so a sum of two members of I and a product u * x with x in I lie in I "+
			"and the COND takes d's branch on both sides. On I the map is d, valued in N's carrier "+
			"and additive (DerivationOn); the Leibniz rule gives d(u * x) = ε(u) • d(x) + ε(x) • "+
			"d(u), where ε(x) = S.zero and S.zero • d(u) = N.zero (ZeroSmul, d(u) in the carrier), "+
			"and N.zero is the additive identity (AddGroupOn). Off I the COND gives N.zero"),
})}

// ---------------------------------------------------------------------------
// The corpus's polynomials in one variable
// ---------------------------------------------------------------------------

// PartialDerivativeTransport — along an embedding, the map from the
// corpus's polynomials in one variable to the algebra on {x} carries
// the formal derivative of p to the partial derivative in x of the image
// of p.
var PartialDerivativeTransport = partialDerivativeTransportThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeTransport",
	Key:  "prop_70ed1dce14549d18",
	Reading: "The left side is the image of polynomial_derivative(p), the sequence n ↦ (n + 1) · p(n " +
		"+ 1), written applied: its coefficient at a monomial m of {x} is that sequence at m(x). p is " +
		"asked to be a polynomial over R's carrier, so its coefficient function is a polynomial in every " +
		"variable, the preimage the derivative reads through ι. The numeral m(x) + 1 of the partial " +
		"derivative and polynomial_derivative's suc(m(x)) are one count: at n·δ_x the free-algebra side " +
		"is (n + 1) · p(n + 1), polynomial_derivative(p) at n, and off the monomials of {x} both sides " +
		"are zero. Over the zero ring both sides are ι of the zero coefficient function.",
	Deps: []registry.EntryLike{
		FreeAlgebraPartialDef,
		PolynomialAlgebraPartialDef,
		polynomial.PolynomialDerivativeDef,
		polynomial.PolynomialOverDef,
		vec_space.VecDef,
		free_algebra.PolynomialOneVariableHomomorphism,
		free_algebra.FreeAlgebraEmbeddingDef,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.MonomialsDef,
		polynomial_algebra.MonomialVarDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		free_module.DeltaAtDef,
		free_algebra.FreeAlgebraEmbeddingDecode,
		polynomial_algebra.PolynomialAlgebraSubset,
		comm_ring.MulRightZeroOn,
		comm_ring.ZeroIn,
		comm_monoid.PowIn,
		comm_ring.AddMonoidOn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D. ∀p:(num → A).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "ι(λm:(D → num). COND(m ∈ monomials({x}), polynomial_derivative(p)(m(x)), R.zero)) = " +
			"free_algebra_partial(ι, R, x, ι(λm:(D → num). COND(m ∈ monomials({x}), p(m(x)), R.zero)))",
	},
		"the coefficient function f of p is a polynomial of {x}, so one in every variable "+
			"(PolynomialAlgebraSubset, as in the free algebra's PolynomialOneVariableHomomorphism), and it "+
			"is the preimage free_algebra_partial reads (FreeAlgebraEmbeddingDecode), and the derivative's "+
			"coefficient at m is the numeral m(x) + 1 times f at m plus the monomial of x "+
			"(PolynomialAlgebraPartialDef). At a monomial m of {x} that sum is the monomial of {x} with "+
			"exponent m(x) + 1, so the coefficient is (m(x) + 1) · p(m(x) + 1), polynomial_derivative's at "+
			"m(x) (PolynomialDerivativeDef); at any other m the sum is no monomial of {x}, f is R.zero there "+
			"and so is the product (MulRightZeroOn, the numeral in the carrier by PowIn at the additive "+
			"monoid). The comparison is coefficient by coefficient; on the basis xⁿ both sides are n · xⁿ⁻¹"),
})}
