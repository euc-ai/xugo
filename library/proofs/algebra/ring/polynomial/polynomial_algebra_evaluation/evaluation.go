// evaluation.go — a polynomial evaluated in a second ring at a map of
// the coefficients and a value for each variable: a monomial's value is
// the product of the powers of the values, a polynomial's the sum over
// its support of the mapped coefficients times the values of their
// monomials. A ring homomorphism carries a monomial's value to its value
// at the images; evaluation keeps sums and products, so along a ring
// homomorphism it is a ring homomorphism out of the polynomials of S. It
// reads only the operations of its two rings, so restricting either ring
// to a subset of its carrier leaves the value as it is.

package polynomial_algebra_evaluation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The value of a monomial
// ---------------------------------------------------------------------------

// MonomialEvalDef — `monomial_eval(R', θ, m)`: the monomial m evaluated
// in the ring R' at the values θ of the variables, the product over the
// variables where m is nonzero of θ(x) ^ m(x).
var MonomialEvalDef = monomialEvalDefThm{family.Define(registry.DefEntry{
	Name:  "MonomialEvalDef",
	Key:   "prop_9915202c5a7eb6d7",
	Const: "monomial_eval",
	Type:  "ring_ops(B) → (D → B) → (D → num) → B",
	Equations: []string{
		"∀R':ring_ops(B). ∀θ:(D → B). ∀m:(D → num). " +
			"    monomial_eval(R', θ, m) = " +
			"    module_sum(R'.mul, R'.one, fun_support(0, m), λx:D. monoid_pow(R'.mul, R'.one, θ(x), m(x)))",
	},
	Reading: "The product is the finite fold of the multiplication, so the monomial " +
		"of the constants evaluates to R'.one; at an exponent function of infinite support " +
		"the fold is unspecified, and no polynomial has such a monomial in its support.",
})}

// MonomialEvalShift — raising the exponent of one variable x by one
// multiplies the value of a monomial m of S by θ(x), θ lying in the
// carrier on S and at x: the raised monomial's variables are x and the
// other variables of m, and splitting off the factor at x from both
// products leaves the same product over the other variables, where the
// two exponents agree.
var MonomialEvalShift = monomialEvalShiftThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalShift",
	Key:  "prop_cbc9484de9ff1acb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀θ:(D → A). ∀m:(D → num). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"m ∈ monomials(S)",
			"θ(x) ∈ R.carrier",
		},
		Conclusion: "monomial_eval(R, θ, λy:D. m(y) + monomial_var(x, y)) = θ(x) * monomial_eval(R, θ, m)",
		Abbrev: Abbrev{
			{Name: "rest", Text: "delete(fun_support(0, m), x)"},
			{Name: "raised", Text: "λy:D. monoid_pow(R.mul, R.one, θ(y), m(y) + monomial_var(x, y))"},
			{Name: "powers", Text: "λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			θ *Arrow[D, A],
			m *Arrow[D, Nat],
			x *Expr[D],
			ring, values, monomial, xValue Fact,
		) {
			products := comm_ring.MulMonoidOn.Read(ring)
			xMonomial := At(polynomial_algebra.MonomialVarValues, x)
			support := a.TermAs[Set[D]]("fun_support(0, m)")
			rest := a.TermAs[Set[D]]("«rest»")
			raised := a.TermAs[Fun[D, A]]("«raised»")
			powers := a.TermAs[Fun[D, A]]("«powers»")
			variables := a.Conjuncts(
				a.Have(
					"m is nonzero at finitely many variables, and those other than x lie in S, where θ lies in R",
					"finite(fun_support(0, m)) ∧ (∀y:D. y ∈ «rest» ⇒ θ(y) ∈ R.carrier)",
					BySets(values, monomial, polynomial_algebra.MonomialSupport.At(S, m))),
				"m is nonzero at finitely many variables",
				"θ lies in R at those other than x")
			restFinite := a.Have(
				"the variables of m other than x are finitely many",
				"finite(«rest»)",
				By(variables[0], finite_set.FiniteDeleteImp.At(support, x)))
			xOut := a.Have(
				"and x is not among them",
				"x ∉ «rest»",
				By(set_basic.InDelete.At(support, x, x)))
			exponents := a.Have(
				"raising x makes the exponent nonzero at x and changes it at no other variable",
				"∀y:D. m(y) + monomial_var(x, y) ≠ 0 ⇔ (m(y) ≠ 0 ∧ y ≠ x) ∨ y = x",
				Derive(func(b *Argument) {
					b.FixAs[D]("y")
					b.Cases(b.TermAs[Bool]("y = x"))
					b.When(
						"at x the exponent is m(x) + 1, never zero",
						func(c *Argument, same Fact) {
							c.Show(
								"a sum is zero only when both terms are",
								By(same, xMonomial, nat_arith.AddEqZero, nat_arith.OneNotZero))
						})
					b.Otherwise(
						"at another variable monomial_var(x) adds nothing",
						func(c *Argument, other Fact) {
							c.Show(
								"so the exponent is m's own",
								By(Normalized, other, xMonomial, nat_arith.AddZero))
						})
				}))
			raisedSupport := a.Have(
				"so the variables of the raised exponent are x and the other variables of m",
				"fun_support(0, λy:D. m(y) + monomial_var(x, y)) = insert(x, «rest»)",
				BySets(exponents))
			a.Do(Unfold(MonomialEvalDef), raisedSupport.Rw())
			xPowers := a.Have(
				"every power of θ(x) lies in R",
				"∀j:num. monoid_pow(R.mul, R.one, θ(x), j) ∈ R.carrier",
				By(xValue, comm_monoid.PowIn.Read(products)))
			restPowers := a.Have(
				"and so does every power of θ at the other variables of m",
				"∀y:D. ∀j:num. y ∈ «rest» ⇒ monoid_pow(R.mul, R.one, θ(y), j) ∈ R.carrier",
				By(variables[1], comm_monoid.PowIn.Read(products)))
			splitRaised := a.Have(
				"the raised product splits off its factor at x",
				"module_sum(R.mul, R.one, insert(x, «rest»), «raised») = "+
					"monoid_pow(R.mul, R.one, θ(x), m(x) + monomial_var(x, x)) * "+
					"module_sum(R.mul, R.one, «rest», «raised»)",
				By(
					restFinite,
					xOut,
					xPowers,
					restPowers,
					module.ModuleSumInsertMonoid.Read(products).At(rest, x, raised)))
			agree := a.Have(
				"off x the raised exponents are m's",
				Statement{
					Binders: "∀z:D.",
					Hypotheses: []string{
						"z ∈ «rest»",
					},
					Conclusion: "monoid_pow(R.mul, R.one, θ(z), m(z) + monomial_var(x, z)) = " +
						"monoid_pow(R.mul, R.one, θ(z), m(z))",
				},
				By(Normalized, xMonomial, set_basic.InDelete, nat_arith.AddZero))
			restAgree := a.Have(
				"so the two products over the other variables agree",
				"module_sum(R.mul, R.one, «rest», «raised») = module_sum(R.mul, R.one, «rest», «powers»)",
				By(
					agree,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("R.mul"), a.TermAs[A]("R.one"), rest, raised, powers)))
			cover := a.Have(
				"x and the other variables of m are finitely many and hold every variable of m",
				"finite(insert(x, «rest»)) ∧ fun_support(0, m) ⊆ insert(x, «rest»)",
				BySets(
					variables[0],
					finite_set.FiniteDeleteImp.At(support, x),
					finite_set.FiniteInsert.At(x, rest)))
			plainOver := a.Have(
				"over them the product of m's powers is the monomial, the factor at x being one when m(x) = 0",
				"module_sum(R.mul, R.one, insert(x, «rest»), «powers») = "+
					"module_sum(R.mul, R.one, fun_support(0, m), «powers»)",
				By(
					cover,
					xPowers,
					restPowers,
					set_basic.InInsert,
					comm_monoid.MonoidPowDef,
					module.ModuleSumSupportMonoid.Read(products).At(
						a.TermAs[Set[D]]("insert(x, «rest»)"), support, powers)))
			splitPlain := a.Have(
				"and splits off its factor at x",
				"module_sum(R.mul, R.one, insert(x, «rest»), «powers») = "+
					"monoid_pow(R.mul, R.one, θ(x), m(x)) * module_sum(R.mul, R.one, «rest», «powers»)",
				By(
					restFinite,
					xOut,
					xPowers,
					restPowers,
					module.ModuleSumInsertMonoid.Read(products).At(rest, x, powers)))
			atX := a.Have(
				"the factor at x gains one power of θ(x)",
				"monoid_pow(R.mul, R.one, θ(x), m(x) + monomial_var(x, x)) = "+
					"θ(x) * monoid_pow(R.mul, R.one, θ(x), m(x))",
				By(xMonomial, nat_arith.Add1, comm_monoid.MonoidPowDef))
			power := a.TermAs[A]("monoid_pow(R.mul, R.one, θ(x), m(x))")
			others := a.TermAs[A]("module_sum(R.mul, R.one, «rest», «powers»)")
			members := a.Have(
				"θ(x), its power and the product over the other variables lie in R",
				"θ(x) ∈ R.carrier ∧ "+
					"monoid_pow(R.mul, R.one, θ(x), m(x)) ∈ R.carrier ∧ "+
					"module_sum(R.mul, R.one, «rest», «powers») ∈ R.carrier",
				By(
					xValue,
					xPowers,
					restFinite,
					restPowers,
					module.ModuleSumInMonoid.Read(products).At(rest, powers)))
			a.Show(
				"so the raised monomial is θ(x) times the monomial",
				By(
					splitRaised,
					restAgree,
					atX,
					plainOver,
					splitPlain,
					members,
					comm_monoid.AssocOn.Read(products).AsFact().At(θ.Apply(x), power, others)))
		}),
})}

// MonomialEvalIn — a monomial of S evaluated at values in the carrier on S
// lies in the carrier: it is a finite product of powers of those values.
var MonomialEvalIn = monomialEvalInThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalIn",
	Key:  "prop_c70beeb7333bc7e3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀S:set(D). ∀θ:(D → B). ∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"m ∈ monomials(S)",
		},
		Conclusion: "monomial_eval(R, θ, m) ∈ R.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[B]],
			S *Expr[Set[D]],
			θ *Arrow[D, B],
			m *Arrow[D, Nat],
			ring, values, monomial Fact,
		) {
			support := a.Have(
				"m is nonzero at finitely many variables, all of them in S, where θ lies in the carrier",
				"finite(fun_support(0, m)) ∧ (∀y:D. y ∈ fun_support(0, m) ⇒ θ(y) ∈ R.carrier)",
				BySets(values, monomial, polynomial_algebra.MonomialSupport.At(S, m)))
			monoid := comm_ring.MulMonoidOn.Read(ring)
			a.Show(
				"a finite product of powers of members of the carrier lies in it",
				Simp(Fwd(MonomialEvalDef)),
				By(
					support,
					comm_monoid.PowIn.Read(monoid),
					module.ModuleSumInMonoid.Read(monoid).At(
						a.TermAs[Set[D]]("fun_support(0, m)"),
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))"))))
		}),
})}

// MonomialEvalAdd — evaluating a monomial turns a sum of exponents into a
// product: over the union of the two supports, finite, each factor
// θ(y)^(m₁(y) + m₂(y)) is θ(y)^m₁(y) · θ(y)^m₂(y), the product of the pairs
// is the product of the two products, and each product over the union is
// the product over its own support, the extra factors θ(y)^0 being one.
var MonomialEvalAdd = monomialEvalAddThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalAdd",
	Key:  "prop_2a3dc57c6a8c81ac",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀S:set(D). ∀θ:(D → B). ∀m₁ m₂:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"m₁ ∈ monomials(S)",
			"m₂ ∈ monomials(S)",
		},
		Conclusion: "monomial_eval(R, θ, λy:D. m₁(y) + m₂(y)) = " +
			"monomial_eval(R, θ, m₁) * monomial_eval(R, θ, m₂)",
		Abbrev: Abbrev{
			{Name: "union", Text: "fun_support(0, m₁) ∪ fun_support(0, m₂)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[B]],
			S *Expr[Set[D]],
			θ *Arrow[D, B],
			m1, m2 *Arrow[D, Nat],
			ring, values, first, second Fact,
		) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			supports := a.Conjuncts(
				a.Have(
					"m₁ and m₂ are nonzero at finitely many variables, all of them in S",
					"finite(fun_support(0, m₁)) ∧ "+
						"finite(fun_support(0, m₂)) ∧ "+
						"(∀y:D. m₁(y) ≠ 0 ⇒ y ∈ S) ∧ "+
						"(∀y:D. m₂(y) ≠ 0 ⇒ y ∈ S)",
					By(
						first,
						second,
						polynomial_algebra.MonomialSupport.At(S, m1),
						polynomial_algebra.MonomialSupport.At(S, m2))),
				"m₁ is nonzero at finitely many variables",
				"so is m₂",
				"those of m₁ lie in S",
				"and those of m₂")
			exponents := a.Have(
				"an exponent of m₁ + m₂ is nonzero exactly where one of m₁, m₂ is",
				"∀y:D. m₁(y) + m₂(y) ≠ 0 ⇔ m₁(y) ≠ 0 ∨ m₂(y) ≠ 0",
				ByArith())
			union := a.Have(
				"so the support of m₁ + m₂ is the union of the two supports",
				"fun_support(0, λy:D. m₁(y) + m₂(y)) = «union»",
				BySets(exponents))
			onUnion := a.Have(
				"the union is finite, and θ lies in the carrier on it",
				"finite(«union») ∧ (∀y:D. y ∈ «union» ⇒ θ(y) ∈ R.carrier)",
				BySets(
					supports[0],
					supports[1],
					supports[2],
					supports[3],
					values,
					finite_set.FiniteUnionImp.At(
						a.TermAs[Set[D]]("fun_support(0, m₁)"), a.TermAs[Set[D]]("fun_support(0, m₂)"))))
			powers := comm_monoid.PowIn.Read(monoid)
			split := a.Have(
				"each factor over the union splits, θ(y)^(m₁(y) + m₂(y)) = θ(y)^m₁(y) · θ(y)^m₂(y)",
				"module_sum(R.mul, R.one, «union», λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y) + m₂(y))) = "+
					"module_sum(R.mul, "+
					"    R.one, "+
					"    «union», "+
					"    λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y)) * monoid_pow(R.mul, R.one, θ(y), m₂(y)))",
				By(onUnion, module.ModuleSumCongruence, comm_monoid.PowAddOn.Read(monoid)))
			restricted := a.Have(
				"over the union each product is the product over "+
					"its own support, the extra factors θ(y)^0 being one",
				"module_sum(R.mul, R.one, «union», λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y))) = "+
					"module_sum(R.mul, R.one, fun_support(0, m₁), λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y))) ∧ "+
					"module_sum(R.mul, R.one, «union», λy:D. monoid_pow(R.mul, R.one, θ(y), m₂(y))) = "+
					"module_sum(R.mul, R.one, fun_support(0, m₂), λy:D. monoid_pow(R.mul, R.one, θ(y), m₂(y)))",
				Derive(func(b *Argument) {
					union := b.TermAs[Set[D]]("«union»")
					offFirst := b.Have(
						"the support of m₁ lies in the union, and off it θ(y)^m₁(y) = θ(y)^0 = one",
						"fun_support(0, m₁) ⊆ «union» ∧ "+
							"(∀y:D. y ∈ «union» ∧ y ∉ fun_support(0, m₁) ⇒ monoid_pow(R.mul, R.one, θ(y), m₁(y)) = R.one)",
						BySets(comm_monoid.MonoidPowDef))
					offSecond := b.Have(
						"so does that of m₂, and off it θ(y)^m₂(y) is one",
						"fun_support(0, m₂) ⊆ «union» ∧ "+
							"(∀y:D. y ∈ «union» ∧ y ∉ fun_support(0, m₂) ⇒ monoid_pow(R.mul, R.one, θ(y), m₂(y)) = R.one)",
						BySets(comm_monoid.MonoidPowDef))
					b.Show(
						"both products drop the factors off their supports",
						By(
							onUnion,
							offFirst,
							offSecond,
							powers,
							module.ModuleSumSupportMonoid.Read(monoid).At(
								union,
								b.TermAs[Set[D]]("fun_support(0, m₁)"),
								b.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y))")),
							module.ModuleSumSupportMonoid.Read(monoid).At(
								union,
								b.TermAs[Set[D]]("fun_support(0, m₂)"),
								b.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m₂(y))"))))
				}))
			a.Show(
				"so the product over the union of the pairs is the product of the two products",
				Simp(Fwd(MonomialEvalDef)),
				union.Rw(),
				By(
					split,
					onUnion,
					restricted,
					powers,
					module.ModuleSumAddMonoid.Read(monoid).At(
						a.TermAs[Set[D]]("«union»"),
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m₁(y))"),
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m₂(y))"))))
		}),
})}

// MonomialEvalScale — scaling every value by c scales a monomial's value by
// c to the sum of its exponents: over the finite support each factor
// (θ(y) · c)^m(y) is θ(y)^m(y) · c^m(y), the product of the pairs is the
// product of the two products, and the powers of c multiply to the power at
// the sum of the exponents (module.PowNatSum).
var MonomialEvalScale = monomialEvalScaleThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalScale",
	Key:  "prop_68ef772fdd96c5f0",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀S:set(D). ∀θ:(D → B). ∀c:B. ∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"c ∈ R.carrier",
			"m ∈ monomials(S)",
		},
		Conclusion: "monomial_eval(R, λy:D. θ(y) * c, m) = " +
			"monomial_eval(R, θ, m) * monoid_pow(R.mul, R.one, c, sum(fun_support(0, m), m))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[B]],
			S *Expr[Set[D]],
			θ *Arrow[D, B],
			c *Expr[B],
			m *Arrow[D, Nat],
			ring, values, cIn, monomial Fact,
		) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			support := a.TermAs[Set[D]]("fun_support(0, m)")
			onSupport := a.Have(
				"m is nonzero at finitely many variables, all of them in S, where θ lies in the carrier",
				"finite(fun_support(0, m)) ∧ (∀y:D. y ∈ fun_support(0, m) ⇒ θ(y) ∈ R.carrier)",
				BySets(values, monomial, polynomial_algebra.MonomialSupport.At(S, m)))
			split := a.Have(
				"each factor splits, (θ(y) · c)^m(y) = θ(y)^m(y) · c^m(y)",
				"module_sum(R.mul, R.one, fun_support(0, m), λy:D. monoid_pow(R.mul, R.one, θ(y) * c, m(y))) = "+
					"module_sum(R.mul, "+
					"    R.one, "+
					"    fun_support(0, m), "+
					"    λy:D. monoid_pow(R.mul, R.one, θ(y), m(y)) * monoid_pow(R.mul, R.one, c, m(y)))",
				By(comm_monoid.MulPowOn.Read(monoid), cIn, onSupport, module.ModuleSumCongruence))
			a.Show(
				"the product of the pairs is the product of the two products",
				Simp(Fwd(MonomialEvalDef)),
				By(
					split,
					cIn,
					onSupport,
					comm_monoid.PowIn.Read(monoid),
					module.PowNatSum.Read(monoid).AsFact().At(c, support, m),
					module.ModuleSumAddMonoid.Read(monoid).At(
						support,
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))"),
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, c, m(y))"))))
		}),
})}

// MonomialEvalPow — raising every value to the e-th power raises a
// monomial's value to the e-th power: over the finite support each factor
// (θ(y)^e)^m(y) is (θ(y)^m(y))^e, and w ↦ w^e keeps the one and products,
// so it carries the product of the factors to the product of their powers.
var MonomialEvalPow = monomialEvalPowThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalPow",
	Key:  "prop_263856508d56491a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀S:set(D). ∀θ:(D → B). ∀e:num. ∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"m ∈ monomials(S)",
		},
		Conclusion: "monomial_eval(R, λy:D. monoid_pow(R.mul, R.one, θ(y), e), m) = " +
			"monoid_pow(R.mul, R.one, monomial_eval(R, θ, m), e)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[B]],
			S *Expr[Set[D]],
			θ *Arrow[D, B],
			e *Expr[Nat],
			m *Arrow[D, Nat],
			ring, values, monomial Fact,
		) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			support := a.TermAs[Set[D]]("fun_support(0, m)")
			onSupport := a.Have(
				"m is nonzero at finitely many variables, all of them in S, where θ lies in the carrier",
				"finite(fun_support(0, m)) ∧ (∀y:D. y ∈ fun_support(0, m) ⇒ θ(y) ∈ R.carrier)",
				BySets(values, monomial, polynomial_algebra.MonomialSupport.At(S, m)))
			parts := a.Conjuncts(
				onSupport,
				"the support is finite",
				"and θ lies in the carrier on it")
			swapped := a.Have(
				"each factor (θ(y)^e)^m(y) is (θ(y)^m(y))^e, both the power at e·m(y)",
				Statement{
					Binders:    "∀y:D.",
					Hypotheses: []string{"y ∈ fun_support(0, m)"},
					Conclusion: "monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, θ(y), e), m(y)) = " +
						"monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, θ(y), m(y)), e)",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("y")
					value := b.Have(
						"θ(y) lies in the carrier",
						"θ(y) ∈ R.carrier",
						By(b.Assume(), parts[1]))
					theta := b.TermAs[B]("θ(y)")
					exponent := b.TermAs[Nat]("m(y)")
					b.Show(
						"the exponents multiply in either order",
						By(
							value,
							b.Have(
								"e·m(y) = m(y)·e",
								"e * m(y) = m(y) * e",
								ByArith()),
							comm_monoid.PowPowOn.Read(monoid).AsFact().At(theta, e, exponent),
							comm_monoid.PowPowOn.Read(monoid).AsFact().At(theta, exponent, e)))
				}))
			factors := a.Have(
				"so the two products agree factor by factor",
				"module_sum(R.mul, "+
					"    R.one, "+
					"    fun_support(0, m), "+
					"    λy:D. monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, θ(y), e), m(y))) = "+
					"module_sum(R.mul, "+
					"    R.one, "+
					"    fun_support(0, m), "+
					"    λy:D. monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, θ(y), m(y)), e))",
				By(swapped, module.ModuleSumCongruence))
			power := a.Have(
				"w ↦ w^e keeps the one and products, so carries the "+
					"product of the factors to the product of their powers",
				"monoid_pow(R.mul, "+
					"    R.one, "+
					"    module_sum(R.mul, R.one, fun_support(0, m), λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))), "+
					"    e) = "+
					"module_sum(R.mul, "+
					"    R.one, "+
					"    fun_support(0, m), "+
					"    λy:D. monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, θ(y), m(y)), e))",
				By(
					parts[0],
					parts[1],
					comm_monoid.PowIn.Read(monoid),
					comm_monoid.IdentityPowOn.Read(monoid).AsFact().At(e),
					comm_monoid.MulPowOn.Read(monoid),
					module.ModuleSumMonoidHomomorphism.Read(monoid).At(
						a.TermAs[Op[B]]("R.mul"),
						a.TermAs[B]("R.one"),
						a.TermAs[Fun[B, B]]("λw:B. monoid_pow(R.mul, R.one, w, e)"),
						support,
						a.TermAs[Fun[D, B]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))"))))
			a.Show(
				"the product of the powers is the power of the product",
				Simp(Fwd(MonomialEvalDef)),
				By(factors, power))
		}),
})}

// MonomialEvalNatural — a ring homomorphism carries the value of a monomial
// to the value of the monomial at the images of the values: over the
// finite support of m it keeps the one and products, so it carries the
// product of the factors θ(y)^m(y) to the product of their images, and
// it keeps powers, so each image is φ(θ(y))^m(y).
var MonomialEvalNatural = monomialEvalNaturalThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalNatural",
	Key:  "prop_b82e2723c67fb2c9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀φ:(A → B). ∀S:set(D). ∀θ:(D → A). ∀m:(D → num).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
			"∀y:D. y ∈ S ⇒ θ(y) ∈ R.carrier",
			"m ∈ monomials(S)",
		},
		Conclusion: "φ(monomial_eval(R, θ, m)) = monomial_eval(T, λy:D. φ(θ(y)), m)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			S *Expr[Set[D]],
			θ *Arrow[D, A],
			m *Arrow[D, Nat],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			values, monomial Fact,
		) {
			products := comm_ring.MulMonoidOn.Read(ring_homomorphism.Source.Read(hom))
			onSupport := a.Have(
				"m is nonzero at finitely many variables, all of them in S, where θ lies in the carrier",
				"finite(fun_support(0, m)) ∧ (∀y:D. y ∈ fun_support(0, m) ⇒ θ(y) ∈ R.carrier)",
				BySets(values, monomial, polynomial_algebra.MonomialSupport.At(S, m)))
			factors := a.Have(
				"φ keeps powers, so it carries each factor θ(y)^m(y) to φ(θ(y))^m(y)",
				"module_sum(T.mul, T.one, fun_support(0, m), λy:D. φ(monoid_pow(R.mul, R.one, θ(y), m(y)))) = "+
					"module_sum(T.mul, T.one, fun_support(0, m), λy:D. monoid_pow(T.mul, T.one, φ(θ(y)), m(y)))",
				By(onSupport, ring_homomorphism.RingMapPower.Read(hom), module.ModuleSumCongruence))
			a.Show(
				"φ keeps the one and products, so it carries the "+
					"product of the factors to the product of their images",
				Simp(Fwd(MonomialEvalDef)),
				By(
					onSupport,
					factors,
					comm_monoid.PowIn.Read(products),
					ring_homomorphism.MapOne.Read(hom),
					ring_homomorphism.MapMul.Read(hom),
					module.ModuleSumMonoidHomomorphism.Read(products).At(
						a.TermAs[Op[B]]("T.mul"),
						a.TermAs[B]("T.one"),
						φ,
						a.TermAs[Set[D]]("fun_support(0, m)"),
						a.TermAs[Fun[D, A]]("λy:D. monoid_pow(R.mul, R.one, θ(y), m(y))"))))
		}),
})}

// MonomialEvalInIdeal — a monomial with a positive exponent at a variable y
// whose value lies in an ideal I has its value in I: the product splits off
// the factor θ(y)^m(y), which is θ(y)^(m(y) − 1) · θ(y), and an ideal
// absorbs a multiple of its member.
var MonomialEvalInIdeal = monomialEvalInIdealThm{family.Add(registry.ProofEntry{
	Name: "MonomialEvalInIdeal",
	Key:  "prop_744e1557f966b099",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀S:set(D). ∀I:set(B). ∀θ:(D → B). ∀m:(D → num). ∀y:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_ideal(R, I)",
			"∀z:D. z ∈ S ⇒ θ(z) ∈ R.carrier",
			"m ∈ monomials(S)",
			"m(y) ≠ 0",
			"θ(y) ∈ I",
		},
		Conclusion: "monomial_eval(R, θ, m) ∈ I",
		Abbrev: Abbrev{
			{Name: "others", Text: "module_sum(R.mul, " +
				"    R.one, " +
				"    delete(fun_support(0, m), y), " +
				"    λz:D. monoid_pow(R.mul, R.one, θ(z), m(z)))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[B]],
			S *Expr[Set[D]],
			I *Expr[Set[B]],
			θ *Arrow[D, B],
			m *Arrow[D, Nat],
			y *Expr[D],
			ring, ideal, values, monomial, positive, yIn Fact,
		) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			support := a.TermAs[Set[D]]("fun_support(0, m)")
			factors := a.TermAs[Fun[D, B]]("λz:D. monoid_pow(R.mul, R.one, θ(z), m(z))")
			thetaY := a.TermAs[B]("θ(y)")
			lower := a.TermAs[Nat]("m(y) - 1")
			onSupport := a.Conjuncts(
				a.Have(
					"m is nonzero at finitely many variables, y among them, all in S, where θ lies in the carrier",
					"finite(fun_support(0, m)) ∧ "+
						"y ∈ fun_support(0, m) ∧ "+
						"(∀z:D. z ∈ fun_support(0, m) ⇒ θ(z) ∈ R.carrier)",
					BySets(values, monomial, positive, polynomial_algebra.MonomialSupport.At(S, m))),
				"the support is finite",
				"y lies in it",
				"and θ lies in the carrier on it")
			yInCarrier := a.Have(
				"θ(y) lies in the carrier, I lying in it",
				"θ(y) ∈ R.carrier",
				BySets(yIn, ring_ideal.IdealSubset.Read(ideal)))
			split := a.Have(
				"the product splits off the factor at y",
				"module_sum(R.mul, R.one, fun_support(0, m), λz:D. monoid_pow(R.mul, R.one, θ(z), m(z))) = "+
					"monoid_pow(R.mul, R.one, θ(y), m(y)) * «others»",
				By(
					onSupport[0],
					onSupport[1],
					onSupport[2],
					powIn,
					module.ModuleSumDeleteMonoid.Read(monoid).At(support, y, factors)))
			others := a.Have(
				"the other factors multiply into the carrier",
				"«others» ∈ R.carrier",
				By(
					onSupport[0],
					onSupport[2],
					powIn,
					finite_set.FiniteDelete.At(support, y),
					set_basic.InDelete,
					module.ModuleSumInMonoid.Read(monoid).At(
						a.TermAs[Set[D]]("delete(fun_support(0, m), y)"), factors)))
			exponent := a.Have(
				"m(y) − 1 + 1 = m(y), m(y) being positive",
				"m(y) - 1 + 1 = m(y)",
				ByArith(positive))
			power := a.Have(
				"so θ(y)^m(y) = θ(y)^(m(y) − 1) · θ(y)",
				"monoid_pow(R.mul, R.one, θ(y), m(y)) = monoid_pow(R.mul, R.one, θ(y), m(y) - 1) * θ(y)",
				By(
					exponent,
					yInCarrier,
					comm_monoid.PowAddOn.Read(monoid).AsFact().At(thetaY, lower, a.TermAs[Nat]("1")),
					comm_monoid.PowOneOn.Read(monoid).AsFact().At(thetaY)))
			lowerIn := powIn.AsFact().At(thetaY, lower)
			regrouped := a.Have(
				"so the value of m is θ(y) times the rest",
				"monoid_pow(R.mul, R.one, θ(y), m(y)) * «others» = "+
					"(monoid_pow(R.mul, R.one, θ(y), m(y) - 1) * «others») * θ(y)",
				ByArith(ring, yInCarrier, others, lowerIn, Scaled(a.TermAs[B]("«others»"), power)))
			a.Show(
				"a multiple of θ(y), in I",
				Simp(Fwd(MonomialEvalDef)),
				split.Rw(),
				regrouped.Rw(),
				By(
					yIn,
					others,
					lowerIn,
					yInCarrier,
					comm_ring.MulIn.Read(ring),
					ring_ideal.IdealMul.Read(ideal).AsFact().At(
						a.TermAs[B]("monoid_pow(R.mul, R.one, θ(y), m(y) - 1) * «others»"), thetaY)))
		}),
})}

// ---------------------------------------------------------------------------
// The value of a polynomial
// ---------------------------------------------------------------------------

// PolynomialAlgebraEvalDef — `polynomial_algebra_eval(R, R', φ, θ, f)`:
// the polynomial f evaluated in the ring R', each coefficient carried by
// φ and each variable x given the value θ(x) — the sum over the
// monomials where f is nonzero of φ(f(m)) * monomial_eval(R', θ, m).
var PolynomialAlgebraEvalDef = polynomialAlgebraEvalDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraEvalDef",
	Key:   "prop_253552fc86b01d60",
	Const: "polynomial_algebra_eval",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → (D → B) → ((D → num) → A) → B",
	Equations: []string{
		"∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀f:((D → num) → A). " +
			"    polynomial_algebra_eval(R, R', φ, θ, f) = " +
			"    module_sum(R'.add, " +
			"        R'.zero, " +
			"        fun_support(R.zero, f), " +
			"        λm:(D → num). R'.mul(φ(f(m)), monomial_eval(R', θ, m)))",
	},
	Reading: "The sum runs over the support of f, finite for a polynomial; φ " +
		"is read on f's nonzero coefficients only, and θ only at the variables of " +
		"those monomials, so the evaluation of a polynomial of S reads θ on S alone.",
	Deps: []registry.EntryLike{MonomialEvalDef},
})}

// PolynomialAlgebraEvalOver — the value of a polynomial is its sum over
// any finite set M of monomials of S that holds its support: at a
// monomial of M where the coefficient vanishes the term is
// φ(R.zero) · monomial_eval(R', θ, m) = R'.zero, so the sum over the
// support extends to M.
var PolynomialAlgebraEvalOver = polynomialAlgebraEvalOverThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalOver",
	Key:  "prop_a17a8988a8bd38a9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀S:set(D). " +
			"∀M:set(D → num). " +
			"∀f:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"∀m:(D → num). f(m) ∈ R.carrier",
			"finite(M)",
			"M ⊆ monomials(S)",
			"fun_support(R.zero, f) ⊆ M",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, f) = " +
			"module_sum(R'.add, R'.zero, M, λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			M *Expr[Set[Fun[D, Nat]]],
			f *Arrow[Fun[D, Nat], A],
			hom, values, coefficients, finite, monomial, support Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			terms := a.Have(
				"on M each term is a product of two members of R', so lies in R'",
				"∀m:(D → num). m ∈ M ⇒ φ(f(m)) * monomial_eval(R', θ, m) ∈ R'.carrier",
				By(
					target,
					ring_homomorphism.MapIn.Read(hom),
					comm_ring.MulIn.Read(target),
					values,
					coefficients,
					monomial,
					MonomialEvalIn,
					set_basic.SubsetDef))
			vanish := a.Have(
				"off the support of f the term is φ(R.zero) times a member of R', which is R'.zero",
				"∀m:(D → num). m ∈ M ∧ m ∉ fun_support(R.zero, f) ⇒ φ(f(m)) * monomial_eval(R', θ, m) = R'.zero",
				By(
					target,
					ring_homomorphism.MapZero.Read(hom),
					comm_ring.MulLeftZeroOn.Read(target),
					values,
					monomial,
					MonomialEvalIn,
					set_basic.SubsetDef))
			a.Show(
				"so the sum over the support of f extends to M",
				Simp(Fwd(PolynomialAlgebraEvalDef)),
				By(
					finite,
					terms,
					vanish,
					support,
					module.ModuleSumSupportMonoid.Read(comm_ring.AddMonoidOn.Read(target)).At(
						M,
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
						a.TermAs[Fun[Fun[D, Nat], B]]("λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m)"))))
		}),
})}

// PolynomialAlgebraEvalIn — a polynomial of S takes its value in R': the
// value is a finite sum of the products φ(f(m)) · monomial_eval(R', θ, m)
// over the monomials of S where f is nonzero, each a product of two
// members of R'.
var PolynomialAlgebraEvalIn = polynomialAlgebraEvalInThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalIn",
	Key:  "prop_5aaeeb66ec7c4613",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀S:set(D). " +
			"∀f:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, f) ∈ R'.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			f *Arrow[Fun[D, Nat], A],
			hom, values, fIn Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			fParts := a.Conjuncts(
				a.Simplified(fIn, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in R")
			terms := a.Have(
				"each term of the value is a product of two members of R', so lies in R'",
				"∀m:(D → num). m ∈ fun_support(R.zero, f) ⇒ φ(f(m)) * monomial_eval(R', θ, m) ∈ R'.carrier",
				By(
					target,
					ring_homomorphism.MapIn.Read(hom),
					comm_ring.MulIn.Read(target),
					values,
					fParts[2],
					fParts[1],
					MonomialEvalIn,
					set_basic.SubsetDef))
			a.Show(
				"a finite sum of members of R' lies in R'",
				Simp(Fwd(PolynomialAlgebraEvalDef)),
				By(
					fParts[0],
					terms,
					module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(target)).At(
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
						a.TermAs[Fun[Fun[D, Nat], B]]("λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m)"))))
		}),
})}

// PolynomialAlgebraEvalAdd — evaluation takes the sum of two polynomials
// of S to the sum of their values: all three values are sums over the
// union of the two supports (PolynomialAlgebraEvalOver), and there each
// term of f + g splits, φ keeping sums and the product distributing over
// them, into the term of f plus the term of g.
var PolynomialAlgebraEvalAdd = polynomialAlgebraEvalAddThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalAdd",
	Key:  "prop_166d3400d3543cca",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀S:set(D). " +
			"∀f g:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, fun_add(f, g)) = " +
			"polynomial_algebra_eval(R, R', φ, θ, f) + polynomial_algebra_eval(R, R', φ, θ, g)",
		Abbrev: Abbrev{
			{Name: "union", Text: "fun_support(R.zero, f) ∪ fun_support(R.zero, g)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			f, g *Arrow[Fun[D, Nat], A],
			hom, values, fIn, gIn Fact,
		) {
			ring := ring_homomorphism.Source.Read(hom)
			target := ring_homomorphism.Target.Read(hom)
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
			union := a.Have(
				"the union of the two supports is a finite set of monomials of S holding each",
				"finite(«union») ∧ "+
					"«union» ⊆ monomials(S) ∧ "+
					"fun_support(R.zero, f) ⊆ «union» ∧ "+
					"fun_support(R.zero, g) ⊆ «union»",
				BySets(
					fParts[0],
					gParts[0],
					fParts[1],
					gParts[1],
					finite_set.FiniteUnionImp.At(
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)"))))
			coefficients := a.Have(
				"every coefficient f(m) + g(m) of the sum lies in R",
				"∀m:(D → num). fun_add(f, g, m) ∈ R.carrier",
				Simp(Fwd(function_module.FunAddDef)),
				By(fParts[2], gParts[2], comm_ring.AddIn.Read(ring)))
			support := a.Have(
				"the sum is nonzero only where f or g is, R.zero + R.zero being R.zero",
				"fun_support(R.zero, λm:(D → num). fun_add(f, g, m)) ⊆ «union»",
				BySets(
					function_module.FunAddDef,
					comm_ring.ZeroIn.Read(ring),
					comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring))))
			terms := a.Have(
				"on the union the terms of f and of g lie in R'",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"m ∈ «union»"},
					Conclusion: "φ(f(m)) * monomial_eval(R', θ, m) ∈ R'.carrier ∧ " +
						"φ(g(m)) * monomial_eval(R', θ, m) ∈ R'.carrier",
				},
				By(
					target,
					ring_homomorphism.MapIn.Read(hom),
					comm_ring.MulIn.Read(target),
					values,
					fParts[2],
					gParts[2],
					union,
					MonomialEvalIn,
					set_basic.SubsetDef))
			splits := a.Have(
				"on the union each term of f + g is the term of f plus the term of g",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"m ∈ «union»"},
					Conclusion: "φ(fun_add(f, g, m)) * monomial_eval(R', θ, m) = " +
						"φ(f(m)) * monomial_eval(R', θ, m) + φ(g(m)) * monomial_eval(R', θ, m)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					inUnion := b.Assume()
					sumValue := b.Have(
						"φ keeps the sum f(m) + g(m)",
						"φ(f(m) + g(m)) = φ(f(m)) + φ(g(m))",
						By(
							fParts[2].At(m),
							gParts[2].At(m),
							At(ring_homomorphism.MapAdd.Read(hom), f.Apply(m), g.Apply(m))))
					members := b.Have(
						"φ(f(m)), φ(g(m)) and the value of m, a monomial of S, lie in R'",
						"φ(f(m)) ∈ R'.carrier ∧ φ(g(m)) ∈ R'.carrier ∧ monomial_eval(R', θ, m) ∈ R'.carrier",
						By(
							target,
							ring_homomorphism.MapIn.Read(hom),
							MonomialEvalIn,
							set_basic.SubsetDef,
							values,
							fParts[2],
							gParts[2],
							inUnion,
							union))
					b.Show(
						"so the product distributes over the sum",
						Simp(Fwd(function_module.FunAddDef)),
						sumValue.Rw(),
						ByArith(target, members))
				}))
			sum := a.TermAs[Fun[Fun[D, Nat], A]]("fun_add(f, g)")
			over := a.TermAs[Set[Fun[D, Nat]]]("«union»")
			a.Show(
				"all three values are sums over the union of the two supports",
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    «union», "+
								"    λm:(D → num). φ(fun_add(f, g, m)) * monomial_eval(R', θ, m))"),
						"f + g is nonzero only on the union, a finite set of monomials of S",
						By(
							hom,
							values,
							coefficients,
							union,
							support,
							PolynomialAlgebraEvalOver.At(R, RPrime, φ, θ, S, over, sum))),
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    «union», "+
								"    λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m) + φ(g(m)) * monomial_eval(R', θ, m))"),
						"split each term",
						By(splits, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, R'.zero, «union», λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m)) + "+
								"module_sum(R'.add, R'.zero, «union», λm:(D → num). φ(g(m)) * monomial_eval(R', θ, m))"),
						"a finite sum of sums is the sum of the two sums",
						By(
							terms,
							union,
							module.ModuleSumAddMonoid.Read(comm_ring.AddMonoidOn.Read(target)).At(
								over,
								a.TermAs[Fun[Fun[D, Nat], B]]("λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m)"),
								a.TermAs[Fun[Fun[D, Nat], B]]("λm:(D → num). φ(g(m)) * monomial_eval(R', θ, m)")))),
					FinalLeg(
						"and the values of f and of g are their sums over the union",
						By(
							hom,
							values,
							fParts[2],
							gParts[2],
							union,
							PolynomialAlgebraEvalOver.At(R, RPrime, φ, θ, S, over, f),
							PolynomialAlgebraEvalOver.At(R, RPrime, φ, θ, S, over, g))),
				))
		}),
})}

// PolynomialAlgebraEvalMul — evaluation takes the product of two
// polynomials of S to the product of their values. The product of the
// values multiplies out to the sum, over the pairs of a monomial where f
// is nonzero and one where g is, of φ(f(m₁) · g(m₂)) · monomial_eval(R',
// θ, m₁ + m₂), a value of a sum of exponents being the product of the
// values (MonomialEvalAdd). Grouped by the sum m of the two parts, the
// pairs adding to m give φ of the coefficient of the product at m
// (polynomial_algebra.PolynomialAlgebraMulPairs) times the value of m,
// and the value of the product is its sum over those sums, which hold
// its support (polynomial_algebra.PolynomialAlgebraMulSupportInSums,
// PolynomialAlgebraEvalOver). The pairs read only the two supports; the
// convolution over the monomials below one monomial, the route of the
// one-variable evaluation, would need one monomial bounding both.
var PolynomialAlgebraEvalMul = polynomialAlgebraEvalMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalMul",
	Key:  "prop_57c675ff10590fa8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀S:set(D). " +
			"∀f g:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, polynomial_algebra_mul(R, f, g)) = " +
			"polynomial_algebra_eval(R, R', φ, θ, f) * polynomial_algebra_eval(R, R', φ, θ, g)",
		Abbrev: Abbrev{
			{Name: "fTerms", Text: "λm:(D → num). φ(f(m)) * monomial_eval(R', θ, m)"},
			{Name: "gTerms", Text: "λm:(D → num). φ(g(m)) * monomial_eval(R', θ, m)"},
			{Name: "pairTerms", Text: "λp:prod(D → num, D → num). " +
				"    φ(f(fst(p)) * g(snd(p))) * monomial_eval(R', θ, λx:D. fst(p, x) + snd(p, x))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			f, g *Arrow[Fun[D, Nat], A],
			hom, values, fIn, gIn Fact,
		) {
			ring := ring_homomorphism.Source.Read(hom)
			target := ring_homomorphism.Target.Read(hom)
			regular := module.RegularModuleOn.Read(target)
			// productIn reads the memberships fIn and gIn, which the unpacks
			// below rewrite in place, so it comes first.
			productIn := a.Have(
				"every coefficient of the product lies in R, the product being a polynomial of S",
				"∀m:(D → num). polynomial_algebra_mul(R, f, g, m) ∈ R.carrier",
				By(
					GroupPremises(ring, fIn, gIn, polynomial_algebra.PolynomialAlgebraMulIn.At(R, S, f, g)),
					polynomial_algebra.PolynomialAlgebraMember))
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
			fSupport := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)")
			gSupport := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)")
			cross := a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«cross»")
			sums := a.TermAs[Set[Fun[D, Nat]]]("«sums»")
			addParts := a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], Fun[D, Nat]]](
				"λp:prod(D → num, D → num). λx:D. fst(p, x) + snd(p, x)")
			fTerms := a.TermAs[Fun[Fun[D, Nat], B]]("«fTerms»")
			gTerms := a.TermAs[Fun[Fun[D, Nat], B]]("«gTerms»")
			pairTerms := a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], B]]("«pairTerms»")
			crossFinite := a.Have(
				"so the pairs of a monomial where f is nonzero and one where g is are finitely many",
				"finite(«cross»)",
				By(fParts[0], gParts[0], finite_set.FiniteProduct.At(fSupport, gSupport)))
			partsIn := a.Have(
				"the two parts of such a pair are monomials of S",
				"∀p:prod(D → num, D → num). p ∈ «cross» ⇒ fst(p) ∈ monomials(S) ∧ snd(p) ∈ monomials(S)",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					b.Show(
						"they lie in the supports of f and of g, which hold monomials of S only",
						By(
							b.Assume(),
							fParts[1],
							gParts[1],
							set_basic.SubsetDef,
							set_product.InCrossProjections.At(fSupport, gSupport, p)))
				}))
			inTarget := a.Have(
				"φ takes the coefficients of f and of g, and their products, "+
					"into R', and the value of a monomial of S lies in R'",
				"(∀m:(D → num). φ(f(m)) ∈ R'.carrier) ∧ "+
					"(∀m:(D → num). φ(g(m)) ∈ R'.carrier) ∧ "+
					"(∀m₁ m₂:(D → num). φ(f(m₁) * g(m₂)) ∈ R'.carrier) ∧ "+
					"(∀m:(D → num). m ∈ monomials(S) ⇒ monomial_eval(R', θ, m) ∈ R'.carrier)",
				SplitConj(
					Case(
						"the coefficients of f and of g, and their products, lie in the carrier, which φ takes into R'",
						By(fParts[2], gParts[2], ring_homomorphism.MapIn.Read(hom), comm_ring.MulIn.Read(ring))),
					Case(
						"θ taking the variables of S into R', so does the value of a monomial of S",
						By(target, values, MonomialEvalIn))))
			termsIn := a.Have(
				"the terms of f and of g lie in R', products of two members",
				"(∀m:(D → num). m ∈ fun_support(R.zero, f) ⇒ φ(f(m)) * monomial_eval(R', θ, m) ∈ R'.carrier) ∧ "+
					"(∀m:(D → num). m ∈ fun_support(R.zero, g) ⇒ φ(g(m)) * monomial_eval(R', θ, m) ∈ R'.carrier)",
				By(inTarget, fParts[1], gParts[1], set_basic.SubsetDef, comm_ring.MulIn.Read(target)))
			product := a.Have(
				"at a pair the product of the term of f and the term of g is the pair's term",
				Statement{
					Binders:    "∀p:prod(D → num, D → num).",
					Hypotheses: []string{"p ∈ «cross»"},
					Conclusion: "φ(f(fst(p))) * " +
						"monomial_eval(R', θ, fst(p)) * " +
						"(φ(g(snd(p))) * monomial_eval(R', θ, snd(p))) = " +
						"φ(f(fst(p)) * g(snd(p))) * monomial_eval(R', θ, λx:D. fst(p, x) + snd(p, x))",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					pIn := b.Assume()
					first, second := b.TermAs[Fun[D, Nat]]("fst(p)"), b.TermAs[Fun[D, Nat]]("snd(p)")
					factors := b.Have(
						"the four factors lie in R', both parts of p being monomials of S",
						"φ(f(fst(p))) ∈ R'.carrier ∧ "+
							"φ(g(snd(p))) ∈ R'.carrier ∧ "+
							"monomial_eval(R', θ, fst(p)) ∈ R'.carrier ∧ "+
							"monomial_eval(R', θ, snd(p)) ∈ R'.carrier",
						By(inTarget, pIn, partsIn.At(p)))
					splits := b.Conjuncts(
						b.Have(
							"φ keeps the product, and the value of the sum of the parts is the product of their values",
							"φ(f(fst(p)) * g(snd(p))) = φ(f(fst(p))) * φ(g(snd(p))) ∧ "+
								"monomial_eval(R', θ, λx:D. fst(p, x) + snd(p, x)) = "+
								"monomial_eval(R', θ, fst(p)) * monomial_eval(R', θ, snd(p))",
							By(
								target,
								values,
								pIn,
								partsIn.At(p),
								fParts[2].At(first),
								gParts[2].At(second),
								At(ring_homomorphism.MapMul.Read(hom), f.Apply(first), g.Apply(second)),
								MonomialEvalAdd.At(RPrime, S, θ, first, second))),
						"φ keeps the product of the coefficients",
						"the value of the sum of the parts is the product of their values")
					b.Show(
						"so both sides are the four factors, regrouped",
						splits[0].Rw(),
						splits[1].Rw(),
						ByArith(target, factors))
				}))
			inner := a.Have(
				"a term of f, a member of R', passes into the sum for g",
				Statement{
					Binders:    "∀m₁:(D → num).",
					Hypotheses: []string{"m₁ ∈ fun_support(R.zero, f)"},
					Conclusion: "φ(f(m₁)) * " +
						"monomial_eval(R', θ, m₁) * " +
						"module_sum(R'.add, R'.zero, fun_support(R.zero, g), «gTerms») = " +
						"module_sum(R'.add, " +
						"    R'.zero, " +
						"    fun_support(R.zero, g), " +
						"    λm₂:(D → num). φ(f(m₁)) * monomial_eval(R', θ, m₁) * (φ(g(m₂)) * monomial_eval(R', θ, m₂)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m₁")
					inF := b.Assume()
					b.Show(
						"a member of R' passes into a finite sum of members",
						By(
							inF,
							gParts[0],
							termsIn,
							At(
								module.ModuleSumSmul.Read(regular),
								gSupport,
								b.TermAs[B]("φ(f(m₁)) * monomial_eval(R', θ, m₁)"),
								gTerms)))
				}))
			valuesAsPairs := a.Have(
				"so the product of the two values is the sum over "+
					"the pairs of the terms of the product at the sums",
				"polynomial_algebra_eval(R, R', φ, θ, f) * polynomial_algebra_eval(R, R', φ, θ, g) = "+
					"module_sum(R'.add, R'.zero, «cross», «pairTerms»)",
				Simp(Fwd(PolynomialAlgebraEvalDef)),
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    fun_support(R.zero, f), "+
								"    λm₁:(D → num). "+
								"        φ(f(m₁)) * "+
								"        monomial_eval(R', θ, m₁) * "+
								"        module_sum(R'.add, R'.zero, fun_support(R.zero, g), «gTerms»))"),
						"the value of g, a member of R', passes into the sum for f",
						By(
							fParts[0],
							gParts[0],
							termsIn,
							module.ModuleSumIn.Read(regular).At(gSupport, gTerms),
							At(
								module.ModuleSumSmulRight.Read(regular),
								fSupport,
								fTerms,
								a.TermAs[B]("module_sum(R'.add, R'.zero, fun_support(R.zero, g), «gTerms»)")))),
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    fun_support(R.zero, f), "+
								"    λm₁:(D → num). "+
								"        module_sum(R'.add, "+
								"            R'.zero, "+
								"            fun_support(R.zero, g), "+
								"            λm₂:(D → num). "+
								"                φ(f(m₁)) * monomial_eval(R', θ, m₁) * (φ(g(m₂)) * monomial_eval(R', θ, m₂))))"),
						"and each term of f passes into the sum for g",
						By(inner, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    «cross», "+
								"    λp:prod(D → num, D → num). "+
								"        φ(f(fst(p))) * "+
								"        monomial_eval(R', θ, fst(p)) * "+
								"        (φ(g(snd(p))) * monomial_eval(R', θ, snd(p))))"),
						"the double sum is the sum over the pairs",
						By(
							fParts[0],
							gParts[0],
							termsIn,
							comm_ring.MulIn.Read(target),
							module.ModuleSumCross.Read(regular).At(
								fSupport,
								gSupport,
								a.TermAs[Fun2[Fun[D, Nat], Fun[D, Nat], B]](
									"λm₁:(D → num). λm₂:(D → num). "+
										"    φ(f(m₁)) * monomial_eval(R', θ, m₁) * (φ(g(m₂)) * monomial_eval(R', θ, m₂))")))),
					FinalLeg(
						"pair by pair, the product of the two terms is the term of the product at the sum",
						By(product, module.ModuleSumCongruence)),
				))
			pairTermsIn := a.Have(
				"each term of the product at the sum of a pair lies in R'",
				Statement{
					Binders:    "∀p:prod(D → num, D → num).",
					Hypotheses: []string{"p ∈ «cross»"},
					Conclusion: "φ(f(fst(p)) * g(snd(p))) * monomial_eval(R', θ, λx:D. fst(p, x) + snd(p, x)) ∈ " +
						"R'.carrier",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					pIn := b.Assume()
					sides := b.Have(
						"its parts are a monomial where f is nonzero and one where g is",
						"fst(p) ∈ fun_support(R.zero, f) ∧ snd(p) ∈ fun_support(R.zero, g)",
						By(pIn, set_product.InCrossProjections.At(fSupport, gSupport, p)))
					b.Show(
						"it is the product of a term of f and a term of g, both in R'",
						By(
							pIn,
							sides,
							termsIn,
							product.At(p),
							comm_ring.MulIn.Read(target).AsFact().At(
								b.TermAs[B]("φ(f(fst(p))) * monomial_eval(R', θ, fst(p))"),
								b.TermAs[B]("φ(g(snd(p))) * monomial_eval(R', θ, snd(p))"))))
				}))
			sumsFinite := a.Have(
				"the sums of the two parts of the pairs are finitely many",
				"finite(«sums»)",
				By(crossFinite, finite_set.FiniteImage.At(addParts, cross)))
			sumsMonomials := a.Have(
				"and each is a monomial of S",
				"«sums» ⊆ monomials(S)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("k")
					p, pair := b.UnpackAs[Prod[Fun[D, Nat], Fun[D, Nat]]](
						b.Unfolded(b.Assume(), set_basic.ImageDef), "p")
					b.Show(
						"k is the sum of two monomials of S, the parts of p",
						By(
							pair,
							partsIn.At(p),
							polynomial_algebra.MonomialAddIn.At(
								S, b.TermAs[Fun[D, Nat]]("fst(p)"), b.TermAs[Fun[D, Nat]]("snd(p)"))))
				}))
			support := GroupPremises(
				ring, fParts[2], gParts[2], polynomial_algebra.PolynomialAlgebraMulSupportInSums.At(R, f, g))
			fibres := a.Have(
				"at the sum m of a pair, the term of the product "+
					"is the sum of the terms over the pairs adding to m",
				Statement{
					Binders:    "∀m:(D → num).",
					Hypotheses: []string{"m ∈ «sums»"},
					Conclusion: "φ(polynomial_algebra_mul(R, f, g, m)) * monomial_eval(R', θ, m) = " +
						"module_sum(R'.add, R'.zero, «fibre»(m), «pairTerms»)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					inSums := b.Assume()
					fibre := b.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«fibre»(m)")
					monomial := b.Have(
						"m is a monomial of S, so finitely supported",
						"m ∈ monomials(S) ∧ finite_support(0, m)",
						BySets(inSums, sumsMonomials, polynomial_algebra.MonomialsDef))
					amongPairs := b.Have(
						"the pairs adding to m are among the pairs",
						"«fibre»(m) ⊆ «cross»",
						BySets())
					fibreFinite := b.Have(
						"so they are finitely many",
						"finite(«fibre»(m))",
						By(crossFinite, amongPairs, finite_set.FiniteSubset.At(fibre, cross)))
					coefficient := b.Have(
						"the coefficient of the product at m is the sum of f(m₁) · g(m₂) over the pairs adding to m",
						"polynomial_algebra_mul(R, f, g, m) = "+
							"module_sum(R.add, R.zero, «fibre»(m), λp:prod(D → num, D → num). f(fst(p)) * g(snd(p)))",
						By(
							ring,
							fParts[2],
							gParts[2],
							fParts[0],
							gParts[0],
							function_module.FiniteSupportDef,
							monomial,
							polynomial_algebra.PolynomialAlgebraMulPairs.At(R, f, g, m)))
					mapped := b.Have(
						"φ keeps that finite sum",
						"φ(module_sum(R.add, R.zero, «fibre»(m), λp:prod(D → num, D → num). f(fst(p)) * g(snd(p)))) = "+
							"module_sum(R'.add, R'.zero, «fibre»(m), λp:prod(D → num, D → num). φ(f(fst(p)) * g(snd(p))))",
						By(
							fibreFinite,
							fParts[2],
							gParts[2],
							ring_homomorphism.MapZero.Read(hom),
							ring_homomorphism.MapAdd.Read(hom),
							comm_ring.MulIn.Read(ring),
							module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(ring)).At(
								b.TermAs[Op[B]]("R'.add"),
								b.TermAs[B]("R'.zero"),
								φ,
								fibre,
								b.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], A]](
									"λp:prod(D → num, D → num). f(fst(p)) * g(snd(p))"))))
					b.Show(
						"the value of m passes into the sum, and on the pairs adding to m the sum of the parts is m",
						coefficient.Rw(),
						mapped.Rw(),
						CalcEq(
							Leg(
								b.TermAs[B](
									"module_sum(R'.add, "+
										"    R'.zero, "+
										"    «fibre»(m), "+
										"    λp:prod(D → num, D → num). φ(f(fst(p)) * g(snd(p))) * monomial_eval(R', θ, m))"),
								"the value of m, a member of R', passes into the sum",
								By(
									fibreFinite,
									inTarget,
									monomial,
									At(
										module.ModuleSumSmulRight.Read(regular),
										fibre,
										b.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], B]](
											"λp:prod(D → num, D → num). φ(f(fst(p)) * g(snd(p)))"),
										b.TermAs[B]("monomial_eval(R', θ, m)")))),
							FinalLeg(
								"on the pairs adding to m the sum of the two parts is m",
								By(module.ModuleSumCongruence)),
						))
				}))
			a.Show(
				"the value of the product, summed over the sums of the "+
					"pairs and regrouped by the sum, is the product of the values",
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    «sums», "+
								"    λm:(D → num). φ(polynomial_algebra_mul(R, f, g, m)) * monomial_eval(R', θ, m))"),
						"the product is nonzero only at sums of pairs, finitely many monomials of S",
						By(
							hom,
							values,
							productIn,
							support,
							sumsFinite,
							sumsMonomials,
							PolynomialAlgebraEvalOver.At(
								R, RPrime, φ, θ, S, sums, a.TermAs[Fun[Fun[D, Nat], A]]("polynomial_algebra_mul(R, f, g)")))),
					Leg(
						a.TermAs[B](
							"module_sum(R'.add, "+
								"    R'.zero, "+
								"    «sums», "+
								"    λm:(D → num). module_sum(R'.add, R'.zero, «fibre»(m), «pairTerms»))"),
						"at each sum the term of the product is the sum over the pairs adding to it",
						By(fibres, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[B]("module_sum(R'.add, R'.zero, «cross», «pairTerms»)"),
						"grouped by the sum of their parts, the pairs give the sum over all of them",
						By(crossFinite, pairTermsIn, module.ModuleSumFibres.Read(regular).At(cross, addParts, pairTerms))),
					FinalLeg(
						"which is the product of the two values",
						By(valuesAsPairs)),
				))
		}),
})}

// PolynomialAlgebraEvalHom — evaluation at values in R' of the
// variables of S, with coefficients carried by a ring homomorphism, is
// a ring homomorphism from the polynomials of S into R'. Of its six
// conditions the two rings are the polynomial ring of S
// (polynomial_algebra.PolynomialAlgebraCommRingOn) and the target of φ;
// the values lie in R', sums go to sums and products to products
// (PolynomialAlgebraEvalIn, PolynomialAlgebraEvalAdd,
// PolynomialAlgebraEvalMul); and the one
// polynomial, the constant R.one, evaluates to φ(R.one) = R'.one.
var PolynomialAlgebraEvalHom = polynomialAlgebraEvalHomThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalHom",
	Key:  "prop_83dffe791db95b50",
	Reading: "θ is read on S only, the variables a polynomial of S uses; its values elsewhere " +
		"are arbitrary. Both rings are commutative by the homomorphism's definition, and " +
		"commutativity of R' is load-bearing for the product: the monomials' values multiply in any " +
		"order. Over the zero ring R, R' is the zero ring too, since φ keeps the one and the zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀S:set(D).",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
		},
		Conclusion: "ring_homomorphism(polynomial_algebra_ring(R, S), " +
			"    R', " +
			"    polynomial_algebra_eval(R, R', φ, θ))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			hom, values Fact,
		) {
			ring := ring_homomorphism.Source.Read(hom)
			one := a.Have(
				"the one polynomial is the constant R.one, whose value is φ(R.one) = R'.one",
				"polynomial_algebra_eval(R, R', φ, θ, polynomial_algebra_one(R)) = R'.one",
				Simp(
					Fwd(polynomial_algebra.PolynomialAlgebraOneDef),
					Rev(polynomial_algebra.PolynomialAlgebraConstDef)),
				By(
					ring_homomorphism.MapOne.Read(hom),
					comm_ring.OneIn.Read(ring),
					PolynomialAlgebraEvalConst.At(R, RPrime, φ, θ, a.TermAs[A]("R.one"))))
			a.Show(
				"evaluation keeps the carrier, sums, products and "+
					"one of the commutative ring of the polynomials of S",
				By(
					hom,
					values,
					one,
					ring_homomorphism.Target.Read(hom),
					polynomial_algebra.PolynomialAlgebraCommRingOn.Read(ring),
					PolynomialAlgebraEvalIn,
					PolynomialAlgebraEvalAdd,
					PolynomialAlgebraEvalMul,
					ring_homomorphism.RingHomomorphism.At(
						a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)"),
						RPrime,
						a.TermAs[Fun[Fun[Fun[D, Nat], A], B]]("polynomial_algebra_eval(R, R', φ, θ)"))))
		}),
})}

// TupleEvaluationHom — at a tuple whose first coordinate is a carrier value, evaluation is a ring
// homomorphism from the polynomials in the variable 0 to the ring: the coefficients are read by the
// identity, a ring homomorphism, and the only variable takes a carrier value.
var TupleEvaluationHom = tupleEvaluationHomThm{family.Add(registry.ProofEntry{
	Name: "TupleEvaluationHom",
	Key:  "prop_78408585fcc3b323",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀x:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"x(0) ∈ R.carrier",
		},
		Conclusion: "ring_homomorphism(polynomial_algebra_ring(R, {i:num | i < 1}), " +
			"    R, " +
			"    polynomial_algebra_eval(R, R, λa:A. a, x))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		x *Arrow[Nat, A],
		ring comm_ring.CommRingFact[on.R],
		first Fact,
	) {
		onVariables := a.Have(
			"x is carrier-valued on the variable 0",
			"∀i:num. i ∈ {i:num | i < 1} ⇒ x(i) ∈ R.carrier",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				zero := b.Have(
					"the only variable is 0",
					"i = 0",
					ByArith(below))
				b.Show(
					"x is carrier-valued there",
					By(Normalized, first, zero))
			}))
		a.Show(
			"evaluation along the identity at values in the carrier",
			By(
				onVariables,
				ring_homomorphism.RingHomIdentity.Read(ring),
				PolynomialAlgebraEvalHom.At(
					R, R, a.TermAs[Fun[A, A]]("λa:A. a"), x, a.TermAs[Set[Nat]]("{i:num | i < 1}"))))
	}),
})}

// PolynomialAlgebraEvalMonomial — the coefficient one at a monomial m
// evaluates to the value of m: its support is m alone, where the term is
// φ(one) · monomial_eval(T, θ, m) = monomial_eval(T, θ, m).
var PolynomialAlgebraEvalMonomial = polynomialAlgebraEvalMonomialThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalMonomial",
	Key:  "prop_868f7979555b54a0",
	Reading: "R.one ≠ R.zero puts m in the support; over the zero ring " +
		"the coefficient function is zero and its value T.zero, which is " +
		"the monomial's value only because T is then the zero ring too.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀m:(D → num).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
			"R.one ≠ R.zero",
			"monomial_eval(T, θ, m) ∈ T.carrier",
		},
		Conclusion: "polynomial_algebra_eval(R, T, φ, θ, delta_at(R.zero, R.one, m)) = " +
			"monomial_eval(T, θ, m)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			m *Arrow[D, Nat],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			nonzero, value Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			support := a.Have(
				"the coefficient function is nonzero at m and nowhere else",
				"fun_support(R.zero, λu:(D → num). delta_at(R.zero, R.one, m, u)) ⊆ {m} ∧ "+
					"m ∈ fun_support(R.zero, λu:(D → num). delta_at(R.zero, R.one, m, u))",
				Simp(Fwd(free_module.DeltaAtDef)),
				BySets(nonzero))
			parts := a.Conjuncts(
				support,
				"the support lies in {m}",
				"and holds m")
			term := a.Have(
				"the term at m is φ(one) times the value of m, which is that value",
				"T.mul(φ(delta_at(R.zero, R.one, m, m)), monomial_eval(T, θ, m)) = monomial_eval(T, θ, m)",
				Simp(Fwd(free_module.DeltaAtDef)),
				Simp(Fwd(ring_homomorphism.MapOne.Read(hom))),
				ByArith(target, value))
			a.Show(
				"so the sum over the support is that one term",
				Simp(Fwd(PolynomialAlgebraEvalDef)),
				By(
					parts[0],
					parts[1],
					term,
					value,
					module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(target)).At(
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, λu:(D → num). delta_at(R.zero, R.one, m, u))"),
						m,
						a.TermAs[Fun[Fun[D, Nat], B]](
							"λu:(D → num). T.mul(φ(delta_at(R.zero, R.one, m, u)), monomial_eval(T, θ, u))"))))
		}),
})}

// PolynomialAlgebraEvalConst — a constant evaluates to its image
// under the coefficient map: the constant a sits at the monomial with no
// variables, whose value is the empty product R'.one, so the sum over
// the support is the one term φ(a) · R'.one = φ(a) — and where a is
// R.zero, which takes that monomial off the support, the term is
// φ(R.zero) = R'.zero.
var PolynomialAlgebraEvalConst = polynomialAlgebraEvalConstThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalConst",
	Key:  "prop_e97d2ea4f53ac125",
	Reading: "a ∈ R.carrier is load-bearing: for a ≠ R.zero the value is φ(a) * R'.one, which " +
		"is φ(a) only for φ(a) in R'.carrier, and φ is asked to land there only from R's carrier.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀a:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"a ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, polynomial_algebra_const(R, a)) = φ(a)",
	},
		func(
			arg *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			a *Expr[A],
			hom, aIn Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			image := ring_homomorphism.MapIn.Read(hom).At(arg.MemberOf[on.Any](a, aIn))
			noVariables := arg.Have(
				"the monomial of the constants has no variables",
				"fun_support(0, λx:D. 0) = ∅",
				BySets())
			emptyProduct := arg.Have(
				"so its value is the empty product, one",
				"monomial_eval(R', θ, λx:D. 0) = R'.one",
				Simp(Fwd(MonomialEvalDef)),
				By(noVariables, module.ModuleSumEmpty))
			support := arg.Have(
				"the constant polynomial vanishes off that monomial",
				"fun_support(R.zero, λm:(D → num). delta_at(R.zero, a, λx:D. 0, m)) ⊆ {λx:D. 0}",
				Simp(Fwd(free_module.DeltaAtDef)),
				BySets())
			term := arg.Have(
				"its term there is φ(a) times one, which is φ(a)",
				"R'.mul(φ(delta_at(R.zero, a, λx:D. 0, λx:D. 0)), monomial_eval(R', θ, λx:D. 0)) = φ(a)",
				Simp(Fwd(emptyProduct), Fwd(free_module.DeltaAtDef)),
				ByArith(target, image))
			offSupport := arg.Have(
				"where the monomial is off the support a is R.zero, which φ sends to R'.zero",
				"(λx:D. 0) ∉ fun_support(R.zero, λm:(D → num). delta_at(R.zero, a, λx:D. 0, m)) ⇒ φ(a) = R'.zero",
				Simp(Fwd(free_module.DeltaAtDef)),
				By(Normalized, ring_homomorphism.MapZero.Read(hom)))
			arg.Show(
				"so the sum over the support is that one term",
				Simp(Fwd(PolynomialAlgebraEvalDef), Fwd(polynomial_algebra.PolynomialAlgebraConstDef)),
				By(
					support,
					term,
					offSupport,
					image,
					module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(target)).At(
						arg.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, λm:(D → num). delta_at(R.zero, a, λx:D. 0, m))"),
						arg.TermAs[Fun[D, Nat]]("λx:D. 0"),
						arg.TermAs[Fun[Fun[D, Nat], B]](
							"λm:(D → num). R'.mul(φ(delta_at(R.zero, a, λx:D. 0, m)), monomial_eval(R', θ, m))"))))
		}),
})}

// PolynomialAlgebraEvalVar — the variable x evaluates to its value θ(x).
// Where R.one ≠ R.zero the variable is the coefficient one at the monomial
// of x, which evaluates to the monomial's value; that monomial is nonzero
// at x alone, so its value is the product over {x} of θ(x) ^ 1, which is
// θ(x). Over the zero ring the variable is the zero polynomial, whose
// evaluation is the empty sum R'.zero; φ keeps the one and the zero, so
// R'.one = R'.zero and θ(x) = θ(x) · R'.one is R'.zero as well.
var PolynomialAlgebraEvalVar = polynomialAlgebraEvalVarThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalVar",
	Key:  "prop_f57abc6ce11464f0",
	Reading: "Over the zero ring R the variable is the zero polynomial and " +
		"evaluates to R'.zero; R' is then the zero ring as well (φ keeps the one " +
		"and the zero), so the value θ(x), a member of its carrier, is R'.zero too.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀x:D.",
		Hypotheses: []string{
			"ring_homomorphism(R, R', φ)",
			"θ(x) ∈ R'.carrier",
		},
		Conclusion: "polynomial_algebra_eval(R, R', φ, θ, polynomial_algebra_var(R, x)) = θ(x)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			x *Expr[D],
			hom, xIn Fact,
		) {
			target := ring_homomorphism.Target.Read(hom)
			a.Cases(a.TermAs[Bool]("R.one = R.zero"))
			a.When(
				"over the zero ring",
				func(b *Argument, trivial Fact) {
					collapse := b.Have(
						"φ carries R.one to R'.one and R.zero to R'.zero, so R' is the zero ring too",
						"R'.one = R'.zero",
						By(trivial, ring_homomorphism.MapOne.Read(hom), ring_homomorphism.MapZero.Read(hom)))
					vanishes := b.Have(
						"so θ(x) = θ(x) · R'.one = θ(x) · R'.zero = R'.zero",
						"θ(x) = R'.zero",
						ByArith(target, Scaled(θ.Apply(x), collapse), xIn))
					empty := b.Have(
						"the variable is R.one = R.zero at the monomial of "+
							"x and R.zero elsewhere, so it is nonzero nowhere",
						"fun_support(R.zero, λm:(D → num). polynomial_algebra_var(R, x, m)) = ∅",
						Simp(Fwd(polynomial_algebra.PolynomialAlgebraVarDef), Fwd(free_module.DeltaAtDef)),
						BySets(trivial))
					b.Show(
						"so its evaluation is the empty sum R'.zero, which is θ(x)",
						Simp(Fwd(PolynomialAlgebraEvalDef)),
						By(vanishes, empty, module.ModuleSumEmpty))
				})
			a.Otherwise(
				"over a nonzero ring",
				func(b *Argument, nonzero Fact) {
					products := comm_ring.MulMonoidOn.Read(target)
					xMonomial := polynomial_algebra.MonomialVarValues.At(x)
					support := b.Have(
						"the monomial of x is nonzero at x alone",
						"fun_support(0, λy:D. monomial_var(x, y)) ⊆ {x}",
						BySets(xMonomial))
					value := b.Have(
						"so its value is the product over {x} of θ(x) ^ 1, which is θ(x)",
						"monomial_eval(R', θ, monomial_var(x)) = θ(x)",
						Simp(Fwd(MonomialEvalDef)),
						By(
							xIn,
							support,
							xMonomial,
							nat_arith.OneNotZero,
							comm_monoid.PowOneOn.Read(products),
							module.ModuleSumSingleMonoid.Read(products).At(
								b.TermAs[Set[D]]("fun_support(0, λy:D. monomial_var(x, y))"),
								x,
								b.TermAs[Fun[D, B]]("λy:D. monoid_pow(R'.mul, R'.one, θ(y), monomial_var(x, y))"))))
					b.Show(
						"the variable is the coefficient one at the monomial of x, which evaluates to the monomial's value",
						Simp(Fwd(polynomial_algebra.PolynomialAlgebraVarDef)),
						By(
							nonzero,
							value,
							xIn,
							hom,
							PolynomialAlgebraEvalMonomial.At(R, RPrime, φ, θ, b.TermAs[Fun[D, Nat]]("monomial_var(x)"))))
				})
		}),
})}

// PolynomialAlgebraEvalRestrictTarget — evaluation into a ring restricted to
// a subset U of its carrier is evaluation into the ring: the value reads the
// sum, zero, product and one of the target, which restricting keeps.
var PolynomialAlgebraEvalRestrictTarget = polynomialAlgebraEvalRestrictTargetThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalRestrictTarget",
	Key:  "prop_6205df90b3656d41",
	Build: family.Theorem("∀R:ring_ops(A). "+
		"∀T:ring_ops(B). "+
		"∀U:set(B). "+
		"∀φ:(A → B). "+
		"∀θ:(D → B). "+
		"∀f:((D → num) → A). "+
		"    polynomial_algebra_eval(R, restrict_ring(T, U), φ, θ, f) = "+
		"    polynomial_algebra_eval(R, T, φ, θ, f)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			U *Expr[Set[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			f *Arrow[Fun[D, Nat], A],
		) {
			a.Show(
				"both values are the one sum of the same products",
				Simp(Fwd(PolynomialAlgebraEvalDef), Fwd(MonomialEvalDef)),
				Basic())
		}),
})}

// PolynomialAlgebraEvalRestrictCoefficients — evaluation with the
// coefficients read in R restricted to a subset k of its carrier is
// evaluation with them read in R: the value reads only R's zero, to find
// the support, which restricting keeps.
var PolynomialAlgebraEvalRestrictCoefficients = polynomialAlgebraEvalRestrictCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalRestrictCoefficients",
	Key:  "prop_f2d9f0aeebfde113",
	Build: family.Theorem("∀R:ring_ops(A). "+
		"∀k:set(A). "+
		"∀T:ring_ops(B). "+
		"∀φ:(A → B). "+
		"∀θ:(D → B). "+
		"∀f:((D → num) → A). "+
		"    polynomial_algebra_eval(restrict_ring(R, k), T, φ, θ, f) = "+
		"    polynomial_algebra_eval(R, T, φ, θ, f)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			T *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			f *Arrow[Fun[D, Nat], A],
		) {
			a.Show(
				"both values are the sum over the one support",
				Simp(Fwd(PolynomialAlgebraEvalDef)),
				Basic())
		}),
})}

// PolynomialAlgebraEvalInSubring — a polynomial over R, evaluated in Q
// along a ring map φ that lands in a subring T at a point with its
// coordinates in T, takes its value in T: evaluation into T, read as a
// ring of its own, is a ring homomorphism, and it reads the operations of
// Q alone, which restricting to T keeps.
var PolynomialAlgebraEvalInSubring = polynomialAlgebraEvalInSubringThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraEvalInSubring",
	Key:  "prop_c103d76dd778bfc3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀S:set(D). " +
			"∀T:set(B). " +
			"∀f:((D → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, Q, φ)",
			"subring(Q, T)",
			"∀a:A. a ∈ R.carrier ⇒ φ(a) ∈ T",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ T",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_eval(R, Q, φ, θ, f) ∈ T",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			Q *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			S *Expr[Set[D]],
			T *Expr[Set[B]],
			f *Arrow[Fun[D, Nat], A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"φ is a ring map from R to Q",
				"T is a subring of Q",
				"φ lands in T",
				"θ lands in T on S",
				"f is a polynomial of S")
			homQ, subringT, φInT, θInT, fIn := parts[0], parts[1], parts[2], parts[3], parts[4]
			intoT := a.Have(
				"φ is a ring map into T",
				"ring_homomorphism(R, restrict_ring(Q, T), φ)",
				By(homQ, subringT, φInT, ring_homomorphism.RingHomCorestrict.At(R, Q, φ, T)))
			ringT := a.TermAs[RingOps[B]]("restrict_ring(Q, T)")
			evaluationT := a.Have(
				"evaluation into T is a ring homomorphism out of the polynomials of S",
				"ring_homomorphism(polynomial_algebra_ring(R, S), "+
					"    restrict_ring(Q, T), "+
					"    polynomial_algebra_eval(R, restrict_ring(Q, T), φ, θ))",
				By(θInT, intoT, PolynomialAlgebraEvalHom.At(R, ringT, φ, θ, S)))
			a.Show(
				"so the value of f lies in T, evaluation into T being evaluation into Q",
				By(
					fIn,
					ring_homomorphism.MapIn.Read(evaluationT).AsFact().At(f),
					PolynomialAlgebraEvalRestrictTarget.At(R, Q, T, φ, θ, f)))
		}),
})}
