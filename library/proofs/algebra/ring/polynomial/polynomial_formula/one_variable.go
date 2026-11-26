// one_variable.go — an integer polynomial read as a polynomial in one
// variable v whose coefficients are integer polynomials in the others: the
// coefficient of v^k, a monomial split into a power of v and its lowering,
// evaluation with v sent to x as the univariate evaluation of the
// specialized coefficients, and the coefficients as a univariate
// polynomial over the polynomials on the other variables.

package polynomial_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// integerPolynomialCoefficientDef — the coefficient of v^k in p, an integer polynomial in the other
// variables.
var integerPolynomialCoefficientDef = integerPolynomialCoefficientDefThm{family.Define(registry.DefEntry{
	Name:  "integerPolynomialCoefficientDef",
	Const: "integer_polynomial_coefficient",
	Type:  "num → ((num → num) → int) → num → (num → num) → int",
	Key:   "prop_965d55634445976b",
	Equations: []string{
		"∀v:num. ∀p:((num → num) → int). ∀k:num. ∀m:(num → num). " +
			"    integer_polynomial_coefficient(v, p, k, m) = " +
			"    COND(m(v) = 0, p(λi:num. COND(i = v, k, m(i))), 0)",
	},
	Reading: "Read at v and p alone, integer_polynomial_coefficient(v, p) " +
		"is p as a univariate polynomial in v whose coefficients are integer " +
		"polynomials; every coefficient vanishes at monomials that mention v.",
})}

// MonomialLowered — zeroing the exponent of one variable v in a monomial of
// S leaves a monomial of the other variables of S: its support is the old one
// with v deleted.
var MonomialLowered = monomialLoweredThm{family.Add(registry.ProofEntry{
	Name: "MonomialLowered",
	Key:  "prop_3dcbc8f3156e634e",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(D). ∀v:D. ∀m:(D → num).",
		Hypotheses: []string{
			"m ∈ monomials(S)",
		},
		Conclusion: "(λi:D. COND(i = v, 0, m(i))) ∈ monomials(S ∖ {v})",
	},
		func(a *Argument, S *Expr[Set[D]], v *Expr[D], m *Arrow[D, Nat], monomial Fact) {
			lowered := a.Have(
				"zeroing the exponent of v deletes v from the support",
				"fun_support(0, λi:D. COND(i = v, 0, m(i))) = delete(fun_support(0, m), v)",
				BySets())
			bounded := a.Simplified(monomial, Fwd(polynomial_algebra.MonomialsMember))
			a.Show(
				"the support left is finite and lies in S without v",
				Simp(Fwd(polynomial_algebra.MonomialsMember), Fwd(lowered)),
				BySets(bounded, finite_set.FiniteDelete))
		}),
})}

// MonomialAtUpdate — a monomial of S evaluated with v sent to x is x to the
// exponent of v times the monomial with that exponent zeroed, evaluated at ρ:
// the product over the support extends to v by factors one, the factor at v
// is x ^ m(v), and away from v the updated environment is ρ.
var MonomialAtUpdate = monomialAtUpdateThm{family.Add(registry.ProofEntry{
	Name: "MonomialAtUpdate",
	Key:  "prop_5c83c18706920839",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀S:set(num). ∀v:num. ∀x:A. ∀m:(num → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"m ∈ monomials(S)",
			"fo_env_ok(R.carrier, S ∖ {v}, ρ)",
			"x ∈ R.carrier",
		},
		Conclusion: "monomial_eval(R, fo_update(ρ, v, x), m) = " +
			"monoid_pow(R.mul, R.one, x, m(v)) * monomial_eval(R, ρ, «lower»(m))",
		Abbrev: Abbrev{
			{Name: "others", Text: "delete(fun_support(0, m), v)"},
			{Name: "around", Text: "insert(v, «others»)"},
			{Name: "factor", Text: "λi:num. monoid_pow(R.mul, R.one, fo_update(ρ, v, x, i), m(i))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			ρ *Arrow[Nat, A],
			S *Expr[Set[Nat]],
			v *Expr[Nat],
			x *Expr[A],
			m *Arrow[Nat, Nat],
			monomial, environment, xIn Fact,
		) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			bounded := a.Conjuncts(
				a.Simplified(monomial, Fwd(polynomial_algebra.MonomialsMember)),
				"m has finitely many nonzero exponents",
				"all of them at variables of S")
			values := a.Unfolded(environment, first_order.EnvOKDef)
			lowered := a.Have(
				"zeroing the exponent of v deletes v from the support",
				"fun_support(0, «lower»(m)) = «others»",
				BySets())
			factors := a.Have(
				"at v and at the other variables of m each factor lies in R",
				"∀i:num. i ∈ «around» ⇒ «factor»(i) ∈ R.carrier",
				BySets(bounded[1], values, xIn, comm_monoid.PowIn.Read(monoid), first_order.EnvUpdateDef))
			cover := a.Have(
				"v and the other variables of m are finitely many and hold all of m's",
				"finite(«around») ∧ fun_support(0, m) ⊆ «around»",
				BySets(bounded[0], finite_set.FiniteInsert, finite_set.FiniteDelete))
			unit := a.Have(
				"off the support of m the exponent is zero and the factor is one",
				"∀i:num. i ∈ «around» ∧ i ∉ fun_support(0, m) ⇒ «factor»(i) = R.one",
				By(comm_monoid.MonoidPowDef))
			rest := a.Have(
				"the other variables of m are finitely many, and v is not among them",
				"finite(«others») ∧ v ∉ «others»",
				BySets(bounded[0], finite_set.FiniteDelete))
			away := a.Have(
				"away from v the updated environment is ρ and the exponent is unchanged",
				"∀i:num. i ∈ «others» ⇒ «factor»(i) = monoid_pow(R.mul, R.one, ρ(i), «lower»(m, i))",
				Simp(Fwd(first_order.EnvUpdateDef)),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					inRest := b.Assume()
					b.Show(
						"i is not v",
						By(b.Simplified(inRest, Fwd(set_basic.InDelete))))
				}))
			restAgree := a.Have(
				"so the product over the other variables is the same at ρ",
				"module_sum(R.mul, R.one, «others», «factor») = "+
					"module_sum(R.mul, R.one, «others», λi:num. monoid_pow(R.mul, R.one, ρ(i), «lower»(m, i)))",
				By(away, module.ModuleSumCongruence))
			a.Show(
				"so the product splits into the power of x at v and the product at ρ over the rest",
				Simp(Fwd(polynomial_algebra_evaluation.MonomialEvalDef), Fwd(lowered)),
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.mul, R.one, «around», «factor»)"),
						"the product over the support extends to v by factors one",
						By(factors, cover, unit, module.ModuleSumSupportMonoid.Read(monoid))),
					Leg(
						a.TermAs[A]("monoid_pow(R.mul, R.one, x, m(v)) * module_sum(R.mul, R.one, «others», «factor»)"),
						"the factor at v is x to the exponent of v",
						BySets(
							factors,
							rest,
							first_order.EnvUpdateDef,
							module.ModuleSumInsertMonoid.Read(monoid).At(
								a.TermAs[Set[Nat]]("«others»"),
								v,
								a.TermAs[Fun[Nat, A]]("«factor»")))),
					FinalLeg(
						"and away from v the factors are those at ρ",
						By(restAgree)),
				))
		}),
})}

// CoefficientAtLowered — the coefficient of v to the power m(v) at m with its
// exponent of v zeroed is p's coefficient at m: the lowered monomial has
// exponent zero at v, and setting v back to m(v) recovers m.
var CoefficientAtLowered = coefficientAtLoweredThm{family.Add(registry.ProofEntry{
	Name: "CoefficientAtLowered",
	Key:  "prop_f25d044c110a0fcd",
	Build: family.Theorem("∀v:num. ∀p:((num → num) → int). ∀m:(num → num). "+
		"    integer_polynomial_coefficient(v, p, m(v), «lower»(m)) = p(m)",
		func(a *Argument, v *Expr[Nat], p *Arrow[Fun[Nat, Nat], Int], m *Arrow[Nat, Nat]) {
			raised := a.Have(
				"setting v back to its exponent in m recovers m",
				"(λi:num. COND(i = v, m(v), «lower»(m, i))) = m",
				BySets())
			a.Show(
				"the lowered monomial has exponent zero at v, so its "+
					"coefficient is p's at the raised monomial, which is m",
				Simp(Fwd(integerPolynomialCoefficientDef), Fwd(raised)),
				Basic())
		}),
})}

// CoefficientSupport — the monomials where the k-th coefficient of p in v is
// nonzero are p's monomials of exponent k at v with that exponent zeroed: a
// nonzero k-th coefficient at m has m(v) = 0 and p nonzero at m with v set to
// k, which lowers back to m, and conversely the coefficient at a lowered
// monomial is p's at the monomial.
var CoefficientSupport = coefficientSupportThm{family.Add(registry.ProofEntry{
	Name: "CoefficientSupport",
	Key:  "prop_8ae0c0cd30c52ea2",
	Build: family.Theorem(Statement{
		Binders: "∀v:num. ∀p:((num → num) → int). ∀k:num.",
		Conclusion: "fun_support(int_of_num(0), integer_polynomial_coefficient(v, p, k)) = " +
			"image(«lower», «fibre»(k))",
	},
		func(a *Argument, v *Expr[Nat], p *Arrow[Fun[Nat, Nat], Int], k *Expr[Nat]) {
			raisedIn := a.Have(
				"where the k-th coefficient is nonzero, setting v to k "+
					"gives a monomial of p in the fibre, which lowers back",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(int_of_num(0), integer_polynomial_coefficient(v, p, k))"},
					Conclusion: "(λi:num. COND(i = v, k, m(i))) ∈ «fibre»(k) ∧ " +
						"m = «lower»(λi:num. COND(i = v, k, m(i)))",
				},
				BySets(integerPolynomialCoefficientDef))
			loweredIn := a.Have(
				"a monomial of the fibre lowers to one where the k-th coefficient is nonzero",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ «fibre»(k)"},
					Conclusion: "«lower»(m) ∈ fun_support(int_of_num(0), integer_polynomial_coefficient(v, p, k))",
				},
				BySets(CoefficientAtLowered))
			intoImage := a.Have(
				"so the support lies in the image of the fibre",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(int_of_num(0), integer_polynomial_coefficient(v, p, k))"},
					Conclusion: "m ∈ image(«lower», «fibre»(k))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[Nat, Nat]]("m")
					inSupport := b.Assume()
					b.Show(
						"m is the lowering of itself with v set to k",
						Simp(Fwd(set_basic.InImage)),
						Witness(b.TermAs[Fun[Nat, Nat]]("λi:num. COND(i = v, k, m(i))")),
						By(inSupport, raisedIn.At(m)))
				}))
			fromImage := a.Have(
				"and the image lies in the support",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ image(«lower», «fibre»(k))"},
					Conclusion: "m ∈ fun_support(int_of_num(0), integer_polynomial_coefficient(v, p, k))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Nat]]("m")
					inImage := b.Assume()
					n, lowering := b.UnpackAs[Fun[Nat, Nat]](b.Simplified(inImage, Fwd(set_basic.InImage)), "n")
					b.Show(
						"m is the lowering of a monomial n of the fibre",
						By(lowering, loweredIn.At(n)))
				}))
			a.Show(
				"the two inclusions",
				By(intoImage, fromImage, set_order.SubsetAntisym, set_basic.SubsetDef))
		}),
})}

// CoefficientEvaluation — evaluating p with v sent to x is evaluating its
// specialized coefficients, as a univariate polynomial, at x. Group the
// monomials of p by their exponent k of v: each splits as x ^ k times its
// lowering, the monomial with that exponent zeroed, at ρ, and lowering is one
// to one on a fibre onto the support of the k-th coefficient, so the fibre of
// exponent k sums to the k-th specialized coefficient times x ^ k; an exponent
// no monomial of p has gives an empty fibre and a zero coefficient.
var CoefficientEvaluation = coefficientEvaluationThm{family.Add(registry.ProofEntry{
	Name: "CoefficientEvaluation",
	Key:  "prop_5e1e83a103a817dd",
	Reading: "The coefficients avoid v, so ρ(v) is never read on the right. This " +
		"is SpecializeOneVariable with its univariate polynomial written down. " +
		"comm_ring_on is load-bearing: commutativity pulls x^k out of each monomial. " +
		"A specialized coefficient may vanish where the integer coefficient does " +
		"not, which is harmless because the evaluation sums over a support.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int). ∀v:num. ∀x:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial(p)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p) ∖ {v}, ρ)",
			"x ∈ R.carrier",
		},
		Conclusion: "integer_polynomial_eval(R, fo_update(ρ, v, x), p) = " +
			"polynomial_eval(R.add, " +
			"    R.zero, " +
			"    R.mul, " +
			"    R.one, " +
			"    «specialized»(R, ρ, integer_polynomial_coefficient(v, p)), " +
			"    x)",
		Abbrev: Abbrev{
			{Name: "term", Text: "λm:(num → num). " +
				"    integer_map(R, p(m)) * monomial_eval(R, fo_update(ρ, v, x), m)"},
			{Name: "rest", Text: "λm:(num → num). integer_map(R, p(m)) * monomial_eval(R, ρ, «lower»(m))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			ρ *Arrow[Nat, A],
			p *Arrow[Fun[Nat, Nat], Int],
			polynomial Fact,
			v *Expr[Nat],
			environment Fact,
			x *Expr[A],
			xIn Fact,
		) {
			additive := comm_ring.AddMonoidOn.Read(ring)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			regular := module.RegularModuleOn.Read(ring)
			support := a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(int_of_num(0), p)")
			own := a.Conjuncts(
				GroupPremises(polynomial, PolynomialSupportFinite.At(p)),
				"p is nonzero at finitely many monomials",
				"each of them a monomial of the variables of p")
			ownMonomials := a.Simplified(own[1], Fwd(set_basic.SubsetDef))
			values := a.Unfolded(environment, first_order.EnvOKDef)
			split := a.Have(
				"a monomial of p evaluated with v sent to x is x to its exponent of v times its lowering at ρ",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(int_of_num(0), p)"},
					Conclusion: "monomial_eval(R, fo_update(ρ, v, x), m) = " +
						"monoid_pow(R.mul, R.one, x, m(v)) * monomial_eval(R, ρ, «lower»(m))",
				},
				By(ownMonomials, ring, environment, xIn, MonomialAtUpdate))
			loweredIn := a.Have(
				"and the lowering at ρ lies in R",
				"∀m:(num → num). m ∈ fun_support(int_of_num(0), p) ⇒ monomial_eval(R, ρ, «lower»(m)) ∈ R.carrier",
				By(ownMonomials, ring, values, MonomialLowered, polynomial_algebra_evaluation.MonomialEvalIn))
			terms := a.Have(
				"so each term of the value at the updated environment lies in R",
				"∀m:(num → num). m ∈ fun_support(int_of_num(0), p) ⇒ «term»(m) ∈ R.carrier",
				By(
					split,
					loweredIn,
					xIn,
					comm_ring.MulIn.Read(ring),
					characteristic_zero.IntegerMapInCarrier.Read(ring),
					comm_monoid.PowIn.Read(monoid)))
			raised := a.Have(
				"setting v back to its exponent recovers a monomial from its lowering",
				"∀m:(num → num). (λi:num. COND(i = v, m(v), «lower»(m, i))) = m",
				BySets())
			injective := a.Have(
				"lowering is one to one on each fibre, whose exponent of v is fixed",
				"∀k:num. injective_on(«fibre»(k), «lower»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					m1 := b.FixAs[Fun[Nat, Nat]]("m₁")
					m2 := b.FixAs[Fun[Nat, Nat]]("m₂")
					same := b.Assume()
					b.Show(
						"each is its lowering with v set back to k",
						By(same, raised.At(m1), raised.At(m2)))
				}))
			fibresFinite := a.Have(
				"each fibre is finite, a part of the support of p",
				"∀k:num. finite(«fibre»(k))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Show(
						"a part of a finite set",
						By(
							own[0],
							set_basic.SubsetDef,
							finite_set.FiniteSubset.At(b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"), support)))
				}))
			coefficientTerms := a.Have(
				"on a fibre the terms of the coefficient at the lowered monomials lie in R",
				Statement{
					Binders:    "∀k:num. ∀m:(num → num).",
					Hypotheses: []string{"m ∈ «fibre»(k)"},
					Conclusion: "integer_map(R, integer_polynomial_coefficient(v, p, k, «lower»(m))) * " +
						"monomial_eval(R, ρ, «lower»(m)) ∈ " +
						"R.carrier",
				},
				By(loweredIn, comm_ring.MulIn.Read(ring), characteristic_zero.IntegerMapInCarrier.Read(ring)))
			value := a.Have(
				"the k-th specialized coefficient sums the terms "+
					"at ρ of the lowerings over the fibre of exponent k",
				"∀k:num. "+
					"    «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) = "+
					"    module_sum(R.add, R.zero, «fibre»(k), «rest»)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.Show(
						"the support of the k-th coefficient is the lowered fibre",
						Simp(
							Fwd(IntegerPolynomialEvalDef),
							Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef),
							Fwd(CoefficientSupport)),
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    «fibre»(k), "+
										"    λm:(num → num). "+
										"        integer_map(R, integer_polynomial_coefficient(v, p, k, «lower»(m))) * "+
										"        monomial_eval(R, ρ, «lower»(m)))"),
								"lowering is one to one on the fibre",
								By(
									fibresFinite.At(k),
									injective.At(k),
									coefficientTerms,
									module.ModuleSumImageMonoid.Read(additive).At(
										b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"),
										b.TermAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]]("«lower»"),
										b.TermAs[Fun[Fun[Nat, Nat], A]](
											"λm:(num → num). "+
												"    integer_map(R, integer_polynomial_coefficient(v, p, k, m)) * monomial_eval(R, ρ, m)")))),
							FinalLeg(
								"on the fibre the coefficient at a lowering is p's at the monomial",
								By(CoefficientAtLowered, module.ModuleSumCongruence)),
						))
				}))
			fibreValue := a.Have(
				"the fibre of exponent k sums to the k-th specialized coefficient times x ^ k",
				"∀k:num. "+
					"    module_sum(R.add, R.zero, «fibre»(k), «term») = "+
					"    «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) * monoid_pow(R.mul, R.one, x, k)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					power := comm_monoid.PowIn.Read(monoid).At(b.MemberOf[on.R](x, xIn), k)
					termwise := b.Have(
						"on the fibre each term is the term at ρ of the lowering times x ^ k",
						"∀m:(num → num). m ∈ «fibre»(k) ⇒ «term»(m) = «rest»(m) * monoid_pow(R.mul, R.one, x, k)",
						Derive(func(c *Argument) {
							m := c.FixAs[Fun[Nat, Nat]]("m")
							parts := c.Conjuncts(
								c.Assume(),
								"m is a monomial of p",
								"of exponent k at v")
							atK := c.Have(
								"so its value with v sent to x is x ^ k times its lowering at ρ",
								"monomial_eval(R, fo_update(ρ, v, x), m) = "+
									"monoid_pow(R.mul, R.one, x, k) * monomial_eval(R, ρ, «lower»(m))",
								By(split.At(m), parts[0], parts[1]))
							factors := c.Have(
								"the three factors lie in R",
								"integer_map(R, p(m)) ∈ R.carrier ∧ "+
									"monomial_eval(R, ρ, «lower»(m)) ∈ R.carrier ∧ "+
									"monoid_pow(R.mul, R.one, x, k) ∈ R.carrier",
								By(loweredIn.At(m), parts[0], power, characteristic_zero.IntegerMapInCarrier.Read(ring)))
							c.Show(
								"and the factors commute in R",
								atK.Rw(),
								ByArith(ring, factors))
						}))
					b.Show(
						"so x ^ k comes out of the sum, which is the k-th specialized coefficient",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    «fibre»(k), "+
										"    λm:(num → num). «rest»(m) * monoid_pow(R.mul, R.one, x, k))"),
								"term by term",
								By(termwise, module.ModuleSumCongruence)),
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, «fibre»(k), «rest») * monoid_pow(R.mul, R.one, x, k)"),
								"x ^ k distributes over the sum",
								By(
									fibresFinite.At(k),
									loweredIn,
									comm_ring.MulIn.Read(ring),
									characteristic_zero.IntegerMapInCarrier.Read(ring),
									module.ModuleSumSmulRight.Read(regular).At(
										b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"),
										b.TermAs[Fun[Fun[Nat, Nat], A]]("«rest»"),
										power))),
							FinalLeg(
								"which is the k-th specialized coefficient times x ^ k",
								By(value.At(k))),
						))
				}))
			exponentsFinite := a.Have(
				"finitely many exponents of v occur in p",
				"finite(«exponents»)",
				By(own[0], finite_set.FiniteImage))
			vanish := a.Have(
				"an exponent no monomial of p has gives an empty fibre and a zero specialized coefficient",
				"∀k:num. k ∉ «exponents» ⇒ «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) = R.zero",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					absent := b.Assume()
					b.Show(
						"a sum over an empty fibre",
						By(
							absent,
							value.At(k),
							fibresFinite.At(k),
							set_basic.InImage,
							module.ModuleSumIdentityMonoid.Read(additive).At(
								b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"),
								b.TermAs[Fun[Fun[Nat, Nat], A]]("«rest»"))))
				}))
			covered := a.Have(
				"so the exponents of v in p hold every k where the specialized coefficient is nonzero",
				"fun_support(R.zero, «specialized»(R, ρ, integer_polynomial_coefficient(v, p))) ⊆ «exponents»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					nonzero := b.Assume()
					b.Show(
						"else it would vanish",
						By(nonzero, vanish.At(k), functions.InFunSupport))
				}))
			summands := a.Have(
				"each summand of the univariate value lies in R, a finite sum of terms in R",
				"∀k:num. "+
					"    «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) * "+
					"    monoid_pow(R.mul, R.one, x, k) ∈ "+
					"    R.carrier",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.Show(
						"the sum over the fibre",
						By(
							fibreValue.At(k),
							fibresFinite.At(k),
							terms,
							module.ModuleSumInMonoid.Read(additive).At(
								b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"),
								b.TermAs[Fun[Fun[Nat, Nat], A]]("«term»"))))
				}))
			zeros := a.Have(
				"where the specialized coefficient vanishes, so does its summand",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ∉ fun_support(R.zero, «specialized»(R, ρ, integer_polynomial_coefficient(v, p)))",
					},
					Conclusion: "«specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) * " +
						"monoid_pow(R.mul, R.one, x, k) = " +
						"R.zero",
				},
				By(functions.InFunSupport, comm_ring.MulLeftZeroOn.Read(ring), comm_monoid.PowIn.Read(monoid), xIn))
			a.Show(
				"grouping the monomials of p by their exponent of v gives the univariate evaluation",
				Simp(Fwd(polynomial_evaluation.PolynomialEvalDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, fun_support(int_of_num(0), p), «term»)"),
						"the value at the updated environment sums the terms of p",
						Simp(Fwd(IntegerPolynomialEvalDef), Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef)),
						Basic()),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, «exponents», λk:num. module_sum(R.add, R.zero, «fibre»(k), «term»))"),
						"group the monomials of p by their exponent of v",
						By(
							own[0],
							terms,
							module.ModuleSumFibres.Read(regular).At(
								support,
								a.TermAs[Fun[Fun[Nat, Nat], Nat]]("λm:(num → num). m(v)"),
								a.TermAs[Fun[Fun[Nat, Nat], A]]("«term»")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «exponents», "+
								"    λk:num. "+
								"        «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) * "+
								"        monoid_pow(R.mul, R.one, x, k))"),
						"the fibre of exponent k is the k-th specialized coefficient times x ^ k",
						By(fibreValue, module.ModuleSumCongruence)),
					FinalLeg(
						"and the exponents of v hold the support of the specialized coefficients",
						By(
							exponentsFinite,
							covered,
							summands,
							zeros,
							module.ModuleSumSupportMonoid.Read(additive).At(
								a.TermAs[Set[Nat]]("«exponents»"),
								a.TermAs[Set[Nat]](
									"fun_support(R.zero, «specialized»(R, ρ, integer_polynomial_coefficient(v, p)))"),
								a.TermAs[Fun[Nat, A]](
									"λk:num. "+
										"    «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) * "+
										"    monoid_pow(R.mul, R.one, x, k)")))),
				))
		}),
})}

// SpecializeOneVariable — fixing all but one variable gives a univariate
// carrier polynomial: the coefficients of p in v, each evaluated at ρ. By
// CoefficientsOverParameters each coefficient is a polynomial on the
// variables of p other than v, where ρ takes values in R, so its value lies in
// R, and past some n the coefficients are the zero polynomial, whose value is
// the empty sum; and evaluating p with v sent to x is evaluating those values
// at x (CoefficientEvaluation).
var SpecializeOneVariable = specializeOneVariableThm{family.Add(registry.ProofEntry{
	Name: "SpecializeOneVariable",
	Key:  "prop_9624f47e404ca90e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int). ∀v:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial(p)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p) ∖ {v}, ρ)",
		},
		Conclusion: "∃q:(num → A). " +
			"    polynomial_over(R.zero, R.carrier, q) ∧ " +
			"    (∀x:A. " +
			"        x ∈ R.carrier ⇒ " +
			"        integer_polynomial_eval(R, fo_update(ρ, v, x), p) = " +
			"        polynomial_eval(R.add, R.zero, R.mul, R.one, q, x))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			ρ *Arrow[Nat, A],
			p *Arrow[Fun[Nat, Nat], Int],
			pPolynomial Fact,
			v *Expr[Nat],
			environment Fact,
		) {
			over := a.Conjuncts(
				a.Unfolded(
					GroupPremises(pPolynomial, CoefficientsOverParameters.At(v, p)), polynomial.PolynomialOverDef),
				"past some n the coefficients of p in v are the zero polynomial",
				"and each is a polynomial on the variables of p other than v")
			n, past := a.UnpackAs[Nat](over[0], "n")
			values := a.Have(
				"each specialized coefficient lies in R, ρ taking values in R at the variables of its coefficient",
				"∀k:num. «specialized»(R, ρ, integer_polynomial_coefficient(v, p), k) ∈ R.carrier",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					coefficient := b.TermAs[IntegerPolynomial]("integer_polynomial_coefficient(v, p, k)")
					b.Show(
						"its variables are variables of p other than v, where ρ takes values in R",
						By(
							ring,
							over[1].At(k),
							PolynomialOnVariables.At(b.TermAs[Set[Nat]]("integer_polynomial_vars(p) ∖ {v}"), coefficient),
							environment,
							first_order.EnvOKSubset.At(
								b.TermAs[Set[A]]("R.carrier"),
								b.TermAs[Set[Nat]]("integer_polynomial_vars(integer_polynomial_coefficient(v, p, k))"),
								b.TermAs[Set[Nat]]("integer_polynomial_vars(p) ∖ {v}"),
								ρ),
							EvaluationInCarrier.At(R, ρ, coefficient)))
				}))
			zeros := a.Have(
				"past n the specialized coefficients are zero",
				"vec⟨n⟩(R.zero, «specialized»(R, ρ, integer_polynomial_coefficient(v, p)))",
				Simp(Fwd(vec_space.VecDef)),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					beyond := b.Assume()
					b.Show(
						"the k-th coefficient is the zero polynomial, whose value is zero",
						By(beyond, past, vec_space.VecDef, IntegerPolynomialRingOperations, ZeroPolynomialValue.At(R, ρ)))
				}))
			univariate := a.Have(
				"so the specialized coefficients are a polynomial over R",
				"polynomial_over(R.zero, R.carrier, «specialized»(R, ρ, integer_polynomial_coefficient(v, p)))",
				Unfold(polynomial.PolynomialOverDef),
				SplitConj(
					Case(
						"zero from n on",
						Witness(n),
						By(zeros)),
					Case(
						"with every coefficient in R",
						By(values))))
			a.Show(
				"and evaluating p with v sent to x is evaluating it at x",
				Witness(a.TermAs[Fun[Nat, A]]("«specialized»(R, ρ, integer_polynomial_coefficient(v, p))")),
				By(univariate, ring, pPolynomial, environment, CoefficientEvaluation))
		}),
})}

// CoefficientsOverParameters — an integer polynomial is a univariate
// polynomial in v over the polynomials on its other variables: finitely
// many exponents of v occur in p, so they are at most some n, and
// past n every coefficient vanishes, a nonzero one coming from a monomial of p
// of that exponent; and the k-th coefficient is supported on the lowerings of
// the finitely many monomials of p of exponent k at v, which are monomials of
// the variables of p other than v.
var CoefficientsOverParameters = coefficientsOverParametersThm{family.Add(registry.ProofEntry{
	Name: "CoefficientsOverParameters",
	Reading: "At p = 0 every coefficient is the zero polynomial. " +
		"integer_polynomial(p) is load-bearing twice: finitely many exponents of v " +
		"occur, and each coefficient vanishes off the finitely supported monomials.",
	Key: "prop_20d9e742e876ac98",
	Build: family.Theorem(Statement{
		Binders: "∀v:num. ∀p:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
		},
		Conclusion: "polynomial_over(integer_polynomial_ring.zero, " +
			"    polynomial_algebra(int_ring, integer_polynomial_vars(p) ∖ {v}), " +
			"    integer_polynomial_coefficient(v, p))",
	},
		func(a *Argument, v *Expr[Nat], p *Arrow[Fun[Nat, Nat], Int], pPolynomial Fact) {
			support := a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(int_of_num(0), p)")
			exponent := a.TermAs[Fun[Fun[Nat, Nat], Nat]]("λm:(num → num). m(v)")
			own := a.Conjuncts(
				GroupPremises(pPolynomial, PolynomialSupportFinite.At(p)),
				"p is nonzero at finitely many monomials",
				"each of them a monomial of the variables of p")
			_, bound := a.Obtain(
				"finitely many exponents of v occur in p, so all of them are at most some n",
				"∃n:num. «exponents» ⊆ 0 .. n",
				By(
					own[0],
					finite_set.FiniteImage.At(exponent, support),
					num_segment.FiniteIffBounded.At(a.TermAs[Set[Nat]]("«exponents»"))))
			absent := a.Have(
				"an exponent past n occurs in no monomial of p",
				"∀k:num. n < k ⇒ k ∉ «exponents»",
				ByArith(bound, set_basic.SubsetDef))
			vanish := a.Have(
				"so past n the coefficients vanish",
				"∀k:num. ∀m:(num → num). n < k ⇒ integer_polynomial_coefficient(v, p, k, m) = 0",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					m := b.FixAs[Fun[Nat, Nat]]("m")
					past := b.Assume()
					b.Show(
						"a nonzero coefficient would come from the monomial m "+
							"with v raised to k, a monomial of p of exponent k at v",
						By(
							absent.At(k),
							past,
							integerPolynomialCoefficientDef.At(v, p, k, m),
							set_basic.InImage.At(exponent, support, k)))
				}))
			coefficients := a.Have(
				"each coefficient is a polynomial in the variables of p other than v",
				"∀k:num. "+
					"    integer_polynomial_coefficient(v, p, k) ∈ "+
					"    polynomial_algebra(int_ring, integer_polynomial_vars(p) ∖ {v})",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					fibre := b.Have(
						"the monomials of p of exponent k at v are finitely many",
						"finite(«fibre»(k))",
						By(
							own[0],
							set_basic.SubsetDef,
							finite_set.FiniteSubset.At(b.TermAs[Set[Fun[Nat, Nat]]]("«fibre»(k)"), support)))
					lowered := b.Have(
						"and lower to monomials of the variables of p other than v",
						"image(«lower», «fibre»(k)) ⊆ monomials(integer_polynomial_vars(p) ∖ {v})",
						By(own[1], set_image.ImageSubsetIff, set_basic.SubsetDef, MonomialLowered))
					b.Show(
						"the k-th coefficient is supported on the finitely many lowerings",
						Simp(Fwd(polynomial_algebra.PolynomialAlgebraMember), Fwd(CoefficientSupport)),
						By(fibre, lowered, finite_set.FiniteImage, set_basic.InUniv))
				}))
			a.Do(Unfold(polynomial.PolynomialOverDef), SplitConj(
				Case(
					"past n the coefficients are the zero polynomial",
					Witness(a.TermAs[Nat]("suc(n)")),
					Simp(Fwd(vec_space.VecDef), Fwd(function_module.FunZeroDef)),
					ByArith(vanish)),
				Case(
					"and each is a polynomial in the variables of p other than v",
					By(coefficients)),
			))
		}),
})}
