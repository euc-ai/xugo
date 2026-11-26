// ideal_membership.go — membership in the ideal finitely many forms generate,
// read at bounded degree: a polynomial of degree at most B lies in that ideal
// exactly when it is a combination of the forms with cofactors of degree at
// most B. A polynomial of degree at most B in the variables below n + 1 is one
// in the variables up to n whose monomials have degree at most B. The ideal of
// a finite family is its combinations; the part of degree at most B of a sum is
// the sum of the parts; and multiplying by a form of degree e takes the terms
// of a cofactor of degree at most B − e to the part of degree at most B of the
// product. Over an infinite domain the combination may be read as an identity
// of values at the points, and the ideal's primality then reads, degree bound
// by degree bound, as a condition on such pointwise combinations.

package homogeneous_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialBoundUpTo — a polynomial has degree at most d in the n + 1 variables below n + 1 exactly
// when it is a polynomial in the variables up to n each of whose monomials where it is nonzero has
// degree at most d: the variables below n + 1 are those up to n, and a monomial of them is zero from
// n + 1 on.
var PolynomialBoundUpTo = polynomialBoundUpToThm{family.Add(registry.ProofEntry{
	Name: "PolynomialBoundUpTo",
	Key:  "prop_4c406e9e905099ab",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num. ∀p:((num → num) → A).",
		Conclusion: "polynomial_bound(R, n + 1, d, p) ⇔ " +
			"p ∈ polynomial_algebra(R, {i:num | i ≤ n}) ∧ " +
			"(∀m:(num → num). p(m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) ≤ d)",
	},
		func(a *Argument, R *Expr[RingOps[A]], n, d *Expr[Nat], p *Arrow[Fun[Nat, Nat], A]) {
			sameVariables := a.Have(
				"the variables below n + 1 are those up to n",
				"{i:num | i < n + 1} = {i:num | i ≤ n}",
				BySets(nat_order.LessThanSucIffLessEq, nat_arith.Add1))
			a.Do(
				Simp(Fwd(polynomial_encoding.PolynomialBoundDef), Fwd(polynomial_encoding.BoundedMonomialsDef)),
				sameVariables.Rw())
			a.Iff()
			a.Forward(
				"a monomial where p is not zero lies in its support, of degree at most d",
				func(b *Argument, given Fact) {
					b.Show(
						"so it has degree at most d",
						BySets(given))
				})
			a.Backward(
				"a monomial where p is not zero is one of the variables "+
					"up to n, so zero past n, and of degree at most d",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"p is a polynomial in the variables up to n",
						"its monomials have degree at most d")
					beyond := b.Have(
						"a variable past n is not one of them",
						"∀i:num. n + 1 ≤ i ⇒ ¬(i ≤ n)",
						ByArith())
					monomials := b.Have(
						"a monomial where p is not zero is a monomial of the variables up to n",
						"∀m:(num → num). p(m) ≠ R.zero ⇒ m ∈ monomials({i:num | i ≤ n})",
						BySets(parts[0], polynomial_algebra.PolynomialAlgebraMember))
					b.Show(
						"so its support lies among the monomials of degree at most d in the variables below n + 1",
						BySets(parts[1], monomials, beyond, parts[0], polynomial_algebra.MonomialSupport))
				})
		}),
})}

// BoundedIdealMembership — a polynomial h of degree at most B lies in the
// ideal the forms P(0), …, P(r − 1) generate exactly when it is a
// combination of them with cofactors of degree at most B. A member of the
// ideal is a combination Σ P(j)·G(j) with polynomial cofactors
// (submodule.SpanFamilyCombinations). Let d(j) be the degree of P(j) and
// H(j) the terms of G(j) of degree at most B − d(j). h, of degree at most B,
// is its own part of degree at most B; that part of a sum is the sum of the
// parts, and the part of degree at most B of P(j)·G(j) is P(j)·H(j)
// (FormTimesTruncation). So h = Σ P(j)·H(j), each H(j) of degree at most B.
var BoundedIdealMembership = boundedIdealMembershipThm{family.Add(registry.ProofEntry{
	Name: "BoundedIdealMembership",
	Key:  "prop_fa70763b8b162aa6",
	Reading: "Homogeneity of the generators is load-bearing: for a generator that is not a form, " +
		"a member of low degree can need cofactors of high degree whose high terms cancel in the " +
		"sum. The bound counts total degree in the variables 0, …, n, read as polynomial_bound's " +
		"variables below n + 1. With r = 0 the ideal is zero and so is the empty combination.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n r B:num. ∀P:(num → (num → num) → A). ∀h:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(R, n, e, P(j))",
			"polynomial_bound(R, n + 1, B, h)",
		},
		Conclusion: "h ∈ ideal_span(«polynomialRing», image(P, {j:num | j < r})) ⇔ " +
			"∃H:(num → (num → num) → A). " +
			"    (∀j:num. j < r ⇒ polynomial_bound(R, n + 1, B, H(j))) ∧ " +
			"    h = " +
			"    module_sum(«polynomialRing».add, " +
			"        «polynomialRing».zero, " +
			"        {j:num | j < r}, " +
			"        λj:num. «polynomialRing».mul(P(j), H(j)))",
		Abbrev: Abbrev{
			{Name: "polynomialRing", Text: "polynomial_algebra_ring(R, {i:num | i ≤ n})"},
			{Name: "upTo", Text: "λd:num. λf:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) ≤ d, f(m), R.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, r, B *Expr[Nat],
			P *Arrow[Nat, Fun[Fun[Nat, Nat], A]],
			h *Arrow[Fun[Nat, Nat], A],
			ring comm_ring.CommRingFact[on.R],
			forms, bounded Fact,
		) {
			type monomial = Fun[Nat, Nat]
			type polynomial = Fun[monomial, A]
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			polynomials := a.Have(
				"the polynomials in the variables up to n form a commutative ring",
				"comm_ring_on(«polynomialRing»)",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn.At(R, variables)))
			_, degrees := a.ObtainAs[Fun[Nat, Nat]](
				"each generator P(j) is a form, of degree d(j)",
				"∃d:(num → num). ∀j:num. j < r ⇒ homogeneous_polynomial(R, n, d(j), P(j))",
				By(forms))
			generators := a.Have(
				"so the generators are polynomials",
				"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					below := b.Assume()
					b.Show(
						"a form is a polynomial",
						By(
							degrees.At(j),
							below,
							FormPolynomial.At(R, n, b.TermAs[Nat]("d(j)"), b.TermAs[polynomial]("P(j)"))))
				}))
			combinations := a.Have(
				"h lies in the ideal exactly when it is a combination of the generators with polynomial cofactors",
				"h ∈ ideal_span(«polynomialRing», image(P, {j:num | j < r})) ⇔ "+
					"∃G:(num → (num → num) → A). "+
					"    (∀j:num. j < r ⇒ G(j) ∈ «polynomialRing».carrier) ∧ "+
					"    h = "+
					"    module_sum(«polynomialRing».add, "+
					"        «polynomialRing».zero, "+
					"        {j:num | j < r}, "+
					"        λj:num. «polynomialRing».mul(P(j), G(j)))",
				By(generators, submodule.SpanFamilyCombinations.Read(polynomials).At(P, r, h)))
			a.Do(combinations.Rw())
			a.Iff()
			a.Backward(
				"cofactors of degree at most B are polynomial cofactors",
				func(b *Argument, given Fact) {
					H, form := b.UnpackAs[Fun[Nat, polynomial]](given, "H")
					b.Take(H)
					b.Show(
						"a polynomial of degree at most B is a polynomial in the variables up to n",
						By(form, At(PolynomialBoundUpTo, R, n, B)))
				})
			a.Forward(
				"truncate each cofactor G(j) to its terms of degree at most B − d(j)",
				func(b *Argument, given Fact) {
					_, form := b.UnpackAs[Fun[Nat, polynomial]](given, "G")
					parts := b.Conjuncts(
						form,
						"each G(j) is a polynomial",
						"h is Σ_{j<r} P(j)·G(j)")
					additive := b.Have(
						"the part of degree at most B of a sum is the sum of the parts",
						"∀u v:((num → num) → A). "+
							"    «upTo»(B, «polynomialRing».add(u, v)) = «polynomialRing».add(«upTo»(B, u), «upTo»(B, v))",
						Derive(func(c *Argument) {
							c.FixAs[polynomial]("u")
							c.FixAs[polynomial]("v")
							c.Do(Funext())
							c.FixAs[monomial]("m")
							c.Do(Simp(Fwd(function_module.FunAddDef)))
							c.Cases(c.TermAs[Bool]("sum({i:num | i ≤ n}, m) ≤ B"))
							c.When(
								"up to degree B both sides keep the coefficients",
								func(d *Argument, low Fact) {
									d.Show(
										"the coefficient of the sum",
										By(low))
								})
							c.Otherwise(
								"above degree B both sides are zero",
								func(d *Argument, high Fact) {
									d.Show(
										"zero plus zero",
										ByArith(high, ring))
								})
						}))
					keepsZero := b.Have(
						"and the part of degree at most B of zero is zero",
						"«upTo»(B, «polynomialRing».zero) = «polynomialRing».zero",
						Funext(),
						Simp(Fwd(function_module.FunZeroDef)),
						Basic())
					products := b.Have(
						"each P(j)·G(j) is a polynomial",
						"∀j:num. j < r ⇒ «polynomialRing».mul(P(j), G(j)) ∈ «polynomialRing».carrier",
						By(parts[0], generators, comm_ring.MulIn.Read(polynomials)))
					H, cofactors := b.LetAs[Fun[Nat, polynomial]](
						"H",
						"λj:num. λm:(num → num). COND(sum({i:num | i ≤ n}, m) + d(j) ≤ B, G(j, m), R.zero)")
					truncated := b.Have(
						"the part of degree at most B of P(j)·G(j) is P(j)·H(j), P(j) a form of degree d(j)",
						"∀j:num. j < r ⇒ «upTo»(B, «polynomialRing».mul(P(j), G(j))) = «polynomialRing».mul(P(j), H(j))",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							c.Show(
								"multiplying by a form of degree d(j) takes the terms of "+
									"degree at most B − d(j) to the part of degree at most B",
								Simp(Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
								cofactors.Rw(),
								By(
									ring,
									degrees.At(j),
									parts[0].At(j),
									below,
									FormTimesTruncation.At(
										R, n, c.TermAs[Nat]("d(j)"), B, c.TermAs[polynomial]("P(j)"), c.TermAs[polynomial]("G(j)"))))
						}))
					boundedCofactors := b.Have(
						"each H(j) is a polynomial of degree at most B",
						"∀j:num. j < r ⇒ polynomial_bound(R, n + 1, B, H(j))",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							coefficients := c.Conjuncts(
								c.Simplified(GroupPremises(below, parts[0].At(j)), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
								"G(j) is nonzero at finitely many monomials",
								"every monomial where G(j) is nonzero is a monomial of the variables up to n",
								"every coefficient of G(j) lies in the carrier")
							support := c.Have(
								"H(j) is nonzero only where G(j) is",
								"fun_support(R.zero, H(j)) ⊆ fun_support(R.zero, G(j))",
								cofactors.Rw(),
								BySets())
							isPolynomial := c.Have(
								"so H(j) is a polynomial in the variables up to n, its coefficients those of G(j) or zero",
								"H(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
								cofactors.Rw(),
								Simp(Fwd(polynomial_algebra.PolynomialAlgebraMember)),
								By(
									coefficients[0],
									coefficients[1],
									coefficients[2],
									support,
									finite_set.FiniteSubset,
									set_order.SubsetTrans,
									comm_ring.ZeroIn.Read(ring)))
							degree := c.Have(
								"a monomial where H(j) is not zero has degree at most B − d(j), so at most B",
								"∀m:(num → num). H(j, m) ≠ R.zero ⇒ sum({i:num | i ≤ n}, m) ≤ B",
								Derive(func(e *Argument) {
									e.FixAs[monomial]("m")
									nonzero := e.Assume()
									kept := e.Have(
										"a nonzero coefficient of H(j) is one the truncation keeps",
										"sum({i:num | i ≤ n}, m) + d(j) ≤ B",
										By(nonzero, cofactors))
									e.Show(
										"so the monomial has degree at most B",
										ByArith(kept))
								}))
							c.Show(
								"which is the bound",
								By(isPolynomial, degree, PolynomialBoundUpTo.At(R, n, B, c.TermAs[polynomial]("H(j)"))))
						}))
					combination := b.Have(
						"h is Σ P(j)·H(j)",
						"h = "+
							"module_sum(«polynomialRing».add, "+
							"    «polynomialRing».zero, "+
							"    {j:num | j < r}, "+
							"    λj:num. «polynomialRing».mul(P(j), H(j)))",
						CalcEq(
							Leg(
								b.TermAs[polynomial]("«upTo»(B, h)"),
								"h has no monomial of degree above B, so it is its own part of degree at most B",
								Funext(),
								By(bounded, PolynomialBoundUpTo.At(R, n, B, h))),
							Leg(
								b.TermAs[polynomial](
									"«upTo»(B, "+
										"    module_sum(«polynomialRing».add, "+
										"        «polynomialRing».zero, "+
										"        {j:num | j < r}, "+
										"        λj:num. «polynomialRing».mul(P(j), G(j))))"),
								"h is Σ P(j)·G(j)",
								By(parts[1])),
							Leg(
								b.TermAs[polynomial](
									"module_sum(«polynomialRing».add, "+
										"    «polynomialRing».zero, "+
										"    {j:num | j < r}, "+
										"    λj:num. «upTo»(B, «polynomialRing».mul(P(j), G(j))))"),
								"the part of degree at most B passes through the sum",
								By(
									additive,
									keepsZero,
									products,
									num_segment.FiniteBelowStrict,
									module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(polynomials)).At(
										b.TermAs[Op[polynomial]]("«polynomialRing».add"),
										b.TermAs[polynomial]("«polynomialRing».zero"),
										b.TermAs[Fun[polynomial, polynomial]]("«upTo»(B)"),
										b.TermAs[Set[Nat]]("{j:num | j < r}"),
										b.TermAs[Fun[Nat, polynomial]]("λj:num. «polynomialRing».mul(P(j), G(j))")))),
							FinalLeg(
								"and the part of degree at most B of each P(j)·G(j) is P(j)·H(j)",
								By(
									truncated,
									module.ModuleSumCongruence.At(
										b.TermAs[Op[polynomial]]("«polynomialRing».add"),
										b.TermAs[polynomial]("«polynomialRing».zero"),
										b.TermAs[Set[Nat]]("{j:num | j < r}"),
										b.TermAs[Fun[Nat, polynomial]]("λj:num. «upTo»(B, «polynomialRing».mul(P(j), G(j)))"),
										b.TermAs[Fun[Nat, polynomial]]("λj:num. «polynomialRing».mul(P(j), H(j))"))))))
					b.Take(H)
					b.Show(
						"H(j) are cofactors of degree at most B",
						By(boundedCofactors, combination))
				})
		}),
})}

// PointwiseIdealMembership — over an infinite integral domain R, a polynomial h of degree at most B
// lies in the ideal the forms P(0), …, P(r − 1) generate exactly when, at every point x of R in
// n + 1 coordinates, h(x) = Σ P(j)(x)·H(j)(x) for cofactors H(j) of degree at most B. A member of
// the ideal is such a combination as a polynomial (BoundedIdealMembership), and evaluation at x, a
// ring homomorphism, carries the combination to the combination of the values. Conversely h and
// Σ P(j)·H(j) then take the same value at every point, so they are the same polynomial
// (polynomial_encoding.PolynomialDeterminedByValues).
var PointwiseIdealMembership = pointwiseIdealMembershipThm{family.Add(registry.ProofEntry{
	Name: "PointwiseIdealMembership",
	Key:  "prop_7311948bd12b20eb",
	Reading: "The infinite carrier is load-bearing: over a field with q elements, x₀^q·x₁ − " +
		"x₀·x₁^q is a nonzero form vanishing at every point, so with no forms (r = 0) it is " +
		"pointwise the empty combination without lying in the zero ideal. The points are the ring " +
		"tuples of length n + 1, the variables 0, …, n, as polynomial_bound and ring_tuple read them.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). " +
			"∀n r B:num. " +
			"∀P:(num → (num → num) → A). " +
			"∀h:((num → num) → A).",
		Hypotheses: []string{
			"infinite(R.carrier)",
			"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(R, n, e, P(j))",
			"polynomial_bound(R, n + 1, B, h)",
		},
		Conclusion: "h ∈ ideal_span(«polynomialRing», image(P, {j:num | j < r})) ⇔ " +
			"∃H:(num → (num → num) → A). " +
			"    (∀j:num. j < r ⇒ polynomial_bound(R, n + 1, B, H(j))) ∧ " +
			"    (∀x:(num → A). " +
			"        ring_tuple(R, n + 1, x) ⇒ " +
			"        polynomial_value(R, h, x) = " +
			"        module_sum(R.add, " +
			"            R.zero, " +
			"            {j:num | j < r}, " +
			"            λj:num. polynomial_value(R, P(j), x) * polynomial_value(R, H(j), x)))",
		Abbrev: Abbrev{
			{Name: "polynomialRing", Text: "polynomial_algebra_ring(R, {i:num | i ≤ n})"},
			{Name: "combinationSum", Text: "λH:(num → (num → num) → A). " +
				"    module_sum(fun_add(R.add), " +
				"        fun_zero(R.zero), " +
				"        {j:num | j < r}, " +
				"        λj:num. polynomial_algebra_mul(R, P(j), H(j)))"},
		},
	},
		func(
			a *Argument,
			R integral_domain.IntegralDomainFact[on.R],
			n, r, B *Expr[Nat],
			P *Arrow[Nat, Fun[Fun[Nat, Nat], A]],
			h *Arrow[Fun[Nat, Nat], A],
			infinite, forms, bounded Fact,
		) {
			type monomial = Fun[Nat, Nat]
			type polynomial = Fun[monomial, A]
			ringR := a.TermAs[RingOps[A]]("R")
			ring := integral_domain.Ring.Read(R)
			polynomials := a.Have(
				"the polynomials in the variables up to n form a commutative ring",
				"comm_ring_on(«polynomialRing»)",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
			generators := a.Have(
				"the generators are polynomials, being forms",
				"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("j")
					below := b.Assume()
					e, form := b.ObtainAs[Nat](
						"P(j) is a form of some degree e",
						"∃e:num. homogeneous_polynomial(R, n, e, P(j))",
						By(forms, below))
					b.Show(
						"a form is a polynomial",
						By(form, FormPolynomial.At(ringR, n, e, b.TermAs[polynomial]("P(j)"))))
				}))
			sameVariables := a.Have(
				"the variables below n + 1 are those up to n",
				"{i:num | i < n + 1} = {i:num | i ≤ n}",
				BySets(nat_order.LessThanSucIffLessEq, nat_arith.Add1))
			combinations := a.Have(
				"a combination Σ P(j)·H(j) with polynomial cofactors is a polynomial, "+
					"whose value at a point of R is the combination of the values",
				Statement{
					Binders: "∀H:(num → (num → num) → A).",
					Hypotheses: []string{
						"∀j:num. j < r ⇒ H(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
					},
					Conclusion: "«combinationSum»(H) ∈ polynomial_algebra(R, {i:num | i ≤ n}) ∧ " +
						"(∀x:(num → A). " +
						"    ring_tuple(R, n + 1, x) ⇒ " +
						"    polynomial_value(R, «combinationSum»(H), x) = " +
						"    module_sum(R.add, " +
						"        R.zero, " +
						"        {j:num | j < r}, " +
						"        λj:num. polynomial_value(R, P(j), x) * polynomial_value(R, H(j), x)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, polynomial]]("H")
					cofactors := b.Assume()
					below := b.TermAs[Set[Nat]]("{j:num | j < r}")
					terms := b.Have(
						"each P(j)·H(j) is a polynomial",
						"∀j:num. j < r ⇒ polynomial_algebra_mul(R, P(j), H(j)) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						By(ring, generators, cofactors, polynomial_algebra.PolynomialAlgebraMulIn))
					summands := b.TermAs[Fun[Nat, polynomial]]("λj:num. polynomial_algebra_mul(R, P(j), H(j))")
					isPolynomial := b.Have(
						"and so is their sum",
						"«combinationSum»(H) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						By(
							terms,
							num_segment.FiniteBelowStrict,
							module.ModuleSumIn.Read(module.RegularModuleOn.Read(polynomials)).At(below, summands)))
					values := b.Have(
						"evaluation at a point x of R carries the combination to the combination of the values",
						Statement{
							Binders: "∀x:(num → A).",
							Hypotheses: []string{
								"ring_tuple(R, n + 1, x)",
							},
							Conclusion: "polynomial_value(R, «combinationSum»(H), x) = " +
								"module_sum(R.add, " +
								"    R.zero, " +
								"    {j:num | j < r}, " +
								"    λj:num. polynomial_value(R, P(j), x) * polynomial_value(R, H(j), x))",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[Fun[Nat, A]]("x")
							tuple := c.Assume()
							coordinates := c.Have(
								"the coordinates of x up to n lie in R",
								"∀i:num. i ∈ {i:num | i ≤ n} ⇒ x(i) ∈ R.carrier",
								ByArith(tuple, polynomial_encoding.RingTupleDef))
							evaluation := c.Have(
								"evaluation at x is a ring homomorphism from the polynomials in the variables up to n",
								"ring_homomorphism(«polynomialRing», R, polynomial_algebra_eval(R, R, λa:A. a, x))",
								By(
									ring_homomorphism.RingHomIdentity.Read(ring),
									coordinates,
									polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
										ringR,
										ringR,
										c.TermAs[Fun[A, A]]("λa:A. a"),
										x,
										c.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
							sum := c.Have(
								"it carries the sum to the sum of the values of the terms",
								"polynomial_algebra_eval(R, R, λa:A. a, x, «combinationSum»(H)) = "+
									"module_sum(R.add, "+
									"    R.zero, "+
									"    {j:num | j < r}, "+
									"    λj:num. polynomial_algebra_eval(R, R, λa:A. a, x, polynomial_algebra_mul(R, P(j), H(j))))",
								By(
									terms,
									num_segment.FiniteBelowStrict,
									ring_homomorphism.MapSum.Read(evaluation).At(below, summands)))
							products := c.Have(
								"and the value of each term P(j)·H(j) to the product of the values",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"j < r",
									},
									Conclusion: "polynomial_algebra_eval(R, R, λa:A. a, x, polynomial_algebra_mul(R, P(j), H(j))) = " +
										"polynomial_algebra_eval(R, R, λa:A. a, x, P(j)) * polynomial_algebra_eval(R, R, λa:A. a, x, H(j))",
								},
								By(generators, cofactors, ring_homomorphism.MapMul.Read(evaluation)))
							c.Show(
								"so the value of the combination is the combination of the values",
								Simp(Fwd(polynomial_encoding.PolynomialValueDef)),
								By(
									sum,
									products,
									module.ModuleSumCongruence.At(
										c.TermAs[Op[A]]("R.add"),
										c.TermAs[A]("R.zero"),
										below,
										c.TermAs[Fun[Nat, A]](
											"λj:num. polynomial_algebra_eval(R, R, λa:A. a, x, polynomial_algebra_mul(R, P(j), H(j)))"),
										c.TermAs[Fun[Nat, A]](
											"λj:num. "+
												"    polynomial_algebra_eval(R, R, λa:A. a, x, P(j)) * "+
												"    polynomial_algebra_eval(R, R, λa:A. a, x, H(j))"))))
						}))
					b.Show(
						"the combination is a polynomial with those values",
						By(isPolynomial, values))
				}))
			membership := a.Have(
				"h lies in the ideal exactly when it is a combination "+
					"Σ P(j)·H(j) with cofactors of degree at most B",
				"h ∈ ideal_span(«polynomialRing», image(P, {j:num | j < r})) ⇔ "+
					"∃H:(num → (num → num) → A). "+
					"    (∀j:num. j < r ⇒ polynomial_bound(R, n + 1, B, H(j))) ∧ h = «combinationSum»(H)",
				By(ring, forms, bounded, BoundedIdealMembership.At(ringR, n, r, B, P, h)))
			a.Do(membership.Rw())
			a.Iff()
			a.Forward(
				"evaluating h = Σ P(j)·H(j) at each point gives the identity of values",
				func(b *Argument, given Fact) {
					H, form := b.UnpackAs[Fun[Nat, polynomial]](given, "H")
					parts := b.Conjuncts(
						form,
						"each H(j) has degree at most B",
						"h is Σ P(j)·H(j)")
					b.Take(H)
					cofactors := b.Have(
						"each H(j) is a polynomial in the variables up to n",
						"∀j:num. j < r ⇒ H(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						By(parts[0], At(PolynomialBoundUpTo, ringR, n, B)))
					b.Show(
						"the same cofactors, the value of h at each point being that of the combination",
						parts[1].Rw(),
						By(parts[0], cofactors, combinations))
				})
			a.Backward(
				"h and Σ P(j)·H(j) take the same value at every point, so they are the same polynomial",
				func(b *Argument, given Fact) {
					H, form := b.UnpackAs[Fun[Nat, polynomial]](given, "H")
					parts := b.Conjuncts(
						form,
						"each H(j) has degree at most B",
						"at each point h takes the value of Σ P(j)·H(j)")
					b.Take(H)
					cofactors := b.Have(
						"each H(j) is a polynomial in the variables up to n",
						"∀j:num. j < r ⇒ H(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						By(parts[0], At(PolynomialBoundUpTo, ringR, n, B)))
					combination := b.Conjuncts(
						GroupPremises(cofactors, combinations.At(H)),
						"Σ P(j)·H(j) is a polynomial in the variables up to n",
						"its value at each point is the combination of the values")
					hPolynomial := b.Have(
						"h is a polynomial in the variables below n + 1",
						"h ∈ polynomial_algebra(R, {i:num | i < n + 1})",
						By(bounded, polynomial_encoding.PolynomialBoundDef))
					combinationPolynomial := b.Have(
						"and so is Σ P(j)·H(j)",
						"«combinationSum»(H) ∈ polynomial_algebra(R, {i:num | i < n + 1})",
						sameVariables.Rw(),
						By(combination[0]))
					sameValues := b.Have(
						"the two take the same value at every point",
						Statement{
							Binders: "∀x:(num → A).",
							Hypotheses: []string{
								"ring_tuple(R, n + 1, x)",
							},
							Conclusion: "polynomial_value(R, h, x) = polynomial_value(R, «combinationSum»(H), x)",
						},
						By(parts[1], combination[1]))
					equal := b.Have(
						"so h is Σ P(j)·H(j)",
						"h = «combinationSum»(H)",
						By(
							infinite,
							hPolynomial,
							combinationPolynomial,
							sameValues,
							polynomial_encoding.PolynomialDeterminedByValues.Read(R).At(
								b.TermAs[Nat]("n + 1"),
								h,
								b.TermAs[polynomial]("«combinationSum»(H)"))))
					b.Show(
						"cofactors of degree at most B with h = Σ P(j)·H(j)",
						By(parts[0], equal))
				})
		}),
})}

// FormIdealPrimeCriterion — over an infinite integral domain R, the ideal the forms P(0), …, P(r − 1)
// generate among the polynomials in the variables up to n is prime exactly when 1 is not a
// combination Σ P(j)·H(j) with constant cofactors, and, at every degree bound D, a product f·g of
// polynomials of degree at most D that is a combination with cofactors of degree at most 2D has a
// factor that is a combination with cofactors of degree at most D — every combination an identity
// of values at the points of R in n + 1 coordinates. A polynomial of degree at most B lies in the
// ideal exactly when it is such a combination with cofactors of degree at most B
// (PointwiseIdealMembership). The one polynomial has degree 0 and value 1 everywhere, so the first
// condition says the ideal is proper; f·g has degree at most 2D and value f(x)·g(x), so the second
// says a product in the ideal has a factor in it, any two polynomials having a common degree bound
// (polynomial_encoding.CommonDegreeBound).
var FormIdealPrimeCriterion = formIdealPrimeCriterionThm{family.Add(registry.ProofEntry{
	Name: "FormIdealPrimeCriterion",
	Key:  "prop_3066b17f94c719bc",
	Reading: "The infinite carrier is load-bearing: membership is read through values at points, " +
		"which over a finite field do not determine a polynomial. Only the second condition depends " +
		"on the degree bound D, and it is asked at every D; the first is the ideal's being proper, " +
		"read at degree 0. With no forms (r = 0) the empty combination is 0, and the criterion reads: " +
		"1 is not 0, and a product vanishing at every point has a factor vanishing at every point.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). ∀n r:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"infinite(R.carrier)",
			"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(R, n, e, P(j))",
		},
		Conclusion: "prime_ideal(«polynomialRing», «ideal») ⇔ " +
			"¬«combination»(0, λx:(num → A). R.one) ∧ " +
			"(∀D:num. ∀f g:((num → num) → A). " +
			"    polynomial_bound(R, n + 1, D, f) ∧ " +
			"    polynomial_bound(R, n + 1, D, g) ∧ " +
			"    «combination»(2 * D, λx:(num → A). polynomial_value(R, f, x) * polynomial_value(R, g, x)) ⇒ " +
			"    «combination»(D, λx:(num → A). polynomial_value(R, f, x)) ∨ " +
			"    «combination»(D, λx:(num → A). polynomial_value(R, g, x)))",
		Abbrev: Abbrev{
			{Name: "polynomialRing", Text: "polynomial_algebra_ring(R, {i:num | i ≤ n})"},
			{Name: "ideal", Text: "ideal_span(«polynomialRing», image(P, {j:num | j < r}))"},
			{Name: "combination", Text: "λB:num. λv:((num → A) → A). ∃H:(num → (num → num) → A). " +
				"    (∀j:num. j < r ⇒ polynomial_bound(R, n + 1, B, H(j))) ∧ " +
				"    (∀x:(num → A). " +
				"        ring_tuple(R, n + 1, x) ⇒ " +
				"        v(x) = " +
				"        module_sum(R.add, " +
				"            R.zero, " +
				"            {j:num | j < r}, " +
				"            λj:num. polynomial_value(R, P(j), x) * polynomial_value(R, H(j), x)))"},
		},
	},
		func(
			a *Argument,
			R integral_domain.IntegralDomainFact[on.R],
			n, r *Expr[Nat],
			P *Arrow[Nat, Fun[Fun[Nat, Nat], A]],
			infinite, forms Fact,
		) {
			type monomial = Fun[Nat, Nat]
			type polynomial = Fun[monomial, A]
			ringR := a.TermAs[RingOps[A]]("R")
			ring := integral_domain.Ring.Read(R)
			polynomials := a.Have(
				"the polynomials in the variables up to n form a commutative ring",
				"comm_ring_on(«polynomialRing»)",
				By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
			pointwise := a.Have(
				"h of degree at most B lies in the ideal exactly when it is pointwise "+
					"a combination of the forms with cofactors of degree at most B",
				Statement{
					Binders: "∀B:num. ∀h:((num → num) → A).",
					Hypotheses: []string{
						"polynomial_bound(R, n + 1, B, h)",
					},
					Conclusion: "h ∈ «ideal» ⇔ «combination»(B, λx:(num → A). polynomial_value(R, h, x))",
				},
				By(infinite, forms, PointwiseIdealMembership.Read(R)))
			sameVariables := a.Have(
				"the variables below n + 1 are those up to n",
				"{i:num | i < n + 1} = {i:num | i ≤ n}",
				BySets(nat_order.LessThanSucIffLessEq, nat_arith.Add1))
			products := a.Have(
				"at a point x of R, evaluation is a ring homomorphism from the "+
					"polynomials: it takes a product to the product of the values",
				Statement{
					Binders: "∀f g:((num → num) → A). ∀x:(num → A).",
					Hypotheses: []string{
						"f ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						"g ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						"ring_tuple(R, n + 1, x)",
					},
					Conclusion: "polynomial_value(R, polynomial_algebra_mul(R, f, g), x) = " +
						"polynomial_value(R, f, x) * polynomial_value(R, g, x)",
				},
				Derive(func(b *Argument) {
					b.FixAs[polynomial]("f")
					b.FixAs[polynomial]("g")
					x := b.FixAs[Fun[Nat, A]]("x")
					given := b.Conjuncts(
						b.Assume(),
						"f is a polynomial in the variables up to n",
						"so is g",
						"x is a point of R in n + 1 coordinates")
					coordinates := b.Have(
						"the coordinates of x up to n lie in F",
						"∀i:num. i ∈ {i:num | i ≤ n} ⇒ x(i) ∈ R.carrier",
						ByArith(given[2], polynomial_encoding.RingTupleDef))
					evaluation := b.Have(
						"evaluation at x is a ring homomorphism from the polynomials in the variables up to n",
						"ring_homomorphism(«polynomialRing», R, polynomial_algebra_eval(R, R, λa:A. a, x))",
						By(
							ring_homomorphism.RingHomIdentity.Read(ring),
							coordinates,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
								ringR,
								ringR,
								b.TermAs[Fun[A, A]]("λa:A. a"),
								x,
								b.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
					b.Show(
						"so it takes f·g to f(x)·g(x)",
						By(
							given[0],
							given[1],
							ring_homomorphism.MapMul.Read(evaluation),
							polynomial_encoding.PolynomialValueDef))
				}))
			one := a.TermAs[polynomial]("polynomial_algebra_one(R)")
			constants := a.Have(
				"the constants are a ring homomorphism into the polynomials",
				"ring_homomorphism(R, «polynomialRing», polynomial_algebra_const(R))",
				By(ring, polynomial_algebra.PolynomialAlgebraConstHom))
			constantOne := a.Have(
				"so the one polynomial is the constant 1",
				"polynomial_algebra_const⟨D:num⟩(R, R.one) = polynomial_algebra_one(R)",
				By(ring_homomorphism.MapOne.Read(constants)))
			oneValue := a.Have(
				"the one polynomial takes the value 1 at every point",
				"∀x:(num → A). polynomial_value(R, polynomial_algebra_one(R), x) = R.one",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("x")
					b.Show(
						"evaluation fixes the constant 1",
						constantOne.RwRev(),
						Simp(Fwd(polynomial_encoding.PolynomialValueDef)),
						By(
							ring_homomorphism.RingHomIdentity.Read(ring),
							comm_ring.OneIn.Read(ring),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalConst))
				}))
			oneBound := a.Have(
				"the constant 1 is a form of degree 0, so of degree at most 0",
				"polynomial_bound(R, n + 1, 0, polynomial_algebra_one(R))",
				constantOne.RwRev(),
				By(
					ring,
					comm_ring.OneIn.Read(ring),
					FormConstant.At(ringR, n, a.TermAs[A]("R.one")),
					FormBound.At(
						ringR, n, a.TermAs[Nat]("0"), a.TermAs[polynomial]("polynomial_algebra_const(R, R.one)"))))
			unit := a.Have(
				"so 1 lies in the ideal exactly when it is pointwise "+
					"a combination of the forms with constant cofactors",
				"polynomial_algebra_one(R) ∈ «ideal» ⇔ «combination»(0, λx:(num → A). R.one)",
				GroupPremises(oneBound, pointwise.At(a.TermAs[Nat]("0"), one)).Rw(),
				Simp(Fwd(oneValue)),
				Basic())
			a.Do(Simp(Fwd(ring_ideal.PrimeIdealDef)))
			a.Iff()
			a.Forward(
				"a prime ideal is proper, and a product in it has a factor in it",
				func(b *Argument, prime Fact) {
					parts := b.Conjuncts(
						prime,
						"the span is an ideal",
						"1 does not lie in it",
						"a product of polynomials in it has a factor in it")
					proper := b.Have(
						"so 1 is not pointwise a combination with constant cofactors",
						"¬«combination»(0, λx:(num → A). R.one)",
						By(parts[1], unit))
					factors := b.Have(
						"and a product of polynomials of degree at most D, a "+
							"combination at degree 2D, has a factor that is one at degree D",
						Statement{
							Binders: "∀D:num. ∀f g:((num → num) → A).",
							Hypotheses: []string{
								"polynomial_bound(R, n + 1, D, f)",
								"polynomial_bound(R, n + 1, D, g)",
								"«combination»(2 * D, λx:(num → A). polynomial_value(R, f, x) * polynomial_value(R, g, x))",
							},
							Conclusion: "«combination»(D, λx:(num → A). polynomial_value(R, f, x)) ∨ " +
								"«combination»(D, λx:(num → A). polynomial_value(R, g, x))",
						},
						Derive(func(c *Argument) {
							D := c.FixAs[Nat]("D")
							f := c.FixAs[polynomial]("f")
							g := c.FixAs[polynomial]("g")
							given := c.Conjuncts(
								c.Assume(),
								"f has degree at most D",
								"g has degree at most D",
								"f·g is pointwise a combination with cofactors of degree at most 2D")
							H, combination := c.UnpackAs[Fun[Nat, polynomial]](given[2], "H")
							cofactors := c.Conjuncts(
								combination,
								"each H(j) has degree at most 2D",
								"f(x)·g(x) is Σ P(j)(x)·H(j)(x) at each point x")
							twice := c.Have(
								"2D is D + D",
								"2 * D = D + D",
								ByArith())
							productBound := c.Have(
								"f·g has degree at most 2D",
								"polynomial_bound(R, n + 1, 2 * D, polynomial_algebra_mul(R, f, g))",
								twice.Rw(),
								By(
									ring,
									given[0],
									given[1],
									polynomial_encoding.PolynomialBoundMul.At(ringR, c.TermAs[Nat]("n + 1"), D, D, f, g)))
							polynomialFactors := c.Have(
								"f and g are polynomials in the variables up to n",
								"f ∈ polynomial_algebra(R, {i:num | i ≤ n}) ∧ g ∈ polynomial_algebra(R, {i:num | i ≤ n})",
								By(
									given[0],
									given[1],
									PolynomialBoundUpTo.At(ringR, n, D, f),
									PolynomialBoundUpTo.At(ringR, n, D, g)))
							inIdeal := c.Have(
								"so f·g lies in the ideal: its value at x is f(x)·g(x), the combination with the cofactors H",
								"polynomial_algebra_mul(R, f, g) ∈ «ideal»",
								GroupPremises(
									productBound,
									pointwise.At(c.TermAs[Nat]("2 * D"), c.TermAs[polynomial]("polynomial_algebra_mul(R, f, g)"))).Rw(),
								Witness(H),
								By(cofactors[0], cofactors[1], polynomialFactors, products.At(f, g)))
							factor := c.Have(
								"so f or g lies in the ideal, which is prime",
								"f ∈ «ideal» ∨ g ∈ «ideal»",
								By(polynomialFactors, inIdeal, parts[2].At(f, g)))
							c.Show(
								"and that factor is pointwise a combination with cofactors of degree at most D",
								By(factor, given[0], given[1], pointwise.At(D, f), pointwise.At(D, g)))
						}))
					b.Show(
						"both conditions hold",
						By(proper, factors))
				})
			a.Backward(
				"the span is a proper ideal, and a product of polynomials in it has a factor in it",
				func(b *Argument, criterion Fact) {
					conditions := b.Conjuncts(
						criterion,
						"1 is not pointwise a combination with constant cofactors",
						"the condition on products at every degree bound D")
					generators := b.Have(
						"the generators are polynomials, being forms",
						"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i ≤ n})",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							below := c.Assume()
							e, form := c.ObtainAs[Nat](
								"P(j) is a form of some degree e",
								"∃e:num. homogeneous_polynomial(R, n, e, P(j))",
								By(forms, below))
							c.Show(
								"a form is a polynomial",
								By(form, FormPolynomial.At(ringR, n, e, c.TermAs[polynomial]("P(j)"))))
						}))
					ideal := b.Have(
						"the span of the forms is an ideal",
						"ring_ideal(«polynomialRing», «ideal»)",
						By(generators, set_image.ImageSubsetIff, ring_ideal.SpanIdeal.Read(polynomials)))
					proper := b.Have(
						"1 does not lie in it",
						"polynomial_algebra_one(R) ∉ «ideal»",
						By(conditions[0], unit))
					prime := b.Have(
						"a product of polynomials in the ideal has a factor in it",
						Statement{
							Binders: "∀p q:((num → num) → A).",
							Hypotheses: []string{
								"p ∈ polynomial_algebra(R, {i:num | i ≤ n})",
								"q ∈ polynomial_algebra(R, {i:num | i ≤ n})",
								"polynomial_algebra_mul(R, p, q) ∈ «ideal»",
							},
							Conclusion: "p ∈ «ideal» ∨ q ∈ «ideal»",
						},
						Derive(func(c *Argument) {
							p := c.FixAs[polynomial]("p")
							q := c.FixAs[polynomial]("q")
							given := c.Conjuncts(
								c.Assume(),
								"p is a polynomial in the variables up to n",
								"so is q",
								"p·q lies in the ideal")
							pair := c.Have(
								"p and q, as a family of two, are polynomials in the variables below n + 1",
								"∀j:num. j < 2 ⇒ COND(j = 0, p, q) ∈ polynomial_algebra(R, {i:num | i < n + 1})",
								sameVariables.Rw(),
								By(given[0], given[1]))
							D, common := c.ObtainAs[Nat](
								"so they have a common degree bound D",
								"∃D:num. ∀j:num. j < 2 ⇒ polynomial_bound(R, n + 1, D, COND(j = 0, p, q))",
								By(
									pair,
									polynomial_encoding.CommonDegreeBound.At(
										ringR,
										c.TermAs[Nat]("n + 1"),
										c.TermAs[Nat]("2"),
										c.TermAs[Fun[Nat, polynomial]]("λj:num. COND(j = 0, p, q)"))))
							bounds := c.Have(
								"p and q have degree at most D",
								"polynomial_bound(R, n + 1, D, p) ∧ polynomial_bound(R, n + 1, D, q)",
								By(common.At(c.TermAs[Nat]("0")), common.At(c.TermAs[Nat]("1"))))
							twice := c.Have(
								"2D is D + D",
								"2 * D = D + D",
								ByArith())
							product := c.TermAs[polynomial]("polynomial_algebra_mul(R, p, q)")
							productBound := c.Have(
								"p·q has degree at most 2D",
								"polynomial_bound(R, n + 1, 2 * D, polynomial_algebra_mul(R, p, q))",
								twice.Rw(),
								By(
									ring,
									bounds,
									polynomial_encoding.PolynomialBoundMul.At(ringR, c.TermAs[Nat]("n + 1"), D, D, p, q)))
							H, combination := c.ObtainAs[Fun[Nat, polynomial]](
								"lying in the ideal, p·q is pointwise Σ P(j)·H(j) with cofactors of degree at most 2D",
								"«combination»(2 * D, λx:(num → A). polynomial_value(R, polynomial_algebra_mul(R, p, q), x))",
								By(productBound, given[2], pointwise.At(c.TermAs[Nat]("2 * D"), product)))
							cofactors := c.Conjuncts(
								combination,
								"each H(j) has degree at most 2D",
								"the value of p·q at each point x is Σ P(j)(x)·H(j)(x)")
							values := c.Have(
								"so p(x)·q(x) is the same combination, the value of p·q being p(x)·q(x)",
								"«combination»(2 * D, λx:(num → A). polynomial_value(R, p, x) * polynomial_value(R, q, x))",
								Witness(H),
								By(cofactors[0], cofactors[1], given[0], given[1], products.At(p, q)))
							c.Show(
								"by the condition on products, p or q is pointwise a combination "+
									"with cofactors of degree at most D, so it lies in the ideal",
								By(conditions[1].At(D, p, q), bounds, values, pointwise.At(D, p), pointwise.At(D, q)))
						}))
					b.Show(
						"so the span is a prime ideal",
						By(ideal, proper, prime))
				})
		}),
})}
