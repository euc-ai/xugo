// domain.go — the polynomials over an integral domain are an integral
// domain. Two nonzero polynomials involve finitely many variables, which
// a sequence ι runs through. Read along ι, exponent functions are ordered
// lexicographically: a strict order that adding a monomial keeps, and
// total on the monomials whose variables ι lists, so each nonzero
// polynomial has a greatest monomial where it is nonzero. For any strict
// order that adding a monomial keeps, the coefficient of a product at the
// sum of the two greatest monomials is the product of their two
// coefficients, nonzero in a domain.

package polynomial_algebra

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The lexicographic order along a sequence of variables
// ---------------------------------------------------------------------------

// MonomialLexOrder — ordering exponent functions lexicographically along a
// sequence ι of variables is a strict order that adding a monomial keeps:
// m comes before n when, at the first i where they differ, m(ι(i)) is
// below n(ι(i)). No m comes before itself; m before n before p puts m
// before p at the earlier of the two first differences; and adding k to
// both moves no comparison of exponents.
var MonomialLexOrder = monomialLexOrderThm{family.Add(registry.ProofEntry{
	Name: "MonomialLexOrder",
	Key:  "prop_296bc1e7e19e761f",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(num → D).",
		Conclusion: "(∀m:(D → num). ¬«lex»(m, m)) ∧ " +
			"(∀m n p:(D → num). «lex»(m, n) ∧ «lex»(n, p) ⇒ «lex»(m, p)) ∧ " +
			"(∀m n k:(D → num). «lex»(m, n) ⇒ «lex»(λx:D. m(x) + k(x), λx:D. n(x) + k(x)))",
	},
		func(a *Argument, ι *Arrow[Nat, D]) {
			irreflexive := a.Have(
				"no monomial comes before itself, which would put an exponent below itself",
				"∀m:(D → num). ¬«lex»(m, m)",
				ByArith())
			transitive := a.Have(
				"coming before is transitive",
				"∀m n p:(D → num). «lex»(m, n) ∧ «lex»(n, p) ⇒ «lex»(m, p)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m")
					b.FixAs[Fun[D, Nat]]("n")
					b.FixAs[Fun[D, Nat]]("p")
					steps := b.Conjuncts(
						b.Assume(),
						"m comes before n",
						"n comes before p")
					i, first := b.UnpackAs[Nat](steps[0], "i")
					k, second := b.UnpackAs[Nat](steps[1], "k")
					mn := b.Conjuncts(
						first,
						"m is below n at ι(i)",
						"m agrees with n before i")
					np := b.Conjuncts(
						second,
						"n is below p at ι(k)",
						"n agrees with p before k")
					b.Cases(b.TermAs[Bool]("k < i"))
					b.When(
						"n first differs from p before m first differs from n: m first differs from p at k",
						func(c *Argument, kFirst Fact) {
							c.Take(k)
							c.Show(
								"m agrees with n up to k, where n is below p",
								SplitConj(
									Case(
										"at ι(k), m equals n, which is below p",
										ByArith(kFirst, mn[1].At(k), np[0])),
									Case(
										"before k, m agrees with n and n with p",
										Derive(func(d *Argument) {
											j := d.FixAs[Nat]("j")
											earlier := d.Assume()
											d.Show(
												"j is before k, so before i too",
												ByArith(earlier, kFirst, mn[1].At(j), np[1].At(j)))
										}))))
						})
					b.Otherwise(
						"m first differs from n no later than n from p: m first differs from p at i",
						func(c *Argument, iFirst Fact) {
							below := c.Have(
								"at ι(i) n is at most p: below it when i = k, equal to it when i < k",
								"n(ι(i)) ≤ p(ι(i))",
								Derive(func(d *Argument) {
									d.Cases(d.TermAs[Bool]("i = k"))
									d.When(
										"at i = k, n is below p",
										func(e *Argument, same Fact) {
											e.Show(
												"by the first difference of n and p",
												ByArith(same, np[0]))
										})
									d.Otherwise(
										"before k, n agrees with p",
										func(e *Argument, other Fact) {
											e.Show(
												"since i is below k",
												ByArith(iFirst, other, np[1].At(i)))
										})
								}))
							c.Take(i)
							c.Show(
								"m is below n, which is at most p, at ι(i)",
								SplitConj(
									Case(
										"at ι(i), m is below n, which is at most p",
										ByArith(below, mn[0])),
									Case(
										"before i, m agrees with n and n with p",
										Derive(func(d *Argument) {
											j := d.FixAs[Nat]("j")
											earlier := d.Assume()
											d.Show(
												"j is before i, so before k too",
												ByArith(earlier, iFirst, mn[1].At(j), np[1].At(j)))
										}))))
						})
				}))
			additive := a.Have(
				"adding a monomial k to both keeps where m and n first differ, and which of them is below there",
				"∀m n k:(D → num). «lex»(m, n) ⇒ «lex»(λx:D. m(x) + k(x), λx:D. n(x) + k(x))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m")
					b.FixAs[Fun[D, Nat]]("n")
					b.FixAs[Fun[D, Nat]]("k")
					i, first := b.UnpackAs[Nat](b.Assume(), "i")
					b.Take(i)
					b.Show(
						"adding k(ι(j)) to both exponents moves no comparison",
						ByArith(first))
				}))
			a.Show(
				"so the order is strict, and adding a monomial keeps it",
				By(irreflexive, transitive, additive))
		}),
})}

// MonomialLexTrichotomy — two monomials whose variables ι lists are equal,
// or one of them comes before the other: where they differ they differ at
// some ι(i), at a least such i by well-ordering, and the one with the
// smaller exponent there comes first.
var MonomialLexTrichotomy = monomialLexTrichotomyThm{family.Add(registry.ProofEntry{
	Name: "MonomialLexTrichotomy",
	Key:  "prop_f87965122126b532",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(num → D). ∀m n:(D → num).",
		Hypotheses: []string{
			"fun_support(0, m) ⊆ image(ι, 𝕌)",
			"fun_support(0, n) ⊆ image(ι, 𝕌)",
		},
		Conclusion: "m = n ∨ «lex»(m, n) ∨ «lex»(n, m)",
	},
		func(a *Argument, ι *Arrow[Nat, D], m, n *Arrow[D, Nat], mListed, nListed Fact) {
			distinct := a.Unless(
				a.TermAs[Bool]("m = n"),
				"settled when m = n",
				Given(func(b *Argument, same Fact) {
					b.Show(
						"m = n is the first of the three",
						By(Normalized, same))
				}))
			differ := a.Have(
				"m and n differ at a variable of one of them, which is some ι(i)",
				"∃i:num. m(ι(i)) ≠ n(ι(i))",
				BySets(distinct, mListed, nListed))
			_, least := a.ObtainAs[Nat](
				"so they differ at ι(i) for a least such i",
				"∃i:num. m(ι(i)) ≠ n(ι(i)) ∧ (∀j:num. j < i ⇒ m(ι(j)) = n(ι(j)))",
				By(differ, nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λi:num. m(ι(i)) ≠ n(ι(i))"))))
			parts := a.Conjuncts(
				least,
				"m and n differ at ι(i)",
				"and agree before i")
			a.Cases(a.TermAs[Bool]("m(ι(i)) < n(ι(i))"))
			a.When(
				"m is below n at ι(i), so m comes first",
				func(b *Argument, below Fact) {
					b.Show(
						"m comes before n",
						By(below, parts[1]))
				})
			a.Otherwise(
				"n is below m at ι(i), so n comes first",
				func(b *Argument, notBelow Fact) {
					above := b.Have(
						"n is below m at ι(i), the two differing there",
						"n(ι(i)) < m(ι(i))",
						ByArith(notBelow, parts[0]))
					b.Show(
						"n comes before m",
						By(above, parts[1]))
				})
		}),
})}

// MonomialLexGreatest — a finite nonempty set of monomials whose
// variables ι lists has a greatest monomial in the lexicographic order
// along ι. Were there none, each monomial of F would have a later one in
// F, two of them always being comparable (MonomialLexTrichotomy), and a
// finite set where every point is followed by another under a strict
// order is empty (finite_set.FiniteTransitivityChain).
var MonomialLexGreatest = monomialLexGreatestThm{family.Add(registry.ProofEntry{
	Name: "MonomialLexGreatest",
	Key:  "prop_a76bf40e6661af13",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(num → D). ∀F:set(D → num).",
		Hypotheses: []string{
			"finite(F)",
			"F ≠ ∅",
			"∀m:(D → num). m ∈ F ⇒ fun_support(0, m) ⊆ image(ι, 𝕌)",
		},
		Conclusion: "∃μ:(D → num). μ ∈ F ∧ (∀m:(D → num). m ∈ F ⇒ m = μ ∨ «lex»(m, μ))",
	},
		func(a *Argument, ι *Arrow[Nat, D], F *Expr[Set[Fun[D, Nat]]], finite, nonempty, listed Fact) {
			none := a.SupposeNot()
			successor := a.Have(
				"then every monomial of F has a later one in F",
				"∀x:(D → num). x ∈ F ⇒ ∃y:(D → num). y ∈ F ∧ «lex»(x, y)",
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[D, Nat]]("x")
					xIn := b.Assume()
					y, other := b.ObtainAs[Fun[D, Nat]](
						"x is not the greatest, so some y of F is neither x nor before x",
						"∃y:(D → num). y ∈ F ∧ y ≠ x ∧ ¬«lex»(y, x)",
						By(none, xIn))
					parts := b.Conjuncts(
						other,
						"y lies in F",
						"y is not x",
						"and y does not come before x")
					b.Take(y)
					b.Show(
						"of two distinct monomials of F one comes first, so x comes before y",
						By(
							xIn,
							parts[0],
							parts[1],
							parts[2],
							listed.At(x),
							listed.At(y),
							MonomialLexTrichotomy.At(ι, x, y)))
				}))
			order := a.Conjuncts(
				MonomialLexOrder.At(ι),
				"no monomial comes before itself",
				"coming before is transitive",
				"adding a monomial keeps the order")
			a.Show(
				"but a finite set where every point has a later one under a strict order is empty, and F is not",
				By(
					finite,
					nonempty,
					order[0],
					order[1],
					successor,
					finite_set.FiniteTransitivityChain.At(a.TermAs[Fun2[Fun[D, Nat], Fun[D, Nat], Bool]]("«lex»"), F)))
		}),
})}

// ---------------------------------------------------------------------------
// The leading term of a product
// ---------------------------------------------------------------------------

// PolynomialAlgebraLeadingCoefficientMul — for a strict order on the
// monomials that adding a monomial keeps, the coefficient of a product
// of polynomials at the sum of the greatest monomial μ where f is nonzero
// and the greatest ν where g is nonzero is f(μ) · g(ν). The coefficient
// is the sum over the pairs (m₁, m₂) with f(m₁) and g(m₂) nonzero that
// add up to μ + ν (PolynomialAlgebraMulPairs), and (μ, ν) is the only
// such pair: were m₁ before μ, adding m₂, which is at most ν, would put
// μ + ν before itself.
var PolynomialAlgebraLeadingCoefficientMul = polynomialAlgebraLeadingCoefficientMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraLeadingCoefficientMul",
	Key:  "prop_9695b60675186817",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀lt:((D → num) → (D → num) → bool). " +
			"∀f g:((D → num) → A). " +
			"∀μ ν:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
			"∀m:(D → num). ¬lt(m, m)",
			"∀m n p:(D → num). lt(m, n) ∧ lt(n, p) ⇒ lt(m, p)",
			"∀m n k:(D → num). lt(m, n) ⇒ lt(λx:D. m(x) + k(x), λx:D. n(x) + k(x))",
			"μ ∈ fun_support(R.zero, f)",
			"ν ∈ fun_support(R.zero, g)",
			"∀m:(D → num). m ∈ fun_support(R.zero, f) ⇒ m = μ ∨ lt(m, μ)",
			"∀m:(D → num). m ∈ fun_support(R.zero, g) ⇒ m = ν ∨ lt(m, ν)",
		},
		Conclusion: "polynomial_algebra_mul(R, f, g, λx:D. μ(x) + ν(x)) = f(μ) * g(ν)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			lt *Arrow2[Fun[D, Nat], Fun[D, Nat], Bool],
			f, g *Arrow[Fun[D, Nat], A],
			μ, ν *Arrow[D, Nat],
			ring, fIn, gIn, irreflexive, transitive, additive, μIn, νIn, leadF, leadG Fact,
		) {
			fFacts := a.Conjuncts(
				a.Have(
					"f is nonzero at finitely many monomials, all of S, and its coefficients lie in R",
					"finite(fun_support(R.zero, f)) ∧ "+
						"fun_support(R.zero, f) ⊆ monomials(S) ∧ "+
						"(∀m:(D → num). f(m) ∈ R.carrier)",
					By(fIn, PolynomialAlgebraMember.At(R, S, f))),
				"f is nonzero at finitely many monomials",
				"all of them monomials of S",
				"the coefficients of f lie in R")
			gFacts := a.Conjuncts(
				a.Have(
					"g is nonzero at finitely many monomials, all of S, and its coefficients lie in R",
					"finite(fun_support(R.zero, g)) ∧ "+
						"fun_support(R.zero, g) ⊆ monomials(S) ∧ "+
						"(∀m:(D → num). g(m) ∈ R.carrier)",
					By(gIn, PolynomialAlgebraMember.At(R, S, g))),
				"g is nonzero at finitely many monomials",
				"all of them monomials of S",
				"the coefficients of g lie in R")
			sum := a.TermAs[Fun[D, Nat]]("λx:D. μ(x) + ν(x)")
			monomials := a.Have(
				"μ and ν are monomials of S",
				"μ ∈ monomials(S) ∧ ν ∈ monomials(S)",
				BySets(μIn, νIn, fFacts[1], gFacts[1]))
			finiteSum := a.Have(
				"so μ + ν is a monomial of S, nonzero at finitely many variables",
				"finite_support(0, λx:D. μ(x) + ν(x))",
				By(
					monomials,
					MonomialAddIn.At(S, μ, ν),
					MonomialsMember.At(S, sum),
					function_module.FiniteSupportDef))
			commute := a.Have(
				"adding monomials commutes, exponent by exponent",
				"∀p q:(D → num). (λx:D. p(x) + q(x)) = (λx:D. q(x) + p(x))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("p")
					b.FixAs[Fun[D, Nat]]("q")
					b.Show(
						"p(x) + q(x) = q(x) + p(x) at every x",
						Funext(),
						ByArith())
				}))
			cancel := a.Have(
				"where two sums of monomials agree exponent by "+
					"exponent, equal first terms leave equal second terms",
				"∀p q r s:(D → num). (∀x:D. p(x) + q(x) = r(x) + s(x)) ∧ p = r ⇒ q = s",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("p")
					b.FixAs[Fun[D, Nat]]("q")
					b.FixAs[Fun[D, Nat]]("r")
					b.FixAs[Fun[D, Nat]]("s")
					parts := b.Conjuncts(
						b.Assume(),
						"p + q = r + s exponent by exponent",
						"and p = r")
					same := b.Have(
						"exponent by exponent p = r",
						"∀x:D. p(x) = r(x)",
						By(Normalized, parts[1]))
					b.Show(
						"so exponent by exponent q = s",
						Funext(),
						ByArith(parts[0], same))
				}))
			split := a.Have(
				"the only pair (m₁, m₂) with f(m₁), g(m₂) nonzero adding up to μ + ν is (μ, ν)",
				Statement{
					Binders: "∀m₁ m₂:(D → num).",
					Hypotheses: []string{
						"m₁ ∈ fun_support(R.zero, f)",
						"m₂ ∈ fun_support(R.zero, g)",
						"(λx:D. m₁(x) + m₂(x)) = (λx:D. μ(x) + ν(x))",
					},
					Conclusion: "m₁ = μ ∧ m₂ = ν",
				},
				Derive(func(b *Argument) {
					m1 := b.FixAs[Fun[D, Nat]]("m₁")
					m2 := b.FixAs[Fun[D, Nat]]("m₂")
					parts := b.Conjuncts(
						b.Assume(),
						"f is nonzero at m₁",
						"g is nonzero at m₂",
						"m₁ + m₂ = μ + ν")
					exponents := b.Have(
						"exponent by exponent, m₁ + m₂ = μ + ν",
						"∀x:D. m₁(x) + m₂(x) = μ(x) + ν(x)",
						By(Normalized, parts[2]))
					swapped := b.Have(
						"the same sums with their terms swapped: m₂ + m₁ = ν + μ",
						"∀x:D. m₂(x) + m₁(x) = ν(x) + μ(x)",
						ByArith(exponents))
					b.Cases(b.TermAs[Bool]("m₁ = μ"))
					b.When(
						"m₁ = μ, and then m₂ = ν",
						func(c *Argument, first Fact) {
							c.Show(
								"cancelling m₁ = μ from m₁ + m₂ = μ + ν",
								By(first, exponents, cancel.At(m1, m2, μ, ν)))
						})
					b.Otherwise(
						"m₁ ≠ μ cannot happen",
						func(c *Argument, other Fact) {
							before := c.Have(
								"m₁ is a monomial of f other than μ, so it comes before μ",
								"lt(m₁, μ)",
								By(Normalized, other, parts[0], leadF.At(m1)))
							beforeSecond := c.Have(
								"and m₂ ≠ ν, else cancelling it would leave m₁ = μ, so m₂ comes before ν",
								"lt(m₂, ν)",
								By(other, swapped, cancel.At(m2, m1, ν, μ), parts[1], leadG.At(m2)))
							shifted := c.Have(
								"adding μ keeps m₂ before ν: μ + m₂ comes before μ + ν",
								"lt(λx:D. μ(x) + m₂(x), λx:D. μ(x) + ν(x))",
								commute.At(μ, m2).Rw(),
								commute.At(μ, ν).Rw(),
								By(beforeSecond, additive.At(m2, ν, μ)))
							lifted := c.Have(
								"adding m₂ keeps m₁ before μ, and m₁ + m₂ is μ + ν: μ + ν comes before μ + m₂",
								"lt(λx:D. μ(x) + ν(x), λx:D. μ(x) + m₂(x))",
								By(Normalized, before, parts[2], additive.At(m1, μ, m2)))
							middle := c.TermAs[Fun[D, Nat]]("λx:D. μ(x) + m₂(x)")
							c.Show(
								"so μ + ν comes before itself, which no monomial does",
								By(lifted, shifted, transitive.At(sum, middle, sum), irreflexive.At(sum)))
						})
				}))
			pair := a.TermAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("(μ, ν)")
			only := a.Have(
				"so the pairs of the fibre over μ + ν lie in {(μ, ν)}",
				"«fibre»(λx:D. μ(x) + ν(x)) ⊆ {(μ, ν)}",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					parts := b.Conjuncts(
						b.Assume(),
						"p pairs a monomial where f is nonzero with one where g is",
						"and its parts add up to μ + ν")
					b.Show(
						"so its first part is μ and its second ν",
						By(
							parts[0],
							parts[1],
							split.At(b.TermAs[Fun[D, Nat]]("fst(p)"), b.TermAs[Fun[D, Nat]]("snd(p)")),
							set_product.InCrossProjections.At(
								b.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
								b.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)"),
								p),
							pairs.PairEta.At(p),
							set_basic.InSing.At(p, pair)))
				}))
			among := a.Have(
				"and (μ, ν) is one of them",
				"(μ, ν) ∈ «fibre»(λx:D. μ(x) + ν(x))",
				By(μIn, νIn, pairs.Fst, pairs.Snd, set_product.InCross))
			a.Show(
				"the coefficient at μ + ν is the term of the one pair (μ, ν)",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «fibre»(λx:D. μ(x) + ν(x)), "+
								"    λp:prod(D → num, D → num). f(fst(p)) * g(snd(p)))"),
						"the coefficient of a product is the sum over the pairs adding up to the monomial",
						By(
							ring,
							fFacts[0],
							fFacts[2],
							gFacts[0],
							gFacts[2],
							finiteSum,
							function_module.FiniteSupportDef,
							PolynomialAlgebraMulPairs.At(R, f, g, sum))),
					FinalLeg(
						"a sum over at most the one pair (μ, ν), which it contains, is that pair's term",
						By(
							only,
							among,
							fFacts[2],
							gFacts[2],
							comm_ring.MulIn.Read(ring),
							pairs.Fst,
							pairs.Snd,
							module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
								a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«fibre»(λx:D. μ(x) + ν(x))"),
								pair,
								a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], A]](
									"λp:prod(D → num, D → num). f(fst(p)) * g(snd(p))")))),
				))
		}),
})}

// PolynomialAlgebraMulLeadingTerms — two nonzero polynomials f, g have
// monomials μ, ν where they are nonzero, at whose sum the coefficient of
// their product is f(μ) · g(ν): μ and ν are the greatest monomials of f
// and of g in the lexicographic order along a sequence ι through the
// finitely many variables of their monomials.
var PolynomialAlgebraMulLeadingTerms = polynomialAlgebraMulLeadingTermsThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulLeadingTerms",
	Key:  "prop_e6d04454bf0d0cca",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀f g:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
			"f ≠ fun_zero(R.zero)",
			"g ≠ fun_zero(R.zero)",
		},
		Conclusion: "∃μ ν:(D → num). " +
			"    f(μ) ≠ R.zero ∧ " +
			"    g(ν) ≠ R.zero ∧ " +
			"    polynomial_algebra_mul(R, f, g, λx:D. μ(x) + ν(x)) = f(μ) * g(ν)",
		Abbrev: Abbrev{
			{Name: "variableSets", Text: "image(λm:(D → num). fun_support(0, m), " +
				"    fun_support(R.zero, f) ∪ fun_support(R.zero, g))"},
			{Name: "variables", Text: "⋃«variableSets»"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			f, g *Arrow[Fun[D, Nat], A],
			ring, fIn, gIn, fNonzero, gNonzero Fact,
		) {
			supports := a.Conjuncts(
				a.Have(
					"f and g are nonzero at finitely many monomials, all of them monomials of S",
					"finite(fun_support(R.zero, f)) ∧ "+
						"fun_support(R.zero, f) ⊆ monomials(S) ∧ "+
						"finite(fun_support(R.zero, g)) ∧ "+
						"fun_support(R.zero, g) ⊆ monomials(S)",
					By(fIn, gIn, PolynomialAlgebraMember.At(R, S, f), PolynomialAlgebraMember.At(R, S, g))),
				"f is nonzero at finitely many monomials",
				"all of them monomials of S",
				"g is nonzero at finitely many monomials",
				"all of them monomials of S")
			F := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)")
			G := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)")
			both := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f) ∪ fun_support(R.zero, g)")
			variablesOf := a.TermAs[Fun[Fun[D, Nat], Set[D]]]("λm:(D → num). fun_support(0, m)")
			variables := a.TermAs[Set[D]]("«variables»")
			each := a.Have(
				"each monomial of f or of g is nonzero at finitely many variables",
				"∀m:(D → num). m ∈ fun_support(R.zero, f) ∪ fun_support(R.zero, g) ⇒ finite(fun_support(0, m))",
				BySets(supports[1], supports[3], MonomialsMember))
			finitelyMany := a.Have(
				"so the variables of the monomials of f and g are finitely many",
				"finite(«variables»)",
				By(
					each,
					supports[0],
					supports[2],
					finite_set.FiniteUnions.At(a.TermAs[Set[Set[D]]]("«variableSets»")),
					finite_set.FiniteImage.At(variablesOf, both),
					finite_set.FiniteUnionImp.At(F, G),
					set_image.ForallInImage.At(variablesOf, both, a.TermAs[Set[Set[D]]]("λt:set(D). finite(t)"))))
			ι, runs := a.ObtainAs[Fun[Nat, D]](
				"so some sequence ι runs through all of them",
				"∃ι:(num → D). «variables» ⊆ image(ι, 𝕌)",
				By(finitelyMany, cardinal.CountableCover.At(variables), cardinal.FiniteCountable.At(variables)))
			listed := a.Conjuncts(
				a.Have(
					"the variables of each monomial of f, and of each of g, are among the ι(i)",
					"(∀m:(D → num). m ∈ fun_support(R.zero, f) ⇒ fun_support(0, m) ⊆ image(ι, 𝕌)) ∧ "+
						"(∀m:(D → num). m ∈ fun_support(R.zero, g) ⇒ fun_support(0, m) ⊆ image(ι, 𝕌))",
					BySets(runs)),
				"those of the monomials of f",
				"those of the monomials of g")
			nonempty := a.Conjuncts(
				a.Have(
					"f and g are nonzero at some monomial",
					"fun_support(R.zero, f) ≠ ∅ ∧ fun_support(R.zero, g) ≠ ∅",
					BySets(fNonzero, gNonzero, function_module.FunZeroDef)),
				"f is nonzero somewhere",
				"g is nonzero somewhere")
			μ, leadF := a.UnpackAs[Fun[D, Nat]](
				GroupPremises(supports[0], nonempty[0], listed[0], MonomialLexGreatest.At(ι, F)),
				"μ")
			ν, leadG := a.UnpackAs[Fun[D, Nat]](
				GroupPremises(supports[2], nonempty[1], listed[1], MonomialLexGreatest.At(ι, G)),
				"ν")
			lex := a.TermAs[Fun2[Fun[D, Nat], Fun[D, Nat], Bool]]("«lex»")
			order := a.Conjuncts(
				MonomialLexOrder.At(ι),
				"no monomial comes before itself",
				"coming before is transitive",
				"adding a monomial keeps the order")
			a.Take(μ)
			a.Take(ν)
			a.Show(
				"f is nonzero at its greatest monomial μ, g at ν, and the coefficient at μ + ν is f(μ) · g(ν)",
				By(
					ring,
					fIn,
					gIn,
					leadF,
					leadG,
					order[0],
					order[1],
					order[2],
					functions.InFunSupport,
					PolynomialAlgebraLeadingCoefficientMul.At(R, S, lex, f, g, μ, ν)))
		}),
})}

// ---------------------------------------------------------------------------
// The domain
// ---------------------------------------------------------------------------

// PolynomialAlgebraDomain — the polynomials over an integral domain, in any
// set of variables, are an integral domain. They form a commutative ring
// (PolynomialAlgebraCommRingOn); the one polynomial is not zero, its
// coefficient at the monomial of the constants being R.one; and the
// product of two nonzero polynomials has a coefficient f(μ) · g(ν) of
// two nonzero factors (PolynomialAlgebraMulLeadingTerms), nonzero as R
// has no zero divisors, so the product is not zero.
var PolynomialAlgebraDomain = polynomialAlgebraDomainThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraDomain",
	Key:  "prop_99c6a32350cf3ffc",
	Reading: "That R has no zero divisors is load-bearing: the constants are a copy of R. S is " +
		"any set of variables, of any type and of any size: a polynomial is nonzero at finitely many " +
		"monomials, each of finitely many variables. At S = ∅ the polynomials are the constants. The " +
		"operations of the ring record do not read S, which enters through the carrier alone.",
	Build: family.Theorem("∀R:integral_domain_on(A). ∀S:set(D). "+
		"    integral_domain_on(polynomial_algebra_ring(R, S))",
		func(a *Argument, R integral_domain.IntegralDomainFact[on.R], S *Expr[Set[D]]) {
			ring := integral_domain.Ring.Read(R)
			record := a.TermAs[RingOps[A]]("R")
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			constants := a.TermAs[Fun[D, Nat]]("λx:D. 0")
			oneNonzero := a.Have(
				"the one polynomial is not zero: its coefficient at the "+
					"monomial of the constants is R.one, which is not R.zero",
				"polynomial_algebra_one⟨D:D⟩(R) ≠ fun_zero(R.zero)",
				By(
					Normalized,
					integral_domain.OneNotZero.Read(R),
					PolynomialAlgebraOneDef.At[A, D](record),
					free_module.DeltaAtDef.At(zero, one, constants, constants),
					function_module.FunZeroDef.At(zero, constants)))
			noZeroDivisors := a.Have(
				"a vanishing product of polynomials of S has a vanishing factor",
				Statement{
					Binders: "∀f g:((D → num) → A).",
					Hypotheses: []string{
						"f ∈ polynomial_algebra(R, S)",
						"g ∈ polynomial_algebra(R, S)",
						"polynomial_algebra_mul(R, f, g) = fun_zero(R.zero)",
					},
					Conclusion: "f = fun_zero(R.zero) ∨ g = fun_zero(R.zero)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[Fun[D, Nat], A]]("f")
					g := b.FixAs[Fun[Fun[D, Nat], A]]("g")
					hypotheses := b.Assume()
					neither := b.SupposeNot()
					_, _, leading := b.Obtain2As[Fun[D, Nat], Fun[D, Nat]](
						"were neither zero, the product's coefficient at the "+
							"sum of their leading monomials μ, ν would be f(μ) · g(ν)",
						"∃μ ν:(D → num). "+
							"    f(μ) ≠ R.zero ∧ "+
							"    g(ν) ≠ R.zero ∧ "+
							"    polynomial_algebra_mul(R, f, g, λx:D. μ(x) + ν(x)) = f(μ) * g(ν)",
						By(ring, hypotheses, neither, PolynomialAlgebraMulLeadingTerms.At(record, S, f, g)))
					b.Show(
						"but the product is zero, and so is each of its "+
							"coefficients, while f(μ) and g(ν) are nonzero members of R",
						By(
							hypotheses,
							leading,
							PolynomialAlgebraMember,
							function_module.FunZeroDef.At(zero, b.TermAs[Fun[D, Nat]]("λx:D. μ(x) + ν(x)")),
							integral_domain.NoZeroDivisors.Read(R).AsFact().At(b.TermAs[A]("f(μ)"), b.TermAs[A]("g(ν)"))))
				}))
			a.Show(
				"the polynomials of S form a commutative ring, which "+
					"with these two gives the three conditions of a domain",
				By(
					ring,
					PolynomialAlgebraCommRingOn.At(record, S),
					oneNonzero,
					noZeroDivisors,
					integral_domain.IntegralDomainOn.At(
						a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)"))))
		}),
})}
