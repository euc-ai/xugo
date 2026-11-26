// product.go — the product of two Dirichlet series as the series of the
// convolution, and what it gives for a completely multiplicative
// coefficient: the series of log n · f(n) as a product, the derivative of
// the series of f as minus that series times the series of Λ(n)·f(n), and
// the series of f as the exponential of a Dirichlet series, so that it
// does not vanish.

package dirichlet_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// DirichletProduct — the product of two absolutely convergent Dirichlet
// series is the Dirichlet series of the convolution of their
// coefficients.
var DirichletProduct = dirichletProductThm{family.Add(registry.ProofEntry{
	Name: "DirichletProduct",
	Key:  "prop_94bd4679fbaf9ec5",
	Build: family.Sections(Statement{
		Binders: "∀a b:(num → complex). ∀σ t u:real. ∀s:complex.",
		Hypotheses: []string{
			"real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			"real_sums(λn:num. |b(n + 1)| * real_rpow(&(n + 1), -σ), u)",
			"σ ≤ re(s)",
		},
		Conclusion: "dirichlet_sums(dirichlet_convolution(a, b), " +
			"    s, " +
			"    dirichlet_series(a, s) * dirichlet_series(b, s))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			finiteFibre := ctx.Lemma(
				"∀k:num. finite({p:prod(num, num) | (fst(p) + 1) * (snd(p) + 1) - 1 = k})",
				func(arg *Argument, k *Expr[Nat]) {
					F, fibreDef := arg.LetAs[Set[Prod[Nat, Nat]]](
						"F", "{p:prod(num, num) | (fst(p) + 1) * (snd(p) + 1) - 1 = k}")
					I, intervalDef := arg.LetAs[Set[Nat]]("I", "{i:num | i ≤ k}")
					subset := arg.Have(
						"both coordinates of every fibre member are at most k",
						"F ⊆ set_cross(I, I)",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(d *Argument) {
							p := d.FixAs[Prod[Nat, Nat]]("p")
							inF := d.Assume()
							index := d.Have(
								"the pair lies in the fibre at k",
								"(fst(p) + 1) * (snd(p) + 1) - 1 = k",
								BySets(fibreDef, inF))
							m, n := d.TermAs[Nat]("fst(p) + 1"), d.TermAs[Nat]("snd(p) + 1")
							bounds := d.Have(
								"each index is bounded because the other factor is positive",
								"fst(p) ≤ k ∧ snd(p) ≤ k",
								ByArith(index, nat_order.LessEqSelfMul.At(m, n), nat_order.LessEqSelfMul.At(n, m)))
							d.Show(
								"the pair is in the bounded rectangle",
								BySets(intervalDef, bounds, set_product.InCrossProjections.At(I, I, p)))
						}))
					finite := arg.Have(
						"I is finite",
						"finite(I)",
						Simp(Fwd(intervalDef)),
						By(num_segment.FiniteBelow.At(k)))
					arg.Show(
						"the fibre is contained in a finite rectangle",
						By(
							finite,
							subset,
							finite_set.FiniteProduct.At(I, I),
							finite_set.FiniteSubset.At(F, arg.TermAs[Set[Prod[Nat, Nat]]]("set_cross(I, I)"))))
				})
			fibreConvolution := ctx.Lemma(
				"∀a b:(num → complex). ∀k:num. "+
					"    Σ_{p∈{p:prod(num, num) | (fst(p) + 1) * (snd(p) + 1) - 1 = k}} a(fst(p) + 1) * "+
					"    b(snd(p) + 1) = "+
					"    dirichlet_convolution(a, b, k + 1)",
				func(arg *Argument, _, _ *Arrow[Nat, Complex], k *Expr[Nat]) {
					arg.Do(Unfold(DirichletConvolutionDef))
					F, fibreDef := arg.LetAs[Set[Prod[Nat, Nat]]](
						"F", "{p:prod(num, num) | (fst(p) + 1) * (snd(p) + 1) - 1 = k}")
					D, divisorsDef := arg.LetAs[Set[Nat]]("D", "{d:num | d ∣ k + 1}")
					h, divisorDef := arg.LetAs[Fun[Prod[Nat, Nat], Nat]]("h", "λp:prod(num, num). fst(p) + 1")
					j, pairDef := arg.LetAs[Fun[Nat, Prod[Nat, Nat]]]("j", "λd:num. ,(d - 1, div(k + 1, d) - 1)")
					next := arg.TermAs[Nat]("k + 1")
					toPair := arg.Have(
						"each divisor determines a pair with that divisor as first factor",
						"∀d:num. d ∈ D ⇒ j(d) ∈ F ∧ h(j(d)) = d",
						Derive(func(c *Argument) {
							d := c.FixAs[Nat]("d")
							inD := c.Assume()
							divides := c.Have(
								"d divides k + 1",
								"d ∣ k + 1",
								BySets(divisorsDef, inD))
							cofactor := c.Have(
								"d and its quotient are positive and multiply to k + 1",
								"0 < d ∧ d * div(k + 1, d) = k + 1 ∧ 0 < div(k + 1, d)",
								ByArith(divides, nat_divides.DivisorQuotient.At(d, next)))
							successors := c.Have(
								"shifting the two positive factors back recovers them",
								"d - 1 + 1 = d ∧ div(k + 1, d) - 1 + 1 = div(k + 1, d)",
								ByArith(cofactor))
							index := c.Have(
								"shifted back, the two factors of the pair are d and its quotient, whose product is k + 1",
								"h(j(d)) * (snd(j(d)) + 1) - 1 = k",
								Simp(Fwd(pairDef), Fwd(divisorDef), Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(successors)),
								ByArith(cofactor))
							inF := c.Have(
								"the shifted divisor pair is in the fibre",
								"j(d) ∈ F",
								BySets(fibreDef, index))
							inverse := c.Have(
								"the first coordinate recovers the divisor",
								"h(j(d)) = d",
								Simp(Fwd(pairDef), Fwd(divisorDef), Fwd(pairs.Fst)),
								ByArith(cofactor))
							c.Show(
								"combine membership and the first factor",
								By(inF, inverse))
						}))
					toDivisor := arg.Have(
						"each fibre pair recovers a divisor and its quotient without changing the summand",
						Statement{
							Binders:    "∀p:prod(num, num).",
							Hypotheses: []string{"p ∈ F"},
							Conclusion: "h(p) ∈ D ∧ j(h(p)) = p ∧ a(h(p)) * b(div(k + 1, h(p))) = a(h(p)) * b(snd(p) + 1)",
						},
						Derive(func(c *Argument) {
							p := c.FixAs[Prod[Nat, Nat]]("p")
							inF := c.Assume()
							first, second := c.TermAs[Nat]("h(p)"), c.TermAs[Nat]("snd(p) + 1")
							index := c.Have(
								"the pair lies in the fibre",
								"h(p) * (snd(p) + 1) - 1 = k",
								BySets(fibreDef, inF))
							positive := c.Have(
								"the first factor is positive",
								"0 < h(p)",
								Simp(Fwd(divisorDef)),
								ByArith())
							exact := c.Have(
								"the two factors multiply to k + 1",
								"h(p) * (snd(p) + 1) = k + 1",
								ByArith(positive, index))
							quotient := c.Have(
								"the second factor is the quotient",
								"div(k + 1, h(p)) = snd(p) + 1",
								Simp(Rev(exact)),
								ByArith(positive, nat_div_mod.DivMult.At(first, second)))
							divides := c.Have(
								"the first factor divides k + 1",
								"h(p) ∣ k + 1",
								Simp(Rev(exact)),
								By(nat_divides.DividesOwnMultiple.At(first, second)))
							inD := c.Have(
								"the first factor is in D",
								"h(p) ∈ D",
								BySets(divisorsDef, divides))
							inverse := c.Have(
								"the divisor and quotient recover the pair",
								"j(h(p)) = p",
								Simp(Fwd(pairDef), Fwd(quotient)),
								Simp(Fwd(divisorDef), Fwd(nat_monus.AddSubCancel)),
								By(pairs.PairEta.At(p)))
							term := c.Have(
								"the quotient preserves the summand",
								"a(h(p)) * b(div(k + 1, h(p))) = a(h(p)) * b(snd(p) + 1)",
								Simp(Fwd(quotient)),
								Refl())
							c.Show(
								"combine membership, the inverse, and the summand identity",
								By(inD, inverse, term))
						}))
					addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
					arg.Show(
						"reindex the fibre sum by the divisors",
						By(
							toPair,
							toDivisor,
							monoidal.Reindex.Read(addition).At(
								F, D,
								arg.TermAs[Fun[Prod[Nat, Nat], Complex]]("λp:prod(num, num). a(h(p)) * b(snd(p) + 1)"),
								arg.TermAs[Fun[Nat, Complex]]("λd:num. a(d) * b(div(k + 1, d))"), h, j)))
				})
			return ctx.Theorem(headline, func(
				arg *Argument,
				a, b *Arrow[Nat, Complex],
				σ, t, u *Expr[Real],
				s *Expr[Complex],
				atSigmaA, atSigmaB, right Fact,
			) {
				x, xDef := arg.LetAs[Fun[Nat, Complex]]("x", "λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
				y, yDef := arg.LetAs[Fun[Nat, Complex]]("y", "λn:num. b(n + 1) * complex_cpow(&(n + 1), -s)")
				U, productDef := arg.LetAs[Fun[Nat, Fun[Nat, Complex]]]("U", "λm:num. λn:num. x(m) * y(n)")
				φ, indexDef := arg.LetAs[Fun[Nat, Fun[Nat, Nat]]]("φ", "λm:num. λn:num. (m + 1) * (n + 1) - 1")
				P, xModuli := arg.ObtainAs[Real](
					"the moduli of the first factor sum",
					"∃P:real. real_sums(λn:num. |x(n)|, P)",
					Simp(Fwd(xDef)),
					By(atSigmaA, right, AbsolutelySummableRight.At(a, σ, t, s)))
				Q, yModuli := arg.ObtainAs[Real](
					"the moduli of the second factor sum",
					"∃Q:real. real_sums(λn:num. |y(n)|, Q)",
					Simp(Fwd(yDef)),
					By(atSigmaB, right, AbsolutelySummableRight.At(b, σ, u, s)))
				R, rowDef := arg.LetAs[Fun[Nat, Real]]("R", "λm:num. Q * |x(m)|")
				rowModuli := arg.Have(
					"the sum of the moduli in each row is R(m)",
					"∀m:num. real_sums(λn:num. |U(m, n)|, R(m))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("m")
						c.Show(
							"scale the modulus sum of the second factor by the first",
							Simp(Fwd(productDef), Fwd(rowDef), Fwd(complex_abs.AbsMul)),
							ByArith(
								yModuli,
								real_series.SumsScale.At(
									c.TermAs[Fun[Nat, Real]]("λn:num. |y(n)|"), Q, c.TermAs[Real]("|x(m)|"))))
					}))
				totalModuli := arg.Have(
					"the sum of the row moduli is the product of the two modulus sums",
					"real_sums(R, Q * P)",
					Simp(Fwd(rowDef)),
					By(xModuli, real_series.SumsScale.At(arg.TermAs[Fun[Nat, Real]]("λn:num. |x(n)|"), P, Q)))
				finite := arg.Have(
					"the multiplicative index has finite fibres",
					"∀k:num. finite({p:prod(num, num) | φ(fst(p), snd(p)) = k})",
					Simp(Fwd(indexDef)),
					By(finiteFibre))
				p, xSum := arg.UnpackAs[Complex](
					GroupPremises(xModuli, complex_series.AbsoluteConvergence.At(x, P)), "p")
				q, ySum := arg.UnpackAs[Complex](
					GroupPremises(yModuli, complex_series.AbsoluteConvergence.At(y, Q)), "q")
				r, S, regrouped := arg.Unpack2As[Fun[Nat, Complex], Complex](
					GroupPremises(
						rowModuli,
						totalModuli,
						finite,
						complex_series.DoubleSeriesRegroup.At(U, φ, R, arg.TermAs[Real]("Q * P"))),
					"r", "S")
				groupedTerms := "λk:num. Σ_{i∈{i:prod(num, num) | φ(fst(i), snd(i)) = k}} U(fst(i), snd(i))"
				parts := arg.Conjuncts(
					regrouped,
					"∀m:num. complex_sums(λn:num. U(m, n), r(m))",
					"complex_sums(r, S)",
					"complex_sums("+groupedTerms+", S)")
				scaledRow := arg.Have(
					"each complex row sums to its first factor times q",
					"∀m:num. complex_sums(λn:num. U(m, n), x(m) * q)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("m")
						c.Show(
							"scale the second series by the first term",
							Simp(Fwd(productDef)),
							By(ySum, complex_series.SumsScale.At(y, q, c.TermAs[Complex]("x(m)"))))
					}))
				rows := arg.Have(
					"uniqueness identifies the row sum function",
					"r = (λm:num. q * x(m))",
					Funext(),
					Derive(func(c *Argument) {
						m := c.FixAs[Nat]("m")
						c.Show(
							"compare the two sums of the same row",
							ByArith(
								At(parts[0], m),
								scaledRow.At(m),
								complex_series.SumsUnique.At(
									c.TermAs[Fun[Nat, Complex]]("λn:num. U(m, n)"),
									c.TermAs[Complex]("r(m)"),
									c.TermAs[Complex]("x(m) * q"))))
					}))
				iterated := arg.Have(
					"summing the row sums scales the first series by q",
					"complex_sums(r, q * p)",
					Simp(Fwd(rows)),
					By(xSum, complex_series.SumsScale.At(x, p, q)))
				total := arg.Have(
					"the regrouped sum is the product of p and q",
					"S = p * q",
					ByArith(parts[1], iterated, complex_series.SumsUnique.At(r, S, arg.TermAs[Complex]("q * p"))))
				valueA := arg.Have(
					"the first Dirichlet series has value p",
					"dirichlet_series(a, s) = p",
					By(arg.Simplified(xSum, Fwd(xDef)), DirichletSumsDef.At(a, s, p), DirichletSeriesValue.At(a, s, p)))
				valueB := arg.Have(
					"the second Dirichlet series has value q",
					"dirichlet_series(b, s) = q",
					By(arg.Simplified(ySum, Fwd(yDef)), DirichletSumsDef.At(b, s, q), DirichletSeriesValue.At(b, s, q)))
				w, weightDef := arg.LetAs[Fun[Nat, Complex]]("w", "λd:num. complex_cpow(&d, -s)")
				A, aWeighted := arg.LetAs[Fun[Nat, Complex]]("A", "λd:num. w(d) * a(d)")
				B, bWeighted := arg.LetAs[Fun[Nat, Complex]]("B", "λd:num. w(d) * b(d)")
				multiplicative := arg.Have(
					"the complex power weight is multiplicative on positive indices",
					"∀m n:num. 0 < m ∧ 0 < n ⇒ w(m * n) = w(m) * w(n)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("m")
						c.FixAs[Nat]("n")
						positive := c.Assume()
						c.Show(
							"split the complex power of a product of positive reals",
							Simp(Fwd(weightDef), Fwd(real_construction.OfNumMul)),
							ByArith(
								positive,
								complex_cpow.CpowMulPositive.At(
									c.TermAs[Real]("&m"), c.TermAs[Real]("&n"), c.TermAs[Complex]("-s"))))
					}))
				terms := arg.Have(
					"the product array multiplies the weighted coefficients",
					"∀m n:num. U(m, n) = A(m + 1) * B(n + 1)",
					StripQuant(),
					Simp(Fwd(productDef), Fwd(xDef), Fwd(yDef), Fwd(aWeighted), Fwd(bWeighted), Fwd(weightDef)),
					ByArith())
				convolution := arg.Have(
					"grouping by the multiplicative index gives the convolution of the weighted coefficients",
					"("+groupedTerms+") = (λk:num. dirichlet_convolution(A, B, k + 1))",
					Funext(),
					Derive(func(c *Argument) {
						k := c.FixAs[Nat]("k")
						c.Show(
							"apply the fibre identity for the two weighted sequences",
							Simp(Fwd(indexDef), Fwd(terms)),
							By(At(fibreConvolution, A, B, k)))
					}))
				untwisted := arg.Have(
					"the convolution of the weighted coefficients is the weighted convolution",
					"(λk:num. dirichlet_convolution(A, B, k + 1)) = "+
						"(λk:num. dirichlet_convolution(a, b, k + 1) * complex_cpow(&(k + 1), -s))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("k")
						positive := c.Have(
							"the convolution index is a successor",
							"0 < k + 1",
							ByArith())
						twist := c.Have(
							"combine the weight at each divisor and quotient",
							"dirichlet_convolution(λd:num. w(d) * a(d), λd:num. w(d) * b(d), k + 1) = "+
								"w(k + 1) * dirichlet_convolution(a, b, k + 1)",
							By(multiplicative, positive, ConvolutionTwist.At(w, a, b, c.TermAs[Nat]("k + 1"))))
						c.Show(
							"read the weight at k + 1",
							Simp(Fwd(aWeighted), Fwd(bWeighted)),
							ByArith(twist, weightDef))
					}))
				sum := arg.Simplified(parts[2], Fwd(total), Fwd(untwisted), Fwd(convolution))
				arg.Show(
					"the Dirichlet sum of the convolution is the product of the factor values",
					Simp(Fwd(DirichletSumsDef), Fwd(valueA), Fwd(valueB)),
					By(sum))
			})
		}),
	Reading: "Absolute convergence of both factors at one real σ ≤ Re s is " +
		"asked; for conditionally convergent factors the product series can diverge.",
})}

// ConvolutionTwist — multiplying both sequences by a completely
// multiplicative f multiplies their convolution by f.
var ConvolutionTwist = convolutionTwistThm{family.Add(registry.ProofEntry{
	Name: "ConvolutionTwist",
	Key:  "prop_271bcfa4cf0c16f3",
	Build: family.Theorem(Statement{
		Binders: "∀f a b:(num → complex). ∀n:num.",
		Hypotheses: []string{
			"∀m k:num. 0 < m ∧ 0 < k ⇒ f(m * k) = f(m) * f(k)",
			"0 < n",
		},
		Conclusion: "dirichlet_convolution(λm:num. f(m) * a(m), λm:num. f(m) * b(m), n) = " +
			"f(n) * dirichlet_convolution(a, b, n)",
	}, func(arg *Argument, f, a, b *Arrow[Nat, Complex], n *Expr[Nat], multiplicative, positive Fact) {
		arg.Do(Unfold(DirichletConvolutionDef))
		D, divisorsDef := arg.LetAs[Set[Nat]]("D", "{d:num | d ∣ n}")
		p, twistedDef := arg.LetAs[Fun[Nat, Complex]](
			"p", "λd:num. (f(d) * a(d)) * (f(div(n, d)) * b(div(n, d)))")
		u, untwistedDef := arg.LetAs[Fun[Nat, Complex]]("u", "λd:num. a(d) * b(div(n, d))")
		finite := arg.Have(
			"D is finite, n being positive",
			"finite(D)",
			Simp(Fwd(divisorsDef)),
			By(positive, nat_divides.DivisorsFinite.At(n)))
		factor := arg.Have(
			"each twisted summand is f(n) times the untwisted summand",
			"∀d:num. d ∈ D ⇒ p(d) = f(n) * u(d)",
			Derive(func(c *Argument) {
				d := c.FixAs[Nat]("d")
				inD := c.Assume()
				c.Do(Simp(Fwd(twistedDef), Fwd(untwistedDef)))
				divisor := c.Have(
					"d is a divisor of n",
					"d ∣ n",
					BySets(divisorsDef, inD))
				quotient := c.TermAs[Nat]("div(n, d)")
				combined := c.Have(
					"d and its quotient are positive and multiply to n, so multiplicativity combines their factors",
					"f(d) * f(div(n, d)) = f(n)",
					By(
						Normalized,
						multiplicative.At(d, quotient),
						positive,
						divisor,
						nat_divides.DivisorQuotient.At(d, n)))
				c.Do(CalcEq(
					Leg(
						c.TermAs[Complex]("(f(d) * f(div(n, d))) * (a(d) * b(div(n, d)))"),
						"collect the two factors supplied by f",
						ByArith()),
					FinalLeg(
						"their product is f(n)",
						Simp(Fwd(combined)),
						Refl())))
			}))
		neutral := arg.Have(
			"multiplying by f(n) preserves the additive identity",
			"f(n) * neutral_elem(complex_add) = neutral_elem(complex_add)",
			Simp(Fwd(comm_ring.NeutralAdd.Read(complex_field.CommRing))),
			ByArith())
		distributes := arg.Have(
			"multiplying by f(n) preserves addition",
			"∀x y:complex. f(n) * (x + y) = f(n) * x + f(n) * y",
			By(At(comm_ring.LeftDistrib.Read(complex_field.CommRing), f.Apply(n))))
		addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		scale := arg.TermAs[Fun[Complex, Complex]]("λz:complex. f(n) * z")
		scaled := arg.TermAs[Fun[Nat, Complex]]("λd:num. f(n) * u(d)")
		arg.Do(CalcEq(
			Leg(
				arg.TermAs[Complex]("Σ_{d∈D} f(n) * u(d)"),
				"replace each twisted term by the scaled untwisted term",
				By(factor, monoidal.Congruence.Read(addition).At(D, p, scaled))),
			FinalLeg(
				"pull the common factor out of the finite sum",
				By(
					finite,
					distributes,
					neutral,
					addition,
					monoidal.Homomorphic.Read(addition).At(arg.TermAs[Op[Complex]]("complex_add"), scale, D, u)))))
	}),
	Reading: "f need be multiplicative only on positive " +
		"arguments: its value at 0 is never read for n > 0.",
})}

// LogSeriesProduct — for a completely multiplicative f bounded by 1 and
// Re s > 1, the Dirichlet series of log n · f(n) is the product of the
// series of f and the series of Λ(n)·f(n).
var LogSeriesProduct = logSeriesProductThm{family.Add(registry.ProofEntry{
	Name: "LogSeriesProduct",
	Key:  "prop_1d3b55e314141e8",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)",
			"∀n:num. |f(n)| ≤ &1",
			"&1 < re(s)",
		},
		Conclusion: "dirichlet_series(λn:num. &(log(&n)) * f(n), s) = " +
			"dirichlet_series(f, s) * dirichlet_series(λn:num. &(von_mangoldt(n)) * f(n), s)",
	},
		func(
			arg *Argument,
			f *Arrow[Nat, Complex],
			s *Expr[Complex],
			multiplicative, bounded, aboveOne Fact,
		) {
			σ := arg.TermAs[Real]("re(s)")
			M, mangoldtDef := arg.LetAs[Fun[Nat, Complex]]("M", "λn:num. &(von_mangoldt(n))")
			g, weightedDef := arg.LetAs[Fun[Nat, Complex]]("g", "λn:num. M(n) * f(n)")
			t, fModuli := arg.UnpackAs[Real](
				GroupPremises(bounded, aboveOne, BoundedAbsolutelySummable.At(f, arg.TermAs[Real]("&1"), σ)), "t")
			logBound := arg.Have(
				"the modulus of g(n + 1) is Λ(n + 1)·|f(n + 1)|, Λ "+
					"being nonnegative, and Λ is at most the logarithm",
				"∀n:num. |g(n + 1)| ≤ log(&(n + 1))",
				Derive(func(c *Argument) {
					c.FixAs[Nat]("n")
					next := c.TermAs[Nat]("n + 1")
					c.Show(
						"bound the Mangoldt factor and the factor f",
						Simp(Fwd(weightedDef), Fwd(mangoldtDef)),
						ByArith(
							bounded.At(next),
							prime_distribution.MangoldtNonneg.At(next),
							prime_distribution.MangoldtLessEqLog.At(next)))
				}))
			u, gModuli := arg.UnpackAs[Real](
				GroupPremises(logBound, aboveOne, LogBoundedAbsolutelySummable.At(g, σ)), "u")
			atRe := arg.Have(
				"comparison is at the real part of s",
				"re(s) ≤ re(s)",
				ByArith())
			product := arg.Have(
				"the convolution series sums to the product of the two factor values",
				"dirichlet_sums(dirichlet_convolution(g, f), s, dirichlet_series(g, s) * dirichlet_series(f, s))",
				By(fModuli, gModuli, atRe, DirichletProduct.At(g, f, σ, u, t, s)))

			one, oneDef := arg.LetAs[Fun[Nat, Complex]]("one", "λn:num. complex_of_real(&1)")
			logConvolution := arg.Have(
				"convolution of the Mangoldt coefficients with the constant one gives the logarithm",
				"∀n:num. 0 < n ⇒ dirichlet_convolution(M, one, n) = &(log(&n))",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					positive := c.Assume()
					D, divisorsDef := c.LetAs[Set[Nat]]("D", "{d:num | d ∣ n}")
					finite := c.Have(
						"the divisors of a positive n are finitely many",
						"finite(D)",
						Simp(Fwd(divisorsDef)),
						By(positive, nat_divides.DivisorsFinite.At(n)))
					identity := c.Have(
						"multiplication by the complex image of one fixes each term",
						"∀z:complex. z * complex_of_real(&1) = z",
						StripQuant(),
						ByArith())
					logarithm := c.Have(
						"the real sum of Λ over the divisors is log n",
						"Σ_{d∈D} von_mangoldt(d) = log(&n)",
						Simp(Fwd(divisorsDef)),
						By(positive, prime_distribution.MangoldtDivisorSum.At(n)))
					c.Show(
						"remove the unit factors and embed the real divisor sum",
						Simp(Fwd(DirichletConvolutionDef), Fwd(mangoldtDef), Fwd(oneDef), Fwd(identity)),
						Simp(Rev(divisorsDef)),
						By(
							Normalized,
							finite,
							logarithm,
							complex_field.OfRealSum.At(D, c.TermAs[Fun[Nat, Real]]("von_mangoldt"))))
				}))
			weightedLeft := arg.Have(
				"the twisted Mangoldt sequence is g",
				"(λd:num. f(d) * M(d)) = g",
				Simp(Fwd(weightedDef)),
				Funext(),
				StripQuant(),
				ByArith())
			weightedRight := arg.Have(
				"twisting the constant one gives f",
				"(λd:num. f(d) * one(d)) = f",
				Simp(Fwd(oneDef)),
				Funext(),
				StripQuant(),
				ByArith())
			logTerms := arg.Have(
				"the convolution coefficients at positive indices are log n times f(n)",
				"∀n:num. 0 < n ⇒ dirichlet_convolution(g, f, n) = &(log(&n)) * f(n)",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					positive := c.Assume()
					twist := c.Have(
						"multiplicativity moves f across convolution",
						"dirichlet_convolution(λd:num. f(d) * M(d), λd:num. f(d) * one(d), n) = "+
							"f(n) * dirichlet_convolution(M, one, n)",
						By(multiplicative, positive, ConvolutionTwist.At(f, M, one, n)))
					logarithm := c.Have(
						"evaluate the untwisted convolution",
						"dirichlet_convolution(M, one, n) = &(log(&n))",
						By(logConvolution.At(n), positive))
					c.Show(
						"substitute the twisted coefficients and the logarithm",
						ByArith(c.Simplified(twist, Fwd(weightedLeft), Fwd(weightedRight), Fwd(logarithm))))
				}))
			shiftedTerms := arg.Have(
				"every coefficient sampled by the Dirichlet series has the claimed value",
				"∀n:num. dirichlet_convolution(g, f, n + 1) = &(log(&(n + 1))) * f(n + 1)",
				Derive(func(c *Argument) {
					c.FixAs[Nat]("n")
					positive := c.Have(
						"a successor is positive",
						"0 < n + 1",
						ByArith())
					c.Show(
						"use the coefficient identity at the successor",
						By(logTerms.At(c.TermAs[Nat]("n + 1")), positive))
				}))
			logSeries := arg.Have(
				"the logarithm-weighted series has the convolution sum",
				"dirichlet_sums(λn:num. &(log(&n)) * f(n), s, dirichlet_series(g, s) * dirichlet_series(f, s))",
				Simp(Fwd(DirichletSumsDef)),
				By(arg.Simplified(product, Fwd(DirichletSumsDef), Fwd(shiftedTerms))))
			logCoefficients := arg.TermAs[Fun[Nat, Complex]]("λn:num. &(log(&n)) * f(n)")
			value := arg.TermAs[Complex]("dirichlet_series(g, s) * dirichlet_series(f, s)")
			equality := arg.Have(
				"the selected logarithm-weighted series value equals that sum",
				"dirichlet_series(λn:num. &(log(&n)) * f(n), s) = dirichlet_series(g, s) * dirichlet_series(f, s)",
				By(logSeries, DirichletSeriesValue.At(logCoefficients, s, value)))
			arg.Show(
				"commute the two Dirichlet series factors",
				ByArith(equality))
		}),
	Reading: "With DirichletSeriesDerivative this reads D(f)′ = −D(f)·D(Λ·f), " +
		"which LogarithmicDerivative states. It holds for the zero function too.",
})}

// LogarithmicDerivative — for a completely multiplicative f bounded by 1
// and Re s > 1, the derivative of the series of f is minus the series of f
// times the series of Λ(n)·f(n): the derivative is minus the series of
// log n · f(n), and that series is the product.
var LogarithmicDerivative = logarithmicDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LogarithmicDerivative",
	Key:  "prop_3adce52149dc8b6f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)",
			"∀n:num. |f(n)| ≤ &1",
			"&1 < re(s)",
		},
		Conclusion: "complex_derivative_at(λz:complex. dirichlet_series(f, z), " +
			"    s, " +
			"    -(dirichlet_series(f, s) * dirichlet_series(λn:num. &(von_mangoldt(n)) * f(n), s)))",
	}, func(
		arg *Argument,
		f *Arrow[Nat, Complex],
		s *Expr[Complex],
		multiplicative, bounded, aboveOne Fact,
	) {
		one := arg.TermAs[Real]("&1")
		absolute := arg.Have(
			"f is bounded by one, so its moduli are summable at every real exponent above one",
			"∀σ:real. &1 < σ ⇒ ∃t:real. real_sums(λn:num. |f(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			Derive(func(c *Argument) {
				σ := c.FixAs[Real]("σ")
				above := c.Assume()
				c.Show(
					"compare with the powers",
					By(bounded, above, BoundedAbsolutelySummable.At(f, one, σ)))
			}))
		derivative := arg.Have(
			"term by term, the derivative is minus the series of log n · f(n)",
			"complex_derivative_at(λz:complex. dirichlet_series(f, z), "+
				"    s, "+
				"    -dirichlet_series(λn:num. &(log(&n)) * f(n), s))",
			By(absolute, aboveOne, DirichletSeriesDerivative.At(f, one, s)))
		arg.Show(
			"the series of log n · f(n) is the product of the series of f and of Λ·f",
			By(derivative, multiplicative, bounded, aboveOne, LogSeriesProduct.At(f, s)))
	}),
	Reading: "Without dividing by the series of f: the series of Λ·f is minus the " +
		"logarithmic derivative of the series of f wherever that series does not vanish.",
})}

// LogarithmicSeries — for a completely multiplicative f with f(1) = 1 and
// bounded by 1, and Re s > 1, the Dirichlet series of f is the
// exponential of the series of Λ(n)/log n · f(n).
var LogarithmicSeries = logarithmicSeriesThm{family.Add(registry.ProofEntry{
	Name: "LogarithmicSeries",
	Key:  "prop_86710cd211f36a9c",
	Build: family.Sections(Statement{
		Binders: "∀f:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)",
			"f(1) = &1",
			"∀n:num. |f(n)| ≤ &1",
			"&1 < re(s)",
		},
		Conclusion: "dirichlet_series(f, s) = " +
			"exp(dirichlet_series(λn:num. &(von_mangoldt(n) / log(&n)) * f(n), s))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			ratioBounds := ctx.Lemma(
				"∀n:num. "+
					"    &0 ≤ von_mangoldt(n) / log(&n) ∧ "+
					"    von_mangoldt(n) / log(&n) ≤ &1 ∧ "+
					"    log(&n) * (von_mangoldt(n) / log(&n)) = von_mangoldt(n)",
				func(arg *Argument, n *Expr[Nat]) {
					zero := arg.Have(
						"Λ vanishes at zero",
						"von_mangoldt(0) = &0",
						Derive(func(c *Argument) {
							noPower := c.Have(
								"zero is no positive power of a prime",
								"¬(∃p k:num. nat_prime(p) ∧ 0 < k ∧ 0 = p ^ k)",
								Derive(func(d *Argument) {
									isPower := d.SupposeNot()
									p, k, power := d.Obtain2As[Nat, Nat](
										"then zero is a positive power p ^ k of a prime p",
										"∃p k:num. nat_prime(p) ∧ 0 < k ∧ 0 = p ^ k",
										By(isPower))
									parts := d.Conjuncts(
										power,
										"nat_prime(p)",
										"0 < k",
										"0 = p ^ k")
									d.Show(
										"a prime base is nonzero, so its power is nonzero",
										ByArith(parts[0], parts[2], nat_prime.PrimeAtLeastTwo.At(p), nat_arith.PowEqZero.At(p, k)))
								}))
							c.Show(
								"the defining test for a prime power is false",
								Simp(Fwd(prime_distribution.VonMangoldtDef), Fwd(noPower)),
								By(noPower))
						}))
					arg.Cases(arg.TermAs[Bool]("n = 0"))
					arg.When(
						"at zero both the quotient and Λ vanish",
						func(c *Argument, nZero Fact) {
							c.Show(
								"substitute zero and use the zero numerator",
								Simp(Fwd(nZero), Fwd(zero)),
								ByArith())
						})
					arg.Otherwise(
						"at a positive integer Λ lies between zero and the logarithm",
						func(c *Argument, nonzero Fact) {
							positive := c.Have(
								"n is positive",
								"0 < n",
								ByArith(nonzero))
							below := c.Have(
								"Λ is at most the logarithm",
								"von_mangoldt(n) ≤ log(&n)",
								By(positive, prime_distribution.MangoldtLessEqLog.At(n)))
							nonnegative := prime_distribution.MangoldtNonneg.At(n)
							c.Cases(c.TermAs[Bool]("&0 < log(&n)"))
							c.When(
								"a positive logarithm is a valid denominator",
								func(d *Argument, logPositive Fact) {
									L := d.TermAs[Real]("log(&n)")
									A := d.TermAs[Real]("von_mangoldt(n)")
									d.Show(
										"divide the bounds by the denominator and cancel it in the product",
										ByArith(
											nonnegative,
											below,
											logPositive,
											real_order_field.LessEqDivMulLeft.At(d.TermAs[Real]("&0"), A, L),
											real_order_field.LessEqDivMulRight.At(A, d.TermAs[Real]("&1"), L),
											field.DivRightMul.Read(real_field.Field).At(A, L)))
								})
							c.Otherwise(
								"a nonpositive logarithm forces Λ to vanish",
								func(d *Argument, notPositive Fact) {
									vanishes := d.Have(
										"Λ is squeezed to zero",
										"von_mangoldt(n) = &0",
										ByArith(nonnegative, below, notPositive))
									d.Show(
										"the zero numerator also makes the quotient zero",
										Simp(Fwd(vanishes)),
										ByArith())
								})
						})
				})
			realAxis := ctx.Lemma(
				Statement{
					Binders:    "∀a:(num → complex).",
					Hypotheses: []string{"∀n:num. |a(n)| ≤ &1"},
					Conclusion: "(λn:num. dirichlet_series(a, complex_of_real(&(n + 2)))) ⟶ a(1)",
				},
				func(arg *Argument, a *Arrow[Nat, Complex], bounded Fact) {
					arg.Do(Simp(Fwd(complex_topology.ComplexConvergesToDef)))
					eps := arg.FixAs[Real]("ε")
					positive := arg.Assume()
					c, tail := arg.ObtainAs[Real](
						"the real-axis tail stays within ε of the first coefficient",
						"∃c:real. ∀σ:real. c ≤ σ ⇒ |dirichlet_series(a, &σ) - a(1)| < ε",
						By(bounded, positive, DirichletSeriesAtInfinity.At(a, arg.TermAs[Real]("&1"), eps)))
					N, above := arg.ObtainAs[Nat](
						"choose a natural larger than the cutoff",
						"∃N:num. c < &N",
						By(real_archimedean.ExistsNumStrictlyAbove.At(c)))
					arg.Take(N)
					arg.FixAs[Nat]("n")
					past := arg.Assume()
					right := arg.Have(
						"the real argument is past the cutoff",
						"c ≤ &(n + 2)",
						ByArith(above, past))
					arg.Show(
						"apply the real-axis tail bound",
						By(tail.At(arg.TermAs[Real]("&(n + 2)")), right))
				})
			return ctx.Theorem(headline, func(
				arg *Argument,
				f *Arrow[Nat, Complex],
				s *Expr[Complex],
				multiplicative, firstOne, bounded, inHalfPlane Fact,
			) {
				g, gDef := arg.LetAs[Fun[Nat, Complex]]("g", "λn:num. &(von_mangoldt(n) / log(&n)) * f(n)")
				_, mangoldtDef := arg.LetAs[Fun[Nat, Complex]]("M", "λn:num. &(von_mangoldt(n)) * f(n)")
				F, fDef := arg.LetAs[Fun[Complex, Complex]]("F", "λz:complex. dirichlet_series(f, z)")
				G, seriesGDef := arg.LetAs[Fun[Complex, Complex]]("G", "λz:complex. dirichlet_series(g, z)")
				P, pDef := arg.LetAs[Fun[Complex, Complex]](
					"P", "λz:complex. -(dirichlet_series(f, z) * dirichlet_series(M, z))")
				Q, qDef := arg.LetAs[Fun[Complex, Complex]]("Q", "λz:complex. -dirichlet_series(M, z)")
				one := arg.TermAs[Real]("&1")
				oneComplex := arg.TermAs[Complex]("complex_of_real(&1)")
				boundedG := arg.Have(
					"the logarithm-normalized Mangoldt coefficients are bounded by one",
					"∀n:num. |g(n)| ≤ &1",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						ratio := c.TermAs[Real]("von_mangoldt(n) / log(&n)")
						bounds := c.Have(
							"the ratio lies between zero and one",
							"&0 ≤ von_mangoldt(n) / log(&n) ∧ von_mangoldt(n) / log(&n) ≤ &1",
							By(At(ratioBounds, n)))
						c.Show(
							"the coefficient magnitude is the product of two factors at most one",
							Simp(Fwd(gDef)),
							ByArith(bounds, bounded.At(n), complex_abs.AbsOfNonnegReal.At(ratio)))
					}))
				mangoldtOne := arg.Have(
					"Λ at one lies between 0 and log 1 = 0",
					"von_mangoldt(1) = &0",
					ByArith(
						prime_distribution.MangoldtNonneg.At(arg.TermAs[Nat]("1")),
						prime_distribution.MangoldtLessEqLog.At(arg.TermAs[Nat]("1")),
						real_exp_log.LogOne))
				firstZero := arg.Have(
					"the first coefficient of g is zero",
					"g(1) = complex_of_real(&0)",
					Simp(Fwd(gDef)),
					Simp(Fwd(mangoldtOne), Fwd(real_exp_log.LogOne)),
					Simp(Fwd(real_field.RealDivDef)),
					ByArith())
				absoluteG := arg.Have(
					"the moduli for g converge at every real exponent above one",
					"∀σ:real. &1 < σ ⇒ ∃t:real. real_sums(λn:num. |g(n + 1)| * real_rpow(&(n + 1), -σ), t)",
					Derive(func(c *Argument) {
						σ := c.FixAs[Real]("σ")
						above := c.Assume()
						c.Show(
							"apply comparison to the bounded coefficients",
							By(boundedG, above, BoundedAbsolutelySummable.At(g, one, σ)))
					}))
				termsG := arg.Have(
					"log n times the coefficients of g are the Mangoldt-weighted coefficients",
					"(λn:num. &(log(&n)) * g(n)) = M",
					Funext(),
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						cancellation := c.Have(
							"the real logarithmic factor recovers Λ",
							"log(&n) * (von_mangoldt(n) / log(&n)) = von_mangoldt(n)",
							By(At(ratioBounds, n)))
						embedded := c.Have(
							"the same cancellation holds after embedding into the complex field",
							"&(log(&n)) * &(von_mangoldt(n) / log(&n)) = &(von_mangoldt(n))",
							By(
								cancellation,
								complex_field.OfRealMul.At(
									c.TermAs[Real]("log(&n)"), c.TermAs[Real]("von_mangoldt(n) / log(&n)"))))
						c.Show(
							"group the two real factors before cancelling the logarithm",
							Simp(Fwd(gDef), Fwd(mangoldtDef)),
							CalcEq(
								Leg(
									c.TermAs[Complex]("(&(log(&n)) * &(von_mangoldt(n)/log(&n))) * f(n)"),
									"associate the logarithm with the ratio",
									ByArith()),
								FinalLeg(
									"substitute the cancellation",
									Simp(Fwd(embedded)),
									ByArith())))
					}))
				derivativeF := arg.Have(
					"P is the derivative of F throughout the half-plane",
					"∀z:complex. &1 < re(z) ⇒ complex_derivative_at(F, z, P(z))",
					Derive(func(c *Argument) {
						z := c.FixAs[Complex]("z")
						right := c.Assume()
						c.Show(
							"the logarithmic derivative of the series of f",
							Simp(Fwd(fDef), Fwd(pDef), Fwd(mangoldtDef)),
							By(multiplicative, bounded, right, LogarithmicDerivative.At(f, z)))
					}))
				derivativeG := arg.Have(
					"Q is the derivative of G throughout the half-plane",
					"∀z:complex. &1 < re(z) ⇒ complex_derivative_at(G, z, Q(z))",
					Derive(func(c *Argument) {
						z := c.FixAs[Complex]("z")
						right := c.Assume()
						c.Show(
							"the derivative of G is minus the series of log n · g(n), which is M",
							Simp(Fwd(seriesGDef), Fwd(qDef)),
							By(c.Simplified(
								GroupPremises(absoluteG, right, DirichletSeriesDerivative.At(g, one, z)),
								Fwd(termsG))))
					}))
				equation := arg.Have(
					"P is F times Q, the sign moved onto the second factor",
					"∀z:complex. &1 < re(z) ⇒ P(z) = F(z) * Q(z)",
					Derive(func(c *Argument) {
						c.FixAs[Complex]("z")
						c.Assume()
						c.Show(
							"−(F(z)·D(M)(z)) = F(z)·(−D(M)(z))",
							Simp(Fwd(pDef), Fwd(fDef), Fwd(qDef)),
							ByArith())
					}))
				C, multiple := arg.ObtainAs[Complex](
					"the differential equation gives a constant multiple of exp G on the half-plane",
					"∃C:complex. ∀z:complex. &1 < re(z) ⇒ F(z) = C * exp(G(z))",
					By(
						derivativeF,
						derivativeG,
						equation,
						complex_power_series.ExponentialOfPrimitive.At(F, G, P, Q, one)))

				X, xDef := arg.LetAs[Fun[Nat, Complex]]("X", "λn:num. F(complex_of_real(&(n + 2)))")
				Y, yDef := arg.LetAs[Fun[Nat, Complex]]("Y", "λn:num. G(complex_of_real(&(n + 2)))")
				xLimit := arg.Have(
					"F tends to its first coefficient one along the real axis",
					"X ⟶ complex_of_real(&1)",
					Simp(Fwd(xDef), Fwd(fDef)),
					By(bounded, firstOne, At(realAxis, f)))
				yLimit := arg.Have(
					"G tends to its first coefficient zero along the same axis",
					"Y ⟶ complex_of_real(&0)",
					Simp(Fwd(yDef), Fwd(seriesGDef)),
					By(boundedG, firstZero, At(realAxis, g)))
				exp := arg.TermAs[Fun[Complex, Complex]]("exp")
				zero := arg.TermAs[Complex]("complex_of_real(&0)")
				exponentLimit := arg.Have(
					"exp, differentiable and so continuous at zero, carries the limit zero of Y to exp(0) = 1",
					"(λn:num. exp(Y(n))) ⟶ complex_of_real(&1)",
					By(
						Normalized,
						yLimit,
						complex_power_series.ExpDerivative.At(zero),
						complex_derivative.DerivativeContinuous.At(
							exp, zero, arg.TermAs[Complex]("exp(complex_of_real(&0))")),
						complex_exp.ExpZero,
						complex_topology.ContinuousAtSequential.At(exp, zero, Y)))
				sequence := arg.Have(
					"the exponential formula holds along the sequence n + 2",
					"X = (λn:num. C * exp(Y(n)))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						z := c.TermAs[Complex]("complex_of_real(&(n + 2))")
						right := c.Have(
							"each real argument lies in the right half-plane",
							"&1 < re(complex_of_real(&(n + 2)))",
							ByArith(complex_field.PartsOfReal.At(c.TermAs[Real]("&(n + 2)"))))
						c.Show(
							"apply the exponential formula at n + 2",
							Simp(Fwd(xDef), Fwd(yDef)),
							By(right, multiple.At(z)))
					}))
				scaledLimit := arg.Have(
					"multiplying the exponential sequence by C multiplies its limit by C",
					"(λn:num. C * exp(Y(n))) ⟶ C * complex_of_real(&1)",
					By(
						exponentLimit,
						complex_topology.LimitConst.At(C),
						complex_topology.LimitMul.At(
							arg.TermAs[Fun[Nat, Complex]]("λn:num. C"),
							arg.TermAs[Fun[Nat, Complex]]("λn:num. exp(Y(n))"),
							C,
							oneComplex)))
				unit := arg.Have(
					"multiplication by one leaves C",
					"C * complex_of_real(&1) = C",
					ByArith())
				constantLimit := arg.Have(
					"the same sequence also tends to C",
					"X ⟶ C",
					Simp(Fwd(sequence)),
					By(arg.Simplified(scaledLimit, Fwd(unit))))
				normalized := arg.Have(
					"uniqueness of the limit fixes C to one",
					"C = complex_of_real(&1)",
					By(xLimit, constantLimit, complex_topology.LimitUnique.At(X, C, oneComplex)))
				atS := arg.Have(
					"apply the exponential formula at s",
					"F(s) = C * exp(G(s))",
					By(inHalfPlane, multiple.At(s)))
				arg.Show(
					"substitute C = 1 into the exponential formula",
					ByArith(atS, normalized))
			})
		}),
	Reading: "f(1) = 1 is needed: the zero function is completely multiplicative " +
		"and bounded, and its series is 0, not an exponential. So the series of such " +
		"an f never vanishes for Re s > 1; this replaces the Euler product. At n = 1 " +
		"the coefficient Λ(1)/log 1 is 0 times an unspecified inverse, which is 0.",
})}

// DirichletSeriesNonzero — for a completely multiplicative f with f(1) = 1
// and bounded by 1, the series of f has no zero in Re s > 1: there it is
// an exponential, and an exponential does not vanish.
var DirichletSeriesNonzero = dirichletSeriesNonzeroThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesNonzero",
	Key:  "prop_92471f9edaaca2e5",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)",
			"f(1) = &1",
			"∀n:num. |f(n)| ≤ &1",
			"&1 < re(s)",
		},
		Conclusion: "dirichlet_series(f, s) ≠ &0",
	}, func(
		arg *Argument,
		f *Arrow[Nat, Complex],
		s *Expr[Complex],
		multiplicative, firstOne, bounded, right Fact,
	) {
		arg.Show(
			"the series of f is the exponential of the logarithmic series, and an exponential is not zero",
			By(
				multiplicative,
				firstOne,
				bounded,
				right,
				LogarithmicSeries.At(f, s),
				complex_power_series.ExpNonzero))
	}),
})}
