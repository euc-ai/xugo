// binomial.go — the binomial theorem over ℝ: (x + y)ⁿ expanded by the
// binomial coefficients, carried into ℝ by the embedding.

package real_pow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The binomial theorem
// ---------------------------------------------------------------------------
//
// The proof is nat_num/binomial's Expansion read in ℝ: the same
// induction on the row, the same split of each term of row suc(n) by
// Pascal's rule into a share from above and a share from above-left,
// the same two sums. What ℝ adds is only the embedding: each
// coefficient is a natural number, carried in by &, and the embedding
// adds, so Pascal's rule holds of the carried coefficients too.

// BinomialExpansion — (x + y)ⁿ is the sum over the row of
// binomial(n, k)·xᵏ·yⁿ⁻ᵏ, for real x and y.
var BinomialExpansion = binomialExpansionThm{family.Add(registry.ProofEntry{
	Name: "BinomialExpansion",
	Key:  "prop_4605ea67b3bed14d",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y:real.",
			Conclusion: "real_pow(x + y, n) = " +
				"sum(0 .. n, λk:num. &binomial(n, k) * real_pow(x, k) * real_pow(y, n - k))",
			Abbrev: Abbrev{
				{Name: "binomialRowTerms", Text: "λk:num. &(binomial(n, k)) * real_pow(x, k) * real_pow(y, n - k)"},
				{Name: "binomialNextRowTerms", Text: "λk:num. " +
					"    &(binomial(suc(n), k)) * real_pow(x, k) * real_pow(y, suc(n) - k)"},
				{Name: "binomialFromAbove", Text: "λk:num. " +
					"    &(binomial(n, k)) * real_pow(x, k) * real_pow(y, suc(n) - k)"},
				{Name: "binomialFromAboveLeft", Text: "λk:num. " +
					"    COND(k = 0, &0, &(binomial(n, k - 1)) * real_pow(x, k) * real_pow(y, suc(n) - k))"},
				{Name: "binomialRowTimesY", Text: "λk:num. " +
					"    y * (&(binomial(n, k)) * real_pow(x, k) * real_pow(y, n - k))"},
				{Name: "binomialRowTimesX", Text: "λj:num. " +
					"    x * (&(binomial(n, j)) * real_pow(x, j) * real_pow(y, n - j))"},
				{Name: "binomialFromAboveLeftOnward", Text: "λj:num. " +
					"    COND(j + 1 = 0, " +
					"        &0, " +
					"        &(binomial(n, j + 1 - 1)) * real_pow(x, j + 1) * real_pow(y, suc(n) - (j + 1)))"},
			},
		},
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"row 0 is the single term 1",
				func(b *Argument) {
					b.FixAs[Real]("x")
					b.FixAs[Real]("y")
					b.Do(
						// ↦ &1 = &(binomial(0, 0)) * &1 * &1
						Simp(Fwd(real_sum.IntervalPoint)),
						Simp(Fwd(nat_monus.Sub)),
						Simp(Fwd(Pow)))
					corner := b.Have(
						"the corner of the triangle is 1",
						"&(binomial(0, 0)) = &1",
						By(Normalized, binomial.Clauses))
					b.Show(
						"every power at exponent 0 is 1",
						ByArith(corner))
				})
			a.Step(
				"from row n to row suc(n)",
				func(b *Argument, ih Fact) {
					x := b.FixAs[Real]("x")
					y := b.FixAs[Real]("y")
					zero, one := b.Ctx().Nat(0), b.Ctx().Nat(1)
					upper := b.TermAs[Nat]("n")
					next := b.TermAs[Nat]("suc(n)")
					row := b.TermAs[Set[Nat]]("0 .. n")
					nextRow := b.TermAs[Set[Nat]]("0 .. suc(n)")
					terms := b.TermAs[Fun[Nat, Real]]("«binomialRowTerms»")
					newTerms := b.TermAs[Fun[Nat, Real]]("«binomialNextRowTerms»")
					above := b.TermAs[Fun[Nat, Real]]("«binomialFromAbove»")
					aboveLeft := b.TermAs[Fun[Nat, Real]]("«binomialFromAboveLeft»")

					split := b.Have(
						"each term of row suc(n) is its share from above plus its share from above-left",
						Statement{
							Binders: "∀k:num.",
							Hypotheses: []string{
								"0 ≤ k",
								"k ≤ suc(n)",
							},
							Conclusion: "&binomial(suc(n), k) * real_pow(x, k) * real_pow(y, suc(n) - k) = " +
								"&binomial(n, k) * real_pow(x, k) * real_pow(y, suc(n) - k) + " +
								"COND(k = 0, &0, &binomial(n, k - 1) * real_pow(x, k) * real_pow(y, suc(n) - k))",
						},
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							c.Assume()
							c.Cases(c.Term("k = 0"))
							c.When(
								"column 0: both rows hold 1 there, and there is no share from above-left",
								func(d *Argument, isZero Fact) {
									d.Do(isZero.Rw())
									nextCorner := d.Have(
										"row suc(n) holds 1 at column 0",
										"&(binomial(suc(n), 0)) = &1",
										By(Normalized, binomial.Clauses))
									corner := d.Have(
										"and so does row n",
										"&(binomial(n, 0)) = &1",
										By(Normalized, binomial.Clauses))
									d.Do(nextCorner.Rw(), corner.Rw())
									d.Show(
										"the two sides are the same term",
										ByArith())
								})
							c.Otherwise(
								"past column 0 the entry is the two above it",
								func(d *Argument, nonzero Fact) {
									natural := d.Have(
										"Pascal's rule, as the definition states it",
										"binomial(suc(n), k) = binomial(n, k - 1) + binomial(n, k)",
										By(Normalized, binomial.BinomialDef, nonzero))
									pascal := d.Have(
										"and carried into ℝ, where the embedding adds",
										"&(binomial(suc(n), k)) = &(binomial(n, k - 1)) + &(binomial(n, k))",
										By(
											natural,
											real_construction.OfNumAdd.At(
												d.TermAs[Nat]("binomial(n, k - 1)"), d.TermAs[Nat]("binomial(n, k)"))))
									share := d.Have(
										"the share from above-left is there",
										"COND(k = 0, &0, &(binomial(n, k - 1)) * real_pow(x, k) * real_pow(y, suc(n) - k)) = "+
											"&(binomial(n, k - 1)) * real_pow(x, k) * real_pow(y, suc(n) - k)",
										By(nonzero))
									d.Do(pascal.Rw(), share.Rw())
									d.Show(
										"and the product distributes over the sum",
										ByArith())
								})
						}))

					rowEnds := b.Have(
						"row n ends before column suc(n)",
						"binomial(n, suc(n)) = 0",
						By(binomial.EqZero.At(upper, next), nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
					fromAboveAtTop := b.Have(
						"so the last share from above is 0",
						"&(binomial(n, suc(n))) = &0",
						By(Normalized, rowEnds))

					ySide := b.Have(
						"the shares from above add up to y times row n's expansion",
						"sum(0 .. suc(n), «binomialFromAbove») = y * sum(0 .. n, «binomialRowTerms»)",
						Derive(func(c *Argument) {
							pointwise := c.Have(
								"y times a term of row n is that term's share from above",
								Statement{
									Binders: "∀k:num.",
									Hypotheses: []string{
										"0 ≤ k",
										"k ≤ n",
									},
									Conclusion: "y * (&binomial(n, k) * real_pow(x, k) * real_pow(y, n - k)) = " +
										"&binomial(n, k) * real_pow(x, k) * real_pow(y, suc(n) - k)",
								},
								Derive(func(d *Argument) {
									d.FixAs[Nat]("k")
									bounds := d.Assume()
									exponent := d.Have(
										"one column in, the exponent of y is one more",
										"suc(n) - k = suc(n - k)",
										ByArith(bounds))
									d.Do(exponent.Rw())
									power := d.Have(
										"which is one more factor y",
										"real_pow(y, suc(n - k)) = y * real_pow(y, n - k)",
										By(Pow))
									d.Do(power.Rw())
									d.Show(
										"so the two products have the same factors",
										ByArith())
								}))
							top := c.Have(
								"the new row's sum takes one term more than row n's",
								"sum(0 .. suc(n), «binomialFromAbove») = "+
									"sum(0 .. n, «binomialFromAbove») + "+
									"&binomial(n, suc(n)) * real_pow(x, suc(n)) * real_pow(y, suc(n) - suc(n))",
								By(Normalized, real_sum.IntervalClauses, nat_order.ZeroLessEq))
							c.Do(top.Rw(), fromAboveAtTop.Rw())
							scaled := c.Have(
								"y comes inside row n's sum",
								"y * sum(0 .. n, «binomialRowTerms») = sum(0 .. n, «binomialRowTimesY»)",
								By(real_sum.ScalarLeft.At(y, terms, row)))
							termwise := c.Have(
								"where it turns each term into its share from above",
								"sum(0 .. n, «binomialRowTimesY») = sum(0 .. n, «binomialFromAbove»)",
								By(
									pointwise,
									real_sum.IntervalCongruence.At(zero, upper,
										b.TermAs[Fun[Nat, Real]]("«binomialRowTimesY»"),
										above)))
							c.Show(
								"and the last share adds nothing",
								ByArith(scaled, termwise))
						}))

					xSide := b.Have(
						"the shares from above-left add up to x times row n's expansion",
						"sum(0 .. suc(n), «binomialFromAboveLeft») = x * sum(0 .. n, «binomialRowTerms»)",
						Derive(func(c *Argument) {
							pointwise := c.Have(
								"x times a term of row n is the share from above-left one column along",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"0 ≤ j",
										"j ≤ n",
									},
									Conclusion: "x * (&binomial(n, j) * real_pow(x, j) * real_pow(y, n - j)) = " +
										"COND(j + 1 = 0, &0, &binomial(n, j + 1 - 1) * real_pow(x, j + 1) * real_pow(y, suc(n) - (j + 1)))",
								},
								Derive(func(d *Argument) {
									d.FixAs[Nat]("j")
									d.Assume()
									along := d.Have(
										"one column along is not column 0",
										"j + 1 ≠ 0",
										ByArith())
									present := d.Have(
										"so the share from above-left is there",
										"COND(j + 1 = 0, "+
											"    &0, "+
											"    &(binomial(n, j + 1 - 1)) * real_pow(x, j + 1) * real_pow(y, suc(n) - (j + 1))) = "+
											"&(binomial(n, j + 1 - 1)) * real_pow(x, j + 1) * real_pow(y, suc(n) - (j + 1))",
										By(along))
									column := d.Have(
										"the column above-left is j",
										"j + 1 - 1 = j",
										ByArith())
									exponent := d.Have(
										"and the exponent of y is unchanged",
										"suc(n) - (j + 1) = n - j",
										ByArith())
									power := d.Have(
										"while x takes one more factor",
										"real_pow(x, j + 1) = x * real_pow(x, j)",
										By(Pow, nat_arith.Add1))
									d.Do(present.Rw(), column.Rw(), exponent.Rw(), power.Rw())
									d.Show(
										"so the two products have the same factors",
										ByArith())
								}))
							firstShare := c.Have(
								"column 0 has no share from above-left",
								"sum(0 .. suc(n), «binomialFromAboveLeft») = sum(0 + 1 .. suc(n), «binomialFromAboveLeft»)",
								Derive(func(d *Argument) {
									peel := d.Have(
										"column 0 comes off the front",
										"sum(0 .. suc(n), «binomialFromAboveLeft») = "+
											"COND(0 = 0, &0, &binomial(n, 0 - 1) * real_pow(x, 0) * real_pow(y, suc(n) - 0)) + "+
											"sum(0 + 1 .. suc(n), «binomialFromAboveLeft»)",
										By(real_sum.PeelLeft.At(zero, next, aboveLeft), nat_order.ZeroLessEq.At(next)))
									d.Do(peel.Rw())
									d.Show(
										"and what it contributes is nothing",
										ByArith())
								}))
							shifted := c.Have(
								"and the rest is a sum over row n, read one column along",
								"sum(0 + 1 .. suc(n), «binomialFromAboveLeft») = sum(0 .. n, «binomialFromAboveLeftOnward»)",
								By(real_sum.Shift.At(zero, upper, one, aboveLeft), nat_arith.Add1))
							scaled := c.Have(
								"x comes inside row n's sum",
								"x * sum(0 .. n, «binomialRowTerms») = sum(0 .. n, «binomialRowTimesX»)",
								By(real_sum.ScalarLeft.At(x, terms, row)))
							termwise := c.Have(
								"where it turns each term into the share one column along",
								"sum(0 .. n, «binomialRowTimesX») = sum(0 .. n, «binomialFromAboveLeftOnward»)",
								By(
									pointwise,
									real_sum.IntervalCongruence.At(zero, upper,
										b.TermAs[Fun[Nat, Real]]("«binomialRowTimesX»"),
										b.TermAs[Fun[Nat, Real]]("«binomialFromAboveLeftOnward»"))))
							c.Show(
								"so the shares from above-left come to x times row n's expansion",
								ByArith(firstShare, shifted, scaled, termwise))
						}))

					whole := b.Have(
						"row suc(n)'s sum is the sum of the two families of shares",
						"sum(0 .. suc(n), «binomialNextRowTerms») = "+
							"sum(0 .. suc(n), «binomialFromAbove») + sum(0 .. suc(n), «binomialFromAboveLeft»)",
						By(
							split,
							real_sum.Add.At(above, aboveLeft, nextRow),
							num_segment.Finite,
							real_sum.IntervalCongruence.At(zero, next, newTerms,
								b.TermAs[Fun[Nat, Real]]("λk:num. "+
									"    &(binomial(n, k)) * real_pow(x, k) * real_pow(y, suc(n) - k) + "+
									"    COND(k = 0, &0, &(binomial(n, k - 1)) * real_pow(x, k) * real_pow(y, suc(n) - k))"))))
					power := b.Have(
						"one more factor x + y",
						"real_pow(x + y, suc(n)) = (x + y) * real_pow(x + y, n)",
						By(Pow))
					expanded := b.Have(
						"so (x + y)ⁿ⁺¹ is x + y times row n's expansion",
						"real_pow(x + y, suc(n)) = (x + y) * sum(0 .. n, «binomialRowTerms»)",
						By(power, ih.At(x, y)))
					b.Show(
						"which is x times it plus y times it",
						ByArith(expanded, whole, ySide, xSide))
				})
		}),
})}
