// binomial.go — the chapter: the binomial coefficients and the theorem
// that names them.
//
// Six parts, marked by banners:
//
// - Pascal's rule
// - The shape of the triangle
// - The factorial formula
// - The binomial theorem
// - What the coefficients count
// - The central coefficients

package binomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Pascal's rule
// ---------------------------------------------------------------------------
//
// The definition recurses on the row and asks of the column only whether
// it is 0, so what it says about a given entry depends on which of three
// kinds the entry is: in column 0, in row 0 past column 0, or past both.
// Read at each kind it is one of the three clauses a reader knows the
// triangle by.

// Clauses — Pascal's triangle as it is drawn. Column 0 holds 1 in every
// row: both of the definition's equations answer 1 when the column is 0,
// so it does not matter which one the row selects. Row 0 holds nothing
// past column 0. And past column 0 in a later row every entry is the sum
// of the two entries above it, because the column's predecessor
// suc(k) - 1 is k.
var Clauses = clausesThm{family.Add(registry.ProofEntry{
	Name: "Clauses",
	Key:  "prop_49864c977b9703a1",
	Build: family.Theorem(
		"(∀n:num. binomial(n, 0) = 1) ∧ "+
			"(∀k:num. binomial(0, suc(k)) = 0) ∧ "+
			"(∀n k:num. binomial(suc(n), suc(k)) = binomial(n, k) + binomial(n, suc(k)))",
		func(a *Argument) {
			a.Do(SplitConjAll(
				Case(
					"column 0 holds 1 in every row",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the row is 0 or a successor, and either equation answers 1 at column 0",
							By(BinomialDef, peano.Cases.At(n)))
					})),
				Case(
					"row 0 holds nothing past column 0",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						b.Show(
							"at column suc(k) the guard fails",
							By(BinomialDef, peano.SucNotZero))
					})),
				Case(
					"past column 0, each entry is the two above it",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						b.FixAs[Nat]("k")
						b.Show(
							"at column suc(k) the guard fails, and the column's predecessor is k",
							By(Normalized, BinomialDef, peano.SucNotZero, nat_monus.SucSubOne))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The shape of the triangle
// ---------------------------------------------------------------------------

// EqZero — an entry of the triangle is zero exactly when its column lies
// past its row. By induction on the row, for every column at once. Row 0
// is 1 at column 0 and 0 everywhere past it. In a later row column 0 is
// 1 again, and past column 0 an entry is the sum of the two above it,
// which vanishes exactly when both do — when the row above ends before
// both of their columns, that is, before the entry's own.
var EqZero = eqZeroThm{family.Add(registry.ProofEntry{
	Name: "EqZero",
	Key:  "prop_221c73401872d40d",
	Build: family.Theorem("∀n k:num. binomial(n, k) = 0 ⇔ n < k",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"row 0 holds 1 at column 0 and nothing past it",
				By(BinomialDef, nat_order.PosIffNonzero, nat_arith.OneNotZero))
			a.Step(
				"from row n to row suc(n)",
				func(b *Argument, ih Fact) {
					k := b.FixAs[Nat]("k")
					b.Cases(b.Term("k = 0"))
					b.When(
						"column 0 holds 1, and no row ends before column 0",
						func(c *Argument, isZero Fact) {
							c.Do(isZero.Rw())
							c.Show(
								"1 is not 0, and nothing lies below 0",
								ByArith(Clauses))
						})
					b.Otherwise(
						"past column 0 the entry is the sum of the two above it",
						func(c *Argument, nonzero Fact) {
							j, isSuc := c.ObtainAs[Nat](
								"the column is a successor",
								"∃j:num. k = suc(j)",
								By(Normalized, nonzero, peano.Cases.At(k)))
							c.Do(isSuc.Rw())
							next := c.TermAs[Nat]("suc(j)")
							bothZero := c.Have(
								"a sum of naturals is zero exactly when both terms are",
								"binomial(suc(n), suc(j)) = 0 ⇔ binomial(n, j) = 0 ∧ binomial(n, suc(j)) = 0",
								By(Clauses, nat_arith.AddEqZero))
							bothPast := c.Have(
								"and the row above ends before both columns exactly when row suc(n) ends before suc(j)",
								"n < j ∧ n < suc(j) ⇔ suc(n) < suc(j)",
								ByArith())
							c.Show(
								"which the induction hypothesis, read at the two columns, joins",
								By(Normalized, bothZero, bothPast, ih.At(j), ih.At(next)))
						})
				})
		}),
})}

// Diagonal — the triangle's right edge is 1 all the way down. By
// induction on the row: past row 0 the diagonal entry is the diagonal
// entry above it plus the entry just past that diagonal, which is 0.
var Diagonal = diagonalThm{family.Add(registry.ProofEntry{
	Name: "Diagonal",
	Key:  "prop_51382c815bb05302",
	Build: family.Theorem("∀n:num. binomial(n, n) = 1",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"row 0 at column 0",
				By(Clauses))
			a.Step(
				"from row n to row suc(n)",
				func(b *Argument, ih Fact) {
					next := b.TermAs[Nat]("suc(n)")
					pascal := b.Have(
						"the diagonal entry is the two above it",
						"binomial(suc(n), suc(n)) = binomial(n, n) + binomial(n, suc(n))",
						By(Clauses))
					past := b.Have(
						"and the one past the diagonal above is 0",
						"binomial(n, suc(n)) = 0",
						By(EqZero.At(b.TermAs[Nat]("n"), next), nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
					b.Show(
						"so it is the diagonal entry above, which is 1",
						ByArith(pascal, past, ih))
				})
		}),
})}

// ColumnOne — column 1 of the triangle counts the rows: binomial(n, 1) = n.
// By induction on the row: past row 0 the entry is the entry above it plus
// the 1 of column 0 beside that.
var ColumnOne = columnOneThm{family.Add(registry.ProofEntry{
	Name: "ColumnOne",
	Key:  "prop_cc0d23a4b07cd033",
	Build: family.Theorem("∀n:num. binomial(n, 1) = n",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"row 0 holds nothing past column 0",
				Simp(Fwd(BinomialDef)),
				ByArith())
			a.Step(
				"one row down, the entry gains the 1 of column 0",
				func(b *Argument, ih Fact) {
					b.Show(
						"binomial(n + 1, 1) is binomial(n, 0) + binomial(n, 1), which is 1 + n",
						Simp(Fwd(BinomialDef)),
						ByArith(ih, Clauses))
				})
		}),
})}

// ColumnTwo — twice an entry of column 2 is n(n − 1), stated as
// 2·binomial(n, 2) + n = n·n to keep clear of truncated subtraction. By
// induction on the row: one row down the entry gains the entry of column 1
// beside the one above it, which is n (ColumnOne), and the doubled gain 2n
// with the new 1 is what (n + 1)² adds to n².
var ColumnTwo = columnTwoThm{family.Add(registry.ProofEntry{
	Name: "ColumnTwo",
	Key:  "prop_e1f785f48682d8fd",
	Build: family.Theorem("∀n:num. 2 * binomial(n, 2) + n = n * n",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"row 0 holds nothing past column 0",
				Simp(Fwd(BinomialDef)),
				ByArith())
			a.Step(
				"one row down, the entry gains binomial(n, 1), which is n",
				func(b *Argument, ih Fact) {
					b.Show(
						"2·(binomial(n, 2) + n) + n + 1 is n·n + 2n + 1",
						Simp(Fwd(BinomialDef)),
						ByArith(ih, At(ColumnOne, b.TermAs[Nat]("n"))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The factorial formula
// ---------------------------------------------------------------------------

// FactorialFormula — k!·(n - k)!·binomial(n, k) = n! for every column up
// to the row: the product formula, stated without a division because ℕ
// has none.
//
// The proof runs in a working form without subtraction, over the row
// written as m + k: m!·k!·binomial(m + k, k) = (m + k)!. That is a double
// induction. At m = 0 the entry sits on the diagonal. Past it, in column
// 0 the entry is 1; and at column suc(k) Pascal's rule splits the entry
// into the two above it, each of which one induction hypothesis prices:
// the one on its left carries an extra factor suc(k) against the
// hypothesis on k, the one above it an extra factor suc(m) against the
// hypothesis on m, and suc(k) + suc(m) is the new factor of the
// factorial. The headline is the working form at m = n - k.
var FactorialFormula = factorialFormulaThm{family.Add(registry.ProofEntry{
	Name: "FactorialFormula",
	Key:  "prop_c68a2a86dc6c64cc",
	Build: family.Sections(
		Statement{
			Binders: "∀n k:num.",
			Hypotheses: []string{
				"k ≤ n",
			},
			Conclusion: "factorial(k) * factorial(n - k) * binomial(n, k) = factorial(n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			working := ctx.Lemma(
				"∀m k:num. factorial(m) * factorial(k) * binomial(m + k, k) = factorial(m + k)",
				func(a *Argument) {
					m := a.Binder("m")

					a.Induct(m)
					a.Base(
						"m = 0: the entry is on the diagonal",
						func(b *Argument) {
							k := b.FixAs[Nat]("k")
							b.Do(
								// ↦ factorial(0) * factorial(k₀) * binomial(k₀, k₀) = factorial(k₀)
								Simp(Fwd(nat_arith.Add)))
							b.Show(
								"1 · k! · 1 is k!",
								ByArith(nat_arith.Factorial, Diagonal.At(k)))
						})
					a.Step(
						"m → suc(m), for every column by a second induction",
						func(b *Argument, above Fact) {
							k := b.Binder("k")

							b.Induct(k)
							b.Base(
								"column 0 holds 1",
								func(c *Argument) {
									c.Do(
										// ↦ factorial(suc(m)) * factorial(0) * binomial(suc(m), 0) = factorial(suc(m))
										Simp(Fwd(nat_arith.AddZero)))
									c.Show(
										"(suc m)! · 1 · 1 is (suc m)!",
										ByArith(nat_arith.Factorial, Clauses))
								})
							b.Step(
								"column k → suc(k)",
								func(c *Argument, left Fact) {
									next := c.TermAs[Nat]("suc(k)")
									c.Do(
										// suc(m) + suc(k) ↦ suc(suc(m) + k): the row is a successor
										Simp(Fwd(nat_arith.AddSuc)))
									pascal := c.Have(
										"the entry is the two above it",
										"binomial(suc(suc(m) + k), suc(k)) = binomial(suc(m) + k, k) + binomial(suc(m) + k, suc(k))",
										By(Clauses))
									c.Do(pascal.Rw())

									factorialK := c.Have(
										"(suc k)! = suc(k)·k!",
										"factorial(suc(k)) = suc(k) * factorial(k)",
										By(nat_arith.Factorial))
									factorialM := c.Have(
										"(suc m)! = suc(m)·m!",
										"factorial(suc(m)) = suc(m) * factorial(m)",
										By(nat_arith.Factorial))
									factorialRow := c.Have(
										"and the new row's factorial takes one more factor",
										"factorial(suc(suc(m) + k)) = suc(suc(m) + k) * factorial(suc(m) + k)",
										By(nat_arith.Factorial))

									leftPriced := c.Have(
										"the entry on the left costs suc(k) times the hypothesis on k",
										"factorial(suc(m)) * factorial(suc(k)) * binomial(suc(m) + k, k) = suc(k) * factorial(suc(m) + k)",
										Derive(func(d *Argument) {
											d.Do(factorialK.Rw())
											regroup := d.Have(
												"the extra factor comes to the front",
												"factorial(suc(m)) * (suc(k) * factorial(k)) * binomial(suc(m) + k, k) = "+
													"suc(k) * (factorial(suc(m)) * factorial(k) * binomial(suc(m) + k, k))",
												ByArith())
											d.Show(
												"and what it multiplies is the hypothesis on k",
												By(regroup, left))
										}))
									sameRow := c.Have(
										"the row above, read from m",
										"m + suc(k) = suc(m) + k",
										ByArith())
									upper := c.Have(
										"the hypothesis on m, at column suc(k)",
										"factorial(m) * factorial(suc(k)) * binomial(suc(m) + k, suc(k)) = factorial(suc(m) + k)",
										By(Normalized, above.At(next), sameRow))
									abovePriced := c.Have(
										"the entry above costs suc(m) times the hypothesis on m",
										"factorial(suc(m)) * factorial(suc(k)) * binomial(suc(m) + k, suc(k)) = "+
											"suc(m) * factorial(suc(m) + k)",
										Derive(func(d *Argument) {
											d.Do(factorialM.Rw())
											regroup := d.Have(
												"the extra factor comes to the front",
												"suc(m) * factorial(m) * factorial(suc(k)) * binomial(suc(m) + k, suc(k)) = "+
													"suc(m) * (factorial(m) * factorial(suc(k)) * binomial(suc(m) + k, suc(k)))",
												ByArith())
											d.Show(
												"and what it multiplies is the hypothesis on m",
												By(regroup, upper))
										}))
									c.Show(
										"suc(k) + suc(m) is the new row's factor",
										ByArith(leftPriced, abovePriced, factorialRow))
								})
						})
				})

			return ctx.Theorem(headline, func(a *Argument, n, k *Expr[Nat], below Fact) {
				rest := a.TermAs[Nat]("n - k")
				read := a.Have(
					"the working form at m = n - k, whose row n - k + k is n, the column lying within it",
					"factorial(n - k) * factorial(k) * binomial(n, k) = factorial(n)",
					By(Normalized, At(working, rest, k), below, nat_monus.SubAddCancel.At(n, k)))
				a.Show(
					"the same product, its factors in the headline's order",
					ByArith(read))
			})
		}),
})}

// Symmetry — complementary columns in a row have equal binomial
// coefficients. The factorial formula multiplies both coefficients by
// the same two nonzero factorials.
var Symmetry = symmetryThm{family.Add(registry.ProofEntry{
	Name: "Symmetry",
	Key:  "prop_ab49220329460ff7",
	Build: family.Theorem(Statement{
		Binders:    "∀n k:num.",
		Hypotheses: []string{"k ≤ n"},
		Conclusion: "binomial(n, k) = binomial(n, n - k)",
	},
		func(a *Argument, n, k *Expr[Nat], inRow Fact) {
			complement := a.TermAs[Nat]("n - k")
			complementOfComplement := a.Have(
				"the complement of the complementary column is k",
				"n - (n - k) = k",
				ByArith(inRow))
			a.Show(
				"the factorial formula gives the same product for both columns, and the factorials cancel",
				ByArith(
					inRow,
					complementOfComplement,
					FactorialFormula.At(n, k),
					FactorialFormula.At(n, complement),
					nat_arith.FactorialNonzero.At(k),
					nat_arith.FactorialNonzero.At(complement)))
		}),
})}

// ---------------------------------------------------------------------------
// The binomial theorem
// ---------------------------------------------------------------------------

// Expansion — (x + y)ⁿ is the sum over the row of binomial(n, k)·xᵏ·yⁿ⁻ᵏ.
// By induction on n. Row 0 is the single term 1. For the step, (x + y)
// times row n's expansion is x times it plus y times it, and Pascal's
// rule splits each term of row suc(n) into a share from the entry above
// it and, past column 0, a share from the entry above-left. The shares
// from above add up to y times row n's expansion — the new row's last
// share is binomial(n, suc(n)) = 0 — and the shares from above-left, one
// column further along, to x times it.
var Expansion = expansionThm{family.Add(registry.ProofEntry{
	Name: "Expansion",
	Key:  "prop_a8c59d9dc7bf3c50",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Conclusion: "nat_pow(x + y, n) = " +
				"sum(0 .. n, λk:num. binomial(n, k) * nat_pow(x, k) * nat_pow(y, n - k))",
			Abbrev: Abbrev{
				{Name: "rowTerms", Text: "λk:num. binomial(n, k) * nat_pow(x, k) * nat_pow(y, n - k)"},
				{Name: "nextRowTerms", Text: "λk:num. " +
					"    binomial(suc(n), k) * nat_pow(x, k) * nat_pow(y, suc(n) - k)"},
				{Name: "fromAbove", Text: "λk:num. binomial(n, k) * nat_pow(x, k) * nat_pow(y, suc(n) - k)"},
				{Name: "fromAboveLeft", Text: "λk:num. " +
					"    COND(k = 0, 0, binomial(n, k - 1) * nat_pow(x, k) * nat_pow(y, suc(n) - k))"},
				{Name: "rowTimesY", Text: "λk:num. y * (binomial(n, k) * nat_pow(x, k) * nat_pow(y, n - k))"},
				{Name: "rowTimesX", Text: "λj:num. x * (binomial(n, j) * nat_pow(x, j) * nat_pow(y, n - j))"},
				{Name: "fromAboveLeftOnward", Text: "λj:num. " +
					"    COND(j + 1 = 0, " +
					"        0, " +
					"        binomial(n, j + 1 - 1) * nat_pow(x, j + 1) * nat_pow(y, suc(n) - (j + 1)))"},
			},
		},
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"row 0 is the single term 1",
				func(b *Argument) {
					b.FixAs[Nat]("x")
					b.FixAs[Nat]("y")
					b.Do(
						// ↦ nat_pow(x₀ + y₀, 0) = binomial(0, 0) * nat_pow(x₀, 0) * nat_pow(y₀, 0 - 0)
						Simp(Fwd(nat_sum.IntervalPoint)),
						// 0 - 0 ↦ 0, and every power at exponent 0 ↦ 1:
						// 1 = binomial(0, 0) * 1 * 1
						Simp(Fwd(nat_monus.Sub)),
						Simp(Fwd(nat_arith.NatPow)))
					b.Show(
						"the corner of the triangle is 1, and every power at exponent 0 is 1",
						ByArith(Clauses))
				})
			a.Step(
				"from row n to row suc(n)",
				func(b *Argument, ih Fact) {
					x := b.FixAs[Nat]("x")
					y := b.FixAs[Nat]("y")
					zero, one := b.Ctx().Nat(0), b.Ctx().Nat(1)
					upper := b.TermAs[Nat]("n")
					next := b.TermAs[Nat]("suc(n)")
					row := b.TermAs[Set[Nat]]("0 .. n")
					nextRow := b.TermAs[Set[Nat]]("0 .. suc(n)")
					terms := b.TermAs[Fun[Nat, Nat]]("«rowTerms»")
					newTerms := b.TermAs[Fun[Nat, Nat]]("«nextRowTerms»")
					above := b.TermAs[Fun[Nat, Nat]]("«fromAbove»")
					aboveLeft := b.TermAs[Fun[Nat, Nat]]("«fromAboveLeft»")

					split := b.Have(
						"each term of row suc(n) is its share from above plus its share from above-left",
						Statement{
							Binders: "∀k:num.",
							Hypotheses: []string{
								"0 ≤ k",
								"k ≤ suc(n)",
							},
							Conclusion: "binomial(suc(n), k) * nat_pow(x, k) * nat_pow(y, suc(n) - k) = " +
								"binomial(n, k) * nat_pow(x, k) * nat_pow(y, suc(n) - k) + " +
								"COND(k = 0, 0, binomial(n, k - 1) * nat_pow(x, k) * nat_pow(y, suc(n) - k))",
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
										"binomial(suc(n), 0) = 1",
										By(Clauses))
									corner := d.Have(
										"and so does row n",
										"binomial(n, 0) = 1",
										By(Clauses))
									d.Do(nextCorner.Rw(), corner.Rw())
									d.Show(
										"the two sides are the same term",
										ByArith())
								})
							c.Otherwise(
								"past column 0 the entry is the two above it",
								func(d *Argument, nonzero Fact) {
									pascal := d.Have(
										"Pascal's rule, as the definition states it",
										"binomial(suc(n), k) = binomial(n, k - 1) + binomial(n, k)",
										By(Normalized, BinomialDef, nonzero))
									share := d.Have(
										"the share from above-left is there",
										"COND(k = 0, 0, binomial(n, k - 1) * nat_pow(x, k) * nat_pow(y, suc(n) - k)) = "+
											"binomial(n, k - 1) * nat_pow(x, k) * nat_pow(y, suc(n) - k)",
										By(nonzero))
									d.Do(pascal.Rw(), share.Rw())
									d.Show(
										"and the product distributes over the sum",
										ByArith())
								})
						}))

					fromAboveAtTop := b.Have(
						"the last share from above is 0: row n ends before column suc(n)",
						"binomial(n, suc(n)) = 0",
						By(EqZero.At(upper, next), nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))

					ySide := b.Have(
						"the shares from above add up to y times row n's expansion",
						"sum(0 .. suc(n), «fromAbove») = y * sum(0 .. n, «rowTerms»)",
						Derive(func(c *Argument) {
							pointwise := c.Have(
								"y times a term of row n is that term's share from above",
								Statement{
									Binders: "∀k:num.",
									Hypotheses: []string{
										"0 ≤ k",
										"k ≤ n",
									},
									Conclusion: "y * (binomial(n, k) * nat_pow(x, k) * nat_pow(y, n - k)) = " +
										"binomial(n, k) * nat_pow(x, k) * nat_pow(y, suc(n) - k)",
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
										"nat_pow(y, suc(n - k)) = y * nat_pow(y, n - k)",
										By(nat_arith.NatPow))
									d.Do(power.Rw())
									d.Show(
										"so the two products have the same factors",
										ByArith())
								}))
							top := c.Have(
								"the new row's sum takes one term more than row n's",
								"sum(0 .. suc(n), «fromAbove») = "+
									"sum(0 .. n, «fromAbove») + binomial(n, suc(n)) * nat_pow(x, suc(n)) * nat_pow(y, suc(n) - suc(n))",
								By(Normalized, nat_sum.IntervalClauses, nat_order.ZeroLessEq))
							c.Do(top.Rw(), fromAboveAtTop.Rw())
							scaled := c.Have(
								"y comes inside row n's sum",
								"y * sum(0 .. n, «rowTerms») = sum(0 .. n, «rowTimesY»)",
								By(nat_sum.ScalarLeft.At(y, terms, row), num_segment.Finite))
							termwise := c.Have(
								"where it turns each term into its share from above",
								"sum(0 .. n, «rowTimesY») = sum(0 .. n, «fromAbove»)",
								By(
									pointwise,
									nat_sum.IntervalCongruence.At(zero, upper,
										b.TermAs[Fun[Nat, Nat]]("«rowTimesY»"),
										above)))
							c.Show(
								"and the last share adds nothing",
								ByArith(scaled, termwise))
						}))

					xSide := b.Have(
						"the shares from above-left add up to x times row n's expansion",
						"sum(0 .. suc(n), «fromAboveLeft») = x * sum(0 .. n, «rowTerms»)",
						Derive(func(c *Argument) {
							pointwise := c.Have(
								"x times a term of row n is the share from above-left one column along",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"0 ≤ j",
										"j ≤ n",
									},
									Conclusion: "x * (binomial(n, j) * nat_pow(x, j) * nat_pow(y, n - j)) = " +
										"COND(j + 1 = 0, 0, binomial(n, j + 1 - 1) * nat_pow(x, j + 1) * nat_pow(y, suc(n) - (j + 1)))",
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
										"COND(j + 1 = 0, 0, binomial(n, j + 1 - 1) * nat_pow(x, j + 1) * nat_pow(y, suc(n) - (j + 1))) = "+
											"binomial(n, j + 1 - 1) * nat_pow(x, j + 1) * nat_pow(y, suc(n) - (j + 1))",
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
										"nat_pow(x, j + 1) = x * nat_pow(x, j)",
										By(nat_arith.NatPow, nat_arith.Add1))
									d.Do(present.Rw(), column.Rw(), exponent.Rw(), power.Rw())
									d.Show(
										"so the two products have the same factors",
										ByArith())
								}))
							firstShare := c.Have(
								"column 0 has no share from above-left",
								"sum(0 .. suc(n), «fromAboveLeft») = sum(0 + 1 .. suc(n), «fromAboveLeft»)",
								Derive(func(d *Argument) {
									peel := d.Have(
										"column 0 comes off the front",
										"sum(0 .. suc(n), «fromAboveLeft») = "+
											"COND(0 = 0, 0, binomial(n, 0 - 1) * nat_pow(x, 0) * nat_pow(y, suc(n) - 0)) + "+
											"sum(0 + 1 .. suc(n), «fromAboveLeft»)",
										By(nat_sum.PeelLeft.At(zero, next, aboveLeft), nat_order.ZeroLessEq.At(next)))
									d.Do(peel.Rw())
									d.Show(
										"and what it contributes is nothing",
										ByArith())
								}))
							shifted := c.Have(
								"and the rest is a sum over row n, read one column along",
								"sum(0 + 1 .. suc(n), «fromAboveLeft») = sum(0 .. n, «fromAboveLeftOnward»)",
								By(nat_sum.Shift.At(zero, upper, one, aboveLeft), nat_arith.Add1))
							scaled := c.Have(
								"x comes inside row n's sum",
								"x * sum(0 .. n, «rowTerms») = sum(0 .. n, «rowTimesX»)",
								By(nat_sum.ScalarLeft.At(x, terms, row), num_segment.Finite))
							termwise := c.Have(
								"where it turns each term into the share one column along",
								"sum(0 .. n, «rowTimesX») = sum(0 .. n, «fromAboveLeftOnward»)",
								By(
									pointwise,
									nat_sum.IntervalCongruence.At(zero, upper,
										b.TermAs[Fun[Nat, Nat]]("«rowTimesX»"),
										b.TermAs[Fun[Nat, Nat]]("«fromAboveLeftOnward»"))))
							c.Show(
								"so the shares from above-left come to x times row n's expansion",
								ByArith(firstShare, shifted, scaled, termwise))
						}))

					whole := b.Have(
						"row suc(n)'s sum is the sum of the two families of shares",
						"sum(0 .. suc(n), «nextRowTerms») = "+
							"sum(0 .. suc(n), «fromAbove») + sum(0 .. suc(n), «fromAboveLeft»)",
						By(
							split,
							nat_sum.Add.At(above, aboveLeft, nextRow),
							num_segment.Finite,
							nat_sum.IntervalCongruence.At(zero, next, newTerms,
								b.TermAs[Fun[Nat, Nat]]("λk:num. "+
									"    binomial(n, k) * nat_pow(x, k) * nat_pow(y, suc(n) - k) + "+
									"    COND(k = 0, 0, binomial(n, k - 1) * nat_pow(x, k) * nat_pow(y, suc(n) - k))"))))
					expanded := b.Have(
						"one more factor x + y: by the hypothesis, (x + y)ⁿ⁺¹ is x + y times row n's expansion",
						"nat_pow(x + y, suc(n)) = (x + y) * sum(0 .. n, «rowTerms»)",
						By(nat_arith.NatPow, ih.At(x, y)))
					b.Show(
						"which is x times it plus y times it",
						ByArith(expanded, whole, ySide, xSide))
				})
		}),
})}

// PowSecondOrder — (1 + a) ^ n is 1 + n · a + C(n, 2) · a² plus a multiple of
// a³. By induction on n: multiplying by 1 + a adds a to the linear term and
// n · a² to the quadratic one, and C(n + 1, 2) = n + C(n, 2), column 1
// counting the rows (ColumnOne).
var PowSecondOrder = powSecondOrderThm{family.Add(registry.ProofEntry{
	Name: "PowSecondOrder",
	Key:  "prop_b54b90f86340d9f8",
	Build: family.Theorem("∀a n:num. ∃r:num. "+
		"    (1 + a) ^ n = 1 + n * a + binomial(n, 2) * a ^ 2 + a ^ 3 * r",
		func(arg *Argument, a *Expr[Nat]) {
			n := arg.Binder("n")
			arg.Induct(n)
			arg.Base(
				"(1 + a) ^ 0 = 1, and C(0, 2) = 0",
				func(b *Argument) {
					b.Take(b.TermAs[Nat]("0"))
					b.Show(
						"with r = 0",
						Simp(Fwd(BinomialDef), Fwd(nat_arith.NatPow)),
						ByArith())
				})
			arg.Step(
				"multiplying by 1 + a",
				func(b *Argument, ih Fact) {
					_, expansion := b.UnpackAs[Nat](ih, "r")
					b.Take(b.TermAs[Nat]("binomial(n, 2) + r + a * r"))
					pascal := b.Have(
						"C(n + 1, 2) = C(n, 1) + C(n, 2) = n + C(n, 2)",
						"binomial(suc(n), 2) = n + binomial(n, 2)",
						ByArith(BinomialDef, At(ColumnOne, n)))
					b.Show(
						"(1 + a) times 1 + n · a + C(n, 2) · a² + a³ · r",
						ByArith(
							Scaled(b.TermAs[Nat]("1 + a"), expansion),
							Scaled(b.TermAs[Nat]("a ^ 2"), pascal),
							nat_arith.NatPow))
				})
		}),
})}

// ---------------------------------------------------------------------------
// What the coefficients count
// ---------------------------------------------------------------------------

// SubsetCount — a set of n elements has binomial(n, k) subsets of k
// elements. By induction on n, for every k and every set at once. The
// empty set has one subset, itself, of size 0. A set of suc(n) elements
// is a point x added to a set t of n; a subset of size 0 is ∅ again, and
// a subset of size suc(j) either misses x — a subset of t of size
// suc(j) — or is x added to a subset of t of size j. The two kinds do not
// meet, and adding x tells the second kind apart, so the count is
// binomial(n, suc(j)) + binomial(n, j), which Pascal's rule makes
// binomial(suc(n), suc(j)).
var SubsetCount = subsetCountThm{family.Add(registry.ProofEntry{
	Name: "SubsetCount",
	Key:  "prop_e5adcdd1006f2aa0",
	Build: family.Sections(
		Statement{
			Binders: "∀n k:num. ∀s:set(A).",
			Hypotheses: []string{
				"has_size(s, n)",
			},
			Conclusion: "has_size({t:set(A) | t ⊆ s ∧ has_size(t, k)}, binomial(n, k))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// The subsets of size suc(j) of a set with x added: those that
			// miss x, and x added to those of size j.
			splitByPoint := ctx.Lemma(
				Statement{
					Binders: "∀x:A. ∀t:set(A). ∀j:num.",
					Hypotheses: []string{
						"x ∉ t",
					},
					Conclusion: "{w:set(A) | w ⊆ insert(x, t) ∧ has_size(w, suc(j))} = " +
						"{w:set(A) | w ⊆ t ∧ has_size(w, suc(j))} ∪ " +
						"image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})",
				},
				func(a *Argument, x, t, j Term, fresh Fact) {
					members := a.Have(
						"the two sides have the same members",
						"∀u:set(A). "+
							"    u ∈ {w:set(A) | w ⊆ insert(x, t) ∧ has_size(w, suc(j))} ⇔ "+
							"    u ∈ "+
							"    {w:set(A) | w ⊆ t ∧ has_size(w, suc(j))} ∪ "+
							"    image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})",
						Derive(func(b *Argument) {
							u := b.FixAs[Set[A]]("u")
							added := b.TermAs[Fun[Set[A], Set[A]]]("λw:set(A). insert(x, w)")
							smallerSubsets := b.TermAs[Set[Set[A]]]("{w:set(A) | w ⊆ t ∧ has_size(w, j)}")
							b.Iff()
							b.Forward(
								"a subset of size suc(j) either misses x or holds it",
								func(c *Argument, member Fact) {
									within := c.Have(
										"u lies in insert(x, t) and has suc(j) elements",
										"u ⊆ insert(x, t) ∧ has_size(u, suc(j))",
										BySets(member))
									c.Cases(c.Term("x ∈ u"))
									c.When(
										"holding x, it is x added to what remains, which has size j",
										func(d *Argument, holds Fact) {
											smaller := d.Have(
												"what remains has one element fewer",
												"has_size(delete(u, x), j)",
												By(within, holds, At(cardinality.HasSizeSuc, u, j)))
											rest := d.Have(
												"and is a subset of t of size j",
												"delete(u, x) ∈ {w:set(A) | w ⊆ t ∧ has_size(w, j)}",
												BySets(within, smaller))
											restored := d.Have(
												"and adding x back gives u",
												"u = insert(x, delete(u, x))",
												By(Normalized, holds, At(set_algebra.InsertDelete, u, x)))
											image := d.Have(
												"so u is x added to a subset of t of size j",
												"u ∈ image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})",
												By(Normalized, rest, restored, set_basic.InImage.At(added, smallerSubsets, u)))
											d.Show(
												"which is the second kind",
												BySets(image))
										})
									c.Otherwise(
										"missing x, it lies in t, which is the first kind",
										func(d *Argument, misses Fact) {
											d.Show(
												"a subset of t of size suc(j)",
												BySets(within, misses))
										})
								})
							b.Backward(
								"either kind is a subset of insert(x, t) of size suc(j)",
								func(c *Argument, member Fact) {
									c.Cases(c.Term("u ∈ {w:set(A) | w ⊆ t ∧ has_size(w, suc(j))}"))
									c.When(
										"the first kind lies in t already",
										func(d *Argument, first Fact) {
											d.Show(
												"and t lies in insert(x, t)",
												BySets(first))
										})
									c.Otherwise(
										"the second kind is x added to a subset of t of size j",
										func(d *Argument, notFirst Fact) {
											_, made := d.Obtain(
												"so u is x added to some subset v of t of size j",
												"∃v:set(A). u = insert(x, v) ∧ v ∈ {w:set(A) | w ⊆ t ∧ has_size(w, j)}",
												By(
													member,
													notFirst,
													set_basic.InUnion.At(d.TermAs[Set[Set[A]]]("{w:set(A) | w ⊆ t ∧ has_size(w, suc(j))}"),
														d.TermAs[Set[Set[A]]]("image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})"), u),
													set_basic.InImage.At(added, smallerSubsets, u)))
											parts := d.Have(
												"v lies in t, has j elements, and misses x",
												"v ⊆ t ∧ has_size(v, j) ∧ x ∉ v",
												BySets(made, fresh))
											bigger := d.Have(
												"so x added to it has suc(j) elements",
												"has_size(insert(x, v), suc(j))",
												By(parts, At(cardinality.HasSizeClauses, d.TermAs[Set[A]]("insert(x, v)"), j)))
											named := d.Have(
												"u is x added to v",
												"u = insert(x, v)",
												By(made))
											d.Do(named.Rw())
											d.Show(
												"and lies in insert(x, t)",
												BySets(parts, bigger))
										})
								})
						}))
					a.Show(
						"so the two sets are one",
						By(members, set_basic.Extension))
				})

			// The one subset of size 0 is ∅, and the family holding ∅ alone
			// has one member.
			justEmpty := ctx.Lemma("has_size({∅⟨A:A⟩}, 1)",
				func(a *Argument) {
					empty := a.TermAs[Set[A]]("∅⟨A:A⟩")
					a.Do(Unfold(cardinality.HasSizeDef))
					a.Show(
						"a singleton is finite and has one element",
						By(finite_set.FiniteSing.At(empty), cardinality.CardSing.At(empty)))
				})

			return ctx.Theorem(headline, func(a *Argument) {
				n := a.Binder("n")

				a.Induct(n)
				a.Base(
					"the empty set",
					func(b *Argument) {
						k := b.FixAs[Nat]("k")
						s := b.FixAs[Set[A]]("s")
						sized := b.Assume()
						empty := b.Have(
							"a set of 0 elements is empty",
							"s = ∅",
							By(sized, cardinality.HasSizeZero.At(s)))
						b.Do(empty.Rw())
						emptySized := b.Hyp("has_size(∅⟨A:A⟩, 0)")
						b.Cases(b.Term("k = 0"))
						b.When(
							"of size 0 it has one subset, ∅ itself",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw())
								only := c.Have(
									"the subsets of ∅ of size 0 are ∅ alone",
									"{t:set(A) | t ⊆ ∅ ∧ has_size(t, 0)} = {∅⟨A:A⟩}",
									BySets(emptySized))
								corner := c.Have(
									"the corner of the triangle is 1",
									"binomial(0, 0) = 1",
									By(Clauses))
								c.Do(only.Rw(), corner.Rw())
								c.Show(
									"so there is one",
									By(justEmpty))
							})
						b.Otherwise(
							"of any larger size it has none",
							func(c *Argument, nonzero Fact) {
								j, larger := c.ObtainAs[Nat](
									"the size is a successor",
									"∃j:num. k = suc(j)",
									By(Normalized, nonzero, peano.Cases.At(k)))
								c.Do(larger.Rw())
								none := c.Have(
									"∅ does not have suc(j) elements, so no subset of ∅ does",
									"{t:set(A) | t ⊆ ∅ ∧ has_size(t, suc(j))} = ∅",
									BySets(cardinality.HasSizeSuc.At(c.TermAs[Set[A]]("∅⟨A:A⟩"), j)))
								rowZero := c.Have(
									"and row 0 is 0 past column 0",
									"binomial(0, suc(j)) = 0",
									By(Clauses))
								c.Do(none.Rw(), rowZero.Rw())
								c.Show(
									"so there are none: the empty family has no members",
									By(cardinality.HasSizeZero.At(c.TermAs[Set[Set[A]]]("∅⟨A:set(A)⟩"))))
							})
					})
				a.Step(
					"a point added to a set of n elements",
					func(b *Argument, ih Fact) {
						k := b.FixAs[Nat]("k")
						s := b.FixAs[Set[A]]("s")
						sized := b.Assume()
						x, t, parts := b.Obtain2As[A, Set[A]](
							"s is a point x added to a set t of n elements that misses it",
							"∃x:A. ∃t:set(A). has_size(t, n) ∧ x ∉ t ∧ s = insert(x, t)",
							By(Normalized, sized, cardinality.HasSizeClauses.At(s, b.TermAs[Nat]("n"))))
						rows := b.Have(
							"t has n elements and misses x",
							"has_size(t, n) ∧ x ∉ t",
							By(parts))
						named := b.Have(
							"s is insert(x, t)",
							"s = insert(x, t)",
							By(parts))
						b.Do(named.Rw())
						b.Cases(b.Term("k = 0"))
						b.When(
							"of size 0 there is one subset, ∅",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw())
								only := c.Have(
									"the subsets of size 0 are ∅ alone",
									"{u:set(A) | u ⊆ insert(x, t) ∧ has_size(u, 0)} = {∅⟨A:A⟩}",
									BySets(cardinality.HasSizeZero))
								corner := c.Have(
									"column 0 holds 1",
									"binomial(suc(n), 0) = 1",
									By(Clauses))
								c.Do(only.Rw(), corner.Rw())
								c.Show(
									"so there is one",
									By(justEmpty))
							})
						b.Otherwise(
							"of size suc(j), the subsets that miss x and those that hold it",
							func(c *Argument, nonzero Fact) {
								j, larger := c.ObtainAs[Nat](
									"the size is a successor",
									"∃j:num. k = suc(j)",
									By(Normalized, nonzero, peano.Cases.At(k)))
								c.Do(larger.Rw())
								missing := c.TermAs[Set[Set[A]]]("{w:set(A) | w ⊆ t ∧ has_size(w, suc(j))}")
								smaller := c.TermAs[Set[Set[A]]]("{w:set(A) | w ⊆ t ∧ has_size(w, j)}")
								added := c.TermAs[Fun[Set[A], Set[A]]]("λw:set(A). insert(x, w)")
								holding := c.TermAs[Set[Set[A]]](
									"image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})")
								split := c.Have(
									"the two kinds",
									"{u:set(A) | u ⊆ insert(x, t) ∧ has_size(u, suc(j))} = "+
										"{w:set(A) | w ⊆ t ∧ has_size(w, suc(j))} ∪ "+
										"image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)})",
									By(rows, At(splitByPoint, x, t, j)))
								first := c.Have(
									"those that miss x number binomial(n, suc(j))",
									"has_size({w:set(A) | w ⊆ t ∧ has_size(w, suc(j))}, binomial(n, suc(j)))",
									By(rows, ih.At(c.TermAs[Nat]("suc(j)"), t)))
								below := c.Have(
									"the subsets of t of size j number binomial(n, j)",
									"has_size({w:set(A) | w ⊆ t ∧ has_size(w, j)}, binomial(n, j))",
									By(rows, ih.At(j, t)))
								apart := c.Have(
									"adding x tells them apart, x not being in t",
									"injective_on({w:set(A) | w ⊆ t ∧ has_size(w, j)}, λw:set(A). insert(x, w))",
									Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Set[A]](), TypeBinder.BindB[Set[A]]()))),
									BySets(rows))
								second := c.Have(
									"so those that hold x number binomial(n, j) too",
									"has_size(image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)}), binomial(n, j))",
									By(apart, below, cardinality.HasSizeImageInj.At(added, smaller, c.TermAs[Nat]("binomial(n, j)"))))
								disjoint := c.Have(
									"and the two kinds do not meet: the second holds x, the first lies in t",
									"disjoint({w:set(A) | w ⊆ t ∧ has_size(w, suc(j))}, "+
										"    image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)}))",
									BySets(rows))
								together := c.Have(
									"so together they number the sum",
									"has_size({w:set(A) | w ⊆ t ∧ has_size(w, suc(j))} ∪ "+
										"    image(λw:set(A). insert(x, w), {w:set(A) | w ⊆ t ∧ has_size(w, j)}), "+
										"    binomial(n, suc(j)) + binomial(n, j))",
									By(
										first,
										second,
										disjoint,
										cardinality.HasSizeUnion.At(
											missing, holding, c.TermAs[Nat]("binomial(n, suc(j))"), c.TermAs[Nat]("binomial(n, j)"))))
								commuted := c.Have(
									"Pascal's rule at column suc(j), its two terms in the order the count adds them",
									"binomial(suc(n), suc(j)) = binomial(n, suc(j)) + binomial(n, j)",
									ByArith(Clauses))
								c.Do(split.Rw(), commuted.Rw())
								c.Show(
									"the count of the two kinds",
									By(together))
							})
					})
			})
		}),
})}

// ---------------------------------------------------------------------------
// The central coefficients
// ---------------------------------------------------------------------------
//
// The middle entry C(2n, n) of an even row and its neighbour C(2m + 1, m)
// in an odd one: one step from C(2n, n) to C(2n + 2, n + 1) multiplies by
// 2(2n + 1)/(n + 1), which keeps C(2n, n) at least 4ⁿ/(2n + 1), and
// C(2m + 1, m), one of two equal terms of a row summing to 2·4ᵐ, is at
// most 4ᵐ.

// CentralBinomialRecurrence — one step along the central binomial
// coefficients multiplies by 2(2n + 1)/(n + 1). Both sides times (n + 1)·n!²
// are (2n + 2)!: by the factorial formula it is (n + 1)!²·C(2n + 2, n + 1) on
// the one hand and (2n + 2)(2n + 1)·n!²·C(2n, n) on the other, and the common
// factor is not 0.
var CentralBinomialRecurrence = centralBinomialRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialRecurrence",
	Key:  "prop_5ae9985a4a9a82a1",
	Build: family.Theorem(
		"∀n:num. (n + 1) * binomial(2 * n + 2, n + 1) = 2 * (2 * n + 1) * binomial(2 * n, n)",
		func(a *Argument, n *Expr[Nat]) {
			nFactorial := a.TermAs[Nat]("factorial(n)")
			oneStep := a.Have(
				"(n + 1)! = (n + 1)·n!",
				"factorial(n + 1) = (n + 1) * factorial(n)",
				Simp(Rev(nat_arith.Add1), Fwd(nat_arith.Factorial)),
				Refl())
			twoSteps := a.Have(
				"(2n + 2)! = (2n + 2)(2n + 1)·(2n)!",
				"factorial(2 * n + 2) = (2 * n + 2) * ((2 * n + 1) * factorial(2 * n))",
				Simp(Fwd(nat_arith.Two), Fwd(nat_arith.AddSuc), Rev(nat_arith.Add1), Fwd(nat_arith.Factorial)),
				Refl())
			squares := a.Have(
				"(2n + 2)! is (n + 1)!²·C(2n + 2, n + 1) and (2n + 2)(2n + 1)·n!²·C(2n, n)",
				"(n + 1) * factorial(n) * ((n + 1) * factorial(n)) * binomial(2 * n + 2, n + 1) = "+
					"(2 * n + 2) * (2 * n + 1) * (factorial(n) * factorial(n) * binomial(2 * n, n))",
				ByArith(
					oneStep,
					twoSteps,
					FactorialFormula.At(a.TermAs[Nat]("2 * n + 2"), a.TermAs[Nat]("n + 1")),
					FactorialFormula.At(a.TermAs[Nat]("2 * n"), n)))
			a.Show(
				"cancel the common factor (n + 1)·n!², which is not 0",
				ByArith(
					squares,
					nat_arith.MulEqLCancel.At(
						a.TermAs[Nat]("(n + 1) * factorial(n) * factorial(n)"),
						a.TermAs[Nat]("(n + 1) * binomial(2 * n + 2, n + 1)"),
						a.TermAs[Nat]("2 * (2 * n + 1) * binomial(2 * n, n)")),
					nat_arith.FactorialNonzero.At(n),
					nat_arith.MulEqZero.At(a.TermAs[Nat]("(n + 1) * factorial(n)"), nFactorial)))
		}),
})}

// CentralBinomialLowerBound — C(2n, n) is at least 4ⁿ/(2n + 1). By induction
// on n: C(0, 0) = 1, and the recurrence carries the bound one step, since
// (2n + 3)·C(2n + 2, n + 1) ≥ 2(n + 1)·C(2n + 2, n + 1) = 4(2n + 1)·C(2n, n)
// ≥ 4·4ⁿ.
var CentralBinomialLowerBound = centralBinomialLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialLowerBound",
	Key:  "prop_b581cbfb6fd574a4",
	Build: family.Theorem(
		"∀n:num. 4 ^ n ≤ (2 * n + 1) * binomial(2 * n, n)",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"4⁰ = 1 = 1·C(0, 0)",
				ByArith(Diagonal.At(a.TermAs[Nat]("0")), nat_arith.NatPow))
			a.Step(
				"from n to n + 1 the recurrence multiplies C(2n, n) by 2(2n + 1)/(n + 1)",
				func(b *Argument, ih Fact) {
					n := b.TermAs[Nat]("n")
					b.Do(
						// ↦ 4^(n + 1) ≤ (2n + 2 + 1)·C(2n + 2, n + 1)
						Simp(Fwd(nat_arith.Add1), Fwd(nat_arith.LeftAddDistrib), Fwd(nat_arith.MulOne)))
					b.Show(
						"(2n + 3)·C(2n + 2, n + 1) ≥ 2(n + 1)·C(2n + 2, n + 1) = 4(2n + 1)·C(2n, n) ≥ 4·4ⁿ",
						ByArith(
							ih,
							CentralBinomialRecurrence.At(n),
							nat_arith.PowAdd.At(b.TermAs[Nat]("4"), n, b.TermAs[Nat]("1"))))
				})
		}),
})}

// MiddleBinomialOddBound — binomial(2m + 1, m) ≤ 4^m: binomial(2m + 1, m) and
// binomial(2m + 1, m + 1) are equal, and they are two terms of the row
// Σ_k binomial(2m + 1, k) = 2^(2m + 1), one in each half of 0 .. 2m + 1, so
// twice binomial(2m + 1, m) is at most 2^(2m + 1) = 2·4^m.
var MiddleBinomialOddBound = middleBinomialOddBoundThm{family.Add(registry.ProofEntry{
	Name: "MiddleBinomialOddBound",
	Key:  "prop_9ee89f823f400394",
	Build: family.Theorem(
		"∀m:num. binomial(2 * m + 1, m) ≤ 4 ^ m",
		func(a *Argument, m *Expr[Nat]) {
			top := a.TermAs[Nat]("2 * m + 1")
			next := a.TermAs[Nat]("m + 1")
			row := a.TermAs[Fun[Nat, Nat]]("λk:num. binomial(2 * m + 1, k)")
			symmetric := a.Have(
				"m and m + 1 are complementary columns in row 2m + 1",
				"binomial(2 * m + 1, m + 1) = binomial(2 * m + 1, m)",
				ByArith(Symmetry.At(top, m)))
			rowSum := a.Have(
				"the row sums to 2^(2m + 1), the binomial expansion of (1 + 1)^(2m + 1)",
				"Σ_{k∈0 .. 2 * m + 1} binomial(2 * m + 1, k) = 2 ^ (2 * m + 1)",
				ByArith(Expansion.At(top, a.TermAs[Nat]("1"), a.TermAs[Nat]("1"))))
			halves := a.Have(
				"0 .. 2m + 1 is cut after m",
				"0 .. 2 * m + 1 = (0 .. m) ∪ (m + 1 .. 2 * m + 1)",
				ByArith(num_segment.CombineRight.At(a.TermAs[Nat]("0"), m, top)))
			lower := a.TermAs[Set[Nat]]("0 .. m")
			upper := a.TermAs[Set[Nat]]("m + 1 .. 2 * m + 1")
			split := a.Have(
				"so the row sum is the sum over the lower half plus the sum over the upper half",
				"Σ_{k∈0 .. 2 * m + 1} binomial(2 * m + 1, k) = "+
					"Σ_{k∈0 .. m} binomial(2 * m + 1, k) + Σ_{k∈m + 1 .. 2 * m + 1} binomial(2 * m + 1, k)",
				ByArith(
					halves,
					nat_sum.Union.At(lower, upper, row),
					num_segment.Finite,
					num_segment.Disjoint.At(a.TermAs[Nat]("0"), m, next, top)))
			inLower := a.Have(
				"binomial(2m + 1, m) is a term of the lower half",
				"binomial(2 * m + 1, m) ≤ Σ_{k∈0 .. m} binomial(2 * m + 1, k)",
				ByArith(nat_sum.TermLeSum.At(row, lower, m), num_segment.Finite))
			inUpper := a.Have(
				"binomial(2m + 1, m + 1) is a term of the upper half",
				"binomial(2 * m + 1, m + 1) ≤ Σ_{k∈m + 1 .. 2 * m + 1} binomial(2 * m + 1, k)",
				ByArith(nat_sum.TermLeSum.At(row, upper, next), num_segment.Finite))
			a.Show(
				"so 2·binomial(2m + 1, m) ≤ 2^(2m + 1) = 2·4^m",
				ByArith(
					inLower,
					inUpper,
					symmetric,
					split,
					rowSum,
					nat_arith.PowAdd.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("2 * m"), a.TermAs[Nat]("1")),
					nat_arith.PowPow.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("2"), m)))
		}),
})}
