// exp.go — the exponential series and its sum, and the functional
// equation, read off the Cauchy product of two such series.

package real_exp_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpSums — the exponential series converges, and exp(x) is its sum.
// Each term is the one before times x/(n + 1), and past an index N with
// 2|x| ≤ N that factor is at most 1/2 in size, so the series has a sum
// by the ratio test. real_exp(x) is a sum of the series chosen by
// Hilbert's ε, and the choice succeeds wherever there is one to make.
var ExpSums = expSumsThm{family.Add(registry.ProofEntry{
	Name: "ExpSums",
	Key:  "prop_5401c5b6f4c37e4",
	Build: family.Theorem("∀x:real. real_sums(λn:num. real_pow(x, n) / &factorial(n), exp(x))",
		func(arg *Argument, x *Expr[Real]) {
			arg.Do(Unfold(RealExpDef))

			converges := arg.Have(
				"the series has a sum",
				"∃s:real. real_sums(λn:num. real_pow(x, n) / &factorial(n), s)",
				Derive(func(d *Argument) {
					N, beyond := d.ObtainAs[Nat](
						"some index N is at least 2|x|, ℝ being Archimedean",
						"∃N:num. &2 * |x| ≤ &N",
						By(real_archimedean.ExistsNumAbove.At(d.TermAs[Real]("&2 * |x|"))))
					ratio := d.Have(
						"past N each term is at most half the one before in size",
						Statement{
							Binders: "∀n:num.",
							Hypotheses: []string{
								"N ≤ n",
							},
							Conclusion: "|real_pow(x, n + 1) / &factorial(n + 1)| ≤ &1 / &2 * |real_pow(x, n) / &factorial(n)|",
						},
						Derive(func(e *Argument) {
							n := e.FixAs[Nat]()
							past := e.Assume()
							next := e.Have(
								"the next term is this one times x/(n + 1), as xⁿ⁺¹ = x·xⁿ and (n + 1)! = (n + 1)·n!",
								"real_pow(x, n + 1) / &factorial(n + 1) = x / &(n + 1) * (real_pow(x, n) / &factorial(n))",
								Simp(
									Rev(nat_arith.Add1),
									Fwd(real_pow.PowExpSucClause),
									Fwd(nat_arith.Factorial),
									Fwd(real_construction.OfNumMul),
									Fwd(real_field.RealDivDef),
									Fwd(field.InvMul.Read(real_field.Field))),
								ByArith())
							e.Have(
								"n + 1 is positive — the guard of the rewrite LessEqDivMulRight below",
								"&0 < &(n + 1)",
								ByArith())
							small := e.Have(
								"and x/(n + 1) is at most 1/2 in size: 2|x| ≤ N ≤ n < n + 1",
								"|x / &(n + 1)| ≤ &1 / &2",
								// ↦ |x| ≤ 1/2·(n + 1)
								Simp(Fwd(real_sgn_abs.AbsDiv), Fwd(real_sgn_abs.AbsOfNum), Fwd(real_order_field.LessEqDivMulRight)),
								ByArith(
									past,
									beyond,
									real_construction.OfNumLessEq.At(N, n),
									real_construction.OfNumAdd.At(n, e.TermAs[Nat]("1"))))
							term := e.TermAs[Real]("real_pow(x, n) / &factorial(n)")
							e.Show(
								"so the next term is |x/(n + 1)| times this one in size, at most half of it",
								next.Rw(),
								Simp(Fwd(real_sgn_abs.AbsMul)),
								By(small, real_sgn_abs.AbsNonneg.At(term), real_order_ring.LessEqMulRight))
						}))
					d.Show(
						"so the series has a sum by the ratio test",
						By(ratio, real_series.Ratio))
				}))

			arg.Show(
				"exp(x) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}

// ExpZero — at 0 the exponential series is 1, 0, 0, …: its first term
// 0⁰/0! is 1 and every later one is 0. So each partial sum is 1, the
// series sums to 1, and a series has only one sum.
var ExpZero = expZeroThm{family.Add(registry.ProofEntry{
	Name: "ExpZero",
	Key:  "prop_f672f73596ffd85b",
	Build: family.Theorem("exp(&0) = &1",
		func(arg *Argument) {
			series := arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(&0, k) / &factorial(k)")
			partialSums := arg.Have(
				"every partial sum of the series at 0 is its first term, 0⁰/0! = 1",
				"(λn:num. Σ_{k∈0 .. n} real_pow(&0, k) / &factorial(k)) = (λn:num. &1)",
				Funext(),
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					tail := d.Have(
						"past the first, each term 0ⁱ/i! is 0, as 0ⁱ is for i ≥ 1",
						"∀i:num. 1 ≤ i ∧ i ≤ n ⇒ real_pow(&0, i) / &factorial(i) = &0",
						d.ForEach(func(i *Expr[Nat]) Action { return ByArith(real_pow.ZeroPow.At(i)) }))
					zero, one := d.TermAs[Nat]("0"), d.TermAs[Nat]("1")
					d.Show(
						"peel the first term off 0 .. n: it is 0⁰/0! = 1, and the rest is a sum of zeros over 1 .. n",
						ByArith(
							tail,
							real_sum.PeelLeft.At(zero, n, series),
							nat_order.ZeroLessEq.At(n),
							real_sum.IntervalEqZero.At(one, n, series)))
				}))
			sums := arg.Have(
				"so the partial sums are the constant sequence 1, and the series at 0 sums to 1",
				"real_sums(λn:num. real_pow(&0, n) / &factorial(n), &1)",
				Simp(Fwd(real_series.RealSumsDef)),
				partialSums.Rw(),
				By(real_sequences.LimitConst.At(arg.TermAs[Real]("&1"))))
			arg.Show(
				"exp(0) is a sum of the same series, and a series has only one sum",
				By(sums, ExpSums.At(arg.TermAs[Real]("&0")), real_series.SumsUnique))
		}),
})}

// ExpProductTerm — the binomial theorem divided by n!. The divisor goes
// into the sum, and term by term C(n, k)/n! is 1/(k!·(n − k)!), because
// k!·(n − k)!·C(n, k) = n! and C(n, k), taken within its row, is not 0.
var ExpProductTerm = expProductTermThm{family.Add(registry.ProofEntry{
	Name: "ExpProductTerm",
	Key:  "prop_3c19cab4a833c64",
	Build: family.Theorem(
		"∀x y:real. ∀n:num. "+
			"    Σ_{k∈0 .. n} real_pow(x, k) / &factorial(k) * (real_pow(y, n - k) / &factorial(n - k)) = "+
			"    real_pow(x + y, n) / &factorial(n)",
		func(arg *Argument, x, y *Expr[Real], n *Expr[Nat]) {
			termwise := arg.Have(
				"term by term, the product of the two series' terms is the binomial term divided by n!",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"0 ≤ k",
						"k ≤ n",
					},
					Conclusion: "real_pow(x, k) / &factorial(k) * (real_pow(y, n - k) / &factorial(n - k)) = " +
						"&binomial(n, k) * real_pow(x, k) * real_pow(y, n - k) / &factorial(n)",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					inRow := b.Assume()
					factorials := b.Have(
						"k!·(n − k)!·C(n, k) = n!, carried into ℝ, where the embedding multiplies",
						"&factorial(k) * &factorial(n - k) * &binomial(n, k) = &factorial(n)",
						By(
							inRow,
							binomial.FactorialFormula.At(n, k),
							real_construction.OfNumMul.At(b.TermAs[Nat]("factorial(k)"), b.TermAs[Nat]("factorial(n - k)")),
							real_construction.OfNumMul.At(
								b.TermAs[Nat]("factorial(k) * factorial(n - k)"), b.TermAs[Nat]("binomial(n, k)"))))
					entryNonzero := b.Have(
						"column k lies within row n, so C(n, k) is not 0",
						"binomial(n, k) ≠ 0",
						ByArith(inRow, binomial.EqZero.At(n, k)))
					nonzero := b.Have(
						"nor is its image in ℝ",
						"&binomial(n, k) ≠ &0",
						By(entryNonzero, real_construction.OfNumEq))
					b.Show(
						"n! is k!·(n − k)!·C(n, k), so C(n, k) cancels against its inverse, leaving the two quotients",
						// ↦ … = &binomial(n, k) * … / (&factorial(k) * &factorial(n - k) * &binomial(n, k))
						factorials.RwRev(),
						Simp(Fwd(real_field.RealDivDef), Fwd(field.InvMul.Read(real_field.Field))),
						ByArith(nonzero))
				}))

			arg.Show(
				"divide the binomial theorem by n!",
				CalcEq(
					Leg(
						arg.TermAs[Real](
							"Σ_{k∈0 .. n} &binomial(n, k) * real_pow(x, k) * real_pow(y, n - k) / &factorial(n)"),
						"term by term, as above",
						By(termwise, real_sum.IntervalCongruence)),
					Leg(
						arg.TermAs[Real](
							"(Σ_{k∈0 .. n} &binomial(n, k) * real_pow(x, k) * real_pow(y, n - k)) / &factorial(n)"),
						"n! divides every term alike, so it divides the sum",
						Simp(Fwd(real_field.RealDivDef)),
						Cite(real_sum.ScalarRight.Inst[Nat]())),
					FinalLeg(
						"and the sum is (x + y)ⁿ by the binomial theorem",
						Cite(real_pow.BinomialExpansion))))
		}),
})}

// ExpAdd — the functional equation of exp. The exponential series
// converges absolutely, the sizes of its terms at z being its terms at
// |z|, so the Cauchy product of the series at x and at y sums to
// exp(x)·exp(y). Term by term that product is the series at x + y,
// which sums to exp(x + y), and a series has only one sum.
var ExpAdd = expAddThm{family.Add(registry.ProofEntry{
	Name: "ExpAdd",
	Key:  "prop_f25314381f154144",
	Build: family.Theorem("∀x y:real. exp(x + y) = exp(x) * exp(y)",
		func(arg *Argument, x, y *Expr[Real]) {
			absolutely := arg.Have(
				"the series converges absolutely: the sizes of its terms at z are its terms at |z|",
				"∀z:real. real_sums(λn:num. |real_pow(z, n) / &factorial(n)|, exp(|z|))",
				Derive(func(d *Argument) {
					d.FixAs[Real]()
					d.Show(
						"|zⁿ/n!| = |z|ⁿ/n!, and the series at |z| sums to exp(|z|)",
						// ↦ real_sums(λn. real_pow(real_abs(z), n) / &factorial(n), real_exp(real_abs(z)))
						Simp(Fwd(real_sgn_abs.AbsDiv), Fwd(real_pow.AbsPow), Fwd(real_sgn_abs.AbsOfNum)),
						By(ExpSums.At(d.TermAs[Real]("|z|"))))
				}))

			product := arg.Have(
				"so the Cauchy product of the series at x and at y sums to exp(x)·exp(y)",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(x, k) / &factorial(k) * (real_pow(y, n - k) / &factorial(n - k)), "+
					"    exp(x) * exp(y))",
				By(ExpSums.At(x), ExpSums.At(y), absolutely.At(x), absolutely.At(y), real_series.CauchyProduct))
			seriesAtSum := arg.Have(
				"its n-th term is (x + y)ⁿ/n!, so it is the series at x + y",
				"real_sums(λn:num. real_pow(x + y, n) / &factorial(n), exp(x) * exp(y))",
				By(product, ExpProductTerm))
			arg.Show(
				"which sums to exp(x + y) as well, and a series has only one sum",
				By(seriesAtSum, ExpSums.At(arg.TermAs[Real]("x + y")), real_series.SumsUnique))
		}),
})}

// ExpNeg — the functional equation at x and −x. It makes exp(x)·exp(−x)
// the value of exp at x + −x = 0, which is 1, and a number whose product
// with exp(x) is 1 is the inverse of exp(x).
var ExpNeg = expNegThm{family.Add(registry.ProofEntry{
	Name: "ExpNeg",
	Key:  "prop_26825e77cbf19f82",
	Build: family.Theorem("∀x:real. exp(-x) = real_inv(exp(x))",
		func(arg *Argument, x *Expr[Real]) {
			negX := arg.TermAs[Real]("-x")
			unit := arg.Have(
				"exp(x)·exp(−x) is exp(x + −x) = exp(0), which is 1",
				"exp(x) * exp(-x) = &1",
				By(ExpAdd.At(x, negX), real_ring.AddRightInv.At(x), ExpZero))
			arg.Show(
				"so exp(−x) inverts exp(x), and an inverse is unique",
				By(
					unit,
					field.InvRightUnique.Read(real_field.Field).At(
						arg.TermAs[Real]("exp(x)"), arg.TermAs[Real]("exp(-x)"))))
		}),
})}

// ExpNatMul — exp turns a natural multiple into a power, by induction on
// the multiple with x held fixed. At 0 the argument is 0 and both sides
// are 1. One step up the argument gains one more x, so the functional
// equation splits off one more factor exp(x), and the induction
// hypothesis reads what is left as the power one below.
var ExpNatMul = expNatMulThm{family.Add(registry.ProofEntry{
	Name: "ExpNatMul",
	Key:  "prop_bcdf110d668f5890",
	Build: family.Theorem("∀n:num. ∀x:real. exp(&n * x) = real_pow(exp(x), n)",
		func(arg *Argument, n *Expr[Nat], x *Expr[Real]) {
			arg.Induct(n)
			arg.Base(
				"at 0 the argument 0·x is 0, and exp(0) = 1 is the empty power exp(x)⁰",
				Simp(Fwd(real_ring.MulLeftZero), Fwd(ExpZero)),
				Cite(real_pow.PowExpZeroClause))
			arg.Step(
				"at suc(n) the argument gains one more x, and exp one more factor exp(x)",
				func(b *Argument, ih Fact) {
					b.Show(
						"so exp((n + 1)·x) is exp(x)ⁿ·exp(x), which is exp(x)ⁿ⁺¹",
						CalcEq(
							Leg(
								b.TermAs[Real]("exp(&n * x + x)"),
								"the successor embeds as n + 1, and (n + 1)·x = n·x + 1·x = n·x + x",
								Simp(Fwd(real_ring.OfNumSuc), Fwd(real_ring.RightDistrib)),
								Cite(real_construction.MulLeftId)),
							Leg(
								b.TermAs[Real]("exp(&n * x) * exp(x)"),
								"the functional equation splits off the factor exp(x)",
								Cite(ExpAdd)),
							Leg(
								b.TermAs[Real]("real_pow(exp(x), n) * exp(x)"),
								"the induction hypothesis",
								By(Normalized, ih)),
							FinalLeg(
								"one more factor of the base, taken in either order, is the next power",
								Simp(Fwd(real_pow.PowExpSucClause)),
								Cite(real_construction.MulSym))))
				})
		}),
})}
