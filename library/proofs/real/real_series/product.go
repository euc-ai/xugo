// product.go — the Cauchy product of two series: for nonnegative
// convergent series, and for absolutely convergent ones.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// CauchyProductNonneg — the Cauchy product of two nonnegative
// convergent series sums to the product of their sums.
//
// Write A and B for the partial sums of a and b, and C(N) for the N-th
// partial sum of the Cauchy product, the sum of a(i)·b(j) over the
// triangle i + j ≤ N. Summed by rows, C(N) = Σ_{i ≤ N} a(i)·B(N − i). As
// B only grows and every a(i) is nonnegative, C(N) is at most
// Σ_{i ≤ N} a(i)·B(N) = A(N)·B(N), the sum over the square i, j ≤ N;
// and once M + M ≤ N it is at least A(M)·B(M), the square i, j ≤ M,
// since each row i ≤ M reaches N − i ≥ M and the rows past M only add.
// The squares A(N)·B(N) tend to s·t: given ε, past some M they are
// within ε of it, and past M + M each C(n) lies between two of them.
var CauchyProductNonneg = cauchyProductNonnegThm{family.Add(registry.ProofEntry{
	Name: "CauchyProductNonneg",
	Key:  "prop_ed0d533222504025",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n) ∧ &0 ≤ b(n)",
			"real_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "real_sums(λn:num. Σ_{k∈0 .. n} a(k) * b(n - k), s * t)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], s, t *Expr[Real], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"the terms of a and b are nonnegative",
				"a sums to s",
				"b sums to t")
			nonneg, sumsA, sumsB := parts[0], parts[1], parts[2]
			zero := arg.TermAs[Nat]("0")

			aNonneg := arg.Have(
				"the terms of a are nonnegative",
				"∀n:num. &0 ≤ a(n)",
				arg.ForEach(func(n *Expr[Nat]) Action { return By(nonneg.At(n)) }))
			bNonneg := arg.Have(
				"and so are the terms of b",
				"∀n:num. &0 ≤ b(n)",
				arg.ForEach(func(n *Expr[Nat]) Action { return By(nonneg.At(n)) }))

			products := arg.TermAs[Fun2[Nat, Nat, Real]]("λi:num. λj:num. a(i) * b(j)")
			rows := arg.Have(
				"summed by rows, the triangle i + j ≤ N puts each a(i) against the partial sum of b up to N − i",
				"∀N:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) = Σ_{i∈0 .. N} a(i) * Σ_{j∈0 .. N - i} b(j)",
				arg.ForEach(func(N *Expr[Nat]) Action {
					return Chain(Simp(Fwd(real_sum.ScalarLeft.Inst[Nat]())), By(real_sum.Antidiagonal.At(N, products)))
				}))

			grows := arg.Have(
				"the partial sums of b only grow: a longer one adds only nonnegative terms",
				"∀m n:num. m ≤ n ⇒ Σ_{j∈0 .. m} b(j) ≤ Σ_{j∈0 .. n} b(j)",
				Derive(func(d *Argument) {
					m := d.FixAs[Nat]()
					n := d.FixAs[Nat]()
					d.Show(
						"extend the segment 0 .. m to 0 .. n",
						By(Normalized, bNonneg, real_sum.IntervalExtend.At(zero, m, n, b)))
				}))

			upper := arg.Have(
				"each partial sum of the Cauchy product is at most the "+
					"product of the partial sums of a and b up to the same index",
				"∀N:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) ≤ (Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j)",
				Derive(func(d *Argument) {
					N := d.FixAs[Nat]()
					termwise := d.Have(
						"row i stops at N − i, and b's partial sum there is at most the one "+
							"up to N — stated for 0 ≤ i ≤ N, the guard the order of sums reads",
						"∀i:num. 0 ≤ i ∧ i ≤ N ⇒ a(i) * (Σ_{j∈0 .. N - i} b(j)) ≤ a(i) * Σ_{j∈0 .. N} b(j)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							e.Assume()
							e.Show(
								"scaled by the nonnegative a(i)",
								ByArith(aNonneg.At(i), grows.At(e.TermAs[Nat]("N - i"), N)))
						}))
					triangleRows := d.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} a(i) * Σ_{j∈0 .. N - i} b(j)")
					squareRows := d.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} a(i) * Σ_{j∈0 .. N} b(j)")
					d.Show(
						"the triangle i + j ≤ N lies inside the square i, j ≤ N",
						real_order_ring.OrderCalc(
							d.Ctx()).CalcLeibniz(d.TermAs[Real]("Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k)"),
							EqLeg(
								triangleRows,
								"summed by rows",
								By(rows.At(N))),
							LeLeg(
								squareRows,
								"row by row the partial sum of b is raised to the one up to N",
								By(termwise, real_sum.IntervalMonotone.At(zero, N, triangleRows.Summand(), squareRows.Summand()))),
							EqLeg(
								d.TermAs[Real]("(Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j)"),
								"and the common factor, the partial sum of b up to N, comes out of the sum",
								By(real_sum.ScalarRight.At(d.TermAs[Real]("Σ_{j∈0 .. N} b(j)"), a, squareRows.Range())))))
				}))

			lower := arg.Have(
				"past M + M each partial sum of the Cauchy product is at "+
					"least the product of the partial sums of a and b up to M",
				Statement{
					Binders: "∀M N:num.",
					Hypotheses: []string{
						"M + M ≤ N",
					},
					Conclusion: "(Σ_{i∈0 .. M} a(i)) * (Σ_{j∈0 .. M} b(j)) ≤ Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k)",
				},
				Derive(func(d *Argument) {
					M := d.FixAs[Nat]()
					N := d.FixAs[Nat]()
					far := d.Assume()
					termwise := d.Have(
						"each row i up to M reaches N − i ≥ M — stated for 0 ≤ i ≤ M, the guard the order of sums reads",
						"∀i:num. 0 ≤ i ∧ i ≤ M ⇒ a(i) * (Σ_{j∈0 .. M} b(j)) ≤ a(i) * Σ_{j∈0 .. N - i} b(j)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							early := e.Assume()
							e.Show(
								"so the partial sum of b up to M is at most the one up to N − i, scaled by the nonnegative a(i)",
								ByArith(early, far, aNonneg.At(i), grows.At(M, e.TermAs[Nat]("N - i"))))
						}))
					among := d.Have(
						"the rows up to M are among the rows up to N",
						"M ≤ N",
						ByArith(far))
					rowTerms := d.Have(
						"and every row contributes a nonnegative term",
						"∀i:num. &0 ≤ a(i) * Σ_{j∈0 .. N - i} b(j)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							partial := e.Have(
								"the partial sum of b up to N − i is a sum of nonnegative terms",
								"&0 ≤ Σ_{j∈0 .. N - i} b(j)",
								By(bNonneg, real_sum.Nonneg.At(e.TermAs[Set[Nat]]("0 .. N - i"), b)))
							e.Show(
								"a product of two nonnegatives",
								ByArith(aNonneg.At(i), partial))
						}))
					squareRows := d.BigOpAs[Nat, Real]("Σ_{i∈0 .. M} a(i) * Σ_{j∈0 .. M} b(j)")
					reachingRows := d.BigOpAs[Nat, Real]("Σ_{i∈0 .. M} a(i) * Σ_{j∈0 .. N - i} b(j)")
					triangleRows := d.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} a(i) * Σ_{j∈0 .. N - i} b(j)")
					d.Show(
						"and past M + M it contains the square i, j ≤ M",
						real_order_ring.OrderCalc(
							d.Ctx()).CalcLeibniz(d.TermAs[Real]("(Σ_{i∈0 .. M} a(i)) * Σ_{j∈0 .. M} b(j)"),
							EqLeg(
								squareRows,
								"the common factor, the partial sum of b up to M, goes into the sum",
								By(real_sum.ScalarRight.At(d.TermAs[Real]("Σ_{j∈0 .. M} b(j)"), a, squareRows.Range()))),
							LeLeg(
								reachingRows,
								"row by row the partial sum of b is raised to the one up to N − i",
								By(termwise, real_sum.IntervalMonotone.At(zero, M, squareRows.Summand(), reachingRows.Summand()))),
							LeLeg(
								triangleRows,
								"the rows past M only add",
								By(among, rowTerms, real_sum.IntervalExtend.At(zero, M, N, triangleRows.Summand()))),
							EqLeg(
								d.TermAs[Real]("Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k)"),
								"which is the partial sum of the Cauchy product, summed by rows",
								By(rows.At(N)))))
				}))

			toS := arg.Have(
				"the partial sums of a tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sumsA, RealSumsDef))
			toT := arg.Have(
				"and those of b to t",
				"(λn:num. Σ_{k∈0 .. n} b(k)) ⟶ t",
				By(sumsB, RealSumsDef))
			squareLimit := arg.Have(
				"so their products tend to s·t",
				"(λn:num. (Σ_{k∈0 .. n} a(k)) * Σ_{k∈0 .. n} b(k)) ⟶ s * t",
				By(toS, toT, real_sequences.LimitMul))
			near := arg.Unfolded(squareLimit, real_sequences.RealConvergesToDef)

			limit := arg.Have(
				"the partial sums of the Cauchy product tend to s·t",
				"(λN:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k)) ⟶ s * t",
				Simp(Fwd(real_sequences.RealConvergesToDef)),
				Derive(func(d *Argument) {
					ε := d.FixAs[Real]()
					pos := d.Assume()
					M, tail := d.ObtainAs[Nat](
						"past some M the products of the partial sums of a and b are within ε of s·t",
						"∃M:num. ∀m:num. M ≤ m ⇒ |(Σ_{k∈0 .. m} a(k)) * Σ_{k∈0 .. m} b(k) - s * t| < ε",
						By(near.At(ε), pos))
					d.Take(d.TermAs[Nat]("M + M"))
					n := d.FixAs[Nat]()
					far := d.Assume()
					d.Show(
						"the partial sum of the Cauchy product up to n lies between "+
							"the products up to M and up to n, both within ε of s·t",
						ByArith(far, lower.At(M, n), upper.At(n), tail.At(M), tail.At(n)))
				}))
			arg.Show(
				"which is the Cauchy product summing to s·t",
				By(limit, RealSumsDef))
		}),
})}

// CauchyProduct — the Cauchy product of two absolutely convergent
// series sums to the product of their sums.
//
// Write A and B for the partial sums of a and b, A′ and B′ for those
// of |a| and |b|, and C(N), C′(N) for the N-th partial sums of the
// Cauchy products of a with b and of |a| with |b|. Summed by rows, the
// gap A(N)·B(N) − C(N) between the square and the triangle puts each
// a(i) against the stretch B(N) − B(N − i) of b, which in size is at
// most the same stretch of |b|; so the gap is, in size, at most the gap
// A′(N)·B′(N) − C′(N) for |a| and |b|. Both A′(N)·B′(N) and, by the
// nonnegative case, C′(N) tend to u·v, so that gap tends to 0; C(N)
// stays within it of A(N)·B(N), which tends to s·t, and so tends to s·t
// as well.
var CauchyProduct = cauchyProductThm{family.Add(registry.ProofEntry{
	Name: "CauchyProduct",
	Key:  "prop_a8697c6c5cd76592",
	Build: family.Sections(Statement{
		Binders: "∀a b:(num → real). ∀s t u v:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
			"real_sums(b, t)",
			"real_sums(λn:num. |a(n)|, u)",
			"real_sums(λn:num. |b(n)|, v)",
		},
		Conclusion: "real_sums(λn:num. Σ_{k∈0 .. n} a(k) * b(n - k), s * t)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			gapByRows := ctx.Lemma("∀a b:(num → real). ∀N:num. "+
				"    (Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j) - Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) = "+
				"    Σ_{i∈0 .. N} a(i) * (Σ_{j∈0 .. N} b(j) - Σ_{j∈0 .. N - i} b(j))",
				func(arg *Argument, a, b *Arrow[Nat, Real], N *Expr[Nat]) {
					products := arg.TermAs[Fun2[Nat, Nat, Real]]("λi:num. λj:num. a(i) * b(j)")
					rows := arg.Have(
						"summed by rows, the triangle i + j ≤ N puts each a(i) against the partial sum of b up to N − i",
						"Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) = Σ_{i∈0 .. N} a(i) * Σ_{j∈0 .. N - i} b(j)",
						Simp(Fwd(real_sum.ScalarLeft.Inst[Nat]())),
						By(real_sum.Antidiagonal.At(N, products)))
					arg.Show(
						"row by row, a(i) against the partial sum of b up to N sums "+
							"to the square, and against the one up to N − i to the triangle",
						Simp(
							Fwd(real_ring.SubLeftDistrib),
							Fwd(real_sum.IntervalSub),
							Rev(real_sum.ScalarRight.Inst[Nat]())),
						By(rows))
				})

			gapDominated := ctx.Lemma("∀a b:(num → real). ∀N:num. "+
				"    |Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) - (Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j)| ≤ "+
				"    (Σ_{i∈0 .. N} |a(i)|) * Σ_{j∈0 .. N} |b(j)| - Σ_{n∈0 .. N} Σ_{k∈0 .. n} |a(k)| * |b(n - k)|",
				func(arg *Argument, a, b *Arrow[Nat, Real], N *Expr[Nat]) {
					zero := arg.TermAs[Nat]("0")
					absA := arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n)|")
					absB := arg.TermAs[Fun[Nat, Real]]("λn:num. |b(n)|")
					stretch := arg.Have(
						"a stretch of b is at most, in size, the same stretch of |b|",
						Statement{
							Binders: "∀m n:num.",
							Hypotheses: []string{
								"m ≤ n",
							},
							Conclusion: "|Σ_{j∈0 .. n} b(j) - Σ_{j∈0 .. m} b(j)| ≤ Σ_{j∈0 .. n} |b(j)| - Σ_{j∈0 .. m} |b(j)|",
						},
						Derive(func(e *Argument) {
							m := e.FixAs[Nat]()
							n := e.FixAs[Nat]()
							upTo := e.Assume()
							offset, offsetEq := e.ObtainAs[Nat](
								"n is m plus an offset d",
								"∃d:num. n = m + d",
								By(upTo, nat_order.LessEqExists.At(n, m)))
							e.Show(
								"both sums split after m, and the triangle inequality bounds the stretch m + 1 .. m + d",
								offsetEq.Rw(),
								ByArith(
									real_sum.SplitAt.At(zero, m, offset, b),
									real_sum.SplitAt.At(zero, m, offset, absB),
									real_sum.IntervalTriangle.At(e.TermAs[Nat]("m + 1"), e.TermAs[Nat]("m + d"), b)))
						}))
					rowBound := arg.Have(
						"row i: a(i) against b's stretch past N − i is at most |a(i)| against "+
							"that of |b| — stated for 0 ≤ i ≤ N, the guard the order of sums reads",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"0 ≤ i",
								"i ≤ N",
							},
							Conclusion: "|a(i) * (Σ_{j∈0 .. N} b(j) - Σ_{j∈0 .. N - i} b(j))| ≤ " +
								"|a(i)| * (Σ_{j∈0 .. N} |b(j)| - Σ_{j∈0 .. N - i} |b(j)|)",
						},
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]()
							d.Assume()
							stretchAtMost := d.Have(
								"the stretch of b past N − i is at most that of |b|",
								"|Σ_{j∈0 .. N} b(j) - Σ_{j∈0 .. N - i} b(j)| ≤ Σ_{j∈0 .. N} |b(j)| - Σ_{j∈0 .. N - i} |b(j)|",
								ByArith(stretch.At(d.TermAs[Nat]("N - i"), N)))
							d.Show(
								"the size of the product is |a(i)| times the size of the "+
									"stretch, whose bound scales by the nonnegative |a(i)|",
								Simp(Fwd(real_sgn_abs.AbsMul)),
								By(stretchAtMost, real_sgn_abs.AbsNonneg.At(a.Apply(i)), real_order_ring.LessEqMulLeft))
						}))
					gapRows := arg.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} a(i) * (Σ_{j∈0 .. N} b(j) - Σ_{j∈0 .. N - i} b(j))")
					absGapRows := arg.BigOpAs[Nat, Real](
						"Σ_{i∈0 .. N} |a(i)| * (Σ_{j∈0 .. N} |b(j)| - Σ_{j∈0 .. N - i} |b(j)|)")
					arg.Show(
						"summed over the rows, the bound on each row bounds the whole gap",
						real_order_ring.OrderCalc(arg.Ctx()).CalcLeibniz(
							arg.TermAs[Real](
								"|Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k) - (Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j)|"),
							EqLeg(
								arg.TermAs[Real]("|Σ_{i∈0 .. N} a(i) * (Σ_{j∈0 .. N} b(j) - Σ_{j∈0 .. N - i} b(j))|"),
								"in size, the gap between the square and the triangle, summed by rows",
								ByArith(At(gapByRows, a, b, N))),
							LeLeg(
								absGapRows,
								"row by row, by the bound on each row",
								By(rowBound, real_sum.IntervalDominated.At(zero, N, gapRows.Summand(), absGapRows.Summand()))),
							EqLeg(
								arg.TermAs[Real](
									"(Σ_{i∈0 .. N} |a(i)|) * Σ_{j∈0 .. N} |b(j)| - Σ_{n∈0 .. N} Σ_{k∈0 .. n} |a(k)| * |b(n - k)|"),
								"which is the gap for |a| and |b|, summed by rows",
								By(At(gapByRows, absA, absB, N)))))
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				a, b *Arrow[Nat, Real],
				s, t, u, v *Expr[Real],
				hyps Fact,
			) {
				parts := arg.Conjuncts(
					hyps,
					"a sums to s",
					"b sums to t",
					"|a| sums to u",
					"|b| sums to v")
				sumsA, sumsB, sumsAbsA, sumsAbsB := parts[0], parts[1], parts[2], parts[3]
				absA := arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n)|")
				absB := arg.TermAs[Fun[Nat, Real]]("λn:num. |b(n)|")

				toS := arg.Have(
					"the partial sums of a tend to s",
					"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
					By(sumsA, RealSumsDef))
				toT := arg.Have(
					"those of b to t",
					"(λn:num. Σ_{k∈0 .. n} b(k)) ⟶ t",
					By(sumsB, RealSumsDef))
				toU := arg.Have(
					"those of |a| to u",
					"(λn:num. Σ_{k∈0 .. n} |a(k)|) ⟶ u",
					By(sumsAbsA, RealSumsDef))
				toV := arg.Have(
					"and those of |b| to v",
					"(λn:num. Σ_{k∈0 .. n} |b(k)|) ⟶ v",
					By(sumsAbsB, RealSumsDef))
				squareLimit := arg.Have(
					"so the products of the partial sums of a and b tend to s·t",
					"(λN:num. (Σ_{i∈0 .. N} a(i)) * Σ_{j∈0 .. N} b(j)) ⟶ s * t",
					By(toS, toT, real_sequences.LimitMul))
				absSquareLimit := arg.Have(
					"and those of |a| and |b| to u·v",
					"(λN:num. (Σ_{i∈0 .. N} |a(i)|) * Σ_{j∈0 .. N} |b(j)|) ⟶ u * v",
					By(toU, toV, real_sequences.LimitMul))
				absNonneg := arg.Have(
					"|a| and |b| have nonnegative terms",
					"∀n:num. &0 ≤ |a(n)| ∧ &0 ≤ |b(n)|",
					arg.ForEach(func(n *Expr[Nat]) Action {
						return By(real_sgn_abs.AbsNonneg.At(a.Apply(n)), real_sgn_abs.AbsNonneg.At(b.Apply(n)))
					}))
				absProduct := arg.Have(
					"so by the nonnegative case the Cauchy product of |a| and |b| sums to u·v",
					"real_sums(λn:num. Σ_{k∈0 .. n} |a(k)| * |b(n - k)|, u * v)",
					By(absNonneg, sumsAbsA, sumsAbsB, CauchyProductNonneg.At(absA, absB, u, v)))
				absTriangleLimit := arg.Have(
					"its partial sums tend to u·v",
					"(λN:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} |a(k)| * |b(n - k)|) ⟶ u * v",
					By(absProduct, RealSumsDef))

				uv := arg.TermAs[Real]("u * v")
				absSquare := arg.TermAs[Fun[Nat, Real]]("λN:num. (Σ_{i∈0 .. N} |a(i)|) * Σ_{j∈0 .. N} |b(j)|")
				absTriangle := arg.TermAs[Fun[Nat, Real]]("λN:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} |a(k)| * |b(n - k)|")
				gapVanishes := arg.Have(
					"so the gap between the square and the triangle for |a| and |b| tends to u·v − u·v = 0",
					"(λN:num. "+
						"    (Σ_{i∈0 .. N} |a(i)|) * "+
						"    Σ_{j∈0 .. N} |b(j)| - Σ_{n∈0 .. N} Σ_{k∈0 .. n} |a(k)| * "+
						"    |b(n - k)|) ⟶ "+
						"&0",
					By(
						absSquareLimit,
						absTriangleLimit,
						real_sequences.LimitSub.At(absSquare, absTriangle, uv, uv),
						real_ring.SubRefl.At(uv)))
				limit := arg.Have(
					"the Cauchy product's partial sums stay within that vanishing gap "+
						"of the products of the partial sums, so they tend to s·t as well",
					"(λN:num. Σ_{n∈0 .. N} Σ_{k∈0 .. n} a(k) * b(n - k)) ⟶ s * t",
					By(At(gapDominated, a, b), gapVanishes, squareLimit, real_sequences.LimitSqueezeDistance))
				arg.Show(
					"which is the Cauchy product summing to s·t",
					By(limit, RealSumsDef))
			})
		}),
})}
