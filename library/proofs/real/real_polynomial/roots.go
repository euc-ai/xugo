// roots.go — where a polynomial takes a value. A polynomial that is
// not constant takes any given value only finitely often, and the
// count is bounded by the degree: a nonzero coefficient sum of degree
// n has at most n roots. The one idea the movement rests on is that a
// polynomial's difference at two points factors through the
// difference of the points — p(x) − p(y) = (x − y)·q(x) with q again
// a coefficient sum, one degree lower — so a root r of p splits off a
// factor x − r, and the remaining roots are roots of q, which the
// degree below already bounds.
//
// The conventions are the closure movement's — `Normalized` for the
// leaves the normalizer decides, `Simp`'s direction read against the
// canonical orientation, the `↦` gloss beside a rewriting step, and an
// opened existential's witnesses keeping their statement names unless
// the proof already declares those names, in which case the claims
// spell the mints (`r₀`, `i₀`). One more belongs to this movement.
//
// Set equations are the working language here, and `BySets` closes a
// set equation or inclusion outright from a pointwise fact handed to
// it. Where the other side is an interval CONSTANT, which the set
// driver cannot expand, the equation is a cut of that interval at a
// point, and `sets/num_segment` states both cuts — below a point and
// above one — each under a guard putting the cut inside.

package real_polynomial

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The factorization
// ---------------------------------------------------------------------------
//
// The difference of a coefficient sum at two points is the sum of the
// differences a(i)·(xⁱ − yⁱ), and each of those factors through x − y
// by the geometric identity xⁱ − yⁱ = (x − y)·Σ_{j<i} xʲ·y^(i−1−j).
// What is left inside the factor is a triangle of terms, one row per
// power i and one entry per j below it; read by columns instead of by
// rows it is a coefficient sum in x, whose coefficient at xʲ collects
// the a(i)·y^(i−j−1) for i above j. The column reading is what makes
// the cofactor a polynomial of degree n − 1, and it is the one place
// the interval calculus has to be left for a moment: the two readings
// are the same restricted double sum, `real_sum.SwapRestricted`, with
// the index sets of the restrictions computed as intervals.

// DifferenceFactors — the cofactor is a coefficient sum of degree
// n − 1 in the first point. At n = 0 the left side is &0, and so is
// the right, its one column summing over the empty interval 1 .. 0.
var DifferenceFactors = differenceFactorsThm{family.Add(registry.ProofEntry{
	Name: "DifferenceFactors",
	Key:  "prop_9621a92b2502cd2e",
	Build: family.Sections(
		Statement{
			Binders: "∀a:(num → real). ∀x y:real. ∀n:num.",
			Conclusion: "sum(0 .. n, λi:num. a(i) * real_pow(x, i)) - " +
				"sum(0 .. n, λi:num. a(i) * real_pow(y, i)) = " +
				"(x - y) * " +
				"sum(0 .. n - 1, λj:num. sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1)) * real_pow(x, j))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// One fact about the truncated predecessor that the interval
			// bounds keep producing: taking 1 then j off a number above j
			// is the same as taking j then 1 — an identity that holds
			// outright in ℕ, both sides being i − (j + 1); the hypothesis
			// is here for the decomposition it supplies.
			monusSwap := ctx.Lemma(Statement{
				Binders: "∀i j:num.",
				Hypotheses: []string{
					"j < i",
				},
				Conclusion: "i - 1 - j = i - j - 1",
			},
				func(a *Argument, i, j *Expr[Nat], above Fact) {
					one := a.Ctx().Nat(1)
					next := a.TermAs[Nat]("j + 1")
					gap, asSum := a.ObtainAs[Nat](
						"i lies some d beyond j + 1",
						"∃d:num. i = j + 1 + d",
						By(
							above,
							nat_order.LessEqExists.At(i, next),
							nat_order.SucLessEqIffLessThan.At(j, i),
							nat_arith.Add1.At(j)))
					// The regroupings of j + 1 + gap, from the AC kit over the
					// chapter's own associativity and commutativity.
					addAC := nat_arith.AddAC(a.Ctx())
					sum := a.TermAs[Nat]("j + 1 + d")
					oneFirst := a.Have(
						"taking 1 and then j off leaves d",
						"i - 1 - j = d",
						By(
							Normalized,
							asSum,
							addAC.Eq(sum, a.Term("j + d + 1")),
							nat_monus.AddSubCancel.At(a.TermAs[Nat]("j + d"), one),
							addAC.Eq(a.Term("j + d"), a.Term("d + j")),
							nat_monus.AddSubCancel.At(gap, j)))
					jFirst := a.Have(
						"and so does taking j and then 1",
						"i - j - 1 = d",
						By(
							Normalized,
							asSum,
							addAC.Eq(sum, a.Term("d + 1 + j")),
							nat_monus.AddSubCancel.At(a.TermAs[Nat]("d + 1"), j),
							nat_monus.AddSubCancel.At(gap, one)))
					a.Show(
						"so the two readings agree",
						By(Normalized, oneFirst, jFirst))
				})

			// The triangle: the entries F(i, j) with j below i, for i up to
			// n, summed by rows or by columns. Each reading is the
			// restricted double sum over the rows 1 .. n and the columns
			// 0 .. n − 1 with the restriction j < i, once the restricted
			// index sets are computed as the intervals they are.
			byColumns := ctx.Lemma(
				"∀n:num. ∀F:(num → num → real). "+
					"    sum(1 .. n, λi:num. sum(0 .. i - 1, λj:num. F(i, j))) = "+
					"    sum(0 .. n - 1, λj:num. sum(j + 1 .. n, λi:num. F(i, j)))",
				func(a *Argument, n *Expr[Nat], F *Arrow2[Nat, Nat, Real]) {
					zero, one := a.Ctx().Nat(0), a.Ctx().Nat(1)
					top := a.TermAs[Nat]("n - 1")
					rows := a.TermAs[Set[Nat]]("1 .. n")
					columns := a.TermAs[Set[Nat]]("0 .. n - 1")
					below := a.TermAs[Fun2[Nat, Nat, Bool]]("λi:num. λj:num. j < i")
					byRow := a.TermAs[Fun[Nat, Real]]("λi:num. sum(0 .. i - 1, λj:num. F(i, j))")
					byRowRestricted := a.TermAs[Fun[Nat, Real]](
						"λi:num. sum({j:num | j ∈ 0 .. n - 1 ∧ j < i}, λj:num. F(i, j))")
					byColumnRestricted := a.TermAs[Fun[Nat, Real]](
						"λj:num. sum({i:num | i ∈ 1 .. n ∧ j < i}, λi:num. F(i, j))")
					byColumn := a.TermAs[Fun[Nat, Real]]("λj:num. sum(j + 1 .. n, λi:num. F(i, j))")

					// Both readings restrict an interval by a cut at a point,
					// which is what the two restriction laws state; each
					// carries a guard putting the cut inside the interval.
					rowReads := a.Have(
						"row i runs over the columns below i, which are the interval up to i − 1",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"1 ≤ i",
								"i ≤ n",
							},
							Conclusion: "sum(0 .. i - 1, λj:num. F(i, j)) = " +
								"sum({j:num | j ∈ 0 .. n - 1 ∧ j < i}, λj:num. F(i, j))",
						},
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]()
							bounds := b.Assume()
							same := b.Have(
								"the columns below i are the interval up to i − 1",
								"{j:num | j ∈ 0 .. n - 1 ∧ j < i} = 0 .. i - 1",
								// The cut at i lies inside 0 .. n − 1: it is at least
								// 1, so n is too, and then n − 1 + 1 is n, which i
								// does not pass.
								By(
									Normalized,
									bounds,
									num_segment.RestrictBelow.At(zero, top, i),
									nat_order.LessEqTrans.At(one, i, n),
									nat_monus.SubAddCancel.At(n, one)))
							b.Show(
								"so the row is a sum over that set",
								By(same))
						}))
					columnReads := a.Have(
						"column j runs over the rows above j, which are the interval from j + 1",
						"∀j:num. sum({i:num | i ∈ 1 .. n ∧ j < i}, λi:num. F(i, j)) = sum(j + 1 .. n, λi:num. F(i, j))",
						Derive(func(b *Argument) {
							j := b.FixAs[Nat]()
							same := b.Have(
								"the rows above j are the interval from j + 1",
								"{i:num | i ∈ 1 .. n ∧ j < i} = j + 1 .. n",
								// The cut at j reaches the interval's bottom outright:
								// 1 ≤ j + 1 wherever j stands.
								By(num_segment.RestrictAbove.At(one, n, j), nat_order.LessEqAddLeft.At(j, one)))
							b.Show(
								"so the column is a sum over that set",
								By(same))
						}))
					a.Do(CalcEq(
						Leg(
							a.TermAs[Real]("sum(1 .. n, λi:num. sum({j:num | j ∈ 0 .. n - 1 ∧ j < i}, λj:num. F(i, j)))"),
							"each row is read as the columns below it",
							By(rowReads, real_sum.IntervalCongruence.At(one, n, byRow, byRowRestricted))),
						Leg(
							a.TermAs[Real]("sum(0 .. n - 1, λj:num. sum({i:num | i ∈ 1 .. n ∧ j < i}, λi:num. F(i, j)))"),
							"a restricted double sum over two finite sets is summed in either order",
							By(
								real_sum.SwapRestricted.At(F, below, rows, columns),
								num_segment.Finite.At(one, n),
								num_segment.Finite.At(zero, top))),
						FinalLeg(
							"and each column is read as the rows above it",
							By(columnReads, real_sum.CongruenceEverywhere.At(columns, byColumnRestricted, byColumn))),
					))
				})

			// The context is `arg`: the statement's first binder is the
			// coefficient list a, and it keeps that name.
			return ctx.Theorem(headline, func(
				arg *Argument,
				a *Arrow[Nat, Real],
				x, y *Expr[Real],
				n *Expr[Nat],
			) {
				zero, one := arg.Ctx().Nat(0), arg.Ctx().Nat(1)
				oneReal := arg.TermAs[Real]("&1")
				columnIndices := arg.TermAs[Set[Nat]]("0 .. n - 1")
				rows := arg.TermAs[Set[Nat]]("1 .. n")
				difference := arg.TermAs[Real]("x - y")
				xTerms := arg.TermAs[Fun[Nat, Real]]("λi:num. a(i) * real_pow(x, i)")
				yTerms := arg.TermAs[Fun[Nat, Real]]("λi:num. a(i) * real_pow(y, i)")
				termDifferences := arg.TermAs[Fun[Nat, Real]](
					"λi:num. a(i) * real_pow(x, i) - a(i) * real_pow(y, i)")
				powerDifferences := arg.TermAs[Fun[Nat, Real]]("λi:num. a(i) * (real_pow(x, i) - real_pow(y, i))")
				fromOne := arg.TermAs[Real]("sum(1 .. n, λi:num. a(i) * (real_pow(x, i) - real_pow(y, i)))")
				factored := arg.TermAs[Fun[Nat, Real]](
					"λi:num. (x - y) * sum(0 .. i - 1, λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j))")
				triangleRows := arg.TermAs[Fun[Nat, Real]](
					"λi:num. sum(0 .. i - 1, λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j))")
				entries := arg.TermAs[Fun2[Nat, Nat, Real]](
					"λi:num. λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)")
				scaledColumns := arg.TermAs[Fun[Nat, Real]](
					"λj:num. sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j))")
				columns := arg.TermAs[Fun[Nat, Real]](
					"λj:num. sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1)) * real_pow(x, j)")

				termwise := arg.Have(
					"from the first power up, a(i)·(xⁱ − yⁱ) is x − y times row i of the triangle",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"1 ≤ i",
							"i ≤ n",
						},
						Conclusion: "a(i) * (real_pow(x, i) - real_pow(y, i)) = " +
							"(x - y) * sum(0 .. i - 1, λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j))",
					},
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]()
						bounds := b.Assume()
						coefficient := b.TermAs[Real]("a(i)")
						pred := b.TermAs[Nat]("i - 1")
						interval := b.TermAs[Set[Nat]]("0 .. i - 1")
						powers := b.TermAs[Fun[Nat, Real]]("λk:num. real_pow(x, k) * real_pow(y, i - 1 - k)")
						geometric := b.TermAs[Real]("sum(0 .. i - 1, λk:num. real_pow(x, k) * real_pow(y, i - 1 - k))")
						scaledPowers := b.TermAs[Fun[Nat, Real]]("λk:num. a(i) * (real_pow(x, k) * real_pow(y, i - 1 - k))")
						row := b.TermAs[Fun[Nat, Real]]("λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)")

						regrouped := b.Have(
							"within the row each term regroups: the exponent of y reads i − j − 1, and xʲ moves to the right",
							Statement{
								Binders: "∀j:num.",
								Hypotheses: []string{
									"0 ≤ j",
									"j ≤ i - 1",
								},
								Conclusion: "a(i) * (real_pow(x, j) * real_pow(y, i - 1 - j)) = " +
									"a(i) * real_pow(y, i - j - 1) * real_pow(x, j)",
							},
							Derive(func(c *Argument) {
								j := c.FixAs[Nat]()
								inRow := c.Assume()
								xPower := c.TermAs[Real]("real_pow(x, j)")
								yPower := c.TermAs[Real]("real_pow(y, i - j - 1)")
								c.Show(
									"j lies below i, so the two readings of the exponent agree, and the product commutes",
									By(
										Normalized,
										bounds,
										inRow,
										nat_monus.LessThanIffAtMostPred.At(i, j),
										At(monusSwap, i, j),
										real_construction.MulSym.At(xPower, yPower),
										real_construction.MulAssoc.At(coefficient, yPower, xPower)))
							}))
						b.Do(CalcEq(
							Leg(
								b.TermAs[Real](
									"a(i) * ((x - y) * sum(0 .. i - 1, λk:num. real_pow(x, k) * real_pow(y, i - 1 - k)))"),
								"xⁱ − yⁱ factors through x − y, i being at least 1",
								By(bounds, real_pow.DifferenceOfPowers.At(x, y, i))),
							Leg(
								b.TermAs[Real](
									"(x - y) * sum(0 .. i - 1, λk:num. a(i) * (real_pow(x, k) * real_pow(y, i - 1 - k)))"),
								"a(i) passes x − y and moves into the sum",
								By(
									Normalized,
									real_construction.MulAssoc.At(coefficient, difference, geometric),
									real_construction.MulSym.At(coefficient, difference),
									real_construction.MulAssoc.At(difference, coefficient, geometric),
									real_sum.ScalarLeft.At(coefficient, powers, interval))),
							FinalLeg(
								"where each term regroups as an entry of the row",
								By(regrouped, real_sum.IntervalCongruence.At(zero, pred, scaledPowers, row))),
						))
					}))
				separated := arg.Have(
					"each column's common factor xʲ comes out of its sum",
					"∀j:num. "+
						"    sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)) = "+
						"    sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1)) * real_pow(x, j)",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("j")
						xPower := b.TermAs[Real]("real_pow(x, j)")
						column := b.TermAs[Set[Nat]]("j + 1 .. n")
						columnEntries := b.TermAs[Fun[Nat, Real]]("λi:num. a(i) * real_pow(y, i - j - 1)")
						b.Show(
							"a scalar on the right of every term is a scalar on the right of the sum",
							By(real_sum.ScalarRight.At(xPower, columnEntries, column)))
					}))
				arg.Do(CalcEq(
					Leg(
						arg.TermAs[Real]("sum(0 .. n, λi:num. a(i) * real_pow(x, i) - a(i) * real_pow(y, i))"),
						"two sums over one interval subtract pointwise",
						By(real_sum.IntervalSub.At(zero, n, xTerms, yTerms))),
					Leg(
						arg.TermAs[Real]("sum(0 .. n, λi:num. a(i) * (real_pow(x, i) - real_pow(y, i)))"),
						"and a(i) comes out of each difference",
						By(
							real_ring.SubLeftDistrib,
							real_sum.IntervalCongruence.At(zero, n, termDifferences, powerDifferences))),
					Leg(
						arg.TermAs[Real]("a(0) * (real_pow(x, 0) - real_pow(y, 0)) + "+
							"sum(0 + 1 .. n, λi:num. a(i) * (real_pow(x, i) - real_pow(y, i)))"),
						"the constant term comes off the front",
						By(nat_order.ZeroLessEq.At(n), real_sum.PeelLeft.At(zero, n, powerDifferences))),
					Leg(
						fromOne,
						"and it is nothing, x⁰ and y⁰ being both &1",
						By(
							Normalized,
							real_pow.PowExpZeroClause.At(x),
							real_pow.PowExpZeroClause.At(y),
							real_ring.SubRefl.At(oneReal),
							real_ring.MulRightZero.At(a.Apply(zero)),
							nat_arith.AddLeftZeroClause.At(one),
							real_construction.AddLeftId.At(fromOne))),
					Leg(
						arg.TermAs[Real]("sum(1 .. n, "+
							"    λi:num. (x - y) * sum(0 .. i - 1, λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)))"),
						"from the first power up, each term is x − y times a row of the triangle",
						By(termwise, real_sum.IntervalCongruence.At(one, n, powerDifferences, factored))),
					Leg(
						arg.TermAs[Real]("(x - y) * "+
							"sum(1 .. n, λi:num. sum(0 .. i - 1, λj:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)))"),
						"the common factor x − y comes out of the sum",
						By(real_sum.ScalarLeft.At(difference, triangleRows, rows))),
					Leg(
						arg.TermAs[Real]("(x - y) * "+
							"sum(0 .. n - 1, λj:num. sum(j + 1 .. n, λi:num. a(i) * real_pow(y, i - j - 1) * real_pow(x, j)))"),
						"and the triangle is summed by columns instead of by rows",
						By(At(byColumns, n, entries))),
					FinalLeg(
						"with xʲ taken out of each column",
						By(separated, real_sum.CongruenceEverywhere.At(columnIndices, scaledColumns, columns))),
				))
			})
		}),
})}

// ---------------------------------------------------------------------------
// The bound and its finiteness corollaries
// ---------------------------------------------------------------------------
//
// A coefficient sum of degree n with some coefficient not &0 has at
// most n roots: induction on the degree, with the factorization
// carrying the step. If the top coefficient is &0 the sum is the sum
// one degree lower, and the hypothesis applies once the coefficient
// that is not &0 is seen not to be the top one. Otherwise
// either there is no root at all, or there is one, r, and at every
// point p(x) = p(x) − p(r) = (x − r)·q(x), with q the cofactor of the
// factorization — a coefficient sum one degree lower whose top
// coefficient is the top coefficient of p. So q is not identically
// &0, the hypothesis bounds its roots, and every root of p is r or
// one of them.

// RootBound — a coefficient sum of degree n with some coefficient not
// &0 has finitely many roots, at most n of them.
var RootBound = rootBoundThm{family.Add(registry.ProofEntry{
	Name: "RootBound",
	Key:  "prop_5fb884a85182f276",
	Build: family.Sections(
		Statement{
			Binders: "∀n:num. ∀c:(num → real).",
			Hypotheses: []string{
				"¬∀i:num. i ∈ 0 .. n ⇒ c(i) = &0",
			},
			Conclusion: "finite({x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0}) ∧ " +
				"card({x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0}) ≤ n",
			Abbrev: Abbrev{
				{Name: "cofactorRootsText", Text: "{x:real | " +
					"    sum(0 .. n, " +
					"        λj:num. sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r₀, i - j - 1)) * real_pow(x, j)) = " +
					"    &0}"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// A root r of a coefficient sum p of degree n + 1 splits off the
			// factor x − r: p(x) is p(x) − p(r), and the difference factors,
			// the cofactor being the coefficient sum of degree n whose
			// coefficient at xʲ collects c(i)·r^(i−j−1) for i above j.
			rootFactor := ctx.Lemma(
				Statement{
					Binders: "∀n:num. ∀c:(num → real). ∀r x:real.",
					Hypotheses: []string{
						"sum(0 .. n + 1, λi:num. c(i) * real_pow(r, i)) = &0",
					},
					Conclusion: "sum(0 .. n + 1, λi:num. c(i) * real_pow(x, i)) = " +
						"(x - r) * " +
						"sum(0 .. n, λj:num. sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r, i - j - 1)) * real_pow(x, j))",
				},
				func(a *Argument, n *Expr[Nat], c *Arrow[Nat, Real], r, x *Expr[Real], atRoot Fact) {
					one := a.Ctx().Nat(1)
					degree := a.TermAs[Nat]("n + 1")
					atX := a.TermAs[Real]("sum(0 .. n + 1, λi:num. c(i) * real_pow(x, i))")
					a.Do(CalcEq(
						Leg(
							a.TermAs[Real]("sum(0 .. n + 1, λi:num. c(i) * real_pow(x, i)) - "+
								"sum(0 .. n + 1, λi:num. c(i) * real_pow(r, i))"),
							"p(x) is p(x) − p(r), p(r) being &0",
							By(atRoot, real_ring.SubRightZero.At(atX))),
						FinalLeg(
							"and the difference factors through x − r, the cofactor's degree n + 1 − 1 being n",
							By(DifferenceFactors.At(c, x, r, degree), nat_monus.AddSubCancel.At(n, one))),
					))
				})

			// The cofactor's top coefficient is c(n + 1): the sum over the
			// one-point interval n + 1 .. n + 1 is its term there, whose
			// exponent n + 1 − n − 1 is 0.
			cofactorTop := ctx.Lemma(
				"∀n:num. ∀c:(num → real). ∀r:real. "+
					"    sum(n + 1 .. n + 1, λi:num. c(i) * real_pow(r, i - n - 1)) = c(n + 1)",
				func(a *Argument, n *Expr[Nat], c *Arrow[Nat, Real], r *Expr[Real]) {
					one := a.Ctx().Nat(1)
					degree := a.TermAs[Nat]("n + 1")
					entries := a.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(r, i - n - 1)")
					a.Show(
						"the one-point sum is c(n + 1)·r⁰, and r⁰ is &1",
						By(
							Normalized,
							real_sum.IntervalPoint.At(degree, entries),
							nat_arith.AddSym.At(n, one),
							nat_monus.AddSubCancel.At(one, n),
							nat_monus.SubRefl.At(one),
							real_pow.PowExpZeroClause.At(r),
							real_ring.MulRightId.At(c.Apply(degree))))
				})

			// Every root of p is r or a root of the cofactor: at a root x of
			// p, (x − r)·q(x) is &0, so x − r is &0 or q(x) is.
			rootsInsert := ctx.Lemma(
				Statement{
					Binders: "∀n:num. ∀c:(num → real). ∀r:real.",
					Hypotheses: []string{
						"sum(0 .. n + 1, λi:num. c(i) * real_pow(r, i)) = &0",
					},
					Conclusion: "{x:real | sum(0 .. n + 1, λi:num. c(i) * real_pow(x, i)) = &0} ⊆ " +
						"insert(r, " +
						"    {x:real | " +
						"        sum(0 .. n, " +
						"            λj:num. " +
						"                sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r, i - j - 1)) * real_pow(x, j)) = " +
						"        &0})",
				},
				func(a *Argument, n *Expr[Nat], c *Arrow[Nat, Real], r *Expr[Real], atRoot Fact) {
					dichotomy := a.Have(
						"a root x of p has (x − r)·q(x) = &0, so x is r or a root of q",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"sum(0 .. n + 1, λi:num. c(i) * real_pow(x, i)) = &0",
							},
							Conclusion: "x = r ∨ " +
								"sum(0 .. n, " +
								"    λj:num. sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r, i - j - 1)) * real_pow(x, j)) = " +
								"&0",
						},
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							root := b.Assume()
							difference := b.TermAs[Real]("x - r")
							cofactorAtX := b.TermAs[Real](
								"sum(0 .. n, λj:num. sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r, i - j - 1)) * real_pow(x, j))")
							b.Show(
								"a product is &0 only through a factor, and x − r = &0 is x = r",
								By(
									root,
									atRoot,
									At(rootFactor, n, c, r, x),
									real_ring.MulEqZero.At(difference, cofactorAtX),
									real_ring.SubEqZero.At(x, r)))
						}))
					a.Show(
						"which is the inclusion, read point by point",
						BySets(dichotomy))
				})

			return ctx.Theorem(headline, func(a *Argument) {
				// The closure binds nothing: n is the induction variable, and
				// the list c is fixed inside each case, so that the hypothesis
				// speaks of every list.
				nBinder := a.Binder("n")
				n := ext.As[Nat](nBinder)
				zero := a.Ctx().Nat(0)

				a.Induct(nBinder)
				a.Base(
					"n = 0: the one coefficient c(0) is not &0, so the sum, which is c(0), has no roots",
					func(b *Argument) {
						b.FixAs[Fun[Nat, Real]]("c")
						some := b.Assume()

						index, nonzero := b.ObtainAs[Nat](
							"some coefficient is not &0",
							"∃i:num. i ∈ 0 .. 0 ∧ c(i) ≠ &0",
							By(Normalized, some))
						constant := b.Have(
							"and the only index up to 0 is 0, so it is c(0)",
							"c(0) ≠ &0",
							By(
								Normalized,
								nonzero,
								num_segment.MembershipFromZero.At(index, zero),
								nat_order.LessEqZeroClause.At(index)))
						noRoots := b.Have(
							"a sum over the one-point interval is its term there, c(0)·x⁰ = c(0), never &0",
							"∀x:real. ¬(sum(0 .. 0, λi:num. c(i) * real_pow(x, i)) = &0)",
							Derive(func(gap *Argument) {
								x := gap.FixAs[Real]()
								terms := gap.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
								gap.Show(
									"x⁰ is &1, and c(0)·&1 is c(0)",
									By(
										Normalized,
										constant,
										real_sum.IntervalPoint.At(zero, terms),
										real_pow.PowExpZeroClause.At(x),
										real_ring.MulRightId.At(gap.TermAs[Real]("c(0)"))))
							}))
						empty := b.Have(
							"so the root set is empty",
							"{x:real | sum(0 .. 0, λi:num. c(i) * real_pow(x, i)) = &0} = ∅",
							BySets(noRoots))
						// ↦ finite(∅) ∧ card(∅) ≤ 0
						b.Do(empty.Rw())
						b.Show(
							"and the empty set is finite, with card 0",
							By(
								Normalized,
								finite_set.FiniteRules.Inst[Real](),
								cardinality.CardClauses.Inst[Real](),
								nat_order.ZeroLessEq.At(zero)))
					})
				a.Step(
					"n → suc n: by cases on the top coefficient c(suc n)",
					func(b *Argument, ih Fact) {
						c := b.FixAs[Fun[Nat, Real]]()
						some := b.Assume()
						top := b.TermAs[Nat]("suc(n)")
						roots := b.TermAs[Set[Real]]("{x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0}")

						b.Cases(b.Term("c(suc(n)) = &0"))
						b.When(
							"c(suc n) = &0: the top term vanishes, so the roots and the hypothesis are those of degree n",
							func(z *Argument, vanishes Fact) {
								same := z.Have(
									"at every point the sum over 0 .. suc n is the sum over 0 .. n",
									"∀x:real. "+
										"    sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = sum(0 .. n, λi:num. c(i) * real_pow(x, i))",
									Derive(func(gap *Argument) {
										gap.FixAs[Real]("x")
										terms := gap.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
										topPower := gap.TermAs[Real]("real_pow(x, suc(n))")
										lowerSum := gap.TermAs[Real]("sum(0 .. n, λi:num. c(i) * real_pow(x, i))")
										gap.Show(
											"the top term c(suc n)·x^(suc n) is &0·x^(suc n), which is &0",
											By(
												vanishes,
												real_sum.IntervalClauses.At(zero, n, terms),
												nat_order.ZeroLessEq.At(top),
												real_ring.MulLeftZero.At(topPower),
												real_ring.AddRightId.At(lowerSum)))
									}))
								sameRoots := z.Have(
									"so the two root sets are the same",
									"{x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0} = "+
										"{x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0}",
									BySets(same))
								index, witness := z.ObtainAs[Nat](
									"some coefficient up to suc n is not &0",
									"∃i:num. i ∈ 0 .. suc(n) ∧ c(i) ≠ &0",
									By(Normalized, some))
								notTop := z.Have(
									"the coefficient that is not &0 is not the top one, so its index is at most n",
									"i₀ ∈ 0 .. n ∧ c(i₀) ≠ &0",
									By(
										Normalized,
										witness,
										vanishes,
										num_segment.MembershipFromZero.At(index, top),
										num_segment.MembershipFromZero.At(index, n),
										nat_order.LessEqSucClause.At(index, n)))
								z.Show(
									"so the hypothesis bounds the roots by n, which is at most suc n",
									By(
										Normalized,
										sameRoots,
										notTop,
										ih.At(c),
										nat_order.LessEqSucClause.At(
											z.TermAs[Nat]("card({x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0})"), n)))
							})
						b.Otherwise(
							"c(suc n) ≠ &0: either p has no root, or a root r splits "+
								"off, and the cofactor's roots are bounded by the hypothesis",
							func(z *Argument, topNonzero Fact) {
								hasRoot := z.Assuming(
									z.Term("∃r:real. sum(0 .. suc(n), λi:num. c(i) * real_pow(r, i)) = &0"),
									"no root: the root set is empty, finite with card 0",
									Given(func(y *Argument, noRoot Fact) {
										empty := y.Have(
											"the root set is empty",
											"{x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0} = ∅",
											BySets(noRoot))
										// ↦ finite(∅) ∧ card(∅) ≤ suc n
										y.Do(empty.Rw())
										y.Show(
											"and the empty set is finite, with card 0",
											By(
												Normalized,
												finite_set.FiniteRules.Inst[Real](),
												cardinality.CardClauses.Inst[Real](),
												nat_order.ZeroLessEq.At(top)))
									}))
								root, atRoot := z.UnpackAs[Real](hasRoot)
								cofactor := z.TermAs[Fun[Nat, Real]](
									"λj:num. sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r₀, i - j - 1))")
								cofactorRoots := z.TermAs[Set[Real]]("«cofactorRootsText»")
								extended := z.TermAs[Set[Real]]("insert(r₀, «cofactorRootsText»)")
								extendedCount := z.TermAs[Nat]("card(insert(r₀, «cofactorRootsText»))")
								count := z.TermAs[Nat]("card({x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0})")

								contained := z.Have(
									"every root of p is r₀ or a root of the cofactor q",
									"{x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0} ⊆ insert(r₀, «cofactorRootsText»)",
									By(Normalized, atRoot, At(rootsInsert, n, c, root), nat_arith.Add1.At(n)))
								notAllZero := z.Have(
									"q's top coefficient is c(suc n), which is not &0, so some coefficient of q is not &0",
									"∃j:num. j ∈ 0 .. n ∧ sum(j + 1 .. n + 1, λi:num. c(i) * real_pow(r₀, i - j - 1)) ≠ &0",
									By(
										Normalized,
										topNonzero,
										At(cofactorTop, n, c, root),
										nat_arith.Add1.At(n),
										num_segment.MembershipFromZero.At(n, n),
										nat_order.LessEqRefl.At(n)))
								bounded := z.Have(
									"so q's roots are finite and at most n, by the hypothesis",
									"finite(«cofactorRootsText») ∧ card(«cofactorRootsText») ≤ n",
									By(notAllZero, ih.At(cofactor)))
								withRoot := z.Have(
									"adding r₀ back keeps them finite and counts at most one more: at most suc n",
									"finite(insert(r₀, «cofactorRootsText»)) ∧ card(insert(r₀, «cofactorRootsText»)) ≤ suc(n)",
									By(bounded, cardinality.InsertCountsAtMostOneMore.At(cofactorRoots, root, n)))
								finite := z.Have(
									"and the roots of p, lying among them, are finite",
									"finite({x:real | sum(0 .. suc(n), λi:num. c(i) * real_pow(x, i)) = &0})",
									By(contained, withRoot, finite_set.FiniteSubset.At(roots, extended)))
								z.Show(
									"and a subset has no more points than the set",
									By(
										finite,
										contained,
										withRoot,
										cardinality.CardSubset.At(roots, extended),
										nat_order.LessEqTrans.At(count, extendedCount, top)))
							})
					})
			})
		}),
})}

// vanishesEverywhere reads a coefficient list that is &0 up to its
// degree as the zero function: between the bounds every term is &0·xⁱ.
// Both corollaries need it, each about its own list, so the claim is
// the caller's and only the argument is shared.
func vanishesEverywhere(a *Argument, allZero Fact, degree Typed[Nat], claim string) Fact {
	return a.Have(
		"with every coefficient up to the degree at &0, the sum is &0 at every point",
		claim,
		Derive(func(gap *Argument) {
			gap.FixAs[Real]("x")
			terms := gap.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
			gap.Show(
				"between the bounds every term is &0·xⁱ, which is &0",
				By(allZero, real_sum.IntervalEqZero.At(gap.Ctx().Nat(0), degree, terms), real_ring.MulLeftZero))
		}))
}

// realsNotFinite is ℝ's own size, in the form the two corollaries
// below use it: each ends by exhibiting a set that is all of ℝ and
// finite at once. The cited fact says infinite, which is the one word
// for ¬finite, so it is unfolded where it is cited and the closes that
// follow are ordinary refutations.
func realsNotFinite(a *Argument) Fact {
	return a.Have(
		"ℝ is not a finite set",
		"¬finite(𝕌⟨A:real⟩)",
		Cite(real_archimedean.Infinite),
		Unfold(finite_set.InfiniteDef))
}

// FiniteRootsIffNonzero — a coefficient sum has finitely many roots
// exactly when it is not the zero list up to n. One direction is the
// bound: a coefficient that is not &0 puts it in force, and finiteness
// is its first half. The other is the line's own size: with every
// coefficient &0 every term of the sum is &0·xⁱ, so the sum vanishes
// at every point, the root set is the whole of ℝ, and ℝ is not finite.
var FiniteRootsIffNonzero = finiteRootsIffNonzeroThm{family.Add(registry.ProofEntry{
	Name: "FiniteRootsIffNonzero",
	Key:  "prop_a5b1691ccce74815",
	Build: family.Theorem(
		"∀n:num. ∀c:(num → real). "+
			"    finite({x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0}) ⇔ "+
			"    ∃i:num. i ∈ 0 .. n ∧ c(i) ≠ &0",
		func(a *Argument, n *Expr[Nat], c *Arrow[Nat, Real]) {
			a.Iff()
			a.Forward(
				"were every coefficient &0 the sum would vanish everywhere, and ℝ is not finite",
				func(b *Argument, finite Fact) {
					allZero := b.SupposeNot()
					vanishes := vanishesEverywhere(b, allZero, n,
						"∀x:real. sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0")
					whole := b.Have(
						"so every real is a root",
						"{x:real | sum(0 .. n, λi:num. c(i) * real_pow(x, i)) = &0} = 𝕌⟨A:real⟩",
						BySets(vanishes))
					notFinite := realsNotFinite(b)
					b.Show(
						"and a finite root set cannot be all of ℝ",
						By(finite, whole, notFinite))
				})
			a.Backward(
				"a coefficient that is not &0 puts the degree bound in force, and finiteness is its first half",
				func(b *Argument, some Fact) {
					i, nonzero := b.Unpack(some)
					// The bound at this degree and list, with i for the index
					// its antecedent speaks of. The antecedent binds that
					// index, so the statement's reading order puts it last,
					// after the degree and the list — a slot the typed
					// wrapper, which carries the headline's binders only,
					// has no room for, so the cite keeps the untyped
					// spelling.
					b.Show(
						"the bound counts the roots, so there are finitely many",
						By(nonzero, At(RootBound, n, c, i)))
				})
		}),
})}

// FiniteLevelSets — a polynomial takes a given value at only finitely
// many points exactly when it does not take it everywhere. The level
// set of p at a is the root set of p − a, which is polynomial again
// and so a coefficient sum, and the two directions are the two ways
// that sum can behave. If p is not constantly a its coefficients are
// not all &0 — were they, the sum would vanish at every point and p
// would be a everywhere — so the root count above bounds the level
// set. If p is constantly a the level set is all of ℝ, which is not
// finite.
var FiniteLevelSets = finiteLevelSetsThm{family.Add(registry.ProofEntry{
	Name: "FiniteLevelSets",
	Key:  "prop_8404a0e9b36395ad",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:(real → real). ∀a:real.",
			Hypotheses: []string{
				"polynomial_function(p)",
			},
			Conclusion: "finite({x:real | p(x) = a}) ⇔ ¬∀x:real. p(x) = a",
		},
		// The context is `arg`: the statement's second binder is the
		// value a, and it keeps that name.
		func(arg *Argument, p *Arrow[Real, Real], a *Expr[Real], polynomial Fact) {
			arg.Iff()
			arg.Forward(
				"were p constantly a the level set would be all of ℝ, which is not finite",
				func(b *Argument, finite Fact) {
					everywhere := b.SupposeNot()
					whole := b.Have(
						"every real would then lie in the level set",
						"{x:real | p(x) = a} = 𝕌⟨A:real⟩",
						BySets(everywhere))
					notFinite := realsNotFinite(b)
					b.Show(
						"but a finite set cannot be all of ℝ",
						By(finite, whole, notFinite))
				})
			arg.Backward(
				"p is not constantly a, so p − a is a coefficient sum whose list is not all &0",
				func(b *Argument, notConstant Fact) {
					constant := b.TermAs[Fun[Real, Real]]("λx:real. a")

					difference := b.Have(
						"p minus the constant a is polynomial",
						"polynomial_function(λx:real. p(x) - a)",
						By(polynomial, Const.At(a), Sub.At(p, constant)))
					// Opened in that hypothesis alone: the difference is some
					// coefficient sum.
					opened := b.Unfolded(difference, PolynomialFunctionDef)
					degree, list, differenceSum := b.Unpack2As[Nat, Fun[Nat, Real]](opened)

					pointwise := b.Have(
						"p takes the value a exactly where that sum has a root",
						"∀y:real. p(y) = a ⇔ sum(0 .. m, λi:num. c(i) * real_pow(y, i)) = &0",
						Derive(func(gap *Argument) {
							y := gap.FixAs[Real]()
							gap.Show(
								"at y the sum is p(y) − a, and a difference is &0 exactly when its sides agree",
								By(differenceSum.At(y), real_ring.SubEqZero.At(p.Apply(y), a)))
						}))
					sameSet := b.Have(
						"so the level set of p at a is that sum's root set",
						"{x:real | p(x) = a} = {x:real | sum(0 .. m, λi:num. c(i) * real_pow(x, i)) = &0}",
						BySets(pointwise))

					// The witness is discarded but not idle: opening the
					// existential grounds the instance the close below runs
					// on, and the bare ∃ leaves it to a search that does not
					// finish.
					_, nonzero := b.Obtain(
						"some coefficient of the difference is not &0",
						"∃i:num. i ∈ 0 .. m ∧ c(i) ≠ &0",
						Derive(func(gap *Argument) {
							allZero := gap.SupposeNot()
							vanishes := vanishesEverywhere(gap, allZero, degree,
								"∀x:real. sum(0 .. m, λi:num. c(i) * real_pow(x, i)) = &0")
							gap.Show(
								"and then p would take the value a everywhere",
								By(notConstant, pointwise, vanishes))
						}))
					b.Show(
						"so that root set is finite, and it is the level set",
						By(Normalized, nonzero, sameSet, FiniteRootsIffNonzero.At(degree, list)))
				})
		}),
})}
