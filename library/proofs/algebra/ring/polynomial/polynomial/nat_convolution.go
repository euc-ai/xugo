// nat_convolution.go — the convolution of sequences of naturals, the
// product of power series with natural coefficients: its n-th coefficient is
// the finite sum of p(i)·q(n − i) over i ≤ n under ℕ's addition, and it is
// left-commutative. ℕ is not a ring, so the chapter's laws of the product
// over a ring do not apply; left-commutativity is their coefficient count
// done in ℕ's finite sums: both sides at n sum the products
// p(i)·q(j)·r(n − i − j) over the triangle i + j ≤ n, in its two orders.

package polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// NatPolynomialMulSum — the n-th coefficient of the convolution of two
// sequences of naturals is the finite sum of p(i)·q(n − i) over i ≤ n. The
// convolution defines its coefficient as a sum of the module chapter, and
// over ℕ's addition, a commutative monoid, that sum is Σ.
var NatPolynomialMulSum = natPolynomialMulSumThm{family.Add(registry.ProofEntry{
	Name: "NatPolynomialMulSum",
	Key:  "prop_99137fab94925bbe",
	Build: family.Theorem(Statement{
		Binders:    "∀p q:(num → num). ∀n:num.",
		Conclusion: "«natConv»(p, q, n) = nat_sum({i:num | i ≤ n}, λi:num. p(i) * q(n - i))",
	}, func(a *Argument, p, q *Arrow[Nat, Nat], n *Expr[Nat]) {
		plus := a.TermAs[Op[Nat]]("λi:num. λj:num. i + j")
		zero := a.TermAs[Nat]("0")
		times := a.TermAs[Op[Nat]]("λi:num. λj:num. i * j")
		a.Show(
			"the convolution's coefficient is a module sum over i ≤ "+
				"n, which over ℕ's addition, a commutative monoid, is Σ",
			By(
				num_segment.FiniteBelow.At(n),
				PolynomialMulDef.At(plus, zero, times, p, q, n),
				module.ModuleSumIteratedOp.Read(nat_sum.CommMonoidNatAdd).At(
					a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
					a.TermAs[Fun[Nat, Nat]]("λi:num. p(i) * q(n - i)")),
				nat_sum.NatSumDef))
	}),
})}

// NatPolynomialMulLeftComm — the convolution of sequences of naturals is
// left-commutative: its first two factors interchange. At n, u ⋆ (v ⋆ r)
// sums u(i)·(v(j)·r(n − i − j)) over i ≤ n and j ≤ n − i, the triangle
// i + j ≤ n; padded with zero, each row runs over j ≤ n, and the sum is
// over the square i, j ≤ n. Read at (p, q) and at (q, p), the two sides
// are one square summed in its two orders (nat_sum.Swap), each term met by
// its partner with i and j exchanged.
var NatPolynomialMulLeftComm = natPolynomialMulLeftCommThm{family.Add(registry.ProofEntry{
	Name: "NatPolynomialMulLeftComm",
	Key:  "prop_42cbd481d92b7fba",
	Build: family.Theorem(Statement{
		Binders:    "∀p q r:(num → num).",
		Conclusion: "«natConv»(p, «natConv»(q, r)) = «natConv»(q, «natConv»(p, r))",
	}, func(a *Argument, p, q, r *Arrow[Nat, Nat]) {
		a.Do(Funext())
		n := a.FixAs[Nat]("n")
		rows := a.Have(
			"for i ≤ n, a row of the triangle scaled by c is "+
				"the row of the square, padded with zero past n − i",
			Statement{
				Binders: "∀i c:num. ∀f:(num → num).",
				Hypotheses: []string{
					"i ≤ n",
				},
				Conclusion: "c * sum({j:num | j ≤ n - i}, f) = " +
					"sum({j:num | j ≤ n}, λj:num. COND(i + j ≤ n, c * f(j), 0))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.FixAs[Nat]()
				b.FixAs[Fun[Nat, Nat]]()
				below := b.Assume()
				bounds := b.Have(
					"as i ≤ n, j ≤ n − i says that j ≤ n and i + j ≤ n",
					"∀j:num. j ≤ n - i ⇔ j ≤ n ∧ i + j ≤ n",
					ByArith(below))
				b.Show(
					"c passes into the finite sum, whose range j ≤ n − i is j ≤ n cut down to i + j ≤ n",
					Simp(Fwd(num_segment.FiniteBelow), Fwd(nat_sum.ScalarLeft)),
					Simp(Fwd(bounds)),
					By(nat_sum.Restrict))
			}))
		square := a.Have(
			"u ⋆ (v ⋆ r) at n sums its triangle of products, padded with zero to the square i, j ≤ n",
			"∀u v:(num → num). "+
				"    «natConv»(u, «natConv»(v, r), n) = "+
				"    sum({i:num | i ≤ n}, "+
				"        λi:num. sum({j:num | j ≤ n}, λj:num. COND(i + j ≤ n, u(i) * (v(j) * r(n - i - j)), 0)))",
			Simp(Fwd(NatPolynomialMulSum)),
			By(rows, nat_sum.Congruence))
		termwise := a.Have(
			"a term of the left side's square is the right side's term with i and j exchanged",
			"∀i j:num. "+
				"    COND(i + j ≤ n, p(i) * (q(j) * r(n - i - j)), 0) = "+
				"    COND(j + i ≤ n, q(j) * (p(i) * r(n - j - i)), 0)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.FixAs[Nat]()
				reorder := b.Have(
					"taking j and then i from n is taking i and then j",
					"n - j - i = n - i - j",
					ByArith())
				b.Show(
					"so the two terms differ only in the order of the sums and of the products",
					reorder.Rw(),
					ByArith())
			}))
		a.Show(
			"read at (p, q) and at (q, p), the two sides sum one square in its two orders",
			square.At(p, q).Rw(),
			square.At(q, p).Rw(),
			Simp(Fwd(termwise)),
			By(num_segment.FiniteBelow.At(n), nat_sum.Swap))
	}),
})}
