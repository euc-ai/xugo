// products.go — products modulo n: complements to p multiply as the
// numbers do, so (p − 1)! splits into two factorials.

package nat_congruence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductOfComplements — complements to p multiply as the numbers do: when
// a + c = p and b + d = p, then a·b ≡ c·d (mod p), each complement being
// ≡ −itself. Over ℕ the signs never appear: a·b + p·p and c·d + p·(a + b)
// are one number, and each differs from its first summand by a multiple
// of p.
var ProductOfComplements = productOfComplementsThm{family.Add(registry.ProofEntry{
	Name: "ProductOfComplements",
	Key:  "prop_9cb5b4e67fcacd18",
	Build: family.Theorem(Statement{
		Binders: "∀p a b c d:num.",
		Hypotheses: []string{
			"a + c = p",
			"b + d = p",
		},
		Conclusion: "a * b ≡ c * d (mod p)",
	}, func(arg *Argument, p, a, b, c, d *Expr[Nat], first, second Fact) {
		balance := arg.Have(
			"b·(a + c) = b·p, less p·(a + c) = p·p and c·(b + d) = c·p, is this equation",
			"a * b + p * p = c * d + p * (a + b)",
			ByArith(Scaled(p, first), Scaled(b, first), Scaled(c, second)))
		arg.Show(
			"a multiple of p added keeps the class mod p, so a·b and c·d are congruent",
			By(
				balance,
				OffsetIffDivides.At(arg.TermAs[Nat]("a * b"), arg.TermAs[Nat]("p * p"), p),
				OffsetIffDivides.At(arg.TermAs[Nat]("c * d"), arg.TermAs[Nat]("p * (a + b)"), p),
				nat_divides.DividesOwnMultiple.At(p, p),
				nat_divides.DividesOwnMultiple.At(p, arg.TermAs[Nat]("a + b")),
				CongDef))
	}),
})}

// FactorialSplitMod — when m + 2k + 1 = p, (p − 1)! ≡ m! · (2k)! (mod p):
// the 2k factors of (p − 1)! above m are the complements of 1, …, 2k, and
// taken two at a time they multiply as those do (ProductOfComplements). By
// induction on k, for every m at once: with no factors above m, m is p − 1;
// and the two lowest factors above m, m + 1 and m + 2, are the complements
// of 2k + 2 and 2k + 1, so the claim at m + 2 gives it at m.
var FactorialSplitMod = factorialSplitModThm{family.Add(registry.ProofEntry{
	Name: "FactorialSplitMod",
	Key:  "prop_bf22e31b277ba243",
	Build: family.Theorem(Statement{
		Binders: "∀p k m:num.",
		Hypotheses: []string{
			"m + 2 * k + 1 = p",
		},
		Conclusion: "factorial(p - 1) ≡ factorial(m) * factorial(2 * k) (mod p)",
	}, func(a *Argument, p *Expr[Nat]) {
		a.Induct("k")
		a.Base(
			"with no factors above m, m is p − 1 and (2·0)! is 1",
			func(b *Argument) {
				b.FixAs[Nat]("m")
				sum := b.Assume()
				top := b.Have(
					"m is p − 1",
					"p - 1 = m",
					ByArith(sum))
				b.Show(
					"both sides are m!",
					Simp(Fwd(top), Fwd(nat_arith.MulZero), Fwd(nat_arith.Factorial), Fwd(nat_arith.MulOne)),
					By(CongDef))
			})
		a.Step(
			"the two lowest factors above m, m + 1 and m + 2, are the complements of 2k + 2 and 2k + 1",
			func(b *Argument, ih Fact) {
				b.FixAs[Nat]("m")
				sum := b.Assume()
				shifted := b.TermAs[Nat]("suc(suc(m))")
				rest := b.TermAs[Nat]("factorial(m) * factorial(2 * k)")
				sums := b.Have(
					"m + 2 lies 2k + 1 below p, and m + 1 lies 2k + 2 below it",
					"suc(suc(m)) + 2 * k + 1 = p ∧ 2 * k + 1 + suc(suc(m)) = p ∧ 2 * k + 2 + suc(m) = p",
					ByArith(sum))
				upper := b.Have(
					"(m + 2)!·(2k)! is (m + 2)(m + 1) · m!(2k)!",
					"factorial(suc(suc(m))) * factorial(2 * k) = "+
						"suc(suc(m)) * suc(m) * (factorial(m) * factorial(2 * k))",
					Simp(Fwd(nat_arith.Factorial)),
					ByArith())
				even := b.Have(
					"2(k + 1) is 2k + 2",
					"2 * suc(k) = suc(suc(2 * k))",
					ByArith())
				lower := b.Have(
					"m!·(2k + 2)! is (2k + 1)(2k + 2) · m!(2k)!",
					"factorial(m) * factorial(2 * suc(k)) = "+
						"(2 * k + 1) * (2 * k + 2) * (factorial(m) * factorial(2 * k))",
					Simp(Fwd(even), Fwd(nat_arith.Factorial)),
					ByArith())
				b.Show(
					"(p − 1)! ≡ (m + 2)! (2k)! by the claim at m + 2, and (m + 2)(m + 1) ≡ (2k + 1)(2k + 2)",
					By(
						ih.At(shifted),
						sums,
						upper,
						lower,
						ProductOfComplements.At(
							p,
							b.TermAs[Nat]("2 * k + 1"),
							b.TermAs[Nat]("2 * k + 2"),
							shifted,
							b.TermAs[Nat]("suc(m)")),
						MulCongruent.At(
							b.TermAs[Nat]("(2 * k + 1) * (2 * k + 2)"),
							b.TermAs[Nat]("suc(suc(m)) * suc(m)"),
							rest,
							rest,
							p),
						CongDef))
			})
	}),
})}
