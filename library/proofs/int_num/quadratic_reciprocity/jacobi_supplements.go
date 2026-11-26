// jacobi_supplements.go — the supplementary laws for the Jacobi symbol:
// (−1/n) = (−1)^((n−1)/2) and (2/n) = (−1)^((n²−1)/8) for odd n. Each is
// the Legendre symbol's law carried to every odd n through
// multiplicativity in the lower argument, and what lets it travel is that
// its sign is itself multiplicative on odd numbers, which comes first. For
// the second, the Legendre symbol's law is read as a sign first: (2/p) = 1
// exactly when p ≡ ±1 (mod 8), which is exactly when (p² − 1)/8 is even.

package quadratic_reciprocity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/registry"
)

// HalfOddSignMul — on odd numbers the sign (−1)^((n−1)/2) is
// multiplicative. Writing m = 2i + 1 and n = 2j + 1, (m − 1)/2 = i,
// (n − 1)/2 = j and (m·n − 1)/2 = 2ij + i + j; the even part 2ij of the
// exponent contributes ((−1)²)^(ij) = 1, and the rest splits over i + j.
var HalfOddSignMul = halfOddSignMulThm{family.Add(registry.ProofEntry{
	Name: "HalfOddSignMul",
	Key:  "prop_87e7bc2d9b6df10c",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"nat_odd(m)",
			"nat_odd(n)",
		},
		Conclusion: "(-int_of_num(1)) ^ «h»(m * n) = (-int_of_num(1)) ^ «h»(m) * (-int_of_num(1)) ^ «h»(n)",
	}, func(a *Argument, m, n *Expr[Nat], mOdd, nOdd Fact) {
		two, zero := a.Ctx().Nat(2), a.Ctx().Nat(0)
		minusOne := a.TermAs[Int]("-1")
		i, mIs := a.ObtainAs[Nat](
			"m is odd: m = 2i + 1",
			"∃i:num. m = suc(2 * i)",
			By(mOdd, nat_parity.OddIffSucDouble.At(m)))
		j, nIs := a.ObtainAs[Nat](
			"and n = 2j + 1",
			"∃j:num. n = suc(2 * j)",
			By(nOdd, nat_parity.OddIffSucDouble.At(n)))
		product := a.TermAs[Nat]("i * j")
		halves := a.Have(
			"(m − 1)/2 = i, (n − 1)/2 = j and (m·n − 1)/2 = 2ij "+
				"+ i + j, each the quotient of an exact division by 2",
			"«h»(m) = i ∧ «h»(n) = j ∧ «h»(m * n) = 2 * (i * j) + (i + j)",
			ByArith(
				mIs,
				nIs,
				nat_div_mod.DivUniq.At(a.TermAs[Nat]("m - 1"), two, i, zero),
				nat_div_mod.DivUniq.At(a.TermAs[Nat]("n - 1"), two, j, zero),
				nat_div_mod.DivUniq.At(
					a.TermAs[Nat]("m * n - 1"), two, a.TermAs[Nat]("2 * (i * j) + (i + j)"), zero)))
		square := a.Have(
			"(−1)² = 1",
			"(-1) ^ 2 = int_of_num(1)",
			ByArith())
		even := a.Have(
			"so the even part of the exponent contributes ((−1)²)^(ij) = 1",
			"(-int_of_num(1)) ^ (2 * (i * j)) = int_of_num(1)",
			By(square, int_pow.PowPow.At(minusOne, two, product), int_pow.OnePow.At(product)))
		a.Show(
			"and the rest of the exponent, i + j, splits into the two signs",
			ByArith(
				halves,
				even,
				int_pow.PowAdd.At(minusOne, a.TermAs[Nat]("2 * (i * j)"), a.TermAs[Nat]("i + j")),
				int_pow.PowAdd.At(minusOne, i, j)))
	}),
})}

// JacobiMinusOne — the first supplement for Jacobi symbols: for odd n,
// (−1/n) = (−1)^((n−1)/2). By strong induction on n: at n = 1 both sides
// are 1. Past 1, a prime p divides n, n = p·m with p and m odd and m < n,
// and (−1/n) = (−1/p)·(−1/m); the first factor is the Legendre symbol at
// the odd prime p, (−1)^((p−1)/2), the second is (−1)^((m−1)/2) by the
// induction hypothesis, and the two signs multiply to (−1)^((p·m−1)/2).
var JacobiMinusOne = jacobiMinusOneThm{family.Add(registry.ProofEntry{
	Name: "JacobiMinusOne",
	Key:  "prop_35fc2f4ac7f1ea19",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
		},
		Conclusion: "jacobi_symbol(-1, n) = (-1) ^ «h»(n)",
	}, func(a *Argument) {
		a.Show(
			"strong induction on n, splitting off one prime factor",
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted the law at every odd number below n, it holds at an odd n",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						below := b.Assume()
						odd := b.Assume()
						minusOne := b.TermAs[Int]("-1")
						b.Cases(b.Term("n = 1"))
						b.When(
							"n = 1: (−1/1) = 1 = (−1)⁰",
							func(c *Argument, isOne Fact) {
								c.Show(
									"(1 − 1)/2 = 0",
									ByArith(
										isOne,
										JacobiAtOne.At(minusOne),
										nat_div_mod.DivUniq.At(c.TermAs[Nat]("n - 1"), c.Ctx().Nat(2), c.Ctx().Nat(0), c.Ctx().Nat(0))))
							})
						b.Otherwise(
							"n > 1: split off an odd prime factor p, n = p·m",
							func(c *Argument, notOne Fact) {
								p, m, split := c.Unpack2As[Nat, Nat](
									GroupPremises(odd, notOne, nat_prime.OddPrimeSplit.At(n)), "p", "m")
								factors := c.Conjuncts(
									split,
									"p is prime",
									"p is not 2",
									"p is odd",
									"m is odd",
									"n = p·m",
									"m < n")
								prime, notTwo, oddP, oddM, nIs, mBelow :=
									factors[0], factors[1], factors[2], factors[3], factors[4], factors[5]
								nonzero := c.Have(
									"p and m are odd, so neither is 0",
									"p ≠ 0 ∧ m ≠ 0",
									By(oddP, oddM, nat_parity.NatOdd))
								c.Show(
									"(−1/n) = (−1/p)·(−1/m): the Legendre symbol at p times the law below n at m",
									CalcEq(
										Leg(
											c.TermAs[Int]("jacobi_symbol(-&1, p * m)"),
											"n = p·m",
											By(Normalized, nIs)),
										Leg(
											c.TermAs[Int]("jacobi_symbol(-1, p) * jacobi_symbol(-1, m)"),
											"the symbol is multiplicative in its lower argument",
											By(nonzero, JacobiMulRight.At(minusOne, p, m))),
										Leg(
											c.TermAs[Int]("legendre_symbol(-1, p) * jacobi_symbol(-1, m)"),
											"at the prime p it is the Legendre symbol",
											By(Normalized, prime, JacobiPrime.At(minusOne, p))),
										Leg(
											c.TermAs[Int]("(-&1) ^ «h»(p) * (-&1) ^ «h»(m)"),
											"the first supplement at the odd prime p, and the induction hypothesis at the odd m < n",
											By(prime, notTwo, oddM, mBelow, below.At(m), quadratic_residue.LegendreMinusOne.At(p))),
										Leg(
											c.TermAs[Int]("(-&1) ^ «h»(p * m)"),
											"the sign is multiplicative on odd numbers",
											By(oddP, oddM, HalfOddSignMul.At(p, m))),
										FinalLeg(
											"p·m = n",
											By(Normalized, nIs))))
							})
					}))))
	}),
})}

// EighthSignMul — on odd numbers the sign (−1)^((n² − 1)/8) is
// multiplicative. With m² = 8a + 1 and n² = 8b + 1, (m² − 1)/8 = a,
// (n² − 1)/8 = b and ((mn)² − 1)/8 = 8ab + a + b, since
// (mn)² = (8a + 1)(8b + 1); the part 8ab of the exponent contributes
// ((−1)⁸)^(ab) = 1, and the rest splits over a + b.
var EighthSignMul = eighthSignMulThm{family.Add(registry.ProofEntry{
	Name: "EighthSignMul",
	Key:  "prop_8bb427e061a54cbf",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"nat_odd(m)",
			"nat_odd(n)",
		},
		Conclusion: "(-int_of_num(1)) ^ div(m * n * (m * n) - 1, 8) = " +
			"(-int_of_num(1)) ^ div(m * m - 1, 8) * (-int_of_num(1)) ^ div(n * n - 1, 8)",
	}, func(arg *Argument, m, n *Expr[Nat], mOdd, nOdd Fact) {
		eight, zero := arg.Ctx().Nat(8), arg.Ctx().Nat(0)
		minusOne := arg.TermAs[Int]("-1")
		// m and n being odd, m² = 8a + 1 and n² = 8b + 1.
		a, mSquare := arg.UnpackAs[Nat](GroupPremises(mOdd, nat_parity.OddSquareModEight.At(m)), "a")
		b, nSquare := arg.UnpackAs[Nat](GroupPremises(nOdd, nat_parity.OddSquareModEight.At(n)), "b")
		product := arg.Have(
			"so m²·n² = (8a + 1)(8b + 1)",
			"m * m * (n * n) = (8 * a + 1) * (8 * b + 1)",
			By(mSquare, nSquare))
		halves := arg.Have(
			"(m² − 1)/8 = a, (n² − 1)/8 = b and ((mn)² − 1)/8 = 8ab "+
				"+ a + b, each the quotient of an exact division by 8",
			"div(m * m - 1, 8) = a ∧ "+
				"div(n * n - 1, 8) = b ∧ "+
				"div(m * n * (m * n) - 1, 8) = 8 * (a * b) + (a + b)",
			ByArith(
				mSquare,
				nSquare,
				product,
				nat_div_mod.DivUniq.At(arg.TermAs[Nat]("m * m - 1"), eight, a, zero),
				nat_div_mod.DivUniq.At(arg.TermAs[Nat]("n * n - 1"), eight, b, zero),
				nat_div_mod.DivUniq.At(
					arg.TermAs[Nat]("m * n * (m * n) - 1"), eight, arg.TermAs[Nat]("8 * (a * b) + (a + b)"), zero)))
		power := arg.Have(
			"(−1)⁸ = 1",
			"(-1) ^ 8 = int_of_num(1)",
			ByArith())
		ab := arg.TermAs[Nat]("a * b")
		even := arg.Have(
			"so the part 8ab of the exponent contributes ((−1)⁸)^(ab) = 1",
			"(-int_of_num(1)) ^ (8 * (a * b)) = int_of_num(1)",
			By(power, int_pow.PowPow.At(minusOne, eight, ab), int_pow.OnePow.At(ab)))
		arg.Show(
			"and the rest of the exponent, a + b, splits into the two signs",
			ByArith(
				halves,
				even,
				int_pow.PowAdd.At(minusOne, arg.TermAs[Nat]("8 * (a * b)"), arg.TermAs[Nat]("a + b")),
				int_pow.PowAdd.At(minusOne, a, b)))
	}),
})}

// JacobiTwo — the second supplement for Jacobi symbols: for odd n,
// (2/n) = (−1)^((n² − 1)/8). By strong induction on n: at n = 1 both sides
// are 1. Past 1, a prime p divides n, n = p·m with p and m odd and m < n,
// and (2/n) = (2/p)·(2/m); the first factor is (−1)^((p² − 1)/8) at the
// odd prime p, the second is (−1)^((m² − 1)/8) by the induction hypothesis,
// and the two signs multiply to (−1)^(((pm)² − 1)/8).
var JacobiTwo = jacobiTwoThm{family.Add(registry.ProofEntry{
	Name: "JacobiTwo",
	Key:  "prop_bd41b6ea6de91afc",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
		},
		Conclusion: "jacobi_symbol(2, n) = (-1) ^ div(n * n - 1, 8)",
	}, func(a *Argument) {
		a.Show(
			"strong induction on n, splitting off one prime factor",
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted the law at every odd number below n, it holds at an odd n",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						below := b.Assume()
						odd := b.Assume()
						two := b.TermAs[Int]("2")
						b.Cases(b.Term("n = 1"))
						b.When(
							"n = 1: (2/1) = 1 = (−1)⁰",
							func(c *Argument, isOne Fact) {
								c.Show(
									"(1·1 − 1)/8 = 0",
									ByArith(
										isOne,
										JacobiAtOne.At(two),
										nat_div_mod.DivUniq.At(c.TermAs[Nat]("n * n - 1"), c.Ctx().Nat(8), c.Ctx().Nat(0), c.Ctx().Nat(0))))
							})
						b.Otherwise(
							"n > 1: split off an odd prime factor p, n = p·m",
							func(c *Argument, notOne Fact) {
								p, m, split := c.Unpack2As[Nat, Nat](
									GroupPremises(odd, notOne, nat_prime.OddPrimeSplit.At(n)), "p", "m")
								factors := c.Conjuncts(
									split,
									"p is prime",
									"p is not 2",
									"p is odd",
									"m is odd",
									"n = p·m",
									"m < n")
								prime, notTwo, oddP, oddM, nIs, mBelow :=
									factors[0], factors[1], factors[2], factors[3], factors[4], factors[5]
								nonzero := c.Have(
									"p and m are odd, so neither is 0",
									"p ≠ 0 ∧ m ≠ 0",
									By(oddP, oddM, nat_parity.NatOdd))
								c.Show(
									"(2/n) = (2/p)·(2/m): the Legendre symbol at p times the law below n at m",
									CalcEq(
										Leg(
											c.TermAs[Int]("jacobi_symbol(2, p * m)"),
											"n = p·m",
											By(Normalized, nIs)),
										Leg(
											c.TermAs[Int]("jacobi_symbol(2, p) * jacobi_symbol(2, m)"),
											"the symbol is multiplicative in its lower argument",
											By(nonzero, JacobiMulRight.At(two, p, m))),
										Leg(
											c.TermAs[Int]("legendre_symbol(2, p) * jacobi_symbol(2, m)"),
											"at the prime p it is the Legendre symbol",
											By(Normalized, prime, JacobiPrime.At(two, p))),
										Leg(
											c.TermAs[Int]("(-&1) ^ div(p * p - 1, 8) * (-&1) ^ div(m * m - 1, 8)"),
											"the second supplement at the odd prime p, and the induction hypothesis at the odd m < n",
											By(prime, notTwo, oddM, mBelow, below.At(m), quadratic_residue.LegendreTwoSign.At(p))),
										Leg(
											c.TermAs[Int]("(-&1) ^ div(p * m * (p * m) - 1, 8)"),
											"the sign is multiplicative on odd numbers",
											By(oddP, oddM, EighthSignMul.At(p, m))),
										FinalLeg(
											"p·m = n",
											By(Normalized, nIs))))
							})
					}))))
	}),
})}
