// prime_powers.go — the powers of a prime among the natural numbers: a
// number is coprime to a positive power of a prime p exactly when p does not
// divide it, the divisors of a power of p are the powers of p below it, and
// so a number whose square is a power of p is itself a power of p.

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CoprimePrimePowerIff — a number is coprime to a positive power of a prime p
// exactly when p does not divide it. If p divided a it would be a common
// divisor of a and p^k, which a prime is not allowed to be; if p does not
// divide a, a is coprime to p and so to every power of p.
var CoprimePrimePowerIff = coprimePrimePowerIffThm{family.Add(registry.ProofEntry{
	Name: "CoprimePrimePowerIff",
	Key:  "prop_dc272981dd480738",
	Build: family.Theorem(Statement{
		Binders: "∀p k a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < k",
		},
		Conclusion: "nat_coprime(a, p ^ k) ⇔ ¬(p ∣ a)",
	}, func(arg *Argument, p, k, a *Expr[Nat], prime, positive Fact) {
		power := arg.TermAs[Nat]("p ^ k")
		dividesPower := arg.Have(
			"p divides p^k = p·p^(k − 1)",
			"p ∣ p ^ k",
			By(
				positive,
				nat_monus.MulPowSubOne.At(p, k),
				nat_divides.DividesOwnMultiple.At(p, arg.TermAs[Nat]("p ^ (k - 1)"))))
		arg.Iff()
		arg.Forward(
			"a number coprime to p^k is not a multiple of p",
			func(forward *Argument, coprime Fact) {
				forward.Show(
					"p would be a common divisor of a and p^k, hence 1, and a prime is not 1",
					By(prime, coprime, dividesPower, nat_gcd.Coprime.At(a, power), PrimeDef.At(p)))
			})
		arg.Backward(
			"a number p does not divide is coprime to p^k",
			func(backward *Argument, notMultiple Fact) {
				backward.Show(
					"a prime not dividing a is coprime to it, so a is coprime to p and to every power of p",
					By(
						Normalized,
						prime,
						notMultiple,
						PrimeCoprimeIffNotDivides.At(p),
						nat_gcd.CoprimeSym.At(p, a),
						nat_gcd.CoprimePowRight.At(a, p, k)))
			})
	}),
})}

// PrimePowerDivisor — a divisor of a power of a prime p is itself a power
// of p, with an exponent no larger: induction on the exponent, the divisor
// kept general. The zeroth power is 1, whose only divisor is 1 = p ^ 0. A
// divisor of p ^ (n + 1) other than 1 has a prime factor, which divides
// p ^ (n + 1) and so is p; writing the divisor as p * e and cancelling p, e
// divides p ^ n, the induction hypothesis makes e a power p ^ k with k ≤ n,
// and the divisor is p ^ (k + 1).
var PrimePowerDivisor = primePowerDivisorThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerDivisor",
	Key:  "prop_d3c082efe1f39dc8",
	Build: family.Theorem(Statement{
		Binders: "∀p n d:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"d ∣ p ^ n",
		},
		Conclusion: "∃k:num. k ≤ n ∧ d = p ^ k",
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		atLeastTwo := a.Have(
			"a prime is at least 2",
			"2 ≤ p",
			By(prime, PrimeAtLeastTwo.At(p)))
		a.Induct("n")
		a.Base(
			"only 1 divides the zeroth power, and 1 is p ^ 0",
			func(b *Argument) {
				d := b.FixAs[Nat]("d")
				divides := b.Assume()
				b.Take(b.TermAs[Nat]("0"))
				b.Show(
					"p ^ 0 is 1, and a divisor of 1 is 1",
					ByArith(divides, nat_arith.NatPow, nat_divides.DividesOne.At(d)))
			})
		a.Step(
			"a divisor of p ^ suc(n) other than 1 is p times a divisor of p ^ n",
			func(b *Argument, ih Fact) {
				d := b.FixAs[Nat]("d")
				divides := b.Assume()
				exponent := b.TermAs[Nat]("suc(n)")
				power := b.TermAs[Nat]("p ^ suc(n)")
				notOne := b.Unless(
					b.TermAs[Bool]("d = 1"),
					"1 is the zeroth power",
					Given(func(c *Argument, one Fact) {
						c.Take(c.TermAs[Nat]("0"))
						c.Show(
							"p ^ 0 is 1, and 0 is at most suc(n)",
							ByArith(one, nat_arith.NatPow))
					}))
				pastOne := b.Have(
					"p ^ suc(n) is not 0, so neither is its divisor d, and d is not 1",
					"1 < d",
					ByArith(
						atLeastTwo,
						notOne,
						divides,
						nat_divides.DividesLessEqStrong.At(d, power),
						nat_order.PowPositive.At(p, exponent)))
				q, primeFactor := b.ObtainAs[Nat](
					"d has a prime factor q",
					"∃q:num. nat_prime(q) ∧ q ∣ d",
					By(pastOne, PrimeFactor.At(d)))
				pDivides := b.Have(
					"q divides p ^ suc(n), hence the prime p, so q is p and p divides d",
					"p ∣ d",
					By(
						Normalized,
						prime,
						divides,
						primeFactor,
						nat_divides.DividesTrans.At(q, d, power),
						PrimeDividesPower.At(q, p, exponent),
						PrimeDividesPrime.At(q, p)))
				e, factor := b.ObtainAs[Nat](
					"write d as p * e",
					"∃e:num. d = p * e",
					By(pDivides, nat_divides.DividesFactor))
				cofactor := b.Have(
					"p * e divides p ^ suc(n) = p * p ^ n, and the nonzero p cancels",
					"e ∣ p ^ n",
					ByArith(
						atLeastTwo,
						factor,
						divides,
						nat_arith.NatPow,
						nat_divides.MulDividesLCancel.At(p, e, b.TermAs[Nat]("p ^ n"))))
				_, smaller := b.ObtainAs[Nat](
					"the induction hypothesis makes e a power p ^ k with k ≤ n",
					"∃k:num. k ≤ n ∧ e = p ^ k",
					By(ih.At(e), cofactor))
				b.Take(b.TermAs[Nat]("suc(k)"))
				b.Show(
					"so d = p * p ^ k is p ^ suc(k), and suc(k) ≤ suc(n)",
					By(Normalized, factor, smaller, nat_arith.NatPow, nat_order.SucLessEqSucIff))
			})
	}),
})}

// PrimePowerSquareRoot — a square root of a power of a prime is a power of
// that prime. It is PrimePowerDivisor at the root: a number divides its own
// square, here the power itself, and the bound on the exponent is dropped.
var PrimePowerSquareRoot = primePowerSquareRootThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerSquareRoot",
	Key:  "prop_f22486c1d1c7e07c",
	Build: family.Theorem(Statement{
		Binders: "∀p e s:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"s * s = p ^ e",
		},
		Conclusion: "∃n:num. s = p ^ n",
	}, func(a *Argument, p, e, s *Expr[Nat], prime, square Fact) {
		a.Show(
			"s divides its own square, the power p ^ e, so it is a power of p",
			By(prime, square, nat_divides.DividesOwnMultiple.At(s, s), PrimePowerDivisor.At(p, e, s)))
	}),
})}
