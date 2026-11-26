// real_character.go — the L-series of a real non-principal character does
// not vanish at 1, by Monsky's argument: the power series whose
// coefficients are the divisor sums of the character is unbounded as
// t → 1⁻, and bounded if the L-series vanished at 1.

package dirichlet_l_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_power_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// primePowerGeometric — at a prime p, a real character's divisor sum at pᴺ is
// the geometric sum 1 + re χ(p) + … + re χ(p)ᴺ, the divisors of pᴺ being the
// powers pʲ with j ≤ N, one each; and re χ(p) is 0, 1 or −1. The two
// prime-power bounds below read the sum by the sign of re χ(p).
func primePowerGeometric(
	a *Argument,
	q, p *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character, qPositive, realValues, prime Fact,
) (geometric, values Fact) {
	zero := a.TermAs[Nat]("0")
	powerMap := a.TermAs[Fun[Nat, Nat]]("«powerMap»")
	realPart := a.TermAs[Fun[Nat, Real]]("λd:num. re(χ(d))")
	powerValues := a.TermAs[Fun[Nat, Real]]("λj:num. re(χ(«powerMap»(j)))")
	geometricTerms := a.TermAs[Fun[Nat, Real]]("«geometricTerms»")
	base := a.TermAs[Real]("re(χ(p))")
	divisors := a.Have(
		"the divisors of the prime power are the images of the exponents",
		"∀N:num. image(«powerMap», 0 .. N) = {d:num | d ∣ p ^ N}",
		Derive(func(b *Argument) {
			N := b.FixAs[Nat]("N")
			b.Do(Simp(Fwd(num_segment.IntervalDef), Fwd(set_basic.Extension), Fwd(set_basic.InImage)))
			d := b.FixAs[Nat]("d")
			b.Iff()
			b.Forward(
				"every divisor is a power of p with exponent at most N",
				func(c *Argument, divides Fact) {
					c.Do(ByArith(prime, divides, nat_prime.PrimePowerDivisor.At(p, N, d)))
				})
			b.Backward(
				"each exponent in the interval gives a divisor of the prime power",
				func(c *Argument, inImage Fact) {
					j, exponent := c.UnpackAs[Nat](inImage, "j")
					c.Do(By(Normalized, exponent, nat_divides.PowDividesPow.At(p, j, N)))
				})
		}))
	reindexed := a.Have(
		"reindex the divisor sum by the exponents of the prime",
		"∀N:num. «divisorSum»(χ, p ^ N) = Σ_{j∈0 .. N} re(χ(«powerMap»(j)))",
		Derive(func(b *Argument) {
			N := b.FixAs[Nat]("N")
			injective := b.Have(
				"strict increase makes the power map injective",
				"injective_on(0 .. N, «powerMap»)",
				Derive(func(c *Argument) {
					c.Do(Simp(Fwd(functions.InjectiveOnDef)))
					i := c.FixAs[Nat]("i")
					j := c.FixAs[Nat]("j")
					equalPowers := c.Assume()
					c.Do(ByArith(
						prime,
						equalPowers,
						nat_prime.PrimeAtLeastTwo.At(p),
						nat_order.LessThanPow.At(p, i, j),
						nat_order.LessThanPow.At(p, j, i)))
				}))
			b.Show(
				"sum over the image of the injective power map",
				By(
					divisors.At(N),
					injective,
					real_sum.Image.At(b.TermAs[Set[Nat]]("0 .. N"), powerMap, realPart),
					functions.ComposeApply.At(realPart, powerMap)))
		}))
	embedded := a.Have(
		"the value at p is the embedding of its real part",
		"χ(p) = complex_of_real(re(χ(p)))",
		By(
			realValues.At(p),
			At(complex_field.ComplexData.Ext, χ.Apply(p), a.TermAs[Complex]("complex_of_real(re(χ(p)))")),
			complex_field.PartsOfReal.At(base)))
	powers := a.Have(
		"the character power law becomes a real power law",
		"∀j:num. re(χ(«powerMap»(j))) = «geometricTerms»(j)",
		Derive(func(b *Argument) {
			j := b.FixAs[Nat]("j")
			b.Do(By(
				Normalized,
				character,
				embedded,
				dirichlet_character.CharacterPow.At(q, p, j, χ),
				complex_field.OfRealPow.At(base, j),
				complex_field.PartsOfReal.At(b.TermAs[Real]("«geometricTerms»(j)"))))
		}))
	geometric = a.Have(
		"the divisor sum is a finite geometric sum",
		"∀N:num. «divisorSum»(χ, p ^ N) = sum(0 .. N, «geometricTerms»)",
		Derive(func(b *Argument) {
			N := b.FixAs[Nat]("N")
			b.Do(By(
				reindexed.At(N),
				powers,
				real_sum.IntervalCongruence.At(zero, N, powerValues, geometricTerms)))
		}))
	values = a.Have(
		"the real character value at p is 0, 1, or −1",
		"re(χ(p)) = &0 ∨ re(χ(p)) = &1 ∨ re(χ(p)) = -&1",
		By(
			Normalized,
			character,
			qPositive,
			realValues,
			dirichlet_character.RealCharacterValues.At(q, p, χ),
			complex_field.PartsOfReal.At(a.TermAs[Real]("&0")),
			complex_field.PartsOfReal.At(a.TermAs[Real]("&1")),
			complex_field.PartsOfReal.At(a.TermAs[Real]("-&1")),
			complex_field.OfRealNeg.At(a.TermAs[Real]("&1"))))
	return geometric, values
}

// CharacterDivisorSumPrimePowerNonneg — for a real character, the divisor sum
// at a power of a prime is nonnegative. It is the geometric sum of the powers
// of re χ(p): with a nonnegative base its terms are nonnegative; with base −1
// the sum is 1 or 0 as the exponent is even or odd.
var CharacterDivisorSumPrimePowerNonneg = characterDivisorSumPrimePowerNonnegThm{family.Add(registry.ProofEntry{
	Name: "CharacterDivisorSumPrimePowerNonneg",
	Key:  "prop_d77fc488fb083a2c",
	Build: family.Theorem(Statement{
		Binders: "∀q p k:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀n:num. im(χ(n)) = &0",
			"nat_prime(p)",
		},
		Conclusion: "&0 ≤ «divisorSum»(χ, p ^ k)",
		Abbrev: Abbrev{
			{Name: "powerMap", Text: "λj:num. p ^ j"},
			{Name: "geometricTerms", Text: "λj:num. re(χ(p)) ^ j"},
		},
	},
		func(
			a *Argument,
			q, p, k *Expr[Nat],
			χ *Arrow[Nat, Complex],
			character, qPositive, realValues, prime Fact,
		) {
			zero := a.TermAs[Nat]("0")
			geometricTerms := a.TermAs[Fun[Nat, Real]]("«geometricTerms»")
			base := a.TermAs[Real]("re(χ(p))")
			geometric, values := primePowerGeometric(a, q, p, χ, character, qPositive, realValues, prime)
			a.Cases(a.TermAs[Bool]("&0 ≤ re(χ(p))"))
			a.When(
				"a nonnegative base gives nonnegative terms",
				func(b *Argument, nonnegative Fact) {
					termsNonnegative := b.Have(
						"all powers of a nonnegative real are nonnegative",
						"∀j:num. &0 ≤ «geometricTerms»(j)",
						By(nonnegative, Where(real_pow.PowNonneg, "x", base)))
					b.Show(
						"the sum contains its initial term of 1, and the other terms are nonnegative",
						ByArith(
							geometric.At(k),
							termsNonnegative,
							nat_order.ZeroLessEq.At(k),
							real_sum.IntervalExtend.At(zero, zero, k, geometricTerms),
							real_sum.IntervalPoint.At(zero, geometricTerms),
							real_pow.PowExpZeroClause.At(base)))
				})
			a.Otherwise(
				"the negative base gives an alternating sum",
				func(b *Argument, negative Fact) {
					minusOne := b.TermAs[Real]("-&1")
					next := b.TermAs[Nat]("k + 1")
					baseIsMinusOne := b.Have(
						"the negative value among the three character values is −1",
						"re(χ(p)) = -&1",
						ByArith(negative, values))
					alternating := b.Simplified(geometric, Fwd(baseIsMinusOne))
					unitModulus := b.Have(
						"−1 has absolute value 1",
						"|-&1| = &1",
						ByArith(real_sgn_abs.AbsNegatedIffNonpos.At(minusOne)))
					upper := b.Have(
						"the power at k + 1 is at most its absolute value of 1",
						"(-&1) ^ (k + 1) ≤ &1",
						By(
							unitModulus,
							real_pow.AbsPow.At(minusOne, next),
							real_pow.OnePow.At(next),
							real_sgn_abs.AbsDominates.At(b.TermAs[Real]("(-&1) ^ (k + 1)"))))
					b.Show(
						"twice the sum is 1 − (−1)^(k+1), which is nonnegative",
						ByArith(upper, alternating.At(k), real_series.GeometricPartialSum.At(minusOne, k)))
				})
		}),
})}

// CharacterDivisorSumEvenPrimePowerAtLeastOne — for a real character, the
// divisor sum at an even power of a prime is at least 1. It is the geometric
// sum of the powers of re χ(p): with a nonnegative base each term is
// nonnegative and the first is 1; with base −1 the 2k + 1 terms alternate from
// 1 and sum to 1.
var CharacterDivisorSumEvenPrimePowerAtLeastOne = characterDivisorSumEvenPrimePowerAtLeastOneThm{family.Add(registry.ProofEntry{
	Name: "CharacterDivisorSumEvenPrimePowerAtLeastOne",
	Key:  "prop_95690ab927ddca75",
	Build: family.Theorem(Statement{
		Binders: "∀q p k:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀n:num. im(χ(n)) = &0",
			"nat_prime(p)",
		},
		Conclusion: "&1 ≤ «divisorSum»(χ, p ^ (2 * k))",
		Abbrev: Abbrev{
			{Name: "powerMap", Text: "λj:num. p ^ j"},
			{Name: "geometricTerms", Text: "λj:num. re(χ(p)) ^ j"},
		},
	},
		func(
			a *Argument,
			q, p, k *Expr[Nat],
			χ *Arrow[Nat, Complex],
			character, qPositive, realValues, prime Fact,
		) {
			zero := a.TermAs[Nat]("0")
			two := a.TermAs[Nat]("2")
			even := a.TermAs[Nat]("2 * k")
			geometricTerms := a.TermAs[Fun[Nat, Real]]("«geometricTerms»")
			base := a.TermAs[Real]("re(χ(p))")
			geometric, values := primePowerGeometric(a, q, p, χ, character, qPositive, realValues, prime)
			a.Cases(a.TermAs[Bool]("&0 ≤ re(χ(p))"))
			a.When(
				"a nonnegative base gives nonnegative terms",
				func(b *Argument, nonnegative Fact) {
					termsNonnegative := b.Have(
						"all powers of a nonnegative real are nonnegative",
						"∀j:num. &0 ≤ «geometricTerms»(j)",
						By(nonnegative, Where(real_pow.PowNonneg, "x", base)))
					b.Show(
						"the sum contains its initial term of 1, and the other terms are nonnegative",
						By(
							geometric.At(even),
							termsNonnegative,
							nat_order.ZeroLessEq.At(even),
							real_sum.IntervalExtend.At(zero, zero, even, geometricTerms),
							real_sum.IntervalPoint.At(zero, geometricTerms),
							real_pow.PowExpZeroClause.At(base)))
				})
			a.Otherwise(
				"the negative base gives an alternating sum",
				func(b *Argument, negative Fact) {
					minusOne := b.TermAs[Real]("-&1")
					baseIsMinusOne := b.Have(
						"the negative value among the three character values is −1",
						"re(χ(p)) = -&1",
						ByArith(negative, values))
					alternating := b.Simplified(geometric, Fwd(baseIsMinusOne))
					unitSquare := b.Have(
						"−1 has square 1",
						"(-&1) ^ 2 = &1",
						ByArith(real_pow.PowTwo.At(minusOne)))
					evenPower := b.Have(
						"each even power of −1 is 1",
						"(-&1) ^ (2 * k) = &1",
						By(unitSquare, real_pow.PowPow.At(minusOne, two, k), real_pow.OnePow.At(k)))
					b.Show(
						"twice the sum is 1 − (−1)^(2k+1) = 2",
						ByArith(
							evenPower,
							alternating.At(even),
							real_series.GeometricPartialSum.At(minusOne, even),
							real_pow.PowAddOne.At(minusOne, even)))
				})
		}),
})}

// realPartsMultiply — a real character's real parts multiply at coprime
// arguments, the character being multiplicative and its imaginary parts zero.
func realPartsMultiply(
	a *Argument,
	q *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character, realValues Fact,
) Fact {
	return a.Have(
		"the real parts multiply because the imaginary parts vanish",
		"∀u v:num. nat_coprime(u, v) ⇒ re(χ(u * v)) = re(χ(u)) * re(χ(v))",
		Derive(func(b *Argument) {
			u := b.FixAs[Nat]("u")
			v := b.FixAs[Nat]("v")
			b.Assume()
			b.Do(ByArith(
				character,
				dirichlet_character.CharacterMul.At(q, u, v, χ),
				realValues.At(u),
				complex_field.PartsMul.At(b.TermAs[Complex]("χ(u)"), b.TermAs[Complex]("χ(v)"))))
		}))
}

// primePowerSplit is the step of the strong inductions below at a positive N
// other than 1: N = pᵃ·c for a prime p dividing N, its multiplicity a, and a
// cofactor c that p does not divide.
type primePowerSplit struct {
	p, c *Expr[Nat]
	// primeDivisor: nat_prime(p) ∧ p ∣ N.
	primeDivisor Fact
	// factorization: N = «primePower»(p, N) * c ∧ ¬(p ∣ c).
	factorization Fact
	// coprime: nat_coprime(p, c).
	coprime Fact
	// factorsPositive: 0 < «primePower»(p, N) ∧ 0 < c.
	factorsPositive Fact
	// cofactorSmaller: c < N.
	cofactorSmaller Fact
}

// splitPrimePower takes a positive N other than 1 apart as primePowerSplit
// says: a prime divisor p exists, removing every factor p leaves a cofactor c
// coprime to p, and pᵃ > 1 makes c smaller than N.
func splitPrimePower(b *Argument, N *Expr[Nat], positive, notOne Fact) primePowerSplit {
	one := b.TermAs[Nat]("1")
	p, primeDivisor := b.ObtainAs[Nat](
		"a positive integer other than 1 has a prime divisor",
		"∃p:num. nat_prime(p) ∧ p ∣ N",
		ByArith(notOne, positive, nat_prime.PrimeFactor.At(N)))
	cofactor, factorization := b.ObtainAs[Nat](
		"remove every occurrence of p from N",
		"∃c:num. N = «primePower»(p, N) * c ∧ ¬(p ∣ c)",
		ByArith(
			primeDivisor,
			positive,
			nat_prime.PrimeAtLeastTwo.At(p),
			nat_multiplicity.MultiplicityCofactor.At(p, N)))
	power := b.TermAs[Nat]("«primePower»(p, N)")
	coprime := b.Have(
		"maximality of the exponent makes p coprime to the cofactor",
		"nat_coprime(p, c)",
		By(Normalized, primeDivisor, factorization, nat_prime.PrimeCoprimeIffNotDivides.At(p)))
	factorsPositive := b.Have(
		"both factors of the positive integer N are positive",
		"0 < «primePower»(p, N) ∧ 0 < c",
		ByArith(positive, factorization, nat_arith.MulEqZero.At(power, cofactor)))
	powerDivisible := b.Have(
		"the prime divides the power after cancellation of the coprime cofactor",
		"p ∣ «primePower»(p, N)",
		By(Normalized, primeDivisor, factorization, coprime, nat_gcd.CoprimeCancel.At(p, power, cofactor)))
	nontrivialPower := b.Have(
		"the positive multiple of the prime exceeds 1",
		"1 < «primePower»(p, N)",
		ByArith(
			powerDivisible,
			factorsPositive,
			primeDivisor,
			nat_divides.DividesLessEq.At(p, power),
			nat_prime.PrimeAtLeastTwo.At(p)))
	cofactorSmaller := b.Have(
		"multiplication by the prime power strictly increases the cofactor",
		"c < N",
		ByArith(
			factorization,
			factorsPositive,
			nontrivialPower,
			nat_order.LessThanMulCancel.At(cofactor, one, power)))
	return primePowerSplit{
		p:               p,
		c:               cofactor,
		primeDivisor:    primeDivisor,
		factorization:   factorization,
		coprime:         coprime,
		factorsPositive: factorsPositive,
		cofactorSmaller: cofactorSmaller,
	}
}

// CharacterDivisorSumNonneg — for a real character, the divisor sum is
// nonnegative at every positive number. By strong induction: a number other
// than 1 is pᵃ·c with c smaller and coprime to pᵃ, the divisor sum is
// multiplicative, and it is nonnegative at pᵃ.
var CharacterDivisorSumNonneg = characterDivisorSumNonnegThm{family.Add(registry.ProofEntry{
	Name: "CharacterDivisorSumNonneg",
	Key:  "prop_3771c66f96d02908",
	Build: family.Theorem(Statement{
		Binders: "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀k:num. im(χ(k)) = &0",
			"0 < n",
		},
		Conclusion: "&0 ≤ «divisorSum»(χ, n)",
		Abbrev: Abbrev{
			{Name: "primePower", Text: "λp:num. λN:num. p ^ nat_multiplicity(p, N)"},
		},
	},
		func(
			a *Argument,
			q, n *Expr[Nat],
			χ *Arrow[Nat, Complex],
			character, qPositive, realValues, nPositive Fact,
		) {
			realPart := a.TermAs[Fun[Nat, Real]]("λd:num. re(χ(d))")
			zero := a.TermAs[Nat]("0")
			two := a.TermAs[Nat]("2")
			multiplicative := realPartsMultiply(a, q, χ, character, realValues)
			bound := a.Have(
				"strong induction gives the bound at each positive integer",
				"∀N:num. 0 < N ⇒ &0 ≤ «divisorSum»(χ, N)",
				ByInduction(nat_order.StrongInduction,
					Case(
						"a full prime power leaves a smaller positive cofactor",
						Derive(func(b *Argument) {
							N := b.FixAs[Nat]("N")
							smaller := b.Assume()
							positive := b.Assume()
							notOne := b.Unless(
								b.TermAs[Bool]("N = 1"),
								"at 1 the prime-power bound applies to 2^0",
								Derive(func(c *Argument) {
									c.Do(ByArith(
										character,
										qPositive,
										realValues,
										c.Hyp("N = 1"),
										nat_prime.PrimeTwo,
										CharacterDivisorSumPrimePowerNonneg.At(q, two, zero, χ)))
								}))
							split := splitPrimePower(b, N, positive, notOne)
							exponent := b.TermAs[Nat]("nat_multiplicity(p, N)")
							power := b.TermAs[Nat]("«primePower»(p, N)")
							cofactorBound := b.Have(
								"the induction hypothesis bounds the cofactor",
								"&0 ≤ «divisorSum»(χ, c)",
								By(split.factorsPositive, split.cofactorSmaller, smaller.At(split.c)))
							powerBound := b.Have(
								"the prime-power bound applies at the multiplicity",
								"&0 ≤ «divisorSum»(χ, «primePower»(p, N))",
								By(
									character,
									qPositive,
									realValues,
									split.primeDivisor,
									CharacterDivisorSumPrimePowerNonneg.At(q, split.p, exponent, χ)))
							powerCoprime := b.Have(
								"taking the power of p preserves coprimality with the cofactor",
								"nat_coprime(«primePower»(p, N), c)",
								By(
									split.coprime,
									nat_gcd.CoprimeSym.At(split.p, split.c),
									nat_gcd.CoprimePowRight.At(split.c, split.p, exponent),
									nat_gcd.CoprimeSym.At(split.c, power)))
							sumProduct := b.Have(
								"the divisor sum at N factors over the coprime pair",
								"«divisorSum»(χ, N) = «divisorSum»(χ, «primePower»(p, N)) * «divisorSum»(χ, c)",
								By(
									multiplicative,
									split.factorization,
									split.factorsPositive,
									powerCoprime,
									totient.DivisorSumMultiplicative.At(realPart, power, split.c)))
							b.Show(
								"a product of nonnegative factors is nonnegative",
								ByArith(sumProduct, powerBound, cofactorBound))
						}))))
			a.Show(
				"apply the bound at n",
				By(bound.At(n), nPositive))
		}),
})}

// CharacterDivisorSumSquareAtLeastOne — for a real character, the divisor sum
// is at least 1 at every positive square. By strong induction: a number m
// other than 1 is pᵃ·c with c smaller and coprime to p, so m² is p²ᵃ·c² with
// coprime factors, the divisor sum is multiplicative, and it is at least 1 at
// the even prime power p²ᵃ.
var CharacterDivisorSumSquareAtLeastOne = characterDivisorSumSquareAtLeastOneThm{family.Add(registry.ProofEntry{
	Name: "CharacterDivisorSumSquareAtLeastOne",
	Key:  "prop_346dcaf301d693bf",
	Build: family.Theorem(Statement{
		Binders: "∀q m:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀k:num. im(χ(k)) = &0",
			"0 < m",
		},
		Conclusion: "&1 ≤ «divisorSum»(χ, m * m)",
		Abbrev: Abbrev{
			{Name: "primePower", Text: "λp:num. λN:num. p ^ nat_multiplicity(p, N)"},
			{Name: "primePowerSquared", Text: "λp:num. λN:num. p ^ (2 * nat_multiplicity(p, N))"},
		},
	},
		func(
			a *Argument,
			q, m *Expr[Nat],
			χ *Arrow[Nat, Complex],
			character, qPositive, realValues, mPositive Fact,
		) {
			realPart := a.TermAs[Fun[Nat, Real]]("λd:num. re(χ(d))")
			zero := a.TermAs[Nat]("0")
			two := a.TermAs[Nat]("2")
			multiplicative := realPartsMultiply(a, q, χ, character, realValues)
			bound := a.Have(
				"strong induction gives the bound at the square of each positive integer",
				"∀N:num. 0 < N ⇒ &1 ≤ «divisorSum»(χ, N * N)",
				ByInduction(nat_order.StrongInduction,
					Case(
						"a full prime power leaves a smaller positive cofactor",
						Derive(func(b *Argument) {
							N := b.FixAs[Nat]("N")
							smaller := b.Assume()
							positive := b.Assume()
							notOne := b.Unless(
								b.TermAs[Bool]("N = 1"),
								"at 1 the even prime-power bound applies to 2^(2·0)",
								Derive(func(c *Argument) {
									c.Do(ByArith(
										character,
										qPositive,
										realValues,
										c.Hyp("N = 1"),
										nat_prime.PrimeTwo,
										CharacterDivisorSumEvenPrimePowerAtLeastOne.At(q, two, zero, χ)))
								}))
							split := splitPrimePower(b, N, positive, notOne)
							exponent := b.TermAs[Nat]("nat_multiplicity(p, N)")
							doubledExponent := b.TermAs[Nat]("2 * nat_multiplicity(p, N)")
							power := b.TermAs[Nat]("«primePower»(p, N)")
							powerSquared := b.TermAs[Nat]("«primePowerSquared»(p, N)")
							cofactorSquared := b.TermAs[Nat]("c * c")
							cofactorBound := b.Have(
								"the induction hypothesis bounds the square of the cofactor",
								"&1 ≤ «divisorSum»(χ, c * c)",
								By(split.factorsPositive, split.cofactorSmaller, smaller.At(split.c)))
							powerBound := b.Have(
								"the even prime-power bound applies at twice the multiplicity",
								"&1 ≤ «divisorSum»(χ, «primePowerSquared»(p, N))",
								By(
									character,
									qPositive,
									realValues,
									split.primeDivisor,
									CharacterDivisorSumEvenPrimePowerAtLeastOne.At(q, split.p, exponent, χ)))
							squaresCoprime := b.Have(
								"the squared factors are coprime",
								"nat_coprime(«primePowerSquared»(p, N), c * c)",
								By(
									split.coprime,
									nat_gcd.CoprimeSym.At(split.p, split.c),
									nat_gcd.CoprimeMul.At(split.c, split.c, split.p),
									nat_gcd.CoprimePowRight.At(cofactorSquared, split.p, doubledExponent),
									nat_gcd.CoprimeSym.At(cofactorSquared, powerSquared)))
							squaredFactors := b.Have(
								"the square of N is the product of the positive squared factors",
								"N * N = «primePowerSquared»(p, N) * (c * c) ∧ 0 < «primePowerSquared»(p, N) ∧ 0 < c * c",
								Derive(func(c *Argument) {
									powerSquare := c.Have(
										"squaring the prime power doubles its exponent",
										"«primePowerSquared»(p, N) = «primePower»(p, N) * «primePower»(p, N)",
										By(
											nat_arith.MulSym.At(two, exponent),
											nat_arith.PowPow.At(split.p, exponent, two),
											nat_arith.PowTwo.At(power)))
									c.Do(SplitConjAll(
										Case(
											"squaring distributes over the product",
											By(
												split.factorization,
												powerSquare,
												nat_arith.MulPowDistrib.At(power, split.c, two),
												nat_arith.PowTwo.At(N),
												nat_arith.PowTwo.At(power),
												nat_arith.PowTwo.At(split.c))),
										Case(
											"the square of the prime power is positive",
											ByArith(split.factorsPositive, powerSquare, nat_arith.MulEqZero.At(power, power))),
										Case(
											"the square of the cofactor is positive",
											ByArith(split.factorsPositive, nat_arith.MulEqZero.At(split.c, split.c)))))
								}))
							squaredSumProduct := b.Have(
								"the divisor sum at the square of N factors over the squared pair",
								"«divisorSum»(χ, N * N) = «divisorSum»(χ, «primePowerSquared»(p, N)) * «divisorSum»(χ, c * c)",
								By(
									multiplicative,
									squaredFactors,
									squaresCoprime,
									totient.DivisorSumMultiplicative.At(realPart, powerSquared, cofactorSquared)))
							b.Show(
								"a product of factors at least 1 is at least 1",
								ByArith(squaredSumProduct, powerBound, cofactorBound))
						}))))
			a.Show(
				"apply the bound at m",
				By(bound.At(m), mPositive))
		}),
})}

// realPartsBounded — a character's real parts are at most 1 in size, its
// values being so: the bound real_power_series.LambertExpansion asks of the
// sequence re∘χ.
func realPartsBounded(
	a *Argument,
	q *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character, qPositive Fact,
) Fact {
	return a.Have(
		"the real parts of the character's values are at most 1 in size",
		"∀n:num. |re(χ(n))| ≤ &1",
		a.ForEach(func(n *Expr[Nat]) Action {
			return ByArith(
				character,
				qPositive,
				dirichlet_character.CharacterAbsLessEqOne.At(q, n, χ),
				complex_abs.ReLessEqAbs.At(χ.Apply(n)))
		}))
}

// MonskyWeights — the weights b(n, t) = 1/(n(1 − t)) − tⁿ/(1 − tⁿ) start at
// b(1, t) = 1, are nonnegative, and decrease in n. Nonnegativity: each of the
// n + 1 terms of Σ_{i≤n} tⁱ = (1 − tⁿ⁺¹)/(1 − t) is at least tⁿ⁺¹, so
// (n + 1)(1 − t)tⁿ⁺¹ ≤ 1 − tⁿ⁺¹. Decrease: the product (Σ_{i<n} tⁱ)(Σ_{j≤n} tʲ)
// sums tⁱtʲ over the rectangle of exponent pairs, whose reflection
// (i, j) ↦ (n − 1 − i, n − j) sends a term tᵃ to t²ⁿ⁻¹⁻ᵃ. For a ≤ n − 1,
// tᵃ + t²ⁿ⁻¹⁻ᵃ − tⁿ − tⁿ⁻¹ = tᵃ(1 − tⁿ⁻ᵃ)(1 − tⁿ⁻¹⁻ᵃ) ≥ 0, so a term and its
// reflection are at least 2tⁿ and the product is at least n(n + 1)tⁿ. Times
// (1 − t)² this is n(n + 1)(1 − t)²tⁿ ≤ (1 − tⁿ)(1 − tⁿ⁺¹), and the difference
// of the two sides is the drop b(n, t) − b(n + 1, t) times its positive common
// denominator.
var MonskyWeights = monskyWeightsThm{family.Add(registry.ProofEntry{
	Name: "MonskyWeights",
	Key:  "prop_5a54ee0a0891209c",
	Reading: "At t = 0 the weight is 1/n. The hypothesis 0 < n is " +
		"needed for the decrease alone: a quotient by zero is zero in this " +
		"encoding, so weight(0, t) = 1/0 − 1/0 is 0, below weight(1, t) = 1.",
	Build: family.Sections(Statement{
		Binders: "∀t:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ t",
			"t < &1",
			"0 < n",
		},
		Conclusion: "«weight»(1, t) = &1 ∧ &0 ≤ «weight»(n + 1, t) ∧ «weight»(n + 1, t) ≤ «weight»(n, t)",
		Abbrev: Abbrev{
			{Name: "rectangle", Text: "set_cross(0 .. n - 1, 0 .. n)"},
			{Name: "reflect", Text: "λp:prod(num, num). (n - 1 - fst(p), n - snd(p))"},
			{Name: "monomial", Text: "λp:prod(num, num). t ^ fst(p) * t ^ snd(p)"},
			{Name: "denominator", Text: "&n * &(n + 1) * (&1 - t) * (&1 - t ^ n) * (&1 - t ^ (n + 1))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// The rectangle bound: the n(n + 1) terms tⁱtʲ of the product pair off
		// with their reflections, each pair at least 2tⁿ.
		rectangleBound := ctx.Lemma(Statement{
			Binders: "∀t:real. ∀n:num.",
			Hypotheses: []string{
				"&0 ≤ t",
				"t < &1",
				"0 < n",
			},
			Conclusion: "&n * &(n + 1) * t ^ n ≤ (Σ_{k∈0 .. n - 1} t ^ k) * Σ_{k∈0 .. n} t ^ k",
		}, func(a *Argument, t *Expr[Real], n *Expr[Nat], nonnegative, belowOne, positive Fact) {
			pairBound := a.Have(
				"for i ≤ n − 1 and i + j = 2n − 1, tⁱ + tʲ is at least tⁿ + tⁿ⁻¹, hence at least 2tⁿ",
				"∀i j:num. i ≤ n - 1 ∧ i + j = 2 * n - 1 ⇒ &2 * t ^ n ≤ t ^ i + t ^ j",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.FixAs[Nat]("j")
					exponents := b.Assume()
					zero := b.TermAs[Nat]("0")
					gap := b.TermAs[Nat]("n - i")
					shortGap := b.TermAs[Nat]("n - 1 - i")
					splits := b.Have(
						"split the exponents at n and at n − 1",
						"i + (n - i) = n ∧ i + (n - 1 - i) = n - 1 ∧ n + (n - 1 - i) = j",
						ByArith(exponents))
					factors := b.Have(
						"so tⁿ = tⁱ·tⁿ⁻ⁱ, tⁿ⁻¹ = tⁱ·tⁿ⁻¹⁻ⁱ and tʲ = tⁿ·tⁿ⁻¹⁻ⁱ",
						"t ^ n = t ^ i * t ^ (n - i) ∧ "+
							"t ^ (n - 1) = t ^ i * t ^ (n - 1 - i) ∧ "+
							"t ^ j = t ^ n * t ^ (n - 1 - i)",
						By(
							splits,
							real_pow.PowAdd.At(t, i, gap),
							real_pow.PowAdd.At(t, i, shortGap),
							real_pow.PowAdd.At(t, n, shortGap)))
					identity := b.Have(
						"the excess of tⁱ + tʲ over tⁿ + tⁿ⁻¹ factors as tⁱ(1 − tⁿ⁻ⁱ)(1 − tⁿ⁻¹⁻ⁱ)",
						"t ^ i + t ^ j - t ^ n - t ^ (n - 1) = t ^ i * (&1 - t ^ (n - i)) * (&1 - t ^ (n - 1 - i))",
						ByArith(factors))
					signs := b.Have(
						"the powers of t lie in [0, 1] and decrease in the exponent",
						"&0 ≤ t ^ i ∧ t ^ (n - i) ≤ &1 ∧ t ^ (n - 1 - i) ≤ &1 ∧ t ^ n ≤ t ^ (n - 1)",
						ByArith(
							nonnegative,
							belowOne,
							real_pow.PowNonneg.At(t, i),
							real_pow.PowMonoExpBelowOne.At(t, zero, gap),
							real_pow.PowMonoExpBelowOne.At(t, zero, shortGap),
							real_pow.PowMonoExpBelowOne.At(t, b.TermAs[Nat]("n - 1"), n),
							real_pow.PowExpZeroClause.At(t)))
					factorSign := b.Have(
						"so 1 − tⁿ⁻ⁱ and 1 − tⁿ⁻¹⁻ⁱ are nonnegative, and so is their product",
						"&0 ≤ (&1 - t ^ (n - i)) * (&1 - t ^ (n - 1 - i))",
						ByArith(signs))
					b.Show(
						"the excess is nonnegative, and tⁿ⁻¹ is at least tⁿ",
						ByArith(identity, factorSign, signs))
				}))
			anyOrder := a.Have(
				"the bound holds whichever of i and j is the smaller",
				"∀i j:num. i + j = 2 * n - 1 ⇒ &2 * t ^ n ≤ t ^ i + t ^ j",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					j := b.FixAs[Nat]("j")
					sum := b.Assume()
					b.Cases(b.TermAs[Bool]("i ≤ n - 1"))
					b.When(
						"i is at most n − 1",
						func(c *Argument, smaller Fact) {
							c.Show(
								"the pair bound applies as it stands",
								By(smaller, sum, pairBound.At(i, j)))
						})
					b.Otherwise(
						"i exceeds n − 1, so j is the smaller exponent",
						func(c *Argument, larger Fact) {
							c.Show(
								"j ≤ n − 1, as i + j = 2n − 1, and the pair bound applies with i and j exchanged",
								ByArith(larger, sum, pairBound.At(j, i)))
						})
				}))
			zero := a.TermAs[Nat]("0")
			lower := a.TermAs[Set[Nat]]("0 .. n - 1")
			upper := a.TermAs[Set[Nat]]("0 .. n")
			rectangle := a.TermAs[Set[Prod[Nat, Nat]]]("«rectangle»")
			monomial := a.TermAs[Fun[Prod[Nat, Nat], Real]]("«monomial»")
			reflected := a.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). «monomial»(«reflect»(p))")
			inRange := a.Have(
				"a point of the rectangle has coordinates at most n − 1 and n",
				"∀p:prod(num, num). p ∈ «rectangle» ⇒ fst(p) ≤ n - 1 ∧ snd(p) ≤ n",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inRectangle := b.Assume()
					b.Show(
						"a pair lies in a product exactly when its coordinates lie in the factors",
						By(inRectangle, set_product.InCrossProjections.At(lower, upper, p)))
				}))
			reflection := a.Have(
				"the reflection maps the rectangle into itself and undoes itself there",
				"∀p:prod(num, num). p ∈ «rectangle» ⇒ «reflect»(p) ∈ «rectangle» ∧ «reflect»(«reflect»(p)) = p",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inRectangle := b.Assume()
					first := b.TermAs[Nat]("n - 1 - fst(p)")
					second := b.TermAs[Nat]("n - snd(p)")
					back := b.Have(
						"reflecting the coordinates twice gives them back, fst(p) being at most n − 1 and snd(p) at most n",
						"«reflect»(«reflect»(p)) = (fst(p), snd(p))",
						ByArith(
							inRectangle,
							inRange.At(p),
							pairs.Fst.At(first, second),
							pairs.Snd.At(first, second),
							pairs.PairEq.At(
								b.TermAs[Nat]("n - 1 - fst(«reflect»(p))"),
								b.TermAs[Nat]("n - snd(«reflect»(p))"),
								b.TermAs[Nat]("fst(p)"),
								b.TermAs[Nat]("snd(p)"))))
					b.Show(
						"the reflected point stays in the rectangle and reflects back to p",
						SplitConj(
							Case(
								"its coordinates n − 1 − fst(p) and n − snd(p) are at most n − 1 and n",
								ByArith(set_product.InCross.At(lower, upper, first, second))),
							Case(
								"a pair is its two coordinates",
								By(back, pairs.PairEta.At(p)))))
				}))
			pointBound := a.Have(
				"a term and its reflection together are at least 2tⁿ",
				"∀p:prod(num, num). p ∈ «rectangle» ⇒ &2 * t ^ n ≤ «monomial»(p) + «monomial»(«reflect»(p))",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inRectangle := b.Assume()
					first := b.TermAs[Nat]("n - 1 - fst(p)")
					second := b.TermAs[Nat]("n - snd(p)")
					exponents := b.Have(
						"the exponents of the term and of its reflection add up to 2n − 1",
						"fst(p) + snd(p) + (fst(«reflect»(p)) + snd(«reflect»(p))) = 2 * n - 1",
						ByArith(inRectangle, inRange.At(p), pairs.Fst.At(first, second), pairs.Snd.At(first, second)))
					b.Show(
						"each term is t to the sum of its exponents",
						By(
							exponents,
							anyOrder.At(
								b.TermAs[Nat]("fst(p) + snd(p)"),
								b.TermAs[Nat]("fst(«reflect»(p)) + snd(«reflect»(p))")),
							real_pow.PowAdd.At(t, b.TermAs[Nat]("fst(p)"), b.TermAs[Nat]("snd(p)")),
							real_pow.PowAdd.At(
								t,
								b.TermAs[Nat]("fst(«reflect»(p))"),
								b.TermAs[Nat]("snd(«reflect»(p))"))))
				}))
			finiteSides := a.Have(
				"both index intervals are finite",
				"finite(0 .. n - 1) ∧ finite(0 .. n)",
				By(num_segment.Finite.At(zero, a.TermAs[Nat]("n - 1")), num_segment.Finite.At(zero, n)))
			finiteRectangle := a.Have(
				"and so is the rectangle",
				"finite(«rectangle»)",
				By(finiteSides, finite_set.FiniteProduct.At(lower, upper)))
			reflectedSum := a.Have(
				"the reflection permutes the rectangle, so the reflected terms have the same sum",
				"Σ_{p∈«rectangle»} «monomial»(«reflect»(p)) = Σ_{p∈«rectangle»} «monomial»(p)",
				Unfold(real_sum.RealSumDef),
				By(
					reflection,
					real_ring.MonoidalAdd,
					monoidal.Reindex.At(
						a.TermAs[Op[Real]]("real_add"),
						rectangle,
						rectangle,
						reflected,
						monomial,
						a.TermAs[Fun[Prod[Nat, Nat], Prod[Nat, Nat]]]("«reflect»"),
						a.TermAs[Fun[Prod[Nat, Nat], Prod[Nat, Nat]]]("«reflect»"))))
			predecessor := a.Have(
				"n is the successor of its predecessor",
				"n - 1 + 1 = n",
				ByArith(positive))
			rectangleCount := a.Have(
				"the rectangle has n(n + 1) points",
				"card(«rectangle») = n * (n + 1)",
				ByArith(
					predecessor,
					finiteSides,
					cardinality.CardProduct.At(lower, upper),
					num_segment.Card.At(zero, a.TermAs[Nat]("n - 1")),
					num_segment.Card.At(zero, n)))
			doubledSum := a.Have(
				"summing the pair bound over the rectangle counts every term twice",
				"&(n * (n + 1)) * (&2 * t ^ n) ≤ &2 * Σ_{p∈«rectangle»} «monomial»(p)",
				ByArith(
					finiteRectangle,
					pointBound,
					rectangleCount,
					reflectedSum,
					real_sum.Monotone.At(
						rectangle,
						a.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). &2 * t ^ n"),
						a.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). «monomial»(p) + «monomial»(«reflect»(p))")),
					real_sum.Const.At(rectangle, a.TermAs[Real]("&2 * t ^ n")),
					real_sum.Add.At(monomial, reflected, rectangle)))
			a.Show(
				"the rectangle sum is the product of the two geometric sums",
				ByArith(
					doubledSum,
					finiteSides,
					real_sum.ProductOfSums.At(
						lower,
						upper,
						a.TermAs[Fun[Nat, Real]]("λk:num. t ^ k"),
						a.TermAs[Fun[Nat, Real]]("λk:num. t ^ k"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			t *Expr[Real],
			n *Expr[Nat],
			nonnegative, belowOne, positive Fact,
		) {
			a.Show(
				"the weight at one, its nonnegativity, and its decrease",
				SplitConjAll(
					Case(
						"at n = 1 both denominators are 1 − t, so the weight is (1 − t)/(1 − t) = 1",
						ByArith(belowOne)),
					Case(
						"the next weight is nonnegative: each of the n + 1 terms of Σ_{i≤n} tⁱ is at least tⁿ⁺¹",
						Derive(func(b *Argument) {
							zero := b.TermAs[Nat]("0")
							positiveDenominators := b.Have(
								"1 − t, n + 1 and 1 − tⁿ⁺¹ are positive, tⁿ⁺¹ being at most t",
								"&0 < &1 - t ∧ &0 < &(n + 1) ∧ &0 < &1 - t ^ (n + 1)",
								ByArith(
									nonnegative,
									belowOne,
									real_pow.PowMonoExpBelowOne.At(t, b.TermAs[Nat]("1"), b.TermAs[Nat]("n + 1")),
									real_pow.PowOne.At(t)))
							termsAbove := b.Have(
								"each term tⁱ with i ≤ n is at least tⁿ⁺¹",
								"∀i:num. 0 ≤ i ∧ i ≤ n ⇒ t ^ (n + 1) ≤ t ^ i",
								Derive(func(c *Argument) {
									i := c.FixAs[Nat]("i")
									inRange := c.Assume()
									c.Show(
										"a base in [0, 1] decreases in the exponent",
										ByArith(
											inRange,
											nonnegative,
											belowOne,
											real_pow.PowMonoExpBelowOne.At(t, i, c.TermAs[Nat]("n + 1"))))
								}))
							sumAbove := b.Have(
								"so the n + 1 terms sum to at least (n + 1)·tⁿ⁺¹",
								"&(n + 1) * t ^ (n + 1) ≤ Σ_{i∈0 .. n} t ^ i",
								ByArith(
									termsAbove,
									real_sum.IntervalMonotone.At(
										zero,
										n,
										b.TermAs[Fun[Nat, Real]]("λi:num. t ^ (n + 1)"),
										b.TermAs[Fun[Nat, Real]]("λi:num. t ^ i")),
									real_sum.IntervalConst.At(b.TermAs[Real]("t ^ (n + 1)"), n, zero)))
							cleared := b.Have(
								"times the positive 1 − t, the geometric sum is 1 − tⁿ⁺¹",
								"&0 < &(n + 1) * (&1 - t) ∧ &(n + 1) * (&1 - t) * t ^ (n + 1) ≤ &1 - t ^ (n + 1)",
								ByArith(sumAbove, positiveDenominators, real_series.GeometricPartialSum.At(t, n)))
							quotient := b.Have(
								"divide by the positive 1 − tⁿ⁺¹",
								"t ^ (n + 1) * (&(n + 1) * (&1 - t)) / (&1 - t ^ (n + 1)) ≤ &1",
								ByArith(
									cleared,
									positiveDenominators,
									real_order_field.LessEqDivMulRight.At(
										b.TermAs[Real]("t ^ (n + 1) * (&(n + 1) * (&1 - t))"),
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("&1 - t ^ (n + 1)"))))
							regrouped := b.Have(
								"that is tⁿ⁺¹/(1 − tⁿ⁺¹) times (n + 1)(1 − t)",
								"t ^ (n + 1) / (&1 - t ^ (n + 1)) * (&(n + 1) * (&1 - t)) ≤ &1",
								ByArith(
									quotient,
									real_field.RealDivDef.At(
										b.TermAs[Real]("t ^ (n + 1) * (&(n + 1) * (&1 - t))"),
										b.TermAs[Real]("&1 - t ^ (n + 1)")),
									real_field.RealDivDef.At(b.TermAs[Real]("t ^ (n + 1)"), b.TermAs[Real]("&1 - t ^ (n + 1)"))))
							b.Show(
								"so tⁿ⁺¹/(1 − tⁿ⁺¹) is at most 1/((n + 1)(1 − t))",
								ByArith(
									regrouped,
									cleared,
									real_order_field.LessEqDivMulLeft.At(
										b.TermAs[Real]("t ^ (n + 1) / (&1 - t ^ (n + 1))"),
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("&(n + 1) * (&1 - t)"))))
						})),
					Case(
						"the weights decrease: cleared of its denominators, "+
							"the drop is (1 − tⁿ)(1 − tⁿ⁺¹) − n(n + 1)(1 − t)²tⁿ ≥ 0",
						Derive(func(b *Argument) {
							predecessor := b.Have(
								"n is the successor of its predecessor",
								"n - 1 + 1 = n",
								ByArith(positive))
							one := b.TermAs[Nat]("1")
							denominator := b.TermAs[Real]("«denominator»")
							factorSigns := b.Have(
								"1 − t, 1 − tⁿ, 1 − tⁿ⁺¹, n(1 − t), (n + 1)(1 − t), "+
									"n and n + 1 are positive, tⁿ and tⁿ⁺¹ being at most t",
								"&0 < &1 - t ∧ "+
									"&0 < &1 - t ^ n ∧ "+
									"&0 < &1 - t ^ (n + 1) ∧ "+
									"&0 < &n * (&1 - t) ∧ "+
									"&0 < &(n + 1) * (&1 - t) ∧ "+
									"&0 < &n ∧ "+
									"&0 < &(n + 1)",
								ByArith(
									nonnegative,
									belowOne,
									positive,
									real_pow.PowMonoExpBelowOne.At(t, one, n),
									real_pow.PowMonoExpBelowOne.At(t, one, b.TermAs[Nat]("n + 1")),
									real_pow.PowOne.At(t)))
							positiveDenominator := b.Have(
								"so is the common denominator, the product of n, n + 1, 1 − t, 1 − tⁿ and 1 − tⁿ⁺¹",
								"&0 < «denominator»",
								By(
									factorSigns,
									real_order_ring.MulPos.At(b.TermAs[Real]("&n"), b.TermAs[Real]("&(n + 1)")),
									real_order_ring.MulPos.At(b.TermAs[Real]("&n * &(n + 1)"), b.TermAs[Real]("&1 - t")),
									real_order_ring.MulPos.At(b.TermAs[Real]("&n * &(n + 1) * (&1 - t)"), b.TermAs[Real]("&1 - t ^ n")),
									real_order_ring.MulPos.At(
										b.TermAs[Real]("&n * &(n + 1) * (&1 - t) * (&1 - t ^ n)"),
										b.TermAs[Real]("&1 - t ^ (n + 1)"))))
							geometricSums := b.Have(
								"times 1 − t, the two geometric sums are 1 − tⁿ and 1 − tⁿ⁺¹",
								"(&1 - t) * (Σ_{k∈0 .. n - 1} t ^ k) = &1 - t ^ n ∧ "+
									"(&1 - t) * (Σ_{k∈0 .. n} t ^ k) = &1 - t ^ (n + 1)",
								By(
									predecessor,
									real_series.GeometricPartialSum.At(t, b.TermAs[Nat]("n - 1")),
									real_series.GeometricPartialSum.At(t, n)))
							regrouped := b.Have(
								"(1 − t)² splits between the two sums",
								"(&1 - t) ^ 2 * ((Σ_{k∈0 .. n - 1} t ^ k) * Σ_{k∈0 .. n} t ^ k) = "+
									"(&1 - t) * (Σ_{k∈0 .. n - 1} t ^ k) * ((&1 - t) * Σ_{k∈0 .. n} t ^ k)",
								Simp(Fwd(real_pow.PowTwo)),
								ByArith())
							squaredProduct := b.Have(
								"so (1 − t)² times the product of the sums is (1 − tⁿ)(1 − tⁿ⁺¹)",
								"(&1 - t) ^ 2 * ((Σ_{k∈0 .. n - 1} t ^ k) * Σ_{k∈0 .. n} t ^ k) = "+
									"(&1 - t ^ n) * (&1 - t ^ (n + 1))",
								By(regrouped, geometricSums))
							scaledBound := b.Have(
								"times (1 − t)², the product bound reads n(n + 1)(1 − t)²tⁿ ≤ (1 − tⁿ)(1 − tⁿ⁺¹)",
								"&n * &(n + 1) * (&1 - t) ^ 2 * t ^ n ≤ (&1 - t ^ n) * (&1 - t ^ (n + 1))",
								Derive(func(c *Argument) {
									square := c.Have(
										"the square (1 − t)² is nonnegative",
										"&0 ≤ (&1 - t) ^ 2",
										ByArith(factorSigns, real_pow.PowNonneg.At(c.TermAs[Real]("&1 - t"), c.TermAs[Nat]("2"))))
									scaled := c.Have(
										"multiplying by it preserves the product bound",
										"&n * &(n + 1) * t ^ n * (&1 - t) ^ 2 ≤ "+
											"(Σ_{k∈0 .. n - 1} t ^ k) * (Σ_{k∈0 .. n} t ^ k) * (&1 - t) ^ 2",
										By(
											square,
											nonnegative,
											belowOne,
											positive,
											At(rectangleBound, t, n),
											real_order_ring.LessEqMulRight.At(
												c.TermAs[Real]("&n * &(n + 1) * t ^ n"),
												c.TermAs[Real]("(Σ_{k∈0 .. n - 1} t ^ k) * Σ_{k∈0 .. n} t ^ k"),
												c.TermAs[Real]("(&1 - t) ^ 2"))))
									c.Show(
										"and (1 − t)² times the product of the sums is (1 − tⁿ)(1 − tⁿ⁺¹)",
										ByArith(squaredProduct, scaled))
								}))
							cancel := b.Have(
								"a factor cancels against its own denominator",
								"∀u v w:real. &0 < v ⇒ w * v * (u / v) = w * u",
								Derive(func(c *Argument) {
									u := c.FixAs[Real]("u")
									v := c.FixAs[Real]("v")
									c.FixAs[Real]("w")
									positiveV := c.Assume()
									cancelled := c.Have(
										"a quotient times its divisor is the dividend",
										"u / v * v = u",
										By(positiveV, real_order_field.EqDivMulLeft.At(c.TermAs[Real]("u / v"), u, v)))
									rearranged := c.Have(
										"bring the divisor beside the quotient",
										"w * v * (u / v) = w * (u / v * v)",
										ByArith())
									c.Show(
										"so the product is w times u",
										By(Normalized, cancelled, rearranged))
								}))
							factored := b.Have(
								"each of n(1 − t), (n + 1)(1 − t) and 1 − tⁿ is a factor of the common denominator",
								"«denominator» = &(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1)) * (&n * (&1 - t)) ∧ "+
									"«denominator» = &n * (&1 - t ^ n) * (&1 - t ^ (n + 1)) * (&(n + 1) * (&1 - t)) ∧ "+
									"«denominator» = &n * &(n + 1) * (&1 - t) * (&1 - t ^ (n + 1)) * (&1 - t ^ n)",
								ByArith())
							scaledTerms := b.Have(
								"the common denominator times each of the four fractions of the two weights",
								"«denominator» * (&1 / (&n * (&1 - t))) = &(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1)) * &1 ∧ "+
									"«denominator» * (&1 / (&(n + 1) * (&1 - t))) = &n * (&1 - t ^ n) * (&1 - t ^ (n + 1)) * &1 ∧ "+
									"«denominator» * (t ^ n / (&1 - t ^ n)) = "+
									"&n * &(n + 1) * (&1 - t) * (&1 - t ^ (n + 1)) * t ^ n ∧ "+
									"«denominator» * (t ^ (n + 1) / (&1 - t ^ (n + 1))) = "+
									"&n * &(n + 1) * (&1 - t) * (&1 - t ^ n) * t ^ (n + 1)",
								By(
									factorSigns,
									factored,
									cancel.At(
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("&n * (&1 - t)"),
										b.TermAs[Real]("&(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1))")),
									cancel.At(
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("&(n + 1) * (&1 - t)"),
										b.TermAs[Real]("&n * (&1 - t ^ n) * (&1 - t ^ (n + 1))")),
									cancel.At(
										b.TermAs[Real]("t ^ n"),
										b.TermAs[Real]("&1 - t ^ n"),
										b.TermAs[Real]("&n * &(n + 1) * (&1 - t) * (&1 - t ^ (n + 1))")),
									cancel.At(
										b.TermAs[Real]("t ^ (n + 1)"),
										b.TermAs[Real]("&1 - t ^ (n + 1)"),
										b.TermAs[Real]("&n * &(n + 1) * (&1 - t) * (&1 - t ^ n)"))))
							scaledDrop := b.Have(
								"cleared of denominators, the drop is (1 − tⁿ)(1 − tⁿ⁺¹) − n(n + 1)(1 − t)²tⁿ",
								"«denominator» * («weight»(n, t) - «weight»(n + 1, t)) = "+
									"(&1 - t ^ n) * (&1 - t ^ (n + 1)) - &n * &(n + 1) * (&1 - t) ^ 2 * t ^ n",
								Simp(Fwd(real_pow.PowTwo)),
								Derive(func(c *Argument) {
									distribute := c.Have(
										"a factor distributes over a difference of differences",
										"∀d x y u v:real. d * (x - y - (u - v)) = d * x - d * y - (d * u - d * v)",
										Derive(func(d *Argument) {
											d.FixAs[Real]("d")
											d.FixAs[Real]("x")
											d.FixAs[Real]("y")
											d.FixAs[Real]("u")
											d.FixAs[Real]("v")
											d.Show(
												"multiply out",
												ByArith())
										}))
									substituted := c.Have(
										"distribute the common denominator over the weights and substitute the four scaled fractions",
										"«denominator» * («weight»(n, t) - «weight»(n + 1, t)) = "+
											"&(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1)) - "+
											"&n * &(n + 1) * (&1 - t) * (&1 - t ^ (n + 1)) * t ^ n - "+
											"(&n * (&1 - t ^ n) * (&1 - t ^ (n + 1)) - &n * &(n + 1) * (&1 - t) * (&1 - t ^ n) * t ^ (n + 1))",
										By(
											scaledTerms,
											distribute.At(
												denominator,
												c.TermAs[Real]("&1 / (&n * (&1 - t))"),
												c.TermAs[Real]("t ^ n / (&1 - t ^ n)"),
												c.TermAs[Real]("&1 / (&(n + 1) * (&1 - t))"),
												c.TermAs[Real]("t ^ (n + 1) / (&1 - t ^ (n + 1))")),
											real_ring.MulRightId.At(c.TermAs[Real]("&(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1))")),
											real_ring.MulRightId.At(c.TermAs[Real]("&n * (&1 - t ^ n) * (&1 - t ^ (n + 1))"))))
									collected := c.Have(
										"collect the two multiples of (1 − tⁿ)(1 − tⁿ⁺¹) and the two power terms",
										"&(n + 1) * (&1 - t ^ n) * (&1 - t ^ (n + 1)) - "+
											"&n * &(n + 1) * (&1 - t) * (&1 - t ^ (n + 1)) * t ^ n - "+
											"(&n * (&1 - t ^ n) * (&1 - t ^ (n + 1)) - "+
											"    &n * &(n + 1) * (&1 - t) * (&1 - t ^ n) * t ^ (n + 1)) = "+
											"(&1 - t ^ n) * (&1 - t ^ (n + 1)) + "+
											"&n * &(n + 1) * (&1 - t) * (t ^ (n + 1) * (&1 - t ^ n) - t ^ n * (&1 - t ^ (n + 1)))",
										ByArith())
									powerDifference := c.Have(
										"the power terms combine to tⁿ⁺¹ − tⁿ = −(1 − t)tⁿ",
										"t ^ (n + 1) * (&1 - t ^ n) - t ^ n * (&1 - t ^ (n + 1)) = (&0 - (&1 - t)) * t ^ n",
										ByArith(real_pow.PowAddOne.At(t, n)))
									assembled := c.Have(
										"so they contribute −n(n + 1)(1 − t)²tⁿ",
										"(&1 - t ^ n) * (&1 - t ^ (n + 1)) + &n * &(n + 1) * (&1 - t) * ((&0 - (&1 - t)) * t ^ n) = "+
											"(&1 - t ^ n) * (&1 - t ^ (n + 1)) - &n * &(n + 1) * ((&1 - t) * (&1 - t)) * t ^ n",
										ByArith())
									c.Show(
										"chain the four equations",
										By(assembled, substituted, powerDifference, collected))
								}))
							scaledNonnegative := b.Have(
								"by the bound times (1 − t)², the cleared drop is nonnegative",
								"«denominator» * &0 ≤ «denominator» * («weight»(n, t) - «weight»(n + 1, t))",
								By(
									scaledDrop,
									scaledBound,
									real_order_ring.SubNonneg.At(
										b.TermAs[Real]("(&1 - t ^ n) * (&1 - t ^ (n + 1))"),
										b.TermAs[Real]("&n * &(n + 1) * (&1 - t) ^ 2 * t ^ n")),
									real_ring.MulRightZero.At(denominator)))
							b.Show(
								"cancel the positive common denominator",
								By(
									scaledNonnegative,
									positiveDenominator,
									real_order_ring.LessEqCancelMulLeft.At(
										denominator,
										b.TermAs[Real]("&0"),
										b.TermAs[Real]("«weight»(n, t) - «weight»(n + 1, t)")),
									real_order_ring.SubNonneg.At(
										b.TermAs[Real]("«weight»(n, t)"), b.TermAs[Real]("«weight»(n + 1, t)"))))
						}))))
		})
	}),
})}

// MonskyBound — if the L-series of a non-principal character χ mod q vanished
// at 1, then for 0 ≤ t < 1 the power series Σ_{n≥1} c(n)·tⁿ of the divisor
// sums c(n) = Σ_{d∣n} re χ(d) would be bounded by φ(q): its sum S has
// |S| ≤ φ(q).
//
// The series sums to the Lambert series Σ re χ(n)·tⁿ/(1 − tⁿ). The vanishing
// L-series makes the harmonic series Σ re χ(n)/n sum to zero, and that series
// divided by 1 − t, less the Lambert series, is Σ re χ(n)·w(n, t) = −S, with
// the weights w(n, t) = 1/(n(1 − t)) − tⁿ/(1 − tⁿ) decreasing from
// w(1, t) = 1. The partial sums of re χ are at most φ(q) in size, so Abel's
// inequality bounds each partial sum Σ_{k≤N} re χ(k)·w(k, t): the endpoint
// is at most w(N + 1, t)·φ(q), the telescoped drops give
// φ(q)(1 − w(N + 1, t)), and together they are at most φ(q). The bound
// passes to the limit −S.
var MonskyBound = monskyBoundThm{family.Add(registry.ProofEntry{
	Name: "MonskyBound",
	Key:  "prop_161174f4778a89fa",
	Reading: "The hypothesis is false: no non-principal character has an L-series vanishing at 1, " +
		"and this member is a step of the contradiction that shows it for a real character, whose " +
		"divisor sums are nonnegative and make the series unbounded as t → 1⁻. The divisor sums are " +
		"read through the real parts of the character's values, so no real-valued hypothesis is needed.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex). ∀t S:real.",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
			"dirichlet_series(χ, complex_of_real(&1)) = &0",
			"&0 ≤ t",
			"t < &1",
			"real_sums(λn:num. «divisorSum»(χ, n + 1) * t ^ (n + 1), S)",
		},
		Conclusion: "|S| ≤ &(totient(q))",
	},
		func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			t, S *Expr[Real],
			character, qPositive, nonprincipal, vanishes, nonnegative, belowOne, total Fact,
		) {
			one := a.TermAs[Nat]("1")
			zero := a.TermAs[Nat]("0")
			atOne := a.TermAs[Complex]("complex_of_real(&1)")
			totient := a.TermAs[Real]("&totient(q)")
			v, converges := a.ObtainAs[Complex](
				"the L-series of the non-principal character converges at s = 1",
				"∃v:complex. dirichlet_sums(χ, &1, v)",
				ByArith(
					character,
					qPositive,
					nonprincipal,
					complex_field.PartsOfReal.At(a.TermAs[Real]("&1")),
					LSeriesConverges.At(q, χ, atOne)))
			realParts := a.Have(
				"its sum is its value, zero, so the real parts of its terms χ(n)·n⁻¹ sum to zero",
				"real_sums(λn:num. re(χ(n + 1) * complex_cpow(&(n + 1), -&1)), &0)",
				By(
					vanishes,
					converges,
					dirichlet_series.DirichletSeriesValue.At(χ, atOne, v),
					dirichlet_series.DirichletSumsDef.At(χ, atOne, a.TermAs[Complex]("complex_of_real(&0)")),
					complex_series.ComplexSumsDef.At(
						a.TermAs[Fun[Nat, Complex]]("λn:num. χ(n + 1) * complex_cpow(&(n + 1), -&1)"),
						a.TermAs[Complex]("complex_of_real(&0)")),
					complex_field.PartsOfReal.At(a.TermAs[Real]("&0"))))
			harmonicTerm := a.Have(
				"n⁻¹ is real, so the real part of χ(n)·n⁻¹ is re χ(n)/n",
				"∀n:num. re(χ(n + 1) * complex_cpow(&(n + 1), -&1)) = re(χ(n + 1)) / &(n + 1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					succ := b.TermAs[Nat]("n + 1")
					base := b.TermAs[Real]("&(n + 1)")
					positiveBase := b.Have(
						"n + 1 is a positive real",
						"&0 < &(n + 1) ∧ &0 ≤ &(n + 1)",
						ByArith())
					powerInverse := b.Have(
						"a positive real to the power −1 is its inverse",
						"complex_cpow(&(n + 1), -&1) = &real_inv(&(n + 1))",
						By(
							positiveBase,
							complex_cpow.CpowRealExponent.At(base, b.TermAs[Real]("-&1")),
							complex_field.OfRealNeg.At(b.TermAs[Real]("&1")),
							real_rpow.RpowNeg.At(base, b.TermAs[Real]("&1")),
							real_rpow.RpowOneExponent.At(base)))
					b.Show(
						"the real part of a complex number times a real one is the real part times it",
						ByArith(
							powerInverse,
							complex_field.PartsMul.At(χ.Apply(succ), b.TermAs[Complex]("complex_of_real(real_inv(&(n + 1)))")),
							complex_field.PartsOfReal.At(b.TermAs[Real]("real_inv(&(n + 1))")),
							real_field.RealDivDef.At(b.TermAs[Real]("re(χ(n + 1))"), base)))
				}))
			harmonic := a.Have(
				"the harmonic series Σ re χ(n)/n sums to zero",
				"real_sums(λn:num. re(χ(n + 1)) / &(n + 1), &0)",
				By(harmonicTerm, realParts))
			realPartBound := realPartsBounded(a, q, χ, character, qPositive)
			T, lambert := a.ObtainAs[Real](
				"the Lambert series Σ re χ(n)·tⁿ/(1 − tⁿ) and the divisor-sum series have a common sum",
				"∃T:real. "+
					"    real_sums(λn:num. re(χ(n + 1)) * t ^ (n + 1) / (&1 - t ^ (n + 1)), T) ∧ "+
					"    real_sums(λn:num. «divisorSum»(χ, n + 1) * t ^ (n + 1), T)",
				By(
					realPartBound,
					nonnegative,
					belowOne,
					real_power_series.LambertExpansion.At(a.TermAs[Fun[Nat, Real]]("λn:num. re(χ(n))"), t)))
			lambertSum := a.Have(
				"a series has one sum, so the Lambert series sums to S",
				"real_sums(λn:num. re(χ(n + 1)) * t ^ (n + 1) / (&1 - t ^ (n + 1)), S)",
				By(
					lambert,
					total,
					real_series.SumsUnique.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. «divisorSum»(χ, n + 1) * t ^ (n + 1)"), T, S)))
			inverse := a.TermAs[Real]("real_inv(&1 - t)")
			difference := a.Have(
				"the harmonic series divided by 1 − t, less the Lambert series, sums to 0 − S",
				"real_sums(λn:num. "+
					"        real_inv(&1 - t) * (re(χ(n + 1)) / &(n + 1)) - "+
					"        re(χ(n + 1)) * t ^ (n + 1) / (&1 - t ^ (n + 1)), "+
					"    &0 - S)",
				By(
					harmonic,
					lambertSum,
					real_series.SumsScale.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. re(χ(n + 1)) / &(n + 1)"),
						a.TermAs[Real]("&0"),
						inverse),
					real_ring.MulRightZero.At(inverse),
					real_series.SumsSub.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. real_inv(&1 - t) * (re(χ(n + 1)) / &(n + 1))"),
						a.TermAs[Fun[Nat, Real]]("λn:num. re(χ(n + 1)) * t ^ (n + 1) / (&1 - t ^ (n + 1))"),
						a.TermAs[Real]("&0"),
						S)))
			weightIdentity := a.Have(
				"term by term the difference is re χ(n) times the weight w(n, t)",
				"∀n:num. "+
					"    real_inv(&1 - t) * (re(χ(n + 1)) / &(n + 1)) - "+
					"    re(χ(n + 1)) * t ^ (n + 1) / (&1 - t ^ (n + 1)) = "+
					"    re(χ(n + 1)) * «weight»(n + 1, t)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"write each quotient as a product with an inverse, and collect",
						Simp(Fwd(real_field.RealDivDef), Fwd(field.InvMul.Read(real_field.Field))),
						ByArith())
				}))
			weighted := a.Have(
				"so the weighted series Σ re χ(n)·w(n, t) sums to −S",
				"real_sums(λn:num. re(χ(n + 1)) * «weight»(n + 1, t), &0 - S)",
				By(weightIdentity, difference))
			characterBound := a.Have(
				"the partial sums of re χ are at most φ(q) in size",
				"∀N:num. |Σ_{k∈1 .. N} re(χ(k))| ≤ &totient(q)",
				Derive(func(b *Argument) {
					N := b.FixAs[Nat]("N")
					b.Show(
						"the character's partial sums are, and a real part is at most the modulus",
						ByArith(
							character,
							qPositive,
							nonprincipal,
							dirichlet_character.CharacterPartialSumsBounded.At(q, N, χ),
							num_segment.Finite.At(one, N),
							complex_series.SumParts.At(b.TermAs[Set[Nat]]("1 .. N"), χ),
							complex_abs.ReLessEqAbs.At(b.TermAs[Complex]("Σ_{i∈1 .. N} χ(i)"))))
				}))
			characterValues := a.TermAs[Fun[Nat, Real]]("λk:num. re(χ(k))")
			weights := a.TermAs[Fun[Nat, Real]]("λk:num. «weight»(k, t)")
			summands := a.TermAs[Fun[Nat, Real]]("λk:num. re(χ(k)) * «weight»(k, t)")
			abel := a.Have(
				"by Abel's inequality each Σ_{k∈1 .. N} re χ(k)·w(k, t) is at most φ(q)·w(1, t) = φ(q) in size",
				"∀N:num. 0 < N ⇒ |Σ_{k∈1 .. N} re(χ(k)) * «weight»(k, t)| ≤ &totient(q)",
				Derive(func(b *Argument) {
					N := b.FixAs[Nat]("N")
					positive := b.Assume()
					ends := b.Have(
						"w(1, t) = 1, and w(N + 1, t) is nonnegative",
						"«weight»(1, t) = &1 ∧ &0 ≤ «weight»(N + 1, t)",
						By(positive, nonnegative, belowOne, MonskyWeights.At(t, N)))
					decreasing := b.Have(
						"the weights decrease from w(1, t) to w(N + 1, t)",
						"∀k:num. 1 ≤ k ∧ k ≤ N ⇒ «weight»(k + 1, t) ≤ «weight»(k, t)",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							inRange := c.Assume()
							c.Show(
								"the weights drop at every positive index",
								ByArith(inRange, nonnegative, belowOne, MonskyWeights.At(t, k)))
						}))
					b.Show(
						"Abel's inequality at the bound φ(q) on the partial sums of re χ",
						By(
							Normalized,
							positive,
							characterBound,
							decreasing,
							ends,
							real_sum.AbelInequality.At(N, characterValues, weights, totient),
							real_ring.MulRightId.At(totient)))
				}))
			partialSums := a.TermAs[Fun[Nat, Real]]("λN:num. Σ_{n∈0 .. N} re(χ(n + 1)) * «weight»(n + 1, t)")
			partialBounds := a.Have(
				"each partial sum of the weighted series lies between −φ(q) and φ(q)",
				"∀N:num. "+
					"    -&totient(q) ≤ Σ_{n∈0 .. N} re(χ(n + 1)) * «weight»(n + 1, t) ∧ "+
					"    Σ_{n∈0 .. N} re(χ(n + 1)) * «weight»(n + 1, t) ≤ &totient(q)",
				Derive(func(b *Argument) {
					N := b.FixAs[Nat]("N")
					shift := b.Have(
						"N + 1 is positive, and the shift by one starts the sum at 1",
						"0 < N + 1 ∧ 0 + 1 = 1",
						ByArith())
					b.Show(
						"the partial sum to N is the sum over 1 .. N + 1, its index shifted by one",
						By(
							shift,
							abel.At(b.TermAs[Nat]("N + 1")),
							real_sum.Shift.At(zero, N, one, summands),
							real_sgn_abs.AbsBounds.At(
								b.TermAs[Real]("Σ_{n∈0 .. N} re(χ(n + 1)) * «weight»(n + 1, t)"), totient)))
				}))
			negated := a.TermAs[Real]("&0 - S")
			limitBounds := a.Have(
				"the partial sums tend to −S, and their bounds hold at the limit",
				"-&totient(q) ≤ &0 - S ∧ &0 - S ≤ &totient(q)",
				By(
					partialBounds,
					weighted,
					real_series.RealSumsDef.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. re(χ(n + 1)) * «weight»(n + 1, t)"), negated),
					real_sequences.BoundLessEqLimit.At(partialSums, negated, a.TermAs[Real]("-&totient(q)")),
					real_sequences.LimitLessEqBound.At(partialSums, negated, totient)))
			a.Show(
				"−S lies between −φ(q) and φ(q), so |S| ≤ φ(q)",
				ByArith(limitBounds, real_sgn_abs.AbsBounds.At(S, totient)))
		}),
})}

// LSeriesNonzeroAtOneReal — the L-series of a real non-principal character
// does not vanish at 1.
var LSeriesNonzeroAtOneReal = lSeriesNonzeroAtOneRealThm{family.Add(registry.ProofEntry{
	Name: "LSeriesNonzeroAtOneReal",
	Key:  "prop_ce8d2eafa31ee502",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀n:num. im(χ(n)) = &0",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
		},
		Conclusion: "dirichlet_series(χ, complex_of_real(&1)) ≠ &0",
		Abbrev: Abbrev{
			{Name: "weightedTerm", Text: "λt:real. λj:num. «divisorSum»(χ, j) * t ^ j"},
			{Name: "squareIndices", Text: "λM:num. image(λm:num. m * m, 1 .. M)"},
			{Name: "partialRange", Text: "λM:num. 1 .. (M * M + 1)"},
		},
	},
		func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			character, qPositive, realValues, nonprincipal Fact,
		) {
			vanishes := a.SupposeNot()
			bound := a.TermAs[Real]("&totient(q) + &1")
			t, M, squareBound := a.Unpack2As[Real, Nat](real_series.SquarePowersUnbounded.At(bound), "t", "M")
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("1")
			last := a.TermAs[Nat]("M * M")
			shiftedLast := a.TermAs[Nat]("M * M + 1")
			squareMap := a.TermAs[Fun[Nat, Nat]]("λm:num. m * m")
			rootRange := a.TermAs[Set[Nat]]("1 .. M")
			squares := a.TermAs[Set[Nat]]("«squareIndices»(M)")
			partialRange := a.TermAs[Set[Nat]]("«partialRange»(M)")
			terms := a.TermAs[Fun[Nat, Real]]("λj:num. «weightedTerm»(t, j)")
			shiftedTerms := a.TermAs[Fun[Nat, Real]]("λn:num. «weightedTerm»(t, n + 1)")
			squarePowers := a.TermAs[Fun[Nat, Real]]("λm:num. t ^ (m * m)")
			squareTerms := a.TermAs[Fun[Nat, Real]]("λm:num. «weightedTerm»(t, m * m)")
			realPartBound := realPartsBounded(a, q, χ, character, qPositive)
			S, total := a.ObtainAs[Real](
				"the Lambert expansion supplies the sum of the divisor-sum series",
				"∃S:real. real_sums(λn:num. «weightedTerm»(t, n + 1), S)",
				By(
					realPartBound,
					squareBound,
					real_power_series.LambertExpansion.At(a.TermAs[Fun[Nat, Real]]("λn:num. re(χ(n))"), t)))
			upper := a.Have(
				"Monsky's bound limits the absolute value of the sum",
				"|S| ≤ &totient(q)",
				By(character, qPositive, nonprincipal, vanishes, squareBound, total, MonskyBound.At(q, χ, t, S)))
			nonnegative := a.Have(
				"the character divisor sums and the powers of t give nonnegative terms",
				"∀j:num. 0 < j ⇒ &0 ≤ «weightedTerm»(t, j)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					positive := b.Assume()
					b.Do(ByArith(
						character,
						qPositive,
						realValues,
						positive,
						squareBound,
						CharacterDivisorSumNonneg.At(q, j, χ),
						real_pow.PowNonneg.At(t, j)))
				}))
			squareSubset := a.Have(
				"the squares of the positive indices up to M lie in the shifted partial range",
				"«squareIndices»(M) ⊆ «partialRange»(M)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(num_segment.IntervalDef), Fwd(set_image.ImageSubsetIff)))
					m := b.FixAs[Nat]("m")
					inRange := b.Assume()
					b.Do(ByArith(inRange, nat_order.LessEqMul2.At(m, M, m, M), nat_arith.MulEqZero.At(m, m)))
				}))
			injective := a.Have(
				"squaring is injective on the positive indices",
				"injective_on(1 .. M, λm:num. m * m)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(num_segment.IntervalDef), Fwd(functions.InjectiveOnDef)))
					i := b.FixAs[Nat]("i")
					j := b.FixAs[Nat]("j")
					equalSquares := b.Assume()
					b.Do(ByArith(
						equalSquares,
						nat_order.LessEqMulMono.At(i, i, j),
						nat_order.LessThanMulCancel.At(j, i, j),
						nat_order.LessEqMulMono.At(j, j, i),
						nat_order.LessThanMulCancel.At(i, j, i)))
				}))
			atSquares := a.Have(
				"at a square the coefficient is at least 1",
				"∀m:num. 1 ≤ m ∧ m ≤ M ⇒ t ^ (m * m) ≤ «weightedTerm»(t, m * m)",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					inRange := b.Assume()
					positive := b.Have(
						"the square index comes from a positive integer",
						"0 < m",
						ByArith(inRange))
					b.Do(ByArith(
						positive,
						qPositive,
						character,
						realValues,
						squareBound,
						CharacterDivisorSumSquareAtLeastOne.At(q, m, χ),
						real_pow.PowNonneg.At(t, b.TermAs[Nat]("m * m"))))
				}))
			omitted := a.Have(
				"the terms added when extending the sum beyond the squares are nonnegative",
				"∀j:num. j ∈ «partialRange»(M) ∖ «squareIndices»(M) ⇒ &0 ≤ «weightedTerm»(t, j)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					inDifference := b.Assume()
					positive := b.Have(
						"the shifted partial range starts at 1",
						"0 < j",
						ByArith(
							inDifference,
							set_basic.InDiff.At(partialRange, squares, j),
							num_segment.IntervalDef.At(one, shiftedLast)))
					b.Do(By(positive, nonnegative.At(j)))
				}))
			shiftedNonnegative := a.Have(
				"the zero-indexed series uses only positive exponents",
				"∀n:num. &0 ≤ «weightedTerm»(t, n + 1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Do(ByArith(nonnegative.At(b.TermAs[Nat]("n + 1"))))
				}))
			lower := a.CalcLeibniz(real_order_ring.OrderCalc(a.Ctx()), bound,
				LeLeg(
					a.TermAs[Real]("Σ_{m∈1 .. M} t ^ (m * m)"),
					"the chosen square sum exceeds the totient",
					By(squareBound)),
				LeLeg(
					a.TermAs[Real]("Σ_{m∈1 .. M} «weightedTerm»(t, m * m)"),
					"multiply the square powers by their divisor-sum coefficients",
					By(atSquares, real_sum.IntervalMonotone.At(one, M, squarePowers, squareTerms))),
				EqLeg(
					a.TermAs[Real]("Σ_{j∈«squareIndices»(M)} «weightedTerm»(t, j)"),
					"reindex the weighted terms by the distinct squares",
					By(
						injective,
						real_sum.Image.At(rootRange, squareMap, terms),
						functions.ComposeApply.At(terms, squareMap))),
				LeLeg(
					a.TermAs[Real]("Σ_{j∈«partialRange»(M)} «weightedTerm»(t, j)"),
					"adding the remaining nonnegative terms can only increase the sum",
					By(
						squareSubset,
						omitted,
						num_segment.Finite.At(one, shiftedLast),
						real_sum.Subset.At(squares, partialRange, terms))),
				EqLeg(
					a.TermAs[Real]("Σ_{n∈0 .. M * M} «weightedTerm»(t, n + 1)"),
					"shift the partial sum back to its zero-indexed form",
					ByArith(real_sum.Shift.At(zero, last, one, terms))),
				LeLeg(
					S,
					"the partial sum is bounded by the convergent sum",
					By(shiftedNonnegative, total, real_series.SumsPartialLessEq.At(shiftedTerms, S, last))))
			a.Show(
				"the sum exceeds the totient, contradicting the upper bound on its absolute value",
				ByArith(lower, upper, real_sgn_abs.AbsDominates.At(S)))
		}),
})}
