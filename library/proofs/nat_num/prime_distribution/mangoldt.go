// mangoldt.go — the von Mangoldt function Λ and Chebyshev's ψ: Λ at prime
// powers, the convergent series of Λ(n)/n over the prime powers p^e with
// e ≥ 2, the divisor sum Σ_{d∣n} Λ(d) = log n, and ψ against π.

package prime_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimePowerChosenBase — the prime divisor selected from a positive
// prime power is its base, since every prime divisor equals that base.
var PrimePowerChosenBase = primePowerChosenBaseThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerChosenBase",
	Key:  "prop_6dde709d51e4cb23",
	Build: family.Theorem(Statement{
		Binders: "∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < k",
		},
		Conclusion: "«primeBase»(p ^ k) = p",
		Abbrev: Abbrev{
			{Name: "hasPrimeDivisor", Text: "∃q:num. nat_prime(q) ∧ q ∣ p ^ k"},
		},
	}, func(a *Argument, p, k *Expr[Nat], prime, positive Fact) {
		exists := a.Have(
			"the base is a prime divisor of its positive power",
			"«hasPrimeDivisor»",
			Witness(p),
			By(
				prime,
				positive,
				nat_monus.MulPowSubOne.At(p, k),
				nat_divides.DividesOwnMultiple.At(p, a.TermAs[Nat]("p ^ (k - 1)"))))
		chosen, divides := a.ObtainChosen(
			"the selected prime divides the power",
			"«hasPrimeDivisor»",
			exists)
		a.Show(
			"the selected prime divides the prime base and thus equals it",
			By(
				prime,
				divides,
				At(nat_prime.PrimeDividesPower, chosen, p, k),
				At(nat_prime.PrimeDividesPrime, chosen, p)))
	}),
})}

// MangoldtPrimePower — Λ(pᵏ) = log p for a prime p and k > 0.
var MangoldtPrimePower = mangoldtPrimePowerThm{family.Add(registry.ProofEntry{
	Name: "MangoldtPrimePower",
	Key:  "prop_b4f444f36ec55525",
	Build: family.Theorem(Statement{
		Binders: "∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < k",
		},
		Conclusion: "von_mangoldt(p ^ k) = log(&p)",
	},
		func(a *Argument, p, k *Expr[Nat], prime, positive Fact) {
			primePower := a.Have(
				"the input is a positive power of a prime",
				"«isPrimePower»(p ^ k)",
				Witness(p),
				Witness(k),
				By(prime, positive))
			a.Show(
				"the prime-power branch gives log of the chosen prime divisor, which is p",
				Unfold(VonMangoldtDef),
				By(primePower, prime, positive, PrimePowerChosenBase.At(p, k)))
		}),
})}

// MangoldtNonneg — Λ is nonnegative. On positive prime powers it is
// the logarithm of the prime base. Elsewhere it is zero.
var MangoldtNonneg = mangoldtNonnegThm{family.Add(registry.ProofEntry{
	Name: "MangoldtNonneg",
	Key:  "prop_1ae3350b6ccd4298",
	Build: family.Theorem("∀n:num. &0 ≤ von_mangoldt(n)",
		func(a *Argument, n *Expr[Nat]) {
			primePower := a.Assuming(
				a.TermAs[Bool]("«isPrimePower»(n)"),
				"away from positive prime powers Λ vanishes",
				Simp(Fwd(VonMangoldtDef)),
				Cite(real_order_ring.LessEqRefl))
			p, k, power := a.Unpack2As[Nat, Nat](primePower)
			parts := a.Conjuncts(
				power,
				"prime base",
				"positive exponent",
				"prime-power representation")
			prime, positive, representation := parts[0], parts[1], parts[2]

			logNonneg := a.Have(
				"log increases from zero at 1, and a prime is at least 2",
				"&0 ≤ log(&p)",
				ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p), real_exp_log.LogNonneg.At(a.TermAs[Real]("&p"))))
			a.Show(
				"Λ at this prime power is log p",
				By(Normalized, prime, positive, representation, logNonneg, MangoldtPrimePower.At(p, k)))
		}),
})}

// MangoldtLessEqLog — on positive integers, Λ is bounded above by the
// logarithm. A positive power of a prime is at least its base.
var MangoldtLessEqLog = mangoldtLessEqLogThm{family.Add(registry.ProofEntry{
	Name: "MangoldtLessEqLog",
	Key:  "prop_ebaf689039a52d0e",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Hypotheses: []string{"0 < n"},
		Conclusion: "von_mangoldt(n) ≤ log(&n)",
	},
		func(a *Argument, n *Expr[Nat], positiveN Fact) {
			nReal := a.TermAs[Real]("&n")
			primePower := a.Assuming(
				a.TermAs[Bool]("«isPrimePower»(n)"),
				"away from positive prime powers Λ vanishes, and n is at least 1",
				Simp(Fwd(VonMangoldtDef)),
				ByArith(positiveN, real_exp_log.LogNonneg.At(nReal)))
			p, k, power := a.Unpack2As[Nat, Nat](primePower)
			parts := a.Conjuncts(
				power,
				"prime base",
				"positive exponent",
				"prime-power representation")
			prime, positive, representation := parts[0], parts[1], parts[2]

			atLeastTwo := a.Have(
				"a prime base is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			baseBound := a.Have(
				"a positive power is at least its base",
				"p ≤ n",
				ByArith(positive, representation, nat_order.LessEqSelfPow.At(p, k)))
			logBound := a.Have(
				"the logarithm preserves order on the positive reals",
				"log(&p) ≤ log(&n)",
				ByArith(
					baseBound,
					atLeastTwo,
					real_construction.OfNumLessEq.At(a.TermAs[Nat]("2"), p),
					real_construction.OfNumLessEq.At(p, n),
					real_exp_log.LogLessIff.At(nReal, a.TermAs[Real]("&p"))))
			a.Show(
				"Λ at this prime power is log p",
				By(Normalized, prime, positive, representation, logBound, MangoldtPrimePower.At(p, k)))
		}),
	Reading: "At n = 0 the right side is the real logarithm at " +
		"0, an unspecified value, so the bound is stated for n > 0.",
})}

// MangoldtPrimePowersConverge — the series of Λ(n)/n over the n that are
// not prime converges. Its nonzero terms sit at the prime powers p^e with
// e ≥ 2; the pairs (p − 1, e − 2) cover them by a rectangle on which the
// weight log p · p⁻² · 2^(−(e − 2)) bounds each term, so the partial sums,
// which increase, are at most the product of the two convergent sums
// Σ log n · n⁻² and Σ 2⁻ᵏ.
var MangoldtPrimePowersConverge = mangoldtPrimePowersConvergeThm{family.Add(registry.ProofEntry{
	Name: "MangoldtPrimePowersConverge",
	Key:  "prop_696bb4feb5734c3",
	Reading: "The series is indexed from n = 1 by the shift n + 1, and its only nonzero terms are at " +
		"the prime powers p^e with e ≥ 2. Its value M is the sum of log p/(p(p − 1)) over the primes, " +
		"about 0.755; the bound the proof produces, 2 · Σ log n/n², about 1.88, is not sharp. At σ > 1 " +
		"every term of the series of Λ(n)·n^(−σ) over the same n is smaller, so M bounds that series too.",
	Build: family.Sections(Statement{
		Conclusion: "∃M:real. " +
			"    real_sums( " +
			"        λn:num. COND(nat_prime(n + 1), &0, von_mangoldt(n + 1) * real_rpow(&(n + 1), -&1)), M)",
		Abbrev: Abbrev{
			{Name: "coefficient", Text: "λn:num. " +
				"    COND(nat_prime(n + 1), &0, von_mangoldt(n + 1) * real_rpow(&(n + 1), -&1))"},
			{Name: "logWeights", Text: "λn:num. log(&(n + 1)) * real_rpow(&(n + 1), -&2)"},
			{Name: "geometricWeights", Text: "λn:num. real_rpow(&2, -&1) ^ n"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			factorWeight := ctx.Lemma(Statement{
				Binders:    "∀p k:num.",
				Hypotheses: []string{"2 ≤ p"},
				Conclusion: "real_rpow(&(p ^ (k + 2)), -&1) = real_rpow(&p, -&2) * real_rpow(&p, -&1) ^ k",
			},
				func(a *Argument, p, k *Expr[Nat], pLarge Fact) {
					base := a.TermAs[Real]("&p")
					negOne := a.TermAs[Real]("-&1")
					pRecip := a.TermAs[Real]("real_rpow(&p, -&1)")
					exponent := a.TermAs[Nat]("k + 2")
					combined := a.Have(
						"move the natural exponent into the real exponent",
						"real_rpow(&(p ^ (k + 2)), -&1) = real_rpow(&p, -&(k + 2))",
						ByArith(
							pLarge,
							real_pow.OfNumPow.At(p, exponent),
							real_rpow.RpowNat.At(base, exponent),
							real_rpow.RpowRpow.At(base, a.TermAs[Real]("&(k + 2)"), negOne)))
					split := a.Have(
						"separate the first two powers of the reciprocal",
						"real_rpow(&p, -&(k + 2)) = real_rpow(&p, -&2) * real_rpow(&p, -&k)",
						ByArith(pLarge, real_rpow.RpowAdd.At(base, a.TermAs[Real]("-&2"), a.TermAs[Real]("-&k"))))
					naturalPower := a.Have(
						"the remaining reciprocal power can be read at a natural exponent",
						"real_rpow(&p, -&k) = real_rpow(&p, -&1) ^ k",
						Derive(func(b *Argument) {
							nested := b.Have(
								"multiply the two real exponents",
								"real_rpow(real_rpow(&p, -&1), &k) = real_rpow(&p, -&k)",
								ByArith(pLarge, real_rpow.RpowRpow.At(base, negOne, b.TermAs[Real]("&k"))))
							b.Do(By(nested, real_rpow.RpowNonneg.At(base, negOne), real_rpow.RpowNat.At(pRecip, k)))
						}))
					a.Do(By(combined, split, naturalPower))
				})
			powerWeight := ctx.Lemma(Statement{
				Binders:    "∀p k:num.",
				Hypotheses: []string{"2 ≤ p"},
				Conclusion: "log(&p) * real_rpow(&(p ^ (k + 2)), -&1) ≤ " +
					"log(&p) * real_rpow(&p, -&2) * real_rpow(&2, -&1) ^ k",
			},
				func(a *Argument, p, k *Expr[Nat], pLarge Fact) {
					base := a.TermAs[Real]("&p")
					negOne := a.TermAs[Real]("-&1")
					negTwo := a.TermAs[Real]("-&2")
					pRecip := a.TermAs[Real]("real_rpow(&p, -&1)")
					twoRecip := a.TermAs[Real]("real_rpow(&2, -&1)")
					morePowers := a.Have(
						"the remaining powers are bounded by the geometric terms",
						"real_rpow(&p, -&1) ^ k ≤ real_rpow(&2, -&1) ^ k",
						By(
							pLarge,
							real_construction.OfNumLessEq.At(a.TermAs[Nat]("2"), p),
							real_rpow.RpowLessEqBaseNonpos.At(a.TermAs[Real]("&2"), base, negOne),
							real_rpow.RpowNonneg.At(base, negOne),
							real_pow.PowMonoBase.At(pRecip, twoRecip, k)))
					logNonneg := a.Have(
						"the logarithm of the prime is nonnegative",
						"&0 ≤ log(&p)",
						ByArith(
							pLarge,
							real_construction.OfNumLessEq.At(a.TermAs[Nat]("1"), p),
							real_exp_log.LogNonneg.At(base)))
					bounded := a.Have(
						"the first two reciprocal factors remain at the prime",
						"real_rpow(&(p ^ (k + 2)), -&1) ≤ real_rpow(&p, -&2) * real_rpow(&2, -&1) ^ k",
						By(
							pLarge,
							morePowers,
							At(factorWeight, p, k),
							real_rpow.RpowNonneg.At(base, negTwo),
							real_order_ring.LessEqMulLeft.At(
								a.TermAs[Real]("real_rpow(&p, -&2)"), a.TermAs[Real]("real_rpow(&p, -&1) ^ k"),
								a.TermAs[Real]("real_rpow(&2, -&1) ^ k"))))
					a.Do(ByArith(
						logNonneg,
						bounded,
						real_order_ring.LessEqMulLeft.At(
							a.TermAs[Real]("log(&p)"), a.TermAs[Real]("real_rpow(&(p ^ (k + 2)), -&1)"),
							a.TermAs[Real]("real_rpow(&p, -&2) * real_rpow(&2, -&1) ^ k"))))
				})
			geometricNonneg := ctx.Lemma("∀n:num. &0 ≤ «geometricWeights»(n)",
				func(a *Argument, n *Expr[Nat]) {
					a.Do(By(
						real_rpow.RpowNonneg.At(a.TermAs[Real]("&2"), a.TermAs[Real]("-&1")),
						real_pow.PowNonneg.At(a.TermAs[Real]("real_rpow(&2, -&1)"), n)))
				})
			logWeightsNonneg := ctx.Lemma("∀n:num. &0 ≤ «logWeights»(n)",
				func(a *Argument, n *Expr[Nat]) {
					argument := a.TermAs[Real]("&(n + 1)")
					logNonneg := a.Have(
						"the shifted input has nonnegative logarithm",
						"&0 ≤ log(&(n + 1))",
						ByArith(
							real_construction.OfNumLessEq.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("n + 1")),
							real_exp_log.LogNonneg.At(argument)))
					a.Do(ByArith(logNonneg, real_rpow.RpowNonneg.At(argument, a.TermAs[Real]("-&2"))))
				})
			rectangleBound := ctx.Lemma(Statement{
				Binders: "∀N:num.",
				Conclusion: "Σ_{n∈«prefix»} «coefficient»(n) ≤ " +
					"(Σ_{n∈«prefix»} «logWeights»(n)) * (Σ_{n∈«prefix»} «geometricWeights»(n))",
				Abbrev: Abbrev{
					{Name: "prefix", Text: "0 .. N"},
					{Name: "support", Text: "{n:num | " +
						"    n ∈ «prefix» ∧ ¬nat_prime(n + 1) ∧ ∃p e:num. nat_prime(p) ∧ 0 < e ∧ n + 1 = p ^ e}"},
					{Name: "rectangle", Text: "set_cross(«prefix», «prefix»)"},
					{Name: "index", Text: "λz:prod(num, num). (fst(z) + 1) ^ (snd(z) + 2) - 1"},
					{Name: "weight", Text: "λz:prod(num, num). «logWeights»(fst(z)) * «geometricWeights»(snd(z))"},
				},
			}, func(a *Argument, N *Expr[Nat]) {
				zero := a.TermAs[Nat]("0")
				prefix := a.TermAs[Set[Nat]]("«prefix»")
				support := a.TermAs[Set[Nat]]("«support»")
				rectangle := a.TermAs[Set[Prod[Nat, Nat]]]("«rectangle»")
				coefficient := a.TermAs[Fun[Nat, Real]]("«coefficient»")
				index := a.TermAs[Fun[Prod[Nat, Nat], Nat]]("«index»")
				productWeight := a.TermAs[Fun[Prod[Nat, Nat], Real]]("«weight»")
				primeWeight := a.TermAs[Fun[Nat, Real]]("«logWeights»")
				geometricWeight := a.TermAs[Fun[Nat, Real]]("«geometricWeights»")
				bounds := a.Have(
					"read the endpoints of the interval",
					"∀n:num. n ∈ «prefix» ⇒ 0 ≤ n ∧ n ≤ N",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						member := b.Assume()
						b.Do(BySets(member))
					}))
				subset := a.Have(
					"the supported terms lie in the interval",
					"«support» ⊆ «prefix»",
					BySets())
				omittedZero := a.Have(
					"the omitted terms have zero coefficient",
					"∀n:num. n ∈ «prefix» ∧ n ∉ «support» ⇒ «coefficient»(n) = &0",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						omitted := b.Assume()
						b.Cases(b.TermAs[Bool]("nat_prime(n + 1)"))
						b.When(
							"a prime takes the zero branch",
							func(c *Argument, prime Fact) {
								c.Do(By(prime))
							})
						b.Otherwise(
							"the nonprime input has no prime power representation",
							func(c *Argument, nonprime Fact) {
								notPower := c.Have(
									"only prime powers with positive exponent remain on the support",
									"¬∃p e:num. nat_prime(p) ∧ 0 < e ∧ n + 1 = p ^ e",
									BySets(omitted, nonprime))
								mangoldtZero := c.Have(
									"the von Mangoldt coefficient vanishes",
									"von_mangoldt(n + 1) = &0",
									By(notPower, VonMangoldtDef.At(c.TermAs[Nat]("n + 1"))))
								c.Do(ByArith(nonprime, mangoldtZero))
							})
					}))
				supportedSum := a.Have(
					"retain only the supported terms",
					"Σ_{n∈«support»} «coefficient»(n) = Σ_{n∈«prefix»} «coefficient»(n)",
					By(subset, omittedZero, real_sum.Superset.At(support, prefix, coefficient)))
				rectangleNonneg := a.Have(
					"each rectangle weight is a product of nonnegative factors",
					"∀z:prod(num, num). z ∈ «rectangle» ⇒ &0 ≤ «weight»(z)",
					Derive(func(b *Argument) {
						b.FixAs[Prod[Nat, Nat]]("z")
						b.Assume()
						b.Do(ByArith(
							At(logWeightsNonneg, b.TermAs[Nat]("fst(z)")),
							At(geometricNonneg, b.TermAs[Nat]("snd(z)"))))
					}))
				coverage := a.Have(
					"cover each supported coefficient by a rectangle weight",
					Statement{
						Binders:    "∀x:num.",
						Hypotheses: []string{"x ∈ «support»"},
						Conclusion: "∃z:prod(num, num). z ∈ «rectangle» ∧ «index»(z) = x ∧ «coefficient»(x) ≤ «weight»(z)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Nat]("x")
						member := b.Assume()
						supportFacts := b.Have(
							"read the supported input and its prime power representation",
							"x ∈ «prefix» ∧ ¬nat_prime(x + 1) ∧ ∃p e:num. nat_prime(p) ∧ 0 < e ∧ x + 1 = p ^ e",
							BySets(member))
						properties := b.Conjuncts(
							supportFacts,
							"the input lies in the interval",
							"the input represents a nonprime",
							"the input represents a prime power")
						inPrefix, nonprime, powerExists := properties[0], properties[1], properties[2]
						_, _, representation := b.Unpack2(powerExists, "p", "e")
						p := b.TermAs[Nat]("p")
						e := b.TermAs[Nat]("e")
						powerParts := b.Conjuncts(
							representation,
							"the base is prime",
							"the exponent is positive",
							"the power is x + 1")
						prime, exponentPositive, power := powerParts[0], powerParts[1], powerParts[2]
						eLarge := b.Have(
							"the exponent is at least two",
							"2 ≤ e",
							Derive(func(c *Argument) {
								c.Cases(c.TermAs[Bool]("e = 1"))
								c.When(
									"exponent one would make the input prime",
									func(d *Argument, equal Fact) {
										d.Do(By(Normalized, equal, prime, nonprime, power, nat_arith.PowOne.At(p)))
									})
								c.Otherwise(
									"a positive exponent other than one is at least two",
									func(d *Argument, different Fact) {
										d.Do(ByArith(different, exponentPositive))
									})
							}))
						pLarge := b.Have(
							"the prime is at least two",
							"2 ≤ p",
							By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
						indexBounds := b.Have(
							"the power bounds both the base and the exponent",
							"p ≤ x + 1 ∧ e ≤ x",
							ByArith(
								pLarge,
								exponentPositive,
								power,
								nat_order.LessEqSelfPow.At(p, e),
								nat_order.LessThanPowSelf.At(p, e)))
						baseIndex := b.TermAs[Nat]("p - 1")
						exponentIndex := b.TermAs[Nat]("e - 2")
						coordinate := b.TermAs[Prod[Nat, Nat]]("(p - 1, e - 2)")
						baseProjection := pairs.Fst.At(baseIndex, exponentIndex)
						exponentProjection := pairs.Snd.At(baseIndex, exponentIndex)
						coordinates := b.Have(
							"the shifted coordinates restore the base and exponent",
							"fst((p - 1, e - 2)) + 1 = p ∧ snd((p - 1, e - 2)) + 2 = e",
							ByArith(pLarge, eLarge, baseProjection, exponentProjection))
						b.Take(coordinate)
						b.Do(SplitConjAll(
							Case(
								"the shifted indices lie in the rectangle",
								ByArith(
									indexBounds,
									inPrefix,
									bounds.At(x),
									num_segment.IntervalDef.At(zero, N),
									set_product.InCross.At(prefix, prefix, baseIndex, exponentIndex))),
							Case(
								"the rectangle index recovers x",
								Derive(func(c *Argument) {
									restoredPower := c.Have(
										"the recovered base and exponent give x + 1",
										"(fst((p - 1, e - 2)) + 1) ^ (snd((p - 1, e - 2)) + 2) = x + 1",
										By(coordinates, power))
									c.Do(ByArith(restoredPower))
								})),
							Case(
								"the rectangle weight bounds the coefficient at x",
								Derive(func(c *Argument) {
									mangoldt := c.Have(
										"the von Mangoldt coefficient is the logarithm of the prime",
										"von_mangoldt(x + 1) = log(&p)",
										By(Normalized, prime, exponentPositive, power, MangoldtPrimePower.At(p, e)))
									exponentRestored := c.Have(
										"adding two to the shifted exponent restores e",
										"e - 2 + 2 = e",
										ByArith(eLarge))
									powerAtShift := c.Have(
										"write the input power using the shifted exponent",
										"x + 1 = p ^ ((e - 2) + 2)",
										By(Normalized, power, exponentRestored))
									c.Do(By(
										nonprime,
										mangoldt,
										coordinates,
										exponentProjection,
										powerAtShift,
										pLarge,
										At(powerWeight, p, exponentIndex)))
								}))))
					}))
				finiteSupport := a.Have(
					"the support and rectangle are finite",
					"finite(«support») ∧ finite(«rectangle»)",
					By(
						subset,
						num_segment.Finite.At(zero, N),
						finite_set.FiniteSubset.At(support, prefix),
						finite_set.FiniteProduct.At(prefix, prefix)))
				covered := a.Have(
					"sum the nonnegative covering weights",
					"Σ_{n∈«support»} «coefficient»(n) ≤ Σ_{z∈«rectangle»} «weight»(z)",
					By(
						finiteSupport,
						rectangleNonneg,
						coverage,
						real_sum.Covered.At(support, rectangle, index, coefficient, productWeight)))
				a.Do(By(
					supportedSum,
					covered,
					num_segment.Finite.At(zero, N),
					real_sum.ProductOfSums.At(prefix, prefix, primeWeight, geometricWeight)))
			})
			return ctx.Theorem(headline, func(a *Argument) {
				T, logarithmicSeries := a.ObtainAs[Real](
					"sum the logarithm weighted p-series at exponent two",
					"∃T:real. real_sums(«logWeights», T)",
					By(real_rpow.LogRpowSeriesConverges.At(a.TermAs[Real]("&2"))))
				one := a.TermAs[Real]("&1")
				two := a.TermAs[Real]("&2")
				negOne := a.TermAs[Real]("-&1")
				rho := a.TermAs[Real]("real_rpow(&2, -&1)")
				geometricSmall := a.Have(
					"the common ratio lies within the unit interval",
					"|real_rpow(&2, -&1)| < &1",
					ByArith(
						real_rpow.RpowLessBaseNegative.At(one, two, negOne),
						real_rpow.RpowOneBase.At(negOne),
						real_rpow.RpowNonneg.At(two, negOne)))
				geometricSeries := a.Have(
					"sum the geometric series at the common ratio",
					"real_sums(«geometricWeights», real_inv(&1 - real_rpow(&2, -&1)))",
					By(geometricSmall, real_series.Geometric.At(rho)))
				maximum := a.TermAs[Real]("T * real_inv(&1 - real_rpow(&2, -&1))")
				geometricSum := a.TermAs[Real]("real_inv(&1 - real_rpow(&2, -&1))")
				coefficient := a.TermAs[Fun[Nat, Real]]("«coefficient»")
				primeWeight := a.TermAs[Fun[Nat, Real]]("«logWeights»")
				geometricWeight := a.TermAs[Fun[Nat, Real]]("«geometricWeights»")
				partial := a.TermAs[Fun[Nat, Real]]("λN:num. Σ_{n∈0 .. N} «coefficient»(n)")
				upper := a.Have(
					"all the partial sums are bounded by the product of the two series values",
					"∀N:num. Σ_{n∈0 .. N} «coefficient»(n) ≤ T * real_inv(&1 - real_rpow(&2, -&1))",
					Derive(func(b *Argument) {
						N := b.FixAs[Nat]("N")
						prefix := b.TermAs[Set[Nat]]("0 .. N")
						logBound := b.Have(
							"the logarithmic partial sum is at most its series value",
							"Σ_{n∈0 .. N} «logWeights»(n) ≤ T",
							By(logarithmicSeries, logWeightsNonneg, real_series.SumsPartialLessEq.At(primeWeight, T, N)))
						geometricBound := b.Have(
							"the geometric partial sum is at most its series value",
							"Σ_{n∈0 .. N} «geometricWeights»(n) ≤ real_inv(&1 - real_rpow(&2, -&1))",
							By(
								geometricSeries,
								geometricNonneg,
								real_series.SumsPartialLessEq.At(geometricWeight, geometricSum, N)))
						nonnegative := b.Have(
							"both partial sums are nonnegative",
							"&0 ≤ (Σ_{n∈0 .. N} «logWeights»(n)) ∧ &0 ≤ (Σ_{n∈0 .. N} «geometricWeights»(n))",
							By(
								logWeightsNonneg,
								geometricNonneg,
								real_sum.Nonneg.At(prefix, primeWeight),
								real_sum.Nonneg.At(prefix, geometricWeight)))
						productBound := b.Have(
							"multiply the two upper bounds",
							"(Σ_{n∈0 .. N} «logWeights»(n)) * (Σ_{n∈0 .. N} «geometricWeights»(n)) ≤ "+
								"T * real_inv(&1 - real_rpow(&2, -&1))",
							By(
								logBound,
								geometricBound,
								nonnegative,
								real_order_ring.LessEqMul2.At(
									b.TermAs[Real]("Σ_{n∈0 .. N} «logWeights»(n)"),
									T,
									b.TermAs[Real]("Σ_{n∈0 .. N} «geometricWeights»(n)"),
									geometricSum)))
						b.Do(ByArith(productBound, At(rectangleBound, N)))
					}))
				coefficientNonneg := a.Have(
					"every original coefficient is nonnegative",
					"∀n:num. &0 ≤ «coefficient»(n)",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						b.Do(ByArith(
							MangoldtNonneg.At(b.TermAs[Nat]("n + 1")),
							real_rpow.RpowNonneg.At(b.TermAs[Real]("&(n + 1)"), b.TermAs[Real]("-&1"))))
					}))
				rising := a.Have(
					"successive partial sums increase",
					"∀N:num. (Σ_{n∈0 .. N} «coefficient»(n)) ≤ Σ_{n∈0 .. (N + 1)} «coefficient»(n)",
					Derive(func(b *Argument) {
						N := b.FixAs[Nat]("N")
						b.Do(ByArith(
							coefficientNonneg,
							real_sum.IntervalExtend.At(
								b.TermAs[Nat]("0"), N, b.TermAs[Nat]("N + 1"), coefficient)))
					}))
				limit := a.TermAs[Real]("sup(image(λN:num. Σ_{n∈0 .. N} «coefficient»(n), 𝕌))")
				converges := a.Have(
					"the bounded increasing partial sums converge to their supremum",
					"(λN:num. Σ_{n∈0 .. N} «coefficient»(n)) ⟶ sup(image(λN:num. Σ_{n∈0 .. N} «coefficient»(n), 𝕌))",
					By(rising, upper, real_sequences.IncreasingBoundedConvergesToSup.At(partial, maximum)))
				a.Take(limit)
				a.Do(By(converges, real_series.RealSumsDef.At(coefficient, limit)))
			})
		}),
})}

// LogPrimeFactorization — log n is the sum of the logarithms of the
// prime bases weighted by their multiplicities in n.
var LogPrimeFactorization = logPrimeFactorizationThm{family.Add(registry.ProofEntry{
	Name: "LogPrimeFactorization",
	Key:  "prop_5fd0763275eabf62",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Hypotheses: []string{"0 < n"},
		Conclusion: "Σ_{p∈«primes»(n)} «multiplicityWeight»(n, p) = log(&n)",
		Abbrev: Abbrev{
			{Name: "natFactors", Text: "λa:num. λp:num. p ^ nat_multiplicity(p, a)"},
			{Name: "realFactors", Text: "λa:num. λp:num. real_of_num(«natFactors»(a, p))"},
			{Name: "multiplicityWeight", Text: "λa:num. λp:num. real_of_num(nat_multiplicity(p, a)) * log(&p)"},
		},
	}, func(a *Argument, n *Expr[Nat], positive Fact) {
		primes := a.TermAs[Set[Nat]]("«primes»(n)")
		finite := PrimesFinite.At(n)
		factor := a.TermAs[Fun[Nat, Real]]("«realFactors»(n)")
		primeDivisors := a.Have(
			"every prime divisor is at most n",
			"∀p:num. nat_prime(p) ∧ p ∣ n ⇒ p ≤ n",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				divisor := b.Assume()
				b.Show(
					"the divisor bound for positive n",
					ByArith(positive, divisor, nat_divides.DividesLessEq.At(p, n)))
			}))
		factorization := a.Have(
			"multiply the prime powers of their full multiplicities",
			"n = Π_{p∈«primes»(n)} «natFactors»(n, p)",
			ByArith(positive, primeDivisors, nat_multiplicity.PrimeFactorizationProduct.At(n, n)))
		realFactorization := a.Have(
			"n as a real is the product of the real prime powers, casting the product factor by factor",
			"&n = Π_{p∈«primes»(n)} «realFactors»(n, p)",
			By(
				factorization,
				finite,
				real_product.RealOfNatProduct.At(primes, a.TermAs[Fun[Nat, Nat]]("«natFactors»(n)"))))
		positiveFactors := a.Have(
			"every prime-power factor is positive",
			"∀p:num. p ∈ «primes»(n) ⇒ &0 < «realFactors»(n, p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				inPrimes := b.Assume()
				b.Show(
					"the base is at least two",
					Simp(Rev(real_pow.OfNumPow)),
					ByArith(
						inPrimes,
						nat_prime.PrimeAtLeastTwo.At(p),
						real_construction.OfNumLessEq.At(b.TermAs[Nat]("2"), p),
						real_pow.PowPos.At(b.TermAs[Real]("&p"), b.TermAs[Nat]("nat_multiplicity(p, n)"))))
			}))
		logFactors := a.Have(
			"the logarithm of a prime power is the base logarithm times its exponent",
			"∀p:num. p ∈ «primes»(n) ⇒ log(«realFactors»(n, p)) = «multiplicityWeight»(n, p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				inPrimes := b.Assume()
				b.Show(
					"take the logarithm at the positive prime base",
					Simp(Rev(real_pow.OfNumPow)),
					ByArith(
						inPrimes,
						nat_prime.PrimeAtLeastTwo.At(p),
						real_construction.OfNumLessEq.At(b.TermAs[Nat]("2"), p),
						real_exp_log.LogPow.At(b.TermAs[Real]("&p"), b.TermAs[Nat]("nat_multiplicity(p, n)"))))
			}))
		logProduct := a.Have(
			"the logarithm of the product is the sum of the factor logarithms",
			"log(Π_{p∈«primes»(n)} «realFactors»(n, p)) = Σ_{p∈«primes»(n)} log(«realFactors»(n, p))",
			By(positiveFactors, finite, real_exp_log.LogProduct.At(primes, factor)))
		weighted := a.Have(
			"replace each factor logarithm by its multiplicity weight",
			"(Σ_{p∈«primes»(n)} log(«realFactors»(n, p))) = Σ_{p∈«primes»(n)} «multiplicityWeight»(n, p)",
			By(
				logFactors,
				real_sum.Congruence.At(
					primes,
					a.TermAs[Fun[Nat, Real]]("λp:num. log(«realFactors»(n, p))"),
					a.TermAs[Fun[Nat, Real]]("«multiplicityWeight»(n)"))))
		a.Show(
			"the weighted sum is the logarithm of n",
			By(realFactorization, logProduct, weighted))
	}),
})}

// MangoldtSumByPrimes — the Mangoldt sum over a set of integers from 1 to n
// counts, for each prime p up to n, the positive powers of p in the set, each
// weighted by log p. Λ vanishes off the prime powers; the prime powers fall
// into fibres by their prime base, which is a prime up to n, and the fibre of
// p is the set of positive powers of p in the set, each worth log p.
var MangoldtSumByPrimes = mangoldtSumByPrimesThm{family.Add(registry.ProofEntry{
	Name: "MangoldtSumByPrimes",
	Key:  "prop_f12a19bcd64f6cb5",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀s:set(num).",
		Hypotheses: []string{"s ⊆ 1 .. n"},
		Conclusion: "Σ_{d∈s} von_mangoldt(d) = Σ_{p∈«primes»(n)} &card(«powersIn»(s, p)) * log(&p)",
		Abbrev: Abbrev{
			{Name: "powerSupport", Text: "λs:set(num). {d:num | d ∈ s ∧ «isPrimePower»(d)}"},
			{Name: "baseFibre", Text: "λs:set(num). λp:num. " +
				"    {d:num | d ∈ «powerSupport»(s) ∧ «primeBase»(d) = p}"},
			{Name: "fibreSum", Text: "λs:set(num). λp:num. sum(«baseFibre»(s, p), von_mangoldt)"},
		},
	}, func(a *Argument, n *Expr[Nat], s *Expr[Set[Nat]], bounded Fact) {
		one := a.TermAs[Nat]("1")
		interval := a.TermAs[Set[Nat]]("1 .. n")
		support := a.TermAs[Set[Nat]]("«powerSupport»(s)")
		primes := a.TermAs[Set[Nat]]("«primes»(n)")
		base := a.TermAs[Fun[Nat, Nat]]("«primeBase»")
		mangoldt := a.TermAs[Fun[Nat, Real]]("von_mangoldt")

		supported := a.Have(
			"the prime powers of s lie in s, and so between 1 and n",
			"«powerSupport»(s) ⊆ s ∧ «powerSupport»(s) ⊆ 1 .. n",
			BySets(bounded))
		finite := a.Have(
			"so they are finitely many",
			"finite(«powerSupport»(s))",
			By(supported, num_segment.Finite.At(one, n), finite_set.FiniteSubset.At(support, interval)))
		vanishes := a.Have(
			"the members of s that are no positive prime power contribute zero",
			"∀d:num. d ∈ s ∧ d ∉ «powerSupport»(s) ⇒ von_mangoldt(d) = &0",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				offSupport := b.Assume()
				b.Have(
					"d is no positive prime power",
					"¬«isPrimePower»(d)",
					BySets(offSupport))
				b.Show(
					"apply the zero branch of Λ",
					Simp(Fwd(VonMangoldtDef)),
					Refl())
			}))
		baseData := a.Have(
			"a prime power of s is a positive power of its chosen prime base, a prime up to n",
			Statement{
				Binders:    "∀d:num.",
				Hypotheses: []string{"d ∈ «powerSupport»(s)"},
				Conclusion: "nat_prime(«primeBase»(d)) ∧ " +
					"«primeBase»(d) ≤ n ∧ " +
					"(∃k:num. 0 < k ∧ d = «primeBase»(d) ^ k)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				inSupport := b.Assume()
				p, k, power := b.Obtain2As[Nat, Nat](
					"take a prime base and a positive exponent for d",
					"«isPrimePower»(d)",
					BySets(inSupport))
				parts := b.Conjuncts(
					power,
					"prime base",
					"positive exponent",
					"power representation")
				prime, posK, representation := parts[0], parts[1], parts[2]
				chosen := b.Have(
					"the chosen prime divisor is the base of the power",
					"«primeBase»(d) = p",
					representation.Rw(),
					By(prime, posK, PrimePowerChosenBase.At(p, k)))
				b.Do(chosen.Rw())
				inInterval := b.Have(
					"d lies between 1 and n",
					"d ∈ 1 .. n",
					BySets(inSupport, supported))
				below := b.Have(
					"the base is at most its power, which is at most n",
					"p ≤ n",
					ByArith(posK, representation, inInterval, nat_order.LessEqSelfPow.At(p, k)))
				exponent := b.Have(
					"d is a positive power of p",
					"∃j:num. 0 < j ∧ d = p ^ j",
					Witness(k),
					By(posK, representation))
				b.Show(
					"the prime, its bound and the power",
					By(prime, below, exponent))
			}))
		covered := a.Have(
			"the chosen bases are primes up to n",
			"image(«primeBase», «powerSupport»(s)) ⊆ «primes»(n)",
			Derive(func(b *Argument) {
				primesOfPowers := b.Have(
					"each chosen base is a prime at most n",
					"∀d:num. d ∈ «powerSupport»(s) ⇒ «primeBase»(d) ∈ «primes»(n)",
					Derive(func(c *Argument) {
						d := c.FixAs[Nat]("d")
						inSupport := c.Assume()
						c.Show(
							"read the base and its bound",
							BySets(inSupport, baseData.At(d)))
					}))
				b.Show(
					"pass membership to the image",
					By(primesOfPowers, set_image.ImageSubsetIff.At(base, support, primes)))
			}))
		fibreValues := a.Have(
			"the fibre of a prime p is the set of positive powers of p in s, each worth log p",
			"∀p:num. p ∈ «primes»(n) ⇒ «fibreSum»(s, p) = &card(«powersIn»(s, p)) * log(&p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				inPrimes := b.Assume()
				prime := b.Have(
					"the fibre is indexed by a prime",
					"nat_prime(p)",
					BySets(inPrimes))
				fibre := b.TermAs[Set[Nat]]("«baseFibre»(s, p)")
				powers := b.TermAs[Set[Nat]]("«powersIn»(s, p)")
				identified := b.Have(
					"the fibre of p is the set of positive powers of p in s",
					"«baseFibre»(s, p) = «powersIn»(s, p)",
					Derive(func(c *Argument) {
						forward := c.Have(
							"a member of the fibre is a positive power of its base p",
							"«baseFibre»(s, p) ⊆ «powersIn»(s, p)",
							Unfold(set_basic.SubsetDef),
							Derive(func(e *Argument) {
								d := e.FixAs[Nat]("d")
								inFibre := e.Assume()
								data := e.Have(
									"d is a prime power of s with chosen base p",
									"d ∈ «powerSupport»(s) ∧ «primeBase»(d) = p",
									BySets(inFibre))
								parts := e.Conjuncts(
									data,
									"prime power of s",
									"base equal to p")
								e.Show(
									"its base data makes it a power of p",
									BySets(parts[0], parts[1], baseData.At(d)))
							}))
						backward := c.Have(
							"a positive power of p in s has chosen base p",
							"«powersIn»(s, p) ⊆ «baseFibre»(s, p)",
							Unfold(set_basic.SubsetDef),
							Derive(func(e *Argument) {
								e.FixAs[Nat]("d")
								inPowers := e.Assume()
								k, represented := e.ObtainAs[Nat](
									"take the exponent of the power",
									"∃k:num. 0 < k ∧ d = p ^ k",
									BySets(inPowers))
								parts := e.Conjuncts(
									represented,
									"positive exponent",
									"power representation")
								posK, representation := parts[0], parts[1]
								chosen := e.Have(
									"its chosen base is p",
									"«primeBase»(d) = p",
									representation.Rw(),
									By(prime, posK, PrimePowerChosenBase.At(p, k)))
								isPower := e.Have(
									"d is a positive prime power",
									"«isPrimePower»(d)",
									Witness(p),
									Witness(k),
									By(prime, posK, representation))
								e.Show(
									"so d lies in the fibre of p",
									BySets(inPowers, chosen, isPower))
							}))
						c.Show(
							"the two sets include each other",
							By(forward, backward, set_order.SubsetAntisym.At(fibre, powers)))
					}))
				termwise := b.Have(
					"each positive power of p is worth log p",
					"∀d:num. d ∈ «powersIn»(s, p) ⇒ von_mangoldt(d) = log(&p)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("d")
						inPowers := c.Assume()
						k, represented := c.ObtainAs[Nat](
							"write d as a positive power of p",
							"∃k:num. 0 < k ∧ d = p ^ k",
							BySets(inPowers))
						c.Show(
							"Λ at a power of a prime is the logarithm of the prime",
							ByArith(prime, represented, MangoldtPrimePower.At(p, k)))
					}))
				finitePowers := b.Have(
					"the powers of p in s are finitely many",
					"finite(«powersIn»(s, p))",
					BySets(bounded, num_segment.Finite.At(one, n), finite_set.FiniteSubset.At(powers, interval)))
				logP := b.TermAs[Real]("log(&p)")
				b.Show(
					"sum the constant log p over the powers of p",
					By(
						identified,
						finitePowers,
						termwise,
						real_sum.Congruence.At(powers, mangoldt, b.TermAs[Fun[Nat, Real]]("λd:num. log(&p)")),
						real_sum.Const.At(powers, logP)))
			}))
		restricted := a.Have(
			"remove the zero contributions",
			"sum(s, von_mangoldt) = sum(«powerSupport»(s), von_mangoldt)",
			By(supported, vanishes, real_sum.Superset.At(support, s, mangoldt)))
		regrouped := a.Have(
			"sum the fibres of the chosen-base map over the primes up to n",
			"sum(«powerSupport»(s), von_mangoldt) = sum(«primes»(n), «fibreSum»(s))",
			By(finite, covered, real_sum.Regroup.At(support, base, mangoldt, primes)))
		a.Show(
			"each fibre sum is the count of the powers of its prime times log p",
			By(
				restricted,
				regrouped,
				fibreValues,
				real_sum.Congruence.At(
					primes,
					a.TermAs[Fun[Nat, Real]]("«fibreSum»(s)"),
					a.TermAs[Fun[Nat, Real]]("λp:num. &card(«powersIn»(s, p)) * log(&p)"))))
	}),
})}

// MangoldtDivisorSum — the Mangoldt sum over the divisors of a positive
// integer is its logarithm: grouped by primes (MangoldtSumByPrimes), the
// positive powers of p dividing n are the pᵏ with 1 ≤ k ≤ v_p(n), and
// Σ_p v_p(n)·log p is log n (LogPrimeFactorization).
var MangoldtDivisorSum = mangoldtDivisorSumThm{family.Add(registry.ProofEntry{
	Name: "MangoldtDivisorSum",
	Key:  "prop_e8b7d68853cc4a35",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Hypotheses: []string{"0 < n"},
		Conclusion: "Σ_{d∈{d:num | d ∣ n}} von_mangoldt(d) = log(&n)",
		Abbrev: Abbrev{
			{Name: "divisors", Text: "λa:num. {d:num | d ∣ a}"},
			{Name: "multiplicityWeight", Text: "λa:num. λp:num. real_of_num(nat_multiplicity(p, a)) * log(&p)"},
		},
	}, func(a *Argument, n *Expr[Nat], positive Fact) {
		one := a.TermAs[Nat]("1")
		divisors := a.TermAs[Set[Nat]]("«divisors»(n)")
		primes := a.TermAs[Set[Nat]]("«primes»(n)")
		bounded := a.Have(
			"a divisor of the positive n lies between 1 and n",
			"«divisors»(n) ⊆ 1 .. n",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				x := b.FixAs[Nat]("x")
				divides := b.Assume()
				b.Show(
					"positive n bounds its divisors",
					ByArith(positive, divides, nat_divides.DividesLessEqStrong.At(x, n)))
			}))
		counts := a.Have(
			"the positive powers of a prime p dividing n are v_p(n) in number",
			Statement{
				Binders:    "∀p:num.",
				Hypotheses: []string{"p ∈ «primes»(n)"},
				Conclusion: "&card(«powersIn»(«divisors»(n), p)) * log(&p) = «multiplicityWeight»(n, p)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				inPrimes := b.Assume()
				atLeastTwo := b.Have(
					"the prime p is at least 2",
					"2 ≤ p",
					By(inPrimes, nat_prime.PrimeAtLeastTwo.At(p)))
				multiplicity := b.TermAs[Nat]("nat_multiplicity(p, n)")
				indices := b.TermAs[Set[Nat]]("1 .. nat_multiplicity(p, n)")
				power := b.TermAs[Fun[Nat, Nat]]("λk:num. p ^ k")
				fibre := b.TermAs[Set[Nat]]("«powersIn»(«divisors»(n), p)")
				powers := b.TermAs[Set[Nat]]("«powersThrough»(p, nat_multiplicity(p, n))")
				identified := b.Have(
					"they are the powers pᵏ with 1 ≤ k ≤ v_p(n)",
					"«powersIn»(«divisors»(n), p) = «powersThrough»(p, nat_multiplicity(p, n))",
					Derive(func(c *Argument) {
						forward := c.Have(
							"a positive power of p dividing n has its exponent at most the multiplicity",
							"«powersIn»(«divisors»(n), p) ⊆ «powersThrough»(p, nat_multiplicity(p, n))",
							Unfold(set_basic.SubsetDef),
							Derive(func(e *Argument) {
								e.FixAs[Nat]("d")
								inFibre := e.Assume()
								k, represented := e.ObtainAs[Nat](
									"write the divisor as a positive power of p",
									"∃k:num. 0 < k ∧ d = p ^ k",
									BySets(inFibre))
								e.Show(
									"divisibility bounds its exponent by the multiplicity",
									ByArith(
										positive,
										atLeastTwo,
										inFibre,
										represented,
										nat_multiplicity.DividesIff.At(p, n, k),
										set_image.FunInImage.At(power, indices, k)))
							}))
						backward := c.Have(
							"a power of p with exponent from 1 to the multiplicity divides n",
							"«powersThrough»(p, nat_multiplicity(p, n)) ⊆ «powersIn»(«divisors»(n), p)",
							Unfold(set_basic.SubsetDef),
							Derive(func(e *Argument) {
								d := e.FixAs[Nat]("d")
								inImage := e.Assume()
								k, represented := e.ObtainAs[Nat](
									"take the exponent of this image point",
									"∃k:num. d = p ^ k ∧ k ∈ 1 .. nat_multiplicity(p, n)",
									By(inImage, set_basic.InImage.At(power, indices, d)))
								parts := e.Conjuncts(
									represented,
									"power equality",
									"exponent in range")
								representation, inRange := parts[0], parts[1]
								divides := e.Have(
									"the power divides n by the multiplicity bound",
									"0 < k ∧ d ∣ n",
									ByArith(positive, atLeastTwo, representation, inRange, nat_multiplicity.DividesIff.At(p, n, k)))
								e.Show(
									"it is a positive power of p dividing n",
									BySets(divides, representation))
							}))
						c.Show(
							"the two sets include each other",
							By(forward, backward, set_order.SubsetAntisym.At(fibre, powers)))
					}))
				injective := b.Have(
					"distinct exponents give distinct powers",
					"injective_on(1 .. nat_multiplicity(p, n), λk:num. p ^ k)",
					Unfold(functions.InjectiveOnDef),
					Derive(func(c *Argument) {
						x := c.FixAs[Nat]("x")
						y := c.FixAs[Nat]("y")
						equal := c.Assume()
						c.Show(
							"strict growth of the powers of p recovers the exponent",
							ByArith(atLeastTwo, equal, nat_order.LessThanPow.At(p, x, y), nat_order.LessThanPow.At(p, y, x)))
					}))
				b.Show(
					"there is one power for each exponent from 1 to v_p(n)",
					By(
						identified,
						injective,
						num_segment.Finite.At(one, multiplicity),
						cardinality.CardImageInj.At(power, indices),
						num_segment.CardFromOne.At(multiplicity)))
			}))
		grouped := a.Have(
			"group the divisors by primes",
			"(Σ_{d∈«divisors»(n)} von_mangoldt(d)) = "+
				"Σ_{p∈«primes»(n)} &card(«powersIn»(«divisors»(n), p)) * log(&p)",
			By(bounded, MangoldtSumByPrimes.At(n, divisors)))
		weighted := a.Have(
			"each prime contributes its multiplicity weight",
			"(Σ_{p∈«primes»(n)} &card(«powersIn»(«divisors»(n), p)) * log(&p)) = "+
				"Σ_{p∈«primes»(n)} «multiplicityWeight»(n, p)",
			By(
				counts,
				real_sum.Congruence.At(
					primes,
					a.TermAs[Fun[Nat, Real]]("λp:num. &card(«powersIn»(«divisors»(n), p)) * log(&p)"),
					a.TermAs[Fun[Nat, Real]]("«multiplicityWeight»(n)"))))
		a.Show(
			"the weighted sum is the logarithm of the prime factorization",
			By(positive, grouped, weighted, LogPrimeFactorization.At(n)))
	}),
	Reading: "This is the identity Λ ∗ 1 = log: it is what makes the " +
		"Dirichlet series of Λ the logarithmic derivative of ζ. For n = 0 " +
		"the index set is infinite and the sum is 0 by the fold's convention.",
})}

// PsiMonotone — ψ is increasing because extending its sum adds nonnegative terms.
var PsiMonotone = psiMonotoneThm{family.Add(registry.ProofEntry{
	Name: "PsiMonotone",
	Key:  "prop_e90f4950dfcfa0f0",
	Build: family.Theorem(Statement{
		Binders:    "∀m n:num.",
		Hypotheses: []string{"m ≤ n"},
		Conclusion: "chebyshev_psi(m) ≤ chebyshev_psi(n)",
	},
		func(a *Argument, m, n *Expr[Nat], ordered Fact) {
			mangoldt := a.TermAs[Fun[Nat, Real]]("von_mangoldt")
			a.Show(
				"the interval from 1 to n extends the interval from 1 to m by nonnegative terms",
				Unfold(ChebyshevPsiDef),
				By(ordered, MangoldtNonneg, real_sum.IntervalExtend.At(a.TermAs[Nat]("1"), m, n, mangoldt)))
		}),
})}

// PsiNonneg — ψ is nonnegative, a sum of nonnegative Mangoldt terms.
var PsiNonneg = psiNonnegThm{family.Add(registry.ProofEntry{
	Name: "PsiNonneg",
	Key:  "prop_bb0a7d895686d7d7",
	Build: family.Theorem("∀n:num. &0 ≤ chebyshev_psi(n)",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"every summand Λ(k) of ψ(n) is nonnegative",
				Unfold(ChebyshevPsiDef),
				By(
					MangoldtNonneg,
					real_sum.Nonneg.At(a.TermAs[Set[Nat]]("1 .. n"), a.TermAs[Fun[Nat, Real]]("von_mangoldt"))))
		}),
})}

// PrimePowerCountLogBound — a set of positive powers of p ≥ 2 up to n
// has total weight at most log n when each power is weighted by log p.
var PrimePowerCountLogBound = primePowerCountLogBoundThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerCountLogBound",
	Key:  "prop_3fc6ec221090a4fe",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀s:set(num).",
		Hypotheses: []string{
			"2 ≤ p",
			"p ≤ n",
			"∀d:num. d ∈ s ⇒ (∃k:num. 0 < k ∧ d = p ^ k) ∧ d ≤ n",
		},
		Conclusion: "&card(s) * log(&p) ≤ log(&n)",
	}, func(a *Argument, p, n *Expr[Nat], s *Expr[Set[Nat]], atLeastTwo, pLeN, powers Fact) {
		one := a.TermAs[Nat]("1")
		nonempty := a.Have(
			"the base itself is a positive power at most n",
			"∃k:num. 0 < k ∧ p ^ k ≤ n",
			Witness(one),
			ByArith(pLeN, nat_arith.PowOne.At(p)))
		bounded := a.Have(
			"every eligible exponent is less than its power and hence at most n",
			"∃M:num. ∀k:num. 0 < k ∧ p ^ k ≤ n ⇒ k ≤ M",
			Witness(n),
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				eligible := b.Assume()
				b.Show(
					"the exponent is strictly below the power",
					ByArith(atLeastTwo, eligible, nat_order.LessThanPowSelf.At(p, k)))
			}))
		K, maximum := a.ObtainAs[Nat](
			"there is a greatest eligible exponent K: the claim is the "+
				"maximum principle's conclusion as it stands, positivity included",
			"∃K:num. 0 < K ∧ p ^ K ≤ n ∧ (∀k:num. 0 < k ∧ p ^ k ≤ n ⇒ k ≤ K)",
			By(nonempty, bounded, nat_order.MaximumExists.At(a.TermAs[Set[Nat]]("λk:num. 0 < k ∧ p ^ k ≤ n"))))
		parts := a.Conjuncts(
			maximum,
			"positive exponent",
			"power at most n",
			"maximal exponent")
		powerLeN, maximal := parts[1], parts[2]

		power := a.TermAs[Fun[Nat, Nat]]("λk:num. p ^ k")
		indices := a.TermAs[Set[Nat]]("1 .. K")
		allPowers := a.TermAs[Set[Nat]]("«powersThrough»(p, K)")
		covered := a.Have(
			"every member of s is the image of one of the eligible exponents",
			"s ⊆ «powersThrough»(p, K)",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				inS := b.Assume()
				member := b.Conjuncts(
					GroupPremises(inS, powers.At(d)),
					"the member is a positive power of p",
					"the member is at most n")
				k, representation := b.UnpackAs[Nat](member[0], "k")
				b.Show(
					"its exponent lies between 1 and K",
					ByArith(representation, member[1], maximal.At(k), set_image.FunInImage.At(power, indices, k)))
			}))
		count := a.Have(
			"the image has at most as many points as its exponent interval",
			"card(s) ≤ K",
			ByArith(
				covered,
				num_segment.Finite.At(one, K),
				finite_set.FiniteImage.At(power, indices),
				cardinality.CardSubset.At(s, allPowers),
				cardinality.CardImageLe.At(power, indices),
				num_segment.CardFromOne.At(K)))
		logNonneg := a.Have(
			"log is increasing from zero at 1 and p is at least 2",
			"&0 ≤ log(&p)",
			ByArith(atLeastTwo, real_exp_log.LogNonneg.At(a.TermAs[Real]("&p"))))
		a.Show(
			"scale the count by log p and compare the largest power with n",
			real_order_ring.OrderCalc(a.Ctx()).Calc(
				a.TermAs[Real]("&card(s) * log(&p)"),
				LeLeg(
					a.TermAs[Real]("&K * log(&p)"),
					"the contribution of at most K powers",
					ByArith(count, logNonneg, real_construction.OfNumLessEq.At(a.TermAs[Nat]("card(s)"), K))),
				LeLeg(
					a.TermAs[Real]("log(&n)"),
					"taking logarithms of the bound on the largest power",
					ByArith(
						atLeastTwo,
						pLeN,
						powerLeN,
						nat_arith.PowOne.At(n),
						real_exp_log.LogPowerLessEq.At(p, n, K, one)))))
	}),
})}

// PsiLessEqPiLog — ψ is at most the prime count times log n: grouped by
// primes (MangoldtSumByPrimes), the positive powers of a prime p up to n weigh
// at most log n (PrimePowerCountLogBound), and there are π(n) primes up to n.
var PsiLessEqPiLog = psiLessEqPiLogThm{family.Add(registry.ProofEntry{
	Name: "PsiLessEqPiLog",
	Key:  "prop_5d43273b4bc9d2b7",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "chebyshev_psi(n) ≤ &prime_counting(n) * log(&n)",
	}, func(a *Argument, n *Expr[Nat]) {
		interval := a.TermAs[Set[Nat]]("1 .. n")
		primes := a.TermAs[Set[Nat]]("«primes»(n)")
		logN := a.TermAs[Real]("log(&n)")
		weights := a.TermAs[Fun[Nat, Real]]("λp:num. &card(«powersIn»(1 .. n, p)) * log(&p)")
		fibreBound := a.Have(
			"the positive powers of a prime p up to n weigh at most log n",
			"∀p:num. p ∈ «primes»(n) ⇒ &card(«powersIn»(1 .. n, p)) * log(&p) ≤ log(&n)",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				inPrimes := b.Assume()
				powers := b.TermAs[Set[Nat]]("«powersIn»(1 .. n, p)")
				bounds := b.Have(
					"p is a prime up to n, so at least 2",
					"2 ≤ p ∧ p ≤ n",
					By(inPrimes, nat_prime.PrimeAtLeastTwo.At(p)))
				members := b.Have(
					"each of them is a positive power of p at most n",
					"∀d:num. d ∈ «powersIn»(1 .. n, p) ⇒ (∃k:num. 0 < k ∧ d = p ^ k) ∧ d ≤ n",
					BySets())
				b.Show(
					"count them against log n",
					By(bounds, members, PrimePowerCountLogBound.At(p, n, powers)))
			}))
		a.Show(
			"group ψ by primes and bound each prime's share by log n",
			real_order_ring.OrderCalc(a.Ctx()).CalcLeibniz(
				a.TermAs[Real]("chebyshev_psi(n)"),
				EqLeg(
					a.TermAs[Real]("Σ_{p∈«primes»(n)} &card(«powersIn»(1 .. n, p)) * log(&p)"),
					"group the terms of ψ by primes",
					Unfold(ChebyshevPsiDef),
					By(set_order.SubsetRefl.At(interval), MangoldtSumByPrimes.At(n, interval))),
				LeLeg(
					a.TermAs[Real]("&card(«primes»(n)) * log(&n)"),
					"each prime up to n has weight at most log n",
					By(PrimesFinite.At(n), fibreBound, real_sum.Bound.At(primes, weights, logN))),
				EqLeg(
					a.TermAs[Real]("&prime_counting(n) * log(&n)"),
					"π(n) counts the primes up to n",
					By(PrimeCountingDef.At(n)))))
	}),
	Reading: "At n = 0 and n = 1 both sides are 0: ψ and π vanish there, " +
		"and 0 times the logarithm is 0 whatever the logarithm's value.",
})}

// PsiLinearBound — ψ is bounded by five times its argument: ψ(n) is at
// most π(n)·log n, which the upper Chebyshev bound puts below 5n for
// n > 0, and ψ(0) is an empty sum.
var PsiLinearBound = psiLinearBoundThm{family.Add(registry.ProofEntry{
	Name: "PsiLinearBound",
	Key:  "prop_e77777dfb5d22435",
	Build: family.Theorem("∀n:num. chebyshev_psi(n) ≤ &5 * &n",
		func(a *Argument, n *Expr[Nat]) {
			mangoldt := a.TermAs[Fun[Nat, Real]]("von_mangoldt")
			nonzero := a.Unless(
				a.TermAs[Bool]("n = 0"),
				"at zero the sum defining ψ is empty",
				Given(func(b *Argument, atZero Fact) {
					b.Show(
						"the empty sum is zero",
						atZero.Rw(),
						Unfold(ChebyshevPsiDef),
						ByArith(real_sum.EmptyInterval.At(b.TermAs[Nat]("0"), b.TermAs[Nat]("1"), mangoldt)))
				}))
			a.Show(
				"bound ψ by the weighted prime count and then by five times n",
				real_order_ring.OrderCalc(a.Ctx()).Calc(
					a.TermAs[Real]("chebyshev_psi(n)"),
					LeLeg(
						a.TermAs[Real]("&prime_counting(n) * log(&n)"),
						"bound ψ by the prime count weighted by log n",
						Cite(PsiLessEqPiLog)),
					LeLeg(
						a.TermAs[Real]("&5 * &n"),
						"use the upper Chebyshev bound",
						ByArith(nonzero, ChebyshevUpperBound.At(n)))))
		}),
})}

// PsiRatioBound — ψ(n)/n lies between 0 and 5: for n > 0 divide
// 0 ≤ ψ(n) ≤ 5n by n, and at n = 0 the quotient is 0, the inverse of zero
// being zero.
var PsiRatioBound = psiRatioBoundThm{family.Add(registry.ProofEntry{
	Name: "PsiRatioBound",
	Key:  "prop_1d1c5cb296ed96f3",
	Build: family.Theorem("∀n:num. &0 ≤ chebyshev_psi(n) / &n ∧ chebyshev_psi(n) / &n ≤ &5",
		func(a *Argument, n *Expr[Nat]) {
			psi := a.TermAs[Real]("chebyshev_psi(n)")
			denominator := a.TermAs[Real]("&n")
			nonzero := a.Unless(
				a.TermAs[Bool]("n = 0"),
				"at zero the quotient is zero",
				Given(func(b *Argument, atZero Fact) {
					b.Show(
						"the inverse of zero is zero",
						Simp(Fwd(real_field.RealDivDef)),
						ByArith(atZero, real_construction.InvZero))
				}))
			a.Show(
				"divide 0 ≤ ψ(n) ≤ 5n by the positive n",
				ByArith(
					nonzero,
					real_order_ring.OfNumLessThan.At(a.TermAs[Nat]("0"), n),
					PsiNonneg.At(n),
					PsiLinearBound.At(n),
					real_order_field.LessEqDivMulLeft.At(a.TermAs[Real]("&0"), psi, denominator),
					real_order_field.LessEqDivMulRight.At(psi, a.TermAs[Real]("&5"), denominator)))
		}),
})}

// PrimeCountingThroughPsi — ψ bounds the difference of the prime counts
// at n and m weighted by log m. Each prime past m contributes at least log m.
var PrimeCountingThroughPsi = primeCountingThroughPsiThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingThroughPsi",
	Key:  "prop_d836d21bccb66881",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"0 < m",
			"m ≤ n",
		},
		Conclusion: "(&prime_counting(n) - &prime_counting(m)) * log(&m) ≤ chebyshev_psi(n)",
	},
		func(a *Argument, m, n *Expr[Nat], positive, ordered Fact) {
			one := a.TermAs[Nat]("1")
			mReal := a.TermAs[Real]("&m")
			logM := a.TermAs[Real]("log(&m)")
			window := a.TermAs[Set[Nat]]("«primesBetween»(m, n)")
			interval := a.TermAs[Set[Nat]]("1 .. n")
			finiteInterval := num_segment.Finite.At(one, n)

			inside := a.Have(
				"every prime in the window lies between 1 and n",
				"«primesBetween»(m, n) ⊆ 1 .. n",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("p")
					inWindow := b.Assume()
					b.Show(
						"the window starts above m and ends at n",
						ByArith(inWindow))
				}))
			finiteWindow := a.Have(
				"the window is part of a finite interval",
				"finite(«primesBetween»(m, n))",
				By(inside, finiteInterval, finite_set.FiniteSubset.At(window, interval)))
			termwise := a.Have(
				"each prime in the window contributes at least log m",
				"∀p:num. p ∈ «primesBetween»(m, n) ⇒ log(&m) ≤ von_mangoldt(p)",
				Derive(func(b *Argument) {
					p := b.FixAs[Nat]("p")
					inWindow := b.Assume()
					b.Show(
						"Λ(p) is log p for a prime and log increases from m to p",
						ByArith(
							positive,
							inWindow,
							real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), m),
							real_order_ring.OfNumLessThan.At(m, p),
							real_exp_log.LogLessIff.At(mReal, b.TermAs[Real]("&p")),
							MangoldtPrimePower.At(p, one),
							nat_arith.PowOne.At(p)))
				}))

			mangoldt := a.TermAs[Fun[Nat, Real]]("von_mangoldt")
			a.Show(
				"sum the common lower bound over the primes and extend to all indices of ψ",
				real_order_ring.OrderCalc(a.Ctx()).CalcLeibniz(
					a.TermAs[Real]("(&prime_counting(n) - &prime_counting(m)) * log(&m)"),
					EqLeg(
						a.TermAs[Real]("Σ_{p∈«primesBetween»(m, n)} log(&m)"),
						"the difference of the counts gives one copy of log m per prime in the window",
						Derive(func(b *Argument) {
							split := b.Have(
								"the primes up to n consist of those up to m and those in the window",
								"prime_counting(n) = prime_counting(m) + card(«primesBetween»(m, n))",
								By(ordered, PrimeCountingSplit.At(m, n)))
							b.Show(
								"subtract the old count and sum the constant log m",
								split.Rw(),
								Simp(Fwd(real_construction.OfNumAdd)),
								ByArith(finiteWindow, real_sum.Const.At(window, logM)))
						})),
					LeLeg(
						a.TermAs[Real]("sum(«primesBetween»(m, n), von_mangoldt)"),
						"replace each log m by the contribution of its prime",
						By(
							finiteWindow,
							termwise,
							real_sum.Monotone.At(window, a.TermAs[Fun[Nat, Real]]("λp:num. log(&m)"), mangoldt))),
					LeLeg(
						a.TermAs[Real]("chebyshev_psi(n)"),
						"the indices outside the window also contribute nonnegative terms",
						Unfold(ChebyshevPsiDef),
						By(inside, finiteInterval, MangoldtNonneg, real_sum.Subset.At(window, interval, mangoldt)))))
		}),
	Reading: "This is the half of the passage from ψ to π that " +
		"bounds π from above; the other half is PsiLessEqPiLog.",
})}
