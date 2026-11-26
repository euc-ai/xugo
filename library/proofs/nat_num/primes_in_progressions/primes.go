// primes.go — from Λ to the primes of the progression. Λ is supported on
// the prime powers, and those p^e with e ≥ 2 form a convergent series
// (prime_distribution.MangoldtPrimePowersConverge), so the primes p ≡ a
// mod q alone, weighted by log p, carry the share 1/φ(q) of the pole as σ
// decreases to 1 (ProgressionPrimeDensity). Finitely many of them could not
// carry a pole: there are infinitely many (PrimesInProgression, Dirichlet's
// theorem).

package primes_in_progressions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ProgressionPrimeDensity — for a coprime to q, (σ − 1) times the series
// of log p · p^(−σ) over the primes p ≡ a mod q tends to 1/φ(q) as σ
// decreases to 1.
var ProgressionPrimeDensity = progressionPrimeDensityThm{family.Add(registry.ProofEntry{
	Name: "ProgressionPrimeDensity",
	Key:  "prop_4a4a6bf3cf62d7d0",
	Build: family.Theorem(Statement{
		Binders: "∀q a:num. ∀ε:real.",
		Hypotheses: []string{
			"0 < q",
			"nat_coprime(a, q)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀σ:real. " +
			"        &1 < σ ∧ σ < &1 + δ ⇒ " +
			"        |complex_of_real(σ - &1) * " +
			"        dirichlet_series(λn:num. " +
			"                COND(nat_prime(n) ∧ n ≡ a (mod q), " +
			"                    complex_of_real(log(&n)), " +
			"                    complex_of_real(&0)), " +
			"            complex_of_real(σ)) - " +
			"        complex_of_real(&1 / &(totient(q)))| < " +
			"        ε",
	}, func(
		arg *Argument,
		q, a *Expr[Nat],
		ε *Expr[Real],
		guards Fact,
	) {
		M, higherPowers := arg.UnpackAs[Real](prime_distribution.MangoldtPrimePowersConverge, "M")
		F, mangoldt := arg.LetAs[Fun[Nat, Real]]("F", "λn:num. COND(n ≡ a (mod q), von_mangoldt(n), &0)")
		G, primes := arg.LetAs[Fun[Nat, Real]](
			"G", "λn:num. COND(nat_prime(n) ∧ n ≡ a (mod q), log(&n), &0)")
		difference := arg.Have(
			"restricting the omitted prime powers to one residue gives the same uniform bound",
			Statement{
				Binders:    "∀σ:real.",
				Hypotheses: []string{"&1 < σ"},
				Conclusion: "|dirichlet_series(λn:num. complex_of_real(F(n)), complex_of_real(σ)) - " +
					"dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(σ))| ≤ " +
					"M",
			},
			Derive(func(b *Argument) {
				σ := b.FixAs[Real]("σ")
				aboveOne := b.Assume()
				_, weightDef := b.LetAs[Fun[Nat, Real]]("W", "λn:num. real_rpow(&n, -σ)")
				H, atOneDef := b.LetAs[Fun[Nat, Real]](
					"H", "λn:num. COND(nat_prime(n + 1), &0, von_mangoldt(n + 1) * real_rpow(&(n + 1), -&1))")
				hSums := b.Have(
					"the higher prime powers at one sum to M",
					"real_sums(H, M)",
					By(higherPowers, atOneDef))
				logBound := b.Have(
					"the coefficients of the progression's Mangoldt series are at most the logarithm",
					"∀n:num. |F(n + 1)| ≤ log(&(n + 1))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						n1 := c.TermAs[Nat]("n + 1")
						c.Show(
							"either the coefficient is retained, between zero and the logarithm, or it is zero",
							ByArith(
								mangoldt,
								prime_distribution.MangoldtNonneg.At(n1),
								prime_distribution.MangoldtLessEqLog.At(n1)))
					}))
				dominated := b.Have(
					"the higher prime powers of one residue at σ are dominated by all of them at one",
					"∀n:num. |F(n + 1) - G(n + 1)| * real_rpow(&(n + 1), -σ) ≤ H(n)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						n1 := c.TermAs[Nat]("n + 1")
						base := c.TermAs[Real]("&(n + 1)")
						negOne := c.TermAs[Real]("-&1")
						positive := c.Have(
							"the shifted base is positive",
							"&0 < &(n + 1)",
							ByArith())
						bounds := c.Have(
							"the Mangoldt coefficient and its positive weight give a nonnegative term",
							"&0 ≤ von_mangoldt(n + 1) ∧ &0 < W(n + 1)",
							ByArith(
								positive,
								weightDef,
								prime_distribution.MangoldtNonneg.At(n1),
								real_rpow.RpowPositive.At(base, c.TermAs[Real]("-σ"))))
						atOne := c.Have(
							"the weight at σ is at most the weight at one",
							"W(n + 1) ≤ real_rpow(&(n + 1), -&1)",
							ByArith(aboveOne, weightDef, real_rpow.RpowLessEqExponent.At(base, c.TermAs[Real]("-σ"), negOne)))
						onPrimes := c.Have(
							"the Mangoldt value at a prime is its logarithm",
							"nat_prime(n + 1) ⇒ von_mangoldt(n + 1) = log(&(n + 1))",
							ByArith(prime_distribution.MangoldtPrimePower.At(n1, c.TermAs[Nat]("1")), nat_arith.NatPow))
						c.Cases(c.Term("nat_prime(n + 1)"))
						c.When(
							"a prime retains its logarithm",
							func(d *Argument, prime Fact) {
								d.Show(
									"the two coefficients agree and the higher-prime-power term is zero",
									ByArith(mangoldt, primes, atOneDef, prime, onPrimes))
							})
						c.Otherwise(
							"a nonprime contributes only to the higher prime powers",
							func(d *Argument, composite Fact) {
								d.Show(
									"in either residue case the term lies between zero and the term at one",
									ByArith(
										mangoldt,
										primes,
										atOneDef,
										weightDef,
										composite,
										bounds,
										atOne,
										real_rpow.RpowNonneg.At(base, negOne),
										real_order_ring.LessEqMulLeft.At(
											d.TermAs[Real]("von_mangoldt(n + 1)"),
											d.TermAs[Real]("W(n + 1)"),
											d.TermAs[Real]("real_rpow(&(n + 1), -&1)"))))
							})
					}))
				b.Show(
					"the series differ by at most the sum of the higher prime powers at one",
					By(
						aboveOne,
						logBound,
						dominated,
						hSums,
						dirichlet_series.DirichletSeriesDifferenceBound.At(F, G, H, σ, M)))
			}))
		allCast := arg.Have(
			"embed the restricted Mangoldt coefficients",
			"(λn:num. complex_of_real(F(n))) = "+
				"(λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the real embedding respects the residue indicator",
					By(
						mangoldt,
						complex_field.OfRealCond.At(
							b.TermAs[Bool]("n ≡ a (mod q)"), b.TermAs[Real]("von_mangoldt(n)"), b.TermAs[Real]("&0"))))
			}))
		primeCast := arg.Have(
			"embed the restricted prime coefficients",
			"(λn:num. complex_of_real(G(n))) = "+
				"(λn:num. COND(nat_prime(n) ∧ n ≡ a (mod q), complex_of_real(log(&n)), complex_of_real(&0)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the real embedding respects the prime indicator",
					By(
						primes,
						complex_field.OfRealCond.At(
							b.TermAs[Bool]("nat_prime(n) ∧ n ≡ a (mod q)"), b.TermAs[Real]("log(&n)"), b.TermAs[Real]("&0"))))
			}))
		_, share := arg.LetAs[Real]("r", "&1 / &(totient(q))")
		f, fDef := arg.LetAs[Fun[Real, Complex]](
			"f", "λs:real. dirichlet_series(λn:num. complex_of_real(F(n)), complex_of_real(s))")
		g, gDef := arg.LetAs[Fun[Real, Complex]](
			"g", "λs:real. dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(s))")
		density := arg.Have(
			"the scaled Mangoldt series of the progression tends to r",
			Statement{
				Binders:    "∀η:real.",
				Hypotheses: []string{"&0 < η"},
				Conclusion: "∃d:real. " +
					"    &0 < d ∧ " +
					"    (∀σ:real. &1 < σ ∧ σ < &1 + d ⇒ |complex_of_real(σ - &1) * f(σ) - complex_of_real(r)| < η)",
			},
			By(guards, fDef, share, allCast, At(ProgressionMangoldtDensity, q, a)))
		limit := arg.Have(
			"the bounded difference leaves the scaled limit unchanged",
			"∃δ:real. "+
				"    &0 < δ ∧ "+
				"    (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ |complex_of_real(σ - &1) * g(σ) - complex_of_real(r)| < ε)",
			By(
				guards,
				difference,
				density,
				complex_topology.ScaledLimitBoundedDifference.At(
					f,
					g,
					arg.TermAs[Real]("&1"),
					arg.TermAs[Real]("&1"),
					M,
					arg.TermAs[Complex]("complex_of_real(r)"),
					ε)))
		arg.Show(
			"read the prime series in the stated coefficients",
			By(limit, gDef, primeCast))
	}),
	Reading: "This is Dirichlet's density statement in its weighted form: the " +
		"primes of the progression, weighted by log p · p^(−σ), carry the share " +
		"1/φ(q) of the pole. The form with p^(−σ) and log(1/(σ − 1)) is not stated.",
})}

// PrimesInProgression — Dirichlet's theorem: for q > 0 and a coprime to q
// there are infinitely many primes p ≡ a mod q.
var PrimesInProgression = primesInProgressionThm{family.Add(registry.ProofEntry{
	Name: "PrimesInProgression",
	Key:  "prop_dcb2b9714aee7b68",
	Build: family.Sections(Statement{
		Binders:    "∀q a:num.",
		Hypotheses: []string{"0 < q", "nat_coprime(a, q)"},
		Conclusion: "infinite({p:num | nat_prime(p) ∧ p ≡ a (mod q)})",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A Dirichlet series whose coefficients vanish past N and at 1 is at most
			// twice the sum of their moduli to the right of 1: the sum of moduli
			// bounds every partial sum, and summation by parts does the rest.
			cutoffBounded := ctx.Lemma(Statement{
				Binders: "∀f:(num → complex). ∀N:num. ∀σ:real.",
				Hypotheses: []string{
					"∀n:num. N < n ⇒ f(n) = complex_of_real(&0)",
					"f(1) = complex_of_real(&0)",
					"&1 < σ",
				},
				Conclusion: "|dirichlet_series(f, complex_of_real(σ))| ≤ &2 * Σ_{k∈1 .. N} |f(k)|",
			}, func(
				a *Argument,
				f *Arrow[Nat, Complex],
				N *Expr[Nat],
				σ *Expr[Real],
				vanishes, first, right Fact,
			) {
				partialBound := a.Have(
					"the sum of coefficient moduli up to N bounds every partial sum",
					"∀M:num. |Σ_{k∈1 .. M} f(k)| ≤ Σ_{k∈1 .. N} |f(k)|",
					Derive(func(b *Argument) {
						M := b.FixAs[Nat]("M")
						short, long := b.TermAs[Set[Nat]]("1 .. M"), b.TermAs[Set[Nat]]("1 .. N")
						one := b.TermAs[Nat]("1")
						finM, finN := num_segment.Finite.At(one, M), num_segment.Finite.At(one, N)
						triangle := b.Have(
							"the finite triangle inequality bounds the partial sum by the sum of moduli",
							"|Σ_{k∈1 .. M} f(k)| ≤ Σ_{k∈1 .. M} |f(k)|",
							By(finM, complex_series.AbsSumLessEq.At(short, f)))
						signs := b.Have(
							"terms present only on the left vanish and terms present only on the right are nonnegative",
							"(∀n:num. n ∈ (1 .. M) ∖ (1 .. N) ⇒ |f(n)| ≤ &0) ∧ (∀n:num. n ∈ (1 .. N) ∖ (1 .. M) ⇒ &0 ≤ |f(n)|)",
							SplitConj(
								Case(
									"terms after the cutoff have modulus zero",
									Derive(func(c *Argument) {
										n := c.FixAs[Nat]("n")
										leftOnly := c.Assume()
										above := c.Have(
											"n lies above N",
											"¬(n ≤ N)",
											BySets(leftOnly))
										past := c.Have(
											"n exceeds the cutoff",
											"N < n",
											ByArith(above))
										c.Show(
											"the vanishing coefficient has modulus zero",
											By(
												vanishes.At(n),
												past,
												complex_abs.AbsEqZero.At(c.TermAs[Complex]("f(n)")),
												real_order_ring.LessEqRefl))
									})),
								Case(
									"moduli are nonnegative",
									By(complex_abs.AbsNonneg))))
						majorant := b.Have(
							"the sum up to N therefore bounds the sum of moduli up to M",
							"Σ_{k∈1 .. M} |f(k)| ≤ Σ_{k∈1 .. N} |f(k)|",
							By(
								finM,
								finN,
								signs,
								real_sum.SubsetSigned.At(short, long, b.TermAs[Fun[Nat, Real]]("λn:num. |f(n)|"))))
						b.Show(
							"combine the triangle inequality with the finite majorant",
							ByArith(triangle, majorant))
					}))
				s := a.TermAs[Complex]("complex_of_real(σ)")
				one := a.TermAs[Nat]("1")
				guards := a.Have(
					"the real part and the first index are positive",
					"&0 < re(complex_of_real(σ)) ∧ 0 < 1",
					ByArith(right, complex_field.PartsOfReal.At(σ)))
				v, sum := a.ObtainAs[Complex](
					"summation by parts bounds the remainder after index one",
					"∃v:complex. "+
						"    dirichlet_sums(f, complex_of_real(σ), v) ∧ "+
						"    |v - Σ_{k∈1 .. 1} f(k) * complex_cpow(&k, -complex_of_real(σ))| ≤ "+
						"    &2 * "+
						"    (Σ_{k∈1 .. N} |f(k)|) * "+
						"    |complex_of_real(σ)| / "+
						"    (re(complex_of_real(σ)) * real_rpow(&1, re(complex_of_real(σ))))",
					By(
						partialBound,
						guards,
						dirichlet_series.BoundedSumsConverge.At(f, a.TermAs[Real]("Σ_{k∈1 .. N} |f(k)|"), s, one)),
					Named("v"))
				initial := a.Have(
					"the first term contributes zero",
					"(Σ_{k∈1 .. 1} f(k) * complex_cpow(&k, -complex_of_real(σ))) = complex_of_real(&0)",
					By(
						first,
						monoidal.IntervalPoint.Read(comm_ring.MonoidalAdd.Read(complex_field.CommRing)).At(one,
							a.TermAs[Fun[Nat, Complex]]("λk:num. f(k) * complex_cpow(&k, -complex_of_real(σ))")),
						comm_ring.MulLeftZero.Read(complex_field.CommRing)))
				bound := a.Have(
					"the modulus and real part of the positive argument cancel",
					"&2 * "+
						"(Σ_{k∈1 .. N} |f(k)|) * "+
						"|complex_of_real(σ)| / "+
						"(re(complex_of_real(σ)) * real_rpow(&1, re(complex_of_real(σ)))) = "+
						"&2 * Σ_{k∈1 .. N} |f(k)|",
					ByArith(
						right,
						complex_field.PartsOfReal.At(σ),
						complex_abs.AbsOfReal.At(σ),
						real_rpow.RpowOneBase.At(a.TermAs[Real]("re(complex_of_real(σ))"))))
				a.Show(
					"the value of the series is its sum v",
					ByArith(initial, bound, sum, dirichlet_series.DirichletSeriesValue.At(f, s, v)))
			})
			return ctx.Theorem(headline, func(arg *Argument, q, a *Expr[Nat], qPositive, coprime Fact) {
				arg.Do(Unfold(finite_set.InfiniteDef))
				finite := arg.SupposeNot()
				N, cutoff := arg.ObtainAs[Nat](
					"a finite set of natural numbers lies in an initial segment",
					"∃N:num. {p:num | nat_prime(p) ∧ p ≡ a (mod q)} ⊆ 0 .. N",
					By(finite, num_segment.FiniteIffBounded),
					Named("N"))
				f, coefficient := arg.LetAs[Fun[Nat, Complex]]("f",
					"λp:num. COND(nat_prime(p) ∧ p ≡ a (mod q), complex_of_real(log(&p)), complex_of_real(&0))")
				vanishes := arg.Have(
					"the coefficients vanish past the initial segment",
					"∀n:num. N < n ⇒ f(n) = complex_of_real(&0)",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						past := b.Assume()
						outside := b.Have(
							"n is above the segment",
							"¬(n ≤ N)",
							ByArith(past))
						notInProgression := b.Have(
							"a prime in the residue class would be in the segment",
							"¬(nat_prime(n) ∧ n ≡ a (mod q))",
							BySets(outside, cutoff))
						b.Show(
							"the coefficient outside the progression is zero",
							Simp(Fwd(coefficient), Fwd(notInProgression)),
							Basic())
					}))
				first := arg.Have(
					"log one makes the first coefficient zero",
					"f(1) = complex_of_real(&0)",
					Simp(Fwd(coefficient), Fwd(real_exp_log.LogOne)),
					Basic())
				r, share := arg.LetAs[Real]("r", "&1 / &(totient(q))")
				_, bound := arg.LetAs[Real]("B", "&2 * Σ_{k∈1 .. N} |f(k)|")
				positive := arg.Have(
					"the share of the pole is positive",
					"&0 < r",
					ByArith(qPositive, share, totient.TotientPositive.At(q)))
				δ, near := arg.ObtainAs[Real](
					"near one the scaled series is within half the pole share of that share",
					"∃δ:real. "+
						"    &0 < δ ∧ "+
						"    (∀s:real. "+
						"        &1 < s ∧ s < &1 + δ ⇒ "+
						"        |complex_of_real(s - &1) * dirichlet_series(f, complex_of_real(s)) - "+
						"        complex_of_real(r)| < "+
						"        r / &2)",
					ByArith(
						qPositive,
						coprime,
						positive,
						coefficient,
						share,
						ProgressionPrimeDensity.At(q, a, arg.TermAs[Real]("r / &2"))),
					Named("δ"))
				nonnegative := arg.Have(
					"B is twice a sum of moduli, so it is nonnegative",
					"&0 ≤ B",
					ByArith(
						bound,
						complex_abs.AbsNonneg,
						real_sum.Nonneg.At(arg.TermAs[Set[Nat]]("1 .. N"), arg.TermAs[Fun[Nat, Real]]("λk:num. |f(k)|"))))
				σ, point := arg.LetAs[Real]("σ", "&1 + min(δ, r) / (&2 * (B + &1))")
				reaches := arg.Have(
					"the chosen point is in the density interval and its excess over one makes the bound small",
					"&1 < σ ∧ σ < &1 + δ ∧ (σ - &1) * B ≤ r / &2",
					ByArith(nonnegative, positive, near, point, real_sup_inf.RealMinDef.At(δ, r)))
				z, scaled := arg.LetAs[Complex](
					"z", "complex_of_real(σ - &1) * dirichlet_series(f, complex_of_real(σ))")
				small := arg.Have(
					"the scaled series is at most half the pole share in modulus",
					"|z| ≤ r / &2",
					ByArith(
						bound,
						vanishes,
						first,
						At(cutoffBounded, f, N, σ),
						reaches,
						scaled,
						complex_abs.AbsMul.At(
							arg.TermAs[Complex]("complex_of_real(σ - &1)"),
							arg.TermAs[Complex]("dirichlet_series(f, complex_of_real(σ))")),
						complex_abs.AbsOfReal.At(arg.TermAs[Real]("σ - &1"))))
				nearShare := arg.Have(
					"but the density law puts the scaled series within half the pole share of r",
					"|z - complex_of_real(r)| < r / &2",
					By(Normalized, near, reaches, scaled))
				arg.Show(
					"the two bounds contradict the reverse triangle inequality",
					ByArith(
						small,
						nearShare,
						positive,
						complex_abs.AbsOfReal.At(r),
						complex_abs.AbsTriangleReverse.At(z, arg.TermAs[Complex]("complex_of_real(r)"))))
			})
		}),
	Reading: "Coprimality is necessary: a prime p ≡ a mod q with gcd(a, q) = d > 1 is " +
		"divisible by d, so there is at most one. q = 1 is the infinitude of the primes.",
})}
