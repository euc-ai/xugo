// mangoldt_density.go — the series of Λ over the progression n ≡ a mod q
// as σ decreases to 1. The orthogonality of the characters mod q writes it
// as the average, over the characters χ, of conj(χ(a)) times the series of
// Λ·χ (ProgressionMangoldtSeries). For the principal character that series
// differs from the series of Λ by a bounded amount, so it carries the pole
// of ζ's logarithmic derivative (PrincipalMangoldtPole); for every other
// character it is −L′/L for the L-series L of χ, which extends continuously
// to 1 because L does not vanish there
// (dirichlet_l_function.NonprincipalMangoldtContinuous). So
// (σ − 1) times the series over the progression tends to 1/φ(q)
// (ProgressionMangoldtDensity).

package primes_in_progressions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_l_function"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ProgressionMangoldtSeries — for a coprime to q and Re s > 1, the series of
// Λ·χ summed over the characters χ mod q, each weighted by conj(χ(a)), is
// φ(q) times the series of Λ over the progression n ≡ a mod q: the
// orthogonality of the characters isolates the residue class, coefficient
// by coefficient.
var ProgressionMangoldtSeries = progressionMangoldtSeriesThm{family.Add(registry.ProofEntry{
	Name: "ProgressionMangoldtSeries",
	Key:  "prop_551021568d5758b8",
	Build: family.Theorem(Statement{
		Binders:    "∀q a:num. ∀s:complex.",
		Hypotheses: []string{"0 < q", "nat_coprime(a, q)", "&1 < re(s)"},
		Conclusion: "Σ_{χ∈{χ:(num → complex) | dirichlet_character(q, χ)}} conj(χ(a)) * " +
			"dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), s) = " +
			"complex_of_real(&(totient(q))) * " +
			"dirichlet_series( " +
			"    λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)), s)",
	}, func(arg *Argument, q, a *Expr[Nat], s *Expr[Complex], guards Fact) {
		S, characters := arg.LetAs[Set[Fun[Nat, Complex]]](
			"S", "{χ:(num → complex) | dirichlet_character(q, χ)}")
		_, twists := arg.LetAs[Fun[Fun[Nat, Complex], Fun[Nat, Complex]]]("H",
			"λχ:(num → complex). λn:num. complex_of_real(von_mangoldt(n)) * χ(n)")
		F, weighted := arg.LetAs[Fun[Fun[Nat, Complex], Fun[Nat, Complex]]]("F",
			"λχ:(num → complex). λn:num. conj(χ(a)) * H(χ,n)")
		V, values := arg.LetAs[Fun[Fun[Nat, Complex], Complex]]("V",
			"λχ:(num → complex). conj(χ(a)) * dirichlet_series(H(χ),s)")
		G, mask := arg.LetAs[Fun[Nat, Complex]]("G",
			"λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), complex_of_real(&0))")
		T, totientValue := arg.LetAs[Complex]("T", "complex_of_real(&totient(q))")
		finite := arg.Have(
			"there are finitely many characters",
			"finite(S)",
			By(guards, characters, dirichlet_character.CharacterCount.At(q)))
		rows := arg.Have(
			"each weighted character series sums to its weighted value",
			"∀χ:(num → complex). χ ∈ S ⇒ dirichlet_sums(F(χ), s, V(χ))",
			Derive(func(b *Argument) {
				χ := b.FixAs[Fun[Nat, Complex]]("χ")
				inS := b.Assume()
				character := b.Have(
					"membership gives the character laws",
					"dirichlet_character(q,χ)",
					BySets(inS, characters))
				bound := b.Have(
					"the modulus of each twisted coefficient is at most the logarithm",
					"∀n:num. |H(χ,n+1)| ≤ log(&(n+1))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						m := c.TermAs[Nat]("n+1")
						c.Show(
							"the Mangoldt coefficient is nonnegative and the character has modulus at most one",
							ByArith(
								guards,
								twists,
								character,
								dirichlet_character.CharacterAbsLessEqOne.At(q, m, χ),
								prime_distribution.MangoldtNonneg.At(m),
								prime_distribution.MangoldtLessEqLog.At(m)))
					}))
				Hχ := b.TermAs[Fun[Nat, Complex]]("H(χ)")
				v := b.TermAs[Complex]("dirichlet_series(H(χ),s)")
				w := b.TermAs[Complex]("conj(χ(a))")
				summed := b.Have(
					"the twisted series converges to its value",
					"dirichlet_sums(H(χ), s, dirichlet_series(H(χ),s))",
					By(guards, bound, dirichlet_series.LogBoundedCoefficientsConverge.At(Hχ, s)))
				scaled := b.Have(
					"scale the coefficients and the sum by the same weight",
					"dirichlet_sums(λn:num. conj(χ(a)) * H(χ,n),s,conj(χ(a)) * dirichlet_series(H(χ),s))",
					By(summed, dirichlet_series.DirichletSumsScale.At(Hχ, s, v, w)))
				b.Show(
					"substitute the weighted coefficients and values",
					By(Normalized, scaled, weighted, values))
			}))
		combined := arg.Have(
			"sum the weighted character series over the finite set",
			"dirichlet_sums(λn:num. Σ_{χ∈S} F(χ,n), s, Σ_{χ∈S} V(χ))",
			By(finite, rows, dirichlet_series.DirichletSumsFiniteSum.At(F, V, s, S)))
		maskBound := arg.Have(
			"the retained coefficients also have modulus at most the logarithm",
			"∀n:num. |G(n+1)| ≤ log(&(n+1))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				m := b.TermAs[Nat]("n+1")
				nonneg := prime_distribution.MangoldtNonneg.At(m)
				upper := prime_distribution.MangoldtLessEqLog.At(m)
				b.Cases(b.Term("n+1 ≡ a (mod q)"))
				b.When(
					"in the residue class",
					func(c *Argument, inClass Fact) {
						c.Show(
							"the coefficient is the Mangoldt value",
							ByArith(inClass, mask, nonneg, upper))
					})
				b.Otherwise(
					"outside the residue class",
					func(c *Argument, offClass Fact) {
						c.Show(
							"zero is at most the nonnegative logarithm",
							ByArith(offClass, mask, nonneg, upper))
					})
			}))
		gv := arg.TermAs[Complex]("dirichlet_series(G,s)")
		masked := arg.Have(
			"the series of the retained coefficients converges to its value",
			"dirichlet_sums(G,s,dirichlet_series(G,s))",
			By(guards, maskBound, dirichlet_series.LogBoundedCoefficientsConverge.At(G, s)))
		scaled := arg.Have(
			"multiply the progression series by the totient",
			"dirichlet_sums(λn:num. T * G(n),s,T * dirichlet_series(G,s))",
			By(masked, dirichlet_series.DirichletSumsScale.At(G, s, gv, T)))
		ring := complex_field.CommRing
		addition := comm_ring.MonoidalAdd.Read(ring)
		coefficients := arg.Have(
			"orthogonality identifies the combined coefficients",
			"(λn:num. Σ_{χ∈S} F(χ,n)) = (λn:num. T * G(n))",
			Funext(),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				reordered := b.Have(
					"put the common Mangoldt factor on the left",
					"(λχ:(num → complex). F(χ,n)) = "+
						"(λχ:(num → complex). complex_of_real(von_mangoldt(n)) * (conj(χ(a)) * χ(n)))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Fun[Nat, Complex]]("χ")
						c.Show(
							"commute and associate the three factors",
							ByArith(twists, weighted))
					}))
				evaluation := b.TermAs[Fun[Fun[Nat, Complex], Complex]]("λχ:(num → complex). conj(χ(a)) * χ(n)")
				multiply := b.TermAs[Fun[Complex, Complex]]("λz:complex. complex_of_real(von_mangoldt(n)) * z")
				factored := b.Have(
					"pull the common factor out of the character sum",
					"complex_of_real(von_mangoldt(n)) * (Σ_{χ∈S} conj(χ(a)) * χ(n)) = "+
						"Σ_{χ∈S} complex_of_real(von_mangoldt(n)) * (conj(χ(a)) * χ(n))",
					By(
						finite,
						monoidal.Homomorphic.Read(addition).At(
							b.TermAs[Op[Complex]]("complex_add"), multiply, S, evaluation),
						addition,
						comm_ring.NeutralAdd.Read(ring),
						comm_ring.LeftDistrib.Read(ring),
						comm_ring.MulRightZero.Read(ring)))
				orthogonal := b.Have(
					"the character sum is the totient exactly in the residue class",
					"Σ_{χ∈S} conj(χ(a)) * χ(n) = COND(n ≡ a (mod q), T, complex_of_real(&0))",
					By(guards, characters, totientValue, dirichlet_character.CharacterOrthogonality.At(q, a, n)))
				indicator := b.Have(
					"multiply the evaluated sum by the Mangoldt coefficient",
					"Σ_{χ∈S} F(χ,n) = complex_of_real(von_mangoldt(n)) * COND(n ≡ a (mod q), T, complex_of_real(&0))",
					By(reordered, factored, orthogonal))
				b.Cases(b.Term("n ≡ a (mod q)"))
				b.When(
					"inside the residue class",
					func(c *Argument, inClass Fact) {
						c.Show(
							"both products use the same coefficient",
							ByArith(inClass, mask, indicator))
					})
				b.Otherwise(
					"outside the residue class",
					func(c *Argument, offClass Fact) {
						c.Show(
							"both products are zero",
							ByArith(offClass, mask, indicator))
					})
			}))
		// The two sums use the same coefficient sequence.
		coeff := arg.TermAs[Fun[Nat, Complex]]("λn:num. Σ_{χ∈S} F(χ,n)")
		gCoeff := arg.TermAs[Fun[Nat, Complex]]("λn:num. T * G(n)")
		combValue := arg.TermAs[Complex]("Σ_{χ∈S} V(χ)")
		gValue := arg.TermAs[Complex]("T * dirichlet_series(G,s)")
		equal := arg.Have(
			"read the two equal series at their sums",
			"Σ_{χ∈S} V(χ) = T * dirichlet_series(G,s)",
			By(
				combined,
				scaled,
				coefficients,
				dirichlet_series.DirichletSeriesValue.At(coeff, s, combValue),
				dirichlet_series.DirichletSeriesValue.At(gCoeff, s, gValue)))
		arg.Show(
			"restore the definitions of the coefficients and weights",
			By(equal, characters, twists, values, mask, totientValue))
	}),
	Reading: "Orthogonality of characters is what isolates one residue " +
		"class. a must be coprime to q: otherwise every conj(χ(a)) is 0 " +
		"and the class holds at most the powers of the primes dividing q.",
})}

// PrincipalMangoldtPole — the scaled Mangoldt series over the numbers
// coprime to q tends to one as the real argument decreases to one.
var PrincipalMangoldtPole = principalMangoldtPoleThm{family.Add(registry.ProofEntry{
	Name: "PrincipalMangoldtPole",
	Key:  "prop_6fb1def2128ecb1d",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀ε:real.",
		Hypotheses: []string{
			"0 < q",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀σ:real. " +
			"        &1 < σ ∧ σ < &1 + δ ⇒ " +
			"        |complex_of_real(σ - &1) * " +
			"        dirichlet_series(λn:num. " +
			"                COND(nat_coprime(n, q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)), " +
			"            complex_of_real(σ)) - " +
			"        complex_of_real(&1)| < " +
			"        ε",
	}, func(a *Argument, q *Expr[Nat], ε *Expr[Real], guards Fact) {
		M, higherPowers := a.UnpackAs[Real](prime_distribution.MangoldtPrimePowersConverge, "M")
		G, coprimeCoefficients := a.LetAs[Fun[Nat, Real]](
			"G", "λn:num. COND(nat_coprime(n, q), von_mangoldt(n), &0)")
		K, cutoff := a.LetAs[Fun[Nat, Real]]("K", "λn:num. COND(n + 1 ≤ q, von_mangoldt(n + 1), &0)")
		k, finiteSum := a.LetAs[Real]("k", "Σ_{n∈0 .. q} K(n)")
		vanishes := a.Have(
			"the majorant for the omitted primes is zero beyond the modulus",
			"(λn:num. K(n + q + 1)) = (λn:num. &0)",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the shifted index exceeds the cutoff",
					ByArith(cutoff))
			}))
		kSums := a.Have(
			"the finite majorant therefore sums to k",
			"real_sums(K, k)",
			ByArith(vanishes, finiteSum, real_series.SumsOffset.At(K, k, q), real_series.SumsZero))
		difference := a.Have(
			"omitting numbers that are not coprime changes the series by a bounded amount",
			Statement{
				Binders:    "∀σ:real.",
				Hypotheses: []string{"&1 < σ"},
				Conclusion: "|dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)), complex_of_real(σ)) - " +
					"dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(σ))| ≤ " +
					"M + k",
			},
			Derive(func(b *Argument) {
				σ := b.FixAs[Real]("σ")
				right := b.Assume()
				_, weight := b.LetAs[Fun[Nat, Real]]("W", "λn:num. real_rpow(&n, -σ)")
				T, higherPowerTerms := b.LetAs[Fun[Nat, Real]](
					"T", "λn:num. COND(nat_prime(n + 1), &0, von_mangoldt(n + 1) * real_rpow(&(n + 1), -&1))")
				U, majorantTerms := b.LetAs[Fun[Nat, Real]]("U", "λn:num. T(n) + K(n)")
				logBound := b.Have(
					"the Mangoldt coefficients are at most the logarithm",
					"∀n:num. |von_mangoldt(n + 1)| ≤ log(&(n + 1))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						n1 := c.TermAs[Nat]("n + 1")
						c.Show(
							"the Mangoldt value lies between zero and the logarithm",
							ByArith(prime_distribution.MangoldtNonneg.At(n1), prime_distribution.MangoldtLessEqLog.At(n1)))
					}))
				removedMajorized := b.Have(
					"the higher prime powers plus the finite majorant dominate all omitted terms",
					"∀n:num. |von_mangoldt(n + 1) - G(n + 1)| * real_rpow(&(n + 1), -σ) ≤ U(n)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						n1 := c.TermAs[Nat]("n + 1")
						base := c.TermAs[Real]("&(n + 1)")
						exponent := c.TermAs[Real]("-σ")
						positive := c.Have(
							"the shifted base is positive",
							"&0 < &(n + 1)",
							ByArith())
						nonnegative := c.Have(
							"the Mangoldt value is nonnegative and its weight positive",
							"&0 ≤ von_mangoldt(n + 1) ∧ &0 < W(n + 1)",
							ByArith(
								positive,
								weight,
								prime_distribution.MangoldtNonneg.At(n1),
								real_rpow.RpowPositive.At(base, exponent)))
						c.Cases(c.Term("nat_prime(n + 1) ∧ ¬nat_coprime(n + 1, q)"))
						c.When(
							"an omitted prime divides q",
							func(d *Argument, omitted Fact) {
								divides := d.Have(
									"a prime fails coprimality exactly when it divides q",
									"(n + 1) ∣ q",
									By(omitted, nat_prime.PrimeCoprimeIffNotDivides.At(n1)))
								inside := d.Have(
									"the omitted prime is no larger than the positive modulus",
									"n + 1 ≤ q",
									ByArith(guards, divides, nat_divides.DividesLessEq.At(n1, q)))
								weightAtMostOne := d.Have(
									"monotonicity in the exponent bounds the weight by one",
									"W(n + 1) ≤ &1",
									ByArith(
										right,
										weight,
										real_rpow.RpowLessEqExponent.At(base, exponent, d.TermAs[Real]("&0")),
										real_rpow.RpowZeroExponent.At(base)))
								d.Show(
									"the finite majorant includes the full unweighted term",
									ByArith(
										majorantTerms,
										higherPowerTerms,
										coprimeCoefficients,
										cutoff,
										weight,
										nonnegative,
										omitted,
										inside,
										weightAtMostOne))
							})
						c.Otherwise(
							"the point is coprime or it is not a prime",
							func(d *Argument, other Fact) {
								negOne := d.TermAs[Real]("-&1")
								atOne := d.Have(
									"the weight at σ is at most the weight at one",
									"W(n + 1) ≤ real_rpow(&(n + 1), -&1)",
									ByArith(right, weight, real_rpow.RpowLessEqExponent.At(base, exponent, negOne)))
								d.Show(
									"the omitted term is zero or at most a term of the higher prime powers",
									ByArith(
										majorantTerms,
										higherPowerTerms,
										coprimeCoefficients,
										cutoff,
										weight,
										nonnegative,
										other,
										atOne,
										real_rpow.RpowNonneg.At(base, negOne),
										real_order_ring.LessEqMulLeft.At(
											d.TermAs[Real]("von_mangoldt(n + 1)"),
											d.TermAs[Real]("W(n + 1)"),
											d.TermAs[Real]("real_rpow(&(n + 1), -&1)"))))
							})
					}))
				majorantSums := b.Have(
					"the two majorants sum to M plus k",
					"real_sums(U, M + k)",
					By(
						Normalized,
						majorantTerms,
						higherPowers,
						higherPowerTerms,
						kSums,
						real_series.SumsAdd.At(T, K, M, k)))
				b.Show(
					"the series differ by at most the sum of the majorant",
					By(
						right,
						logBound,
						removedMajorized,
						majorantSums,
						dirichlet_series.DirichletSeriesDifferenceBound.At(
							b.TermAs[Fun[Nat, Real]]("von_mangoldt"),
							G,
							U,
							σ,
							b.TermAs[Real]("M + k"))))
			}))
		embedded := a.Have(
			"embed the coefficients of the coprime part",
			"(λn:num. complex_of_real(G(n))) = "+
				"(λn:num. COND(nat_coprime(n, q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the real embedding respects the coprimality indicator",
					By(
						coprimeCoefficients,
						complex_field.OfRealCond.At(
							b.TermAs[Bool]("nat_coprime(n, q)"), b.TermAs[Real]("von_mangoldt(n)"), b.TermAs[Real]("&0"))))
			}))
		f, fDef := a.LetAs[Fun[Real, Complex]](
			"f", "λσ:real. dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)), complex_of_real(σ))")
		g, gDef := a.LetAs[Fun[Real, Complex]](
			"g", "λσ:real. dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(σ))")
		pole := a.Have(
			"the full scaled series tends to one",
			Statement{
				Binders:    "∀η:real.",
				Hypotheses: []string{"&0 < η"},
				Conclusion: "∃d:real. " +
					"    &0 < d ∧ " +
					"    (∀σ:real. &1 < σ ∧ σ < &1 + d ⇒ |complex_of_real(σ - &1) * f(σ) - complex_of_real(&1)| < η)",
			},
			By(fDef, riemann_zeta.MangoldtSeriesPole))
		limit := a.Have(
			"the bounded difference leaves the scaled limit unchanged",
			"∃δ:real. "+
				"    &0 < δ ∧ "+
				"    (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ |complex_of_real(σ - &1) * g(σ) - complex_of_real(&1)| < ε)",
			By(
				guards,
				difference,
				pole,
				complex_topology.ScaledLimitBoundedDifference.At(
					f,
					g,
					a.TermAs[Real]("&1"),
					a.TermAs[Real]("&1"),
					a.TermAs[Real]("M + k"),
					a.TermAs[Complex]("complex_of_real(&1)"),
					ε)))
		a.Show(
			"read the restricted series in the stated coefficients",
			By(limit, gDef, embedded))
	}),
	Reading: "The omitted primes divide q and contribute a finite majorant. " +
		"The remaining omitted terms are among the higher prime powers, whose " +
		"series at σ = 1 converges and dominates them at every σ > 1.",
})}

// ProgressionMangoldtDensity — for a coprime to q, (σ − 1) times the
// Mangoldt series in the progression tends to 1/φ(q) as σ decreases to one.
var ProgressionMangoldtDensity = progressionMangoldtDensityThm{family.Add(registry.ProofEntry{
	Name: "ProgressionMangoldtDensity",
	Key:  "prop_3d8a803e1c94c658",
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
			"        dirichlet_series( " +
			"            λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)), " +
			"            complex_of_real(σ)) - " +
			"        complex_of_real(&1 / &(totient(q)))| < " +
			"        ε",
	},
		func(arg *Argument, q, a *Expr[Nat], ε *Expr[Real], guards Fact) {
			P, principalDef := arg.LetAs[Fun[Nat, Complex]](
				"P", "λn:num. COND(nat_coprime(n, q), complex_of_real(&1), complex_of_real(&0))")
			S, characters := arg.LetAs[Set[Fun[Nat, Complex]]](
				"S", "{χ:(num → complex) | dirichlet_character(q, χ)}")
			R, others := arg.LetAs[Set[Fun[Nat, Complex]]]("R", "S ∖ {P}")
			W, weighted := arg.LetAs[Fun[Fun[Nat, Complex], Fun[Real, Complex]]]("W",
				"λχ:(num → complex). λσ:real. "+
					"    conj(χ(a)) * "+
					"    dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), complex_of_real(σ))")
			finiteS := arg.Have(
				"the characters of a positive modulus form a finite set",
				"finite(S)",
				By(guards, characters, dirichlet_character.CharacterCount.At(q)))
			finiteR := arg.Have(
				"the nonprincipal characters form a finite set",
				"finite(R)",
				BySets(finiteS, others, finite_set.FiniteSubset.At(R, S)))
			principal := arg.Have(
				"the coprimality indicator is a Dirichlet character",
				"dirichlet_character(q, P)",
				By(principalDef, dirichlet_character.PrincipalCharacter.At(q)))
			inS := arg.Have(
				"the principal character belongs to S",
				"P ∈ S",
				BySets(characters, principal))
			outside := arg.Have(
				"the principal character is excluded from R",
				"P ∉ R",
				BySets(others))
			separate := arg.Have(
				"the principal character and R exhaust S",
				"S = insert(P, R)",
				BySets(inS, others))
			pointwise := arg.Have(
				"each of the nonprincipal summands is bounded near one",
				"∀χ:(num → complex). χ ∈ R ⇒ ∃d M:real. &0 < d ∧ (∀σ:real. &1 < σ ∧ σ < &1 + d ⇒ |W(χ, σ)| ≤ M)",
				Derive(func(b *Argument) {
					χ := b.FixAs[Fun[Nat, Complex]]("χ")
					inR := b.Assume()
					character := b.Have(
						"χ is a Dirichlet character",
						"dirichlet_character(q, χ)",
						BySets(inR, others, characters))
					distinct := b.Have(
						"χ differs from the principal character",
						"χ ≠ P",
						BySets(inR, others))
					wouldBePrincipal := b.Have(
						"a character equal to one on the coprime numbers is principal",
						"(¬∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ complex_of_real(&1)) ⇒ χ = P",
						Derive(func(c *Argument) {
							denial := c.Assume()
							c.Show(
								"the two functions agree pointwise",
								Funext(),
								Derive(func(d *Argument) {
									d.FixAs[Nat]("n")
									d.Cases(d.Term("nat_coprime(n, q)"))
									d.When(
										"both values are one on the coprime numbers",
										func(e *Argument, coprime Fact) {
											e.Show(
												"the hypothesized agreement and the indicator give one",
												By(denial, principalDef, coprime))
										})
									d.Otherwise(
										"both values vanish elsewhere",
										func(e *Argument, notCoprime Fact) {
											e.Show(
												"a character vanishes off the coprime numbers, and so does the indicator",
												By(
													notCoprime,
													principalDef,
													character,
													dirichlet_character.CharacterEqZero.At(q, e.TermAs[Nat]("n"), χ)))
										})
								}))
						}))
					nonprincipal := b.Have(
						"a different character has a coprime input with value different from one",
						"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ complex_of_real(&1)",
						By(distinct, wouldBePrincipal))
					weight := b.Have(
						"the character weight has modulus one at the given coprime residue",
						"|conj(χ(a))| = &1",
						By(
							Normalized,
							character,
							guards,
							dirichlet_character.CharacterUnitModulus.At(q, a, χ),
							complex_abs.AbsConj.At(b.TermAs[Complex]("χ(a)"))))
					Q, regular := b.ObtainAs[Fun[Complex, Complex]](
						"the nonprincipal Mangoldt series extends continuously to one",
						"∃Q:(complex → complex). "+
							"    complex_continuous_at(Q, complex_of_real(&1)) ∧ "+
							"    (∀s:complex. "+
							"        &1 < re(s) ⇒ Q(s) = dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), s))",
						By(character, guards, nonprincipal, dirichlet_l_function.NonprincipalMangoldtContinuous.At(q, χ)),
						Named("Q"))
					regularity := b.Conjuncts(
						regular,
						"Q is continuous at one",
						"Q is the series to the right of one")
					continuous, agrees := regularity[0], regularity[1]
					one := b.TermAs[Complex]("complex_of_real(&1)")
					d, ball := b.ObtainAs[Real](
						"in a ball about one Q changes by less than one",
						"∃d:real. "+
							"    &0 < d ∧ (∀z:complex. |z - complex_of_real(&1)| < d ⇒ |Q(z) - Q(complex_of_real(&1))| < &1)",
						By(continuous, complex_topology.ComplexContinuousAtDef.At(Q, one)),
						Named("d"))
					b.Show(
						"a modulus-one weight keeps the bound of Q near one",
						Witness(d),
						Witness(b.TermAs[Real]("|Q(complex_of_real(&1))| + &1")),
						SplitConj(Case(
							"the radius is positive",
							By(ball)), Case(
							"the weighted term stays bounded",
							Derive(func(c *Argument) {
								σ := c.FixAs[Real]("σ")
								near := c.Assume()
								s := c.TermAs[Complex]("complex_of_real(σ)")
								nearOne := c.Have(
									"Q at σ differs from its value at one by less than one",
									"|Q(complex_of_real(σ)) - Q(complex_of_real(&1))| < &1",
									ByArith(ball, near, complex_abs.AbsOfRealSub.At(σ, c.TermAs[Real]("&1"))))
								bounded := c.Have(
									"the reverse triangle inequality bounds Q at σ",
									"|Q(complex_of_real(σ))| ≤ |Q(complex_of_real(&1))| + &1",
									ByArith(
										nearOne,
										complex_abs.AbsTriangleReverse.At(
											c.TermAs[Complex]("Q(complex_of_real(σ))"), c.TermAs[Complex]("Q(complex_of_real(&1))"))))
								series := c.Have(
									"the series at σ is Q at σ, so the bound holds for it",
									"|dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), complex_of_real(σ))| ≤ "+
										"|Q(complex_of_real(&1))| + &1",
									By(bounded, near, complex_field.PartsOfReal.At(σ), agrees.At(s)))
								c.Show(
									"take the modulus of the product",
									ByArith(
										series,
										weight,
										weighted,
										complex_abs.AbsMul.At(c.TermAs[Complex]("conj(χ(a))"), c.TermAs[Complex](
											"dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), complex_of_real(σ))"))))
							}))))
				}))
			e, _, remainder := arg.Obtain2As[Real, Real](
				"finitely many nonprincipal terms have a bounded sum near one",
				"∃e M:real. &0 < e ∧ (∀σ:real. &1 < σ ∧ σ < &1 + e ⇒ |Σ_{χ∈R} W(χ, σ)| ≤ M)",
				By(finiteR, pointwise, complex_topology.FiniteSumBoundedNear.At(R, W, arg.TermAs[Real]("&1"))),
				Named("e", "M"))
			r, reciprocal := arg.LetAs[Real]("r", "&1 / &(totient(q))")
			_, principalSeries := arg.LetAs[Fun[Real, Complex]]("ΛP",
				"λσ:real. "+
					"    dirichlet_series( "+
					"        λn:num. COND(nat_coprime(n, q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)), "+
					"        complex_of_real(σ))")
			f, scaledSeries := arg.LetAs[Fun[Real, Complex]]("f", "λσ:real. complex_of_real(r) * ΛP(σ)")
			g, progression := arg.LetAs[Fun[Real, Complex]]("g",
				"λσ:real. "+
					"    dirichlet_series( "+
					"        λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)), "+
					"        complex_of_real(σ))")
			conjugateOne := arg.Have(
				"the principal character's conjugate weight is one",
				"conj(P(a)) = complex_of_real(&1)",
				By(guards, principalDef, complex_field.ConjOfReal.At(arg.TermAs[Real]("&1"))))
			coefficients := arg.Have(
				"multiplication by P restricts the Mangoldt coefficients to the coprime inputs",
				"(λn:num. complex_of_real(von_mangoldt(n)) * P(n)) = "+
					"(λn:num. COND(nat_coprime(n, q), complex_of_real(von_mangoldt(n)), complex_of_real(&0)))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Cases(b.Term("nat_coprime(n, q)"))
					b.When(
						"a coprime coefficient is retained",
						func(c *Argument, yes Fact) {
							c.Show(
								"multiply by one",
								ByArith(principalDef, yes))
						})
					b.Otherwise(
						"the other coefficient vanishes",
						func(c *Argument, no Fact) {
							c.Show(
								"multiply by zero",
								ByArith(principalDef, no))
						})
				}))
			identity := comm_monoid.LeftIdentity.Read(complex_field.MulMonoid)
			weightedPrincipal := arg.Have(
				"the weighted principal term is the series ΛP",
				"∀σ:real. W(P, σ) = ΛP(σ)",
				By(weighted, principalSeries, conjugateOne, coefficients, identity))
			positive := arg.Have(
				"the share of the pole is positive",
				"&0 < r",
				ByArith(reciprocal, guards, totient.TotientPositive.At(q)))
			φ := arg.TermAs[Real]("&totient(q)")
			inverseReal := arg.Have(
				"r is the reciprocal of the number of units",
				"r * &totient(q) = &1",
				ByArith(reciprocal, guards, totient.TotientPositive.At(q)))
			inverse := arg.Have(
				"the embedded factors multiply to one",
				"complex_of_real(r) * complex_of_real(&totient(q)) = complex_of_real(&1)",
				By(Normalized, inverseReal, complex_field.OfRealMul.At(r, φ)))
			scaledLimit := arg.Have(
				"after scaling by r, the principal term tends to r",
				Statement{
					Binders:    "∀η:real.",
					Hypotheses: []string{"&0 < η"},
					Conclusion: "∃d:real. " +
						"    &0 < d ∧ " +
						"    (∀σ:real. &1 < σ ∧ σ < &1 + d ⇒ |complex_of_real(σ - &1) * f(σ) - complex_of_real(r)| < η)",
				},
				Derive(func(b *Argument) {
					η := b.FixAs[Real]("η")
					tolerance := b.Assume()
					d, pole := b.ObtainAs[Real](
						"below some radius d the scaled principal series is within η / r of one",
						"∃d:real. "+
							"    &0 < d ∧ "+
							"    (∀σ:real. "+
							"        &1 < σ ∧ σ < &1 + d ⇒ |complex_of_real(σ - &1) * ΛP(σ) - complex_of_real(&1)| < η / r)",
						ByArith(
							guards,
							positive,
							tolerance,
							principalSeries,
							PrincipalMangoldtPole.At(q, b.TermAs[Real]("η / r"))),
						Named("d"))
					b.Show(
						"the same radius serves the rescaled series",
						Witness(d),
						SplitConj(Case(
							"the radius is positive",
							By(pole)), Case(
							"the rescaled pole has the required error",
							Derive(func(c *Argument) {
								c.FixAs[Real]("σ")
								near := c.Assume()
								_, zDef := c.LetAs[Complex]("z", "complex_of_real(σ - &1)")
								errorBound := c.Have(
									"the principal pole estimate at σ",
									"|z * ΛP(σ) - complex_of_real(&1)| < η / r",
									By(Normalized, near, pole, zDef))
								factored := c.Have(
									"factor the reciprocal out of the principal error",
									"|z * f(σ) - complex_of_real(r)| = |complex_of_real(r) * (z * ΛP(σ) - complex_of_real(&1))|",
									ByArith(scaledSeries))
								unscaledError := c.TermAs[Real]("|z * ΛP(σ) - complex_of_real(&1)|")
								cross := c.Have(
									"cross the positive denominator in the tolerance",
									"|z * ΛP(σ) - complex_of_real(&1)| * r < η",
									By(errorBound, positive, real_order_field.LessThanDivMulLeft.At(unscaledError, η, r)))
								c.Show(
									"the rescaled error is r times the principal error in modulus, so below η",
									ByArith(
										factored,
										cross,
										positive,
										complex_abs.AbsOfReal.At(r),
										complex_abs.AbsMul.At(c.TermAs[Complex]("complex_of_real(r)"),
											c.TermAs[Complex]("z * ΛP(σ) - complex_of_real(&1)"))))
							}))))
				}))
			difference := arg.Have(
				"the nonprincipal sum accounts for a bounded difference from the principal term",
				"∀σ:real. &1 < σ ∧ σ < &1 + e ⇒ |f(σ) - g(σ)| ≤ r * M",
				Derive(func(b *Argument) {
					σ := b.FixAs[Real]("σ")
					near := b.Assume()
					U, remainderDef := b.LetAs[Complex]("U", "Σ_{χ∈R} W(χ, σ)")
					bounded := b.Have(
						"the remaining finite sum is bounded",
						"|U| ≤ M",
						By(Normalized, near, remainder, remainderDef))
					split := b.Have(
						"separate the principal term from the finite sum",
						"Σ_{χ∈S} W(χ, σ) = ΛP(σ) + U",
						By(
							Normalized,
							finiteR,
							outside,
							separate,
							weightedPrincipal.At(σ),
							remainderDef,
							monoidal.OneTurn.Read(comm_ring.MonoidalAdd.Read(complex_field.CommRing)).At(R, P,
								b.TermAs[Fun[Fun[Nat, Complex], Complex]]("λχ:(num → complex). W(χ, σ)"))))
					series := b.Have(
						"character orthogonality identifies the full sum with the progression series",
						"Σ_{χ∈S} W(χ, σ) = complex_of_real(&totient(q)) * g(σ)",
						By(
							near,
							guards,
							characters,
							weighted,
							progression,
							complex_field.PartsOfReal.At(σ),
							ProgressionMangoldtSeries.At(q, a, b.TermAs[Complex]("complex_of_real(σ)"))))
					total := b.Have(
						"equate the two expressions for the full sum",
						"complex_of_real(&totient(q)) * g(σ) = ΛP(σ) + U",
						By(Normalized, split, series))
					gValue := b.Have(
						"divide the full sum by the totient",
						"g(σ) = complex_of_real(r) * (ΛP(σ) + U)",
						By(
							Normalized,
							total,
							inverse,
							identity.At(b.TermAs[Complex]("g(σ)")),
							comm_monoid.Assoc.Read(complex_field.MulMonoid).At(
								b.TermAs[Complex]("complex_of_real(r)"),
								b.TermAs[Complex]("complex_of_real(&totient(q))"),
								b.TermAs[Complex]("g(σ)"))))
					errorTerm := b.Have(
						"the difference consists of the scaled nonprincipal contributions",
						"g(σ) - f(σ) = complex_of_real(r) * U",
						ByArith(gValue, scaledSeries))
					modulus := b.Have(
						"the modulus of a difference is symmetric",
						"|f(σ) - g(σ)| = |complex_of_real(r) * U|",
						By(
							Normalized,
							errorTerm,
							complex_abs.AbsSubComm.At(b.TermAs[Complex]("f(σ)"), b.TermAs[Complex]("g(σ)"))))
					b.Show(
						"the positive scalar multiplies the bound by r",
						ByArith(
							modulus,
							bounded,
							positive,
							complex_abs.AbsOfReal.At(r),
							complex_abs.AbsMul.At(b.TermAs[Complex]("complex_of_real(r)"), U)))
				}))
			arg.Show(
				"a bounded difference preserves the weighted limit",
				By(
					guards,
					remainder,
					scaledLimit,
					difference,
					complex_topology.ScaledLimitBoundedDifference.At(
						f,
						g,
						arg.TermAs[Real]("&1"),
						e,
						arg.TermAs[Real]("r * M"),
						arg.TermAs[Complex]("complex_of_real(r)"),
						ε)))
		}),
	Reading: "Only the principal character contributes to the scaled " +
		"limit. The finite sum of nonprincipal terms stays bounded near one.",
})}
