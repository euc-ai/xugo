// psi.go — the asymptotics of ψ and of the prime-counting function. The
// series of ψ(n)/n − 1 converges at s = 1, so its late blocks have small
// mass; ψ is monotone, so ψ(n) is eventually within ε·n of n on either side,
// ψ(n)/n tends to 1, and π(n)·log n/n with it.

package prime_asymptotics

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// centeredBlockMass — the block estimate both halves of ψ(n) ~ n read: for
// ε > 0 there are δ ≤ 1 with 2δ ≤ ε and a threshold M such that, for each
// n > 0, some D at most δn and at most half of n bounds the mass of every
// block of centered terms past M by D + 1 times δ/(4n). Take δ = 1/q for an
// integer q ≥ 2/ε + 2 and D = div(n, q), which is ⌊δn⌋ with no integer part;
// the centered series converges (PsiSeriesConverges), so its late blocks have
// mass below δ²/8, while δn ≤ D + 1 puts (D + 1)·δ/(4n) at δ²/4 or above.
var centeredBlockMass = centeredBlockMassThm{family.Add(registry.ProofEntry{
	Name: "centeredBlockMass",
	Key:  "prop_9923662eeee36942",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "∃δ:real. ∃M:num. " +
			"    &0 < δ ∧ " +
			"    δ ≤ &1 ∧ " +
			"    &2 * δ ≤ ε ∧ " +
			"    (∀n:num. " +
			"        0 < n ⇒ " +
			"        ∃D:num. " +
			"            2 * D ≤ n ∧ " +
			"            &D ≤ δ * &n ∧ " +
			"            (∀l u:num. M ≤ l ⇒ |sum(l .. u, «centeredTerm»)| < &(D + 1) * (δ / (&4 * &n))))",
		Abbrev: Abbrev{
			{Name: "weightedTerms", Text: "λn:num. " +
				"    «centeredRatio»(n + 1) * complex_cpow(complex_of_real(&(n + 1)), -complex_of_real(&1))"},
		},
	}, func(a *Argument, ε *Expr[Real], positiveEpsilon Fact) {
		terms := a.TermAs[Fun[Nat, Real]]("«centeredTerm»")
		two := a.TermAs[Real]("&2")
		q, large := a.ObtainAs[Nat](
			"choose an integer q with 1/q small compared with ε: δ = 1/q makes "+
				"div(n, q) the block length ⌊δn⌋, so no integer part is needed",
			"∃q:num. &2 / ε + &2 ≤ &q",
			Cite(real_archimedean.ExistsNumAbove))
		qReal := a.TermAs[Real]("&q")
		δ, reciprocal := a.LetAs[Real]("δ", "&1 / &q")
		qBound := a.Have(
			"the integer is at least two",
			"&2 ≤ &q",
			ByArith(large, positiveEpsilon))
		deltaBounds := a.Have(
			"the reciprocal is positive and at most one",
			"&0 < δ ∧ δ ≤ &1",
			ByArith(reciprocal, qBound))
		unit := a.Have(
			"the reciprocal cancels q",
			"δ * &q = &1",
			ByArith(reciprocal, qBound))
		epsilonScale := a.Have(
			"multiply the lower bound involving ε by ε",
			"&2 ≤ ε * &q",
			ByArith(large, positiveEpsilon, real_order_field.LessEqDivMulRight.At(two, qReal, ε)))
		deltaSmall := a.Have(
			"twice the reciprocal is at most ε",
			"&2 * δ ≤ ε",
			ByArith(epsilonScale, unit, deltaBounds))
		positiveTolerance := a.Have(
			"the Cauchy tolerance is positive",
			"&0 < δ ^ 2 / &8",
			ByArith(deltaBounds))
		converges := a.Have(
			"the centered terms are the real parts of the terms "+
				"of the series of ψ(n)/n − 1 at 1, so they have a sum",
			"∃t:real. real_sums(«centeredTerm», t)",
			Derive(func(b *Argument) {
				_, atOne := b.ObtainAs[Complex](
					"the Dirichlet series of ψ(n)/n − 1 converges at 1",
					"∃v:complex. dirichlet_sums(«centeredRatio», complex_of_real(&1), v)",
					Cite(PsiSeriesConverges))
				reciprocal := b.Have(
					"the complex weight at 1 divides each real coefficient by n + 1",
					"«weightedTerms» = (λn:num. complex_of_real(«centeredTerm»(n)))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						x := c.TermAs[Real]("&(n + 1)")
						positive := c.Have(
							"the base n + 1 is positive",
							"&0 < &(n + 1)",
							ByArith(real_order_ring.OfNumLessThan.At(c.TermAs[Nat]("0"), c.TermAs[Nat]("n + 1"))))
						c.Show(
							"the power at −1 is the reciprocal, embedded in ℂ",
							Simp(
								Rev(complex_field.OfRealNeg),
								Fwd(complex_cpow.CpowRealExponent),
								Fwd(real_rpow.RpowNeg),
								Fwd(real_field.RealDivDef),
								Rev(complex_field.OfRealMul)),
							ByArith(positive, real_rpow.RpowOneExponent.At(x)))
					}))
				embedded := b.Have(
					"the terms of the sum at 1 are the embedded centered terms",
					"complex_sums(λn:num. complex_of_real(«centeredTerm»(n)), v)",
					By(reciprocal, b.Unfolded(atOne, dirichlet_series.DirichletSumsDef)))
				parts := b.Conjuncts(
					b.Unfolded(embedded, complex_series.ComplexSumsDef),
					"the real parts sum to the real part of v",
					"the imaginary parts sum to the imaginary part of v")
				b.Show(
					"taking real parts gives a real sum",
					Witness(b.TermAs[Real]("re(v)")),
					By(b.Simplified(parts[0], Fwd(complex_field.PartsOfReal))))
			}))
		M, cauchy := a.ObtainAs[Nat](
			"all blocks of the centered series past M have small mass",
			"∃M:num. ∀l u:num. M ≤ l ⇒ |sum(l .. u, «centeredTerm»)| < δ ^ 2 / &8",
			By(positiveTolerance, converges, real_series.SumsCauchy.At(terms)))
		blocks := a.Have(
			"for n > 0 the quotient D = div(n, q) gives the block bound",
			Statement{
				Binders:    "∀n:num.",
				Hypotheses: []string{"0 < n"},
				Conclusion: "∃D:num. " +
					"    2 * D ≤ n ∧ " +
					"    &D ≤ δ * &n ∧ " +
					"    (∀l u:num. M ≤ l ⇒ |sum(l .. u, «centeredTerm»)| < &(D + 1) * (δ / (&4 * &n)))",
			},
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				positive := b.Assume()
				D, quotient := b.LetAs[Nat]("D", "div(n, q)")
				positiveN := b.Have(
					"n is positive as a real",
					"&0 < &n",
					By(positive, real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), n)))
				naturalBounds := b.Have(
					"the quotient rounds n over q down, and q ≥ 2 keeps it at most half of n",
					"q * D ≤ n ∧ n < q * (D + 1) ∧ 2 * D ≤ n",
					ByArith(
						qBound,
						quotient,
						real_construction.OfNumLessEq.At(b.TermAs[Nat]("2"), q),
						nat_div_mod.DivMulLessEq.At(n, q),
						nat_div_mod.Division.At(n, q)))
				scaleBounds := b.Have(
					"D is at most δ times n, and δ times n at most D + 1",
					"&D ≤ δ * &n ∧ δ * &n ≤ &(D + 1)",
					Derive(func(c *Argument) {
						cast := c.Have(
							"lift the quotient inequalities to the reals",
							"&q * &D ≤ &n ∧ &n ≤ &q * &(D + 1)",
							ByArith(
								naturalBounds,
								real_construction.OfNumMul.At(q, D),
								real_construction.OfNumMul.At(q, c.TermAs[Nat]("D + 1")),
								real_construction.OfNumLessEq.At(c.TermAs[Nat]("q * D"), n),
								real_order_ring.OfNumLessThan.At(n, c.TermAs[Nat]("q * (D + 1)"))))
						scaled := c.Have(
							"n over q is δ times n",
							"&n / &q = δ * &n",
							ByArith(reciprocal, qBound))
						positiveQ := c.Have(
							"q is a positive divisor",
							"&0 < &q",
							ByArith(qBound))
						divided := c.Have(
							"divide the product inequalities by q",
							"&D ≤ &n / &q ∧ &n / &q ≤ &(D + 1)",
							ByArith(positiveQ, cast))
						c.Show(
							"replace the quotient by δ times n",
							By(Normalized, divided, scaled))
					}))
				margin, marginDef := b.LetAs[Real]("η", "δ / (&4 * &n)")
				marginProperties := b.Have(
					"the margin η is positive with the prescribed scale",
					"&0 < η ∧ η * &n = δ / &4",
					ByArith(positiveN, deltaBounds, marginDef))
				mass := b.Have(
					"the block length cancels the n in the margin",
					"δ ^ 2 / &4 ≤ &(D + 1) * η",
					ByArith(
						scaleBounds,
						marginProperties,
						deltaBounds,
						real_order_ring.LessEqMulRight.At(
							b.TermAs[Real]("δ * &n"), b.TermAs[Real]("&(D + 1)"), margin)))
				b.Take(D)
				b.Show(
					"late blocks have mass below δ²/8, which is less than D + 1 times the margin",
					ByArith(naturalBounds, scaleBounds, mass, positiveTolerance, cauchy))
			}))
		a.Take(δ)
		a.Take(M)
		a.Show(
			"δ and M have the stated properties",
			By(deltaBounds, deltaSmall, blocks))
	}),
})}

// PsiUpperAsymptotic — for every ε > 0, ψ(n) ≤ (1 + ε)·n eventually.
// An overshoot at n would make every centered term on the block of D + 1
// terms from n on at least δ/(4n), against centeredBlockMass.
var PsiUpperAsymptotic = psiUpperAsymptoticThm{family.Add(registry.ProofEntry{
	Name: "PsiUpperAsymptotic",
	Key:  "prop_84ed1e5742de0ab",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "∃K:num. ∀n:num. K ≤ n ⇒ chebyshev_psi(n) ≤ (&1 + ε) * &n",
	}, func(a *Argument, ε *Expr[Real], positiveEpsilon Fact) {
		terms := a.TermAs[Fun[Nat, Real]]("«centeredTerm»")
		_, _, choice := a.Unpack2As[Real, Nat](
			GroupPremises(positiveEpsilon, centeredBlockMass.At(ε)), "δ", "M")
		parts := a.Conjuncts(
			choice,
			"δ is positive",
			"δ is at most one",
			"twice δ is at most ε",
			"the block bound past M")
		positiveDelta, deltaLeOne, deltaSmall, blocks := parts[0], parts[1], parts[2], parts[3]
		a.Show(
			"no overshoot occurs at an index past M",
			Witness(a.TermAs[Nat]("M + 1")),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				late := b.Assume()
				overshoot := b.SupposeNot()
				positive := b.Have(
					"an index past M is positive",
					"0 < n",
					ByArith(late))
				D, blockData := b.UnpackAs[Nat](GroupPremises(positive, blocks.At(n)), "D")
				block := b.Conjuncts(
					blockData,
					"D is at most half of n",
					"D is at most δ times n",
					"late blocks have mass below D + 1 times δ/(4n)")
				positiveN := b.Have(
					"n is positive as a real",
					"&0 < &n",
					By(positive, real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), n)))
				L, startDef := b.LetAs[Nat]("L", "n - 1")
				U, endDef := b.LetAs[Nat]("U", "n + D - 1")
				margin, marginDef := b.LetAs[Real]("η", "δ / (&4 * &n)")
				shiftedBlock := b.Have(
					"the shifted block starts past M and contains D plus one terms",
					"M ≤ L ∧ U + 1 - L = D + 1",
					ByArith(late, startDef, endDef))
				marginProperties := b.Have(
					"the margin η is positive with the prescribed scale",
					"&0 < η ∧ η * &n = δ / &4",
					ByArith(positiveN, positiveDelta, marginDef))
				pointwise := b.Have(
					"every centered term on the block is at least η",
					"∀k:num. L ≤ k ∧ k ≤ U ⇒ η ≤ «centeredTerm»(k)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("k")
						inBlock := c.Assume()
						j, shifted := c.LetAs[Nat]("j", "k + 1")
						jReal := c.TermAs[Real]("&j")
						bounds := c.Have(
							"the unshifted index runs from n through n plus D",
							"n ≤ j ∧ j ≤ n + D",
							ByArith(inBlock, startDef, endDef, shifted, late))
						positiveJ := c.Have(
							"the unshifted index is positive",
							"&0 < &j",
							ByArith(bounds, positiveN, real_construction.OfNumLessEq.At(n, j)))
						upper := c.Have(
							"the unshifted index grows by at most δ times n",
							"&j ≤ (&1 + δ) * &n ∧ &j ≤ &2 * &n",
							ByArith(
								bounds,
								block[1],
								deltaLeOne,
								positiveN,
								real_construction.OfNumLessEq.At(j, c.TermAs[Nat]("n + D")),
								real_construction.OfNumAdd.At(n, D)))
						gap := c.Have(
							"monotonicity preserves the overshoot while the index grows",
							"δ * &n ≤ chebyshev_psi(j) - &j",
							ByArith(overshoot, deltaSmall, positiveN, upper, bounds, prime_distribution.PsiMonotone.At(n, j)))
						ratio := c.Have(
							"dividing by an index at most twice n retains half the relative gap",
							"&1 + δ / &2 ≤ chebyshev_psi(j) / &j",
							ByArith(gap, upper, positiveDelta, positiveJ))
						weighted := c.Have(
							"multiplying η by j stays within that half-gap",
							"η * &j ≤ δ / &2",
							ByArith(
								upper,
								marginProperties,
								real_order_ring.LessEqMulLeft.At(margin, jReal, c.TermAs[Real]("&2 * &n"))))
						c.Show(
							"the centered term divides the relative gap by the positive index",
							ByArith(
								weighted,
								ratio,
								positiveJ,
								real_order_field.LessEqDivMulLeft.At(
									margin, c.TermAs[Real]("chebyshev_psi(j) / &j - &1"), jReal)))
					}))
				sumLower := b.Have(
					"the block sum is at least its length times η",
					"&(D + 1) * η ≤ sum(L .. U, «centeredTerm»)",
					By(
						shiftedBlock,
						pointwise,
						real_sum.IntervalConst.At(margin, U, L),
						real_sum.IntervalMonotone.At(L, U, b.TermAs[Fun[Nat, Real]]("λk:num. η"), terms)))
				b.Show(
					"the block mass reaches the bound it must stay below",
					ByArith(shiftedBlock, block[2].At(L, U), sumLower))
			}))
	}),
	Reading: "Monotonicity of ψ is the Tauberian condition: without it " +
		"a convergent series says nothing about single terms of this size.",
})}

// PsiLowerAsymptotic — for every ε > 0, ψ(n) ≥ (1 − ε)·n eventually.
// An undershoot at n would make every centered term on the block of D + 1
// terms up to n at most −δ/(4n), against centeredBlockMass.
var PsiLowerAsymptotic = psiLowerAsymptoticThm{family.Add(registry.ProofEntry{
	Name: "PsiLowerAsymptotic",
	Key:  "prop_f4aa8759c211731d",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "∃K:num. ∀n:num. K ≤ n ⇒ (&1 - ε) * &n ≤ chebyshev_psi(n)",
	}, func(a *Argument, ε *Expr[Real], positiveEpsilon Fact) {
		terms := a.TermAs[Fun[Nat, Real]]("«centeredTerm»")
		_, _, choice := a.Unpack2As[Real, Nat](
			GroupPremises(positiveEpsilon, centeredBlockMass.At(ε)), "δ", "M")
		parts := a.Conjuncts(
			choice,
			"δ is positive",
			"δ is at most one",
			"twice δ is at most ε",
			"the block bound past M")
		positiveDelta, deltaSmall, blocks := parts[0], parts[2], parts[3]
		a.Show(
			"no undershoot occurs beyond twice M plus two",
			Witness(a.TermAs[Nat]("2 * (M + 1)")),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				late := b.Assume()
				undershoot := b.SupposeNot()
				positive := b.Have(
					"an index past twice M is positive",
					"0 < n",
					ByArith(late))
				D, blockData := b.UnpackAs[Nat](GroupPremises(positive, blocks.At(n)), "D")
				block := b.Conjuncts(
					blockData,
					"D is at most half of n",
					"D is at most δ times n",
					"late blocks have mass below D + 1 times δ/(4n)")
				positiveN := b.Have(
					"n is positive as a real",
					"&0 < &n",
					By(positive, real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), n)))
				L, startDef := b.LetAs[Nat]("L", "n - D - 1")
				U, endDef := b.LetAs[Nat]("U", "n - 1")
				margin, marginDef := b.LetAs[Real]("η", "δ / (&4 * &n)")
				shiftedBlock := b.Have(
					"the shifted block starts past M and contains D plus one terms",
					"M ≤ L ∧ U + 1 - L = D + 1",
					ByArith(late, startDef, endDef, block[0]))
				marginProperties := b.Have(
					"the margin η is positive with the prescribed scale",
					"&0 < η ∧ η * &n = δ / &4",
					ByArith(positiveN, positiveDelta, marginDef))
				pointwise := b.Have(
					"every centered term on the backward block is at most minus η",
					"∀k:num. L ≤ k ∧ k ≤ U ⇒ «centeredTerm»(k) ≤ -η",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("k")
						inBlock := c.Assume()
						j, shifted := c.LetAs[Nat]("j", "k + 1")
						jReal := c.TermAs[Real]("&j")
						bounds := c.Have(
							"the unshifted index lies between n minus D and n",
							"n ≤ j + D ∧ j ≤ n",
							ByArith(inBlock, startDef, endDef, shifted, late, block[0]))
						positiveJ := c.Have(
							"the unshifted index is positive",
							"&0 < &j",
							ByArith(shifted, real_order_ring.OfNumLessThan.At(c.TermAs[Nat]("0"), j)))
						span := c.Have(
							"moving backward takes off at most δ times n",
							"(&1 - δ) * &n ≤ &j ∧ &j ≤ &n",
							ByArith(
								bounds,
								block[1],
								real_construction.OfNumLessEq.At(n, c.TermAs[Nat]("j + D")),
								real_construction.OfNumLessEq.At(j, n),
								real_construction.OfNumAdd.At(j, D)))
						gap := c.Have(
							"monotonicity makes ψ(j) no larger than the undershoot at n",
							"chebyshev_psi(j) - &j ≤ -(δ * &n)",
							ByArith(undershoot, deltaSmall, positiveN, span, bounds, prime_distribution.PsiMonotone.At(j, n)))
						ratio := c.Have(
							"the relative gap still has magnitude at least δ over two",
							"chebyshev_psi(j) / &j ≤ &1 - δ / &2",
							ByArith(
								gap,
								span,
								positiveDelta,
								positiveJ,
								real_order_field.LessEqDivMulRight.At(
									c.TermAs[Real]("chebyshev_psi(j)"), c.TermAs[Real]("&1 - δ / &2"), jReal)))
						weighted := c.Have(
							"multiplying η by the smaller index stays within that gap",
							"η * &j ≤ δ / &2",
							ByArith(
								span,
								marginProperties,
								real_order_ring.LessEqMulLeft.At(margin, jReal, c.TermAs[Real]("&n"))))
						c.Show(
							"divide the negative relative gap by the positive index",
							ByArith(
								weighted,
								ratio,
								positiveJ,
								real_order_field.LessEqDivMulRight.At(
									c.TermAs[Real]("chebyshev_psi(j) / &j - &1"), c.TermAs[Real]("-η"), jReal)))
					}))
				sumUpper := b.Have(
					"the block sum is at most minus η times its length",
					"sum(L .. U, «centeredTerm») ≤ &(D + 1) * (-η)",
					By(
						shiftedBlock,
						pointwise,
						real_sum.IntervalConst.At(b.TermAs[Real]("-η"), U, L),
						real_sum.IntervalMonotone.At(L, U, terms, b.TermAs[Fun[Nat, Real]]("λk:num. -η"))))
				b.Show(
					"the negative block sum reaches in magnitude the bound it must stay below",
					ByArith(shiftedBlock, block[2].At(L, U), sumUpper))
			}))
	}),
})}

// PsiAsymptotic — ψ(n)/n tends to 1: past both thresholds of the two
// one-sided asymptotics at ε/2, ψ(n) lies within ε/2·n of n, and dividing by
// n > 0 puts ψ(n)/n within ε/2 of 1.
var PsiAsymptotic = psiAsymptoticThm{family.Add(registry.ProofEntry{
	Name: "PsiAsymptotic",
	Key:  "prop_57d86d4a01e798b1",
	Build: family.Theorem("(λn:num. chebyshev_psi(n) / &n) ⟶ &1",
		func(a *Argument) {
			a.Do(Unfold(real_sequences.RealConvergesToDef))
			a.FixAs[Real]("ε")
			positive := a.Assume()
			half := a.TermAs[Real]("ε / &2")
			halfPositive := a.Have(
				"half the tolerance is positive",
				"&0 < ε / &2",
				ByArith(positive))
			_, upper := a.Obtain(
				"from U onward ψ(n) is at most (1 + ε/2)·n",
				"∃U:num. ∀n:num. U ≤ n ⇒ chebyshev_psi(n) ≤ (&1 + ε / &2) * &n",
				By(halfPositive, PsiUpperAsymptotic.At(half)))
			_, lower := a.Obtain(
				"from L onward ψ(n) is at least (1 − ε/2)·n",
				"∃L:num. ∀n:num. L ≤ n ⇒ (&1 - ε / &2) * &n ≤ chebyshev_psi(n)",
				By(halfPositive, PsiLowerAsymptotic.At(half)))
			a.Take(a.TermAs[Nat]("U + L + 1"))
			n := a.FixAs[Nat]("n")
			late := a.Assume()
			indices := a.Have(
				"n is past both thresholds and is positive",
				"U ≤ n ∧ L ≤ n ∧ 0 < n",
				ByArith(late))
			denominator := a.TermAs[Real]("&n")
			psi := a.TermAs[Real]("chebyshev_psi(n)")
			denominatorPositive := a.Have(
				"the denominator n is positive",
				"&0 < &n",
				By(indices, real_order_ring.OfNumLessThan.At(a.TermAs[Nat]("0"), n)))
			bounds := a.Have(
				"dividing by n puts the quotient within half the tolerance of 1",
				"&1 - ε / &2 ≤ chebyshev_psi(n) / &n ∧ chebyshev_psi(n) / &n ≤ &1 + ε / &2",
				By(
					indices,
					denominatorPositive,
					lower.At(n),
					upper.At(n),
					real_order_field.LessEqDivMulLeft.At(a.TermAs[Real]("&1 - ε / &2"), psi, denominator),
					real_order_field.LessEqDivMulRight.At(psi, a.TermAs[Real]("&1 + ε / &2"), denominator)))
			a.Show(
				"the distance from 1 is strictly below ε",
				ByArith(positive, bounds))
		}),
	Reading: "The term at n = 0 is a quotient by zero, an unspecified value the limit does not see.",
})}

// PrimeCountingUpperAsymptotic — for every ε > 0, π(n)·log n is eventually
// at most (1 + ε)·n. Split the count at the least integer above a power of n.
var PrimeCountingUpperAsymptotic = primeCountingUpperAsymptoticThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingUpperAsymptotic",
	Key:  "prop_2c15540aa15fa1f",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "∃K:num. ∀n:num. K ≤ n ⇒ &prime_counting(n) * log(&n) ≤ (&1 + ε) * &n",
		Abbrev: Abbrev{
			{Name: "logDecay", Text: "λd:real. λk:num. log(&(k + 1)) / real_rpow(&(k + 1), d)"},
		},
	}, func(a *Argument, ε *Expr[Real], positiveEpsilon Fact) {
		δ, deltaDef := a.LetAs[Real]("δ", "ε / (&4 + &4 * ε)")
		exponent, exponentDef := a.LetAs[Real]("β", "&1 - δ")
		quarter := a.TermAs[Real]("ε / &4")
		zero := a.TermAs[Real]("&0")
		one := a.TermAs[Real]("&1")

		deltaRange := a.Have(
			"the exponent loss is strictly between zero and one",
			"&0 < δ ∧ δ < &1",
			ByArith(deltaDef, positiveEpsilon))
		exponentRange := a.Have(
			"the cutoff exponent is also strictly between zero and one",
			"&0 < β ∧ β < &1",
			ByArith(exponentDef, deltaRange))
		scale := a.Have(
			"the cutoff exponent leaves room for the error in ψ",
			"&1 + ε / &4 ≤ (&1 + ε / &2) * β",
			Derive(func(b *Argument) {
				product := b.Have(
					"the exponent loss times one plus ε is ε over four",
					"δ * (&1 + ε) = ε / &4",
					ByArith(deltaDef, positiveEpsilon))
				b.Show(
					"apply the definition of the cutoff exponent",
					ByArith(product, deltaRange, positiveEpsilon, exponentDef))
			}))
		positiveQuarter := a.Have(
			"the quarter tolerance is positive",
			"&0 < ε / &4",
			ByArith(positiveEpsilon))
		_, psiTail := a.ObtainAs[Nat](
			"ψ is eventually bounded with the quarter tolerance",
			"∃M:num. ∀n:num. M ≤ n ⇒ chebyshev_psi(n) ≤ (&1 + ε / &4) * &n",
			By(positiveQuarter, PsiUpperAsymptotic.At(quarter)))
		_, logTail := a.ObtainAs[Nat](
			"the shifted logarithm divided by the δ power tends to zero",
			"∃L:num. ∀k:num. L ≤ k ⇒ |«logDecay»(δ, k) - &0| < ε / &4",
			By(
				positiveQuarter,
				deltaRange,
				real_rpow.LogOverRpowTendsToZero.At(δ),
				real_sequences.RealConvergesToDef.At(a.TermAs[Fun[Nat, Real]]("«logDecay»(δ)"), zero)))
		a.Show(
			"take an index beyond both thresholds and at least two",
			Witness(a.TermAs[Nat]("M + L + 2")),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				late := b.Assume()
				nReal := b.TermAs[Real]("&n")
				logN := b.TermAs[Real]("log(&n)")
				nLarge := b.Have(
					"n is larger than one",
					"&1 < &n",
					ByArith(late, real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("1"), n)))
				r, cutoff := b.LetAs[Real]("r", "real_rpow(&n, β)")
				rRange := b.Have(
					"a fractional positive exponent places the cutoff above one and below n",
					"&1 < r ∧ r ≤ &n",
					ByArith(
						nLarge,
						exponentRange,
						cutoff,
						real_rpow.RpowLessExponent.At(nReal, zero, exponent),
						real_rpow.RpowLessExponent.At(nReal, exponent, one),
						real_rpow.RpowZeroExponent.At(nReal),
						real_rpow.RpowOneExponent.At(nReal)))
				m, minimum := b.ObtainAs[Nat](
					"take the least natural number at or above the cutoff",
					"∃m:num. r ≤ &m ∧ (∀k:num. k < m ⇒ ¬(r ≤ &k))",
					By(
						real_archimedean.ExistsNumAbove.At(r),
						nat_order.WellOrdering.At(b.TermAs[Set[Nat]]("λk:num. r ≤ &k"))))
				parts := b.Conjuncts(
					minimum,
					"cutoff attained",
					"no smaller integer attains the cutoff")
				attained, minimal := parts[0], parts[1]
				mReal := b.TermAs[Real]("&m")
				logM := b.TermAs[Real]("log(&m)")
				mRange := b.Have(
					"the integer cutoff is at least two and at most n",
					"2 ≤ m ∧ m ≤ n",
					ByArith(attained, rRange, minimal.At(n), real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("1"), m)))
				mSmall := b.Have(
					"the cutoff is at most r plus one, hence at most twice r",
					"&m ≤ &2 * r",
					Derive(func(c *Argument) {
						predecessor := c.TermAs[Nat]("m - 1")
						addOne := c.Have(
							"m is the successor of its predecessor",
							"m - 1 + 1 = m",
							ByArith(mRange))
						c.Show(
							"the predecessor does not reach r",
							ByArith(
								addOne,
								mRange,
								rRange,
								minimal.At(predecessor),
								real_construction.OfNumAdd.At(predecessor, c.TermAs[Nat]("1"))))
					}))
				logNonnegative := b.Have(
					"the logarithm increases from zero at one",
					"&0 ≤ log(&n)",
					ByArith(nLarge, real_exp_log.LogNonneg.At(nReal)))
				logCutoff := b.Have(
					"log m is at least the cutoff exponent times log n",
					"β * log(&n) ≤ log(&m)",
					ByArith(
						nLarge,
						rRange,
						attained,
						cutoff,
						real_rpow.LogRpow.At(nReal, exponent),
						real_exp_log.LogLessIff.At(mReal, r)))
				difference := b.TermAs[Real]("&prime_counting(n) - &prime_counting(m)")
				countOrder := b.Have(
					"the number of primes between m and n is nonnegative",
					"&0 ≤ &prime_counting(n) - &prime_counting(m)",
					ByArith(
						mRange,
						prime_distribution.PrimeCountingMonotone.At(m, n),
						real_construction.OfNumLessEq.At(
							b.TermAs[Nat]("prime_counting(m)"), b.TermAs[Nat]("prime_counting(n)"))))
				countedByPsi := b.Have(
					"each prime above the cutoff contributes at least log m to ψ",
					"(&prime_counting(n) - &prime_counting(m)) * log(&m) ≤ chebyshev_psi(n)",
					ByArith(mRange, prime_distribution.PrimeCountingThroughPsi.At(m, n)))
				split := b.Have(
					"the weighted primes above the cutoff are bounded by ψ",
					"β * (&prime_counting(n) * log(&n)) ≤ chebyshev_psi(n) + β * (&prime_counting(m) * log(&n))",
					ByArith(
						countOrder,
						logCutoff,
						countedByPsi,
						real_order_ring.LessEqMulLeft.At(difference, b.TermAs[Real]("β * log(&n)"), logM)))
				s, decayPower := b.LetAs[Real]("s", "real_rpow(&n, δ)")
				positiveS := b.Have(
					"the δ power of n is positive",
					"&0 < s",
					ByArith(nLarge, decayPower, real_rpow.RpowPositive.At(nReal, δ)))
				powerProduct := b.Have(
					"the exponents β and δ add to one",
					"r * s = &n",
					ByArith(
						nLarge,
						decayPower,
						cutoff,
						exponentDef,
						real_rpow.RpowAdd.At(nReal, exponent, δ),
						real_rpow.RpowOneExponent.At(nReal)))
				logIndex := b.Have(
					"the predecessor of n lies beyond the threshold for logarithmic decay",
					"L ≤ n - 1 ∧ n - 1 + 1 = n",
					ByArith(late))
				decay := b.Have(
					"the logarithm divided by the δ power is at most the quarter tolerance",
					"log(&n) / s ≤ ε / &4",
					ByArith(logIndex, logTail.At(b.TermAs[Nat]("n - 1")), decayPower))
				logBound := b.Have(
					"multiply the decay estimate by the positive δ power",
					"log(&n) ≤ (ε / &4) * s",
					By(decay, positiveS, real_order_field.LessEqDivMulRight.At(logN, quarter, s)))
				countM := b.TermAs[Real]("&prime_counting(m)")
				twiceR := b.TermAs[Real]("&2 * r")
				countBound := b.Have(
					"the number of primes up to m is at most m and hence at most twice r",
					"&prime_counting(m) ≤ &2 * r",
					ByArith(
						mSmall,
						prime_distribution.PrimeCountingLessEqSelf.At(m),
						real_construction.OfNumLessEq.At(b.TermAs[Nat]("prime_counting(m)"), m)))
				smallPrimes := b.Have(
					"the primes up to m use at most half the available error",
					"&prime_counting(m) * log(&n) ≤ ε / &2 * &n",
					ByArith(
						logNonnegative,
						rRange,
						countBound,
						logBound,
						powerProduct,
						positiveEpsilon,
						real_order_ring.LessEqMulRight.At(countM, twiceR, logN),
						real_order_ring.LessEqMulLeft.At(twiceR, logN, b.TermAs[Real]("(ε / &4) * s"))))
				scaledPsi := b.Have(
					"the eventual ψ bound uses the main term and the other half of the error",
					"chebyshev_psi(n) ≤ β * ((&1 + ε / &2) * &n)",
					ByArith(
						late,
						psiTail.At(n),
						scale,
						nLarge,
						real_order_ring.LessEqMulRight.At(
							b.TermAs[Real]("&1 + ε / &4"), b.TermAs[Real]("(&1 + ε / &2) * β"), nReal)))
				scaledCount := b.Have(
					"the two contributions fit within the full tolerance",
					"β * (&prime_counting(n) * log(&n)) ≤ β * ((&1 + ε) * &n)",
					ByArith(
						split,
						smallPrimes,
						scaledPsi,
						exponentRange,
						real_order_ring.LessEqMulLeft.At(
							exponent, b.TermAs[Real]("&prime_counting(m) * log(&n)"), b.TermAs[Real]("ε / &2 * &n"))))
				b.Show(
					"cancel the positive cutoff exponent",
					By(
						scaledCount,
						exponentRange,
						real_order_ring.LessEqCancelMulLeft.At(
							exponent, b.TermAs[Real]("&prime_counting(n) * log(&n)"), b.TermAs[Real]("(&1 + ε) * &n"))))
			}))
	}),
})}

// PrimeNumberTheorem — the prime number theorem: π(n)·log n / n tends to
// 1.
var PrimeNumberTheorem = primeNumberTheoremThm{family.Add(registry.ProofEntry{
	Name: "PrimeNumberTheorem",
	Key:  "prop_9ef8ef394fc76349",
	Build: family.Theorem("(λn:num. &prime_counting(n) * log(&n) / &n) ⟶ &1",
		func(a *Argument) {
			a.Do(Unfold(real_sequences.RealConvergesToDef))
			a.FixAs[Real]("ε")
			positive := a.Assume()
			half := a.TermAs[Real]("ε / &2")
			halfPositive := a.Have(
				"half the tolerance is positive",
				"&0 < ε / &2",
				ByArith(positive))
			_, upper := a.Obtain(
				"from U onward π(n)·log n is at most (1 + ε/2)·n",
				"∃U:num. ∀n:num. U ≤ n ⇒ &prime_counting(n) * log(&n) ≤ (&1 + ε / &2) * &n",
				By(halfPositive, PrimeCountingUpperAsymptotic.At(half)))
			_, lower := a.Obtain(
				"from L onward ψ(n) is at least (1 − ε/2)·n",
				"∃L:num. ∀n:num. L ≤ n ⇒ (&1 - ε / &2) * &n ≤ chebyshev_psi(n)",
				By(halfPositive, PsiLowerAsymptotic.At(half)))

			a.Take(a.TermAs[Nat]("U + L + 1"))
			n := a.FixAs[Nat]("n")
			late := a.Assume()
			indices := a.Have(
				"n is past both cutoffs and is positive",
				"U ≤ n ∧ L ≤ n ∧ 0 < n",
				ByArith(late))
			denominator := a.TermAs[Real]("&n")
			denominatorPositive := a.Have(
				"the denominator n is positive",
				"&0 < &n",
				By(indices, real_order_ring.OfNumLessThan.At(a.TermAs[Nat]("0"), n)))
			numerator := a.TermAs[Real]("&prime_counting(n) * log(&n)")
			bounds := a.Have(
				"the quotient is within half the tolerance of 1",
				"&1 - ε / &2 ≤ &prime_counting(n) * log(&n) / &n ∧ &prime_counting(n) * log(&n) / &n ≤ &1 + ε / &2",
				SplitConj(
					Case(
						"the lower bound passes from ψ(n) to π(n)·log n and is divided by n",
						ByArith(
							indices,
							denominatorPositive,
							lower.At(n),
							prime_distribution.PsiLessEqPiLog.At(n),
							real_order_field.LessEqDivMulLeft.At(
								a.TermAs[Real]("&1 - ε / &2"), numerator, denominator))),
					Case(
						"the upper bound for π(n)·log n is divided by n",
						By(
							indices,
							denominatorPositive,
							upper.At(n),
							real_order_field.LessEqDivMulRight.At(
								numerator, a.TermAs[Real]("&1 + ε / &2"), denominator)))))
			a.Show(
				"the distance from 1 is strictly below ε",
				ByArith(positive, bounds))
		}),
	Reading: "π is the count of primes up to a natural number, so the limit is that " +
		"of a sequence; the terms at n = 0 and n = 1 are quotients the limit does not see.",
})}
