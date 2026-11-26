// lambert.go — the Lambert series: for 0 ≤ t < 1 and a sequence bounded
// by 1, the series Σ a(n)·tⁿ/(1 − tⁿ) is the power series whose m-th
// coefficient is the sum of a over the divisors of m.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// LambertExpansion — the Lambert identity: for 0 ≤ t < 1 and a real sequence
// a bounded by 1, the Lambert series Σ_{n≥1} a(n)·tⁿ/(1 − tⁿ) and the power
// series Σ_{m≥1} (Σ_{d∣m} a(d))·t^m have a common sum. The n-th Lambert term
// is the sum of the geometric row a(n)·t^(nk), k ≥ 1, whose absolute values
// sum to at most tⁿ/(1 − t); so the double series is absolutely summable and
// may be regrouped by the products m = n·k of its indices. The index pairs
// with product m are the pairs of a divisor of m and its quotient, one for
// each divisor, and the regrouped term is (Σ_{d∣m} a(d))·t^m.
var LambertExpansion = lambertExpansionThm{family.Add(registry.ProofEntry{
	Name: "LambertExpansion",
	Key:  "prop_577d5d729865e0db",
	Reading: "The bound on a is what makes the double series absolutely " +
		"summable; a sequence bounded by any constant scales to one bounded by 1.",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀t:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ &1",
			"&0 ≤ t",
			"t < &1",
		},
		Conclusion: "∃S:real. " +
			"    real_sums(λn:num. a(n + 1) * t ^ (n + 1) / (&1 - t ^ (n + 1)), S) ∧ " +
			"    real_sums(λn:num. (Σ_{d∈{d:num | d ∣ n + 1}} a(d)) * t ^ (n + 1), S)",
		Abbrev: Abbrev{
			{Name: "signedRows", Text: "λn:num. a(n + 1) * t ^ (n + 1) / (&1 - t ^ (n + 1))"},
			{Name: "absoluteRows", Text: "λn:num. |a(n + 1)| * t ^ (n + 1) / (&1 - t ^ (n + 1))"},
			{Name: "majorant", Text: "λn:num. t ^ (n + 1) / (&1 - t)"},
			{Name: "lambertEntry", Text: "λn:num. λk:num. a(n + 1) * t ^ ((n + 1) * (k + 1))"},
			{Name: "productIndex", Text: "λn:num. λk:num. (n + 1) * (k + 1) - 1"},
			{Name: "lambertFibre", Text: "λj:num. {p:prod(num,num) | «productIndex»(fst(p), snd(p)) = j}"},
			{Name: "divisors", Text: "λj:num. {d:num | d ∣ j + 1}"},
			{Name: "fibreTerm", Text: "λp:prod(num,num). «lambertEntry»(fst(p), snd(p))"},
			{Name: "groupedTerms", Text: "λj:num. Σ_{p∈«lambertFibre»(j)} «fibreTerm»(p)"},
		},
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			t *Expr[Real],
			bounded, nonnegative, belowOne Fact,
		) {
			zero := arg.TermAs[Nat]("0")
			powerBounds := arg.Have(
				"each power t^(n+1) lies between zero and t",
				"∀n:num. &0 ≤ t ^ (n + 1) ∧ t ^ (n + 1) ≤ t",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"positive powers of t decrease",
						ByArith(
							nonnegative,
							belowOne,
							real_pow.PowNonneg.At(t, b.TermAs[Nat]("n + 1")),
							real_pow.PowMonoExpBelowOne.At(t, b.TermAs[Nat]("1"), b.TermAs[Nat]("n + 1")),
							real_pow.PowOne.At(t)))
				}))
			rows := arg.Have(
				"the signed and absolute rows have geometric sums",
				"∀n:num. "+
					"    real_sums(λk:num. «lambertEntry»(n,k), «signedRows»(n)) ∧ "+
					"    real_sums(λk:num. |«lambertEntry»(n,k)|, «absoluteRows»(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					power := b.TermAs[Real]("t ^ (n + 1)")
					powers := b.Have(
						"factor one copy of t^(n+1) out of each power in the row",
						"∀k:num. t ^ ((n + 1) * (k + 1)) = t ^ (n + 1) * (t ^ (n + 1)) ^ k",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							c.Show(
								"power of a power and successor exponent",
								By(
									real_pow.PowPow.At(t, c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k + 1")),
									real_pow.PowAddOne.At(power, k)))
						}))
					powerInUnit := b.Have(
						"the ratio t^(n+1) of the row has absolute value below one",
						"|t ^ (n + 1)| < &1",
						ByArith(powerBounds.At(n), belowOne, real_sgn_abs.AbsFixedIffNonneg.At(power)))
					factors := b.Have(
						"put each row into geometric form",
						"∀k:num. "+
							"    «lambertEntry»(n,k) = a(n + 1) * t ^ (n + 1) * (t ^ (n + 1)) ^ k ∧ "+
							"    |«lambertEntry»(n,k)| = |a(n + 1)| * t ^ (n + 1) * (t ^ (n + 1)) ^ k",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							exponent := c.TermAs[Nat]("(n + 1) * (k + 1)")
							entryPower := c.TermAs[Real]("t ^ ((n + 1) * (k + 1))")
							c.Show(
								"multiply the factored powers by the respective coefficients",
								ByArith(
									nonnegative,
									powers.At(k),
									real_sgn_abs.AbsMul.At(c.TermAs[Real]("a(n + 1)"), entryPower),
									real_pow.PowNonneg.At(t, exponent),
									real_sgn_abs.AbsFixedIffNonneg.At(entryPower)))
						}))
					geometric := b.Have(
						"the geometric series of ratio t^(n+1)",
						"real_sums(λk:num. (t ^ (n + 1)) ^ k, real_inv(&1 - t ^ (n + 1)))",
						By(powerInUnit, real_series.Geometric.At(power)))
					powersAtN := b.TermAs[Fun[Nat, Real]]("λk:num. (t ^ (n + 1)) ^ k")
					denominator := b.TermAs[Real]("&1 - t ^ (n + 1)")
					inverse := b.TermAs[Real]("real_inv(&1 - t ^ (n + 1))")
					signedFactor := b.TermAs[Real]("a(n + 1) * t ^ (n + 1)")
					absoluteFactor := b.TermAs[Real]("|a(n + 1)| * t ^ (n + 1)")
					b.Show(
						"scale the geometric sum by each numerator",
						By(
							factors,
							geometric,
							real_series.SumsScale.At(powersAtN, inverse, signedFactor),
							real_series.SumsScale.At(powersAtN, inverse, absoluteFactor),
							real_field.RealDivDef.At(signedFactor, denominator),
							real_field.RealDivDef.At(absoluteFactor, denominator)))
				}))
			domination := arg.Have(
				"the absolute row sums are bounded by a geometric term",
				"∀n:num. |«absoluteRows»(n)| ≤ «majorant»(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					succ := b.TermAs[Nat]("n + 1")
					power := b.TermAs[Real]("t ^ (n + 1)")
					smallDenom := b.TermAs[Real]("&1 - t")
					largeDenom := b.TermAs[Real]("&1 - t ^ (n + 1)")
					denominators := b.Have(
						"the common denominator is positive and at most each row denominator",
						"&0 < &1 - t ∧ &1 - t ≤ &1 - t ^ (n + 1) ∧ &0 ≤ &1 - t ^ (n + 1)",
						ByArith(belowOne, powerBounds.At(n)))
					inverses := b.Have(
						"the inverse of the row denominator is at most the common inverse",
						"&0 ≤ real_inv(&1 - t ^ (n + 1)) ∧ real_inv(&1 - t ^ (n + 1)) ≤ real_inv(&1 - t)",
						By(
							denominators,
							real_order_field.InvNonneg.At(largeDenom),
							real_order_field.InvAntitoneWeak.At(smallDenom, largeDenom)))
					numerator := b.TermAs[Real]("|a(n + 1)| * t ^ (n + 1)")
					numeratorBounds := b.Have(
						"the numerator is between zero and t^(n+1)",
						"&0 ≤ |a(n + 1)| * t ^ (n + 1) ∧ |a(n + 1)| * t ^ (n + 1) ≤ t ^ (n + 1)",
						ByArith(powerBounds.At(n), bounded.At(succ), real_sgn_abs.AbsNonneg.At(a.Apply(succ))))
					products := b.Have(
						"multiply the bounds on the numerator and inverse",
						"&0 ≤ «absoluteRows»(n) ∧ «absoluteRows»(n) ≤ «majorant»(n)",
						ByArith(
							numeratorBounds,
							inverses,
							real_order_ring.LessEqMul2.At(
								numerator,
								power,
								b.TermAs[Real]("real_inv(&1 - t ^ (n + 1))"),
								b.TermAs[Real]("real_inv(&1 - t)")),
							real_field.RealDivDef.At(numerator, largeDenom),
							real_field.RealDivDef.At(power, smallDenom)))
					b.Show(
						"the nonnegative row sum equals its absolute value",
						By(products, real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("«absoluteRows»(n)"))))
				}))
			tInUnit := arg.Have(
				"the common ratio t is in the unit interval",
				"|t| < &1",
				ByArith(nonnegative, belowOne, real_sgn_abs.AbsFixedIffNonneg.At(t)))
			majorantFactors := arg.Have(
				"factor the majorant as a multiple of t to the n",
				"∀n:num. «majorant»(n) = (t / (&1 - t)) * t ^ n",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Do(Simp(Fwd(real_field.RealDivDef), Fwd(real_pow.PowAddOne)))
					b.Show(
						"associate the common factors",
						ByArith())
				}))
			summableMajorant := arg.Have(
				"the majorant sums by the geometric series formula",
				"real_sums(«majorant», (t / (&1 - t)) * real_inv(&1 - t))",
				By(
					majorantFactors,
					tInUnit,
					real_series.Geometric.At(t),
					real_series.SumsScale.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. t ^ n"),
						arg.TermAs[Real]("real_inv(&1 - t)"),
						arg.TermAs[Real]("t / (&1 - t)"))))
			absoluteRows := arg.TermAs[Fun[Nat, Real]]("«absoluteRows»")
			T, summableRows := arg.ObtainAs[Real](
				"the absolute row sums converge by comparison with the majorant from index 0",
				"∃T:real. real_sums(«absoluteRows», T)",
				By(
					domination,
					summableMajorant,
					Where(real_series.Comparison, "a", absoluteRows).
						Where("b", arg.TermAs[Fun[Nat, Real]]("«majorant»")).
						Where("N", zero)))

			// Identify each fibre with the divisors of j + 1 by its first coordinate.
			fibreProduct := arg.Have(
				"both shifted coordinates multiply to j + 1 on the fibre",
				"∀j:num. ∀p:prod(num,num). p ∈ «lambertFibre»(j) ⇒ (fst(p) + 1) * (snd(p) + 1) = j + 1",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("j")
					b.FixAs[Prod[Nat, Nat]]("p")
					inFibre := b.Assume()
					b.Show(
						"undo the subtraction of one in the index",
						ByArith(inFibre))
				}))
			project := arg.TermAs[Fun[Prod[Nat, Nat], Nat]]("λp:prod(num,num). fst(p) + 1")
			divisorImage := arg.Have(
				"the shifted first coordinates form exactly the divisors",
				"∀j:num. image(λp:prod(num,num). fst(p) + 1, «lambertFibre»(j)) = «divisors»(j)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Do(Simp(Fwd(set_basic.Extension), Fwd(set_basic.InImage)))
					d := b.FixAs[Nat]("d")
					b.Iff()
					b.Forward(
						"represent a divisor and its quotient by the shifted coordinates",
						func(c *Argument, divides Fact) {
							e, quotient := c.ObtainAs[Nat](
								"the divisor has a quotient",
								"∃e:num. j + 1 = d * e",
								By(divides, nat_divides.DividesFactor.At(d, c.TermAs[Nat]("j + 1"))))
							positive := c.Have(
								"the positive product has positive factors",
								"0 < d ∧ 0 < e",
								ByArith(quotient, nat_arith.MulEqZero.At(d, e)))
							dPredecessor := c.TermAs[Nat]("d - 1")
							ePredecessor := c.TermAs[Nat]("e - 1")
							pair, predecessors := c.ObtainAs[Prod[Nat, Nat]](
								"the pair of the predecessors of the two factors",
								"∃p:prod(num,num). d = fst(p) + 1 ∧ e = snd(p) + 1",
								Witness(c.TermAs[Prod[Nat, Nat]]("(d - 1, e - 1)")),
								ByArith(
									positive,
									pairs.Fst.At(dPredecessor, ePredecessor),
									pairs.Snd.At(dPredecessor, ePredecessor)))
							c.Take(pair)
							c.Show(
								"its first coordinate is d − 1, and its shifted coordinates multiply to j + 1",
								ByArith(quotient, predecessors))
						})
					b.Backward(
						"each first coordinate supplies a divisor",
						func(c *Argument, inImage Fact) {
							p, point := c.UnpackAs[Prod[Nat, Nat]](inImage, "p")
							c.Show(
								"the second shifted coordinate is a quotient",
								By(
									point,
									fibreProduct.At(j, p),
									nat_divides.DividesOwnMultiple.At(c.TermAs[Nat]("fst(p) + 1"), c.TermAs[Nat]("snd(p) + 1"))))
						})
				}))
			fibreInjective := arg.Have(
				"a first coordinate determines the pair on each fibre",
				"∀j:num. injective_on(«lambertFibre»(j), λp:prod(num,num). fst(p) + 1)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Do(Simp(Fwd(functions.InjectiveOnDef)))
					p := b.FixAs[Prod[Nat, Nat]]("p")
					r := b.FixAs[Prod[Nat, Nat]]("r")
					matches := b.Assume()
					commonProduct := b.Have(
						"write both products with the same first factor",
						"(fst(p) + 1) * (snd(p) + 1) = (fst(p) + 1) * (snd(r) + 1)",
						By(matches, fibreProduct.At(j, p), fibreProduct.At(j, r)))
					coordinates := b.Have(
						"cancel the common positive first factor",
						"fst(p) = fst(r) ∧ snd(p) = snd(r)",
						ByArith(
							commonProduct,
							matches,
							nat_arith.MulEqLCancel.At(
								b.TermAs[Nat]("fst(p) + 1"), b.TermAs[Nat]("snd(p) + 1"), b.TermAs[Nat]("snd(r) + 1"))))
					b.Show(
						"a pair is determined by its two coordinates",
						By(coordinates, pairs.PairEta.At(p), pairs.PairEta.At(r)))
				}))
			finiteFibres := arg.Have(
				"each fibre is finite by the injective projection onto divisors",
				"∀j:num. finite(«lambertFibre»(j))",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Show(
						"transport finiteness along the injective projection",
						ByArith(
							divisorImage.At(j),
							fibreInjective.At(j),
							nat_divides.DivisorsFinite.At(b.TermAs[Nat]("j + 1")),
							finite_set.FiniteImageInjEq.At(project, b.TermAs[Set[Prod[Nat, Nat]]]("«lambertFibre»(j)"))))
				}))
			grouped := arg.Have(
				"the grouped terms are the divisor sums times their common power",
				"«groupedTerms» = (λj:num. (Σ_{d∈«divisors»(j)} a(d)) * t ^ (j + 1))",
				Funext(),
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					fibre := b.TermAs[Set[Prod[Nat, Nat]]]("«lambertFibre»(j)")
					divisorSet := b.TermAs[Set[Nat]]("«divisors»(j)")
					weightedDivisors := b.TermAs[Fun[Nat, Real]]("λd:num. a(d) * t ^ (j + 1)")
					weightedFibre := b.TermAs[Fun[Prod[Nat, Nat], Real]](
						"λp:prod(num,num). a(fst(p) + 1) * t ^ (j + 1)")
					termwise := b.Have(
						"the exponent is constant on the fibre",
						"∀p:prod(num,num). p ∈ «lambertFibre»(j) ⇒ «fibreTerm»(p) = a(fst(p) + 1) * t ^ (j + 1)",
						Derive(func(c *Argument) {
							p := c.FixAs[Prod[Nat, Nat]]("p")
							inFibre := c.Assume()
							c.Show(
								"substitute the fibre product as the exponent",
								By(inFibre, fibreProduct.At(j, p)))
						}))
					reindexed := b.Have(
						"reindex the fibre sum by the corresponding divisors",
						"Σ_{p∈«lambertFibre»(j)} a(fst(p) + 1) * t ^ (j + 1) = Σ_{d∈«divisors»(j)} a(d) * t ^ (j + 1)",
						By(
							divisorImage.At(j),
							fibreInjective.At(j),
							real_sum.Image.At(fibre, project, weightedDivisors),
							functions.ComposeApply.At(weightedDivisors, project)))
					b.Show(
						"factor the common power out of the divisor sum",
						By(
							termwise,
							reindexed,
							real_sum.Congruence.At(fibre, b.TermAs[Fun[Prod[Nat, Nat], Real]]("«fibreTerm»"), weightedFibre),
							real_sum.ScalarRight.At(b.TermAs[Real]("t ^ (j + 1)"), a, divisorSet)))
				}))
			_, S, regrouped := arg.Obtain2As[Fun[Nat, Real], Real](
				"regroup the absolutely summable double series by the products of its indices",
				"∃r:(num → real). ∃S:real. "+
					"    (∀n:num. real_sums(λk:num. «lambertEntry»(n,k), r(n))) ∧ "+
					"    real_sums(r, S) ∧ "+
					"    real_sums(«groupedTerms», S)",
				By(
					rows,
					summableRows,
					finiteFibres,
					extended_nonneg_real.AbsolutelySummableRegroup.At(
						arg.TermAs[Fun2[Nat, Nat, Real]]("«lambertEntry»"),
						arg.TermAs[Op[Nat]]("«productIndex»"),
						absoluteRows,
						T)))
			regroupedParts := arg.Conjuncts(
				regrouped,
				"row n sums to r(n)",
				"the row sums r sum to S",
				"the grouped terms sum to S")
			arg.Take(S)
			rowsEqual := arg.Have(
				"each abstract row sum equals the calculated geometric sum",
				"r = «signedRows»",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the value of a convergent row sum is unique",
						By(
							regroupedParts[0].At(n),
							rows.At(n),
							real_series.SumsUnique.At(b.TermAs[Fun[Nat, Real]]("λk:num. «lambertEntry»(n,k)"),
								b.TermAs[Real]("r(n)"), b.TermAs[Real]("«signedRows»(n)"))))
				}))
			arg.Show(
				"replace both sums by the explicitly calculated series",
				By(rowsEqual, grouped, regroupedParts[1], regroupedParts[2]))
		}),
})}
