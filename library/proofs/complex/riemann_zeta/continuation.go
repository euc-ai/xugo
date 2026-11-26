// continuation.go — ζ on the half-plane Re s > 0: the regularized series
// «xi» is holomorphic there and is 1 at s = 1, ζ is the sum of n^(−s) for
// Re s > 1, and ζ(s) − 1/(s − 1) continues holomorphically to Re s > 0.

package riemann_zeta

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// XiSums — for Re s > 0 the regularized series converges, to «xi»(s) − 1.
var XiSums = xiSumsThm{family.Add(registry.ProofEntry{
	Name: "XiSums",
	Key:  "prop_bfd74173796e1085",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&0 < re(s)"},
		Conclusion: "complex_sums(«xiTerm»(s), «xi»(s) - &1)",
		Abbrev: Abbrev{
			{Name: "powers", Text: "λs:complex. λn:num. real_rpow(&(n + 1), -(re(s) + &1))"},
			{Name: "majorant", Text: "λs:complex. λn:num. |s - &1| * |s| * «powers»(s, n)"},
		},
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		powers := a.TermAs[Fun[Nat, Real]]("«powers»(s)")
		σ := a.TermAs[Real]("re(s) + &1")
		above := a.Have(
			"the exponent Re s + 1 of the power majorant exceeds 1",
			"&1 < re(s) + &1",
			ByArith(right))
		t, powerSum := a.UnpackAs[Real](GroupPremises(above, real_rpow.RpowSeriesConverges.At(σ)), "t")
		scale := a.TermAs[Real]("|s - &1| * |s|")
		scaled := a.Have(
			"scaling preserves summability",
			"real_sums(«majorant»(s), |s - &1| * |s| * t)",
			By(powerSum, real_series.SumsScale.At(powers, t, scale)))
		estimates := a.Have(
			"the majorant bounds each term's modulus",
			"∀n:num. |«xiTerm»(s, n)| ≤ «majorant»(s, n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				indices := b.Have(
					"the term bound applies at n + 1, as Re s ≥ −1, and reads as the majorant there",
					"-&1 ≤ re(s) ∧ 0 < n + 1 ∧ n + 1 + 1 = n + 2 ∧ -(re(s) + &1) = -re(s) - &1",
					ByArith(right))
				b.Show(
					"the term bound at n + 1",
					By(indices, complex_cpow.CpowTangentRemainderBound.At(s, b.TermAs[Nat]("n + 1"))))
			}))
		_, chosen := a.ObtainChosen(
			"comparison with the majorant yields a complex sum; choose the one appearing in ξ(s)",
			"∃v:complex. complex_sums(«xiTerm»(s), v)",
			estimates,
			scaled,
			complex_series.Comparison.At(
				a.TermAs[Fun[Nat, Complex]]("«xiTerm»(s)"),
				a.TermAs[Fun[Nat, Real]]("«majorant»(s)"),
				a.TermAs[Real]("|s - &1| * |s| * t")))
		a.Show(
			"the choice of the sum is ξ(s) − 1",
			ByArith(chosen))
	}),
})}

// XiHolomorphic — «xi» is holomorphic on Re s > 0: its terms are, and the
// term bound puts the n-th of them under (|s| + 1)²·(n + 1)^(−Re s − 1),
// so their series has a holomorphic sum there.
var XiHolomorphic = xiHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "XiHolomorphic",
	Key:  "prop_17d99d5ff36439e5",
	Build: family.Theorem(Statement{
		Conclusion: "holomorphic_on({s:complex | &0 < re(s)}, «xi»)",
		Abbrev: Abbrev{
			{Name: "halfPlane", Text: "{s:complex | &0 < re(s)}"},
			{Name: "exponential", Text: "λx:real. λw:complex. complex_cpow(&x, w)"},
			{Name: "product", Text: "λn:num. λw:complex. (w - &1) * «exponential»(&(n + 1), -w)"},
			{Name: "difference", Text: "λn:num. λw:complex. " +
				"    «exponential»(&(n + 1), &1 - w) - «exponential»(&(n + 2), &1 - w)"},
			{Name: "term", Text: "λn:num. λw:complex. «xiTerm»(w, n)"},
		},
	}, func(a *Argument) {
		S := a.TermAs[Set[Complex]]("«halfPlane»")
		universe := a.TermAs[Set[Complex]]("𝕌")
		one := a.TermAs[Complex]("&1")
		oneFunction := a.TermAs[Fun[Complex, Complex]]("λw:complex. &1")
		id := a.TermAs[Fun[Complex, Complex]]("λw:complex. w")
		neg := a.TermAs[Fun[Complex, Complex]]("λw:complex. -w")
		oneMinus := a.TermAs[Fun[Complex, Complex]]("λw:complex. &1 - w")
		minusOne := a.TermAs[Fun[Complex, Complex]]("λw:complex. w - &1")
		negative := a.Have(
			"negation is holomorphic on the half-plane",
			"holomorphic_on(«halfPlane», λw:complex. -w)",
			By(complex_derivative.HolomorphicOnId.At(S), complex_derivative.HolomorphicOnNeg.At(S, id)))
		affine := a.Have(
			"subtracting the identity from one or one from the identity preserves holomorphy",
			"holomorphic_on(«halfPlane», λw:complex. &1 - w) ∧ holomorphic_on(«halfPlane», λw:complex. w - &1)",
			By(
				complex_derivative.HolomorphicOnId.At(S),
				complex_derivative.HolomorphicOnConst.At(S, one),
				complex_derivative.HolomorphicOnSub.At(S, oneFunction, id),
				complex_derivative.HolomorphicOnSub.At(S, id, oneFunction)))
		shiftedPowers := a.Have(
			"the powers at exponents −w and 1 − w are holomorphic by composition",
			Statement{
				Binders: "∀x:real.", Hypotheses: []string{"&0 < x"},
				Conclusion: "holomorphic_on(«halfPlane», λw:complex. «exponential»(x, -w)) ∧ " +
					"holomorphic_on(«halfPlane», λw:complex. «exponential»(x, &1 - w))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Real]()
				positive := b.Assume()
				exponential := b.TermAs[Fun[Complex, Complex]]("«exponential»(x)")
				b.Show(
					"both affine maps take values in the domain of the entire power",
					By(
						positive,
						complex_cpow.CpowHolomorphicExponent.At(x),
						affine,
						negative,
						set_basic.InUniv.Inst[Complex](),
						complex_derivative.HolomorphicOnCompose.At(S, universe, exponential, neg),
						complex_derivative.HolomorphicOnCompose.At(S, universe, exponential, oneMinus),
						functions.ComposeApply))
			}))
		terms := a.Have(
			"each regularized term is holomorphic on the half-plane",
			"∀n:num. holomorphic_on(«halfPlane», «term»(n))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.Show(
					"products and differences preserve holomorphy at the two positive bases",
					ByArith(
						affine,
						shiftedPowers.At(b.TermAs[Real]("&(n + 1)")),
						shiftedPowers.At(b.TermAs[Real]("&(n + 2)")),
						complex_derivative.HolomorphicOnMul.At(S, minusOne,
							b.TermAs[Fun[Complex, Complex]]("λw:complex. «exponential»(&(n + 1), -w)")),
						complex_derivative.HolomorphicOnSub.At(S,
							b.TermAs[Fun[Complex, Complex]]("λw:complex. «exponential»(&(n + 1), &1 - w)"),
							b.TermAs[Fun[Complex, Complex]]("λw:complex. «exponential»(&(n + 2), &1 - w)")),
						complex_derivative.HolomorphicOnSub.At(S, b.TermAs[Fun[Complex, Complex]]("«product»(n)"),
							b.TermAs[Fun[Complex, Complex]]("«difference»(n)"))))
			}))
		bounded := a.Have(
			"each term is at most (|w| + 1)²·(n + 1)^(−Re w − 1) on the half-plane",
			Statement{
				Binders:    "∀n:num. ∀w:complex.",
				Hypotheses: []string{"&0 < re(w)"},
				Conclusion: "|«term»(n, w)| ≤ &1 * (|w| + &1) * (|w| + &1) * real_rpow(&(n + 1), -re(w) - &1)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				w := b.FixAs[Complex]()
				positive := b.Assume()
				modulus := b.TermAs[Real]("|w|")
				bound := b.TermAs[Real]("|w| + &1")
				translated := b.Have(
					"subtracting one increases the modulus by at most one",
					"|w - &1| ≤ |w| + &1",
					Simp(Fwd(complex_field.ComplexSubDef)),
					ByArith(
						complex_abs.AbsTriangle.At(w, b.TermAs[Complex]("-complex_of_real(&1)")),
						complex_abs.AbsNeg.At(one),
						complex_abs.AbsOfReal.At(b.TermAs[Real]("&1"))))
				factors := b.Have(
					"so the factor |w − 1|·|w| of the term bound is at most (|w| + 1)²",
					"|w - &1| * |w| ≤ (|w| + &1) * (|w| + &1)",
					ByArith(
						translated,
						real_order_ring.LessEqMul2.At(b.TermAs[Real]("|w - &1|"), bound, modulus, bound)))
				next := b.Have(
					"align the two successive indices",
					"n + 2 = n + 1 + 1",
					ByArith())
				b.Show(
					"the term bound at n + 1, its factor enlarged at the nonnegative power",
					Simp(Fwd(next)),
					ByArith(
						positive,
						factors,
						complex_cpow.CpowTangentRemainderBound.At(w, b.TermAs[Nat]("n + 1")),
						real_order_ring.LessEqMulRight.At(
							b.TermAs[Real]("|w - &1| * |w|"),
							b.TermAs[Real]("(|w| + &1) * (|w| + &1)"),
							b.TermAs[Real]("real_rpow(&(n + 1), -re(w) - &1)")),
						real_rpow.RpowNonneg.At(b.TermAs[Real]("&(n + 1)"), b.TermAs[Real]("-re(w) - &1"))))
			}))
		F, sums := a.ObtainAs[Fun[Complex, Complex]](
			"the dominated series has a holomorphic sum",
			"∃F:(complex → complex). "+
				"    (∀w:complex. &0 < re(w) ⇒ complex_sums(λn:num. «term»(n, w), F(w))) ∧ "+
				"    holomorphic_on(«halfPlane», F)",
			By(
				terms,
				bounded,
				dirichlet_series.DominatedSeriesHolomorphic.At(
					a.TermAs[Fun2[Nat, Complex, Complex]]("«term»"), a.TermAs[Real]("&1"))),
			Named("F"))
		parts := a.Conjuncts(
			sums,
			"F is the pointwise sum",
			"F is holomorphic")
		agree := a.Have(
			"uniqueness identifies ξ with F plus one on the half-plane",
			"∀w:complex. w ∈ «halfPlane» ⇒ «xi»(w) = F(w) + &1",
			Derive(func(b *Argument) {
				w := b.FixAs[Complex]()
				member := b.Assume()
				positive := b.Have(
					"the point has positive real part",
					"&0 < re(w)",
					BySets(member))
				b.Show(
					"both sums are sums of the same regularized series",
					ByArith(
						positive,
						parts[0].At(w),
						XiSums.At(w),
						complex_series.SumsUnique.At(
							b.TermAs[Fun[Nat, Complex]]("λn:num. «term»(n, w)"),
							b.TermAs[Complex]("F(w)"),
							b.TermAs[Complex]("«xi»(w) - &1"))))
			}))
		a.Show(
			"add the constant one to the holomorphic sum and transfer by agreement on the open half-plane",
			By(
				complex_topology.RightHalfPlaneOpen.At(a.TermAs[Real]("&0")),
				agree,
				parts[1],
				complex_derivative.HolomorphicOnConst.At(S, one),
				complex_derivative.HolomorphicOnAdd.At(S, F, oneFunction),
				complex_derivative.HolomorphicOnAgree.At(
					S,
					a.TermAs[Fun[Complex, Complex]]("«xi»"),
					a.TermAs[Fun[Complex, Complex]]("λw:complex. F(w) + &1"))))
	}),
})}

// XiAtOne — «xi» is 1 at s = 1.
var XiAtOne = xiAtOneThm{family.Add(registry.ProofEntry{
	Name: "XiAtOne",
	Key:  "prop_934428ef5bffec6b",
	Build: family.Theorem("«xi»(complex_of_real(&1)) = &1", func(a *Argument) {
		one := a.TermAs[Complex]("complex_of_real(&1)")
		zero := a.TermAs[Complex]("complex_of_real(&0)")
		terms := a.TermAs[Fun[Nat, Complex]]("«xiTerm»(complex_of_real(&1))")
		oneDifference := a.Have(
			"the difference 1 − 1 is zero",
			"complex_of_real(&1) - complex_of_real(&1) = complex_of_real(&0)",
			ByArith())
		vanishing := a.Have(
			"each term at 1 is zero since both powers in the difference are 1",
			"«xiTerm»(complex_of_real(&1)) = (λn:num. complex_of_real(&0))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the first term has a zero factor and the two zeroth powers cancel",
					ByArith(
						oneDifference,
						complex_cpow.CpowZeroExponent.At(b.TermAs[Complex]("complex_of_real(&(n + 1))")),
						complex_cpow.CpowZeroExponent.At(b.TermAs[Complex]("complex_of_real(&(n + 2))"))))
			}))
		sum := a.Have(
			"the series of zero terms sums to zero",
			"complex_sums(«xiTerm»(complex_of_real(&1)), complex_of_real(&0))",
			By(
				vanishing,
				real_series.SumsZero,
				complex_series.SumsOfReal.At(
					a.TermAs[Fun[Nat, Real]]("λn:num. &0"), a.TermAs[Real]("&0"))))
		positive := a.Have(
			"1 is in the half-plane of convergence",
			"&0 < re(complex_of_real(&1))",
			ByArith(complex_field.PartsOfReal.At(a.TermAs[Real]("&1"))))
		a.Show(
			"uniqueness gives ξ(1) − 1 = 0",
			ByArith(
				sum,
				positive,
				XiSums.At(one),
				complex_series.SumsUnique.At(terms, a.TermAs[Complex]("«xi»(complex_of_real(&1)) - &1"), zero)))
	}),
	Reading: "This is where «xi» and the product (s − 1)·ζ(s) " +
		"part ways: at s = 1 the product is 0, while «xi» is 1.",
})}

// ZetaSums — for Re s > 1, ζ(s) is the sum of n^(−s) over n ≥ 1.
var ZetaSums = zetaSumsThm{family.Add(registry.ProofEntry{
	Name: "ZetaSums",
	Key:  "prop_f56603fda694095c",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "dirichlet_sums(λn:num. &1, s, riemann_zeta(s))",
		Abbrev: Abbrev{
			{Name: "difference", Text: "λn:num. " +
				"    complex_cpow(&(n + 1), &1 - s) - complex_cpow(&(n + 2), &1 - s)"},
			{Name: "tail", Text: "λn:num. complex_cpow(&(n + 2), &1 - s)"},
			{Name: "scaled", Text: "λn:num. (s - &1) * complex_cpow(&(n + 1), -s)"},
			{Name: "realPower", Text: "λn:num. real_rpow(&(n + 1), -(re(s) - &1))"},
		},
	}, func(a *Argument, s *Expr[Complex], aboveOne Fact) {
		zero := a.TermAs[Complex]("complex_of_real(&0)")
		one := a.TermAs[Complex]("complex_of_real(&1)")
		oneReal := a.TermAs[Real]("&1")
		exponent := a.TermAs[Complex]("complex_of_real(&1) - s")
		difference := a.TermAs[Fun[Nat, Complex]]("«difference»")
		tail := a.TermAs[Fun[Nat, Complex]]("«tail»")
		addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		telescope := a.Have(
			"successive differences telescope to the endpoint powers",
			"∀n:num. Σ_{k∈0 .. n} «difference»(k) = complex_cpow(&(0 + 1), &1 - s) - «tail»(n)",
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"the first partial sum is its only difference",
					By(monoidal.IntervalPoint.Read(addition).At(b.TermAs[Nat]("0"), difference)))
				b.Step(
					"adding the next difference cancels the shared endpoint",
					func(c *Argument, ih Fact) {
						next := c.Have(
							"the next partial sum appends one difference",
							"Σ_{k∈0 .. suc(n)} «difference»(k) = Σ_{k∈0 .. n} «difference»(k) + «difference»(suc(n))",
							By(
								monoidal.IntervalClauses.Read(addition).At(difference),
								nat_order.ZeroLessEq.At(c.TermAs[Nat]("suc(n)"))))
						index := c.Have(
							"the consecutive differences share an index",
							"suc(n) + 1 = n + 2",
							ByArith())
						c.Show(
							"cancel the power at the shared index",
							ByArith(ih, next, index))
					})
			}))
		vanishes := a.Have(
			"the final endpoint power tends to zero",
			"complex_converges_to(«tail», complex_of_real(&0))",
			Derive(func(b *Argument) {
				delta := b.TermAs[Real]("re(s) - &1")
				zeroReal := b.TermAs[Real]("&0")
				exponentPart := b.Have(
					"the exponent has real part 1 − Re s",
					"re(complex_of_real(&1) - s) = -(re(s) - &1)",
					ByArith(complex_field.PartsSub.At(one, s), complex_field.PartsOfReal.At(oneReal)))
				positiveDelta := b.Have(
					"Re s exceeds one",
					"&0 < re(s) - &1",
					ByArith(aboveOne))
				realLimit := b.Have(
					"the corresponding real power tends to zero after shifting the index by one",
					"real_converges_to(λn:num. «realPower»(n + 1), &0)",
					By(
						positiveDelta,
						real_rpow.RpowNegTendsToZero.At(delta),
						real_sequences.LimitShift.At(b.TermAs[Fun[Nat, Real]]("«realPower»"), zeroReal)))
				modulus := b.Have(
					"the modulus of each endpoint power is the real power at the real part of the exponent",
					"∀n:num. |«tail»(n)| ≤ «realPower»(n + 1)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						base := c.TermAs[Real]("real_of_num(n + 2)")
						positiveBase := c.Have(
							"the base is positive",
							"&0 < real_of_num(n + 2)",
							ByArith())
						index := c.Have(
							"both sequences use the same base",
							"n + 2 = n + 1 + 1",
							ByArith())
						c.Show(
							"take the real power at the real part of the exponent",
							By(
								positiveBase,
								index,
								exponentPart,
								complex_cpow.AbsCpow.At(base, exponent),
								real_order_ring.LessEqRefl))
					}))
				b.Show(
					"so the endpoint powers are squeezed to zero by the vanishing real powers",
					By(
						modulus,
						realLimit,
						complex_topology.LimitSqueezeZero.At(tail, b.TermAs[Fun[Nat, Real]]("λn:num. «realPower»(n + 1)"))))
			}))
		correction := a.Have(
			"the telescoping correction series sums to one",
			"complex_sums(«difference», complex_of_real(&1))",
			Derive(func(b *Argument) {
				partial := b.Have(
					"each partial sum is one minus the last endpoint power",
					"(λn:num. Σ_{k∈0 .. n} «difference»(k)) = (λn:num. complex_of_real(&1) - «tail»(n))",
					Funext(),
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"the power at the first endpoint is one",
							ByArith(telescope.At(n), complex_cpow.CpowOneBase.At(exponent)))
					}))
				atOne := b.Have(
					"one minus zero is one",
					"complex_of_real(&1) - complex_of_real(&0) = &1",
					ByArith())
				b.Show(
					"the partial sums tend to one as the endpoint power vanishes",
					By(
						partial,
						vanishes,
						atOne,
						complex_topology.LimitConst.At(one),
						complex_topology.LimitSub.At(b.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(&1)"),
							tail, one, zero),
						complex_series.SumsIffPartialSums.At(difference, one)))
			}))
		positive := a.Have(
			"s is in the right half-plane",
			"&0 < re(s)",
			ByArith(aboveOne))
		scaled := a.TermAs[Fun[Nat, Complex]]("«scaled»")
		scaledSum := a.Have(
			"adding back the correction gives the scaled Dirichlet series",
			"complex_sums(«scaled», «xi»(s))",
			Derive(func(b *Argument) {
				regularized := b.Have(
					"the regularized terms sum to ξ minus one",
					"complex_sums(«xiTerm»(s), «xi»(s) - &1)",
					By(positive, XiSums.At(s)))
				terms := b.Have(
					"adding the corresponding correction cancels it in each term",
					"(λn:num. «xiTerm»(s, n) + «difference»(n)) = «scaled»",
					Funext(),
					b.ForEach(func(*Expr[Nat]) Action { return ByArith() }))
				sum := b.Have(
					"adding one restores ξ",
					"(«xi»(s) - &1) + &1 = «xi»(s)",
					ByArith())
				b.Show(
					"add the two convergent series",
					By(
						regularized,
						correction,
						terms,
						sum,
						complex_series.SumsAdd.At(
							b.TermAs[Fun[Nat, Complex]]("«xiTerm»(s)"), difference,
							b.TermAs[Complex]("«xi»(s) - &1"), one)))
			}))
		denominator := a.TermAs[Complex]("s - &1")
		inv := a.TermAs[Complex]("complex_inv(s - &1)")
		realParts := a.Have(
			"the real part of s − 1 differs from the real part of zero",
			"re(s - &1) ≠ re(complex_of_real(&0))",
			ByArith(
				aboveOne,
				complex_field.PartsSub.At(s, one),
				complex_field.PartsOfReal.At(oneReal),
				complex_field.PartsOfReal.At(a.TermAs[Real]("&0"))))
		nonzero := a.Have(
			"s − 1 is nonzero",
			"s - &1 ≠ complex_of_real(&0)",
			By(Normalized, realParts))
		inverse := a.Have(
			"the inverse cancels the factor s − 1",
			"complex_inv(s - &1) * (s - &1) = complex_of_real(&1)",
			By(nonzero, field.MulLeftInverse.Read(complex_field.Field).At(denominator)))
		terms := a.Have(
			"division leaves the Dirichlet terms",
			"(λn:num. complex_inv(s - &1) * «scaled»(n)) = "+
				"(λn:num. complex_of_real(&1) * complex_cpow(&(n + 1), -s))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"cancel s − 1 in the term",
					ByArith(Scaled(b.TermAs[Complex]("complex_cpow(&(n + 1), -s)"), inverse)))
			}))
		value := a.Have(
			"ξ divided by s − 1 is ζ",
			"complex_inv(s - &1) * «xi»(s) = riemann_zeta(s)",
			Simp(Fwd(RiemannZetaDef)),
			Simp(Fwd(complex_field.ComplexDivDef)),
			ByArith())
		a.Show(
			"scaling the series by the inverse gives the Dirichlet sum",
			Simp(Fwd(dirichlet_series.DirichletSumsDef)),
			By(scaledSum, terms, value, complex_series.SumsScale.At(scaled, a.TermAs[Complex]("«xi»(s)"), inv)))
	}),
	Reading: "This is the statement that riemann_zeta is ζ: " +
		"on Re s > 1 it is dirichlet_series of the constant 1.",
})}

// ZetaHolomorphic — ζ is holomorphic on Re s > 0 away from s = 1.
var ZetaHolomorphic = zetaHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "ZetaHolomorphic",
	Key:  "prop_ce7c96c4af4f5ef0",
	Build: family.Theorem("holomorphic_on({s:complex | &0 < re(s) ∧ s ≠ &1}, riemann_zeta)",
		func(a *Argument) {
			halfPlane := a.TermAs[Set[Complex]]("{s:complex | &0 < re(s)}")
			domain := a.TermAs[Set[Complex]]("{s:complex | &0 < re(s) ∧ s ≠ &1}")
			regularized := a.TermAs[Fun[Complex, Complex]]("«xi»")
			shift := a.TermAs[Fun[Complex, Complex]]("λs:complex. s - &1")
			subset := a.Have(
				"the punctured half-plane lies in the half-plane",
				"{s:complex | &0 < re(s) ∧ s ≠ &1} ⊆ {s:complex | &0 < re(s)}",
				BySets())
			numerator := a.Have(
				"the regularized series is holomorphic off the pole",
				"holomorphic_on({s:complex | &0 < re(s) ∧ s ≠ &1}, «xi»)",
				By(
					subset,
					XiHolomorphic,
					complex_derivative.HolomorphicOnSubset.At(halfPlane, domain, regularized)))
			denominator := a.Have(
				"the denominator s − 1 is a difference of holomorphic functions",
				"holomorphic_on({s:complex | &0 < re(s) ∧ s ≠ &1}, λs:complex. s - &1)",
				By(
					complex_derivative.HolomorphicOnId.At(domain),
					complex_derivative.HolomorphicOnConst.At(domain, a.TermAs[Complex]("&1")),
					complex_derivative.HolomorphicOnSub.At(
						domain,
						a.TermAs[Fun[Complex, Complex]]("λs:complex. s"),
						a.TermAs[Fun[Complex, Complex]]("λs:complex. complex_of_real(&1)"))))
			nonvanishing := a.Have(
				"the denominator does not vanish on the punctured half-plane",
				"∀z:complex. z ∈ {s:complex | &0 < re(s) ∧ s ≠ &1} ⇒ z - &1 ≠ &0",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					member := b.Assume()
					away := b.Have(
						"the domain excludes 1",
						"z ≠ complex_of_real(&1)",
						BySets(member))
					b.Show(
						"subtracting 1 leaves a nonzero value",
						ByArith(away))
				}))
			a.Show(
				"ζ is the quotient of these holomorphic functions",
				Unfold(RiemannZetaDef),
				By(
					nonvanishing,
					numerator,
					denominator,
					complex_derivative.HolomorphicOnDiv.At(domain, regularized, shift)))
		}),
	Reading: "The set is open, so this is holomorphy in the usual sense.",
})}

// ZetaContinuation — ζ(s) − 1/(s − 1) continues to a function holomorphic
// on the whole half-plane Re s > 0.
var ZetaContinuation = zetaContinuationThm{family.Add(registry.ProofEntry{
	Name: "ZetaContinuation",
	Key:  "prop_5afb68677a0eef83",
	Build: family.Theorem(Statement{
		Conclusion: "∃k:(complex → complex). " +
			"    holomorphic_on({s:complex | &0 < re(s)}, k) ∧ " +
			"    ∀s:complex. &0 < re(s) ∧ s ≠ &1 ⇒ riemann_zeta(s) = complex_inv(s - &1) + k(s)",
		Abbrev: Abbrev{
			{Name: "halfPlane", Text: "{z:complex | &0 < re(z)}"},
		},
	}, func(a *Argument) {
		S := a.TermAs[Set[Complex]]("«halfPlane»")
		one := a.TermAs[Complex]("complex_of_real(&1)")
		xi := a.TermAs[Fun[Complex, Complex]]("«xi»")
		open := complex_topology.RightHalfPlaneOpen.At(a.TermAs[Real]("&0"))
		convex := a.Have(
			"the segment between two points of the right half-plane stays in it",
			Statement{
				Binders: "∀u v:complex. ∀t:real.",
				Hypotheses: []string{
					"u ∈ «halfPlane»",
					"v ∈ «halfPlane»",
					"&0 ≤ t",
					"t ≤ &1",
				},
				Conclusion: "segment_path(u, v, t) ∈ «halfPlane»",
			},
			Derive(func(b *Argument) {
				b.FixAs[Complex]("u")
				b.FixAs[Complex]("v")
				t := b.FixAs[Real]("t")
				segment := b.Assume()
				ends := b.Have(
					"both endpoints have positive real part",
					"&0 < re(u) ∧ &0 < re(v)",
					BySets(segment))
				positive := b.Have(
					"the real part along the segment is a convex combination of the endpoint real parts",
					"&0 < re(segment_path(u, v, t))",
					Simp(
						Fwd(path_integral.SegmentPathDef),
						Fwd(complex_field.PartsAdd),
						Fwd(complex_field.PartsMul),
						Fwd(complex_field.PartsSub),
						Fwd(complex_field.PartsOfReal),
						Fwd(real_ring.MulLeftZero),
						Fwd(real_ring.SubRightZero)),
					Derive(func(c *Argument) {
						c.Cases(c.TermAs[Bool]("t = &0"))
						c.When(
							"at the initial endpoint",
							func(d *Argument, zero Fact) {
								d.Show(
									"the initial endpoint has positive real part",
									ByArith(zero, ends))
							})
						c.Otherwise(
							"at positive parameter",
							func(d *Argument, nonzero Fact) {
								d.Show(
									"the term t·Re v is positive and the term (1 − t)·Re u is nonnegative",
									ByArith(
										nonzero,
										ends,
										segment,
										real_order_ring.MulPos.At(t, d.TermAs[Real]("re(v)")),
										real_construction.LessEqMul.At(d.TermAs[Real]("&1 - t"), d.TermAs[Real]("re(u)"))))
							})
					}))
				b.Show(
					"positive real part is membership of the half-plane",
					BySets(positive))
			}))
		oneIn := a.Have(
			"the half-plane contains 1",
			"complex_of_real(&1) ∈ «halfPlane»",
			Derive(func(b *Argument) {
				positive := b.Have(
					"the real part of 1 is positive",
					"&0 < re(complex_of_real(&1))",
					Simp(Fwd(complex_field.PartsOfReal)),
					ByArith())
				b.Show(
					"1 has positive real part",
					BySets(positive))
			}))
		K, quotient := a.ObtainAs[Fun[Complex, Complex]](
			"the divided difference of ξ at 1 is continuous on the half-plane and holomorphic off 1",
			"∃K:(complex → complex). "+
				"    (∀z:complex. «xi»(z) - «xi»(complex_of_real(&1)) = K(z) * (z - &1)) ∧ "+
				"    complex_continuous_on(«halfPlane», K) ∧ "+
				"    holomorphic_on(«halfPlane» ∖ {complex_of_real(&1)}, K)",
			By(oneIn, XiHolomorphic, cauchy_integral.DifferenceQuotientHolomorphic.At(S, xi, one)),
			Named("K"))
		quotientParts := a.Conjuncts(
			quotient,
			"the factorization at 1",
			"continuity on the half-plane",
			"holomorphy off 1")
		F, primitive := a.ObtainAs[Fun[Complex, Complex]](
			"the divided difference has a primitive on the half-plane",
			"∃F:(complex → complex). ∀z:complex. z ∈ «halfPlane» ⇒ complex_derivative_at(F, z, K(z))",
			By(open, convex, quotientParts[1], quotientParts[2], cauchy_integral.ConvexPrimitive.At(S, K, one)),
			Named("F"))
		FHolomorphic := a.Have(
			"the primitive is holomorphic on the half-plane",
			"holomorphic_on(«halfPlane», F)",
			Simp(Fwd(complex_derivative.HolomorphicOnDef)),
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				member := b.Assume()
				b.Show(
					"the primitive has derivative K at this point",
					By(Normalized, member, primitive.At(z)))
			}))
		G, differentiated := a.ObtainAs[Fun[Complex, Complex]](
			"the derivative of the primitive is holomorphic",
			"∃G:(complex → complex). "+
				"    (∀z:complex. z ∈ «halfPlane» ⇒ complex_derivative_at(F, z, G(z))) ∧ "+
				"    holomorphic_on(«halfPlane», G)",
			By(open, FHolomorphic, cauchy_integral.HolomorphicDerivative.At(S, F)),
			Named("G"))
		derivativeParts := a.Conjuncts(
			differentiated,
			"G is a derivative of F",
			"G is holomorphic")
		agree := a.Have(
			"uniqueness of the derivative identifies K with G throughout the half-plane",
			"∀z:complex. z ∈ «halfPlane» ⇒ K(z) = G(z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				member := b.Assume()
				b.Show(
					"K and G are both derivatives of F at z",
					By(
						member,
						primitive.At(z),
						derivativeParts[0].At(z),
						complex_derivative.DerivativeUnique.At(F, z, b.TermAs[Complex]("K(z)"), b.TermAs[Complex]("G(z)"))))
			}))
		a.Show(
			"the divided difference is the holomorphic remainder after subtracting the pole",
			Witness(K),
			SplitConj(
				Case(
					"the divided difference agrees with a holomorphic function",
					By(open, derivativeParts[1], agree, complex_derivative.HolomorphicOnAgree.At(S, K, G))),
				Case(
					"the factorization gives the pole and remainder away from 1",
					Derive(func(b *Argument) {
						s := b.FixAs[Complex]("s")
						away := b.Assume()
						d := b.TermAs[Complex]("s - &1")
						inv := b.TermAs[Complex]("complex_inv(s - &1)")
						nonzero := b.Have(
							"the denominator is nonzero",
							"s - &1 ≠ complex_of_real(&0)",
							ByArith(away))
						factored := b.Have(
							"ξ(s) is 1 + K(s)·(s − 1), the factorization at 1 read with ξ(1) = 1",
							"«xi»(s) = complex_of_real(&1) + K(s) * (s - &1)",
							ByArith(quotientParts[0].At(s), XiAtOne))
						inverse := b.Have(
							"the denominator cancels its inverse",
							"(s - &1) * complex_inv(s - &1) = complex_of_real(&1)",
							By(nonzero, field.MulRightInverse.Read(complex_field.Field).At(d)))
						b.Show(
							"division gives the pole term plus K",
							Simp(Fwd(RiemannZetaDef)),
							Simp(Fwd(complex_field.ComplexDivDef)),
							ByArith(Scaled(inv, factored), Scaled(b.TermAs[Complex]("K(s)"), inverse)))
					}))))
	}),
	Reading: "This is the analytic continuation of ζ to Re s > 0: a simple pole at 1 with residue 1 " +
		"and nothing else. The continuation to the whole plane and the functional equation are not here.",
})}

// ZetaPole — (s − 1)·ζ(s) tends to 1 at s = 1.
var ZetaPole = zetaPoleThm{family.Add(registry.ProofEntry{
	Name: "ZetaPole",
	Key:  "prop_e61b26632f795c5f",
	Build: family.Card(
		"(λs:complex. (s - &1) * riemann_zeta(s)) ⟶ complex_of_real(&1) (at complex_of_real(&1))",
		"Off 1 the product is «xi»(s), and «xi» is continuous at 1 with value 1 (XiHolomorphic, "+
			"XiAtOne); a limit at a point reads only the punctured disc (complex_topology.LimitAtLocal)."),
	Deps: []registry.EntryLike{XiHolomorphic, XiAtOne},
})}
