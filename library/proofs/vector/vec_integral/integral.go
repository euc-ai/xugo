// integral.go — the integral over ℝⁿ of continuous functions of rapid
// decay. On the line the Lebesgue integral of a continuous function with
// compact support is its Riemann integral over any interval holding the
// support; each slice integral of a continuous function of rapid decay on
// ℝⁿ⁺¹ is again one in the remaining coordinate, and integrable, which is
// what makes the iterated integral linear and monotone. The integral of a
// product of functions of separate coordinates is the product of their
// integrals.

package vec_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegralCongruence — the integral over ℝⁿ reads its integrand only at
// n-vectors.
var IntegralCongruence = integralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IntegralCongruence",
	Key:  "prop_d044b21bcfed668b",
	Reading: "Unconditional: no continuity is asked, the " +
		"definition evaluating g only at the n-vectors it builds.",
	Deps: []registry.EntryLike{VecIntegralDef, euclidean_topology.AppendCoordinateVec},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"∀x:(num → real). vec⟨n⟩(x) ⇒ g(x) = h(x)",
		},
		Conclusion: "vec_integral⟨n⟩(g) = vec_integral⟨n⟩(h)",
	},
		"induction on n for all g, h: the zero vector is a 0-vector, and «append»(x, t) "+
			"is an (n + 1)-vector for x an n-vector (euclidean_topology.AppendCoordinateVec), "+
			"so the slices of g and h agree at every n-vector and their integrals at every t"),
})}

// IntegralSliceContinuous — each slice of a continuous function with
// compact support on ℝⁿ⁺¹ is one on ℝⁿ, and the slice integral is
// continuous in the last coordinate and zero for it large.
var IntegralSliceContinuous = integralSliceContinuousThm{family.Add(registry.ProofEntry{
	Name: "IntegralSliceContinuous",
	Key:  "prop_4e5a07464dc577d",
	Deps: []registry.EntryLike{
		IntegralBound,
		IntegralAdd,
		IntegralScale,
		CcRapid,
		complete_metric.HeineCantor,
		euclidean_topology.HeineBorel,
		euclidean_topology.AppendCoordinateContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real).",
		Hypotheses: []string{
			"«Cc»(n + 1, g)",
		},
		Conclusion: "(∀t:real. «Cc»(n, λx:(num → real). g(«append»(x, t)))) ∧ " +
			"real_continuous_on(𝕌, λt:real. vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t)))) ∧ " +
			"∃R:real. ∀t:real. R < |t| ⇒ vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t))) = &0",
	},
		"the slices: g's support lies in a box ⟦−R, R⟧ⁿ⁺¹ (euclidean_topology.HeineBorel's "+
			"bound), so every slice vanishes off ⟦−R, R⟧ⁿ, and for |t| > R entirely; a slice is "+
			"continuous, x ↦ «append»(x, t) being so (AppendCoordinateContinuous). Continuity in "+
			"t: g is uniformly continuous on the box (complete_metric.HeineCantor), so for |t − "+
			"t'| small the two slices differ by at most ε at every n-vector; their difference "+
			"integrates to the difference of the integrals (IntegralAdd and IntegralScale, a "+
			"«Cc» function being «rapid» by CcRapid), and IntegralBound bounds it by ε·(2R)ⁿ"),
})}

// InnerIntegralContinuous — integrating a continuous function with compact
// support on ℝⁿ⁺ᵐ over its first n coordinates leaves one on ℝᵐ.
var InnerIntegralContinuous = innerIntegralContinuousThm{family.Add(registry.ProofEntry{
	Name: "InnerIntegralContinuous",
	Key:  "prop_32e20e5eab5f6712",
	Reading: "At m = 0 the result is a function on ℝ⁰ = {0}, continuous with compact " +
		"support for any g. Values at sequences that are not m-vectors are not read.",
	Deps: []registry.EntryLike{
		IntegralBound,
		IntegralAdd,
		IntegralScale,
		CcRapid,
		complete_metric.HeineCantor,
		euclidean_topology.HeineBorel,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀g:((num → real) → real).",
		Hypotheses: []string{
			"«Cc»(n + m, g)",
		},
		Conclusion: "«Cc»(m, λy:(num → real). vec_integral⟨n⟩(λx:(num → real). g(«join»(x, y))))",
	},
		"g's support lies in a box ⟦−R, R⟧ⁿ⁺ᵐ (euclidean_topology.HeineBorel's bound), so the "+
			"inner integrand vanishes for y outside ⟦−R, R⟧ᵐ, and for y an m-vector x ↦ g(«join»(x, "+
			"y)) is «Cc»(n), «join» being continuous; g is uniformly continuous "+
			"(complete_metric.HeineCantor), so for y, y' close the two inner integrands differ by at "+
			"most ε at every n-vector and vanish off ⟦−R, R⟧ⁿ, and their integrals differ by at most "+
			"ε·(2R)ⁿ (IntegralAdd, IntegralScale, IntegralBound) — jointly in all m coordinates of "+
			"y, which IntegralSliceContinuous, one coordinate at a time, does not give"),
})}

// IntegralBound — the integral of a function bounded by B and zero off the
// box ⟦−R, R⟧ⁿ is at most B times the box's volume.
var IntegralBound = integralBoundThm{family.Add(registry.ProofEntry{
	Name: "IntegralBound",
	Key:  "prop_31a18b70f51c8042",
	Reading: "No continuity is asked: the Lebesgue integral of each part is a supremum " +
		"over simple functions below it, monotone without measurability. &0 ≤ R is " +
		"load-bearing: with R < 0 and n odd every n-vector is outside the box when n ≥ 1, the " +
		"integral is 0, and B·(2R)ⁿ is negative for B > 0. At n = 0 the bound is |g(0)| ≤ B.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		IntegralCongruence,
		nonneg_integral.NonnegIntegralMono,
		measure_simple.SimpleIntegralIndicator,
		lebesgue_measure.LebesgueMeasureOn,
		lebesgue_integral.LebesgueNonnegIntegralEq,
		lebesgue_integral.LebesgueSimpleIff,
		lebesgue_integral.LebesgueSimpleIntegralEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real). ∀B R:real.",
		Hypotheses: []string{
			"&0 ≤ R",
			"∀x:(num → real). vec⟨n⟩(x) ⇒ |g(x)| ≤ B",
			"∀x:(num → real). vec⟨n⟩(x) ∧ (∃i:num. i < n ∧ R < |x(i)|) ⇒ g(x) = &0",
		},
		Conclusion: "|vec_integral⟨n⟩(g)| ≤ B * (&2 * R) ^ n",
	},
		"induction on n for all g: each slice satisfies the hypotheses in ℝⁿ, so its integral is "+
			"at most B·(2R)ⁿ in absolute value, and it is the zero function's, of integral 0, for |t| "+
			"> R (IntegralCongruence); the positive and negative parts of the slice integral then lie "+
			"below B·(2R)ⁿ times the indicator of ⟦−R, R⟧, so each part's integral is at most "+
			"2R·B·(2R)ⁿ (nonneg_integral.NonnegIntegralMono and SimpleIntegralIndicator at the "+
			"Lebesgue measure, both functions being nonnegative so that "+
			"lebesgue_integral.LebesgueNonnegIntegralEq reads their integrals as the general ones, and "+
			"LebesgueSimpleIff and LebesgueSimpleIntegralEq the indicator's) and so is their difference"),
})}

// IntegralAdd — the integral of a sum is the sum of the integrals.
var IntegralAdd = integralAddThm{family.Add(registry.ProofEntry{
	Name: "IntegralAdd",
	Key:  "prop_86c210160d1f565c",
	Reading: "«rapid» is load-bearing: at n = 1, g ≡ 1 has an infinite positive part, read as 0, and " +
		"with h a continuous bump between −1 and 0 of integral −1/2 the left side is 0 and the right −1/2.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		RapidSliceIntegral,
		measure_integral.IntegralAdd,
		lebesgue_measure.LebesgueMeasureOn,
		lebesgue_integral.LebesgueIntegrableIff,
		lebesgue_integral.LebesgueIntegralEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"«rapid»(n, g)",
			"«rapid»(n, h)",
		},
		Conclusion: "vec_integral⟨n⟩(λx:(num → real). g(x) + h(x)) = " +
			"vec_integral⟨n⟩(g) + vec_integral⟨n⟩(h)",
	},
		"induction on n: the slices of g + h are the sums of the slices, of integral the sum "+
			"by the induction hypothesis; the slice integrals of g and h are Lebesgue integrable "+
			"(RapidSliceIntegral), and measure_integral.IntegralAdd at the Lebesgue measure, read "+
			"through lebesgue_integral.LebesgueIntegrableIff and LebesgueIntegralEq, adds them"),
})}

// IntegralScale — the integral of a multiple is the multiple of the
// integral.
var IntegralScale = integralScaleThm{family.Add(registry.ProofEntry{
	Name: "IntegralScale",
	Key:  "prop_e8a86c85e3ecf24d",
	Reading: "No hypothesis: the scaling holds at every function, the defined value of a " +
		"non-integrable one included, since extended_to_real reads an infinite part as 0 on both sides.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		IntegralCongruence,
		nonneg_integral.NonnegIntegralScale,
		lebesgue_measure.LebesgueMeasureOn,
		lebesgue_integral.LebesgueNonnegIntegralEq,
	},
	Build: family.Card(
		"∀n:num. ∀g:((num → real) → real). ∀a:real. "+
			"    vec_integral⟨n⟩(λx:(num → real). a * g(x)) = a * vec_integral⟨n⟩(g)",
		"induction on n: the slices of a·g are a times those of g, of integral a times theirs by the "+
			"hypothesis at n. On the line lebesgue_integral(a·F) = a·lebesgue_integral(F) at every F: for a "+
			"≥ 0 the positive and negative parts of a·F are a times those of F, for a < 0 they are −a times "+
			"the swapped parts, and the nonnegative integral scales (nonneg_integral.NonnegIntegralScale at "+
			"the Lebesgue measure, through lebesgue_integral.LebesgueNonnegIntegralEq), an infinite part "+
			"staying infinite and read as 0 by extended_to_real"),
})}

// IntegralSum — the integral of a finite sum is the sum of the integrals.
var IntegralSum = integralSumThm{family.Add(registry.ProofEntry{
	Name:    "IntegralSum",
	Key:     "prop_675ce117c291ec3c",
	Reading: "At N = 0 both sides are 0, the integral of the zero function.",
	Deps:    []registry.EntryLike{IntegralAdd, IntegralCongruence},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀h:(num → (num → real) → real).",
		Hypotheses: []string{
			"∀i:num. i < N ⇒ «rapid»(n, h(i))",
		},
		Conclusion: "vec_integral⟨n⟩(λx:(num → real). Σ_{i<N} h(i)(x)) = Σ_{i<N} vec_integral⟨n⟩(h(i))",
	},
		"induction on N with IntegralAdd, a finite sum of continuous functions of rapid decay being "+
			"one; the zero function integrates to 0 (induction on n, lebesgue_integral of the zero function)"),
})}

// IntegralMono — the integral is monotone.
var IntegralMono = integralMonoThm{family.Add(registry.ProofEntry{
	Name: "IntegralMono",
	Key:  "prop_ef8a09944381051b",
	Reading: "«rapid»(n, h) is load-bearing: at n = 1 a bump g with 0 ≤ " +
		"g ≤ 1 and positive integral lies below h ≡ 1, whose integral reads 0.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		RapidSliceIntegral,
		measure_integral.IntegralMono,
		lebesgue_integral.LebesgueIntegrableIff,
		lebesgue_integral.LebesgueIntegralEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"«rapid»(n, g)",
			"«rapid»(n, h)",
			"∀x:(num → real). vec⟨n⟩(x) ⇒ g(x) ≤ h(x)",
		},
		Conclusion: "vec_integral⟨n⟩(g) ≤ vec_integral⟨n⟩(h)",
	},
		"induction on n: the slice integrals compare at every t by the induction hypothesis and are "+
			"integrable (RapidSliceIntegral), and measure_integral.IntegralMono, read on the line through "+
			"lebesgue_integral.LebesgueIntegrableIff and LebesgueIntegralEq, compares their integrals"),
})}

// CcRapid — a continuous function with compact support decreases rapidly:
// the support K is compact, so its points have norm at most some B and g,
// whose values on K form a compact set of reals, is at most some M in
// absolute value there; on K the weight (1 + ⟪x, x⟫)ᵖ is then at most
// (1 + B²)ᵖ, and off K g vanishes.
var CcRapid = ccRapidThm{family.Add(registry.ProofEntry{
	Name: "CcRapid",
	Key:  "prop_927edaac09441f55",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀g:((num → real) → real).",
		Hypotheses: []string{"«Cc»(n, g)"},
		Conclusion: "«rapid»(n, g)",
	}, func(a *Argument, n *Expr[Nat], g *Arrow[Fun[Nat, Real], Real], continuity, support Fact) {
		K, supported := a.UnpackAs[Set[Fun[Nat, Real]]](
			a.Unfolded(support, vec_smooth.CompactlySupportedInDef), "K")
		onK := a.Conjuncts(
			supported,
			"K is compact",
			"K lies in ℝⁿ",
			"g vanishes at the n-vectors off K")
		compactK, vanishes := onK[0], onK[2]
		_, radius := a.ObtainAs[Real](
			"K is bounded, a compact set of ℝⁿ: its points have norm at most some B",
			"∃B:real. ∀x:(num → real). x ∈ K ⇒ ‖x‖_n ≤ B",
			By(euclidean_topology.CompactIffClosedBounded.At(n, K), compactK),
			Named("B"))
		_, height := a.ObtainAs[Real](
			"g is at most some M in absolute value on K, its values there a "+
				"compact set of reals, the image of the compact K under a continuous map",
			"∃M:real. ∀x:(num → real). x ∈ K ⇒ |g(x)| ≤ M",
			By(
				compactK,
				real_topology.CompactBounded.At(a.TermAs[Set[Real]]("image(g, K)")),
				continuous.ImageCompact.Read(continuity).At(K),
				At(set_image.FunInImage, g, K)),
			Named("M"))
		decay := a.Have(
			"every power of 1 + ⟪x, x⟫ times |g| is at most (1 + B²)ᵖ·|M|",
			"∀p:num. ∃C:real. ∀x:(num → real). vec⟨n⟩(x) ⇒ real_pow(&1 + ⟪x, x⟫_n, p) * |g(x)| ≤ C",
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				b.Take(b.Term("real_pow(&1 + B ^ 2, p) * |M|"))
				x := b.VecFixAs[Real, DimN]("x")
				isVec := b.Assume()
				base := b.TermAs[Real]("&1 + B ^ 2")
				b.Cases(b.Term("x ∈ K"))
				b.When(
					"on K both factors are bounded",
					func(c *Argument, xInK Fact) {
						weight := c.Have(
							"the weight at x is at most (1 + B²)ᵖ, ⟪x, x⟫ being ‖x‖² and ‖x‖ at most B",
							"real_pow(&1 + ⟪x, x⟫_n, p) ≤ real_pow(&1 + B ^ 2, p)",
							ByArith(
								radius.At(x),
								xInK,
								euclidean.NormPow2.At(x),
								euclidean.NormNonneg.At(x),
								real_pow.PowMonoBase.At(c.TermAs[Real]("&1 + ⟪x, x⟫_n"), base, p)))
						c.Show(
							"so the product is at most (1 + B²)ᵖ·|M|, the bound being nonnegative",
							ByArith(height.At(x), xInK, weight, real_pow.PowNonneg.At(base, p)))
					})
				b.Otherwise(
					"off K g vanishes",
					func(c *Argument, xOffK Fact) {
						c.Show(
							"so the product is 0, below the nonnegative (1 + B²)ᵖ·|M|",
							ByArith(vanishes.At(x), isVec, xOffK, real_pow.PowNonneg.At(base, p)))
					})
			}))
		a.Show(
			"g is continuous and decreases rapidly",
			By(continuity, decay))
	}),
})}

// RapidSliceIntegral — each slice of a continuous function of rapid decay on
// ℝⁿ⁺¹ is one on ℝⁿ, and the slice integral is continuous, of rapid decay
// and Lebesgue integrable in the last coordinate.
var RapidSliceIntegral = rapidSliceIntegralThm{family.Add(registry.ProofEntry{
	Name: "RapidSliceIntegral",
	Key:  "prop_f902d889172fffcf",
	Reading: "The Cc case is IntegralSliceContinuous; here the slice integral need not vanish " +
		"for large t, and its integrability is part of the claim. ⟪«append»(x, t), «append»(x, t)⟫ " +
		"= ⟪x, x⟫ + t² is what makes every slice «rapid». At n = 0 the slice integral is t ↦ g(t·e₀).",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		IntegralCongruence,
		lebesgue_riemann.LebesgueIntegralInterval,
		euclidean_topology.AppendCoordinateContinuous,
		measure_integral.IntegralAdd,
		measure_integral.IntegralMono,
		measure_integral.IntegrableDominated,
		integral_convergence.DominatedConvergence,
		lebesgue_measure.LebesgueMeasureOn,
		lebesgue_integral.LebesgueIntegrableIff,
		lebesgue_integral.LebesgueIntegralEq,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀g:((num → real) → real).",
		Hypotheses: []string{"«rapid»(n + 1, g)"},
		Conclusion: "(∀t:real. «rapid»(n, λx:(num → real). g(«append»(x, t)))) ∧ " +
			"real_continuous_on(𝕌, λt:real. vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t)))) ∧ " +
			"(∀p:num. ∃C:real. ∀t:real. " +
			"    real_pow(&1 + real_pow(t, 2), p) * |vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t)))| ≤ " +
			"    C) ∧ " +
			"lebesgue_integrable(λt:real. vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t))))",
	},
		"induction on n, carrying along that vec_integral⟨n⟩ is additive and monotone on the «rapid»(n) "+
			"functions — IntegralAdd and IntegralMono, which read this card and so are re-proved inside the "+
			"induction — and the weighted bound: a «rapid»(n) function h with |h(x)|·Πᵢ (1 + x(i)²) ≤ C on "+
			"ℝⁿ has |vec_integral⟨n⟩(h)| ≤ C·πⁿ. At n + 1 the slices of a combination are the combinations "+
			"of the slices, integrable by the hypothesis at n, and the one-variable integrals combine and "+
			"compare (measure_integral.IntegralAdd, IntegralMono at the Lebesgue measure, through "+
			"lebesgue_integral.LebesgueIntegrableIff and LebesgueIntegralEq); for the weighted bound the "+
			"slice at t obeys it with C·(1 + t²)⁻¹, so its integral is at most C·πⁿ·(1 + t²)⁻¹, and ∫(1 + "+
			"t²)⁻¹ = π. A slice is continuous (AppendCoordinateContinuous) and inherits the bound, ⟪x, x⟫ ≤ "+
			"⟪«append»(x, t), «append»(x, t)⟫. Bound in t: (1 + t²)ᵖ|g(«append»(x, t))| is at most C·Πᵢ (1 "+
			"+ x(i)²)⁻¹, the bound for the power p + n, so the weighted bound at n bounds the slice "+
			"integral by C·πⁿ·(1 + t²)⁻ᵖ (∫(1 + t²)⁻¹ = π over the line, the limit of its Riemann integrals "+
			"over ⟦−R, R⟧, LebesgueIntegralInterval). Continuity in t: dominated convergence at every level "+
			"(integral_convergence.DominatedConvergence), the weighted bound at each level giving the "+
			"dominating function of the next. Integrable: continuous, so measurable, and below C·(1 + "+
			"t²)⁻¹, which is integrable (measure_integral.IntegrableDominated)"),
})}

// RapidInnerIntegral — integrating a continuous function of rapid decay on
// ℝⁿ⁺ᵐ over its first n coordinates leaves one on ℝᵐ.
var RapidInnerIntegral = rapidInnerIntegralThm{family.Add(registry.ProofEntry{
	Name: "RapidInnerIntegral",
	Key:  "prop_bdedf678c83766fe",
	Reading: "At n = 0 the function is g itself, «join»(vec_zero, y) " +
		"being y; at m = 0 it is the one value vec_integral⟨n⟩(g), always " +
		"«rapid»(0). Values at sequences that are not m-vectors are not read.",
	Deps: []registry.EntryLike{
		RapidSliceIntegral,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders:    "∀n m:num. ∀g:((num → real) → real).",
		Hypotheses: []string{"«rapid»(n + m, g)"},
		Conclusion: "«rapid»(m, λy:(num → real). vec_integral⟨n⟩(λx:(num → real). g(«join»(x, y))))",
	},
		"for y an m-vector the inner integrand is «rapid»(n), «join» being continuous; (1 + ⟪y, y⟫)ᵖ "+
			"times it is at most C·Πᵢ (1 + x(i)²)⁻¹ by the bound for the power p + n, so the weighted bound "+
			"carried in RapidSliceIntegral's induction bounds the inner integral by C·πⁿ. Continuity in y, "+
			"jointly in all m coordinates: for y_k → y the inner integrands converge at every n-vector under "+
			"that same weighted bound, and dominated convergence at every level of the iterated integral, "+
			"each level's weighted bound dominating the next, (integral_convergence.DominatedConvergence, "+
			"the slices integrable by RapidSliceIntegral) passes the limit through"),
})}

// IntegralProduct — the integral of a product of functions of separate
// coordinates is the product of their integrals.
var IntegralProduct = integralProductThm{family.Add(registry.ProofEntry{
	Name: "IntegralProduct",
	Key:  "prop_3d1aea1786c7520c",
	Reading: "No hypothesis: each slice of such a product is a multiple of a " +
		"product of the same kind, and the Lebesgue integral of a multiple is the " +
		"multiple of the integral at every function (IntegralScale at n = 1), so " +
		"every level of the iterated integral factors. At n = 0 both sides are 1.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		IntegralCongruence,
		IntegralScale,
	},
	Build: family.Card(
		"∀n:num. ∀φ:(num → real → real). "+
			"    vec_integral⟨n⟩( "+
			"        λx:(num → real). module_sum(real_mul, &1, {i:num | i < n}, λi:num. φ(i, x(i)))) = "+
			"    module_sum(real_mul, &1, {i:num | i < n}, λi:num. lebesgue_integral(φ(i)))",
		"induction on n, proving at once vec_integral⟨n⟩(λx. c·Πᵢ φ(i, x(i))) = c·Πᵢ "+
			"lebesgue_integral(φ(i)) for every real c: at n + 1 the slice at t is c·φ(n, "+
			"t) times the product over i < n, «append»(x, t) keeping x's coordinates "+
			"below n, whose integral is c·φ(n, t)·Π_{i<n} lebesgue_integral(φ(i)) by the "+
			"hypothesis at n, and the integral over t of that multiple of φ(n) is the "+
			"multiple of its integral (IntegralScale at n = 1). At n = 0 both sides are c"),
})}
