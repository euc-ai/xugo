// fubini.go — the integral over ℝⁿ⁺ᵐ as an integral over ℝᵐ of integrals
// over ℝⁿ, in either order, for a continuous function of rapid decay; the
// integral of such a function is unchanged by a permutation of the
// coordinates and by a translation, and a linear change of variables
// multiplies it by the absolute value of the determinant.

package vec_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegralSplit — the integral over ℝⁿ⁺ᵐ is the integral over the last m
// coordinates of the integral over the first n.
var IntegralSplit = integralSplitThm{family.Add(registry.ProofEntry{
	Name: "IntegralSplit",
	Key:  "prop_e60d7c1e936b9ca7",
	Reading: "Unconditional: it is the definition's own order " +
		"of integration, the last coordinates outermost, grouped.",
	Deps: []registry.EntryLike{VecIntegralDef, IntegralCongruence},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀g:((num → real) → real).",
		Conclusion: "vec_integral⟨n + m⟩(g) = " +
			"vec_integral⟨m⟩(λy:(num → real). vec_integral⟨n⟩(λx:(num → real). g(«join»(x, y))))",
	},
		"induction on m for all g: at m = 0, «join»(x, vec_zero) is x at every n-vector "+
			"(IntegralCongruence); at m + 1 both sides integrate over the last coordinate t "+
			"outermost, and «join»(x, y with t at coordinate m) is «join»(x, y) with t at coordinate "+
			"n + m, so the induction hypothesis at the slice equates the integrands at every t"),
})}

// Fubini — Fubini's theorem: for a continuous function with compact
// support on ℝⁿ⁺ᵐ the two iterated integrals agree.
var Fubini = fubiniThm{family.Add(registry.ProofEntry{
	Name: "Fubini",
	Key:  "prop_9a6ae9aa5f750bbf",
	Reading: "The right side puts the first n coordinates outermost, the reverse of " +
		"IntegralSplit. At n = 0 or m = 0 it is IntegralCongruence, with no decay used.",
	Deps: []registry.EntryLike{
		IntegralSplit,
		InnerIntegralContinuous,
		IntegralSliceContinuous,
		RapidInnerIntegral,
		RapidSliceIntegral,
		lebesgue_riemann.LebesgueIntegralInterval,
		real_integral.ContinuousIntegrable,
		vec_smooth.BumpFunction,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀g:((num → real) → real).",
		Hypotheses: []string{
			"«rapid»(n + m, g)",
		},
		Conclusion: "vec_integral⟨n + m⟩(g) = " +
			"vec_integral⟨n⟩(λx:(num → real). vec_integral⟨m⟩(λy:(num → real). g(«join»(x, y))))",
	},
		"by IntegralSplit the left side integrates over y outermost; the heart is the plane, ∫∫ "+
			"F(s, t) ds dt = ∫∫ F(s, t) dt ds for F continuous with compact support, both sides being "+
			"limits of one double Riemann sum over a grid of ⟦−R, R⟧² (F uniformly continuous, "+
			"real_integral.ContinuousIntegrable, LebesgueIntegralInterval); with it, the two outermost "+
			"coordinates swap, the integral over the others being a function of both of them continuous "+
			"with compact support (InnerIntegralContinuous, jointly; IntegralSliceContinuous for the "+
			"one-variable integrals), and induction on m and then n carries each coordinate of y "+
			"inside. For g of rapid decay, cut it off: g·φ_R with φ_R a continuous cutoff equal to 1 on "+
			"the ball of radius R (vec_smooth.BumpFunction) has compact support, and both iterated "+
			"integrals of g·φ_R tend to those of g as R → ∞ by dominated convergence at every level "+
			"(integral_convergence.DominatedConvergence, the slices and the inner integrals of rapid "+
			"decay by RapidSliceIntegral and RapidInnerIntegral)"),
})}

// IntegralPermuteCoordinates — permuting the coordinates does not change
// the integral.
var IntegralPermuteCoordinates = integralPermuteCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "IntegralPermuteCoordinates",
	Key:  "prop_e7890046e594b6d2",
	Reading: "p moves only indices below n (symmetric_group's meaning), " +
		"so x ∘ p is an n-vector with x; that is load-bearing: at n = 1 the " +
		"transposition (0 1) sends s·e₀ to s·e₁, where g is unconstrained.",
	Deps: []registry.EntryLike{Fubini, IntegralSplit, IntegralCongruence, RapidInnerIntegral},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real). ∀p:permutation(num).",
		Hypotheses: []string{
			"«rapid»(n, g)",
			"p ∈ symmetric_group({i:num | i < n})",
		},
		Conclusion: "vec_integral⟨n⟩(λx:(num → real). g(λi:num. x(permutation_map(p, i)))) = " +
			"vec_integral⟨n⟩(g)",
	},
		"the adjacent transpositions (k, k + 1), k + 1 < n, generate the permutations "+
			"of {0, …, n − 1}; for one of them split ℝⁿ as ℝᵏ × ℝ² × ℝⁿ⁻ᵏ⁻² (IntegralSplit) "+
			"and swap the two middle integrals (Fubini at n = m = 1), the integral over the "+
			"first k coordinates being «rapid» in the others (RapidInnerIntegral)"),
})}

// IntegralTranslate — translation does not change the integral.
var IntegralTranslate = integralTranslateThm{family.Add(registry.ProofEntry{
	Name: "IntegralTranslate",
	Key:  "prop_4c5f56cb022abf1d",
	Reading: "vec⟨n⟩(a) is load-bearing: at n = 0 with a = e₀ the " +
		"left side is g(e₀), which «rapid»(0, g) does not constrain.",
	Deps: []registry.EntryLike{
		VecIntegralDef,
		lebesgue_riemann.LebesgueIntegralInterval,
		real_integral.IntegralSubstitution,
		RapidSliceIntegral,
		IntegralCongruence,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real). ∀a:(num → real).",
		Hypotheses: []string{
			"«rapid»(n, g)",
			"vec⟨n⟩(a)",
		},
		Conclusion: "vec_integral⟨n⟩(λx:(num → real). g(x + a)) = vec_integral⟨n⟩(g)",
	},
		"induction on n: the slice of x ↦ g(x + a) at t is the translate by a's first n "+
			"coordinates of g's slice at t + a(n), so the induction hypothesis turns the slice "+
			"integrals into those of g at t + a(n); on the line a translate of a continuous "+
			"integrable function of rapid decay (RapidSliceIntegral) has the same integral: "+
			"over ⟦−R, R⟧ the Riemann integrals agree (real_integral.IntegralSubstitution with "+
			"t ↦ t + a(n), LebesgueIntegralInterval), and R → ∞ by dominated convergence"),
})}

// IntegralLinearChange — under an invertible linear change of variables
// the integral is multiplied by the absolute value of the determinant.
var IntegralLinearChange = integralLinearChangeThm{family.Add(registry.ProofEntry{
	Name: "IntegralLinearChange",
	Key:  "prop_b5a301927e03e8e",
	Reading: "The nonzero determinant is load-bearing: for a singular L the left side " +
		"is the integral of 0. Linearity is asked on all sequences, vec_linear's meaning.",
	Deps: []registry.EntryLike{
		IntegralPermuteCoordinates,
		Fubini,
		IntegralTranslate,
		IntegralScale,
		lebesgue_riemann.LebesgueIntegralInterval,
		real_integral.IntegralSubstitution,
		determinant.DeterminantMultiplicative,
		matrix.MatrixCompose,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real). ∀L:((num → real) → num → real).",
		Hypotheses: []string{
			"«rapid»(n, g)",
			"vec_linear(L)",
			"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨n⟩(L(u))",
			"determinant(real_ring, n, matrix_of(n, L)) ≠ &0",
		},
		Conclusion: "vec_integral⟨n⟩( " +
			"    λx:(num → real). g(L(x)) * |determinant(real_ring, n, matrix_of(n, L))|) = " +
			"vec_integral⟨n⟩(g)",
	},
		"Gaussian elimination writes the matrix of L as a product of elementary matrices, and g ∘ E is "+
			"«rapid» for each invertible E, |Ex| being at least a constant times |x|; and both sides are "+
			"multiplicative along a product (matrix.MatrixCompose, determinant.DeterminantMultiplicative). A "+
			"permutation of the coordinates has |det| = 1 (IntegralPermuteCoordinates); scaling one "+
			"coordinate by c ≠ 0 has |det| = |c|, a one-variable substitution in that coordinate's integral, "+
			"brought innermost by Fubini (real_integral.IntegralSubstitution and LebesgueIntegralInterval "+
			"over ⟦−R, R⟧, then R → ∞ by integral_convergence.DominatedConvergence); adding c times "+
			"coordinate j to coordinate i ≠ j has det 1, a translation of the innermost integral over "+
			"coordinate i at fixed others (Fubini, IntegralTranslate at n = 1)"),
})}
