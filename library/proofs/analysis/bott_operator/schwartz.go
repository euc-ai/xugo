// schwartz.go — the Schwartz class on ℝⁿ: its functions decrease rapidly,
// it is an algebra closed under the coordinates and the partial
// derivatives, it holds the Hermite functions, a Schwartz function with no
// Hermite coefficient is zero, and rapidly decreasing coefficients are the
// coefficients of a Schwartz function.

package bott_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/hermite_function"
	"github.com/euc-ai/xugo/library/proofs/real/real_uniform_convergence"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// SchwartzRapid — a Schwartz function is continuous and decreases rapidly.
var SchwartzRapid = schwartzRapidThm{family.Add(registry.ProofEntry{
	Name: "SchwartzRapid",
	Key:  "prop_ff78c1804868e4cb",
	Reading: "The bound is the word of length 0 in the definition, with the " +
		"power p doubled and the square root taken; continuity comes from smoothness " +
		"on ℝⁿ. Together they are vec_integral's «rapid» for re(f) and im(f).",
	Deps: []registry.EntryLike{schwartzDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀f:((num → real) → complex).",
		Hypotheses: []string{"bott_schwartz(n, f)"},
		Conclusion: "continuous_map(euclidean_topology(n), real_topology, λx:(num → real). re(f(x))) ∧ " +
			"continuous_map(euclidean_topology(n), real_topology, λx:(num → real). im(f(x))) ∧ " +
			"(∀p:num. ∃C:real. ∀x:(num → real). " +
			"    vec⟨n⟩(&0, x) ⇒ " +
			"    real_pow(&1 + real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2)), p) * |f(x)| ≤ C)",
	},
		"the word of length 0 is the function itself (ps_derivative_word at 0), so "+
			"the definition bounds (1 + |x|²)²ᵖ|f(x)|² by some C, and (1 + |x|²)ᵖ|f(x)| "+
			"by √C; a function smooth on the open set of n-vectors is continuous there"),
})}

// SchwartzAlgebra — the Schwartz class is closed under sums, complex
// multiples and products.
var SchwartzAlgebra = schwartzAlgebraThm{family.Add(registry.ProofEntry{
	Name: "SchwartzAlgebra",
	Key:  "prop_29060126f6e8e7d8",
	Deps: []registry.EntryLike{
		SchwartzRapid,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothSub,
		vec_smooth.PartialDerivativeAdd,
		vec_smooth.PartialDerivativeMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀f g:((num → real) → complex). ∀c:complex.",
		Hypotheses: []string{"bott_schwartz(n, f)", "bott_schwartz(n, g)"},
		Conclusion: "bott_schwartz(n, λx:(num → real). f(x) + g(x)) ∧ " +
			"bott_schwartz(n, λx:(num → real). c * f(x)) ∧ " +
			"bott_schwartz(n, λx:(num → real). f(x) * g(x))",
	},
		"the real and imaginary parts of a sum, a multiple and a product are sums and products of "+
			"those of f, g and c, smooth by vec_smooth.SmoothAdd, SmoothSub and SmoothMul, and zero off ℝⁿ "+
			"with f and g. A derivative word of a product is, by the Leibniz rule iterated along the word "+
			"(vec_smooth.PartialDerivativeAdd, PartialDerivativeMul, induction on the word's length), a "+
			"finite sum over the splittings of the word of products of subwords of f and g; each term is "+
			"bounded by the bound of one factor at the power p and a bound of the other at power 0"),
})}

// SchwartzDerivativeCoordinate — the Schwartz class is closed under
// multiplication by a coordinate and under a partial derivative.
var SchwartzDerivativeCoordinate = schwartzDerivativeCoordinateThm{family.Add(registry.ProofEntry{
	Name: "SchwartzDerivativeCoordinate",
	Key:  "prop_ca432c1422dad796",
	Reading: "The coordinate half holds for every i: for i ≥ n, x(i)·f(x) is 0, x(i) " +
		"being 0 on ℝⁿ and f 0 off it. i < n is load-bearing for the derivative: along a " +
		"coordinate i ≥ n a Schwartz function jumps to 0 off ℝⁿ. Off ℝⁿ the derivative " +
		"is 0, the line through a non-vector along a coordinate below n holding no vector.",
	Deps: []registry.EntryLike{
		SchwartzAlgebra,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothCoordinate,
		vec_smooth.PartialDerivativeMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n i:num. ∀f:((num → real) → complex).",
		Hypotheses: []string{"bott_schwartz(n, f)"},
		Conclusion: "bott_schwartz(n, λx:(num → real). complex_of_real(x(i)) * f(x)) ∧ " +
			"(i < n ⇒ " +
			"    bott_schwartz(n, " +
			"        λx:(num → real). " +
			"            complex_of_real(partial_derivative(λy:(num → real). re(f(y)), i, x)) + " +
			"            complex_i * complex_of_real(partial_derivative(λy:(num → real). im(f(y)), i, x))))",
	},
		"the partial derivative: a derivative word of ∂ᵢf is the word with i put first, j′(0) = i "+
			"and j′(l + 1) = j(l) (ps_derivative_word applies its last letter last), bounded by the "+
			"definition, and ∂ᵢ of a smooth function is smooth (vec_smooth.SmoothPartial). The "+
			"coordinate: a derivative word of xᵢf is xᵢ times the word of f plus, for each letter equal "+
			"to i, the word of f with that letter removed (Leibniz, vec_smooth.PartialDerivativeMul); "+
			"xᵢ² ≤ 1 + |x|², so the bound at power p + 1 covers the first term"),
})}

// HermiteSchwartz — the Hermite functions are Schwartz functions.
var HermiteSchwartz = hermiteSchwartzThm{family.Add(registry.ProofEntry{
	Name: "HermiteSchwartz",
	Key:  "prop_ad7635ddbc0e8dc2",
	Reading: "The COND is load-bearing: h_α is not 0 off ℝⁿ (h_0 at " +
		"the unit vector eₙ is h_0(0) ≠ 0), and a Schwartz function must be.",
	Deps: []registry.EntryLike{
		hermite_function.HermiteLadder,
		hermite_function.HermiteOrthonormal,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothComposeReal,
		vec_smooth.SmoothCoordinate,
	},
	Build: family.Card(
		"∀n:num. ∀α:(num → num). "+
			"    bott_schwartz(n, "+
			"        λx:(num → real). "+
			"            COND(vec⟨n⟩(&0, x), complex_of_real(hermite_function(n, α, x)), complex_of_real(&0)))",
		"h_α is a finite product of a polynomial in each coordinate times exp(−x(i)²/2), "+
			"smooth (vec_smooth.SmoothMul, SmoothComposeReal, SmoothCoordinate). Each derivative "+
			"word of it is a polynomial times exp(−|x|²/2), the derivative of p(t)exp(−t²/2) "+
			"being (p′(t) − tp(t))exp(−t²/2), and a polynomial times exp(−|x|²/2) is bounded by "+
			"every power of (1 + |x|²)⁻¹, exp(s) dominating every power of s"),
})}

// HermiteComplete — a Schwartz function orthogonal to every Hermite
// function is zero.
var HermiteComplete = hermiteCompleteThm{family.Add(registry.ProofEntry{
	Name: "HermiteComplete",
	Key:  "prop_d45abf9592ef6bdd",
	Reading: "bott_schwartz is load-bearing twice: it makes f 0 off ℝⁿ, which " +
		"no integral sees, and continuous, which turns zero almost everywhere into " +
		"zero at every n-vector. The h_α read α below n only, so the hypothesis " +
		"ranges over the indices of ℝⁿ; on ℝ⁰ it says re(f(0)) = im(f(0)) = 0.",
	Deps: []registry.EntryLike{
		SchwartzRapid,
		hermite_function.HermiteRecurrence,
		vec_integral.GaussianIntegral,
		vec_integral.Fubini,
		vec_integral.IntegralTranslate,
		vec_integral.IntegralSum,
		vec_integral.IntegralScale,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀f:((num → real) → complex).",
		Hypotheses: []string{
			"bott_schwartz(n, f)",
			"∀α:(num → num). " +
				"    vec_integral⟨n⟩(λx:(num → real). re(f(x)) * hermite_function(n, α, x)) = &0 ∧ " +
				"    vec_integral⟨n⟩(λx:(num → real). im(f(x)) * hermite_function(n, α, x)) = &0",
		},
		Conclusion: "f = (λx:(num → real). complex_of_real(&0))",
	},
		"the h_α span the polynomials times exp(−|x|²/2) (HermiteRecurrence, induction on the "+
			"degree), so g = f·exp(−|x|²/2) has every moment zero. Then its Fourier transform "+
			"vanishes: cos⟨ξ, x⟩ and sin⟨ξ, x⟩ are the sums of their power series, integrated "+
			"termwise under the domination exp(|ξ||x|)·|g| (integral_convergence.DominatedConvergence "+
			"at every level). A Gaussian approximate identity recovers g: the Fourier transform of "+
			"exp(−ε|ξ|²) is a Gaussian bump of width √ε (GaussianIntegral, completing the square, "+
			"IntegralTranslate), so by Fubini the integral of g against the normalized bump of width "+
			"√ε centred at any y is 0; as ε → 0 it tends to g(y), g being continuous and bounded "+
			"(SchwartzRapid). So g = 0, and f = 0, exp(−|x|²/2) having no zero"),
})}

// HermiteSynthesis — rapidly decreasing Hermite coefficients are the
// coefficients of a Schwartz function.
var HermiteSynthesis = hermiteSynthesisThm{family.Add(registry.ProofEntry{
	Name: "HermiteSynthesis",
	Key:  "prop_82c055decd3f5f27",
	Reading: "The restriction to α supported below n is load-bearing: two indices that " +
		"agree below n have the same h_α and so the same coefficient, which an arbitrary c " +
		"need not give. The weight (1 + Σ α(i))ᵖ is equivalent, up to constants, to " +
		"bott_energy's. On ℝ⁰ the one index is 0, and f is the constant c(0) at 0.",
	Deps: []registry.EntryLike{
		HermiteSchwartz,
		SchwartzAlgebra,
		SchwartzDerivativeCoordinate,
		hermite_function.HermiteLadder,
		hermite_function.HermiteOrthonormal,
		real_uniform_convergence.UniformLimitDerivative,
		real_uniform_convergence.UniformLimitContinuous,
		vec_integral.IntegralSum,
		vec_integral.IntegralScale,
		vec_integral.IntegralMono,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀c:((num → num) → complex).",
		Hypotheses: []string{
			"∀p:num. ∃C:real. " +
				"    &0 ≤ C ∧ " +
				"    ∀α:(num → num). " +
				"        (∀j:num. n ≤ j ⇒ α(j) = 0) ⇒ " +
				"        real_pow(&1 + real_sum({i:num | i < n}, λi:num. &(α(i))), p) * real_pow(|c(α)|, 2) ≤ C",
		},
		Conclusion: "∃f:((num → real) → complex). " +
			"    bott_schwartz(n, f) ∧ " +
			"    ∀α:(num → num). " +
			"        (∀j:num. n ≤ j ⇒ α(j) = 0) ⇒ " +
			"        complex_of_real( " +
			"            vec_integral⟨n⟩(λx:(num → real). re(f(x)) * hermite_function(n, α, x))) + " +
			"        complex_i * " +
			"        complex_of_real( " +
			"            vec_integral⟨n⟩(λx:(num → real). im(f(x)) * hermite_function(n, α, x))) = " +
			"        c(α)",
	},
		"f is the sum of c(α)·h_α over the indices supported below n. Every Schwartz bound of h_α "+
			"grows at most polynomially in |α|: xᵢ and ∂ᵢ are half-sums and half-differences of the "+
			"raising and lowering steps (hermite_function.HermiteLadder), of weights at most √(2|α| + "+
			"2), and the supremum of |h_β| grows polynomially by the one-variable inequality sup h² ≤ "+
			"2‖h‖₂‖h′‖₂ (the fundamental theorem of calculus and Cauchy–Schwarz) with "+
			"HermiteOrthonormal and the ladder. The coefficients decrease faster than every power of "+
			"1 + |α| and there are polynomially many indices of each size, so the series and every "+
			"derivative word of it converge uniformly with rapid decay; the limit is smooth with the "+
			"termwise derivatives (real_uniform_convergence.UniformLimitDerivative one coordinate at "+
			"a time, UniformLimitContinuous). Its coefficients: integrate termwise, the tails bounded "+
			"by ε·|h_β| (IntegralMono, IntegralScale), and HermiteOrthonormal leaves c(β)"),
})}
