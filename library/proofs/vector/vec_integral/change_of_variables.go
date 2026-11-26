// change_of_variables.go — the change of variables under a diffeomorphism
// of open sets of ℝⁿ, the integrand carried back multiplied by the absolute
// value of the Jacobian determinant; near each point first, then
// everywhere through a partition of unity. And the integral of a partial
// derivative of a function of class C¹ with compact support, which is 0.

package vec_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// ChangeOfVariablesLocal — each point of U has an open neighbourhood W on
// which the change of variables holds for every continuous integrand with
// compact support in the image of W.
var ChangeOfVariablesLocal = changeOfVariablesLocalThm{family.Add(registry.ProofEntry{
	Name: "ChangeOfVariablesLocal",
	Key:  "prop_75d1f6abd003c4ab",
	Deps: []registry.EntryLike{
		IntegralLinearChange,
		CcRapid,
		vec_smooth.SmoothInverseFunction,
		vec_smooth.JacobianDeterminantChain,
		Fubini,
		IntegralSplit,
		real_integral.IntegralSubstitution,
		lebesgue_riemann.LebesgueIntegralInterval,
		vec_smooth.SmoothPartitionOfUnity,
		IntegralSum,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V:((num → real) → bool). ∀φ:((num → real) → num → real). ∀a:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"vec_diffeomorphic_map⟨n⟩(U, V, φ)",
			"a ∈ U",
		},
		Conclusion: "∃W:set(num → real). " +
			"    W ∈ euclidean_topology(n) ∧ " +
			"    a ∈ W ∧ " +
			"    W ⊆ U ∧ " +
			"    ∀g:((num → real) → real). " +
			"        continuous_map(euclidean_topology(n), real_topology, g) ∧ " +
			"        vec_compactly_supported_in⟨n⟩(image(φ, W), g) ⇒ " +
			"        vec_integral⟨n⟩( " +
			"            λx:(num → real). COND(x ∈ W, g(φ(x)) * |vec_jacobian_determinant⟨n⟩(φ, x)|, &0)) = " +
			"        vec_integral⟨n⟩(g)",
	},
		"induction on n, n = 0 being the one point. Composing with the inverse of φ's Jacobian at a "+
			"(IntegralLinearChange) makes that Jacobian the identity, and then near a, φ = ψ ∘ χ with "+
			"χ(x) = (φ₀(x), …, φ_{n−2}(x), x_{n−1}) fixing the last coordinate and ψ(y) = (y₀, …, "+
			"y_{n−2}, φ_{n−1}(χ⁻¹(y))) changing only the last, both diffeomorphisms near a by the "+
			"inverse function theorem (vec_smooth.SmoothInverseFunction); the Jacobian determinants "+
			"multiply (JacobianDeterminantChain). χ: at each value of the last coordinate it is a "+
			"diffeomorphism of ℝⁿ⁻¹ with the same Jacobian determinant, and the slice integrand's "+
			"support is a compact set in its image that need lie in no one neighbourhood the induction "+
			"hypothesis gives; so the hypothesis is used in its global form, the local formula at n − 1 "+
			"patched over that compact set by a partition of unity (vec_smooth.SmoothPartitionOfUnity, "+
			"IntegralSum) as ChangeOfVariables does at n — which reads this card and so is re-proved "+
			"here, not cited — on each slice, under the outermost integral (IntegralSplit). ψ: at fixed "+
			"first n − 1 coordinates it is a one-variable substitution in the last "+
			"(real_integral.IntegralSubstitution), that integral brought innermost by Fubini"),
})}

// ChangeOfVariables — the change of variables formula for a diffeomorphism
// of open sets of ℝⁿ.
var ChangeOfVariables = changeOfVariablesThm{family.Add(registry.ProofEntry{
	Name: "ChangeOfVariables",
	Key:  "prop_a91dc71594cb0d82",
	Reading: "The left integrand is continuous on ℝⁿ with compact support in " +
		"U, the preimage of g's support under φ; it is 0 off U, where φ is not read.",
	Deps: []registry.EntryLike{
		ChangeOfVariablesLocal,
		vec_smooth.SmoothPartitionOfUnity,
		IntegralSum,
		CcRapid,
		vec_smooth.DiffeomorphismInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U V:((num → real) → bool). " +
			"∀φ:((num → real) → num → real). " +
			"∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"vec_diffeomorphic_map⟨n⟩(U, V, φ)",
			"continuous_map(euclidean_topology(n), real_topology, g)",
			"vec_compactly_supported_in⟨n⟩(V, g)",
		},
		Conclusion: "vec_integral⟨n⟩( " +
			"    λx:(num → real). COND(x ∈ U, g(φ(x)) * |vec_jacobian_determinant⟨n⟩(φ, x)|, &0)) = " +
			"vec_integral⟨n⟩(g)",
	},
		"g's support K is compact in V; the images under φ of the neighbourhoods W of "+
			"ChangeOfVariablesLocal are open (φ⁻¹ continuous, vec_smooth.DiffeomorphismInverse) "+
			"and cover K; a partition of unity on K subordinate to them "+
			"(vec_smooth.SmoothPartitionOfUnity) cuts g into finitely many pieces each "+
			"supported in one image, and both sides add up over the pieces (IntegralSum)"),
})}

// IntegralPartialZero — the integral of a partial derivative of a function
// of class C¹ with compact support is 0.
var IntegralPartialZero = integralPartialZeroThm{family.Add(registry.ProofEntry{
	Name: "IntegralPartialZero",
	Key:  "prop_c443ef8d64de9b21",
	Reading: "The decay of g is load-bearing: on ℝ¹ the derivative of a function that " +
		"is 0 far to the left and 1 far to the right has compact support and integrates to " +
		"1. The decay of the derivative is not implied by the decay of g and C¹: " +
		"exp(−x²)·sin(exp(x²)) decreases rapidly while its derivative holds 2x·cos(exp(x²)).",
	Deps: []registry.EntryLike{
		IntegralPermuteCoordinates,
		IntegralSplit,
		lebesgue_riemann.LebesgueIntegralInterval,
		real_integral.NewtonLeibnizContinuous,
		vec_smooth.PartialDerivativeValue,
		IntegralCongruence,
		RapidSliceIntegral,
		integral_convergence.DominatedConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀g:((num → real) → real). ∀j:num.",
		Hypotheses: []string{
			"vec_continuously_differentiable_on⟨n⟩({u:num → real | vec⟨n⟩(u)}, 1, g)",
			"«rapid»(n, g)",
			"«rapid»(n, partial_derivative(g, j))",
			"j < n",
		},
		Conclusion: "vec_integral⟨n⟩(partial_derivative(g, j)) = &0",
	},
		"move coordinate j to the front (IntegralPermuteCoordinates; the partial derivative of the "+
			"permuted function is the permuted partial derivative) and split off the first coordinate "+
			"innermost (IntegralSplit with n = 1): at fixed other coordinates the inner integral is of "+
			"the derivative of a C¹ function of one variable that decreases rapidly with its derivative: "+
			"over ⟦−R, R⟧ it is a Riemann integral by LebesgueIntegralInterval, g(R) − g(−R) by the "+
			"fundamental theorem of calculus (real_integral.NewtonLeibnizContinuous), and R → ∞ gives 0 "+
			"on the left by dominated convergence (integral_convergence.DominatedConvergence, the "+
			"derivative integrable by RapidSliceIntegral) and on the right by the decay of g"),
})}
