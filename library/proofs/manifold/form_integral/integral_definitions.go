// A finite positive-chart decomposition defines the integral relation and its operator.

package form_integral

import (
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var chartIntegralDef = chartIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "chartIntegralDef",
	Key:   "prop_2d80391480ff1489",
	Const: "manifold_chart_integral",
	Type: "num → " +
		"prod(set(A), A → num → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real",
	Dim: "n",
	Reading: "The identity-frame coefficient is integrated over all of Euclidean " +
		"n-space. For a top form with compact base support inside c, its normalized coordinate " +
		"coefficient is globally smooth and compactly supported inside the coordinate image.",
	Equations: []string{
		"∀n:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_chart_integral⟨n⟩(c, ω) = " +
			"    vec_integral⟨n⟩(λy:(num → real). ω(c, y, matrix_identity(real_ring, n)))",
	},
})}

var integralPartitionDef = integralPartitionDefThm{family.Define(registry.DefEntry{
	Name:  "integralPartitionDef",
	Key:   "prop_67254ec4ef841f40",
	Const: "manifold_integral_partition",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"num → " +
		"(num → prod(set(A), A → num → real)) → " +
		"(num → A → real) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{PositiveChartDef},
	Reading: "The partition is one on an open neighbourhood of K. Each active weight has compact " +
		"support inside its assigned positive chart. Indices i >= N are unused, and K empty admits N = 0.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀K:set(A). " +
			"∀N:num. " +
			"∀c:(num → prod(set(A), A → num → real)). " +
			"∀ψ:(num → A → real). " +
			"    manifold_integral_partition⟨n⟩(T, 𝒜, K, N, c, ψ) ⇔ " +
			"    manifold_partition_of_unity⟨n⟩(T, 𝒜, K, «positive domains», N, ψ) ∧ " +
			"    (∀i:num. " +
			"        i < N ⇒ " +
			"        positive_manifold_chart⟨n⟩(T, 𝒜, c(i)) ∧ function_support(T, &0, ψ(i)) ⊆ fst(c(i)))",
	},
})}

var HasIntegralDef = hasIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "HasIntegralDef",
	Key:   "prop_18dda0a647cc4cb4",
	Const: "has_manifold_form_integral",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{OrientedManifoldDef, integralPartitionDef, chartIntegralDef},
	Reading: "An integral value is witnessed by one finite positive-chart partition " +
		"of the compact support. Existence and independence of this witness are separate " +
		"cards; the definition does not quantify over an empty collection of decompositions.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀I:real. " +
			"    has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I) ⇔ " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, n, ω) ∧ " +
			"    compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω)) ∧ " +
			"    (∃N:num. ∃c:(num → prod(set(A), A → num → real)). ∃ψ:(num → A → real). " +
			"        manifold_integral_partition⟨n⟩(T, 𝒜, manifold_form_support⟨n⟩(T, 𝒜, ω), N, c, ψ) ∧ " +
			"        I = Σ_{i<N} manifold_chart_integral⟨n⟩(c(i), manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω)))",
	},
})}

var IntegralDef = integralDefThm{family.Define(registry.DefEntry{
	Name:  "IntegralDef",
	Key:   "prop_3d530a805ed75076",
	Const: "manifold_form_integral",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real",
	Dim:  "n",
	Deps: []registry.EntryLike{HasIntegralDef},
	Reading: "The epsilon operator is characterized only for compactly supported top-degree forms " +
		"on an oriented manifold. For other inputs no integral value or convergence claim is asserted.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_integral⟨n⟩(T, 𝒜, ω) = εI:real. has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)",
	},
})}
