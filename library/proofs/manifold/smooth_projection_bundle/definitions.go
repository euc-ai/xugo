package smooth_projection_bundle

import (
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothProjectionDef = smoothProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothProjectionDef",
	Key:   "prop_8f53f8e6b5454bb5",
	Const: "smooth_projection_bundle",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀P:(A → num → num → complex). " +
			"    smooth_projection_bundle(n, r, T, 𝒜, P) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀i j:num. " +
			"        i < r ∧ j < r ⇒ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. re(P(x, i, j))) ∧ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. im(P(x, i, j)))) ∧ " +
			"    (∀x:A. ∀i j:num. x ∉ ⋃T ∨ r ≤ i ∨ r ≤ j ⇒ P(x, i, j) = complex_of_real(&0)) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ ⋃T ∧ i < r ∧ j < r ⇒ " +
			"        P(x, i, j) = complex_conj(P(x, j, i)) ∧ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < r}, " +
			"            λl:num. P(x, i, l) * P(x, l, j)) = " +
			"        P(x, i, j))",
	},
})}

var SmoothBundleMapDef = smoothBundleMapDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothBundleMapDef",
	Key:   "prop_506c83ce7999ee73",
	Const: "smooth_projection_map",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r t:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q B:(A → num → num → complex). " +
			"    smooth_projection_map(n, r, t, T, 𝒜, P, Q, B) ⇔ " +
			"    (∀i j:num. " +
			"        i < t ∧ j < r ⇒ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. re(B(x, i, j))) ∧ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. im(B(x, i, j)))) ∧ " +
			"    (∀x:A. ∀i j:num. x ∉ ⋃T ∨ t ≤ i ∨ r ≤ j ⇒ B(x, i, j) = complex_of_real(&0)) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ ⋃T ∧ i < t ∧ j < r ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {a:num | a < t}, " +
			"            λa:num. " +
			"                Q(x, i, a) * " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {b:num | b < r}, " +
			"                    λb:num. B(x, a, b) * P(x, b, j))) = " +
			"        B(x, i, j))",
	},
})}
