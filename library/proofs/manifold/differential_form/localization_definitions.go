// Base support, scalar weights and extension through restricted charts.

package differential_form

import (
	_ "github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/registry"
)

var SupportDef = supportDefThm{family.Define(registry.DefEntry{
	Name:  "SupportDef",
	Key:   "prop_a5fd974bebab6938",
	Const: "manifold_form_support",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(A)",
	Dim: "n",
	Reading: "The support lives on the base manifold. Its nonzero predicate " +
		"asks whether some active compatible chart and some matrix give a nonzero " +
		"value. For a form, invertible transition pullbacks make vanishing " +
		"independent of the active chart. No degree parameter is needed for this set.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_support⟨n⟩(T, 𝒜, ω) = " +
			"    function_support(T, " +
			"        ⊥, " +
			"        λx:A. ∃c:prod(set(A), A → num → real). " +
			"            compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"            x ∈ fst(c) ∧ " +
			"            (∃P:(num → num → real). ω(c, snd(c, x), P) ≠ &0))",
	},
})}

var FunctionFormDef = functionFormDefThm{family.Define(registry.DefEntry{
	Name:  "FunctionFormDef",
	Key:   "prop_72e9db678f1230b7",
	Const: "manifold_function_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_function_form⟨n⟩(T, 𝒜, f, c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c), " +
			"        f(inverse_on(fst(c), snd(c), y)), " +
			"        &0)",
	},
})}

var WeightDef = weightDefThm{family.Define(registry.DefEntry{
	Name:  "WeightDef",
	Key:   "prop_4ac299332f70e719",
	Const: "manifold_form_weight",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "The multiplier is a scalar function of the base point, " +
		"distinct from multiplication by one constant real scalar. The " +
		"output is normalized at both the chart and coordinate-image levels.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_form_weight⟨n⟩(T, 𝒜, f, ω, c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c), " +
			"        f(inverse_on(fst(c), snd(c), y)) * ω(c, y, P), " +
			"        &0)",
	},
})}

var ExtendZeroDef = extendZeroDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendZeroDef",
	Key:   "prop_c5eb8764272a33f4",
	Const: "manifold_form_extend_zero",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "For an ambient chart c, read the component at its restriction " +
		"(domain(c) intersect U, coordinate(c)); the coordinate map is unchanged. " +
		"This defines a total family even when it is not smooth. Smooth extension is " +
		"asserted only when the submanifold support is closed in the ambient manifold.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω, c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ image(snd(c), fst(c) ∩ U), " +
			"        ω((fst(c) ∩ U, snd(c)), y, P), " +
			"        &0)",
	},
})}
