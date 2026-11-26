// Horizontal insertion followed by top-form integration defines integration over the second factor.

package form_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

var fiberSliceDef = fiberSliceDefThm{family.Define(registry.DefEntry{
	Name:  "fiberSliceDef",
	Key:   "prop_47c6f821c0d65712",
	Const: "manifold_fiber_slice",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"prod(set(B), B → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Reading: "Fix k horizontal vectors in a base chart and insert m vertical vectors " +
		"after them. The result is a top-degree form on the fiber, with zero values on " +
		"incompatible fiber charts or outside their coordinate images. Invalid base chart " +
		"data also give the whole zero fiber form. The output degree k is an ordinary argument.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"∀d:prod(set(B), B → num → real). " +
			"∀z:(num → real). " +
			"∀Q:(num → num → real). " +
			"    manifold_fiber_slice⟨n, m⟩(T, 𝒜, S, ℬ, k, ω, c, y, P)(d, z, Q) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        y ∈ «chart image»(c) ∧ " +
			"        compatible_chart⟨m⟩(S, ℬ, d) ∧ " +
			"        z ∈ image(snd(d), fst(d)), " +
			"        ω(«product chart»(c, d), «product coordinates»(y, z), «fiber frame»(P, Q)), " +
			"        &0)",
	},
})}

var FiberIntegralDef = fiberIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "FiberIntegralDef",
	Key:   "prop_68ee115579d86e4b",
	Const: "manifold_fiber_integral",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Deps: []registry.EntryLike{fiberSliceDef, IntegralDef},
	Reading: "The operator integrates the vertical top form obtained after k horizontal " +
		"insertions. Its laws require a compact oriented fiber and a smooth product form; the base " +
		"need not be compact or oriented, and total product support need not be compact. Horizontal " +
		"slots precede vertical slots, fixing the sign convention for differentiation and projection.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)(c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c), " +
			"        manifold_form_integral⟨m⟩(S, ℬ, manifold_fiber_slice⟨n, m⟩(T, 𝒜, S, ℬ, k, ω, c, y, P)), " +
			"        &0)",
	},
})}
