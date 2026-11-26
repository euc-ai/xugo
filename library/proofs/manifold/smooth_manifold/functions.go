// Scalar smoothness is local in charts and respects normalized restriction.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FunctionConstant = functionConstantThm{family.Add(registry.ProofEntry{
	Name: "FunctionConstant",
	Key:  "prop_a4f7e5673136ece1",
	Deps: []registry.EntryLike{SmoothFunctionDef, ChartDef, vec_smooth.SmoothConst},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀r:real.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. COND(x ∈ ⋃T, r, &0))",
	},
		"Every compatible chart lies in the carrier, so the coordinate function is constant r on its "+
			"image. SmoothConst gives smoothness there and the definition supplies zero values elsewhere."),
})}

var FunctionAdd = functionAddThm{family.Add(registry.ProofEntry{
	Name: "FunctionAdd",
	Key:  "prop_9278ac6322c22d9b",
	Deps: []registry.EntryLike{SmoothFunctionDef, vec_smooth.SmoothAdd},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f g:(A → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨n⟩(T, 𝒜, f)",
			"smooth_manifold_function⟨n⟩(T, 𝒜, g)",
		},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. f(x) + g(x))",
	},
		"In coordinates the sum is the sum of the two smooth coordinate functions. "+
			"SmoothAdd applies, and their zero values off the carrier add to zero."),
})}

var FunctionMul = functionMulThm{family.Add(registry.ProofEntry{
	Name: "FunctionMul",
	Key:  "prop_966ddbb25c00650c",
	Deps: []registry.EntryLike{SmoothFunctionDef, vec_smooth.SmoothMul},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f g:(A → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨n⟩(T, 𝒜, f)",
			"smooth_manifold_function⟨n⟩(T, 𝒜, g)",
		},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. f(x) * g(x))",
	},
		"In each compatible chart use SmoothMul for the coordinate functions. "+
			"The pointwise product retains zero normalization off the carrier."),
})}

var FunctionFiniteSum = functionFiniteSumThm{family.Add(registry.ProofEntry{
	Name: "FunctionFiniteSum",
	Key:  "prop_f27bcb7ecd940ca1",
	Reading: "The separate manifold hypothesis is needed when N is " +
		"zero, since the smoothness assumptions on summands are then vacuous.",
	Deps: []registry.EntryLike{SmoothFunctionDef, vec_smooth.SmoothSum},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N:num. " +
			"∀f:(num → A → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀i:num. i < N ⇒ smooth_manifold_function⟨n⟩(T, 𝒜, f(i))",
		},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. Σ_{i<N} f(i, x))",
	},
		"SmoothSum applies to the finite family in every chart, including the empty "+
			"sum. Each summand is zero off the carrier, so their finite sum is normalized."),
})}

var FunctionReciprocal = functionReciprocalThm{family.Add(registry.ProofEntry{
	Name: "FunctionReciprocal",
	Key:  "prop_b999069eaf96b138",
	Deps: []registry.EntryLike{SmoothFunctionDef, ChartDef, vec_smooth.SmoothReciprocal},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real).",
		Hypotheses: []string{"smooth_manifold_function⟨n⟩(T, 𝒜, f)", "∀x:A. x ∈ ⋃T ⇒ f(x) ≠ &0"},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, normalize_on(⋃T, &0, λx:A. &1 / f(x)))",
	},
		"Chart inverse points lie in the carrier, where f does not vanish. SmoothReciprocal "+
			"gives the local inverse and the explicit normalization supplies the exterior values."),
})}

var FunctionContinuous = functionContinuousThm{family.Add(registry.ProofEntry{
	Name: "FunctionContinuous",
	Key:  "prop_f3e2456090819c18",
	Deps: []registry.EntryLike{
		SmoothFunctionDef,
		AtlasDef,
		ChartDef,
		vec_smooth.SmoothOnDef,
		vec_smooth.ContinuouslyDifferentiableOnDef,
		continuous.OpenPasting,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real).",
		Hypotheses: []string{"smooth_manifold_function⟨n⟩(T, 𝒜, f)"},
		Conclusion: "continuous_map(T, real_topology, f)",
	},
		"Smooth coordinate functions are continuous by the zero-order "+
			"differentiability clause. Compose with each chart and paste along "+
			"the original open atlas cover to obtain continuity on the manifold."),
})}

var FunctionLocal = functionLocalThm{family.Add(registry.ProofEntry{
	Name: "FunctionLocal",
	Key:  "prop_27b106487e545f4a",
	Reading: "Local tests ignore all values outside the manifold. The conclusion normalizes " +
		"to the full carrier rather than imposing a condition on those unused input values.",
	Deps: []registry.EntryLike{
		SmoothFunctionDef,
		ChartRestrict,
		OpenCompatibleChart,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀x:A. " +
				"    x ∈ ⋃T ⇒ " +
				"    ∃U:set(A). " +
				"        U ∈ T ∧ " +
				"        x ∈ U ∧ " +
				"        smooth_manifold_function⟨n⟩(subtopology(T, U), " +
				"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
				"            normalize_on(U, &0, f))",
		},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, normalize_on(⋃T, &0, f))",
	},
		"Intersect a compatible chart with each supplied open neighbourhood. Its restricted chart is "+
			"compatible with that submanifold and has the same inverse locally, giving smooth coordinate "+
			"expressions on an open cover. SmoothLocal glues them and normalization settles exterior values."),
})}

var FunctionRestrict = functionRestrictThm{family.Add(registry.ProofEntry{
	Name: "FunctionRestrict",
	Key:  "prop_728d130ade48fb3",
	Deps: []registry.EntryLike{SmoothFunctionDef, OpenSubmanifold, OpenCompatibleChart},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀f:(A → real).",
		Hypotheses: []string{"smooth_manifold_function⟨n⟩(T, 𝒜, f)", "U ∈ T"},
		Conclusion: "smooth_manifold_function⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    normalize_on(U, &0, f))",
	},
		"Compatible submanifold charts are ambient compatible charts with "+
			"domain in U. The normalized restriction agrees with f at all "+
			"inverse-chart points, so the same coordinate smoothness applies."),
})}

var FunctionExtendZero = functionExtendZeroThm{family.Add(registry.ProofEntry{
	Name: "FunctionExtendZero",
	Key:  "prop_88bb3b0588fd5602",
	Reading: "The submanifold function already vanishes outside U in the " +
		"same host type A, so no new function is constructed. Ambient closedness " +
		"of its support is the condition that makes this zero extension smooth.",
	Deps: []registry.EntryLike{
		SmoothFunctionDef,
		FunctionLocal,
		FunctionConstant,
		function_support.SupportOutside,
		topological_space.OpenClosedComplement,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀f:(A → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"smooth_manifold_function⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), f)",
			"closed_in(T, function_support(subtopology(T, U), &0, f))",
		},
		Conclusion: "smooth_manifold_function⟨n⟩(T, 𝒜, f)",
	},
		"On U use the given smooth function. On the open ambient complement of its subspace "+
			"support it is identically zero, both inside U by SupportOutside and outside U by "+
			"normalization. These two open sets cover the carrier, so FunctionLocal proves smoothness."),
})}
