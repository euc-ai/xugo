// Base support is local in charts and decreases under weighting, wedge and differentiation.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var SupportClosed = supportClosedThm{family.Add(registry.ProofEntry{
	Name: "SupportClosed",
	Key:  "prop_caf2625dbcd3af33",
	Deps: []registry.EntryLike{SupportDef, function_support.SupportClosed},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "closed_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
	},
		"The defining Boolean nonzero predicate is a function on the base type. SupportClosed "+
			"applies to its carrier-relative support, even for an arbitrary component family."),
})}

var SupportEmpty = supportEmptyThm{family.Add(registry.ProofEntry{
	Name: "SupportEmpty",
	Key:  "prop_5e558792f7876d41",
	Deps: []registry.EntryLike{
		SupportDef,
		FormOnDef,
		function_support.SupportEmpty,
		smooth_manifold.ChartDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, ω) = ∅ ⇔ ω = «zero family»",
	},
		"An empty support makes every active chart value zero at every base point and "+
			"matrix. Chart surjectivity covers each coordinate image, and both normalization "+
			"clauses settle all other arguments. The zero family has empty nonzero locus."),
})}

var SupportCoordinate = supportCoordinateThm{family.Add(registry.ProofEntry{
	Name: "SupportCoordinate",
	Key:  "prop_98c42dc3f7e39949",
	Reading: "The left support uses the topology of the coordinate " +
		"image, not all of Euclidean space. A coordinate component need " +
		"not extend smoothly or without boundary support beyond that image.",
	Deps: []registry.EntryLike{
		SupportDef,
		FormOnDef,
		function_support.SupportRestrictOpen,
		function_support.SupportHomeomorphism,
		smooth_manifold.CompatibleTransition,
		vec_form.PullbackCompose,
		vec_form.PullbackIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "compatible_chart⟨n⟩(T, 𝒜, c)"},
		Conclusion: "function_support(subtopology(euclidean_topology(n), «chart image»(c)), " +
			"    λP:(num → num → real). &0, " +
			"    ω(c)) = " +
			"image(snd(c), fst(c) ∩ manifold_form_support⟨n⟩(T, 𝒜, ω))",
	},
		"Transition pullbacks are invertible on open overlaps, so vanishing in one active chart is "+
			"equivalent to vanishing in every active chart. Thus the coordinate nonzero locus "+
			"corresponds to the base nonzero locus restricted to the chart domain. SupportRestrictOpen "+
			"and the chart homeomorphism carry the closures to the displayed equality."),
})}

var WeightSupport = weightSupportThm{family.Add(registry.ProofEntry{
	Name: "WeightSupport",
	Key:  "prop_5308c7023eecb218",
	Deps: []registry.EntryLike{
		SupportDef,
		SupportClosed,
		WeightDef,
		function_support.SupportOutside,
		function_support.SupportClosed,
		function_support.SupportClosedBound,
		topological_space.InterClosed,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨n⟩(T, 𝒜, f)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
		},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, manifold_form_weight⟨n⟩(T, 𝒜, f, ω)) ⊆ " +
			"function_support(T, &0, f) ∩ manifold_form_support⟨n⟩(T, 𝒜, ω)",
	},
		"Outside the intersection, either the scalar vanishes or all active "+
			"form values vanish. The weighted nonzero locus therefore lies in the "+
			"intersection of two closed supports, and closure preserves this bound."),
})}

var WedgeSupport = wedgeSupportThm{family.Add(registry.ProofEntry{
	Name:    "WedgeSupport",
	Key:     "prop_c1e05d29c659b43f",
	Reading: "No hypothesis: the bound holds for any two families, on any T.",
	Deps: []registry.EntryLike{
		SupportDef,
		function_support.SupportDef,
		WedgeDef,
		vec_form.WedgeDef,
		topological_space.ClosureMono,
	},
	Build: family.Card(
		"∀n p q:num. "+
			"∀T:set(set(A)). "+
			"∀𝒜:set(prod(set(A), A → num → real)). "+
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
			"    manifold_form_support⟨n⟩(T, 𝒜, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)) ⊆ "+
			"    manifold_form_support⟨n⟩(T, 𝒜, α) ∩ manifold_form_support⟨n⟩(T, 𝒜, β)",
		"In an active chart every wedge coefficient at a point is a sum of products of a "+
			"value of α and a value of β there, so it vanishes where all values of either factor "+
			"vanish. The nonzero locus of the wedge lies in the meet of the two nonzero loci, "+
			"and closure is monotone: the closure of a meet lies in the meet of the closures."),
})}

var ExteriorDerivativeSupport = exteriorDerivativeSupportThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeSupport",
	Key:  "prop_8a7eed190bbd5a47",
	Deps: []registry.EntryLike{
		SupportDef,
		SupportClosed,
		FormOnDef,
		ExteriorDerivativeDef,
		function_support.SupportClosedBound,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω)) ⊆ " +
			"manifold_form_support⟨n⟩(T, 𝒜, ω)",
	},
		"On the open complement of the base support, every coordinate coefficient is identically "+
			"zero locally. PartialDerivativeLocal makes all exterior derivative coefficients zero "+
			"there. The original support is closed, so it bounds the derivative support."),
})}

var SupportRestrict = supportRestrictThm{family.Add(registry.ProofEntry{
	Name: "SupportRestrict",
	Key:  "prop_4db0e610166fa990",
	Deps: []registry.EntryLike{
		SupportDef,
		RestrictDef,
		SupportCoordinate,
		smooth_manifold.ChartRestrict,
		smooth_manifold.OpenCompatibleChart,
		function_support.SupportRestrictOpen,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "U ∈ T"},
		Conclusion: "manifold_form_support⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)) = " +
			"U ∩ manifold_form_support⟨n⟩(T, 𝒜, ω)",
	},
		"At a point of U, restrict any active ambient chart to U; it remains compatible and "+
			"has the same coordinate map. The restricted family therefore has exactly the ambient "+
			"nonzero locus intersected with U. SupportRestrictOpen identifies their closures."),
})}
