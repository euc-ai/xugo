// duality.go — the chapter's duality statements.

package curve_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/registry"
)

// DualizingAdjunction — The source dualizing pair is the relative Hom pair of the base dualizing pair.
var DualizingAdjunction = dualizingAdjunctionThm{family.Add(registry.ProofEntry{
	Name: "DualizingAdjunction",
	Key:  "prop_f7d45189af39cef3",
	Reading: "Both nested functions vanish outside their respective carriers. The map is " +
		"linear over B₀₁, not merely over A₀₁; chart one carries values into the t⁻²-twisted target.",
	Deps: []registry.EntryLike{
		hom_module.CoextendScalarsAdjunction,
		serre_duality.DualizingIsLattice,
		coverHomPairDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "lattice_pair(restrict_ring(field_ring(L), B₀₁), " +
			"    B₀, " +
			"    B₁, " +
			"    coextend_scalars(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_ring(field_ring(L), B₀₁), " +
			"        λa:A. a, " +
			"        restrict_module(curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"            lattice_pair_ambient(restrict_ring(field_ring(L), A₀₁), " +
			"                curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"                curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁)))), " +
			"    cover_hom_pair(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_ring(field_ring(L), B₀₁), " +
			"        B₀, " +
			"        B₁, " +
			"        curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"        curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁))) ∧ " +
			"lattice_pair_isomorphism(restrict_ring(field_ring(L), B₀₁), " +
			"    curve_dualizing_module(field_ring(L), k, t, B₀₁), " +
			"    curve_dualizing_pair(L, k, t, B₀, B₁, B₀₁), " +
			"    coextend_scalars(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_ring(field_ring(L), B₀₁), " +
			"        λa:A. a, " +
			"        restrict_module(curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"            lattice_pair_ambient(restrict_ring(field_ring(L), A₀₁), " +
			"                curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"                curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁)))), " +
			"    cover_hom_pair(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_ring(field_ring(L), B₀₁), " +
			"        B₀, " +
			"        B₁, " +
			"        curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"        curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁)), " +
			"    λφ:(A → A). " +
			"        COND(φ ∈ " +
			"            lattice_pair_ambient(restrict_ring(field_ring(L), B₀₁), " +
			"                curve_dualizing_module(field_ring(L), k, t, B₀₁), " +
			"                curve_dualizing_pair(L, k, t, B₀, B₁, B₀₁)), " +
			"            λb:A. COND(b ∈ B₀₁, λa:A. COND(a ∈ A₀₁, φ(a * b), L.zero), λa:A. L.zero), " +
			"            λb:A. λa:A. L.zero))",
	},
		"Apply CoextendScalarsAdjunction on the overlap, check B₀₁-linearity for "+
			"precomposition, and compare the chart conditions. The inverse evaluates "+
			"the A₀₁-functional at one. The line target remains O(−2) on both sides."),
})}

// HomToModelIsTraceDual — A base dualizing model identifies relative Hom with its product with the inverse different.
var HomToModelIsTraceDual = homToModelIsTraceDualThm{family.Add(registry.ProofEntry{
	Name: "HomToModelIsTraceDual",
	Key:  "prop_57022c9f25da756c",
	Deps: []registry.EntryLike{
		TraceDualHomIso,
		TraceDualOfInvertible,
		serre_duality.DualizingModelDef,
		TraceDualLocalizes,
		CoverPullbackLattice,
		hom_module.PostComposeHom,
		hom_module.PostComposeInjective,
		module_homomorphism.IsomorphismInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_model(restrict_field(L, K), k, t, A₀, A₁, A₀₁, N)",
		},
		Conclusion: "∃f:((A → A → A) → A). " +
			"    lattice_pair_isomorphism(restrict_ring(field_ring(L), B₀₁), " +
			"        coextend_scalars(restrict_ring(field_ring(L), A₀₁), " +
			"            restrict_ring(field_ring(L), B₀₁), " +
			"            λa:A. a, " +
			"            restrict_module(curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"                lattice_pair_ambient(restrict_ring(field_ring(L), A₀₁), " +
			"                    curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"                    curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁)))), " +
			"        cover_hom_pair(restrict_ring(field_ring(L), A₀₁), " +
			"            restrict_ring(field_ring(L), B₀₁), " +
			"            B₀, " +
			"            B₁, " +
			"            curve_dualizing_module(restrict_ring(field_ring(L), K), k, t, A₀₁), " +
			"            curve_dualizing_pair(restrict_field(L, K), k, t, A₀, A₁, A₀₁)), " +
			"        regular_module(field_ring(L)), " +
			"        lattice_pair_mul(field_ring(L), " +
			"            B₀, " +
			"            B₁, " +
			"            cover_pullback(field_ring(L), B₀, B₁, N), " +
			"            inverse_different(L, K, A₀, A₁, B₀, B₁)), " +
			"        f)",
	},
		"Restrict the chosen model isomorphism to the two ambient modules. "+
			"Postcomposition and postcomposition by its inverse identify their coextensions, "+
			"B₀₁-linearly because both actions precompose the argument. TraceDualHomIso and "+
			"TraceDualOfInvertible identify the chart modules with N_i C_i."),
})}

// HomPairLocalizes — The model identification uses a common overlap trace dual.
var HomPairLocalizes = homPairLocalizesThm{family.Add(registry.ProofEntry{
	Name: "HomPairLocalizes",
	Key:  "prop_de5aca0dabb8549f",
	Deps: []registry.EntryLike{
		TraceDualLocalizes,
		TraceDualOfInvertible,
		HomToModelIsTraceDual,
		invertible_lattice_pair.AmbientOfMul,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_model(restrict_field(L, K), k, t, A₀, A₁, A₀₁, N)",
		},
		Conclusion: "trace_dual(L, " +
			"    K, " +
			"    B₀₁, " +
			"    lattice_pair_ambient(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_module(regular_module(field_ring(L)), K), " +
			"        N)) = " +
			"lattice_pair_ambient(restrict_ring(field_ring(L), B₀₁), " +
			"    regular_module(field_ring(L)), " +
			"    lattice_pair_mul(field_ring(L), " +
			"        B₀, " +
			"        B₁, " +
			"        cover_pullback(field_ring(L), B₀, B₁, N), " +
			"        inverse_different(L, K, A₀, A₁, B₀, B₁)))",
	},
		"TraceDualLocalizes and TraceDualOfInvertible on the overlap show that the "+
			"chart identifications use a single trace-pairing map on their common ambient."),
})}

// DualizingBridge — The source dualizing pair is isomorphic to the pulled-back base model times the inverse different.
var DualizingBridge = dualizingBridgeThm{family.Add(registry.ProofEntry{
	Name: "DualizingBridge",
	Key:  "prop_74df413ac1d98a4c",
	Deps: []registry.EntryLike{
		DualizingAdjunction,
		HomToModelIsTraceDual,
		HomPairLocalizes,
		lattice_pair_map.IsomorphismCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_model(restrict_field(L, K), k, t, A₀, A₁, A₀₁, N)",
		},
		Conclusion: "∃f:((A → A) → A). " +
			"    lattice_pair_isomorphism(restrict_ring(field_ring(L), B₀₁), " +
			"        curve_dualizing_module(field_ring(L), k, t, B₀₁), " +
			"        curve_dualizing_pair(L, k, t, B₀, B₁, B₀₁), " +
			"        regular_module(field_ring(L)), " +
			"        lattice_pair_mul(field_ring(L), " +
			"            B₀, " +
			"            B₁, " +
			"            cover_pullback(field_ring(L), B₀, B₁, N), " +
			"            inverse_different(L, K, A₀, A₁, B₀, B₁)), " +
			"        f)",
	},
		"Compose DualizingAdjunction with HomToModelIsTraceDual; HomPairLocalizes "+
			"ensures that the same isomorphism carries both chart modules. No "+
			"separability of L over k(t) or transitivity of trace is used."),
})}

// InverseDifferentInvertible — Invertible dualizing models on both curves make the inverse different invertible.
var InverseDifferentInvertible = inverseDifferentInvertibleThm{family.Add(registry.ProofEntry{
	Name: "InverseDifferentInvertible",
	Key:  "prop_427c88570242958e",
	Reading: "The known invertible model is the source of InvertibleIsoIffScale. Using f*N·C " +
		"as its source would assume invertibility of the product and make this argument circular.",
	Deps: []registry.EntryLike{
		DualizingBridge,
		serre_duality.DualizingInvertibleDef,
		CoverPullbackInvertible,
		InverseDifferentLattice,
		lattice_pair_map.IsomorphismInverse,
		invertible_lattice_pair.InvertibleIsoIffScale,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.InvertibleLatticeProduct,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_invertible(restrict_field(L, K), k, t, A₀, A₁, A₀₁)",
			"dualizing_invertible(L, k, t, B₀, B₁, B₀₁)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    B₀₁, " +
			"    inverse_different(L, K, A₀, A₁, B₀, B₁))",
	},
		"Choose invertible models N and N′ of ω_Y and ω_X. Reverse the isomorphism "+
			"so its source is N′, then InvertibleIsoIffScale makes f*N·C invertible. "+
			"Multiply by the invertible inverse of f*N to obtain C invertible."),
})}

// DifferentIsIdeal — The different consists of chart ideals in the structure pair.
var DifferentIsIdeal = differentIsIdealThm{family.Add(registry.ProofEntry{
	Name: "DifferentIsIdeal",
	Key:  "prop_5966a13840c2127b",
	Deps: []registry.EntryLike{
		InverseDifferentInvertible,
		TraceDualContainsStructure,
		fractional_ideal.FractionalInverseDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_invertible(restrict_field(L, K), k, t, A₀, A₁, A₀₁)",
			"dualizing_invertible(L, k, t, B₀, B₁, B₀₁)",
		},
		Conclusion: "fst(cover_different(L, K, A₀, A₁, B₀, B₁)) ⊆ B₀ ∧ " +
			"snd(cover_different(L, K, A₀, A₁, B₀, B₁)) ⊆ B₁ ∧ " +
			"ring_ideal(restrict_ring(field_ring(L), B₀), fst(cover_different(L, K, A₀, A₁, B₀, B₁))) ∧ " +
			"ring_ideal(restrict_ring(field_ring(L), B₁), snd(cover_different(L, K, A₀, A₁, B₀, B₁)))",
	},
		"The inverse of C consists of elements z with zC_i⊆B_i. Since B_i⊆C_i and one∈B_i, "+
			"such z lies in B_i; closure and the ideal property follow from the fractional inverse."),
})}

// InverseDifferentQuotientFinite — The inverse-different quotients on both charts and the overlap are finite-dimensional.
var InverseDifferentQuotientFinite = inverseDifferentQuotientFiniteThm{family.Add(registry.ProofEntry{
	Name: "InverseDifferentQuotientFinite",
	Key:  "prop_ac94063dbe2c49f1",
	Deps: []registry.EntryLike{
		InverseDifferentInvertible,
		TraceDualContainsStructure,
		TraceDualLocalizes,
		algebraic_curve.InvertibleQuotientFinite,
		lattice_pair.QuotientDimLocalizes,
		InverseDifferentLattice,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_invertible(restrict_field(L, K), k, t, A₀, A₁, A₀₁)",
			"dualizing_invertible(L, k, t, B₀, B₁, B₀₁)",
		},
		Conclusion: "finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), " +
			"            fst(inverse_different(L, K, A₀, A₁, B₀, B₁))), " +
			"        B₀)) ∧ " +
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), " +
			"            snd(inverse_different(L, K, A₀, A₁, B₀, B₁))), " +
			"        B₁)) ∧ " +
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), trace_dual(L, K, B₀₁, A₀₁)), " +
			"        B₀₁))",
	},
		"C and O_X are invertible and O_X⊆C. InvertibleQuotientFinite gives both "+
			"finite chart quotients; QuotientDimLocalizes gives the finite overlap "+
			"quotient, identified by InverseDifferentLattice and TraceDualLocalizes."),
})}
