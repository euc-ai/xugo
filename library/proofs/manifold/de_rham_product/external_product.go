// External products are bilinear, natural, and compatible with the graded multiplication and diagonal.

package de_rham_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var ExternalProductClass = externalProductClassThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductClass",
	Key:  "prop_46620d534a7c416c",
	Reading: "The product form puts first-factor columns before second-factor columns. " +
		"No compactness or orientation is required, and empty factors are included.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		WedgeClass,
		de_rham.PullbackClass,
		differential_form.PullbackForm,
		differential_form.PullbackExteriorDerivative,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀β:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"manifold_form_on⟨m⟩(S, ℬ, q, β)",
			"manifold_exterior_derivative⟨m⟩(S, ℬ, q, β) = de_rham_complex⟨m⟩(S, ℬ).zero",
		},
		Conclusion: "de_rham_external_product⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    p, " +
			"    q, " +
			"    de_rham_class⟨n⟩(T, 𝒜, p, α), " +
			"    de_rham_class⟨m⟩(S, ℬ, q, β)) = " +
			"de_rham_class⟨n + m⟩(product_topology(T, S), " +
			"    «product atlas», " +
			"    p + q, " +
			"    manifold_form_wedge⟨n + m⟩(product_topology(T, S), " +
			"        «product atlas», " +
			"        p, " +
			"        q, " +
			"        manifold_form_pullback⟨n + m, n⟩(product_topology(T, S), " +
			"            «product atlas», " +
			"            T, " +
			"            𝒜, " +
			"            p, " +
			"            fst, " +
			"            α), " +
			"        manifold_form_pullback⟨n + m, m⟩(product_topology(T, S), " +
			"            «product atlas», " +
			"            S, " +
			"            ℬ, " +
			"            q, " +
			"            snd, " +
			"            β)))",
	},
		"Both projections are smooth. PullbackClass identifies the two pulled-back classes with their "+
			"pulled-back closed forms, and WedgeClass gives the displayed class of the product form."),
})}

var ExternalProductBilinear = externalProductBilinearThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductBilinear",
	Key:  "prop_5155a2de65a7edd5",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		WedgeBilinear,
		de_rham.PullbackHom,
		smooth_manifold.ProductManifold,
		smooth_manifold.SmoothProductProjections,
		module_homomorphism.BilinearMapOfClauses,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "smooth_manifold⟨m⟩(S, ℬ)"},
		Conclusion: "bilinear_map(real_ring, " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, p), " +
			"    de_rham_cohomology_module⟨m⟩(S, ℬ, q), " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), «product atlas», p + q), " +
			"    de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, p, q))",
	},
		"Projection pullbacks are linear into the two product cohomology degrees. "+
			"Compose each with the corresponding linear slice of WedgeBilinear; carrier "+
			"preservation and the two linearity laws give the external-product bilinear map."),
})}

var ExternalProductNaturality = externalProductNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductNaturality",
	Key:  "prop_f2bd933a1aa0adc7",
	Reading: "All four point types and dimensions may differ. Equalities of composite " +
		"maps are used on their source carriers; no inverse or embedding hypotheses are needed.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		PullbackWedge,
		de_rham.PullbackCompose,
		de_rham.PullbackCongruence,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m N M p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀Q:set(set(D)). " +
			"∀𝒟:set(prod(set(D), D → num → real)). " +
			"∀f:(A → C). " +
			"∀g:(B → D). " +
			"∀s:set(prod(set(C), C → num → real) → (num → real) → (num → num → real) → real). " +
			"∀t:set(prod(set(D), D → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, 𝒜, R, 𝒞, f)",
			"smooth_manifold_map⟨m, M⟩(S, ℬ, Q, 𝒟, g)",
			"s ∈ de_rham_cohomology_module⟨N⟩(R, 𝒞, p).carrier",
			"t ∈ de_rham_cohomology_module⟨M⟩(Q, 𝒟, q).carrier",
		},
		Conclusion: "de_rham_pullback⟨n + m, N + M⟩(product_topology(T, S), " +
			"    «product atlas», " +
			"    product_topology(R, Q), " +
			"    smooth_product_atlas⟨N, M⟩(𝒞, 𝒟), " +
			"    p + q, " +
			"    (λz:prod(A, B). (f(fst(z)), g(snd(z)))))( " +
			"    de_rham_external_product⟨N, M⟩(R, 𝒞, Q, 𝒟, p, q, s, t)) = " +
			"de_rham_external_product⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    p, " +
			"    q, " +
			"    de_rham_pullback⟨n, N⟩(T, 𝒜, R, 𝒞, p, f)(s), " +
			"    de_rham_pullback⟨m, M⟩(S, ℬ, Q, 𝒟, q, g)(t))",
	},
		"Build f×g using smooth projection compositions and pairing. PullbackWedge "+
			"separates its pullback of the product, and PullbackCompose with the "+
			"projection identities identifies each factor with the required pullback."),
})}

var ExternalProductSwap = externalProductSwapThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductSwap",
	Key:  "prop_e6cac9b2a1a24ef6",
	Reading: "The sign uses cohomological degrees p and q, not the dimensions " +
		"n and m. The equality lives on the reversed product point type B×A.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		PullbackWedge,
		de_rham.PullbackCompose,
		de_rham.PullbackCongruence,
		WedgeGradedCommutative,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀t:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
			"t ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, q).carrier",
		},
		Conclusion: "de_rham_pullback⟨m + n, n + m⟩(product_topology(S, T), " +
			"    smooth_product_atlas⟨m, n⟩(ℬ, 𝒜), " +
			"    product_topology(T, S), " +
			"    «product atlas», " +
			"    p + q, " +
			"    (λz:prod(B, A). (snd(z), fst(z))))( " +
			"    de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, p, q, s, t)) = " +
			"de_rham_cohomology_module⟨m + n⟩(product_topology(S, T), " +
			"    smooth_product_atlas⟨m, n⟩(ℬ, 𝒜), " +
			"    p + q).smul((-&1)^(p * q), de_rham_external_product⟨m, n⟩(S, ℬ, T, 𝒜, q, p, t, s))",
	},
		"The swap is smooth by projections and pairing. Pullback interchanges the two "+
			"projection factors, and graded commutativity reverses their wedge with sign (-1)^(pq)."),
})}

var ExternalProductMultiplicative = externalProductMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductMultiplicative",
	Key:  "prop_1cba8d8de7cc5dfe",
	Reading: "The Koszul sign is (-1)^(q*r): only the second-factor class " +
		"of the first pair crosses the first-factor class of the second pair.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		WedgeAssociative,
		WedgeGradedCommutative,
		WedgeBilinear,
		PullbackWedge,
		de_rham.PullbackHom,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q r h:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀s u:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀t v:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
			"t ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, q).carrier",
			"u ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, r).carrier",
			"v ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, h).carrier",
		},
		Conclusion: "de_rham_wedge⟨n + m⟩(product_topology(T, S), " +
			"    «product atlas», " +
			"    p + q, " +
			"    r + h, " +
			"    de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, p, q, s, t), " +
			"    de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, r, h, u, v)) = " +
			"de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"    «product atlas», " +
			"    p + q + (r + h)).smul((-&1)^(q * r), " +
			"    de_rham_external_product⟨n, m⟩(T, " +
			"        𝒜, " +
			"        S, " +
			"        ℬ, " +
			"        p + r, " +
			"        q + h, " +
			"        de_rham_wedge⟨n⟩(T, 𝒜, p, r, s, u), " +
			"        de_rham_wedge⟨m⟩(S, ℬ, q, h, t, v)))",
	},
		"Expand the two external products as wedges of projection pullbacks. Associate the "+
			"four factors, commute the middle degrees q and r, and combine like projection "+
			"factors with PullbackWedge. Bilinearity carries the sign to the full product."),
})}

var ExternalProductUnit = externalProductUnitThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductUnit",
	Key:  "prop_99a7ffdd04be9981",
	Reading: "Each unit law asks membership of its own class " +
		"only, so either is used without a class of the other factor.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		PullbackUnit,
		de_rham.PullbackHom,
		WedgeUnit,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
		},
		Conclusion: "(∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier ⇒ " +
			"    de_rham_external_product⟨n, m⟩(T, " +
			"        𝒜, " +
			"        S, " +
			"        ℬ, " +
			"        k, " +
			"        0, " +
			"        s, " +
			"        de_rham_class⟨m⟩(S, ℬ, 0, manifold_form_unit⟨m⟩(S, ℬ))) = " +
			"    de_rham_pullback⟨n + m, n⟩(product_topology(T, S), «product atlas», T, 𝒜, k, fst)(s)) ∧ " +
			"(∀t:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    t ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier ⇒ " +
			"    de_rham_external_product⟨n, m⟩(T, " +
			"        𝒜, " +
			"        S, " +
			"        ℬ, " +
			"        0, " +
			"        k, " +
			"        de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)), " +
			"        t) = " +
			"    de_rham_pullback⟨n + m, m⟩(product_topology(T, S), «product atlas», S, ℬ, k, snd)(t))",
	},
		"PullbackUnit takes either factor’s unit class to the product unit. The right and left "+
			"WedgeUnit laws then reduce the two external products to the corresponding projection pullbacks."),
})}

var ExternalProductDiagonal = externalProductDiagonalThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductDiagonal",
	Key:  "prop_cc767e5cfa426781",
	Reading: "The diagonal need not be an open inclusion. Only smoothness and the two " +
		"projection identities enter; empty and zero-dimensional manifolds are allowed.",
	Deps: []registry.EntryLike{
		ExternalProductDef,
		PullbackWedge,
		de_rham.PullbackCompose,
		de_rham.PullbackIdentity,
		de_rham.PullbackCongruence,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
			"t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, n + n⟩(T, " +
			"    𝒜, " +
			"    product_topology(T, T), " +
			"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"    p + q, " +
			"    (λx:A. (x, x)))(de_rham_external_product⟨n, n⟩(T, 𝒜, T, 𝒜, p, q, s, t)) = " +
			"de_rham_wedge⟨n⟩(T, 𝒜, p, q, s, t)",
	},
		"The diagonal pairs two smooth identity maps. Pull its external "+
			"product back using PullbackWedge; each projection composed with "+
			"the diagonal is the identity, so the two factors become s and t."),
})}
