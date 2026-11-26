package compact_chern

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	"github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothRepresentative = smoothRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "SmoothRepresentative",
	Key:  "prop_e283e6d6ab7887fe",
	Deps: []registry.EntryLike{
		k_compact_support.Equivalence,
		smooth_manifold.PartitionOfUnity,
		smooth_manifold.FunctionBump,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "a ∈ (kc_group(T)).carrier"},
		Conclusion: "∃t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    smooth_kc_triple(n, T, 𝒜, t) ∧ a = kc_class(T, t)",
	},
		"The smoothing is the filler's promotion. Approximate the projections and the map by smooth "+
			"data, on an exhaustion of T by compact sets so that the error is small on each "+
			"(smooth_manifold.PartitionOfUnity, FunctionBump), retract the spectra of the approximating "+
			"projections to projections and compress the map between them; a small enough error keeps the "+
			"map invertible off a compact neighbourhood of the singular support. The straight-line homotopy, "+
			"retracted the same way, is a kc triple on T × [0, 1] invertible off that compact set, so the "+
			"homotopy generator of kc_equivalent (k_compact_support.Equivalence) keeps the class."),
})}

var AdaptedConnectionsExist = adaptedConnectionsExistThm{family.Add(registry.ProofEntry{
	Name: "AdaptedConnectionsExist",
	Key:  "prop_11b98a7d0c7e927",
	Deps: []registry.EntryLike{
		chern_weil.GrassmannConnection,
		chern_weil.MatrixProductForm,
		smooth_projection_bundle.SmoothNormalizedInverse,
		smooth_manifold.FunctionBump,
		smooth_manifold.FunctionLocal,
		compact.CompactClosed,
		differential_form.FunctionForm,
		differential_form.ExteriorDerivativeForm,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{"smooth_kc_triple(n, T, 𝒜, t)"},
		Conclusion: "∃K:set(A). " +
			"∃Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ)",
	},
		"For t = (P, (Q, σ)), kc_triple gives a compact K₀ off which σ is invertible; FunctionBump on K₀ "+
			"⊆ ⋃T gives f with compact support K, equal to one on an open V ⊇ K₀, so kc_supported_in(T, K, "+
			"t) holds. Take Γ = 0 (GrassmannConnection) and Δ = −(1 − f)·Q(dσ)τ, with Δ = 0 on V, where τ = "+
			"PτQ is the inverse of σ at each point of the open set off K₀ (CompactClosed), unique once "+
			"normalized; SmoothNormalizedInverse in each chart makes τ smooth there, FunctionLocal glues Δ "+
			"smooth, and MatrixProductForm with FunctionForm and ExteriorDerivativeForm makes it a projected "+
			"matrix of one-forms. Off K, f = 0 and Q(dσ)P + Δσ − σΓ = Q(dσ)P − Q(dσ)τσ = 0, since τσ = P."),
})}

var CompactCharacterForm = compactCharacterFormThm{family.Add(registry.ProofEntry{
	Name: "CompactCharacterForm",
	Key:  "prop_50625dbb3a9b81e1",
	Deps: []registry.EntryLike{chern_weil.ChernClosed},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀K:set(A). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ)"},
		Conclusion: "manifold_form_on⟨n⟩(T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V))) ∧ " +
			"compact_in(T, " +
			"    manifold_form_support⟨n⟩(T, " +
			"        𝒜, " +
			"        (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"            chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"            chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V)))) ∧ " +
			"manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V))) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
	},
		"Intertwining makes the curvatures conjugate off K, so their "+
			"invariant traces agree there. Bianchi closes both Chern forms."),
})}

var ConnectionsIndependent = connectionsIndependentThm{family.Add(registry.ProofEntry{
	Name: "ConnectionsIndependent",
	Key:  "prop_c0e64ea975667d46",
	Deps: []registry.EntryLike{CompactCharacterForm, chern_weil.ChernConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀K L:set(A). " +
			"∀Γ Δ Γ₁ Δ₁:(num → " +
			"        num → " +
			"        prod(set(A), A → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ)",
			"relative_chern_connections(n, T, 𝒜, t, L, Γ₁, Δ₁)",
		},
		Conclusion: "compact_de_rham_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V))) = " +
			"compact_de_rham_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ₁, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ₁, k, c, y, V)))",
	},
		"Interpolate both adapted pairs simultaneously. Off the union of compact supports "+
			"their transgression traces intertwine, so the difference primitive is compact."),
})}

var RelativeRelations = relativeRelationsThm{family.Add(registry.ProofEntry{
	Name: "RelativeRelations",
	Key:  "prop_60154d47f36d53c1",
	Deps: []registry.EntryLike{ConnectionsIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t u:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀K L:set(A). " +
			"∀Γ Δ Γ₁ Δ₁:(num → " +
			"        num → " +
			"        prod(set(A), A → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ)",
			"relative_chern_connections(n, T, 𝒜, u, L, Γ₁, Δ₁)",
			"kc_equivalent(T, t, u)",
		},
		Conclusion: "compact_de_rham_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V))) = " +
			"compact_de_rham_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(u), Γ₁, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(u)), Δ₁, k, c, y, V)))",
	},
		"Verify the actual relative generators: degenerate triples have matching connections "+
			"everywhere; direct sums add traces; compact homotopies have one compact support and "+
			"an integrated compact transgression. Smooth replacement preserves these relations."),
})}

var CharacterOnTriple = characterOnTripleThm{family.Add(registry.ProofEntry{
	Name: "CharacterOnTriple",
	Key:  "prop_f6cf6a7ee7b636e0",
	Deps: []registry.EntryLike{RelativeRelations, AdaptedConnectionsExist},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀K:set(A). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ)"},
		Conclusion: "compact_chern_class(n, T, 𝒜, kc_class(T, t), k) = " +
			"compact_de_rham_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"        chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V)))",
	},
		"Existence supplies a geometric witness, and invariance under the "+
			"relative relation makes every witness give the same quotient class."),
})}

var CharacterCarrier = characterCarrierThm{family.Add(registry.ProofEntry{
	Name: "CharacterCarrier",
	Key:  "prop_5c53f20fcadc6271",
	Deps: []registry.EntryLike{
		CharacterOnTriple,
		SmoothRepresentative,
		CompactCharacterForm,
		AdaptedConnectionsExist,
		compact_de_rham.ClassCarrier,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "a ∈ (kc_group(T)).carrier"},
		Conclusion: "compact_chern_class(n, T, 𝒜, a, k) ∈ (compact_de_rham_module(n, T, 𝒜, 2 * k)).carrier",
	},
		"Choose a smooth representative and adapted connections; "+
			"their compact closed difference represents the character."),
})}

var CharacterAdditive = characterAdditiveThm{family.Add(registry.ProofEntry{
	Name: "CharacterAdditive",
	Key:  "prop_5c08c67779cf2ecc",
	Deps: []registry.EntryLike{
		CharacterOnTriple,
		chern_weil.ChernDirectSum,
		SmoothRepresentative,
		AdaptedConnectionsExist,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a b:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"a ∈ (kc_group(T)).carrier",
			"b ∈ (kc_group(T)).carrier",
		},
		Conclusion: "compact_chern_class(n, T, 𝒜, (kc_group(T)).mul(a, b), k) = " +
			"(compact_de_rham_module(n, T, 𝒜, 2 * k)).add(compact_chern_class(n, T, 𝒜, a, k), " +
			"    compact_chern_class(n, T, 𝒜, b, k))",
	}, "Take direct-sum adapted connections and split their curvature traces."),
})}
