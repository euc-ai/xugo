package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_deformation"
	"github.com/euc-ai/xugo/library/registry"
)

var biaffineCoverRingsDef = biaffineCoverRingsDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineCoverRingsDef",
	Key:   "prop_59843031d2350457",
	Const: "biaffine_cover_rings",
	Type:  "ring_ops(B) → set(B) → set(B) → set(num) → ring_ops(B)",
	Equations: []string{
		"∀T:ring_ops(B). ∀A₀ A₁:set(B). ∀σ:set(num). " +
			"    biaffine_cover_rings(T, A₀, A₁, σ) = " +
			"    COND(σ = {0}, restrict_ring(T, A₀), COND(0 ∉ σ, restrict_ring(T, A₁), T))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Chart zero, repeated chart one, and their overlap, read inside the old overlap ring."})}

var biaffineCoverModulesDef = biaffineCoverModulesDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineCoverModulesDef",
	Key:   "prop_9709b9856801ceb8",
	Const: "biaffine_cover_modules",
	Type:  "ring_ops(B) → module_ops(B, D) → prod(set(D), set(D)) → set(num) → module_ops(B, D)",
	Equations: []string{
		"∀T:ring_ops(B). ∀V:module_ops(B, D). ∀M:prod(set(D), set(D)). ∀σ:set(num). " +
			"    biaffine_cover_modules(T, V, M, σ) = " +
			"    COND(σ = {0}, " +
			"        restrict_module(V, fst(M)), " +
			"        COND(0 ∉ σ, " +
			"            restrict_module(V, snd(M)), " +
			"            restrict_module(V, lattice_pair_ambient(T, V, M))))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "The old chart modules and their common localized span."})}

var biaffineCoverDenominatorsDef = biaffineCoverDenominatorsDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineCoverDenominatorsDef",
	Key:   "prop_8db63f9861570e9a",
	Const: "biaffine_cover_denominators",
	Type:  "ring_ops(B) → B → B → set(num) → set(num) → B",
	Equations: []string{
		"∀T:ring_ops(B). ∀a b:B. ∀σ τ:set(num). " +
			"    biaffine_cover_denominators(T, a, b, σ, τ) = " +
			"    COND(τ = {0} ∨ 0 ∉ τ ∨ (¬(σ = {0}) ∧ 0 ∈ σ), T.one, COND(σ = {0}, a, b))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Identity arrows invert one; the two chart-to-overlap " +
		"arrows invert the prescribed biaffine denominators."})}

var BiaffineCoverDatum = biaffineCoverDatumThm{family.Add(registry.ProofEntry{
	Name: "BiaffineCoverDatum",
	Key:  "prop_f49e8129e7c550f1",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀h:(A → B). " +
				"∀T:ring_ops(B). " +
				"∀A₀ A₁:set(B). " +
				"∀a b:B. " +
				"∀V:module_ops(B, D). " +
				"∀M:prod(set(D), set(D)).",
			Hypotheses: []string{
				"biaffine(T, A₀, A₁, a, b)",
				"lattice_pair(T, A₀, A₁, V, M)",
				"ring_homomorphism(R, restrict_ring(T, A₀), h)",
				"ring_homomorphism(R, restrict_ring(T, A₁), h)",
			},
			Conclusion: "cover_datum(R, " +
				"    biaffine_cover_rings(T, A₀, A₁), " +
				"    λσ:set(num). h, " +
				"    biaffine_cover_modules(T, V, M), " +
				"    λσ:set(num). λτ:set(num). λx:B. x, " +
				"    λσ:set(num). λτ:set(num). λn:D. n, " +
				"    biaffine_cover_denominators(T, a, b)) ∧ " +
				"cover_repeated(biaffine_cover_rings(T, A₀, A₁), " +
				"    λσ:set(num). h, " +
				"    biaffine_cover_modules(T, V, M), " +
				"    λσ:set(num). λτ:set(num). λx:B. x, " +
				"    λσ:set(num). λτ:set(num). λn:D. n, " +
				"    λi:num. COND(i = 0, 0, 1))",
		},
		"The existing chart-localization and span-localization theorems give every "+
			"nonidentity arrow. All arrows are inclusions in place, so composition is literal."),
	Deps: []registry.EntryLike{
		biaffineCoverRingsDef,
		biaffineCoverModulesDef,
		biaffineCoverDenominatorsDef,
		coverRepeatedDef,
	},
	Reading: "The existing chart-localization and span-localization theorems give every " +
		"nonidentity arrow. All arrows are inclusions in place, so composition is literal.",
})}

var biaffineCoverGluingDef = biaffineCoverGluingDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineCoverGluingDef",
	Key:   "prop_56b5f3e5bd5e89ab",
	Const: "biaffine_cover_gluing",
	Type: "ring_ops(A) → " +
		"(A → B) → " +
		"ring_ops(B) → " +
		"set(B) → " +
		"set(B) → " +
		"B → " +
		"B → " +
		"module_ops(B, D) → " +
		"prod(set(D), set(D)) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"set(prod(prod(D, B), prod(D, B))) → " +
		"set(prod(prod(D, B), prod(D, B)))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀h:(A → B). " +
			"∀T:ring_ops(B). " +
			"∀A₀ A₁:set(B). " +
			"∀a b:B. " +
			"∀V:module_ops(B, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"    biaffine_cover_gluing(R, h, T, A₀, A₁, a, b, V, M, q) = " +
			"    λx:set(prod(prod(D, B), prod(D, B))). " +
			"        inverse_on(square_zero_localization(biaffine_cover_modules(T, V, M)({1}), " +
			"                T, " +
			"                λx:B. x, " +
			"                biaffine_cover_modules(T, V, M)({0, 1}), " +
			"                λn:D. n, " +
			"                cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
			"                    λσ:set(num). h, " +
			"                    biaffine_cover_modules(T, V, M), " +
			"                    q, " +
			"                    {1}), " +
			"                (biaffine_cover_modules(T, V, M)({1}).zero, b)).ring.carrier, " +
			"            induced_map(λz:prod(prod(D, B), prod(D, B)). " +
			"                    inverse_on(cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
			"                            λσ:set(num). h, " +
			"                            biaffine_cover_modules(T, V, M), " +
			"                            q, " +
			"                            {0, 1}).ring.carrier, " +
			"                        λw:prod(D, B). " +
			"                            cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
			"                                λσ:set(num). h, " +
			"                                biaffine_cover_modules(T, V, M), " +
			"                                q, " +
			"                                {0, 1}).ring.mul(w, " +
			"                                cover_code_maps(biaffine_cover_rings(T, A₀, A₁), " +
			"                                    biaffine_cover_modules(T, V, M), " +
			"                                    λσ:set(num). λτ:set(num). λx:B. x, " +
			"                                    λσ:set(num). λτ:set(num). λn:D. n, " +
			"                                    q)({1}, {0, 1})(snd(z))), " +
			"                        cover_code_maps(biaffine_cover_rings(T, A₀, A₁), " +
			"                            biaffine_cover_modules(T, V, M), " +
			"                            λσ:set(num). λτ:set(num). λx:B. x, " +
			"                            λσ:set(num). λτ:set(num). λn:D. n, " +
			"                            q)({1}, {0, 1})(fst(z)))), " +
			"            induced_map(λz:prod(prod(D, B), prod(D, B)). " +
			"                    inverse_on(cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
			"                            λσ:set(num). h, " +
			"                            biaffine_cover_modules(T, V, M), " +
			"                            q, " +
			"                            {0, 1}).ring.carrier, " +
			"                        λw:prod(D, B). " +
			"                            cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
			"                                λσ:set(num). h, " +
			"                                biaffine_cover_modules(T, V, M), " +
			"                                q, " +
			"                                {0, 1}).ring.mul(w, " +
			"                                cover_code_maps(biaffine_cover_rings(T, A₀, A₁), " +
			"                                    biaffine_cover_modules(T, V, M), " +
			"                                    λσ:set(num). λτ:set(num). λx:B. x, " +
			"                                    λσ:set(num). λτ:set(num). λn:D. n, " +
			"                                    q)({0}, {0, 1})(snd(z))), " +
			"                        cover_code_maps(biaffine_cover_rings(T, A₀, A₁), " +
			"                            biaffine_cover_modules(T, V, M), " +
			"                            λσ:set(num). λτ:set(num). λx:B. x, " +
			"                            λσ:set(num). λτ:set(num). λn:D. n, " +
			"                            q)({0}, {0, 1})(fst(z))))(x))",
	},
	Deps: []registry.EntryLike{
		biaffineCoverModulesDef,
		biaffineCoverRingsDef,
		coverCodeExtensionsDef,
		coverCodeMapsDef,
	},
	Reading: "Both localizations map isomorphically to the coded overlap " +
		"extension; compose the first map with the inverse of the second."})}

var BiaffineCoverSpecialization = biaffineCoverSpecializationThm{family.Add(registry.ProofEntry{
	Name: "BiaffineCoverSpecialization",
	Key:  "prop_f732cc25e036d3e3",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀h:(A → B). " +
				"∀T:ring_ops(B). " +
				"∀A₀ A₁:set(B). " +
				"∀a b:B. " +
				"∀V:module_ops(B, D). " +
				"∀M:prod(set(D), set(D)). " +
				"∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"biaffine(T, A₀, A₁, a, b)",
				"lattice_pair(T, A₀, A₁, V, M)",
				"ring_homomorphism(R, restrict_ring(T, A₀), h)",
				"ring_homomorphism(R, restrict_ring(T, A₁), h)",
				"q ∈ " +
					"cover_extension_codes(R, " +
					"    biaffine_cover_rings(T, A₀, A₁), " +
					"    λσ:set(num). h, " +
					"    biaffine_cover_modules(T, V, M), " +
					"    λσ:set(num). λτ:set(num). λx:B. x, " +
					"    λσ:set(num). λτ:set(num). λn:D. n)",
			},
			Conclusion: "biaffine_extension(R, " +
				"    h, " +
				"    T, " +
				"    A₀, " +
				"    A₁, " +
				"    a, " +
				"    b, " +
				"    V, " +
				"    M, " +
				"    cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
				"        λσ:set(num). h, " +
				"        biaffine_cover_modules(T, V, M), " +
				"        q, " +
				"        {0}), " +
				"    (biaffine_cover_modules(T, V, M)({0}).zero, a), " +
				"    cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
				"        λσ:set(num). h, " +
				"        biaffine_cover_modules(T, V, M), " +
				"        q, " +
				"        {1}), " +
				"    (biaffine_cover_modules(T, V, M)({1}).zero, b), " +
				"    biaffine_cover_gluing(R, h, T, A₀, A₁, a, b, V, M, q))",
		},
		"The two actual maps to the overlap are localizations by CoverExtensionMapsLocalize, "+
			"so their comparison is the old marked biaffine gluing isomorphism."),
	Deps: []registry.EntryLike{
		BiaffineCoverDatum,
		biaffineCoverGluingDef,
		CoverExtensionMapsLocalize,
		biaffine_deformation.BiaffineExtensionDef,
	},
	Reading: "The two actual maps to the overlap are localizations by CoverExtensionMapsLocalize, " +
		"so their comparison is the old marked biaffine gluing isomorphism.",
})}

var BiaffineExtensionCoverRealization = biaffineExtensionCoverRealizationThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExtensionCoverRealization",
	Key:  "prop_dcc13d2a1fe9cb0d",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀h:(A → B). " +
				"∀T:ring_ops(B). " +
				"∀A₀ A₁:set(B). " +
				"∀a b:B. " +
				"∀V:module_ops(B, D). " +
				"∀M:prod(set(D), set(D)). " +
				"∀E₀:square_zero_ops(A, B, I, D). " +
				"∀e₀:I. " +
				"∀E₁:square_zero_ops(A, B, H, D). " +
				"∀e₁:H. " +
				"∀φ:(set(prod(I, I)) → set(prod(H, H))).",
			Hypotheses: []string{
				"biaffine(T, A₀, A₁, a, b)",
				"lattice_pair(T, A₀, A₁, V, M)",
				"ring_homomorphism(R, restrict_ring(T, A₀), h)",
				"ring_homomorphism(R, restrict_ring(T, A₁), h)",
				"biaffine_extension(R, h, T, A₀, A₁, a, b, V, M, E₀, e₀, E₁, e₁, φ)",
			},
			Conclusion: "∃q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"∃ψ₀:(prod(D, B) → I). " +
				"∃ψ₁:(prod(D, B) → H). " +
				"    q ∈ " +
				"    cover_extension_codes(R, " +
				"        biaffine_cover_rings(T, A₀, A₁), " +
				"        λσ:set(num). h, " +
				"        biaffine_cover_modules(T, V, M), " +
				"        λσ:set(num). λτ:set(num). λx:B. x, " +
				"        λσ:set(num). λτ:set(num). λn:D. n) ∧ " +
				"    biaffine_isomorphism(R, " +
				"        T, " +
				"        V, " +
				"        M, " +
				"        cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
				"            λσ:set(num). h, " +
				"            biaffine_cover_modules(T, V, M), " +
				"            q, " +
				"            {0}), " +
				"        (biaffine_cover_modules(T, V, M)({0}).zero, a), " +
				"        cover_code_extensions(biaffine_cover_rings(T, A₀, A₁), " +
				"            λσ:set(num). h, " +
				"            biaffine_cover_modules(T, V, M), " +
				"            q, " +
				"            {1}), " +
				"        (biaffine_cover_modules(T, V, M)({1}).zero, b), " +
				"        biaffine_cover_gluing(R, h, T, A₀, A₁, a, b, V, M, q), " +
				"        E₀, " +
				"        e₀, " +
				"        E₁, " +
				"        e₁, " +
				"        φ, " +
				"        ψ₀, " +
				"        ψ₁)",
		},
		"Use the localization of E₁ as common overlap and the given gluing for the "+
			"chart-zero map, then repeat these three objects over finite intersections. "+
			"Choose zero-preserving sections and apply CoverExtensionExtraction."),
	Deps: []registry.EntryLike{
		BiaffineCoverSpecialization,
		CoverExtensionExtraction,
		biaffine_deformation.BiaffineIsomorphismDef,
	},
	Reading: "Together with CoverExtensionIsoIffBoundary this identifies the " +
		"new marked code classification with the existing biaffine classification; " +
		"changing lifts is allowed by the old isomorphism predicate.",
})}
