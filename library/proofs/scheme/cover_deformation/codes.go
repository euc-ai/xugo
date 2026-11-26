package cover_deformation

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	"github.com/euc-ai/xugo/library/registry"
)

var coverArrowsDef = coverArrowsDefThm{family.Define(registry.DefEntry{
	Name:  "coverArrowsDef",
	Key:   "prop_72dc5b1c3f4f8459",
	Const: "cover_arrows",
	Type:  "set(prod(set(num), set(num)))",
	Equations: []string{
		"cover_arrows = " +
			"{a:prod(set(num), set(num)) | " +
			"    fst(a) ∈ intersection_indices ∧ snd(a) ∈ intersection_indices ∧ fst(a) ⊆ snd(a)}",
	},
	Deps:    []registry.EntryLike{},
	Reading: "All inclusion arrows between finite nonempty intersections."})}

var coverCodeAmbientDef = coverCodeAmbientDefThm{family.Define(registry.DefEntry{
	Name:  "coverCodeAmbientDef",
	Key:   "prop_a16e6d0df9d81a55",
	Const: "cover_code_ambient",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → module_ops(B, D)) → " +
		"group_ops(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:(set(num) → ring_ops(B)). ∀N:(set(num) → module_ops(B, D)). " +
			"    cover_code_ambient(R, S, N) = " +
			"    mk_group(λp:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"                prod(set(num), set(num)) → B → D). " +
			"        λq:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"                prod(set(num), set(num)) → B → D). " +
			"            (λσ:set(num). " +
			"                COND(σ ∈ intersection_indices, " +
			"                    factor_set_ambient(R, S(σ), N(σ)).mul(fst(p, σ), fst(q, σ)), " +
			"                    factor_set_ambient(R, S(σ), N(σ)).one), " +
			"            λa:prod(set(num), set(num)). λx:B. " +
			"                COND(a ∈ cover_arrows ∧ x ∈ S(fst(a)).carrier, " +
			"                    N(snd(a)).add(snd(p, a, x), snd(q, a, x)), " +
			"                    N(snd(a)).zero)), " +
			"        (λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).one, " +
			"        λa:prod(set(num), set(num)). λx:B. N(snd(a)).zero), " +
			"        λp:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"                prod(set(num), set(num)) → B → D). " +
			"            (λσ:set(num). " +
			"                COND(σ ∈ intersection_indices, " +
			"                    factor_set_ambient(R, S(σ), N(σ)).inv(fst(p, σ)), " +
			"                    factor_set_ambient(R, S(σ), N(σ)).one), " +
			"            λa:prod(set(num), set(num)). λx:B. " +
			"                COND(a ∈ cover_arrows ∧ x ∈ S(fst(a)).carrier, " +
			"                    N(snd(a)).neg(snd(p, a, x)), " +
			"                    N(snd(a)).zero)), " +
			"        set_cross(indexed_functions(intersection_indices, " +
			"                λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).one, " +
			"                λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).carrier), " +
			"            indexed_functions(cover_arrows, " +
			"                λa:prod(set(num), set(num)). λx:B. N(snd(a)).zero, " +
			"                λa:prod(set(num), set(num)). " +
			"                    indexed_functions(S(fst(a)).carrier, " +
			"                        λx:B. N(snd(a)).zero, " +
			"                        λx:B. N(snd(a)).carrier))))",
	},
	Deps: []registry.EntryLike{coverArrowsDef},
	Reading: "Pointwise addition on local defects and arrow shears, with " +
		"explicit normalization at inactive intersections and scalar coordinates."})}

var coverCodeTopologyDef = coverCodeTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "coverCodeTopologyDef",
	Key:   "prop_21ffa859ee61d128",
	Const: "cover_code_topology",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → module_ops(B, D)) → " +
		"set(set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"            prod(set(num), set(num)) → B → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:(set(num) → ring_ops(B)). ∀N:(set(num) → module_ops(B, D)). " +
			"    cover_code_topology(R, S, N) = " +
			"    product_topology(indexed_product_topology(intersection_indices, " +
			"            λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).one, " +
			"            λσ:set(num). factor_set_topology(R, S(σ), N(σ))), " +
			"        indexed_product_topology(cover_arrows, " +
			"            λa:prod(set(num), set(num)). λx:B. N(snd(a)).zero, " +
			"            λa:prod(set(num), set(num)). " +
			"                indexed_discrete_topology(S(fst(a)).carrier, " +
			"                    λx:B. N(snd(a)).zero, " +
			"                    λx:B. N(snd(a)).carrier)))",
	},
	Deps:    []registry.EntryLike{coverArrowsDef},
	Reading: "Countable products of local defect arrays and normalized arrow functions."})}

var coverCodeExtensionsDef = coverCodeExtensionsDefThm{family.Define(registry.DefEntry{
	Name:  "coverCodeExtensionsDef",
	Key:   "prop_5d37e788f397e4c5",
	Const: "cover_code_extensions",
	Type: "(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"set(num) → " +
		"square_zero_ops(A, B, prod(D, B), D)",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"∀σ:set(num). " +
			"    cover_code_extensions(S, f, N, p)(σ) = factor_set_extension(S(σ), f(σ), N(σ), fst(p, σ))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "The local marked extension encoded by the local factor set."})}

var coverCodeMapsDef = coverCodeMapsDefThm{family.Define(registry.DefEntry{
	Name:  "coverCodeMapsDef",
	Key:   "prop_44592bb1f0d41681",
	Const: "cover_code_maps",
	Type: "(set(num) → ring_ops(B)) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"set(num) → " +
		"set(num) → " +
		"prod(D, B) → " +
		"prod(D, B)",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"∀σ τ:set(num). " +
			"∀x:prod(D, B). " +
			"    cover_code_maps(S, N, g, v, p)(σ, τ, x) = " +
			"    (N(τ).add(v(σ, τ, fst(x)), snd(p, (σ, τ), snd(x))), g(σ, τ, snd(x)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Actual maps on extension elements. This " +
		"expression contains no chosen localization section."})}

var coverComparisonCodesDef = coverComparisonCodesDefThm{family.Define(registry.DefEntry{
	Name:  "coverComparisonCodesDef",
	Key:   "prop_cfb62d83f9ab52c5",
	Const: "cover_comparison_codes",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"    cover_comparison_codes(R, S, f, N, g, v) = " +
			"    {p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"            prod(set(num), set(num)) → B → D) | " +
			"        p ∈ cover_code_ambient(R, S, N).carrier ∧ " +
			"        (∀σ:set(num). " +
			"            σ ∈ intersection_indices ⇒ " +
			"            fst(p, σ) ∈ factor_set_codes(R, S(σ), f(σ), N(σ)) ∧ " +
			"            (∀x:B. x ∈ S(σ).carrier ⇒ snd(p, (σ, σ), x) = N(σ).zero)) ∧ " +
			"        (∀σ τ:set(num). " +
			"            σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"            ring_homomorphism(cover_code_extensions(S, f, N, p)(σ).ring, " +
			"                cover_code_extensions(S, f, N, p)(τ).ring, " +
			"                cover_code_maps(S, N, g, v, p)(σ, τ)) ∧ " +
			"            (∀a:A. " +
			"                a ∈ R.carrier ⇒ " +
			"                cover_code_maps(S, N, g, v, p)(σ, " +
			"                    τ, " +
			"                    cover_code_extensions(S, f, N, p)(σ).structure(a)) = " +
			"                cover_code_extensions(S, f, N, p)(τ).structure(a)) ∧ " +
			"            (∀n:D. " +
			"                n ∈ N(σ).carrier ⇒ " +
			"                cover_code_maps(S, N, g, v, p)(σ, " +
			"                    τ, " +
			"                    cover_code_extensions(S, f, N, p)(σ).inclusion(n)) = " +
			"                cover_code_extensions(S, f, N, p)(τ).inclusion(v(σ, τ, n))))}",
	},
	Deps: []registry.EntryLike{coverCodeAmbientDef, coverCodeExtensionsDef, coverCodeMapsDef},
	Reading: "Local codes and actual marked maps on individual arrows, without " +
		"composition equations. This witnesses compatible local extension classes."})}

var coverExtensionCodesDef = coverExtensionCodesDefThm{family.Define(registry.DefEntry{
	Name:  "coverExtensionCodesDef",
	Key:   "prop_a09dccdd5b5c57cf",
	Const: "cover_extension_codes",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"    cover_extension_codes(R, S, f, N, g, v) = " +
			"    {p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"            prod(set(num), set(num)) → B → D) | " +
			"        p ∈ cover_comparison_codes(R, S, f, N, g, v) ∧ " +
			"        (∀σ τ υ:set(num). " +
			"            σ ∈ intersection_indices ∧ " +
			"            τ ∈ intersection_indices ∧ " +
			"            υ ∈ intersection_indices ∧ " +
			"            σ ⊆ τ ∧ " +
			"            τ ⊆ υ ⇒ " +
			"            (∀x:B. " +
			"                x ∈ S(σ).carrier ⇒ " +
			"                snd(p, (σ, υ), x) = " +
			"                N(υ).add(v(τ, υ, snd(p, (σ, τ), x)), snd(p, (τ, υ), g(σ, τ, x)))))}",
	},
	Deps:    []registry.EntryLike{coverComparisonCodesDef},
	Reading: "Impose the linear strict-composition equations on actual extension maps."})}

var coverGaugeGroupDef = coverGaugeGroupDefThm{family.Define(registry.DefEntry{
	Name:  "coverGaugeGroupDef",
	Key:   "prop_2bc7c9d4954c586d",
	Const: "cover_gauge_group",
	Type:  "(set(num) → ring_ops(B)) → (set(num) → module_ops(B, D)) → group_ops(set(num) → B → D)",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). ∀N:(set(num) → module_ops(B, D)). " +
			"    cover_gauge_group(S, N) = " +
			"    mk_group(λh:(set(num) → B → D). λk:(set(num) → B → D). λσ:set(num). λx:B. " +
			"            COND(σ ∈ intersection_indices ∧ x ∈ S(σ).carrier, " +
			"                N(σ).add(h(σ, x), k(σ, x)), " +
			"                N(σ).zero), " +
			"        λσ:set(num). λx:B. N(σ).zero, " +
			"        λh:(set(num) → B → D). λσ:set(num). λx:B. " +
			"            COND(σ ∈ intersection_indices ∧ x ∈ S(σ).carrier, N(σ).neg(h(σ, x)), N(σ).zero), " +
			"        indexed_functions(intersection_indices, " +
			"            λσ:set(num). λx:B. N(σ).zero, " +
			"            λσ:set(num). factor_set_gauge(S(σ), N(σ)).carrier))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "The countable product of zero-preserving normalized section changes."})}

var coverGaugeTopologyDef = coverGaugeTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "coverGaugeTopologyDef",
	Key:   "prop_86a5e2a06e965aa6",
	Const: "cover_gauge_topology",
	Type:  "(set(num) → ring_ops(B)) → (set(num) → module_ops(B, D)) → set(set(set(num) → B → D))",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). ∀N:(set(num) → module_ops(B, D)). " +
			"    cover_gauge_topology(S, N) = " +
			"    indexed_product_topology(intersection_indices, " +
			"        λσ:set(num). λx:B. N(σ).zero, " +
			"        λσ:set(num). " +
			"            subtopology( " +
			"                indexed_discrete_topology(S(σ).carrier, λx:B. N(σ).zero, λx:B. N(σ).carrier), " +
			"                factor_set_gauge(S(σ), N(σ)).carrier))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Product of the closed zero-preserving gauge groups."})}

var coverCoboundaryDef = coverCoboundaryDefThm{family.Define(registry.DefEntry{
	Name:  "coverCoboundaryDef",
	Key:   "prop_5a2099d4b70ef224",
	Const: "cover_coboundary",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → B → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀h:(set(num) → B → D). " +
			"    cover_coboundary(R, S, f, N, g, v)(h) = " +
			"    (λσ:set(num). " +
			"        COND(σ ∈ intersection_indices, " +
			"            factor_set_coboundary(R, S(σ), f(σ), N(σ), h(σ)), " +
			"            factor_set_ambient(R, S(σ), N(σ)).one), " +
			"    λa:prod(set(num), set(num)). λx:B. " +
			"        COND(a ∈ cover_arrows ∧ x ∈ S(fst(a)).carrier, " +
			"            N(snd(a)).add(v(fst(a), snd(a), h(fst(a), x)), " +
			"                N(snd(a)).neg(h(snd(a), g(fst(a), snd(a), x)))), " +
			"            N(snd(a)).zero))",
	},
	Deps: []registry.EntryLike{coverArrowsDef},
	Reading: "Local section coboundaries and the " +
		"conjugation shear nu(gamma_source)-gamma_target after g."})}

var coverBoundariesDef = coverBoundariesDefThm{family.Define(registry.DefEntry{
	Name:  "coverBoundariesDef",
	Key:   "prop_f44a8afa556f5b70",
	Const: "cover_boundaries",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"    cover_boundaries(R, S, f, N, g, v) = " +
			"    image(cover_coboundary(R, S, f, N, g, v), cover_gauge_group(S, N).carrier)",
	},
	Deps:    []registry.EntryLike{coverCoboundaryDef, coverGaugeGroupDef},
	Reading: "The image of simultaneous changes of coordinates, not its closure."})}
