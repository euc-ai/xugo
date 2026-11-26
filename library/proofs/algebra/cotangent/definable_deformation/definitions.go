package definable_deformation

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	_ "github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var FactorSetAmbientDef = factorSetAmbientDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetAmbientDef",
	Key:   "prop_6d01d57408e5a70c",
	Const: "factor_set_ambient",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"module_ops(B, D) → " +
		"group_ops(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀N:module_ops(B, D). " +
			"    factor_set_ambient(R, S, N) = " +
			"    mk_group(λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"        λw:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"            (λp:prod(B, B). N.add(fst(z, p), fst(w, p)), " +
			"            (λp:prod(B, B). N.add(fst(snd(z), p), fst(snd(w), p)), " +
			"            λr:A. N.add(snd(snd(z), r), snd(snd(w), r)))), " +
			"        (λp:prod(B, B). N.zero, (λp:prod(B, B). N.zero, λr:A. N.zero)), " +
			"        λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"            (λp:prod(B, B). N.neg(fst(z, p)), " +
			"            (λp:prod(B, B). N.neg(fst(snd(z), p)), λr:A. N.neg(snd(snd(z), r)))), " +
			"        set_cross(indexed_functions(set_cross(S.carrier, S.carrier), " +
			"                λp:prod(B, B). N.zero, " +
			"                λp:prod(B, B). N.carrier), " +
			"            set_cross(indexed_functions(set_cross(S.carrier, S.carrier), " +
			"                    λp:prod(B, B). N.zero, " +
			"                    λp:prod(B, B). N.carrier), " +
			"                indexed_functions(R.carrier, λr:A. N.zero, λr:A. N.carrier))))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Three normalized function spaces for additive defect, " +
		"multiplicative defect and structure defect, with pointwise addition."})}

var FactorSetTopologyDef = factorSetTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetTopologyDef",
	Key:   "prop_50ce6b820a1d177e",
	Const: "factor_set_topology",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"module_ops(B, D) → " +
		"set(set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀N:module_ops(B, D). " +
			"    factor_set_topology(R, S, N) = " +
			"    product_topology(indexed_discrete_topology(set_cross(S.carrier, S.carrier), " +
			"            λp:prod(B, B). N.zero, " +
			"            λp:prod(B, B). N.carrier), " +
			"        product_topology(indexed_discrete_topology(set_cross(S.carrier, S.carrier), " +
			"                λp:prod(B, B). N.zero, " +
			"                λp:prod(B, B). N.carrier), " +
			"            indexed_discrete_topology(R.carrier, λr:A. N.zero, λr:A. N.carrier)))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "The topology of pointwise discrete coefficient values on all three defect arrays."})}

var factorSetRingDef = factorSetRingDefThm{family.Define(registry.DefEntry{
	Name:  "factorSetRingDef",
	Key:   "prop_52874cf2053de422",
	Const: "factor_set_ring",
	Type: "ring_ops(B) → " +
		"module_ops(B, D) → " +
		"prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) → " +
		"ring_ops(prod(D, B))",
	Equations: []string{
		"∀S:ring_ops(B). ∀N:module_ops(B, D). ∀z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"    factor_set_ring(S, N, z) = " +
			"    mk_ring(λx:prod(D, B). λy:prod(D, B). " +
			"            (N.add(N.add(fst(x), fst(y)), fst(z, (snd(x), snd(y)))), S.add(snd(x), snd(y))), " +
			"        (N.zero, S.zero), " +
			"        λx:prod(D, B). (N.neg(N.add(fst(x), fst(z, (snd(x), S.neg(snd(x)))))), S.neg(snd(x))), " +
			"        λx:prod(D, B). λy:prod(D, B). " +
			"            (N.add(N.add(N.smul(snd(x), fst(y)), N.smul(snd(y), fst(x))), " +
			"                    fst(snd(z), (snd(x), snd(y)))), " +
			"                S.mul(snd(x), snd(y))), " +
			"        (N.neg(fst(snd(z), (S.one, S.one))), S.one), " +
			"        λx:prod(D, B). λy:prod(D, B). " +
			"            (N.add(N.add(fst(x), N.neg(N.add(fst(y), fst(z, (snd(y), S.neg(snd(y))))))), " +
			"                    fst(z, (snd(x), S.neg(snd(y))))), " +
			"                S.sub(snd(x), snd(y))), " +
			"        set_cross(N.carrier, S.carrier))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The ring operations of a zero-preserving section. Its unit " +
		"is corrected by minus beta(1,1); the section need not preserve one."})}

var FactorSetExtensionDef = factorSetExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetExtensionDef",
	Key:   "prop_738c653bfcbe6416",
	Const: "factor_set_extension",
	Type: "ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) → " +
		"square_zero_ops(A, B, prod(D, B), D)",
	Equations: []string{
		"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"    factor_set_extension(S, f, N, z) = " +
			"    mk_square_zero(factor_set_ring(S, N, z), " +
			"        λr:A. (snd(snd(z), r), f(r)), " +
			"        λn:D. (n, S.zero), " +
			"        λx:prod(D, B). snd(x))",
	},
	Deps:    []registry.EntryLike{factorSetRingDef},
	Reading: "The fixed markings are n ↦ (n,0), projection to S, and r ↦ (rho(r),f(r))."})}

var FactorSetCodesDef = factorSetCodesDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetCodesDef",
	Key:   "prop_407cc700c223d24f",
	Const: "factor_set_codes",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    factor_set_codes(R, S, f, N) = " +
			"    {z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) | " +
			"        z ∈ factor_set_ambient(R, S, N).carrier ∧ " +
			"        square_zero_extension(R, S, f, N, factor_set_extension(S, f, N, z))}",
	},
	Deps: []registry.EntryLike{FactorSetAmbientDef, FactorSetExtensionDef},
	Reading: "Valid normalized defects are exactly the arrays for " +
		"which the explicit operations and fixed markings form a square-zero " +
		"extension. This is a structural condition, not a class condition."})}

var FactorSetGaugeDef = factorSetGaugeDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetGaugeDef",
	Key:   "prop_764781a737c64d91",
	Const: "factor_set_gauge",
	Type:  "ring_ops(B) → module_ops(B, D) → group_ops(B → D)",
	Equations: []string{
		"∀S:ring_ops(B). ∀N:module_ops(B, D). " +
			"    factor_set_gauge(S, N) = " +
			"    restrict_group(module_additive_group(function_module(N, S.carrier)), " +
			"        {h:(B → D) | " +
			"            h ∈ module_additive_group(function_module(N, S.carrier)).carrier ∧ " +
			"            h(S.zero) = N.zero})",
	},
	Deps: []registry.EntryLike{},
	Reading: "Zero-preserving, off-carrier-normalized " +
		"changes of section. The fixed inclusion forces h(0)=0."})}

var FactorSetCoboundaryDef = factorSetCoboundaryDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetCoboundaryDef",
	Key:   "prop_45f41e9ad0b8b860",
	Const: "factor_set_coboundary",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"(B → D) → " +
		"prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀h:(B → D). " +
			"    factor_set_coboundary(R, S, f, N, h) = " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            N.add(N.add(h(fst(p)), h(snd(p))), N.neg(h(S.add(fst(p), snd(p))))), " +
			"            N.zero), " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            N.add(N.add(N.smul(fst(p), h(snd(p))), N.smul(snd(p), h(fst(p)))), " +
			"                N.neg(h(S.mul(fst(p), snd(p))))), " +
			"            N.zero), " +
			"    λr:A. COND(r ∈ R.carrier, N.neg(h(f(r))), N.zero)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The three components are h(s)+h(t)-h(s+t), s*h(t)+t*h(s)-h(st), " +
		"and -h(f(r)). Values outside active carriers are zero."})}

var factorSetGroupDef = factorSetGroupDefThm{family.Define(registry.DefEntry{
	Name:  "factorSetGroupDef",
	Key:   "prop_c9e7e9c9f36f21d5",
	Const: "factor_set_group",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"group_ops(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    factor_set_group(R, S, f, N) = " +
			"    restrict_group(factor_set_ambient(R, S, N), factor_set_codes(R, S, f, N))",
	},
	Deps:    []registry.EntryLike{FactorSetAmbientDef, FactorSetCodesDef},
	Reading: "The additive group record of valid factor sets."})}

var FactorSetBoundariesDef = factorSetBoundariesDefThm{family.Define(registry.DefEntry{
	Name:  "FactorSetBoundariesDef",
	Key:   "prop_14e1a3e68168bf13",
	Const: "factor_set_boundaries",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    factor_set_boundaries(R, S, f, N) = " +
			"    image(factor_set_coboundary(R, S, f, N), factor_set_gauge(S, N).carrier)",
	},
	Deps:    []registry.EntryLike{FactorSetCoboundaryDef, FactorSetGaugeDef},
	Reading: "Actual coboundaries, with no closure."})}
