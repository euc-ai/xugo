// yoneda_ext.go — Ext¹(M, N) read on the canonical resolution and the
// extensions of M by N classified by it, with both directions explicit.
// The basis of degree 1 is the kernel K of the augmentation F₀ → M under
// the index embedding j, and the boundary sends the generator at j(k) to
// k; so a 1-cochain g is a cocycle exactly when its linear extension
// kills the kernel of the boundary, and the cocycles and the
// homomorphisms K → N are carried into each other by g ∘ j and φ ∘ j⁻¹,
// linear and inverse; the coboundaries are the restrictions of the
// homomorphisms F₀ → N, and Ext¹ is Hom(K, N) modulo those restrictions.
// An extension is lifted from F₀, free, and its class is the class of the
// map on K the lift reads; a class is realized by the graph extension of
// its map on K; the realization of the class of an extension is
// isomorphic to it, and two extensions are isomorphic exactly when they
// have one class.

package yoneda_ext

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// index is the canonical resolution's index type I(A, B); a member of F₀
// is a function index → A.
const index = "set(prod(num, prod(A, B)))"

// ---------------------------------------------------------------------------
// The conversions and the class
// ---------------------------------------------------------------------------

// syzygyMapDef — `syzygy_map(R, M, N, g, k)`: the map on the kernel K of
// the augmentation a 1-cochain g gives — at k in K the value of g at the
// generator j(k) of degree 1, N.zero off K.
var syzygyMapDef = syzygyMapDefThm{family.Define(registry.DefEntry{
	Name:  "syzygyMapDef",
	Key:   "prop_e4edb97e890e8168",
	Const: "syzygy_map",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, D) → (" + index + " → D) → (" + index + " → A) → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀g:(" + index + " → D). ∀k:(" + index + " → A). " +
			"syzygy_map(R, M, N, g, k) = COND(k ∈ canonical_kernel(R, M, 0), g(index_embedding(k)), N.zero)",
	},
	Reading: "The basis of degree 1 of the canonical resolution is the image of " +
		"K under index_embedding, and the boundary sends the generator at j(k) to k, " +
		"so g ∘ j is g descended along d₁ to K. canonical_kernel(R, M, 0) is the " +
		"kernel group_kernel(M.zero, F₀, canonical_eps(R, M)) of the augmentation, by " +
		"its definition. On a cocycle the result is linear on K (ExtCocycleSyzygyMap).",
})}

// syzygyCocycleDef — `syzygy_cocycle(R, M, N, φ, x)`: the 1-cochain a map φ
// on K gives — at a generator x of degree 1 the value of φ at the member
// j⁻¹(x) of K, N.zero off the generators.
var syzygyCocycleDef = syzygyCocycleDefThm{family.Define(registry.DefEntry{
	Name:  "syzygyCocycleDef",
	Key:   "prop_aec04f6f11320d7d",
	Const: "syzygy_cocycle",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, D) → ((" + index + " → A) → D) → " + index + " → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀φ:((" + index + " → A) → D). ∀x:" + index + ". " +
			"syzygy_cocycle(R, M, N, φ, x) = COND(x ∈ canonical_resolution_terms(R, M, 1), φ(index_preimage(x)), N.zero)",
	},
	Reading: "index_preimage reads a generator of degree 1 back as the member of K it encodes, " +
		"the one preimage index_embedding being injective on the eventually constant functions. The " +
		"value is N.zero off the generators, as a 1-cochain is, and the map keeps sums and negatives " +
		"of every φ and multiples by R's carrier, the zero branch being kept by those operations of N.",
})}

// syzygyClassDef — `syzygy_class(R, M, N, φ)`: the class in Ext¹(M, N) of
// the map φ on K, the coset of its 1-cochain modulo the coboundaries of
// degree 1.
var syzygyClassDef = syzygyClassDefThm{family.Define(registry.DefEntry{
	Name:  "syzygyClassDef",
	Key:   "prop_d2ee27a5729bba85",
	Const: "syzygy_class",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, D) → ((" + index + " → A) → D) → set(" + index + " → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀φ:((" + index + " → A) → D). syzygy_class(R, M, N, φ) = " +
			"left_coset(fun_add(N.add), syzygy_cocycle(R, M, N, φ), coboundaries(canonical_hom_complex(R, M, N), 1))",
	},
	Reading: "The coset is the one cohomology_module forms, so for φ " +
		"linear on K it is a member of ext_module(R, M, N, 1).carrier, and two " +
		"classes are equal exactly when the cochains differ by a coboundary.",
	Deps: []registry.EntryLike{syzygyCocycleDef},
})}

// YonedaClassDef — `yoneda_class(R, M, N, E)`: the class in Ext¹(M, N) of
// the extension E, the class of the map on K read by a lift chosen among
// the lifts of the augmentation to E.
var YonedaClassDef = yonedaClassDefThm{family.Define(registry.DefEntry{
	Name:  "YonedaClassDef",
	Key:   "prop_4299e297ace23d1",
	Const: "yoneda_class",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, D) → module_extension_ops(A, B, C, D) → set(" + index + " → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀E:module_extension_ops(A, B, C, D). yoneda_class(R, M, N, E) = " +
			"syzygy_class(R, M, N, extract_syzygy_map(free_module_record(R, canonical_resolution_terms(R, M, 0)), M, canonical_eps(R, M), N, E, " +
			"εs:((" + index + " → A) → C). module_extension_lift(R, free_module_record(R, canonical_resolution_terms(R, M, 0)), canonical_eps(R, M), E, s)))",
	},
	Reading: "The type C of E enters only through the choice of the lift; the " +
		"class lives in the fixed Ext¹ of the canonical resolution, whatever C is. " +
		"F₀ is free and an extension's projection onto, so a lift exists, and every " +
		"lift gives the same class (YonedaClassWellDefined): the choice is never read.",
	Deps: []registry.EntryLike{syzygyClassDef},
})}

// yonedaRealizationDef — `yoneda_realization(R, M, N, ξ)`: the extension
// realizing the class ξ, the graph extension over F₀ of the map on K of a
// cocycle chosen in ξ.
var yonedaRealizationDef = yonedaRealizationDefThm{family.Define(registry.DefEntry{
	Name:  "yonedaRealizationDef",
	Key:   "prop_1b6ec900e08b394d",
	Const: "yoneda_realization",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, D) → set(" + index + " → D) → module_extension_ops(A, B, set(prod(" + index + " → A, D)), D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀ξ:set(" + index + " → D). yoneda_realization(R, M, N, ξ) = " +
			"module_extension_graph(free_module_record(R, canonical_resolution_terms(R, M, 0)), M, canonical_eps(R, M), N, syzygy_map(R, M, N, εg:(" + index + " → D). g ∈ ξ))",
	},
	Reading: "It is (F₀ ⊕ N)/J_φ for φ = g ∘ j: every realization lives on one type, so the " +
		"classification maps Ext¹ into one type of extensions. A class is a coset of the " +
		"coboundaries at a cocycle, never empty, and each of its members is a cocycle; the chosen " +
		"one is read only up to a coboundary, which changes the extension by an isomorphism.",
	Deps: []registry.EntryLike{syzygyMapDef},
})}

// ---------------------------------------------------------------------------
// Cocycles and homomorphisms on the kernel
// ---------------------------------------------------------------------------

// ExtCocycleSyzygyMap — a 1-cochain is a cocycle exactly when its linear
// extension kills the kernel of the boundary of degree 1; a cocycle gives
// the homomorphism g ∘ j on K.
var ExtCocycleSyzygyMap = extCocycleSyzygyMapThm{family.Add(registry.ProofEntry{
	Name: "ExtCocycleSyzygyMap",
	Key:  "prop_192501b07cfa5214",
	Reading: "The coboundary at a generator j(z) of degree 2 is the linear extension " +
		"of g at z, the boundary of degree 2 sending that generator to z. Linearity on " +
		"K: δ_{j(k + k')} − δ_{j(k)} − δ_{j(k')} and δ_{j(c • k)} − c • δ_{j(k)} lie in " +
		"the kernel of the boundary of degree 1, which sends each δ_{j(k)} to k.",
	Deps: []registry.EntryLike{
		syzygyMapDef,
		tor_ext.CanonicalHomComplexDef,
		tor_ext.HomComplexOf,
		tor_ext.HomCoboundaryDef,
		function_module.FunModuleDef,
		chain_complex.CocyclesDef,
		resolution.CanonicalBoundaryDef,
		resolution.CanonicalSyzygyDef,
		resolution.CanonicalResolutionTermsDef,
		resolution.CanonicalKernelDef,
		resolution.CanonicalKernelAtDef,
		resolution.IndexPreimageDef,
		resolution.IndexEmbeddingInjective,
		resolution.CanonicalBoundaryHom,
		resolution.CanonicalKernelSubmodule,
		free_module.FreeLiftDef,
		free_module.FreeLiftDelta,
		free_module.FreeLiftHom,
		free_module.DeltaAtDef,
		free_module.DeltaAtIn,
		free_module.FreeModuleOn,
		hom_module.HomSetDef,
		module_record.RestrictModuleDef,
		functions.InverseOnLeft,
		module.AddGroupOn,
		module.SmulOne,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀g:(set(prod(num, prod(A, B))) → D). " +
			"    g ∈ cocycles(canonical_hom_complex(R, M, N), 1) ⇔ " +
			"    g ∈ canonical_hom_complex(R, M, N).terms(1) ∧ " +
			"    (∀z:(set(prod(num, prod(A, B))) → A). " +
			"        z ∈ canonical_kernel(R, M, 1) ⇒ «linearExtension»(g, z) = N.zero)) ∧ " +
			"(∀g:(set(prod(num, prod(A, B))) → D). " +
			"    g ∈ cocycles(canonical_hom_complex(R, M, N), 1) ⇒ " +
			"    syzygy_map(R, M, N, g) ∈ " +
			"    hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N))",
	},
		"unfold the coboundary out of degree 1 (CanonicalHomComplexDef, HomComplexOf, "+
			"HomCoboundaryDef): at a generator x of degree 2 it is Σ_y d₂(δ_x)(y) • g(y), N.zero off "+
			"the generators. The generators of degree 2 are j(z) for z in canonical_kernel(R, M, 1) "+
			"(CanonicalResolutionTermsDef, CanonicalSyzygyDef), and d₂ is the linear extension of "+
			"index_preimage (CanonicalBoundaryDef), so d₂(δ_{j(z)}) = index_preimage(j(z)) = z "+
			"(FreeLiftDelta, InverseOnLeft, IndexEmbeddingInjective) and the coboundary there is the "+
			"linear extension of g at z (FreeLiftDef); a cocycle is a cochain the coboundary sends to "+
			"zero (CocyclesDef), which gives the criterion. For the second conjunct, d₁ sends δ_{j(k)} "+
			"to k in the same way, so δ_{j(k + k')} − δ_{j(k)} − δ_{j(k')} and δ_{j(c • k)} − c • "+
			"δ_{j(k)}, members of the free module of degree 1 (DeltaAtIn, FreeModuleOn), are in the "+
			"kernel of d₁ (CanonicalBoundaryHom, DeltaAtDef); the linear extension of g at them is "+
			"g(j(k + k')) − g(j(k)) − g(j(k')) and g(j(c • k)) − c • g(j(k)) (FreeLiftHom, "+
			"FreeLiftDelta), zero by the criterion. Values in N's carrier and N.zero off K make it a "+
			"member of hom_set (HomSetDef, RestrictModuleDef, K a submodule by CanonicalKernelSubmodule)"),
})}

// ExtSyzygyCocycle — a homomorphism φ from K to N gives the 1-cocycle
// φ ∘ j⁻¹.
var ExtSyzygyCocycle = extSyzygyCocycleThm{family.Add(registry.ProofEntry{
	Name: "ExtSyzygyCocycle",
	Key:  "prop_d0e685aafaca75d2",
	Reading: "The linear extension of φ ∘ j⁻¹ at a member z of the " +
		"kernel of d₁ is φ of Σ_x z(x) • j⁻¹(x), which is φ(d₁(z)) = φ(0) " +
		"= N.zero, φ being linear on K and d₁ the linear extension of j⁻¹.",
	Deps: []registry.EntryLike{
		ExtCocycleSyzygyMap,
		syzygyCocycleDef,
		tor_ext.CanonicalHomComplexDef,
		tor_ext.HomComplexOf,
		function_module.FunModuleDef,
		resolution.CanonicalBoundaryDef,
		resolution.CanonicalSyzygyDef,
		resolution.CanonicalResolutionTermsDef,
		resolution.CanonicalKernelDef,
		resolution.CanonicalKernelAtDef,
		resolution.IndexPreimageDef,
		resolution.CanonicalImageIsKernel,
		resolution.CanonicalKernelSubmodule,
		resolution.IndexEmbeddingInjective,
		free_module.FreeLiftDef,
		hom_module.HomSetDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomZero,
		module_record.RestrictModuleDef,
		functions.InverseOnIn,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀φ:((set(prod(num, prod(A, B))) → A) → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"φ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N)",
		},
		Conclusion: "syzygy_cocycle(R, M, N, φ) ∈ cocycles(canonical_hom_complex(R, M, N), 1)",
	},
		"φ ∘ j⁻¹ is a 1-cochain: at a generator x = j(k) of degree 1, index_preimage(x) is k, the "+
			"member of K it encodes, j being injective on the eventually constant functions "+
			"(CanonicalResolutionTermsDef, CanonicalSyzygyDef, IndexPreimageDef, IndexEmbeddingInjective, "+
			"InverseOnLeft, InverseOnIn), so the value is in N's carrier, and it is N.zero off the "+
			"generators (syzygyCocycleDef, FunModuleDef). By ExtCocycleSyzygyMap it is a cocycle when its "+
			"linear extension kills the kernel of d₁: at such z, Σ_x z(x) • φ(j⁻¹(x)) = φ(Σ_x z(x) • "+
			"j⁻¹(x)) (FreeLiftDef, HomSum at φ on K, every j⁻¹(x) in K), and Σ_x z(x) • j⁻¹(x) is d₁(z) "+
			"(CanonicalBoundaryDef), zero, so the value is φ(0) = N.zero (HomZero)"),
})}

// SyzygyCocycleLinearInverse — syzygy_map after syzygy_cocycle is the
// identity on the homomorphisms on K, and syzygy_cocycle after
// syzygy_map on the 1-cochains, as functions; both keep sums, negatives
// and multiples by R on every function.
var SyzygyCocycleLinearInverse = syzygyCocycleLinearInverseThm{family.Add(registry.ProofEntry{
	Name: "SyzygyCocycleLinearInverse",
	Key:  "prop_3207f717a274807f",
	Reading: "The round trips are j⁻¹ ∘ j on K and j ∘ j⁻¹ on the generators of degree 1, " +
		"with the zero branches matching off them: unlike the square-zero bridge, the second " +
		"holds on every 1-cochain, not only the cocycles. Both maps are linear on all functions, " +
		"the zero branch being kept by N's operations; the multiples are by R's carrier.",
	Deps: []registry.EntryLike{
		syzygyMapDef,
		syzygyCocycleDef,
		tor_ext.CanonicalHomComplexDef,
		tor_ext.HomComplexOf,
		function_module.FunModuleDef,
		resolution.CanonicalResolutionTermsDef,
		resolution.CanonicalSyzygyDef,
		resolution.IndexPreimageDef,
		resolution.IndexEmbeddingInjective,
		resolution.CanonicalKernelSubmodule,
		hom_module.HomSetDef,
		function_module.FunAddDef,
		function_module.FunNegDef,
		function_module.FunSmulDef,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InverseOnIn,
		module.AddGroupOn,
		module.SmulZero,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"    φ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N) ⇒ " +
			"    syzygy_map(R, M, N, syzygy_cocycle(R, M, N, φ)) = φ) ∧ " +
			"(∀g:(set(prod(num, prod(A, B))) → D). " +
			"    g ∈ canonical_hom_complex(R, M, N).terms(1) ⇒ " +
			"    syzygy_cocycle(R, M, N, syzygy_map(R, M, N, g)) = g) ∧ " +
			"(∀g₁ g₂:(set(prod(num, prod(A, B))) → D). " +
			"    syzygy_map(R, M, N, fun_add(g₁, g₂)) = " +
			"    fun_add(syzygy_map(R, M, N, g₁), syzygy_map(R, M, N, g₂))) ∧ " +
			"(∀g:(set(prod(num, prod(A, B))) → D). " +
			"    syzygy_map(R, M, N, fun_neg(g)) = fun_neg(syzygy_map(R, M, N, g))) ∧ " +
			"(∀c:A. ∀g:(set(prod(num, prod(A, B))) → D). " +
			"    c ∈ R.carrier ⇒ " +
			"    syzygy_map(R, M, N, fun_smul(N.smul, c, g)) = " +
			"    fun_smul(N.smul, c, syzygy_map(R, M, N, g))) ∧ " +
			"(∀φ₁ φ₂:((set(prod(num, prod(A, B))) → A) → D). " +
			"    syzygy_cocycle(R, M, N, fun_add(φ₁, φ₂)) = " +
			"    fun_add(syzygy_cocycle(R, M, N, φ₁), syzygy_cocycle(R, M, N, φ₂))) ∧ " +
			"(∀φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"    syzygy_cocycle(R, M, N, fun_neg(φ)) = fun_neg(syzygy_cocycle(R, M, N, φ))) ∧ " +
			"(∀c:A. ∀φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"    c ∈ R.carrier ⇒ " +
			"    syzygy_cocycle(R, M, N, fun_smul(N.smul, c, φ)) = " +
			"    fun_smul(N.smul, c, syzygy_cocycle(R, M, N, φ)))",
	},
		"at k in K, syzygy_map(syzygy_cocycle(φ))(k) = φ(index_preimage(j(k))) = φ(k), j(k) being a "+
			"generator of degree 1 (CanonicalResolutionTermsDef, CanonicalSyzygyDef) and j injective on the "+
			"eventually constant functions, which the members of a free module are (IndexEmbeddingInjective, "+
			"InverseOnLeft); off K both are N.zero, φ being N.zero there (HomSetDef). At a generator x = "+
			"j(k), syzygy_cocycle(syzygy_map(g))(x) = g(j(index_preimage(x))) = g(x), index_preimage(x) "+
			"being k in K (IndexPreimageDef, IndexEmbeddingInjective, InverseOnLeft) and j of it x "+
			"(InverseOnIn, InverseOnRight); off the generators both are N.zero, a cochain vanishing there "+
			"(FunModuleDef). Linearity: pointwise at each branch (FunAddDef, FunNegDef, FunSmulDef), N.zero "+
			"kept by N's operations (AddGroupOn, SmulZero)"),
})}

// ExtCoboundaryRestriction — the coboundary of a 0-cochain h is the
// 1-cochain of the restriction to K of its linear extension, and the
// 1-cochain of φ is a coboundary exactly when φ is the restriction to K
// of a homomorphism F₀ → N.
var ExtCoboundaryRestriction = extCoboundaryRestrictionThm{family.Add(registry.ProofEntry{
	Name: "ExtCoboundaryRestriction",
	Key:  "prop_7b4e1687df387679",
	Reading: "The coboundaries of degree 1 are the image of the coboundary out of " +
		"degree 0, and every homomorphism F₀ → N is the linear extension of its values " +
		"at the generators: so the maps on K whose class vanishes are exactly the " +
		"restrictions of homomorphisms out of F₀, the image of Hom(F₀, N) → Hom(K, N).",
	Deps: []registry.EntryLike{
		syzygyCocycleDef,
		SyzygyCocycleLinearInverse,
		ExtCocycleSyzygyMap,
		tor_ext.CanonicalHomComplexDef,
		tor_ext.HomComplexOf,
		tor_ext.HomCoboundaryDef,
		tor_ext.HomComplex,
		function_module.FunModuleDef,
		chain_complex.CoboundariesSucc,
		resolution.CanonicalBoundaryDef,
		resolution.CanonicalSyzygyDef,
		resolution.CanonicalResolutionTermsDef,
		resolution.IndexPreimageDef,
		resolution.IndexEmbeddingInjective,
		resolution.CanonicalKernelDef,
		resolution.CanonicalKernelAtDef,
		resolution.CanonicalResolution,
		resolution.ResolutionComplex,
		free_module.FreeLiftDef,
		free_module.FreeLiftDelta,
		free_module.FreeLiftHom,
		free_module.FreeLiftUnique,
		free_module.FreeModuleOn,
		free_module.DeltaAtDef,
		free_module.DeltaAtIn,
		hom_module.HomSetDef,
		module_record.RestrictModuleDef,
		functions.InverseOnIn,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀h:(set(prod(num, prod(A, B))) → D). " +
			"    h ∈ canonical_hom_complex(R, M, N).terms(0) ⇒ " +
			"    canonical_hom_complex(R, M, N).d(0)(h) = " +
			"    syzygy_cocycle(R, " +
			"        M, " +
			"        N, " +
			"        λk:(set(prod(num, prod(A, B))) → A). " +
			"            COND(k ∈ canonical_kernel(R, M, 0), «linearExtension»(h, k), N.zero))) ∧ " +
			"(∀φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"    φ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N) ⇒ " +
			"    (syzygy_cocycle(R, M, N, φ) ∈ coboundaries(canonical_hom_complex(R, M, N), 1) ⇔ " +
			"        ∃f:((set(prod(num, prod(A, B))) → A) → D). " +
			"            f ∈ hom_set(R, «freeZero», N) ∧ " +
			"            φ = " +
			"            λk:(set(prod(num, prod(A, B))) → A). " +
			"                COND(k ∈ canonical_kernel(R, M, 0), f(k), N.zero)))",
	},
		"the first conjunct: at a generator x = j(k) of degree 1, d₁(δ_x) = index_preimage(x) = k "+
			"(CanonicalBoundaryDef, FreeLiftDelta at the free module F₀ by FreeModuleOn, IndexPreimageDef, "+
			"IndexEmbeddingInjective, InverseOnLeft), so the coboundary there is Σ_y k(y) • h(y), the linear "+
			"extension of h at k (HomCoboundaryDef, FreeLiftDef), which is the right side (syzygyCocycleDef, "+
			"InverseOnIn); off the generators both are N.zero. The coboundaries of degree 1 are the image of "+
			"d(0) on the 0-cochains (CoboundariesSucc, the Hom complex a cochain complex by HomComplex at "+
			"CanonicalResolution, ResolutionComplex). ⇐: for f in hom_set(R, F₀, N) take h(y) = f(δ_y) on "+
			"the generators of degree 0 and N.zero off them, a 0-cochain, δ_y lying in F₀ (DeltaAtIn); its "+
			"linear extension is f on F₀ (FreeLiftHom, FreeLiftDelta, FreeLiftUnique), so d(0)(h) is the "+
			"1-cochain of f restricted to K, which is φ. ⇒: the 1-cochain of φ is d(0)(h) for a 0-cochain h, "+
			"the 1-cochain of the restriction of h's linear extension; syzygy_map undoes syzygy_cocycle on "+
			"maps on K (SyzygyCocycleLinearInverse), so φ is that restriction, and f = h's linear extension "+
			"on F₀, N.zero off it, is in hom_set (FreeLiftHom, HomSetDef), its restriction to K being the "+
			"same since K lies in F₀ (CanonicalKernelDef, CanonicalKernelAtDef)"),
})}

// ---------------------------------------------------------------------------
// Ext¹ as homomorphisms on the kernel modulo restrictions
// ---------------------------------------------------------------------------

// ExtClassRepresented — the class of a homomorphism on K is a member of
// Ext¹(M, N), and every member of Ext¹ is the class of one.
var ExtClassRepresented = extClassRepresentedThm{family.Add(registry.ProofEntry{
	Name: "ExtClassRepresented",
	Key:  "prop_47b880464924fcb8",
	Reading: "The representing map of a class ξ is g ∘ j for any cocycle " +
		"g in ξ: its class is [syzygy_cocycle(syzygy_map(g))] = [g] = ξ.",
	Deps: []registry.EntryLike{
		syzygyClassDef,
		ExtSyzygyCocycle,
		ExtCocycleSyzygyMap,
		SyzygyCocycleLinearInverse,
		tor_ext.ExtModuleDef,
		tor_ext.CanonicalHomComplexDef,
		tor_ext.HomComplexOf,
		chain_complex.CohomologyModuleDef,
		chain_complex.ComplexModuleDef,
		submodule.QuotientModuleDef,
		module_record.RestrictModuleDef,
		quotient_group.LeftCosetsDef,
		quotient_group.InLeftCosets,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"    φ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N) ⇒ " +
			"    syzygy_class(R, M, N, φ) ∈ «ext1») ∧ " +
			"(∀ξ:set(set(prod(num, prod(A, B))) → D). " +
			"    ξ ∈ «ext1» ⇒ " +
			"    ∃φ:((set(prod(num, prod(A, B))) → A) → D). " +
			"        φ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N) ∧ " +
			"        syzygy_class(R, M, N, φ) = ξ)",
	},
		"the carrier of Ext¹ is the set of cosets of the coboundaries of degree 1 at the cocycles "+
			"under fun_add (ExtModuleDef, CohomologyModuleDef, QuotientModuleDef, RestrictModuleDef, "+
			"ComplexModuleDef, CanonicalHomComplexDef, HomComplexOf, LeftCosetsDef), so the class of "+
			"φ is a member, its 1-cochain being a cocycle (ExtSyzygyCocycle, syzygyClassDef). A "+
			"member ξ is the coset of a cocycle g (InLeftCosets); syzygy_map(g) is a homomorphism on "+
			"K (ExtCocycleSyzygyMap) with syzygy_cocycle of it g (SyzygyCocycleLinearInverse)"),
})}

// SyzygyClassEqIffExtends — two homomorphisms on K have one class in
// Ext¹(M, N) exactly when their difference is the restriction to K of a
// homomorphism F₀ → N.
var SyzygyClassEqIffExtends = syzygyClassEqIffExtendsThm{family.Add(registry.ProofEntry{
	Name: "SyzygyClassEqIffExtends",
	Key:  "prop_fefc90728b783adb",
	Reading: "With ExtClassRepresented this is Ext¹(M, N) ≅ Hom(K, N) / image(Hom(F₀, N) → " +
		"Hom(K, N)), K the first syzygy of the canonical resolution. The difference is φ₂ − φ₁ " +
		"pointwise; the class equation is symmetric, so the sign of f is the one convention to keep.",
	Deps: []registry.EntryLike{
		syzygyClassDef,
		ExtCoboundaryRestriction,
		SyzygyCocycleLinearInverse,
		ExtSyzygyCocycle,
		group.LeftCosetEqOn,
		group.SubgroupDef,
		chain_complex.CochainComplex,
		chain_complex.CoboundariesSucc,
		tor_ext.HomComplex,
		resolution.CanonicalResolution,
		resolution.ResolutionComplex,
		hom_module.HomSetModuleOn,
		module_record.RestrictModuleDef,
		module_homomorphism.KernelSubmodule,
		module.AddGroupOn,
		module.AddComm,
		function_module.FunAddDef,
		function_module.FunNegDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀φ₁ φ₂:((set(prod(num, prod(A, B))) → A) → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"φ₁ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N)",
			"φ₂ ∈ hom_set(R, restrict_module(«freeZero», canonical_kernel(R, M, 0)), N)",
		},
		Conclusion: "syzygy_class(R, M, N, φ₁) = syzygy_class(R, M, N, φ₂) ⇔ " +
			"∃f:((set(prod(num, prod(A, B))) → A) → D). " +
			"    f ∈ hom_set(R, «freeZero», N) ∧ " +
			"    fun_add(φ₂, fun_neg(φ₁)) = " +
			"    λk:(set(prod(num, prod(A, B))) → A). COND(k ∈ canonical_kernel(R, M, 0), f(k), N.zero)",
	},
		"the two classes are cosets of the coboundaries, a subgroup of the cochains of degree "+
			"1 under fun_add (HomComplex at CanonicalResolution, CoboundariesSucc, the image of a "+
			"homomorphism), so they are equal exactly when −c₁ + c₂ is a coboundary, c_i the "+
			"1-cochain of φ_i (LeftCosetEqOn at the cochains' additive group). That cochain is "+
			"the 1-cochain of φ₂ − φ₁ by linearity (SyzygyCocycleLinearInverse, AddComm), φ₂ − φ₁ "+
			"is a homomorphism on K (HomSetModuleOn at restrict_module(F₀, K), K a submodule), "+
			"and ExtCoboundaryRestriction turns its being a coboundary into the extension f"),
})}

// ---------------------------------------------------------------------------
// The class of an extension, the realization of a class, and back
// ---------------------------------------------------------------------------

// YonedaClassWellDefined — an extension of M by N has a lift of the
// augmentation, its class is a member of Ext¹(M, N), it is the class of
// the map on K of every lift, and an isomorphic extension has the same
// class.
var YonedaClassWellDefined = yonedaClassWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "YonedaClassWellDefined",
	Key:  "prop_ed4dc718c87c1bc1",
	Reading: "F₀ is free, so the augmentation lifts through the projection onto M " +
		"(FreeLiftThrough). Two lifts differ by a homomorphism F₀ → N whose restriction " +
		"to K is the difference of their maps, which is exactly what leaves the class " +
		"unchanged. An isomorphism φ carries a lift s to the lift φ ∘ s, reading the same " +
		"map, φ being the identity on N. The second extension may be on another type I.",
	Deps: []registry.EntryLike{
		YonedaClassDef,
		SyzygyClassEqIffExtends,
		ExtClassRepresented,
		resolution.FreeLiftThrough,
		resolution.CanonicalEpsHom,
		resolution.CanonicalKernelDef,
		resolution.CanonicalKernelAtDef,
		resolution.CanonicalSyzygyDef,
		resolution.CanonicalResolutionTermsDef,
		module_extension.LiftExtractSyzygy,
		module_extension.LiftDifferenceHom,
		module_extension.ModuleExtension,
		module_extension.ModuleExtensionLiftDef,
		module_extension.ModuleExtensionIsomorphismDef,
		module_extension.ExtractSyzygyMapDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.HomCompose,
		module_homomorphism.ModuleIsomorphismDef,
		free_module.FreeModuleRecordDef,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀E:module_extension_ops(A, B, C, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"module_extension(R, M, N, E)",
		},
		Conclusion: "(∃s:((set(prod(num, prod(A, B))) → A) → C). «lift»(E, s)) ∧ " +
			"yoneda_class(R, M, N, E) ∈ «ext1» ∧ " +
			"(∀s:((set(prod(num, prod(A, B))) → A) → C). " +
			"    «lift»(E, s) ⇒ syzygy_class(R, M, N, «extract»(E, s)) = yoneda_class(R, M, N, E)) ∧ " +
			"(∀E':module_extension_ops(A, B, I, D). ∀φ:(C → I). " +
			"    module_extension(R, M, N, E') ∧ module_extension_isomorphism(R, N, E, E', φ) ⇒ " +
			"    yoneda_class(R, M, N, E') = yoneda_class(R, M, N, E))",
		Abbrev: Abbrev{
			{Name: "lift", Text: "module_extension_lift(R, «freeZero», canonical_eps(R, M))"},
			{Name: "extract", Text: "extract_syzygy_map(«freeZero», M, canonical_eps(R, M), N)"},
		},
	},
		"the lift: FreeLiftThrough at the projection, onto M (ModuleExtension, ShortExactModules), "+
			"and the augmentation, a homomorphism out of F₀ (CanonicalEpsHom, FreeModuleRecordDef); so "+
			"the chosen lift is a lift (YonedaClassDef). The kernel group_kernel(M.zero, F₀, ε) the "+
			"module_extension cards read is canonical_kernel(R, M, 0) (CanonicalKernelDef, "+
			"CanonicalKernelAtDef, CanonicalSyzygyDef, CanonicalResolutionTermsDef). For any lift s, "+
			"its map and the chosen one's are homomorphisms on K (LiftExtractSyzygy) whose difference "+
			"is the restriction of a homomorphism F₀ → N (LiftDifferenceHom), so they have one class "+
			"(SyzygyClassEqIffExtends), a member of Ext¹ (ExtClassRepresented). For φ an isomorphism, "+
			"φ ∘ s is a lift to E' (HomCompose, ModuleExtensionIsomorphismDef), and φ(s(k)) = "+
			"φ(i(φ_s(k))) = i'(φ_s(k)) for k in K, so it reads φ_s (ExtractSyzygyMapDef, "+
			"InverseOnRight, InjectiveOnDef); the third conjunct at E' gives the fourth"),
})}

// YonedaRealizeClass — the realization of a class ξ of Ext¹(M, N) is an
// extension of M by N, and its class is ξ.
var YonedaRealizeClass = yonedaRealizeClassThm{family.Add(registry.ProofEntry{
	Name: "YonedaRealizeClass",
	Key:  "prop_4761e46a26cbbcb",
	Reading: "The class is computed through the canonical lift u ↦ [(u, 0)], not " +
		"through the lift yoneda_class chooses: YonedaClassWellDefined lets any lift " +
		"serve. The canonical lift reads φ back because [(k, 0)] = [(0, φ(k))] for k in K.",
	Deps: []registry.EntryLike{
		yonedaRealizationDef,
		YonedaClassWellDefined,
		ExtCocycleSyzygyMap,
		SyzygyCocycleLinearInverse,
		syzygyClassDef,
		resolution.CanonicalEpsHom,
		resolution.CanonicalEpsOnto,
		resolution.CanonicalKernelDef,
		resolution.CanonicalKernelAtDef,
		resolution.CanonicalSyzygyDef,
		module_extension.GraphModuleExtension,
		module_extension.TwistedGraphSubmodule,
		module_homomorphism.ProductModuleOn,
		module_extension.ModuleExtensionGraphDef,
		module_extension.ModuleExtensionLiftDef,
		module_extension.ExtractSyzygyMapDef,
		module_extension.ModuleExtension,
		module_homomorphism.ProjectionHom,
		module_homomorphism.HomCompose,
		tor_ext.ExtModuleDef,
		tor_ext.HomComplex,
		resolution.CanonicalResolution,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesSucc,
		quotient_group.InLeftCosets,
		group.InOwnLeftCosetOn,
		group.LeftCosetEqOn,
		functions.InverseOnLeft,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀ξ:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"ξ ∈ «ext1»",
		},
		Conclusion: "module_extension(R, M, N, yoneda_realization(R, M, N, ξ)) ∧ " +
			"yoneda_class(R, M, N, yoneda_realization(R, M, N, ξ)) = ξ",
	},
		"ξ is the coset of a cocycle (ExtModuleDef, CohomologyModuleDef, InLeftCosets), so it holds the "+
			"chosen g, a cocycle with ξ its coset (InOwnLeftCosetOn, LeftCosetEqOn): the coboundaries are a "+
			"subgroup of the cocycles (HomComplex at CanonicalResolution, CoboundariesSucc). φ = "+
			"syzygy_map(g) is a homomorphism on K (ExtCocycleSyzygyMap), K being the kernel of the "+
			"augmentation (CanonicalKernelDef, CanonicalKernelAtDef, CanonicalSyzygyDef); the augmentation "+
			"is linear and onto (CanonicalEpsHom, CanonicalEpsOnto), so GraphModuleExtension makes the "+
			"realization an extension (yonedaRealizationDef). The canonical lift u ↦ [(u, 0)] is a "+
			"homomorphism, the inclusion followed by the projection onto the quotient by the submodule J_φ "+
			"(ProductModuleOn, TwistedGraphSubmodule, ProjectionHom, HomCompose), lifting the augmentation "+
			"(GraphModuleExtension); at k in K it is [(k, 0)] = i(φ(k)), so it reads φ (ExtractSyzygyMapDef, "+
			"InverseOnLeft, injectivity of i), and off K both are N.zero. By YonedaClassWellDefined the "+
			"class is [syzygy_cocycle(syzygy_map(g))] = [g] (SyzygyCocycleLinearInverse, syzygyClassDef) = ξ"),
})}

// YonedaRealizeRoundTrip — every extension of M by N is isomorphic to the
// realization of its class.
var YonedaRealizeRoundTrip = yonedaRealizeRoundTripThm{family.Add(registry.ProofEntry{
	Name: "YonedaRealizeRoundTrip",
	Key:  "prop_ce242c4928119fbc",
	Reading: "The isomorphism is a composite: E_{φ_c} ≅ E_{φ_s} by the shear of " +
		"the homomorphism F₀ → N the two maps on K differ by, then E_{φ_s} ≅ E by the " +
		"sum map of the lift s. No card composes extension isomorphisms: the proof " +
		"composes the module isomorphisms and chains the two commutations in place.",
	Deps: []registry.EntryLike{
		yonedaRealizationDef,
		YonedaClassDef,
		YonedaClassWellDefined,
		SyzygyClassEqIffExtends,
		ExtCocycleSyzygyMap,
		ExtSyzygyCocycle,
		SyzygyCocycleLinearInverse,
		syzygyClassDef,
		resolution.CanonicalEpsHom,
		resolution.CanonicalEpsOnto,
		module_extension.LiftExtractSyzygy,
		module_extension.LiftSumQuotientIso,
		module_extension.ShearModuleExtensionIso,
		module_extension.ModuleExtensionIsomorphismDef,
		tor_ext.HomComplex,
		resolution.CanonicalResolution,
		chain_complex.CoboundariesSucc,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
		functions.InjectiveOnCompose,
		group.InOwnLeftCosetOn,
		group.LeftCosetEqOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀E:module_extension_ops(A, B, C, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"module_extension(R, M, N, E)",
		},
		Conclusion: "∃φ:(set(prod(set(prod(num, prod(A, B))) → A, D)) → C). " +
			"    module_extension_isomorphism(R, " +
			"        N, " +
			"        yoneda_realization(R, M, N, yoneda_class(R, M, N, E)), " +
			"        E, " +
			"        φ)",
	},
		"let s be the chosen lift (YonedaClassWellDefined, YonedaClassDef) and φ_s its map on K "+
			"(LiftExtractSyzygy); LiftSumQuotientIso gives E_{φ_s} ≅ E, the augmentation being linear "+
			"and onto (CanonicalEpsHom, CanonicalEpsOnto). The realization is E_{φ_c} for c chosen in "+
			"the class of E, the class of syzygy_cocycle(φ_s) (yonedaRealizationDef, YonedaClassDef, "+
			"syzygyClassDef); syzygy_cocycle(φ_s) is a cocycle (ExtSyzygyCocycle) and the coboundaries "+
			"a subgroup of the cocycles (HomComplex at CanonicalResolution, CoboundariesSucc), so c, a "+
			"member of its coset, is a cocycle; φ_c = syzygy_map(c) is a homomorphism on K "+
			"(ExtCocycleSyzygyMap) with [syzygy_cocycle(φ_c)] = [c] = [syzygy_cocycle(φ_s)] "+
			"(SyzygyCocycleLinearInverse, InOwnLeftCosetOn, LeftCosetEqOn), so φ_s − φ_c is the "+
			"restriction of a homomorphism h: F₀ → N (SyzygyClassEqIffExtends) and "+
			"ShearModuleExtensionIso gives E_{φ_c} ≅ E_{φ_s}. Compose: homomorphisms compose "+
			"(HomCompose), the composite is injective (InjectiveOnCompose) and onto, and the inclusion "+
			"and projection equations chain (ModuleExtensionIsomorphismDef, ModuleIsomorphismDef)"),
})}

// YonedaIsoIffSameClass — two extensions of M by N, on any two types, are
// isomorphic exactly when they have the same class in Ext¹(M, N).
var YonedaIsoIffSameClass = yonedaIsoIffSameClassThm{family.Add(registry.ProofEntry{
	Name: "YonedaIsoIffSameClass",
	Key:  "prop_689ec028dc4ee03b",
	Reading: "With YonedaRealizeClass this is the classification: the isomorphism " +
		"classes of extensions of M by N are in bijection with Ext¹(M, N), yoneda_class " +
		"one way and yoneda_realization the other. ⇐ goes through the realization of the " +
		"common class, an inverse of one isomorphism composed with the other. Only the " +
		"set-level bijection is stated; the module structure of Ext¹ as the Baer sum is not.",
	Deps: []registry.EntryLike{
		YonedaClassWellDefined,
		YonedaRealizeRoundTrip,
		module_extension.ModuleExtensionIsomorphismDef,
		module_extension.ModuleExtension,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InverseOnIn,
		functions.InjectiveOnCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀E':module_extension_ops(A, B, I, D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"module_extension(R, M, N, E)",
			"module_extension(R, M, N, E')",
		},
		Conclusion: "(∃φ:(C → I). module_extension_isomorphism(R, N, E, E', φ)) ⇔ " +
			"yoneda_class(R, M, N, E) = yoneda_class(R, M, N, E')",
	},
		"⇒ is the fourth conjunct of YonedaClassWellDefined. ⇐: with ξ the common class, "+
			"YonedaRealizeRoundTrip gives isomorphisms ψ from the realization of ξ to E and ψ' to "+
			"E'. inverse_on(the realization's carrier, ψ) is a module isomorphism from E to the "+
			"realization (IsomorphismInverse), and it commutes with the inclusions and the "+
			"projections, each equation of ψ read through the inverse (InverseOnLeft, "+
			"InverseOnRight, InverseOnIn); composed with ψ' (HomCompose, InjectiveOnCompose, "+
			"ModuleIsomorphismDef) it is an isomorphism from E to E' (ModuleExtensionIsomorphismDef)"),
})}
