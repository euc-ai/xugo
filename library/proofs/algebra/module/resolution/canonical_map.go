// canonical_map.go — strict maps of the canonical free resolutions.

package resolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CanonicalMapDef — transport the encoded carrier at zero and the encoded preceding kernel at each successor.
var CanonicalMapDef = canonicalMapDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalMapDef",
	Const: "canonical_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(B → C) → " +
		"num → " +
		"(set(prod(num, prod(A, B))) → A) → " +
		"(set(prod(num, prod(A, C))) → A)",
	Key: "prop_bcfa1932ef9f1fc6",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀L:module_ops(A, C). ∀f:(B → C). " +
			"    canonical_map(R, M, L, f, 0) = " +
			"    free_pushforward(R, " +
			"        λj:set(prod(num, prod(A, B))). carrier_embedding⟨A:A, B:C⟩(f(carrier_preimage(M, j))))",
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀L:module_ops(A, C). ∀f:(B → C). ∀n:num. " +
			"    canonical_map(R, M, L, f, suc(n)) = " +
			"    free_pushforward(R, " +
			"        λj:set(prod(num, prod(A, B))). " +
			"            index_embedding⟨A:A, B:C⟩(canonical_map(R, M, L, f, n, index_preimage⟨A:A, B:B⟩(j))))",
	},
	Deps: []registry.EntryLike{
		carrierEmbeddingDef,
		carrierPreimageDef,
		IndexEmbeddingDef,
		IndexPreimageDef,
	},
})}

// CanonicalMapAugmentation — the degree-0 lift of a homomorphism commutes
// with the augmentations on the free module of degree 0.
var CanonicalMapAugmentation = canonicalMapAugmentationThm{family.Add(registry.ProofEntry{
	Name: "CanonicalMapAugmentation",
	Key:  "prop_5725dd5963936510",
	Deps: []registry.EntryLike{
		CanonicalMapDef,
		CanonicalEpsDef,
		CanonicalEpsHom,
		CanonicalResolutionTermsDef,
		CanonicalSyzygyDef,
		CarrierPreimageEmbedding,
		free_module.FreePushforwardDelta,
		free_module.FreePushforwardHom,
		free_module.FreeLiftUnique,
		module_homomorphism.HomCompose,
		module_homomorphism.HomIn,
		free_module.FreeLiftDelta,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀u:(set(prod(num, prod(A, B))) → A).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"u ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, 0))",
		},
		Conclusion: "canonical_eps(R, L, canonical_map(R, M, L, f, 0, u)) = f(canonical_eps(R, M, u))",
	},
		"On a basis point carrier_embedding(b) with b in M.carrier, CarrierPreimageEmbedding "+
			"decodes b. HomIn puts f(b) in L.carrier, where CarrierPreimageEmbedding decodes the "+
			"target code to f(b). FreePushforwardDelta and FreeLiftDelta give the augmentation "+
			"square there; uniqueness of linear extension gives it on the degree-zero free carrier."),
})}

// CanonicalMapKernel — the lift of a homomorphism carries each kernel of
// the source resolution into the kernel of the target in that degree.
var CanonicalMapKernel = canonicalMapKernelThm{family.Add(registry.ProofEntry{
	Name: "CanonicalMapKernel",
	Key:  "prop_35c2fa0eb27ed4f1",
	Deps: []registry.EntryLike{
		CanonicalMapDef,
		CanonicalMapAugmentation,
		CanonicalResolution,
		CanonicalKernelDef,
		CanonicalKernelAtDef,
		CanonicalImageIsKernel,
		CanonicalTermsEncodeKernel,
		CanonicalBoundaryFreeLift,
		CanonicalKernelInFree,
		IndexPreimageEmbedding,
		free_module.FreePushforwardHom,
		free_module.FreePushforwardDelta,
		free_module.FreeLiftUnique,
		module_homomorphism.HomZero,
		set_basic.InImage,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportEventuallyConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀L:module_ops(A, C). ∀f:(B → C). ∀n:num.",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
		},
		Conclusion: "image(canonical_map(R, M, L, f, n), canonical_kernel(R, M, n)) ⊆ " +
			"canonical_kernel(R, L, n)",
	},
		"Induct with the stronger invariant: the map is linear on the free term and commutes with the "+
			"augmentation or boundary. The square carries the kernel into the kernel. A kernel vector lies "+
			"in its free term (CanonicalKernelInFree), so it has finite support and is eventually constant, "+
			"and IndexPreimageEmbedding decodes its code in source and target. The next basis transport "+
			"lands in its target basis (CanonicalTermsEncodeKernel), and equality on those generators proves "+
			"the next square, each boundary being the free lift of the decoder (CanonicalBoundaryFreeLift)."),
})}

// CanonicalMapChain — the lift of a homomorphism is a chain map between
// the canonical free complexes.
var CanonicalMapChain = canonicalMapChainThm{family.Add(registry.ProofEntry{
	Name: "CanonicalMapChain",
	Key:  "prop_fcbdf6b537344ff0",
	Deps: []registry.EntryLike{
		CanonicalMapDef,
		CanonicalMapKernel,
		CanonicalResolution,
		FreeComplexOf,
		chain_complex.ChainMapDef,
		CanonicalTermsEncodeKernel,
		CanonicalBoundaryFreeLift,
		CanonicalKernelInFree,
		IndexPreimageEmbedding,
		free_module.FreePushforwardHom,
		free_module.FreePushforwardDelta,
		free_module.FreeLiftUnique,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportEventuallyConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀L:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
		},
		Conclusion: "chain_map(R, " +
			"    free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)), " +
			"    free_complex(R, canonical_resolution_terms(R, L), canonical_boundary(R, L)), " +
			"    canonical_map(R, M, L, f))",
	},
		"CanonicalMapKernel makes each basis map land in the next basis. Write a source "+
			"basis point of positive degree as index_embedding(v), with v in the source kernel "+
			"(CanonicalTermsEncodeKernel), and its transported point using canonical_map(v) in "+
			"the target kernel. Both vectors lie in their free terms (CanonicalKernelInFree), "+
			"so they are eventually constant and IndexPreimageEmbedding decodes both codes. "+
			"The boundaries, free lifts of the decoder (CanonicalBoundaryFreeLift), commute on "+
			"these generators and hence on the free carrier by FreeLiftUnique."),
})}

// CanonicalMapIdentity — the lift of the identity is the identity on each
// free module of the canonical resolution.
var CanonicalMapIdentity = canonicalMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "CanonicalMapIdentity",
	Key:  "prop_f536c1e3bbd0c409",
	Deps: []registry.EntryLike{
		CanonicalMapDef,
		CanonicalMapKernel,
		CanonicalMapChain,
		CanonicalResolution,
		CanonicalResolutionTermsDef,
		CanonicalSyzygyDef,
		CanonicalTermsEncodeKernel,
		CanonicalKernelInFree,
		CarrierPreimageEmbedding,
		IndexPreimageEmbedding,
		free_module.FreePushforwardIdentity,
		free_module.FreeLiftUnique,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportEventuallyConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀u:(set(prod(num, prod(A, B))) → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"u ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n))",
		},
		Conclusion: "canonical_map(R, M, M, λv:B. v, n, u) = u",
	},
		"Induct on degree. At zero write each basis point as carrier_embedding(b), b in "+
			"M.carrier, which CarrierPreimageEmbedding decodes to b. At a successor write it as "+
			"index_embedding(v), v in the preceding kernel (CanonicalTermsEncodeKernel); v lies in "+
			"its free term (CanonicalKernelInFree), so it is eventually constant and "+
			"IndexPreimageEmbedding decodes it to v, which the induction hypothesis fixes. So the "+
			"basis map is the identity, and its linear extension is the identity on the free carrier."),
})}

// CanonicalMapCompose — the lift of a composite is the composite of the
// lifts on each free module of the canonical resolution.
var CanonicalMapCompose = canonicalMapComposeThm{family.Add(registry.ProofEntry{
	Name: "CanonicalMapCompose",
	Key:  "prop_8c71c4ffa9caa59",
	Deps: []registry.EntryLike{
		CanonicalMapDef,
		CanonicalMapKernel,
		CanonicalMapChain,
		CanonicalResolution,
		CanonicalResolutionTermsDef,
		CanonicalSyzygyDef,
		CanonicalTermsEncodeKernel,
		CanonicalKernelInFree,
		CarrierPreimageEmbedding,
		IndexPreimageEmbedding,
		free_module.FreePushforwardCompose,
		free_module.FreeLiftUnique,
		module_homomorphism.HomIn,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportEventuallyConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀K:module_ops(A, D). " +
			"∀g:(C → D). " +
			"∀n:num. " +
			"∀u:(set(prod(num, prod(A, B))) → A).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_homomorphism(R, L, K, g)",
			"u ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n))",
		},
		Conclusion: "canonical_map(R, M, K, g ∘ f, n, u) = " +
			"canonical_map(R, L, K, g, n, canonical_map(R, M, L, f, n, u))",
	},
		"Induct on degree. At zero HomIn puts f(b) in the intermediate module carrier, "+
			"where CarrierPreimageEmbedding decodes its code. At a successor CanonicalMapKernel "+
			"puts the transported vector in the intermediate kernel, which lies in its free "+
			"term (CanonicalKernelInFree); so the vector is eventually constant, and "+
			"IndexPreimageEmbedding decodes its code. The induction hypothesis makes the basis "+
			"maps compose there, hence their linear extensions agree on the free carrier."),
})}
