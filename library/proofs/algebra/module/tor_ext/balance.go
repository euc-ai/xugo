// balance.go — the tensor double complex of the two canonical free
// resolutions. A basis index is (p, (x, y)); retaining p distinguishes
// summands even when the same basis element occurs in several degrees.
// Its two augmentation edges give the natural symmetry of Tor.

package tor_ext

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// totalBasisDef — the product basis in bidegree (p,q).
var totalBasisDef = totalBasisDefThm{family.Define(registry.DefEntry{
	Name:  "totalBasisDef",
	Const: "total_basis",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"num → " +
		"set(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))))",
	Key: "prop_46ac43cf1c559c31",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀p q:num. " +
			"    total_basis(R, M, N, p, q) = " +
			"    set_cross(canonical_resolution_terms(R, M, p), canonical_resolution_terms(R, N, q))",
	},
})}

// totalCellsDef — the free module in each bidegree.
var totalCellsDef = totalCellsDefThm{family.Define(registry.DefEntry{
	Name:  "totalCellsDef",
	Const: "total_cells",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"num → " +
		"set((prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A))",
	Key: "prop_b6ce73d66c275a72",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀p q:num. " +
			"    total_cells(R, M, N, p, q) = finite_supp(R.zero, R.carrier, total_basis(R, M, N, p, q))",
	},
	Deps: []registry.EntryLike{totalBasisDef},
})}

// totalHorizontalDef — extend the corresponding resolution differential on product generators.
var totalHorizontalDef = totalHorizontalDefThm{family.Define(registry.DefEntry{
	Name:  "totalHorizontalDef",
	Const: "total_horizontal",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"num → " +
		"(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A) → " +
		"(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A)",
	Key: "prop_a53c64f12464e885",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀p q:num. " +
			"    total_horizontal(R, M, N, p, q) = " +
			"    free_lift(R.zero, " +
			"        fun_add⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.add), " +
			"        fun_zero⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.zero), " +
			"        fun_smul⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.mul), " +
			"        λz:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"        λw:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"            R.mul(canonical_boundary(R, M, p, delta_at(R.zero, R.one, fst(z)))(fst(w)), " +
			"                COND(snd(w) = snd(z), R.one, R.zero)))",
	},
})}

// totalVerticalDef — extend the corresponding resolution differential on product generators.
var totalVerticalDef = totalVerticalDefThm{family.Define(registry.DefEntry{
	Name:  "totalVerticalDef",
	Const: "total_vertical",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"num → " +
		"(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A) → " +
		"(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A)",
	Key: "prop_77e122433ce41017",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀p q:num. " +
			"    total_vertical(R, M, N, p, q) = " +
			"    free_lift(R.zero, " +
			"        fun_add⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.add), " +
			"        fun_zero⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.zero), " +
			"        fun_smul⟨D:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩(R.mul), " +
			"        λz:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"        λw:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"            R.mul(COND(fst(w) = fst(z), R.one, R.zero), " +
			"                canonical_boundary(R, N, q, delta_at(R.zero, R.one, snd(z)))(snd(w))))",
	},
})}

// totalTaggedBasisDef — the disjoint diagonal union, represented by its horizontal-degree tag.
var totalTaggedBasisDef = totalTaggedBasisDefThm{family.Define(registry.DefEntry{
	Name:  "totalTaggedBasisDef",
	Const: "total_tagged_basis",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))))",
	Key: "prop_a9f18d0c038a545a",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    total_tagged_basis(R, M, N, n) = " +
			"    {z:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) | " +
			"        fst(z) ≤ n ∧ snd(z) ∈ total_basis(R, M, N, fst(z), n - fst(z))}",
	},
	Deps: []registry.EntryLike{totalBasisDef},
})}

// totalBoundaryDef — flatten the diagonal differential h + (−1)^p v onto tagged coefficients.
var totalBoundaryDef = totalBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "totalBoundaryDef",
	Const: "total_boundary",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A) → " +
		"(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A)",
	Key: "prop_e111c4f3d5690d6c",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀u:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"∀z:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))). " +
			"    total_boundary(R, M, N, n, u, z) = " +
			"    double_boundary(free_module_record(R, " +
			"            𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩), " +
			"        total_horizontal(R, M, N), " +
			"        total_vertical(R, M, N), " +
			"        alternating_sign(R.one, R.neg), " +
			"        n, " +
			"        (λp:num. λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). u((p, j))), " +
			"        fst(z))(snd(z))",
	},
	Deps: []registry.EntryLike{totalHorizontalDef, totalVerticalDef},
})}

// totalComplexOf — the total complex in the single tagged index type.
var totalComplexOf = totalComplexOfThm{family.Define(registry.DefEntry{
	Name:  "totalComplexOf",
	Const: "total_complex",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A)",
	Key: "prop_9722ebf4c51a7c9c",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    total_complex(R, M, N) = " +
			"    pack_complex(fun_add⟨ " +
			"            D:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))))⟩(R.add), " +
			"        fun_zero⟨D:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))))⟩( " +
			"            R.zero), " +
			"        fun_neg⟨D:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))))⟩( " +
			"            R.neg), " +
			"        fun_smul⟨D:prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))))⟩( " +
			"            R.mul), " +
			"        (λn:num. finite_supp(R.zero, R.carrier, total_tagged_basis(R, M, N, n))), " +
			"        total_boundary(R, M, N))",
	},
	Deps: []registry.EntryLike{totalTaggedBasisDef, totalBoundaryDef},
})}

// TensorFreeIsFreeOnProduct — Send δ_x ⊗ δ_y to δ_(x,y). Bilinearity extends this map, and expansion in the two bases supplies its inverse.
var TensorFreeIsFreeOnProduct = tensorFreeIsFreeOnProductThm{family.Add(registry.ProofEntry{
	Name: "TensorFreeIsFreeOnProduct",
	Key:  "prop_64b88da4d26b90f1",
	Deps: []registry.EntryLike{
		tensor_product.TensorModuleDef,
		free_module.FreeModuleRecordDef,
		FiniteSuppTensorIso,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		free_module.FreeModuleExpand,
		free_module.FreeLiftUnique,
		module_homomorphism.ModuleIsomorphicDef,
		set_product.SetCrossDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀T:set(E).",
		Hypotheses: []string{
			"module_on(R, free_module_record(R, S))",
		},
		Conclusion: "module_isomorphic(R, " +
			"    tensor_module(R, free_module_record(R, S), free_module_record(R, T)), " +
			"    free_module_record(R, set_cross(S, T)))",
	},
		"Send δ_x ⊗ δ_y to δ_(x,y). Bilinearity extends this map, "+
			"and expansion in the two bases supplies its inverse."),
})}

// FreeTensorExact — Tensoring a short exact sequence with a free module is exact. Work pointwise, choosing zero as the preimage of zero so finite support is preserved. Applied to kernels and successive terms, this proves exactness of the augmented columns.
var FreeTensorExact = freeTensorExactThm{family.Add(registry.ProofEntry{
	Name: "FreeTensorExact",
	Key:  "prop_eb0e71be4b5347",
	Deps: []registry.EntryLike{
		module_homomorphism.ShortExactModules,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppModuleOn,
		function_module.FiniteSuppDef,
		FiniteSuppTensorIso,
		module_homomorphism.HomZero,
		module_homomorphism.ExactAtDef,
		set_basic.InImage,
	},
	Build: family.Card(
		module_homomorphism.ShortExactModules.Statement(
			"∀S:set(I). "+
				"    short_exact_modules(R, "+
				"        finite_supp_module(N', S), "+
				"        finite_supp_module(N, S), "+
				"        finite_supp_module(N'', S), "+
				"        (λg:(I → C). λx:I. i(g(x))), "+
				"        (λg:(I → D). λx:I. p(g(x))))"),
		"Tensoring a short exact sequence with a free module is exact. Work pointwise, "+
			"choosing zero as the preimage of zero so finite support is preserved. Applied "+
			"to kernels and successive terms, this proves exactness of the augmented columns."),
})}

// ResolutionDoubleComplex — On product generators h² and v² are the corresponding squares in the resolutions. The two mixed maps commute on generators, hence on the free carrier by uniqueness of linear extension.
var ResolutionDoubleComplex = resolutionDoubleComplexThm{family.Add(registry.ProofEntry{
	Name: "ResolutionDoubleComplex",
	Key:  "prop_19e050440cabb443",
	Deps: []registry.EntryLike{
		chain_complex.DoubleComplex,
		totalCellsDef,
		totalHorizontalDef,
		totalVerticalDef,
		totalBasisDef,
		TensorFreeIsFreeOnProduct,
		resolution.CanonicalResolution,
		resolution.CanonicalBoundaryTwice,
		resolution.CanonicalBoundaryHom,
		free_module.FreeLiftHom,
		free_module.FreeLiftUnique,
		free_module.FreeModuleExpand,
		free_module.FreeModuleRecordDef,
		module.ModuleSumSwap,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "double_complex(R, " +
			"    free_module_record(R, 𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩), " +
			"    total_cells(R, M, N), " +
			"    total_horizontal(R, M, N), " +
			"    total_vertical(R, M, N))",
	},
		"On product generators h² and v² are the corresponding squares in the resolutions. The two "+
			"mixed maps commute on generators, hence on the free carrier by uniqueness of linear extension."),
})}

// TotalComplex — Currying tagged coefficients identifies a total term with the finite diagonal direct sum. DoubleTotalComplex gives the differential laws; a finite union of the finitely supported diagonal slices is finitely supported.
var TotalComplex = totalComplexThm{family.Add(registry.ProofEntry{
	Name: "TotalComplex",
	Key:  "prop_7b24e9b5209a44ae",
	Deps: []registry.EntryLike{
		totalComplexOf,
		totalBoundaryDef,
		totalTaggedBasisDef,
		totalCellsDef,
		ResolutionDoubleComplex,
		chain_complex.DoubleTotalComplex,
		chain_complex.DoubleTotalDef,
		chain_complex.DoubleTotalTermsDef,
		comm_ring.AlternatingSignDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "chain_complex(R, total_complex(R, M, N))",
	},
		"Currying tagged coefficients identifies a total term with the finite "+
			"diagonal direct sum. DoubleTotalComplex gives the differential laws; a "+
			"finite union of the finitely supported diagonal slices is finitely supported."),
})}

// TotalCurryIso — Currying has the explicit inverse u ↦ (z ↦ u(fst z)(snd z)). It respects the differentials by definition and gives inverse maps on homology.
var TotalCurryIso = totalCurryIsoThm{family.Add(registry.ProofEntry{
	Name: "TotalCurryIso",
	Key:  "prop_d7f7143c3985a91c",
	Deps: []registry.EntryLike{
		TotalComplex,
		totalComplexOf,
		totalBoundaryDef,
		totalTaggedBasisDef,
		totalCellsDef,
		ResolutionDoubleComplex,
		chain_complex.DoubleTotalComplex,
		chain_complex.DoubleTotalDef,
		chain_complex.DoubleTotalTermsDef,
		chain_complex.ChainMapDef,
		chain_complex.HomologyMapHom,
		chain_complex.HomologyMapCoset,
		chain_complex.HomologyModuleDef,
		module_homomorphism.ModuleIsomorphismDef,
		pairs.Fst,
		pairs.Snd,
		function_module.FiniteSupportDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "chain_map(R, " +
			"    total_complex(R, M, N), " +
			"    double_total(free_module_record(R, " +
			"            𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩), " +
			"        total_cells(R, M, N), " +
			"        total_horizontal(R, M, N), " +
			"        total_vertical(R, M, N), " +
			"        alternating_sign), " +
			"    λn:num. " +
			"    λu:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"    λp:num. " +
			"    λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"        u((p, j))) ∧ " +
			"(∀n:num. " +
			"    module_isomorphism(R, " +
			"        homology_module(total_complex(R, M, N), n), " +
			"        homology_module(double_total(free_module_record(R, " +
			"                    𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩), " +
			"                total_cells(R, M, N), " +
			"                total_horizontal(R, M, N), " +
			"                total_vertical(R, M, N), " +
			"                alternating_sign), " +
			"            n), " +
			"        homology_map(double_total(free_module_record(R, " +
			"                    𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))⟩), " +
			"                total_cells(R, M, N), " +
			"                total_horizontal(R, M, N), " +
			"                total_vertical(R, M, N), " +
			"                alternating_sign), " +
			"            λn:num. " +
			"            λu:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"            λp:num. " +
			"            λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"                u((p, j)), " +
			"            n)))",
	},
		"Currying has the explicit inverse u ↦ (z ↦ u(fst z)(snd z)). It respects "+
			"the differentials by definition and gives inverse maps on homology."),
})}

// totalLeftAugmentationDef — augment the second resolution and retain the first basis index.
var totalLeftAugmentationDef = totalLeftAugmentationDefThm{family.Define(registry.DefEntry{
	Name:  "totalLeftAugmentationDef",
	Const: "total_left_augmentation",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A) → " +
		"set(prod(num, prod(A, B))) → " +
		"C",
	Key: "prop_4e85e021dd690369",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    total_left_augmentation(R, M, N) = " +
			"    free_lift(R.zero, " +
			"        fun_add⟨D:set(prod(num, prod(A, B)))⟩(N.add), " +
			"        fun_zero⟨D:set(prod(num, prod(A, B)))⟩(N.zero), " +
			"        fun_smul⟨D:set(prod(num, prod(A, B)))⟩(N.smul), " +
			"        λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"        λx:set(prod(num, prod(A, B))). " +
			"            COND(x = fst(j), canonical_eps(R, N, delta_at(R.zero, R.one, snd(j))), N.zero))",
	},
})}

// totalLeftEdgeDef — read the q=0 slice and augment the second resolution.
var totalLeftEdgeDef = totalLeftEdgeDefThm{family.Define(registry.DefEntry{
	Name:  "totalLeftEdgeDef",
	Const: "total_left_edge",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A) → " +
		"set(prod(num, prod(A, B))) → " +
		"C",
	Key: "prop_f724c85f461982ba",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀u:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"    total_left_edge(R, M, N, n, u) = " +
			"    total_left_augmentation(R, " +
			"        M, " +
			"        N, " +
			"        λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). u((n, j)))",
	},
	Deps: []registry.EntryLike{totalLeftAugmentationDef},
})}

// totalRightEdgeDef — read the p=0 slice and augment the first resolution.
var totalRightEdgeDef = totalRightEdgeDefThm{family.Define(registry.DefEntry{
	Name:  "totalRightEdgeDef",
	Const: "total_right_edge",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A) → " +
		"set(prod(num, prod(A, C))) → " +
		"B",
	Key: "prop_8882de8fe1321911",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀u:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"    total_right_edge(R, M, N, n, u) = " +
			"    free_lift(R.zero, " +
			"        fun_add⟨D:set(prod(num, prod(A, C)))⟩(M.add), " +
			"        fun_zero⟨D:set(prod(num, prod(A, C)))⟩(M.zero), " +
			"        fun_smul⟨D:set(prod(num, prod(A, C)))⟩(M.smul), " +
			"        (λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). " +
			"        λy:set(prod(num, prod(A, C))). " +
			"            COND(y = snd(j), canonical_eps(R, M, delta_at(R.zero, R.one, fst(j))), M.zero)), " +
			"        (λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). u((0, j))))",
	},
})}

// totalSwapDef — transpose the two basis indices and multiply bidegree (p,q) by (−1)^(pq).
var totalSwapDef = totalSwapDefThm{family.Define(registry.DefEntry{
	Name:  "totalSwapDef",
	Const: "total_swap",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A) → " +
		"prod(num, prod(set(prod(num, prod(A, C))), set(prod(num, prod(A, B))))) → " +
		"A",
	Key: "prop_63be9901aaf31d0b",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀u:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). " +
			"∀w:prod(num, prod(set(prod(num, prod(A, C))), set(prod(num, prod(A, B))))). " +
			"    total_swap(R, M, N, n, u, w) = " +
			"    COND(fst(w) ≤ n, " +
			"        R.mul(alternating_sign(R.one, R.neg, fst(w) * (n - fst(w))), " +
			"            u((n - fst(w), (snd(snd(w)), fst(snd(w)))))), " +
			"        R.zero)",
	},
})}

// TotalSwapChain — The Koszul sign converts the horizontal sign convention to the vertical one. Verify the square on each tagged generator and extend linearly.
var TotalSwapChain = totalSwapChainThm{family.Add(registry.ProofEntry{
	Name: "TotalSwapChain",
	Key:  "prop_65f7de61654dc43a",
	Deps: []registry.EntryLike{
		TotalComplex,
		totalSwapDef,
		totalBoundaryDef,
		totalHorizontalDef,
		totalVerticalDef,
		totalTaggedBasisDef,
		chain_complex.ChainMapDef,
		comm_ring.AlternatingSignDef,
		free_module.FreeModuleExpand,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "chain_map(R, total_complex(R, M, N), total_complex(R, N, M), total_swap(R, M, N))",
	},
		"The Koszul sign converts the horizontal sign convention to the vertical "+
			"one. Verify the square on each tagged generator and extend linearly."),
})}

// TotalSwapInvolution — Transposing twice restores p and q; the two identical signs multiply to one on each coefficient. Outside the diagonal both sides are zero.
var TotalSwapInvolution = totalSwapInvolutionThm{family.Add(registry.ProofEntry{
	Name: "TotalSwapInvolution",
	Key:  "prop_8c5216f2a1d07bb0",
	Deps: []registry.EntryLike{
		totalSwapDef,
		totalTaggedBasisDef,
		function_module.FiniteSuppDef,
		comm_ring.AlternatingSignDef,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀u:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"u ∈ finite_supp(R.zero, R.carrier, total_tagged_basis(R, M, N, n))",
		},
		Conclusion: "total_swap(R, N, M, n, total_swap(R, M, N, n, u)) = u",
	},
		"Transposing twice restores p and q; the two identical signs multiply "+
			"to one on each coefficient. Outside the diagonal both sides are zero."),
})}

// TotalLeftAugmentationOnto — the augmentation of N's resolution, applied
// slice by slice, maps the cells of vertical degree 0 linearly onto the tensor
// complex of M's resolution with N.
var TotalLeftAugmentationOnto = totalLeftAugmentationOntoThm{family.Add(registry.ProofEntry{
	Name: "TotalLeftAugmentationOnto",
	Key:  "prop_729d7efa4b06120b",
	Deps: []registry.EntryLike{
		totalLeftAugmentationDef,
		totalCellsDef,
		totalBasisDef,
		CanonicalTensorComplexDef,
		TensorComplexOf,
		function_module.FiniteSuppDef,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
		free_module.FreeModuleRecordDef,
		free_module.DeltaAtIn,
		resolution.CanonicalEpsHom,
		resolution.CanonicalEpsOnto,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀p:num. " +
			"    module_homomorphism(R, " +
			"        restrict_module(free_module_record(R, 𝕌), total_cells(R, M, N, p, 0)), " +
			"        complex_module(canonical_tensor_complex(R, M, N), p), " +
			"        total_left_augmentation(R, M, N))) ∧ " +
			"(∀p:num. " +
			"    image(total_left_augmentation(R, M, N), total_cells(R, M, N, p, 0)) = " +
			"    canonical_tensor_complex(R, M, N).terms(p))",
	},
		"Slice a cell u as x ↦ (y ↦ u((x, y))). On a generator total_left_augmentation(R, M, N, "+
			"δ_(x,y)) is the function with value canonical_eps(R, N, δ_y) at x and N.zero elsewhere "+
			"(totalLeftAugmentationDef, FreeLiftDelta), so on total_cells(R, M, N, p, 0) it is u ↦ "+
			"(x ↦ canonical_eps(R, N, λy. u((x, y)))), both sides linear (FreeLiftUnique). Read "+
			"total_cells(R, M, N, p, 0) under the cell module's operations as free_module_record(R, "+
			"total_basis(R, M, N, p, 0)) and complex_module(canonical_tensor_complex(R, M, N), p) "+
			"as finite_supp_module(N, canonical_resolution_terms(R, M, p)): FreeLiftHom gives the "+
			"homomorphism, each generator's value lying among the finitely supported functions "+
			"(support {x}, CanonicalEpsHom, DeltaAtIn). Onto: canonical_eps(R, N) maps onto N "+
			"(CanonicalEpsOnto), so a finitely supported g has a preimage chosen slice by slice, "+
			"the zero slice where g(x) = N.zero, which keeps the support finite."),
})}

// TotalLeftColumnsExact — every column of the tensor double complex,
// augmented by the left augmentation, is exact: slice by slice it is the
// augmented canonical resolution of N.
var TotalLeftColumnsExact = totalLeftColumnsExactThm{family.Add(registry.ProofEntry{
	Name: "TotalLeftColumnsExact",
	Key:  "prop_62ef7fc62d920669",
	Deps: []registry.EntryLike{
		totalVerticalDef,
		totalLeftAugmentationDef,
		totalCellsDef,
		totalBasisDef,
		CanonicalTensorComplexDef,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
		module_homomorphism.ExactAtDef,
		resolution.CanonicalResolution,
		resolution.ResolutionAugmentationKernel,
		resolution.ResolutionExact,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "(∀p:num. " +
			"    exact_at(canonical_tensor_complex(R, M, N).zero, " +
			"        total_cells(R, M, N, p, 1), " +
			"        total_cells(R, M, N, p, 0), " +
			"        total_vertical(R, M, N, p, 1), " +
			"        total_left_augmentation(R, M, N))) ∧ " +
			"(∀p q:num. " +
			"    exact_at(free_module_record(R, 𝕌).zero, " +
			"        total_cells(R, M, N, p, q + 2), " +
			"        total_cells(R, M, N, p, q + 1), " +
			"        total_vertical(R, M, N, p, q + 2), " +
			"        total_vertical(R, M, N, p, q + 1)))",
	},
		"Slice a cell u as x ↦ (y ↦ u((x, y))). On generators total_vertical(R, M, N, p, q + 1) "+
			"is canonical_boundary(R, N, q + 1) slice by slice: total_vertical(R, M, N, p, q + 1, "+
			"u)((x, y)) = canonical_boundary(R, N, q + 1, λy'. u((x, y')), y) (totalVerticalDef, "+
			"FreeLiftDelta, FreeLiftUnique), and total_left_augmentation is canonical_eps(R, N) "+
			"slice by slice (totalLeftAugmentationDef). So each column is the augmented canonical "+
			"resolution of N, one copy for each x in canonical_resolution_terms(R, M, p), finitely "+
			"many slices nonzero. It is exact at degree 0 by ResolutionAugmentationKernel and above "+
			"by ResolutionExact at CanonicalResolution; a preimage of a cell in the kernel is "+
			"chosen slice by slice, the zero slice over a zero slice, so its support stays finite."),
})}

// TotalLeftAugmentationSquare — the left augmentation carries the horizontal
// boundary out of vertical degree 0 to the boundary of the tensor complex.
var TotalLeftAugmentationSquare = totalLeftAugmentationSquareThm{family.Add(registry.ProofEntry{
	Name: "TotalLeftAugmentationSquare",
	Key:  "prop_7368572da4adc964",
	Deps: []registry.EntryLike{
		TotalLeftAugmentationOnto,
		totalHorizontalDef,
		totalLeftAugmentationDef,
		TensorBoundaryDef,
		CanonicalTensorComplexDef,
		ResolutionDoubleComplex,
		TensorComplex,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀p:num. " +
			"∀u:(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"u ∈ total_cells(R, M, N, p + 1, 0)",
		},
		Conclusion: "canonical_tensor_complex(R, M, N).d(p + 1)(total_left_augmentation(R, M, N, u)) = " +
			"total_left_augmentation(R, M, N, total_horizontal(R, M, N, p + 1, 0, u))",
	},
		"Both sides are homomorphisms of total_cells(R, M, N, p + 1, 0) into the tensor complex in "+
			"degree p: total_left_augmentation followed by the tensor boundary (TotalLeftAugmentationOnto "+
			"at p + 1, TensorComplex), and total_horizontal(R, M, N, p + 1, 0) into total_cells(R, M, N, "+
			"p, 0) followed by the augmentation (ResolutionDoubleComplex, TotalLeftAugmentationOnto at "+
			"p). By FreeLiftUnique it suffices to compare them on a generator δ_(x, y), x in "+
			"canonical_resolution_terms(R, M, p + 1) and y in canonical_resolution_terms(R, N, 0): both "+
			"sides are the function x' ↦ canonical_boundary(R, M, p + 1, δ_x, x') • canonical_eps(R, N, "+
			"δ_y) (totalHorizontalDef, totalLeftAugmentationDef, TensorBoundaryDef, FreeLiftDelta)."),
})}

// TotalLeftQuasiIsomorphism — the left edge of the tensor double complex of
// the two canonical resolutions induces isomorphisms from the homology of the
// total complex onto Tor. Currying carries the total complex to the double
// total complex quasi-isomorphically; its augmented columns are exact, so the
// augmentation of N's resolution, read on the corner of each diagonal, is a
// quasi-isomorphism onto the tensor complex; the left edge is the composite.
var TotalLeftQuasiIsomorphism = totalLeftQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TotalLeftQuasiIsomorphism",
	Key:  "prop_5b631ea554cdcec9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    homology_module(total_complex(R, M, N), n), " +
			"    tor_module(R, M, N, n), " +
			"    homology_map(canonical_tensor_complex(R, M, N), total_left_edge(R, M, N), n))",
		Abbrev: Abbrev{
			{Name: "cellTotal", Text: "double_total(free_module_record(R, 𝕌), " +
				"    total_cells(R, M, N), " +
				"    total_horizontal(R, M, N), " +
				"    total_vertical(R, M, N), " +
				"    alternating_sign)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			modules Fact,
		) {
			type cell = Fun[Prod[Set[Prod[Nat, Prod[A, B]]], Set[Prod[Nat, Prod[A, C]]]], A]
			type chain = Fun[Set[Prod[Nat, Prod[A, B]]], C]
			double := a.Have(
				"the cells with the two resolution boundaries form a double complex",
				"double_complex(R, "+
					"    free_module_record(R, 𝕌), "+
					"    total_cells(R, M, N), "+
					"    total_horizontal(R, M, N), "+
					"    total_vertical(R, M, N))",
				By(ResolutionDoubleComplex.At(R, M, N), modules))
			moduleOf := a.Conjuncts(
				modules,
				"M is an R-module",
				"N is an R-module")
			resolvesM := a.Simplified(GroupPremises(moduleOf[0], resolution.CanonicalResolution.At(R, M)))
			tensorComplex := a.Have(
				"the canonical resolution of M tensored with N is a chain complex",
				"chain_complex(R, canonical_tensor_complex(R, M, N))",
				Simp(Fwd(CanonicalTensorComplexDef)),
				By(TensorComplex, resolution.ResolutionComplex.Read(resolvesM), moduleOf[1]))
			totalComplex := a.Have(
				"the total complex is a chain complex",
				"chain_complex(R, total_complex(R, M, N))",
				By(TotalComplex.At(R, M, N), modules))
			doubleTotal := a.Have(
				"so is the double total complex of the cells",
				"chain_complex(R, «cellTotal»)",
				By(chain_complex.DoubleTotalComplex.Read(double)))
			onto := a.Conjuncts(
				a.Simplified(GroupPremises(moduleOf[0], moduleOf[1], At(TotalLeftAugmentationOnto, R, M, N))),
				"the augmentation is linear on the bottom row",
				"the augmentation maps the bottom row onto the tensor complex")
			exact := a.Conjuncts(
				a.Simplified(GroupPremises(moduleOf[0], moduleOf[1], At(TotalLeftColumnsExact, R, M, N))),
				"each augmented column is exact at the bottom row",
				"each column is exact above the bottom row")
			square := a.Simplified(
				GroupPremises(moduleOf[0], moduleOf[1], At(TotalLeftAugmentationSquare, R, M, N)))
			edge := a.Have(
				"so the augmentation of N's resolution is a quasi-isomorphism "+
					"of the double total complex onto the tensor complex",
				"quasi_isomorphism(R, "+
					"    «cellTotal», "+
					"    canonical_tensor_complex(R, M, N), "+
					"    double_edge(λp:num. total_left_augmentation(R, M, N)))",
				Simp(Fwd(chain_complex.QuasiIsomorphismDef)),
				By(
					tensorComplex,
					onto[0],
					onto[1],
					exact[0],
					exact[1],
					square,
					chain_complex.AugmentedAssembly.Read(double).At(
						a.TermAs[chain_complex.ComplexOps[A, chain]]("canonical_tensor_complex(R, M, N)"),
						a.TermAs[Fun2[Nat, cell, chain]]("λp:num. total_left_augmentation(R, M, N)"))))
			corner := a.Unfolded(edge, chain_complex.DoubleEdgeDef)
			curry := a.Have(
				"currying is a quasi-isomorphism from the total complex onto the double total complex",
				"quasi_isomorphism(R, "+
					"    total_complex(R, M, N), "+
					"    «cellTotal», "+
					"    λn:num. "+
					"    λu:(prod(num, prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C))))) → A). "+
					"    λp:num. "+
					"    λj:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))). "+
					"        u((p, j)))",
				By(chain_complex.QuasiIsomorphismDef, TotalCurryIso.At(R, M, N), modules))
			leftEdge := a.Have(
				"the left edge is the augmentation of the corner after currying, so it is a quasi-isomorphism",
				"quasi_isomorphism(R, "+
					"    total_complex(R, M, N), "+
					"    canonical_tensor_complex(R, M, N), "+
					"    total_left_edge(R, M, N))",
				Unfold(totalLeftEdgeDef),
				By(
					Where(
						chain_complex.QuasiIsomorphismCompose,
						"g",
						a.TermAs[Fun2[Nat, Fun[Nat, cell], chain]](
							"λn:num. λu:(num → prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, C)))) → A). "+
								"    total_left_augmentation(R, M, N, u(n))")),
					totalComplex,
					doubleTotal,
					tensorComplex,
					curry,
					corner))
			a.Show(
				"Tor is the homology of the tensor complex, so the left edge induces the isomorphisms onto it",
				Unfold(TorModuleDef),
				By(leftEdge, chain_complex.QuasiIsomorphismDef))
		}),
})}

// TotalRightEdgeChain — The augmentation kills the boundary into degree zero. The surviving edge differential is the other resolution differential, so the augmentation commutes with the total differential.
var TotalRightEdgeChain = totalRightEdgeChainThm{family.Add(registry.ProofEntry{
	Name: "TotalRightEdgeChain",
	Key:  "prop_1d43a61595e2981c",
	Deps: []registry.EntryLike{
		TotalComplex,
		totalRightEdgeDef,
		totalBoundaryDef,
		totalHorizontalDef,
		totalVerticalDef,
		resolution.CanonicalResolution,
		resolution.CanonicalEpsHom,
		resolution.CanonicalImageIsKernel,
		resolution.CanonicalKernelDef,
		chain_complex.ChainMapDef,
		TensorComplex,
		CanonicalTensorComplexDef,
		free_module.FreeLiftUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "chain_map(R, " +
			"    total_complex(R, M, N), " +
			"    canonical_tensor_complex(R, N, M), " +
			"    total_right_edge(R, M, N))",
	},
		"The augmentation kills the boundary into degree zero. The surviving edge differential is "+
			"the other resolution differential, so the augmentation commutes with the total differential."),
})}

// TotalRightQuasiIsomorphism — For the left edge, each augmented column is a free module tensored with the augmented resolution of N, hence exact by FreeTensorExact; apply AugmentedAssembly and the currying isomorphism. For the right edge, transpose the double complex and apply the left-edge result, using the involution to obtain an isomorphism.
var TotalRightQuasiIsomorphism = totalRightQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TotalRightQuasiIsomorphism",
	Key:  "prop_89b25a707e4b67bf",
	Deps: []registry.EntryLike{
		TotalRightEdgeChain,
		totalRightEdgeDef,
		TorModuleDef,
		TotalLeftQuasiIsomorphism,
		TotalSwapChain,
		TotalSwapInvolution,
		totalSwapDef,
		totalLeftEdgeDef,
		chain_complex.HomologyMapHom,
		chain_complex.HomologyMapCoset,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    homology_module(total_complex(R, M, N), n), " +
			"    tor_module(R, N, M, n), " +
			"    homology_map(canonical_tensor_complex(R, N, M), total_right_edge(R, M, N), n))",
	},
		"Apply TotalLeftQuasiIsomorphism to (N,M). Signed transposition "+
			"commutes with both edge maps, whose surviving bidegrees have sign one; "+
			"TotalSwapChain and TotalSwapInvolution give the required isomorphism."),
})}

// torBalanceDef — apply the carrier inverse of the left homology edge and project through the right.
var torBalanceDef = torBalanceDefThm{family.Define(registry.DefEntry{
	Name:  "torBalanceDef",
	Const: "tor_balance",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → C) → " +
		"set(set(prod(num, prod(A, C))) → B)",
	Key: "prop_645ed9a13de4304a",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → C). " +
			"    tor_balance(R, M, N, n, s) = " +
			"    homology_map(canonical_tensor_complex(R, N, M), " +
			"        total_right_edge(R, M, N), " +
			"        n, " +
			"        inverse_on(homology(total_complex(R, M, N), n), " +
			"            homology_map(canonical_tensor_complex(R, M, N), total_left_edge(R, M, N), n), " +
			"            s))",
	},
	Deps: []registry.EntryLike{
		totalLeftEdgeDef,
		totalRightEdgeDef,
		totalComplexOf,
		CanonicalTensorComplexDef,
	},
})}

// TorBalanceMapIso — compose the inverse isomorphism of the left edge with the right edge.
var TorBalanceMapIso = torBalanceMapIsoThm{family.Add(registry.ProofEntry{
	Name: "TorBalanceMapIso",
	Key:  "prop_2c942d76eb737241",
	Deps: []registry.EntryLike{
		torBalanceDef,
		TotalLeftQuasiIsomorphism,
		TotalRightQuasiIsomorphism,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
		functions.InjectiveOnCompose,
		set_image.ImageCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    tor_module(R, M, N, n), " +
			"    tor_module(R, N, M, n), " +
			"    tor_balance(R, M, N, n))",
	},
		"TotalLeftQuasiIsomorphism makes the left homology edge an isomorphism. Its carrier "+
			"inverse inverse_on(homology(total_complex(R, M, N), n), left_edge) is an isomorphism "+
			"in the reverse direction (IsomorphismInverse). Compose it with the right edge "+
			"(TotalRightQuasiIsomorphism): HomCompose gives linearity, InjectiveOnCompose "+
			"injectivity, and ImageCompose the target image; torBalanceDef is this composite."),
})}

// TorBalance — The named balance isomorphism witnesses the symmetry of Tor, even though the two canonical index types differ.
var TorBalance = torBalanceThm{family.Add(registry.ProofEntry{
	Name: "TorBalance",
	Key:  "prop_c6324b5dd89165f4",
	Deps: []registry.EntryLike{TorBalanceMapIso, module_homomorphism.ModuleIsomorphicDef},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphic(R, tor_module(R, M, N, n), tor_module(R, N, M, n))",
	},
		"The named balance isomorphism witnesses the symmetry of "+
			"Tor, even though the two canonical index types differ."),
})}

// TorBalanceInvolution — The signed transposition exchanges the two edges and squares to the identity, so balance in the opposite direction is its inverse.
var TorBalanceInvolution = torBalanceInvolutionThm{family.Add(registry.ProofEntry{
	Name: "TorBalanceInvolution",
	Key:  "prop_847b1a12cc4798f7",
	Deps: []registry.EntryLike{
		torBalanceDef,
		TorBalanceMapIso,
		TotalLeftQuasiIsomorphism,
		module_homomorphism.ModuleIsomorphismDef,
		TotalSwapInvolution,
		TotalSwapChain,
		totalLeftEdgeDef,
		totalRightEdgeDef,
		totalSwapDef,
		chain_complex.HomologyMapCoset,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InverseOnIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_balance(R, N, M, n, tor_balance(R, M, N, n, s)) = s",
	},
		"The signed transposition exchanges the two edges and squares to the "+
			"identity. Expand torBalanceDef in both directions; InverseOnIn keeps "+
			"each chosen class in total homology and InverseOnLeft and InverseOnRight "+
			"cancel the edge maps there, leaving the transposition applied twice."),
})}

// TorBalanceNaturalLeft — the canonical lift gives commuting edge squares; their left-edge inverses commute on homology carriers.
var TorBalanceNaturalLeft = torBalanceNaturalLeftThm{family.Add(registry.ProofEntry{
	Name: "TorBalanceNaturalLeft",
	Key:  "prop_2b06653af2739e8e",
	Deps: []registry.EntryLike{
		torBalanceDef,
		TorBalanceMapIso,
		TotalLeftQuasiIsomorphism,
		module_homomorphism.ModuleIsomorphismDef,
		TorMapLeftDef,
		TorMapDef,
		totalLeftEdgeDef,
		totalRightEdgeDef,
		totalHorizontalDef,
		totalVerticalDef,
		resolution.CanonicalMapChain,
		resolution.CanonicalMapAugmentation,
		TensorChainMap,
		chain_complex.HomologyMapHom,
		chain_complex.HomologyMapCoset,
		free_module.FreeLiftUnique,
		functions.InverseOnIn,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_balance(R, L, N, n, tor_map_left(R, M, L, f, N, n, s)) = " +
			"tor_map(R, N, L, f, n, tor_balance(R, M, N, n, s))",
	},
		"Keep the degree tag p and extend δ_(p,x,y) ↦ Σ_x' canonical_map(R,M,L,f,p)(δ_x)(x') · "+
			"δ_(p,x',y) linearly. CanonicalMapChain gives the differential squares; "+
			"CanonicalMapAugmentation gives the right edge square and the left edge square is tensoring "+
			"that chain map. Pass both squares to homology. The total map preserves its carrier "+
			"(HomologyMapHom); InverseOnIn and InverseOnRight identify the two candidate lifts after "+
			"the target's left edge, whose injectivity (TotalLeftQuasiIsomorphism, "+
			"ModuleIsomorphismDef) makes the lifts equal. Apply the right-edge square and torBalanceDef."),
})}

// torConnectingLeftDef — transport the second-variable connecting map through the natural balance isomorphisms.
var torConnectingLeftDef = torConnectingLeftDefThm{family.Define(registry.DefEntry{
	Name:  "torConnectingLeftDef",
	Const: "tor_connecting_left",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"module_ops(A, D) → " +
		"module_ops(A, E) → " +
		"(C → D) → " +
		"(D → E) → " +
		"num → " +
		"set(set(prod(num, prod(A, E))) → B) → " +
		"set(set(prod(num, prod(A, C))) → B)",
	Key: "prop_c4c68054ccfa98be",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀N'':module_ops(A, E). " +
			"∀i:(C → D). " +
			"∀p:(D → E). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, E))) → B). " +
			"    tor_connecting_left(R, M, N', N, N'', i, p, n, s) = " +
			"    tor_balance(R, " +
			"        M, " +
			"        N', " +
			"        n, " +
			"        tor_connecting(R, M, N', N, i, p, n, tor_balance(R, N'', M, n + 1, s)))",
	},
	Deps: []registry.EntryLike{torBalanceDef, TorConnectingDef},
})}

// TorLongExactLeftMiddle — Transport the second-variable long exact sequence through balance. Naturality identifies the transported arrows with the named first-variable maps; the transported connecting arrow is torConnectingLeftDef.
var TorLongExactLeftMiddle = torLongExactLeftMiddleThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactLeftMiddle",
	Key:  "prop_d46bf1b68b1c35bf",
	Deps: []registry.EntryLike{
		TorLongExactMiddle,
		TorBalanceMapIso,
		TorBalanceInvolution,
		TorBalanceNaturalLeft,
		torConnectingLeftDef,
		TorMapLeftDef,
		TorZeroDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, N'', M, n), " +
			"    tor(R, N', M, n), " +
			"    tor(R, N, M, n), " +
			"    tor_map_left(R, N', N, i, M, n), " +
			"    tor_map_left(R, N, N'', p, M, n))",
	}),
		"Transport the second-variable long exact sequence through balance. "+
			"Naturality identifies the transported arrows with the named first-variable "+
			"maps; the transported connecting arrow is torConnectingLeftDef."),
})}

// TorLongExactLeftQuotient — Transport the second-variable long exact sequence through balance. Naturality identifies the transported arrows with the named first-variable maps; the transported connecting arrow is torConnectingLeftDef.
var TorLongExactLeftQuotient = torLongExactLeftQuotientThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactLeftQuotient",
	Key:  "prop_14dfeda77a788489",
	Deps: []registry.EntryLike{
		TorLongExactQuotient,
		TorBalanceMapIso,
		TorBalanceInvolution,
		TorBalanceNaturalLeft,
		torConnectingLeftDef,
		TorMapLeftDef,
		TorZeroDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, N', M, n), " +
			"    tor(R, N, M, n + 1), " +
			"    tor(R, N'', M, n + 1), " +
			"    tor_map_left(R, N, N'', p, M, n + 1), " +
			"    tor_connecting_left(R, M, N', N, N'', i, p, n))",
	}),
		"Transport the second-variable long exact sequence through balance. "+
			"Naturality identifies the transported arrows with the named first-variable "+
			"maps; the transported connecting arrow is torConnectingLeftDef."),
})}

// TorLongExactLeftSub — Transport the second-variable long exact sequence through balance. Naturality identifies the transported arrows with the named first-variable maps; the transported connecting arrow is torConnectingLeftDef.
var TorLongExactLeftSub = torLongExactLeftSubThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactLeftSub",
	Key:  "prop_8cfece67bcb89480",
	Deps: []registry.EntryLike{
		TorLongExactSub,
		TorBalanceMapIso,
		TorBalanceInvolution,
		TorBalanceNaturalLeft,
		torConnectingLeftDef,
		TorMapLeftDef,
		TorZeroDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, N, M, n), " +
			"    tor(R, N'', M, n + 1), " +
			"    tor(R, N', M, n), " +
			"    tor_connecting_left(R, M, N', N, N'', i, p, n), " +
			"    tor_map_left(R, N', N, i, M, n))",
	}),
		"Transport the second-variable long exact sequence through balance. "+
			"Naturality identifies the transported arrows with the named first-variable "+
			"maps; the transported connecting arrow is torConnectingLeftDef."),
})}

// TorLongExactLeftEnd — Transport the second-variable long exact sequence through balance. Naturality identifies the transported arrows with the named first-variable maps; the transported connecting arrow is torConnectingLeftDef.
var TorLongExactLeftEnd = torLongExactLeftEndThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactLeftEnd",
	Key:  "prop_e1e5e33738db9880",
	Deps: []registry.EntryLike{
		TorLongExactEnd,
		TorBalanceMapIso,
		TorBalanceInvolution,
		TorBalanceNaturalLeft,
		torConnectingLeftDef,
		TorMapLeftDef,
		TorZeroDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "image(tor_map_left(R, N, N'', p, M, 0), tor(R, N, M, 0)) = tor(R, N'', M, 0)",
	}),
		"Transport the second-variable long exact sequence through balance. "+
			"Naturality identifies the transported arrows with the named first-variable "+
			"maps; the transported connecting arrow is torConnectingLeftDef."),
})}
