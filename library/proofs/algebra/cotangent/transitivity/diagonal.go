// diagonal.go — the bisimplicial modules behind the triangle's double
// complexes, and the diagonal of the middle one. The middle term, with
// the Jacobians of Q's horizontal maps and of its vertical faces and
// degeneracies, is a bisimplicial module over T whose alternating face
// sums are the middle boundaries; the left term is one under the same
// maps, its vertical faces the identity; the double complex with
// constant rows is one with identity horizontal faces; and the
// comparison from the constant rows into the middle term is a map of
// bisimplicial modules. On the diagonal of the middle module the faces
// are the Jacobians of the faces of the diagonal of Q, so its face
// complex is, on its terms, the differential complex of that diagonal
// resolution, and the comparison read on the diagonal is the Jacobian of
// the map from the standard resolution of T over R into it. Through the
// Alexander–Whitney map these carry a homotopy found on the diagonal back
// to the middle total.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// The faces of the middle bisimplicial module. The horizontal face i out
// of column p on row q is the Jacobian of the map of row q induced by
// P's face i, read through the augmentation of column p − 1; the
// vertical faces of column p are those of its differential simplicial
// module.
const (
	middleHorizontalFaces = "λp:num. λq:num. λi:num. differential_map(R, " +
		"triangle_column_names(R, S, T, p), triangle_column_names(R, S, T, p - 1), " +
		"relative_vertical_face(R, S, f, T, g, p - 1), relative_vertical_eps(R, S, f, T, g, " +
		"p - 1), λm:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), m), N, q)"
	middleVerticalFaces = "λp:num. differential_face(R, triangle_column_names(R, S, T, p), " +
		"relative_vertical_face(R, S, f, T, g, p), relative_vertical_eps(R, S, f, T, g, p), N)"
)

// TriangleMiddleBisimplicial — in a universe for the tower, the middle
// term with the Jacobians of Q's horizontal maps, faces and degeneracies
// is a bisimplicial module over T.
var TriangleMiddleBisimplicial = triangleMiddleBisimplicialThm{family.Add(registry.ProofEntry{
	Name: "TriangleMiddleBisimplicial",
	Key:  "prop_a026dbbdc7d6e522",
	Reading: "Its alternating face sums are the middle boundaries: the horizontal sum out " +
		"of column p on row q is triangle_horizontal at (p, q) up to β, and the vertical sum " +
		"is triangle_vertical once differential_boundary is unfolded. Column p is the " +
		"differential simplicial module of the resolution Q(p, •); each horizontal map is the " +
		"Jacobian of a map of such columns covering the identity of T. Each identity is Q's " +
		"identity after JacobianCompose, at one of four augmentation compatibilities: ε^(p+1) " +
		"= ε^(p) ∘ d^h_i, ε^(p) = ε^(p+1) ∘ s^h_i, ε_{q+1} = ε_q ∘ d^v_j, ε_q = ε_{q+1} ∘ s^v_j.",
	Deps: []registry.EntryLike{
		simplicial_module.BisimplicialModule,
		simplicial_module.SimplicialModule,
		simplicial_homotopy.BisimplicialSet,
		triangleMiddleDef,
		TriangleColumnNamesDef,
		cotangent_complex.DifferentialSimplicialModule,
		cotangent_complex.DifferentialMapDef,
		cotangent_complex.DifferentialFaceDef,
		cotangent_complex.DifferentialDegeneracyDef,
		standard_resolution.RelativeColumnAugmented,
		standard_resolution.RelativeHorizontalHom,
		standard_resolution.RelativeHorizontalSimplicial,
		standard_resolution.RelativeDirectionsCommute,
		standard_resolution.RelativeAugmentationC,
		standard_resolution.RelativeBisimplicialSet,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		partial_derivative.JacobianHom,
		function_module.FiniteSuppModuleOn,
		simplicial_ring.AugmentationAtFaceIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "bisimplicial_module(T, " +
			"    finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"    mk_bisimplicial(triangle_middle(R, S, T, N), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p - 1), " +
			"                relative_vertical_face(R, S, f, T, g, p - 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p - 1), " +
			"                λm:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p + 1), " +
			"                relative_vertical_face(R, S, f, T, g, p + 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p + 1), " +
			"                λm:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N), " +
			"        λp:num. " +
			"            differential_degeneracy(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_degeneracy(R), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N)))",
	},
		"column p is the differential simplicial module of Q(p, •) (DifferentialSimplicialModule "+
			"at RelativeColumnAugmented), its terms the middle terms (triangleMiddleDef). Row q: "+
			"each horizontal map is the Jacobian of an algebra map between the algebras of adjacent "+
			"columns (RelativeHorizontalHom), linear (JacobianHom), read through the target column's "+
			"augmentation, which after the map is the source column's (RelativeAugmentationC); so "+
			"the Jacobian of a composite is the composite of the Jacobians (JacobianCompose, "+
			"JacobianCongruence), and each simplicial identity of the row is that of Q's row "+
			"(RelativeHorizontalSimplicial). The four commutations of the two directions are Q's "+
			"(RelativeDirectionsCommute) through the same chain rule, the inner augmentations "+
			"agreeing by RelativeAugmentationC and AugmentationAtFaceIndependent; every term is a "+
			"submodule of finite_supp_module(N, 𝕌) (FiniteSuppModuleOn)"),
})}

// TriangleLeftBisimplicial — in a universe for the tower, the left term
// is a bisimplicial module over T under the maps of the middle one.
var TriangleLeftBisimplicial = triangleLeftBisimplicialThm{family.Add(registry.ProofEntry{
	Name: "TriangleLeftBisimplicial",
	Key:  "prop_986b5b7384e15bfa",
	Reading: "The maps are the middle module's, read on the functions on P's names: every " +
		"vertical face and degeneracy is the identity there (LeftColumnsConstant), so the columns " +
		"are constant simplicial modules, and the horizontal maps keep the left term, P's variables " +
		"going into the algebra on P's names. Its alternating face sums are the left boundaries, " +
		"which are the middle ones. The vertical Jacobians are the identity on the left term only " +
		"because the augmentation sends one to T.one and N is unital; the horizontal ones keep it " +
		"because a polynomial in the first-tag names has no derivative at a second-tag name.",
	Deps: []registry.EntryLike{
		simplicial_module.BisimplicialModule,
		TriangleMiddleBisimplicial,
		LeftColumnsConstant,
		TriangleLeftDouble,
		triangleLeftDef,
		standard_resolution.RelativeBaseInclusionNatural,
		standard_resolution.RelativeGeneratorsClosed,
		standard_resolution.RelativeVerticalFixesBase,
		partial_derivative.JacobianBlockTriangular,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		partial_derivative.PartialSupportFinite,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.AugmentationAtHom,
		submodule.SubmoduleModuleOn,
		function_module.FiniteSuppModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "bisimplicial_module(T, " +
			"    finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"    mk_bisimplicial(triangle_left(R, S, N), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p - 1), " +
			"                relative_vertical_face(R, S, f, T, g, p - 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p - 1), " +
			"                λm:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p + 1), " +
			"                relative_vertical_face(R, S, f, T, g, p + 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p + 1), " +
			"                λm:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N), " +
			"        λp:num. " +
			"            differential_degeneracy(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_degeneracy(R), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N)))",
	},
		"each left term is a submodule of finite_supp_module(N, 𝕌) (FiniteSuppModuleOn). The "+
			"vertical faces fix P's variables (LeftColumnsConstant), and so do the vertical degeneracies "+
			"(RelativeGeneratorsClosed, RelativeVerticalFixesBase), whose Jacobians are then the "+
			"identity on the left term (PartialVar, JacobianDelta, the augmentation sending one to "+
			"T.one, AugmentationAtHom). A horizontal face or degeneracy carries P's variable under the "+
			"first tag into the algebra on P's names under the first tag (RelativeBaseInclusionNatural), "+
			"whose derivatives in the second-tag names vanish (PartialSupportFinite, TagsDisjoint), so "+
			"its Jacobian keeps the left term (JacobianBlockTriangular). Every identity and linearity is "+
			"then the middle module's (TriangleMiddleBisimplicial) restricted"),
})}

// ConstantCotangentBisimplicial — in a universe for R and T, the double
// complex with constant rows, identity faces and degeneracies
// horizontally and the differential simplicial module of the standard
// resolution of T over R vertically, is a bisimplicial module over T.
var ConstantCotangentBisimplicial = constantCotangentBisimplicialThm{family.Add(registry.ProofEntry{
	Name: "ConstantCotangentBisimplicial",
	Key:  "prop_7df83afab1efe65a",
	Reading: "Its alternating face sums are the double complex with constant rows: " +
		"the horizontal sum is constant_cotangent_horizontal, and the vertical sum is " +
		"the cotangent complex's boundary up to β. Its diagonal has the faces dh_i ∘ " +
		"dv_i = dv_i, so its face complex is the cotangent complex of T over R itself.",
	Deps: []registry.EntryLike{
		simplicial_module.BisimplicialModule,
		simplicial_module.ConstantSimplicialModule,
		simplicial_homotopy.BisimplicialSet,
		constantCotangentDef,
		cotangent_complex.DifferentialSimplicialModule,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		simplicial_ring.AugmentedAlongRingMap,
		standard_resolution.StandardPolynomialAlgebra,
		function_module.FiniteSuppModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, T, φ)",
			"module_on(T, N)",
		},
		Conclusion: "bisimplicial_module(T, " +
			"    finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"    mk_bisimplicial(constant_cotangent(R, T, φ, N), " +
			"        λp:num. λq:num. λi:num. λv:(U → D). v, " +
			"        λp:num. λq:num. λi:num. λv:(U → D). v, " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, φ), " +
			"                λu:U. standard_eps(R, T, φ, u), " +
			"                N), " +
			"        λp:num. " +
			"            differential_degeneracy(R, " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, φ), " +
			"                standard_degeneracy(R), " +
			"                λu:U. standard_eps(R, T, φ, u), " +
			"                N)))",
	},
		"the terms of column p are those of the cotangent complex (constantCotangentDef, "+
			"CotangentComplexDef, DifferentialComplexDef), the differential simplicial module of the "+
			"standard resolution of T over R (DifferentialSimplicialModule at StandardPolynomialAlgebra); "+
			"each row is constant with identity maps (ConstantSimplicialModule, FiniteSuppModuleOn); the "+
			"identity commutes with every vertical map, which does not depend on the column"),
})}

// MiddleComparisonBisimplicialMap — in a universe for the tower, the
// comparison from the bisimplicial module with constant rows to the
// middle one is a map of bisimplicial sets.
var MiddleComparisonBisimplicialMap = middleComparisonBisimplicialMapThm{family.Add(registry.ProofEntry{
	Name: "MiddleComparisonBisimplicialMap",
	Key:  "prop_d6c51611a1a2657e",
	Reading: "MiddleComparisonDoubleMap says the same of the boundaries; this is the " +
		"statement face by face, which the naturality of the Alexander–Whitney map reads. " +
		"Its linearity in every bidegree is MiddleComparisonDoubleMap's first conjunct. The " +
		"vertical half reads that the column-p augmentation after relative_from_absolute is " +
		"the augmentation of the standard resolution of T over R in every vertical degree; " +
		"the horizontal half is RelativeFromAbsoluteNatural with RelativeAugmentationC.",
	Deps: []registry.EntryLike{
		simplicial_homotopy.BisimplicialMap,
		ConstantCotangentBisimplicial,
		TriangleMiddleBisimplicial,
		triangleMiddleComparisonDef,
		standard_resolution.RelativeFromAbsoluteMap,
		standard_resolution.RelativeFromAbsoluteNatural,
		standard_resolution.RelativeAugmentationC,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		partial_derivative.JacobianHom,
		cotangent_complex.DifferentialMapDef,
		simplicial_ring.AugmentationAtFaceIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "bisimplicial_map(mk_bisimplicial(constant_cotangent(R, T, λa:A. g(f(a)), N), " +
			"        λp:num. λq:num. λi:num. λv:(U → D). v, " +
			"        λp:num. λq:num. λi:num. λv:(U → D). v, " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, λa:A. g(f(a))), " +
			"                λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"                N), " +
			"        λp:num. " +
			"            differential_degeneracy(R, " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, λa:A. g(f(a))), " +
			"                standard_degeneracy(R), " +
			"                λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"                N)), " +
			"    mk_bisimplicial(triangle_middle(R, S, T, N), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p - 1), " +
			"                relative_vertical_face(R, S, f, T, g, p - 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p - 1), " +
			"                λm:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p + 1), " +
			"                relative_vertical_face(R, S, f, T, g, p + 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p + 1), " +
			"                λm:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N), " +
			"        λp:num. " +
			"            differential_degeneracy(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_degeneracy(R), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N)), " +
			"    triangle_middle_comparison(R, S, f, T, g, N))",
	},
		"both are bisimplicial sets (ConstantCotangentBisimplicial at φ = g ∘ f, "+
			"TriangleMiddleBisimplicial). Each comparison is the Jacobian of relative_from_absolute, "+
			"carrying the functions on the names of degree q into those on the names of (p, q) "+
			"(JacobianHom). Vertically, relative_from_absolute is a simplicial algebra map into "+
			"column p (RelativeFromAbsoluteMap), so the Jacobian of either composite is the Jacobian "+
			"of one map, read through augmentations that agree (JacobianCompose, JacobianCongruence, "+
			"AugmentationAtFaceIndependent). Horizontally, every horizontal map of Q fixes its values "+
			"(RelativeFromAbsoluteNatural), so the Jacobian of a horizontal map after the comparison "+
			"into column p + 1 is the comparison into column p, the augmentations agreeing after the "+
			"map (RelativeAugmentationC), and the constant rows' horizontal maps are identities"),
})}

// MiddleDiagonalDifferential — in a universe for the tower, on the
// diagonal of the middle bisimplicial module each face is the face of the
// differential simplicial module of the diagonal resolution, and the
// comparison read on the diagonal is the Jacobian of relative_from_absolute
// into that resolution.
var MiddleDiagonalDifferential = middleDiagonalDifferentialThm{family.Add(registry.ProofEntry{
	Name: "MiddleDiagonalDifferential",
	Key:  "prop_8f89d86cf6149fbf",
	Reading: "The whole content, beside the chain rule, is that the diagonal resolution's " +
		"augmentation read in degree n is column n's in vertical degree n: augmentation_at(Δ, " +
		"n) = augmentation_at(column n, n) on Q(n, n), by induction along d^Δ_0 = d^h_0 d^v_0 " +
		"with RelativeAugmentationC, which at (n, n) is also JacobianCompose's side " +
		"condition. So on its terms the face complex of the diagonal of the middle module is " +
		"the differential complex of the diagonal of Q, the terms differential_terms of the " +
		"diagonal names being the diagonal middle terms; the two complexes differ as records " +
		"only off the terms, which no cycle, boundary or chain map reads.",
	Deps: []registry.EntryLike{
		TriangleMiddleBisimplicial,
		triangleMiddleDef,
		TriangleColumnNamesDef,
		triangleMiddleComparisonDef,
		constantCotangentDef,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		cotangent_complex.DifferentialFaceDef,
		cotangent_complex.DifferentialMapDef,
		simplicial_ring.AugmentationAtDef,
		standard_resolution.RelativeAugmentationC,
		standard_resolution.RelativeDiagonalResolution,
		standard_resolution.RelativeVerticalHom,
		standard_resolution.RelativeHorizontalHom,
		standard_resolution.RelativeDiagonalFromAbsolute,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "(∀n i:num. ∀u:(U → D). " +
			"    i ≤ n + 1 ∧ u ∈ triangle_middle(R, S, T, N, n + 1, n + 1) ⇒ " +
			"    bisimplicial_diagonal_face(λp:num. λq:num. λi:num. " +
			"            differential_map(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                triangle_column_names(R, S, T, p - 1), " +
			"                relative_vertical_face(R, S, f, T, g, p - 1), " +
			"                relative_vertical_eps(R, S, f, T, g, p - 1), " +
			"                λm:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), m), " +
			"                N, " +
			"                q), " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                triangle_column_names(R, S, T, p), " +
			"                relative_vertical_face(R, S, f, T, g, p), " +
			"                relative_vertical_eps(R, S, f, T, g, p), " +
			"                N), " +
			"        n + 1, " +
			"        i, " +
			"        u) = " +
			"    differential_face(R, " +
			"        λm:num. " +
			"            image(universe_tag(0), standard_names(R, S, m)) ∪ " +
			"            image(universe_tag(1), relative_names(R, S, T, m, m)), " +
			"        bisimplicial_diagonal_face(λp:num. λq:num. λi:num. " +
			"                relative_horizontal_map(R, standard_face(R, S, f, p, i), q), " +
			"            relative_vertical_face(R, S, f, T, g)), " +
			"        relative_vertical_eps(R, S, f, T, g, 0), " +
			"        N, " +
			"        n + 1, " +
			"        i, " +
			"        u)) ∧ " +
			"(∀n:num. ∀u:(U → D). " +
			"    u ∈ constant_cotangent(R, T, λa:A. g(f(a)), N, n, n) ⇒ " +
			"    differential_map(R, " +
			"        standard_names(R, T), " +
			"        λm:num. " +
			"            image(universe_tag(0), standard_names(R, S, m)) ∪ " +
			"            image(universe_tag(1), relative_names(R, S, T, m, m)), " +
			"        bisimplicial_diagonal_face(λp:num. λq:num. λi:num. " +
			"                relative_horizontal_map(R, standard_face(R, S, f, p, i), q), " +
			"            relative_vertical_face(R, S, f, T, g)), " +
			"        relative_vertical_eps(R, S, f, T, g, 0), " +
			"        relative_from_absolute(R), " +
			"        N, " +
			"        n, " +
			"        u) = " +
			"    triangle_middle_comparison(R, S, f, T, g, N, n, n, u))",
	},
		"by induction on n, the diagonal's augmentation in degree n is column n's in vertical "+
			"degree n on the (n, n)-simplices: its 0-th face is the vertical face 0 followed by the map "+
			"of P's face 0, and column n + 1's augmentation in vertical degree n is column n's after "+
			"that map (AugmentationAtDef, RelativeAugmentationC). The diagonal face i of the middle "+
			"module is the Jacobian of the map of P's face i after the Jacobian of the vertical face i, "+
			"the inner one read through column n + 1's augmentation in vertical degree n, which is the "+
			"outer one's after the map (RelativeAugmentationC); by the chain rule it is the Jacobian of "+
			"the composite, the diagonal face of Q (BisimplicialDiagonalFaceDef, JacobianCompose at "+
			"RelativeVerticalHom and RelativeHorizontalHom), read through column n's augmentation, the "+
			"diagonal's (JacobianCongruence, DifferentialFaceDef). The second conjunct is the Jacobian "+
			"of relative_from_absolute(R, n) read through two augmentations of the (n, n)-simplices "+
			"that agree (DifferentialMapDef, triangleMiddleComparisonDef, JacobianCongruence)"),
})}
