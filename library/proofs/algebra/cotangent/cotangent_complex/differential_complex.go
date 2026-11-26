// differential_complex.go — the module of differentials of a polynomial
// simplicial algebra with coefficients in a module, as a simplicial
// module and as a chain complex. For an augmented polynomial simplicial
// algebra over R on the name sets X(n), with augmentation ε into the
// ring S and a module N over S, the differentials of the free algebra on
// X(n) with coefficients in N are the finitely supported functions on
// X(n) with values in N; a face or a degeneracy acts on them by its
// Jacobian, the partial derivatives carried into S by the augmentation
// read in the target degree, and the alternating sum of the faces is the
// boundary. The faces and degeneracies so made are linear and a
// simplicial module, so the differentials are a chain complex; an
// algebra map covering the identity of S acts by its Jacobian in every
// degree as a chain map, functorially, and an algebra homotopy as a
// chain homotopy, so a map of resolutions of S over its identity is a
// chain homotopy equivalence, whatever ring the coefficients are carried
// to.

package cotangent_complex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/resolution_comparison"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"

	// free_module mints the pointwise operations the complexes are built
	// with; the import initializes those mints before the definitions
	// here are parsed.
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
)

// hostEmbedding spells the embedding every free algebra over R in the
// universe is read through.
const hostEmbedding = "universe_embedding(R)"

// jacobian spells the Jacobian over R in the universe of the map Φ from
// the free algebra on the names S to the free algebra on the names T,
// its entries carried by ε into the scalars of N.
func jacobian(S, T, Φ, ε string) string {
	return "free_algebra_jacobian(" + hostEmbedding + ", " + hostEmbedding + ", R, R, " + S + ", " + T + ", " + Φ + ", " + ε + ", N)"
}

// ---------------------------------------------------------------------------
// The terms, the faces and the degeneracies
// ---------------------------------------------------------------------------

// DifferentialTermsDef — `differential_terms(X, N, n)`: the differentials
// of the free algebra on the names X(n) with coefficients in N, the
// finitely supported functions on X(n) with values in N's carrier.
var DifferentialTermsDef = differentialTermsDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialTermsDef",
	Key:   "prop_1343fc6b427e717a",
	Const: "differential_terms",
	Type:  "(num → set(U)) → module_ops(B, D) → num → set(U → D)",
	Equations: []string{
		"∀X:(num → set(U)). ∀N:module_ops(B, D). ∀n:num. " +
			"    differential_terms(X, N, n) = finite_supp(N.zero, N.carrier, X(n))",
	},
	Reading: "A function u stands for Σ_x dx ⊗ u(x), the names x of X(n) a basis of the " +
		"differentials of the free algebra on X(n) over any ring; the terms read neither the base ring " +
		"nor the augmentation. On an empty name set the term is the zero function alone. Over the zero " +
		"ring the free algebras are one point while X(n) may hold many names, but a module over a ring " +
		"receiving a ring map from the zero ring is zero, so the term is again the zero function alone.",
})}

// DifferentialFaceDef — `differential_face(R, X, d, ε, N, n, i)`: the
// face i out of degree n acting on the differentials, the Jacobian of
// d(n, i) from the free algebra on X(n) to the free algebra on X(n − 1),
// its entries carried into S by the augmentation read in degree n − 1.
var DifferentialFaceDef = differentialFaceDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialFaceDef",
	Key:   "prop_e05c84b04906bba8",
	Const: "differential_face",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"num → " +
		"(U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:(num → set(U)). ∀d:(num → num → U → U). ∀ε:(U → B). ∀N:module_ops(B, D). ∀n i:num. " +
			"differential_face(R, X, d, ε, N, n, i) = " + jacobian(
			"X(n)", "X(n - 1)", "d(n, i)", "augmentation_at(d, ε, n - 1)"),
	},
	Reading: "Indexed as the faces are, by the source degree: the faces are read for n ≥ 1 and i " +
		"≤ n, and at n = 0 the value is a Jacobian of d(0, i) from X(0) to itself that no axiom reads. " +
		"A differential dx ⊗ m goes to Σ_t dt ⊗ ε_{n−1}(∂_t d(n, i)(x)) • m, the coefficients reaching " +
		"N through the augmentation in the target degree; that the augmentation in degree n − 1 after " +
		"any face is the augmentation in degree n is what makes the faces compose as the chain rule asks.",
})}

// DifferentialDegeneracyDef — `differential_degeneracy(R, X, d, s, ε, N,
// n, j)`: the degeneracy j out of degree n acting on the differentials,
// the Jacobian of s(n, j) from the free algebra on X(n) to the free
// algebra on X(n + 1), its entries carried into S by the augmentation
// read in degree n + 1.
var DifferentialDegeneracyDef = differentialDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialDegeneracyDef",
	Key:   "prop_6d83ff3dff4db92e",
	Const: "differential_degeneracy",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"num → " +
		"(U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:(num → set(U)). ∀d s:(num → num → U → U). ∀ε:(U → B). ∀N:module_ops(B, D). ∀n j:num. " +
			"differential_degeneracy(R, X, d, s, ε, N, n, j) = " + jacobian(
			"X(n)", "X(n + 1)", "s(n, j)", "augmentation_at(d, ε, n + 1)"),
	},
	Reading: "The faces d enter only through the augmentation in degree n + 1, the 0-th faces " +
		"down to degree 0; only j ≤ n is read. In a polynomial simplicial algebra a degeneracy " +
		"carries the variable of a name to the variable of a name, so its Jacobian sends dx ⊗ m to " +
		"dy ⊗ m for the name y with s(n, j)(var x) = var y, the entry being the augmentation of one.",
})}

// ---------------------------------------------------------------------------
// The boundary and the complex
// ---------------------------------------------------------------------------

// DifferentialBoundaryDef — `differential_boundary(R, X, d, S, ε, N, n)`:
// the boundary out of degree n, Σ_{i ≤ n} (−1)^i • differential_face(R,
// X, d, ε, N, n, i), the signs those of S and the sum taken among the
// finitely supported functions on the whole host with values in N.
var DifferentialBoundaryDef = differentialBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialBoundaryDef",
	Key:   "prop_425f6bc6e152f916",
	Const: "differential_boundary",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"ring_ops(B) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"(U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀ε:(U → B). " +
			"∀N:module_ops(B, D). " +
			"∀n:num. " +
			"    differential_boundary(R, X, d, S, ε, N, n) = " +
			"    face_boundary(S, finite_supp_module(N, 𝕌⟨A:U⟩), differential_face(R, X, d, ε, N), n)",
	},
	Reading: "It is face_boundary's alternating sum at the faces of the " +
		"differentials, so the differential complex is the face complex of the simplicial " +
		"module those faces make; S enters only through its one and its negation, the " +
		"signs. At n = 0 it is the one face of a vertex, a value the complex never reads.",
	Deps: []registry.EntryLike{DifferentialFaceDef},
})}

// DifferentialComplexDef — `differential_complex(R, X, d, S, ε, N)`: the
// complex of differentials of the polynomial simplicial algebra with
// coefficients in N, a complex over S — in degree n the finitely
// supported functions on X(n) with values in N, under N's operations
// pointwise, and the alternating sum of the faces' Jacobians as the
// differential.
var DifferentialComplexDef = differentialComplexDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialComplexDef",
	Key:   "prop_8e698351b1d63e86",
	Const: "differential_complex",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"ring_ops(B) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"complex_ops(B, U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀ε:(U → B). " +
			"∀N:module_ops(B, D). " +
			"    differential_complex(R, X, d, S, ε, N) = " +
			"    pack_complex(fun_add(N.add), " +
			"        fun_zero(N.zero), " +
			"        fun_neg(N.neg), " +
			"        fun_smul(N.smul), " +
			"        differential_terms(X, N), " +
			"        differential_boundary(R, X, d, S, ε, N))",
	},
	Reading: "Its ring is S, the ring N is a module over; the degeneracies are not read. " +
		"ε is any map into S's type: at the augmentation of a resolution of S this is L_{S/R} " +
		"⊗_S N computed on that resolution, and at g ∘ ε for a ring map g from S to T, with T " +
		"in S's place and N a module over T, it is the complex with coefficients extended " +
		"along g. The complex is read as one of modules under cotangent_universe(R, 𝕌⟨A:U⟩), " +
		"which makes the free algebras and their partial derivatives what they are named.",
	Deps: []registry.EntryLike{DifferentialTermsDef, DifferentialBoundaryDef},
})}

// ---------------------------------------------------------------------------
// Algebra maps
// ---------------------------------------------------------------------------

// DifferentialMapDef — `differential_map(R, X, Y, d', ε', F, N, n)`: the
// map on the differentials in degree n induced by an algebra map F from
// a polynomial simplicial algebra on the names X to one on the names Y,
// the Jacobian of F(n) from the free algebra on X(n) to the free algebra
// on Y(n), its entries carried into the scalars of N by the target's
// augmentation read in degree n.
var DifferentialMapDef = differentialMapDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialMapDef",
	Key:   "prop_7986c45d55261fcf",
	Const: "differential_map",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(U → B) → " +
		"(num → U → U) → " +
		"module_ops(B, D) → " +
		"num → " +
		"(U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). ∀X Y:(num → set(U)). ∀d':(num → num → U → U). ∀ε':(U → B). ∀F:(num → U → U). ∀N:module_ops(B, D). ∀n:num. " +
			"differential_map(R, X, Y, d', ε', F, N, n) = " + jacobian(
			"X(n)", "Y(n)", "F(n)", "augmentation_at(d', ε', n)"),
	},
	Reading: "The faces and the augmentation are the target's; the source's are not " +
		"read. It is a chain map from the source's differential complex at ε to the " +
		"target's at ε' when F covers the identity of the augmentation target, ε'(F(0, u)) " +
		"= ε(u) on the free algebra on X(0): then the two augmentations agree after F in " +
		"every degree, which the chain rule asks. F(n) is read at the variables of X(n) only.",
})}

// ---------------------------------------------------------------------------
// The differentials as a simplicial module and a chain complex
// ---------------------------------------------------------------------------

// DifferentialFaceHom — in a universe for R, each face of the
// differentials of an augmented polynomial simplicial algebra is a
// homomorphism of modules over S, from the functions on the names of
// degree n + 1 to those on the names of degree n.
var DifferentialFaceHom = differentialFaceHomThm{family.Add(registry.ProofEntry{
	Name: "DifferentialFaceHom",
	Key:  "prop_330af8a73bf1c2bb",
	Reading: "cotangent_universe(R) is load-bearing only through " +
		"UniverseEmbeddingHost, which JacobianHom needs; the scalars come " +
		"from the augmentation in the target degree, n for a face out of n + 1.",
	Deps: []registry.EntryLike{
		DifferentialFaceDef,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.AugmentationAtHom,
		partial_derivative.JacobianHom,
	},
	Build: family.Card(simplicial_ring.AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀N:module_ops(B, D). ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"module_on(S, N)",
			"i ≤ n + 1",
		},
		Conclusion: "module_homomorphism(S, " +
			"    finite_supp_module(N, X(n + 1)), " +
			"    finite_supp_module(N, X(n)), " +
			"    differential_face(R, X, d, ε, N, n + 1, i))",
	}),
		"unfold DifferentialFaceDef and apply JacobianHom: the universe embedding of R is an embedding "+
			"(UniverseEmbeddingHost), R is a commutative ring (a conjunct of PolynomialSimplicialAlgebra), "+
			"the face is an algebra map over R between the free algebras on X(n + 1) and X(n) "+
			"(UniverseAlgebraHomomorphismDef), and the augmentation in degree n is a ring map out of the "+
			"free algebra on X(n) (AugmentationAtHom, its record unfolded by UniverseAlgebraRingDef)"),
})}

// DifferentialDegeneracyHom — in a universe for R, each degeneracy of the
// differentials of an augmented polynomial simplicial algebra is a
// homomorphism of modules over S, from the functions on the names of
// degree n to those on the names of degree n + 1.
var DifferentialDegeneracyHom = differentialDegeneracyHomThm{family.Add(registry.ProofEntry{
	Name: "DifferentialDegeneracyHom",
	Key:  "prop_1b0a39de8a1568dc",
	Reading: "cotangent_universe(R) is load-bearing only through " +
		"UniverseEmbeddingHost, which JacobianHom needs; the scalars come from " +
		"the augmentation in the target degree, n + 1 for a degeneracy out of n.",
	Deps: []registry.EntryLike{
		DifferentialDegeneracyDef,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.AugmentationAtHom,
		partial_derivative.JacobianHom,
	},
	Build: family.Card(simplicial_ring.AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀N:module_ops(B, D). ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"module_on(S, N)",
			"i ≤ n",
		},
		Conclusion: "module_homomorphism(S, " +
			"    finite_supp_module(N, X(n)), " +
			"    finite_supp_module(N, X(n + 1)), " +
			"    differential_degeneracy(R, X, d, s, ε, N, n, i))",
	}),
		"as DifferentialFaceHom: unfold DifferentialDegeneracyDef and apply "+
			"JacobianHom at the degeneracy, an algebra map over R from the free "+
			"algebra on X(n) to the one on X(n + 1) (UniverseAlgebraHomomorphismDef), "+
			"and the augmentation in degree n + 1, a ring map (AugmentationAtHom)"),
})}

// DifferentialSimplicialModule — in a universe for R, the differentials
// of an augmented polynomial simplicial algebra with coefficients in a
// module N over S, under the Jacobians of its faces and degeneracies, are
// a simplicial module over S inside the finitely supported functions on
// the whole host.
var DifferentialSimplicialModule = differentialSimplicialModuleThm{family.Add(registry.ProofEntry{
	Name: "DifferentialSimplicialModule",
	Key:  "prop_d171c88c4962954d",
	Reading: "The faces and degeneracies are the Jacobians at the augmentation in the target degree. " +
		"Every simplicial identity reduces through JacobianCompose to aug(n + 1) = aug(n) ∘ d(n + 1, i) " +
		"on the algebra on X(n + 1) — the augmentation in degree n + 1 is the one in degree n after any " +
		"face, which holds because ε coequalizes the two faces out of degree 1 — and after a degeneracy " +
		"to aug(n + 2) ∘ s(n + 1, i) = aug(n + 1), which follows by d_i s_i = id; without ε d_0 = ε d_1 " +
		"the identity d_0 d_2 = d_1 d_0 fails on the Jacobians. The faces of vertices are not read.",
	Deps: []registry.EntryLike{
		DifferentialTermsDef,
		DifferentialFaceDef,
		DifferentialDegeneracyDef,
		DifferentialFaceHom,
		DifferentialDegeneracyHom,
		simplicial_module.SimplicialModule,
		simplicial_set.SimplicialSet,
		function_module.FiniteSuppModuleOn,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppDef,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.AugmentationAtFaceIndependent,
		simplicial_ring.AugmentationAtHom,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		partial_derivative.JacobianIdentity,
	},
	Build: family.Card(simplicial_ring.AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"module_on(S, N)",
		},
		Conclusion: "simplicial_module(S, " +
			"    finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"    mk_simplicial(differential_terms(X, N), " +
			"        differential_face(R, X, d, ε, N), " +
			"        differential_degeneracy(R, X, d, s, ε, N)))",
	}),
		"finite_supp_module(N, 𝕌) is a module (FiniteSuppModuleOn) and each finite_supp(N.zero, "+
			"N.carrier, X(n)) a submodule, closed under the pointwise operations; faces and degeneracies "+
			"are linear (DifferentialFaceHom, DifferentialDegeneracyHom). For each simplicial identity "+
			"both sides are composites of Jacobians, and JacobianCompose makes each the Jacobian of the "+
			"composite map, the inner augmentation agreeing with the outer after the face or degeneracy "+
			"(AugmentationAtFaceIndependent, and after a degeneracy d_i s_i = id); the composites agree "+
			"on the variables by the identity of the simplicial set of PolynomialSimplicialAlgebra "+
			"(JacobianCongruence), and d_i s_i = d_{i+1} s_i = id is JacobianIdentity"),
})}

// DifferentialComplexChain — in a universe for R, the differential
// complex of an augmented polynomial simplicial algebra with coefficients
// in a module N over S is a chain complex over S.
var DifferentialComplexChain = differentialComplexChainThm{family.Add(registry.ProofEntry{
	Name: "DifferentialComplexChain",
	Key:  "prop_c01f0b61ff5be1f3",
	Reading: "The boundary out of degree 0, the Jacobian of d(0, 0), is never read: the " +
		"faces of vertices, arbitrary in every polynomial simplicial algebra, do not matter.",
	Deps: []registry.EntryLike{
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialSimplicialModule,
		simplicial_module.FaceComplexChain,
		simplicial_module.FaceComplexDef,
		function_module.FiniteSuppModuleDef,
	},
	Build: family.Card(simplicial_ring.AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"module_on(S, N)",
		},
		Conclusion: "chain_complex(S, differential_complex(R, X, d, S, ε, N))",
	}),
		"differential_complex(R, X, d, S, ε, N) is face_complex(S, finite_supp_module(N, "+
			"𝕌), differential_terms(X, N), differential_face(R, X, d, ε, N)) "+
			"(DifferentialComplexDef, DifferentialBoundaryDef, FaceComplexDef, the operations "+
			"of FiniteSuppModuleDef); FaceComplexChain at DifferentialSimplicialModule"),
})}

// ---------------------------------------------------------------------------
// Algebra maps and homotopies
// ---------------------------------------------------------------------------

// DifferentialMapChainMap — in a universe for R, an algebra map between
// augmented polynomial simplicial algebras over R that covers the
// identity of their common augmentation target S induces, by its
// Jacobians, a chain map of the differential complexes.
var DifferentialMapChainMap = differentialMapChainMapThm{family.Add(registry.ProofEntry{
	Name: "DifferentialMapChainMap",
	Key:  "prop_c02c3c52ae17986",
	Reading: "The covering condition is load-bearing: the source complex reads the " +
		"source's augmentation and the Jacobian of F the target's, and the two agree after F " +
		"in every degree, aug_Y(n) ∘ F(n) = aug_X(n) (SimplicialAlgebraMapAugmentationAt), " +
		"exactly because they agree in degree 0; since F fixes the constants, covering also " +
		"forces f = f' on R's carrier. A map over a ring map S → S' is this statement after " +
		"both augmentations are followed into one ring (AugmentedAlongRingMap).",
	Deps: []registry.EntryLike{
		DifferentialMapDef,
		DifferentialComplexChain,
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialFaceDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.AugmentationAtHom,
		simplicial_ring.AugmentationAtFaceIndependent,
		simplicial_ring.UniverseEmbeddingHost,
		resolution_comparison.SimplicialAlgebraMapAugmentationAt,
		partial_derivative.JacobianHom,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		chain_complex.ChainMapDef,
		simplicial_module.FaceBoundaryDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		simplicial_set.SimplicialMap,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f f':(A → B). " +
			"∀ε ε':(U → B). " +
			"∀N:module_ops(B, D). " +
			"∀F:(num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"augmented_polynomial_algebra(R, Y, d', s', S, f', ε')",
			"module_on(S, N)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)",
		},
		Conclusion: "chain_map(S, " +
			"    differential_complex(R, X, d, S, ε, N), " +
			"    differential_complex(R, Y, d', S, ε', N), " +
			"    differential_map(R, X, Y, d', ε', F, N))",
	},
		"each differential_map(n) is linear by JacobianHom, F(n) an algebra map over R and the target's "+
			"augmentation in degree n a ring map (AugmentationAtHom). The augmentations agree after F in "+
			"every degree (SimplicialAlgebraMapAugmentationAt at the identity of S), so JacobianCompose "+
			"makes both J(F(n)) ∘ J(d(n + 1, i)) and J(d'(n + 1, i)) ∘ J(F(n + 1)) the Jacobian of one "+
			"composite, the inner augmentations read through AugmentationAtFaceIndependent; the composites "+
			"agree on the variables, F being simplicial (JacobianCongruence), and the alternating sums of "+
			"the boundaries follow by linearity (HomSum, HomSmul)"),
})}

// DifferentialMapIdentity — the identity map of an augmented polynomial
// simplicial algebra induces the identity on its differentials.
var DifferentialMapIdentity = differentialMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "DifferentialMapIdentity",
	Key:  "prop_13bbb1b066b427e8",
	Deps: []registry.EntryLike{
		DifferentialMapDef,
		DifferentialTermsDef,
		simplicial_ring.AugmentationAtHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseAlgebraRingDef,
		partial_derivative.JacobianIdentity,
	},
	Build: family.Card(simplicial_ring.AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀N:module_ops(B, D). ∀n:num. ∀u:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"module_on(S, N)",
			"u ∈ differential_terms(X, N, n)",
		},
		Conclusion: "differential_map(R, X, X, d, ε, λm:num. λx:U. x, N, n, u) = u",
	}),
		"JacobianIdentity at the identity of the free algebra on X(n), which "+
			"fixes every variable, and the augmentation in degree n, a ring map "+
			"(AugmentationAtHom); the embedding is one by UniverseEmbeddingHost"),
})}

// DifferentialMapCompose — the Jacobians of a composite of algebra maps
// are the composites of their Jacobians, the second map covering the
// identity of the augmentation target.
var DifferentialMapCompose = differentialMapComposeThm{family.Add(registry.ProofEntry{
	Name: "DifferentialMapCompose",
	Key:  "prop_5a11bf0d0753366f",
	Reading: "Only G need cover the identity: the inner Jacobian reads the middle " +
		"augmentation, which must agree with the last after G. F is any algebra map. " +
		"X needs no augmentation: differential_map never reads the source's.",
	Deps: []registry.EntryLike{
		DifferentialMapDef,
		DifferentialTermsDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.AugmentationAtHom,
		simplicial_ring.UniverseEmbeddingHost,
		resolution_comparison.SimplicialAlgebraMapAugmentationAt,
		partial_derivative.JacobianCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X Y Z:(num → set(U)). " +
			"∀d s d' s' d'' s'':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f' f'':(A → B). " +
			"∀ε' ε'':(U → B). " +
			"∀F G:(num → U → U). " +
			"∀N:module_ops(B, D). " +
			"∀n:num. " +
			"∀u:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, Y, d', s', S, f', ε')",
			"augmented_polynomial_algebra(R, Z, d'', s'', S, f'', ε'')",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"simplicial_algebra_map(R, Y, d', s', Z, d'', s'', G)",
			"∀v:U. v ∈ universe_algebra(R, Y(0)) ⇒ ε''(G(0, v)) = ε'(v)",
			"module_on(S, N)",
			"u ∈ differential_terms(X, N, n)",
		},
		Conclusion: "differential_map(R, X, Z, d'', ε'', λm:num. λx:U. G(m, F(m, x)), N, n, u) = " +
			"differential_map(R, Y, Z, d'', ε'', G, N, n, differential_map(R, X, Y, d', ε', F, N, n, u))",
	},
		"JacobianCompose at F(n) and G(n), algebra maps over R, the outer augmentation the one of "+
			"Z in degree n, a ring map (AugmentationAtHom), and the inner the one of Y in degree n, "+
			"which agrees with it after G by SimplicialAlgebraMapAugmentationAt at the identity of S"),
})}

// DifferentialHomotopyChainHomotopy — in a universe for R, an algebra
// homotopy from F to G between maps of augmented polynomial simplicial
// algebras covering the identity of S induces the chain homotopy
// Σ_{j ≤ n} (−1)^j J(H(n, j)) between the chain maps of F and G.
var DifferentialHomotopyChainHomotopy = differentialHomotopyChainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "DifferentialHomotopyChainHomotopy",
	Key:  "prop_574264b6e5534a0e",
	Reading: "G covers the identity as F does, ε'(G(0, u)) = ε'(d'(1, 1, H(0, 0, u))) = ε'(d'(1, 0, " +
		"H(0, 0, u))) = ε'(F(0, u)), so it is not asked. The homotopy runs from F to G, the direction of " +
		"chain_homotopy's f − g; its Jacobians are taken at the target's augmentation one degree up. The " +
		"key lemma is aug_Y(n + 1) ∘ H(n, j) = aug_X(n) on the algebra on X(n) for every j ≤ n, by " +
		"induction on j — j = 0 from d_0 H_0 = F and covering, j > 0 from d_0 H_j = H_{j−1} d_0; it " +
		"gives both the linearity of J(H) and the identities ∂h + h∂ = J(F) − J(G) under May's convention.",
	Deps: []registry.EntryLike{
		DifferentialMapDef,
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialSimplicialModule,
		DifferentialMapChainMap,
		simplicial_ring.SimplicialAlgebraHomotopy,
		simplicial_homotopy.SimplicialHomotopy,
		simplicial_ring.AugmentationAtHom,
		simplicial_ring.AugmentationAtFaceIndependent,
		resolution_comparison.SimplicialAlgebraMapAugmentationAt,
		partial_derivative.JacobianHom,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		simplicial_module.SimplicialModuleHomotopy,
		simplicial_module.SimplicialModuleHomotopyChainHomotopy,
		simplicial_module.FaceComplexDef,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f f':(A → B). " +
			"∀ε ε':(U → B). " +
			"∀N:module_ops(B, D). " +
			"∀F G:(num → U → U). " +
			"∀H:(num → num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"augmented_polynomial_algebra(R, Y, d', s', S, f', ε')",
			"module_on(S, N)",
			"simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, H)",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)",
		},
		Conclusion: "chain_homotopy(S, " +
			"    differential_complex(R, X, d, S, ε, N), " +
			"    differential_complex(R, Y, d', S, ε', N), " +
			"    differential_map(R, X, Y, d', ε', F, N), " +
			"    differential_map(R, X, Y, d', ε', G, N), " +
			"    λn:num. λu:(U → D). " +
			"        module_sum(fun_add(N.add), " +
			"            fun_zero(N.zero), " +
			"            0 .. n, " +
			"            λj:num. " +
			"                fun_smul(N.smul, " +
			"                    alternating_sign(S.one, S.neg, j), " +
			"                    free_algebra_jacobian(universe_embedding(R), " +
			"                        universe_embedding(R), " +
			"                        R, " +
			"                        R, " +
			"                        X(n), " +
			"                        Y(n + 1), " +
			"                        H(n, j), " +
			"                        augmentation_at(d', ε', n + 1), " +
			"                        N, " +
			"                        u))))",
	},
		"the augmentation of Y in degree n + 1 after H(n, j) is the augmentation of X in degree "+
			"n: read it after the 0-th face (AugmentationAtFaceIndependent) and use d_0 H_0 = F, "+
			"d_0 H_j = H_{j-1} d_0 and the covering of F (SimplicialAlgebraMapAugmentationAt). So "+
			"the Jacobians of the H(n, j) are linear (JacobianHom) and satisfy the homotopy "+
			"identities (JacobianCompose, JacobianCongruence): a simplicial_module_homotopy between "+
			"the differential simplicial modules (DifferentialSimplicialModule; the Jacobians of F "+
			"and of G commute with every face and degeneracy, as in DifferentialMapChainMap), and "+
			"SimplicialModuleHomotopyChainHomotopy on their face complexes, which the differential "+
			"complexes are (DifferentialComplexDef, DifferentialBoundaryDef, FaceComplexDef)"),
})}

// ResolutionMapChainHomotopyEquivalence — in a universe for R, a map of
// polynomial resolutions of S over the identity of S induces a chain
// homotopy equivalence of the differential complexes, with coefficients
// in a module N over any ring T that S maps to; its inverse is the
// Jacobian of a map of resolutions back, again over the identity.
var ResolutionMapChainHomotopyEquivalence = resolutionMapChainHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ResolutionMapChainHomotopyEquivalence",
	Key:  "prop_2e93826fcdb9e968",
	Reading: "F must cover the identity of S; a map over another endomorphism of S is not an " +
		"equivalence in general. Both algebras must be resolutions: the inverse map is built " +
		"into X and the two homotopies are built into X and into Y. The coefficients are carried " +
		"to T after the resolution property is used, so T and N are arbitrary; T = S with g = " +
		"λx:B. x is the case of a module over S. The shared structure map f is no restriction, " +
		"since covering forces it; the homotopies needed are G ∘ F ⇒ id and F ∘ G ⇒ id, the " +
		"direction ComparisonHomotopyExists produces, and composites are identified only on terms.",
	Deps: []registry.EntryLike{
		DifferentialMapChainMap,
		DifferentialHomotopyChainHomotopy,
		DifferentialMapCompose,
		DifferentialMapIdentity,
		simplicial_ring.AugmentedAlongRingMap,
		resolution_comparison.ComparisonMapExists,
		resolution_comparison.ComparisonHomotopyExists,
		resolution_comparison.SimplicialAlgebraMapCompose,
		resolution_comparison.SimplicialAlgebraMapIdentity,
		simplicial_ring.PolynomialResolution,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.Target,
		chain_complex.ChainHomotopyEquivalenceDef,
		chain_complex.ChainHomotopyDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε ε':(U → B). " +
			"∀F:(num → U → U). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S, f, ε')",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "∃G:(num → U → U). " +
			"    simplicial_algebra_map(R, Y, d', s', X, d, s, G) ∧ " +
			"    (∀v:U. v ∈ universe_algebra(R, Y(0)) ⇒ ε(G(0, v)) = ε'(v)) ∧ " +
			"    chain_homotopy_equivalence(T, " +
			"        differential_complex(R, X, d, T, λu:U. g(ε(u)), N), " +
			"        differential_complex(R, Y, d', T, λu:U. g(ε'(u)), N), " +
			"        differential_map(R, X, Y, d', λu:U. g(ε'(u)), F, N), " +
			"        differential_map(R, Y, X, d, λu:U. g(ε(u)), G, N))",
	},
		"ComparisonMapExists into the resolution X, at the identity of S (RingHomIdentity, S a "+
			"ring by Target of f), gives G covering the identity. ComparisonHomotopyExists gives a "+
			"homotopy from G ∘ F to the identity of X and one from F ∘ G to the identity of Y, each "+
			"pair agreeing after the augmentation (SimplicialAlgebraMapCompose, "+
			"SimplicialAlgebraMapIdentity) — the directions chain_homotopy_equivalence asks, so no "+
			"homotopy is reversed. Followed into T (AugmentedAlongRingMap), DifferentialMapChainMap "+
			"makes the two Jacobians chain maps and DifferentialHomotopyChainHomotopy the homotopies "+
			"chain homotopies; on the terms, which is all chain_homotopy reads, the Jacobian of a "+
			"composite is the composite of the Jacobians (DifferentialMapCompose) and that of the "+
			"identity the identity (DifferentialMapIdentity) (ChainHomotopyEquivalenceDef)"),
})}

var DifferentialScalarBased = differentialScalarBasedThm{family.Add(registry.ProofEntry{
	Name: "DifferentialScalarBased",
	Key:  "prop_f488f8a817a90e85",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "based_chain_complex(T, " +
			"    differential_complex(R, X, d, T, λu:U. g(ε(u)), regular_module(T)), " +
			"    X, " +
			"    λn:num. λa:(U → C). a, " +
			"    λn:num. λa:(U → C). a)",
	},
		"The arbitrary augmented polynomial algebra version of CotangentScalarBased. "+
			"AugmentedAlongRingMap and DifferentialComplexChain supply the chain laws over T; each "+
			"term is the free module on X(n), so the identity gives its expansion and coordinate maps."),
	Deps: []registry.EntryLike{
		simplicial_ring.AugmentedAlongRingMap,
		DifferentialComplexChain,
		free_module.FreeModuleOn,
		module.RegularModuleOn,
	},
	Reading: "No resolution or countability hypothesis is needed for the " +
		"basis. The augmentation and the host capacity give the differential; " +
		"the basis is the given name set in each degree, not the whole host.",
})}
