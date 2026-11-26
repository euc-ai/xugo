// simplicial_ring.go — polynomial simplicial algebras over a commutative
// ring in the one host type: a simplicial set of name sets X(n), whose
// n-simplices are the free algebra in the universe on X(n), every face
// and degeneracy an algebra map fixing the constants and every
// degeneracy carrying generators to generators;
// an augmentation onto an algebra over the base ring, its composite
// with the 0-th faces in every degree, and a resolution, the
// augmentation acyclic on the underlying simplicial module; the algebra
// maps and algebra homotopies between polynomial simplicial algebras
// over one ring. In a universe the algebra is a simplicial module, a Kan
// complex, and its maps and homotopies are linear; the augmentation in
// every degree is an algebra map and reads any face; the constant
// algebra resolves its own free algebra.

package simplicial_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Polynomial simplicial algebras
// ---------------------------------------------------------------------------

// PolynomialSimplicialAlgebra — `polynomial_simplicial_algebra(R, X, d,
// s)`: R is a commutative ring, the free algebras universe_algebra(R,
// X(n)) over R on the name sets X(n) are a simplicial set under the
// faces d and the degeneracies s, every face d(n + 1, i) and every
// degeneracy s(n, i) is an algebra map over R between the free algebras
// on X(n + 1) and on X(n), and every degeneracy carries the variable of
// a name of X(n) to the variable of a name of X(n + 1).
var PolynomialSimplicialAlgebra = polynomialSimplicialAlgebraThm{family.DefineStructure(registry.DefEntry{
	Name:  "PolynomialSimplicialAlgebra",
	Key:   "prop_154642d90de2566b",
	Const: "polynomial_simplicial_algebra",
	Type:  "ring_ops(A) → (num → set(U)) → (num → num → U → U) → (num → num → U → U) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:(num → set(U)). ∀d s:(num → num → U → U). " +
			"    polynomial_simplicial_algebra(R, X, d, s) ⇔ " +
			"    comm_ring_on(R) ∧ " +
			"    simplicial_set(polynomial_simplicial_set(R, X, d, s)) ∧ " +
			"    (∀n i:num. i ≤ n + 1 ⇒ universe_algebra_homomorphism(R, X(n + 1), X(n), d(n + 1, i))) ∧ " +
			"    (∀n i:num. i ≤ n ⇒ universe_algebra_homomorphism(R, X(n), X(n + 1), s(n, i))) ∧ " +
			"    (∀n i:num. " +
			"        i ≤ n ⇒ " +
			"        image(s(n, i), image(universe_algebra_var(R), X(n))) ⊆ " +
			"        image(universe_algebra_var(R), X(n + 1)))",
	},
	Reading: "All the free algebras are subrings of the one ring on 𝕌 under the same operations, " +
		"so the faces and degeneracies are functions of the host and only the carriers vary with n; the " +
		"faces of vertices, d(0, i), are not read. Each algebra-map conjunct asks the free algebras to " +
		"be rings, which needs universe_embedding(R) to be an embedding: statements carry " +
		"cotangent_universe(R, 𝕌⟨A:U⟩) for that. Over the zero ring every free algebra is one point; on " +
		"an empty name set the free algebra is the constants. The closure is on the variables " +
		"universe_algebra_var(R, x), which is what the standard resolution satisfies — s(n, 0) sends var " +
		"x to var(var x), s(n, j + 1) sends var x to var(s(n − 1, j)(x)); a closure on the names would " +
		"read s(n, j) at a name, an arbitrary member of U outside the algebra s(n, j) is a map of, where " +
		"its value is an ε-choice. Only the degeneracies keep generators: a face of a generator is an " +
		"arbitrary member of the algebra below. Over a nonzero ring var is injective, so the last " +
		"conjunct amounts to a map of the names of X(n) into those of X(n + 1); over the zero ring every " +
		"variable is the one point, and it asks only that X(n + 1) be nonempty where X(n) is.",
	Deps: []registry.EntryLike{
		UniverseAlgebraDef,
		UniverseAlgebraHomomorphismDef,
		UniverseAlgebraVarDef,
		PolynomialSimplicialSetDef,
	},
})}

// AugmentedPolynomialAlgebra — `augmented_polynomial_algebra(R, X, d, s,
// S, f, ε)`: a polynomial simplicial algebra over R augmented over the
// R-algebra S — f a ring map from R to S, the structure map, and ε a
// ring map from the free algebra on X(0) to S carrying the constant a
// to f(a), with ε d_0 = ε d_1 on the free algebra on X(1).
var AugmentedPolynomialAlgebra = augmentedPolynomialAlgebraThm{family.DefineStructure(registry.DefEntry{
	Name:  "AugmentedPolynomialAlgebra",
	Key:   "prop_18598470243182ce",
	Const: "augmented_polynomial_algebra",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(U → B) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"    augmented_polynomial_algebra(R, X, d, s, S, f, ε) ⇔ " +
			"    polynomial_simplicial_algebra(R, X, d, s) ∧ " +
			"    ring_homomorphism(R, S, f) ∧ " +
			"    ring_homomorphism(restrict_ring(universe_algebra_ring(R, X(0)), universe_algebra(R, X(0))), " +
			"        S, " +
			"        ε) ∧ " +
			"    (∀a:A. a ∈ R.carrier ⇒ ε(universe_algebra_const(R, a)) = f(a)) ∧ " +
			"    (∀u:U. u ∈ universe_algebra(R, X(1)) ⇒ ε(d(1, 0, u)) = ε(d(1, 1, u)))",
	},
	Reading: "The structure map f is a component: S is an algebra over R through f, " +
		"and ε is an algebra map over f, so a map of augmented algebras over a map S → S' is " +
		"asked to commute with the two structure maps. ε is read on the free algebra on X(0) " +
		"only and is not asked to be onto; a resolution asks that. Over the zero ring R the " +
		"ring map f forces S to be the zero ring, since f(R.one) = S.one and R.one = R.zero.",
	Deps: []registry.EntryLike{
		PolynomialSimplicialAlgebra,
		UniverseAlgebraRingDef,
		UniverseAlgebraConstDef,
		UniverseAlgebraDef,
	},
})}

// AugmentationAtDef — `augmentation_at(d, ε, n)`: the augmentation read
// in degree n, ε ∘ d(1, 0) ∘ … ∘ d(n, 0) — ε in degree 0, and in degree
// n + 1 the 0-th face followed by the augmentation in degree n.
var AugmentationAtDef = augmentationAtDefThm{family.Define(registry.DefEntry{
	Name:  "AugmentationAtDef",
	Key:   "prop_8ca79492b1c00856",
	Const: "augmentation_at",
	Type:  "(num → num → U → U) → (U → B) → num → U → B",
	Equations: []string{
		"∀d:(num → num → U → U). ∀ε:(U → B). augmentation_at(d, ε, 0) = ε",
		"∀d:(num → num → U → U). ∀ε:(U → B). ∀n:num. " +
			"    augmentation_at(d, ε, suc(n)) = (λu:U. augmentation_at(d, ε, n, d(suc(n), 0, u)))",
	},
	Reading: "Composed with the 0-th faces only; that any face may be used — augmentation_at(d, " +
		"ε, n + 1) = augmentation_at(d, ε, n) ∘ d(n + 1, i) for every i ≤ n + 1 — is a theorem of an " +
		"augmented algebra, from ε d_0 = ε d_1 in degree 1 and the face identities above it.",
})}

// PolynomialResolution — `polynomial_resolution(R, X, d, s, S, f, ε)`: an
// augmented polynomial simplicial algebra over the R-algebra S whose
// underlying simplicial module over R — the free algebras on X(n) inside
// the module of the free algebra on 𝕌 — is acyclic over S's carrier
// through ε: its Moore complex is exact in positive degrees, ε is onto S,
// and two members of the degree-0 algebra have one image under ε exactly
// when their difference is d_0 of a Moore 1-simplex.
var PolynomialResolution = polynomialResolutionThm{family.DefineStructure(registry.DefEntry{
	Name:  "PolynomialResolution",
	Key:   "prop_71f3161bd870568",
	Const: "polynomial_resolution",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(U → B) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"    polynomial_resolution(R, X, d, s, S, f, ε) ⇔ " +
			"    augmented_polynomial_algebra(R, X, d, s, S, f, ε) ∧ " +
			"    acyclic_augmentation(R, " +
			"        universe_algebra_module(R), " +
			"        polynomial_simplicial_set(R, X, d, s), " +
			"        S.carrier, " +
			"        ε)",
	},
	Reading: "Acyclicity is stated on the Moore complex, the simplices whose faces 1, …, n vanish " +
		"with d_0 as differential, and needs no Kan condition and no homotopy groups. With ε a ring map " +
		"onto S, the degree-0 conjunct says ε reads the degree-0 algebra modulo d_0 of the Moore " +
		"1-simplices onto S, an ideal. The constant algebra on a generator set S₀ — X(n) = S₀, every " +
		"face and degeneracy the identity — resolves its own degree-0 algebra through the identity.",
	Deps: []registry.EntryLike{
		AugmentedPolynomialAlgebra,
		UniverseAlgebraModuleDef,
		UniverseAlgebraDef,
		PolynomialSimplicialSetDef,
	},
})}

// ---------------------------------------------------------------------------
// Algebra maps and algebra homotopies
// ---------------------------------------------------------------------------

// SimplicialAlgebraMap — `simplicial_algebra_map(R, X, d, s, Y, d', s',
// F)`: between two polynomial simplicial algebras over R, a simplicial
// map of the free algebras whose component F(n) is an algebra map over R
// from the free algebra on X(n) to the free algebra on Y(n) in every
// degree.
var SimplicialAlgebraMap = simplicialAlgebraMapThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialAlgebraMap",
	Key:   "prop_4a88e218de17b04d",
	Const: "simplicial_algebra_map",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → U → U) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F:(num → U → U). " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', F) ⇔ " +
			"    polynomial_simplicial_algebra(R, X, d, s) ∧ " +
			"    polynomial_simplicial_algebra(R, Y, d', s') ∧ " +
			"    simplicial_map(polynomial_simplicial_set(R, X, d, s), " +
			"        polynomial_simplicial_set(R, Y, d', s'), " +
			"        F) ∧ " +
			"    (∀n:num. universe_algebra_homomorphism(R, X(n), Y(n), F(n)))",
	},
	Reading: "Both algebras are over the one ring R in the one host, so a map is a " +
		"family of functions of U; it need not carry generators to generators. Compatibility " +
		"with augmentations is not part of the notion and is stated where it is wanted.",
	Deps: []registry.EntryLike{
		PolynomialSimplicialAlgebra,
		UniverseAlgebraDef,
		UniverseAlgebraHomomorphismDef,
		PolynomialSimplicialSetDef,
	},
})}

// SimplicialAlgebraHomotopy — `simplicial_algebra_homotopy(R, X, d, s, Y,
// d', s', F, G, H)`: a simplicial homotopy H from F to G, both algebra
// maps of polynomial simplicial algebras over R, every component H(n, j)
// an algebra map over R from the free algebra on X(n) to the free
// algebra on Y(n + 1).
var SimplicialAlgebraHomotopy = simplicialAlgebraHomotopyThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialAlgebraHomotopy",
	Key:   "prop_56b499a2b98f535e",
	Const: "simplicial_algebra_homotopy",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → U → U) → " +
		"(num → U → U) → " +
		"(num → num → U → U) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀H:(num → num → U → U). " +
			"    simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, H) ⇔ " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', F) ∧ " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', G) ∧ " +
			"    simplicial_homotopy(polynomial_simplicial_set(R, X, d, s), " +
			"        polynomial_simplicial_set(R, Y, d', s'), " +
			"        F, " +
			"        G, " +
			"        H) ∧ " +
			"    (∀n j:num. j ≤ n ⇒ universe_algebra_homomorphism(R, X(n), Y(n + 1), H(n, j)))",
	},
	Reading: "The homotopy is May's combinatorial one, in one direction, from F " +
		"to G; the relation it generates is simplicial_maps_homotopic of the underlying " +
		"simplicial sets. Every component being an algebra map, the homotopy is linear " +
		"over R, so it is a homotopy of the underlying simplicial modules.",
	Deps: []registry.EntryLike{
		SimplicialAlgebraMap,
		UniverseAlgebraDef,
		UniverseAlgebraHomomorphismDef,
		PolynomialSimplicialSetDef,
	},
})}

// ---------------------------------------------------------------------------
// The underlying simplicial module
// ---------------------------------------------------------------------------

// PolynomialAlgebraSimplicialModule — in a universe for R, a polynomial
// simplicial algebra is a simplicial module over R: its free algebras are
// submodules of the free algebra on all of U, its faces and degeneracies
// linear.
var PolynomialAlgebraSimplicialModule = polynomialAlgebraSimplicialModuleThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraSimplicialModule",
	Key:  "prop_40b585585b05ab8",
	Reading: "The universe hypothesis enters only through FreeAlgebraModuleOn, " +
		"which makes the algebra on 𝕌 a module and each degree a submodule. A face " +
		"or degeneracy is linear because the constant of every r lies in the algebra " +
		"on every X(n), ∅ included, and all degrees share one set of operations.",
	Deps: []registry.EntryLike{
		PolynomialSimplicialAlgebra,
		UniverseEmbeddingHost,
		UniverseAlgebraDef,
		UniverseAlgebraModuleDef,
		UniverseAlgebraRingDef,
		UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraModuleOn,
		free_algebra.FreeAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraModuleDef,
		free_algebra.FreeAlgebraRingDef,
		simplicial_module.SimplicialModule,
		module_homomorphism.ModuleHomomorphismDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(PolynomialSimplicialAlgebra.Statement(Statement{
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "simplicial_module(R, " +
			"    universe_algebra_module(R), " +
			"    polynomial_simplicial_set(R, X, d, s))",
	}),
		"the universe embedding is an embedding (UniverseEmbeddingHost), so FreeAlgebraModuleOn gives "+
			"the module and each free algebra a submodule; the simplicial set is a conjunct. A face or "+
			"degeneracy is a ring map fixing the constants, under operations that do not read the names "+
			"(FreeAlgebraRingDef), so it keeps the sum (MapAdd) and carries the scaling const(r) * u to "+
			"const(r) * F(u) (MapMul and the constant conjunct of FreeAlgebraHomomorphismDef): a module "+
			"homomorphism between the free algebras cut out of the module"),
})}

// AlgebraMapIsModuleMap — in a universe for R, an algebra map of
// polynomial simplicial algebras is a linear simplicial map of their
// simplicial modules.
var AlgebraMapIsModuleMap = algebraMapIsModuleMapThm{family.Add(registry.ProofEntry{
	Name: "AlgebraMapIsModuleMap",
	Key:  "prop_ac242d0589e9dd43",
	Deps: []registry.EntryLike{
		SimplicialAlgebraMap,
		PolynomialAlgebraSimplicialModule,
		UniverseEmbeddingHost,
		UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraHomomorphismDef,
		simplicial_module.SimplicialModuleMap,
		module_homomorphism.ModuleHomomorphismDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(SimplicialAlgebraMap.Statement(Statement{
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "simplicial_module_map(R, " +
			"    universe_algebra_module(R), " +
			"    polynomial_simplicial_set(R, X, d, s), " +
			"    universe_algebra_module(R), " +
			"    polynomial_simplicial_set(R, Y, d', s'), " +
			"    F)",
	}),
		"both ends are simplicial modules by PolynomialAlgebraSimplicialModule "+
			"and F is a simplicial map by definition; each F(n) is a ring map "+
			"fixing the constants, linear as in PolynomialAlgebraSimplicialModule"),
})}

// AlgebraHomotopyIsModuleHomotopy — in a universe for R, an algebra
// homotopy of polynomial simplicial algebras is a linear simplicial
// homotopy of their simplicial modules.
var AlgebraHomotopyIsModuleHomotopy = algebraHomotopyIsModuleHomotopyThm{family.Add(registry.ProofEntry{
	Name: "AlgebraHomotopyIsModuleHomotopy",
	Key:  "prop_3b4e40a6fa5ede2",
	Deps: []registry.EntryLike{
		SimplicialAlgebraHomotopy,
		AlgebraMapIsModuleMap,
		UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraHomomorphismDef,
		simplicial_module.SimplicialModuleHomotopy,
		module_homomorphism.ModuleHomomorphismDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(SimplicialAlgebraHomotopy.Statement(Statement{
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "simplicial_module_homotopy(R, " +
			"    universe_algebra_module(R), " +
			"    polynomial_simplicial_set(R, X, d, s), " +
			"    universe_algebra_module(R), " +
			"    polynomial_simplicial_set(R, Y, d', s'), " +
			"    F, " +
			"    G, " +
			"    H)",
	}),
		"the two ends are linear simplicial maps by AlgebraMapIsModuleMap and "+
			"H a simplicial homotopy by definition; each H(n, j) is a ring map "+
			"fixing the constants, linear as in PolynomialAlgebraSimplicialModule"),
})}

// PolynomialAlgebraKan — in a universe for R, the simplicial set of a
// polynomial simplicial algebra is a Kan complex.
var PolynomialAlgebraKan = polynomialAlgebraKanThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraKan",
	Key:  "prop_d98dd1f0fc56bf38",
	Reading: "In dimension 1 a horn is one vertex y, filled by the degenerate edge " +
		"s(0, 0)(y); above that it is Moore's theorem for the underlying simplicial " +
		"module, which reads the additive group of the algebras and no product.",
	Deps: []registry.EntryLike{
		PolynomialAlgebraSimplicialModule,
		simplicial_module.HornFillerExists,
		kan_complex.KanComplex,
	},
	Build: family.Card(PolynomialSimplicialAlgebra.Statement(Statement{
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "kan_complex(polynomial_simplicial_set(R, X, d, s))",
	}),
		"HornFillerExists, Moore's theorem for a simplicial module, at the simplicial module "+
			"PolynomialAlgebraSimplicialModule gives; only the additive group of the algebras is used"),
})}

// ---------------------------------------------------------------------------
// The augmentation in every degree
// ---------------------------------------------------------------------------

// AugmentationAtFaceIndependent — the augmentation in degree n after any
// face out of degree n + 1 is the augmentation in degree n + 1.
var AugmentationAtFaceIndependent = augmentationAtFaceIndependentThm{family.Add(registry.ProofEntry{
	Name: "AugmentationAtFaceIndependent",
	Key:  "prop_427b741ca139f14a",
	Reading: "No universe hypothesis and no ring law: it holds for any simplicial set with " +
		"ε coequalizing d_0 and d_1 in degree 1, the face identities and that conjunct being " +
		"all that is read. At n = 0 the statement for i = 1 is that coequalizing conjunct itself.",
	Deps: []registry.EntryLike{
		AugmentedPolynomialAlgebra,
		AugmentationAtDef,
		PolynomialSimplicialAlgebra,
		simplicial_set.SimplicialSet,
		simplicial_set.FaceFace,
		simplicial_set.FaceIn,
	},
	Build: family.Card(AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀n i:num. ∀u:U.",
		Hypotheses: []string{
			"i ≤ n + 1",
			"u ∈ universe_algebra(R, X(n + 1))",
		},
		Conclusion: "augmentation_at(d, ε, n, d(n + 1, i, u)) = augmentation_at(d, ε, n + 1, u)",
	}),
		"induct on n, keeping i and u universally quantified. At n = 0, i = 0 is AugmentationAtDef "+
			"and i = 1 is ε d_0 = ε d_1. At n + 1 and i = 0 it is AugmentationAtDef; for i = k + 1, "+
			"d_0 d_{k+1} = d_k d_0 on degree n + 2 (FaceFace), so the left side is augmentation_at(d, "+
			"ε, n, d(n + 1, k, d(n + 2, 0, u))), which the induction hypothesis at d(n + 2, 0, u) ∈ "+
			"universe_algebra(R, X(n + 1)) (FaceIn) turns into the right side"),
})}

// AugmentationAtHom — the augmentation in degree n is a ring map from the
// free algebra on X(n) to S carrying each constant a to f(a).
var AugmentationAtHom = augmentationAtHomThm{family.Add(registry.ProofEntry{
	Name: "AugmentationAtHom",
	Key:  "prop_9de352ceabac53cf",
	Reading: "No universe hypothesis: the faces are ring maps fixing the constants by the " +
		"definition of a polynomial simplicial algebra, and composites of ring maps are ring " +
		"maps. The ring d(n + 1, 0) lands in and the ring augmentation_at(d, ε, n) starts " +
		"from are literally one record, universe_algebra_ring(R, X(n)); a constant passes the " +
		"face unchanged because universe_algebra_homomorphism is the algebra map at φ = λa. a.",
	Deps: []registry.EntryLike{
		AugmentedPolynomialAlgebra,
		AugmentationAtDef,
		PolynomialSimplicialAlgebra,
		UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
	},
	Build: family.Card(
		AugmentedPolynomialAlgebra.Statement(
			"∀n:num. "+
				"    ring_homomorphism(restrict_ring(universe_algebra_ring(R, X(n)), universe_algebra(R, X(n))), "+
				"        S, "+
				"        augmentation_at(d, ε, n)) ∧ "+
				"    (∀a:A. a ∈ R.carrier ⇒ augmentation_at(d, ε, n, universe_algebra_const(R, a)) = f(a))"),
		"induct on n with AugmentationAtDef. At 0 both conjuncts are conjuncts of the "+
			"augmentation. At n + 1 the map is the augmentation in degree n after d(n + 1, 0), a "+
			"ring map of the free algebras fixing the constants (FreeAlgebraHomomorphismDef), so "+
			"the composite keeps the sum, the product and the one and lands in S (MapIn, MapAdd, "+
			"MapMul, MapOne), and a constant passes the face unchanged to the degree-n case"),
})}

// AugmentedAlongRingMap — an augmented polynomial simplicial algebra over
// the R-algebra S is augmented over every ring T it reaches through a
// ring map g out of S, its structure map and augmentation followed by g.
var AugmentedAlongRingMap = augmentedAlongRingMapThm{family.Add(registry.ProofEntry{
	Name: "AugmentedAlongRingMap",
	Key:  "prop_3b805c7264c56032",
	Reading: "This is how coefficients in a module over T enter: the differential complex at T and g " +
		"∘ ε (algebra/cotangent/cotangent_complex) is L ⊗ N for N a module over T through g, and every " +
		"law of that complex holds there by this instance. No universe hypothesis is read, only the " +
		"closure of ring_homomorphism under composition; if S is the zero ring, g forces T to be zero too.",
	Deps: []registry.EntryLike{
		AugmentedPolynomialAlgebra,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.Target,
	},
	Build: family.Card(AugmentedPolynomialAlgebra.Statement(Statement{
		Binders: "∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "augmented_polynomial_algebra(R, X, d, s, T, λa:A. g(f(a)), λu:U. g(ε(u)))",
	}),
		"unfold AugmentedPolynomialAlgebra: the composites g ∘ f and g ∘ ε are ring maps "+
			"(RingHomomorphism; MapIn, MapAdd, MapMul, MapOne of each, the rings at the ends "+
			"from the two maps, Target), a constant goes to g(f(a)), and g keeps ε d_0 = ε d_1"),
})}

// ---------------------------------------------------------------------------
// The constant algebra
// ---------------------------------------------------------------------------

// ConstantPolynomialAlgebra — in a universe for a commutative ring R, the
// free algebra on one name set W in every degree, with every face and
// degeneracy the identity, is a polynomial simplicial algebra.
var ConstantPolynomialAlgebra = constantPolynomialAlgebraThm{family.Add(registry.ProofEntry{
	Name: "ConstantPolynomialAlgebra",
	Key:  "prop_f94dc3a64cb635e2",
	Reading: "For W = ∅ every degree is the algebra of the constants, and " +
		"over the zero ring every degree is one point; both are polynomial " +
		"simplicial algebras, with every face and degeneracy the identity.",
	Deps: []registry.EntryLike{
		PolynomialSimplicialAlgebra,
		UniverseEmbeddingHost,
		UniverseAlgebraDef,
		UniverseAlgebraRingDef,
		UniverseAlgebraHomomorphismDef,
		UniverseAlgebraVarDef,
		simplicial_set.ConstantSimplicialSet,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "polynomial_simplicial_algebra(R, " +
			"    λn:num. W, " +
			"    λn:num. λi:num. λu:U. u, " +
			"    λn:num. λi:num. λu:U. u)",
	},
		"the constant simplicial set on universe_algebra(R, W) (ConstantSimplicialSet); "+
			"the free algebra is a commutative ring (FreeAlgebraCommRingOn at "+
			"UniverseEmbeddingHost), so the identity is a ring homomorphism of it "+
			"(RingHomomorphism) and fixes the constants; the identity keeps the variables of W"),
})}

// ConstantPolynomialResolution — in a universe for a commutative ring R,
// the constant algebra on W resolves its own free algebra through the
// identity, the constants as the structure map.
var ConstantPolynomialResolution = constantPolynomialResolutionThm{family.Add(registry.ProofEntry{
	Name: "ConstantPolynomialResolution",
	Key:  "prop_60a28abe424ff923",
	Reading: "The augmentation is the identity of universe_algebra(R, W), an " +
		"algebra over R through the constants. The Moore complex is the free algebra " +
		"in degree 0 and {0} above it, so its boundaries in degree 0 are {0} and the " +
		"degree-0 conjunct says ε(x) = ε(y) ⇔ x = y, which the identity satisfies.",
	Deps: []registry.EntryLike{
		PolynomialResolution,
		AugmentedPolynomialAlgebra,
		ConstantPolynomialAlgebra,
		PolynomialAlgebraSimplicialModule,
		UniverseEmbeddingHost,
		UniverseAlgebraConstDef,
		UniverseAlgebraRingDef,
		simplicial_module.ConstantAcyclicAugmentation,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraModuleOn,
		free_algebra.FreeAlgebraCommRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "polynomial_resolution(R, " +
			"    λn:num. W, " +
			"    λn:num. λi:num. λu:U. u, " +
			"    λn:num. λi:num. λu:U. u, " +
			"    universe_algebra_ring(R, W), " +
			"    universe_algebra_const(R), " +
			"    λu:U. u)",
	},
		"ConstantPolynomialAlgebra; the constants are a ring map into the free algebra "+
			"(FreeAlgebraConstHom) and the identity a ring map of it, agreeing on the "+
			"constants, and ε d_0 = ε d_1 holds as both faces are the identity; acyclicity is "+
			"ConstantAcyclicAugmentation at the module and submodule of FreeAlgebraModuleOn, "+
			"the carrier of universe_algebra_ring(R, W) being universe_algebra(R, W)"),
})}
