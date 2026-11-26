// cotangent_complex.go — the cotangent complex of an algebra S over a
// ring R through the structure map f, with coefficients in a module N
// over an algebra T over S through the ring map g: the complex of
// differentials of the standard resolution of S over R, its augmentation
// onto S followed by g, whose homology in degree n is the André–Quillen
// homology D_n(S/R, N); and the cochain complex of functions on the names
// of the standard resolution with values in N, under the transposed
// Jacobians, whose cohomology is D^n(S/R, N). A module over S itself is
// the case T = S, g the identity. The complex is a chain complex and its
// homology modules over T; any polynomial resolution of S computes it up
// to chain homotopy equivalence; an algebra map over R induces a chain
// map, functorially, an isomorphism a chain isomorphism even between
// rings on different types, a linear map of coefficients a chain map,
// coefficients over a ring T' that T maps to the same homology as their
// restriction to T, and a change of the base ring along a tower
// R → S → T a chain map from the complex of T over R to that of T over S. In degree 0 the homology
// is the module of Kähler differentials, tensored with the coefficients.
// With coefficients in T itself the complex is based by the identity on
// the names; its dual with coefficients in N is the cochain complex, and
// the duals of the two maps of a tower are the transposed Jacobians.

package cotangent_complex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/resolution_comparison"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/kaehler"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The cotangent complex and its homology
// ---------------------------------------------------------------------------

// CotangentComplexDef — `cotangent_complex(R, S, f, T, g, N)`: the
// cotangent complex of S over R through f with coefficients in the
// module N over T, an algebra over S through g, L_{S/R} ⊗_S N — the
// differential complex of the standard resolution of S over R, its
// augmentation onto S followed by g, a complex over T.
var CotangentComplexDef = cotangentComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentComplexDef",
	Key:   "prop_76db0c62209f92fb",
	Const: "cotangent_complex",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"complex_ops(C, U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C). ∀N:module_ops(C, D). " +
			"    cotangent_complex(R, S, f, T, g, N) = " +
			"    differential_complex(R, " +
			"        standard_names(R, S), " +
			"        standard_face(R, S, f), " +
			"        T, " +
			"        λu:U. g(standard_eps(R, S, f, u)), " +
			"        N)",
	},
	Reading: "A statement over one ring map f and a module N over S itself passes (R, S, " +
		"f, S, λx:B. x, N); with a ring map g into T the coefficients are extended along g, so " +
		"the complexes of a tower of rings with coefficients in one module over its top ring " +
		"are all complexes over that ring. The host type U is a letter of the constant that no " +
		"argument carries: a statement fixes it by its hypothesis cotangent_universe(R, " +
		"𝕌⟨A:U⟩) ∧ cotangent_universe(S, 𝕌⟨A:U⟩), under which the standard resolution's free " +
		"algebras, the tags of S's elements and the augmentation's preimages are what they are " +
		"chosen to be, and a text where nothing fixes it writes cotangent_complex⟨U:U⟩.",
	Deps: []registry.EntryLike{DifferentialComplexDef},
})}

// CotangentHomologyDef — `cotangent_homology(R, S, f, T, g, N, n)`: the
// André–Quillen homology D_n(S/R, N) of S over R with coefficients in
// the module N over T, the homology of the cotangent complex in degree n
// as a module over T.
var CotangentHomologyDef = cotangentHomologyDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentHomologyDef",
	Key:   "prop_fd8130931ede1f76",
	Const: "cotangent_homology",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"num → " +
		"module_ops(C, set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"    cotangent_homology(R, S, f, T, g, N, n) = " +
			"    homology_module(cotangent_complex(R, S, f, T, g, N), n)",
	},
	Reading: "A module record: its carrier is the set of classes " +
		"homology(cotangent_complex(R, S, f, T, g, N), n), its zero the class of the " +
		"boundaries, so D_n(S/R, N) = 0 is the carrier being the one class. A module over S " +
		"itself is the case T = S, g = λx:B. x; the letter U is fixed as cotangent_complex's is.",
	Deps: []registry.EntryLike{CotangentComplexDef},
})}

// ---------------------------------------------------------------------------
// The cotangent cochain complex and its cohomology
// ---------------------------------------------------------------------------

// CotangentCochainDef — `cotangent_cochain(R, S, f, T, g, N)`: the
// cochain complex of the derivations of the standard resolution of S
// over R into the module N over T, Hom_T(L_{S/R} ⊗_S T, N) — in degree n
// the functions on the names of degree n with values in N, zero off
// them, under N's operations pointwise, and as the coboundary out of
// degree n the alternating sum over i ≤ n + 1 of the transposed
// Jacobians of the faces d(n + 1, i), their entries carried into T by
// the augmentation read in degree n followed by g.
var CotangentCochainDef = cotangentCochainDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentCochainDef",
	Key:   "prop_d522a600d0730cf6",
	Const: "cotangent_cochain",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"complex_ops(C, U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C). ∀N:module_ops(C, D). " +
			"cotangent_cochain(R, S, f, T, g, N) = pack_complex(fun_add(N.add), fun_zero(N.zero), fun_neg(N.neg), fun_smul(N.smul), " +
			"λn:num. fun_module(N.zero, N.carrier, standard_names(R, S, n)), " +
			"λn:num. λw:(U → D). module_sum(fun_add(N.add), fun_zero(N.zero), 0 .. n + 1, " +
			"λi:num. fun_smul(N.smul, alternating_sign(T.one, T.neg, i), " +
			"free_algebra_jacobian_transpose(" + hostEmbedding + ", " + hostEmbedding + ", R, R, standard_names(R, S, n + 1), standard_names(R, S, n), " +
			"standard_face(R, S, f, n + 1, i), λu:U. g(standard_to_base(R, S, f, n, u)), N, w))))",
	},
	Reading: "A function w on the names of degree n stands for the derivation of the free " +
		"algebra on them into N that takes the variable of x to w(x); any support is allowed, the " +
		"names being a basis. The coboundary is w after the boundary of the cotangent complex out of " +
		"degree n + 1, the transposed Jacobian of a face reading w against the same entries the face's " +
		"Jacobian scales by, so the cochain complex is Hom_T of the cotangent complex into N. A module " +
		"over S itself passes T = S and g = λx:B. x; the letter U is fixed as cotangent_complex's is.",
})}

// CotangentCohomologyDef — `cotangent_cohomology(R, S, f, T, g, N, n)`:
// the André–Quillen cohomology D^n(S/R, N) of S over R with coefficients
// in the module N over T, the cohomology of the cotangent cochain complex
// in degree n as a module over T.
var CotangentCohomologyDef = cotangentCohomologyDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentCohomologyDef",
	Key:   "prop_8134f0be9e17f2e4",
	Const: "cotangent_cohomology",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"num → " +
		"module_ops(C, set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"    cotangent_cohomology(R, S, f, T, g, N, n) = " +
			"    cohomology_module(cotangent_cochain(R, S, f, T, g, N), n)",
	},
	Reading: "A module record whose carrier is the set of classes " +
		"cohomology(cotangent_cochain(R, S, f, T, g, N), n); in degree 0 the coboundaries " +
		"are the zero alone, so D^0(S/R, N) is the cocycles of degree 0 themselves.",
	Deps: []registry.EntryLike{CotangentCochainDef},
})}

// ---------------------------------------------------------------------------
// The complex, its homology and its independence of the resolution
// ---------------------------------------------------------------------------

// CotangentChainComplex — in a universe for R and for S, the cotangent
// complex of S over R with coefficients in a module N over T is a chain
// complex over T.
var CotangentChainComplex = cotangentChainComplexThm{family.Add(registry.ProofEntry{
	Name: "CotangentChainComplex",
	Key:  "prop_b68ca23bf6e33aaa",
	Deps: []registry.EntryLike{
		CotangentComplexDef,
		DifferentialComplexChain,
		simplicial_ring.AugmentedAlongRingMap,
		standard_resolution.StandardPolynomialAlgebra,
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
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "chain_complex(T, cotangent_complex⟨U:U⟩(R, S, f, T, g, N))",
	},
		"the standard resolution is an augmented polynomial simplicial algebra over S "+
			"(StandardPolynomialAlgebra), followed by g one over T (AugmentedAlongRingMap); "+
			"DifferentialComplexChain there, after CotangentComplexDef"),
})}

// CotangentScalarBased — with coefficients in T itself, the cotangent
// complex is based by the identity on the standard names.
var CotangentScalarBased = cotangentScalarBasedThm{family.Add(registry.ProofEntry{
	Name: "CotangentScalarBased",
	Key:  "prop_3bfe6d37fc827394",
	Reading: "One card covers the three complexes of a tower R → S → T with coefficients " +
		"in T: L_{S/R} ⊗ T at (R, S, f, T, g), L_{T/R} ⊗ T at (R, T, λa:A. g(f(a)), T, λc:C. " +
		"c) and L_{T/S} ⊗ T at (S, T, g, T, λc:C. c). No module hypothesis is stated: T is a " +
		"commutative ring because g is a ring map, and so a module over itself.",
	Deps: []registry.EntryLike{
		CotangentChainComplex,
		CotangentComplexDef,
		DifferentialComplexDef,
		DifferentialTermsDef,
		free_complex_duality.BasedChainComplex,
		free_module.FreeModuleRecordDef,
		free_module.FreeModuleOn,
		chain_complex.ComplexModuleDef,
		module_homomorphism.HomIdentity,
		module.RegularModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "based_chain_complex(T, " +
			"    cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"    standard_names(R, S), " +
			"    λn:num. λa:(U → C). a, " +
			"    λn:num. λa:(U → C). a)",
	},
		"T is a commutative ring (g's ring_homomorphism carries it) and so a module over itself "+
			"(RegularModuleOn); CotangentChainComplex at that module makes the complex a chain "+
			"complex. Its degree n is finite_supp(T.zero, T.carrier, standard_names(R, S, n)) under "+
			"fun_add, fun_zero, fun_neg and fun_smul (CotangentComplexDef, DifferentialComplexDef, "+
			"DifferentialTermsDef, ComplexModuleDef), which is free_module_record(T, "+
			"standard_names(R, S, n)) field by field (FreeModuleRecordDef); so the identity is "+
			"linear both ways (HomIdentity at FreeModuleOn) and inverse to itself"),
})}

// CotangentHomologyModuleOn — in a universe for R and for S, each
// André–Quillen homology D_n(S/R, N) is a module over T.
var CotangentHomologyModuleOn = cotangentHomologyModuleOnThm{family.Add(registry.ProofEntry{
	Name: "CotangentHomologyModuleOn",
	Key:  "prop_b401b4cba25a70c2",
	Deps: []registry.EntryLike{
		CotangentHomologyDef,
		CotangentChainComplex,
		chain_complex.HomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "module_on(T, cotangent_homology⟨U:U⟩(R, S, f, T, g, N, n))",
	},
		"HomologyModuleOn at CotangentChainComplex, after CotangentHomologyDef"),
})}

// CotangentResolutionIndependence — in a universe for R and for S, every
// polynomial resolution of S over R maps to the standard resolution over
// the identity of S, and the Jacobians of that map are a chain homotopy
// equivalence from its differential complex to the cotangent complex,
// with coefficients in any module over any T that S maps to.
var CotangentResolutionIndependence = cotangentResolutionIndependenceThm{family.Add(registry.ProofEntry{
	Name: "CotangentResolutionIndependence",
	Key:  "prop_207280d82e013961",
	Reading: "X is any polynomial resolution: its generators are closed under the degeneracies, as " +
		"polynomial_simplicial_algebra asks, and nothing else of its shape is read. The homology of " +
		"its differential complex is therefore D_n(S/R, N) (ChainHomotopyEquivalenceQuasiIsomorphism), " +
		"which is how a small resolution computes the cotangent complex. The same f in both " +
		"resolutions is forced by covering; the standard resolution needs universes for R and S.",
	Deps: []registry.EntryLike{
		CotangentComplexDef,
		ResolutionMapChainHomotopyEquivalence,
		resolution_comparison.ComparisonMapExists,
		standard_resolution.StandardResolution,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.Target,
		simplicial_ring.PolynomialResolution,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀ε:(U → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
		},
		Conclusion: "∃F:(num → U → U). " +
			"    simplicial_algebra_map(R, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        standard_names(R, S), " +
			"        standard_face(R, S, f), " +
			"        standard_degeneracy(R), " +
			"        F) ∧ " +
			"    (∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ standard_eps(R, S, f, F(0, u)) = ε(u)) ∧ " +
			"    (∃G:(num → (U → D) → U → D). " +
			"        chain_homotopy_equivalence(T, " +
			"            differential_complex(R, X, d, T, λu:U. g(ε(u)), N), " +
			"            cotangent_complex(R, S, f, T, g, N), " +
			"            differential_map(R, " +
			"                X, " +
			"                standard_names(R, S), " +
			"                standard_face(R, S, f), " +
			"                λu:U. g(standard_eps(R, S, f, u)), " +
			"                F, " +
			"                N), " +
			"            G))",
	},
		"ComparisonMapExists from X into the standard resolution, a resolution of S "+
			"(StandardResolution), at the identity of S (RingHomIdentity, S a ring by Target of f), gives "+
			"F; ResolutionMapChainHomotopyEquivalence at F, X and the standard resolution both resolutions "+
			"of S, gives the equivalence, the target being cotangent_complex by CotangentComplexDef"),
})}

// ---------------------------------------------------------------------------
// Functoriality
// ---------------------------------------------------------------------------

// CotangentFunctorialMap — in a universe for R, S and S', an algebra map
// φ from S to S' over R induces, by the Jacobians of the map of standard
// resolutions, a chain map from the cotangent complex of S to that of S',
// with coefficients in a module N over T through g out of S'.
var CotangentFunctorialMap = cotangentFunctorialMapThm{family.Add(registry.ProofEntry{
	Name: "CotangentFunctorialMap",
	Key:  "prop_e09014d6997912d5",
	Reading: "The coefficients of S reach T through φ followed by g. Over a tower R → S → " +
		"T through f and g, with N a module over T, the instance S' = T, f' = λa:A. g(f(a)), φ " +
		"= g and the identity of T as coefficient map is the map L_{S/R} ⊗_S N → L_{T/R} ⊗_T N " +
		"of the transitivity triangle. φ need agree with the structure maps only on R's carrier.",
	Deps: []registry.EntryLike{
		CotangentComplexDef,
		DifferentialMapChainMap,
		simplicial_ring.AugmentedAlongRingMap,
		standard_resolution.StandardMapAlgebraMap,
		standard_resolution.StandardMapAugmentation,
		standard_resolution.StandardPolynomialAlgebra,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀S':ring_ops(E). " +
			"∀f':(A → E). " +
			"∀φ:(B → E). " +
			"∀T:ring_ops(C). " +
			"∀g:(E → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(R, S', f')",
			"∀a:A. a ∈ R.carrier ⇒ φ(f(a)) = f'(a)",
			"ring_homomorphism(S', T, g)",
			"module_on(T, N)",
			"ring_homomorphism(S, S', φ)",
		},
		Conclusion: "chain_map(T, " +
			"    cotangent_complex(R, S, f, T, λy:B. g(φ(y)), N), " +
			"    cotangent_complex(R, S', f', T, g, N), " +
			"    differential_map(R, " +
			"        standard_names(R, S), " +
			"        standard_names(R, S'), " +
			"        standard_face(R, S', f'), " +
			"        λu:U. g(standard_eps(R, S', f', u)), " +
			"        standard_map(R, S, S', φ), " +
			"        N))",
	},
		"standard_map(R, S, S', φ) is a simplicial algebra map of the standard resolutions "+
			"(StandardMapAlgebraMap) carrying the augmentation of S' back to φ after the "+
			"augmentation of S (StandardMapAugmentation); followed by g both standard resolutions "+
			"are augmented over T (StandardPolynomialAlgebra, AugmentedAlongRingMap), the map "+
			"covering the identity of T, so DifferentialMapChainMap, after CotangentComplexDef"),
})}

// CotangentFunctorialIdentity — the identity of S induces the identity on
// its cotangent complex.
var CotangentFunctorialIdentity = cotangentFunctorialIdentityThm{family.Add(registry.ProofEntry{
	Name: "CotangentFunctorialIdentity",
	Key:  "prop_f7e2a304402561db",
	Deps: []registry.EntryLike{
		DifferentialMapIdentity,
		DifferentialMapDef,
		standard_resolution.StandardMapIdentity,
		standard_resolution.StandardPolynomialAlgebra,
		simplicial_ring.AugmentedAlongRingMap,
		partial_derivative.JacobianCongruence,
		simplicial_ring.UniverseAlgebraVarDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"∀u:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"u ∈ differential_terms(standard_names(R, S), N, n)",
		},
		Conclusion: "differential_map(R, " +
			"    standard_names(R, S), " +
			"    standard_names(R, S), " +
			"    standard_face(R, S, f), " +
			"    λv:U. g(standard_eps(R, S, f, v)), " +
			"    standard_map(R, S, S, λy:B. y), " +
			"    N, " +
			"    n, " +
			"    u) = " +
			"u",
	},
		"standard_map at the identity is the identity on the simplices "+
			"(StandardMapIdentity), so on the variables of the names, and the Jacobian is that "+
			"of the identity (JacobianCongruence); DifferentialMapIdentity at the standard "+
			"resolution followed into T (StandardPolynomialAlgebra, AugmentedAlongRingMap)"),
})}

// CotangentFunctorialCompose — the map induced by a composite of algebra
// maps over R is the composite of the induced maps.
var CotangentFunctorialCompose = cotangentFunctorialComposeThm{family.Add(registry.ProofEntry{
	Name: "CotangentFunctorialCompose",
	Key:  "prop_3744093ca3edd30e",
	Reading: "The middle complex is augmented by g ∘ φ' ∘ " +
		"standard_eps(S'), as spelled, not by g ∘ standard_eps(S').",
	Deps: []registry.EntryLike{
		DifferentialMapCompose,
		DifferentialMapDef,
		standard_resolution.StandardMapCompose,
		standard_resolution.StandardMapAlgebraMap,
		standard_resolution.StandardMapAugmentation,
		standard_resolution.StandardPolynomialAlgebra,
		simplicial_ring.AugmentedAlongRingMap,
		partial_derivative.JacobianCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀S':ring_ops(E). " +
			"∀f':(A → E). " +
			"∀φ:(B → E). " +
			"∀S'':ring_ops(I). " +
			"∀f'':(A → I). " +
			"∀φ':(E → I). " +
			"∀T:ring_ops(C). " +
			"∀g:(I → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"∀u:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"cotangent_universe(S'', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(R, S', f')",
			"ring_homomorphism(R, S'', f'')",
			"ring_homomorphism(S, S', φ)",
			"ring_homomorphism(S', S'', φ')",
			"∀a:A. a ∈ R.carrier ⇒ φ(f(a)) = f'(a)",
			"∀a:A. a ∈ R.carrier ⇒ φ'(f'(a)) = f''(a)",
			"ring_homomorphism(S'', T, g)",
			"module_on(T, N)",
			"u ∈ differential_terms(standard_names(R, S), N, n)",
		},
		Conclusion: "differential_map(R, " +
			"    standard_names(R, S), " +
			"    standard_names(R, S''), " +
			"    standard_face(R, S'', f''), " +
			"    λv:U. g(standard_eps(R, S'', f'', v)), " +
			"    standard_map(R, S, S'', λy:B. φ'(φ(y))), " +
			"    N, " +
			"    n, " +
			"    u) = " +
			"differential_map(R, " +
			"    standard_names(R, S'), " +
			"    standard_names(R, S''), " +
			"    standard_face(R, S'', f''), " +
			"    λv:U. g(standard_eps(R, S'', f'', v)), " +
			"    standard_map(R, S', S'', φ'), " +
			"    N, " +
			"    n, " +
			"    differential_map(R, " +
			"        standard_names(R, S), " +
			"        standard_names(R, S'), " +
			"        standard_face(R, S', f'), " +
			"        λv:U. g(φ'(standard_eps(R, S', f', v))), " +
			"        standard_map(R, S, S', φ), " +
			"        N, " +
			"        n, " +
			"        u))",
	},
		"standard_map of the composite is the composite of the standard_maps on the simplices "+
			"(StandardMapCompose), so on the variables (JacobianCongruence); DifferentialMapCompose "+
			"at the two simplicial algebra maps (StandardMapAlgebraMap), the middle resolution "+
			"augmented over T through g ∘ φ' (StandardPolynomialAlgebra, AugmentedAlongRingMap) and "+
			"standard_map(R, S', S'', φ') covering the identity of T there (StandardMapAugmentation)"),
})}

// CotangentIsomorphismInvariance — in a universe for R, S and S', an
// isomorphism φ of algebras over R from S to S', two rings on different
// types, induces a chain isomorphism of their cotangent complexes and
// isomorphisms D_n(S/R, N) ≅ D_n(S'/R, N) in every degree.
var CotangentIsomorphismInvariance = cotangentIsomorphismInvarianceThm{family.Add(registry.ProofEntry{
	Name: "CotangentIsomorphismInvariance",
	Key:  "prop_d490ffc70d3f88c2",
	Reading: "S and S' are on different types, both with room in the one host, so an algebra given " +
		"on another type — a quotient presented as a hypersurface, a field adjunction, a localization " +
		"— carries its André–Quillen homology across this isomorphism. The isomorphism is over R: φ ∘ " +
		"f = f' on R's carrier. With ψ = inverse_on(S.carrier, φ) the source coefficient map g ∘ φ ∘ ψ " +
		"agrees with g only on S'.carrier, so the two complexes are identified through " +
		"JacobianCongruence on terms, all chain_isomorphism reads; standard_map(R, S, S, ψ ∘ φ) is the " +
		"identity on standard_terms by induction from StandardMapDef, inverse_on landing in the carrier.",
	Deps: []registry.EntryLike{
		CotangentFunctorialMap,
		CotangentFunctorialCompose,
		CotangentFunctorialIdentity,
		CotangentChainComplex,
		CotangentHomologyDef,
		standard_resolution.StandardMapCompose,
		standard_resolution.StandardMapIdentity,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.IsomorphismInverse,
		chain_complex.ChainIsomorphismDef,
		chain_complex.ChainIsomorphismQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀S':ring_ops(E). " +
			"∀f':(A → E). " +
			"∀φ:(B → E). " +
			"∀T:ring_ops(C). " +
			"∀g:(E → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(R, S', f')",
			"∀a:A. a ∈ R.carrier ⇒ φ(f(a)) = f'(a)",
			"ring_homomorphism(S', T, g)",
			"module_on(T, N)",
			"ring_isomorphism(S, S', φ)",
		},
		Conclusion: "chain_isomorphism(T, " +
			"    cotangent_complex(R, S, f, T, λy:B. g(φ(y)), N), " +
			"    cotangent_complex(R, S', f', T, g, N), " +
			"    differential_map(R, " +
			"        standard_names(R, S), " +
			"        standard_names(R, S'), " +
			"        standard_face(R, S', f'), " +
			"        λu:U. g(standard_eps(R, S', f', u)), " +
			"        standard_map(R, S, S', φ), " +
			"        N)) ∧ " +
			"(∀n:num. " +
			"    module_isomorphism(T, " +
			"        cotangent_homology(R, S, f, T, λy:B. g(φ(y)), N, n), " +
			"        cotangent_homology(R, S', f', T, g, N, n), " +
			"        homology_map(cotangent_complex(R, S', f', T, g, N), " +
			"            differential_map(R, " +
			"                standard_names(R, S), " +
			"                standard_names(R, S'), " +
			"                standard_face(R, S', f'), " +
			"                λu:U. g(standard_eps(R, S', f', u)), " +
			"                standard_map(R, S, S', φ), " +
			"                N), " +
			"            n)))",
	},
		"the inverse inverse_on(S.carrier, φ) is a ring isomorphism over R (IsomorphismInverse); "+
			"CotangentFunctorialMap for φ and for it, and CotangentFunctorialCompose with "+
			"CotangentFunctorialIdentity, the composites being the identity on the carriers, which "+
			"is all standard_map reads (StandardMapCompose, StandardMapIdentity), make the two "+
			"induced maps inverse on the terms, so each is a module isomorphism in every degree "+
			"(ChainIsomorphismDef); ChainIsomorphismQuasiIsomorphism at CotangentChainComplex gives "+
			"the homology, unfolded by CotangentHomologyDef"),
})}

// CotangentCoefficientMap — in a universe for R and for S, a linear map k
// of modules over T induces, by composition, a chain map of the
// cotangent complexes with coefficients in them.
var CotangentCoefficientMap = cotangentCoefficientMapThm{family.Add(registry.ProofEntry{
	Name: "CotangentCoefficientMap",
	Key:  "prop_b0ea05ef7864d85d",
	Reading: "The index sets of the two Jacobian sums differ exactly at the " +
		"s where k kills u(s) ≠ 0; those terms are ε(…) • 0, so the sums agree.",
	Deps: []registry.EntryLike{
		CotangentComplexDef,
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialFaceDef,
		CotangentChainComplex,
		partial_derivative.FreeAlgebraJacobianDef,
		chain_complex.ChainMapDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module.ModuleSumSupport,
		function_module.FiniteSuppDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀N':module_ops(C, E). " +
			"∀k:(D → E).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"module_homomorphism(T, N, N', k)",
		},
		Conclusion: "chain_map(T, " +
			"    cotangent_complex(R, S, f, T, g, N), " +
			"    cotangent_complex(R, S, f, T, g, N'), " +
			"    λn:num. λu:(U → D). λx:U. k(u(x)))",
	},
		"k keeps N's zero, so k ∘ u is finitely supported on the names when u is "+
			"(FiniteSuppDef), and composing with k is linear pointwise; k commutes with each "+
			"Jacobian, a finite sum of scalars acting (HomSum, HomSmul), the index sets differing "+
			"only where the terms vanish (ModuleSumSupport), and so with the alternating sums"),
})}

// CotangentCoefficientRestriction — for a ring map k from T to T' and a
// module N' over T', the homology of the cotangent complex with
// coefficients in N' over T', through k after g, is the homology with
// coefficients in N' restricted to T along k: the same classes and the
// same zero in every degree.
var CotangentCoefficientRestriction = cotangentCoefficientRestrictionThm{family.Add(registry.ProofEntry{
	Name: "CotangentCoefficientRestriction",
	Reading: "No hypothesis on R, S, f or g and no universe: the two complexes have the " +
		"same terms and the same boundary map, the augmentation read through k after g being k " +
		"after the one read through g, since augmentation_at applies ε after the 0-th faces. k " +
		"a ring map is load-bearing for the signs and for module_on(T, N). Only the carriers " +
		"and the zeros agree: one homology module has T's scalars, the other those of T'.",
	Key: "prop_4dcceeed16be33e4",
	Deps: []registry.EntryLike{
		CotangentHomologyDef,
		CotangentComplexDef,
		DifferentialComplexDef,
		DifferentialTermsDef,
		DifferentialBoundaryDef,
		DifferentialFaceDef,
		simplicial_ring.AugmentationAtDef,
		partial_derivative.FreeAlgebraJacobianDef,
		simplicial_module.FaceBoundaryDef,
		chain_complex.HomologyModuleDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		module.ModuleOn,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapOne,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀T':ring_ops(E). " +
			"∀k:(C → E). " +
			"∀N':module_ops(E, D).",
		Hypotheses: []string{
			"ring_homomorphism(T, T', k)",
			"module_on(T', N')",
			"N = scalar_restriction(k, N')",
		},
		Conclusion: "module_on(T, N) ∧ " +
			"(∀n:num. " +
			"    cotangent_homology⟨U:U⟩(R, S, f, T', λy:B. k(g(y)), N', n).carrier = " +
			"    cotangent_homology(R, S, f, T, g, N, n).carrier ∧ " +
			"    cotangent_homology⟨U:U⟩(R, S, f, T', λy:B. k(g(y)), N', n).zero = " +
			"    cotangent_homology(R, S, f, T, g, N, n).zero)",
	},
		"unfold both homologies down to the Jacobians (CotangentHomologyDef, CotangentComplexDef, "+
			"DifferentialComplexDef, DifferentialTermsDef, DifferentialBoundaryDef, "+
			"DifferentialFaceDef, FreeAlgebraJacobianDef): the terms are the finitely supported "+
			"functions into N'.carrier on both sides; the augmentation read in degree n through k is "+
			"k after the one read through g, by induction on n (AugmentationAtDef), so every entry of "+
			"every Jacobian acts on N' as k of it on both sides; the signs alternating_sign(i) act "+
			"through k as alternating_sign(i) (FaceBoundaryDef, MapOne, k keeping negation). So the "+
			"two complexes have one boundary map in each degree, hence the same cycles and boundaries "+
			"(CyclesDef, BoundariesDef), and the homology modules the same cosets and the same zero "+
			"(HomologyModuleDef). N is a module over T because the module laws of N' hold at k's "+
			"values, k being additive, multiplicative and unital (ModuleOn, RingHomomorphism)"),
})}

// ---------------------------------------------------------------------------
// The cochain complex and its cohomology
// ---------------------------------------------------------------------------

// CotangentCochainComplex — in a universe for R and for S, the cotangent
// cochain complex of S over R with coefficients in a module N over T is a
// cochain complex over T.
var CotangentCochainComplex = cotangentCochainComplexThm{family.Add(registry.ProofEntry{
	Name: "CotangentCochainComplex",
	Key:  "prop_4d5c8691fe941f7b",
	Reading: "The terms are all functions on the names, with no " +
		"finiteness condition; each coboundary sum is still finite, because " +
		"Φ(var s) has finitely many nonzero partial derivatives and ε(0) = 0.",
	Deps: []registry.EntryLike{
		CotangentCochainDef,
		function_module.FunModuleOn,
		function_module.FunctionModuleDef,
		function_module.FunModuleDef,
		partial_derivative.JacobianTransposeHom,
		partial_derivative.JacobianTransposeCompose,
		partial_derivative.JacobianCongruence,
		standard_resolution.StandardFacesHom,
		standard_resolution.StandardToBaseHom,
		standard_resolution.StandardToBaseFaceIndependent,
		standard_resolution.StandardFaceFace,
		chain_complex.CochainComplex,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		ring_homomorphism.RingHomomorphism,
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
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "cochain_complex(T, cotangent_cochain⟨U:U⟩(R, S, f, T, g, N))",
	},
		"each term is a module (FunModuleOn); each transposed face is linear (JacobianTransposeHom "+
			"at a face, an algebra map by StandardFacesHom, and g after standard_to_base, a ring map by "+
			"StandardToBaseHom), so the alternating sum is (HomSum, HomSmul). Two coboundaries in a "+
			"row: JacobianTransposeCompose makes each product of transposes the transpose of a "+
			"composite face, the inner augmentation through StandardToBaseFaceIndependent, and the face "+
			"identity StandardFaceFace (JacobianCongruence) cancels the double alternating sum in pairs"),
})}

// CotangentDualAgreement — the dual of the cotangent complex with
// coefficients in T, taken with coefficients in N, is cotangent_cochain:
// the same terms, the same coboundary on them, the same cohomology
// modules.
var CotangentDualAgreement = cotangentDualAgreementThm{family.Add(registry.ProofEntry{
	Name: "CotangentDualAgreement",
	Key:  "prop_7bbccbe6650e7fe0",
	Reading: "The identity is therefore a cochain map both ways, and the identification on " +
		"cohomology is an equation of modules: a statement about the dual's cohomology is one about " +
		"D^n(S/R, N) as cotangent_cohomology names it. The coboundaries agree on the terms only, " +
		"which is all the cocycles, the coboundaries and a cochain map read. Over the zero ring T " +
		"every N is the zero module, and both complexes hold the one zero function in every degree.",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeLinear,
		partial_derivative.JacobianTransposeAgreement,
		CotangentComplexDef,
		CotangentCochainDef,
		CotangentCohomologyDef,
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialFaceDef,
		DifferentialTermsDef,
		free_complex_duality.FreeDualComplexDef,
		free_module.HomPrecomposeDef,
		free_module.FreeLiftDef,
		free_module.DeltaAtDef,
		simplicial_module.FaceBoundaryDef,
		standard_resolution.StandardToBaseDef,
		simplicial_ring.AugmentationAtDef,
		partial_derivative.FreeAlgebraJacobianDef,
		partial_derivative.FreeAlgebraJacobianTransposeDef,
		partial_derivative.JacobianCongruence,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
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
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "(∀n:num. " +
			"    free_dual_complex(T, " +
			"        N, " +
			"        cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"        standard_names(R, S), " +
			"        λn:num. λa:(U → C). a, " +
			"        λn:num. λa:(U → C). a).terms(n) = " +
			"    cotangent_cochain(R, S, f, T, g, N).terms(n)) ∧ " +
			"(∀n:num. ∀w:(U → D). " +
			"    w ∈ cotangent_cochain(R, S, f, T, g, N).terms(n) ⇒ " +
			"    free_dual_complex(T, " +
			"        N, " +
			"        cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"        standard_names(R, S), " +
			"        λn:num. λa:(U → C). a, " +
			"        λn:num. λa:(U → C). a).d(n)(w) = " +
			"    cotangent_cochain(R, S, f, T, g, N).d(n)(w)) ∧ " +
			"(∀n:num. " +
			"    cohomology_module(free_dual_complex(T, " +
			"            N, " +
			"            cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"            standard_names(R, S), " +
			"            λn:num. λa:(U → C). a, " +
			"            λn:num. λa:(U → C). a), " +
			"        n) = " +
			"    cotangent_cohomology(R, S, f, T, g, N, n))",
	},
		"both terms are fun_module(N.zero, N.carrier, standard_names(R, S, n)) and the operations "+
			"the same pointwise ones (FreeDualComplexDef, CotangentCochainDef). The dual's coboundary "+
			"transposes the boundary out of degree n + 1 with coefficients in T, the alternating sum "+
			"Σ_{i ≤ n + 1} (−1)^i of the face Jacobians (CotangentComplexDef, DifferentialBoundaryDef, "+
			"FaceBoundaryDef, DifferentialFaceDef); its transpose is the alternating sum of the "+
			"transposes (HomPrecomposeLinear's finite combination), each free_algebra_jacobian_transpose "+
			"with coefficients in N (JacobianTransposeAgreement), the augmentation in degree n read as g "+
			"after standard_to_base (StandardToBaseDef, AugmentationAtDef, JacobianCongruence) — "+
			"cotangent_cochain's coboundary on the terms. Equal operations and terms and coboundaries "+
			"equal on the terms give equal cocycles and coboundaries, hence equal cohomology modules "+
			"(CohomologyModuleDef, CocyclesDef, CoboundariesDef, CotangentCohomologyDef)"),
})}

// CotangentMapsDualAgreement — the duals of the map g induces and of the
// change of base are the transposed Jacobians, cochain maps between the
// cochain complexes.
var CotangentMapsDualAgreement = cotangentMapsDualAgreementThm{family.Add(registry.ProofEntry{
	Name: "CotangentMapsDualAgreement",
	Key:  "prop_fe205ba27f1ec9ee",
	Reading: "Over a tower R → S → T the map g induces runs L_{S/R} ⊗ T → L_{T/R} ⊗ T and " +
		"the change of base L_{T/R} ⊗ T → L_{T/S} ⊗ T, so their duals run from the cochain " +
		"complex of T over R to that of S over R and from the cochain complex of T over S to " +
		"that of T over R. The two transposes are those the cohomology sequence of the tower " +
		"is defined with (co_transitivity_right_map and co_transitivity_left_map), so the maps " +
		"of that sequence are the maps the duals induce on cohomology. The two equations of " +
		"maps are stated on the terms of the dual's source only, which is all cochain_map reads.",
	Deps: []registry.EntryLike{
		partial_derivative.JacobianTransposeAgreement,
		free_complex_duality.FreeDualCochainMap,
		free_complex_duality.FreeDualMapDef,
		free_module.HomPrecomposeDef,
		DifferentialMapDef,
		CotangentFunctorialMap,
		CotangentBaseChangeMap,
		CotangentScalarBased,
		CotangentDualAgreement,
		CotangentCochainComplex,
		standard_resolution.StandardToBaseDef,
		standard_resolution.StandardBaseChangeMap,
		standard_resolution.StandardBaseChangeAugmentation,
		simplicial_ring.AugmentationAtDef,
		partial_derivative.JacobianCongruence,
		chain_complex.CochainMapDef,
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
		Conclusion: "(∀m:num. ∀w:(U → D). " +
			"    w ∈ fun_module(N.zero, N.carrier, standard_names(R, T, m)) ⇒ " +
			"    free_dual_map(T, " +
			"        N, " +
			"        standard_names(R, S), " +
			"        «dualAgreementIdentityBasis», " +
			"        «dualAgreementIdentityBasis», " +
			"        λk:num. " +
			"            differential_map(R, " +
			"                standard_names(R, S), " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, λa:A. g(f(a))), " +
			"                λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"                standard_map(R, S, T, g), " +
			"                regular_module(T), " +
			"                k), " +
			"        m, " +
			"        w) = " +
			"    free_algebra_jacobian_transpose(universe_embedding(R), " +
			"        universe_embedding(R), " +
			"        R, " +
			"        R, " +
			"        standard_names(R, S, m), " +
			"        standard_names(R, T, m), " +
			"        standard_map(R, S, T, g, m), " +
			"        λu:U. standard_to_base(R, T, λa:A. g(f(a)), m, u), " +
			"        N, " +
			"        w)) ∧ " +
			"cochain_map(T, " +
			"    cotangent_cochain(R, T, λa:A. g(f(a)), T, λc:C. c, N), " +
			"    cotangent_cochain(R, S, f, T, g, N), " +
			"    λm:num. λw:(U → D). " +
			"        free_algebra_jacobian_transpose(universe_embedding(R), " +
			"            universe_embedding(R), " +
			"            R, " +
			"            R, " +
			"            standard_names(R, S, m), " +
			"            standard_names(R, T, m), " +
			"            standard_map(R, S, T, g, m), " +
			"            λu:U. standard_to_base(R, T, λa:A. g(f(a)), m, u), " +
			"            N, " +
			"            w)) ∧ " +
			"(∀m:num. ∀w:(U → D). " +
			"    w ∈ fun_module(N.zero, N.carrier, standard_names(S, T, m)) ⇒ " +
			"    free_dual_map(T, " +
			"        N, " +
			"        standard_names(R, T), " +
			"        «dualAgreementIdentityBasis», " +
			"        «dualAgreementIdentityBasis», " +
			"        λk:num. " +
			"            free_algebra_jacobian(universe_embedding(R), " +
			"                universe_embedding(S), " +
			"                R, " +
			"                S, " +
			"                standard_names(R, T, k), " +
			"                standard_names(S, T, k), " +
			"                standard_base_change(R, S, f, k), " +
			"                standard_to_base(S, T, g, k), " +
			"                regular_module(T)), " +
			"        m, " +
			"        w) = " +
			"    free_algebra_jacobian_transpose(universe_embedding(R), " +
			"        universe_embedding(S), " +
			"        R, " +
			"        S, " +
			"        standard_names(R, T, m), " +
			"        standard_names(S, T, m), " +
			"        standard_base_change(R, S, f, m), " +
			"        standard_to_base(S, T, g, m), " +
			"        N, " +
			"        w)) ∧ " +
			"cochain_map(T, " +
			"    cotangent_cochain(S, T, g, T, λc:C. c, N), " +
			"    cotangent_cochain(R, T, λa:A. g(f(a)), T, λc:C. c, N), " +
			"    λm:num. λw:(U → D). " +
			"        free_algebra_jacobian_transpose(universe_embedding(R), " +
			"            universe_embedding(S), " +
			"            R, " +
			"            S, " +
			"            standard_names(R, T, m), " +
			"            standard_names(S, T, m), " +
			"            standard_base_change(R, S, f, m), " +
			"            standard_to_base(S, T, g, m), " +
			"            N, " +
			"            w))",
		Abbrev: Abbrev{
			{Name: "dualAgreementIdentityBasis", Text: "(λn:num. λa:(U → C). a)"},
		},
	},
		"with identity bases free_dual_map is hom_precompose of the chain map (FreeDualMapDef, "+
			"HomPrecomposeDef). The map g induces is, with coefficients in T, the Jacobian of "+
			"standard_map(R, S, T, g, m) read through the augmentation of T over R in degree m "+
			"(DifferentialMapDef; CotangentFunctorialMap's chain map at S' = T, f' = λa:A. g(f(a)), φ "+
			"= g), and JacobianTransposeAgreement makes its transpose free_algebra_jacobian_transpose "+
			"with coefficients in N, the augmentation read as standard_to_base (StandardToBaseDef, "+
			"AugmentationAtDef, JacobianCongruence); the change of base likewise, its chain map the "+
			"Jacobian of standard_base_change(R, S, f, m) (CotangentBaseChangeMap with "+
			"StandardBaseChangeMap and StandardBaseChangeAugmentation). Each is a cochain map: the "+
			"dual of a chain map of based complexes is one (FreeDualCochainMap at "+
			"CotangentScalarBased), the duals are cotangent_cochain on the terms "+
			"(CotangentDualAgreement), the coboundary keeps the terms (CotangentCochainComplex), and "+
			"cochain_map reads a map and the coboundaries on the terms only (CochainMapDef)"),
})}

// CotangentCohomologyModuleOn — in a universe for R and for S, each
// André–Quillen cohomology D^n(S/R, N) is a module over T.
var CotangentCohomologyModuleOn = cotangentCohomologyModuleOnThm{family.Add(registry.ProofEntry{
	Name: "CotangentCohomologyModuleOn",
	Key:  "prop_291809fcf7f0845b",
	Deps: []registry.EntryLike{
		CotangentCohomologyDef,
		CotangentCochainComplex,
		chain_complex.CohomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "module_on(T, cotangent_cohomology⟨U:U⟩(R, S, f, T, g, N, n))",
	},
		"CohomologyModuleOn at CotangentCochainComplex, after CotangentCohomologyDef"),
})}

// CotangentCohomologyCoefficientLongExact — a short exact sequence of
// coefficient modules over T gives the long exact sequence
// 0 → D^0(S/R, N') → D^0(S/R, N) → D^0(S/R, N”) → D^1(S/R, N') → ….
var CotangentCohomologyCoefficientLongExact = cotangentCohomologyCoefficientLongExactThm{family.Add(registry.ProofEntry{
	Name: "CotangentCohomologyCoefficientLongExact",
	Key:  "prop_541c808409571e76",
	Reading: "Every map is named: composition with i and with p on cohomology, and the " +
		"coboundary-lifting connecting map of the sequence of cochain complexes; with the " +
		"maps quantified the sequence would say nothing. It is the long exact sequence of " +
		"D^n(S/R, −) in its coefficient variable, the module N over T read through g.",
	Deps: []registry.EntryLike{
		CotangentScalarBased,
		CotangentDualAgreement,
		CotangentCochainComplex,
		CotangentCohomologyDef,
		free_complex_duality.FreeDualCoefficientShortExact,
		chain_complex.ShortExactCochainComplexes,
		chain_complex.CochainMapDef,
		chain_complex.ExactComplexesDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.CoLongExactStart,
		chain_complex.CoLongExactMiddle,
		chain_complex.CoLongExactQuotient,
		chain_complex.CoLongExactSub,
		module_homomorphism.ShortExactModules,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N':module_ops(C, D). " +
			"∀N:module_ops(C, E). " +
			"∀N'':module_ops(C, F). " +
			"∀i:(D → E). " +
			"∀p:(E → F).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"short_exact_modules(T, N', N, N'', i, p)",
		},
		Conclusion: "injective_on(«coefficientCohomology»(N', 0).carrier, " +
			"    «coefficientInclusionMap»(0)) ∧ " +
			"(∀n:num. " +
			"    exact_at(«coefficientCohomology»(N'', n).zero, " +
			"        «coefficientCohomology»(N', n).carrier, " +
			"        «coefficientCohomology»(N, n).carrier, " +
			"        «coefficientInclusionMap»(n), " +
			"        «coefficientProjectionMap»(n))) ∧ " +
			"(∀n:num. " +
			"    exact_at(«coefficientCohomology»(N', n + 1).zero, " +
			"        «coefficientCohomology»(N, n).carrier, " +
			"        «coefficientCohomology»(N'', n).carrier, " +
			"        «coefficientProjectionMap»(n), " +
			"        «coefficientConnecting»(n))) ∧ " +
			"(∀n:num. " +
			"    exact_at(«coefficientCohomology»(N, n + 1).zero, " +
			"        «coefficientCohomology»(N'', n).carrier, " +
			"        «coefficientCohomology»(N', n + 1).carrier, " +
			"        «coefficientConnecting»(n), " +
			"        «coefficientInclusionMap»(n + 1)))",
		Abbrev: Abbrev{
			{Name: "coefficientInclusion", Text: "λm:num. λw:(U → D). λu:U. i(w(u))"},
			{Name: "coefficientProjection", Text: "λm:num. λw:(U → E). λu:U. p(w(u))"},
			{Name: "coefficientCohomology", Text: "cotangent_cohomology⟨U:U⟩(R, S, f, T, g)"},
			{Name: "coefficientInclusionMap", Text: "cohomology_map(cotangent_cochain(R, S, f, T, g, N), " +
				"    «coefficientInclusion»)"},
			{Name: "coefficientProjectionMap", Text: "cohomology_map(cotangent_cochain(R, S, f, T, g, N''), " +
				"    «coefficientProjection»)"},
			{Name: "coefficientConnecting", Text: "coconnecting_hom(cotangent_cochain(R, S, f, T, g, N'), " +
				"    cotangent_cochain(R, S, f, T, g, N), " +
				"    «coefficientInclusion», " +
				"    «coefficientProjection»)"},
		},
	},
		"the cotangent complex with coefficients in T is based by its names "+
			"(CotangentScalarBased), so the duals with coefficients N', N and N'' form a short exact "+
			"sequence of cochain complexes under composition with i and p "+
			"(FreeDualCoefficientShortExact). Each dual has the cotangent cochain complex's operations "+
			"and terms and its coboundary on the terms (CotangentDualAgreement), and short exactness "+
			"reads no more (ShortExactCochainComplexes, CochainMapDef, ExactComplexesDef), so 0 → "+
			"cotangent_cochain(…, N') → cotangent_cochain(…, N) → cotangent_cochain(…, N'') → 0 is "+
			"short exact. CoLongExactStart, CoLongExactMiddle, CoLongExactQuotient and CoLongExactSub "+
			"give the four clauses, the carriers and zeros of the cotangent cohomology modules being "+
			"the cohomology sets and their zero classes (CotangentCohomologyDef, CohomologyModuleDef)"),
})}

// ---------------------------------------------------------------------------
// Degree zero: the Kähler differentials
// ---------------------------------------------------------------------------

// CotangentDegreeZero — in a universe for R and for S, the André–Quillen
// homology in degree 0 with coefficients in S itself is the module of
// Kähler differentials of S over R.
var CotangentDegreeZero = cotangentDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "CotangentDegreeZero",
	Key:  "prop_616bc520ceb55e0e",
	Reading: "S is a module over itself, its sum and its product as the scaling; T = S " +
		"and g the identity. The isomorphism crosses types: the classes of functions on the " +
		"host against the classes of functions on S's type, the tag of an element of S " +
		"carried to the element. The boundary out of degree 1 sends δ_u to Σ_t ε(∂_t u) δ_t " +
		"− δ_{tag ε(u)}; the polynomials var(tag a) + var(tag b), var(tag a)·var(tag b) and " +
		"const(a) give the three kinds of Kähler relation up to sign. The relabelling needs " +
		"CarrierTagInjective, so cotangent_universe(S) is load-bearing; the zero ring and N " +
		"= 0 give one class on both sides, and at S = R with the identity both sides are 0.",
	Deps: []registry.EntryLike{
		CotangentHomologyDef,
		CotangentComplexDef,
		kaehler.KaehlerModuleDef,
		kaehler.KaehlerRelationsDef,
		kaehler.KaehlerModuleOn,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		partial_derivative.ChainRule,
		standard_resolution.StandardNamesDef,
		standard_resolution.StandardEpsDef,
		standard_resolution.StandardFaceDef,
		simplicial_ring.CarrierTagInjective,
		chain_complex.HomologyModuleDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		module.RegularModuleOn,
		module_homomorphism.ModuleIsomorphicDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "module_isomorphic(S, " +
			"    cotangent_homology⟨U:U⟩(R, S, f, S, λy:B. y, regular_module(S), 0), " +
			"    kaehler_module(R, S, f))",
	},
		"in degree 0 every function is a cycle (CyclesDef), and the terms of degree 0 are the free "+
			"module over S on the tags of S's elements (StandardNamesDef). The boundary out of degree 1 "+
			"carries the generator at a polynomial u in those tags to Σ_x ε(∂_x u) • δ_x − δ_{tag(ε(u))} "+
			"(JacobianDelta, StandardFaceDef, StandardEpsDef); at a sum, a product and a constant these "+
			"are the three kinds of kaehler_relations carried by the tag (CarrierTagInjective), and every "+
			"such element is a combination of those, by induction on u (PartialVar at a variable, where "+
			"it vanishes, ChainRule). So relabelling by the tag carries kaehler_relations onto the "+
			"boundaries and induces the isomorphism of the quotients (KaehlerModuleDef, HomologyModuleDef)"),
})}

// CotangentDegreeZeroCoefficients — in a universe for R and for S, the
// André–Quillen homology in degree 0 with coefficients in a module N
// over S is the module of Kähler differentials of S over R tensored with
// N over S.
var CotangentDegreeZeroCoefficients = cotangentDegreeZeroCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "CotangentDegreeZeroCoefficients",
	Key:  "prop_52751ee1e7daa40a",
	Reading: "The coefficients are a module over S itself, T = S and g the identity. The " +
		"isomorphism crosses types: D_0 is a set of classes of functions on the host, the " +
		"differentials classes of functions on S's type. finite_supp(N, X(n)) is " +
		"finite_supp(S, X(n)) ⊗_S N with the same Jacobian matrix, and the cokernel commutes " +
		"with ⊗ (right exactness); for N = 0 or S the zero ring both sides are a single point.",
	Deps: []registry.EntryLike{
		CotangentHomologyDef,
		CotangentComplexDef,
		CotangentDegreeZero,
		CotangentChainComplex,
		kaehler.KaehlerModuleDef,
		kaehler.KaehlerRelationsDef,
		kaehler.KaehlerModuleOn,
		tensor_product.TensorRightExact,
		tensor_product.TensorModuleDef,
		tor_ext.FiniteSuppTensorIso,
		partial_derivative.JacobianDelta,
		standard_resolution.StandardEpsDef,
		standard_resolution.StandardFaceDef,
		simplicial_ring.CarrierTagInjective,
		chain_complex.HomologyModuleDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		ring_homomorphism.RingHomIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "module_isomorphic(S, " +
			"    cotangent_homology⟨U:U⟩(R, S, f, S, λy:B. y, N, 0), " +
			"    tensor_module(S, kaehler_module(R, S, f), N))",
	},
		"in degree 0 every function is a cycle and D_0 is the cokernel of the boundary out of "+
			"degree 1 (CyclesDef, BoundariesDef, HomologyModuleDef); the terms of degrees 0 and 1 are "+
			"the free modules over S on the names tensored with N (FiniteSuppTensorIso), and the "+
			"boundary is the presentation of CotangentDegreeZero tensored with N, the generator at a "+
			"polynomial u going to Σ_x ε(∂_x u) • δ_x − δ_{tag(ε(u))} (JacobianDelta, StandardFaceDef, "+
			"StandardEpsDef); right exactness of the tensor product (TensorRightExact) carries the "+
			"cokernel kaehler_module(R, S, f) of the presentation to the cokernel here"),
})}

// ---------------------------------------------------------------------------
// Change of the base ring
// ---------------------------------------------------------------------------

// CotangentBaseChangeMap — over a tower R → S → T and a module N over T,
// in a universe for the three rings, a map F of the standard resolution
// of T over R to that of T over S that commutes with the faces and the
// degeneracies, is in every degree an algebra map over f, and carries
// the augmentation over S back to the augmentation over R, induces by its
// Jacobians a chain map from L_{T/R} ⊗_T N to L_{T/S} ⊗_T N.
var CotangentBaseChangeMap = cotangentBaseChangeMapThm{family.Add(registry.ProofEntry{
	Name: "CotangentBaseChangeMap",
	Key:  "prop_c30beeb03df0a002",
	Reading: "The map meant is the one that changes the coefficients of the standard resolution of T " +
		"from R to S along f and keeps the names: F(0) = universe_algebra_map(R, S, f, λx. x), the " +
		"identity on the tags of T's elements, and F(n + 1) = universe_algebra_map(R, S, f, F(n)), the " +
		"map induced on the names, the simplices of degree n, by the map of degree n. The statement asks " +
		"of F only what that map satisfies: its bottom face identity F(0) ∘ d^R(1, 1) = d^S(1, 1) ∘ F(1) " +
		"holds exactly by the augmentation hypothesis, the other identities by induction from the monad " +
		"laws, and the augmentations agree after F in every degree by commuting F past the 0-th faces " +
		"down to degree 0. Over the tower it is the map L_{T/R} ⊗ N → L_{T/S} ⊗ N of the transitivity " +
		"triangle; the Jacobian changes the coefficient ring of the free algebras, from R to S.",
	Deps: []registry.EntryLike{
		CotangentComplexDef,
		DifferentialComplexDef,
		DifferentialBoundaryDef,
		DifferentialFaceDef,
		CotangentChainComplex,
		partial_derivative.JacobianHom,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		standard_resolution.StandardPolynomialAlgebra,
		standard_resolution.StandardToBaseHom,
		standard_resolution.StandardToBaseFaceIndependent,
		standard_resolution.StandardToBaseDef,
		simplicial_ring.UniverseEmbeddingHost,
		chain_complex.ChainMapDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀F:(num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"simplicial_map(standard_resolution⟨U:U⟩(R, T, λa:A. g(f(a))), " +
				"    standard_resolution⟨U:U⟩(S, T, g), " +
				"    F)",
			"∀n:num. " +
				"    free_algebra_homomorphism(universe_embedding(R), " +
				"        universe_embedding(S), " +
				"        R, " +
				"        S, " +
				"        f, " +
				"        standard_names(R, T, n), " +
				"        standard_names(S, T, n), " +
				"        F(n))",
			"∀u:U. " +
				"    u ∈ standard_terms(R, T, 0) ⇒ " +
				"    standard_eps(S, T, g, F(0, u)) = standard_eps(R, T, λa:A. g(f(a)), u)",
		},
		Conclusion: "chain_map(T, " +
			"    cotangent_complex(R, T, λa:A. g(f(a)), T, λc:C. c, N), " +
			"    cotangent_complex(S, T, g, T, λc:C. c, N), " +
			"    λn:num. " +
			"        free_algebra_jacobian(universe_embedding(R), " +
			"            universe_embedding(S), " +
			"            R, " +
			"            S, " +
			"            standard_names(R, T, n), " +
			"            standard_names(S, T, n), " +
			"            F(n), " +
			"            standard_to_base(S, T, g, n), " +
			"            N))",
	},
		"the augmentations agree after F in every degree, from degree 0 up the 0-th faces F "+
			"commutes with (StandardToBaseDef); each Jacobian is linear (JacobianHom, the target's "+
			"augmentation a ring map by StandardToBaseHom, the embeddings by UniverseEmbeddingHost). "+
			"JacobianCompose, which lets the coefficient ring change along f, makes both sides of each "+
			"square the Jacobian of one composite, the inner augmentations read through "+
			"StandardToBaseFaceIndependent; the composites agree on the variables, F commuting with the "+
			"faces (JacobianCongruence), and the alternating sums follow by linearity (HomSum, HomSmul)"),
})}
