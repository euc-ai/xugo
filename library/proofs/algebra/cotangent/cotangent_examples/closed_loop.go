// closed_loop.go — the cotangent complex computed from a resolution other
// than the standard one. The free algebra on a set of names W resolves
// itself, the constant algebra on W with every face the identity, so its
// André–Quillen homology is the free module on W in degree 0 and zero
// above; the constants resolve a ring over itself, so all of its homology
// vanishes. The Koszul algebra of g has as differentials the one-point
// model of a circle with coefficients in N, whatever g is: homology N in
// degree 1 and zero elsewhere; when g is no zero divisor the Koszul
// algebra resolves R/(g), so D_1(R/(g) / R, N) is N, m standing for the
// class of the conormal cycle of g with coefficient m, and every other
// D_n vanishes, and 𝔽_p over ℤ has its homology in degree 1 alone.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The free algebra resolves itself
// ---------------------------------------------------------------------------

// ConstantDifferentialComplex — the differential complex of the constant
// algebra on W, augmented by the identity, is exact above degree 0 and
// has no boundaries in degree 0.
var ConstantDifferentialComplex = constantDifferentialComplexThm{family.Add(registry.ProofEntry{
	Name: "ConstantDifferentialComplex",
	Key:  "prop_b01f33b2151da80b",
	Reading: "Every face of the constant algebra is the identity, whose Jacobian is the " +
		"identity on finite_supp(N, W), the ring's one acting as N's identity; so the complex " +
		"is the face complex of a constant simplicial module, the boundary out of degree m the " +
		"identity for m even and zero for m odd, and boundaries(0) = {fun_zero} needs only that " +
		"fun_zero lies in the terms of degree 1. On an empty W every term is the zero function " +
		"alone. Only R's universe is read: the Jacobians are those of free algebras over R.",
	Deps: []registry.EntryLike{
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		cotangent_complex.DifferentialFaceDef,
		cotangent_complex.DifferentialTermsDef,
		simplicial_ring.AugmentationAtDef,
		simplicial_ring.UniverseEmbeddingHost,
		partial_derivative.JacobianIdentity,
		simplicial_module.ConstantFaceComplexHomology,
		simplicial_module.FaceComplexDef,
		function_module.FiniteSuppModuleOn,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U). ∀N:module_ops(U, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"module_on(universe_algebra_ring(R, W), N)",
		},
		Conclusion: "boundaries(differential_complex(R, " +
			"        λn:num. W, " +
			"        λn:num. λi:num. λu:U. u, " +
			"        universe_algebra_ring(R, W), " +
			"        λu:U. u, " +
			"        N), " +
			"    0) = " +
			"{fun_zero(N.zero)} ∧ " +
			"(∀n:num. " +
			"    cycles(differential_complex(R, " +
			"            λn:num. W, " +
			"            λn:num. λi:num. λu:U. u, " +
			"            universe_algebra_ring(R, W), " +
			"            λu:U. u, " +
			"            N), " +
			"        n + 1) = " +
			"    boundaries(differential_complex(R, " +
			"            λn:num. W, " +
			"            λn:num. λi:num. λu:U. u, " +
			"            universe_algebra_ring(R, W), " +
			"            λu:U. u, " +
			"            N), " +
			"        n + 1))",
	},
		"the augmentation read in every degree is the identity (AugmentationAtDef), and the "+
			"Jacobian of the identity is the identity on finite_supp(N, W) (JacobianIdentity at "+
			"UniverseEmbeddingHost), so the differential complex has the terms and, on them, the "+
			"boundaries of the face complex of the constant simplicial module finite_supp(N, W) "+
			"inside finite_supp_module(N, 𝕌), and cycles and boundaries read the boundary on the "+
			"terms only (DifferentialComplexDef, DifferentialBoundaryDef, FaceComplexDef, "+
			"FiniteSuppModuleOn, CyclesDef, BoundariesDef); ConstantFaceComplexHomology"),
})}

// PolynomialCotangentDegreeZero — the free algebra on W over R has
// D_0(R[W]/R, N) ≅ finite_supp(N, W), the differentials Ω_{R[W]/R} ⊗ N.
var PolynomialCotangentDegreeZero = polynomialCotangentDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCotangentDegreeZero",
	Key:  "prop_ddc64bef62a20a72",
	Reading: "The free algebra is the universe's own, a ring on U, so U must be a universe for it " +
		"as well as for R: the room it asks is for its carrier, a set of U's members, for its " +
		"polynomials and for prod(num, U), which holds exactly when U is infinite; at U = set(prod(num, " +
		"D)) FreeAlgebraCotangentUniverse discharges it. R's hypothesis asks room for R's carrier " +
		"besides. On an empty W both sides are zero; over the zero ring N is the zero module.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentResolutionIndependence,
		cotangent_complex.CotangentHomologyModuleOn,
		ConstantDifferentialComplex,
		simplicial_ring.ConstantPolynomialResolution,
		simplicial_ring.PowerSetUniverse,
		cotangent_complex.CotangentHomologyDef,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyModuleDef,
		chain_complex.HomologyDef,
		chain_complex.CyclesDef,
		submodule.QuotientModuleDef,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppModuleOn,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U). ∀N:module_ops(U, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, W), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"module_on(universe_algebra_ring(R, W), N)",
		},
		Conclusion: "module_isomorphic(universe_algebra_ring(R, W), " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        universe_algebra_ring(R, W), " +
			"        universe_algebra_const(R), " +
			"        universe_algebra_ring(R, W), " +
			"        λu:U. u, " +
			"        N, " +
			"        0), " +
			"    finite_supp_module(N, W))",
	},
		"the constant algebra on W resolves the free algebra through the identity "+
			"(ConstantPolynomialResolution), so its differential complex and the cotangent "+
			"complex are chain homotopy equivalent (CotangentResolutionIndependence), and "+
			"their homology modules are isomorphic (ChainHomotopyEquivalenceQuasiIsomorphism, "+
			"QuasiIsomorphismDef). In degree 0 every differential is a cycle and the "+
			"boundaries are the zero function alone (ConstantDifferentialComplex), so the "+
			"homology is the cosets {w} of the members of finite_supp(N, W), and w ↦ {w} is an "+
			"isomorphism from finite_supp_module(N, W) (HomologyModuleDef, QuotientModuleDef, "+
			"FiniteSuppModuleOn); invert and compose (IsomorphismInverse, HomCompose)"),
})}

// PolynomialCotangentVanishes — the free algebra on W over R has
// D_n(R[W]/R, N) = 0 for every n ≥ 1.
var PolynomialCotangentVanishes = polynomialCotangentVanishesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCotangentVanishes",
	Key:  "prop_de2ac9199ebc4f26",
	Reading: "The universe hypotheses are those of PolynomialCotangentDegreeZero; no " +
		"hypothesis on W or N, which may be empty or zero. The constant complex's exactness " +
		"carried across CotangentResolutionIndependence; W = ∅ and N = 0 are allowed.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentResolutionIndependence,
		ConstantDifferentialComplex,
		simplicial_ring.ConstantPolynomialResolution,
		cotangent_complex.CotangentHomologyDef,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyTrivialIffExact,
		chain_complex.HomologyModuleDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U). ∀N:module_ops(U, D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, W), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"module_on(universe_algebra_ring(R, W), N)",
			"1 ≤ n",
		},
		Conclusion: "cotangent_homology⟨U:U⟩(R, " +
			"    universe_algebra_ring(R, W), " +
			"    universe_algebra_const(R), " +
			"    universe_algebra_ring(R, W), " +
			"    λu:U. u, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_homology⟨U:U⟩(R, " +
			"        universe_algebra_ring(R, W), " +
			"        universe_algebra_const(R), " +
			"        universe_algebra_ring(R, W), " +
			"        λu:U. u, " +
			"        N, " +
			"        n).zero}",
	},
		"as in PolynomialCotangentDegreeZero the homology of the cotangent complex is that of the "+
			"constant algebra's differential complex (ConstantPolynomialResolution, "+
			"CotangentResolutionIndependence, ChainHomotopyEquivalenceQuasiIsomorphism), which is "+
			"exact above degree 0 (ConstantDifferentialComplex); an exact degree has one class "+
			"(HomologyTrivialIffExact), and a bijection of the carriers keeps a carrier a single point"),
})}

// ---------------------------------------------------------------------------
// A ring over itself
// ---------------------------------------------------------------------------

// EmptyNamesResolution — in a universe for a commutative ring R, the
// constant algebra on no names, the constants of R, resolves R over
// itself through evaluation.
var EmptyNamesResolution = emptyNamesResolutionThm{family.Add(registry.ProofEntry{
	Name: "EmptyNamesResolution",
	Key:  "prop_5f0ad3df8e697abc",
	Reading: "The evaluation reads no variable, the algebra on no names having none, so the value " +
		"given the names is never read; it carries the constant a to a. The faces are identities, so " +
		"the Moore complex is the constants in degree 0 and zero above; the degree-0 condition is " +
		"that the evaluation, const a ↦ a, is a bijection of the constants onto R's carrier.",
	Deps: []registry.EntryLike{
		simplicial_ring.PolynomialResolution,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.ConstantPolynomialAlgebra,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_module.AcyclicAugmentation,
		simplicial_module.MooreTermsDef,
		simplicial_module.MooreComplexDef,
		free_algebra.FreeAlgebraNoVariables,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraConstHom,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "polynomial_resolution(R, " +
			"    λn:num. ∅, " +
			"    λn:num. λi:num. λu:U. u, " +
			"    λn:num. λi:num. λu:U. u, " +
			"    R, " +
			"    λa:A. a, " +
			"    universe_algebra_eval(R, R, λa:A. a, λx:U. R.zero))",
	},
		"the constant algebra on ∅ is a polynomial simplicial algebra (ConstantPolynomialAlgebra); "+
			"its algebra is the constants (FreeAlgebraNoVariables), and the evaluation is a ring map "+
			"to R sending the constant a to a (FreeAlgebraEvalHom, FreeAlgebraEvalConst), so it is "+
			"augmented over R through the identity, both faces of degree 1 being the identity. Unfold "+
			"PolynomialResolution and AcyclicAugmentation: the Moore terms above degree 0 vanish, the "+
			"faces being the identity (MooreTermsDef), so cycles and boundaries are both the zero; the "+
			"evaluation is onto R's carrier and injective on the constants (FreeAlgebraConstHom), and "+
			"the Moore boundaries of degree 0 are the zero alone"),
})}

// IdentityCotangentVanishes — a ring over itself has no André–Quillen
// homology: D_n(R/R, N) = 0 for every n and every module N over R.
var IdentityCotangentVanishes = identityCotangentVanishesThm{family.Add(registry.ProofEntry{
	Name: "IdentityCotangentVanishes",
	Key:  "prop_82b8dfe42266e034",
	Reading: "R is read on its own type, so the one universe hypothesis is R's; the " +
		"structure map and the coefficient map are the identity. In degree 0 it says " +
		"Ω_{R/R} = 0. Every term of the empty-names resolution's differential complex " +
		"is finite_supp(N, ∅) = {fun_zero}, so its homology vanishes in every degree.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentResolutionIndependence,
		EmptyNamesResolution,
		cotangent_complex.CotangentHomologyDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialTermsDef,
		function_module.FiniteSuppDef,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyTrivialIffExact,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"module_on(R, N)",
		},
		Conclusion: "cotangent_homology⟨U:U⟩(R, R, λa:A. a, R, λa:A. a, N, n).carrier = " +
			"{cotangent_homology(R, R, λa:A. a, R, λa:A. a, N, n).zero}",
	},
		"the constants resolve R over itself (EmptyNamesResolution), so the cotangent complex is chain "+
			"homotopy equivalent to that resolution's differential complex "+
			"(CotangentResolutionIndependence), whose every term is finite_supp(N, ∅), the zero function "+
			"alone (DifferentialTermsDef, FiniteSuppDef); its homology vanishes in every degree, and so does "+
			"the cotangent complex's (ChainHomotopyEquivalenceQuasiIsomorphism, HomologyTrivialIffExact)"),
})}

// ---------------------------------------------------------------------------
// The differentials of the Koszul algebra
// ---------------------------------------------------------------------------

// KoszulDifferentialFaces — the face d_i out of degree n carries the
// basis differential dx_k ⊗ m to dx_j ⊗ m when d_i sends x_k to the
// variable x_j, and to zero when it sends x_k to a constant: x_n under
// d_n and x_1 under d_0.
var KoszulDifferentialFaces = koszulDifferentialFacesThm{family.Add(registry.ProofEntry{
	Name: "KoszulDifferentialFaces",
	Key:  "prop_cb3e501ee6d518f9",
	Reading: "g is not read: the faces send variables to variables or to constants, whose partial " +
		"derivatives are zero, and the constant g of d_0 x_1 disappears with them. The index j is k " +
		"when k ≤ i and k − 1 when k > i. koszul_index(koszul_name(k)) = k needs carrier_tag(𝕌⟨A:num⟩) " +
		"injective on num, which R's universe supplies: card_le(prod(num, U), U) puts num into U.",
	Deps: []registry.EntryLike{
		cotangent_complex.DifferentialFaceDef,
		partial_derivative.FreeAlgebraJacobianDef,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		partial_derivative.PartialConst,
		KoszulFaces,
		koszulFaceValueDef,
		KoszulNames,
		koszulNamesDef,
		KoszulAugmented,
		simplicial_ring.AugmentationAtHom,
		free_module.DeltaAtDef,
		function_module.FunZeroDef,
		module.RegularModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀N:module_ops(set(A), D). ∀n i k:num. ∀m:D.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"module_on(koszul_quotient(R, g), N)",
			"i ≤ n",
			"1 ≤ k",
			"k ≤ n",
			"m ∈ N.carrier",
		},
		Conclusion: "differential_face(R, " +
			"    koszul_names⟨U:U⟩, " +
			"    koszul_face(R, g), " +
			"    koszul_augmentation(R, g), " +
			"    N, " +
			"    n, " +
			"    i, " +
			"    delta_at(N.zero, m, koszul_name(k))) = " +
			"COND(k = n ∧ i = n ∨ (i = 0 ∧ k = 1), " +
			"    fun_zero(N.zero), " +
			"    delta_at(N.zero, m, koszul_name(COND(k ≤ i, k, k - 1))))",
	},
		"the Jacobian at a basis differential is ε(∂_t d_i(x_k)) • m at each name t of degree "+
			"n − 1 (DifferentialFaceDef, JacobianDelta), and d_i(x_k) is koszul_face_value(R, g, "+
			"n, i, k) (KoszulFaces): the constant zero for k = i = n, the constant g for i = 0 and "+
			"k = 1, and otherwise the variable of x_k or x_{k−1}, a name of degree n − 1 "+
			"(KoszulNames, koszulNamesDef). A constant has no partial derivative (PartialConst) "+
			"and a variable's is one at its name and zero elsewhere (PartialVar); the augmentation "+
			"read in degree n − 1 is a ring map (AugmentationAtHom at KoszulAugmented), carrying "+
			"them to the one and the zero of R/(g), which act on N as m and N.zero"),
})}

// KoszulDifferentialHomologyOne — the homology in degree 1 of the Koszul
// algebra's differentials is N, m going to the class of dx_1 ⊗ m.
var KoszulDifferentialHomologyOne = koszulDifferentialHomologyOneThm{family.Add(registry.ProofEntry{
	Name: "KoszulDifferentialHomologyOne",
	Key:  "prop_29a82f184a303de4",
	Reading: "No hypothesis on g: the differentials do not read it. Both faces out of " +
		"degree 1 kill dx_1 ⊗ m and the boundary out of degree 2 is zero, so the classes of " +
		"degree 1 are singletons and the homology is the differentials of degree 1, one copy " +
		"of N on the name x_1. At a unit g, module_on over the zero ring forces N = {N.zero}.",
	Deps: []registry.EntryLike{
		cotangent_complex.DifferentialComplexChain,
		KoszulDifferentialFaces,
		KoszulAugmented,
		KoszulPolynomialAlgebra,
		koszulNamesDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		cotangent_complex.DifferentialTermsDef,
		chain_complex.HomologyModuleDef,
		chain_complex.HomologyDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		submodule.QuotientModuleDef,
		module_homomorphism.ModuleIsomorphismDef,
		function_module.FiniteSuppDef,
		free_module.DeltaAtDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀N:module_ops(set(A), D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"module_on(koszul_quotient(R, g), N)",
		},
		Conclusion: "module_isomorphism(koszul_quotient(R, g), " +
			"    N, " +
			"    homology_module(differential_complex(R, " +
			"            koszul_names⟨U:U⟩, " +
			"            koszul_face(R, g), " +
			"            koszul_quotient(R, g), " +
			"            koszul_augmentation(R, g), " +
			"            N), " +
			"        1), " +
			"    λm:D. " +
			"        left_coset(fun_add(N.add), " +
			"            delta_at(N.zero, m, koszul_name(1)), " +
			"            boundaries(differential_complex(R, " +
			"                    koszul_names⟨U:U⟩, " +
			"                    koszul_face(R, g), " +
			"                    koszul_quotient(R, g), " +
			"                    koszul_augmentation(R, g), " +
			"                    N), " +
			"                1)))",
	},
		"the differentials of degree 1 are the functions on {x_1} with values in N "+
			"(DifferentialTermsDef, koszulNamesDef, FiniteSuppDef), each dx_1 ⊗ m. By "+
			"KoszulDifferentialFaces both faces out of degree 1 send it to zero, so every one is a cycle "+
			"(CyclesDef); out of degree 2, d_0 sends dx_1 ⊗ m to zero and dx_2 ⊗ m to dx_1 ⊗ m, d_1 "+
			"sends both to dx_1 ⊗ m, d_2 sends dx_1 ⊗ m to itself and dx_2 ⊗ m to zero, so the "+
			"alternating sum vanishes and the boundaries of degree 1 are the zero alone (BoundariesDef). "+
			"The classes are then the singletons and m ↦ the class of dx_1 ⊗ m is additive, linear and "+
			"bijective (HomologyModuleDef, QuotientModuleDef, ModuleIsomorphismDef), the homology a "+
			"module over R/(g) since the differential complex of an augmented polynomial algebra is a "+
			"chain complex (DifferentialComplexChain at KoszulAugmented)"),
})}

// KoszulDifferentialHomologyVanishes — the differentials of the Koszul
// algebra are exact in every degree but 1.
var KoszulDifferentialHomologyVanishes = koszulDifferentialHomologyVanishesThm{family.Add(registry.ProofEntry{
	Name: "KoszulDifferentialHomologyVanishes",
	Key:  "prop_5b57ab76d1f003f",
	Reading: "No hypothesis on g: this is the differential complex of the Koszul algebra, " +
		"not yet a statement about R/(g). In degree 0 there is no name, so the term is the zero " +
		"function alone; above degree 1 the complex is N tensored with the reduced chains of " +
		"the circle Δ[1]/∂Δ[1]. x_k in degree n is the simplex 0^k 1^{n+1−k} of Δ[1]/∂Δ[1], so " +
		"the complex is N ⊗ C̃(S¹), exact off degree 1 for every N because H̃₁(S¹) = ℤ is free.",
	Deps: []registry.EntryLike{
		cotangent_complex.DifferentialComplexChain,
		KoszulDifferentialFaces,
		koszulNamesDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		cotangent_complex.DifferentialTermsDef,
		simplicial_module.FaceBoundaryDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		function_module.FiniteSuppDef,
		module.ModuleSumInsert,
		module.ModuleSumEmpty,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀N:module_ops(set(A), D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"module_on(koszul_quotient(R, g), N)",
			"¬(n = 1)",
		},
		Conclusion: "cycles(differential_complex(R, " +
			"        koszul_names⟨U:U⟩, " +
			"        koszul_face(R, g), " +
			"        koszul_quotient(R, g), " +
			"        koszul_augmentation(R, g), " +
			"        N), " +
			"    n) = " +
			"boundaries(differential_complex(R, " +
			"        koszul_names⟨U:U⟩, " +
			"        koszul_face(R, g), " +
			"        koszul_quotient(R, g), " +
			"        koszul_augmentation(R, g), " +
			"        N), " +
			"    n)",
	},
		"by KoszulDifferentialFaces the boundary out of degree n sends dx_k ⊗ m to dx_{k−1} ⊗ m "+
			"when k ≥ 2 is odd, plus (−1)^k dx_k ⊗ m when k < n and n − k is even, and to nothing "+
			"else (the alternating sums over the faces fixing x_k and over those lowering it). In "+
			"degree 0 both sides are the zero function, the boundary out of degree 1 being zero. "+
			"For n ≥ 2 the formula shows the cycles of degree n spanned over N by the boundaries of "+
			"the dx_k ⊗ m of degree n + 1 with k odd: the complex is the reduced chains of the "+
			"simplicial circle Δ[1]/∂Δ[1], free with boundary entries 0 and ±1, tensored with N"),
})}

// ---------------------------------------------------------------------------
// Regular quotients, and 𝔽_p over ℤ
// ---------------------------------------------------------------------------

// RegularQuotientCotangent — when g is not a zero divisor, D_1(R/(g) / R,
// N) ≅ N and D_n(R/(g) / R, N) = 0 for every n ≠ 1, N any module over
// R/(g).
var RegularQuotientCotangent = regularQuotientCotangentThm{family.Add(registry.ProofEntry{
	Name: "RegularQuotientCotangent",
	Key:  "prop_ce635435aa0836f3",
	Reading: "That g is no zero divisor is load-bearing, and read through KoszulAcyclic " +
		"alone: at g = 0 in a nonzero ring the projection onto R/(g) is an isomorphism, " +
		"whose D_1 vanishes while N need not. At a unit g both sides are zero. At n = 1 it " +
		"agrees with ConormalModule, (g)/(g²) being R/(g) (PrincipalConormalModule). R/(g) " +
		"lives on set(A), but its universe asks room for its carrier only, the cosets of " +
		"R's carrier: a powerset host R's carrier fits holds it (QuotientCotangentUniverse).",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentResolutionIndependence,
		cotangent_complex.CotangentHomologyModuleOn,
		KoszulAcyclic,
		KoszulDifferentialHomologyOne,
		KoszulDifferentialHomologyVanishes,
		cotangent_complex.CotangentHomologyDef,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyTrivialIffExact,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀N:module_ops(set(A), D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"∀a:A. a ∈ R.carrier ∧ R.mul(g, a) = R.zero ⇒ a = R.zero",
			"cotangent_universe(koszul_quotient(R, g), 𝕌⟨A:U⟩)",
			"module_on(koszul_quotient(R, g), N)",
		},
		Conclusion: "module_isomorphic(koszul_quotient(R, g), " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        koszul_quotient(R, g), " +
			"        koszul_projection(R, g), " +
			"        koszul_quotient(R, g), " +
			"        λy:set(A). y, " +
			"        N, " +
			"        1), " +
			"    N) ∧ " +
			"(∀n:num. " +
			"    ¬(n = 1) ⇒ " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        koszul_quotient(R, g), " +
			"        koszul_projection(R, g), " +
			"        koszul_quotient(R, g), " +
			"        λy:set(A). y, " +
			"        N, " +
			"        n).carrier = " +
			"    {cotangent_homology⟨U:U⟩(R, " +
			"            koszul_quotient(R, g), " +
			"            koszul_projection(R, g), " +
			"            koszul_quotient(R, g), " +
			"            λy:set(A). y, " +
			"            N, " +
			"            n).zero})",
	},
		"the Koszul algebra is a polynomial resolution of R/(g) (KoszulAcyclic), so its differential "+
			"complex with coefficients in N is chain homotopy equivalent to the cotangent complex "+
			"(CotangentResolutionIndependence, the coefficient map the identity of R/(g)), and the "+
			"homology modules are isomorphic in every degree (ChainHomotopyEquivalenceQuasiIsomorphism, "+
			"QuasiIsomorphismDef). KoszulDifferentialHomologyOne gives N in degree 1, inverted and "+
			"composed (IsomorphismInverse, HomCompose); KoszulDifferentialHomologyVanishes and "+
			"HomologyTrivialIffExact give the zero elsewhere"),
})}

// RegularQuotientFirstHomology — when g is not a zero divisor, the
// isomorphism of N onto D_1(R/(g) / R, N) can be written down: m goes to
// the class of the conormal cycle of g with coefficient m.
var RegularQuotientFirstHomology = regularQuotientFirstHomologyThm{family.Add(registry.ProofEntry{
	Name: "RegularQuotientFirstHomology",
	Reading: "g regular is load-bearing: at g = 0 in a nonzero ring the quotient is R itself, " +
		"D_1 vanishes, and the map from N is not injective. At a unit g, or over the zero ring, N is " +
		"the zero module and both sides are one point; at g = R.zero the conormal cycle is the zero " +
		"function. R/(g) lives on set(A), but its universe asks room for its carrier only, the " +
		"cosets of R's carrier: a powerset host R's carrier fits holds it (QuotientCotangentUniverse).",
	Key: "prop_91b6b9250583cc35",
	Deps: []registry.EntryLike{
		KoszulAcyclic,
		KoszulDifferentialHomologyOne,
		KoszulFaces,
		cotangent_complex.CotangentResolutionIndependence,
		cotangent_complex.CotangentHomologyDef,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyMapCoset,
		StandardDifferentialBoundaryTwo,
		conormalCycleDef,
		simplicial_ring.SimplicialAlgebraMap,
		partial_derivative.JacobianDelta,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀N:module_ops(set(A), D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"∀a:A. a ∈ R.carrier ∧ R.mul(g, a) = R.zero ⇒ a = R.zero",
			"cotangent_universe(koszul_quotient(R, g), 𝕌⟨A:U⟩)",
			"module_on(koszul_quotient(R, g), N)",
		},
		Conclusion: "module_isomorphism(koszul_quotient(R, g), " +
			"    N, " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        koszul_quotient(R, g), " +
			"        koszul_projection(R, g), " +
			"        koszul_quotient(R, g), " +
			"        λy:set(A). y, " +
			"        N, " +
			"        1), " +
			"    λm:D. " +
			"        left_coset(fun_add(N.add), " +
			"            λy:U. N.smul(conormal_cycle(R, koszul_quotient(R, g), g, y), m), " +
			"            boundaries(cotangent_complex(R, " +
			"                    koszul_quotient(R, g), " +
			"                    koszul_projection(R, g), " +
			"                    koszul_quotient(R, g), " +
			"                    λy:set(A). y, " +
			"                    N), " +
			"                1)))",
	},
		"the Koszul algebra resolves R/(g) (KoszulAcyclic), so CotangentResolutionIndependence gives a "+
			"simplicial algebra map F from it into the standard resolution covering the identity of R/(g), "+
			"whose Jacobians are a chain homotopy equivalence onto the cotangent complex, an isomorphism "+
			"on homology (ChainHomotopyEquivalenceQuasiIsomorphism, QuasiIsomorphismDef); composed with "+
			"KoszulDifferentialHomologyOne, m goes to the class of the Jacobian of F at dx_1 ⊗ m, the "+
			"differential of v = F(1, x_1) with coefficient m (JacobianDelta). F commutes with the faces "+
			"and fixes the constants (SimplicialAlgebraMap), so d_0 v = F(0, g) is the constant g and d_1 "+
			"v = F(0, 0) the constant zero (KoszulFaces); by StandardDifferentialBoundaryTwo at v, with "+
			"the coefficients through the identity of R/(g), the differential of v with coefficient m "+
			"differs by a boundary from the basis differential at d_0 v less the one at d_1 v, both with "+
			"coefficient m, which is the conormal cycle of g times m (conormalCycleDef)"),
})}

// FpOverZ —D_n(𝔽_p/ℤ, 𝔽_p) vanishes for every n ≥ 2, so with
// FpOverZLowDegrees the cotangent complex of 𝔽_p over ℤ is 𝔽_p in degree
// 1.
var FpOverZ = fpOverZThm{family.Add(registry.ProofEntry{
	Name: "FpOverZ",
	Key:  "prop_16749ad70a67d09",
	Reading: "As in FpOverZLowDegrees only p ≠ 0 is read. The universe " +
		"hypotheses hold at U = set(int), and ConcreteUniverse at int and " +
		"set(int) discharges them; D_0 vanishes too, by FpOverZLowDegrees.",
	Deps: []registry.EntryLike{
		RegularQuotientCotangent,
		nat_prime.PrimeDef,
		int_real_lift.CommRing,
		int_real_lift.MulEqZero,
		module.RegularModuleOn,
		simplicial_ring.ConcreteUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀p:num. ∀Z:ring_ops(int). ∀F:ring_ops(set(int)). ∀n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"Z = «integerRing»",
			"F = koszul_quotient(Z, &p)",
			"cotangent_universe(Z, 𝕌⟨A:U⟩)",
			"cotangent_universe(F, 𝕌⟨A:U⟩)",
			"2 ≤ n",
		},
		Conclusion: "cotangent_homology⟨U:U⟩(Z, " +
			"    F, " +
			"    koszul_projection(Z, &p), " +
			"    F, " +
			"    λy:set(int). y, " +
			"    regular_module(F), " +
			"    n).carrier = " +
			"{cotangent_homology(Z, " +
			"        F, " +
			"        koszul_projection(Z, &p), " +
			"        F, " +
			"        λy:set(int). y, " +
			"        regular_module(F), " +
			"        n).zero}",
	},
		"ℤ is a commutative ring (CommRing) without zero divisors (MulEqZero) and &p ≠ &0 for a "+
			"prime p (PrimeDef), so p is no zero divisor; RegularQuotientCotangent at g = &p and the "+
			"coefficients 𝔽_p as a module over itself (RegularModuleOn) gives the vanishing for n ≠ 1"),
})}
