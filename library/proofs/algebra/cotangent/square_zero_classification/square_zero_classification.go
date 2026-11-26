// square_zero_classification.go — the square-zero extensions of an
// algebra S over R by a module N over S classified by D^1(S/R, N), with
// both directions explicit. An extension E is lifted from the standard
// presentation P = R[S] by choosing preimages of the variables, and its
// class is the class of the conormal map the lift reads, the same for
// every lift and for every extension isomorphic to E; a class ξ is
// realized as the graph extension of the conormal map of a cocycle in ξ,
// whose class is ξ; the realization of the class of E is isomorphic to E,
// and two extensions, on any two types, are isomorphic exactly when they
// have one class.

package square_zero_classification

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cohomology_one"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The class of an extension and the realization of a class
// ---------------------------------------------------------------------------

// SquareZeroClassDef — `square_zero_class(R, S, f, N, E)`: the class in
// D^1(S/R, N) of the extension E, the class of the conormal map read by a
// lift chosen among the lifts of the standard presentation's
// augmentation to E.
var SquareZeroClassDef = squareZeroClassDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroClassDef",
	Key:   "prop_dc32cfec5f7d3bbc",
	Const: "square_zero_class",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"square_zero_ops(A, B, C, D) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"    square_zero_class(R, S, f, N, E) = " +
			"    conormal_class(R, " +
			"        S, " +
			"        f, " +
			"        N, " +
			"        extract_conormal(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"            S, " +
			"            standard_eps(R, S, f), " +
			"            N, " +
			"            E, " +
			"            εs:(U → C). " +
			"                square_zero_lift(R, " +
			"                    universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"                    universe_algebra_const(R), " +
			"                    standard_eps(R, S, f), " +
			"                    E, " +
			"                    s)))",
	},
	Reading: "The host type C of E enters only through the choice of the lift; the class lives in " +
		"the fixed D^1 on the host U, whatever C is. A lift exists for every extension " +
		"(StandardExtensionLiftExists) and every lift gives the same class (ExtensionClassWellDefined), " +
		"so the choice is never read. The letter U is fixed by the universe hypotheses of the " +
		"statements; a text where nothing else fixes it writes square_zero_class⟨U:U⟩.",
})}

// SquareZeroRealizationDef — `square_zero_realization(R, S, f, N, ξ)`: the
// extension realizing the class ξ, the graph extension of the conormal
// map G(c) of a cocycle c chosen in ξ, over the standard presentation.
var SquareZeroRealizationDef = squareZeroRealizationDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroRealizationDef",
	Key:   "prop_db85733571001646",
	Const: "square_zero_realization",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"set(U → D) → " +
		"square_zero_ops(A, B, set(prod(U, D)), D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀ξ:set(U → D). " +
			"    square_zero_realization(R, S, f, N, ξ) = " +
			"    square_zero_graph(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        universe_algebra_const(R), " +
			"        S, " +
			"        standard_eps(R, S, f), " +
			"        N, " +
			"        cocycle_to_conormal(R, S, f, N, εc:(U → D). c ∈ ξ))",
	},
	Reading: "It is (P ⋉_ε N)/J_γ for γ = G(c): every realization lives on set(prod(U, D)), " +
		"so the classification maps D^1 into one type of extensions. A class is a coset of the " +
		"coboundaries at a cocycle, never empty, and each of its members is a cocycle; the chosen " +
		"one is read only up to a coboundary, which changes the extension by an isomorphism.",
})}

// ---------------------------------------------------------------------------
// From an extension to its class
// ---------------------------------------------------------------------------

// StandardExtensionLiftExists — in a universe for R and S, the
// augmentation of the standard presentation lifts to every square-zero
// extension of S by N over R.
var StandardExtensionLiftExists = standardExtensionLiftExistsThm{family.Add(registry.ProofEntry{
	Name: "StandardExtensionLiftExists",
	Key:  "prop_6a57047e665915da",
	Reading: "P is free on the tags of S's elements, so a lift is fixed by a preimage under the " +
		"projection for each element: s = universe_algebra_eval(R, E.ring, E.structure, λt. " +
		"inverse_on(E.ring.carrier, E.projection, inverse_on(S.carrier, carrier_tag(S.carrier), t))). " +
		"The projection onto is load-bearing, and so is p ∘ k = f, which makes p ∘ s and ε agree on the " +
		"constants; the universe for S is not read, p ∘ s and ε reading the same preimage of each tag.",
	Deps: []registry.EntryLike{
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.SquareZeroExtension,
		square_zero_extension.ProjectionOnto,
		standard_resolution.StandardEpsDef,
		standard_resolution.StandardEpsHom,
		standard_resolution.StandardTermsDef,
		standard_resolution.StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseAlgebraConstDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraRingDef,
		ring_homomorphism.RingHomomorphism,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"square_zero_extension(R, S, f, N, E)",
		},
		Conclusion: "∃s:(U → C). " +
			"    square_zero_lift(R, " +
			"        universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        universe_algebra_const(R), " +
			"        standard_eps(R, S, f), " +
			"        E, " +
			"        s)",
	},
		"take θ(t) = inverse_on(E.ring.carrier, E.projection, inverse_on(S.carrier, "+
			"carrier_tag(S.carrier), t)), a member of E's ring over the element t names, the "+
			"projection being onto (ProjectionOnto, InverseOnIn, InverseOnRight), and s the "+
			"evaluation into E's ring at the structure map and θ (UniverseAlgebraEvalDef): a ring "+
			"map from P (FreeAlgebraEvalHom, P's record the free algebra at the universe embedding, "+
			"UniverseEmbeddingHost, UniverseAlgebraRingDef, FreeAlgebraRingDef), carrying the "+
			"constant a to E.structure(a) (FreeAlgebraEvalConst, UniverseAlgebraConstDef). The "+
			"projection after s and the augmentation are ring maps from P to S (RingHomomorphism, "+
			"StandardEpsHom) agreeing on the constants, p(E.structure(a)) = f(a), and on the "+
			"variables, p(θ(t)) and ε(var t) both being the preimage chosen in S's carrier for the "+
			"tag t (FreeAlgebraEvalVar, InverseOnRight, StandardEpsDef); FreeAlgebraEvalUnique"),
})}

// ExtensionClassWellDefined — in a universe for R and S, the class of a
// square-zero extension is a member of D^1(S/R, N), it is the class of
// the conormal map of every lift, and an isomorphic extension has the
// same class.
var ExtensionClassWellDefined = extensionClassWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "ExtensionClassWellDefined",
	Key:  "prop_fb675c1d6fbcdc3d",
	Reading: "Two lifts differ by a derivation whose restriction to I is the difference " +
		"of their conormal maps, which is exactly what leaves the class unchanged. An " +
		"isomorphism φ carries a lift s to the lift φ ∘ s, reading the same conormal map, φ " +
		"being the identity on N. The second extension may be on another type I.",
	Deps: []registry.EntryLike{
		SquareZeroClassDef,
		StandardExtensionLiftExists,
		square_zero_extension.LiftExtractConormal,
		square_zero_extension.LiftDifferenceDerivation,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		square_zero_extension.SquareZeroExtension,
		cohomology_one.ConormalClassSurjective,
		cohomology_one.ConormalClassEqIffDerivation,
		standard_resolution.StandardEpsHom,
		simplicial_ring.UniverseAlgebraConstDef,
		free_algebra.FreeAlgebraConstHom,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"square_zero_extension(R, S, f, N, E)",
		},
		Conclusion: "square_zero_class⟨U:U⟩(R, S, f, N, E) ∈ " +
			"cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).carrier ∧ " +
			"(∀s:(U → C). " +
			"    square_zero_lift(R, " +
			"        universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        universe_algebra_const(R), " +
			"        standard_eps(R, S, f), " +
			"        E, " +
			"        s) ⇒ " +
			"    conormal_class(R, " +
			"        S, " +
			"        f, " +
			"        N, " +
			"        extract_conormal(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"            S, " +
			"            standard_eps(R, S, f), " +
			"            N, " +
			"            E, " +
			"            s)) = " +
			"    square_zero_class(R, S, f, N, E)) ∧ " +
			"(∀E':square_zero_ops(A, B, I, D). ∀φ:(C → I). " +
			"    square_zero_extension(R, S, f, N, E') ∧ square_zero_isomorphism(R, N, E, E', φ) ⇒ " +
			"    square_zero_class⟨U:U⟩(R, S, f, N, E') = square_zero_class(R, S, f, N, E))",
	},
		"the standard presentation is an algebra over R through the constants "+
			"(FreeAlgebraConstHom, UniverseAlgebraConstDef) and its augmentation an algebra map onto "+
			"S (StandardEpsHom), so the square_zero_extension cards apply. A lift exists "+
			"(StandardExtensionLiftExists), so the chosen one is a lift (SquareZeroClassDef). For any "+
			"lift s, its conormal map and the chosen one's are conormal maps (LiftExtractConormal) "+
			"whose difference is a derivation on I (LiftDifferenceDerivation), so they have one class "+
			"(ConormalClassEqIffDerivation), a member of D^1 (ConormalClassSurjective). For φ an "+
			"isomorphism, φ ∘ s is a lift to E' (SquareZeroIsomorphismDef, RingHomomorphism), and "+
			"φ(s(x)) = φ(i(γ_s(x))) = i'(γ_s(x)) for x in I, so it reads γ_s (ExtractConormalDef, "+
			"InverseOnRight, InjectiveOnDef); the second conjunct at E' gives the third"),
})}

// ---------------------------------------------------------------------------
// From a class to an extension, and back
// ---------------------------------------------------------------------------

// ExtensionRealizeClass — in a universe for R and S, the realization of
// a class ξ of D^1(S/R, N) is a square-zero extension of S by N over R,
// and its class is ξ.
var ExtensionRealizeClass = extensionRealizeClassThm{family.Add(registry.ProofEntry{
	Name: "ExtensionRealizeClass",
	Key:  "prop_66dcc301e342f30b",
	Reading: "The class is computed through the canonical lift u ↦ [(u, 0)], not through " +
		"the lift square_zero_class chooses: ExtensionClassWellDefined lets any lift serve. " +
		"The canonical lift reads γ back because [(x, 0)] = [(0, γ(x))] for x in I.",
	Deps: []registry.EntryLike{
		SquareZeroRealizationDef,
		ExtensionClassWellDefined,
		cohomology_one.CocycleToConormal,
		cohomology_one.CocycleConormalLinearInverse,
		cohomology_one.ConormalClassDef,
		square_zero_extension.GraphQuotientExtension,
		square_zero_extension.TwistedGraphIdeal,
		square_zero_extension.SplitSquareZeroRing,
		square_zero_extension.SquareZeroGraphDef,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		square_zero_extension.SquareZeroExtension,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.IdealQuotientProjectionDef,
		standard_resolution.StandardEpsHom,
		standard_resolution.StandardExtraBottom,
		standard_resolution.StandardExtraIn,
		free_algebra.FreeAlgebraConstHom,
		cotangent_complex.CotangentCohomologyDef,
		cotangent_complex.CotangentCochainComplex,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesSucc,
		quotient_group.InLeftCosets,
		group.InOwnLeftCosetOn,
		group.LeftCosetEqOn,
		ring_homomorphism.RingHomomorphism,
		functions.InverseOnLeft,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀ξ:set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"ξ ∈ cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).carrier",
		},
		Conclusion: "square_zero_extension(R, S, f, N, square_zero_realization(R, S, f, N, ξ)) ∧ " +
			"square_zero_class(R, S, f, N, square_zero_realization(R, S, f, N, ξ)) = ξ",
	},
		"ξ is the coset of a cocycle (CotangentCohomologyDef, CohomologyModuleDef, InLeftCosets), so it "+
			"holds the chosen c, a cocycle with ξ its coset (InOwnLeftCosetOn, LeftCosetEqOn): the "+
			"coboundaries are a subgroup of the cocycles, two coboundaries in a row vanishing "+
			"(CotangentCochainComplex, CoboundariesSucc); γ = G(c) is a conormal map (CocycleToConormal). "+
			"The augmentation of P is onto S, ε of the bottom of y being y (StandardExtraBottom, "+
			"StandardExtraIn), and an algebra map over R (StandardEpsHom, FreeAlgebraConstHom), so "+
			"GraphQuotientExtension makes the realization an extension (SquareZeroRealizationDef). The "+
			"canonical lift u ↦ [(u, 0)] is a ring map, the section followed by the projection onto the "+
			"quotient by the ideal J_γ (SplitSquareZeroRing, TwistedGraphIdeal, IdealQuotientProjection), "+
			"carrying the constant a to the structure map and lifting ε (SquareZeroGraphDef, "+
			"GraphQuotientExtension); at x in I it is [(x, 0)] = i(γ(x)), so it reads γ (ExtractConormalDef, "+
			"InverseOnLeft, injectivity of i), and off I both are N.zero. By ExtensionClassWellDefined the "+
			"class is [C(G(c))] = [c] (CocycleConormalLinearInverse, ConormalClassDef) = ξ"),
})}

// ExtensionRealizeRoundTrip — in a universe for R and S, every
// square-zero extension of S by N over R is isomorphic to the realization
// of its class.
var ExtensionRealizeRoundTrip = extensionRealizeRoundTripThm{family.Add(registry.ProofEntry{
	Name: "ExtensionRealizeRoundTrip",
	Key:  "prop_556f8dc8fe80da6f",
	Reading: "The isomorphism is a composite: E_{G(c)} ≅ E_{γ_s} by the shear of " +
		"the derivation that the two conormal maps differ by on I, then E_{γ_s} ≅ E by " +
		"the sum map of the lift s. No card composes square-zero isomorphisms: the " +
		"proof composes the ring isomorphisms and chains the three commutations in place.",
	Deps: []registry.EntryLike{
		SquareZeroRealizationDef,
		SquareZeroClassDef,
		StandardExtensionLiftExists,
		ExtensionClassWellDefined,
		cohomology_one.ConormalClassEqIffDerivation,
		cohomology_one.CocycleToConormal,
		cohomology_one.ConormalToCocycle,
		cohomology_one.CocycleConormalLinearInverse,
		cohomology_one.ConormalClassDef,
		cotangent_complex.CotangentCochainComplex,
		chain_complex.CoboundariesSucc,
		square_zero_extension.LiftExtractConormal,
		square_zero_extension.LiftSumKernelAndQuotientIso,
		square_zero_extension.ShearGraphExtensionIso,
		square_zero_extension.SquareZeroIsomorphismDef,
		standard_resolution.StandardEpsHom,
		standard_resolution.StandardExtraBottom,
		standard_resolution.StandardExtraIn,
		free_algebra.FreeAlgebraConstHom,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		functions.InjectiveOnCompose,
		group.InOwnLeftCosetOn,
		group.LeftCosetEqOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"square_zero_extension(R, S, f, N, E)",
		},
		Conclusion: "∃φ:(set(prod(U, D)) → C). " +
			"    square_zero_isomorphism(R, " +
			"        N, " +
			"        square_zero_realization(R, S, f, N, square_zero_class(R, S, f, N, E)), " +
			"        E, " +
			"        φ)",
	},
		"let s be the chosen lift (StandardExtensionLiftExists, SquareZeroClassDef) and γ_s its conormal "+
			"map (LiftExtractConormal); LiftSumKernelAndQuotientIso gives E_{γ_s} ≅ E, the presentation "+
			"being onto S (StandardExtraBottom, StandardExtraIn) and an algebra map over R (StandardEpsHom, "+
			"FreeAlgebraConstHom). The realization is E_{G(c)} for c chosen in the class of E, the class of "+
			"C(γ_s) (SquareZeroRealizationDef, SquareZeroClassDef); C(γ_s) is a cocycle (ConormalToCocycle) "+
			"and the coboundaries a subgroup of the cocycles (CotangentCochainComplex, CoboundariesSucc), so "+
			"c, a member of its coset, is a cocycle; G(c) is a conormal map (CocycleToConormal) with "+
			"[C(G(c))] = [c] = [C(γ_s)] (CocycleConormalLinearInverse, InOwnLeftCosetOn, LeftCosetEqOn), so "+
			"γ_s − G(c) is a derivation d on I (ConormalClassEqIffDerivation) and ShearGraphExtensionIso "+
			"gives E_{G(c)} ≅ E_{γ_s}. Compose: ring homomorphisms compose (RingHomomorphism), the composite "+
			"is injective (InjectiveOnCompose) and onto, and the structure, inclusion and projection "+
			"equations chain (SquareZeroIsomorphismDef, RingIsomorphismDef)"),
})}

// ExtensionIsoIffSameClass — in a universe for R and S, two square-zero
// extensions of S by N over R, on any two types, are isomorphic exactly
// when they have the same class in D^1(S/R, N).
var ExtensionIsoIffSameClass = extensionIsoIffSameClassThm{family.Add(registry.ProofEntry{
	Name: "ExtensionIsoIffSameClass",
	Key:  "prop_4b6e329a6226825d",
	Reading: "With ExtensionRealizeClass this is the classification: the isomorphism " +
		"classes of square-zero extensions of S by N over R are in bijection with D^1(S/R, N), " +
		"square_zero_class one way and square_zero_realization the other. ⇐ goes through the " +
		"realization of the common class, an inverse of one isomorphism composed with the other.",
	Deps: []registry.EntryLike{
		ExtensionClassWellDefined,
		ExtensionRealizeRoundTrip,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SquareZeroExtension,
		ring_homomorphism.IsomorphismInverse,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InverseOnIn,
		functions.InjectiveOnCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
		},
		Conclusion: "(∃φ:(C → I). square_zero_isomorphism(R, N, E, E', φ)) ⇔ " +
			"square_zero_class⟨U:U⟩(R, S, f, N, E) = square_zero_class(R, S, f, N, E')",
	},
		"⇒ is the third conjunct of ExtensionClassWellDefined. ⇐: with ξ the common class, "+
			"ExtensionRealizeRoundTrip gives isomorphisms ψ from the realization of ξ to E and ψ' to "+
			"E'. inverse_on(the realization's carrier, ψ) is a ring isomorphism from E to the "+
			"realization (IsomorphismInverse), and it commutes with the structure maps, the inclusions "+
			"and the projections, each equation of ψ read through the inverse (InverseOnLeft, "+
			"InverseOnRight, InverseOnIn); composed with ψ' (RingHomomorphism, InjectiveOnCompose, "+
			"RingIsomorphismDef) it is an isomorphism from E to E' (SquareZeroIsomorphismDef)"),
})}
