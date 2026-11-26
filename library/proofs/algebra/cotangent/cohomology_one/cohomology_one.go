// cohomology_one.go — D^1(S/R, N) read on the standard presentation
// P = R[S] → S with kernel I: the coboundaries of the cotangent cochain
// complex in degrees 0 and 1 written through the derivations of the free
// algebras with given values at the variables, so that a 1-cochain c is
// a cocycle exactly when the derivation of P_1 with values c is c(d_0 w)
// − c(d_1 w); then the cocycles and the conormal maps of P → S into N
// carried into each other, x ↦ c(x) − c(0) on I one way and u ↦ γ(u −
// τ(u)) the other, linear and inverse; the coboundaries the conormal maps
// that are restrictions of derivations of P; and so D^1 the conormal
// maps modulo those restrictions — each class one conormal map's, two
// conormal maps one class exactly when their difference is a
// derivation on I.

package cohomology_one

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The conversions and the class
// ---------------------------------------------------------------------------

// CocycleToConormalDef — `cocycle_to_conormal(R, S, f, N, c, x)`: the
// conormal map G(c) of the 1-cochain c — at x in the kernel I of the
// augmentation the difference c(x) − c(0), N.zero off I.
var CocycleToConormalDef = cocycleToConormalDefThm{family.Define(registry.DefEntry{
	Name:  "CocycleToConormalDef",
	Key:   "prop_337236059f262294",
	Const: "cocycle_to_conormal",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, D) → (U → D) → U → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀c:(U → D). ∀x:U. " +
			"    cocycle_to_conormal(R, S, f, N, c, x) = " +
			"    COND(x ∈ ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
			"        N.add(c(x), N.neg(c(universe_algebra_ring(R, standard_names(R, S, 0)).zero))), " +
			"        N.zero)",
	},
	Reading: "A 1-cochain is a function on the names of degree 1, the members of P = " +
		"R[S]; 0 is a name like any other, and a cocycle need not vanish there, its value " +
		"at 0 being what the subtraction removes. On a cocycle the result is a conormal " +
		"map (CocycleToConormal); the cochain is read at the members of I and at 0 only.",
})}

// ConormalToCocycleDef — `conormal_to_cocycle(R, S, f, N, γ, u)`: the
// 1-cochain C(γ) of the conormal map γ — at a member u of P the value of
// γ at u − τ(u), which lies in I, and N.zero off P.
var ConormalToCocycleDef = conormalToCocycleDefThm{family.Define(registry.DefEntry{
	Name:  "ConormalToCocycleDef",
	Key:   "prop_e0c40977fc0f0a7b",
	Const: "conormal_to_cocycle",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, D) → (U → D) → U → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀γ:(U → D). ∀u:U. " +
			"    conormal_to_cocycle(R, S, f, N, γ, u) = " +
			"    COND(u ∈ standard_terms(R, S, 0), " +
			"        γ(universe_algebra_ring(R, standard_names(R, S, 0)).sub(u, " +
			"                standard_representative(R, S, f, u))), " +
			"        N.zero)",
	},
	Reading: "u − τ(u) has augmentation ε(u) − ε(u) = S.zero " +
		"(StandardRepresentativeLaws), so it is in I and γ is read on I only. The value is " +
		"N.zero off the names of degree 1, as a 1-cochain is, and the map keeps sums and " +
		"negatives of every γ and multiples by S's carrier, the zero branch being kept by " +
		"those operations of N. With conormal_class it is the map from conormal maps to D^1.",
})}

// ConormalClassDef — `conormal_class(R, S, f, N, γ)`: the class [C(γ)]
// of the conormal map γ, the coset of C(γ) modulo the coboundaries of
// degree 1.
var ConormalClassDef = conormalClassDefThm{family.Define(registry.DefEntry{
	Name:  "ConormalClassDef",
	Key:   "prop_b97cfc3679e9e770",
	Const: "conormal_class",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, D) → (U → D) → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀γ:(U → D). " +
			"    conormal_class(R, S, f, N, γ) = " +
			"    left_coset(fun_add(N.add), " +
			"        conormal_to_cocycle(R, S, f, N, γ), " +
			"        coboundaries(cotangent_cochain(R, S, f, S, λy:B. y, N), 1))",
	},
	Reading: "The coset is the one cohomology_module forms, so for γ a conormal map it is a " +
		"member of cotangent_cohomology(R, S, f, S, λy. y, N, 1).carrier, the D^1 of the cotangent " +
		"complex, and two classes are equal exactly when the cochains differ by a coboundary.",
	Deps: []registry.EntryLike{ConormalToCocycleDef},
})}

// ---------------------------------------------------------------------------
// The coboundaries in degrees 0 and 1
// ---------------------------------------------------------------------------

// CotangentLowCoboundaries — in a universe for R and S, the coboundary of
// a 0-cochain h at u is D_h(u) − D_h(τ(u)), and that of a 1-cochain c at
// w is D_c(w) − c(d_0 w) + c(d_1 w), D_h and D_c the derivations with the
// cochains' values at the variables; so c is a cocycle exactly when
// D_c(w) = c(d_0 w) − c(d_1 w) for every 1-simplex w.
var CotangentLowCoboundaries = cotangentLowCoboundariesThm{family.Add(registry.ProofEntry{
	Name: "CotangentLowCoboundaries",
	Key:  "prop_a343a9c55f40c9d8",
	Reading: "The coefficients are a module over S itself, T = S and g the identity. Each " +
		"formula holds on the names of the next degree and both sides are N.zero off them. D_h is " +
		"the derivation of P = R[S] through the augmentation, D_c that of P_1 = R[P] through the " +
		"augmentation read in degree 1; D_h(τ(u)) is h at the tag of ε(u). These are the transposes " +
		"of the boundaries StandardDifferentialBoundaryOne and StandardDifferentialBoundaryTwo " +
		"state on the chain side; this card reads the cochain definition directly.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentCochainDef,
		partial_derivative.FreeAlgebraJacobianTransposeDef,
		partial_derivative.FreeAlgebraDerivationDef,
		partial_derivative.FreeAlgebraDerivationFromValues,
		partial_derivative.PartialVar,
		partial_derivative.PartialSupportFinite,
		standard_resolution.StandardLowFaceFormulas,
		standard_resolution.StandardRepresentativeDef,
		standard_resolution.StandardToBaseDef,
		standard_resolution.StandardToBaseHom,
		standard_resolution.StandardEpsHom,
		standard_resolution.StandardNamesDef,
		standard_resolution.StandardTermsDef,
		simplicial_ring.AugmentationAtDef,
		comm_ring.AlternatingSignDef,
		chain_complex.CocyclesDef,
		function_module.FunModuleDef,
		function_module.FunAddDef,
		function_module.FunSmulDef,
		function_module.FunZeroDef,
		module.ModuleSumSupport,
		module.ModuleSumInsert,
		module.ModuleSumEmpty,
		module.AddGroupOn,
		module.SmulOne,
		module.SmulNeg,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "(∀h:(U → D). " +
			"    h ∈ «cochains».terms(0) ⇒ " +
			"    «cochains».d(0)(h) = " +
			"    λu:U. " +
			"        COND(u ∈ standard_terms(R, S, 0), " +
			"            N.add(«zeroDerivation»(h, u), " +
			"                N.neg(«zeroDerivation»(h, standard_representative(R, S, f, u)))), " +
			"            N.zero)) ∧ " +
			"(∀c:(U → D). " +
			"    c ∈ «cochains».terms(1) ⇒ " +
			"    «cochains».d(1)(c) = " +
			"    λw:U. " +
			"        COND(w ∈ standard_terms(R, S, 1), " +
			"            N.add(N.add(«oneDerivation»(c, w), N.neg(c(«vertexZero»(w)))), c(«vertexOne»(w))), " +
			"            N.zero)) ∧ " +
			"(∀c:(U → D). " +
			"    c ∈ cocycles(«cochains», 1) ⇔ " +
			"    c ∈ «cochains».terms(1) ∧ " +
			"    (∀w:U. " +
			"        w ∈ standard_terms(R, S, 1) ⇒ " +
			"        «oneDerivation»(c, w) = N.add(c(«vertexZero»(w)), N.neg(c(«vertexOne»(w))))))",
		Abbrev: Abbrev{
			{Name: "zeroDerivation", Text: "free_algebra_derivation(universe_embedding(R), " +
				"    R, " +
				"    standard_names(R, S, 0), " +
				"    standard_eps(R, S, f), " +
				"    N)"},
			{Name: "oneDerivation", Text: "free_algebra_derivation(universe_embedding(R), " +
				"    R, " +
				"    standard_names(R, S, 1), " +
				"    standard_to_base(R, S, f, 1), " +
				"    N)"},
			{Name: "vertexZero", Text: "standard_face(R, S, f, 1, 0)"},
			{Name: "vertexOne", Text: "standard_face(R, S, f, 1, 1)"},
		},
	},
		"unfold CotangentCochainDef in degrees 0 and 1: the coboundary at a name s of the next "+
			"degree is the alternating sum (AlternatingSignDef) of the transposed Jacobians of the faces "+
			"at var(s) (FreeAlgebraJacobianTransposeDef), their entries carried by the augmentation read "+
			"in the lower degree, ε itself in degree 0 (StandardToBaseDef, AugmentationAtDef); off the "+
			"names every term is N.zero. StandardLowFaceFormulas gives the faces: d_0 of var(u) is u, so "+
			"the first transpose at u is Σ_t ε(∂_t u) • h(t) over the finitely many t with a nonzero "+
			"term, which is D_h(u) (FreeAlgebraDerivationDef, the two index sets differing by zero "+
			"terms, ModuleSumSupport, PartialSupportFinite); d_1 of var(u) is τ(u), the variable of the "+
			"tag of ε(u), whose only nonzero derivative is one at that tag (PartialVar), carried to "+
			"S.one (StandardEpsHom), giving h(tag ε(u)) = D_h(τ(u)) (FreeAlgebraDerivationFromValues). "+
			"In degree 1, d_0 of var(w) is w, giving D_c(w), and d_1, d_2 of var(w) are the variables of "+
			"d_0 w and d_1 w, giving c(d_0 w) and c(d_1 w) (PartialVar, StandardToBaseHom); the signs "+
			"are +, −, + (SmulOne, SmulNeg). The last conjunct: a cocycle is a cochain the coboundary "+
			"sends to the zero function (CocyclesDef, FunZeroDef), and with all values in N's carrier "+
			"D_c(w) − c(d_0 w) + c(d_1 w) = N.zero is D_c(w) = c(d_0 w) − c(d_1 w) (AddGroupOn)"),
})}

// ---------------------------------------------------------------------------
// Cocycles and conormal maps
// ---------------------------------------------------------------------------

// CocycleToConormal — in a universe for R and S, a 1-cocycle c gives the
// conormal map G(c), x ↦ c(x) − c(0) on I.
var CocycleToConormal = cocycleToConormalThm{family.Add(registry.ProofEntry{
	Name: "CocycleToConormal",
	Key:  "prop_7a907a742d232877",
	Reading: "Two test 1-simplices carry the argument, built from the extra degeneracy v̂(x) " +
		"= [x] − [0]: v̂(x) + v̂(y) has faces x + y and τ(x) − τ(0) + τ(y) − τ(0), which vanishes " +
		"for x, y in I, so the cocycle condition reads c(x + y) − c(0) = (c(x) − c(0)) + (c(y) − " +
		"c(0)); [u] v̂(x) has faces u x and τ(u)(τ(x) − τ(0)) = 0, and D_c of it is ε(u) • (c(x) " +
		"− c(0)) + ε(x) • c(u) with ε(x) = S.zero. No degeneracy of the resolution is read.",
	Deps: []registry.EntryLike{
		CotangentLowCoboundaries,
		CocycleToConormalDef,
		partial_derivative.ConormalHom,
		partial_derivative.FreeAlgebraDerivationFromValues,
		standard_resolution.StandardExtraDef,
		standard_resolution.StandardExtraIn,
		standard_resolution.StandardLowFaceFormulas,
		standard_resolution.StandardRepresentativeLaws,
		standard_resolution.StandardFacesHom,
		standard_resolution.StandardToBaseHom,
		standard_resolution.StandardEpsHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.AdditiveHomomorphism,
		ring_homomorphism.MapMul,
		partial_derivative.DerivationOn,
		function_module.FunModuleDef,
		module.ZeroSmul,
		module.SmulAddLeft,
		module.SmulNeg,
		module.AddGroupOn,
		module.AddComm,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀c:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"c ∈ cocycles(cotangent_cochain(R, S, f, S, λy:B. y, N), 1)",
		},
		Conclusion: "conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"    S, " +
			"    standard_eps(R, S, f), " +
			"    N, " +
			"    cocycle_to_conormal(R, S, f, N, c))",
	},
		"unfold conormal_hom (ConormalHom) at CocycleToConormalDef: on I the values are in N's "+
			"carrier, the cochain's being (FunModuleDef); off I the COND gives N.zero; I is an ideal "+
			"(KernelIdeal at StandardEpsHom). Additivity: the 1-simplex w = v̂(x) + v̂(y), v̂ = "+
			"standard_extra (StandardExtraDef, StandardExtraIn), has d_0 w = x + y and d_1 w = τ(x) − τ(0) "+
			"+ τ(y) − τ(0) = 0 (StandardFacesHom, StandardLowFaceFormulas, StandardRepresentativeLaws for "+
			"x, y in I), and D_c(w) = c(x) − c(0) + c(y) − c(0) (FreeAlgebraDerivationFromValues, additive "+
			"by DerivationOn); the cocycle condition of CotangentLowCoboundaries at w, with c(0) − c(0) = "+
			"0, is the additivity of G(c). Linearity: w = [u] v̂(x) for u in P and x in I has d_0 w = u x "+
			"and d_1 w = τ(u)(τ(x) − τ(0)) = 0 (MapMul), and D_c(w) = ε_1([u]) • D_c(v̂(x)) + ε_1(v̂(x)) • "+
			"c(u) by the Leibniz rule, ε_1([u]) = ε(u) and ε_1(v̂(x)) = ε(x) − ε(0) = S.zero "+
			"(StandardToBaseHom, StandardLowFaceFormulas), so the cocycle condition is c(u x) − c(0) = "+
			"ε(u) • (c(x) − c(0)) (ZeroSmul, SmulAddLeft, SmulNeg)"),
})}

// ConormalToCocycle — in a universe for R and S, a conormal map γ gives
// the 1-cocycle C(γ), u ↦ γ(u − τ(u)).
var ConormalToCocycle = conormalToCocycleThm{family.Add(registry.ProofEntry{
	Name: "ConormalToCocycle",
	Key:  "prop_1cecd329ce33e5a6",
	Reading: "The derivation of P_1 with values C(γ) is w ↦ γ(d_0 w − d_1 w): both are derivations " +
		"through ε_1 with one value at every variable, γ(u − τ(u)). The cocycle condition is then γ(d_0 " +
		"w − d_1 w) = γ(d_0 w − τ(d_0 w)) − γ(d_1 w − τ(d_1 w)), which holds because τ(d_0 w) = τ(d_1 w).",
	Deps: []registry.EntryLike{
		CotangentLowCoboundaries,
		ConormalToCocycleDef,
		partial_derivative.ConormalHom,
		partial_derivative.DerivationOn,
		partial_derivative.DerivationUniqueOnGenerators,
		partial_derivative.FreeAlgebraDerivationFromValues,
		standard_resolution.StandardLowFaceFormulas,
		standard_resolution.StandardRepresentativeLaws,
		standard_resolution.StandardFacesHom,
		standard_resolution.StandardEpsCoequalizes,
		standard_resolution.StandardToBaseHom,
		standard_resolution.StandardToBaseFaceIndependent,
		standard_resolution.StandardEpsHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		function_module.FunModuleDef,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		comm_ring.SubAddNegOn,
		comm_ring.LeftDistribOn,
		module.AddGroupOn,
		module.AddComm,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀γ:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), S, standard_eps(R, S, f), N, γ)",
		},
		Conclusion: "conormal_to_cocycle(R, S, f, N, γ) ∈ " +
			"cocycles(cotangent_cochain(R, S, f, S, λy:B. y, N), 1)",
	},
		"C(γ) is a 1-cochain: γ's values on I are in N's carrier and u − τ(u) is in I "+
			"(StandardRepresentativeLaws, KernelIdeal), N.zero off the names (ConormalToCocycleDef, "+
			"FunModuleDef). By CotangentLowCoboundaries it is a cocycle when D_c(w) = c(d_0 w) − "+
			"c(d_1 w) on P_1 for c = C(γ). The map w ↦ γ(d_0 w − d_1 w) is a derivation of P_1 "+
			"through ε_1: d_0 w − d_1 w is in I by StandardEpsCoequalizes; it is additive (MapAdd); "+
			"at a product, d_0(w w') − d_1(w w') = d_0 w (d_0 w' − d_1 w') + d_1 w' (d_0 w − d_1 w) "+
			"(MapMul, LeftDistribOn, SubAddNegOn), which γ sends to ε(d_0 w) • γ(…) + ε(d_1 w') • "+
			"γ(…), ε after either face being ε_1 (StandardToBaseFaceIndependent); the constants "+
			"have equal faces. At var(u) it is γ(u − τ(u)) = C(γ)(u) (StandardLowFaceFormulas), so "+
			"it is D_c (DerivationUniqueOnGenerators, FreeAlgebraDerivationFromValues). Then c(d_0 "+
			"w) − c(d_1 w) = γ(d_0 w − τ(d_0 w)) − γ(d_1 w − τ(d_1 w)) = γ(d_0 w − d_1 w), by "+
			"additivity on I and τ(d_0 w) = τ(d_1 w) (StandardRepresentativeLaws)"),
})}

// CocycleConormalLinearInverse — in a universe for R and S, G ∘ C is the
// identity on the conormal maps and C ∘ G on the 1-cocycles, as functions
// of the host; C keeps sums, negatives and multiples by S on every
// function, and G on the 1-cochains.
var CocycleConormalLinearInverse = cocycleConormalLinearInverseThm{family.Add(registry.ProofEntry{
	Name: "CocycleConormalLinearInverse",
	Key:  "prop_daa44199f0793d07",
	Reading: "The zero branches make the round trips equations of whole functions: a conormal map " +
		"is N.zero off I, a cochain off the names of degree 1. C ∘ G = id needs two identities of " +
		"every 1-cocycle c, read off the 1-simplices [u] and [a + b] − [a] − [b]: c(τ(u)) = N.zero, " +
		"and c(a + b) − c(a) − c(b) = c(0) − c(τ(a + b) − τ(a) − τ(b)); at a = u − τ(u), b = τ(u) the " +
		"second gives c(u − τ(u)) − c(0) = c(u). C is linear on all functions, the zero branch being " +
		"kept by N's operations; G is linear on the cochains, whose values lie in N's carrier.",
	Deps: []registry.EntryLike{
		CotangentLowCoboundaries,
		CocycleToConormalDef,
		ConormalToCocycleDef,
		CocycleToConormal,
		ConormalToCocycle,
		partial_derivative.ConormalHom,
		partial_derivative.FreeAlgebraDerivationFromValues,
		standard_resolution.StandardLowFaceFormulas,
		standard_resolution.StandardRepresentativeLaws,
		standard_resolution.StandardFacesHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.AdditiveHomomorphism,
		chain_complex.CocyclesDef,
		function_module.FunModuleDef,
		function_module.FunAddDef,
		function_module.FunNegDef,
		function_module.FunSmulDef,
		comm_ring.SubAddNegOn,
		module.AddGroupOn,
		module.AddComm,
		module.SmulZero,
		module.SmulAddLeft,
		module.SmulNeg,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "(∀γ:(U → D). «conormal»(γ) ⇒ «toConormal»(«toCocycle»(γ)) = γ) ∧ " +
			"(∀c:(U → D). c ∈ cocycles(«cochains», 1) ⇒ «toCocycle»(«toConormal»(c)) = c) ∧ " +
			"(∀γ₁ γ₂:(U → D). «toCocycle»(fun_add(γ₁, γ₂)) = fun_add(«toCocycle»(γ₁), «toCocycle»(γ₂))) ∧ " +
			"(∀γ:(U → D). «toCocycle»(fun_neg(γ)) = fun_neg(«toCocycle»(γ))) ∧ " +
			"(∀b:B. ∀γ:(U → D). " +
			"    b ∈ S.carrier ⇒ " +
			"    «toCocycle»(fun_smul(N.smul, b, γ)) = fun_smul(N.smul, b, «toCocycle»(γ))) ∧ " +
			"(∀c₁ c₂:(U → D). " +
			"    c₁ ∈ «cochains».terms(1) ∧ c₂ ∈ «cochains».terms(1) ⇒ " +
			"    «toConormal»(fun_add(c₁, c₂)) = fun_add(«toConormal»(c₁), «toConormal»(c₂))) ∧ " +
			"(∀c:(U → D). c ∈ «cochains».terms(1) ⇒ «toConormal»(fun_neg(c)) = fun_neg(«toConormal»(c))) ∧ " +
			"(∀b:B. ∀c:(U → D). " +
			"    b ∈ S.carrier ∧ c ∈ «cochains».terms(1) ⇒ " +
			"    «toConormal»(fun_smul(N.smul, b, c)) = fun_smul(N.smul, b, «toConormal»(c)))",
		Abbrev: Abbrev{
			{Name: "presentation", Text: "universe_algebra_ring(R, standard_names(R, S, 0))"},
			{Name: "conormal", Text: "conormal_hom(«presentation», S, standard_eps(R, S, f), N)"},
			{Name: "toCocycle", Text: "conormal_to_cocycle(R, S, f, N)"},
			{Name: "toConormal", Text: "cocycle_to_conormal(R, S, f, N)"},
		},
	},
		"G(C(γ)) at x in I is γ(x − τ(x)) − γ(0 − τ(0)) = γ(x − τ(0)) − γ(−τ(0)) = γ(x), τ(x) = τ(0) "+
			"and τ(0) in I (StandardRepresentativeLaws), γ additive on I (ConormalHom, SubAddNegOn); off I "+
			"both are N.zero. C(G(c)) at u in P is c(u − τ(u)) − c(0): CotangentLowCoboundaries at the "+
			"1-simplex [u] gives c(τ(u)) = N.zero (StandardLowFaceFormulas, "+
			"FreeAlgebraDerivationFromValues), and at [a + b] − [a] − [b], whose 0-th face is zero and 1-st "+
			"face τ(a + b) − τ(a) − τ(b) (StandardFacesHom), c(a + b) − c(a) − c(b) = c(0) − c(τ(a + b) − "+
			"τ(a) − τ(b)); at a = b = 0 this is c(−τ(0)) = c(0) + c(0), and at a = u − τ(u), b = τ(u), "+
			"where τ(a) = τ(0) and τ(τ(u)) = τ(u), it is c(u) − c(u − τ(u)) = c(0) − c(−τ(0)) = −c(0). Off "+
			"P both are N.zero, a cochain vanishing off the names (FunModuleDef). Linearity: pointwise at "+
			"each branch (FunAddDef, FunNegDef, FunSmulDef), N.zero kept by N's operations (AddGroupOn, "+
			"SmulZero), and for G the values of the cochains in N's carrier (AddComm, SmulAddLeft, SmulNeg)"),
})}

// ---------------------------------------------------------------------------
// Coboundaries and derivations
// ---------------------------------------------------------------------------

// CotangentCoboundaryConormal — in a universe for R and S, the
// coboundary of a 0-cochain h is C of the restriction of D_h to I, and
// C(γ) is a coboundary exactly when γ is the restriction to I of a
// derivation of P over R into N.
var CotangentCoboundaryConormal = cotangentCoboundaryConormalThm{family.Add(registry.ProofEntry{
	Name: "CotangentCoboundaryConormal",
	Key:  "prop_d046a7414f2dce4b",
	Reading: "The coboundaries are the image of the coboundary out of degree " +
		"0, and every derivation of P is D_h for h its values at the variables " +
		"(FreeAlgebraDerivationRepresentation): so the conormal maps whose class " +
		"vanishes are exactly the restrictions of derivations, B^1 ↔ Der_R(P, N)|_I.",
	Deps: []registry.EntryLike{
		CotangentLowCoboundaries,
		ConormalToCocycleDef,
		CocycleConormalLinearInverse,
		partial_derivative.FreeAlgebraDerivationFromValues,
		partial_derivative.FreeAlgebraDerivationRepresentation,
		partial_derivative.DerivationRestrictionConormal,
		partial_derivative.DerivationOn,
		chain_complex.CoboundariesSucc,
		cotangent_complex.CotangentCochainComplex,
		standard_resolution.StandardRepresentativeLaws,
		standard_resolution.StandardEpsHom,
		standard_resolution.StandardNamesDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseAlgebraConstDef,
		simplicial_ring.UniverseAlgebraDef,
		free_algebra.FreeAlgebraRingDef,
		free_algebra.FreeAlgebraVarIn,
		function_module.FunModuleDef,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "(∀h:(U → D). " +
			"    h ∈ cotangent_cochain(R, S, f, S, λy:B. y, N).terms(0) ⇒ " +
			"    cotangent_cochain(R, S, f, S, λy:B. y, N).d(0)(h) = " +
			"    conormal_to_cocycle(R, " +
			"        S, " +
			"        f, " +
			"        N, " +
			"        λx:U. " +
			"            COND(x ∈ ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
			"                free_algebra_derivation(universe_embedding(R), " +
			"                    R, " +
			"                    standard_names(R, S, 0), " +
			"                    standard_eps(R, S, f), " +
			"                    N, " +
			"                    h, " +
			"                    x), " +
			"                N.zero))) ∧ " +
			"(∀γ:(U → D). " +
			"    conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        S, " +
			"        standard_eps(R, S, f), " +
			"        N, " +
			"        γ) ⇒ " +
			"    (conormal_to_cocycle(R, S, f, N, γ) ∈ " +
			"        coboundaries(cotangent_cochain(R, S, f, S, λy:B. y, N), 1) ⇔ " +
			"        ∃d:(U → D). " +
			"            derivation_on(R, " +
			"                universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"                universe_algebra_const(R), " +
			"                scalar_restriction(standard_eps(R, S, f), N), " +
			"                d) ∧ " +
			"            γ = " +
			"            λx:U. " +
			"                COND(x ∈ ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
			"                    d(x), " +
			"                    N.zero)))",
	},
		"the first conjunct at u in P: C(D_h|_I)(u) = D_h(u − τ(u)) = D_h(u) − D_h(τ(u)), D_h "+
			"additive (FreeAlgebraDerivationFromValues) and u − τ(u) in I (StandardRepresentativeLaws), "+
			"which is the coboundary by CotangentLowCoboundaries; off P both are N.zero. The coboundaries "+
			"of degree 1 are the image of d(0) (CoboundariesSucc at CotangentCochainComplex). ⇐: for a "+
			"derivation d take h(t) = d(var t) on the names of degree 0 and N.zero off them, a 0-cochain "+
			"(FunModuleDef, FreeAlgebraVarIn); D_h = d on P (FreeAlgebraDerivationRepresentation, P's "+
			"ring record being the free algebra at the universe embedding, UniverseAlgebraRingDef, "+
			"FreeAlgebraRingDef), so d(0)(h) = C(d|_I) = C(γ). ⇒: C(γ) = d(0)(h) = C(D_h|_I), and D_h|_I "+
			"is a conormal map (DerivationRestrictionConormal), so γ = G(C(γ)) = G(C(D_h|_I)) = D_h|_I "+
			"(CocycleConormalLinearInverse), D_h a derivation"),
})}

// ---------------------------------------------------------------------------
// D^1 as conormal maps modulo derivations
// ---------------------------------------------------------------------------

// ConormalClassSurjective — in a universe for R and S, the class of a
// conormal map is a member of D^1(S/R, N), and every member of D^1 is the
// class of a conormal map.
var ConormalClassSurjective = conormalClassSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "ConormalClassSurjective",
	Key:  "prop_aa06dacd10645ef7",
	Reading: "The representing conormal map of a class ξ is G(c) " +
		"for any cocycle c in ξ: its class is [C(G(c))] = [c] = ξ.",
	Deps: []registry.EntryLike{
		ConormalClassDef,
		ConormalToCocycle,
		CocycleToConormal,
		CocycleConormalLinearInverse,
		cotangent_complex.CotangentCohomologyDef,
		chain_complex.CohomologyModuleDef,
		submodule.QuotientModuleDef,
		module_record.RestrictModuleDef,
		chain_complex.ComplexModuleDef,
		quotient_group.LeftCosetsDef,
		quotient_group.InLeftCosets,
		cotangent_complex.CotangentCochainDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "(∀γ:(U → D). " +
			"    conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        S, " +
			"        standard_eps(R, S, f), " +
			"        N, " +
			"        γ) ⇒ " +
			"    conormal_class(R, S, f, N, γ) ∈ cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).carrier) ∧ " +
			"(∀ξ:set(U → D). " +
			"    ξ ∈ cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).carrier ⇒ " +
			"    ∃γ:(U → D). " +
			"        conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"            S, " +
			"            standard_eps(R, S, f), " +
			"            N, " +
			"            γ) ∧ " +
			"        conormal_class(R, S, f, N, γ) = ξ)",
	},
		"the carrier of D^1 is the set of cosets of the coboundaries of degree 1 at the cocycles "+
			"under the cochains' sum, fun_add (CotangentCohomologyDef, CohomologyModuleDef, "+
			"QuotientModuleDef, RestrictModuleDef, ComplexModuleDef, CotangentCochainDef, "+
			"LeftCosetsDef), so the class of γ is a member, C(γ) being a cocycle (ConormalToCocycle, "+
			"ConormalClassDef). A member ξ is the coset of a cocycle c (InLeftCosets); G(c) is a "+
			"conormal map (CocycleToConormal) with C(G(c)) = c (CocycleConormalLinearInverse)"),
})}

// ConormalClassEqIffDerivation — in a universe for R and S, two conormal
// maps have one class in D^1(S/R, N) exactly when their difference is the
// restriction to I of a derivation of P over R into N.
var ConormalClassEqIffDerivation = conormalClassEqIffDerivationThm{family.Add(registry.ProofEntry{
	Name: "ConormalClassEqIffDerivation",
	Key:  "prop_5d3762680d66b7b0",
	Reading: "With ConormalClassSurjective this is D^1(S/R, N) ≅ Hom_P(I, N) / Der_R(P, N)|_I, read " +
		"on the standard presentation P = R[S], with no module I/I² formed. The difference is γ₂ − γ₁ " +
		"pointwise; the class equation is symmetric, so the sign of d is the one convention to keep.",
	Deps: []registry.EntryLike{
		ConormalClassDef,
		CotangentCoboundaryConormal,
		CocycleConormalLinearInverse,
		ConormalToCocycle,
		partial_derivative.ConormalHom,
		group.LeftCosetEqOn,
		group.SubgroupDef,
		chain_complex.CochainComplex,
		cotangent_complex.CotangentCochainComplex,
		chain_complex.CoboundariesSucc,
		module.AddGroupOn,
		module.AddComm,
		function_module.FunAddDef,
		function_module.FunNegDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀γ₁ γ₂:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), S, standard_eps(R, S, f), N, γ₁)",
			"conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), S, standard_eps(R, S, f), N, γ₂)",
		},
		Conclusion: "conormal_class(R, S, f, N, γ₁) = conormal_class(R, S, f, N, γ₂) ⇔ " +
			"∃d:(U → D). " +
			"    derivation_on(R, " +
			"        universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"        universe_algebra_const(R), " +
			"        scalar_restriction(standard_eps(R, S, f), N), " +
			"        d) ∧ " +
			"    fun_add(γ₂, fun_neg(γ₁)) = " +
			"    λx:U. " +
			"        COND(x ∈ ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
			"            d(x), " +
			"            N.zero)",
	},
		"the two classes are cosets of the coboundaries, a subgroup of the cochains of degree 1 "+
			"under fun_add (CotangentCochainComplex, CoboundariesSucc, the image of a homomorphism), so "+
			"they are equal exactly when −C(γ₁) + C(γ₂) is a coboundary (LeftCosetEqOn at the cochains' "+
			"additive group). That cochain is C(γ₂ − γ₁) by the linearity of C "+
			"(CocycleConormalLinearInverse, AddComm), γ₂ − γ₁ is a conormal map (ConormalHom, "+
			"pointwise), and CotangentCoboundaryConormal turns its being a coboundary into the derivation"),
})}
