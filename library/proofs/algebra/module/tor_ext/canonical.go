// canonical.go — Tor and Ext of two modules, evaluated on the fixed
// free resolution of the first module. Named maps describe the second
// variable and the connecting morphisms of short exact sequences.

package tor_ext

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CanonicalTensorComplexDef — the complex associated to the canonical free resolution.
var CanonicalTensorComplexDef = canonicalTensorComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalTensorComplexDef",
	Const: "canonical_tensor_complex",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, set(prod(num, prod(A, B))) → C)",
	Key: "prop_6739b7c752c8f9be",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    canonical_tensor_complex(R, M, N) = " +
			"    tensor_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M), N)",
	},
	Deps: []registry.EntryLike{TensorComplexOf},
})}

// CanonicalTensorComplex — the canonical tensor complex is a chain complex: M's
// canonical resolution is a free resolution, and TensorComplex holds at its
// free complex.
var CanonicalTensorComplex = canonicalTensorComplexThm{family.Add(registry.ProofEntry{
	Name: "CanonicalTensorComplex",
	Key:  "prop_791f2a3deca38673",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "chain_complex(R, canonical_tensor_complex(R, M, N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			modules Fact,
		) {
			given := a.Conjuncts(
				modules,
				"M is a module",
				"N is a module")
			moduleM, moduleN := given[0], given[1]
			canonical := a.Have(
				"M's canonical resolution is a free resolution",
				"free_resolution(R, "+
					"    M, "+
					"    canonical_resolution_terms(R, M), "+
					"    canonical_boundary(R, M), "+
					"    canonical_eps(R, M))",
				By(resolution.CanonicalResolution, moduleM))
			free := a.Have(
				"its free complex is a chain complex",
				"chain_complex(R, free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)))",
				By(resolution.ResolutionComplex.Read(canonical)))
			a.Show(
				"the canonical tensor complex is the tensor complex of that free complex",
				Simp(Fwd(CanonicalTensorComplexDef)),
				By(TensorComplex, moduleN, free))
		}),
})}

// TorDef — the derived functor carrier, with no resolution or size parameter.
var TorDef = torDefThm{family.Define(registry.DefEntry{
	Name:  "TorDef",
	Const: "tor",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(set(prod(num, prod(A, B))) → C))",
	Key: "prop_22b1c989fe0a617d",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    tor(R, M, N, n) = " +
			"    tor_of_resolution(R, canonical_resolution_terms(R, M), canonical_boundary(R, M), N, n)",
	},
	Deps: []registry.EntryLike{TorOfResolutionDef},
})}

// TorAsHomology — Tor is the homology of the canonical tensor complex.
var TorAsHomology = torAsHomologyThm{family.Add(registry.ProofEntry{
	Name: "TorAsHomology",
	Key:  "prop_9cd8f973f7b20cc3",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. "+
		"    tor(R, M, N, n) = homology(canonical_tensor_complex(R, M, N), n)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			n *Expr[Nat],
		) {
			a.Show(
				"both sides read the canonical resolution's complex",
				Unfold(TorDef),
				Unfold(TorOfResolutionDef),
				Unfold(CanonicalTensorComplexDef))
		}),
})}

// TorModuleDef — the derived functor with its quotient operations.
var TorModuleDef = torModuleDefThm{family.Define(registry.DefEntry{
	Name:  "TorModuleDef",
	Const: "tor_module",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"module_ops(A, set(set(prod(num, prod(A, B))) → C))",
	Key: "prop_c83896f7c1d74a27",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    tor_module(R, M, N, n) = homology_module(canonical_tensor_complex(R, M, N), n)",
	},
	Deps: []registry.EntryLike{CanonicalTensorComplexDef},
})}

// TorZeroDef — the zero class in degree n.
var TorZeroDef = torZeroDefThm{family.Define(registry.DefEntry{
	Name:  "TorZeroDef",
	Const: "tor_zero",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_4c057f8e1cca20b1",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    tor_zero(R, M, N, n) = boundaries(canonical_tensor_complex(R, M, N), n)",
	},
	Deps: []registry.EntryLike{CanonicalTensorComplexDef},
})}

// TorMapDef — the map induced in the second variable; the target record determines the quotient operations.
var TorMapDef = torMapDefThm{family.Define(registry.DefEntry{
	Name:  "TorMapDef",
	Const: "tor_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(D → C) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → D) → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_f329164db1328638",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(D → C). ∀n:num. " +
			"    tor_map(R, M, N, f, n) = " +
			"    homology_map(canonical_tensor_complex(R, M, N), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). f(g(x))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalTensorComplexDef},
})}

// TorConnectingDef — the connecting map, from degree n+1 to n for Tor and from n to n+1 for Ext.
var TorConnectingDef = torConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "TorConnectingDef",
	Const: "tor_connecting",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"module_ops(A, D) → " +
		"(C → D) → " +
		"(D → E) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → E) → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_1489f8c6dc04f915",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀i:(C → D). " +
			"∀p:(D → E). " +
			"∀n:num. " +
			"    tor_connecting(R, M, N', N, i, p, n) = " +
			"    connecting_hom(canonical_tensor_complex(R, M, N'), " +
			"        canonical_tensor_complex(R, M, N), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → C). λx:set(prod(num, prod(A, B))). i(g(x))), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). p(g(x))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalTensorComplexDef},
})}

// TorMapHom — Postcomposition acts pointwise on the function complex and commutes with the differential; pass to homology.
var TorMapHom = torMapHomThm{family.Add(registry.ProofEntry{
	Name: "TorMapHom",
	Key:  "prop_ccf21950edf35848",
	Deps: []registry.EntryLike{
		TorMapDef,
		TorModuleDef,
		resolution.CanonicalResolution,
		TensorComplex,
		chain_complex.HomologyMapHom,
		chain_complex.ChainMapDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f:(C → D). " +
			"∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, L, f)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    tor_module(R, M, N, n), " +
			"    tor_module(R, M, L, n), " +
			"    tor_map(R, M, L, f, n))",
	},
		"Postcomposition acts pointwise on the function complex "+
			"and commutes with the differential; pass to homology."),
})}

// TorMapIdentity — The pointwise identity induces the identity on each quotient carrier.
var TorMapIdentity = torMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "TorMapIdentity",
	Key:  "prop_cca0a9579e3092fd",
	Deps: []registry.EntryLike{
		resolution.CanonicalResolution,
		module_homomorphism.HomSource,
		module_homomorphism.HomTarget,
		TensorComplex,
		chain_complex.ChainMapDef,
		function_module.FiniteSuppModuleOn,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		TorMapDef,
		TorDef,
		chain_complex.HomologyMapCoset,
		module_homomorphism.HomIdentity,
		set_basic.Extension,
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
		Conclusion: "tor_map(R, M, N, λu:C. u, n, s) = s",
	}, "The pointwise identity induces the identity on each quotient carrier."),
})}

// TorMapCompose — Pointwise postcomposition composes strictly; evaluate on a representative of each quotient class.
var TorMapCompose = torMapComposeThm{family.Add(registry.ProofEntry{
	Name: "TorMapCompose",
	Key:  "prop_215e70dc11c90295",
	Deps: []registry.EntryLike{
		resolution.CanonicalResolution,
		module_homomorphism.HomSource,
		module_homomorphism.HomTarget,
		TensorComplex,
		chain_complex.ChainMapDef,
		function_module.FiniteSuppModuleOn,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		TorMapDef,
		TorDef,
		TorMapHom,
		chain_complex.HomologyMapCoset,
		module_homomorphism.HomCompose,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f:(C → D). " +
			"∀K:module_ops(A, E). " +
			"∀g:(D → E). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, L, f)",
			"module_homomorphism(R, L, K, g)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_map(R, M, K, g ∘ f, n, s) = tor_map(R, M, K, g, n, tor_map(R, M, L, f, n, s))",
	},
		"Pointwise postcomposition composes strictly; "+
			"evaluate on a representative of each quotient class."),
})}

// TorMapCongruence — the map induced in the second variable reads its map
// only on the carrier: two maps that agree on N's carrier induce one map on
// each Tor.
var TorMapCongruence = torMapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "TorMapCongruence",
	Key:  "prop_b7c1a5fbcf5bf926",
	Reading: "A class of Tor_n(M, N) is a coset of functions whose values lie in N's carrier, " +
		"and postcomposition evaluates the map only at those values; so an inverse taken with " +
		"inverse_on, which is the identity only on the carrier, composes to the identity on Tor.",
	Deps: []registry.EntryLike{
		TorMapDef,
		TorDef,
		TorMapHom,
		chain_complex.HomologyMapCoset,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f f':(C → D). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, L, f)",
			"∀u:C. u ∈ N.carrier ⇒ f'(u) = f(u)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_map(R, M, L, f', n, s) = tor_map(R, M, L, f, n, s)",
	},
		"the representatives of a class take their values in N's carrier, where f' "+
			"and f agree, so the two postcompositions agree on every representative "+
			"(TorMapDef) and the induced classes are equal (HomologyMapCoset)"),
})}

// CanonicalHomComplexDef — the complex associated to the canonical free resolution.
var CanonicalHomComplexDef = canonicalHomComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalHomComplexDef",
	Const: "canonical_hom_complex",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, set(prod(num, prod(A, B))) → C)",
	Key: "prop_be23c4d941084110",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    canonical_hom_complex(R, M, N) = " +
			"    hom_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M), N)",
	},
	Deps: []registry.EntryLike{HomComplexOf},
})}

// CanonicalHomComplex — the canonical Hom complex is a cochain complex: M's
// canonical resolution is a free resolution, and HomComplex holds at its
// free complex.
var CanonicalHomComplex = canonicalHomComplexThm{family.Add(registry.ProofEntry{
	Name: "CanonicalHomComplex",
	Key:  "prop_1f09efea3e56ab00",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "cochain_complex(R, canonical_hom_complex(R, M, N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			modules Fact,
		) {
			given := a.Conjuncts(
				modules,
				"M is a module",
				"N is a module")
			moduleM, moduleN := given[0], given[1]
			canonical := a.Have(
				"M's canonical resolution is a free resolution",
				"free_resolution(R, "+
					"    M, "+
					"    canonical_resolution_terms(R, M), "+
					"    canonical_boundary(R, M), "+
					"    canonical_eps(R, M))",
				By(resolution.CanonicalResolution, moduleM))
			free := a.Have(
				"its free complex is a chain complex",
				"chain_complex(R, free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)))",
				By(resolution.ResolutionComplex.Read(canonical)))
			a.Show(
				"the canonical Hom complex is the Hom complex of that free complex",
				Simp(Fwd(CanonicalHomComplexDef)),
				By(HomComplex, moduleN, free))
		}),
})}

// ExtDef — the derived functor carrier, with no resolution or size parameter.
var ExtDef = extDefThm{family.Define(registry.DefEntry{
	Name:  "ExtDef",
	Const: "ext",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(set(prod(num, prod(A, B))) → C))",
	Key: "prop_7c7518c1f8d7e734",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    ext(R, M, N, n) = " +
			"    ext_of_resolution(R, canonical_resolution_terms(R, M), canonical_boundary(R, M), N, n)",
	},
	Deps: []registry.EntryLike{extOfResolutionDef},
})}

// ExtAsCohomology — Ext is the cohomology of the canonical Hom complex.
var ExtAsCohomology = extAsCohomologyThm{family.Add(registry.ProofEntry{
	Name: "ExtAsCohomology",
	Key:  "prop_620929eb7b1147c0",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. "+
		"    ext(R, M, N, n) = cohomology(canonical_hom_complex(R, M, N), n)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			n *Expr[Nat],
		) {
			a.Show(
				"both sides read the canonical resolution's complex",
				Unfold(ExtDef),
				Unfold(extOfResolutionDef),
				Unfold(CanonicalHomComplexDef))
		}),
})}

// ExtModuleDef — the derived functor with its quotient operations.
var ExtModuleDef = extModuleDefThm{family.Define(registry.DefEntry{
	Name:  "ExtModuleDef",
	Const: "ext_module",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"module_ops(A, set(set(prod(num, prod(A, B))) → C))",
	Key: "prop_aec977d5b0f7ace9",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    ext_module(R, M, N, n) = cohomology_module(canonical_hom_complex(R, M, N), n)",
	},
	Deps: []registry.EntryLike{CanonicalHomComplexDef},
})}

// extZeroDef — the zero class in degree n.
var extZeroDef = extZeroDefThm{family.Define(registry.DefEntry{
	Name:  "extZeroDef",
	Const: "ext_zero",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_e3f87ea9124c47d",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num. " +
			"    ext_zero(R, M, N, n) = coboundaries(canonical_hom_complex(R, M, N), n)",
	},
	Deps: []registry.EntryLike{CanonicalHomComplexDef},
})}

// ExtMapDef — the map induced in the second variable; the target record determines the quotient operations.
var ExtMapDef = extMapDefThm{family.Define(registry.DefEntry{
	Name:  "ExtMapDef",
	Const: "ext_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(D → C) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → D) → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_d2d1a38225f1be1a",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(D → C). ∀n:num. " +
			"    ext_map(R, M, N, f, n) = " +
			"    cohomology_map(canonical_hom_complex(R, M, N), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). f(g(x))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalHomComplexDef},
})}

// ExtConnectingDef — the connecting map, from degree n+1 to n for Tor and from n to n+1 for Ext.
var ExtConnectingDef = extConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "ExtConnectingDef",
	Const: "ext_connecting",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"module_ops(A, D) → " +
		"(C → D) → " +
		"(D → E) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → E) → " +
		"set(set(prod(num, prod(A, B))) → C)",
	Key: "prop_7354cfc69f8b261b",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀i:(C → D). " +
			"∀p:(D → E). " +
			"∀n:num. " +
			"    ext_connecting(R, M, N', N, i, p, n) = " +
			"    coconnecting_hom(canonical_hom_complex(R, M, N'), " +
			"        canonical_hom_complex(R, M, N), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → C). λx:set(prod(num, prod(A, B))). i(g(x))), " +
			"        (λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). p(g(x))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalHomComplexDef},
})}
