// first_variable.go — first-variable maps induced by the canonical resolution functor.

package tor_ext

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TorMapLeftDef — tensor the canonical chain map with the identity, then take homology.
var TorMapLeftDef = torMapLeftDefThm{family.Define(registry.DefEntry{
	Name:  "TorMapLeftDef",
	Const: "tor_map_left",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(B → C) → " +
		"module_ops(A, D) → " +
		"num → " +
		"set(set(prod(num, prod(A, B))) → D) → " +
		"set(set(prod(num, prod(A, C))) → D)",
	Key: "prop_923b426cd0f0c821",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"    tor_map_left(R, M, L, f, N, n) = " +
			"    homology_map(canonical_tensor_complex(R, L, N), " +
			"        (λk:num. finite_supp_map(R, N, canonical_map(R, M, L, f, k))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalTensorComplexDef, FiniteSuppMapDef},
})}

// ExtMapLeftDef — precompose with the canonical chain map, then take cohomology; the first variable is contravariant.
var ExtMapLeftDef = extMapLeftDefThm{family.Define(registry.DefEntry{
	Name:  "ExtMapLeftDef",
	Const: "ext_map_left",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(B → C) → " +
		"module_ops(A, D) → " +
		"num → " +
		"set(set(prod(num, prod(A, C))) → D) → " +
		"set(set(prod(num, prod(A, B))) → D)",
	Key: "prop_2d09f30d2842e296",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"    ext_map_left(R, M, L, f, N, n) = " +
			"    cohomology_map(canonical_hom_complex(R, M, N), " +
			"        (λk:num. " +
			"            hom_precompose(R, " +
			"                N, " +
			"                canonical_resolution_terms(R, M, k), " +
			"                canonical_map(R, M, L, f, k))), " +
			"        n)",
	},
	Deps: []registry.EntryLike{CanonicalHomComplexDef},
})}

// TorMapLeftHom — The canonical lift induces a map of tensor complexes; pass to the quotient module.
var TorMapLeftHom = torMapLeftHomThm{family.Add(registry.ProofEntry{
	Name: "TorMapLeftHom",
	Key:  "prop_138689d74689f87f",
	Deps: []registry.EntryLike{
		TensorComplex,
		TorMapLeftDef,
		TorModuleDef,
		resolution.CanonicalResolution,
		resolution.CanonicalMapChain,
		TensorChainMap,
		chain_complex.HomologyMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    tor_module(R, M, N, n), " +
			"    tor_module(R, L, N, n), " +
			"    tor_map_left(R, M, L, f, N, n))",
	}, "The canonical lift induces a map of tensor complexes; pass to the quotient module."),
})}

// TorMapLeftIdentity — CanonicalMapIdentity holds on the free carrier. Its tensor map is the identity on the function carrier, hence on classes.
var TorMapLeftIdentity = torMapLeftIdentityThm{family.Add(registry.ProofEntry{
	Name: "TorMapLeftIdentity",
	Key:  "prop_c9c7f10ce546cd14",
	Deps: []registry.EntryLike{
		resolution.CanonicalResolution,
		module_homomorphism.HomSource,
		module_homomorphism.HomTarget,
		resolution.CanonicalMapChain,
		TensorComplex,
		TensorChainMap,
		module_homomorphism.HomIdentity,
		TorMapLeftDef,
		TorDef,
		resolution.CanonicalMapIdentity,
		chain_complex.HomologyMapCoset,
		FiniteSuppMapDef,
		free_module.FreeModuleExpand,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_map_left(R, M, M, λu:B. u, N, n, s) = s",
	},
		"CanonicalMapIdentity holds on the free carrier. Its tensor "+
			"map is the identity on the function carrier, hence on classes."),
})}

// TorMapLeftCompose — CanonicalMapCompose gives equality on each free carrier. Tensoring respects that equality. Evaluate the induced maps on quotient representatives.
var TorMapLeftCompose = torMapLeftComposeThm{family.Add(registry.ProofEntry{
	Name: "TorMapLeftCompose",
	Key:  "prop_8072fb41aaa9c10f",
	Deps: []registry.EntryLike{
		resolution.CanonicalResolution,
		module_homomorphism.HomSource,
		module_homomorphism.HomTarget,
		resolution.CanonicalMapChain,
		TensorComplex,
		TensorChainMap,
		module_homomorphism.HomIdentity,
		TorMapLeftDef,
		TorDef,
		TorMapLeftHom,
		resolution.CanonicalMapCompose,
		chain_complex.HomologyMapCoset,
		FiniteSuppMapDef,
		free_module.FreeModuleExpand,
		free_module.FreeLiftUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀K:module_ops(A, E). " +
			"∀g:(C → E). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
			"module_homomorphism(R, L, K, g)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_map_left(R, M, K, g ∘ f, N, n, s) = " +
			"tor_map_left(R, L, K, g, N, n, tor_map_left(R, M, L, f, N, n, s))",
	},
		"CanonicalMapCompose gives equality on each free carrier. Tensoring respects "+
			"that equality. Evaluate the induced maps on quotient representatives."),
})}

// TorMapLeftCongruence — the map induced in the first variable reads its
// map only on M's carrier: two maps that agree there induce one map on
// each Tor.
var TorMapLeftCongruence = torMapLeftCongruenceThm{family.Add(registry.ProofEntry{
	Name: "TorMapLeftCongruence",
	Key:  "prop_821bdd542310b14f",
	Reading: "The canonical lift of f between canonical resolutions reads f at preimages " +
		"chosen inside M's carrier, in degree zero and, through them, in every degree; so f " +
		"and an f' equal to it on the carrier have the same lift and the same induced map.",
	Deps: []registry.EntryLike{TorMapLeftDef, TorMapLeftHom, TorDef, set_basic.Extension},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f f':(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
			"∀u:B. u ∈ M.carrier ⇒ f'(u) = f(u)",
			"s ∈ tor(R, M, N, n)",
		},
		Conclusion: "tor_map_left(R, M, L, f', N, n, s) = tor_map_left(R, M, L, f, N, n, s)",
	},
		"the canonical map between the canonical resolutions reads f only at members of M's "+
			"carrier (its degree-zero step at the chosen preimages, higher degrees through those), "+
			"so the lifts of f and f' coincide and so do the induced maps on Tor (TorMapLeftDef)"),
})}

// ExtMapLeftHom — a homomorphism f from M to L induces a linear map from
// Ext^n(L, N) to Ext^n(M, N): the canonical lift of f is a chain map of the
// canonical free resolutions, so precomposing with it is a cochain map of
// their Hom complexes, which induces a homomorphism on cohomology.
var ExtMapLeftHom = extMapLeftHomThm{family.Add(registry.ProofEntry{
	Name: "ExtMapLeftHom",
	Key:  "prop_4f6dd2079333b90d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    ext_module(R, L, N, n), " +
			"    ext_module(R, M, N, n), " +
			"    ext_map_left(R, M, L, f, N, n))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			L *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			N *Expr[ModuleOps[A, D]],
			n *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism",
				"N is a module")
			hom, moduleN := parts[0], parts[1]
			lift := a.Have(
				"f lifts to the canonical chain map between the "+
					"free complexes of M's and L's canonical resolutions",
				"chain_map(R, "+
					"    free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)), "+
					"    free_complex(R, canonical_resolution_terms(R, L), canonical_boundary(R, L)), "+
					"    canonical_map(R, M, L, f))",
				By(resolution.CanonicalMapChain.Read(hom)))
			cochain := a.Have(
				"so precomposition with the lift is a cochain map "+
					"from the Hom complex of L's resolution to that of M's",
				"cochain_map(R, "+
					"    canonical_hom_complex(R, L, N), "+
					"    canonical_hom_complex(R, M, N), "+
					"    λk:num. "+
					"        hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, L, f, k)))",
				Simp(Fwd(CanonicalHomComplexDef)),
				By(
					moduleN,
					lift,
					HomCochainMap,
					resolution.ResolutionComplex.Read(
						resolution.CanonicalResolution.Read(module_homomorphism.HomSource.Read(hom))),
					resolution.ResolutionComplex.Read(
						resolution.CanonicalResolution.Read(module_homomorphism.HomTarget.Read(hom)))))
			complexes := a.Have(
				"both Hom complexes are cochain complexes",
				"cochain_complex(R, canonical_hom_complex(R, L, N)) ∧ "+
					"cochain_complex(R, canonical_hom_complex(R, M, N))",
				By(
					moduleN,
					module_homomorphism.HomSource.Read(hom),
					module_homomorphism.HomTarget.Read(hom),
					CanonicalHomComplex))
			a.Show(
				"a cochain map induces a homomorphism between the cohomology modules, which are the Ext modules",
				Simp(Fwd(ExtModuleDef), Fwd(ExtMapLeftDef), Fwd(chain_complex.CohomologyModuleDef)),
				By(chain_complex.CohomologyMapHom, complexes, cochain))
		}),
})}

// ExtMapLeftIdentity — the identity of M induces the identity on every Ext^n(M, N): a class of
// Ext^n(M, N) is a class of the canonical Hom complex; the canonical map at the identity is the
// identity on each free term, so its transpose fixes every cochain, and maps agreeing with the
// identity cochain map on the terms induce its map on cohomology, which fixes every class.
var ExtMapLeftIdentity = extMapLeftIdentityThm{family.Add(registry.ProofEntry{
	Name: "ExtMapLeftIdentity",
	Key:  "prop_971a416ed440cbc1",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, B))) → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"s ∈ ext(R, M, N, n)",
		},
		Conclusion: "ext_map_left(R, M, M, λu:B. u, N, n, s) = s",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, D]],
			modules Fact,
			n *Expr[Nat],
			s *Expr[Set[Fun[Set[Prod[Nat, Prod[A, B]]], D]]],
			class Fact,
		) {
			complex := a.Have(
				"the Hom complex of M's canonical resolution into N is a cochain complex",
				"cochain_complex(R, canonical_hom_complex(R, M, N))",
				By(modules, CanonicalHomComplex.At(R, M, N)))
			inCohomology := a.Have(
				"Ext^n(M, N) is the cohomology of that complex in degree n, so s is one of its classes",
				"s ∈ cohomology(canonical_hom_complex(R, M, N), n)",
				By(Normalized, class, ExtAsCohomology.At(R, M, N, n)))
			identity := a.Have(
				"the identity is a cochain map of the Hom complex",
				"cochain_map(R, "+
					"    canonical_hom_complex(R, M, N), "+
					"    canonical_hom_complex(R, M, N), "+
					"    λm:num. λx:(set(prod(num, prod(A, B))) → D). x)",
				By(chain_complex.CochainMapIdentity.Read(complex)))
			agreement := a.Have(
				"on the terms of the Hom complex the transpose of "+
					"the canonical map at the identity is the identity",
				Statement{
					Binders: "∀k:num. ∀g:(set(prod(num, prod(A, B))) → D).",
					Hypotheses: []string{
						"g ∈ canonical_hom_complex(R, M, N).terms(k)",
					},
					Conclusion: "hom_precompose(R, " +
						"    N, " +
						"    canonical_resolution_terms(R, M, k), " +
						"    canonical_map(R, M, M, λu:B. u, k), " +
						"    g) = " +
						"g",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					g := b.FixAs[Fun[Set[Prod[Nat, Prod[A, B]]], D]]("g")
					inFunctions := b.Unfolded(b.Assume(), CanonicalHomComplexDef)
					generators := b.TermAs[Set[Set[Prod[Nat, Prod[A, B]]]]]("canonical_resolution_terms(R, M, k)")
					fixes := b.Have(
						"the canonical map at the identity is the identity on the free term of degree k",
						Statement{
							Binders: "∀a:(set(prod(num, prod(A, B))) → A).",
							Hypotheses: []string{
								"a ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, k))",
							},
							Conclusion: "canonical_map(R, M, M, λu:B. u, k, a) = a",
						},
						By(modules, resolution.CanonicalMapIdentity))
					same := b.Have(
						"so it has the identity's transpose",
						"hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, M, λu:B. u, k)) = "+
							"hom_precompose(R, N, canonical_resolution_terms(R, M, k), λa:(set(prod(num, prod(A, B))) → A). a)",
						By(
							fixes,
							modules,
							free_module.HomPrecomposeCongruence.At(R, N, generators,
								b.TermAs[Fun2[Fun[Set[Prod[Nat, Prod[A, B]]], A], Set[Prod[Nat, Prod[A, B]]], A]](
									"canonical_map(R, M, M, λu:B. u, k)"),
								b.TermAs[Fun2[Fun[Set[Prod[Nat, Prod[A, B]]], A], Set[Prod[Nat, Prod[A, B]]], A]](
									"λa:(set(prod(num, prod(A, B))) → A). a"))))
					b.Show(
						"the transpose of the identity fixes g, an N-valued function on the generators of degree k",
						By(same, inFunctions, modules, free_module.HomPrecomposeIdentity.At(R, N, generators, g)))
				}))
			// The Hom complex, the identity cochain map on it, and the transposes of the canonical map
			// at the identity.
			hom := a.TermAs[chain_complex.ComplexOps[A, Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
				"canonical_hom_complex(R, M, N)")
			identityMap := a.TermAs[Fun2[Nat, Fun[Set[Prod[Nat, Prod[A, B]]], D], Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
				"λm:num. λx:(set(prod(num, prod(A, B))) → D). x")
			transposes := a.TermAs[Fun2[Nat, Fun[Set[Prod[Nat, Prod[A, B]]], D], Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
				"λk:num. " +
					"    hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, M, λu:B. u, k))")
			a.Show(
				"the map Ext^n(M, N) → Ext^n(M, N) of the identity fixes the class s",
				CalcEq(
					Leg(
						a.TermAs[Set[Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
							"cohomology_map(canonical_hom_complex(R, M, N), "+
								"    λk:num. "+
								"        hom_precompose(R, "+
								"            N, "+
								"            canonical_resolution_terms(R, M, k), "+
								"            canonical_map(R, M, M, λu:B. u, k)), "+
								"    n, "+
								"    s)"),
						"ext_map_left is the map on cohomology of the transposes of the canonical map",
						Unfold(ExtMapLeftDef)),
					Leg(
						a.TermAs[Set[Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
							"cohomology_map(canonical_hom_complex(R, M, N), "+
								"    λm:num. λx:(set(prod(num, prod(A, B))) → D). x, "+
								"    n, "+
								"    s)"),
						"the transposes agree with the identity cochain map "+
							"on the terms, so they induce its map on cohomology",
						By(
							agreement,
							complex,
							inCohomology,
							identity,
							chain_complex.CohomologyMapCongruence.At(R, hom, hom, identityMap, transposes, n, s))),
					FinalLeg(
						"the identity induces the identity on cohomology",
						By(complex, inCohomology, chain_complex.CohomologyMapIdentity.At(R, hom, n, s))),
				))
		}),
})}

// ExtMapLeftCompose — Ext in the first variable takes a composite g ∘ f to the
// map of f after the map of g: the canonical lifts are chain maps, so their
// transposes are cochain maps of the Hom complexes; the transpose of g ∘ f agrees
// on the terms with that of f after that of g, and cohomology composes the maps.
var ExtMapLeftCompose = extMapLeftComposeThm{family.Add(registry.ProofEntry{
	Name: "ExtMapLeftCompose",
	Key:  "prop_deb889ed3f68d72",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀K:module_ops(A, E). " +
			"∀g:(C → E). " +
			"∀n:num. " +
			"∀s:set(set(prod(num, prod(A, E))) → D).",
		Hypotheses: []string{
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
			"module_homomorphism(R, L, K, g)",
			"s ∈ ext(R, K, N, n)",
		},
		Conclusion: "ext_map_left(R, M, K, g ∘ f, N, n, s) = " +
			"ext_map_left(R, M, L, f, N, n, ext_map_left(R, L, K, g, N, n, s))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			L *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			N *Expr[ModuleOps[A, D]],
			fHyps Fact,
			K *Expr[ModuleOps[A, E]],
			g *Arrow[C, E],
			gHom Fact,
			n *Expr[Nat],
			s *Expr[Set[Fun[Set[Prod[Nat, Prod[A, E]]], D]]],
			sIn Fact,
		) {
			given := a.Conjuncts(
				fHyps,
				"f is a homomorphism",
				"N is a module")
			fHom, moduleN := given[0], given[1]
			moduleM, moduleL, moduleK :=
				module_homomorphism.HomSource.Read(fHom),
				module_homomorphism.HomTarget.Read(fHom),
				module_homomorphism.HomTarget.Read(gHom)
			// The free complexes of the three canonical resolutions are chain complexes.
			freeM := resolution.ResolutionComplex.Read(resolution.CanonicalResolution.Read(moduleM))
			freeL := resolution.ResolutionComplex.Read(resolution.CanonicalResolution.Read(moduleL))
			freeK := resolution.ResolutionComplex.Read(resolution.CanonicalResolution.Read(moduleK))

			liftF := a.Have(
				"f lifts to a chain map between the free complexes of the canonical resolutions of M and L",
				"chain_map(free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)), "+
					"    free_complex(R, canonical_resolution_terms(R, L), canonical_boundary(R, L)), "+
					"    canonical_map(R, M, L, f))",
				By(fHom, resolution.CanonicalMapChain))
			liftG := a.Have(
				"and g to one between those of L and K",
				"chain_map(free_complex(R, canonical_resolution_terms(R, L), canonical_boundary(R, L)), "+
					"    free_complex(R, canonical_resolution_terms(R, K), canonical_boundary(R, K)), "+
					"    canonical_map(R, L, K, g))",
				By(gHom, resolution.CanonicalMapChain))
			gfHom := a.Have(
				"g ∘ f is a homomorphism from M to K",
				"module_homomorphism(R, M, K, g ∘ f)",
				By(fHom, gHom, module_homomorphism.HomCompose))
			liftGF := a.Have(
				"so it lifts to a chain map between those of M and K",
				"chain_map(free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)), "+
					"    free_complex(R, canonical_resolution_terms(R, K), canonical_boundary(R, K)), "+
					"    canonical_map(R, M, K, g ∘ f))",
				By(gfHom, resolution.CanonicalMapChain))

			cochainF := a.Have(
				"so precomposing with the lift of f is a cochain map from the Hom complex of L into N to that of M",
				"cochain_map(R, "+
					"    canonical_hom_complex(R, L, N), "+
					"    canonical_hom_complex(R, M, N), "+
					"    λk:num. "+
					"        hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, L, f, k)))",
				Unfold(CanonicalHomComplexDef),
				By(moduleN, freeM, freeL, liftF, HomCochainMap))
			cochainG := a.Have(
				"precomposing with the lift of g, one from the Hom complex of K to that of L",
				"cochain_map(R, "+
					"    canonical_hom_complex(R, K, N), "+
					"    canonical_hom_complex(R, L, N), "+
					"    λk:num. "+
					"        hom_precompose(R, N, canonical_resolution_terms(R, L, k), canonical_map(R, L, K, g, k)))",
				Unfold(CanonicalHomComplexDef),
				By(moduleN, freeL, freeK, liftG, HomCochainMap))
			cochainGF := a.Have(
				"and precomposing with the lift of g ∘ f, one from the Hom complex of K to that of M",
				"cochain_map(R, "+
					"    canonical_hom_complex(R, K, N), "+
					"    canonical_hom_complex(R, M, N), "+
					"    λk:num. "+
					"        hom_precompose(R, "+
					"            N, "+
					"            canonical_resolution_terms(R, M, k), "+
					"            canonical_map(R, M, K, g ∘ f, k)))",
				Unfold(CanonicalHomComplexDef),
				By(moduleN, freeM, freeK, liftGF, HomCochainMap))

			agree := a.Have(
				"on the terms of the Hom complex of K, the transpose "+
					"of the lift of g ∘ f is that of f after that of g",
				Statement{
					Binders: "∀k:num. ∀x:(set(prod(num, prod(A, E))) → D).",
					Hypotheses: []string{
						"x ∈ canonical_hom_complex(R, K, N).terms(k)",
					},
					Conclusion: "hom_precompose(R, " +
						"    N, " +
						"    canonical_resolution_terms(R, M, k), " +
						"    canonical_map(R, M, K, g ∘ f, k), " +
						"    x) = " +
						"hom_precompose(R, " +
						"    N, " +
						"    canonical_resolution_terms(R, M, k), " +
						"    canonical_map(R, M, L, f, k), " +
						"    hom_precompose(R, N, canonical_resolution_terms(R, L, k), canonical_map(R, L, K, g, k), x))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.FixAs[Fun[Set[Prod[Nat, Prod[A, E]]], D]]("x")
					// x is an N-valued function on the generators of K's resolution in degree k.
					function := b.Simplified(b.Assume(), Fwd(CanonicalHomComplexDef), Fwd(HomComplexOf))
					// In degree k each lift is linear between the free modules on the generators.
					linearF := b.Simplified(
						chain_complex.ChainMapHom.Read(liftF).At(k),
						Fwd(chain_complex.ComplexModuleDef),
						Fwd(resolution.FreeComplexOf),
						Rev(free_module.FreeModuleRecordDef))
					linearG := b.Simplified(
						chain_complex.ChainMapHom.Read(liftG).At(k),
						Fwd(chain_complex.ComplexModuleDef),
						Fwd(resolution.FreeComplexOf),
						Rev(free_module.FreeModuleRecordDef))
					sameTranspose := b.Have(
						"the lift of g ∘ f is the lift of g after that of "+
							"f on the free module, so the two have one transpose",
						"hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, K, g ∘ f, k)) = "+
							"hom_precompose(R, "+
							"    N, "+
							"    canonical_resolution_terms(R, M, k), "+
							"    λa:(set(prod(num, prod(A, B))) → A). "+
							"        canonical_map(R, L, K, g, k, canonical_map(R, M, L, f, k, a)))",
						By(moduleN, fHom, gHom, free_module.HomPrecomposeCongruence, resolution.CanonicalMapCompose))
					b.Show(
						"and the transpose of a composite of linear maps is "+
							"the composite of their transposes in the other order",
						sameTranspose.Rw(),
						By(
							moduleN,
							function,
							linearF,
							linearG,
							Where(
								free_module.HomPrecomposeCompose,
								"Ψ",
								b.TermAs[Fun2[Fun[Set[Prod[Nat, Prod[A, C]]], A], Set[Prod[Nat, Prod[A, E]]], A]](
									"canonical_map(R, L, K, g, k)"))))
				}))

			complexes := a.Have(
				"the Hom complexes of K, L and M into N are cochain complexes",
				"cochain_complex(R, canonical_hom_complex(R, K, N)) ∧ "+
					"cochain_complex(R, canonical_hom_complex(R, L, N)) ∧ "+
					"cochain_complex(R, canonical_hom_complex(R, M, N))",
				By(moduleN, moduleK, moduleL, moduleM, CanonicalHomComplex))
			inCohomology := a.Have(
				"s is a cohomology class of the Hom complex of K",
				"s ∈ cohomology(canonical_hom_complex(R, K, N), n)",
				By(sIn, ExtAsCohomology))
			a.Show(
				"Ext of g ∘ f is Ext of f after Ext of g",
				Simp(Fwd(ExtMapLeftDef)),
				CalcEq(
					Leg(
						a.TermAs[Set[Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
							"cohomology_map(canonical_hom_complex(R, M, N), "+
								"    λm:num. λx:(set(prod(num, prod(A, E))) → D). "+
								"        hom_precompose(R, "+
								"            N, "+
								"            canonical_resolution_terms(R, M, m), "+
								"            canonical_map(R, M, L, f, m), "+
								"            hom_precompose(R, "+
								"                N, "+
								"                canonical_resolution_terms(R, L, m), "+
								"                canonical_map(R, L, K, g, m), "+
								"                x)), "+
								"    n, "+
								"    s)"),
						"cochain maps that agree on the terms induce one map on cohomology",
						By(complexes, cochainGF, agree, inCohomology, chain_complex.CohomologyMapCongruence)),
					FinalLeg(
						"a composite of cochain maps induces the composite of the induced maps",
						By(
							complexes,
							cochainG,
							cochainF,
							inCohomology,
							Where(chain_complex.CohomologyMapCompose, "g",
								a.TermAs[Fun2[Nat, Fun[Set[Prod[Nat, Prod[A, C]]], D], Fun[Set[Prod[Nat, Prod[A, B]]], D]]](
									"λk:num. "+
										"    hom_precompose(R, N, canonical_resolution_terms(R, M, k), canonical_map(R, M, L, f, k))")))),
				))
		}),
})}
