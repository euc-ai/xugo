// Smooth pullback induces a contravariant functor on de Rham cohomology.

package de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PullbackCochain = pullbackCochainThm{family.Add(registry.ProofEntry{
	Name: "PullbackCochain",
	Key:  "prop_88a010cca7023224",
	Reading: "The cochain map runs from the target complex to the source complex. " +
		"Smooth-map membership includes both manifold predicates, even for empty carriers.",
	Deps: []registry.EntryLike{
		Complex,
		ComplexDef,
		differential_form.PullbackLinear,
		differential_form.PullbackExteriorDerivative,
		chain_complex.CochainMapDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "cochain_map(real_ring, " +
			"    de_rham_complex⟨m⟩(S, ℬ), " +
			"    de_rham_complex⟨n⟩(T, 𝒜), " +
			"    λq:num. manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f))",
	},
		"The degree modules of each de Rham complex are the corresponding manifold "+
			"form modules. PullbackLinear supplies the degreewise homomorphisms and "+
			"PullbackExteriorDerivative supplies the commuting squares."),
})}

// PullbackCocycle — pulling a k-cocycle of the target's de Rham complex
// back along a smooth map gives a k-cocycle of the source's: pullback is
// a cochain map between the two de Rham complexes, and a cochain map
// carries cocycles to cocycles.
var PullbackCocycle = pullbackCocycleThm{family.Add(registry.ProofEntry{
	Name: "PullbackCocycle",
	Key:  "prop_9e687fe23080bf21",
	Build: family.Theorem(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"ω ∈ cocycles(de_rham_complex⟨m⟩(S, ℬ), k)",
		},
		Conclusion: "manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω) ∈ " +
			"cocycles(de_rham_complex⟨n⟩(T, 𝒜), k)",
	},
		func(
			a *Argument,
			n, m, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			S *Expr[Set[Set[B]]],
			ℬ *Expr[Set[Prod[Set[B], Fun2[B, Nat, Real]]]],
			f *Arrow[A, B],
			ω *Expr[Fun3[Prod[Set[B], Fun2[B, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			smooth, cocycle Fact,
		) {
			target := a.Have(
				"the target's de Rham complex is a cochain complex",
				"cochain_complex(real_ring, de_rham_complex⟨m⟩(S, ℬ))",
				By(smooth, smooth_manifold.SmoothMapDef, Complex))
			source := a.Have(
				"so is the source's",
				"cochain_complex(real_ring, de_rham_complex⟨n⟩(T, 𝒜))",
				By(smooth, smooth_manifold.SmoothMapDef, Complex))
			pullback := a.Have(
				"pullback along f is a cochain map",
				"cochain_map(real_ring, "+
					"    de_rham_complex⟨m⟩(S, ℬ), "+
					"    de_rham_complex⟨n⟩(T, 𝒜), "+
					"    λq:num. manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f))",
				By(smooth, PullbackCochain))
			a.Show(
				"a cochain map carries cocycles to cocycles",
				By(
					source,
					pullback,
					cocycle,
					chain_complex.CochainMapCocycles.Read(target).At(
						a.TermAs[chain_complex.ComplexOps[
							Real,
							Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real],
						]]("de_rham_complex⟨n⟩(T, 𝒜)"),
						a.TermAs[Fun2[
							Nat,
							Fun3[Prod[Set[B], Fun2[B, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real],
							Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real],
						]]("λq:num. manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f)"),
						k)))
		}),
})}

var PullbackHom = pullbackHomThm{family.Add(registry.ProofEntry{
	Name: "PullbackHom",
	Key:  "prop_a4addc57667f810f",
	Deps: []registry.EntryLike{
		Complex,
		PullbackCochain,
		PullbackDef,
		CohomologyModuleDef,
		chain_complex.CohomologyMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num. " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    de_rham_cohomology_module⟨m⟩(S, ℬ, k), " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
			"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f))",
	},
		"Apply CohomologyMapHom to the degreewise pullback "+
			"cochain map, then identify both named quotient modules."),
})}

var PullbackClass = pullbackClassThm{family.Add(registry.ProofEntry{
	Name: "PullbackClass",
	Key:  "prop_228787798451999e",
	Deps: []registry.EntryLike{
		Complex,
		PullbackCochain,
		PullbackDef,
		ClassDef,
		chain_complex.CocyclesDef,
		chain_complex.CohomologyMapCoset,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num. " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, k, ω)",
			"manifold_exterior_derivative⟨m⟩(S, ℬ, k, ω) = " +
				"λc:prod(set(B), B → num → real). λy:(num → real). λP:(num → num → real). &0",
		},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(de_rham_class⟨m⟩(S, ℬ, k, ω)) = " +
			"de_rham_class⟨n⟩(T, 𝒜, k, manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(ω))",
	},
		"The target form is a cocycle. The generic induced-map coset theorem sends its class to the "+
			"class of its degreewise pullback, which is precisely the named de Rham pullback formula."),
})}

var PullbackCongruence = pullbackCongruenceThm{family.Add(registry.ProofEntry{
	Name: "PullbackCongruence",
	Key:  "prop_90bbc66ec109e131",
	Reading: "Equality is required only on the source manifold carrier. The " +
		"induced-map conclusion is likewise restricted to genuine target cohomology classes.",
	Deps: []registry.EntryLike{
		Complex,
		PullbackCochain,
		PullbackDef,
		CohomologyModuleDef,
		differential_form.PullbackCoordinate,
		vec_smooth.PartialDerivativeLocal,
		chain_complex.CohomologyMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num. " +
			"∀f g:(A → B). " +
			"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, g)",
			"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
			"s ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(s) = " +
			"de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, g)(s)",
	},
		"Carrier agreement makes the coordinate maps equal on each open source chart domain, so their "+
			"Jacobians and pullbacks of every target form agree there by locality. Normalization gives "+
			"agreement on whole source forms. Apply CohomologyMapCongruence on the target degree carriers."),
})}

var PullbackIdentity = pullbackIdentityThm{family.Add(registry.ProofEntry{
	Name: "PullbackIdentity",
	Key:  "prop_981868c314f70669",
	Deps: []registry.EntryLike{
		Complex,
		PullbackCochain,
		PullbackDef,
		CohomologyModuleDef,
		smooth_manifold.SmoothMapIdentity,
		differential_form.PullbackIdentity,
		chain_complex.CohomologyMapCongruence,
		chain_complex.CohomologyMapIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, n⟩(T, 𝒜, T, 𝒜, k, identity_map)(s) = s",
	},
		"Pullback by the identity agrees with the identity on every form "+
			"degree carrier. Replace the degreewise map by the identity using "+
			"CohomologyMapCongruence and apply CohomologyMapIdentity to s."),
})}

var PullbackCompose = pullbackComposeThm{family.Add(registry.ProofEntry{
	Name: "PullbackCompose",
	Key:  "prop_574d6412b42e3910",
	Deps: []registry.EntryLike{
		Complex,
		PullbackCochain,
		PullbackDef,
		CohomologyModuleDef,
		smooth_manifold.SmoothMapCompose,
		differential_form.PullbackCompose,
		chain_complex.CohomologyMapCongruence,
		chain_complex.CohomologyMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀l k:num. " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀s:set(prod(set(C), C → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, l⟩(S, ℬ, R, 𝒞, g)",
			"s ∈ de_rham_cohomology_module⟨l⟩(R, 𝒞, k).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, l⟩(T, 𝒜, R, 𝒞, k, g ∘ f)(s) = " +
			"de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(de_rham_pullback⟨m, l⟩(S, ℬ, R, 𝒞, k, g)(s))",
	},
		"The pullback of a composite agrees on every form degree with the reversed composite of "+
			"the two pullbacks. Replace that cochain map on its carriers and use CohomologyMapCompose; "+
			"the quotient maps therefore compose in the same contravariant order."),
})}
