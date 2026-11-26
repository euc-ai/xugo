// Finite bases and cohomology isomorphisms compute Betti numbers.

package de_rham_betti

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/registry"
)

var BettiAboveDimension = bettiAboveDimensionThm{family.Add(registry.ProofEntry{
	Name: "BettiAboveDimension",
	Key:  "prop_c0be76c825267ed7",
	Reading: "No finiteness hypothesis in the lower degrees is needed. Vanishing is a " +
		"statement about the cohomology carrier, not the entire host type of sets of forms.",
	Deps: []registry.EntryLike{
		BettiDef,
		de_rham.CohomologyModule,
		de_rham.CohomologyAboveDimension,
		module_dimension.FiniteCarrierFiniteDimensional,
		module_dimension.DimZero,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"n < k",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ∧ " +
			"de_rham_betti⟨n⟩(T, 𝒜, k) = 0",
	},
		"CohomologyAboveDimension makes the cohomology carrier the singleton zero class. The "+
			"finite-carrier criterion gives finite dimensionality, and DimZero computes its dimension."),
})}

var BettiBasis = bettiBasisThm{family.Add(registry.ProofEntry{
	Name: "BettiBasis",
	Key:  "prop_47f67697dfe310f2",
	Reading: "The basis is a finite set of cohomology classes, each a set of whole " +
		"normalized forms. No orientation or compactness of the manifold is required.",
	Deps: []registry.EntryLike{BettiDef, de_rham.CohomologyModule, module_dimension.FiniteBasisDim},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀B:set(set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"finite(B)",
			"module_basis(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k), B)",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ∧ " +
			"de_rham_betti⟨n⟩(T, 𝒜, k) = card(B)",
	},
		"Apply FiniteBasisDim to the degree-k cohomology module over the "+
			"real field. Unfold BettiDef to identify the resulting dimension."),
})}

var BettiIsomorphic = bettiIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "BettiIsomorphic",
	Key:  "prop_acc1a51cfc1f77e1",
	Reading: "The point types and manifold dimensions may differ. Finiteness on " +
		"one side is what the first conclusion carries to the other. The equation of " +
		"Betti numbers would hold without it, module_dim taking one value on every " +
		"module with no finite basis, and would then say nothing about dimension.",
	Deps: []registry.EntryLike{BettiDef, de_rham.CohomologyModule, module_dimension.IsomorphicDim},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k))",
			"module_isomorphic(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_cohomology_module⟨m⟩(S, ℬ, k))",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨m⟩(S, ℬ, k)) ∧ " +
			"de_rham_betti⟨m⟩(S, ℬ, k) = de_rham_betti⟨n⟩(T, 𝒜, k)",
	},
		"Use IsomorphicDim on the two cohomology modules over the real "+
			"field. It transfers both finite dimensionality and the dimension."),
})}

var BettiHomogeneousBasis = bettiHomogeneousBasisThm{family.Add(registry.ProofEntry{
	Name: "BettiHomogeneousBasis",
	Key:  "prop_3a1bb88240adc2a9",
	Reading: "Degree tags distinguish classes of different degrees even if their " +
		"representations happen to agree. Empty fibres are bases exactly of the zero modules.",
	Deps: []registry.EntryLike{de_rham_kunneth.HomogeneousBasisDef, BettiBasis},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀k:num.",
		Hypotheses: []string{
			"de_rham_homogeneous_basis⟨n⟩(T, 𝒜, E)",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ∧ " +
			"de_rham_betti⟨n⟩(T, 𝒜, k) = " +
			"card({s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) | " +
			"        (k, s) ∈ E})",
	},
		"Each degree fibre of E is a basis by definition and finite because it "+
			"injects into E by tagging its degree. Apply BettiBasis to that fibre."),
})}

var CompactZeroDimensionBetti = compactZeroDimensionBettiThm{family.Add(registry.ProofEntry{
	Name: "CompactZeroDimensionBetti",
	Key:  "prop_615559500aed546f",
	Reading: "Compactness is essential for the finite cardinal interpretation. An empty " +
		"carrier has cardinal zero; each point contributes one independently of any orientation " +
		"convention. Points of the host type outside the manifold carrier contribute nothing.",
	Deps: []registry.EntryLike{
		BettiDef,
		BettiAboveDimension,
		de_rham.ClassEqualZero,
		de_rham.ClassRepresentative,
		de_rham.ClassAdd,
		de_rham.ClassScale,
		de_rham.CohomologyModule,
		differential_form.FormZeroDegree,
		differential_form.FunctionForm,
		differential_form.FormAboveDimension,
		module_dimension.FreeModuleFiniteDim,
		module_dimension.IsomorphismDim,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
		Hypotheses: []string{
			"smooth_manifold⟨0⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "finite(⋃T) ∧ " +
			"finite_dimensional(real_ring, de_rham_cohomology_module⟨0⟩(T, 𝒜, k)) ∧ " +
			"de_rham_betti⟨0⟩(T, 𝒜, k) = COND(k = 0, card(⋃T), 0)",
	},
		"Every nonempty zero-dimensional chart is a singleton, so compactness extracts "+
			"a finite singleton cover. Every function on this finite discrete carrier is "+
			"smooth. Evaluation identifies H^0 with its real free module: degree-zero "+
			"coboundaries are zero and degree-one forms vanish. FreeModuleFiniteDim "+
			"computes degree zero, and BettiAboveDimension handles positive degrees."),
})}
