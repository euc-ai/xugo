// Homogeneous bases have finite degree range, and their coefficient records are modules.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/registry"
)

var HomogeneousBasisExists = homogeneousBasisExistsThm{family.Add(registry.ProofEntry{
	Name: "HomogeneousBasisExists",
	Key:  "prop_4f4231ccef4f95b5",
	Reading: "Finite dimensionality is required in each degree. The finite manifold dimension " +
		"makes the union of the degreewise bases finite; no compactness or orientability is assumed.",
	Deps: []registry.EntryLike{
		HomogeneousBasisDef,
		de_rham.CohomologyAboveDimension,
		module_dimension.FiniteDimensionalBasis,
		linear_independence.IndependentEmpty,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))",
		},
		Conclusion: "∃E:set(prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))). " +
			"    de_rham_homogeneous_basis⟨n⟩(T, 𝒜, E)",
	},
		"Choose finite bases in the finitely many degrees from zero through "+
			"n and take their degree-tagged union. CohomologyAboveDimension "+
			"gives zero modules in all higher degrees, whose basis is empty."),
})}

var HomogeneousBasisDegreeBound = homogeneousBasisDegreeBoundThm{family.Add(registry.ProofEntry{
	Name: "HomogeneousBasisDegreeBound",
	Key:  "prop_c63cb45a5947fc24",
	Deps: []registry.EntryLike{
		HomogeneousBasisDef,
		de_rham.CohomologyAboveDimension,
		linear_independence.IndependentZeroNotIn,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀e:prod(num, set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)).",
		Hypotheses: []string{
			"de_rham_homogeneous_basis⟨n⟩(T, 𝒜, E)",
			"e ∈ E",
		},
		Conclusion: "fst(e) ≤ n",
	},
		"If the degree exceeds n, its entire cohomology carrier is the singleton "+
			"zero class. The basis fibre is independent and therefore cannot contain "+
			"this class, contradicting membership of the tagged element."),
})}

var KunnethCoefficientModule = kunnethCoefficientModuleThm{family.Add(registry.ProofEntry{
	Name: "KunnethCoefficientModule",
	Key:  "prop_f268a464e7756cd4",
	Reading: "No basis or finiteness hypothesis on E is needed for this " +
		"module construction. Labels above k carry forced zero coordinates.",
	Deps: []registry.EntryLike{
		KunnethCoefficientModuleDef,
		de_rham.CohomologyModule,
		function_module.IndexedProductModule,
		submodule.ZeroSubmodule,
		submodule.SubmoduleModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
		},
		Conclusion: "module_on(real_ring, de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E))",
	},
		"For a label at most k use CohomologyModule in the difference degree. "+
			"For a higher label use the zero submodule of H^0. IndexedProductModule "+
			"assembles these into a module, also when E is infinite or empty."),
})}
