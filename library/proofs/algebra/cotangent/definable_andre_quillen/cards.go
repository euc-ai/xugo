package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// StandardNamesCountable — The initial names are the image of the countable target carrier
var StandardNamesCountable = standardNamesCountableThm{family.Add(registry.ProofEntry{
	Name: "StandardNamesCountable",
	Key:  "prop_62fbc4058587d19a",
	Deps: []registry.EntryLike{
		cardinal.CountableImage,
		cardinal.NumCountable,
		function_module.FiniteSuppCountable,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "countable(standard_names⟨A:A, B:B, U:U⟩(R, S, n))",
	},
		"The initial names are the image of the countable target carrier (CountableImage). "+
			"Each successor is the image of polynomial_algebra(R, names) = finite_supp(R.zero, "+
			"R.carrier, monomials(names)), and monomials(names) is finite_supp(0, 𝕌, names): "+
			"FiniteSuppCountable twice, the numbers being countable, then CountableImage."),
})}

// AndreQuillenPolishModel — The standard cotangent dual reuses the common countable-based-dual construction.
var AndreQuillenPolishModel = andreQuillenPolishModelThm{family.Add(registry.ProofEntry{
	Name: "AndreQuillenPolishModel",
	Key:  "prop_435f280517fff658",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, C).",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N.carrier)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "polish_cochain_complex(S, " +
			"    cotangent_cochain⟨A:A, B:B, C:B, D:C, U:U⟩(R, S, f, S, λx:B. x, N), " +
			"    aq_topologies⟨A:A, B:B, C:C, U:U⟩(R, S, N))",
	},
		"First derive the target-ring host capacity from countable(S.carrier) and the given "+
			"R-universe by finite-polynomial cardinal bounds. CotangentScalarBased supplies the "+
			"standard based cotangent complex; StandardNamesCountable and CountableBasedDualPolish "+
			"make its dual Polish. CotangentDualAgreement identifies degree carriers and "+
			"differentials on those carriers, while unfolding the two complexes identifies their "+
			"operations, so the structure transfers to cotangent_cochain."),
	Deps: []registry.EntryLike{
		StandardNamesCountable,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		polish_cohomology.CountableBasedDualPolish,
	},
	Reading: "Both cotangent comparison cards also require cotangent_universe(S,U): establish it " +
		"from countable coefficients, finite polynomial support and the infinity/cardinal absorption " +
		"of U supplied by cotangent_universe(R,U). CotangentDualAgreement is carrier-level " +
		"agreement, not equality of total complex records; continuity transfers along that agreement.",
})}

// AndreQuillenHasPolishCover — Apply CohomologyHasPolishCover to AndreQuillenPolishModel
var AndreQuillenHasPolishCover = andreQuillenHasPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "AndreQuillenHasPolishCover",
	Key:  "prop_1f8b34a0e736f40f",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, C). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N.carrier)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "cohomology_cover( " +
			"    cotangent_cochain⟨A:A, B:B, C:B, D:C, U:U⟩(R, S, f, S, λx:B. x, N), " +
			"    aq_topologies⟨A:A, B:B, C:C, U:U⟩(R, S, N), " +
			"    n)",
	},
		"Apply CohomologyHasPolishCover to AndreQuillenPolishModel. Its underlying quotient "+
			"module is the existing cotangent_cohomology at the identity coefficient-ring map."),
	Deps: []registry.EntryLike{AndreQuillenPolishModel, polish_cohomology.CohomologyHasPolishCover},
})}

// AndreQuillenCoefficientMapContinuous — Coefficient postcomposition is continuous by singleton-coordinate dependence.
var AndreQuillenCoefficientMapContinuous = andreQuillenCoefficientMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "AndreQuillenCoefficientMapContinuous",
	Key:  "prop_631eeed3d87997d6",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, C). " +
			"∀P:module_ops(B, D). " +
			"∀v:(C → D).",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"ring_homomorphism(R, S, f)",
			"module_homomorphism(S, N, P, v)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N.carrier)",
			"countable(P.carrier)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "polish_cochain_map(S, " +
			"    cotangent_cochain⟨A:A, B:B, C:B, D:C, U:U⟩(R, S, f, S, λx:B. x, N), " +
			"    aq_topologies⟨A:A, B:B, C:C, U:U⟩(R, S, N), " +
			"    cotangent_cochain⟨A:A, B:B, C:B, D:D, U:U⟩(R, S, f, S, λx:B. x, P), " +
			"    aq_topologies⟨A:A, B:B, C:D, U:U⟩(R, S, P), " +
			"    λn:num. λw:(U → C). λu:U. v(w(u)))",
	},
		"Postcomposition by the coefficient homomorphism preserves the normalized cochain "+
			"carriers. Each output reads one input coordinate, so FiniteCoordinateContinuous supplies "+
			"continuity; finite-sum linearity gives commutation with the cotangent differential."),
	Deps: []registry.EntryLike{AndreQuillenPolishModel, polish_space.FiniteCoordinateContinuous},
	Reading: "Coefficient maps may shrink a finite summation support. Finite-sum linearity and " +
		"preservation of zero give commutation with the differential and preserve inactive coordinates.",
})}

// AndreQuillenCountableOrContinuum — André–Quillen cohomology of countable rings with countable coefficients is countable or has at least continuum many classes.
var AndreQuillenCountableOrContinuum = andreQuillenCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "AndreQuillenCountableOrContinuum",
	Key:  "prop_ffd35343625707c",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, C). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N.carrier)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "countable( " +
			"    cohomology(cotangent_cochain⟨A:A, B:B, C:B, D:C, U:U⟩(R, S, f, S, λx:B. x, N), n)) ∨ " +
			"card_le(𝕌⟨A:set(num)⟩, " +
			"    cohomology(cotangent_cochain⟨A:A, B:B, C:B, D:C, U:U⟩(R, S, f, S, λx:B. x, N), n))",
	}, "CohomologyCountableOrContinuum at the Polish model of AndreQuillenPolishModel."),
	Deps: []registry.EntryLike{
		AndreQuillenPolishModel,
		polish_cohomology.CohomologyCountableOrContinuum,
	},
	Reading: "The set is the carrier of cotangent_cohomology at the " +
		"identity coefficient-ring map, D^n(S/R, N) as a set of classes.",
})}
