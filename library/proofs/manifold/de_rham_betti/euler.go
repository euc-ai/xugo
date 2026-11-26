// The Euler characteristic is an integer-valued signed dimension sum, also read on a homogeneous basis or by traces.

package de_rham_betti

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/registry"
)

var EulerFiniteRange = eulerFiniteRangeThm{family.Add(registry.ProofEntry{
	Name: "EulerFiniteRange",
	Key:  "prop_141a4b17cf6f7f57",
	Reading: "This only extends the summation bound; it does not change the manifold " +
		"dimension parameter. The identity holds even without finite-dimensional lower cohomology.",
	Deps: []registry.EntryLike{EulerDef, BettiAboveDimension, real_sum.Superset},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀N:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"n ≤ N",
		},
		Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = " +
			"real_sum({q:num | q ≤ N}, λq:num. (-&1) ^ q * &de_rham_betti⟨n⟩(T, 𝒜, q))",
	},
		"The extra degrees are above n and hence have zero Betti number by "+
			"BettiAboveDimension. Extend the finite sum by these zero terms."),
})}

var EulerEmpty = eulerEmptyThm{family.Add(registry.ProofEntry{
	Name: "EulerEmpty",
	Key:  "prop_bb09fcf8b21b8999",
	Reading: "The empty manifold is allowed in every dimension, " +
		"and its Euler characteristic is zero in all of them.",
	Deps: []registry.EntryLike{BettiDef, EulerDef, de_rham.EmptyCohomology, real_sum.EqZero},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"⋃T = ∅",
		},
		Conclusion: "(∀k:num. de_rham_betti⟨n⟩(T, 𝒜, k) = 0) ∧ de_rham_euler⟨n⟩(T, 𝒜) = &0",
	},
		"EmptyCohomology computes every degree dimension as zero. "+
			"Substitute these values in the defining finite sum."),
})}

var EulerConvexOpen = eulerConvexOpenThm{family.Add(registry.ProofEntry{
	Name: "EulerConvexOpen",
	Key:  "prop_ee6f59fc474cb7c1",
	Reading: "This is ordinary de Rham cohomology: a nonempty open Euclidean ball has Euler " +
		"characteristic one in every dimension, not the compact-support sign. Dimension zero is included.",
	Deps: []registry.EntryLike{EulerDef, BettiDef, de_rham.ConvexOpenCohomology, real_sum.Delta},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:set(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"convex(U)",
		},
		Conclusion: "de_rham_euler⟨n⟩(subtopology(euclidean_topology(n), U), euclidean_atlas(U)) = " +
			"COND(U = ∅, &0, &1)",
	},
		"ConvexOpenCohomology gives dimension one only in degree zero when U is nonempty, "+
			"and zero in every degree otherwise. Evaluate the resulting single-term sum."),
})}

var EulerZeroDimension = eulerZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "EulerZeroDimension",
	Key:  "prop_ee7df5778cedae09",
	Reading: "Empty and disconnected zero-manifolds are included. No " +
		"signed-point convention or orientation enters this cohomological count.",
	Deps: []registry.EntryLike{EulerDef, CompactZeroDimensionBetti, real_sum.Clauses},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨0⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "de_rham_euler⟨0⟩(T, 𝒜) = &card(⋃T)",
	},
		"The degree set has only zero. CompactZeroDimensionBetti identifies "+
			"this Betti number with the finite cardinal of the carrier."),
})}

var EulerIdentityTrace = eulerIdentityTraceThm{family.Add(registry.ProofEntry{
	Name: "EulerIdentityTrace",
	Key:  "prop_6e554884187e4b1d",
	Reading: "The trace is real-valued, so the natural dimension is coerced to real. This gives " +
		"the alternating identity-trace formula without a pairing, an orientation or Poincaré duality. " +
		"Finite dimensionality justifies both choice operators; an empty basis gives trace zero.",
	Deps: []registry.EntryLike{
		EulerDef,
		BettiDef,
		de_rham.CohomologyModule,
		module_dimension.FiniteDimensionalDef,
		module_dimension.DimBasis,
		module_dimension.TraceFromBasis,
		module_dimension.BasisCoordinateDelta,
		module_homomorphism.HomIdentity,
		real_sum.RealModuleSum,
		real_sum.CardAsSum,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))",
		},
		Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = " +
			"real_sum({q:num | q ≤ n}, " +
			"    λq:num. " +
			"        (-&1) ^ q * module_trace(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q), identity_map))",
	},
		"Choose a finite basis in each degree. TraceFromBasis and BasisCoordinateDelta make "+
			"the identity trace a sum of ones, equal to the real coercion of its dimension by "+
			"DimBasis and RealModuleSum. Substitute degree by degree into EulerDef."),
})}
