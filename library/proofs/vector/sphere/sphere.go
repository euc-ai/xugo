// sphere.go — the spheres as spaces: a sphere less a point is
// contractible, by stereographic projection onto a hyperplane; Sⁿ⁺¹ less
// its two poles is homotopy equivalent to its equator Sⁿ, which as a set
// of sequences is Sⁿ itself; so for n ≥ 2 Sⁿ is the union of two simply
// connected open sets with a path-connected intersection, simply
// connected; and the Mayer–Vietoris sequence of the same two open sets
// lowers the top homology one degree at a time to H₁(S¹), so Hₙ(Sⁿ) ≅ R.

package sphere

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_homology"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_set"
	"github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// SpherePuncturedContractible — a sphere less one of its points is
// contractible.
var SpherePuncturedContractible = spherePuncturedContractibleThm{family.Add(registry.ProofEntry{
	Name: "SpherePuncturedContractible",
	Key:  "prop_5c35bf3894d4634e",
	Reading: "x ∈ Sⁿ is load-bearing: for x off the sphere the space is the " +
		"whole sphere, not contractible. At n = 0 the space is the one point −x.",
	Deps: []registry.EntryLike{
		convex_topology.ConvexContractible,
		homotopy.ContractibleSpaceDef,
		euclidean_topology.EuclideanSphereDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀x:(num → real).",
		Hypotheses: []string{
			"x ∈ euclidean_sphere(n)",
		},
		Conclusion: "contractible_space(subtopology(euclidean_topology(n + 1), euclidean_sphere(n) ∖ {x}))",
	},
		"stereographic projection from x is a homeomorphism of the sphere less x onto "+
			"the hyperplane orthogonal to x, a convex set (ConvexContractible); a "+
			"straight-line contraction there, read back through the projection, contracts "+
			"the punctured sphere. For n = 0 the punctured sphere is the one point −x"),
})}

// SphereEquatorHomotopyEquivalence — Sⁿ⁺¹ less its north and south poles
// is homotopy equivalent to the equator Sⁿ, included as itself.
var SphereEquatorHomotopyEquivalence = sphereEquatorHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "SphereEquatorHomotopyEquivalence",
	Key:  "prop_a9c1b787fd02514c",
	Reading: "The inclusion is λx. x because Sⁿ ⊆ Sⁿ⁺¹ as sets and the two distances " +
		"agree on (n + 1)-vectors. Both poles are removed so that the first n + 1 " +
		"coordinates do not all vanish and g is defined. At n = 0, S⁰ against two open arcs.",
	Deps: []registry.EntryLike{
		homotopy.HomotopyEquivalenceDef,
		homotopy.HomotopicRelDef,
		euclidean_topology.EuclideanSphereDef,
		euclidean_topology.NormContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num.",
		Conclusion: "∃g:((num → real) → num → real). " +
			"    homotopy_equivalence(euclidean_sphere_topology(n), " +
			"        subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1) ∖ {«north», «south»}), " +
			"        λx:(num → real). x, " +
			"        g)",
		Abbrev: Abbrev{
			{Name: "north", Text: "λi:num. COND(i = n + 1, &1, &0)"},
			{Name: "south", Text: "λi:num. COND(i = n + 1, -&1, &0)"},
		},
	},
		"a point of Sⁿ is an (n + 2)-vector with last coordinate 0 and norm 1, a point of Sⁿ⁺¹ off "+
			"both poles. g sets the last coordinate to 0 and rescales to norm 1, defined off the poles; "+
			"g after the inclusion is the identity, and the straight line from y to g(y), rescaled to "+
			"norm 1, homotopes the inclusion after g to the identity (NormContinuous for the rescaling)"),
})}

// SphereSimplyConnected — the spheres of dimension at least 2 are simply
// connected.
var SphereSimplyConnected = sphereSimplyConnectedThm{family.Add(registry.ProofEntry{
	Name: "SphereSimplyConnected",
	Key:  "prop_aaf6920cc4d40f07",
	Reading: "The dimension n + 2 ≥ 2 is load-bearing — S¹ is not simply connected: " +
		"the sphere less both poles is path-connected only from dimension 2 on.",
	Deps: []registry.EntryLike{
		SpherePuncturedContractible,
		fundamental_group.ContractibleSimplyConnected,
		fundamental_group.SimplyConnectedUnion,
		euclidean_topology.EuclideanSphereDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num.",
		Conclusion: "simply_connected_space(euclidean_sphere_topology(n + 2))",
	},
		"the sphere less the north pole and the sphere less the south pole are open, "+
			"contractible (SpherePuncturedContractible) and so simply connected "+
			"(ContractibleSimplyConnected); their intersection, the sphere less both poles, is "+
			"path-connected for a sphere of dimension at least 2, and SimplyConnectedUnion applies"),
})}

// CircleFirstHomology — the circle has the ring for its homology in degree
// 1.
var CircleFirstHomology = circleFirstHomologyThm{family.Add(registry.ProofEntry{
	Name:    "CircleFirstHomology",
	Key:     "prop_d23c970637691a08",
	Reading: "Needs only comm_ring_on(R); for the zero ring both sides are 0.",
	Deps: []registry.EntryLike{
		SpherePuncturedContractible,
		singular_homology.ContractibleAcyclic,
		singular_homology.PathConnectedZerothHomology,
		singular_homology.SmallChainsQuasiIsomorphism,
		singular_homology.HomotopyEquivalenceHomology,
		singular_set.SubspaceSingularSimplices,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    homology_module(singular_complex(R, euclidean_sphere_topology(1)), 1), " +
			"    regular_module(R))",
	},
		"cover the circle by the two punctured circles U and V, contractible arcs "+
			"(SpherePuncturedContractible) with no homology in degree 1 (ContractibleAcyclic) and R in "+
			"degree 0 (PathConnectedZerothHomology); their intersection is two disjoint open contractible "+
			"arcs, whose degree-0 homology is R ⊕ R, the singular chains of a disjoint union of two open "+
			"sets being the sum of theirs (SubspaceSingularSimplices; a simplex has a connected image). "+
			"The Mayer–Vietoris sequence, built as in MayerVietorisDiagonal, gives 0 → H₁(S¹) → R ⊕ R → R "+
			"⊕ R, the last map (a, b) ↦ (a + b, a + b), whose kernel {(a, −a)} is a copy of R"),
})}

// SphereHomologyStep — the top homology of Sⁿ⁺² is that of Sⁿ⁺¹, one degree
// lower.
var SphereHomologyStep = sphereHomologyStepThm{family.Add(registry.ProofEntry{
	Name: "SphereHomologyStep",
	Key:  "prop_2d2c368486db44a5",
	Reading: "The step starts at Sⁿ⁺¹ with n + 1 ≥ 1; one " +
		"lower it would be false, H₁(S¹) ≅ R while H₀(S⁰) ≅ R ⊕ R.",
	Deps: []registry.EntryLike{
		SpherePuncturedContractible,
		SphereEquatorHomotopyEquivalence,
		singular_homology.ContractibleAcyclic,
		singular_homology.MayerVietorisDiagonal,
		singular_homology.HomotopyEquivalenceHomology,
		module_homomorphism.ModuleIsomorphicDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    homology_module(singular_complex(R, euclidean_sphere_topology(n + 2)), n + 2), " +
			"    homology_module(singular_complex(R, euclidean_sphere_topology(n + 1)), n + 1))",
	},
		"the sphere less the north pole and the sphere less the south pole are open and "+
			"contractible (SpherePuncturedContractible), so have no homology in degrees n + 1 and n "+
			"+ 2 (ContractibleAcyclic); MayerVietorisDiagonal identifies H_(n+2)(Sⁿ⁺²) with H_(n+1) "+
			"of the sphere less both poles, which is H_(n+1)(Sⁿ⁺¹) through the homotopy equivalence "+
			"with the equator (SphereEquatorHomotopyEquivalence, HomotopyEquivalenceHomology)"),
})}

// SphereTopHomology — Hₙ(Sⁿ) ≅ R for n ≥ 1.
var SphereTopHomology = sphereTopHomologyThm{family.Add(registry.ProofEntry{
	Name:    "SphereTopHomology",
	Key:     "prop_bb42bb849d6aa193",
	Reading: "n + 1 ≥ 1 is load-bearing: H₀(S⁰) ≅ R ⊕ R, not R for a nonzero ring.",
	Deps: []registry.EntryLike{
		CircleFirstHomology,
		SphereHomologyStep,
		module_homomorphism.ModuleIsomorphicDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    homology_module(singular_complex(R, euclidean_sphere_topology(n + 1)), n + 1), " +
			"    regular_module(R))",
	},
		"induction on n: CircleFirstHomology at n = 0, "+
			"SphereHomologyStep and the transitivity of isomorphism above it"),
})}
