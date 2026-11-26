package polish_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousSurjectionBorelSection — A continuous homomorphism onto a Polish group has a Borel section.
var ContinuousSurjectionBorelSection = continuousSurjectionBorelSectionThm{family.Add(registry.ProofEntry{
	Name: "ContinuousSurjectionBorelSection",
	Key:  "prop_2f63778ae65183b6",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀H:group_ops(B). ∀U:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"polish_abelian_group(H, U)",
			"group_homomorphism(G, H, f)",
			"continuous_map(T, U, f)",
			"image(f, G.carrier) = H.carrier",
		},
		Conclusion: "∃s:(B → A). borel_map(U, T, s) ∧ (∀y:B. y ∈ H.carrier ⇒ f(s(y)) = y)",
	},
		"By the open mapping theorem for Polish groups a continuous surjective "+
			"homomorphism is open, so the bijection it induces from the quotient by its "+
			"closed kernel is a homeomorphism onto H. A Borel transversal of the closed "+
			"cosets of the kernel, read through that homeomorphism, is the section."),
	Deps: []registry.EntryLike{polish_space.ClosedSubspacePolish},
	Reading: "Surjectivity onto a Polish group keeps the image closed, so no Borel-image " +
		"theorem enters. The section is Borel, not continuous and not a homomorphism.",
})}

// ContinuousHomImagePolishable — The image need not be closed or Polish in its subspace topology; its Polish topology is transported from the quotient by the kernel.
var ContinuousHomImagePolishable = continuousHomImagePolishableThm{family.Add(registry.ProofEntry{
	Name: "ContinuousHomImagePolishable",
	Key:  "prop_60214f78bbc52811",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀H:group_ops(B). ∀U:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"polish_abelian_group(H, U)",
			"group_homomorphism(G, H, f)",
			"continuous_map(T, U, f)",
		},
		Conclusion: "polishable_subgroup(H, U, image(f, G.carrier)) ∧ image(f, G.carrier) ∈ borel_sets(U)",
	},
		"Bergfalk, Lupini and Panagiotopoulos, The definable content of homological invariants I, "+
			"Lemma 2.3: quotient the source by its closed kernel and transport the Polish topology to "+
			"the image along the induced continuous injection. The image is Borel, and its trace Borel "+
			"sets are those of the transported topology, by the Lusin–Souslin theorem. The kernel is a "+
			"subgroup (KernelSubgroup), closed as the inverse image of a point (ClosedPreimage), a point "+
			"of a metric topology being closed (MetricHausdorff, HausdorffImpT1, T1IffSingletonsClosed), "+
			"so the quotient by it is a Polish group (ClosedSubgroupQuotientPolish). The induced map of "+
			"the quotient group is an isomorphism onto the image (FirstIsomorphism) taking a coset to "+
			"the value at its points (InducedMapCoset), so it is continuous for the quotient topology "+
			"(QuotientTopologyQuotientMap, QuotientUniversal); being injective, it carries the Borel "+
			"sets of the quotient, the whole quotient among them, to Borel sets of the target "+
			"(LusinSouslin). The inclusion of the image under the transported topology is continuous, so "+
			"the trace of an ambient Borel set is Borel for it (ContinuousMapBorel)."),
	Deps: []registry.EntryLike{
		group_homomorphism.KernelSubgroup,
		continuous.ClosedPreimage,
		metric_space.MetricHausdorff,
		separation.HausdorffImpT1,
		separation.T1IffSingletonsClosed,
		ClosedSubgroupQuotientPolish,
		quotient_group.FirstIsomorphism,
		quotient_group.InducedMapCoset,
		continuous.QuotientTopologyQuotientMap,
		continuous.QuotientUniversal,
		polish_space.LusinSouslin,
		borel_space.ContinuousMapBorel,
	},
	Reading: "The image need not be closed or Polish in its subspace topology; only " +
		"the Borel sets of the transported topology are asserted to agree with the trace.",
})}

// ClosedSubgroupPolish — Restrict the continuous operations to the closed subgroup and apply ClosedSubspacePolish.
var ClosedSubgroupPolish = closedSubgroupPolishThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubgroupPolish",
	Key:  "prop_8a6a566b160a1e6",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"closed_in(T, N)",
		},
		Conclusion: "polish_abelian_group(restrict_group(G, N), subtopology(T, N))",
	}, "Restrict the continuous operations to the closed subgroup and apply ClosedSubspacePolish."),
	Deps: []registry.EntryLike{polish_space.ClosedSubspacePolish},
})}

// ClosedSubgroupQuotientPolish — The quotient of a Polish abelian group by a closed subgroup is a Polish abelian group in the quotient topology.
var ClosedSubgroupQuotientPolish = closedSubgroupQuotientPolishThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubgroupQuotientPolish",
	Key:  "prop_5fe86105e094c111",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"closed_in(T, N)",
		},
		Conclusion: "polish_abelian_group(quotient_group(G, N), " +
			"    quotient_topology(T, λx:A. left_coset(G.mul, x, N)))",
	},
		"The coset map is open, the cosets through an open set filling a union of its translates, "+
			"so it is a quotient map onto the cosets (LeftCosetsImage, QuotientTopologyQuotientMap), "+
			"and so is its square (ProductMapContinuous, OpenSurjectionQuotient). The quotient is a "+
			"group (QuotientGroupOn) whose operations (LeftCosetMulOn, LeftCosetInvOn) are continuous "+
			"because they lift to the group's (QuotientUniversal). By the Birkhoff–Kakutani theorem "+
			"the group has a compatible invariant metric; the distance between the nearest points of "+
			"two cosets is then a metric for the quotient topology, the subgroup being closed, and by "+
			"Sierpiński's theorem a metrizable open continuous image of a Polish space is Polish."),
	Deps: []registry.EntryLike{
		quotient_group.LeftCosetsImage,
		continuous.QuotientTopologyQuotientMap,
		product_topology.ProductMapContinuous,
		continuous.OpenSurjectionQuotient,
		quotient_group.QuotientGroupOn,
		quotient_group.LeftCosetMulOn,
		quotient_group.LeftCosetInvOn,
		continuous.QuotientUniversal,
	},
	Reading: "The subgroup is normal because the group is abelian. Closedness is load-bearing: " +
		"a point of the quotient is closed exactly when its coset is, and the line modulo the " +
		"rationals has the indiscrete quotient topology. No Polish topology on the subgroup is asked.",
})}

// BorelLiftModuloSubgroup — The lift need only be additive modulo M and send N into M; no homomorphism lift or quotient selector is required.
var BorelLiftModuloSubgroup = borelLiftModuloSubgroupThm{family.Add(registry.ProofEntry{
	Name: "BorelLiftModuloSubgroup",
	Key:  "prop_53f9843c8a7c2d47",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). " +
			"∀T:set(set(A)). " +
			"∀N:set(A). " +
			"∀H:group_ops(B). " +
			"∀U:set(set(B)). " +
			"∀M:set(B). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"polish_cover_on(G, T, N)",
			"polish_cover_on(H, U, M)",
			"borel_map(T, U, f)",
			"image(f, N) ⊆ M",
			"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ H.mul(f(G.mul(x, y)), H.inv(H.mul(f(x), f(y)))) ∈ M",
		},
		Conclusion: "borel_cover_map(G, T, N, H, U, M, induced_map(λx:A. left_coset(H.mul, f(x), M)))",
	},
		"The additive defect lies in M, so the target coset of f(x) depends "+
			"only on the source coset and multiplication descends. The original "+
			"f witnesses Borel regularity of the induced quotient homomorphism."),
	Deps: []registry.EntryLike{equivalence.InducedMapClass},
	Reading: "The lift need only be additive modulo M and send N " +
		"into M; no homomorphism lift or quotient selector is required.",
})}

// ContinuousLiftBijectiveIso — A continuous homomorphic lift bijective on quotient carriers, with the target denominator a continuous image, has a Borel-liftable inverse.
var ContinuousLiftBijectiveIso = continuousLiftBijectiveIsoThm{family.Add(registry.ProofEntry{
	Name: "ContinuousLiftBijectiveIso",
	Key:  "prop_4b90abad52c5a695",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). " +
			"∀T:set(set(A)). " +
			"∀N:set(A). " +
			"∀H:group_ops(B). " +
			"∀U:set(set(B)). " +
			"∀M:set(B). " +
			"∀P:group_ops(C). " +
			"∀V:set(set(C)). " +
			"∀q:(C → B). " +
			"∀f:(A → B). " +
			"∀h:(set(A) → set(B)).",
		Hypotheses: []string{
			"polish_cover_on(G, T, N)",
			"polish_cover_on(H, U, M)",
			"group_homomorphism(G, H, f)",
			"continuous_map(T, U, f)",
			"polish_abelian_group(P, V)",
			"group_homomorphism(P, H, q)",
			"continuous_map(V, U, q)",
			"image(q, P.carrier) = M",
			"∀x:A. x ∈ G.carrier ⇒ h(left_coset(G.mul, x, N)) = left_coset(H.mul, f(x), M)",
			"injective_on(left_cosets(G.mul, G.carrier, N), h)",
			"image(h, left_cosets(G.mul, G.carrier, N)) = left_cosets(H.mul, H.carrier, M)",
		},
		Conclusion: "borel_cover_iso(G, T, N, H, U, M, h)",
	},
		"The map (x, p) ↦ H.mul(f(x), q(p)) on the product group of G and P is a continuous "+
			"homomorphism onto H, since every coset of M is the image of a coset of N. "+
			"ContinuousSurjectionBorelSection gives it a Borel section, whose first coordinate k satisfies "+
			"f(k(y)) ∈ left_coset(H.mul, y, M). Injectivity on the quotients makes k additive modulo N and "+
			"carry M into N, so BorelLiftModuloSubgroup descends it to the inverse; the product is a "+
			"Polish abelian group by ProductMetric, ProductComplete and SecondCountableProduct."),
	Deps: []registry.EntryLike{
		ContinuousSurjectionBorelSection,
		BorelLiftModuloSubgroup,
		borel_space.ContinuousMapBorel,
		complete_metric.ProductComplete,
		metric_space.ProductMetric,
		product_topology.SecondCountableProduct,
	},
	Reading: "Both bijectivity conditions are on the quotient carriers. The lift is a continuous " +
		"homomorphism and the denominator is presented as the continuous image of a Polish group; the " +
		"inverse lift is Borel and inverse only modulo the denominators. A lift that is merely Borel " +
		"and additive modulo the denominator is not covered: inverting it needs a uniformization theorem.",
})}

// DiscreteProductGroupPolish — A countable product of countable discrete abelian groups, with pointwise operations on the normalized carrier, is a Polish abelian group.
var DiscreteProductGroupPolish = discreteProductGroupPolishThm{family.Add(registry.ProofEntry{
	Name: "DiscreteProductGroupPolish",
	Key:  "prop_25c0f86e87353537",
	Build: family.Card(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀G:(I → group_ops(A)). ∀H:group_ops(I → A).",
		Hypotheses: []string{
			"countable(J)",
			"∀i:I. abelian_group_on(G(i)) ∧ z(i) = G(i).one",
			"∀i:I. i ∈ J ⇒ countable(G(i).carrier)",
			"H.carrier = indexed_functions(J, z, λi:I. G(i).carrier)",
			"H.one = z",
			"∀u v:(I → A). ∀i:I. u ∈ H.carrier ∧ v ∈ H.carrier ⇒ H.mul(u, v)(i) = G(i).mul(u(i), v(i))",
			"∀u:(I → A). ∀i:I. u ∈ H.carrier ⇒ H.inv(u)(i) = G(i).inv(u(i))",
		},
		Conclusion: "polish_abelian_group(H, indexed_discrete_topology(J, z, λi:I. G(i).carrier))",
	},
		"CountableDiscretePolish and CountableProductPolish make the product Polish, and "+
			"IndexedProductCarrier identifies its carrier with H.carrier. The group laws hold "+
			"coordinatewise, inactive coordinates staying at their units. The preimage of a coordinate "+
			"cylinder under multiplication is a union of rectangles of cylinders, open by ProductOpenIff, "+
			"and inversion reads one coordinate, so FiniteCoordinateContinuous gives its continuity."),
	Deps: []registry.EntryLike{
		polish_space.CountableDiscretePolish,
		polish_space.CountableProductPolish,
		product_topology.IndexedProductCarrier,
		polish_space.FiniteCoordinateContinuous,
		product_topology.ProductOpenIff,
	},
	Reading: "Factor carriers and inactive values may vary with the coordinate. The " +
		"operations are asked to agree with the factors only pointwise on the carrier, so " +
		"any pointwise constructor of the product qualifies without a record equation. " +
		"Countability is asked of the index set and the active factors, not of the host type.",
})}
