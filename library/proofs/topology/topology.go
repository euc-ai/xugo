// Package topology is the aggregator for the chapters of point-set
// topology: a topology as a family of sets closed under the
// intersection of two members and the union of any subfamily, and
// what is said about the subsets of a space and the maps between
// spaces through that family alone.
//
// # The boundary
//
// The objects of the chapters below ℝ are FAMILIES of sets,
// `set(set(A))`. Their definitional layer closes in sets/ — every
// constant is a predicate on such a family or a set the comprehension
// builds from one — so by the letter of the placement rule those
// chapters would sit there. They
// sit here for the reason relations/ is a domain of its own: the tree's
// levels are reading levels, not levels of the mathematics, and a
// reader looking for "open" or "closed" looks under topology, not under
// sets. There the space is never a type and never a carrier argument: a
// topology IS its family of open sets, its points are the union of that
// family, and "open" is membership in it. metric_space is the one
// chapter with a carrier argument, since a distance does not determine
// its points, and its layer closes in ℝ: it sits above ℝ for the same
// reading-level reason, and its topology is a family of that same kind.
// The topology on ℝ is an instance theorem of real/real_topology citing
// these laws, as ℝ's ring is an instance of comm_ring; a chapter here
// states something about the line only where its notion is built on the
// line — a path is a map from an interval of ℝ, Urysohn's function takes
// real values — and then it sits above real_topology.
//
// # The chapters
//
// One space, read through its open sets alone:
//
// - topological_space — the structure `is_topology(T)` and its two
// axioms; open and closed sets, interior and closure and their algebra,
// the limit points and the frontier of a set; bases and the topology a
// family generates; the subspace topology; the discrete topology; and
// the Hausdorff property's definition. A law here carries
// `is_topology(T)` and leaves T implicit.
// - compact — compact sets: what compactness survives, the finite
// intersection property, the compact sets of a Hausdorff space, and
// locally compact spaces.
// - function_support — closure of a function's nonzero locus on the
// space carrier, with restriction, zero extension and composition laws.
// - connected — connected sets, the components of a space, and locally
// connected spaces.
// - separation — the separation axioms, T0, T1, regular and normal, and
// how they stand to each other and to Hausdorff.
// - countability — a countable base, a countable base at each point, a
// countable dense set, a countable subcover of every open cover.
//
// Two spaces and a map, or two spaces and their product:
//
// - continuous — continuity by the preimage of open sets, read on a
// base, at a point, on a cover; the images of compact and connected
// sets; open, closed and quotient maps; homeomorphisms, embeddings and
// retracts; the fixed point property. Continuity and the other properties of a map are structures
// over the two spaces and the map, their theorems laws that bind the
// three once; one that needs an axiom of a space carries that space's
// `is_topology` in its body.
// - compactification — the one-point compactification of a space, on the
// optional values of its type: a topology, compact, the space an open
// subspace of it, and Hausdorff exactly when the space is Hausdorff and
// locally compact.
// - topology_category — topologies in one host type, with normalized
// continuous maps as morphisms and their underlying sets.
// - product_topology — the topology on the product of two spaces, its
// projections, the tube lemma, and what the product inherits from its
// factors; the product of an indexed family and Tychonoff's theorem. The product of two sets is sets/set_product's.
//
// Sections over the open sets of one space:
//
// - cech_cohomology — module-valued presheaves, their countable-cover Čech
// complexes and regular refinement maps; this chapter reads algebra.
// - presheaf — presheaves and sheaves, the sections of every open set in
// one type; germs and stalks. A sheaf of rings, which reads the ring
// chapters, is scheme/locally_ringed_space's.
//
// Regularity on representative spaces:
//
// - borel_space — sigma algebras and Borel maps relative to space carriers.
//
// Above ℝ:
//
// - metric_space — a set with a distance, `metric_space(M, d)`, and the
// topology the distance determines: the balls, the open sets, the
// subspace of a subset, continuity as the ε-δ condition; bounded sets;
// the countability properties, which coincide here; the product
// distance; metrizable spaces. The line and ℝⁿ are its instances in
// their own chapters.
// - polish_space — compatible complete separable topologies and indexed
// products, with the Polish theorem for countably many factors, and
// continuity by finite-coordinate dependence in discrete products, which
// needs no countability; and the Lusin–Souslin theorem on the injective
// continuous images of Borel sets.
// - baire_category — nowhere dense and meager sets, the Baire property and
// Baire spaces: a Polish space is a Baire space, Borel sets have the Baire
// property, a continuous open map pulls meager sets back, and Mycielski's
// independent Cantor set for a meager relation.
// - complete_metric — sequences in a metric space: convergence, Cauchy
// sequences, completeness and total boundedness; Cantor's nested sets,
// Baire's theorem and Banach's fixed point theorem; compactness as
// sequential compactness and as completeness with total boundedness,
// the Lebesgue number; uniformly continuous and Lipschitz maps.
// - path_connected — paths, maps from the unit interval of the line,
// the sets any two points of which a path joins, path components, and
// locally path-connected spaces.
// - homotopy — homotopy of maps relative to a set, the homotopy of
// paths with their ends held and the groupoid laws of joining paths up
// to it, homotopy equivalences and contractible spaces.
// - fundamental_group — the classes of paths, the fundamental group of
// a space at a point as a group record, the homomorphisms continuous
// maps induce, simply connected spaces and the Seifert–van Kampen
// theorem as a universal property.
// - covering_space — covering maps, and the lifting of paths and of
// homotopies of paths through them.
// - real_valued — continuous real-valued functions on a space: Urysohn's
// lemma, Tietze's extension, and completely regular spaces.
package topology

import (
	_ "github.com/euc-ai/xugo/library/proofs/topology/baire_category"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/bott_periodicity"
	_ "github.com/euc-ai/xugo/library/proofs/topology/cech_cohomology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compactification"
	_ "github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	_ "github.com/euc-ai/xugo/library/proofs/topology/connected"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/countability"
	_ "github.com/euc-ai/xugo/library/proofs/topology/covering_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/function_support"
	_ "github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	_ "github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_pushforward"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_theory"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	_ "github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	_ "github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	_ "github.com/euc-ai/xugo/library/proofs/topology/separation"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topology_category"
)
