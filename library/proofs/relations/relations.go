// Package relations is the aggregator for the chapters about binary
// relations themselves — the properties a relation can have, the
// closures that give it one, and the recursion a relation licenses
// when it admits no infinite descent.
//
// # The boundary
//
// Placement follows the definitional layer, as everywhere. A family
// belongs here when its objects are RELATIONS and its constants close
// over the relation, the logic, and the sets a relation carves its
// carrier into: `wellfounded` quantifies over predicates on the
// relation's own carrier, a closure operator builds one relation from
// another, and an equivalence's classes and the partition they form
// are sets of that carrier, read from the relation side because the
// relation a partition induces is the other half of one
// correspondence. A theorem ABOUT a particular relation —
// divisibility, congruence, the order on ℕ — belongs to the chapter
// that defines that relation, however relational its subject matter;
// the corpus's own equivalences (`nadd_eq`, `treal_eq`, `int_cong`) are
// instances of `equivalence` proved in the chapters that define them,
// not here. The exception is forced by the tree: a chapter that lies
// below this domain — the set chapters, the order of ℕ — cannot state
// that its relation is an order, and inclusion's instances are kept in
// `order`.
//
// The domain is one level of the tree, not a level of the mathematics:
// `well_founded` sat at the root while it was the only chapter of its
// kind, and moved here when it stopped being.
package relations

import (
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/hypercube"
	// The properties a relation can have — reflexive, symmetric,
	// transitive, and their conjunction — with the classes of an
	// equivalence and the partition theorem in both directions.
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	// The transitive closure: the least transitive relation above a
	// given one, and the laws that make it a closure operator; the
	// reflexive–transitive closure beside it.
	_ "github.com/euc-ai/xugo/library/proofs/relations/closure"
	// Well-founded relations: the minimal-element definition, the
	// induction it licenses, and the recursion theorem the define
	// door's WF shape compiles against.
	_ "github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	// Orders: preorders, partial and total orders, the chains and
	// bounds of a set under one, and Zorn's lemma.
	_ "github.com/euc-ai/xugo/library/proofs/relations/order"
	// Simple undirected graphs: degrees, connected components, and the
	// edge count of a tree.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/simple_graph"
	// Finite directed acyclic graphs: parents, ancestors, deleting the
	// edges into or out of a set, and well-foundedness.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	// Separation in a directed acyclic graph, read on the moral graph of
	// an ancestral set; semigraphoids and the local-to-global theorem.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	// Open paths: Pearl's reading of separation by colliders.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_connection"
	// Acyclic directed mixed graphs: m-separation, districts, C-forests
	// and hedges.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	// The latent projection of a DAG onto its observed vertices.
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/latent_projection"
	// Finite Hall matchings for a family of sets.
	_ "github.com/euc-ai/xugo/library/proofs/relations/matching"
)
