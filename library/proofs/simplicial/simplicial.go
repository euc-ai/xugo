// Package simplicial is the aggregator for combinatorial homotopy
// theory: simplicial sets and the Kan complexes among them, their
// homotopy groups, Kan fibrations with the long exact sequence, and
// the nerve of a category with the quasi-categories it is the model
// of.
//
// # The encoding
//
// A simplicial set on a carrier type A is one value of the record
// `simplicial_ops(A)`, `mk_simplicial(simplices, d, s)`: under a binder
// X of the type, `X.simplices(n)` is the set of n-simplices, and the two
// total maps `X.d`, `X.s : num → num → A → A` read the dimension of
// their argument as a term, `X.d(n, i, x)` the i-th face of the
// n-simplex x and `X.s(n, i, x)` its i-th degeneracy;
// `simplicial_set(X)` says the record is a simplicial set. Every simplex
// of every dimension lives in the one type, so a horn, a filler, a
// homotopy and a class of spheres are all sets of one type and no
// equality between types is ever asked; the index conditions a face or
// a degeneracy is defined under are arithmetic in the statement, closed
// by the arithmetic closer, and nothing is cast. An operation that reads
// only the faces or only the degeneracies, as an iterated face or the
// base simplex at a vertex does, takes that component,
// `face_iterate_top(X.d, n, k, x)`, `base_simplex(X.s, x₀, n)`. A
// simplicial set the corpus builds — the nerve of a category, a standard
// simplex, the fibre of a map, the mapping complex, the singular
// simplices of a space — is one value of
// the record, its simplices a family defined beside it
// (`nerve_simplices`, `standard_simplex_simplices`, …). A bisimplicial
// set is likewise one value of `bisimplicial_ops(A)`, with horizontal
// and vertical faces and degeneracies. The standard simplices are
// monotone sequences `num → num` padded with zero past their length,
// the nerve's simplices composable chains padded with an identity,
// both the one idiom of the vector chapters.
//
// # The chapters
//
// - simplicial_set — the structure and its identities, sub-simplicial
// sets and simplicial maps, the base simplex at a vertex, iterated
// faces, the standard simplices with their boundaries and horns, and
// fixed-prefix cones with their boundary restriction and tail projection.
// - simplicial_chain — the alternating face map complex over a ring
// on a set, ∂∂ = 0, the integral chains, and the chain map a
// simplicial map induces.
// - kan_complex — the Kan condition in its combinatorial form, the
// point as a Kan complex and the standard simplices as non-examples.
// - homotopy_group — the spheres at a vertex, homotopy between them,
// πₙ as the set of classes, a group for 0 < n and abelian for 2 ≤ n,
// and the map a simplicial map induces.
// - kan_fibration — Kan and left fibrations, the fibre, the connecting map and
// the long exact sequence of homotopy groups.
// - nerve — the nerve of a category and unique inner fillers.
// - quasi_category — quasi-categories, homotopy of edges, the
// homotopy category, fixed-prefix cone lifting, Joyal's theorem and the homotopy category as left
// adjoint to the nerve.
// - segal — spines, the category of a simplicial set with unique inner
// fillers, and Segal's characterization of the nerves.
// - simplex_category — the simplex category Δ, its morphisms the
// monotone maps the standard simplices already hold, its generators,
// and the canonical factorization of a monotone map.
// - simplicial_operator — the action of a monotone map on the
// simplices, the Yoneda reading of a simplex and horns as maps out of
// the standard horns.
// - mapping_complex — the mapping complex between two vertices, a Kan
// complex in a quasi-category.
// - simplicial_homotopy — homotopies of simplicial maps and the
// relation they generate, extra degeneracies of an augmented
// simplicial set, and the diagonal of a bisimplicial set.
// - simplicial_module — simplicial modules over a ring on a set, their
// alternating face complex and Moore complex, acyclic augmentations,
// and the free chains on a simplicial set.
// - simplicial_group — the homotopy groups of a simplicial module, read
// off its Moore complex.
// - singular_set — the singular simplicial set of a topological space,
// its simplices the normalized continuous maps of the standard
// simplices: a Kan complex, whose first homotopy group is the
// fundamental group.
// - singular_homology — singular chains and homology with coefficients
// in a ring: homotopy invariance, the homology of contractible and of
// path-connected spaces, small simplices and the Mayer–Vietoris step.
// Real singular cochains carry natural two-open cover sequences; evaluation
// identifies their cohomology with the full real dual of singular homology.
package simplicial

import (
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/homotopy_group"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/kan_fibration"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/mapping_complex"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/nerve"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/quasi_category"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/segal"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplex_category"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_group"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_operator"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/singular_cohomology"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/singular_homology"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/singular_set"
)
