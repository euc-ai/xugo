// Package sets is the aggregator for set theory's chapters.
//
// A set here is its own membership predicate: `A → bool`, written
// `set(A)` in a statement whose binder is a set, with `x ∈ s`
// spelled `set_member(x, s)` and every constructor introduced as a
// comprehension over that. A family lands here when its own constants
// are BUILT by that layer — when what they denote is a set the
// comprehension makes — and the boundary section below is where that
// is made precise, because the obvious reading of it is wrong.
//
// The clause about maps is wider than it looks, and `functions` is why:
// most of that chapter's statements name no set constructor at all —
// `identity_map` and `∘` are function combinators, and injectivity and
// surjectivity are conditions on a map that can be written without
// mentioning a set. They belong here because the restricted forms — the
// same conditions relativized to a source and a target set — are where
// the mathematics gets used, and a law and its own corollary at 𝕌
// belong in one chapter.
//
// - set_basic — the language: what membership in each constructed set
// amounts to. The chapter every other set family reads through.
// - set_order — inclusion: ⊆ as a partial order, its strict part ⊊,
// and how both meet the constructors.
// - set_algebra — the equations: what the constructions do to each
// other, from the ∪/∩ lattice to ⋃/⋂ at arbitrary arity.
// - set_image — the image functor: how a map between sets carries the
// constructions across, and how the image characterizes injectivity
// and surjectivity.
// - functions — the maps themselves: composition and the identity,
// and what injectivity, surjectivity and bijectivity amount to in
// terms of inverses.
// - finite_set — finiteness and cardinality: has_size's recursion
// clauses and the finite pigeonhole principle; and listing, the set of
// a list's elements and a list enumerating a finite set.
// - num_segment — the interval `m .. n` of naturals: the canonical
// finite set, and the one chapter here whose element type is pinned.
// - cardinal — comparing sizes without counting: injections,
// bijections, Schröder–Bernstein, Cantor's theorem, and the countable
// sets.
// - indexed_functions — products of indexed carrier sets, with prescribed
// values at inactive coordinates so equality reads on the active indices;
// finite-coordinate dependence of a map on a source carrier.
// - sigma_algebra and measurable_space — sigma algebras on explicit carriers
// and maps characterized by relative inverse images.
// - set_product — the product of two sets: the pairs with a component
// in each. The pair type itself is cartesian/pairs'; the constant
// here is a set the comprehension builds from two sets, which is what
// puts the chapter on this side.
//
// # The boundary
//
// A chapter belongs here or to a number domain by which side of the set
// layer its constants sit on — never by their ELEMENT type, which is a
// fact about the bounds rather than about where the definition lives.
//
// - `..` DENOTES a set the comprehension builds: `m .. n` IS
// `{x | m ≤ x ∧ x ≤ n}`, and unfolding it lands in this layer.
// Its elements happen to be naturals, and that is a fact about the
// bounds, not about where the definition lives. It belongs here,
// and it is the one chapter here whose element type is pinned.
// - `real_sup` CONSUMES a set and returns a real. Its defining condition
// mentions `x ∈ s`, so it reads set-theoretic, but nothing the set
// layer builds is what `real_sup` is; the analysis is in the order on ℝ.
// It belongs to `real/`, and so do the finiteness of a real interval
// and the rest of that strand.
//
// Direction settles the near cases the discriminator leaves close.
// `nat_num/` is the corpus's ℕ basement — `cartesian`, `int_num` and
// `real` all import it and nothing inside it imports upward — so a
// chapter citing `nat_order` cannot live there without
// asserting a dependency the dep edges contradict, which is the
// failure mode plan §"Directory organization" calls a tree that lies.
//
// So most families here hold at every element type at once; num_segment
// is the exception that says what the rule is actually about.
//
// # Where a witness set is built
//
// A proof that has to EXHIBIT a set — a witness for an `∃`, or the
// instance a law is read at — builds a term, and the domain places
// those by how far the reason travels:
//
// - A CONSTRUCTOR's handle comes from `internal/setvocab`, always
// `Term` for a name the chapter applies, `Pinned` for a nullary one
// at the build site, `PinnedAt` where the chapter needs it at a
// chosen element type (a statement about a map `f : A → B` wants
// `∅` and `𝕌` on both sides).
// - `Sing` is there too, and is the one witness the table supplies
// ready-made — `{y}` is notation rather than an application, and it
// was written twice byte for byte before it was written once.
// - Anything ASSEMBLED FROM the proof's own terms — `image(f, k)`,
// the comprehensions `{x | φ}` — belongs to the chapter, in the
// file that needs it, or in its `vocab.go` when two files do. Its
// element types come from the terms it is built from, so it has no
// reason to be shared and nothing to say that the surrounding proof
// does not already say.
package sets

import (
	_ "github.com/euc-ai/xugo/library/proofs/sets/boolean_function/boolean_degree"
	_ "github.com/euc-ai/xugo/library/proofs/sets/boolean_function/boolean_function"
	_ "github.com/euc-ai/xugo/library/proofs/sets/boolean_function/sensitivity"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"
	_ "github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	// cardinality is nested INSIDE finite_set and imports it, so its
	// blank import belongs here rather than in the parent — the
	// reverse would be an import cycle.
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/listing"
	_ "github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_image"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_order"
)
