// Package int_num is the aggregator for ℤ's theory chapters: the
// families curating the integers.
//
// A family lands here when it is CLOSED IN ℤ — its statements quantify
// over int and its definitional layer reaches no further than int's own
// construction. That construction is an embedding: int is carved out
// of ℝ (the type definition binds int to {x : real | integer x}),
// every operation is defined by transport along real_of_int, and the
// homomorphism bridges are proved (int_construction's AddBridge and
// siblings). Two consequences shape the domain:
//
// - The elementary algebra of ℤ is INHERITED, not re-proved: the ring,
// order and absolute-value laws are one-step lifts of their ℝ
// twins (Script.IntOfRealDerive, capability "int_of_real:<source>").
// int_real_lift is that chapter — thin by design, populated only
// with the laws the corpus actually cites.
// - What is NATIVE to ℤ is everything discreteness gives and ℝ cannot
// the ℕ↔ℤ boundary (int_embed), the division algorithm (int_div_rem),
// divisibility (int_divides) and congruence (int_congruence). A
// DERIVED operation gets its own chapter above the construction:
// int_pow is ℤ's power — transfer theorem, recursion equations and
// embedding law — kept out of int_construction so the construction
// itself stays power-free. Below
// all of them, int_construction owns how the type is built out of ℝ:
// the `integer` predicate, the type bijection, and the homomorphism
// bridges every transport is defined through. Its reason is the
// ENGINE rather than a reader — `serve.InstallIntBundle` reads each
// bridge as a typed entry — so each bridge landed there moves a piece
// of ℤ's inherited algebra onto foundations the corpus owns, through a
// route no dep edge shows.
//
// ℤ's ORDER has no chapter, and that is not an omission. Its laws fall
// into three groups. Most are one-step lifts and so int_real_lift's,
// which carries
// the ones the corpus cites and the ones completing a pair it already
// holds; some are division facts wearing an order relation, and so
// int_div_rem's, by subject. The rest is discreteness —
// `x + &1 ≤ y ⇔ x < y` and its mirror — which is the one order fact
// ℝ cannot supply, so it is proved from the ℕ↔ℤ image analysis where
// that boundary already lives (int_embed's `Discrete`, which
// int_div_rem then spends throughout). Each group belongs to a chapter
// that exists; none of the three wants one of its own.
//
// ℕ's number theory is not defined by pushing its arguments through &
// and asking the question in ℤ:
// ℕ's divisibility, gcd, congruence and primality are defined inside ℕ
// (nat_num/nat_divides, nat_gcd, nat_cong, nat_prime). What this domain
// keeps of the crossing is the two
// transport laws, each beside the ℤ relation it lands in: divisibility's
// (int_divides.OfNumDivides) and congruence's (int_congruence.OfNumCongruent).
//
// The domain sits ABOVE real in the dependency tower — its definitional
// layer is closed over ℝ — and above nat_num's number-theory chapters,
// whose definitions the two transport laws unfold.
//
// The blank imports below are the package's whole content: they trigger
// the families' registration into registry and give
// proofs/proofs.go one line per domain rather than one per family.
package int_num

import (
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/quadratic_reciprocity"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
)
