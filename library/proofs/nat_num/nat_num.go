// Package nat_num is the aggregator for ℕ's theory chapters: the families
// curating the natural numbers themselves.
//
// - peano — the construction of num itself: from the axiom of infinity
// through the is_num type definition to the Peano axioms and
// primitive recursion. The domain's basement, and what the other two
// chapters' induction and recursive definitions rest on.
// - nat_arith — the recursive operations and their algebraic laws
// (+ * **). The core below the order: nothing in it states ≤ or <.
// - nat_order — the order predicate (≤ <), a family of its own because
// defining m ≤ n needs +, so it stands ON nat_arith rather than in it;
// its top tier carries the growth-bounds estimates (Bounds*).
// - nat_monus — truncated subtraction and the dist metric. The
// operators are plain recursion, but the chapter's laws are
// order-entangled (m - n = 0 ⇔ m ≤ n), so it stands ABOVE
// nat_order.
// - nat_div_mod — Euclidean division (nat_div nat_mod). Above nat_order by
// definition, not just by proof: the spec itself states the
// remainder bound nat_mod(m, n) < n.
// - nat_divides — divisibility, defined in ℕ: d ∣ n when n is a multiple
// of d. The relation is ℕ's own; see below.
// - nat_congruence — congruence, defined in ℕ: x ≡ y (mod n) when the two
// leave the same remainder; its arithmetic, its reading as divisibility
// of the distance, and the Chinese remainder theorem.
// - nat_gcd — the greatest common divisor and coprimality, defined in
// ℕ over nat_divides. The existence its Hilbert choice needs is
// Euclid's algorithm, run as a course-of-values induction on
// nat_order's well-foundedness tier.
// - nat_prime — primality, defined in ℕ over nat_divides, Euclid's
// lemma, the infinitude of the primes, and factorization into primes
// (as a list, unique up to permutation — datatypes/list's), and
// Fermat's little theorem by the binomial theorem. Euclid's lemma needs
// no descent: the gcd's universal property is enough to cancel a coprime
// factor.
// - binomial — the binomial coefficients, defined by Pascal's rule as a
// recursion on the row, and the binomial theorem over nat_sum.
// - nat_parity — nat_even and nat_odd. Two primitive recursions returning
// bool, so the chapter's definitional layer is nat_arith's recursion
// principle at a different result type; it stands above nat_div_mod
// for the laws that read parity off a remainder.
//
// Divisibility is defined here, inside ℕ. `a ∣ b` is arithmetic, and a
// divisibility DEFINED through the ℤ embedding would put ℤ underneath
// every ℕ statement about it.
// nat_divides defines the relation inside ℕ, and nat_cong,
// nat_gcd and nat_prime do the same for congruence, the gcd and
// primality.
// What the crossing itself says is the two transport laws on the ℤ
// side — int_divides.OfNumDivides and int_congruence.OfNumCongruent.
//
// The notation follows the same choice. `d ∣ n` and `x ≡ y (mod n)` mean
// the NATIVE constants.
//
// The blank imports below are the package's whole content: they trigger
// the families' registration into registry and give
// proofs/proofs.go one line per domain rather than one per family.
package nat_num

import (
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_asymptotics"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/primes_in_progressions"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/sum_of_squares"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/totient"
)
