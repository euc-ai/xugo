package prime_distribution

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed prime_distribution.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter names two sets of primes its
// proofs keep returning to, the primes up to m and the primes in ⟬a, b⟧, and
// the prime powers Λ reads: «isPrimePower»(d), d is a positive power of a prime;
// «primeBase»(d), the prime divisor chosen from d, which is the base of a
// prime power; «powersThrough»(p, K), the powers p, …, pᴷ; and
// «powersIn»(s, p), the positive powers of p in s. Λ and ψ are real-valued,
// so an `&` no operand anchors is ℝ's embedding, by the declaration on the handle.
var family = registry.NewFamily("nat_num/prime_distribution", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "primes", Text: "λm:num. {p:num | p ≤ m ∧ nat_prime(p)}"},
	{Name: "primesBetween", Text: "λa:num. λb:num. {p:num | a < p ∧ p ≤ b ∧ nat_prime(p)}"},
	{Name: "isPrimePower", Text: "λd:num. ∃p k:num. nat_prime(p) ∧ 0 < k ∧ d = p ^ k"},
	{Name: "primeBase", Text: "λd:num. εq:num. nat_prime(q) ∧ q ∣ d"},
	{Name: "powersThrough", Text: "λp:num. λK:num. image(λk:num. p ^ k, 1 .. K)"},
	{Name: "powersIn", Text: "λs:set(num). λp:num. {d:num | d ∈ s ∧ (∃k:num. 0 < k ∧ d = p ^ k)}"},
})
