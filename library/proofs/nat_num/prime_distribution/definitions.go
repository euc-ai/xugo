package prime_distribution

import (
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeCountingDef — π(n): the number of primes up to n.
var PrimeCountingDef = primeCountingDefThm{family.Define(registry.DefEntry{
	Name:      "PrimeCountingDef",
	Key:       "prop_8ecd7ea894466421",
	Const:     "prime_counting",
	Type:      "num → num",
	Equations: []string{"∀n:num. prime_counting(n) = card({p:num | p ≤ n ∧ nat_prime(p)})"},
})}

// PrimorialDef — the product of the primes up to n.
var PrimorialDef = primorialDefThm{family.Define(registry.DefEntry{
	Name:  "PrimorialDef",
	Key:   "prop_2a9bac30abb909b3",
	Const: "primorial",
	Type:  "num → num",
	Equations: []string{
		"∀n:num. primorial(n) = nat_product({p:num | p ≤ n ∧ nat_prime(p)}, λp:num. p)",
	},
})}

// VonMangoldtDef — Λ(n): log p when n is a power pᵏ of a prime p with
// k > 0, and 0 otherwise.
var VonMangoldtDef = vonMangoldtDefThm{family.Define(registry.DefEntry{
	Name:  "VonMangoldtDef",
	Key:   "prop_ea8a035a1e238c0e",
	Const: "von_mangoldt",
	Type:  "num → real",
	Equations: []string{
		"∀n:num. von_mangoldt(n) = COND(«isPrimePower»(n), log(&«primeBase»(n)), &0)",
	},
	Reading: "A prime power pᵏ with k > 0 has p as its only prime divisor, " +
		"so the ε picks p. Λ(0) = Λ(1) = 0: neither is a positive power of a prime.",
})}

// ChebyshevPsiDef — ψ(n): the sum of Λ(m) over 1 ≤ m ≤ n, the logarithm
// of the least common multiple of 1, …, n.
var ChebyshevPsiDef = chebyshevPsiDefThm{family.Define(registry.DefEntry{
	Name:      "ChebyshevPsiDef",
	Key:       "prop_78b44c26eccd370b",
	Const:     "chebyshev_psi",
	Type:      "num → real",
	Equations: []string{"∀n:num. chebyshev_psi(n) = Σ_{m∈1 .. n} von_mangoldt(m)"},
	Deps:      []registry.EntryLike{VonMangoldtDef},
})}
