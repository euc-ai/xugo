package quadratic_reciprocity

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed quadratic_reciprocity.cnf.pb
var familyCNF []byte

// family is the family handle. It reads under quadratic_residue's table,
// whose «h»(n) = (n − 1)/2 is the exponent of every sign here. The chapter
// names the set its Jacobi symbols are products over, the primes dividing n,
// and the signed prime p* = (−1/p)·p whose symbol the Gauss sum computes.
var family = registry.NewFamily("int_num/quadratic_reciprocity", familyCNF).WithOuterAbbrev(
	quadratic_residue.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "primeDivisors", Text: "λn:num. {p:num | nat_prime(p) ∧ p ∣ n}"},
	{Name: "p*", Text: "λp:num. legendre_symbol(-1, p) * p"},
})
