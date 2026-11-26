package weighted_divisors

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed weighted_divisors.cnf.pb
var familyCNF []byte

// family is the family handle, with the chapter's abbreviations: «conv»
// multiplies sequences of naturals as power series, «step» multiplies by
// the geometric series of a point's weight and «unit» is the series 1,
// «lowWeight» is the level of the weight at n, «divisors» the effective
// divisors of degree n, and «oneToN» the degrees 0 < m ≤ n.
var family = registry.NewFamily("sets/weighted_divisors", familyCNF).WithAbbrev(Abbrev{
	{Name: "conv", Text: "polynomial_mul(λi:num. λj:num. i + j, 0, λi:num. λj:num. i * j)"},
	{Name: "step", Text: "λx:A. λa:(num → num). «conv»(λi:num. COND(w(x) ∣ i, 1, 0), a)"},
	{Name: "unit", Text: "λi:num. COND(i = 0, 1, 0)"},
	{Name: "lowWeight", Text: "{y:A | y ∈ S ∧ w(y) ≤ n}"},
	{Name: "divisors", Text: "{D:A → num | weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n}"},
	{Name: "oneToN", Text: "{m:num | 0 < m ∧ m ≤ n}"},
})
