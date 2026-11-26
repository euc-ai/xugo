package gauss_sum

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed gauss_sum.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter's statements, over a field F and
// an odd prime p, read every Legendre symbol (a/p) in F through the
// integers' map: that character is χ.
var family = registry.NewFamily("algebra/field/gauss_sum", familyCNF).WithAbbrev(Abbrev{
	{Name: "χ", Text: "λa:num. integer_map(field_ring(F), legendre_symbol(a, p))"},
})
