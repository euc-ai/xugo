package ideal_factorization

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ideal_factorization.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/ideal_factorization", familyCNF).WithAbbrev(Abbrev{
	{Name: "Delete", Text: "λt:(set(A) → num). λm:set(A). λq:set(A). COND(q = m, 0, t(q))"},
	{Name: "R", Text: "restrict_ring(field_ring(L), S)"},
	{Name: "RestSupport", Text: "fun_support(0, λp:set(A). «Delete»(v, m, p))"},
})
