package ordered_ring_formula_combinators

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ordered_ring_formula_combinators.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/ordered_ring_formula_combinators", familyCNF)
