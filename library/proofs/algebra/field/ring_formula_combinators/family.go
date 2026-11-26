package ring_formula_combinators

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_formula_combinators.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/ring_formula_combinators", familyCNF)
