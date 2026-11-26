package integral_closure

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed integral_closure.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/number_field/integral_closure", familyCNF)
