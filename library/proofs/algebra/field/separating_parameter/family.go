package separating_parameter

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed separating_parameter.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/separating_parameter", familyCNF)
