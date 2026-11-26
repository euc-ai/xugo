package definable_deformation

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed definable_deformation.cnf.pb
var familyCNF []byte
var family = registry.NewFamily("algebra/cotangent/definable_deformation", familyCNF)
