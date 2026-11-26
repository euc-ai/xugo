package discriminant

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed discriminant.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/number_field/discriminant", familyCNF)
