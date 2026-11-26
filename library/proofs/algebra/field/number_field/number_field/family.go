package number_field

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed number_field.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/number_field/number_field", familyCNF)
