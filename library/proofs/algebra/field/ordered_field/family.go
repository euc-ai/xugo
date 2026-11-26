package ordered_field

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ordered_field.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/ordered_field", familyCNF)
