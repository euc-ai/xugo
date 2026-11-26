package rational_function_field

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed rational_function_field.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/rational_function_field", familyCNF)
