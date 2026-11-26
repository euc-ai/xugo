package boolean_function

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed boolean_function.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/boolean_function/boolean_function", familyCNF)
