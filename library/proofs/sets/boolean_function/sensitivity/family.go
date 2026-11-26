package sensitivity

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed sensitivity.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/boolean_function/sensitivity", familyCNF)
