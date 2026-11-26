package function_support

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed function_support.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/function_support", familyCNF)
