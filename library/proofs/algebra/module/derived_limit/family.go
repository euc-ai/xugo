package derived_limit

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed derived_limit.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/derived_limit", familyCNF)
