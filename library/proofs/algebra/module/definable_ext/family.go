package definable_ext

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed definable_ext.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/definable_ext", familyCNF)
