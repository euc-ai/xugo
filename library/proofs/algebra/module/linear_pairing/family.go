package linear_pairing

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed linear_pairing.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/linear_pairing", familyCNF)
