package definable_andre_quillen

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed definable_andre_quillen.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/cotangent/definable_andre_quillen", familyCNF)
