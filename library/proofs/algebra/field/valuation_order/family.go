package valuation_order

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed valuation_order.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/valuation_order", familyCNF)
