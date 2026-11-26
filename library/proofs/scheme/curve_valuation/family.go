package curve_valuation

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed curve_valuation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/curve_valuation", familyCNF)
