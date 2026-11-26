package first_order

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed first_order.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("datatypes/first_order", familyCNF)
