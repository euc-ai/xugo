package integral_element

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed integral_element.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/integral_element", familyCNF)
