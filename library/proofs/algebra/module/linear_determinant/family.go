package linear_determinant

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed linear_determinant.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/linear_determinant", familyCNF)
