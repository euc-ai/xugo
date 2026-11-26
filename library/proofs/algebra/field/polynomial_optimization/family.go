package polynomial_optimization

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_optimization.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/polynomial_optimization", familyCNF)
