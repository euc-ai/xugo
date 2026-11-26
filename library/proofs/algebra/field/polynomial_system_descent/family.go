package polynomial_system_descent

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_system_descent.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/polynomial_system_descent", familyCNF)
