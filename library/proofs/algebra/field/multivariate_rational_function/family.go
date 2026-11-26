package multivariate_rational_function

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed multivariate_rational_function.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/multivariate_rational_function", familyCNF)
