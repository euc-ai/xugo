package polynomial_brouwer

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_brouwer.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/polynomial_brouwer", familyCNF)
