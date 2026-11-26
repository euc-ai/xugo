package polynomial_sign_table

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_sign_table.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/polynomial_sign_table", familyCNF)
