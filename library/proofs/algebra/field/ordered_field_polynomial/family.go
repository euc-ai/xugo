package ordered_field_polynomial

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ordered_field_polynomial.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/ordered_field_polynomial", familyCNF)
