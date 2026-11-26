package roots_of_unity

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed roots_of_unity.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/roots_of_unity", familyCNF)
