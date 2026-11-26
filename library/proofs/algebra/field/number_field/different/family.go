package different

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed different.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/number_field/different", familyCNF)
