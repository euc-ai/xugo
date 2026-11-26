package constant_composite

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed constant_composite.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/constant_composite", familyCNF)
