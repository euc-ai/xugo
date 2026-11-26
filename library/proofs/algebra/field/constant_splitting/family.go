package constant_splitting

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed constant_splitting.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/constant_splitting", familyCNF)
