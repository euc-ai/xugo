package units_mod

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed units_mod.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/units_mod", familyCNF)
