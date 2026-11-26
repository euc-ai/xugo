package semialgebraic_properties

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed semialgebraic_properties.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/semialgebraic_properties", familyCNF)
