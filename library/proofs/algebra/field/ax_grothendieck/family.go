package ax_grothendieck

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ax_grothendieck.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/ax_grothendieck", familyCNF)
