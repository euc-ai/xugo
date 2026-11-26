package polish_cohomology

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polish_cohomology.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/polish_cohomology", familyCNF)
