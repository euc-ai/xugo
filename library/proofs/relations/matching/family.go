package matching

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed matching.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/matching", familyCNF)
