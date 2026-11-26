package indexed_functions

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed indexed_functions.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/indexed_functions", familyCNF)
