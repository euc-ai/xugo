package milnor_sequence

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed milnor_sequence.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/milnor_sequence", familyCNF)
