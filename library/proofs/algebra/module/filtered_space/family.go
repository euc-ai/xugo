package filtered_space

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed filtered_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/filtered_space", familyCNF)
