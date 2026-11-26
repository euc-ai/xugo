package polish_space

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polish_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/polish_space", familyCNF)
