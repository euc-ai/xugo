package polish_group

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polish_group.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/polish_group", familyCNF)
