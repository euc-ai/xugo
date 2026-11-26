package cyclic_group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cyclic_group.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/cyclic_group", familyCNF)
