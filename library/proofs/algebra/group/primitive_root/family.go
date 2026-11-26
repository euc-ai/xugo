package primitive_root

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed primitive_root.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/primitive_root", familyCNF)
