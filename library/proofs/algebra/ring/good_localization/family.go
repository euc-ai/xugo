package good_localization

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed good_localization.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/good_localization", familyCNF)
