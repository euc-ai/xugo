package field_norm

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field_norm.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/field_norm", familyCNF)
