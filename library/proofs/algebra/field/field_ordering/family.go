package field_ordering

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field_ordering.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/field_ordering", familyCNF)
