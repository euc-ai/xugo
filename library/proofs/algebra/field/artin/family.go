package artin

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed artin.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/artin", familyCNF)
