package constant_galois

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed constant_galois.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/constant_galois", familyCNF)
