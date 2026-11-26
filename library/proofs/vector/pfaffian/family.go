package pfaffian

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed pfaffian.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("vector/pfaffian", familyCNF)
