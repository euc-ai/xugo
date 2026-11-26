package twist_quotient_bound

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed twist_quotient_bound.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/twist_quotient_bound", familyCNF)
