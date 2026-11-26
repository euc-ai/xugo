package fixed_twist_models

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed fixed_twist_models.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/fixed_twist_models", familyCNF)
