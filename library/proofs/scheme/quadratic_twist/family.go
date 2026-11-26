package quadratic_twist

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed quadratic_twist.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/quadratic_twist", familyCNF)
