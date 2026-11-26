package constant_twist

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed constant_twist.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/constant_twist", familyCNF)
