package algebra_points

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebra_points.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/algebra_points", familyCNF)
