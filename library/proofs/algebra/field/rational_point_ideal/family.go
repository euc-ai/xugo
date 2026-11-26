package rational_point_ideal

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed rational_point_ideal.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/rational_point_ideal", familyCNF)
