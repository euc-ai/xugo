package residue_points

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed residue_points.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/residue_points", familyCNF)
