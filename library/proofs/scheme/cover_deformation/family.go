package cover_deformation

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cover_deformation.cnf.pb
var familyCNF []byte
var family = registry.NewFamily("scheme/cover_deformation", familyCNF)
