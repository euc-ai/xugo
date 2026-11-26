package gamma_spec

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed gamma_spec.cnf.pb
var familyCNF []byte
var family = registry.NewFamily("scheme/gamma_spec", familyCNF)
