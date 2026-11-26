package spec_functor

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed spec_functor.cnf.pb
var familyCNF []byte
var family = registry.NewFamily("scheme/spec_functor", familyCNF)
