package dyadic_integers

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dyadic_integers.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/dyadic_integers", familyCNF)
