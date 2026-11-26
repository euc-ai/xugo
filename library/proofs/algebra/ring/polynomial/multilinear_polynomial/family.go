package multilinear_polynomial

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed multilinear_polynomial.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/polynomial/multilinear_polynomial", familyCNF)
