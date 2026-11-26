package sum_of_squares

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed sum_of_squares.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("nat_num/sum_of_squares", familyCNF)
