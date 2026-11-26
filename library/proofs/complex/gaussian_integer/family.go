package gaussian_integer

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed gaussian_integer.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("complex/gaussian_integer", familyCNF)
