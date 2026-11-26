package measurable_space

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"
	_ "github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed measurable_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/measurable_space", familyCNF)
