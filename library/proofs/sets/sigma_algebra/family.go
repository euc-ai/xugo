package sigma_algebra

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed sigma_algebra.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/sigma_algebra", familyCNF)
