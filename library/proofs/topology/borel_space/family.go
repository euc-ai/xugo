package borel_space

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed borel_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/borel_space", familyCNF)
