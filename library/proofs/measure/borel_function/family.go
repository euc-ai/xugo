package borel_function

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed borel_function.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/borel_function", familyCNF).WithCoerceDomain(RealDomain)
