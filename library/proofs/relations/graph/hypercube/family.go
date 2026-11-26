package hypercube

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed hypercube.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/hypercube", familyCNF).WithCoerceDomain(RealDomain)
