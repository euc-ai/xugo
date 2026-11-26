package l2_space

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/lp_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed l2_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/l2_space", familyCNF).WithCoerceDomain(RealDomain)
