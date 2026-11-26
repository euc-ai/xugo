package discrete_l2

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/l2_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed discrete_l2.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/discrete_l2", familyCNF).WithCoerceDomain(RealDomain)
