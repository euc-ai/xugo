package l2_martingale

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/conditional_projection"
	_ "github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed l2_martingale.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/martingale/l2_martingale", familyCNF).WithCoerceDomain(
	RealDomain)
