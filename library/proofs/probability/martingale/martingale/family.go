package martingale

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	_ "github.com/euc-ai/xugo/library/proofs/probability/stopping_time"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed martingale.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/martingale/martingale", familyCNF).WithCoerceDomain(
	RealDomain)
