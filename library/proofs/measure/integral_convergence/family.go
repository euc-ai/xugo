package integral_convergence

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed integral_convergence.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/integral_convergence", familyCNF).WithCoerceDomain(
	RealDomain)
