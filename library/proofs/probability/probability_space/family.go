package probability_space

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed probability_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/probability_space", familyCNF).WithCoerceDomain(
	RealDomain)
