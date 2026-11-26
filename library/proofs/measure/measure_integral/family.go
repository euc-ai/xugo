package measure_integral

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed measure_integral.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/measure_integral", familyCNF).WithCoerceDomain(RealDomain)
