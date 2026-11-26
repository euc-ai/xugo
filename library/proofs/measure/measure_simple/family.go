package measure_simple

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed measure_simple.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/measure_simple", familyCNF).WithCoerceDomain(RealDomain)
