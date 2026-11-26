package measure_space

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	_ "github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed measure_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/measure_space", familyCNF).WithCoerceDomain(RealDomain)
