package conditional_projection

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/l2_space"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed conditional_projection.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/conditional_projection", familyCNF).WithCoerceDomain(
	RealDomain)
