package conditional_expectation

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	_ "github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed conditional_expectation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/conditional_expectation", familyCNF).WithCoerceDomain(
	RealDomain)
