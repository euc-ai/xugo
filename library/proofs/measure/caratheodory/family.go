package caratheodory

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	_ "github.com/euc-ai/xugo/library/proofs/measure/outer_measure"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed caratheodory.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/caratheodory", familyCNF).WithCoerceDomain(RealDomain)
