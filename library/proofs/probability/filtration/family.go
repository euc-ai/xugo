package filtration

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	_ "github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed filtration.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/filtration", familyCNF).WithCoerceDomain(RealDomain)
