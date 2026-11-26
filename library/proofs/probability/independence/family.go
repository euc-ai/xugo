package independence

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	_ "github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed independence.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/independence", familyCNF).WithCoerceDomain(RealDomain)
