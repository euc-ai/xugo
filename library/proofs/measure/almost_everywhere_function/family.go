package almost_everywhere_function

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed almost_everywhere_function.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/almost_everywhere_function", familyCNF).WithCoerceDomain(
	RealDomain)
