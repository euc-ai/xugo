package complex_measure_integral

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	_ "github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_measure_integral.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/complex_measure_integral", familyCNF).WithCoerceDomain(
	RealDomain)
