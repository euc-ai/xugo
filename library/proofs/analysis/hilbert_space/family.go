package hilbert_space

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	_ "github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed hilbert_space.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/hilbert_space", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
