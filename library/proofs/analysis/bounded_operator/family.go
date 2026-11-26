package bounded_operator

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bounded_operator.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/bounded_operator", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
