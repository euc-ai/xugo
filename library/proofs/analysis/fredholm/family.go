package fredholm

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed fredholm.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/fredholm", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
