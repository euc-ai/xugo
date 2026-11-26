package analytic_index

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/pseudo_differential"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed analytic_index.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/analytic_index", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
