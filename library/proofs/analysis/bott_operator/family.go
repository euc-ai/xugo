package bott_operator

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_pseudo_differential"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/hermite_function"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bott_operator.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/bott_operator", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
