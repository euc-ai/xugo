package toeplitz_operator

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	_ "github.com/euc-ai/xugo/library/proofs/complex/residue"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed toeplitz_operator.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/toeplitz_operator", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
