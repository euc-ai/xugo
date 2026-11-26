package torus_fourier

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/lattice"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed torus_fourier.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/torus_fourier", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
