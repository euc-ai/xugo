package torus_sobolev

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/function_support"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed torus_sobolev.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/torus_sobolev", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
