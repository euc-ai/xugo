package torus_pseudo_differential

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed torus_pseudo_differential.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("analysis/torus_pseudo_differential", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
