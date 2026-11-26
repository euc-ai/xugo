package compact_chern

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed compact_chern.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/compact_chern", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
