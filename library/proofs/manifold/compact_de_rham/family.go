package compact_de_rham

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed compact_de_rham.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/compact_de_rham", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
