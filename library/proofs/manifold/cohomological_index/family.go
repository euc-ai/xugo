package cohomological_index

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/chern_thom"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/index_comparison"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cohomological_index.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/cohomological_index", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
