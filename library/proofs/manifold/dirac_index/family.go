package dirac_index

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/spin_geometry"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dirac_index.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/dirac_index", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
