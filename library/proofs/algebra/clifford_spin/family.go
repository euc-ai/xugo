package clifford_spin

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed clifford_spin.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/clifford_spin", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
