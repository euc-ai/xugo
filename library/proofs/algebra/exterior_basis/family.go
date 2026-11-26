package exterior_basis

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	_ "github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed exterior_basis.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/exterior_basis", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
