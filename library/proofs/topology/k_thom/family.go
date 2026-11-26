package k_thom

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/topology/bott_periodicity"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed k_thom.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/k_thom", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
