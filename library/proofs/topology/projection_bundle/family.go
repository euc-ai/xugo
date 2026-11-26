package projection_bundle

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projection_bundle.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/projection_bundle", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
