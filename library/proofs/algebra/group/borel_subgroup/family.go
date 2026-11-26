package borel_subgroup

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed borel_subgroup.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/borel_subgroup", familyCNF)
