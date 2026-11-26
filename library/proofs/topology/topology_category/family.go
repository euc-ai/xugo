package topology_category

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/category/category"
	_ "github.com/euc-ai/xugo/library/proofs/category/set_category"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed topology_category.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/topology_category", familyCNF)
