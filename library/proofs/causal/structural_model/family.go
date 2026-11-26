// family.go — the structural_model family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=structural_model.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/structural_model go test -run TestRecordFamilyCNF ./library/integrity/gates/

package structural_model

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	_ "github.com/euc-ai/xugo/library/proofs/probability/independence"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed structural_model.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the product σ-algebra on
// the configurations of a model M's nodes.
var family = registry.NewFamily("causal/structural_model", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "configSigma", Text: "indexed_product_sigma(M.nodes, M.default, M.states, M.state_sigma)"},
})
