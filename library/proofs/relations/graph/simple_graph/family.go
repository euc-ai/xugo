// family.go — the simple_graph family manifest: the registry handle every
// member registers into, the family's shared recorded CNF cache, and the
// chapter's abbreviation table.
//
//	XUGO_RECORD_FAMILY_CNF=simple_graph.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/simple_graph go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simple_graph

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simple_graph.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the adjacency left when
// the edge {u, v} is deleted and the components of u and of v in what is
// left, which the edge-deletion and tree members spell over their binders
// V, R, u and v.
var family = registry.NewFamily("relations/graph/simple_graph", familyCNF).WithAbbrev(Abbrev{
	{Name: "remaining", Text: "graph_delete_edge(R, {u, v})"},
	{Name: "componentOfU", Text: "graph_component(V, «remaining», u)"},
	{Name: "componentOfV", Text: "graph_component(V, «remaining», v)"},
})
