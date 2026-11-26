// vocab.go — the vertex types of the bow graph and the front-door graph
// as phantoms of the typed term surface, declared beside their mints
// (ext/holtype_phantom.go).

package identifiability

import (
	"github.com/euc-ai/xugo/ext"
)

// BowNode is `bow_node`: the vertices of the bow graph.
type BowNode struct{}

func (BowNode) Reify() ext.HolType { return ext.MakeType("bow_node") }

// FdNode is `fd_node`: the vertices of the front-door graph.
type FdNode struct{}

func (FdNode) Reify() ext.HolType { return ext.MakeType("fd_node") }
