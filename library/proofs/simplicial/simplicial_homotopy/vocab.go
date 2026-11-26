// vocab.go — the typed bisimplicial record.

package simplicial_homotopy

import "github.com/euc-ai/xugo/ext"

// BisimplicialOps is the typed surface of a bisimplicial set's record.
type BisimplicialOps[Simplex ext.TypePhantom] struct{}

func (BisimplicialOps[Simplex]) Reify() ext.HolType {
	return ext.MakeType("bisimplicial_ops", ext.HolTypeOf[Simplex]())
}
