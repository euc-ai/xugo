// vocab.go — the typed simplicial record.

package simplicial_set

import "github.com/euc-ai/xugo/ext"

// SimplicialOps is the typed surface of a simplicial set's record.
type SimplicialOps[Simplex ext.TypePhantom] struct{}

func (SimplicialOps[Simplex]) Reify() ext.HolType {
	return ext.MakeType("simplicial_ops", ext.HolTypeOf[Simplex]())
}
