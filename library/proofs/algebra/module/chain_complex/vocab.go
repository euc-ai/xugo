// vocab.go — typed complex records.

package chain_complex

import "github.com/euc-ai/xugo/ext"

// ComplexOps is the typed surface of a complex's data record.
type ComplexOps[Scalar, Vector ext.TypePhantom] struct{}

func (ComplexOps[Scalar, Vector]) Reify() ext.HolType {
	return ext.MakeType("complex_ops", ext.HolTypeOf[Scalar](), ext.HolTypeOf[Vector]())
}
