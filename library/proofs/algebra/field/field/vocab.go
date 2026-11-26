package field

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// FieldOps is a field's ring operations, inverse, division and carrier in one value.
type FieldOps[Scalar ext.TypePhantom] struct{}

func (FieldOps[Scalar]) Reify() ext.HolType {
	return MakeType(
		"field_ops", ext.HolTypeOf[Scalar]())
}
