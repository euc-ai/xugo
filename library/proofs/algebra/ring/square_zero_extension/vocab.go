// vocab.go — the chapter's record type as a phantom of the typed term
// surface, declared beside its mint (ext/holtype_phantom.go).

package square_zero_extension

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// SquareZeroOps is `square_zero_ops(A, B, C, D)`: the ring of an
// extension on the type C, its structure map from the base ring's type
// A, the inclusion of the module's vectors D and the projection onto the
// type B of the ring extended, as one value.
type SquareZeroOps[Base, Quotient, Host, Kernel ext.TypePhantom] struct{}

func (SquareZeroOps[Base, Quotient, Host, Kernel]) Reify() ext.HolType {
	return MakeType(
		"square_zero_ops",
		ext.HolTypeOf[Base](),
		ext.HolTypeOf[Quotient](),
		ext.HolTypeOf[Host](),
		ext.HolTypeOf[Kernel]())
}
