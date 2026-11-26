// vocab.go — the chapter's record type as a phantom of the typed term
// surface, declared beside its mint (ext/holtype_phantom.go).

package module_extension

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// ModuleExtensionOps is `module_extension_ops(A, B, C, D)`: the module of
// an extension on the type C over the scalars A, the inclusion of the
// kernel's vectors D and the projection onto the quotient's vectors B, as
// one value.
type ModuleExtensionOps[Scalar, Quotient, Host, Kernel ext.TypePhantom] struct{}

func (ModuleExtensionOps[Scalar, Quotient, Host, Kernel]) Reify() ext.HolType {
	return MakeType(
		"module_extension_ops",
		ext.HolTypeOf[Scalar](),
		ext.HolTypeOf[Quotient](),
		ext.HolTypeOf[Host](),
		ext.HolTypeOf[Kernel]())
}
