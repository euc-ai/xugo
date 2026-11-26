// vocab.go — the chapter's two record types as phantoms of the typed
// term surface, declared beside their mints (ext/holtype_phantom.go).

package module_record

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// RingOps is `ring_ops(A)`: a ring's six operations and its carrier
// set, as one value.
type RingOps[Scalar ext.TypePhantom] struct{}

func (RingOps[Scalar]) Reify() ext.HolType { return MakeType("ring_ops", ext.HolTypeOf[Scalar]()) }

// ModuleOps is `module_ops(A, B)`: a module's addition, zero,
// negation, scalar action and carrier set, as one value.
type ModuleOps[Scalar, Vector ext.TypePhantom] struct{}

func (ModuleOps[Scalar, Vector]) Reify() ext.HolType {
	return MakeType("module_ops", ext.HolTypeOf[Scalar](), ext.HolTypeOf[Vector]())
}
