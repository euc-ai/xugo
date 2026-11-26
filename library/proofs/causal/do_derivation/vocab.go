// vocab.go — the expression datatype as a phantom of the typed term
// surface, declared beside its mint (ext/holtype_phantom.go).

package do_derivation

import (
	"github.com/euc-ai/xugo/ext"
)

// DoExpr is `do_expr(I)`: a causal expression over nodes of type I.
type DoExpr[Node ext.TypePhantom] struct{}

func (DoExpr[Node]) Reify() ext.HolType { return ext.MakeType("do_expr", ext.HolTypeOf[Node]()) }
