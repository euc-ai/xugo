// vocab.go — the model record as a phantom of the typed term surface,
// declared beside its mint (ext/holtype_phantom.go).

package structural_model

import (
	"github.com/euc-ai/xugo/ext"
)

// ScmModel is `scm_model(A, B, I)`: a structural causal model with
// samples of type A, states in B and nodes of type I, as one value.
type ScmModel[Sample, State, Node ext.TypePhantom] struct{}

func (ScmModel[Sample, State, Node]) Reify() ext.HolType {
	return ext.MakeType(
		"scm_model", ext.HolTypeOf[Sample](), ext.HolTypeOf[State](), ext.HolTypeOf[Node]())
}
