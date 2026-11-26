// vocab.go — the chapter's three record types as phantoms of the typed
// term surface, declared beside their mints (ext/holtype_phantom.go).

package category

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// CategoryOps is `category_ops(A, M)`: a category's objects and
// morphisms with its source, target, identity and composition, as one
// value.
type CategoryOps[Object, Morphism ext.TypePhantom] struct{}

func (CategoryOps[Object, Morphism]) Reify() ext.HolType {
	return MakeType("category_ops", ext.HolTypeOf[Object](), ext.HolTypeOf[Morphism]())
}

// FunctorOps is `functor_ops(A, M, B, N)`: a functor's map of objects
// and map of morphisms, as one value.
type FunctorOps[Object, Morphism, Object2, Morphism2 ext.TypePhantom] struct{}

func (FunctorOps[Object, Morphism, Object2, Morphism2]) Reify() ext.HolType {
	return MakeType(
		"functor_ops",
		ext.HolTypeOf[Object](),
		ext.HolTypeOf[Morphism](),
		ext.HolTypeOf[Object2](),
		ext.HolTypeOf[Morphism2]())
}

// MorphismTriple is `morphism_triple(A, D)`: a morphism datum framed
// by its source and target, as one value.
type MorphismTriple[Object, Datum ext.TypePhantom] struct{}

func (MorphismTriple[Object, Datum]) Reify() ext.HolType {
	return MakeType("morphism_triple", ext.HolTypeOf[Object](), ext.HolTypeOf[Datum]())
}
