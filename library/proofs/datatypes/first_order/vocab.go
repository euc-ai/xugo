package first_order

import "github.com/euc-ai/xugo/ext"

// Formula is the phantom of formulas with atoms of type Atom.
type Formula[Atom ext.TypePhantom] struct{}

func (Formula[Atom]) Reify() ext.HolType {
	return ext.MakeType(
		"fo_formula", ext.HolTypeOf[Atom]())
}
