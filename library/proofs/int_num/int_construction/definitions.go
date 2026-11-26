// definitions.go — the chapter's definitional layer: what an integer
// IS, the type carved out for it, and every operation on it.
//
// ℤ is not built from ℕ here. It is carved out of ℝ: a real is an
// INTEGER when its magnitude is a natural, and `int` is the type of
// exactly those reals, with real_of_int taking an integer down to its
// representative and int_of_real bringing a representative back up.
// The inhabitant the type is stamped against is `&0`, a natural seen
// in ℝ.
//
// Every operation is then defined the same way — go down, do the
// arithmetic in ℝ, come back up — so no operation here carries an
// argument of its own, and the chapter's work is showing that the
// round trip is faithful. The two comparisons that are not
// arithmetic, and the two that are not even total, follow the same
// shape: they simply read the real order at the representatives.

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerDef — a real is an integer when its magnitude is a natural.
var IntegerDef = integerDefThm{family.Define(registry.DefEntry{
	Name:      "IntegerDef",
	Key:       "prop_39de4566eb9f7e18",
	Const:     "integer",
	Type:      "real → bool",
	Equations: []string{"∀x:real. integer(x) ⇔ ∃n:num. |x| = &n"},
})}

// IntegerInhabited — there is an integer. A type may only be stamped
// against a non-empty subset, and supplying that inhabitant is the
// only mathematics the type definition costs: `&0` is an integer,
// being the natural 0 seen in ℝ.
var IntegerInhabited = integerInhabitedThm{family.Add(registry.ProofEntry{
	Name: "IntegerInhabited",
	Key:  "prop_5160ef162d1fbb6a",
	// The body's cite of IntegerOfNum also runs the mint before this
	// entry's statement is read: the statement names `integer`, and
	// only the mint answers for the name — read first, the statement
	// fails to parse.
	Build: family.Theorem("∃x:real. integer(x)",
		func(a *Argument) {
			a.Take(a.Term("&0"))
			a.Show(
				"&0 is an integer, being the natural 0 seen in ℝ",
				By(IntegerOfNum.At(a.Ctx().Nat(0))))
		}),
})}

// IntDef — the type of integers: the reals the predicate picks out,
// with real_of_int / int_of_real the bijection, stamped against the
// inhabitant above. Its two facts are the whole content of
// TypeBijection.
var IntDef = family.DefineType(registry.TypeEntry{
	Name:      "Int",
	Type:      "int",
	Abs:       "int_of_real",
	Rep:       "real_of_int",
	Pred:      "λx:real. integer(x)",
	Existence: IntegerInhabited,
	Deps:      []registry.EntryLike{IntegerDef},
})

// IntOfNumDef — a natural as an integer: itself, seen in ℝ and read
// back up. Spelled by a stand-in because the DSL keeps `int_of_num`
// for its own integer-literal surface.
var IntOfNumDef = intOfNumDefThm{family.Define(registry.DefEntry{
	Name:      "IntOfNumDef",
	Key:       "prop_8c7c57af9ad0394",
	Const:     "int_of_num",
	Spelled:   "intOfNum",
	Type:      "num → int",
	Equations: []string{"∀n:num. intOfNum(n) = int_of_real(&n)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

// NumOfIntDef — and back: the natural this integer is the image of,
// chosen. It says nothing about a negative integer, which is why every
// law about it carries a nonnegativity hypothesis.
var NumOfIntDef = numOfIntDefThm{family.Define(registry.DefEntry{
	Name:      "NumOfIntDef",
	Key:       "prop_1777922cbdaa03b4",
	Const:     "num_of_int",
	Type:      "int → num",
	Equations: []string{"∀x:int. num_of_int(x) = εn:num. n = x"},
	Deps:      []registry.EntryLike{IntOfNumDef},
})}

// The four comparisons: the real order, read at the representatives.

var IntLeDef = intLeDefThm{family.Define(registry.DefEntry{
	Name:      "IntLeDef",
	Key:       "prop_aff27e6472e07076",
	Const:     "int_le",
	Type:      "int → int → bool",
	Equations: []string{"∀x y:int. int_le(x, y) ⇔ real_of_int(x) ≤ real_of_int(y)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntLtDef = intLtDefThm{family.Define(registry.DefEntry{
	Name:      "IntLtDef",
	Key:       "prop_5fe43801c8ae91fd",
	Const:     "int_lt",
	Type:      "int → int → bool",
	Equations: []string{"∀x y:int. int_lt(x, y) ⇔ real_of_int(x) < real_of_int(y)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntGeDef = intGeDefThm{family.Define(registry.DefEntry{
	Name:      "IntGeDef",
	Key:       "prop_a3dbac6d18b8c849",
	Const:     "int_ge",
	Type:      "int → int → bool",
	Equations: []string{"∀x y:int. int_ge(x, y) ⇔ real_of_int(x) ≥ real_of_int(y)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntGtDef = intGtDefThm{family.Define(registry.DefEntry{
	Name:      "IntGtDef",
	Key:       "prop_e4b2c7518373b428",
	Const:     "int_gt",
	Type:      "int → int → bool",
	Equations: []string{"∀x y:int. int_gt(x, y) ⇔ real_of_int(x) > real_of_int(y)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

// The arithmetic: go down, compute in ℝ, come back up.

var IntNegDef = intNegDefThm{family.Define(registry.DefEntry{
	Name:      "IntNegDef",
	Key:       "prop_6bdc52b3bc718285",
	Const:     "int_neg",
	Type:      "int → int",
	Equations: []string{"∀x:int. int_neg(x) = int_of_real(-real_of_int(x))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntAddDef = intAddDefThm{family.Define(registry.DefEntry{
	Name:      "IntAddDef",
	Key:       "prop_160e3b071cbc60be",
	Const:     "int_add",
	Type:      "int → int → int",
	Equations: []string{"∀x y:int. int_add(x, y) = int_of_real(real_of_int(x) + real_of_int(y))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntSubDef = intSubDefThm{family.Define(registry.DefEntry{
	Name:      "IntSubDef",
	Key:       "prop_9fd24b8931352214",
	Const:     "int_sub",
	Type:      "int → int → int",
	Equations: []string{"∀x y:int. int_sub(x, y) = int_of_real(real_of_int(x) - real_of_int(y))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntMulDef = intMulDefThm{family.Define(registry.DefEntry{
	Name:      "IntMulDef",
	Key:       "prop_2526ccc27e3cd4c4",
	Const:     "int_mul",
	Type:      "int → int → int",
	Equations: []string{"∀x y:int. int_mul(x, y) = int_of_real(real_of_int(x) * real_of_int(y))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntAbsDef = intAbsDefThm{family.Define(registry.DefEntry{
	Name:      "IntAbsDef",
	Key:       "prop_a84439d5c4135f10",
	Const:     "int_abs",
	Type:      "int → int",
	Notation:  "|x|",
	Overload:  "abs",
	Equations: []string{"∀x:int. int_abs(x) = int_of_real(|real_of_int(x)|)"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntSgnDef = intSgnDefThm{family.Define(registry.DefEntry{
	Name:      "IntSgnDef",
	Key:       "prop_a4246b59588ee9d8",
	Const:     "int_sgn",
	Type:      "int → int",
	Overload:  "sgn",
	Equations: []string{"∀x:int. int_sgn(x) = int_of_real(sgn(real_of_int(x)))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntMaxDef = intMaxDefThm{family.Define(registry.DefEntry{
	Name:      "IntMaxDef",
	Key:       "prop_254a05c052480947",
	Const:     "int_max",
	Type:      "int → int → int",
	Overload:  "max",
	Equations: []string{"∀x y:int. int_max(x, y) = int_of_real(max(real_of_int(x), real_of_int(y)))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}

var IntMinDef = intMinDefThm{family.Define(registry.DefEntry{
	Name:      "IntMinDef",
	Key:       "prop_7ffcc27ee8d0fc71",
	Const:     "int_min",
	Type:      "int → int → int",
	Overload:  "min",
	Equations: []string{"∀x y:int. int_min(x, y) = int_of_real(min(real_of_int(x), real_of_int(y)))"},
	Deps:      []registry.EntryLike{IntDef.Retraction},
})}
