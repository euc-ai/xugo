// definitions.go — the chapter's definitional layer: the mechanism
// itself, carrier-free.
//
// Four constants, in the order they build on one another. `neutral_elem`
// picks the element an operation folds from — by CHOICE, so it names
// something whether or not the operation has a unit, and every law
// about it holds under `monoidal_op`. `monoidal_op` is the condition: the
// operation commutes, associates, and has that element as its unit.
// `op_support` is where a function differs from the neutral, which is the
// only part of an index set a fold can see. And `iterated_op` is the fold:
// over the support when the support is finite, and the neutral
// otherwise — total by construction, so the chapter's laws carry
// finiteness hypotheses rather than the definition carrying a
// side-condition.

package monoidal

import (
	"github.com/euc-ai/xugo/library/registry"
)

// NeutralElemDef — the element an operation folds from, chosen: something
// both sides of the operation leave alone.
var NeutralElemDef = neutralElemDefThm{family.Define(registry.DefEntry{
	Name:      "NeutralElemDef",
	Key:       "prop_8e2535afb1108688",
	Const:     "neutral_elem",
	Type:      "(A → A → A) → A",
	Equations: []string{"∀op:(A → A → A). neutral_elem(op) = εx:A. ∀y:A. op(x, y) = y ∧ op(y, x) = y"},
})}

// MonoidalOpDef — what it takes to fold: commutative, associative, and
// with the chosen element as unit.
var MonoidalOpDef = monoidalOpDefThm{family.Define(registry.DefEntry{
	Name:  "MonoidalOpDef",
	Key:   "prop_4180876e8f4fd995",
	Const: "monoidal_op",
	Type:  "(A → A → A) → bool",
	Equations: []string{"∀op:(A → A → A). " +
		"    monoidal_op(op) ⇔ " +
		"    (∀x y:A. op(x, y) = op(y, x)) ∧ " +
		"    (∀x y z:A. op(x, op(y, z)) = op(op(x, y), z)) ∧ " +
		"    (∀x:A. op(neutral_elem(op), x) = x)"},
	Deps: []registry.EntryLike{NeutralElemDef},
})}

// OpSupportDef — where a function differs from the neutral: the only
// part of an index set the fold can see.
var OpSupportDef = opSupportDefThm{family.Define(registry.DefEntry{
	Name:  "OpSupportDef",
	Key:   "prop_930fed4f0058948c",
	Const: "op_support",
	Type:  "(B → B → B) → (A → B) → set(A) → set(A)",
	Equations: []string{
		"∀op:(B → B → B). ∀f:(A → B). ∀s:set(A). " +
			"    op_support(op, f, s) = {x:A | x ∈ s ∧ ¬(f(x) = neutral_elem(op))}",
	},
	Deps: []registry.EntryLike{NeutralElemDef},
})}

// IteratedOpDef — the fold: over the support when that is finite, and
// the neutral otherwise. Total, so no law here is stated as a partial
// function's would be.
var IteratedOpDef = iteratedOpDefThm{family.Define(registry.DefEntry{
	Name:  "IteratedOpDef",
	Key:   "prop_e4e5d7968cfb11c9",
	Const: "iterated_op",
	Type:  "(B → B → B) → set(A) → (A → B) → B",
	Equations: []string{"∀op:(B → B → B). ∀s:set(A). ∀f:(A → B). " +
		"    iterated_op(op, s, f) = " +
		"    COND(finite(op_support(op, f, s)), " +
		"        set_fold((λx:A. λa:B. op(f(x), a)), op_support(op, f, s), neutral_elem(op)), " +
		"        neutral_elem(op))"},
	Deps: []registry.EntryLike{OpSupportDef, NeutralElemDef},
})}
