// definitions.go — the chapter's definitional layer: the datatype
// option(A) with its two constructors.

package option

import (
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// OptionData — an optional value is either absent (none) or present
// (some a). The datatype door mints the type and its constructors and
// registers the four principles a datatype comes with, each derived
// through the recursive-type universe the type is carved from
// (recspace): induction, the recursion schema, injectivity of some and
// the distinctness of the constructors. The induction tactic reads the
// first under the library name option_induction, and the define door's
// equation compiler reads the second under option_recursion.
var OptionData = family.DefineData(registry.DataEntry{
	Name:   "Option",
	Type:   "option",
	Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "none"},
		{Name: "some", Args: []string{"A"}},
	},
	// The four principles' registered names — the words the vars below
	// carry, so a session cites what this file spells.
	Principles: registry.DataPrinciples{
		Induction: "Induction",
		Recursion: "Recursion",
		Injective: "SomeInjective",
		Distinct:  "NoneNotSome",
	},
	// The universe's rows the derivations read: its recursion theorem
	// and its countable-family constructor (the schema), its node
	// constructor's injectivity (read for some's injectivity and for
	// none ≠ some), and 0 ≠ suc (the two tags differ).
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
	},
})

// The four principles under chapter names — the names the door
// registers (Principles above), so `option.NoneNotSome` is one name in
// Go and in a session.
var (
	// Induction — a property holding at none and at every some(a) holds
	// of every optional value: P(none), (∀a. P(some(a))) ⊢ P(x). There
	// is no recursive constructor, so this is a case analysis dressed
	// as an induction.
	Induction = inductionThm{OptionData.Induct}
	// Recursion — a function on optional values is determined by its
	// value at none and its values at the some(a): ∀none' some'. ∃fn.
	// fn(none) = none' ∧ ∀a. fn(some(a)) = some'(a).
	Recursion = recursionThm{OptionData.Recursion}
	// SomeInjective — some(a) = some(b) ⇔ a = b.
	SomeInjective = someInjectiveThm{OptionData.Inj}
	// NoneNotSome — none ≠ some(a).
	NoneNotSome = noneNotSomeThm{OptionData.Distinct}
)
