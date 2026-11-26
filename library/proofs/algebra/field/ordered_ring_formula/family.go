package ordered_ring_formula

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ordered_ring_formula.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the models a quantifier-free
// equivalent ranges over: the pairs of a field and an order, real closed,
// with the field's carrier, reading an atom as negativity; a statement over
// the models on B ties them there, «realClosed»⟨A:B⟩.
var family = registry.NewFamily("algebra/field/ordered_ring_formula", familyCNF).WithAbbrev(Abbrev{
	{Name: "realClosed", Text: "λM:prod(field_ops(A), A → A → bool). " +
		"    real_closed_field(fst(M), snd(M))"},
	{Name: "carrier", Text: "λM:prod(field_ops(A), A → A → bool). fst(M).carrier"},
	{Name: "negative", Text: "λM:prod(field_ops(A), A → A → bool). " +
		"    ordered_ring_formula_atom(fst(M), snd(M))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under it
// name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
