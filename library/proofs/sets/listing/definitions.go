// definitions.go — the chapter's definitional layer: the set of a
// list's elements, and a list enumerating a set.

package listing

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SetOfListDef — the set of a list's elements, by recursion on the
// list: nothing for nil, and the head laid into the tail's set for
// cons.
var SetOfListDef = setOfListDefThm{family.Define(registry.DefEntry{
	Name:  "SetOfListDef",
	Key:   "prop_fd4c5081b9a8d310",
	Const: "set_of_list",
	Type:  "list(A) → set(A)",
	Equations: []string{
		"set_of_list(nil) = ∅",
		"∀h:A. ∀t:list(A). set_of_list(cons(h, t)) = insert(h, set_of_list(t))",
	},
})}

// ListOfSetDef — a list enumerating a set: some list whose set is s
// and whose length is s's count, chosen. The length clause is what
// makes the enumeration repetition-free — a list's set counts at most
// its length, with equality exactly for a distinct list — so a list
// meeting both clauses lists each element of s once. A finite set has
// such a list; an infinite set has none, since every list's set is
// finite, and the choice is then arbitrary.
var ListOfSetDef = listOfSetDefThm{family.Define(registry.DefEntry{
	Name:  "ListOfSetDef",
	Key:   "prop_a6acf6d684407987",
	Const: "list_of_set",
	Type:  "set(A) → list(A)",
	Equations: []string{
		"∀s:set(A). list_of_set(s) = εl:list(A). set_of_list(l) = s ∧ list_length(l) = card(s)",
	},
	Deps: []registry.EntryLike{SetOfListDef},
})}
