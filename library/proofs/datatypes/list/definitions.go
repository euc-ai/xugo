// definitions.go — the chapter's definitional layer: the datatype
// list(A) with its two constructors, and the operations on lists the
// chapter's theory is about.

package list

import (
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ListData — a list is either empty (nil) or one element in front of a
// list (cons). The datatype door mints the type and its constructors and
// registers the four principles a datatype comes with, each derived
// through the recursive-type universe the type is carved from
// (recspace): induction, the recursion schema, injectivity of cons and
// the distinctness of the constructors. The induction tactic reads the
// first under the library name list_induction, and the define door's
// equation compiler reads the second under list_recursion — every
// recursive definition below compiles against it.
var ListData = family.DefineData(registry.DataEntry{
	Name:   "List",
	Type:   "list",
	Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "nil"},
		{Name: "cons", Args: []string{"A", "list(A)"}},
	},
	// The four principles' registered names — the words the vars below
	// carry, so a session cites what this file spells.
	Principles: registry.DataPrinciples{
		Induction: "Induction",
		Recursion: "Recursion",
		Injective: "ConsInjective",
		Distinct:  "NilNotCons",
	},
	// The universe's rows the derivations read: its recursion theorem
	// and its countable-family constructor (the schema), its node
	// constructor's injectivity (read for cons's injectivity and for
	// nil ≠ cons), and 0 ≠ suc (the two tags differ).
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
	},
})

// The four principles under chapter names — the names the door
// registers (Principles above), so `list.NilNotCons` is one name in Go
// and in a session.
var (
	// Induction — a property holding at nil and preserved by cons holds
	// of every list: P(nil), (∀h t. P(t) ⇒ P(cons(h, t))) ⊢ P(l).
	Induction = inductionThm{ListData.Induct}
	// Recursion — a function on lists is determined by its value at nil
	// and its step at cons: ∀nil' cons'. ∃fn. fn(nil) = nil' ∧
	// ∀h t. fn(cons(h, t)) = cons'(h, t, fn(t)).
	Recursion = recursionThm{ListData.Recursion}
	// ConsInjective — cons(h, t) = cons(h', t') ⇔ h = h' ∧ t = t'.
	ConsInjective = consInjectiveThm{ListData.Inj}
	// NilNotCons — nil ≠ cons(h, t).
	NilNotCons = nilNotConsThm{ListData.Distinct}
)

// The operations: six by primitive recursion over the two
// constructors, and four more: `list_distinct` and `list_sum`, the
// notions the listing
// correspondence (sets/listing) reads a list through, and
// `list_product` and the relation `list_permutation`, the two factorization
// into primes (nat_num/nat_prime) is stated with. A
// definition that spells a sibling constant names the sibling's entry
// in Deps: the dependency is real, and Go's init order is not
// declaration order.

// ListAppendDef — concatenation: nil in front of l is l, and cons(h, t) in
// front of l is h in front of t in front of l.
var ListAppendDef = listAppendDefThm{family.Define(registry.DefEntry{
	Name:  "ListAppendDef",
	Key:   "prop_ee3b2c9de449d027",
	Const: "list_append",
	Type:  "list(A) → list(A) → list(A)",
	Equations: []string{
		"∀l:list(A). list_append(nil, l) = l",
		"∀h:A. ∀t:list(A). ∀l:list(A). list_append(cons(h, t), l) = cons(h, list_append(t, l))",
	},
})}

// ListLengthDef — the number of elements.
var ListLengthDef = listLengthDefThm{family.Define(registry.DefEntry{
	Name:  "ListLengthDef",
	Key:   "prop_49d44d76f223e33d",
	Const: "list_length",
	Type:  "list(A) → num",
	Equations: []string{
		"list_length(nil) = 0",
		"∀h:A. ∀t:list(A). list_length(cons(h, t)) = suc(list_length(t))",
	},
})}

// ListReverseDef — the elements in the opposite order: the head goes to
// the far end, behind the reversed tail.
var ListReverseDef = listReverseDefThm{family.Define(registry.DefEntry{
	Name:  "ListReverseDef",
	Key:   "prop_c19141d9a89aabbd",
	Const: "list_reverse",
	Type:  "list(A) → list(A)",
	Equations: []string{
		"list_reverse(nil) = nil",
		"∀x:A. ∀l:list(A). list_reverse(cons(x, l)) = list_append(list_reverse(l), cons(x, nil))",
	},
	Deps: []registry.EntryLike{ListAppendDef},
})}

// ListNthDef — the element at position i, counting from 0: the head at 0,
// and the tail's element at i − 1 after it. Past the end the value is one
// fixed element of A, the same for every list and position.
var ListNthDef = listNthDefThm{family.Define(registry.DefEntry{
	Name:  "ListNthDef",
	Key:   "prop_430c907e4027785",
	Const: "list_nth",
	Type:  "list(A) → num → A",
	Equations: []string{
		"∀i:num. list_nth(nil, i) = εx:A. ⊤",
		"∀h:A. ∀t:list(A). ∀i:num. list_nth(cons(h, t), i) = COND(i = 0, h, list_nth(t, i - 1))",
	},
})}

// ListMapDef — a function applied to every element, the order kept.
var ListMapDef = listMapDefThm{family.Define(registry.DefEntry{
	Name:  "ListMapDef",
	Key:   "prop_345b81dff5d7c9a0",
	Const: "list_map",
	Type:  "(A → B) → list(A) → list(B)",
	Equations: []string{
		"∀f:(A → B). list_map(f, nil) = nil",
		"∀f:(A → B). ∀h:A. ∀t:list(A). list_map(f, cons(h, t)) = cons(f(h), list_map(f, t))",
	},
})}

// ListMemberDef — membership: nothing is in nil, and x is in cons(h, t) when
// it is the head or in the tail.
var ListMemberDef = listMemberDefThm{family.Define(registry.DefEntry{
	Name:  "ListMemberDef",
	Key:   "prop_6907706f10d51ab1",
	Const: "list_member",
	Type:  "A → list(A) → bool",
	Equations: []string{
		"∀x:A. list_member(x, nil) ⇔ ⊥",
		"∀x:A. ∀h:A. ∀t:list(A). list_member(x, cons(h, t)) ⇔ x = h ∨ list_member(x, t)",
	},
})}

// ListFoldDef — the fold: f applied to each element and the fold of the
// rest, from the right, starting at b. list_fold(f, [a₁, …, aₙ], b) is
// f(a₁, f(a₂, … f(aₙ, b))).
var ListFoldDef = listFoldDefThm{family.Define(registry.DefEntry{
	Name:  "ListFoldDef",
	Key:   "prop_ed55f9bebd05e7bb",
	Const: "list_fold",
	Type:  "(A → B → B) → list(A) → B → B",
	Equations: []string{
		"∀f:(A → B → B). ∀b:B. list_fold(f, nil, b) = b",
		"∀f:(A → B → B). ∀h:A. ∀t:list(A). ∀b:B. list_fold(f, cons(h, t), b) = f(h, list_fold(f, t, b))",
	},
})}

// ListDistinctDef — no element occurs twice: the head is not in the tail,
// and the tail has no repetition. A list's set counts at most its
// length, with equality exactly for a distinct list.
var ListDistinctDef = listDistinctDefThm{family.Define(registry.DefEntry{
	Name:  "ListDistinctDef",
	Key:   "prop_86a676e42e21bc6",
	Const: "list_distinct",
	Type:  "list(A) → bool",
	Equations: []string{
		"list_distinct(nil) ⇔ ⊤",
		"∀h:A. ∀t:list(A). list_distinct(cons(h, t)) ⇔ ¬list_member(h, t) ∧ list_distinct(t)",
	},
	Deps: []registry.EntryLike{ListMemberDef},
})}

// ListSumDef — Σ over a list of naturals is the fold at addition,
// started at 0: the list-side twin of `nat_sum = iterated_op(+)`, so that Σ
// over a set and Σ over a list are two folds at one operation. Read
// through list_fold's clauses it is the recursion a reader expects,
// list_sum(nil) = 0 and list_sum(cons(h, t)) = h + list_sum(t).
var ListSumDef = listSumDefThm{family.Define(registry.DefEntry{
	Name:  "ListSumDef",
	Key:   "prop_f8136e0c216d5d28",
	Const: "list_sum",
	Type:  "list(num) → num",
	Equations: []string{
		"∀l:list(num). list_sum(l) = list_fold((+), l, 0)",
	},
	Deps: []registry.EntryLike{ListFoldDef},
})}

// ListProductDef — Π over a list of naturals is the fold at
// multiplication, started at 1: the list-side twin of
// `nat_product = iterated_op(*)`, and list_sum's twin at the other operation.
// Read through list_fold's clauses it is list_product(nil) = 1 and
// list_product(cons(h, t)) = h * list_product(t).
var ListProductDef = listProductDefThm{family.Define(registry.DefEntry{
	Name:  "ListProductDef",
	Key:   "prop_8ec74d6c520b3fc6",
	Const: "list_product",
	Type:  "list(num) → num",
	Equations: []string{
		"∀l:list(num). list_product(l) = list_fold((*), l, 1)",
	},
	Deps: []registry.EntryLike{ListFoldDef},
})}

// permutation — two lists are permutations of each other when one can
// be rearranged into the other, and the definition says so by the
// moves a rearrangement is made of: the empty list is a rearrangement
// of itself, a common head can be put in front of a list and a
// rearrangement of it,
// the first two elements can trade places, and two rearrangements in
// a row are one. The relation is the smallest closed under those four
// moves; the theorems it comes with are the faces at the top of
// permutation.go.
var listPermutation = family.DefineInductive(registry.InductiveEntry{
	Name: "ListPermutation",
	Keys: registry.InductiveKeys{
		Rules:        "prop_ad05a3a7611b0405",
		Induct:       "prop_bdca1b8b7ceac12c",
		Cases:        "prop_c6f000526ec5f130",
		InductStrong: "prop_5526202ee059edda",
	},
	Const: "list_permutation",
	Type:  "list(A) → list(A) → bool",
	Rules: []string{
		"list_permutation(nil, nil)",
		"∀x:A. ∀l m:list(A). list_permutation(l, m) ⇒ list_permutation(cons(x, l), cons(x, m))",
		"∀x y:A. ∀l:list(A). list_permutation(cons(x, cons(y, l)), cons(y, cons(x, l)))",
		"∀l m n:list(A). list_permutation(l, m) ∧ list_permutation(m, n) ⇒ list_permutation(l, n)",
	},
})
