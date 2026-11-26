// listing.go — reading a list as a set: what set_of_list IS, and what
// it does to the list operations.
//
// The elementary layer of the chapter, and it divides in two. The
// first pair is the reading itself — membership in a list becomes
// membership in its set — together with the one degenerate case, where
// the correspondence plays no part because each constructor decides
// both sides on sight. The last three are one sentence in three
// operations: concatenation becomes union, list_map becomes image, and
// reversal changes nothing, which is the chapter's statement that the
// reading forgets exactly order and repetition.
//
// Every proof here is an extensionality argument. At an arbitrary
// point both sides come down to a condition on that point, and the
// list side is read through the elementwise law the file opens with.

package listing

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// InSetOfList — the two notions of "occurs in" agree. It is the
// correspondence's first fact and the one the rest of the chapter is
// read through: once membership in a list and membership in its set are
// the same condition, any statement here may cross freely between a
// list and the set it lists.
//
// By induction on the list. The empty list holds nothing and its set is
// empty, so both sides are false. Laying the head into the tail's set
// offers that head as an alternative exactly as putting it in front of
// the tail does, so both sides peel the same head, and the hypothesis
// identifies what remains.
var InSetOfList = inSetOfListThm{family.Add(registry.ProofEntry{
	Name: "InSetOfList",
	Key:  "prop_80b07f331ddfc286",
	Build: family.Theorem("∀x:A. ∀l:list(A). x ∈ set_of_list(l) ⇔ list_member(x, l)",
		func(a *Argument, x *Expr[A], l *Expr[list.List[A]]) {
			a.Induct(l)
			a.Base(
				"the empty list holds nothing and its set is empty, so both sides are false",
				Simp(Fwd(SetOfListDef), Fwd(list.ListMemberDef), Fwd(set_basic.NotInEmpty)),
				Refl())
			a.Step(
				"a head laid into the tail's set, met by that same head put in front of the tail",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides offer the head first, and the hypothesis identifies what is left",
						Simp(Fwd(SetOfListDef), Fwd(list.ListMemberDef), Fwd(set_basic.InInsert)),
						ih.Rw(),
						Basic())
				})
		}),
})}

// SetOfListEqEmpty — a list's set is empty exactly when the list is.
//
// The correspondence plays no part here: each constructor decides both
// sides on sight, so the whole argument is that nil and cons exhaust
// the lists. The empty list's set is ∅ by the recursion's first clause
// and nil is nil, so both sides hold there. A head in front of a tail
// gives a list the datatype keeps apart from nil, and a set built by
// laying that head in, where ∅ admits nothing, so both sides fail
// there. One distinctness fact per side is the whole content: the
// datatype's constructors on the list side, the set constructors on
// the other.
var SetOfListEqEmpty = setOfListEqEmptyThm{family.Add(registry.ProofEntry{
	Name: "SetOfListEqEmpty",
	Key:  "prop_547703c788b57fd2",
	Build: family.Theorem("∀l:list(A). set_of_list(l) = ∅ ⇔ l = nil",
		func(a *Argument, l *Expr[List[A]]) {
			shape := a.Have(
				"a list is empty or a head in front of a tail",
				"l = nil ∨ (∃h:A. ∃t:list(A). l = cons(h, t))",
				Cite(list.Cases))
			a.Do(shape.SplitDisj(
				LeftHolds(
					"the empty list: its set is ∅, and it is nil",
					Given(func(b *Argument, isNil Fact) {
						b.Show(
							"reading l as nil leaves ∅ = ∅ on the left and nil = nil on the right",
							isNil.Subst(),
							Simp(Fwd(SetOfListDef)),
							Refl())
					})),
				RightHolds(
					"a head in front of a tail: its set holds that head, and it is not nil",
					Given(func(b *Argument, isCons Fact) {
						// The head and the tail are the disjunct's own
						// binders, read back under the names the proof
						// gave them: the insertion law is cited at the
						// tail's set, with the head both laid in and
						// looked for.
						_, _, decomposed := b.Unpack2(isCons)
						head := b.TermAs[A]("h")
						tailSet := b.TermAs[Set[A]]("set_of_list(t)")

						b.Show(
							"both sides fail: the set admits h where ∅ admits nothing, and cons(h, t) is not nil",
							decomposed.Rw(),
							Simp(Fwd(SetOfListDef), Fwd(list.NilNotCons)),
							By(Normalized, set_basic.InInsert.At(tailSet, head, head), set_basic.NotInEmpty.At(head)))
					})),
			))
		}),
})}

// SetOfListAppend — the first of the chapter's transport laws, and the
// model for the rest: an operation on lists, carried across the
// correspondence, becomes a construction on sets.
//
// No transport law touches the recursion that defines set_of_list.
// Membership is all a set is, so a set equality is settled at an
// arbitrary point; there InSetOfList reads either side as membership
// in a list, the set construction contributes its own membership law,
// and what is left is the list-side fact the law transports — here
// that a concatenation holds exactly what one of the two lists holds.
var SetOfListAppend = setOfListAppendThm{family.Add(registry.ProofEntry{
	Name: "SetOfListAppend",
	Key:  "prop_1389291446de823b",
	Build: family.Theorem("∀l m:list(A). "+
		"    set_of_list(list_append(l, m)) = set_of_list(l) ∪ set_of_list(m)",
		func(a *Argument) {
			a.Show(
				"at an arbitrary point the two sides come to the same "+
					"alternative — the point lies in one of the two lists",
				Simp(Fwd(set_basic.Extension), Fwd(InSetOfList), Fwd(set_basic.InUnion), Fwd(list.MemberAppend)),
				Basic())
		}),
})}

// SetOfListMap — the pattern SetOfListAppend announced holds here
// too: the recursion stays untouched. At an arbitrary point each side comes
// down to membership in a list — in the image list on the left, and in
// l on the right, once the image has been read as the values f takes on
// it — and what the two readings leave is a fact about list_map alone, which
// MemMap supplies. The induction on the list belongs to that law and is
// not repeated here.
//
// Two element types meet, which is what sets this law apart from the one
// above: the image list and the set equality live at B, l and its own
// set at A, and the correspondence is cited at each.
var SetOfListMap = setOfListMapThm{family.Add(registry.ProofEntry{
	Name: "SetOfListMap",
	Key:  "prop_c714fe27680e2333",
	Build: family.Theorem("∀f:(A → B). ∀l:list(A). "+
		"    set_of_list(list_map(f, l)) = image(f, set_of_list(l))",
		func(a *Argument) {
			a.Show(
				"at an arbitrary point the two sides come to the same condition "+
					"— the point is a value f takes on an element the list holds",
				Simp(
					Fwd(set_basic.Extension.Inst[B]()),
					Fwd(InSetOfList),
					Fwd(proof.InstSole[B](InSetOfList)),
					Fwd(list.MemberMap),
					Fwd(set_basic.InImage)),
				CnfRefute())
		}),
})}

// SetOfListReverse — reversal rearranges a list without changing what
// it contains, so it does not change the set the list lists. The two
// laws above each left a fact about their own list operation; the one
// left here is MemReverse, and the induction on the list was spent
// once, there.
//
// One element type throughout — the reversed list, the list itself
// and both their sets stand at A — which is why the correspondence is
// cited once and nothing has to be named at an instance.
var SetOfListReverse = setOfListReverseThm{family.Add(registry.ProofEntry{
	Name: "SetOfListReverse",
	Key:  "prop_fd0177b53f7b6e95",
	Build: family.Theorem("∀l:list(A). set_of_list(list_reverse(l)) = set_of_list(l)",
		func(a *Argument) {
			a.Show(
				"at an arbitrary point the two sides come to the same "+
					"condition — the point lies in l, which reversal did not change",
				Simp(Fwd(set_basic.Extension), Fwd(InSetOfList), Fwd(list.MemberReverse)),
				Basic())
		}),
})}
