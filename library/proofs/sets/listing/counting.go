// counting.go — the chapter's counting part: how many points a list
// lists.

package listing

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// CardSetOfListLe — a list's set holds each of its letters once while
// the list counts every occurrence, so the set counts at most as many
// points as the list has letters.
//
// By induction on the list. nil lists nothing: its set is ∅, which
// counts 0, and 0 is its length as well. A head in front adds exactly
// one letter to the length; what it adds to the count is what the
// counting clause reads off its conditional — one more point only if the
// head is not already a point of the tail's set — and nothing here
// decides that conditional, since a head may or may not occur in its own
// tail.
//
// That undecided conditional is the content of the member, and the
// reason the statement is an inequality: both readings meet the raised
// length, each by its own law, but the first slackens the bound by a
// letter where the second carries it across unchanged. Equality
// survives exactly when no head is ever old, which is the
// repetition-freeness `list_of_set`'s length clause pins.
//
// The counting clause carries a finiteness side condition, which is why
// a finiteness fact joins the rewrites at the step.
var CardSetOfListLe = cardSetOfListLeThm{family.Add(registry.ProofEntry{
	Name: "CardSetOfListLe",
	Key:  "prop_aa203eb901ddd2bd",
	Build: family.Theorem("∀l:list(A). card(set_of_list(l)) ≤ list_length(l)",
		func(a *Argument) {
			a.Induct("l")
			a.Base(
				"nil lists nothing: its set is ∅, which counts 0, and 0 is its length too",
				Simp(Fwd(SetOfListDef), Fwd(list.ListLengthDef), Fwd(cardinality.CardClauses)),
				Cite(nat_order.LessEqRefl))
			a.Step(
				"one more letter in front, and one more point only if "+
					"the head is new — which the counting clause leaves open",
				func(b *Argument) {
					b.StepArgs("h", "l")
					b.Do(Simp(
						Fwd(SetOfListDef),
						Fwd(list.ListLengthDef),
						Fwd(cardinality.CardClauses),
						Fwd(FiniteSetOfList)))
					b.Cases(b.Term("h ∈ set_of_list(l)"))
					b.When(
						"the head is an old point: the count stands, and ≤'s "+
							"successor clause lets the tail's bound serve one step higher",
						CondRewrite(),
						Simp(Fwd(nat_order.LessEqSucClause)),
						Basic())
					b.Otherwise(
						"the head is a new point: the count rises by one, and "+
							"the bound rises with it, ≤ being invariant under suc",
						CondRewrite(),
						Simp(Fwd(nat_order.SucLessEqSucIff)),
						Basic())
				})
		}),
})}

// HasSizeSetOfListIffDistinct — CardSetOfListLe's bound becomes an
// equality
// exactly for a repetition-free list: a list's set has the list's own
// length for a size precisely when the list repeats nothing. This is
// where `list_distinct` and the counting meet, and it is what makes
// `list_of_set`'s length clause an honest definition of "enumerates
// without repeating".
//
// Having a size is two demands, and the first costs nothing: every
// list's set is finite, so what is left to decide is whether the count
// reaches the length. That is settled one head at a time: the head
// clause is the whole content of the theorem, and the induction only
// carries that clause along the list.
//
// The head clause is also where CardSetOfListLe is spent. An old head
// leaves the count where it was, and a count that already falls short
// of the tail's length cannot be one more than it; a new head raises
// both numbers by one, and suc cancels.
var HasSizeSetOfListIffDistinct = hasSizeSetOfListIffDistinctThm{family.Add(registry.ProofEntry{
	Name: "HasSizeSetOfListIffDistinct",
	Key:  "prop_1701551ac9220447",
	Build: family.Sections(
		"∀l:list(A). has_size(set_of_list(l), list_length(l)) ⇔ list_distinct(l)",
		func(ctx *Script, headline string) *GoalStackNode {
			// One head laid in front, and what it does to the two numbers:
			// the length rises by one whatever the head is, while the count
			// rises only if the head is a point the tail's set does not
			// already hold. So the raised count meets the raised length
			// exactly when the head is new and the tail's own two numbers
			// already agreed.
			headIsNew := ctx.Lemma(
				"∀h:A. ∀t:list(A). "+
					"    card(set_of_list(cons(h, t))) = list_length(cons(h, t)) ⇔ "+
					"    ¬list_member(h, t) ∧ card(set_of_list(t)) = list_length(t)",
				func(a *Argument, h *Expr[A], t *Expr[list.List[A]]) {
					tailCount := a.TermAs[Nat]("card(set_of_list(t))")
					tailLength := a.TermAs[Nat]("list_length(t)")

					// The counting clause reads the head off a conditional,
					// and the correspondence reads that conditional's guard
					// as the head's occurrence in the tail. Both of its
					// readings go on the page before the split decides
					// between them.
					a.Do(
						Simp(
							Fwd(SetOfListDef),
							Fwd(list.ListLengthDef),
							Fwd(cardinality.CardClauses),
							Fwd(FiniteSetOfList),
							Fwd(InSetOfList)),
						CondRewrite())

					a.Cases(a.Term("list_member(h, t)"))
					a.When(
						"the head is an old point: the count stands where it "+
							"was, and it already fell short of the tail's length",
						func(b *Argument, occurs Fact) {
							bound := b.Have(
								"the tail's set counts at most the tail's length",
								"card(set_of_list(t)) ≤ list_length(t)",
								Cite(CardSetOfListLe))

							b.Show(
								"so the count is not one more than that length, and the right side fails on the head as well",
								By(
									occurs,
									bound,
									nat_order.SucLessEqIffLessThan.At(tailLength, tailLength),
									nat_order.LessThanIrrefl.At(tailLength)))
						})
					a.Otherwise(
						"the head is a new point: both numbers rise by one, and suc cancels from the equation",
						func(b *Argument, fresh Fact) {
							b.Show(
								"what is left is the tail's own equation, which is the whole of what the right side asks",
								By(fresh, peano.SucInjective.At(tailCount, tailLength)))
						})
				})

			// The counting half of the theorem, along the list: nil counts
			// 0 and is 0 long, and every head after it is asked to be new,
			// which is exactly what repetition-freeness asks of the list.
			counts := ctx.Lemma("∀l:list(A). card(set_of_list(l)) = list_length(l) ⇔ list_distinct(l)",
				func(a *Argument) {
					a.Induct("l")
					a.Base(
						"the empty list lists nothing: its set is ∅, which "+
							"counts 0, and 0 is its length, and nil repeats nothing",
						Simp(
							Fwd(SetOfListDef),
							Fwd(list.ListLengthDef),
							Fwd(cardinality.CardClauses),
							Fwd(list.ListDistinctDef)),
						Basic())
					a.Step(
						"a head in front asks the same of both sides — that "+
							"the head be new — and leaves the tail to the hypothesis",
						func(b *Argument, ih Fact) {
							b.Show(
								"both sides read as the head's newness beside a clause "+
									"about the tail, and the hypothesis identifies the two",
								Simp(Fwd(list.ListDistinctDef), Fwd(headIsNew)),
								ih.Rw(),
								Basic())
						})
				})

			return ctx.Theorem(headline, func(a *Argument) {
				a.Show(
					"a list's set is finite whatever the list, so having "+
						"the list's length for a size is exactly counting it",
					Simp(Fwd(cardinality.HasSizeDef), Fwd(FiniteSetOfList)),
					Cite(counts))
			})
		}),
})}
