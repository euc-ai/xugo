// sum.go — the chapter's Σ part: a sum over a set, read off a list
// that enumerates it.

package listing

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// SumOverListing — a sum over a finite set is the fold over any list
// that enumerates it without repetition: the two sides of the
// correspondence, a set and a list, meet at the number they carry.
//
// Repetition-freeness is the mathematics of the hypothesis and not
// decoration. A set holds each of its points once while a list counts
// every occurrence, so an element occurring twice in a list is summed
// once on the left and twice on the right; the hypothesis is exactly
// what rules that out.
//
// By induction on the list, with the summand fixed. The empty list
// lists nothing, and an empty sum and an empty fold are both 0. Over a
// list with a head, the head is a point the tail's set does not already
// hold — the lemma below spends the correspondence's founding fact on
// reading it that way — so both sides shed the head's value and the
// hypothesis, at the tail's own distinctness, identifies what is left.
var SumOverListing = sumOverListingThm{family.Add(registry.ProofEntry{
	Name: "SumOverListing",
	Key:  "prop_eb926534575dc64e",
	Build: family.Sections(
		Statement{
			Binders: "∀f:(A → num). ∀l:list(A).",
			Hypotheses: []string{
				"list_distinct(l)",
			},
			Conclusion: "sum(set_of_list(l), f) = list_sum(list_map(f, l))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// One turn of the fold, and the one place the correspondence
			// is spent: a point a list does not hold is a point its set
			// does not hold, so laying h in front genuinely enlarges the
			// set and the fold's recursion takes the branch that sheds
			// f(h). Nothing here asks the rest of the list to be
			// repetition-free — only that h is new.
			oneTurn := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → num). ∀h:A. ∀t:list(A).",
					Hypotheses: []string{
						"¬list_member(h, t)",
					},
					Conclusion: "sum(set_of_list(cons(h, t)), f) = f(h) + sum(set_of_list(t), f)",
				},
				func(a *Argument, f *Arrow[A, Nat], h *Expr[A], t *Expr[list.List[A]], fresh Fact) {
					a.Have(
						"the tail's set is finite, which is what the fold's recursion asks of it",
						"finite(set_of_list(t))",
						Cite(FiniteSetOfList))
					a.Have(
						"and h is none of its points, since it does not occur in t",
						"h ∉ set_of_list(t)",
						Simp(Fwd(InSetOfList)),
						By(fresh))
					a.Show(
						"so the fold's clause applies, and h's absence sends its conditional to the branch that sheds f(h)",
						Simp(Fwd(SetOfListDef), Fwd(nat_sum.Clauses.Inst(TypeBinder.BindA[A](), TypeBinder.BindC[A]()))),
						CondRewrite(),
						Basic())
				})

			return ctx.Theorem(headline, func(a *Argument, f *Arrow[A, Nat], l *Expr[list.List[A]]) {
				a.Induct(l)
				a.Base(
					"the empty list lists nothing: an empty sum and an empty fold are both 0",
					Simp(
						Fwd(SetOfListDef),
						Fwd(list.ListMapDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Nat]())),
						Fwd(list.ListSumClauses),
						Fwd(nat_sum.Clauses)),
					Basic())
				a.Step(
					"a head in front: distinctness asks the head to avoid the tail and "+
						"the tail to repeat nothing, the second being what the hypothesis asks",
					Simp(Fwd(list.ListDistinctDef)),
					Basic(),
					Derive(func(b *Argument) {
						tail := b.Hyp("sum(set_of_list(l), f) = list_sum(list_map(f, l))")
						b.Show(
							"the head is new to the tail, so both sides shed f of it, "+
								"and what is left beside that value is the tail's equation",
							Simp(
								Fwd(oneTurn),
								Fwd(list.ListMapDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Nat]())),
								Fwd(list.ListSumClauses)),
							tail.Rw(),
							TrivialNormalized())
					}))
			})
		}),
})}

// SumViaListOfSet — a sum over a finite set is a fold over a list, and `list_of_set(s)` is a list
// that computes it. Nothing is found here. Every finite set has a list
// enumerating it, and `list_of_set` is the ε-reading of that
// existence, so the sum is read off a term the statement itself
// spells.
//
// The middle step is where the chapter's two halves meet. Repeating
// nothing is what the fold asks of a list, and the chosen list is not
// chosen to repeat nothing: it is chosen to have s for a set and
// card(s) for a length. Those two clauses are what carry "s has its
// own count for a size" — which is all that finiteness says of s —
// over to "the chosen list's set has that list's own length for a
// size", and a list whose set has its length for a size repeats
// nothing. This is why `list_of_set`'s definition asks for the length
// at all: a list is pinned to enumerate s by its set clause alone, and
// only the length clause stops it listing a point twice.
var SumViaListOfSet = sumViaListOfSetThm{family.Add(registry.ProofEntry{
	Name: "SumViaListOfSet",
	Key:  "prop_da1adaeb8d7cb8b",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → num). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, f) = list_sum(list_map(f, list_of_set(s)))",
		},
		func(a *Argument, f *Arrow[A, Nat], s *Expr[Set[A]], finite Fact) {
			chosen := a.TermAs[list.List[A]]("list_of_set(s)")

			lists := a.Have(
				"the chosen list's set is s itself",
				"set_of_list(list_of_set(s)) = s",
				By(finite, At(ListOfSetProperties, s)))
			counts := a.Have(
				"and it carries one letter for each point s counts",
				"list_length(list_of_set(s)) = card(s)",
				By(finite, At(ListOfSetProperties, s)))

			sized := a.Have(
				"s has its own count for a size, which is all that finiteness says of it",
				"has_size(s, card(s))",
				By(finite, cardinality.FiniteHasSize.At(s)))

			repeatsNothing := a.Have(
				"carried along those two clauses, that reads as the "+
					"chosen list's set having the list's own length for a size",
				"list_distinct(list_of_set(s))",
				By(Normalized, sized, lists, counts, At(HasSizeSetOfListIffDistinct, chosen)))

			a.Show(
				"so the fold over the chosen list is the sum over that list's set, and that set is s",
				By(Normalized, repeatsNothing, lists, At(SumOverListing, f, chosen)))
		}),
})}
