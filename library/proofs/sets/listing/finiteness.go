// finiteness.go — the set of a list's elements is finite.

package listing

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteSetOfList — by induction on the list, one clause of the
// definition per case. The empty list's set is ∅, which finite's base
// rule makes finite outright; a head laid into the tail's set is an
// insertion, and an insertion leaves finiteness alone, so the case is
// left with exactly its hypothesis.
//
// This is the easy half of the chapter's correspondence, and it is what
// shapes the hard one: since no list enumerates an infinite set,
// `list_of_set` is an enumeration only where the set is finite, which is
// why the chapter sits inside finite_set.
var FiniteSetOfList = finiteSetOfListThm{family.Add(registry.ProofEntry{
	Name: "FiniteSetOfList",
	Key:  "prop_d064aa2cd6d3c24d",
	Build: family.Theorem("∀l:list(A). finite(set_of_list(l))",
		func(a *Argument) {
			a.Induct("l")
			a.Base(
				"at nil: the empty list's set is ∅, and finite's base rule makes ∅ finite",
				Simp(Fwd(SetOfListDef), Fwd(finite_set.FiniteRules)),
				TrivialNormalized())
			a.Step(
				"at cons(h, t): the head is laid into the tail's set, and an insertion leaves finiteness alone",
				func(b *Argument, tailFinite Fact) {
					b.Show(
						"what is left is the tail's own set, finite by the hypothesis",
						Simp(Fwd(SetOfListDef), Fwd(finite_set.FiniteInsert)),
						By(tailFinite))
				})
		}),
})}

// FiniteIffListable — the chapter's sentence, and the statement a
// reader should meet first: a set is finite exactly when some list
// enumerates it. It carries no argument of its own, the two directions
// being the chapter's two halves read once each. Enumerates makes a
// list out of finiteness alone, and makes it count the set as well,
// which is more than an equivalence between finiteness and listability
// asks — so the count clause is dropped here. FiniteSetOfList is the
// way back: the hypothesis hands over a list, and its set is finite
// whatever the list.
var FiniteIffListable = finiteIffListableThm{family.Add(registry.ProofEntry{
	Name: "FiniteIffListable",
	Key:  "prop_9e45622728a9fcfe",
	Build: family.Theorem("∀s:set(A). finite(s) ⇔ ∃l:list(A). set_of_list(l) = s",
		func(a *Argument, s *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"a finite set has an enumerating list, and that list is the witness",
				func(b *Argument, finite Fact) {
					l, enumerates := b.Obtain(
						"some list has s for its set, and counts it besides",
						"∃l:list(A). set_of_list(l) = s ∧ list_length(l) = card(s)",
						By(finite, At(Enumerates, s)))

					b.Take(l)
					b.Show(
						"its set is s, which is the whole of what is asked here",
						By(enumerates))
				})
			a.Backward(
				"the existence supplies a list, and finiteness is read off it",
				func(b *Argument, listed Fact) {
					_, lists := b.Unpack(listed)

					b.Show(
						"s is that list's set, and every list's set is finite",
						lists.RwRev(),
						Cite(FiniteSetOfList))
				})
		}),
})}
