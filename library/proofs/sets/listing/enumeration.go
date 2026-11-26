// enumeration.go — every finite set is the set of some list.

package listing

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// Enumerates — the hard half of the correspondence, and the one the
// chapter does not get for free. The easy half only reads a set off a
// list; this one produces a list out of nothing but finiteness, and
// the list it produces lists each element once, the length clause
// being what rules repetition out. `list_of_set` is the ε-reading of
// exactly this existence, so everything the chapter goes on to say
// about that constant rests here.
//
// Induction over finite sets, on the property "some list enumerates
// this set with its count as length". ∅ is listed by nil. A set
// enlarged by one element is listed by that element put in front of a
// list of the rest: the set gains exactly the new element and the list
// gains exactly one letter, so the two clauses advance together.
//
// The induction has to be the one granting FRESHNESS, and the count is
// why. What an enlargement does to a count depends on whether the
// element was already there — one more only if it was not — and
// ordinary finite induction leaves that undecided at its step, where
// the length has already gone up by one regardless. The sharpened
// principle settles it by granting that the element is new, and that
// the set enlarged is already finite, which is the other thing a count
// needs.
var Enumerates = enumeratesThm{family.Add(registry.ProofEntry{
	Name: "Enumerates",
	Key:  "prop_efcd91a28bd40971",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "∃l:list(A). set_of_list(l) = s ∧ list_length(l) = card(s)",
		},
		func(a *Argument, s *Expr[Set[A]], finite Fact) {
			v := ops(a.Ctx())

			a.Show(
				"so every finite set has such a list, and s is one of them",
				ByInduction(finite_set.FiniteInductFresh, finite,

					Case(
						"∅ is listed by nil: nothing is in it, and its length is 0, which is ∅'s count too",
						Witness(v.Nil),
						Simp(Fwd(SetOfListDef), Fwd(list.ListLengthDef), Fwd(cardinality.CardClauses)),
						Basic()),

					Case(
						"insert(x, t) for an x outside t is listed by x put in front of a list of t",
						Derive(func(b *Argument) {
							// The set the induction step lays a point into, and the point
							// itself. The first is the principle's own binder, so it
							// is taken unnamed; the second is named because the
							// section's claims below spell it.
							x, t := b.Fix(), b.Fix("t")
							carried := b.Assume() // t has such a list, x lies outside t, t is finite

							m, lists := b.Obtain(
								"t is the set of some m, as long as t's count",
								"∃m:list(A). set_of_list(m) = t ∧ list_length(m) = card(t)",
								By(carried))

							counted := b.Have(
								"x being new to t is what settles the enlarged count on the successor side",
								"card(insert(x, t)) = suc(card(t))",
								// The exact law asks its set to be finite and its
								// point to be new; `carried` answers both. It binds
								// the set before the point, so the witnesses read (t, x).
								By(carried, At(cardinality.InsertCountsOneMore, t, x)))

							b.Take(v.Cons.Apply(x, m))
							b.Show(
								"x in front of m lists insert(x, t), and is one longer than m, which is one more than t's count",
								Simp(Fwd(SetOfListDef), Fwd(list.ListLengthDef)),
								// Normalized: once the rewrites have run, each clause
								// has the same set, and the same number, on both
								// sides — simplification alone settles them.
								By(Normalized, lists, counted))
						})),
				))
		}),
})}

// ListOfSetProperties — the chosen list is one of the lists Enumerates
// provides. Nothing mathematical is added here: Enumerates is the
// whole content, and this member only reads it at the name.
//
// That naming is what every consumer wants. A theorem about "some list
// enumerating s" has to open the existential before it can say
// anything, and each consumer that does so opens it at a different
// letter; `list_of_set(s)` is one term every one of them can spell, and
// this is where it acquires the two clauses that make it worth
// spelling.
//
// The step from the one to the other is the choice: `list_of_set` is by
// definition a choice among the lists meeting the specification, so
// unfolding the definition leaves the ε-term facing that specification,
// which the existence discharges.
var ListOfSetProperties = listOfSetPropertiesThm{family.Add(registry.ProofEntry{
	Name: "ListOfSetProperties",
	Key:  "prop_bda8b064057c0527",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "set_of_list(list_of_set(s)) = s ∧ list_length(list_of_set(s)) = card(s)",
		},
		func(a *Argument, s *Expr[Set[A]], finite Fact) {
			// The existence is not cited below by name. Unfolding a
			// choice leaves TWO obligations — that something meets the
			// specification, and the conclusion granted that the chosen
			// term does — and this Have is what stands against the
			// first, which is why it is stated before the unfolding
			// rather than beside it.
			a.Have(
				"some list does list s with its count as length — "+
					"that is Enumerates, and finiteness is its whole input",
				"∃l:list(A). set_of_list(l) = s ∧ list_length(l) = card(s)",
				By(finite, At(Enumerates, s)))

			a.Show(
				"and list_of_set(s) is chosen among those lists, so it is one of them",
				Unfold(ListOfSetDef))
		}),
})}
