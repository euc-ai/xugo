package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A COND whose condition is one `<` or `≤` of its carrier is split on
// that comparison, each arm pinned to the branch the comparison selects
// (condSplit, intCondSplit, realCondSplit). A condition of any other
// shape — a disjunction, a conjunction, a negation, an equation, a
// statement the carrier does not read — is split here, by its atoms:
// the condition read through ¬, ∧, ∨, ⇒ and ⇔ down to the statements
// that are none of them.
//
//	a ∨ ¬a                              [excluded middle on the first atom a]
//	a  branch:  pin c = c[⊤/a]           [the condition and the COND folded]
//	¬a branch:  pin c = c[⊥/a]
//
// A pin's right side is a branch of the COND where the atom decides the
// condition, and otherwise a COND on a condition with one atom fewer,
// which the branch splits in its turn; so the splits of one COND end,
// at most one per atom of its condition down a path.

// isOrderAtom reports whether guard is one `<` or `≤` of d's carrier,
// the condition the carrier's own COND split reads.
func (d *Domain) isOrderAtom(guard Term) bool {
	if _, _, ok := d.matchLt(guard); ok {
		return true
	}
	_, _, ok := d.matchLe(guard)
	return ok
}

// guardAtom is the first atom of a COND's condition, in the order the
// condition spells them; false where the condition has none, being built
// of ⊤ and ⊥ alone.
func guardAtom(guard Term) (Term, bool) {
	if guard.AlphaEquals(prop.T) || guard.AlphaEquals(prop.F) {
		return nil, false
	}
	if inner := ext.MatchesNOT(guard); inner != nil {
		return guardAtom(inner)
	}
	for _, match := range []func(Term) (Term, Term, bool){prop.MatchesAND, prop.MatchesOR, ext.MatchesIMPLY} {
		if l, r, ok := match(guard); ok {
			if a, ok := guardAtom(l); ok {
				return a, true
			}
			return guardAtom(r)
		}
	}
	if l, r, ok := ext.MatchesEQ(guard); ok && ext.IsBool(l) {
		if a, ok := guardAtom(l); ok {
			return a, true
		}
		return guardAtom(r)
	}
	return guard, true
}

// compoundCondSplit is the split of atom, whose value def gives as a
// COND on guard (`def : ⊢ atom = COND(guard, x, y)`), on the first atom
// of guard. The ¬a arm holds `¬a` and, where a is a comparison the
// carrier's negComparison reads, the comparison ¬a is; ok=false where
// the condition has no atom.
func compoundCondSplit(
	atom Term, def *prop.PropWrapper, guard Term,
	negComparison func(Term) (Term, *prop.PropWrapper, bool),
) (splittableAtom, bool) {
	a, ok := guardAtom(guard)
	if !ok {
		return splittableAtom{}, false
	}
	no := not(a)
	pinT := pinUnder(def, eqtIntro(prop.Assume(a)))  // {a} ⊢ atom = …
	pinF := pinUnder(def, eqfIntro(prop.Assume(no))) // {¬a} ⊢ atom = …
	if pinT == nil || pinF == nil {
		panic("compoundCondSplit: an atom of the condition did not fold in the COND it was read from (engine invariant): " +
			ext.PrintTerm(prop.Rhs(def)))
	}
	denied := []*prop.PropWrapper{prop.Assume(no)}
	if _, bridge, ok := negComparison(a); ok {
		denied = append(denied, bridge) // {¬a} ⊢ the comparison ¬a is
	}
	return splittableAtom{
		atom:      atom,
		disjProof: prop.ExcludedMiddle(a), // a ∨ ¬a
		branches: [2]splitBranch{
			{guard: a, facts: []*prop.PropWrapper{prop.Assume(a), pinT}},
			{guard: no, facts: append(denied, pinF)},
		},
	}, true
}

// pinUnder collapses the right side of def at one statement's truth
// value: truth is `Γ ⊢ s ⇔ ⊤` or `Γ ⊢ s ⇔ ⊥`, every occurrence of s on
// the right side is rewritten to that value, and the connectives and
// the COND fold over it. The result is `Γ ⊢ (def's left side) = (the
// folded right side)`; nil where s does not occur. No decider runs: the
// fold is syntactic.
func pinUnder(def, truth *prop.PropWrapper) *prop.PropWrapper {
	s := prop.Lhs(truth)
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(truth.Hyps(), pred) }
	fold := prop.BasicRewritesWithEnv(anyHyp, func(t Term) *prop.PropWrapper {
		if t.AlphaEquals(s) {
			return truth
		}
		return nil
	})(prop.Rhs(def))
	if fold == nil {
		return nil
	}
	return def.EqTrans(fold)
}
