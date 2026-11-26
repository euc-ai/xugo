package proof

// listed_suppliers.go — what a fact in hand may discharge its guards
// from.
//
// A fact in hand arrives with the facts it is handed with: the group it
// travels in (GroupPremises, a typed reading's At), the fact its law is
// read at, the evidence of its members, its own ∀-source. Its instance's
// guards are discharged from those and from nothing else, as a By
// discharges a premise's guard from the listed premises alone: a fact
// standing in the context supplies a guard only once it is named, so
// the Go value that names it is the edge the proof shows.
//
// The edge runs the other way too: a fact the author lists discharges a
// guard of the instance that no other listed fact states, or the group
// is refused naming it. A member's evidence travels with the member,
// listed whether a guard reads it or not, and is never reported.
//
// A guard that reads ⊤ at its numerals (`0 < 2`) is discharged with no
// fact listed. A fact that states it is still a fact that states a
// guard of the instance, and is not reported.

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// _ListedTerm is one fact listed with an instance, as the leaf states
// it: the handle's name for the refusal, and whether it is a member's
// evidence (carried) rather than a fact the author listed.
type _ListedTerm struct {
	term    core.Term
	name    string
	carried bool
}

// _DischargedGuard is one guard a listed fact discharged, with the goal
// and the reading it was read in.
type _DischargedGuard struct {
	goal    Prop
	ante    core.Term
	reading rungOpts
}

// _ListedSuppliers is the facts a fact in hand lists, with the facts it
// is read at besides (extra: the fact its law is read at, its own
// ∀-source), the verb and the fact for the refusals, and the guards the
// discharge met: discharged, or stalled on one the context does not
// supply.
type _ListedSuppliers struct {
	who        string
	instance   string
	listed     []_ListedTerm
	extra      []core.Term
	discharged []_DischargedGuard
	stalled    bool
}

// listedSuppliers builds the list, nils dropped.
func listedSuppliers(who, instance string, listed []_ListedTerm, extra ...core.Term) *_ListedSuppliers {
	l := &_ListedSuppliers{who: who, instance: instance}
	for _, t := range listed {
		if t.term != nil {
			l.listed = append(l.listed, t)
		}
	}
	for _, t := range extra {
		if t != nil {
			l.extra = append(l.extra, t)
		}
	}
	return l
}

// terms is every fact a guard may be discharged from, the listed ones
// where kept says so (nil keeps them all).
func (l *_ListedSuppliers) terms(kept []bool) []core.Term {
	var out []core.Term
	for i, t := range l.listed {
		if kept == nil || kept[i] {
			out = append(out, t.term)
		}
	}
	return append(out, l.extra...)
}

// check refuses a guard the context supplies that the listed facts
// alone do not, in the reading the discharge takes, and records the
// guard as discharged.
func (l *_ListedSuppliers) check(goal Prop, ante core.Term, reading rungOpts) {
	restricted := core.MakeProp(goal.Conclusion(), l.terms(nil)...)
	missing := unsuppliedPieces(restricted, ante, true, reading)
	if len(missing) == 0 {
		l.discharged = append(l.discharged, _DischargedGuard{goal: goal, ante: ante, reading: reading})
		return
	}
	// The context may state the guard whole where no listed fact states
	// a piece: that fact is the supplier of every piece.
	whole := supplierOf(reading.reader(), goal, ante)
	suppliers := make([]core.Term, len(missing))
	for i, piece := range missing {
		if suppliers[i] = supplierOf(reading.reader(), goal, piece); suppliers[i] == nil {
			suppliers[i] = whole
		}
	}
	refuseUnlistedGuard(l, ante, missing, suppliers)
}

// supplierOf is the resident hypothesis that supplies piece — as
// written up to the rung's reading, turned round where piece is an
// equation, or as a conjunct of it in that reading, so a membership in
// a set-builder supplies each clause of its condition — nil where none
// does.
func supplierOf(read rungReader, goal Prop, piece core.Term) core.Term {
	piece = read.reading(piece)
	same := read.resident(piece)
	var turned func(core.Term) bool
	if l, r, ok := ext.MatchesEQ(piece); ok {
		turned = read.resident(ext.WrapTerm(r).Eq(ext.WrapTerm(l)).Core())
	}
	holds := func(h core.Term) bool { return same(h) || (turned != nil && turned(h)) }
	var found core.Term
	goal.AnyHyp(func(h core.Term) bool {
		if holds(h) {
			found = h
		}
		return found != nil
	})
	if found != nil {
		return found
	}
	goal.AnyHyp(func(h core.Term) bool {
		if parts := conjuncts(read.reading(h)); len(parts) >= 2 && slices.ContainsFunc(parts, holds) {
			found = h
		}
		return found != nil
	})
	return found
}

// refuseUnlistedGuard refuses a fact in hand whose instance is guarded by
// a clause the context supplies through a fact the verb was not handed.
// The refusal names each missing piece, the resident fact that states it,
// and the spelling that lists it.
func refuseUnlistedGuard(listed *_ListedSuppliers, guard core.Term, missing []core.Term, suppliers []core.Term) {
	var lines []string
	for i, piece := range missing {
		from := "closed from the context"
		if suppliers[i] != nil {
			from = "stated by the resident fact " + clipRunes(ext.PrintTerm(suppliers[i]), 120)
		}
		lines = append(lines, fmt.Sprintf("\n  %s — %s", clipRunes(ext.PrintTerm(piece), 120), from))
	}
	panic(fmt.Sprintf("%s: the instance of %s is guarded by %s, which the context supplies and the fact in hand does not list:%s\n"+
		"  a guard is discharged from the facts listed with the instance, never from the context at large — name the fact "+
		"beside the instance, GroupPremises(fact, …, instance): a Have, an assumption or a branch hypothesis by its handle, "+
		"a conjunct of a Conjuncts by its index, a member by itself or with its membership (member.With(instance))",
		listed.who, listed.instance, clipRunes(ext.PrintTerm(guard), 120), strings.Join(lines, "")))
}

// stall records a guard the discharge stopped at: one the context does
// not supply stays on the instance, and what the listed facts would
// have discharged of it is not known. nil-safe, for a discharge that
// lists nothing.
func (l *_ListedSuppliers) stall() {
	if l != nil {
		l.stalled = true
	}
}

// refuseSurplus refuses the facts the author listed that no guard the
// discharge met needs: dropped one at a time from the last, a fact goes
// when the facts left still supply every discharged guard, so of two
// that state one guard the first stays. A member's evidence is kept
// whether it is needed or not. Nothing is refused after a stall, where
// the guard left on the instance is the fault.
func (l *_ListedSuppliers) refuseSurplus() {
	if l == nil || l.stalled {
		return
	}
	kept := make([]bool, len(l.listed))
	for i := range kept {
		kept[i] = true
	}
	var surplus []int
	for i := len(l.listed) - 1; i >= 0; i-- {
		if l.listed[i].carried {
			continue
		}
		kept[i] = false
		if l.suppliesDischarged(kept) {
			surplus = append(surplus, i)
		} else {
			kept[i] = true
		}
	}
	if len(surplus) == 0 {
		return
	}
	slices.Reverse(surplus)
	var lines []string
	for _, i := range surplus {
		lines = append(lines, fmt.Sprintf("\n  %s — hyp %q", clipRunes(ext.PrintTerm(l.listed[i].term), 120), l.listed[i].name))
	}
	why := "every guard of it the discharge met is stated by the other facts listed"
	if len(l.discharged) == 0 {
		why = "it carries no guard the listed facts discharge"
	}
	panic(fmt.Sprintf("%s: the instance of %s is listed with facts it does not need — %s:%s\n"+
		"  a fact listed with an instance discharges a guard of it that no other listed fact states — drop it from "+
		"the group; a member's evidence travels with the member and is never reported",
		l.who, l.instance, why, strings.Join(lines, "")))
}

// suppliesDischarged reports whether the kept facts alone supply every
// guard the discharge met that the listed facts supply, each in the
// goal and reading it was read in. The facts are read for what they
// state (rungOpts.plain): a guard that reads ⊤ at its numerals asks for
// no fact, so read with the numerals every listed fact would be one the
// instance does not need, the `0 < 1` an author stated for that guard
// among them. A piece no listed fact states — one only its numerals
// supply — asks nothing of the kept ones. Each Prop takes a slice of
// its own: MakeProp sorts and compacts the one it is handed.
func (l *_ListedSuppliers) suppliesDischarged(kept []bool) bool {
	for _, d := range l.discharged {
		stated := d.reading
		stated.plain = true
		unstated := len(unsuppliedPieces(core.MakeProp(d.goal.Conclusion(), l.terms(nil)...), d.ante, true, stated))
		if len(unsuppliedPieces(core.MakeProp(d.goal.Conclusion(), l.terms(kept)...), d.ante, true, stated)) > unstated {
			return false
		}
	}
	return true
}
