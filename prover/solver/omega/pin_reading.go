package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A split branch read at its pins.
//
// An operator's split gives each branch a pin, `real_min(d, &1) = d` under
// the guard `d ≤ &1`, and the linear prover uses it as an equation between
// two unknowns. That reaches the operator where it stands alone in a linear
// form and nowhere else: beside `real_min(d, &1) * w` the pin says nothing,
// the monomial being one unknown and `d * w` another. It is the gap the
// variable-sided rule closes for a hypothesis `v = e` (variable_subst.go),
// met here by an equation whose defined side is an operator term and which
// only the branch holds.
//
// So a branch whose pinned operator stands inside an unknown of the linear
// reader is read at its pins: the goal and the hypotheses the provers read,
// each operator replaced by its arm. A pin's own equation, which then reads
// `arm = arm`, is left out, and its guard stays. What is proved of the
// reading is carried back to the branch as spelled, the pins among its
// hypotheses; the split cuts them back to their guards as it does every
// fact of a branch.
//
// The rewrite takes a pinned operator before it enters the operator's
// arguments, and goes on into the arm it produced. A pin is stated over the
// spelling the split met, so an operator that holds another (`real_min(|x|,
// &1)`) or is pinned to another (`real_sgn(x)` to its inner COND) is met as
// its pin spells it. An arm holds fewer of the split's operators than the
// operator it replaces — it is one of the operator's arguments or its
// negation, a literal, for a sign the inner COND, whose own arms are
// literals, or for a COND split by its condition's atoms the COND on the
// condition with one atom fewer (cond_split.go) — so the rewrite ends.

// pinOf finds the pin of atom among added, the facts one arm of atom's
// split put into its branch: the equation `atom = arm`. ok=false for a
// split that pins nothing of that form — a hypothesis split, whose atom is
// the hypothesis, and ℕ's subtraction where it is not zero.
func pinOf(atom Term, added []Term) (Term, bool) {
	for _, fact := range added {
		l, r, ok := ext.MatchesEQ(fact)
		if ok && l.AlphaEquals(atom) && !holdsTerm(r, atom) {
			return fact, true
		}
	}
	return nil, false
}

// holdsTerm reports whether a occurs in t, t itself counted, by the raw
// walk of collectRawSubterms: an abstraction's body is entered.
func holdsTerm(t, a Term) bool {
	if t.AlphaEquals(a) {
		return true
	}
	if app, ok := t.AsAppliedTerm(); ok {
		return holdsTerm(app.Fun(), a) || holdsTerm(app.Arg(), a)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return holdsTerm(abs.Body(), a)
	}
	return false
}

// pinnedAtom is the operator term pin defines.
func pinnedAtom(pin Term) Term {
	atom, _, ok := ext.MatchesEQ(pin)
	if !ok {
		panic("omega: a pin is an equation")
	}
	return atom
}

// pinStandsInAnUnknown reports whether an operator pins define stands
// inside a term d's linear reader takes as an unknown, in the goal or in a
// hypothesis the provers read: a factor of a monomial, the argument of an
// opaque atom, a divisor. A pinned operator that is itself the unknown is
// where its pin reaches; one inside another pinned operator is that
// operator's pin's to place, and the arm it is pinned to is read on its own
// as a side of the pin.
func (d *Domain) pinStandsInAnUnknown(hyps []Term, goal Term, pins []Term) bool {
	if len(pins) == 0 {
		return false
	}
	atoms := make([]Term, len(pins))
	for i, pin := range pins {
		atoms[i] = pinnedAtom(pin)
	}
	pinned := func(t Term) bool { return slices.ContainsFunc(atoms, t.AlphaEquals) }
	holdsPinned := func(t Term) bool {
		return slices.ContainsFunc(atoms, func(a Term) bool { return holdsTerm(t, a) })
	}
	inUnknown := false
	// sum walks the linear contexts linOf does not read (a difference and
	// a negation are the signed normalizer's) down to the forms it does.
	var sum func(t Term)
	sum = func(t Term) {
		if inUnknown || pinned(t) {
			return
		}
		if d.matchNeg != nil {
			if x, ok := d.matchNeg(t); ok {
				sum(x)
				return
			}
		}
		if d.matchSub != nil {
			if l, r, ok := d.matchSub(t); ok {
				sum(l)
				sum(r)
				return
			}
		}
		if l, r, ok := d.matchPlus(t); ok {
			sum(l)
			sum(r)
			return
		}
		form, ok := d.linOf(t)
		if !ok {
			inUnknown = holdsPinned(t)
			return
		}
		for _, m := range form.monos {
			if !pinned(m.atom) && holdsPinned(m.atom) {
				inUnknown = true
				return
			}
		}
	}
	// carrierTerms hands sum the outermost carrier terms of a formula.
	var carrierTerms func(t Term)
	carrierTerms = func(t Term) {
		if inUnknown {
			return
		}
		if d.isElem(t) {
			sum(t)
			return
		}
		if app, ok := t.AsAppliedTerm(); ok {
			carrierTerms(app.Fun())
			carrierTerms(app.Arg())
		}
	}
	carrierTerms(goal)
	for _, h := range hyps {
		if readByTheProvers(h) {
			carrierTerms(h)
		}
	}
	return inUnknown
}

// readByTheProvers reports whether a split branch's provers may read h: an
// atom, its negation, or a conjunction of such. A quantified hypothesis is
// read by none of them, and a disjunction or an implication is the split's
// own, its disjunct a fact of the branch.
func readByTheProvers(h Term) bool {
	if inner := ext.MatchesNOT(h); inner != nil {
		return readByTheProvers(inner)
	}
	if l, r, ok := prop.MatchesAND(h); ok {
		return readByTheProvers(l) || readByTheProvers(r)
	}
	if _, _, ok := prop.MatchesOR(h); ok {
		return false
	}
	if _, _, ok := prop.MatchesIMPLY(h); ok {
		return false
	}
	if abs := ext.MatchesFORALL(h); !abs.IsZero() {
		return false
	}
	if abs := ext.MatchesEXISTS(h); !abs.IsZero() {
		return false
	}
	return true
}

// pinReading is a split branch read at its pins and at the rules its
// pairs of comparisons make.
type pinReading struct {
	// hyps is the branch's hypotheses as read, the pins' own equations
	// and the rules' own comparisons left out; bridges holds
	// `{h, pins, pairs} ⊢ h′` for each hypothesis h the reading changed
	// to h′.
	hyps    []Term
	bridges []*prop.PropWrapper
	// goal is the goal as read, and target its
	// `{pins, pairs} ⊢ goal = goal′`, nil where the goal names no pinned
	// operator and no defined variable.
	goal   Term
	target *prop.PropWrapper
}

// readBranch reads the branch `hyps ⊢ goal` at pins, which are among hyps,
// and at rules, each read off a pair of hyps (caseSplit.pairedRules). A
// variable a rule defines is read as its definition wherever the reading
// meets it, the arm a pin produced included.
func readBranch(hyps []Term, goal Term, pins []Term, rules []varSubst) *pinReading {
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	atRules := varSubstLeaf(rules)
	read := prop.DeepRewriteWithEnv(anyHyp, func(t Term) *prop.PropWrapper {
		for _, pin := range pins {
			if t.AlphaEquals(pinnedAtom(pin)) {
				return prop.Assume(pin) // {atom = arm} ⊢ atom = arm
			}
		}
		return atRules(t)
	})
	defines := make([]bool, len(hyps))
	for _, rule := range rules {
		for _, at := range rule.at {
			defines[at] = true
		}
	}
	r := &pinReading{goal: goal}
	if w := read(goal); w != nil {
		r.goal, r.target = prop.Rhs(w), w
	}
	for j, h := range hyps {
		if defines[j] || slices.ContainsFunc(pins, h.AlphaEquals) {
			continue
		}
		if readByTheProvers(h) {
			if w := read(h); w != nil {
				r.hyps = append(r.hyps, prop.Rhs(w))
				r.bridges = append(r.bridges, w.EqMP(prop.Assume(h))) // {h, pins} ⊢ h′
				continue
			}
		}
		r.hyps = append(r.hyps, h)
	}
	return r
}

// carryBack turns `{r.hyps} ⊢ r.goal` into the branch's `{hyps} ⊢ goal`.
func (r *pinReading) carryBack(w *prop.PropWrapper) *prop.PropWrapper {
	w = bridgeBackHyps(w, r.bridges)
	if r.target != nil {
		w = r.target.EqSym().EqMP(w)
	}
	return w
}
