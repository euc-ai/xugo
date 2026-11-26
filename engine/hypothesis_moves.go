// hypothesis_moves.go — the session twins of three Go spellings: `lemma
// {key, read_at}` for `Cite(Law.Read(h))`, `split_conj {hyp_index}` for
// `a.Conjuncts(fact, …)`, `def_expand {const, hyp_index}` for
// `a.Unfolded(fact, <c's definition>)`. Each records the ministeps its Go spelling
// records (prover/proof), so the emitted member replays the session's
// steps through the same executors, and emit-section renders the record
// back as that spelling (library/emit, emit_hypothesis_verbs.go).

package engine

import (
	"context"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
)

// applyLemmaReadingOnClone is the `lemma` tactic with `read_at`: the
// law `tactic.LemmaKey` read at the instance (reading.go), cited as the
// Go `Cite(Law.Read(instance))` cites it. A letter the instance leaves
// loose — a polymorphic instance entry's — is pinned off the goal when
// the cite is bare (proof.ReadingAtGoalTypes) and off the tuple when it
// is witnessed (proof.ReadingAtWitnessTypes); a hypothesis's letters
// stay rigid. A goal the reading proves — the certificate stronger
// than it, or the goal its statement modulo Normalize — closes on it,
// recording the KnownThm that carries the reading. Any other goal has
// the reading brought to bear by the preserving lemma chain, as the Go
// verb brings it: an equational reading whose left side occurs in the
// goal rewrites it; otherwise the reading is installed as a resident
// hypothesis, exactly as derived, its claim child closed from the
// derived theorem, and a term_specialize PREFIX then grounds the
// installed hypothesis at the tuple, the ∀-source dropped (Go:
// `Cite(Law.Read(h), w…)`). A tuple on an install that closed the goal
// is accepted when it names the instance closed with, and on one that
// rewrote the goal is refused naming the roads. Text, type_specialize
// and a sparse table are refused by name: the law is an entry, the
// reading's types are the instance's or pinned off the goal or the
// tuple, and a binder pinned by name is a `by` premise's Where.
func (e *Engine) applyLemmaReadingOnClone(s *Session, clone *proof.GoalStackNode, tactic TacticReq) error {
	goal := clone.Goal
	if tactic.LemmaText != "" || tactic.Lemma != nil {
		return fmt.Errorf("lemma: read_at reads a law at an instance — name the law by its key, or a proved section of this session by its id, not by text")
	}
	if len(tactic.TypeSpecialize) > 0 {
		return fmt.Errorf("lemma: read_at with type_specialize: the reading's type letters are the instance's, " +
			"fixed by its components or pinned off the goal or the tuple — drop type_specialize")
	}
	reading, err := e.resolveReading(s, goal, tactic.LemmaKey, tactic.ReadAt)
	if err != nil {
		return fmt.Errorf("lemma: %w", err)
	}
	witnesses, named, _, _, err := e.byPremiseTable(
		s, goal, reading.statement(), tactic.TermSpecialize, proof.ReadingFixedLetters(reading.theorem), reading.renamedBinders())
	if err != nil {
		return fmt.Errorf("lemma: %s: %w", reading.describe, err)
	}
	if len(named) > 0 {
		return fmt.Errorf("lemma: %s: term_specialize names a binder its stated prefix does not reach — "+
			"a binder pinned by name is a `by` premise's Where; `lemma` grounds the reading positionally, "+
			"as the Go `Cite(Law.Read(h), w…)` does", reading.describe)
	}

	// Bare, the reading is typed off the goal; a goal that IS the
	// reading then closes on the cite, as Go's Cite does at its two
	// closing tiers. A tuple is grounding intent and never closes.
	install := reading.theorem
	if len(witnesses) == 0 {
		install = proof.ReadingAtGoalTypes(reading.theorem, goal)
		if proof.ApplyCiteReading(clone, install, reading.record) {
			return nil
		}
	}
	if len(witnesses) > 0 {
		typed, retyped, err := proof.ReadingAtWitnessTypes(reading.theorem, witnesses)
		if err != nil {
			return fmt.Errorf("lemma: %s: %w", reading.describe, err)
		}
		install, witnesses = typed, retyped
	}
	// The install is exact: the reading is an explicit instance, its
	// letters the instance's (the `lemma` dispatch's explicit-σ fork).
	if !proof.ApplyLemmaPreserveExactWithSource(clone, install, "") {
		return fmt.Errorf("lemma: %s neither closes the goal nor installs (already resident?)\n  goal: %s\n  reading: %s",
			reading.describe, extprop.PrintProp(goal), extprop.PrintProp(install))
	}
	// The claim child closes from the derived theorem; what is left is
	// the residual the reading is resident in.
	var open []*proof.GoalStackNode
	for child := range clone.ChildrenIter() {
		if child.Proved() || proof.ApplyCiteReading(child, install, reading.record) {
			continue
		}
		open = append(open, child)
	}
	switch len(open) {
	case 0:
		// The install's chain closed the goal (its conclusion match): a
		// bare cite accepts that, as Go's Cite does, and a witnessed one
		// only when the tuple names the instance the install closed with
		// (Lean's `exact foo a b`; prover/proof, WitnessesNameClosedGoal).
		if len(witnesses) == 0 || proof.WitnessesNameClosedGoal(reading.statement(), witnesses, goal.Conclusion()) {
			return nil
		}
		return fmt.Errorf("lemma: %s closed the goal outright through the install, at an instance the tuple does not name — "+
			"cite it bare", reading.describe)
	case 1:
	default:
		return fmt.Errorf("lemma: %s: the install left two open leaves and certified neither:\n  %s\n  %s",
			reading.describe, extprop.PrintProp(open[0].Goal), extprop.PrintProp(open[1].Goal))
	}
	residual := open[0]
	if len(witnesses) == 0 {
		return nil
	}
	idx, err := installedReadingIndex(goal, residual.Goal, install)
	if err != nil {
		return fmt.Errorf("lemma: %s: %w", reading.describe, err)
	}
	if !proof.ApplySpecialize(residual, []proof.SpecializeHyp{{HypIndex: idx, Witnesses: witnesses}}, false) {
		printed := make([]string, len(witnesses))
		for i, w := range witnesses {
			printed[i] = ext.PrintTerm(w)
		}
		return fmt.Errorf("lemma: %s: the tuple (%s) does not ground the reading's leading binders\n  reading: %s",
			reading.describe, strings.Join(printed, ", "), extprop.PrintProp(install))
	}
	return nil
}

// installedReadingIndex is the index, in the residual goal, of the
// hypothesis an exact install of `install` added: the one α-equal to
// its conclusion. None is there when the chain consumed the reading
// instead — rewrote the goal's conclusion by it, or applied it to the
// conclusion — and the refusal names that and the roads; a residual
// whose conclusion is the goal's holds the reading in another form.
func installedReadingIndex(goal, residual, install core.Prop) (int, error) {
	concl := install.Conclusion()
	for i := range residual.NumHyps() {
		if residual.Hyp(i).AlphaEquals(concl) {
			return i, nil
		}
	}
	if residual.Conclusion().AlphaEquals(goal.Conclusion()) {
		return 0, fmt.Errorf("the install left the reading resident in another form than stated, which the tuple does not ground — "+
			"ground that hypothesis with `instantiate`\n  residual: %s", extprop.PrintProp(residual))
	}
	return 0, fmt.Errorf("the install rewrote the goal by the reading, or applied it to the conclusion, so no hypothesis states it "+
		"and the tuple grounds nothing\n  residual: %s\n  cite it bare to take that; bring the instance to bear as a `by` premise "+
		"at the tuple, with_lemmas:[{key, read_at, term_specialize}], or by `lean_rw`; an `assert` of the instance closed by "+
		"that premise leaves it resident", extprop.PrintProp(residual))
}

// applyConjunctsOnClone is `split_conj {hyp_index}`: the conjunctive
// hypothesis at idx split into one hypothesis per flat conjunct, in the
// conjunction's order, a membership in a set-builder of a conjunction
// split through its predicate (proof.FactConjuncts) — the Go
// `a.Conjuncts(fact, …)`, recorded as the
// verb records it (prover/proof/derive.go): one assert per conjunct,
// each on the continuation of the last, its claim closed by `By(Normalized,
// fact)` with the conjunction its one resident premise. The conjunction
// stays resident beside its parts, as it does in Go. Refused: a
// conjunct that is the conclusion, in the verb's words; one already
// resident, and one that repeats an earlier conjunct, which the verb
// binds to the hypothesis stating it and this record, one assert per
// conjunct, has no step for.
func (e *Engine) applyConjunctsOnClone(ctx context.Context, s *Session, clone *proof.GoalStackNode, idx int) error {
	goal := clone.Goal
	if err := conjunctsSplittable(goal, idx); err != nil {
		return err
	}
	conjunction := goal.Hyp(idx)
	premise := proof.ByPremiseSpec{
		Install:  core.MakeProp(conjunction),
		Resident: true,
		Describe: fmt.Sprintf("hyp %d", idx),
	}
	continuation := clone
	for i, part := range proof.FactConjuncts(conjunction) {
		claim := core.MakeProp(part)
		if !proof.ApplyAssert(continuation, claim) {
			return fmt.Errorf("split_conj hyp_index %d: conjunct %d (%s) repeats an earlier conjunct — "+
				"state the distinct conjuncts with `assert` (Go: Have)", idx, i+1, ext.PrintTerm(part))
		}
		claimBranch, next := assertBranches(continuation, claim)
		if !proof.ApplyByStep(claimBranch, s.env, ctx, proof.BySpec{
			Premises: []proof.ByPremiseSpec{premise},
			Shapes:   []proof.ByShape{proof.Normalized},
		}) || !claimBranch.Proved() {
			panic(fmt.Sprintf("split_conj: the conjunction %s did not close its own conjunct %s by normalization",
				ext.PrintTerm(conjunction), ext.PrintTerm(part)))
		}
		continuation = next
	}
	return nil
}

// hypothesisOpens reports whether a structural move that opens the
// shape match tests opens hyp: as written, or — where hyp is a
// membership in a set-builder — through its predicate's reading, the
// reading the index-targeted moves and the Go verbs read it through
// (tactic.ReadAsShape).
func hypothesisOpens(hyp core.Term, match func(core.Term) bool) bool {
	return tactic.ReadAsShape(hyp, match) != nil
}

// setEquationRule says how an equation between sets is opened: the
// sentence the refusal of a set-builder at its point and funext's own
// answer (DiagSetEquation) share.
const setEquationRule = "funext is function extensionality; an equation between sets is opened by " +
	"`simp_with` with `set_basic.Extension` in place of `funext`, which leaves `∀x. x ∈ S ⇔ x ∈ T`, " +
	"the memberships every move and every law of sets reads."

// membershipReadingNote is a refusal's ", nor is its reading R" for a
// hypothesis that is a membership in a set-builder, and for a
// set-builder applied to its point the form's name, the rewrite that
// opens an equation between sets in funext's place, and the move that
// takes the content where the funext stays; "" for any other.
func membershipReadingNote(hyp core.Term) string {
	read, ok := tactic.MembershipAtomReading(hyp)
	if !ok {
		if tactic.SetBuilderAtPoint(hyp) {
			return "; it is a set-builder applied to its point, the form funext leaves of an equation between sets, " +
				"which no move reads as the membership it unfolds. " + setEquationRule +
				" Here, assert what the membership says and close it by `by {settac:true}` over this hypothesis"
		}
		return ""
	}
	return ", nor is its reading " + ext.PrintTerm(read)
}

// conjunctsSplittable refuses a `split_conj {hyp_index}` with a
// conjunct that is the goal's conclusion — the Go `a.Conjuncts` refuses
// it in these words: the author wanted the whole fact, not its part —
// or one already resident, which the Go verb binds to that hypothesis
// and the move's record, one assert per conjunct, has no step for.
func conjunctsSplittable(goal core.Prop, idx int) error {
	for i, part := range proof.FactConjuncts(goal.Hyp(idx)) {
		switch {
		case goal.Conclusion().AlphaEquals(part):
			return fmt.Errorf("split_conj hyp_index %d: conjunct %d (%s) is the goal's conclusion — close with "+
				"`by {by_hyps:[{hyp_index:%d}]}` instead of splitting (Go: By(f))", idx, i+1, ext.PrintTerm(part), idx)
		case goal.AnyHyp(part.AlphaEquals):
			return fmt.Errorf("split_conj hyp_index %d: conjunct %d (%s) is already resident — use the hypothesis in hand, "+
				"and state the rest with `assert` (Go: Have)", idx, i+1, ext.PrintTerm(part))
		}
	}
	return nil
}

// applyUnfoldedHypOnClone is `def_expand {const, hyp_index}`: the
// constant c opened in the hypothesis at idx alone, the unfolded
// statement joining the hypotheses beside the folded one, the goal and
// every other hypothesis untouched — the Go `a.Unfolded(fact, <c's definition>)`,
// recorded as the verb records it (prover/proof/derive.go): an assert
// of the unfolded statement whose claim child the step Unfold(c)
// records closes. The statement is computed by the def-expand walker on
// the hypothesis (proof.UnfoldedHypothesis), so no text restates what
// the engine holds.
func (e *Engine) applyUnfoldedHypOnClone(clone *proof.GoalStackNode, c core.ConstTerm, idx int) error {
	unfolded, err := clone.UnfoldedHypothesis(idx, c)
	if err != nil {
		return fmt.Errorf("def_expand hyp_index %d: %w", idx, err)
	}
	claim := core.MakeProp(unfolded)
	if !proof.ApplyAssert(clone, claim) {
		return fmt.Errorf("def_expand hyp_index %d: the unfolded statement is already resident, or is the goal's conclusion — "+
			"nothing to open:\n  %s", idx, ext.PrintTerm(unfolded))
	}
	claimBranch, _ := assertBranches(clone, claim)
	if !proof.ApplyUnfold(claimBranch, c) || !claimBranch.Proved() {
		var open []string
		for _, leaf := range claimBranch.UnsolvedLeaves() {
			open = append(open, extprop.PrintProp(leaf.Goal))
		}
		return fmt.Errorf("def_expand hyp_index %d: opening %s in the claim obligation did not close it:\n  %s",
			idx, c.Name(), strings.Join(open, "\n  "))
	}
	return nil
}
