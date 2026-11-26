package engine

import (
	"context"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// applyByInductionOnClone is the session's `by_induction`: Go's
// `ByInduction(At(principle, w…), extras…, Case…)` (prover/proof/
// induction.go) as a session move. The principle is an entry named by
// key; term_specialize grounds it at the PREFIX of its stated binders —
// the parameters stated before the predicate, the predicate, and the
// indices after it if the author grounds them too — in the names the
// statement binds, which is the tuple Go's `At` writes positionally. A
// table that stops before the predicate, or none, has the predicate
// read from the goal (proof.InductionMotive): at the index a by_hyps
// hypothesis fixes by stating the principle's guard, or off the binders
// of a goal that is the principle's conclusion.
// The obligations are read off the principle at that tuple
// (proof.InductionObligations), one is asserted per case, and the
// terminal `by` closes the goal from the asserted obligations, the
// extras (by_hyps, with_lemmas) and the principle in its STATED form
// grounded at the tuple. What stays open is one leaf per obligation,
// each the case the author proves next; the terminal either closes or
// the move fails with the By diagnostics and nothing is applied.
//
// The record is the shape Go's verb records — one assert per
// obligation, then the by — so `emit-section` renders it as the verb
// (library/emit, byInductionFusion), and a member written by hand on
// that shape replays the session's keys.
func (e *Engine) applyByInductionOnClone(ctx context.Context, s *Session, clone *proof.GoalStackNode, req TacticReq) error {
	goal := clone.Goal
	switch {
	case req.LemmaText != "" || req.Lemma != nil:
		return fmt.Errorf("by_induction: the principle is an entry named by key, {\"lemma\":{\"key\":\"<entry>\"}} — " +
			"its obligations are read off the entry's statement, and the entry certifies the terminal's claim; a text states neither")
	case req.LemmaKey == "":
		return fmt.Errorf("by_induction: name the induction principle: {\"lemma\":{\"key\":\"<entry>\"}}")
	case req.Arith || req.Settac:
		return fmt.Errorf("by_induction: the terminal is the plain refutation By runs — arith and settac are `by`'s closers")
	}

	principle, err := e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: req.LemmaKey}, goal)
	if err != nil {
		return fmt.Errorf("by_induction: %w", err)
	}
	// rowProp is the entry's statement before any σ, for the
	// type-instance close of the terminal's claim child (as `by`).
	rowProp := principle
	exact := false
	var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
	if len(req.TypeSpecialize) > 0 {
		specialized, goalLetters, sErr := buildSpecializedLemma(principle, req.TypeSpecialize, goal)
		if sErr != nil {
			return fmt.Errorf("by_induction: %w", sErr)
		}
		principle, fixed = specialized, goalLetters
		exact = true
	}
	var witnesses []core.Term
	stated := principle
	if len(req.TermSpecialize) > 0 {
		ws, named, adapted, typesPinned, tErr := e.byPremiseTable(s, goal, principle, req.TermSpecialize, fixed, nil)
		if tErr != nil {
			return fmt.Errorf("by_induction: %w", tErr)
		}
		if len(named) > 0 || len(ws) == 0 {
			return fmt.Errorf("by_induction: term_specialize must name a PREFIX of the principle's stated binders — the "+
				"parameters stated before the predicate, then the predicate (%s) — since the obligations are read at that "+
				"tuple in stated order, as Go's At(principle, w…) grounds it; a table that stops before the predicate "+
				"has it read from the goal", principleBinderNames(principle))
		}
		witnesses, stated = ws, adapted
		if typesPinned {
			exact = true
		}
	}
	if slot, isPrinciple := proof.PredicateSlot(stated.Conclusion()); isPrinciple && len(witnesses) <= slot {
		// The table stops before the predicate: it is read from the
		// goal, the index off a hypothesis by_hyps names.
		var facts []core.Term
		for _, h := range req.ByHyps {
			if h.HypIndex != nil && len(h.Terms) == 0 && *h.HypIndex >= 0 && *h.HypIndex < goal.NumHyps() {
				facts = append(facts, goal.Hyp(*h.HypIndex))
			}
		}
		tuple, typed, mErr := proof.InductionMotive(stated, witnesses, goal, facts, nil, req.LemmaKey)
		if mErr != nil {
			return fmt.Errorf("by_induction: %s", mErr)
		}
		witnesses, stated = tuple, typed
	}
	// A principle whose statement still carries a type letter is
	// installed in its stated form all the same: the terminal's claim
	// child is then certified by the type-instance match, as `by`'s
	// exact premises are.
	exact = true

	obligations, err := proof.InductionObligations(stated, witnesses, req.LemmaKey)
	if err != nil {
		return fmt.Errorf("by_induction: %s", err)
	}

	// The extras: resident hypotheses and named entries, resolved
	// against the goal as `by` resolves them — a resident premise is
	// recorded by statement, so it is found again in the continuation.
	extras, srcs, certs, err := e.byPremiseSpecs(s, goal, TacticReq{ByHyps: req.ByHyps, WithLemmas: req.WithLemmas})
	if err != nil {
		return fmt.Errorf("by_induction: %w", err)
	}
	srcs = append(srcs, byInstallSource{key: core.PropKey(req.LemmaKey), prop: rowProp})
	shapes, err := req.ByShape.shapes(func(text string) (core.Term, error) {
		return e.resolveTermWithFallback(text, goal, nil, s.familyScope())
	})
	if err != nil {
		return fmt.Errorf("by_induction: %w", err)
	}

	// One assert per obligation, each on the continuation of the last;
	// the claim branches are the cases left open.
	continuation := clone
	cases := make([]*proof.GoalStackNode, 0, len(obligations))
	premises := make([]proof.ByPremiseSpec, 0, len(extras)+len(obligations)+1)
	premises = append(premises, extras...)
	for i, obligation := range obligations {
		if !proof.ApplyAssert(continuation, obligation) {
			return fmt.Errorf("by_induction: obligation %d of %s is already a hypothesis of the goal, or is the goal's own "+
				"conclusion — there is nothing to prove by induction for it: %s",
				i, req.LemmaKey, extprop.PrintProp(obligation))
		}
		claim, next := assertBranches(continuation, obligation)
		cases = append(cases, claim)
		continuation = next
		premises = append(premises, proof.ByPremiseSpec{
			Install:  extprop.MakeProp(obligation.Conclusion()),
			Resident: true,
			Describe: fmt.Sprintf("obligation %d", i),
		})
	}
	premises = append(premises, proof.ByPremiseSpec{
		Install:   stated,
		Witnesses: witnesses,
		Exact:     exact,
		Describe:  req.LemmaKey,
		SourceKey: core.PropKey(req.LemmaKey),
	})

	var applyErr error
	var economy []string
	var cuts []skeleton.WhistleEvent
	func() {
		defer func() {
			if r := utils.Failure(recover()); r != nil {
				applyErr = fmt.Errorf("by_induction: the terminal By did not close the goal from the obligations and the principle — %v", r)
			}
		}()
		if !proof.ApplyByStep(continuation, s.env, ctx, proof.BySpec{
			Premises: premises,
			Shapes:   shapes,
			Report:   func(finding string) { economy = append(economy, finding) },
			Whistle:  func(fired []skeleton.WhistleEvent) { cuts = fired },
		}) {
			applyErr = fmt.Errorf("by_induction: the terminal By did not apply")
		}
	}()
	if applyErr != nil {
		return applyErr
	}

	// Certify the terminal's claim children — the principle's by its
	// entry (both channels, as `by`), a reading's by its theorem.
	s.applyAutoMatchOnRoots([]*proof.GoalStackNode{clone}, s.autoMatchCache)
	for _, src := range srcs {
		s.applyAutoMatchTypeInstanceOnRoots([]*proof.GoalStackNode{clone}, src.key, src.prop, nil, s.autoMatchCache)
	}
	s.closeOnCertificates([]*proof.GoalStackNode{clone}, certs)

	// What is left open is exactly the cases.
	isCase := map[*proof.GoalStackNode]bool{}
	for _, c := range cases {
		isCase[c] = true
	}
	var stray []string
	for _, leaf := range clone.UnsolvedLeaves() {
		if !isCase[leaf] {
			stray = append(stray, extprop.PrintProp(leaf.Goal))
		}
	}
	if len(stray) > 0 {
		return fmt.Errorf("by_induction: the terminal closed, but %d of its premise claim(s) did not certify — "+
			"the principle is certified by the entry it names; a key premise of a polymorphic principle that did not "+
			"certify installed at a type instance the entry is not read back from — pin the instance with "+
			"type_specialize, or ground the type letters through the predicate's type:\n  %s",
			len(stray), strings.Join(stray, "\n  "))
	}
	for _, finding := range economy {
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, Diagnostic{
			Type:    DiagByEconomy,
			Message: finding + "\n  In a session: the same by_induction with by_shape:{\"normalized\":true}.",
		})
	}
	if len(cuts) > 0 {
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, byWhistleDiagnostic(cuts))
	}
	return nil
}

// assertBranches tells an assert's two children apart: the claim
// branch, whose conclusion is the claim, and the continuation, which
// carries the claim as one more hypothesis.
func assertBranches(asserted *proof.GoalStackNode, claim core.Prop) (claimBranch, continuation *proof.GoalStackNode) {
	for _, child := range asserted.Children() {
		if child.Goal.NumHyps() == asserted.Goal.NumHyps() && child.Goal.Conclusion().AlphaEquals(claim.Conclusion()) {
			claimBranch = child
		} else {
			continuation = child
		}
	}
	if claimBranch == nil || continuation == nil {
		panic(fmt.Sprintf("assertBranches: an assert of %s produced %d child(ren), not a claim and a continuation",
			extprop.PrintProp(claim), len(asserted.Children())))
	}
	return claimBranch, continuation
}

// principleBinderNames spells a principle's guarded ∀-prefix for a
// refusal.
func principleBinderNames(principle core.Prop) string {
	var names []string
	for _, name := range guardedForAllBinderOrder(principle) {
		names = append(names, utils.FormatSubscript(name))
	}
	return strings.Join(names, ", ")
}
