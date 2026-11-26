// branch.go — the statement form of a structural split: the opener and
// its branches are separate sentences, and each branch is claimed BY
// NAME.
//
// A split is two moves on paper, not one. "We argue by cases on t"
// opens the fan-out; "when t holds: …" and "otherwise: …" each take one
// branch and prove it. The expression form made the whole thing a
// single nested expression:
//
//	a.Cases(t,
//	    Case("t holds: …",
//	        Given(func(b *Argument, h Fact) {
//	            …
//	        })),
//	    Case("t fails: …", …),
//	)
//
// which cost THREE indents per level of case analysis — the Case value,
// the Given closure, the closure body — and put the branch's label two
// lines away from the hypothesis it grants. Nested case analysis paid
// that three times over: the sign-table argument in int_divides reached
// thirteen tabs before its first mathematical word.
//
// The statement form spends one:
//
//	a.Cases(t)
//	a.When("t holds: …", func(b *Argument, h Fact) {
//	    …
//	})
//	a.Otherwise("t fails: …", …)
//
// WHICH BRANCH IS WHICH IS THE VERB, NOT THE POSITION. `When` takes the
// branch where the case term holds and `Otherwise` the branch where it
// fails, `Base` and `Step` take an induction's two obligations,
// `Forward` and `Backward` the two halves of an ⇔ — the same principle
// iff_direction.go established for the ⇔ split, applied to every split.
// Two branches may be written in either order, a branch claimed twice
// is a loud panic, and a branch never claimed is a loud panic naming
// it. Nothing is positional, so nothing can silently drift.
//
// A branch body is a list of Actions, or ONE closure — `func(b
// *Argument, h Fact)` where the branch grants a hypothesis (what
// `Given` spelled), `func(b *Argument)` where it does not (what
// `Derive` spelled), and for an induction step that grants SEVERAL —
// one per recursive constructor argument, a binary tree's two subtrees
// — `func(b *Argument, left, right Fact)` or `func(b *Argument, ihs
// []Fact)`, the hypotheses in the constructor's argument order (what
// `GivenEach` spells). The list form means a one-line branch stays one
// line: `a.Base("at 0 the power is 1", By(Pow))`.
//
// NOTHING ABOUT THE PROOF CHANGES. The opener runs the same ministep
// with no Case bodies, and each branch body runs against the same child
// goal, in the same order, through the same block machinery
// dispatchCases uses. A converted site is tree-identical, so every
// recorded CNF key keeps hitting.

package proof

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// branchSlot is one child of a pending split, named for the verb that
// claims it.
type branchSlot struct {
	verb  string
	child *GoalStackNode
	taken bool
}

// pendingSplit is a fan-out an opener verb produced whose branches are
// not all claimed yet. While one is open the Argument's ordinary verbs
// refuse to run: the deduction has no single line to continue on until
// every branch is accounted for.
type pendingSplit struct {
	opener string
	slots  []branchSlot
}

// unclaimed names the slots still waiting, in declaration order.
func (p *pendingSplit) unclaimed() []string {
	var out []string
	for _, s := range p.slots {
		if !s.taken {
			out = append(out, s.verb)
		}
	}
	return out
}

// verbs names every slot of the split, claimed or not.
func (p *pendingSplit) verbs() []string {
	out := make([]string, 0, len(p.slots))
	for _, s := range p.slots {
		out = append(out, s.verb)
	}
	return out
}

// ---------------------------------------------------------------------------
// The openers
// ---------------------------------------------------------------------------

// Cases splits on the truth of t — "by cases on t". `When` then claims
// the branch on which t holds and `Otherwise` the branch on which it
// fails, whatever t's polarity: the split orders its children by the
// term under one leading ¬, and the verbs are named for t itself
// (ByCaseBranch), so `a.Cases(¬p)` gives `When` the branch holding ¬p.
//
// For an ASYMMETRIC split — one branch trivial, the argument continuing
// in the other — reach for the linearizers (Assuming / Unless) instead,
// which keep the main line at this level and cost no branch at all.
func (a *Argument) Cases(t TermLike) {
	term := t.Core()
	names := []string{"Otherwise", "Otherwise"}
	when, _ := ByCaseBranch(term, true)
	names[when] = "When"
	a.openSplit("Cases", ByCaseStep(term), names...)
}

// Induct is induction on the goal binder named `on` — "by induction on
// m". `Base` then claims the zero obligation and `Step` the successor
// obligation.
//
// The variable is taken FROM THE STATEMENT (its type comes from the
// binder, and the name is registered in the ParseScope so the step case
// can spell its induction hypothesis), which is why this verb takes a
// name and not a term: the alternative is re-declaring a variable the
// goal already binds and hoping the two agree. The binder may sit at
// any position in the goal's leading ∀-prefix — the induction tactic
// does not require it to be outermost, and nothing needs to be stripped
// first.
//
// It takes the binder's NAME, or — when the branch bodies need the
// variable as a term, and so must have it before the branches are
// written — the term Binder returned for it. The name is the
// statement's whether or not closure parameters were bound before it:
// Binder inverts the α-rename an earlier strip leaves (`n` finds `n₀`),
// so `a.Induct("n")` is the same move in a zero-parameter closure and
// after `func(a *Argument, f *Arrow[A, Nat], …)`.
//
// A name the goal no longer binds is the variable the section fixed
// under it: a section binds every binder of a statement in the standard
// form before its body runs, so the variable is free in the goal, and
// the induction generalizes it there — the hypotheses that mention it
// move back into the conclusion, and each case states the conclusion
// at the constructor (inductionVariable).
//
// A datatype with ONE constructor and no recursive argument — a pair
// type, `complex(x, y)` — has one case and no hypothesis: "write z as
// complex(x, y)". That is not a split, so the opener takes no branches
// and the deduction continues on the case, whose constructor arguments
// a.StepArgs names as it does in a step.
func (a *Argument) Induct(on any) {
	var v Term
	switch t := on.(type) {
	case string:
		v = a.inductionVariable(t)
	case Term:
		v = t
	case TermLike:
		v = t.Core()
	default:
		panic(fmt.Sprintf("Argument.Induct: induct on a binder NAME or on the term Binder returned; got %T", on))
	}
	a.openSplit("Induct", a.s.InductStep(v), "Base", "Step")
}

// inductionVariable is the variable Induct(name) inducts on: the goal's
// leading ∀-binder by that name (Binder), or else the variable of that
// name free in the goal — the one the section fixed for the statement's
// binder, its name the statement's up to the α-rename a strip leaves
// (`n` finds `n₀`).
func (a *Argument) inductionVariable(name string) Term {
	key := dsl.IdentifierName(name)
	for t := a.cur.Goal.Conclusion(); ; {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		if spelled := string(abs.Var().Name()); spelled == key || SurfaceBase(spelled) == key {
			return a.Binder(name)
		}
		t = abs.Body()
	}
	var exact, renamed []core.VarTerm
	seen := map[string]bool{}
	frees := a.cur.Goal.Conclusion().Frees(nil)
	for h := range a.cur.Goal.HypIter() {
		frees = append(frees, h.Frees(nil)...)
	}
	for _, v := range frees {
		spelled := string(v.Name())
		if seen[spelled] {
			continue
		}
		seen[spelled] = true
		switch {
		case spelled == key:
			exact = append(exact, v)
		case SurfaceBase(spelled) == key:
			renamed = append(renamed, v)
		}
	}
	if len(exact) == 0 {
		exact = renamed
	}
	switch len(exact) {
	case 0:
		return a.Binder(name)
	case 1:
		return exact[0]
	}
	names := make([]string, len(exact))
	for i, v := range exact {
		names[i] = string(v.Name())
	}
	panic(a.withAliasLegend(fmt.Sprintf(
		"Argument.Induct(%q): the goal binds no such binder, and %d of its free variables carry that name (%v) — induct on the term of the one you mean",
		name, len(exact), names)))
}

// Iff splits an ⇔ goal into its two directions — "we prove both
// directions". `Forward` then claims the ⇒ half (the left side
// resident, the right side the claim) and `Backward` the ⇐ half. The
// tactic emits the ⇐ child FIRST; that is this verb's business, not the
// author's, and the two may be written in either order.
func (a *Argument) Iff() {
	a.openSplit("Iff", SplitIffCases(), "Backward", "Forward")
}

// openSplit runs a branching ministep with NO Case bodies and records
// its children as the pending slots `names` claims, in the tactic's own
// child order.
func (a *Argument) openSplit(opener string, step Step, names ...string) {
	a.guard(opener)
	a.s.Do(a.cur, step)
	kids := a.cur.children
	if opener == "Induct" && len(kids) == 1 {
		a.advanceOrClose(opener)
		return
	}
	if len(kids) != len(names) {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s: the split produced %d branches, and this verb names %d (%s) — "+
				"a shape with a different branch count has no verb here yet; report it "+
				"([kernel-wishlist]) rather than addressing branches by position\n  goal: %s",
			opener, len(kids), len(names), strings.Join(names, " / "), prop.PrintProp(a.cur.Goal))))
	}
	p := &pendingSplit{opener: opener}
	for i, name := range names {
		p.slots = append(p.slots, branchSlot{verb: name, child: kids[i]})
	}
	a.open = p
}

// ---------------------------------------------------------------------------
// The branch verbs
// ---------------------------------------------------------------------------

// When claims the branch of the open Cases split on which the case term
// HOLDS — "when t: …". The branch's hypothesis is t.
func (a *Argument) When(label string, body ...any) { a.claimBranch("When", label, body) }

// Otherwise claims the branch on which the case term FAILS — "otherwise:
// …". The branch's hypothesis is t's denial: ¬t, or p for t = ¬p, the
// split contracting a leading ¬ rather than stacking one.
func (a *Argument) Otherwise(label string, body ...any) { a.claimBranch("Otherwise", label, body) }

// Base claims the open Induct's zero obligation — the branch that
// proves the property at the datatype's base, with no hypothesis.
func (a *Argument) Base(label string, body ...any) { a.claimBranch("Base", label, body) }

// Step claims the open Induct's successor obligation — the branch whose
// hypothesis is the induction hypothesis.
func (a *Argument) Step(label string, body ...any) { a.claimBranch("Step", label, body) }

// StepArgs names the constructor's arguments the enclosing induction
// step introduced — "at cons(h, t): …" — binding one author-chosen
// surface name per argument, in the constructor's own order, so the
// step's claim texts can spell them, and returning them as terms for
// the places a verb takes one (an At witness, a Take):
//
//	a.Step("at a cons: …", func(b *Argument, ih Fact) {
//	    head, tail := b.StepArgs("h", "t")[0], …   // or: args := b.StepArgs("h", "t")
//	    b.Show("…", By(ih, Law.At(head, tail)))
//	})
//
// A constructor's arguments are variables the ENGINE minted, and until
// this verb they had no spelling at all: they are not the statement's
// binders, so a.Binder cannot reach them, and a fresh argument occurs
// in no hypothesis, so the term parser's scope does not carry them
// either. The one exception is the primary recursive argument — the
// tail of a cons, the left subtree of a Node — which the induction
// makes the induction variable itself (the step's hypothesis is stated
// at it); its name here is a second spelling of a variable already in
// scope, and passing that variable's own name is accepted as a no-op.
//
// It records nothing — a binding is bookkeeping, like Given's — so a
// step converted to it keeps its tree and every recorded key. The
// names are required, one per argument, and must be fresh (§"One name,
// one meaning" in derive.go): the engine's own spelling of a minted
// argument is deliberately not offered, because a claim text speaks the
// author's names and that spelling is read off whichever principle the
// env serves.
//
// Valid anywhere inside an induction step's body, before or after
// shaping, and on the line a one-case induction continues on: the
// arguments are read off the nearest enclosing induction branch, by re-running the tactic's own minting on that branch's
// parent goal (tactic.InductionCaseArguments). A case that introduces
// nothing — the base case — refuses.
func (a *Argument) StepArgs(names ...string) []*ext.TermWrapper {
	a.guardRead("StepArgs")
	branch, index := a.inductionBranch()
	if branch == nil {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.StepArgs: no enclosing induction step — StepArgs names the constructor "+
				"arguments an a.Induct's Step introduced, so it runs inside a Step body\n  goal: %s",
			prop.PrintProp(a.cur.Goal))))
	}
	step := branch.parent.miniStep.(_InductionStep)
	if step.template == nil {
		panic("Argument.StepArgs: the induction step carries no template — a replayed placeholder, not a live Induct")
	}
	c := step.template.Cases[index]
	args := tactic.InductionCaseArguments(branch.parent.Goal, step.inductVar, step.template, index)
	if len(args) == 0 {
		panic(fmt.Sprintf("Argument.StepArgs: this case of the induction on %s introduces no constructor "+
			"argument (its obligation is %s) — there is nothing to name",
			ext.PrintTerm(step.inductVar), ext.PrintTerm(c.Constructor)))
	}
	if len(names) != len(args) {
		binders := make([]string, len(c.Args))
		for j, v := range c.Args {
			binders[j] = string(v.Name())
		}
		panic(fmt.Sprintf("Argument.StepArgs: the constructor %s takes %d argument(s) (the principle binds them %s), "+
			"and %d name(s) were given — one name per argument, in the constructor's order",
			ext.PrintTerm(c.Constructor), len(args), strings.Join(binders, ", "), len(names)))
	}
	out := make([]*ext.TermWrapper, len(args))
	for j, name := range names {
		if name == "" {
			panic("Argument.StepArgs: surface name must be non-empty")
		}
		if how := a.spellingTaken(name, args[j]); how != "" {
			panic(a.withAliasLegend(fmt.Sprintf(
				"Argument.StepArgs(%q): that name is already %s — pick a fresh one", name, how)))
		}
		a.bindSurface(name, args[j])
		out[j] = ext.WrapTerm(args[j])
	}
	return out
}

// inductionBranch finds the nearest enclosing induction branch of the
// block's current leaf — the ancestor whose parent ran an induction
// ministep — and that branch's index among the induction's children,
// which is its case's index in the principle. nil when no induction
// encloses the leaf.
func (a *Argument) inductionBranch() (*GoalStackNode, int) {
	return inductionBranchOf(a.cur)
}

// inductionBranchOf is inductionBranch from any node: the nearest
// ancestor-or-self whose parent ran an induction ministep, and its
// index among that induction's children.
func inductionBranchOf(leaf *GoalStackNode) (*GoalStackNode, int) {
	for n := leaf; n != nil && n.parent != nil; n = n.parent {
		if _, ok := n.parent.miniStep.(_InductionStep); !ok {
			continue
		}
		for i, c := range n.parent.children {
			if c == n {
				return n, i
			}
		}
		panic("an induction branch is not among its parent's children (engine invariant)")
	}
	return nil, -1
}

// Forward claims the ⇒ half of the open Iff — the left side is
// resident, the right side is the claim. `label` says what carries that
// implication, in mathematics: the direction is the verb, so the label
// never has to name it and cannot disagree with it.
func (a *Argument) Forward(label string, body ...any) { a.claimBranch("Forward", label, body) }

// Backward claims the ⇐ half — the right side is resident, the left
// side is the claim.
func (a *Argument) Backward(label string, body ...any) { a.claimBranch("Backward", label, body) }

// claimBranch takes the named slot of the open split and runs `body`
// against its child goal — the same application dispatchCases performs
// for a Case body, so a converted site records the identical tree.
//
// When the last slot is taken the split is complete and the block
// resumes: no leaf left means the branches closed the goal between them
// and the block is done; exactly one means the deduction continues
// there, as it always did.
func (a *Argument) claimBranch(verb, label string, body []any) {
	if a.closed {
		panic(fmt.Sprintf("Argument.%s: the block already closed its goal — a verb after the step that closed it", verb) + closedLeafNote(a.cur))
	}
	if a.cur == nil {
		panic(fmt.Sprintf("Argument.%s: no current leaf", verb))
	}
	if a.open == nil {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s: no split is open — %s claims a branch some opener produced, so it "+
				"follows a.Cases(t) / a.Induct(v) / a.Iff() in the same block\n  goal: %s",
			verb, verb, prop.PrintProp(a.cur.Goal))))
	}
	idx := -1
	for i := range a.open.slots {
		if a.open.slots[i].verb == verb {
			idx = i
			break
		}
	}
	if idx < 0 {
		panic(fmt.Sprintf("Argument.%s: the open a.%s has no such branch — its branches are %s",
			verb, a.open.opener, strings.Join(a.open.verbs(), " and ")))
	}
	if a.open.slots[idx].taken {
		panic(fmt.Sprintf("Argument.%s: that branch is already proved — the open a.%s has one %s, "+
			"and its other branch is %s", verb, a.open.opener, verb,
			strings.Join(a.open.unclaimed(), " and ")))
	}
	a.open.slots[idx].taken = true
	runBranchBody(a.s, verb, label, a.open.slots[idx].child, body)

	if len(a.open.unclaimed()) > 0 {
		return
	}
	opener := a.open.opener
	a.open = nil
	a.advanceOrClose(opener)
}

// runBranchBody applies a branch body to its child goal. The block
// forms are told apart by the closure's own signature — a branch that
// grants a hypothesis takes it, one that does not cannot ask for it,
// and a step that grants several takes them all — so neither the
// author nor this function has to predict which the branch is: a wrong
// guess is a compile error at the closure, and a branch that grants a
// different number of hypotheses than the closure asks for fails
// loudly in the binding's own diagnosis (Given's, or GivenEach's).
func runBranchBody(s *Script, verb, label string, child *GoalStackNode, body []any) {
	if len(body) == 0 {
		panic(fmt.Sprintf("Argument.%s(%q): no body — a branch has to prove its goal\n  goal: %s",
			verb, label, prop.PrintProp(child.Goal)))
	}
	if len(body) == 1 {
		switch fn := body[0].(type) {
		case func(*Argument, Fact):
			_GivenAction{body: fn}.applyAction(s, child)
			return
		case func(*Argument, Fact, Fact):
			_GivenEachAction{verb: verb, arity: 2, body: func(b *Argument, hs []Fact) { fn(b, hs[0], hs[1]) }}.applyAction(s, child)
			return
		case func(*Argument, []Fact):
			_GivenEachAction{verb: verb, body: fn}.applyAction(s, child)
			return
		case func(*Argument):
			_DeriveAction{body: fn}.applyAction(s, child)
			return
		}
	}
	acts := make([]Action, 0, len(body))
	for i, b := range body {
		act, ok := b.(Action)
		if !ok {
			extra := ""
			switch b.(type) {
			case func(*Argument, Fact), func(*Argument, Fact, Fact), func(*Argument, []Fact), func(*Argument):
				extra = " — a closure is the WHOLE body, never one item beside Actions"
			}
			panic(fmt.Sprintf("Argument.%s(%q): body item %d is %T%s\n"+
				"a branch body is a list of Actions, or ONE closure: "+
				"func(b *Argument, h Fact) where the branch grants a hypothesis, "+
				"func(b *Argument, left, right Fact) or func(b *Argument, ihs []Fact) where an induction "+
				"step grants one per recursive constructor argument, "+
				"func(b *Argument) where it grants none", verb, label, i, b, extra))
		}
		acts = append(acts, act)
	}
	for _, act := range acts {
		act.applyAction(s, child)
	}
}

// requireBranchesClaimed is the block-exit half of the branch contract:
// a body that opened a split has to prove every branch of it. Without
// this the failure surfaces as the generic "block ended with N open
// goal(s) — close with Show(…)", which names neither the split nor the
// branch that was forgotten.
func (a *Argument) requireBranchesClaimed(verb string) {
	if a.open == nil {
		return
	}
	left := a.open.unclaimed()
	msg := fmt.Sprintf("%s: the block ended with a.%s's %s unproved — every branch of a split "+
		"has to be claimed", verb, a.open.opener, strings.Join(left, " and "))
	for _, s := range a.open.slots {
		if !s.taken {
			msg += fmt.Sprintf("\n  a.%s(…) proves: %s", s.verb, prop.PrintProp(s.child.Goal))
		}
	}
	panic(msg)
}
