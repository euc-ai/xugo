// derive.go — the closure-style linear deduction context (Argument) and
// its verbs: the mathematical surface of a proof body, with facts as
// first-class values.
//
// Derive(func(a *Argument) { … }) is Deduce's value-returning sibling: the
// same linearity contracts (every non-terminal verb leaves exactly one
// unsolved leaf; the block must close its goal; a Have's proof must
// close its claim, eagerly and by name), with the facts the deduction
// establishes RETURNED as Fact values (fact.go) instead of left as
// anonymous residents addressed by content. The Go variable graph is
// the proof DAG: a Have's fact flows into later By premise lists by
// name, and what a By is not handed it cannot see (lexical scope; see
// fact.go's spine/leaf contract).
//
// Given(func(a *Argument, h Fact) { … }) is Derive for a branch: a Case
// body whose parent step introduced exactly one hypothesis receives it
// as a value instead of re-spelling it as text.
//
// The verb inventory follows one rule — A VERB EXISTS EXACTLY WHERE A
// PAPER PROOF HAS A WORD FOR THE MOVE:
//
//	Fix         "let n be arbitrary"       ∀-intro; returns the fixed term
//	Assume      "assume H"                 ⇒-intro; returns H as a Fact
//	SupposeNot  "suppose not"              contradiction entry; returns ¬goal
//	Assuming    "we may assume t"          linearized case split; returns t
//	Unless      "settled when t holds"     linearized case split; returns ¬t
//	Obtain      "obtain d with P(d)"       ∃-elim; returns d and P(d)
//	ObtainChosen "let d be THE chosen witness" ∃-elim by Hilbert choice;
//	            returns εd.P(d) and P(εd.P(d)) — for the argument that
//	            must keep speaking about the canonical ε-term
//	Have        "we have P, because …"     cut; returns P
//	Denote      "write d for ⟨term⟩"       abbreviation, no proof
//	            obligation; returns the equation d = term
//	Take        "take B := t"              ∃-intro, and ∃!-intro on a
//	                                       leading ∃! (Witness)
//	Hyp         name an already-resident hypothesis (assumed premise,
//	            branch hyp) so premise lists can cite it
//	Show        "hence G ∎"                the labeled terminal close
//
// Goal-surface choreography with NO paper word (Basic, bare StripQuant,
// CondRewrite, Clear) deliberately has no verb here: it lives inside
// these verbs' implementations — computed plumbing, the Cite/CalcOrder
// principle applied to goal-state transitions — or behind Do(…), the
// marked escape hatch.

package proof

import (
	"fmt"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"slices"
	"strings"
	"unicode"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// Argument is the running state of a Derive block: the Script and the
// current spine leaf. Verbs advance the spine; each verb enforces the
// Deduce linearity contract at its own call (loud, named panics).
type Argument struct {
	s      *Script
	cur    *GoalStackNode
	closed bool

	// parent is the enclosing block in the dynamic chain (nil at a
	// section root). Wired at block creation from Script.curArg; the
	// chain is what a nested block's claim texts resolve surface names
	// through — see §"Surface names" below.
	parent *Argument
	// aliases maps a surface (statement binder) name to the minted
	// variable it denotes within this block. Lazily allocated by
	// bindSurface; nil for a block that minted nothing.
	aliases map[string]core.VarTerm
	// declared lists the names this block ADDED to the Script's parse
	// scope (declare): the variables it minted or named. A mint is a
	// free of this block's goal only — a sibling branch is a different
	// goal, and the strip that mints there picks its names from that
	// goal alone, so it can mint the same name at another type. The
	// block's exit withdraws them (enterArgument's restore).
	declared []string

	// open is the split whose branches are still being claimed, nil
	// between splits. While it is set the deduction has no single line
	// to continue on, so every ordinary verb refuses (guard) and only
	// the branch verbs run — see branch.go.
	open *pendingSplit

	// forEach is, in the block ForEach runs its body in, the stated
	// name of the binder it fixed ("" in every other block). The
	// variable is fixed with no surface name, so a text that spells the
	// binder finds no such free — the refusal names the spelling that
	// has one (forEachNote).
	forEach string
}

// forEachNote is the repair appended to a refusal of the text raw
// raised while a ForEach body is running, when raw spells the loop's
// binder: the variable is minted without a surface name, and a body
// whose text spells it is a Derive that fixes it by name. Empty
// outside a ForEach, and for a text that does not spell the binder.
func (s *Script) forEachNote(raw string) string {
	for b := s.curArg; b != nil; b = b.parent {
		if b.forEach == "" || !spellsName(raw, b.forEach) {
			continue
		}
		return fmt.Sprintf("\n(inside a ForEach: its variable %s is fixed without a surface name, so a text cannot "+
			"spell it. ForEach is for a body whose witnesses are the closure value itself; a body that writes "+
			"the variable in a text is `Derive(func(b *Argument) { %s := b.FixAs[T](%q); … })`.)",
			b.forEach, b.forEach, b.forEach)
	}
	return ""
}

// spellsName reports whether text holds name as a whole identifier.
func spellsName(text, name string) bool {
	isIdent := func(r rune) bool { return r == '_' || r == '\'' || unicode.IsLetter(r) || unicode.IsDigit(r) }
	return slices.Contains(strings.FieldsFunc(text, func(r rune) bool { return !isIdent(r) }), name)
}

// enterArgument wires a new block into the Script's dynamic Argument
// chain and returns the restore func. Lexical nesting of the Go
// closures IS the dynamic nesting of their execution — blocks run
// synchronously — so the chain at parse time is exactly the enclosing
// blocks of the claim being parsed.
func (s *Script) enterArgument(a *Argument) func() {
	prev := s.curArg
	s.curArg = a
	return func() {
		s.curArg = prev
		for _, name := range a.declared {
			delete(s.ParseScope.Vars, name)
		}
	}
}

// declare registers a variable this block mints or names in the
// Script's parse scope, so later claim texts may spell it (Script.Var:
// idempotent at the same type, loud at a different one), and — when
// the name was not declared before — records it for withdrawal at the
// block's exit. A name some enclosing scope already declared stays
// that scope's.
func (a *Argument) declare(name string, ty core.HolType) *ext.TermWrapper {
	_, existed := a.s.ParseScope.Vars[name]
	w := a.s.Var(name, ty)
	if !existed {
		a.declared = append(a.declared, name)
	}
	return w
}

// Derive runs body against the current leaf as a linear deduction and
// requires the block to close it. The closure receives the Argument context
// whose verbs return Fact values and fixed terms — see the file header.
func Derive(body func(a *Argument)) Action { return _DeriveAction{body: body} }

type _DeriveAction struct{ body func(a *Argument) }

func (act _DeriveAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("Derive: no unsolved leaves remaining (section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	a := &Argument{s: s, cur: anchor, parent: s.curArg}
	defer s.enterArgument(a)()
	act.body(a)
	a.requireBranchesClaimed("Derive")
	requireBlockClosed("Derive", anchor)
}

// Given is Derive for a Case body whose PARENT step introduced exactly
// one hypothesis: the branch receives that hypothesis as a value.
//
//	a.Induct(p)
//	a.Base("at 0: …", By(…))
//	a.Step("p → suc p: …", func(b *Argument, ih Fact) {   // the IH, not re-spelled
//	    b.Show("…", By(ih, …))
//	})
//
// A branch verb takes such a closure directly (branch.go); the bare
// Given value below is what a Chain-form Case body still passes.
//
// The alternative is `a.Hyp("<the hypothesis restated>")`: a text that
// must match what the engine just built, and for an induction
// hypothesis one that additionally forces binding the induction
// variable so the text parses. The engine holds the fact — take it
// rather than re-spell it.
//
// It is not induction-specific: any step whose branch adds exactly one
// hypothesis qualifies — an Induct step case (the IH), a ByCaseStep
// branch (the discriminant or its negation), a SplitDisj arm (the
// disjunct). `a.Hyp` remains right for the hyps no Case introduced. An
// induction step that grants SEVERAL — one per recursive constructor
// argument — is GivenEach's (`func(b *Argument, left, right Fact)`).
//
// Binding is pure bookkeeping — the hypothesis is located by diffing
// the parent goal against this branch's, and NO ministep is recorded —
// so converting a `Derive` + `a.Hyp` body to `Given` leaves the proof
// tree (and every recorded CNF key) untouched.
//
// The body runs as a full Argument block under Derive's contracts:
// every non-terminal verb leaves exactly one unsolved leaf, and the
// block must close its goal.
func Given(body func(a *Argument, h Fact)) Action { return _GivenAction{body: body} }

type _GivenAction struct{ body func(a *Argument, h Fact) }

func (act _GivenAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("Given: no unsolved leaves remaining (section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	if anchor.parent == nil {
		panic("Given: no parent step — Given binds a hypothesis some enclosing step introduced, " +
			"so it belongs in a branch body (Induct / Cases / SplitDisj / SplitIff / …) or after a " +
			"step that introduces one. A block with no hypothesis to receive is " +
			"Derive(func(a *Argument){ … }).\n  goal: " + prop.PrintProp(anchor.Goal))
	}
	before, idx, err := givenSource(root, anchor)
	if err != nil {
		panic(givenBindingFailure(before, anchor.Goal, err))
	}
	a := &Argument{s: s, cur: anchor, parent: s.curArg}
	defer s.enterArgument(a)()
	h := a.bindNewHyp("Given", ext.PrintTerm(anchor.Goal.Hyp(idx)), before)
	act.body(a, h)
	a.requireBranchesClaimed("Given")
	requireBlockClosed("Given", anchor)
}

// ForEach — "for every x, this": an Action that fixes the goal's
// leading ∀-binder under its stated name and type, hands it to body,
// and runs the one Action body returns, which must close the leaf. It
// is the one-line form of the ∀-lift block
//
//	Derive(func(g *Argument) {
//	    n := g.FixAs[Nat]()
//	    g.Show("…", By(bounded.At(n), AbsBounds.At(a.Apply(n), B)))
//	})
//
// spelled
//
//	a.ForEach(func(n *Expr[Nat]) Action { return By(bounded.At(n), AbsBounds.At(a.Apply(n), B)) })
//
// and it records what that block records: the strip and the close,
// nothing else. The bare `By(bounded, AbsBounds)` on the ∀-goal closes
// too, but at a price the page does not show — the premises are
// installed wide before the goal is stripped, and grounding them at
// the fixed variable is the conditioning stage's search, persisted as
// a plan row; here the author grounds them, so no search runs and no
// row is written. The binder is fixed as FixAs fixes it: the type is
// checked against the goal's binder at the site, and the stated name
// is offered as the claim-text spelling.
//
// A method rather than a function for the reason FixAs is one: a
// generic FUNCTION cannot be aliased into a family package
// un-instantiated (typed.go, TypeBinder), a generic method rides the
// value. The receiver is the block the loop is written in — the
// Action runs where it is placed, in a block of its own, as Derive's
// does.
//
// The body receives the variable only. A block that must parse a term
// against it, assume an antecedent by name, or state a fact on the way
// is a Derive; an antecedent the close needs is the conditioning
// stage's to move into the context (the goal strip) and needs no name.
//
// Panics, naming ForEach: a goal without a leading ∀ (FixAs's
// refusal), a binder of another type, an Action that leaves the leaf
// open.
func (a *Argument) ForEach[T ext.TypePhantom](body func(x *ext.Expr[T]) Action) Action {
	a.guardRead("ForEach")
	if body == nil {
		panic("Argument.ForEach: the body is nil — pass func(x *Expr[T]) Action")
	}
	return _ForEachAction[T]{body: body}
}

type _ForEachAction[T ext.TypePhantom] struct {
	body func(x *ext.Expr[T]) Action
}

func (act _ForEachAction[T]) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("ForEach: no unsolved leaves remaining (section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	if ext.MatchesFORALL(anchor.Goal.Conclusion()).IsZero() {
		panic("ForEach: the goal has no leading ∀ to fix — \n  goal: " + prop.PrintProp(anchor.Goal))
	}
	a := &Argument{s: s, cur: anchor, parent: s.curArg}
	defer s.enterArgument(a)()
	x := a.FixAs[T]()
	if v, isVar := x.Core().AsVar(); isVar {
		a.forEach = SurfaceBase(string(v.Name()))
	}
	step := act.body(x)
	if step == nil {
		panic("ForEach: the body returned a nil Action")
	}
	a.Do(step)
	a.requireBranchesClaimed("ForEach")
	requireBlockClosed("ForEach", anchor)
}

// GivenEach is Given for an induction step that grants SEVERAL
// hypotheses — a constructor with more than one recursive argument, a
// binary tree's node, grants one induction hypothesis per subtree. The
// body receives them in the CONSTRUCTOR'S ARGUMENT ORDER (the left
// subtree's first), each located by content: the step's conclusion at
// that subtree, read off the induction the branch belongs to
// (tactic.InductionCaseHypotheses) — the same preparation the tactic
// ran, so the goal's own hypothesis list, which is sorted, never decides
// which is which.
//
//	a.Step("at node(l, a, r): …", func(b *Argument, left, right Fact) {
//	    b.Show("…", Simp(…), right.Rw(), left.Rw(), Basic())
//	})
//
// A branch verb takes such a closure directly (branch.go): two named
// hypotheses as `func(b *Argument, left, right Fact)`, any number as
// `func(b *Argument, ihs []Fact)`. `arity` > 0 is the count the closure
// spelled; a step granting a different number is a loud panic naming
// both. A step that grants exactly one is Given's; one that grants none
// is Derive's — a mismatch in either direction is refused rather than
// bound by position.
//
// Before this form the only way to take a second hypothesis was to
// name the constructor's arguments (StepArgs) and re-spell each
// hypothesis with a.Hyp — a text that had to match what the engine
// built. Binding is pure bookkeeping, NO ministep is recorded, so a
// step converted to this form keeps its tree and every recorded key.
func GivenEach(body func(a *Argument, hs []Fact)) Action {
	return _GivenEachAction{verb: "GivenEach", body: body}
}

type _GivenEachAction struct {
	verb  string
	arity int
	body  func(a *Argument, hs []Fact)
}

func (act _GivenEachAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic(act.verb + ": no unsolved leaves remaining (section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	branch, index := inductionBranchOf(anchor)
	if branch == nil {
		panic(fmt.Sprintf("%s: no enclosing induction step — a branch that grants SEVERAL hypotheses is an "+
			"induction step over a constructor with several recursive arguments; every other split grants one "+
			"(func(b *Argument, h Fact)) or none (func(b *Argument))\n  goal: %s",
			act.verb, prop.PrintProp(anchor.Goal)))
	}
	step := branch.parent.miniStep.(_InductionStep)
	if step.template == nil {
		panic(act.verb + ": the induction step carries no template — a replayed placeholder, not a live Induct")
	}
	hyps := tactic.InductionCaseHypotheses(branch.parent.Goal, step.inductVar, step.template, index)
	c := step.template.Cases[index]
	switch {
	case len(hyps) == 0:
		panic(fmt.Sprintf("%s: this case of the induction on %s grants no hypothesis (its obligation is at %s) — "+
			"the branch is func(b *Argument)", act.verb, ext.PrintTerm(step.inductVar), ext.PrintTerm(c.Constructor)))
	case len(hyps) == 1:
		panic(fmt.Sprintf("%s: this case of the induction on %s grants ONE hypothesis (at %s) — "+
			"the branch is func(b *Argument, h Fact)", act.verb, ext.PrintTerm(step.inductVar), ext.PrintTerm(c.Constructor)))
	case act.arity > 0 && act.arity != len(hyps):
		panic(fmt.Sprintf("%s: the closure names %d hypotheses and this case of the induction on %s grants %d "+
			"(one per recursive argument of %s, in the constructor's order) — spell that many, or take them as "+
			"func(b *Argument, ihs []Fact)", act.verb, act.arity, ext.PrintTerm(step.inductVar), len(hyps), ext.PrintTerm(c.Constructor)))
	}
	a := &Argument{s: s, cur: anchor, parent: s.curArg}
	defer s.enterArgument(a)()
	facts := make([]Fact, len(hyps))
	for i, h := range hyps {
		idx, err := findHypIndex(anchor.Goal, h)
		if err != nil {
			panic(fmt.Sprintf("%s: the induction hypothesis at recursive argument %d is not resident on the branch "+
				"(engine invariant): %v\n  expected: %s\n  goal: %s",
				act.verb, i+1, err, ext.PrintTerm(h), prop.PrintProp(anchor.Goal)))
		}
		handle := NewHypHandle(ext.PrintTerm(anchor.Goal.Hyp(idx)))
		handle.bindTo(anchor, anchor.Goal.Hyp(idx))
		facts[i] = residentFact(handle)
	}
	act.body(a, facts)
	a.requireBranchesClaimed(act.verb)
	requireBlockClosed(act.verb, anchor)
}

// givenSource locates the step whose hypothesis this Given binds: the
// NEAREST enclosing step that actually introduced one.
//
// Neither end of the ancestor chain is right on its own, because two
// shapes want different answers:
//
//   - a Given at the head of a branch body, with a hyp-neutral step in
//     between (`Case(Chain(TrivialSimplify(), Given(…)))`) — the
//     hypothesis came from the BRANCH, several levels up;
//   - a Given running mid-chain, after an Unless/Assuming introduced a
//     hypothesis in the same body — the branch node is far above and
//     carries its own hypothesis, which must not be picked up.
//
// So walk up from the leaf's own parent, skipping steps that introduced
// nothing, and stop at the first that introduced exactly one — bounded
// by the body's own branch (root.parent), which is as far as a Given's
// hypothesis can possibly come from. A step that introduced SEVERAL is
// reported where it is found rather than skipped: that is the authoring
// error the panic explains, not a reason to keep climbing.
func givenSource(root, anchor *GoalStackNode) (Prop, int, error) {
	last, lastErr := anchor.parent.Goal, error(nil)
	for n := anchor.parent; n != nil; n = n.parent {
		idx, err := newHypIndex(n.Goal, anchor.Goal)
		if err == nil {
			return n.Goal, idx, nil
		}
		last, lastErr = n.Goal, err
		if countAddedHyps(n.Goal, anchor.Goal) > 1 {
			break // several: report here, do not climb past it
		}
		if root.parent != nil && n == root.parent {
			break // the branch itself — nothing above it is this Given's
		}
	}
	return last, 0, lastErr
}

// countAddedHyps counts the hypotheses present in `after` and absent
// from `before`.
func countAddedHyps(before, after Prop) int {
	n := 0
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if !before.HasHyp(h) && !before.AnyHyp(h.AlphaEquals) {
			n++
		}
	}
	return n
}

// givenBindingFailure turns the hyp-diff error into the authoring
// advice for the shape that produced it: a parent that added no
// hypothesis, or one that added several.
func givenBindingFailure(before, after Prop, err error) string {
	var added []core.Term
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if before.HasHyp(h) || before.AnyHyp(h.AlphaEquals) {
			continue
		}
		added = append(added, h)
	}
	msg := fmt.Sprintf("Given: the parent step introduced %d hypotheses, not one (%v)", len(added), err)
	switch len(added) {
	case 0:
		msg += "\nthis branch receives no new hypothesis — the block is Derive(func(a *Argument){ … })"
	default:
		msg += "\nGiven binds exactly one; write Derive(func(a *Argument){ … }) and name each with a.Hyp(…):"
		for _, h := range added {
			msg += "\n  " + ext.PrintTerm(h)
		}
	}
	return msg + "\n(parent goal: " + prop.PrintProp(before) + ")\n(branch goal: " + prop.PrintProp(after) + ")"
}

// requireBlockClosed is the must-close contract shared by the block
// forms: the body has to close the leaf it was handed.
func requireBlockClosed(verb string, anchor *GoalStackNode) {
	leaves := anchor.UnsolvedLeaves()
	if len(leaves) == 0 {
		return
	}
	msg := fmt.Sprintf("%s: block ended with %d open goal(s) — close with Show(…)", verb, len(leaves))
	for _, l := range leaves {
		msg += "\n  leaf: " + prop.PrintProp(l.Goal)
	}
	panic(msg)
}

// ---------------------------------------------------------------------------
// Internal mechanics
// ---------------------------------------------------------------------------

func (a *Argument) guard(verb string) {
	a.guardRead(verb)
	if a.open != nil {
		panic(fmt.Sprintf("Argument.%s: a.%s's %s branch(es) are still unproved — "+
			"the deduction has no single line to continue on until every branch of an open "+
			"split is claimed", verb, a.open.opener, strings.Join(a.open.unclaimed(), " and ")))
	}
}

// guardRead is guard for the verbs that only READ the block — Term,
// Goal, Hyp, and the typed term readers. They are exempt from the
// open-split refusal because Go evaluates a branch's argument list
// BEFORE the branch verb runs, so a leg's `b.Term("…")` is evaluated
// with the split already open:
//
//	b.Cases(b.Term("j < m"))
//	b.When("…", Unfold(AdjointDef), CalcEq(Leg(b.Term("…"), …)))
//
// That read is well defined and unchanged by the split: an opener does
// not move the spine, so `a.cur` is still the node that was split and
// its Goal — the resident facts a read consults — is exactly what it
// was before. The expression form evaluated the identical call at the
// identical goal; only the punctuation moved. A read cannot be the
// half-finished-split mistake, because it records nothing.
func (a *Argument) guardRead(verb string) {
	if a.closed {
		panic(fmt.Sprintf("Argument.%s: the block already closed its goal — a verb after the step that closed it", verb) + closedLeafNote(a.cur))
	}
	if a.cur == nil {
		panic(fmt.Sprintf("Argument.%s: no current leaf", verb))
	}
}

// advance moves the spine to the single unsolved leaf the last verb
// left — the linearity contract, enforced per verb.
func (a *Argument) advance(verb string) {
	leaves := a.cur.UnsolvedLeaves()
	if len(leaves) != 1 {
		msg := fmt.Sprintf("Argument.%s: left %d unsolved leaves — a non-terminal verb must leave exactly one", verb, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(a.withAliasLegend(msg))
	}
	a.cur = leaves[0]
}

// advanceOrClose is advance for the verbs that may legitimately be
// TERMINAL: a structural split whose branches each close their own case
// leaves nothing behind, and the block is then done — the same state
// Show reaches, reached without a label because the Case labels already
// carry the narrative. One surviving leaf continues the deduction as
// usual; two or more is the linearity violation it always was.
func (a *Argument) advanceOrClose(verb string) {
	leaves := a.cur.UnsolvedLeaves()
	switch len(leaves) {
	case 0:
		a.closed = true
	case 1:
		a.cur = leaves[0]
	default:
		msg := fmt.Sprintf("Argument.%s: left %d unsolved leaves — label them as Cases, or leave exactly one for the deduction to continue on", verb, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(a.withAliasLegend(msg))
	}
}

// ---------------------------------------------------------------------------
// Surface names — the hygienic alias environment
// ---------------------------------------------------------------------------
//
// A claim text names the variables of the STATEMENT, not the engine's
// minted spellings: after `x := a.Fix()` on `∀x:real. …`, a claim may
// write `&0 ≤ x` even though the goal's variable is the minted `x₀`.
// Each block records `surface name → minted variable` bindings as its
// verbs mint (Fix; Obtain/Unpack via skolemizeSpine), and a nested
// block inherits its parent chain's bindings. The minted spelling
// stays valid for the rest of the block that minted it and every block
// nested in it: the verbs declare it in the Script's ParseScope, and the
// block's exit withdraws what it declared (declare, enterArgument).
//
// ONE NAME, ONE MEANING: a spelling that is already live — an alias,
// a declared variable, a constant, or another free of the goal — is
// never silently re-pointed. The automatic bindings (the goal's own
// binder name and its α-rename-inverted base) are OFFERS, skipped
// when the name is taken; an EXPLICIT name — Fix("u") — panics when
// taken, and is the road to a readable spelling where the binder's
// own name is unavailable. The one deliberate exception is the
// section boundary (section.go's bindSlot): a statement's own binder
// names are authoritative for its body and take the text namespace
// over anything resident — the statement is the frame the claims are
// read in.
//
// Resolution is a parse-scope overlay plus a free-variable rename, not
// a text substitution: the claim parses with each surface name declared
// at its minted variable's type, and the parsed Prop's FREE occurrences
// of that name are then renamed to the minted variable (core.Substitute
// — simultaneous and capture-avoiding). A binder inside the claim that
// re-uses the name binds as usual and is untouched; a claim decl prefix
// (`x:T ⊢ …`) that declares the name at a DIFFERENT type overrides the
// overlay, so an explicit declaration always wins.
//
// A surface name is keyed by the IDENTIFIER a claim text reads it as
// (dsl.IdentifierName): the lexer folds a printed subscript to the
// kernel's `_digits`, so Fix("s₁") binds `s_1` — the name a claim
// spelling `s₁` parses to — and `s_1` written by the author is the same
// name, bound once and taken under either spelling. A prime is an
// identifier character and folds to nothing. Every verb that takes a
// surface name (Fix, the witness names of Obtain and Unpack, Binder,
// StepArgs, the section boundary's binder slots) binds and checks
// through bindSurface and spellingTaken, which read the key; the
// legend prints it back as the printer does (`s₁`). A verb that names
// the variable it introduces (Let, LetAs, Denote) names it by the same
// key: Let("i₀", …) introduces i_0, which a claim spells `i₀` or `i_0`
// and the printer shows as `i₀`.

// bindSurface records a surface-name binding in this block,
// unconditionally — the section boundary's authoritative path. Every
// other caller goes through bindSurfaceIfFree or assertSpellingFree
// (§"One name, one meaning" above). The key is the name's identifier
// (§"Surface names": `s₁` is bound as `s_1`).
func (a *Argument) bindSurface(name string, v core.VarTerm) {
	if name == "" || v.IsZero() {
		return
	}
	if a.aliases == nil {
		a.aliases = map[string]core.VarTerm{}
	}
	a.aliases[dsl.IdentifierName(name)] = v
}

// bindSurfaceIfFree is bindSurface as an OFFER: a name that is already
// spellable — or visible as another free of the goal — keeps its
// meaning, and the new spelling is simply not offered. The minted
// name always resolves; Fix("u") is the road to a readable one.
func (a *Argument) bindSurfaceIfFree(name string, v core.VarTerm) {
	if name == "" || v.IsZero() || a.spellingTaken(name, v) != "" {
		return
	}
	a.bindSurface(name, v)
}

// spellingTaken reports how `name` already means something in this
// block's claim text — or "" when it is free for the taking. `minted`,
// when non-nil, is the variable the caller is naming: its own presence
// among the goal's frees does not count against it. The name is read
// as a claim text reads it (§"Surface names"), so a name live as `s₁`
// is taken under `s_1` too.
func (a *Argument) spellingTaken(name string, minted core.VarTerm) string {
	name = dsl.IdentifierName(name)
	if v, ok := a.surfaceAliases()[name]; ok {
		if !minted.IsZero() && v.Name() == minted.Name() && v.Type().Equals(minted.Type()) {
			return ""
		}
		return fmt.Sprintf("a live surface alias (for %s)", ext.PrintTerm(v))
	}
	if ty, ok := a.s.ParseScope.Vars[name]; ok {
		if !minted.IsZero() && string(minted.Name()) == name && ty.Equals(minted.Type()) {
			return "" // the declaration IS this variable: one name, one meaning, already
		}
		return "a declared variable"
	}
	if _, ok := a.s.ParseScope.Consts[name]; ok {
		return "a constant"
	}
	if _, ok := a.s.ParseScope.ConstMetas[name]; ok {
		return "a constant"
	}
	if goalHasOtherFreeNamed(a.cur.Goal, name, minted) {
		return "the name of another free variable of the goal"
	}
	return ""
}

// goalHasOtherFreeNamed reports whether the sequent has a free
// variable spelled `name` that is not `minted` itself.
func goalHasOtherFreeNamed(g Prop, name string, minted core.VarTerm) bool {
	check := func(t core.Term) bool {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			if string(v.Name()) != name {
				continue
			}
			if !minted.IsZero() && v.Name() == minted.Name() && v.Type().Equals(minted.Type()) {
				continue
			}
			return true
		}
		return false
	}
	if check(g.Conclusion()) {
		return true
	}
	for i := 0; i < g.NumHyps(); i++ {
		if check(g.Hyp(i)) {
			return true
		}
	}
	return false
}

// assertSpellingFree is the author-facing half of the naming contract:
// an EXPLICIT surface name must be fresh — a live spelling never
// changes meaning under the author's feet. (Section binding differs:
// the statement's binder names are authoritative there, and bindSlot
// reaches fixImpl directly.)
func (a *Argument) assertSpellingFree(verb, name string) {
	if how := a.spellingTaken(name, core.VarTerm{}); how != "" {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s(%q): that name is already %s — pick a fresh one (the minted name always resolves)",
			verb, name, how)))
	}
}

// fixName unpacks Fix/FixAs' optional surface name: at most one, and
// non-empty — an explicit "" would silently mean the automatic path,
// exactly the ambiguity the argument exists to remove.
func fixName(verb string, name []string) string {
	switch len(name) {
	case 0:
		return ""
	case 1:
		if name[0] == "" {
			panic("Argument." + verb + ": surface name must be non-empty (omit the argument for the automatic spelling)")
		}
		return name[0]
	default:
		panic("Argument." + verb + ": at most one surface name")
	}
}

// surfaceAliases collects the block's effective alias environment —
// its own bindings under the parent chain's, innermost wins.
func (a *Argument) surfaceAliases() map[string]core.VarTerm {
	var out map[string]core.VarTerm
	for b := a; b != nil; b = b.parent {
		for n, v := range b.aliases {
			if out == nil {
				out = map[string]core.VarTerm{}
			}
			if _, ok := out[n]; !ok {
				out[n] = v
			}
		}
	}
	return out
}

// aliasLegend renders the active non-identity aliases — the author
// wrote surface names, a goal prints minted ones, and the legend is
// the bridge a panic message carries between the two. Each key is
// printed as the printer spells a variable (`s_1` as `s₁`). Empty when
// nothing is aliased.
func (a *Argument) aliasLegend() string {
	var entries []string
	for n, v := range a.surfaceAliases() {
		if n == string(v.Name()) {
			continue
		}
		entries = append(entries, utils.FormatSubscript(n)+" ≔ "+ext.PrintTerm(v))
	}
	if len(entries) == 0 {
		return ""
	}
	slices.Sort(entries)
	return "surface names: " + strings.Join(entries, ", ")
}

// withAliasLegend appends the legend to a panic message when aliases
// are active.
func (a *Argument) withAliasLegend(msg string) string {
	if legend := a.aliasLegend(); legend != "" {
		return msg + "\n(" + legend + ")"
	}
	return msg
}

// parseClaim parses a claim text at the block's focus — the variables
// of its goal and its surface aliases (§"Surface names" above), the
// goal's hypotheses as resident facts (claimScope) — as every door
// reads a text (dsl.ParsePropTextAtDoor): a closed claim with the focus
// set aside, any other at the focus. A claim binds none of the member's
// binders, so no binder of the text is exempt from the abbreviation
// capture check; parseClaimBinding exempts the ones a claim written in
// parts declares as its own.
func (a *Argument) parseClaim(verb, raw string) Prop {
	return a.parseClaimBinding(verb, raw, nil)
}

// parseClaimBinding is parseClaim with binders — the names a claim
// written in parts binds in its Binders — exempt from the abbreviation
// capture check (dsl.ParseScope.AbbreviationBinders), as a section's
// own leading binders are exempt at its door
// (Script.withSectionAbbreviations): an entry spelled under such a
// binder is read at it.
func (a *Argument) parseClaimBinding(verb, raw string, binders map[string]bool) Prop {
	scope, substs := a.s.parseScopeWithAliases(a.surfaceAliases())
	scope = a.claimScope(a.withResidentFacts(scope))
	if len(binders) > 0 {
		scope.AbbreviationBinders = binders
	}
	res := dsl.ParsePropTextAtDoor(raw, scope)
	if len(res.Errors) > 0 {
		panic(a.withAliasLegend(fmt.Sprintf("Argument.%s: %q: %s%s", verb, raw, res.Errors[0].Message, a.s.forEachNote(raw))))
	}
	p := res.Prop
	// The statement door's contract on a polymorphic constant, held at
	// the claim door: a letter no term of the claim fixes is the parser's
	// stand-in, so the claim would speak of a type its author never wrote
	// — a different proposition, met later as a leaf no premise fits.
	if unpinned := dsl.UnpinnedLetters(p); len(unpinned) > 0 {
		rows := make([]string, len(unpinned))
		for i, u := range unpinned {
			rows[i] = u.Repair()
		}
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s: %q leaves a type letter unpinned: no term of the claim has that type, so nothing says "+
				"at which type the constant is read. Pin it once where the constant is written:\n  %s",
			verb, raw, strings.Join(rows, "\n  "))))
	}
	// The TermText contract, on the claim path: a free name the scope
	// does not declare is a typo or a missing introduction, never an
	// intent to mint a fresh variable — silently freshening it would
	// state a DIFFERENT proposition. (A `name:type ⊢` decl prefix that
	// re-types a declared name still parses: the check is by name.)
	undeclared := undeclaredFrees(p.Conclusion(), scope)
	for i := 0; i < p.NumHyps(); i++ {
		undeclared = append(undeclared, undeclaredFrees(p.Hyp(i), scope)...)
	}
	slices.Sort(undeclared)
	if undeclared = slices.Compact(undeclared); len(undeclared) > 0 {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s: %q: undeclared free %v — a claim speaks the goal's own names; fix the spelling, or introduce the name first (Fix/Obtain/Denote) (declared: %v)%s",
			verb, raw, undeclared, declaredNames(scope), a.s.forEachNote(raw))))
	}
	return substituteProp(p, substs)
}

// claimScope is scope with only the variables the block's goal states
// and its surface names, as the session's claim door reads a claim with
// its goal's: a variable the script registered for another section or
// branch, which no goal of this block states, is not the claim's to read
// — beside it a symbol the claim's own structure binds would meet a
// second record. A copy where anything is set aside; the Script's own
// scope is shared.
func (a *Argument) claimScope(scope *dsl.ParseScope) *dsl.ParseScope {
	if a.cur == nil || a.cur.Goal == nil {
		return scope
	}
	keep := map[string]bool{}
	goal := a.cur.Goal
	for _, v := range goal.Conclusion().Frees(nil) {
		keep[string(v.Name())] = true
	}
	for i := range goal.NumHyps() {
		for _, v := range goal.Hyp(i).Frees(nil) {
			keep[string(v.Name())] = true
		}
	}
	for n := range a.surfaceAliases() {
		keep[n] = true
	}
	drop := false
	for n := range scope.Vars {
		if !keep[n] {
			drop = true
			break
		}
	}
	if !drop {
		return scope
	}
	narrowed := *scope
	narrowed.Vars = make(map[string]core.HolType, len(keep))
	for n, ty := range scope.Vars {
		if keep[n] {
			narrowed.Vars[n] = ty
		}
	}
	return &narrowed
}

// withResidentFacts is scope with the block's goal hypotheses as the
// resident facts a claim or term text is read under: a structure fact
// among them binds the symbols its components carry
// (ext/dsl/structure.go). A copy — the Script's own scope is shared.
func (a *Argument) withResidentFacts(scope *dsl.ParseScope) *dsl.ParseScope {
	if a.cur == nil || a.cur.Goal == nil || a.cur.Goal.NumHyps() == 0 {
		return scope
	}
	with := *scope
	with.ResidentFacts = a.cur.Goal.Hyps()
	return &with
}

// substituteProp applies a free-variable substitution to every part of
// a Prop (conclusion + hyps).
func substituteProp(p Prop, substs []core.TermSubst) Prop {
	if len(substs) == 0 {
		return p
	}
	hyps := make([]core.Term, 0, p.NumHyps())
	for i := 0; i < p.NumHyps(); i++ {
		hyps = append(hyps, p.Hyp(i).Substitute(substs...))
	}
	return prop.MakeProp(p.Conclusion().Substitute(substs...), hyps...)
}

// Term parses a TERM text against the block's scope — Script.TermText
// with the block's surface aliases applied, for the places a verb takes
// a Term (a Take witness, a Calc leg, an At ground witness):
//
//	a.Take(a.Term("q + 1"))
//
// after `q := a.Fix()` denotes the minted variable even where the goal
// spells it q₀.
func (a *Argument) Term(raw string) *ext.TermWrapper {
	return a.termAt("Term", raw, nil)
}

// termAt is Term read at an expected type (nil: none). The expectation
// reaches the parse, not only a check after it, so a polymorphic
// constant the text leaves bare takes its instance from it — TermAs
// hands its phantom's type, and `a.TermAs[Set[A]]("∅")` is ∅ at
// set(A), as a claim reads `s = ∅` from the partner.
func (a *Argument) termAt(verb, raw string, expected core.HolType) *ext.TermWrapper {
	a.guardRead(verb)
	scope, substs := a.s.parseScopeWithAliases(a.surfaceAliases())
	scope = a.withResidentFacts(scope)
	res := dsl.ParseTermTextInScope(raw, nil, scope, expected)
	if len(res.Errors) > 0 {
		panic(a.withAliasLegend(fmt.Sprintf("Argument.%s: %q: %s%s", verb, raw, res.Errors[0].Message, a.s.forEachNote(raw))))
	}
	if undeclared := undeclaredFrees(res.Term, scope); len(undeclared) > 0 {
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.%s: %q: undeclared free %v — a term speaks the goal's own names; fix the spelling, or introduce the name first (Fix/Obtain/Denote) (declared: %v)%s",
			verb, raw, undeclared, declaredNames(scope), a.s.forEachNote(raw))))
	}
	t := res.Term
	if len(substs) > 0 {
		t = t.Substitute(substs...)
	}
	return ext.WrapTerm(t)
}

// propOf coerces a claim argument: a string parses against the
// Script's ParseScope with the block's surface aliases applied
// (§"Surface names" — Skolems registered by Fix/Obtain resolve under
// either spelling), a Statement written in parts assembles to the one
// string and parses as it (claimParts), a Prop passes through.
func (a *Argument) propOf(verb string, claim any) Prop {
	switch c := claim.(type) {
	case string:
		return a.parseClaim(verb, c)
	case dsl.Statement:
		return a.claimParts(verb, &c)
	case *dsl.Statement:
		if c == nil {
			panic(fmt.Sprintf("Argument.%s: a nil *Statement — write the claim as a string or as a Statement literal", verb))
		}
		return a.claimParts(verb, c)
	case Prop:
		return c
	default:
		panic(fmt.Sprintf("Argument.%s: claim must be a statement string, a Statement{Binders, Hypotheses, Conclusion} or a Prop; got %T", verb, claim))
	}
}

// claimParts reads a claim written in parts, as the member constructors
// read a statement (dsl.Statement.Text): the hypotheses ∧-joined into
// the one antecedent, the binders in front, the whole parsed at the
// claim door as the one string would be. The claim's own Binders are
// exempt from the abbreviation capture check, as a section's leading
// binders are at its door; the abbreviations a claim spells are the
// member's, whose table is in scope for the whole proof, so a claim
// declaring entries of its own is refused.
func (a *Argument) claimParts(verb string, st *dsl.Statement) Prop {
	if len(st.Abbrev) > 0 {
		names := make([]string, len(st.Abbrev))
		for i, entry := range st.Abbrev {
			names[i] = "«" + entry.Name + "»"
		}
		panic(fmt.Sprintf("Argument.%s: the claim declares %s — a claim's abbreviations are the member's: declare the entry in the member's statement, whose table every text of the proof reads",
			verb, strings.Join(names, ", ")))
	}
	text, err := st.Text()
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: %v", verb, err))
	}
	names, err := st.BinderNames()
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: %v", verb, err))
	}
	var binders map[string]bool
	if len(names) > 0 {
		binders = make(map[string]bool, len(names))
		for _, name := range names {
			binders[name] = true
		}
	}
	return a.parseClaimBinding(verb, text, binders)
}

// bindNewHyp diffs before → d.cur.Goal and binds a fresh handle to the
// single net-new hyp.
func (a *Argument) bindNewHyp(verb, name string, before Prop) Fact {
	idx, err := newHypIndex(before, a.cur.Goal)
	if err != nil {
		panic(a.withAliasLegend(fmt.Sprintf("Argument.%s: cannot identify the introduced hypothesis: %v\n(goal: %s)",
			verb, err, prop.PrintProp(a.cur.Goal))))
	}
	h := NewHypHandle(name)
	h.bindTo(a.cur, a.cur.Goal.Hyp(idx))
	return residentFact(h)
}

// sequentFrees keys every free variable of the sequent (conclusion +
// hyps) by name and type.
func sequentFrees(g Prop) map[string]bool {
	m := map[string]bool{}
	collect := func(t core.Term) {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			m[freeVarKey(v)] = true
		}
	}
	collect(g.Conclusion())
	for i := 0; i < g.NumHyps(); i++ {
		collect(g.Hyp(i))
	}
	return m
}

func freeVarKey(v core.VarTerm) string {
	return string(v.Name()) + " : " + ext.FormatType(v.Type())
}

// newFreeVars lists the sequent's free variables absent from `before`,
// deduped, in first-occurrence order (conclusion first, then hyps).
func newFreeVars(before map[string]bool, g Prop) []core.VarTerm {
	var out []core.VarTerm
	seen := map[string]bool{}
	collect := func(t core.Term) {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			k := freeVarKey(v)
			if before[k] || seen[k] {
				continue
			}
			seen[k] = true
			out = append(out, v)
		}
	}
	collect(g.Conclusion())
	for i := 0; i < g.NumHyps(); i++ {
		collect(g.Hyp(i))
	}
	return out
}

// ---------------------------------------------------------------------------
// Verbs
// ---------------------------------------------------------------------------

// Have asserts and proves one fact, then continues the deduction with
// it resident — "we have P, because label: proof". Returns the fact
// for later premise lists. The proof must CLOSE the claim (eager,
// labeled panic — the Deduce contract).
func (a *Argument) Have(label string, claim any, proof ...Action) Fact {
	a.guard("Have")
	cl := a.propOf("Have", claim)
	before := a.cur.Goal
	a.s.Do(a.cur, AssertStep(cl,
		MakeCase("have: "+label, proof...),
		MakeCase("continue: the fact joins the goal's hyps"),
	))
	Assert(len(a.cur.children) == 2)
	claimChild, residual := a.cur.children[0], a.cur.children[1]
	if leaves := claimChild.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("Argument.Have(%q): proof left the claim open (%d unsolved leaf(ves))", label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(a.withAliasLegend(msg))
	}
	a.cur = residual
	return a.bindNewHyp("Have", label, before)
}

// Conjuncts splits a conjunctive fact into one Fact per conjunct —
// "from A ∧ B, A; and B" — one label per conjunct, in the conjunction's
// order. Each conjunct is asserted and closed against the fact by
// normalization alone (an ∧-elimination the closer makes on contact, no
// refutation), so the record is the two Haves an author would write, and
// the deduction continues with the parts resident: the halves of a
// conjunctive hypothesis, which neither Unpack (an ∃) nor a rewrite (an
// equation) opens. A conjunct the leaf already holds — a hypothesis
// α-equal to it, resident before the split or installed by an earlier
// conjunct — is not asserted again: its Fact names that hypothesis, so
// a fact restating part of the context is split for the rest. The fact
// is any fact a context verb takes: a resident fact is split in place, a
// ground instance f.At(w…) or a law read at a fact (a typed reading's
// `.At`) is materialized first (residentHandle). A membership in a
// set-builder of a conjunction is split through its predicate
// (FactConjuncts): `x ∈ {y | P(y) ∧ K(y)}` into P(x) and K(x).
//
//	xZero, yZero := a.Conjuncts(both, "x is zero", "y is zero")
//	inS, inT := a.Conjuncts(inBoth.At(x), "x is in s", "x is in t")
func (a *Argument) Conjuncts(f any, labels ...string) []Fact {
	a.guard("Conjuncts")
	whole := a.inHand("Conjuncts", f)
	// The hypothesis as it stands at the leaf, not as the handle was
	// bound: a Let or a rewrite since then respelled it, and the parts
	// are of the current text.
	content := a.cur.Goal.Hyp(whole.handle.resolveOrPanic("Conjuncts", a.cur))
	parts := FactConjuncts(content)
	if len(parts) < 2 {
		panic(fmt.Sprintf("Argument.Conjuncts: %s is not a conjunction%s%s", clipRunes(ext.PrintTerm(content), 80),
			readingNote(content), unsuppliedGuardNote(a.cur, content)))
	}
	if len(labels) != len(parts) {
		listed := make([]string, len(parts))
		for i, part := range parts {
			listed[i] = fmt.Sprintf("\n  %d. %s", i+1, clipRunes(ext.PrintTerm(part), 120))
		}
		panic(fmt.Sprintf("Argument.Conjuncts: the fact has %d conjuncts and %d label(s) were given — one per conjunct, in order; "+
			"the conjuncts as the fact states them (a cited instance is handed over in the instance normal form, so a "+
			"projection of a packed value is computed here):%s", len(parts), len(labels), strings.Join(listed, "")))
	}
	// A conjunct that is the goal's conclusion is refused: the author
	// wanted the whole fact there, not its part.
	for i, part := range parts {
		if a.cur.Goal.Conclusion().AlphaEquals(part) {
			panic(fmt.Sprintf("Argument.Conjuncts: conjunct %d, %q, is the goal's conclusion — close with By(f) instead of splitting",
				i+1, labels[i]))
		}
	}
	// A conjunct already resident when its turn comes — a hypothesis
	// α-equal to it, held before the split or installed by an earlier
	// conjunct of it — is bound to that hypothesis, and nothing is
	// asserted for it; every other conjunct is a Have.
	out := make([]Fact, len(parts))
	for i, part := range parts {
		if !a.cur.Goal.AnyHyp(part.AlphaEquals) {
			out[i] = a.Have(labels[i], prop.MakeProp(part), engineShaped(By(Normalized, whole)))
			continue
		}
		idx, err := alphaHypIndex(a.cur.Goal, part)
		if err != nil {
			panic(fmt.Sprintf("Argument.Conjuncts: conjunct %d, %q: %v", i+1, labels[i], err))
		}
		h := NewHypHandle(labels[i])
		h.bindTo(a.cur, a.cur.Goal.Hyp(idx))
		out[i] = residentFact(h)
	}
	return out
}

// FactConjuncts is the flat conjuncts Conjuncts splits t into: a
// conjunction's own, or — where t is a membership in a set-builder and
// no conjunction as written — its reading's (tactic.ReadAsShape), each
// closed from t by the membership reading the By closer makes. One
// element, t, where neither is a conjunction. The session's
// `split_conj {hyp_index}` and emit's reading of the record split by it.
func FactConjuncts(t core.Term) []core.Term {
	isAnd := func(u core.Term) bool { _, _, ok := ext.MatchesAND(u); return ok }
	if read := tactic.ReadAsShape(t, isAnd); read != nil {
		return ext.DecomposesAND(read)
	}
	return []core.Term{t}
}

// readingNote names, for a fact a verb could not open, the reading of
// a membership in a set-builder the verb also tried, and the verb that
// opens an ∃ reading; for a set-builder applied to its point, which no
// verb reads, it says so (setBuilderAtPointNote). "" for any other fact.
func readingNote(t core.Term) string {
	read, ok := tactic.MembershipAtomReading(t)
	if !ok {
		return setBuilderAtPointNote(t)
	}
	note := ", nor is its reading " + clipRunes(ext.PrintTerm(read), 80)
	if !ext.MatchesEXISTS(read).IsZero() {
		note += " — an ∃, which Unpack opens"
	}
	return note
}

// setBuilderAtPointNote says, for a fact a verb could not open, that it
// is a set-builder applied to its point, which rewrite opens an
// equation between sets where Funext left that form, and how the
// fact's content is taken where the Funext stays. "" for any other
// fact.
func setBuilderAtPointNote(t core.Term) string {
	if !tactic.SetBuilderAtPoint(t) {
		return ""
	}
	return "\n  The fact is a set-builder applied to its point, the form Funext leaves of an equation between sets, " +
		"and no verb reads that form as the membership it unfolds. Funext is function extensionality; an equation " +
		"between sets is opened by Simp(Fwd(set_basic.Extension)) in place of Funext(), which leaves " +
		"∀x. x ∈ S ⇔ x ∈ T, the memberships every verb and every law of sets reads, or by its two inclusions " +
		"(set_order.SubsetAntisym). Where the Funext stays, state what the membership says and take it from the fact " +
		"by the set driver: Obtain…As(label, \"∃…\", BySets(fact)) for an ∃, Have(label, claim, BySets(fact)) otherwise."
}

// inHand materializes a fact a verb acts on as a hypothesis of the
// spine (inHandHandle, fact.go) and returns it as the resident Fact
// naming it. A resident fact is returned as itself, with nothing
// recorded.
func (a *Argument) inHand(verb string, f any) Fact {
	h := inHandHandle(verb, a.s, a.cur, f)
	a.advance(verb)
	return residentFact(h)
}

// unsuppliedGuardNote names the guard a materialized instance still
// carries at leaf and, clause by clause, what of it the context does not
// supply — a guard is discharged by a fact listed with the instance that
// states it, as written or as a conjunct, never assumed — with, for each
// clause an earlier step rewrote out of the context, that step
// (rewrittenAwayNote). "" when the instance is no implication.
func unsuppliedGuardNote(leaf *GoalStackNode, instance core.Term) string {
	guard, _, ok := ext.MatchesIMPLY(instance)
	if !ok {
		return ""
	}
	note := fmt.Sprintf("\n  the instance is still guarded by %s: a guard is discharged by a fact listed with the instance "+
		"that states it — as written, or as a conjunct — never assumed; state what is missing as a Have first and list it "+
		"(GroupPremises(fact, instance))",
		clipRunes(ext.PrintTerm(guard), 80))
	if leaf == nil {
		return note
	}
	for _, piece := range unsuppliedPieces(leaf.Goal, guard, true, rungOpts{depth: byAssumption, scope: leaf.proofScope}) {
		note += fmt.Sprintf("\n  the context does not supply %s%s", clipRunes(ext.PrintTerm(piece), 80),
			rewrittenAwayNote(leaf, piece))
	}
	return note
}

// Denote is the abbreviation — "write d for ⟨term⟩". A member of the
// deduction vocabulary next to Have, Obtain and Let, and one of the two
// with NO proof obligation: Have introduces a fact that must be proved,
// Obtain unpacks an ∃ that must be shown inhabited, Denote merely gives
// a long term the goal already carries a short name. It performs the
// denote on the spine (every occurrence of the term in the context
// becomes `name`) and returns the defining equation `name = term` as a
// Fact for later premise lists.
//
//	d := a.Denote("d", v.sum(v.at(x, n), v.at(y, n)))
//	a.Show("…", By(d, sum, perm4))
//
// Its sibling Let DEFINES rather than abbreviates: it keeps the goal's
// form and needs no occurrence — reach for it when the name is the
// mathematics ("take w = ‖v‖·u − ‖u‖·v") and for Denote when a term
// the goal spells is to be read as one atom at a ⊥-form close.
//
// The denote leaves the spine in ⊥-FORM: the goal's negated conclusion
// joins the hypotheses, like a SupposeNot. That is the shape the naming
// transform produces (the abbreviation has to reach the conclusion
// too), and it is what the rest of the block then argues in — a
// terminal `Show` closes by refutation.
//
// The term is any TermLike — a text read by a.Term, a typed value, a
// core term — as the verbs' term slots take one.
//
// Panics when the term does not occur in the goal, or when the name is
// already free in it. Both are the point: an abbreviation for something
// that is not there is a stale line of the proof, and it should fail on
// that line.
func (a *Argument) Denote(name string, term TermLike) Fact {
	a.guard("Denote")
	if name == "" {
		panic("Argument.Denote: a name is required — the whole point is that the " +
			"abbreviation is legible (the anonymous form is the engine's own search stage)")
	}
	t := ext.CoreOf(term)
	if t == nil {
		panic(fmt.Sprintf("Argument.Denote(%q): nil term", name))
	}
	name = dsl.IdentifierName(name)
	a.s.Do(a.cur, DenoteTerm(name, t))
	a.advance("Denote")
	_, d := a.defined("Denote", name, t)
	return d
}

// defined is the bookkeeping Denote and Let share once their step has
// run: the name, now a resident free of the goal, is declared in the
// parse scope so later claim texts may speak it (Script.Var is
// idempotent at the same type, loud at a different one), and its
// defining equation is located among the resulting hypotheses — by
// CONTENT rather than by diffing hyp lists, since the step rewrites
// the hyps it touches and "the one new hyp" is not well defined here.
// Returns the name's variable, the handle LetAs adopts at its phantom,
// and the equation as a resident Fact.
func (a *Argument) defined(verb, name string, t core.Term) (*ext.TermWrapper, Fact) {
	v := a.declare(name, t.Type())
	d := ext.Eq(core.Var(core.TermName(name), t.Type()), t)
	for i := range a.cur.Goal.NumHyps() {
		if a.cur.Goal.Hyp(i).Equals(d) {
			h := NewHypHandle(name)
			h.bindTo(a.cur, a.cur.Goal.Hyp(i))
			return v, residentFact(h)
		}
	}
	panic(fmt.Sprintf("Argument.%s(%q): the defining equation is not among the "+
		"resulting hypotheses — %s\n(goal: %s)",
		verb, name, ext.PrintTerm(d), prop.PrintProp(a.cur.Goal)))
}

// Let is the definition — "let w := ⟨term⟩" — Denote's sibling in the
// deduction vocabulary, and like it without a proof obligation. Where
// Denote abbreviates a term the goal already carries and moves the
// spine to ⊥-form, Let defines: the equation `name = term` joins the
// hypotheses, every occurrence of the term in the hypotheses and in the
// conclusion becomes the name, and the goal keeps its form — a fresh name for an object the
// argument is about to build with, whether or not the goal mentions
// it yet. Later claim texts spell the name (it is registered in the
// parse scope at the term's type), and the returned Fact is the
// defining equation, for the premise lists that unfold it. The term is
// any TermLike — a text read by a.Term or a.TermAs, a typed value, a
// core term; LetAs (typed.go) reads the text at a phantom and returns
// the name's typed handle beside the equation.
//
//	w := a.Let("w", a.Term("vsub(vsmul(‖v‖_n, u), vsmul(‖u‖_n, v))"))
//	nonneg := a.Have("the form at w is nonnegative", "&0 ≤ dot⟨n⟩(w, w)", By(DotPosLe.At(…)))
//	… By(w, expand, …)
//
// Block-level naming is the reader's; a closer that needs the term
// read as ONE atom at a leaf still says so with DenotedAs, since a
// resident equation may be unfolded either way by the refuter.
//
// Panics when the name is already free in the goal.
func (a *Argument) Let(name string, term TermLike) Fact {
	_, d := a.letImpl("Let", name, ext.CoreOf(term))
	return d
}

// letImpl is the body of Let and LetAs: the LetTerm step, then the
// name declared and its equation located (defined). The name is the
// identifier a claim text reads it as (§"Surface names"). Returns the
// name's variable beside the equation, for LetAs to adopt at its
// phantom.
func (a *Argument) letImpl(verb, name string, t core.Term) (*ext.TermWrapper, Fact) {
	a.guard(verb)
	if name == "" {
		panic(fmt.Sprintf("Argument.%s: a name is required — the definition is for the reader", verb))
	}
	if t == nil {
		panic(fmt.Sprintf("Argument.%s(%q): nil term", verb, name))
	}
	name = dsl.IdentifierName(name)
	a.s.Do(a.cur, LetTerm(name, t))
	a.advance(verb)
	return a.defined(verb, name, t)
}

// Show is the labeled terminal close — "hence G ∎". The actions
// (typically one By) must fully close the remaining goal.
func (a *Argument) Show(label string, proof ...Action) {
	a.guard("Show")
	func() {
		defer func() {
			if r := recover(); r != nil {
				panic(fmt.Sprintf("Argument.Show(%q): %v", label, r))
			}
		}()
		for _, act := range proof {
			act.applyAction(a.s, a.cur)
		}
	}()
	if leaves := a.cur.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("Argument.Show(%q): did not close the goal (%d unsolved leaf(ves))", label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(a.withAliasLegend(msg))
	}
	a.closed = true
}

// Obtain is ∃-elimination — "obtain w such that P(w), because label:
// proof". The claim must be an ∃-statement; Obtain proves it (like
// Have), then Skolemizes it on the spine (one StripQuantAt at the hyp
// the assert added), DECLARES the minted witness name in the parse
// scope for the rest of the block (so later claim texts may spell it),
// and returns the witness term plus the instantiated fact. The label
// states why the witness exists — the same obligation Have's label
// carries.
func (a *Argument) Obtain(label string, claim any, proof ...Action) (*ext.TermWrapper, Fact) {
	ws, f := a.obtainN("Obtain", 1, label, claim, proof)
	return ws[0], f
}

// Named names the witnesses an Obtain verb of any arity mints, as
// Unpack's trailing names and Fix's name do: one surface
// spelling per witness, strict (a name that already means something is
// refused), all or none. It rides in the proof list — the verbs' one
// variadic slot — and is not a step:
//
//	r0, radius := c.ObtainAs[Real]("w gives x a ball of radius r₀ inside it",
//	    "∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ w", By(open.At(x), inW), Named("r₀"))
//
// Without it the witness is spelled by the claim's own binder where
// that name is free in the block and by the engine's subscripted form
// otherwise — a choice the file cannot show.
func Named(names ...string) Action { return witnessNames{names} }

type witnessNames struct{ names []string }

func (witnessNames) applyAction(*Script, *GoalStackNode) {
	panic("Named(…) names the witnesses of an Obtain and is not a step — it belongs in an Obtain's proof list only")
}

// splitWitnessNames takes the Named marker out of an Obtain's proof
// list: the steps that remain, and the checked surface names (none
// where no marker was given).
func splitWitnessNames(verb string, n int, proof []Action) ([]Action, []string) {
	var steps []Action
	var names []string
	seen := false
	for _, st := range proof {
		if w, ok := st.(witnessNames); ok {
			if seen {
				panic(fmt.Sprintf("Argument.%s: Named(…) given twice — name every witness in one marker", verb))
			}
			seen = true
			names = w.names
			continue
		}
		steps = append(steps, st)
	}
	return steps, unpackNames(verb, n, names)
}

// Obtain2 is Obtain for a two-witness ∃∃-claim.
func (a *Argument) Obtain2(label string, claim any, proof ...Action) (*ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, f := a.obtainN("Obtain2", 2, label, claim, proof)
	return ws[0], ws[1], f
}

// Obtain3 is Obtain for a three-witness ∃∃∃-claim.
func (a *Argument) Obtain3(label string, claim any, proof ...Action) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, f := a.obtainN("Obtain3", 3, label, claim, proof)
	return ws[0], ws[1], ws[2], f
}

// Obtain4 is Obtain for a four-witness claim.
func (a *Argument) Obtain4(
	label string, claim any, proof ...Action,
) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, f := a.obtainN("Obtain4", 4, label, claim, proof)
	return ws[0], ws[1], ws[2], ws[3], f
}

// Obtain5 is Obtain for a five-witness claim.
func (a *Argument) Obtain5(
	label string, claim any, proof ...Action,
) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, f := a.obtainN("Obtain5", 5, label, claim, proof)
	return ws[0], ws[1], ws[2], ws[3], ws[4], f
}

// ObtainChosen is ∃-elimination by CHOICE rather than by fresh name:
// "let d be THE chosen witness — εd.P(d) — then P holds of it." Obtain's
// sibling for the argument that must keep speaking about the canonical
// ε-term, because sibling statements or the section's own goal spell
// that term — a minted Skolem would not connect to them.
//
// `exists` (text or Prop, like Have's claim) is the single-∃ statement
// `∃d. P(d)` whose choice the argument realizes. The CHOSEN fact
// P(εd.P(d)) is COMPUTED from it — the author never hand-substitutes
// the ε-term into the body, which removes the ε-spelling drift class —
// then asserted and closed from the given premises by a By under an
// implicit HilbertDenoted shaping (the ε-realization close; further
// shaping values among the premises merge, exactly as in a By):
//
//	eps, gapEq := a.ObtainChosen(
//	    "x ≤ y realizes the gap's choice set (LessEqExists)",
//	    "∃d:hreal. y₀ = x₀ + d",
//	    le, nn.LessEqExists)
//
// The label states why the choice set is inhabited — the same
// obligation Obtain's label carries. The ∃ itself never becomes a
// resident fact: the realization consumes it inside the claim branch,
// and what joins the spine is P(εd.P(d)), returned as a Fact alongside
// the ε-term for later premise lists and term building.
func (a *Argument) ObtainChosen(label string, exists any, premises ...any) (*ext.TermWrapper, Fact) {
	a.guard("ObtainChosen")
	cl := a.propOf("ObtainChosen", exists)
	if cl.NumHyps() != 0 {
		panic(fmt.Sprintf("Argument.ObtainChosen(%q): the ∃-statement must be hyp-free "+
			"(got a sequent):\n%s", label, prop.PrintProp(cl)))
	}
	abs := ext.MatchesEXISTS(cl.Conclusion())
	if abs.IsZero() {
		panic(fmt.Sprintf("Argument.ObtainChosen(%q): the statement has no leading ∃ — "+
			"the chosen fact is computed from `∃d. P(d)`:\n%s", label, prop.PrintProp(cl)))
	}
	if len(premises) == 0 {
		panic(fmt.Sprintf("Argument.ObtainChosen(%q): premises required — the label's "+
			"inhabitation argument is the By premise list", label))
	}
	v, body := abs.Var(), abs.Body()
	eps := ext.WrapTerm(v).SuchThat(body)
	chosen := core.MakeProp(body.Substitute(core.MakeTermSubst(v, eps.Core())))
	if a.cur.Goal.Conclusion().AlphaEquals(chosen.Conclusion()) {
		panic(fmt.Sprintf("Argument.ObtainChosen(%q): the goal is the chosen fact itself, P(εd. P(d)) — "+
			"there is nothing for it to join as a hypothesis. Close the goal with "+
			"Show(%q, By(HilbertDenoted, <the same premises>)): that By is the realization "+
			"ObtainChosen runs.\n  goal: %s", label, label, prop.PrintProp(a.cur.Goal)))
	}

	before := a.cur.Goal
	byPremises := append([]any{HilbertDenoted}, premises...)
	a.s.Do(a.cur, AssertStep(chosen,
		MakeCase("chosen: "+label, engineShaped(By(byPremises...))),
		MakeCase("continue: the chosen fact joins the goal's hyps"),
	))
	Assert(len(a.cur.children) == 2)
	claimChild, residual := a.cur.children[0], a.cur.children[1]
	if leaves := claimChild.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("Argument.ObtainChosen(%q): realization left the claim open (%d unsolved leaf(ves))", label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(msg)
	}
	a.cur = residual
	return eps, a.bindNewHyp("ObtainChosen", label, before)
}

// Unpack is ∃-elimination on a fact that is ALREADY established —
// "write f as P(w) for some w". Obtain's sibling for the ∃ you did not
// have to prove: an assumed premise, a branch hypothesis, a fact an
// earlier Have produced — or an established THEOREM. Same
// Skolemization, same ParseScope registration, no claim and no proof.
//
// The step recorded is StripQuantAt at the hypothesis the target
// resolved to: the elimination reads the factorial, not the goal's shape,
// so a ∀-prefix still standing on the conclusion is not stripped and
// no other ∃-hyp is opened.
//
// The target is a premise as a By list reads one (premiseFact), or a
// value carrying evidence. A resident fact is
// Skolemized in place. A NAMED fact (entry var, cert, sibling
// section) is first brought into the context — the Cite verb's
// preserving install, or its ground instance when the fact is
// `At(dep, w…)` — and then Skolemized the same way:
//
//	h, laws := a.Unpack(RealHrealLemma2)          // ∃-headed theorem
//	n, bound := a.Unpack(At(HrealComplete, s))    // ∀-theorem's ∃-instance
//
// This is the naming path for the resident a `Cite(X) + StripQuant()`
// pair leaves ANONYMOUS: the instance comes back as a Fact that
// later premise lists cite by value, instead of a hypothesis only a
// machine-text a.Hyp could re-find.
//
// The witness the goal ends up carrying is named off the RESIDENT
// hypothesis's ∃-binder, subscripted (`∃w. …` Skolemizes to `w₀`) —
// never off the text a caller used to FIND the fact, since a.Hyp
// matches α-equivalently and its binder spellings carry no weight.
// So a comment naming the witness is a claim about the fact's own
// spelling: unfolding a definition whose binder is `w` puts `w₀` in
// the goal however the a.Hyp locating it was written.
//
// A trailing name makes the witness's spelling the author's, exactly as
// Fix("u") does for a ∀: `a.Unpack(fact, "a")` binds `a` as the one
// surface name for the minted witness — loud when `a` already means
// something — and offers none of the binder's own. It is the road to a
// readable name where two facts share a binder (two memberships of one
// set read off its definition both say `∃c`, and the second witness
// would otherwise be spellable only by its mint). The machine layer is
// untouched: the mint, the instance and every key are the unnamed
// Unpack's. Obtain is not that road — it PROVES its claim, and a claim
// α-equal to a resident hypothesis is refused by the assert.
//
// A fact headed by ∃! is opened at its definition: `∃!x. P(x)` hands
// over its witness c with `∀y. P(y) ⇔ c = y`, the fact unfolded at ∃!
// and then unpacked.
func (a *Argument) Unpack(target any, name ...string) (*ext.TermWrapper, Fact) {
	ws, out := a.unpackN("Unpack", 1, target, name)
	return ws[0], out
}

// Unpack2 is Unpack for a two-witness ∃∃-fact; names, when given, are
// both witnesses' spellings, in the fact's binder order.
func (a *Argument) Unpack2(target any, names ...string) (*ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, out := a.unpackN("Unpack2", 2, target, names)
	return ws[0], ws[1], out
}

// Unpack3 is Unpack for a three-witness ∃∃∃-fact; names as Unpack2's.
func (a *Argument) Unpack3(target any, names ...string) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, out := a.unpackN("Unpack3", 3, target, names)
	return ws[0], ws[1], ws[2], out
}

// Unpack4 is Unpack for a four-witness fact; names as Unpack2's.
func (a *Argument) Unpack4(
	target any, names ...string,
) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, out := a.unpackN("Unpack4", 4, target, names)
	return ws[0], ws[1], ws[2], ws[3], out
}

// Unpack5 is Unpack for a five-witness fact; names as Unpack2's.
func (a *Argument) Unpack5(
	target any, names ...string,
) (*ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper, Fact) {
	ws, out := a.unpackN("Unpack5", 5, target, names)
	return ws[0], ws[1], ws[2], ws[3], ws[4], out
}

func (a *Argument) unpackN(verb string, n int, target any, names []string) ([]*ext.TermWrapper, Fact) {
	a.guard(verb)
	surfaces := unpackNames(verb, n, names)
	for _, name := range surfaces {
		a.assertSpellingFree(verb, name)
	}
	var f Fact
	if carrier, ok := target.(_EvidenceCarrier); ok {
		f = a.inHand(verb, carrier)
	} else {
		f = premiseFact(target)
		switch {
		case f.claim != nil:
			panic(fmt.Sprintf("Argument.%s: a self-proving premise is the ground fact it claims — "+
				"there is no ∃ to unpack", verb))
		case f.handle == nil && f.residentContent == nil:
			f = a.installForUnpack(verb, f)
		case len(f.witnesses) > 0 || f.residentContent != nil || len(f.named) > 0 || f.coefficient != nil || len(f.listed) > 0:
			f = a.inHand(verb, f)
		}
	}
	idx := f.handle.resolveOrPanic(verb, a.cur)
	hyp := a.cur.Goal.Hyp(idx)
	// A fact headed by ∃! is opened at its definition, the ∃ of the
	// one witness: Unfolded's Have, and the witness's fact is that the
	// body holds of exactly it.
	if n == 1 && !ext.MatchesUNIQUE(hyp).IsZero() {
		f = a.Unfolded(f, uniqueExistence)
		idx = f.handle.resolveOrPanic(verb, a.cur)
		hyp = a.cur.Goal.Hyp(idx)
	}
	// A membership in a set-builder whose reading is an ∃ is opened
	// through that reading, as the strip reads it
	// (tactic.StripQuantAtTactic).
	opened := hyp
	if read := tactic.ReadAsShape(hyp, func(t core.Term) bool { return !ext.MatchesEXISTS(t).IsZero() }); read != nil {
		opened = read
	}
	binders, err := leadingExistentials(opened, n)
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: %v\n(hyp: %s)%s%s", verb, err, ext.PrintTerm(hyp),
			setBuilderAtPointNote(hyp), unsuppliedGuardNote(a.cur, hyp)))
	}
	return a.skolemizeSpine(verb, binders, idx, surfaces)
}

// unpackNames checks the Unpack verbs' optional surface names: none, or
// one per witness, each non-empty and distinct — a partial list or an
// explicit "" would silently mean the automatic path for some witness,
// exactly the ambiguity the argument exists to remove.
func unpackNames(verb string, n int, names []string) []string {
	if len(names) == 0 {
		return nil
	}
	if len(names) != n {
		panic(fmt.Sprintf("Argument.%s: %d surface name(s) for %d witness(es) — name every witness or none", verb, len(names), n))
	}
	seen := map[string]bool{}
	for _, name := range names {
		if name == "" {
			panic("Argument." + verb + ": surface name must be non-empty (omit the names for the automatic spelling)")
		}
		if seen[name] {
			panic(fmt.Sprintf("Argument.%s: surface name %q given twice", verb, name))
		}
		seen[name] = true
	}
	return names
}

// installForUnpack brings a NAMED fact into the context so unpackN's
// shared Skolemization can eliminate its ∃, and advances the spine onto
// the install's residual leaf. The install itself is the Fact layer's
// shared one (fact.go's installFactResident — the Cite verb's path), so
// `Unpack(At(dep, w…))` and `At(dep, w…)` in a By denote the same ground
// fact, witness order included.
func (a *Argument) installForUnpack(verb string, f Fact) Fact {
	// The stated form keeps its existential where the author wrote it —
	// under a disjunction (`(∃n. A) ∨ (∃n. B)`), a guard, a conjunction.
	// Unpack wants it in front. Where the stated matrix is not ∃-headed
	// but the prenex normal form is, the prenex form is what installs:
	// the same fact, its ∃ hoisted.
	if prenex := prenexForUnpack(a.s, f); prenex != nil {
		f.target = prenex // the same witnesses ground the prenex form
	}
	f, listed := f.materializeListed("Argument."+verb, a.s, a.cur, nil)
	out := installFactResident("Argument."+verb, a.s, a.cur, f, listed)
	a.advance(verb)
	return out
}

// prenexForUnpack returns the normalized form of a named fact when its
// stated matrix (binders and guards peeled) is not ∃-headed while the
// normalized matrix is; nil otherwise (the stated form serves).
func prenexForUnpack(s *Script, f Fact) Prop {
	if f.handle != nil || f.claim != nil {
		return nil
	}
	stated := resolveLemmaTarget("Argument.Unpack", s, f.target)
	if stated == nil || stated.NumHyps() > 0 {
		return nil
	}
	_, matrix := ematch.StripGuardedForalls(stated.Conclusion())
	for {
		_, rest, ok := ext.MatchesIMPLY(matrix)
		if !ok {
			break
		}
		matrix = rest
	}
	if !ext.MatchesEXISTS(matrix).IsZero() {
		return nil
	}
	thm, ok := stated.(Thm)
	if !ok {
		return nil
	}
	norm := s.NormalizedThm(thm)
	_, nmatrix := ematch.StripLeadingForalls(norm.AsProp().Conclusion())
	if ext.MatchesEXISTS(nmatrix).IsZero() {
		return nil
	}
	return norm
}

// maxWitnessArity is the longest ∃-prefix one Obtain or Unpack verb
// opens: Obtain5 and Unpack5.
const maxWitnessArity = 5

// prefixVerbNote says, for an Obtain or Unpack verb that met an
// ∃-prefix of `found` binders where its own arity is another, which verb
// opens that prefix: the strip opens a prefix whole, so the verb is the
// one of the prefix's length. Past maxWitnessArity there is none, and
// the fact is stated with its further witnesses under an inner ∃.
func prefixVerbNote(verb string, found int) string {
	family := strings.TrimRight(verb, "0123456789")
	if found > maxWitnessArity {
		return fmt.Sprintf(" — a leading ∃-prefix opens whole, and no %s verb opens more than %d witnesses: "+
			"state the further witnesses under an inner ∃ and open that in a second step", family, maxWitnessArity)
	}
	fitting := family
	if found > 1 {
		fitting = fmt.Sprintf("%s%d", family, found)
	}
	return fmt.Sprintf(" — a leading ∃-prefix opens whole: %s opens this one", fitting)
}

// leadingExistentials peels n leading ∃-binders off t.
func leadingExistentials(t core.Term, n int) ([]core.VarTerm, error) {
	binders := make([]core.VarTerm, 0, n)
	for i := 0; i < n; i++ {
		abs := ext.MatchesEXISTS(t)
		if abs.IsZero() {
			return nil, fmt.Errorf("only %d leading ∃-binder(s), need %d", i, n)
		}
		binders = append(binders, abs.Var())
		t = abs.Body()
	}
	return binders, nil
}

func (a *Argument) obtainN(verb string, n int, label string, claim any, proof []Action) ([]*ext.TermWrapper, Fact) {
	a.guard(verb)
	cl := a.propOf(verb, claim)
	binders, err := leadingExistentials(cl.Conclusion(), n)
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: claim has %v\n(claim: %s)", verb, err, prop.PrintProp(cl)))
	}

	steps, surfaces := splitWitnessNames(verb, n, proof)
	for _, name := range surfaces {
		a.assertSpellingFree(verb, name)
	}

	// Prove the ∃-fact (the Have half; the ∃-hyp is consumed by the
	// Skolemization right below, so it is not returned).
	before := a.cur.Goal
	a.s.Do(a.cur, AssertStep(cl,
		MakeCase("have: "+label, steps...),
		MakeCase("continue: the fact joins the goal's hyps"),
	))
	Assert(len(a.cur.children) == 2)
	claimChild, residual := a.cur.children[0], a.cur.children[1]
	if leaves := claimChild.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("Argument.%s(%q): proof left the claim open (%d unsolved leaf(ves))", verb, label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(a.withAliasLegend(msg))
	}
	a.cur = residual
	idx, err := newHypIndex(before, a.cur.Goal)
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: cannot identify the asserted ∃-hyp: %v", verb, err))
	}
	if h := a.cur.Goal.Hyp(idx); !h.AlphaEquals(cl.Conclusion()) {
		panic(fmt.Sprintf("Argument.%s: the hyp the assert added is not the claim\n(added: %s)\n(claim: %s)",
			verb, ext.PrintTerm(h), ext.PrintTerm(cl.Conclusion())))
	}
	return a.skolemizeSpine(verb, binders, idx, surfaces)
}

// skolemizeSpine Skolemizes ONE resident ∃-hypothesis (α-equal to
// `source`) on the spine and returns its witnesses plus the instance.
//
// StripQuant is a whole-sequent strip, so the shared guard is that it
// touched exactly this fact: the conclusion is unchanged, exactly one
// hyp was replaced, and exactly n free variables are new. Anything else
// means a second ∃-hyp was strippable too, and the successor would be
// ambiguous — that fails loudly rather than guessing (the HypHandle
// tracking discipline).
// skolemizeSpine is the ∃-elimination Unpack and Obtain share: the
// hypothesis at idx — the one the handle resolved to, or the one the
// assert just added — has its leading ∃-prefix Skolemized by ONE
// StripQuantAt step, and the witnesses come back in the binders' order:
// the strip says which variable it fixes for which binder
// (tactic.ExistsWitnessesAt), so witness k is binder k's whatever the
// two are named. The step names the hypothesis, so a ∀-prefix still on
// the conclusion and every other ∃-hyp are untouched by construction;
// the sequent diff below only locates the instance.
//
// `surfaces`, when non-nil, holds one author-chosen spelling per binder
// (Unpack's trailing names, checked free before the strip): each is
// bound as that witness's one surface name, and the binder's own
// spellings are not offered.
func (a *Argument) skolemizeSpine(verb string, binders []core.VarTerm, idx int, surfaces []string) ([]*ext.TermWrapper, Fact) {
	n := len(binders)
	names := make([]string, n)
	for i, b := range binders {
		names[i] = string(b.Name())
	}
	freesBefore := sequentFrees(a.cur.Goal)
	goalBefore := a.cur.Goal
	source := goalBefore.Hyp(idx)
	witnesses := tactic.ExistsWitnessesAt(goalBefore, idx, a.s.declaredOtherwise)
	a.s.Do(a.cur, _StripQuant{hypIndex: &idx, refused: a.s.declaredOtherwise})
	a.advance(verb)
	g := a.cur.Goal
	var removed, added []core.Term
	for i := 0; i < goalBefore.NumHyps(); i++ {
		if h := goalBefore.Hyp(i); !goalHasHypAlpha(g, h) {
			removed = append(removed, h)
		}
	}
	for i := 0; i < g.NumHyps(); i++ {
		if h := g.Hyp(i); !goalHasHypAlpha(goalBefore, h) {
			added = append(added, h)
		}
	}
	if len(removed) != 1 || len(added) != 1 || !removed[0].AlphaEquals(source) {
		panic(fmt.Sprintf("Argument.%s: StripQuantAt(%d) must replace exactly the ∃-hyp it names by one new instance hyp "+
			"(%d hyp(s) removed, %d added — an instance α-equal to a resident hyp collapses into it)\n(hyp: %s)",
			verb, idx, len(removed), len(added), ext.PrintTerm(source)))
	}

	// The strip fixes one variable per binder of the whole leading
	// ∃-prefix, and each is new to the sequent: a prefix longer than the
	// verb's arity, or a binder its body does not mention, is refused
	// here.
	minted := newFreeVars(freesBefore, g)
	if len(witnesses) != n {
		panic(fmt.Sprintf("Argument.%s: expected %d minted witness(es), found %d%s\n(instance hyp: %s)",
			verb, n, len(witnesses), prefixVerbNote(verb, len(witnesses)), ext.PrintTerm(added[0])))
	}
	if len(minted) != n {
		panic(fmt.Sprintf("Argument.%s: the fact binds %d witness(es) and its body mentions %d of them — "+
			"a binder the body does not mention fixes no variable of the instance\n(instance hyp: %s)",
			verb, n, len(minted), ext.PrintTerm(added[0])))
	}
	out := make([]*ext.TermWrapper, n)
	for i, b := range binders {
		base := string(b.Name())
		match := witnesses[i]
		Assert(match.Type().Equals(b.Type()))
		Assert(slices.ContainsFunc(minted, func(v core.VarTerm) bool { return freeVarKey(v) == freeVarKey(match) }))
		// Declare it in the parse scope for this block (declare) so later
		// claim texts resolve the Skolem by name, and — unless the author
		// named it (surfaces) — OFFER the ∃-binder's own name, plus its
		// rename-inverted base when a resident hyp's binder was already
		// α-renamed, as the block's surface names for it (§"Surface
		// names"; taken names are skipped, never re-pointed).
		if surfaces != nil {
			a.bindSurface(surfaces[i], match)
		} else {
			a.bindSurfaceIfFree(base, match)
			if stripped := SurfaceBase(base); stripped != base {
				a.bindSurfaceIfFree(stripped, match)
			}
		}
		out[i] = a.declare(string(match.Name()), match.Type())
	}

	h := NewHypHandle("obtained " + strings.Join(names, ", "))
	h.bindTo(a.cur, added[0])
	return out, residentFact(h)
}

// Assume is ⇒-introduction — "assume H". Moves the implication's
// antecedent into the hypotheses and returns it as a Fact.
func (a *Argument) Assume() Fact {
	a.guard("Assume")
	before := a.cur.Goal
	a.s.Do(a.cur, StripImp())
	a.advance("Assume")
	return a.bindNewHyp("Assume", "assumption", before)
}

// SupposeNot enters a proof by contradiction — "suppose not": the goal
// G becomes ⊥ with ¬G resident, returned as a Fact.
func (a *Argument) SupposeNot() Fact {
	a.guard("SupposeNot")
	before := a.cur.Goal
	a.s.Do(a.cur, ByContra())
	a.advance("SupposeNot")
	return a.bindNewHyp("SupposeNot", "¬goal", before)
}

// Hyp names an already-resident hypothesis — an assumed premise or a
// branch hyp — so premise lists can cite it. content is a statement
// string, a Statement in parts, a Prop, or a Term; located by
// α-equality, loud on no/ambiguous match.
func (a *Argument) Hyp(content any) Fact {
	a.guardRead("Hyp")
	var t core.Term
	switch c := content.(type) {
	case string, dsl.Statement, *dsl.Statement:
		t = a.propOf("Hyp", c).Conclusion()
	case Prop:
		t = c.AsProp().Conclusion()
	case core.Term:
		t = c
	case TermLike:
		t = c.Core()
	default:
		panic(fmt.Sprintf("Argument.Hyp: content must be a statement string, a Statement in parts, a Prop or a Term; got %T", content))
	}
	idx, err := findHypIndex(a.cur.Goal, t)
	if err != nil {
		panic(a.withAliasLegend(fmt.Sprintf("Argument.Hyp: %v\n(goal: %s)", err, prop.PrintProp(a.cur.Goal))))
	}
	h := NewHypHandle(ext.PrintTerm(t))
	h.bindTo(a.cur, a.cur.Goal.Hyp(idx))
	return residentFact(h)
}

// Unfolded is a resident fact read by the definition of one constant
// — "h, unfolded" — returned as a new resident Fact beside the folded
// one. The goal and every other hypothesis are untouched: this is the
// Fact-level face of Unfold, where Unfold(d) opens the constant on
// the whole leaf, splits any conjunction the opening leaves in the
// hypotheses, and so ends every handle that pointed into them.
//
//	near := a.Unfolded(converges, RealConvergesToDef)   // the ∀ε statement, as a Fact
//	pOpens := a.Unfolded(isPolynomial, PolynomialFunctionDef)
//	m, c, pSum := a.Unpack2(pOpens)
//
// It records exactly what the hand-written idiom records — a Have whose
// claim is the unfolded statement and whose proof is Unfold(d):
// the claim obligation's Unfold opens the resident copy and the residual
// is the claim itself. The claim is COMPUTED, by the def-expand walker
// the Unfold step runs (dispatchDefExpandRewrite on the fact's content
// alone), so no text restates what the engine holds; the unfolded form
// is one Fact even when it is a conjunction (the halves are a further
// step). d is read as Unfold reads it (unfoldedConstant).
//
// h may be any Fact a context verb accepts: a resident fact is read in
// place, a named one is installed first (residentHandle). Panics,
// naming Unfolded: an inductively-minted constant, a fact the constant
// does not occur in, a definition the walker declines.
func (a *Argument) Unfolded(h any, d Definition) Fact {
	a.guard("Unfolded")
	handle := a.inHand("Unfolded", h).handle
	content := a.cur.Goal.Hyp(handle.resolveOrPanic("Unfolded", a.cur))
	c := unfoldedConstant("Unfolded", d)
	unfolded, err := UnfoldedHypothesis(content, c, libraryRead(a.s.Scope))
	if err != nil {
		panic(a.withAliasLegend(fmt.Sprintf("Argument.Unfolded(%s): %v", c.Name(), err)))
	}
	return a.Have(string(c.Name())+" unfolded", core.MakeProp(unfolded), Unfold(d))
}

// Simplified is a fact rewritten by rules — "h, simplified" — returned
// as the resident fact it becomes. A fact that is not resident (a law
// read at an instance, a named lemma) is installed first, as the context
// verbs install one; it is then rewritten in place, as
// `a.Do(h.Simp(rules…))` rewrites a resident fact. The statement is the
// engine's, so no text restates it: a law grounded at a packed record
// value, a definition among its terms unfolded, states the parts the
// record was packed from (the instance normal form computes the
// projections; prover/tactic, InstanceNormal).
//
//	free := a.Simplified(free_module.FreeModuleOn.At(packed, S), Fwd(free_module.FreeModuleRecordDef))
//
// With no rules h is installed as the engine hands it over, already in
// the instance normal form: a law read at a packed record value states
// its parts with no rule at all.
//
//	sums := a.Simplified(module_homomorphism.HomSum.Read(linear))
//
// It records the install and the rewrite, the two steps the hand-written
// idiom records. Panics as Fact.Simp does when rules are given and none
// fires.
func (a *Argument) Simplified(h any, rules ...SimpRule) Fact {
	a.guard("Simplified")
	fact := a.inHand("Simplified", h)
	if len(rules) > 0 {
		a.Do(fact.Simp(rules...))
	}
	return fact
}

// Fix is ∀-introduction — "let x be arbitrary": strips ONE leading ∀,
// registers the minted Skolem in the ParseScope, binds a surface
// spelling for it (§"Surface names" — later claim texts may spell
// it), and returns it. Bare Fix() offers the goal's own binder name
// (and its α-rename base) as the spelling, skipping either when it is
// taken; Fix("u") makes `u` the one spelling — the road to a readable
// name where the binder's own is unavailable — loud when `u` already
// means something.
func (a *Argument) Fix(name ...string) *ext.TermWrapper {
	surface := fixName("Fix", name)
	if surface != "" {
		a.guard("Fix")
		a.assertSpellingFree("Fix", surface)
	}
	return a.fixImpl(surface)
}

// fixImpl is Fix with an optional caller-supplied surface name, bound
// WITHOUT a freshness check — the section boundary (section.go's
// bindSlot) passes the STATEMENT's binder name, which is authoritative
// over anything resident; the author-facing verbs check first via
// assertSpellingFree. A bare surface derives the spelling from the
// goal's own binder — reading the name before the strip, and inverting
// any earlier strip's α-rename via SurfaceBase (an outer StripQuant1
// renames the binders it substitutes under, so the goal may already
// spell this binder `n₀` where the statement said `n`) — and each
// derived spelling is an OFFER: taken names are skipped, never
// re-pointed (§"One name, one meaning").
func (a *Argument) fixImpl(surface string) *ext.TermWrapper {
	a.guard("Fix")
	binder := ""
	if abs := ext.MatchesFORALL(a.cur.Goal.Conclusion()); !abs.IsZero() {
		binder = string(abs.Var().Name())
	}
	stated := a.cur.Goal
	freesBefore := sequentFrees(stated)
	a.s.Do(a.cur, _StripQuant1{refused: a.s.declaredOtherwise})
	a.advance("Fix")
	// The variable the strip fixed is the one new in the goal it left —
	// or, where the binder is vacuous and its body mentions nothing of
	// it, the one the strip names for that goal (StripQuant1Fixes): such
	// a binder is fixed like any other, and its variable is free in
	// nothing.
	var fixed core.VarTerm
	switch minted := newFreeVars(freesBefore, a.cur.Goal); len(minted) {
	case 1:
		fixed = minted[0]
	case 0:
		fixed, _ = tactic.StripQuant1Fixes(stated, a.s.declaredOtherwise)
	default:
		panic(fmt.Sprintf("Argument.Fix: expected 1 minted variable, found %d", len(minted)))
	}
	if surface != "" {
		a.bindSurface(surface, fixed)
	} else {
		a.bindSurfaceIfFree(binder, fixed)
		if base := SurfaceBase(binder); base != binder {
			a.bindSurfaceIfFree(base, fixed)
		}
	}
	return a.declare(string(fixed.Name()), fixed.Type())
}

// SurfaceBase inverts the engine's rename convention (utils.NextName:
// body + ʹ* + optional _digits) back to the base name — `n_0` (shown
// `n₀`) → `n`, `kʹ` → `k`, `nʹ_1` → `n`. A bare-digit tail (`x2`) is
// NOT stripped: that spelling is an authored name, and the renamer
// only produces it from a base that already ended in a digit — which
// is then unrecoverable anyway. Returns the name unchanged when
// nothing strips.
//
// Exported for the session engine, whose goal-local surface aliases
// (engine/surface_alias.go) invert the same convention.
func SurfaceBase(name string) string {
	i := len(name)
	for i > 0 && '0' <= name[i-1] && name[i-1] <= '9' {
		i--
	}
	s := name
	if i > 0 && i < len(name) && name[i-1] == '_' {
		s = name[:i-1]
	}
	return strings.TrimRight(s, "ʹ")
}

// Take is ∃-introduction — "take B := t": witnesses the goal's leading
// ∃ with the given term. On a leading ∃! it is the introduction of
// unique existence: the goal becomes the body at t together with the
// claim that the body holds of nothing but t, `P(t) ∧ (∀y. P(y) ⇒ y = t)`.
func (a *Argument) Take(w TermLike) {
	a.guard("Take")
	a.s.Do(a.cur, Witness(w.Core()))
	a.advance("Take")
}

// Calc runs a relation chain as a deduction item and RETURNS the fact
// it establishes — rel(from, last leg's term) — for the premise lists
// downstream. The chain itself is CalcRel.Calc (calc.go): each
// leg asserts its own link, and the transitivity groundings are
// computed from the leg terms.
//
// Without this the chain has to run through d.Do and the fact it just
// produced has to be re-found by content, which is exactly the
// bookkeeping the Fact layer exists to remove.
func (a *Argument) Calc(kit CalcRel, from TermLike, legs ...CalcLeg) Fact {
	return a.calc("Calc", kit.Calc(from, legs...), kit.Rel(ext.CoreOf(from), legs[len(legs)-1].to))
}

// CalcOrder is Calc for a mixed order/equivalence chain
// (CalcOrder.Calc). The fact it returns is Le(from, last) when any leg
// travels the order, else Eq(from, last) — the same rule the chain
// folds by.
func (a *Argument) CalcOrder(kit CalcOrder, from TermLike, legs ...CalcLeg) Fact {
	last := legs[len(legs)-1].to
	produced := kit.Eq
	for _, leg := range legs {
		if leg.rel == relLe {
			produced = kit.Le
			break
		}
	}
	return a.calc("CalcOrder", kit.Calc(from, legs...), produced(ext.CoreOf(from), last))
}

// CalcLeibniz is CalcOrder for a chain whose ≈ side is the kernel's own
// equality (CalcOrder.CalcLeibniz). Its produced fact is always the
// order fact when any leg travels the order.
func (a *Argument) CalcLeibniz(kit CalcOrder, from TermLike, legs ...CalcLeg) Fact {
	last := legs[len(legs)-1].to
	le := false
	for _, leg := range legs {
		if leg.rel == relLe {
			le = true
			break
		}
	}
	produced := leibnizEq(ext.CoreOf(from), last)
	if le {
		produced = kit.Le(ext.CoreOf(from), last)
	}
	// CalcLeibniz installs its own Eq builder; run it through the same
	// spine mechanics as the other two.
	return a.calc("CalcLeibniz", kit.CalcLeibniz(from, legs...), produced)
}

// calc runs a chain action on the spine and binds the fact it left
// resident. A chain that ARRIVES at the goal closes the block instead
// (the terminal-chain semantics of calc.go), and there is then
// no fact to return — that spelling belongs in Show, not here.
func (a *Argument) calc(verb string, chain Action, produced Prop) Fact {
	a.guard(verb)
	chain.applyAction(a.s, a.cur)
	if leaves := a.cur.UnsolvedLeaves(); len(leaves) == 0 {
		panic(fmt.Sprintf("Argument.%s: the chain arrived AT the goal and closed the block — "+
			"a terminal chain produces no fact to name; run it inside Show(...) instead", verb))
	}
	a.advance(verb)
	idx, err := findHypIndex(a.cur.Goal, produced.AsProp().Conclusion())
	if err != nil {
		panic(fmt.Sprintf("Argument.%s: cannot find the fact the chain produced (%s): %v",
			verb, ext.PrintTerm(produced.AsProp().Conclusion()), err))
	}
	h := NewHypHandle(verb + " chain")
	h.bindTo(a.cur, a.cur.Goal.Hyp(idx))
	return residentFact(h)
}

// Do is the marked escape hatch: run arbitrary Actions on the spine
// (a goal-surface move with no verb yet). The linearity contract still
// holds — the actions must leave exactly one unsolved leaf, or none at
// all when they close the block outright.
func (a *Argument) Do(actions ...Action) {
	a.guard("Do")
	for _, act := range actions {
		act.applyAction(a.s, a.cur)
	}
	a.advanceOrClose("Do")
}

// ---------------------------------------------------------------------------
// Structure verbs
// ---------------------------------------------------------------------------
//
// The argument's SHAPE — "we prove both directions", "by cases on t",
// "by induction on m" — is as much a paper move as Have or Show, so it
// gets verbs here rather than riding the Do escape hatch. Each desugars
// to the same bare ministep the Chain form used (tree-identical), and
// each may be terminal: when every Case closes its own branch the block
// is closed, and when one branch survives the deduction continues on it.
// The Case labels carry the narrative, which is why these verbs take no
// label of their own.

// The splits themselves — Cases / Induct / Iff and the branch verbs
// that claim their branches by name — are in branch.go: an opener and
// its branches are separate sentences, so a level of case analysis
// costs one indent instead of three.

// Assuming is "we may assume t": boolean case analysis on t whose ¬t
// branch sideBody discharges inline (and must CLOSE — the side-case
// contract of action.go's linearizers), the deduction continuing at
// this level with t resident, returned as a Fact. The engine holds the
// surviving hypothesis, so premise lists take the returned value rather
// than re-spelling it through Hyp — the Given principle. Never
// terminal: the main line always survives.
func (a *Argument) Assuming(t TermLike, label string, sideBody ...Action) Fact {
	_, resident := ByCaseBranch(ext.CoreOf(t), true)
	return a.sideCase("Assuming", ext.PrintTerm(resident),
		Assuming(t, label, sideBody...))
}

// Unless is "the goal is settled when t holds": boolean case analysis
// on t whose branch on which t holds sideBody discharges inline, the
// deduction continuing at this level with t's denial resident — ¬t, or
// p for t = ¬p (ByCaseBranch) — returned as a Fact: Assuming with the
// discharged branch on the other side.
func (a *Argument) Unless(t TermLike, label string, sideBody ...Action) Fact {
	_, resident := ByCaseBranch(ext.CoreOf(t), false)
	return a.sideCase("Unless", ext.PrintTerm(resident),
		Unless(t, label, sideBody...))
}

// sideCase runs a linearizer on the spine and binds the hypothesis the
// surviving branch received, named as that hypothesis prints: the same
// bare ministep as the Action spelling — tree-identical, so recorded
// CNF keys keep hitting — plus a binding, and binding records nothing.
func (a *Argument) sideCase(verb, hypName string, act Action) Fact {
	a.guard(verb)
	before := a.cur.Goal
	act.applyAction(a.s, a.cur)
	a.advance(verb)
	return a.bindNewHyp(verb, hypName, before)
}

// Binder names one of the goal's leading ∀-binders — "where N is the
// bound variable" — registering it in the ParseScope at the type the
// STATEMENT gives it and returning the term. It is not a proof step:
// nothing is stripped and the goal does not move. It exists for the
// bodies that must refer to a binder they are deliberately not
// stripping (an induction variable, whose case bodies need it before
// Induct is even called), and it replaces the `ctx.Var("N", NumType)`
// spelling that had to restate the type and hope it matched.
//
// The name is the STATEMENT'S. Once a closure parameter is bound the
// binders after it may read α-renamed — an outer StripQuant1 renames
// the binders it substitutes under, so the statement's `n` is the
// goal's `n₀` by the time a body runs — and the rename is inverted
// here (SurfaceBase, the same inversion Fix uses for its offered
// spelling): `a.Binder("n")` finds `n_0`, binds `n` as a surface
// spelling so the claim texts can say `n`, and returns the engine's
// variable. A body that spelled the renamed form (`a.Binder("n_0")`,
// or `n₀` as the goal prints it — one identifier, §"Surface names")
// still resolves, by exact match first; a name that several binders
// rename to is refused as ambiguous.
func (a *Argument) Binder(name string) *ext.TermWrapper {
	key := dsl.IdentifierName(name)
	var seen []string
	var renamed []core.VarTerm
	for t := a.cur.Goal.Conclusion(); ; {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		v := abs.Var()
		spelled := string(v.Name())
		if spelled == key {
			return a.declare(key, v.Type())
		}
		if SurfaceBase(spelled) == key {
			renamed = append(renamed, v)
		}
		seen = append(seen, spelled)
		t = abs.Body()
	}
	switch len(renamed) {
	case 0:
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.Binder(%q): the goal has no leading ∀-binder by that name (binders: %v)\n(goal: %s)",
			name, seen, prop.PrintProp(a.cur.Goal))))
	case 1:
		v := renamed[0]
		if how := a.spellingTaken(name, v); how != "" {
			panic(a.withAliasLegend(fmt.Sprintf(
				"Argument.Binder(%q): the goal binds it as %s, and %q is already %s — the statement's name "+
					"cannot be offered for it", name, v.Name(), name, how)))
		}
		a.bindSurface(name, v)
		return a.declare(string(v.Name()), v.Type())
	default:
		names := make([]string, len(renamed))
		for i, v := range renamed {
			names[i] = string(v.Name())
		}
		panic(a.withAliasLegend(fmt.Sprintf(
			"Argument.Binder(%q): %d leading ∀-binders rename to that name (%v) — name the one you mean as the "+
				"goal spells it\n(goal: %s)", name, len(renamed), names, prop.PrintProp(a.cur.Goal))))
	}
}

// Ctx exposes the running Script — the parse scope, dep claiming
// (Dep), numerals and term construction. A Derive body reaches for it
// the same way a Chain body used its `ctx`; it is not an escape hatch,
// just the surrounding proof state the verbs themselves run on.
func (a *Argument) Ctx() *Script { return a.s }

// Goal is what remains to be proved, right here on the spine — a
// READ, not a step: it changes nothing and it is not a verb.
//
// It exists for the solver kits that COMPUTE a proof plan from the
// statement rather than taking premises (quotient.TransportLaw is the
// motivating one: it reads the law's shape off the goal and derives
// the transport cites). Before this accessor such a body had to
// re-parse its own statement text to recover a Prop the Argument was
// already holding, which put the statement in the file twice and
// invited the two copies to drift.
//
// It is NOT the way to inspect the goal and branch on it: that is the
// proof reacting to machine state, which is what the verbs exist to
// keep out of bodies.
func (a *Argument) Goal() Prop {
	a.guardRead("Goal")
	return a.cur.Goal
}

// engineShaped marks a By the prover built with a shape element of its
// own (_ByAction.engineShape).
func engineShaped(a Action) Action {
	b := a.(_ByAction)
	b.engineShape = true
	return b
}
