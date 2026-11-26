// action.go — the unified Prove API. The umbrella Action interface
// (defined here) is satisfied by every concrete Step (atomic, step.go)
// and every concrete Macro (compound, macro.go) via an applyAction
// method; callers pass any mix of them directly into ctx.Prove(...)
// instead of the older three-line `Section + chain + ClaimProved`
// ceremony. Note the three-layer vocabulary: Step (atomic) and Macro
// (compound) are the two real execution layers; Action is the interface
// that abstracts over both at the call site.
//
// Cite (the fused Lemma + KnownThm idiom that emit has been producing
// into corpus files) lifts here from emit text into a runtime Action
// value. The companion fused Rewrite(d, c) is intentionally NOT added
// at the package level in this step — it would collide with the
// existing no-arg Rewrite() Step constructor; the *GoalStackNode
// method Rewrite(d, c) continues to handle that idiom for fluent-chain
// callers. Resolution moves into a later step once the v1 Action API has
// shaken out.
//
// Multi-residual Step wrapping via Case(label, body...) is the next
// step in the rollout (// section, implementation order step 3). Action bodies that need
// case-local naming (induction hypothesis, witnessed variables) arrive
// alongside Case via WithIH / WithWitness / WithHyp closure helpers.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Action is the umbrella value type for the Prove API: a single unit of
// proof work applied to a section's first unsolved leaf. Every concrete
// Step (atomic) and Macro (compound) satisfies Action, so any Step /
// Macro constructor can be passed directly into ctx.Prove(...).
//
// Action composes via Chain(steps...) and is the body shape passed to
// Case branches of multi-residual Steps.
type Action interface {
	applyAction(s *Script, root *GoalStackNode)
}

// Chain composes multiple Actions into one. Primarily used inside Case
// bodies that hold a single Action argument; at the top-level Prove
// call site the variadic `...Action` already handles sequencing.
func Chain(steps ...Action) Action { return _ChainAction{steps} }

// DenoteRefute is the standard denote-close of the ε-heavy arguments:
// Denote(size) turns the large ground terms (ε-gap sums, iterated pair
// projections) into stable opaque atoms, Basic() clause-forms the
// residual, and CnfRefute() finishes. A hand-written leaf that closes
// this way keeps its reasons to stay hand-written (chartered per-leg
// labels, mid-close Arith); the name says "this is the standard
// denote-close" once instead of at every site. Pure Chain sugar —
// tree-identical to spelling the three steps, so a retrofit moves no
// recorded CNF key. (Inside a By the same stage is the Denoted(size)
// shaping value, which is the preferred, premise-disciplined form.)
// The size is optional and defaults to the engine's own threshold;
// see Denote.
//
// SEARCH form, excluded from the bare-name surface (library/authoring)
// alongside Denote / Denoted. The authoring form is DenoteRefuteAs.
func DenoteRefute(size ...int) Action { return Chain(Denote(size...), Basic(), CnfRefute()) }

// DenoteRefuteAs is the EXPLICIT denote-close: name `term` by `name`,
// clause-form the residual, refute.
//
//	DenoteRefuteAs("gap", v.eps_gap(x, y))
//
// Same three steps as DenoteRefute, with the abbreviation on the page
// instead of a size threshold. Pure Chain sugar — tree-identical to
// spelling DenoteTerm + Basic + CnfRefute.
func DenoteRefuteAs(name string, term TermLike) Action {
	return Chain(DenoteTerm(name, ext.CoreOf(term)), Basic(), CnfRefute())
}

// HilbertDenoteRefuteAs is DenoteRefuteAs for an ε-term — the explicit
// form of the `HilbertDenote(), Basic(), CnfRefute()` close.
func HilbertDenoteRefuteAs(name string, term TermLike) Action {
	return Chain(HilbertDenoteTerm(name, ext.CoreOf(term)), Basic(), CnfRefute())
}

type _ChainAction struct{ steps []Action }

func (c _ChainAction) applyAction(s *Script, root *GoalStackNode) {
	for _, step := range c.steps {
		step.applyAction(s, root)
	}
}

// Case is one labeled branch of a multi-residual ministep
// (SplitConj / SplitDisj / SplitIff / SplitHypIff / SplitHypImply /
// ByCaseStep / InductStep / raw Lemma / AssertStep). Case is a
// distinct value type from Step so the type system rejects Case
// appearing outside a case-eligible parent ministep constructor.
//
// The label is display-only — the runtime dispatches positionally,
// matching kernel subgoal order. The body is a sequence of Steps
// applied against the corresponding child subgoal.
type Case struct {
	Label string
	Body  []Action
}

// MakeCase constructs a Case value. Variadic body matches the call
// shape inside multi-residual ministep constructors:
//
//	SplitConj(
//	    Case("left: ⊢ A", CiteKnown(p.lemmaA)),
//	    Case("right: ⊢ B", CiteKnown(p.lemmaB)),
//	)
//
// (Constructor name is `MakeCase` because plain `Case` is the type;
// a proof file writes the bare name `Case`, which library/authoring
// declares for it.)
func MakeCase(label string, body ...Action) Case {
	return Case{Label: label, Body: body}
}

// caseCarrier is the unexported interface satisfied by every
// case-eligible ministep struct that carries a (possibly empty)
// `cases []Case` field. Script.Do uses it to detect Case-bearing
// ministep values and dispatch each Case body against its subgoal
// after runStep produces children.
type caseCarrier interface {
	caseBodies() []Case
}

// dispatchCases is the shared post-runStep dispatch loop. After
// `leaf` has children, walk each Case body against the matching
// child positionally. The Case label is display-only and is NOT
// checked for alpha-equality with the subgoal prop in this v1 — a
// future debug-flag may add the check. step is the ministep that
// produced the children, named where the counts disagree.
func dispatchCases(s *Script, leaf *GoalStackNode, step _Step, cases []Case) {
	if len(cases) == 0 {
		return
	}
	if len(cases) != len(leaf.children) {
		msg := fmt.Sprintf("Step.dispatchCases: %d Case body(ies) provided but %v produced %d subgoal(s)",
			len(cases), step, len(leaf.children))
		if _, binary := step.(_SplitConj); binary {
			msg += "\n  SplitConj splits the conclusion at its outermost ∧, in two, however many conjuncts it has " +
				"(and gives one subgoal for A ∧ A); SplitConjAll gives one subgoal per conjunct of the whole ∧-spine."
		}
		msg += "\n  the subgoals:"
		for _, child := range leaf.children {
			msg += "\n    " + prop.PrintProp(child.Goal)
		}
		panic(msg)
	}
	for i, c := range cases {
		sub := leaf.children[i]
		for _, step := range c.Body {
			step.applyAction(s, sub)
		}
	}
}

// ---------------------------------------------------------------------------
// Structured fan-out combinators: Expect / Finally
// ---------------------------------------------------------------------------
//
// Chain binds each Action to "the leftmost unsolved leaf at the moment
// it runs" — a temporal binding that carries no tree structure in the
// script text: the reader must simulate the goal stack to know which
// leaf a step targets, and a fan-out drift upstream silently rebinds
// every later step. dispatchCases fixes this for the nine explicit
// case-eligible ministeps; Expect and Finally extend the same
// discipline to EVERY Action, including auto-splitting ones (Basic's
// iff split, HilbertDenote's ε split) that take no Case arguments.
//
// Both are Script-layer drivers over the existing dispatch: they apply
// the same macros to the same leaves in the same order as the working
// flat-chain spelling (provided each Case body closes its leaf, which a
// working flat tail already did), so converting a flat tail changes
// neither the proof tree nor the CNF goal-key trajectory — recorded
// .cnf.pb blobs keep hitting.

// Expect is the generalized THENL: run `action` at the current leftmost
// unsolved leaf, require the subtree it worked on to be left with
// EXACTLY len(cases) unsolved leaves, and dispatch each Case body
// against its leaf positionally (preorder — leaves may sit at different
// depths when `action` is a Chain of splits). A count mismatch panics
// with both the Case labels and the actual leaf goals printed.
//
// The exact-count contract includes zero: Expect(action) with no cases
// asserts that `action` fully closes the leaf it runs on.
func Expect(action Action, cases ...Case) Action { return _ExpectAction{action, cases} }

type _ExpectAction struct {
	action Action
	cases  []Case
}

func (e _ExpectAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("Expect: focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	// The action (and everything it chains) is scoped to the anchor's
	// subtree — it cannot escape onto sibling goals.
	e.action.applyAction(s, anchor)
	leaves := anchor.UnsolvedLeaves()
	if len(leaves) != len(e.cases) {
		msg := fmt.Sprintf("Expect: %d Case body(ies) provided but the action left %d unsolved leaf(ves)",
			len(e.cases), len(leaves))
		for i, c := range e.cases {
			msg += fmt.Sprintf("\n  case %d: %s", i, c.Label)
		}
		for i, l := range leaves {
			msg += fmt.Sprintf("\n  leaf %d: %s", i, prop.PrintProp(l.Goal))
		}
		panic(msg)
	}
	for i, c := range e.cases {
		sub := leaves[i]
		for _, step := range c.Body {
			step.applyAction(s, sub)
		}
	}
}

// Finally is the broadcast terminator (THEN restricted to closing):
// apply `action` separately to every remaining unsolved leaf under the
// focus (leftmost-first) and require each application to CLOSE its
// leaf. Replaces N copy-pasted closing calls — whose count silently
// encodes the engine's fan-out — with one line that says "everything
// left closes this way" and is robust to fan-out drift.
func Finally(action Action) Action { return _FinallyAction{action} }

type _FinallyAction struct{ action Action }

func (f _FinallyAction) applyAction(s *Script, root *GoalStackNode) {
	leaves := root.UnsolvedLeaves()
	if len(leaves) == 0 {
		panic("Finally: focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	for i, leaf := range leaves {
		f.action.applyAction(s, leaf)
		if !leaf.Proved() {
			panic(fmt.Sprintf("Finally: broadcast action did not close leaf %d/%d\n  leaf goal: %s",
				i+1, len(leaves), prop.PrintProp(leaf.Goal)))
		}
	}
}

// CloseIfOpen runs `action` on the focus only when an unsolved leaf
// remains, and is a no-op when the preceding steps already closed it.
//
// It exists for the LADDER GENERATORS (quotient.Transporter and
// friends), where whether the last cite closes the goal by itself is a
// property of the individual statement pair, not of the ladder's shape
// — so a hand-written "does it close?" flag is the author predicting
// the goal state, the same class the Cite consolidation absorbed by
// reading it off instead. Wrapping the terminator makes the generated
// ladder tree-identical to the correctly-flagged hand spelling in both
// cases: an open leaf gets the closer, a closed one gets nothing.
//
// It is deliberately NOT a general "try to close" escape hatch: it
// hides no failure, because a leaf the action fails to close is still
// open and the section's Qed still fails.
func CloseIfOpen(action Action) Action { return _CloseIfOpenAction{action} }

type _CloseIfOpenAction struct{ action Action }

func (c _CloseIfOpenAction) applyAction(s *Script, root *GoalStackNode) {
	if root.unsolvedLeaf(0) == nil {
		return
	}
	c.action.applyAction(s, root)
}

// ---------------------------------------------------------------------------
// Sequential-fact combinators: Deduce / Have / Show
// ---------------------------------------------------------------------------
//
// AssertStep's claim/after Case pair is binary: establishing k facts in
// order nests k AssertSteps in the "after" branch, and the k-th residual
// has no independent mathematical identity to label — it is just "the
// rest of the argument". Deduce is the flat spelling of that sequence:
// Have items mark the asserted facts (each labeled with the fact's
// mathematical meaning), bare Actions between them operate on the
// running residual (hyp hygiene, installs), and the tail — optionally
// wrapped in Show for a labeled finish — closes the goal.
//
// Deduce desugars to the exact nested-AssertStep tree the handwritten
// staircase produces: same kernel steps on the same goals in the same
// order, so converting a staircase changes neither the proof tree nor
// the CNF goal-key trajectory — recorded .cnf.pb blobs keep hitting
// (the same contract Expect / Finally establish above).
//
// On top of the sugar, two contracts that bare Chain lacks:
//
//   - Per-Have eager close: a Have's proof must close its claim child;
//     failure panics immediately with the Have's label instead of
//     surfacing as a distant "unsolved leaves" panic at Qed.
//   - Linearity: after every non-final item exactly ONE unsolved leaf
//     remains under the block (fan-out must be resolved inside the item
//     via its own Case structure); after the final item, ZERO. This is
//     the property whose absence makes flat AssertStep chains in bare
//     Chain unreadable — the reader would have to simulate the goal
//     stack to know what each step targets.
//
// AssertStep with explicit Cases remains the right form for a genuinely
// binary assert — a single claim whose residual immediately branches
// into structure (ByCase, SplitHypIff) and therefore has a real label.

// Have marks one asserted fact inside a Deduce block: prove `claim`
// with `proof`, then continue the sequence with the fact resident as a
// hypothesis. The label carries the fact's mathematical meaning or the
// technique that proves it (the claim text is adjacent — no need to
// restate it).
//
// Have is a Deduce item, not a free-standing Action: applying it
// outside Deduce panics.
//
// To NAME the asserted fact for later handle-addressed use
// (h.Rw / h.CongrArg / Clear(h) / h.Ground after further binders),
// wrap the Have in a handle bind — `h.From(Have(label, claim, proof…))`
// — and Deduce binds h to the claim hyp on the residual branch.
func Have(label string, claim Prop, proof ...Action) Action {
	return _HaveAction{label: label, claim: claim, proof: proof}
}

type _HaveAction struct {
	label string
	claim Prop
	proof []Action
}

func (h _HaveAction) applyAction(s *Script, root *GoalStackNode) {
	panic(fmt.Sprintf("Have(%q): Have is a Deduce item and cannot run as a free-standing Action — wrap the sequence in Deduce(...)", h.label))
}

// Show is the labeled terminal of a Deduce block: run `actions` on the
// final residual and require the goal fully closed. The label states
// how the accumulated facts finish the argument. Optional — a bare
// closing tail works too — but Show gives the close a name in both the
// text and the failure message.
func Show(label string, actions ...Action) Action {
	return _ShowAction{label: label, actions: actions}
}

type _ShowAction struct {
	label   string
	actions []Action
}

func (sh _ShowAction) applyAction(s *Script, root *GoalStackNode) {
	panic(fmt.Sprintf("Show(%q): Show is a Deduce terminal and cannot run as a free-standing Action — wrap the sequence in Deduce(...)", sh.label))
}

// Deduce runs a linear sequence of items against the current leaf and
// closes it. Items are Have facts, an optional final Show, and bare
// Actions in between (scoped to the running residual). See the section
// comment above for the desugar identity and the two contracts.
func Deduce(items ...Action) Action { return _DeduceAction{items} }

type _DeduceAction struct{ items []Action }

func (d _DeduceAction) applyAction(s *Script, root *GoalStackNode) {
	if len(d.items) == 0 {
		panic("Deduce: empty block")
	}
	cur := root.unsolvedLeaf(0)
	if cur == nil {
		panic("Deduce: focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	for i, item := range d.items {
		last := i == len(d.items)-1
		// Named Have: `h.From(Have(...))` binds the handle to the
		// asserted fact's hyp in the residual — unwrap the bind so the
		// item classifies as the Have it is (any other From-wrapped
		// action stays a plain interstitial item below).
		var bindH *HypHandle
		if hb, ok := item.(_HypBindAction); ok {
			if hv, ok := hb.act.(_HaveAction); ok {
				bindH, item = hb.h, hv
			}
		}
		switch it := item.(type) {
		case _HaveAction:
			// Identical tree to the handwritten staircase: the claim
			// Case carries the proof, the residual Case is empty and
			// the driver continues on it.
			s.Do(cur, AssertStep(it.claim,
				MakeCase("have: "+it.label, it.proof...),
				MakeCase("continue: the fact joins the goal's hyps"),
			))
			Assert(len(cur.children) == 2)
			claim, residual := cur.children[0], cur.children[1]
			if leaves := claim.UnsolvedLeaves(); len(leaves) != 0 {
				msg := fmt.Sprintf("Deduce: Have(%q) proof left its claim open (%d unsolved leaf(ves))",
					it.label, len(leaves))
				for _, l := range leaves {
					msg += "\n  leaf: " + prop.PrintProp(l.Goal)
				}
				panic(msg)
			}
			if last {
				panic(fmt.Sprintf("Deduce: Have(%q) is the final item — the residual goal is left open; close the block with trailing actions or Show(...)", it.label))
			}
			if bindH != nil {
				idx, err := newHypIndex(cur.Goal, residual.Goal)
				if err != nil {
					panic(fmt.Sprintf("Deduce: Have(%q) is bound to HypHandle %q but its claim hyp "+
						"cannot be identified in the residual: %v", it.label, bindH.Name(), err))
				}
				bindH.bindTo(residual, residual.Goal.Hyp(idx))
			}
			cur = residual
		case _ShowAction:
			if !last {
				panic(fmt.Sprintf("Deduce: Show(%q) must be the final item (it is item %d of %d)",
					it.label, i+1, len(d.items)))
			}
			for _, a := range it.actions {
				a.applyAction(s, cur)
			}
			if leaves := cur.UnsolvedLeaves(); len(leaves) != 0 {
				msg := fmt.Sprintf("Deduce: Show(%q) did not close the goal (%d unsolved leaf(ves))",
					it.label, len(leaves))
				for _, l := range leaves {
					msg += "\n  leaf: " + prop.PrintProp(l.Goal)
				}
				panic(msg)
			}
		default:
			item.applyAction(s, cur)
			leaves := cur.UnsolvedLeaves()
			if last {
				if len(leaves) != 0 {
					msg := fmt.Sprintf("Deduce: final item left %d unsolved leaf(ves) — the block must close its goal", len(leaves))
					for _, l := range leaves {
						msg += "\n  leaf: " + prop.PrintProp(l.Goal)
					}
					panic(msg)
				}
			} else {
				if len(leaves) != 1 {
					msg := fmt.Sprintf("Deduce: item %d left %d unsolved leaves — a non-final item must leave exactly one (resolve fan-out inside the item's own Case structure)",
						i+1, len(leaves))
					for _, l := range leaves {
						msg += "\n  leaf: " + prop.PrintProp(l.Goal)
					}
					panic(msg)
				}
				cur = leaves[0]
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Linearizing side-case combinators: Assuming / Unless / Suffices
// ---------------------------------------------------------------------------
//
// A mathematical argument linearizes its asymmetric case analysis: "we
// may assume x ≁ 0 — otherwise any witness settles the goal", "it
// suffices to prove the eventual bound — a bound that holds eventually can be made to hold everywhere".
// The trivial side is discharged in a clause and the main line
// CONTINUES AT THE SAME LEVEL. Spelling such a move as
// ByCaseStep(t, Case(side), Case(main)) forces the main line into a
// sibling argument literal instead: k consecutive "we may assume"
// moves indent the page 2k levels while the prose form is flat — the
// deep-pyramid tax.
//
// Assuming, Unless and Suffices are the linear spellings. Each runs
// the SAME bare ministep (ByCaseStep / AssertStep) at the current
// leaf, discharges the side branch inline with a labeled proof, and
// leaves the surviving branch as THE unsolved leaf — the enclosing
// Chain or Deduce continues on it, exactly as Deduce's Have continues
// on its residual. Same kernel steps producing the same subgoals in
// the same tree: converting a Case-nested spelling changes neither
// the proof tree nor the CNF goal-key set, so recorded .cnf.pb blobs
// keep hitting (the Expect / Finally / Deduce contract). No hidden
// hygiene steps are inserted on either branch.
//
// Contracts: the side proof must CLOSE its branch — failure panics
// immediately with the side label (Have's eager-close discipline) —
// and the label is mandatory, carrying the dismissed case's
// mathematical content: linearizing the control flow never erases the
// narrative.
//
// A genuinely symmetric split — two branches with real, comparable
// arguments — keeps the explicit ByCaseStep/Case spelling; these
// combinators are for the asymmetric shape only.

// Assuming is "we may assume t": boolean case analysis on t whose
// branch on which t FAILS is discharged inline by sideBody; the proof
// continues in the enclosing chain on the branch on which t holds,
// under the hyp t. Which child each is reads off t's own polarity
// (ByCaseBranch): the split orders its children by the term under one
// leading ¬, so `Assuming(¬p)` continues on child 1.
func Assuming(t TermLike, label string, sideBody ...Action) Action {
	return _SideCaseAction{name: "Assuming", caseTerm: ext.CoreOf(t), sideHolds: false,
		sideLabel: label, sideBody: sideBody}
}

// Unless is "the goal is settled when t holds": boolean case analysis
// on t whose branch on which t HOLDS is discharged inline by sideBody;
// the proof continues in the enclosing chain on the branch on which t
// fails, under its hypothesis — ¬t, or p for t = ¬p, the split
// contracting a leading ¬ rather than stacking one.
func Unless(t TermLike, label string, sideBody ...Action) Action {
	return _SideCaseAction{name: "Unless", caseTerm: ext.CoreOf(t), sideHolds: true,
		sideLabel: label, sideBody: sideBody}
}

type _SideCaseAction struct {
	name      string // "Assuming" | "Unless" — for panic messages
	caseTerm  Term
	sideHolds bool // the discharged branch: the one on which caseTerm holds (Unless) or fails (Assuming)
	sideLabel string
	sideBody  []Action
}

func (a _SideCaseAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic(fmt.Sprintf("%s(%q): focus has no unsolved leaves remaining "+
			"(section already proved — extra Step in chain?)", a.name, a.sideLabel) + closedLeafNote(root))
	}
	s.Do(anchor, ByCaseStep(a.caseTerm))
	Assert(len(anchor.children) == 2)
	sideChild, _ := ByCaseBranch(a.caseTerm, a.sideHolds)
	side := anchor.children[sideChild]
	for _, act := range a.sideBody {
		act.applyAction(s, side)
	}
	if leaves := side.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("%s: side case %q did not close (%d unsolved leaf(ves))",
			a.name, a.sideLabel, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(msg)
	}
}

// Suffices is "it suffices to prove claim": assert claim, discharge
// the residual Γ, claim ⊢ G inline with the labeled bridge proof, and
// continue in the enclosing chain on Γ ⊢ claim. The mirror image of
// Deduce's Have (which proves the claim inline and continues on the
// residual); label states why the claim implies the goal.
func Suffices(claim Prop, bridgeLabel string, bridge ...Action) Action {
	return _SufficesAction{claim: claim, label: bridgeLabel, bridge: bridge}
}

type _SufficesAction struct {
	claim  Prop
	label  string
	bridge []Action
}

func (a _SufficesAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic(fmt.Sprintf("Suffices(%q): focus has no unsolved leaves remaining "+
			"(section already proved — extra Step in chain?)", a.label) + closedLeafNote(root))
	}
	s.Do(anchor, AssertStep(a.claim))
	Assert(len(anchor.children) == 2)
	residual := anchor.children[1] // Γ, claim ⊢ G — the bridge's obligation
	for _, act := range a.bridge {
		act.applyAction(s, residual)
	}
	if leaves := residual.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("Suffices: bridge %q did not close the goal from the claim (%d unsolved leaf(ves))",
			a.label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(msg)
	}
	// children[0] — Γ ⊢ claim — is the surviving leaf the chain continues on.
}

// ---------------------------------------------------------------------------
// Step bodies for MiniStep concrete types
// ---------------------------------------------------------------------------
//
// Every concrete MiniStep type gets an applyAction that delegates to
// s.Do — same dispatch as the old `ctx.Do(focus, step)` form,
// including the special KnownThm cache-lookup path inside Do.

func (x _BasicTactic) applyAction(s *Script, root *GoalStackNode)     { s.Do(root, x) }
func (x _TrivialSimplify) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }

func (x _TrivialNormalizedStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }
func (x _CondRewrite) applyAction(s *Script, root *GoalStackNode)           { s.Do(root, x) }
func (x _Rewrite) applyAction(s *Script, root *GoalStackNode)               { s.Do(root, x) }
func (x _SplitConj) applyAction(s *Script, root *GoalStackNode)             { s.Do(root, x) }
func (x _SplitConjAll) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _SplitDisj) applyAction(s *Script, root *GoalStackNode)             { s.Do(root, x) }
func (x _StripImp) applyAction(s *Script, root *GoalStackNode)              { s.Do(root, x) }
func (x _StripQuant) applyAction(s *Script, root *GoalStackNode)            { s.Do(root, x) }
func (x _StripQuant1) applyAction(s *Script, root *GoalStackNode)           { s.Do(root, x) }
func (x _SplitIff) applyAction(s *Script, root *GoalStackNode)              { s.Do(root, x) }
func (x _SplitHypConj) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _OpenTelescope) applyAction(s *Script, root *GoalStackNode)         { s.Do(root, x) }
func (x _SplitHypIff) applyAction(s *Script, root *GoalStackNode)           { s.Do(root, x) }
func (x _SplitHypImply) applyAction(s *Script, root *GoalStackNode)         { s.Do(root, x) }
func (x _Assumption) applyAction(s *Script, root *GoalStackNode)            { s.Do(root, x) }
func (x _Refl) applyAction(s *Script, root *GoalStackNode)                  { s.Do(root, x) }
func (x _MembershipRead) applyAction(s *Script, root *GoalStackNode)        { s.Do(root, x) }
func (x _Left) applyAction(s *Script, root *GoalStackNode)                  { s.Do(root, x) }
func (x _Right) applyAction(s *Script, root *GoalStackNode)                 { s.Do(root, x) }
func (x _Funext) applyAction(s *Script, root *GoalStackNode)                { s.Do(root, x) }
func (x _ByContra) applyAction(s *Script, root *GoalStackNode)              { s.Do(root, x) }
func (x _Symm) applyAction(s *Script, root *GoalStackNode)                  { s.Do(root, x) }
func (x _Congr) applyAction(s *Script, root *GoalStackNode)                 { s.Do(root, x) }
func (x _Arith) applyAction(s *Script, root *GoalStackNode)                 { s.Do(root, x) }
func (x _CongrArgStep) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _CongrFunStep) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _ClearHypsStep) applyAction(s *Script, root *GoalStackNode)         { s.Do(root, x) }
func (x _CNFRefute) applyAction(s *Script, root *GoalStackNode)             { s.Do(root, x) }
func (x _WitnessStep) applyAction(s *Script, root *GoalStackNode)           { s.Do(root, x) }
func (x _InstantiateStep) applyAction(s *Script, root *GoalStackNode)       { s.Do(root, x) }
func (x _SpecializeStep) applyAction(s *Script, root *GoalStackNode)        { s.Do(root, x) }
func (x _SubstStep) applyAction(s *Script, root *GoalStackNode)             { s.Do(root, x) }
func (x _RwStep) applyAction(s *Script, root *GoalStackNode)                { s.Do(root, x) }
func (x _TransStep) applyAction(s *Script, root *GoalStackNode)             { s.Do(root, x) }
func (x _AutoDenote) applyAction(s *Script, root *GoalStackNode)            { s.Do(root, x) }
func (x _LemmaTactic) applyAction(s *Script, root *GoalStackNode)           { s.Do(root, x) }
func (x _LemmaPreserveTactic) applyAction(s *Script, root *GoalStackNode)   { s.Do(root, x) }
func (x _LeanRwTactic) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _TypeInstStep) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _KnownThmStep) applyAction(s *Script, root *GoalStackNode)          { s.Do(root, x) }
func (x _ByCaseStep) applyAction(s *Script, root *GoalStackNode)            { s.Do(root, x) }
func (x _AssertStep) applyAction(s *Script, root *GoalStackNode)            { s.Do(root, x) }
func (x _ExistentialConstDefStep) applyAction(s *Script, root *GoalStackNode) {
	s.Do(root, x)
}
func (x _InductionStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }
func (x _AxiomDefStep) applyAction(s *Script, root *GoalStackNode)  { s.Do(root, x) }

// ---------------------------------------------------------------------------
// Step bodies for Action concrete types
// ---------------------------------------------------------------------------
//
// Each Action concrete type gets an applyAction that finds the first
// unsolved leaf reachable from root and calls leaf.Apply on it. The
// existing chain semantics still apply — leaf.Apply panics on 2+
// remaining unsolved leaves after the action. Multi-residual
// branching support arrives with Case in the next rollout step.

func applyMacro(root *GoalStackNode, a Macro) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("Step.applyAction: section has no unsolved leaves remaining " +
			"(already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	leaf.Apply(a)
}

func (a AutoExpand) applyAction(_ *Script, root *GoalStackNode) { applyMacro(root, a) }

// ---------------------------------------------------------------------------
// Fused-idiom Step constructors
// ---------------------------------------------------------------------------

// UseLemma is the package-level form of the *GoalStackNode.UseLemma
// method: applies a lemma whose obligation is then closed by KnownThm
// cache lookup of the same prop. target may be a Thm (a typed dep,
// external thm, or any standalone Thm), a *GoalStackNode (a
// prior section — its ProvedThm is taken), or any Prop value (rare,
// for completeness). Runtime semantics is identical to the two-Do
// sequence Lemma(L) + KnownThm(L). Contrast with CiteKnown(prop) below,
// which is the bare cache-lookup close (no lemma-tactic adaptation).
func UseLemma(target any) Action { return _UseLemmaAction{target} }

type _UseLemmaAction struct{ target any }

func (c _UseLemmaAction) applyAction(s *Script, root *GoalStackNode) {
	var p Prop
	switch t := c.target.(type) {
	case ThmCert:
		p = t
	case *GoalStackNode:
		p = t.ProvedThm()
	case Prop:
		p = t
	default:
		panic(fmt.Sprintf("UseLemma: target must be *Thm, *GoalStackNode, or Prop; got %T", t))
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("UseLemma: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	leaf.UseLemma(p)
}

// UseLemmaExact is the replay-exact package-level form of
// *GoalStackNode.UseLemmaExact: it applies the payload exactly as
// given, without re-running chooseTypeAdaptedStep. Same target dispatch
// as UseLemma. Emit renders a cite as Cite, never as this verb.
func UseLemmaExact(target any) Action { return _UseLemmaExactAction{target} }

type _UseLemmaExactAction struct{ target any }

func (c _UseLemmaExactAction) applyAction(s *Script, root *GoalStackNode) {
	var p Prop
	switch t := c.target.(type) {
	case ThmCert:
		p = t
	case *GoalStackNode:
		p = t.ProvedThm()
	case Prop:
		p = t
	default:
		panic(fmt.Sprintf("UseLemmaExact: target must be *Thm, *GoalStackNode, or Prop; got %T", t))
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("UseLemmaExact: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	leaf.UseLemmaExact(p)
}

// UseLemmaFlipped closes a leaf whose residual is a defined-equivalence
// row read RIGHT-TO-LEFT: the wanted fact is dep's statement with its
// equivalence sides flipped, and the refuter cannot flip it itself —
// paramodulation works only on native `=`, so a defined equivalence
// (nadd_eq, …) never turns around inside the CNF search. The flip-tail
// idiom installs the row AND the symmetry law and lets the refute
// compose them:
//
//	UseLemma(dep)     // the row in its stated orientation
//	UseLemma(symDep)  // the relation's symmetry lemma
//	CnfRefute()       // resolves the two against the flipped residual
//
// UseLemmaFlipped(dep, symDep) is EXACTLY that 3-call chain (tree-
// identical sugar — same ministeps on the same goals, so existing
// hand-written sites and their recorded pbs are untouched). Both
// arguments accept what UseLemma accepts: ThmCert, *GoalStackNode, or
// Prop.
//
// Use it when a morphism/bridge reduction leaves the goal as a registry
// entry's statement with its sides swapped (the of_num_add / of_num_mul
// shape). Not
// for native `=` residuals — those flip inside the refuter for free.
func UseLemmaFlipped(dep any, symDep any) Action {
	return Chain(UseLemma(dep), UseLemma(symDep), CnfRefute())
}

// StripQuantN strips EXACTLY n leading ∀-binders off the current
// leaf's conclusion, Skolemizing each to a fixed variable and leaving
// every deeper quantifier intact — the bounded counterpart of the
// strip-everything StripQuant(). Panics up front (naming the actual
// conclusion) when the conclusion has fewer than n leading ∀s, or
// when n < 1.
//
// Desugar: n applications of the single-binder StripQuant1 ministep —
// the recorded tree is n plain replayable strip_quant1 nodes, and the
// Skolem names are exactly the ones StripQuant would mint for the
// same prefix (x → x_0, clash → next subscript; see
// tactic.StripQuant1Tactic's name-compatibility note).
func StripQuantN(n int) Action { return _StripQuantNAction{n: n} }

type _StripQuantNAction struct{ n int }

func (a _StripQuantNAction) applyAction(s *Script, root *GoalStackNode) {
	if a.n < 1 {
		panic(fmt.Sprintf("StripQuantN: n must be ≥ 1, got %d", a.n))
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("StripQuantN: section has no unsolved leaves remaining " +
			"(already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	concl := leaf.Goal.Conclusion()
	depth := 0
	for t := concl; ; depth++ {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() || depth == a.n {
			break
		}
		t = abs.Body()
	}
	if depth < a.n {
		panic(fmt.Sprintf("StripQuantN(%d): conclusion has only %d leading ∀-binder(s) — conclusion: %s",
			a.n, depth, ext.PrintTerm(concl)))
	}
	for i := 0; i < a.n; i++ {
		s.Do(leaf, _StripQuant1{})
	}
}

// UseLemmaSpecialize is the fused `UseLemma(target) + ground at one point`
// shape — the Script API mirror of `lemma {key:…, specialize:[…]}`.
// Same target dispatch as `UseLemma`: ThmCert, *GoalStackNode (sibling
// section), or Prop. The witnesses SEQUENTIALLY peel the cited lemma's
// nested ∀-prefix:
//
//	∀x₁…∀xₖ.P  ⇒  P(t₁, …, tₖ)
//
// encoded as ONE InstHyp(0, t₁, …, tₖ) — a single composite
// `specialize` ministep (proto tag 52) whose witnesses chain through
// prop.InstForAll rungs (SpecializeTactic). For k = 1 this coincides
// with UseLemmaInstances.
//
// k instances of the TOP binder — k SEPARATE 1-witness InstHyp
// entries, not a sequential peel — is UseLemmaInstances below.
func UseLemmaSpecialize(target any, witnesses ...TermLike) Action {
	return Chain(UseLemma(target), Specialize(InstHyp(0, ext.CoreTerms(witnesses)...)))
}

// UseLemmaInstances cites a ONE-binder lemma and takes k ground
// instances of it:
//
//	∀r.F(r)  ⇒  F(t₁), …, F(tₖ)
//
// encoded as k InstHyp entries each with a 1-witness list, all
// resolved against the cited hyp at index 0 — SpecializeTactic drops
// the source once and keeps every produced instance. The canonical
// use is a surjectivity lemma instantiated at two representatives
// ({hreal_add,hreal_mul,real_add}_sym's
// `UseLemmaInstances(p.surjFn(), …, …)` sites). For a MULTI-binder
// lemma this yields k partial instances — if you meant "ground at one
// point", that is UseLemmaSpecialize.
func UseLemmaInstances(target any, witnesses ...TermLike) Action {
	hyps := make([]SpecializeHyp, len(witnesses))
	for i, w := range witnesses {
		hyps[i] = InstHyp(0, ext.CoreOf(w))
	}
	return Chain(UseLemma(target), Specialize(hyps...))
}

// CiteSpecialize is the package-level Action form of
// *GoalStackNode.CiteSpecialize — the fused "cite L (replay-exact
// LemmaPreserve install), then ground it at witnesses" with the
// installed hyp located by content diff instead of a caller-supplied
// index. See the GoalStackNode method for semantics; this is the
// cite-at-use primitive (each use of a lemma cites it at the use site
// and consumes it there). The target is Cite's: any CiteTarget, a
// certificate or explicit Prop named through MakeFact.
func CiteSpecialize(target CiteTarget, witnesses ...TermLike) Action {
	return _CiteSpecializeAction{target: targetFact("CiteSpecialize", target), witnesses: ext.CoreTerms(witnesses)}
}

// CiteSpecializeKeep is CiteSpecialize keeping the cited ∀-source
// resident after grounding.
func CiteSpecializeKeep(target CiteTarget, witnesses ...TermLike) Action {
	return _CiteSpecializeAction{target: targetFact("CiteSpecializeKeep", target), witnesses: ext.CoreTerms(witnesses), keep: true}
}

type _CiteSpecializeAction struct {
	target    Fact
	witnesses []Term
	keep      bool
}

func (c _CiteSpecializeAction) applyAction(s *Script, root *GoalStackNode) {
	root.citeSpecialize(resolveLemmaTarget("CiteSpecialize", s, c.target), c.keep, c.witnesses...)
}

// GroundHyp is the package-level Action form of *GoalStackNode.GroundHyp
// — ground an EXISTING resident ∀-hyp at witnesses, locating it by
// content (α-equality) instead of by index. content may be a Prop (its
// conclusion is matched) or a Term.
func GroundHyp(content any, witnesses ...TermLike) Action {
	return _GroundHypAction{content: content, witnesses: ext.CoreTerms(witnesses)}
}

// GroundHypKeep is GroundHyp keeping the ∀-source resident after
// grounding.
func GroundHypKeep(content any, witnesses ...TermLike) Action {
	return _GroundHypAction{content: content, witnesses: ext.CoreTerms(witnesses), keep: true}
}

type _GroundHypAction struct {
	content   any
	witnesses []Term
	keep      bool
}

func (c _GroundHypAction) applyAction(s *Script, root *GoalStackNode) {
	content := c.content
	// A named dep (a registry entry) resolves through the shared
	// cite dispatch, to the SAME canonical form the cite verbs install —
	// so `Cite(X)` + `GroundHyp(X, w…)` match by construction.
	switch content.(type) {
	case NamedDep:
		content = resolveLemmaTarget("GroundHyp", s, content)
	}
	root.groundHyp(content, c.keep, c.witnesses...)
}

// resolveLemmaTarget is the shared cite-family target dispatch
// (Cite / CiteSpecialize / CiteSpecializeKeepAs / GroundHyp):
//
//   - ThmCert / Prop — used verbatim (explicit certs keep full control
//     over the install form);
//   - *TypedThm (an AtTypes instance) — its stated reference half at
//     the instance types when that is hyp-free, else its install half;
//   - *GoalStackNode — the section's certificate, preserving deferred
//     proof promises;
//   - NamedDep (registry entry vars) — the entry's dep, claimed at use
//     via Script.Dep.
//
// A named dep resolves to the dep's STATED form: the
// statement as its author wrote it (an entry's headline). Normalization
// happens LAST, inside the closer that needs clause form; nothing about
// a premise is decided by
// what its normal form looks like (the apply rung reads the
// telescope only the stated form has).
//
// A witnessed premise is typed and ordered by its tuple
// (witness_order.go). A row's normalized form is cited by naming it:
// `MakeFact(ctx.DepNormalized(name))`.
func resolveLemmaTarget(who string, s *Script, target any) Prop {
	switch t := target.(type) {
	case *TypedThm:
		// AtTypes' pair value: the STATED form at the instance types is
		// the install (normalize last); the normalized half remains the
		// value the wrapper presents as a plain Thm.
		if ref := t.Reference(); ref != nil && ref.NumHyps() == 0 {
			return ref
		}
		return t.Thm
	case typedInst:
		// The deferred spelling of the case above (proof.Inst — a
		// wrapper's Inst/ExactAt carries no Script): build the AtTypes
		// pair now that one is in scope, then proceed as *TypedThm.
		return resolveLemmaTarget(who, s, t.resolve(s))
	case _TypedSoleInst:
		// proof.InstSole — the sole-variable deferred instance; same
		// resolution shape as typedInst above.
		return resolveLemmaTarget(who, s, t.resolve(s))
	case readingInst:
		// proof.Read — a law read at an instance: derived at the
		// script, stated form; closed at an entry, under the
		// hypothesis at a resident fact — here at the content the fact
		// was bound to, no leaf being in hand; a verb at a leaf derives
		// it there (resolveTargetAt).
		return t.resolve(s, nil)
	case ThmCert:
		return t
	case *GoalStackNode:
		if !t.Proved() {
			panic(who + ": section node has no proved thm yet")
		}
		return t.PromisedThm()
	case NamedDep:
		return statedInstallForm(s, s.Dep(t))
	case Prop:
		return t
	case Fact:
		// A Fact reaching a cite verb is one of three things, and only
		// one of them is a mistake about the VERB rather than about the
		// value. Fact.applyAction already points the other direction
		// (a Fact used as a step); this is the same discipline on the
		// way in, and it is the gap that made the generic default below
		// the one cite-family message that named no repair.
		switch {
		case t.claim != nil:
			panic(who + ": a self-proving premise carries its own proof — it runs inside a By " +
				"premise list, not as a cite")
		case t.handle != nil:
			// The repair depends on what the fact is: an equation
			// rewrites, a boolean fact only closes or splits.
			repair := "close with By(f), or let Basic() split the goal against it; a boolean fact rewrites nothing"
			if content, bound := t.BoundContent(); bound {
				if _, _, isEquation := ext.MatchesEQ(content); isEquation {
					repair = "close with By(f), or rewrite with f.Rw() / f.RwRev()"
				}
			}
			panic(fmt.Sprintf("%s: hyp %q is a RESIDENT fact — it is already in context, so there "+
				"is nothing to cite; %s. Cite brings an OUTSIDE fact to bear.", who, t.handle.Name(), repair))
		case len(t.witnesses) > 0:
			// A named fact already carrying its grounding: the cite verb
			// takes witnesses positionally, so this is a spelling slip
			// with an exact repair.
			panic(fmt.Sprintf("%s: a grounded named fact is spelled %s(dep, w…), not %s(At(dep, w…))",
				who, who, who))
		}
		// The NAMED/CERTIFIED flavor — a Fact wrapping exactly this
		// function's own universe. Unwrap it: a dep read as its Fact
		// and the dep name the same fact, and a cite of one should not
		// depend on which spelling reached it.
		return resolveLemmaTarget(who, s, t.target)
	default:
		panic(fmt.Sprintf("%s: target must be *Thm, *GoalStackNode, a registry entry "+
			"(NamedDep), or Prop — a dep is named by its entry, never by a string; got %T", who, target))
	}
}

// statedInstallForm is a named dep's install: the served certificate
// itself. A named dep states a closed theorem — a member's statement
// and a definition door's computed one alike (ProofEntry.Statement
// refuses a sequent) — so a dep with hypotheses is an inconsistency
// between the library and the registry, and panics. The normalized
// form is still REGISTERED (NormalizedThm's side effect): the bare-cite
// cache-close tier answers "is the leaf this fact modulo Normalize" by
// key, and that key is the normalized one. Only the install is stated.
func statedInstallForm(s *Script, dep ThmCert) Prop {
	if dep.NumHyps() > 0 {
		panic(fmt.Sprintf("a named dep states a sequent, which no member and no definition door states: %s",
			PrintProp(dep)))
	}
	s.NormalizedThm(dep)
	return dep
}

// Rewrite is the package-level Step form of the fused
// `LeanRw(d) + AxiomDefStep(c)` idiom — the rewrite-by-def-thm
// pattern. Inside Case bodies the bare `Rewrite(d, c)`
// Step expression resolves here. d may be any Prop (the def thm
// equation); c is the const being unfolded as the discharge of the
// LeanRw obligation.
//
// The no-arg auto-rewrite ministep is `RewriteAuto()`.
func Rewrite(d Prop, c TermLike) Action { return _RewriteAction{d: d, c: ext.CoreOf(c)} }

type _RewriteAction struct {
	d Prop
	c Term
}

func (r _RewriteAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("Rewrite: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	leaf.Rewrite(r.d, r.c)
}

// ---------------------------------------------------------------------------
// Closure-bound case-local naming helpers
// ---------------------------------------------------------------------------
//
// WithIH / WithHyp / Let bind a name (a Hyp handle) within a body
// closure. The handle is opaque at v1 — its primary role is to give
// a Go identifier to a hypothesis introduced by the parent ministep
// (Induct step case, Assert residual, ByCase branch) so the body can
// pass it to forthcoming hyp-aware Step constructors (planned: a
// kernel-level Assume primitive that materializes a hyp as a Thm
// for Cite/Rewrite/UseThm consumption).
//
// Equivalent in spirit to Lean's
//   induction n with | succ k ih => …body using ih…
// The closure provides lexical scope without inventing new syntax;
// Go's first-class functions are sufficient.
//
// Emit detection — when a kernel trace contains a KnownThm reference
// to a hypothesis introduced by the parent ministep — would render
// the closure form instead of flat Step lists. Emit has no such
// dispatch; the runtime API serves hand-written proofs.

// Hyp is the opaque handle bound by WithIH / WithHyp / Let. It
// carries the hyp's term plus an optional display name; subsequent
// hyp-aware Step constructors (planned) will read these to construct
// kernel-level Assume thms.
type Hyp struct {
	Term Term
	Name string
}

// WithIH binds the leaf's last hypothesis as the induction
// hypothesis under the given name, invokes body with the Hyp
// handle, and applies the returned Step. Intended for use inside
// the `step` Case body of an Induct(...) call:
//
//	Induct(p.m,
//	    Case("base", CiteKnown(p.baseCase)),
//	    Case("step", WithIH("ih", func(ih Hyp) Step {
//	        return Chain(CiteKnown(p.stepLemma), ...)
//	    })),
//	)
//
// Panics if the leaf has no hypotheses (typical when called outside
// a parent-ministep step case).
func WithIH(name string, body func(ih Hyp) Action) Action {
	return _WithIHAction{name: name, body: body}
}

type _WithIHAction struct {
	name string
	body func(ih Hyp) Action
}

func (w _WithIHAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("WithIH: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	nh := leaf.Goal.NumHyps()
	if nh == 0 {
		panic(fmt.Sprintf("WithIH(%q): leaf has no hypotheses (must be called inside step case of Induct, ByCase, Assert, or similar)", w.name))
	}
	ih := Hyp{Term: leaf.Goal.Hyp(nh - 1), Name: w.name}
	w.body(ih).applyAction(s, root)
}

// WithHyp scans the leaf's hypothesis list for one whose term
// matches the predicate, binds it under the given name, invokes
// body with the Hyp handle, and applies the returned Step. The
// scan walks hyps in their stored order; the first match wins.
// Panics with the leaf's printed goal when no hyp matches.
//
// Use this when the role of the target hyp isn't "the last one
// introduced" (so WithIH doesn't fit) — e.g., when picking out a
// specific shape from a multi-hyp goal.
func WithHyp(pred func(Term) bool, name string, body func(h Hyp) Action) Action {
	return _WithHypAction{pred: pred, name: name, body: body}
}

type _WithHypAction struct {
	pred func(Term) bool
	name string
	body func(h Hyp) Action
}

func (w _WithHypAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("WithHyp: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	for hyp := range leaf.Goal.HypIter() {
		if w.pred(hyp) {
			h := Hyp{Term: hyp, Name: w.name}
			w.body(h).applyAction(s, root)
			return
		}
	}
	panic(fmt.Sprintf("WithHyp(%q): no hypothesis matched predicate; leaf has %d hyp(s)", w.name, leaf.Goal.NumHyps()))
}
