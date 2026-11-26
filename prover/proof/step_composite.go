// step_composite.go — recurring mathematical actions as first-class
// recorded composite ministeps.
//
// Every member here is the same design, instantiated once per action:
// ONE proto tag whose payload is the action's mathematical content, and
// whose `apply` IS the shared executor. Live agent dispatch (the engine
// RPC), emitted members, and replay all call that one
// function with the same inputs, so the SubGoals shape and the
// reconstruction are byte-for-byte identical — there is no wire layer
// that could see a different dispatch than what live commit saw. This
// is the record/emit/replay code-reuse principle: record the COMPOSITE
// step, never an expansion snapshot.
//
// What each member folds, and what its payload records:
//
//   - DefExpand       — unfold one definitional const (the const)
//   - SetTac          — the set closer (the set vocabulary)
//   - SimpWith        — the simplifier (the rule set)
//   - PairedBeta      — paired-λ β-normalization (the site)
//   - PairCollapse    — fst/snd on a literal pair (the site)
//

package proof

import (
	"context"
	"fmt"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// =======================================================================
// DefExpand — definitional-const unfolding
// =======================================================================
//
// def_expand — the agent-facing `def_expand` tactic as a first-class
// recorded composite ministep.
//
// ONE proto tag (StepProto_DefExpand, tag 51) whose payload is the const
// `c` being unfolded. `apply(goal)` IS the shared driver:
// computeDefExpandSubGoals(c, goal) reproduces the whole
// LeanRw(defThm) + AxiomDef(c) + TrivialSimplify(residual) composite as
// ONE 1-subgoal SubGoals (or 0-subgoal when the fast path closes). Record
// (the engine's `def_expand` dispatch) and replay (a member's Build)
// both call this same function with the same inputs, so the SubGoals
// shape and reconstruct are byte-for-byte identical. There is no wire
// layer that could see a different dispatch than what live commit saw.
//
// A choice constant — `c = εx.P(x)`, with or without parameters — is
// opened like any other definition: c becomes its ε-term, and with
// `∃x.P(x)` resident the tidy closes the opened P(c), whose trivial
// normalizer reads P(εx.P(x)) as ∃x.P(x) (prop.HilbertExistsRewrite).
// ExistentialConstDefStep is the other reading of the same choice: c
// kept folded, the two obligations handed over as cases.

type _DefExpandStep struct {
	constTerm ConstTerm
	// site is where the author wrote the Unfold (authorCallSite), named
	// by a refusal of a step after one that closed its leaf; runtime
	// only — never serialized, so empty on a step built from its record
	// or by a session.
	site string
}

func (step _DefExpandStep) String() string {
	return fmt.Sprintf("DefExpand: %s", ext.PrintTerm(step.constTerm))
}

func (step _DefExpandStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_DefExpand{DefExpand: b.TermRef(step.constTerm)}
}

func (step _DefExpandStep) apply(p Prop) *SubGoals {
	return computeDefExpandSubGoals(step.constTerm, p, nil)
}

// applyScoped reads the record equations of the unfolding's normal form
// as the proof's cites (libraryRead).
func (step _DefExpandStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	sub := computeDefExpandSubGoals(step.constTerm, p, libraryRead(scope))
	if sub != nil {
		scope.noteUnfolded(step.constTerm.Name())
	}
	return sub
}

func (step _DefExpandStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// DefExpandStep is the handle-taking ministep-level constructor:
// `<node>.Do(DefExpandStep(v.SomeConst))`. Emitted members render the
// definition-taking Unfold(<definition>), which records the identical
// ministep.
// Replay routes through the same computeDefExpandSubGoals as record.
//
// Sibling of AxiomDefStep / ExistentialConstDefStep at the ministep layer,
// and the ONLY def-expand entry (with its Unfold spelling): there is no
// Action macro `DefExpand(c)` wrapping a lemma application of the def thm
// in a post-simplify.
func DefExpandStep(c core.Term) Step {
	ct := c.Core().(core.ConstTerm)
	if err := InductiveUnfoldRefusal(ct); err != nil {
		panic(fmt.Sprintf("DefExpandStep: %v", err))
	}
	return _DefExpandStep{constTerm: ct}
}

// Definition is what Unfold and Unfolded open: a definition, read as
// the constant it defines. The typed wrapper of an entry a definition
// door registered with one unfoldable constant is one, and so is a
// structure; a theorem's wrapper is not, so a proof that names a theorem
// where a definition belongs does not compile.
type Definition interface {
	DefinedConstant() core.ConstTermMeta
}

// constantDefinition is a constant read as the definition it has.
type constantDefinition struct{ constant core.ConstTerm }

func (d constantDefinition) DefinedConstant() core.ConstTermMeta { return d.constant.Meta() }

// DefinitionOf reads a constant as the definition it has, for a caller
// that holds the constant and no entry: the session, which resolved a
// name, and a test that minted one. A chapter names the definition's
// own entry.
func DefinitionOf(c ConstTerm) Definition { return constantDefinition{constant: c} }

// uniqueExistence is ∃! as a definition, for Unpack, which opens a fact
// headed by it into the existence of a point every satisfying point
// equals. No chapter unfolds ∃!: the logic defines it, and a closer
// reads it through normalization (prop.UniqueRewrite).
var uniqueExistence = DefinitionOf(ext.UNIQUE)

// Unfold opens a definition on the whole leaf: the constant d defines
// is expanded in the goal and in every resident hypothesis.
//
//	a.Do(Unfold(real_order.LtDef), Cite(LessEqAddLeft))
//
// d is the definition itself — the typed wrapper of the entry that
// defines the constant, or a structure — so a name that is no
// definition does not compile.
// The step it records is DefExpandStep's at the constant's abstract
// type: the walker instantiates the definition at each occurrence.
//
// A proof that opens a constant stands on its definition. The step
// notes the constant on the proof's scope (ProofScope.Unfolded), and
// the corpus records the entry that defines it among the member's
// dependencies.
func Unfold(d Definition) Action {
	return _unfoldAction{definition: d, site: authorCallSite()}
}

type _unfoldAction struct {
	definition Definition
	site       string
}

func (u _unfoldAction) applyAction(s *Script, root *GoalStackNode) {
	s.Do(root, _DefExpandStep{constTerm: unfoldedConstant("Unfold", u.definition), site: u.site})
}

// ApplyUnfold records on n the step Unfold records for the constant c:
// the def_expand composite, whatever kind of definition c has. The
// session's `def_expand {const, hyp_index}` closes its claim child with
// it, as a.Unfolded's Have does.
func ApplyUnfold(n *GoalStackNode, c ConstTerm) bool {
	return n.runStep(_DefExpandStep{constTerm: c})
}

// unfoldedConstant is the constant Unfold and Argument.Unfolded open
// for a definition: the one it defines, at its abstract type. Panics,
// naming the verb, for no definition and for a constant the walker may
// not open (an inductive relation).
func unfoldedConstant(verb string, d Definition) ConstTerm {
	if d == nil {
		panic(verb + ": no definition to open")
	}
	meta := d.DefinedConstant()
	c := core.MakeConstTerm(meta, meta.AbsType())
	if err := InductiveUnfoldRefusal(c); err != nil {
		panic(fmt.Sprintf("%s(%s): %v", verb, c.Name(), err))
	}
	return c
}

// UnfoldedHypothesis is what the hypothesis `content` states once the
// constant c is opened in it — the claim a.Unfolded makes of a fact
// (derive.go), computed by the def-expand walker on the hypothesis
// alone, its record equations read through `read`; the session's
// `def_expand {const, hyp_index}` claims the same statement. The error
// names the refusal the verb makes: a hypothesis that does not mention
// c, a c with no definition to open, a walker that leaves the
// hypothesis as it stands.
func UnfoldedHypothesis(content core.Term, c ConstTerm, read tactic.LibraryRead) (core.Term, error) {
	folded := core.MakeProp(content)
	if !prop.ContainsConstName(folded, c.Name()) {
		return nil, fmt.Errorf("the fact does not mention %s:\n  %s", c.Name(), ext.PrintTerm(content))
	}
	defThm := getDefThm(c)
	if defThm.IsZero() {
		return nil, fmt.Errorf("%s has no definition to open", c.Name())
	}
	sg, _ := dispatchDefExpandRewrite(defThm, folded, read)
	if sg == nil || sg.Size() != 2 {
		return nil, fmt.Errorf("the def-expand walker did not open %s in\n  %s", c.Name(), ext.PrintTerm(content))
	}
	unfolded := sg.ChildGoal(1).Conclusion()
	if unfolded.AlphaEquals(content) {
		return nil, fmt.Errorf("opening %s changes nothing in\n  %s", c.Name(), ext.PrintTerm(content))
	}
	return unfolded, nil
}

// UnfoldedHypothesis is UnfoldedHypothesis at n's hypothesis idx, the
// record equations read through n's scope — what a session's
// `def_expand {const, hyp_index}` claims of the hypothesis at the node
// it runs on.
func (n *GoalStackNode) UnfoldedHypothesis(idx int, c ConstTerm) (core.Term, error) {
	if idx < 0 || idx >= n.Goal.NumHyps() {
		return nil, fmt.Errorf("hyp_index %d out of range [0, %d)", idx, n.Goal.NumHyps())
	}
	return UnfoldedHypothesis(n.Goal.Hyp(idx), c, libraryRead(n.proofScope))
}

// computeDefExpandSubGoals is the shared record/replay driver for the
// def_expand composite. Given const c and goal, returns SubGoals whose sole
// child (when non-nil and size > 0) is the def-unfolded residual after
// TrivialSimplify, and whose reconstruct closes the defThm
// obligation inline via getDefThm(c) — the same Thm _AxiomDefStep would use.
//
// Returns nil when:
//   - c doesn't occur in goal (no rewrite site)
//   - c has no def thm (basic const)
//   - No dispatch produced subgoals for the rewrite.
//
// Dispatch: TryDefExpand (dedicated unfold-everywhere walker) first,
// general LeanRwTactic as capability fallback — see
// dispatchDefExpandRewrite. The composite IS the semantics: record and
// replay both run this function, so there is no other implementation to
// stay in sync with.
func computeDefExpandSubGoals(c ConstTerm, goal Prop, read tactic.LibraryRead) *SubGoals {
	if !prop.ContainsConstName(goal, c.Name()) {
		return nil
	}
	defThm := getDefThm(c)
	if defThm.IsZero() {
		return nil
	}

	// IsStronger fast path — defThm directly proves goal, no rewrite needed.
	if IsStronger(defThm, goal) {
		return tactic.MakeEmptySubGoals(goal, defThm)
	}

	inner, skipResidualPostprocess := dispatchDefExpandRewrite(defThm, goal, read)
	if inner == nil {
		return nil
	}

	// inner is a 2-subgoal shape [defThm_obligation, residual] — the
	// LeanRw / TryDefExpand tactics uniformly produce this. The defThm
	// obligation is closed inline by AxiomDef — the actual Thm is
	// defThm itself (LeanRw's child(0) α-matches defThm's statement
	// modulo the type instantiation getDefThm already performed).
	if inner.Size() < 1 || inner.Size() > 2 {
		panic(fmt.Sprintf("_DefExpandStep: unexpected dispatch subgoal shape size=%d for const %s",
			inner.Size(), ext.PrintTerm(c)))
	}
	if inner.Size() == 1 {
		// Degenerate: dispatch yielded only the defThm obligation — goal
		// closed as an immediate consequence. Close with defThm.
		closedThm := inner.Reconstruct(defThm)
		return tactic.MakeEmptySubGoals(goal, closedThm)
	}
	residualPre := inner.ChildGoal(1)

	if skipResidualPostprocess {
		// set_comprehension fold skips the residual post-process (its hyps rewrite is
		// already the caller's intended shape). One residual child, no
		// TrivialSimplify inline.
		return tactic.MakeTrackedSubGoals(goal, func(thms ...Prop) Prop {
			return inner.Reconstruct(defThm, thms[0])
		}, [][]int{inner.HypSuccessors(1)}, residualPre)
	}

	// Compose the residual's tidy (composeResidualPost). Each SubGoals in
	// postChain is a 1-subgoal step whose reconstruct we unwind in
	// reverse to lift the final residual thm back to residualPre.
	postChain, finalResidual, closed := composeResidualPost(residualPre)
	if closed != nil {
		return tactic.MakeEmptySubGoals(goal, inner.Reconstruct(defThm, closed))
	}
	// The residual's hypothesis provenance is the walker's map composed
	// with the tidy's, so a handle follows a hypothesis the unfold
	// rewrote and loses one the tidy split.
	successors := inner.HypSuccessors(1)
	for _, post := range postChain {
		successors = tactic.ComposeSuccessors(successors, post.HypSuccessors(0))
	}
	return tactic.MakeTrackedSubGoals(goal, func(thms ...Prop) Prop {
		cur := thms[0]
		for i := len(postChain) - 1; i >= 0; i-- {
			cur = postChain[i].Reconstruct(cur)
		}
		return inner.Reconstruct(defThm, cur)
	}, [][]int{successors}, finalResidual)
}

// dispatchDefExpandRewrite is the composite's rewrite dispatch:
// TryDefExpand (the dedicated unfold-everywhere def walker — α-faithful
// per-occurrence type instantiation over conclusion AND hyps) first,
// then the general LeanRwTactic as capability fallback for shapes the
// walker declines (e.g. Type-2 typedef def thms).
//
// Deliberately NO const-name special cases here: a set_comprehension
// hyp-fold or a set_member iff-left variant is not defensible def_expand
// semantics (def_expand(set_comprehension) silently REVERSING the unfold
// direction on hyps; def_expand(set_member) rewriting only the left side
// of an ⇔) — an agent wanting a directed fold reaches for lean_rw /
// simp_with explicitly.
// Returns (subgoals, skipResidualPostprocess); the latter is always
// false now and kept only for signature stability at the call site.
func dispatchDefExpandRewrite(defThm, goal Prop, read tactic.LibraryRead) (*tactic.SubGoals, bool) {
	if sg := tactic.TryDefExpandReading(defThm, goal, read); sg != nil {
		return sg, false
	}
	// Fallback to the general LeanRwTactic path. `defThm` is already
	// type-instantiated to c's ConstTerm by getDefThm, so we do NOT run
	// chooseTypeAdaptedStep here — the extra adaptation could pick a
	// different σ than record (the "adaptive rewrite drift" this
	// composite exists to exclude).
	if sg := tactic.LeanRwTactic(defThm)(goal); sg != nil {
		return sg, false
	}
	return nil, false
}

// composeResidualPost is the tidy after the walker: UnfoldTidyTactic on
// the unfolded residual — the connectives simplified and the leaf closed
// where a hypothesis states its conclusion, and no rewrite by a resident
// equation, which the author spells. It returns (postChain,
// finalResidual, nil) when the residual stayed open, or (nil, nil,
// closedThm) when the tidy closed it outright.
func composeResidualPost(residualPre Prop) (postChain []*tactic.SubGoals, finalResidual Prop, closed Prop) {
	cur := residualPre
	if ts := tactic.UnfoldTidyTactic(cur); ts != nil {
		if ts.Size() == 0 {
			return nil, nil, ts.Reconstruct()
		}
		if ts.Size() != 1 {
			panic(fmt.Sprintf("_DefExpandStep: the tidy produced %d subgoals on residual %s",
				ts.Size(), prop.PrintProp(residualPre)))
		}
		postChain = append(postChain, ts)
		cur = ts.ChildGoal(0)
	}
	return postChain, cur, nil
}

// =======================================================================
// SetTac — the set closer
// =======================================================================
//
// set_tac — the set closer as a first-class recorded ministep.
//
// ONE proto tag (StepProto_SetTac, tag 49) whose apply IS the shared
// executor: deterministic fixpoint unfold of the recorded set-vocabulary
// consts across goal + hyps (tactic.SetTacExpand), then a bare CNF refute
// on every residual leaf. Close-or-fail: apply returns nil unless every
// leaf closes, so a recorded step's refutes are guaranteed to exist in the
// cnf_proofs cache — strict-mode replay (RequireCNFCacheHit) HITs under
// the same keys record-time wrote, because replay re-runs THIS function.
//
// The record/emit/replay-reuse principle (supersedes the abandoned
// "record only resolved executors" doctrine): live agent dispatch
// (engine `case "set_tac"` → ApplySetTac, the door below), emitted
// members (`<node>.Do(SetTacMembership())` / `SetTacLegacy()`, the
// recorded mode's form), and the emit-time CNF collector (cnf_cache.go)
// all execute this same apply — divergence between record and replay is
// impossible by construction, not by parallel careful implementations.

// DefaultSetTacConsts is the set vocabulary the engine's `set_tac`
// dispatch records — StandardSetVocabulary as TermNames, sorted
// (SetTacProto contract: the recorded order is the deterministic
// processing order). One list, two spellings: the Go call sites take
// strings, the engine dispatch and the collector take TermNames.
// Extending the vocabulary changes only NEWLY recorded steps —
// previously recorded steps carry their own const list in the proto and
// replay exactly as recorded.
func DefaultSetTacConsts() []core.TermName {
	standard := StandardSetVocabulary()
	names := make([]core.TermName, len(standard))
	for i, c := range standard {
		names[i] = core.TermName(c)
	}
	return tactic.SortTermNames(names)
}

type _SetTacStep struct {
	env *ProverEnv
	// ctx is context.Background() at a member's replay, where Script
	// threads no context. Live dispatch passes the agent's budgeted ctx so
	// the expansion fixpoint AND the closing refutes honor budget_ms.
	ctx    context.Context
	consts []core.TermName
	// mode selects the executor (recorded verbatim in the proto; replay
	// re-runs exactly the recorded mode — see SetTacProto's doc):
	// LEGACY = full def-expansion everywhere; MEMBERSHIP =
	// membership-level rewriting + rule residence
	// (tactic.MembershipSetTacExpand / MembershipResidence).
	mode SetTacMode
	// residuals is an optional RUNTIME-ONLY diagnostic sink (never
	// serialized — proto() carries consts alone). When non-nil and the
	// close-or-fail step fails, apply deposits the residual leaf goals
	// (capped at maxSetTacResidualDiag) that the CNF refute could not
	// close, so the engine can tell the agent WHICH leaves walled instead
	// of a bare "did not apply". Replay and emit paths leave it nil.
	residuals *[]Prop
	// bare suppresses the door's conditioning ladder: the driver runs
	// exactly as spelled, single attempt. Set by the By executor's
	// settac closer (step_by.go closeOne), whose OWN ladder already
	// conditioned the leaf — laddering again would double the stage
	// and probe against keys the By attempt owns. Runtime-only, never
	// serialized (proto() carries consts + mode alone), so recorded
	// protos always decode to the laddered door.
	bare bool
	// scope is the leaf's proof scope, threaded by applyScoped. The
	// private stacks the conditioning stage and the apply rung close
	// on carry it, so a record equation the rung reads there is the
	// proof's own cite (libraryRead) and lands in its recorded
	// dependencies. Runtime-only, never serialized.
	scope *ProofScope
}

// maxSetTacResidualDiag caps how many unclosed residual leaves a failing
// set_tac reports — enough to see the wall's shape without flooding the
// diagnostic with a wide expansion fan-out.
const maxSetTacResidualDiag = 3

func (step _SetTacStep) String() string {
	return fmt.Sprintf("SetTac(%d consts, %s)", len(step.consts), step.mode)
}

func (step _SetTacStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	names := make([]string, len(step.consts))
	for i, n := range step.consts {
		names[i] = string(n)
	}
	return &StepProto_SetTac{SetTac: &SetTacProto{Consts: names, Mode: step.mode}}
}

// setTacAssumptionClose closes a residual leaf whose conclusion is
// already among its hypotheses — α-aware: HasHyp compares via
// Term.Compare, which identifies renamed binders — with the kernel's
// Assume certificate. The set drivers manufacture their residuals
// INTERNALLY (the membership rewrite can turn the conclusion into
// exactly an installed premise, modulo binder naming), so no
// author-level shaping (By(Normalized, …) runs on the leaf BEFORE the
// driver) can ever reach such a residual; without this pre-check the
// terminal handed it to the CNF refuter, and a refute with no content
// demanded a recorded cnf_proofs key at strict replay. Cost: one
// α-aware binary search per residual leaf. Returns nil when the
// conclusion is not resident — the terminal falls through to the
// refuter exactly as before.
func setTacAssumptionClose(leaf Prop) *tactic.SubGoals {
	if leaf.HasHyp(leaf.Conclusion()) {
		return tactic.MakeEmptySubGoals(leaf, prop.Assume(leaf.Conclusion()).AsThmCert())
	}
	return nil
}

// setTacRungClose is the apply rung on a residual of the set driver:
// the one closing procedure of the By family (closeGoal) run where the
// driver's unfolding has put the goal and the hypotheses in the
// vocabulary the driver decides — every set operator a membership
// formula here, a union or an image included, and a resident law that
// concludes one applies to the goal it unfolds to. The stage's rung runs
// BEFORE the driver and reads the spelling as written up to the
// membership reading alone (`y ∈ {x | … ∧ P(x)}` as `… ∧ P(y)`, a
// set-builder's condition at the point, and nothing of the other
// operators); measured on ContinuousMapIffPointwise, whose two radii
// closed as one BySets each cost a key and a plan with the rung outside
// the driver and nothing with it inside. The goal takes one apply and
// its antecedents one more, as on the stage. scope is the leaf's proof
// scope, carried by the rung's stack so a record equation the rung
// reads is the proof's own cite. The rung reads no numeral here: the
// numeral reading has rungs in the refuter's By alone, which runs the By
// as written first, and the driver has no such ladder. Returns nil when
// the rung does not close — the terminal falls through to the refuter
// as before.
func setTacRungClose(leaf Prop, scope *ProofScope) *tactic.SubGoals {
	n := CreateGoalStack(leaf)
	if scope != nil {
		n.SetProofScope(scope)
	}
	if !closeGoal(n, rungOpts{depth: antecedentApplies + 1, scope: scope, plain: true}) || !n.Proved() {
		return nil
	}
	return tactic.MakeEmptySubGoals(leaf, n.provedThm)
}

// apply is the raw set_tac door: the conditioning ladder
// (this door reuses the By executor's stages) around the close-or-fail
// driver. Rung 1 attempts the BARE driver with CNF refutes cache-only,
// so every row recorded before the door was conditioned keeps closing on
// its recorded keys with zero re-records and no live search spent. Rung 2
// conditions the sequent (premise split / goal strip / grounding, the
// manual's S4 — the Settac column of the closer matrix; denotation stays
// with the CNF closer) on a private stack and runs the bare driver on the
// conditioned leaf; new recordings therefore mint conditioned keys exactly
// where conditioning was needed, with S4's search persisted as a plan under
// the bare leaf key. Rung 3 (live mode only — a strict replay must not
// live-refute) retries the bare driver with full semantics: conditioning
// must never LOSE a goal the bare spelling closes today (the
// no-lost-search-power boundary). The conditioned attempt's residual
// diagnostics win when both fail — the conditioned spelling is the primary
// path.
func (step _SetTacStep) apply(p Prop) *SubGoals {
	if step.bare {
		return step.applyBare(p)
	}
	if sg := step.probeBare(p); sg != nil {
		return sg
	}
	if step.env.RequireCNFCacheHit {
		// Strict replay: the conditioned attempt applies recorded plans
		// mechanically and hits conditioned keys; a MISS panics loudly
		// (drift), never re-searches.
		return step.applyConditioned(p)
	}
	if sg := step.applyConditioned(p); sg != nil {
		return sg
	}
	bare := step
	bare.residuals = nil // rung 2's diagnostics win
	return bare.applyBare(p)
}

// probeBare is rung 1: the bare driver with CNF refutes cache-only
// (the withCNFCacheOnlyProbe context mark — tryCNFRefute treats it as
// strict replay, and its MISS panic is the graceful probe failure
// recovered here, through rungFailure).
func (step _SetTacStep) probeBare(p Prop) (sg *SubGoals) {
	defer func() { rungFailure(recover()) }()
	probe := step
	probe.ctx = withCNFCacheOnlyProbe(step.ctx)
	probe.residuals = nil
	return probe.applyBare(p)
}

// applyConditioned is rung 2: the door-shared conditioning stage
// (step_condition.go) over a private stack, then the bare driver on
// the conditioned leaf. The private tree is the composite's own — nothing
// in it is serialized (the recorded proto stays the SetTac step; replay
// re-runs this same code, the split and the strip as pure functions and S4
// through the plan table). Plans persist only on a successful close.
func (step _SetTacStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	step.scope = scope
	return step.apply(p)
}

func (step _SetTacStep) applyConditioned(p Prop) *SubGoals {
	root := CreateGoalStack(p)
	if step.scope != nil {
		root.SetProofScope(step.scope)
	}
	c := &conditioner{env: step.env, ctx: step.ctx, s4: &byS4State{}, scope: step.scope}
	inner := step
	inner.bare = true
	// A conjunctive goal is conditioned and closed conjunct by conjunct
	// (conditionEach): the driver runs on each leaf the stage leaves.
	// The door's one conditioned attempt is on the pruned leaf: its bare
	// rung, which follows, is the driver on the leaf with every source wide.
	closed := conditionEach(c, root, conditionOpts{ground: true, prune: true, splitConj: true}, func(leaf *GoalStackNode) bool {
		return leaf.runStep(inner)
	})
	if !closed || !root.Proved() {
		// Conditioning alone cannot close a set goal; an unproved root
		// with nothing left to run the driver on is the α-closable
		// exemption returning on an already-degenerate stack.
		return nil
	}
	c.persistConditionPlans()
	return tactic.MakeEmptySubGoals(p, root.provedThm)
}

func (step _SetTacStep) applyBare(p Prop) *SubGoals {
	cnf := _CNFRefute{env: step.env, ctx: step.ctx}
	// The terminal: assumption first (a residual whose goal IS a resident
	// hyp needs no refuter and must not mint a CNF cache key), the apply
	// rung on the unfolded residual, then the closing refute. Shared by
	// both modes and both call sites below.
	closeLeaf := func(leaf Prop) *SubGoals {
		if s := setTacAssumptionClose(leaf); s != nil {
			return s
		}
		if s := setTacRungClose(leaf, step.scope); s != nil {
			return s
		}
		return cnf.apply(leaf)
	}
	var s *SubGoals
	if step.mode == SetTacMode_SET_TAC_MEMBERSHIP {
		s = tactic.MembershipSetTacExpand(step.ctx, p, step.consts)
		// Residence: install the derived membership rules of set-valued
		// consts surviving in each rewrite residual (the rules as
		// premises), per leaf, BEFORE the closing refute.
		residence := tactic.Tactic(func(leaf Prop) *SubGoals {
			return tactic.MembershipResidence(leaf, step.consts)
		})
		if s == nil {
			// No membership rewrite fired; the goal may still be a bare
			// pointwise residual needing rules (or need none at all).
			s = residence(p)
		} else {
			s = residence.Expand(s)
		}
	} else {
		s = tactic.SetTacExpand(step.ctx, p, step.consts)
	}
	if s == nil {
		// Nothing fired — close-or-fail on the bare terminal, mirroring a
		// plain CnfRefute ministep (plus the assumption pre-check).
		r := closeLeaf(p)
		if r == nil && step.residuals != nil {
			*step.residuals = append(*step.residuals, p)
		}
		return r
	}
	s = tactic.Tactic(closeLeaf).Expand(s)
	if s.Size() != 0 {
		// Some residual leaf did not refute. Close-or-fail: recording a
		// partially-closed composite would leave replay re-attempting a
		// refute that never succeeded at record time — a guaranteed
		// strict-mode cache MISS. Fail the whole step instead; the agent
		// falls back to manual def_expand navigation.
		if step.residuals != nil {
			for i := 0; i < s.Size() && i < maxSetTacResidualDiag; i++ {
				*step.residuals = append(*step.residuals, s.ChildGoal(i))
			}
		}
		return nil
	}
	return s
}

func (step _SetTacStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// SetTacOrder is the order the set door tries its modes in — the
// session's `set_tac` and the Go `SetTac()` alike: MEMBERSHIP first (set
// operators stay first-order and set witnesses are synthesizable —
// strictly more capable on composite-witness goals like
// `s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}`), then LEGACY full expansion (whose λ-level
// computation closes some goals the membership residual leaves opaque).
// Both attempts are close-or-fail, so the order hides nothing; the mode
// that closes is the one recorded.
func SetTacOrder() []SetTacMode {
	return []SetTacMode{SetTacMode_SET_TAC_MEMBERSHIP, SetTacMode_SET_TAC_LEGACY}
}

// _SetTacDoor is the set closer as the session's `set_tac` and the Go
// `SetTac()` run it: the raw door of each mode in SetTacOrder, tried in
// turn, each with its own conditioning ladder (_SetTacStep.apply). The
// ministep it commits is the _SetTacStep of the mode that closed — the
// exact-mode step the proto records, `dump-section` prints and emit
// renders (SetTacMembership / SetTacLegacy) — so a recorded close and
// its replay are one driver; the door itself is never recorded.
//
// Where no refute may search — a strict replay, or a context every
// refute under which is cache-only — a mode before the last runs as a
// probe: its refute's cache MISS, raised as a panic, reads as the mode
// not closing, and the last mode's MISS is the loud one. A replay of a
// hand-written `SetTac()` thus closes on the recorded mode's keys
// whichever mode that was, and a record that no longer replays still
// panics at the last mode.
type _SetTacDoor struct {
	env *ProverEnv
	// ctx is context.Background() at a member's replay; live dispatch
	// passes the agent's budgeted ctx, polled between modes.
	ctx    context.Context
	consts []core.TermName
	// residuals is the runtime-only diagnostic sink of the FIRST mode
	// (_SetTacStep.residuals): on failure the agent sees the membership
	// residual, the legible one — first-order operators, not λ-soup.
	residuals *[]Prop
}

func (door _SetTacDoor) String() string {
	modes := make([]string, 0, len(SetTacOrder()))
	for _, mode := range SetTacOrder() {
		modes = append(modes, mode.String())
	}
	return fmt.Sprintf("SetTac(%d consts, %s)", len(door.consts), strings.Join(modes, " then "))
}

// proto is unreachable: runStep commits the mode step applyRecording
// returns, never the door.
func (door _SetTacDoor) proto(*ext.PoolBuilder) isStepProto_Step {
	panic("the set door records the step of the mode that closed, never itself")
}

func (door _SetTacDoor) apply(p Prop) *SubGoals {
	_, sg := door.applyRecording(p, nil)
	return sg
}

// applyRecording runs the modes in SetTacOrder and returns the step of
// the mode that closed with its SubGoals; (nil, nil) when none closes or
// the context is done before a mode starts.
func (door _SetTacDoor) applyRecording(p Prop, scope *ProofScope) (_Step, *SubGoals) {
	order := SetTacOrder()
	probing := door.env.RequireCNFCacheHit || cnfCacheOnlyProbe(door.ctx)
	for i, mode := range order {
		if door.ctx.Err() != nil {
			return nil, nil
		}
		step := _SetTacStep{env: door.env, ctx: door.ctx, consts: door.consts, mode: mode, scope: scope}
		if i == 0 {
			step.residuals = door.residuals
		}
		var sg *SubGoals
		if probing && i < len(order)-1 {
			sg = probeSetTacMode(step, p)
		} else {
			sg = step.apply(p)
		}
		if sg != nil {
			return step, sg
		}
	}
	return nil, nil
}

// probeSetTacMode runs one mode where a cache MISS is the mode not
// closing (see _SetTacDoor): the MISS panic is recovered, a fault is
// raised again (rungFailure).
func probeSetTacMode(step _SetTacStep, p Prop) (sg *SubGoals) {
	defer func() { rungFailure(recover()) }()
	return step.apply(p)
}

func (door _SetTacDoor) applyAction(s *Script, root *GoalStackNode) { s.Do(root, door) }

// ApplySetTac runs the set door on n's goal — the session's `set_tac`
// dispatch — recording the _SetTacStep of the mode that closed. consts
// is recorded verbatim into the proto (DefaultSetTacConsts()). residuals
// is the optional failure-diagnostic sink (_SetTacDoor.residuals): when
// non-nil and no mode closes, it receives the first mode's unclosed
// residual leaves (≤ maxSetTacResidualDiag).
func ApplySetTac(n *GoalStackNode, env *ProverEnv, ctx context.Context,
	consts []core.TermName, residuals *[]Prop) bool {
	return n.runStep(_SetTacDoor{env: env, ctx: ctx, consts: consts, residuals: residuals})
}

// ApplySetTacMode is the mode-explicit entry: replay and emit's CNF
// collector pass the RECORDED mode and re-run exactly its driver.
// residuals is the optional failure-diagnostic sink (see
// _SetTacStep.residuals): when non-nil and the close-or-fail composite
// fails, it receives the unclosed residual leaves (≤
// maxSetTacResidualDiag); replay/emit pass nil and stay byte-identical.
func ApplySetTacMode(n *GoalStackNode, env *ProverEnv, ctx context.Context,
	consts []core.TermName, mode SetTacMode, residuals *[]Prop) bool {
	return n.runStep(_SetTacStep{env: env, ctx: ctx, consts: consts, mode: mode, residuals: residuals})
}

// SetTac, SetTacMembership and SetTacLegacy return nil-env steps; env is
// injected by Script.Do at execution time (see the env-injection switch
// there). This lets emit render bare `SetTacMembership()` inside
// `.Do(...)` instead of `ctx.SetTac(…)`. The Script-method forms are kept
// as delegating aliases so hand-written `ctx.SetTac(…)` calls still
// compile — under the same nil-env-then-inject contract.
// StandardSetVocabulary is the driver's own notion of "the set
// vocabulary" — the names its fixpoint unfolder knows how to expand.
// Called with NO consts, the three constructors use it.
//
// It is not a per-caller choice, and the corpus says so: this exact
// list, in this order, is what EVERY set_tac call site in the tree
// passes — both chapter set families. A name a goal does not mention is inert, so
// there is nothing for a narrower list to buy; what a hand-spelled
// copy can do is silently omit a name, and then the driver fails to
// unfold rather than reporting anything.
//
// The family-level operators big_union / big_intersection are in the
// list because their def bodies unfold into the set_comprehension /
// comprehension_spec / set_member layer, so the fixpoint's termination
// argument is unchanged. After set_basic's names come the constants
// declared to read their membership (registry.DefEntry.MembershipRead,
// tactic.MembershipReadConstants), sorted — preimage_on and
// fun_support, `..`, the real intervals: each is a set-builder over its
// arguments, whose definition opens into the same layer, and the set
// driver reads `x ∈ [a, b]` as the set-builder `[a, b]` names. Goals
// needing a COMPOSITE set witness (`s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}`) still fail under
// the legacy full expansion — the residual demands a λ-term witness,
// outside the first-order refuter; that class is the membership mode's.
//
// Returned by value so a caller cannot mutate the shared list.
func StandardSetVocabulary() []string {
	names := []string{
		"delete", "set_difference", "disjoint", "empty_set", "set_comprehension", "image",
		"set_member", "insert", "intersection", "big_intersection", "proper_subset",
		"comprehension_spec", "subset", "union", "big_union", "universe",
	}
	for _, c := range tactic.MembershipReadConstants() {
		if !slices.Contains(names, string(c)) {
			names = append(names, string(c))
		}
	}
	return names
}

// SetTac is the session's `set_tac` as a Go step: the set door
// (_SetTacDoor) — the modes in SetTacOrder tried in turn, the mode that
// closes recorded. SetTacMembership and SetTacLegacy are the exact-mode
// forms, what emit renders a recorded close as.
func SetTac(consts ...string) Step {
	return _SetTacDoor{ctx: context.Background(), consts: setConstNames(defaultSetConsts(consts))}
}
func SetTacMembership(consts ...string) Step {
	return newSetTacStep(defaultSetConsts(consts), SetTacMode_SET_TAC_MEMBERSHIP)
}
func SetTacLegacy(consts ...string) Step {
	return newSetTacStep(defaultSetConsts(consts), SetTacMode_SET_TAC_LEGACY)
}

// defaultSetConsts supplies StandardSetVocabulary when the caller named
// no consts. An empty list would otherwise give the unfolder nothing to
// expand and the step would fail with a residual identical to its input
// — a confusing way to spell "you forgot the vocabulary".
func defaultSetConsts(consts []string) []string {
	if len(consts) == 0 {
		return StandardSetVocabulary()
	}
	return consts
}

func (s *Script) SetTac(consts ...string) Step           { return SetTac(consts...) }
func (s *Script) SetTacMembership(consts ...string) Step { return SetTacMembership(consts...) }

func newSetTacStep(consts []string, mode SetTacMode) Step {
	return _SetTacStep{ctx: context.Background(), consts: setConstNames(consts), mode: mode}
}

// setConstNames is the vocabulary as the driver takes it.
func setConstNames(consts []string) []core.TermName {
	names := make([]core.TermName, len(consts))
	for i, c := range consts {
		names[i] = core.TermName(c)
	}
	return names
}

// =======================================================================
// SimpWith — the simplifier
// =======================================================================
//
// simp_with — the simplifier as a first-class
// recorded ministep.
//
// ONE proto tag (StepProto_SimpWith, tag 50) whose apply IS the shared
// executor: tactic.SimpWithExpand rewrites the goal's conclusion with the
// recorded ORDERED rule set to joint fixpoint — unconditional equations,
// ⇔⊤-oriented facts, and conditional (Horn / clause-form) rules fired by
// instance mining with side-condition discharge against goal hyps, fact
// rules, and the set's own unconditional rewrites. Progress-or-fail: apply
// returns nil unless at least one rule fired and every bridge hypothesis
// was attributed (rule clause, mined instance, or goal hyp).
//
// The record/emit/replay-reuse principle (same as set_tac): live agent
// dispatch (engine `case "simp_with"` → ApplySimpWith), emitted members
// (`<node>.Do(<ctx>.SimpWith(...))`), and any emit-time verification
// all execute this same apply — divergence between record and replay is
// impossible by construction. The proto carries the RESOLVED rule props
// verbatim (post type/term-specialize, post type-adaptation), so a later
// restatement of a cited entry never alters a recorded step's replay.
//
// Unlike set_tac there is no CNF refute inside: simp_with is a pure
// rewrite composite, so it participates in no CNF cache. Its children are
// the USED rule statements (closed against their cited entries at record
// time, by KnownThm/recall steps at replay) followed by the rewritten
// residual.

type _SimpWithStep struct {
	rules []Prop
	// flips is a parallel slice: flips[i]=true means the driver applies
	// EqSym to rule i BEFORE mining (`l = r` fires as `r → l`). The
	// recorded rule prop stays the STATED (natural-direction) form so
	// the rule child closes against its cited entry exactly as an
	// unflipped rule does. A nil or empty flips is all-false, and an
	// all-false step leaves SimpWithProto.rule_flip empty on the wire, so
	// a snapshot without the field round-trips byte for byte.
	flips []bool
	// atHyp addresses the target: 0 is the conclusion (the Simp of old);
	// k > 0 is hypothesis k−1, rewritten in its place with the rules'
	// side conditions discharged against the other hypotheses (Lean's
	// `simp at h`; tactic.SimpWithExpandFlippedAt). On the wire as
	// SimpWithProto.at_hyp, absent for the conclusion.
	atHyp int
	// readings is parallel to rules: what rule i was read from when it
	// is a structure law read at an instance (ReadingRecord), nil
	// otherwise. A session sets it, for the wire
	// (SimpWithProto.rule_reading), where emit spells the rule
	// `law.Read(instance)`; the driver never consults it. Nil or
	// all-nil leaves the field off the wire.
	readings []*ReadingRecord
	// rewritten is the hypothesis an at-hypothesis step produced, as it
	// stands on the residual: the kernel sorts a goal's hypotheses and
	// merges α-equal ones, so it is found there by content, not at
	// atHyp−1. Filled by applyRecording when the step commits, read by
	// the handle that goes on naming the hypothesis (HypHandle.Simp);
	// in memory only — the wire never carries it, replay recomputes it.
	rewritten core.Term
}

func (step _SimpWithStep) String() string {
	nFlips := 0
	for _, f := range step.flips {
		if f {
			nFlips++
		}
	}
	at := ""
	if step.atHyp > 0 {
		at = fmt.Sprintf(" at hyp %d", step.atHyp-1)
	}
	if nFlips == 0 {
		return fmt.Sprintf("SimpWith(%d rules%s)", len(step.rules), at)
	}
	return fmt.Sprintf("SimpWith(%d rules, %d flipped%s)", len(step.rules), nFlips, at)
}

func (step _SimpWithStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	rules := make([]*ext.HolPropProto, len(step.rules))
	for i, r := range step.rules {
		rules[i] = b.PropRef(r.AsProp())
	}
	// Omit the parallel flip slice when no rule is flipped — byte-stable
	// with snapshots from before rule_flip was introduced.
	var flips []bool
	for _, f := range step.flips {
		if f {
			flips = append([]bool(nil), step.flips...)
			break
		}
	}
	var readings []*ReadingProto
	for _, r := range step.readings {
		if r == nil {
			continue
		}
		readings = make([]*ReadingProto, len(step.rules))
		for i := range readings {
			readings[i] = &ReadingProto{}
			if i < len(step.readings) && step.readings[i] != nil {
				readings[i] = step.readings[i].proto(b)
			}
		}
		break
	}
	return &StepProto_SimpWith{SimpWith: &SimpWithProto{
		Rules: rules, RuleFlip: flips, AtHyp: int32(step.atHyp), RuleReading: readings}}
}

func (step _SimpWithStep) apply(p Prop) *SubGoals {
	return step.applyReading(p, nil)
}

func (step _SimpWithStep) applyReading(p Prop, read tactic.LibraryRead) *SubGoals {
	if step.atHyp > 0 {
		subGoals, _ := tactic.SimpWithExpandFlippedAtReading(p, step.atHyp-1, step.rules, step.flips, read)
		return subGoals
	}
	return tactic.SimpWithExpandFlippedReading(p, step.rules, step.flips, read)
}

// applyRecording (the GoalStackNode.runStep hook) commits an
// at-hypothesis step with the rewritten hypothesis filled in, so the
// node's step says which hypothesis of the residual the step produced.
// The conclusion form has nothing to record. The record equations of the
// rewrite's normal form are read as the proof's cites (libraryRead).
func (step _SimpWithStep) applyRecording(p Prop, scope *ProofScope) (_Step, *SubGoals) {
	read := libraryRead(scope)
	if step.atHyp == 0 {
		return step, step.applyReading(p, read)
	}
	subGoals, rewritten := tactic.SimpWithExpandFlippedAtReading(p, step.atHyp-1, step.rules, step.flips, read)
	step.rewritten = rewritten
	return step, subGoals
}

// ApplySimpWithFlippedAt is ApplySimpWithFlipped at hypothesis hyp
// (0-based): the hypothesis is rewritten in its place, the conclusion
// untouched — Lean's `simp at h`.
func ApplySimpWithFlippedAt(n *GoalStackNode, hyp int, rules []Prop, flips []bool) bool {
	return n.runStep(_SimpWithStep{rules: rules, flips: flips, atHyp: hyp + 1})
}

func (step _SimpWithStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplySimpWith runs the simp_with composite on n's goal, recording ONE
// _SimpWithStep ministep on success. rules is recorded verbatim into the
// proto — callers pass fully-resolved props (engine dispatch resolves
// key/text + type/term-specialize + type adaptation BEFORE this call).
//
// No rule is flipped. Use ApplySimpWithFlipped when the caller wants to
// fire one or more equation rules right-to-left.
func ApplySimpWith(n *GoalStackNode, rules []Prop) bool {
	return n.runStep(_SimpWithStep{rules: rules})
}

// ApplySimpWithFlipped is ApplySimpWith with a per-rule flip slice. flips
// must be nil (== no flip) or len(rules)-long. flips[i]=true means the
// driver EqSym's rule i before mining, so `l = r` fires as `r → l`. The
// recorded rule stays the natural-direction stated form; only the
// parallel SimpWithProto.rule_flip bit changes on the wire. See the
// LemmaWithSpec.Flip contract for the engine-side surface.
func ApplySimpWithFlipped(n *GoalStackNode, rules []Prop, flips []bool) bool {
	return n.runStep(_SimpWithStep{rules: rules, flips: flips})
}

// ApplySimpWithRead is ApplySimpWithFlipped — at hypothesis *hyp when
// hyp is non-nil — for a rule set some of whose rules are structure
// laws read at an instance: readings is parallel to rules and says what
// each such rule was read from (nil elsewhere), for the record. The
// driver runs on rules alone.
func ApplySimpWithRead(n *GoalStackNode, hyp *int, rules []Prop, flips []bool, readings []*ReadingRecord) bool {
	step := _SimpWithStep{rules: rules, flips: flips, readings: readings}
	if hyp != nil {
		step.atHyp = *hyp + 1
	}
	return n.runStep(step)
}

// SimpWith is the Script-level constructor emitted members call:
// `<node>.Do(<ctx>.SimpWith(rule1, rule2, …))` with each rule a Prop
// (typically MakePropText / a recalled statement). Same shared executor.
// No rule is flipped — use SimpWithFlipped for the reversed direction.
func (s *Script) SimpWith(rules ...Prop) Step {
	return _SimpWithStep{rules: rules}
}

// SimpWithFlipped is SimpWith with a parallel per-rule flip slice.
// Emitted members call this when at least one rule fired
// right-to-left in the recorded step. flips must be nil or same length
// as rules; unflipped entries stay natural direction.
//
// Hand-written proofs prefer SimpWithOriented: a positional bool
// vector at a call site is machine bookkeeping the reader must align
// against the rule list by hand.
func (s *Script) SimpWithFlipped(rules []Prop, flips []bool) Step {
	return _SimpWithStep{rules: rules, flips: flips}
}

// SimpRule is one simp rule together with its firing orientation —
// the per-rule spelling of SimpWithFlipped's parallel bool vector.
// Build via Fwd (the equation fires as its statement writes it, left
// to right) or Rev (right to left); the
// orientation is read at the rule it modifies instead of counted off
// a positional slice. RuleSet builds the third form, several rules
// travelling as one.
//
// A rule names a cite target, not a pre-built statement: the same
// universe the cite family takes (CiteTarget) — a registry entry var,
// a TYPE instance of one (`dep.Inst[T]()`), a sibling section node, a
// resident fact, or a certificate or explicit Prop named through
// MakeFact — and never a GROUND one (`dep.At(w…)`): a rule matches its
// own instances, so it has no witness slot (resolveSimpRules refuses
// one, naming what to write). It is served the way a
// cite is served: a named dep in its STATED form, the headline the
// author reads in the source (normalize last, exactly as for a By
// premise), so Fwd and Rev name a direction against that
// spelling and nothing about a rule is decided by what its normal
// form looks like. The driver reads the stated shapes directly: a
// Horn law `∀comps. S(comps) ⇒ ∀xs. l = r` is a conditional rule
// whose side condition it discharges from the context, and a
// function-valued equation reaches it unexpanded, so it rewrites a
// function that occurs as an argument (`neutral_elem(vadd) = vzero` under
// `vec⟨n⟩(·)`). Spelling a rule as MakeFact(MakePropText(…)) is the
// compute-don't-pin defect on the simp face: the copy is unchecked
// against the dep it claims to state, so a restated dep breaks it
// silently.
type SimpRule struct {
	// fact is the rule's target read as its Fact; zero for a set.
	fact Fact
	flip bool
	// set is RuleSet's members, each carrying its own orientation;
	// non-nil exactly for a set.
	set []SimpRule
}

// Fwd marks a simp rule to fire as its statement writes it (l → r).
func Fwd(target CiteTarget) SimpRule { return SimpRule{fact: targetFact("Fwd", target)} }

// Rev marks a simp rule to fire right-to-left (r → l): the driver
// applies EqSym before mining, exactly as SimpWithFlipped's true
// entries do. The recorded rule prop stays the stated form.
func Rev(target CiteTarget) SimpRule { return SimpRule{fact: targetFact("Rev", target), flip: true} }

// RuleSet bundles rules into one SimpRule, so that a chapter can export
// a rewrite it performs as a unit and a consumer names it beside its
// own rules — `Simp(int_construction.InReals, Fwd(DotBridge))` reads a
// statement about integers in ℝ and then the chapter's own bridge. The
// Simp constructors flatten a set in place, so the step built, recorded
// and rendered is the flat list; a set has no orientation of its own,
// and neither Fwd nor Rev takes one.
func RuleSet(rules ...SimpRule) SimpRule { return SimpRule{set: append([]SimpRule{}, rules...)} }

// flattenSimpRules expands every RuleSet in rules, in order.
func flattenSimpRules(rules []SimpRule) []SimpRule {
	flat := make([]SimpRule, 0, len(rules))
	for _, r := range rules {
		if r.set == nil {
			flat = append(flat, r)
			continue
		}
		flat = append(flat, flattenSimpRules(r.set)...)
	}
	return flat
}

// residentFact is the resident fact a rule names — a hypothesis by
// handle or by content — and false for every other rule.
func (r SimpRule) residentFact() (Fact, bool) {
	return r.fact, r.fact.handle != nil || r.fact.residentContent != nil
}

// resolveSimpRules resolves each rule's cite target to the rule prop
// the driver records — the cite family's own resolution, so a rule and
// a premise naming one dep are served one form — alongside the
// parallel flip vector. A resident fact of leaf is a rule too
// (residentRule), and a law read under one is derived at leaf
// (resolveTargetAt); leaf is nil where no leaf is in scope, and a
// resident rule is then refused.
func resolveSimpRules(who string, s *Script, leaf *GoalStackNode, rules []SimpRule) ([]Prop, []bool) {
	props := make([]Prop, len(rules))
	flips := make([]bool, len(rules))
	for i, r := range rules {
		if len(r.fact.witnesses) > 0 || len(r.fact.named) > 0 {
			// The cite verbs answer a grounded fact with "spell it
			// verb(dep, w…)"; a simp verb has no such form.
			panic(fmt.Sprintf("%s: rule %d is grounded (.At / Where), and a rule is not: the driver matches the "+
				"law's instances itself. Give the law bare — Fwd(dep); pin a polymorphic law at a TYPE "+
				"instance — Fwd(dep.Inst[T]()); or, where exactly this ground instance must fire, rewrite by "+
				"it — f.At(w…).Rw() for a fact in hand, or h := a.Have(…, By(dep.At(w…))), then h.Rw()", who, i))
		}
		if f, ok := r.residentFact(); ok {
			props[i] = residentRule(who, leaf, f)
		} else {
			props[i], _ = resolveTargetAt(who, s, leaf, r.fact)
		}
		flips[i] = r.flip
	}
	return props, flips
}

// residentRule is a resident hypothesis of leaf as a simp rule: the
// hypothesis assumed, the sequent `h ⊢ h`. The driver fires a rule that
// carries hypotheses only where the goal holds them, so the rule fires
// in this leaf and the leaves below it that keep h; its obligation
// closes on h itself (closeSimpRuleObligations), never on a certificate
// of its own. A guarded equation `∀y. y ∈ t ⇒ F(y) = z` is a
// conditional rule whose guard discharges against the context, and a
// resident closure `∀x y. x ∈ s ∧ y ∈ s ⇒ x * y ∈ s` discharges another
// rule's side condition, as a cited law's do. The hypothesis's types
// are the proof's: the rule is never type-adapted
// (simpAdaptationAllowed).
func residentRule(who string, leaf *GoalStackNode, f Fact) Prop {
	if leaf == nil {
		panic(fmt.Sprintf("%s: %s is a resident fact — a rule of the Simp verbs at a leaf that holds it "+
			"(Simp, fact.Simp), not of a Script-level rule list", who, f.describe()))
	}
	if f.coefficient != nil {
		panic(fmt.Sprintf("%s: %s carries a coefficient — Scaled is a By premise, not a rule", who, f.describe()))
	}
	return core.Assume(leaf.Goal.Hyp(f.residentIndex(who, leaf)))
}

// AssumedRule reports a simp rule that is a resident hypothesis assumed
// (residentRule): its one hypothesis is its conclusion. Emit spells such
// a rule as the fact naming the hypothesis.
func AssumedRule(p Prop) bool {
	return p.NumHyps() == 1 && p.Hyp(0).AlphaEquals(p.Conclusion())
}

// simpAdaptationAllowed retains the caller's instance choice before
// resolving a target to its proposition. A reading's types belong to
// its instance, even when that reading is a closed theorem.
func simpAdaptationAllowed(rules []SimpRule) []bool {
	allowed := make([]bool, len(rules))
	for i, rule := range rules {
		if _, resident := rule.residentFact(); resident {
			continue
		}
		if _, reading := rule.fact.target.(readingInst); reading {
			continue
		}
		allowed[i] = !isExplicitInstance(rule.fact.target)
	}
	return allowed
}

// SimpWithOriented is SimpWith with a per-rule orientation, one
// SimpRule per rule. It builds the IDENTICAL step (and proto) as the
// equivalent SimpWithFlipped call, so converting a call site between
// the two spellings never re-records a pb.
//
// It leaves every rule obligation the driver surfaces as an unsolved
// leaf for the caller to discharge. Prefer Simp, which discharges them
// from the rules' own certificates.
func (s *Script) SimpWithOriented(rules ...SimpRule) Step {
	props, flips := resolveSimpRules("SimpWithOriented", s, nil, flattenSimpRules(rules))
	return _SimpWithStep{rules: props, flips: flips}
}

// =======================================================================
// Simp — the simp verb: rewrite by named equations, obligations closed
// =======================================================================
//
// The simp_with composite reports the rules it USED as child goals, so
// the bare Step surface leaves the caller holding one obligation leaf
// per fired rule. Every call site discharged them the same
// way — a `Case("rule: … — cited from nn.X", CiteKnown(xThm))` per
// rule, above the one Case that carries the residual's mathematics —
// and paid twice for it:
//
//   - The rule STATEMENT had to be re-spelled as MakePropText, because
//     the Step took props and not deps. That is pinned text (§"Citation
//     forms: compute, don't pin"): a copy of a dep's statement, checked
//     against nothing, which a restatement of that dep breaks silently.
//   - The Case COUNT had to be predicted. A rule the driver does not
//     fire surfaces no child, and a rule child that auto-closes against
//     its cited entry never becomes a leaf, so the list is "one Case per
//     rule that both fires and fails to auto-close" — a fact about
//     driver behavior, hand-maintained at the call site. Two
//     files carry decoder comments for exactly this ("4 Cases for a
//     4-rule SimpWith").
//
// Simp removes both. Rules arrive as cite targets, so the statement is
// COMPUTED from the dep; and the Action discharges the obligations it
// surfaces against those same certificates, so the count is read off
// the tree instead of predicted. What is left for the caller is the
// residual — the only leaf whose content is mathematics rather than
// bookkeeping:
//
//	Expect(Simp(Rev(nn.MulLeftId), Fwd(nn.AddSym)),
//	    Case("residual: …", By(…)))
//
// This is the cite-verb consolidation applied to the simp face, and it
// is the same trade: the premise list is the checked record of which
// equations the rewrite ran on, so folding the per-rule ceremony folds
// no narrative.
//
// The discharge is exact, not a heuristic. SimpWithExpandFlipped builds
// its children as the used rules' props VERBATIM followed by the
// rewritten residual last, so a child that α-equals a rule prop IS that
// rule's obligation and the rule's own certificate closes it. A
// surfaced obligation matching no rule cannot happen; Simp panics if it
// ever does rather than leaving a leaf silently mislabeled.
//
// Simp does NOT assert how many leaves remain — that assertion belongs
// to the enclosing Expect, where the reader sees it next to the Case
// labels.

// Simp rewrites the current leaf with the given rules to joint fixpoint
// and discharges every rule obligation the driver surfaces, leaving the
// rewritten residual as the section's unsolved leaf. See the block
// comment above for the contract; Fwd / Rev build the rules. A
// polymorphic rule is adapted to the type instances the leaf exhibits
// and to those the rewrite exposes (adaptedSimpRules), as the session's
// simp_with adapts its rules: a definition stated at the chapter's
// letter fires at the goal's type without a pin.
//
// Panics (soundness-first) when no rule fires, when the divergence
// whistle cuts the rewrite (the rule set does not terminate on the
// leaf), when the section has no unsolved leaf, when a surfaced
// obligation matches no rule, and when the type adaptation reaches no
// fixpoint (MaxSimpAdaptRounds).
func Simp(rules ...SimpRule) Action { return _SimpAction{rules: flattenSimpRules(rules)} }

type _SimpAction struct{ rules []SimpRule }

func (a _SimpAction) applyAction(s *Script, root *GoalStackNode) {
	if len(a.rules) == 0 {
		panic("Simp: no rules given")
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("Simp: section has no unsolved leaves remaining " +
			"(already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	props, flips := resolveSimpRules("Simp", s, leaf, a.rules)
	allowed := simpAdaptationAllowed(a.rules)
	props, flips, sources := adaptedSimpRules(props, flips, allowed, nil, leaf.Goal)
	if !ApplySimpWithFlipped(leaf, props, flips) {
		what, why := simpFailure(leaf.Goal, props, flips, leaf.Goal.Conclusion())
		panic(fmt.Sprintf("Simp: %s on\n  goal: %s\n  rules: %s%s",
			what, prop.PrintProp(leaf.Goal), printProps(props), why))
	}
	closeSimpRuleObligations("Simp", s, leaf, props, sources)
}

// simpNoFire is what a simp step that rewrote nothing says of its rules.
const simpNoFire = "no rule fired"

// simpFailure words a simp step that did not apply to targets. what is
// simpNoFire, or "the rule set was cut as divergent" where the
// divergence whistle ended the rewrite of one of them; why is the lines
// a panic adds after its rules, tactic.SimpCut's and tactic.SimpRefusal's,
// and nothing when neither has anything to say.
func simpFailure(goal Prop, props []Prop, flips []bool, targets ...core.Term) (what, why string) {
	what = simpNoFire
	if note := tactic.SimpCut(goal, props, flips, targets...); note != "" {
		what, why = "the rule set was cut as divergent", "\n  "+note
	}
	if note := tactic.SimpRefusal(goal, props, flips, targets...); note != "" {
		why += "\n  " + note
	}
	return what, why
}

// closeSimpRuleObligations closes the rule children a simp step surfaced
// under leaf — the used rules' props verbatim, residual last — each with
// the certificate that states it, an adapted copy's as the type instance
// of the rule it copies (sources, from adaptedSimpRules); the residual
// matches no rule and stays for the caller.
func closeSimpRuleObligations(verb string, s *Script, leaf *GoalStackNode, props []Prop, sources []int) {
	open := leaf.UnsolvedLeaves()
	for i, sub := range open {
		isLast := i == len(open)-1
		at := matchingRuleIndex(props, sub.Goal)
		if at < 0 {
			if isLast {
				continue // the residual
			}
			panic(fmt.Sprintf("%s: surfaced obligation matches no rule\n  leaf: %s\n  rules: %s",
				verb, prop.PrintProp(sub.Goal), printProps(props)))
		}
		if at < len(sources) && sources[at] >= 0 {
			s.Do(sub, TypeInst(props[sources[at]]))
			continue
		}
		if AssumedRule(props[at]) {
			// A resident fact's rule: the obligation is the hypothesis.
			s.Do(sub, Assumption())
			continue
		}
		s.Do(sub, CiteKnown(props[at]))
	}
}

// matchingRuleIndex is the index of the rule prop stating goal, −1
// when goal is the rewritten residual rather than a rule obligation.
func matchingRuleIndex(props []Prop, goal Prop) int {
	for i, p := range props {
		if p.AsProp().AlphaEquals(goal) {
			return i
		}
	}
	return -1
}

// SimpAt is Simp at the hypothesis at index hyp of the current leaf —
// the positional form emit falls back to when no Fact names the
// hypothesis; a chapter addresses a hypothesis through its Fact
// (`fact.Simp(rules…)`). The hypothesis is rewritten in its place, its
// side conditions discharged against the other hypotheses; no rule
// firing is a panic, as for Simp.
func SimpAt(hyp int, rules ...SimpRule) Action {
	return _SimpAtAction{hyp: hyp, rules: flattenSimpRules(rules)}
}

type _SimpAtAction struct {
	hyp   int
	rules []SimpRule
}

func (a _SimpAtAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("SimpAt: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	simpAtHyp("SimpAt", s, leaf, a.hyp, a.rules)
}

// simpAtHyp runs the rule set at hypothesis hyp of leaf and closes the
// rule obligations; it returns the residual leaf and the rewritten
// hypothesis as it stands there. The residual's hypotheses are in the
// kernel's order, so the rewritten one is at the index its new content
// sorts to, not at hyp.
func simpAtHyp(verb string, s *Script, leaf *GoalStackNode, hyp int, rules []SimpRule) (*GoalStackNode, core.Term) {
	if len(rules) == 0 {
		panic(verb + ": no rules given")
	}
	if hyp < 0 || hyp >= leaf.Goal.NumHyps() {
		panic(fmt.Sprintf("%s: hypothesis %d is out of range on\n  goal: %s", verb, hyp, prop.PrintProp(leaf.Goal)))
	}
	props, flips := resolveSimpRules(verb, s, leaf, rules)
	for i, p := range props {
		if AssumedRule(p) && leaf.Goal.Hyp(hyp).AlphaEquals(p.Conclusion()) {
			panic(fmt.Sprintf("%s: rule %d is the hypothesis being rewritten — a fact does not rewrite itself",
				verb, i))
		}
	}
	props, flips, sources := adaptedSimpRules(props, flips, simpAdaptationAllowed(rules), &hyp, leaf.Goal)
	if !ApplySimpWithFlippedAt(leaf, hyp, props, flips) {
		what, why := simpFailure(leaf.Goal, props, flips, leaf.Goal.Hyp(hyp))
		panic(fmt.Sprintf("%s: %s on hypothesis %d\n  hyp: %s\n  rules: %s%s",
			verb, what, hyp, ext.PrintTerm(leaf.Goal.Hyp(hyp)), printProps(props), why))
	}
	closeSimpRuleObligations(verb, s, leaf, props, sources)
	open := leaf.UnsolvedLeaves()
	if len(open) != 1 {
		panic(fmt.Sprintf("%s: expected one residual leaf, found %d", verb, len(open)))
	}
	rewritten := leaf.miniStep.(_SimpWithStep).rewritten
	if rewritten == nil {
		panic(verb + ": the step committed without its rewritten hypothesis")
	}
	return open[0], rewritten
}

// SimpAll is Simp over the conclusion and every hypothesis, to a fixpoint
// across the targets — Lean's `simp_all` without the hypotheses as rules
// of each other (a resident equation rewrites through `fact.Rw()`). Each
// target is rewritten in place, and a Fact bound to a hypothesis SimpAll
// rewrites follows it, by the provenance each at-hypothesis step
// records. No target changing is a panic.
func SimpAll(rules ...SimpRule) Action {
	return _SimpAllAction{rules: flattenSimpRules(rules)}
}

type _SimpAllAction struct{ rules []SimpRule }

func (a _SimpAllAction) applyAction(s *Script, root *GoalStackNode) {
	if len(a.rules) == 0 {
		panic("SimpAll: no rules given")
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("SimpAll: section has no unsolved leaves remaining" + closedLeafNote(root))
	}
	for _, r := range a.rules {
		if f, resident := r.residentFact(); resident {
			panic(fmt.Sprintf("SimpAll: %s is a resident fact, and SimpAll rewrites every hypothesis, that one "+
				"among them — rewrite the conclusion or one other fact by it with Simp / fact.Simp", f.describe()))
		}
	}
	given, givenFlips := resolveSimpRules("SimpAll", s, nil, a.rules)
	allowed := simpAdaptationAllowed(a.rules)
	props, flips := given, givenFlips
	var sources []int
	fired := false
	// One target per round; a round that rewrites nothing ends the loop,
	// and the rounds are bounded by the targets' count times the driver's
	// own round cap, past which a rule set that keeps finding work is
	// left where it stands.
	for round := 0; round < 8*(leaf.Goal.NumHyps()+1); round++ {
		progressed := false
		props, flips, sources = adaptedSimpRules(given, givenFlips, allowed, nil, leaf.Goal)
		if ApplySimpWithFlipped(leaf, props, flips) {
			closeSimpRuleObligations("SimpAll", s, leaf, props, sources)
			progressed, fired = true, true
		} else {
			for i := 0; i < leaf.Goal.NumHyps(); i++ {
				props, flips, sources = adaptedSimpRules(given, givenFlips, allowed, &i, leaf.Goal)
				if ApplySimpWithFlippedAt(leaf, i, props, flips) {
					closeSimpRuleObligations("SimpAll", s, leaf, props, sources)
					progressed, fired = true, true
					break
				}
			}
		}
		if !progressed {
			break
		}
		open := leaf.UnsolvedLeaves()
		if len(open) != 1 {
			break // the residual closed, or the step fanned: nothing more to rewrite here
		}
		leaf = open[0]
	}
	if !fired {
		what, why := simpFailure(leaf.Goal, props, flips, append(leaf.Goal.Hyps(), leaf.Goal.Conclusion())...)
		which := "any"
		if what != simpNoFire {
			which = "a"
		}
		panic(fmt.Sprintf("SimpAll: %s on %s target of\n  goal: %s\n  rules: %s%s",
			what, which, prop.PrintProp(leaf.Goal), printProps(props), why))
	}
}

// MaxSimpAdaptRounds bounds the re-adaptation against what a rewrite
// exposes: each round needs the previous one to have exposed a new
// instance of some rule, and a chain of unfolds each exposing the next
// constant's instance is two or three deep in practice (letter_inverse
// → fst/snd; word_inverse → list_map → list_reverse). The rounds need
// a bound because a rule can restate its constant at a larger type
// (`card(s) = card(image(singleton, s))`) and expose a new instance of
// itself at every round. A round at the bound whose copies rewrite the
// residual further is a refusal naming those copies; copies with no
// redex are inert, and the set is complete as it stands.
const MaxSimpAdaptRounds = 4

// adaptedSimpRules is the rule set the driver runs: the rules as given,
// and beside each polymorphic one a copy at every type instance the
// target exhibits (typematch.EnumerateLemmaTypeAdaptations — the
// complete finite anchor-pin enumeration, dedup by the instantiated
// rule's α-key), re-read off the residual the
// set so far leaves while a round adds a copy, MaxSimpAdaptRounds deep.
// This is the session's simp_with adaptation, so a rule stated at the
// chapter's letter fires at the goal's type without a pin, and a rule
// whose constant appears only once an earlier rule's unfold exposes it
// (fst under letter_inverse) adapts in the same step. The driver then
// runs ONCE over the final set — it is a pure function of (goal,
// rules), so with every needed instance present it reaches the full
// rewrite in that run — and that run is what the step records; the
// rule at its own letters stays in the set beside its copies. A copy's
// obligation closes as a type instance of the rule it copies
// (TypeInst), recorded against that rule as the session records its
// copies, so only a rule that is a realized theorem or a promise — a
// registry entry, a served theorem — is adapted; a derived rule (a
// reading) is passed as given. sources is parallel to the returned
// rules: the index of the rule a copy adapts, −1 for a rule as given.
// hyp is the hypothesis a SimpAt rewrites, nil for the conclusion.
func adaptedSimpRules(props []Prop, flips []bool, allowed []bool, hyp *int, target core.Prop) (rules []Prop, ruleFlips []bool, sources []int) {
	return adaptedSimpRulesOf(props, flips, allowed, hyp, target, func(p Prop) bool { return p.Proved() || core.IsPromised(p) })
}

// adaptedSimpRulesOf is adaptedSimpRules with the test of which rules
// are theorems — the ones a copy's TypeInst obligation can close against
// — given by realized: the driver asks the rule itself, a caller that
// holds statements says which of them its Simp would be handed as
// theorems (SimpInstancesAdapted).
func adaptedSimpRulesOf(props []Prop, flips []bool, allowed []bool, hyp *int, target core.Prop, realized func(Prop) bool) (rules []Prop, ruleFlips []bool, sources []int) {
	adaptable := func(i int, p Prop) bool {
		return i < len(allowed) && allowed[i] && p.NumHyps() == 0 && ext.PropHasTypeVars(p) && realized(p)
	}
	sources = make([]int, len(props))
	for i := range sources {
		sources[i] = -1
	}
	polymorphic := false
	for i, p := range props {
		if adaptable(i, p) {
			polymorphic = true
			break
		}
	}
	if !polymorphic {
		return props, flips, sources
	}
	seen := make(map[core.PropKey]bool, len(props))
	for _, p := range props {
		seen[p.AsProp().AlphaKey()] = true
	}
	rules = append([]Prop{}, props...)
	ruleFlips = make([]bool, len(props))
	copy(ruleFlips, flips)
	adapt := func(against core.Prop) int {
		added := 0
		for i, p := range props {
			if !adaptable(i, p) {
				continue
			}
			for _, instance := range typematch.EnumerateLemmaTypeAdaptations(p.AsProp(), against) {
				if seen[instance.AlphaKey()] {
					continue
				}
				seen[instance.AlphaKey()] = true
				rules = append(rules, instance)
				ruleFlips = append(ruleFlips, ruleFlips[i])
				sources = append(sources, i)
				added++
			}
		}
		return added
	}
	adapt(target)
	for round := 0; ; round++ {
		residual := SimpResidual(target, hyp, rules, ruleFlips)
		if residual == nil {
			break
		}
		added := adapt(residual)
		if added == 0 {
			break
		}
		if round < MaxSimpAdaptRounds {
			continue
		}
		// At the bound, the copies this round added are what the
		// residual exhibits: one that rewrites it on its own keeps the
		// set from a fixpoint and is named; copies with no redex leave
		// the next residual as this one, so the set is complete.
		exposed := copiesThatRewrite(rules, ruleFlips, sources, len(rules)-added, props, hyp, residual)
		if len(exposed) == 0 {
			break
		}
		panic(fmt.Sprintf("Simp: the rewrite keeps exposing rule instances that rewrite further, %d residual rounds deep\n  goal: %s\n  left: %s%s",
			MaxSimpAdaptRounds, prop.PrintProp(target), prop.PrintProp(residual), exposedCopiesNote(exposed)))
	}
	return rules, ruleFlips, sources
}

// SimpInstancesAdapted is what Simp adapts beside the rules it is given
// at target: the type-instance copies adaptedSimpRules adds, each with
// the index of the rule it copies. The rules are statements — a
// recorded call read back — and theorems[i] says whether the call hands
// rule i to Simp as an adaptable theorem (a registry entry, bare), the
// rules Simp adapts; an explicit instance, a reading or a text rule is
// handed as given.
// Only statements are read, the rounds reading the residual's statement
// alone (SimpResidual). hyp is the hypothesis a SimpAt rewrites, nil for
// the conclusion.
func SimpInstancesAdapted(rules []core.Prop, flips []bool, theorems []bool, hyp *int, target core.Prop) (instances []core.Prop, sources []int) {
	props := make([]Prop, len(rules))
	for i, r := range rules {
		props[i] = r
	}
	adapted, _, from := adaptedSimpRulesOf(props, flips, theorems, hyp, target, func(Prop) bool { return true })
	for i := len(props); i < len(adapted); i++ {
		instances = append(instances, adapted[i].AsProp())
		sources = append(sources, from[i])
	}
	return instances, sources
}

// SimpResidual is what the rule set leaves of target — the last child
// of the driver's run, at hypothesis *hyp when hyp is non-nil — or nil
// when no rule fires. Only the residual's statement is read: the driver
// runs once and nothing is reconstructed (tactic.SimpResidualReading),
// and the record equations of the rewrite's normal form are read as
// statements (tactic.StatedRead).
func SimpResidual(target core.Prop, hyp *int, rules []Prop, flips []bool) core.Prop {
	return tactic.SimpResidualReading(target, hyp, rules, flips, tactic.StatedRead)
}

// A simpRuleCopy is a copy of a polymorphic Simp rule at one type
// instance: index and rule are the rule it copies, instance the copy.
type simpRuleCopy struct {
	index    int
	rule     Prop
	instance core.Prop
}

// copiesThatRewrite reports, among the copies rules[from:] holds (one
// round's additions; sources parallel), those that rewrite leaf on
// their own — at hypothesis *hyp when hyp is non-nil — each with the
// rule it copies.
func copiesThatRewrite(rules []Prop, flips []bool, sources []int, from int, props []Prop, hyp *int, leaf core.Prop) []simpRuleCopy {
	var out []simpRuleCopy
	for j := from; j < len(rules); j++ {
		if SimpResidual(leaf, hyp, rules[j:j+1], flips[j:j+1]) != nil {
			out = append(out, simpRuleCopy{index: sources[j], rule: props[sources[j]], instance: rules[j].AsProp()})
		}
	}
	return out
}

// exposedCopiesNote names each copy's rule and the instance the last
// round exposed, and the spelling that ends the re-adaptation: an
// explicit instance is not re-adapted.
func exposedCopiesNote(found []simpRuleCopy) string {
	var b strings.Builder
	for _, f := range found {
		fmt.Fprintf(&b, "\n  rule %d is polymorphic and was passed at its own letters: %s\n    the last round exposed it at %s",
			f.index+1, prop.PrintProp(f.rule.AsProp()), typeInstanceText(f.rule.AsProp(), f.instance))
	}
	b.WriteString("\n  A rule restating its constant at a larger type reaches no fixpoint, and a chain of unfolds deeper than " +
		"the bound is not followed: pass the instance meant explicitly — Fwd(<Entry>.Inst[τ]()) for one letter, " +
		"Fwd(<Entry>.Inst(TypeBinder.BindA[τ](), TypeBinder.BindB[σ]())) for several — or drop the rule")
	return b.String()
}

// typeInstanceText spells instance as the rule's letters and what each
// stands for (`A := A → bool`), or prints the instance when the two do
// not align letter by letter.
func typeInstanceText(rule, instance core.Prop) string {
	every := func(core.VarTerm) bool { return true }
	letters := func(core.VarType) bool { return true }
	substs, ok := typematch.TypeOnlyMatch(rule.Conclusion(), instance.Conclusion(), every, letters)
	if !ok || len(substs) == 0 {
		return prop.PrintProp(instance)
	}
	parts := make([]string, 0, len(substs))
	for _, sub := range substs {
		parts = append(parts, fmt.Sprintf("%s := %s", sub.VarType.Name(), ext.FormatType(sub.HolType)))
	}
	sort.Strings(parts)
	return strings.Join(parts, ", ")
}

// matchingRule returns the rule prop stating goal, or nil when goal is
// the rewritten residual rather than a rule obligation.
func matchingRule(props []Prop, goal Prop) Prop {
	for _, p := range props {
		if p.AsProp().AlphaEquals(goal) {
			return p
		}
	}
	return nil
}

func printProps(props []Prop) string {
	parts := make([]string, len(props))
	for i, p := range props {
		parts[i] = prop.PrintProp(p.AsProp())
	}
	return strings.Join(parts, "; ")
}

// =======================================================================
// PairedBeta — paired-λ β-normalization
// =======================================================================
//
// paired_beta — the auto-pipeline paired-beta normalization as a
// first-class recorded composite ministep.
//
// ONE proto tag (StepProto_PairedBeta, tag 53) whose payload is the
// POLYMORPHIC source equation — pairs.PairedLambda's engine-canonical prop
//
//	∀p g. g(fst p, snd p) = pattern_abstraction(λf. ∀x y. f(x,y) = g(x,y)) p
//
// `apply(goal)` IS the shared driver: computePairedBetaSubGoals runs a
// deterministic first-site fixpoint over the goal's paired-beta redexes
// (`pattern_abstraction(λf. ∀x y. f(,(x,y)) = body) pair`), manually instantiates the
// source per site (InstantiateLambdaPair — LeanRw's HO unification
// can't recover `g := λx y. body` from the `g(x,y)` pattern), rewrites
// via the inner _LeanRwTactic, and discharges each rewrite's rule
// obligation inside reconstruct with the same instantiation chained on
// the source's promise. Record and replay (a member's Build) both call
// this same function with the same inputs.
//
// This retires the LeanRw+KnownThm expansion snapshot the pass recorded
// before: the KnownThm payload was the per-site TERM instance, which has
// no stable identity outside the recording session — no emit
// classification tier (section / external-leaf / const-def)
// can resolve it, so emit panicked on any proof that used the pass
// (the [auto-pipeline-gap] emit wall; first recorded instance was
// cardinality.HasSizeProduct). The composite records the DRIVER
// CALL; the only wire payload is the polymorphic source, whose identity
// is exactly as stable as any lemma cite.
//
// Sibling of set_tac / simp_with / def_expand / specialize.

type _PairedBetaStep struct {
	// source is the polymorphic pairs.PairedLambda prop. On the engine path it
	// is promise-backed (env.PromiseByKey / fail-at-force fallback); on
	// the emitted-code path it is the external-leaf-resolved Thm
	// (widened to Prop). apply is deterministic on (source statement,
	// goal) either way — the backing only matters at cert realization.
	source Prop
}

func (step _PairedBetaStep) String() string {
	return fmt.Sprintf("PairedBeta:\n%s", prop.PrintProp(step.source))
}

func (step _PairedBetaStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_PairedBeta{PairedBeta: b.PropRef(step.source)}
}

func (step _PairedBetaStep) apply(p Prop) *SubGoals {
	return computePairedBetaSubGoals(step.source, p)
}

func (step _PairedBetaStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// PairedBetaStep is the ministep-level constructor emitted members
// call: `Do(g, PairedBetaStep(<pairs.PairedLambda ref>))`. The argument is
// the polymorphic source (a prior-section / library Thm widens to
// Prop). Replay routes through the same computePairedBetaSubGoals as
// record.
func PairedBetaStep(source Prop) Step { return _PairedBetaStep{source: source} }

// pairedBetaMaxSites bounds the per-step rewrite fixpoint. Each
// iteration eliminates the goal's first paired-beta redex; a goal with
// more sites than this is not a shape the pass has ever produced —
// treat it as a runaway rewrite (soundness posture: panic, don't spin).
const pairedBetaMaxSites = 64

// computePairedBetaSubGoals is the shared record/replay driver for the
// paired_beta composite. Given the polymorphic source and a goal,
// returns SubGoals whose sole child (when the goal doesn't close
// outright) is the goal with every reachable paired-beta redex
// rewritten to its destructured `body[fst pair/x, snd pair/y]` form.
//
// Returns nil when the goal has no instantiable paired-beta site (no
// site at all, or InstantiateLambdaPair / the inner rewrite refuse the
// first site before any progress was made).
//
// Fixpoint discipline: at each iteration take the goal's FIRST site
// (FindFirstPairedBetaSite — outermost-first, deterministic), build the
// per-site instance, rewrite via the inner _LeanRwTactic, and continue
// on the residual. A site that stops being instantiable mid-run ends the
// fixpoint with the partial normalization — deterministic on (source,
// goal), so record and replay stop at the same place.
//
// Reconstruction threads each level's rule obligation inline: the
// obligation's closer is the instance built from `source` itself, so on
// a promise-backed source every level forces to a kernel cert derived
// from pairs.PairedLambda's — no KnownThm, no term-instance on the wire.
func computePairedBetaSubGoals(source Prop, goal Prop) *SubGoals {
	if source.NumHyps() != 0 {
		// PairedLambda is hyp-free; a hyp-carrying source is a caller bug.
		return nil
	}
	// Statement-only twin for the inner rewrite; the promise-backed
	// source is reserved for the reconstruct-side obligation closers.
	plainSource := core.MakeProp(source.Conclusion())

	type level struct {
		inner *tactic.SubGoals
		rule  Prop // per-site instance chained on source; discharges the obligation
	}
	var levels []level
	cur := goal
	for {
		if len(levels) >= pairedBetaMaxSites {
			panic(fmt.Sprintf(
				"_PairedBetaStep: more than %d paired-beta rewrites on one goal — runaway fixpoint\n%s",
				pairedBetaMaxSites, prop.PrintProp(goal)))
		}
		site := FindFirstPairedBetaSite(cur)
		if site == nil {
			break
		}
		instPlain := InstantiateLambdaPair(plainSource, site)
		instRule := InstantiateLambdaPair(source, site)
		if instPlain == nil || instRule == nil {
			break
		}
		inner := (_LeanRwTactic{lemma: instPlain}).apply(cur)
		if inner == nil {
			break
		}
		if inner.Size() < 1 || inner.Size() > 2 {
			panic(fmt.Sprintf(
				"_PairedBetaStep: unexpected inner rewrite subgoal shape size=%d on\n%s",
				inner.Size(), prop.PrintProp(cur)))
		}
		if inner.Size() == 1 {
			// Degenerate: the rewrite closed the residual outright — only
			// the rule obligation remains, discharged by instRule.
			closed := inner.Reconstruct(instRule)
			for i := len(levels) - 1; i >= 0; i-- {
				closed = levels[i].inner.Reconstruct(levels[i].rule, closed)
			}
			return tactic.MakeEmptySubGoals(goal, closed)
		}
		levels = append(levels, level{inner: inner, rule: instRule})
		cur = inner.ChildGoal(1)
	}
	if len(levels) == 0 {
		return nil
	}
	return tactic.MakeSubGoals(goal, func(thms ...Prop) Prop {
		out := thms[0]
		for i := len(levels) - 1; i >= 0; i-- {
			out = levels[i].inner.Reconstruct(levels[i].rule, out)
		}
		return out
	}, cur)
}

// ---------------------------------------------------------------------------
// Site matcher + per-site instantiation (moved from engine/auto_pipeline.go
// so the composite's apply — the shared record/replay driver — lives next to
// the step; the engine pass and its tests consume the exported forms).
// ---------------------------------------------------------------------------

// PairedBetaSite is the parsed structure of a paired-beta occurrence
// in a goal: the matched `App(pattern_abstraction(...), pair)` term plus the bound
// vars / body / pair extracted from it. `InstantiateLambdaPair`
// consumes this to build a specialized PairedLambda equation per-site.
type PairedBetaSite struct {
	Outer core.AppliedTerm // the matched App(pattern_abstraction(Abs(f, ∀x y. f(,(x,y)) = body)), pair)
	XVar  core.VarTerm     // pattern_abstraction body's outer ∀-binder
	YVar  core.VarTerm     // pattern_abstraction body's inner ∀-binder
	Body  core.Term        // RHS of f(,(x,y)) = body; depends on XVar, YVar
	Pair  core.Term        // the argument to which pattern_abstraction-form is applied
}

// ContainsPairedBetaSite is a cheap presence check used as a gate
// before running the per-leaf rewrite. Returns true iff p (concl +
// hyps) has at least one paired-beta subterm.
func ContainsPairedBetaSite(p core.Prop) bool {
	return FindFirstPairedBetaSite(p) != nil
}

// FindFirstPairedBetaSite walks p depth-first (concl then hyps in
// HypIter order) and returns the first paired-beta site found. Returns
// nil if no site exists. The walk yields the OUTERMOST occurrence,
// which is what the rewrite consumes — rewriting an outer site that
// nests inner sites typically leaves the inner sites unchanged, so the
// fixpoint re-scans afterward.
func FindFirstPairedBetaSite(p core.Prop) *PairedBetaSite {
	if site := findPairedBetaSubterm(p.Conclusion()); site != nil {
		return site
	}
	for h := range p.HypIter() {
		if site := findPairedBetaSubterm(h); site != nil {
			return site
		}
	}
	return nil
}

// findPairedBetaSubterm walks t depth-first; returns the first site
// found, nil otherwise. Inspects t before recursing into children, so
// the outermost match wins.
func findPairedBetaSubterm(t core.Term) *PairedBetaSite {
	if site := parsePairedBetaSite(t); site != nil {
		return site
	}
	if app, ok := t.AsAppliedTerm(); ok {
		if s := findPairedBetaSubterm(app.Fun()); s != nil {
			return s
		}
		if s := findPairedBetaSubterm(app.Arg()); s != nil {
			return s
		}
		return nil
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return findPairedBetaSubterm(abs.Body())
	}
	return nil
}

// parsePairedBetaSite returns the parsed site struct if t has the
// paired-beta pattern, nil otherwise. Pattern:
//
//	App(pattern_abstraction(Abs(f, ∀x:A. ∀y:B. App(f, App(App(",", x), y)) = body)), pair)
//
// The matcher fires on any pair argument (variable, literal, complex
// term). Pair-type validity is enforced later by the kernel ops in
// InstantiateLambdaPair.
func parsePairedBetaSite(t core.Term) *PairedBetaSite {
	app, ok := t.AsAppliedTerm()
	if !ok {
		return nil
	}
	patternAbstractionApp, ok := app.Fun().AsAppliedTerm()
	if !ok {
		return nil
	}
	patternAbstractionConst, ok := patternAbstractionApp.Fun().AsConst()
	if !ok || patternAbstractionConst.Name() != "pattern_abstraction" {
		return nil
	}
	patternAbstractionAbs, ok := patternAbstractionApp.Arg().AsAbsTerm()
	if !ok {
		return nil
	}
	fVar := patternAbstractionAbs.Var()
	body1 := patternAbstractionAbs.Body()
	xAbs := ext.MatchesFORALL(body1)
	if xAbs.IsZero() {
		return nil
	}
	xVar := xAbs.Var()
	body2 := xAbs.Body()
	yAbs := ext.MatchesFORALL(body2)
	if yAbs.IsZero() {
		return nil
	}
	yVar := yAbs.Var()
	body3 := yAbs.Body()
	lhs, rhs, ok := ext.MatchesEQ(body3)
	if !ok {
		return nil
	}
	lhsApp, ok := lhs.AsAppliedTerm()
	if !ok {
		return nil
	}
	lhsFunVar, ok := lhsApp.Fun().AsVar()
	if !ok || !lhsFunVar.Equals(fVar) {
		return nil
	}
	commaApp, ok := lhsApp.Arg().AsAppliedTerm()
	if !ok {
		return nil
	}
	commaInner, ok := commaApp.Fun().AsAppliedTerm()
	if !ok {
		return nil
	}
	commaConst, ok := commaInner.Fun().AsConst()
	if !ok || commaConst.Name() != "," {
		return nil
	}
	xRef, ok := commaInner.Arg().AsVar()
	if !ok || !xRef.Equals(xVar) {
		return nil
	}
	yRef, ok := commaApp.Arg().AsVar()
	if !ok || !yRef.Equals(yVar) {
		return nil
	}
	return &PairedBetaSite{
		Outer: app,
		XVar:  xVar,
		YVar:  yVar,
		Body:  rhs,
		Pair:  app.Arg(),
	}
}

// InstantiateLambdaPair builds a per-site specialized PairedLambda
// equation:
//
//	⊢ pattern_abstraction(λf. ∀X Y. f(,(X,Y)) = body[X/x,Y/y]) pair
//	  = body[fst pair / x, snd pair / y]
//
// from PairedLambda's prop and a parsed site. The returned equation's
// LHS α-equals the site (post-rename of the inner ∀-binders), so the
// inner _LeanRwTactic rewrites the site to the destructured body.
// Returns nil on type or shape mismatch.
//
// Construction sequence:
//
//  1. Strip PairedLambda's outer ∀p ∀g to read the binder types.
//  2. Compute the type substitution σ that aligns p's binder type
//     (prod(A,B)) with the site's pair type, and g's binder type
//     (A→B→C) with xType→yType→bodyType.
//  3. Apply σ via TypeInst to make types concrete.
//  4. Specialize p := site.Pair and g := λx.λy.site.Body via
//     two ConclForAllInst calls.
//  5. Deep β-reduce both sides — the lambda-witness g_witness applied
//     to (fst pair, snd pair) on the LHS, and to (X,Y) inside the
//     RHS's pattern_abstraction body.
//  6. EqSym to flip direction so the rewrite eliminates the pattern_abstraction form.
//
// Kernel-faithful: every step uses prop.WrapProp's kernel-proved
// operations; on a promise-backed lpProp the chain derives a promise
// (core.deriveProp), which is what lets the composite's reconstruct
// discharge the rule obligation at the promise layer.
func InstantiateLambdaPair(lpProp core.Prop, site *PairedBetaSite) core.Prop {
	// Step 1: read PairedLambda's binder structure.
	pAbs := ext.MatchesFORALL(lpProp.Conclusion())
	if pAbs.IsZero() {
		return nil
	}
	pVar := pAbs.Var()
	gAbs := ext.MatchesFORALL(pAbs.Body())
	if gAbs.IsZero() {
		return nil
	}
	gVar := gAbs.Var()

	// Step 2: compute type substitution.
	xType := site.XVar.Type()
	yType := site.YVar.Type()
	bodyType := site.Body.Type()

	// Match p's binder type (prod(A,B)) against site.Pair's type to
	// pin A and B. Then chain g's binder type to pin C.
	pSubsts, ok := pVar.Type().Matches(site.Pair.Type(), utils.FullPredicate[core.VarType])
	if !ok {
		return nil
	}
	gPattern := gVar.Type().Substitute(pSubsts...)
	gTarget := core.MakeFun(xType, yType, bodyType)
	gSubsts, ok := gPattern.Matches(gTarget, utils.FullPredicate[core.VarType])
	if !ok {
		return nil
	}
	allSubsts := append([]core.TypeSubst{}, pSubsts...)
	allSubsts = append(allSubsts, gSubsts...)

	// Step 4: build g_witness := λXVar. λYVar. site.Body.
	// Reuse site.XVar and site.YVar as bound vars so body's existing
	// free var references get captured correctly.
	gWitnessInner := core.Abs(site.YVar, site.Body)
	gWitness := core.Abs(site.XVar, gWitnessInner)

	// Steps 3+4+5+6 chained on PropWrapper.
	defer func() {
		// A step of the chain that reports a failure leaves the site
		// un-instantiable to the caller. A fault is raised again
		// (rungFailure): the matcher validated the surface shape, so a
		// step the kernel refuses means PairedLambda's stored form has
		// drifted from what this chain assumes.
		rungFailure(recover())
	}()

	w := prop.WrapProp(lpProp)
	if len(allSubsts) > 0 {
		w = w.TypeInst(allSubsts...)
	}
	w = w.ConclForAllInst(site.Pair)
	w = w.ConclForAllInst(gWitness)
	w = w.Rewrite(prop.DeepBeta)
	w = w.EqSym()
	return w
}

// =======================================================================
// PairCollapse — literal-pair projection collapse
// =======================================================================
//
// pair_collapse — literal-pair projection collapse (`fst(,(a,b)) → a`,
// `snd(,(a,b)) → b`) as a first-class Action.
//
// A step that exposes a projection applied to a concrete pair
// constructor — a def-expand of a component-wise operator, a paired-λ
// β-reduction — leaves the projections resident (the CNF refuter cannot
// hash them, SimpWith Expect counts mismatch). PairCollapse rewrites
// each redex away with the polymorphic fst / snd rules and closes each
// rewrite's rule-reproduction child by type-instance matching, driven
// to fixpoint, as ONE Action.
//
// Pure sugar — no new proto tag. Each iteration commits an ordinary
// _LeanRwTactic ministep (via ApplyLeanRw's type-adaptation path) and
// closes its rule-reproduction child with a _TypeInstStep from the
// polymorphic rule. Deterministic on (rules, goal): record and replay execute the
// same Go against the same goal state, so the ministep sequence is
// reproducible by construction — the WithSource school, not the
// PairedBetaStep one (paired-beta needed a composite
// tag because its per-site instances had no stable wire identity;
// fst / snd rewrites cite stable registry entries).

// PairProjKind identifies which projection const heads the first
// literal-pair projection site found in a goal.
type PairProjKind int

const (
	PairProjNone PairProjKind = iota
	PairProjFST
	PairProjSND
)

// FindPairProjectionSite walks p (conclusion then hyps) depth-first
// and returns the kind of the first `fst(,(a, b))` / `snd(,(a, b))`
// site whose kind is wanted; PairProjNone when no wanted site exists.
// The pair argument must be a concrete `,` constructor application —
// projection over a variable / abstract term has no fixed reduct and
// is not matched. A site of an UNwanted kind does not stop the walk:
// the search continues into its subterms (a caller that serves only one
// projection passes want=false for the other and must still find the
// wanted sites nested deeper).
func FindPairProjectionSite(p core.Prop, wantFST, wantSND bool) PairProjKind {
	if k := findPairProjSubterm(p.Conclusion(), wantFST, wantSND); k != PairProjNone {
		return k
	}
	for h := range p.HypIter() {
		if k := findPairProjSubterm(h, wantFST, wantSND); k != PairProjNone {
			return k
		}
	}
	return PairProjNone
}

// findPairProjSubterm walks t depth-first; outermost site wins. The
// walk descends through App and Abs constructors so projection sites
// buried under curried applications (`snd(,(a,b))(c,x)`) or λ-binders
// are reached.
func findPairProjSubterm(t core.Term, wantFST, wantSND bool) PairProjKind {
	if k := parsePairProjSite(t, wantFST, wantSND); k != PairProjNone {
		return k
	}
	if app, ok := t.AsAppliedTerm(); ok {
		if k := findPairProjSubterm(app.Fun(), wantFST, wantSND); k != PairProjNone {
			return k
		}
		if k := findPairProjSubterm(app.Arg(), wantFST, wantSND); k != PairProjNone {
			return k
		}
		return PairProjNone
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return findPairProjSubterm(abs.Body(), wantFST, wantSND)
	}
	return PairProjNone
}

// parsePairProjSite returns the site kind if t has shape
// `fst(,(a, b))` or `snd(,(a, b))` and that kind is wanted.
func parsePairProjSite(t core.Term, wantFST, wantSND bool) PairProjKind {
	outer, ok := t.AsAppliedTerm()
	if !ok {
		return PairProjNone
	}
	headConst, ok := outer.Fun().AsConst()
	if !ok {
		return PairProjNone
	}
	var kind PairProjKind
	switch headConst.Name() {
	case "fst":
		if !wantFST {
			return PairProjNone
		}
		kind = PairProjFST
	case "snd":
		if !wantSND {
			return PairProjNone
		}
		kind = PairProjSND
	default:
		return PairProjNone
	}
	// outer.Arg() must be ,(a, b) = App(App(",", a), b).
	pairApp, ok := outer.Arg().AsAppliedTerm()
	if !ok {
		return PairProjNone
	}
	pairInner, ok := pairApp.Fun().AsAppliedTerm()
	if !ok {
		return PairProjNone
	}
	pairConst, ok := pairInner.Fun().AsConst()
	if !ok || pairConst.Name() != "," {
		return PairProjNone
	}
	return kind
}

// pairCollapseMaxSites bounds the fixpoint. Each iteration eliminates
// at least the goal's first projection site; a goal with more sites
// than this is not a shape the collapse has ever met — treat it as a
// runaway rewrite (soundness posture: panic, don't spin).
const pairCollapseMaxSites = 64

type _PairCollapseAction struct {
	fst, snd Prop // the polymorphic projection rules (library certs)
}

// PairCollapse rewrites every literal-pair projection redex reachable
// in the current leaf — `fst(,(a, b)) → a`, `snd(,(a, b)) → b` — to
// fixpoint. `fst` and `snd` are the polymorphic projection rules,
// normally the fst / snd library certs claimed via `ctx.Dep(pairs.Fst)` /
// `ctx.Dep(pairs.Snd)` (a ThmCert widens to Prop; the read is a dep of
// the entry). Each site costs one LeanRw ministep whose
// rule-reproduction child is closed by TypeInst from the polymorphic
// rule — the hand-written per-site
//
//	Expect(LeanRw(<monomorphic projection text>),
//	    Case("axiom leaf: …", TypeInst(fstThm)),
//	    Case("residual: …", cont))
//
// ladder this Action replaces.
//
// Loud contracts: both rules must mention their projection const
// (swapped-argument guard, panics at construction); the current leaf
// must contain at least one projection site (a PairCollapse on a goal
// with nothing to collapse is an authoring error, panics at apply);
// a rewrite or discharge that fails mid-fixpoint panics with the goal.
func PairCollapse(fst, snd Prop) Action {
	if fst == nil || snd == nil {
		panic("PairCollapse: nil projection rule")
	}
	if !prop.ContainsConstName(fst, "fst") {
		panic(fmt.Sprintf("PairCollapse: first rule does not mention fst (swapped arguments?)\n%s",
			prop.PrintProp(fst)))
	}
	if !prop.ContainsConstName(snd, "snd") {
		panic(fmt.Sprintf("PairCollapse: second rule does not mention snd (swapped arguments?)\n%s",
			prop.PrintProp(snd)))
	}
	return _PairCollapseAction{fst: fst, snd: snd}
}

func (m _PairCollapseAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("PairCollapse: focus has no unsolved leaves remaining " +
			"(section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	if FindPairProjectionSite(anchor.Goal, true, true) == PairProjNone {
		panic(fmt.Sprintf("PairCollapse: no fst/snd-of-literal-pair site in goal — "+
			"nothing to collapse (authoring error)\n%s", prop.PrintProp(anchor.Goal)))
	}
	for i := 0; ; i++ {
		if i >= pairCollapseMaxSites {
			panic(fmt.Sprintf(
				"PairCollapse: more than %d projection rewrites on one goal — runaway fixpoint\n%s",
				pairCollapseMaxSites, prop.PrintProp(anchor.Goal)))
		}
		leaf := anchor.unsolvedLeaf(0)
		if leaf == nil {
			return // collapse closed the whole subtree
		}
		kind := FindPairProjectionSite(leaf.Goal, true, true)
		if kind == PairProjNone {
			return // fixpoint reached
		}
		rule := m.fst
		if kind == PairProjSND {
			rule = m.snd
		}
		if !ApplyLeanRw(leaf, rule) {
			panic(fmt.Sprintf("PairCollapse: projection rewrite refused on goal\n%s",
				prop.PrintProp(leaf.Goal)))
		}
		// The rewrite's children are [rule-reproduction obligation,
		// residual] (or the obligation alone when the residual closed
		// outright). Discharge the obligation immediately — it is the
		// subtree's first unsolved leaf, and it MATCHES the scanner (its
		// own `,(x, y)` is a literal pair), so leaving it open would send
		// the next iteration rewriting the rule itself. TypeInst from the
		// polymorphic rule is the same discharge the session's trailing
		// auto-match-type-instance pass performs.
		if ob := leaf.unsolvedLeaf(0); ob != nil {
			TypeInst(rule).applyAction(s, ob)
		}
	}
}
