package proof

// step_condition.go — the conditioning stage shared by the closer doors:
// the By executor, and the standalone set_tac / auto doors that reuse the
// same stages. Its rules and its stages in order are the manual's
// §"The conditioning stage of `by`". The stage is a pure function
// of the leaf: the goal strip fixes the residual goal's ∀-binders, moves
// antecedents into hypotheses and splits a conjunctive goal into its
// conjuncts, each a leaf of its own from there on; the premise split breaks
// conjunctive hyps into their conjuncts; grounding (the manual's S4)
// instantiates the wide ∀-hyps at the leaf's own ground terms and keeps
// them beside their instances, or, where the door asks for the pruned
// leaf, replaces by its instances each one a match pinned in full (the one
// searchy stage — its search output persists as PLANS in the CNF store, so
// every replay path applies the recorded plans with zero search);
// denotation names fat comprehension atoms for the CNF closer. Which stages
// run is the caller's closer matrix (conditionOpts); the executor ladders
// around the stage stay with each door.

import (
	"context"
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// conditioner carries the stage's environment through one door attempt.
// s4 accumulates the grounding stage's outcome: live-searched plans to
// persist on success (persistConditionPlans) and the action
// transcript for the failure diagnostics.
type conditioner struct {
	env *ProverEnv
	ctx context.Context
	s4  *byS4State
	// claims is the By executor's claim-obligation set, by pointer: the
	// apply rung may install a premise's stated form on demand, and the
	// claim that install leaves must join the composite's children.
	// nil for the standalone doors.
	claims *[]*GoalStackNode
	// heads are the named premises' stated forms (see applyHeads).
	heads []applyHead
	// namedMiss keeps the apply rung's nearest miss for a head pinned
	// by name (applyHead.named) — the By executor reports it when the
	// premise the author meant to apply did not fire.
	namedMiss string
	// closed reports whether the last conditionLeaf closed the leaf it
	// conditioned (the apply rung did). With a goal split into its
	// conjuncts the next working leaf is the next conjunct, so "a
	// working leaf remains" no longer says the conditioned one is open.
	closed bool
	// prune and wide are conditionOpts' for the grounding stage.
	prune bool
	wide  bool
	// arith says the door's closer is the arithmetic decider, and scope
	// is the leaf's proof scope: the apply rung then supplies a guard
	// that closer decides (rungOpts.arith).
	arith bool
	scope *ProofScope
	// numerals is the door reading numerals at the rung: the attempts a
	// By's ladder runs with the numeral reading (_ByStep.numerals), and no
	// other door's.
	numerals bool
	// cut names the stage of the last conditionLeaf that ctx ended
	// before it reached its end; empty where every stage ran to its end.
	// A stage that was cut changed nothing, so the leaf is not the one
	// a run with no deadline conditions, and the door does not go on to
	// close it: the By raises its cut-off, the auto door declines.
	cut string
}

// rung is the apply rung's reading for this door at the top depth.
func (c *conditioner) rung() rungOpts {
	return rungOpts{depth: antecedentApplies, arith: c.arith, scope: c.scope, ctx: c.ctx, plain: !c.numerals}
}

// conditionOpts is the closer applicability matrix: the split and the strip
// always run (they are neutral where they are not needed); ground is
// S4 (every closer: a wide law grounded at the leaf's own terms is a
// fact the arithmetic decider reads as readily as the refuter — `(∀y.
// y < 3 ⇒ P(y)) ∧ x + 1 < 3 ⊢ P(x)` closes by arith once the law
// stands at x); denote is the denotation stage (CnfRefute only, and
// suppressed when the author's shape already denoted — the author's hand
// wins).
type conditionOpts struct {
	ground bool
	// prune makes a grounding replace, by its instances, each source a
	// match pinned in full (groundStage); without it a grounding adds the
	// instances and removes nothing. The two leaves differ in what a
	// closer can lose: on the pruned one, a source the close needs at a
	// point the stage did not ground it at — a witness the refutation
	// makes, a term another instance produces; on the whole one, the
	// search among the wide forms, and the instances themselves wherever a
	// simplifier discards a hypothesis that its source subsumes. Which the
	// close needs is known only once a search has run: the By ladder is
	// run on the whole leaf and then on the pruned one (applyLadder); the
	// standalone doors take the pruned leaf, their own ladders running the
	// bare one beside it.
	prune bool
	// wide is the closer that reads its facts wide — the arithmetic one,
	// whose conditional rewriting wants each law as stated: a stored plan
	// that replaces, which a pruning run of another closer recorded for
	// the same leaf, is passed over, and the stage grounds afresh. Without
	// it a stored plan is applied as recorded.
	wide   bool
	denote bool
	// recordParts is the record reading at the refuter's own
	// instantiations (_RecordParts; CnfRefute only): the part equations
	// of the record values the leaf spells, at the projections it
	// spells, installed before the search. A function of the leaf and
	// the installed record equations, recorded nowhere, as the strips
	// are.
	recordParts bool
	// applyClose runs the apply rung (apply_close.go) once the strips
	// have exposed the bare goal, and again after grounding: a leaf
	// that is an instance of a resident law with its antecedents in
	// the context closes by kernel apply and never reaches a closer.
	applyClose bool
	// readMemberships hands the closer the leaf with every membership
	// in a set-builder read as its condition at the point (the
	// MembershipRead step; CnfRefute and Arith, the closers that unfold
	// no definition), after the rung and the grounding have matched the
	// leaf as spelled: a law over a set `s` pins `s := {i | i < n}` at a
	// membership, and a plan recorded at one is read back at one, so
	// the reading comes last. The set driver unfolds the memberships
	// itself and is handed the leaf as spelled.
	readMemberships bool
	// readRecords hands the closer the leaf with every record projection
	// of a packed value read as the part (the RecordRead step; the
	// refuter, the arithmetic closer and the set driver): the reading
	// the apply rung compares in, run on the leaf for the closers that
	// compare terms as written. A resident fact keeps the projection its
	// author spelled and a cited instance arrives at the part, so unread
	// the two are different atoms to each of them. It runs where the
	// membership reading does, after the rung and the grounding have
	// matched the leaf as spelled, and with it to a fixpoint: a part may
	// spell a set-builder, a read condition a projection.
	readRecords bool
	// splitConj is the goal strip's split of a conjunctive goal: the
	// working leaf becomes the first conjunct, and the conjuncts after it
	// are leaves the door conditions and closes in turn (conditionEach). A
	// door that closes ONE leaf leaves it off.
	splitConj bool
}

// claimLeaves is the claim obligations the door's working leaf is read
// past: the By executor's set as it stands at the read — the apply
// rung's on-demand install of a stated form adds its obligation while
// the stage runs, and a set read before the rung would count that
// obligation as a working leaf — and none for a standalone door.
func (c *conditioner) claimLeaves() []*GoalStackNode {
	if c.claims == nil {
		return nil
	}
	return *c.claims
}

// conditionLeaf runs the stage over the door's working leaf.
func (c *conditioner) conditionLeaf(root *GoalStackNode, opts conditionOpts) {
	c.closed = false
	c.cut = ""
	open := len(byWorkingLeaves(root, c.claimLeaves()))
	defer func() {
		// The strips add a leaf per conjunct they split off; the leaf
		// conditioned is closed when fewer are open than they left.
		c.closed = len(byWorkingLeaves(root, c.claimLeaves())) < open
	}()
	// A leaf whose conclusion is resident is already in perfect
	// shape — the settac driver closes it by assumption with no key,
	// and the CNF closer's ruled behavior (reach the refuter, diagnose
	// Basic()) reads the sequent as spelled. Conditioning such a leaf
	// could only degrade it. Resident is α-equal to a hypothesis, and,
	// where the door runs the apply rung, the rung's own identity
	// (rungReader.resident): a goal that names a predicate applied,
	// `∀E. fin(E) ⇒ «Motive»(E)` beside the law spelled with its body,
	// is that law up to β, and stripped it is a redex the law no longer
	// matches.
	bare := byWorkingLeaf(root, c.claimLeaves())
	if bare == nil {
		return
	}
	resident := bare.Goal.Conclusion().AlphaEquals
	if opts.applyClose {
		resident = c.rung().reader().resident(bare.Goal.Conclusion())
	}
	if bare.Goal.AnyHyp(resident) {
		// Lean's `exact h`: the apply rung closes it by assumption, with
		// no key. The doors that do not take the rung keep the leaf as
		// spelled for their closer.
		if opts.applyClose {
			c.tryApplyClose(root)
		}
		return
	}
	// The BARE key — the plan table's key, snapshotted before any
	// stage transforms the leaf. "Bare" means β-normal: the leaf
	// exactly as premise install left it.
	bareKey := planKey(bare.Goal)
	bareGoal := bare.Goal
	split := false
	for {
		leaf := byWorkingLeaf(root, c.claimLeaves())
		if leaf == nil {
			return
		}
		if leaf.runStep(_StripQuant1{}) || leaf.runStep(_StripImp{}) ||
			leaf.runStep(_SplitHypConj{}) {
			continue
		}
		// A conjunctive goal is its conjuncts: splitting loses nothing,
		// each conjunct is a smaller question for the rung and for the
		// closer, and one the context already answers costs nothing.
		if opts.splitConj && leaf.runStep(_SplitConj{}) {
			split = true
			continue
		}
		break
	}
	open = len(byWorkingLeaves(root, c.claimLeaves()))
	if split {
		// The leaf conditioned from here on is the first conjunct, and
		// a plan is that leaf's: keyed by the whole goal it would be
		// read back for a leaf it was not made on.
		if leaf := byWorkingLeaf(root, c.claimLeaves()); leaf != nil {
			bareKey, bareGoal = planKey(leaf.Goal), leaf.Goal
		}
	}
	// S5 at the refuter's own instantiations: a clause with a variable
	// of a record type is instantiated at the record values the leaf
	// spells, and a projection of such a value is a redex the refuter
	// has no equation for; the stage hands it the parts, as facts of the
	// leaf the rung and the grounding read like the premises.
	if opts.recordParts {
		if leaf := byWorkingLeaf(root, c.claimLeaves()); leaf != nil {
			leaf.runStep(_RecordParts{})
		}
	}
	// The apply rung — Lean's `apply h; assumption` over the context,
	// tried before any search. Keyless and deterministic, so it runs
	// in strict replay exactly as live.
	if opts.applyClose && c.tryApplyClose(root) {
		return
	}
	// The keyless probe grounds nothing and applies no plan. Where the
	// store holds one for this leaf, under the key the conditioned rung's
	// grounding stage reads it at, the leaf's recorded close is that
	// rung's: a strict replay's probe tells the ladder and ends here,
	// before the closer builds the leaf's CNF for a close it is barred
	// from (byLadderState.planned). A strict replay's alone: its store is
	// the By's recording, where a session's store and one being recorded
	// into also hold the plans of other spellings of the leaf — the plan's
	// key is the leaf before any shaping — and a spelling whose shaping
	// closes the leaf further down this probe reads none of them.
	if !opts.ground && noRefuteProbe(c.ctx) && c.env.RequireCNFCacheHit && auditReplayOf(c.ctx) == nil {
		if svc := c.env.ProofService; svc != nil && svc.CNFStore != nil && cnfStoreHoldsPlan(svc.CNFStore, bareKey) {
			if st := ladderStateOf(c.ctx); st != nil {
				st.planned = true
				panic("By[keyless probe]: the store holds a plan for the leaf — its recorded close is the conditioned rung's")
			}
		}
	}
	// S4 — grounding wide ∀-premises.
	if opts.ground {
		if opts.prune && opts.wide {
			panic("conditionLeaf: a closer that reads its facts wide is handed no pruned leaf")
		}
		c.prune, c.wide = opts.prune, opts.wide
		c.groundStage(root, bareKey, bareGoal)
		// A grounding may have pinned the binder the conclusion could
		// not; the apply rung is cheap enough to ask again.
		if opts.applyClose && c.tryApplyClose(root) {
			return
		}
	}
	// The readings, after the rung and the grounding, which match the
	// leaf as spelled.
	//
	// The record reading, for every closer that compares terms as
	// written: every record projection of a packed value the leaf
	// spells, in the goal or a hypothesis, read as the part through the
	// record equations (the apply rung's reading, apply_close.go).
	// Unread, a resident `x ∈ V.carrier` at a packed V and an instance's
	// `x ∈ hom_set(…)` were two atoms to the refuter, the arithmetic
	// closer and the set driver, and a close the rung did not take
	// failed on a fact the author had stated.
	//
	// The membership reading, for a closer that unfolds no definition:
	// every membership in a set-builder the leaf spells, in the goal or
	// a hypothesis, read as its condition at the point — the three-part
	// form as the ∃ over its binders — through the kernel's bridge.
	// Unread, the membership was an opaque atom to the refuter:
	// `x ∈ {i | i < n}` beside `x < n` did not meet,
	// `f(a) ∈ {f(k) | k | k < n}` had no witness to find, and a
	// membership whose condition the context contradicts ran to the
	// ceiling.
	//
	// Each is taken until neither changes the leaf, as the rung's
	// reading is (rungReader.reading), and the strips run once more on what
	// they expose: a condition that is a conjunction, an ∃ in the goal.
	if opts.readMemberships || opts.readRecords {
		read := false
		for pass := 0; ; pass++ {
			leaf := byWorkingLeaf(root, c.claimLeaves())
			if leaf == nil {
				return
			}
			fired := opts.readRecords && leaf.runStep(_RecordRead{})
			if !fired && opts.readMemberships {
				fired = leaf.runStep(_MembershipRead{})
			}
			if !fired {
				break
			}
			if pass == rungReadingPasses {
				panic(fmt.Sprintf("By: the conditioning stage's readings reach no fixpoint after %d passes on %s — "+
					"the record reading and the membership reading feed each other", pass, prop.PrintProp(leaf.Goal)))
			}
			read = true
		}
		if read {
			for {
				leaf := byWorkingLeaf(root, c.claimLeaves())
				if leaf == nil {
					return
				}
				if leaf.runStep(_StripQuant1{}) || leaf.runStep(_StripImp{}) || leaf.runStep(_SplitHypConj{}) {
					continue
				}
				break
			}
		}
	}
	// Fat-atom denotation: a set comprehension is an opaque blob
	// the refuter can only fail on, so set_comprehension-headed applications are
	// denoted into atoms (the AutoDenote mechanism with the trigger
	// extended beyond raw size), then the size-threshold search runs
	// once — the same firing the AutoExpand path performs. Each
	// firing's minted equation is the self-terminating filter for the
	// next. A trailing Basic settles the equations into clause form,
	// as the explicit Denoted(n) shaping does. Its fixpoint is a search
	// over the leaf's case splits and equations, so it runs under the
	// door's context, and one the context ends is the stage's cut.
	if !opts.denote {
		return
	}
	fired := false
	for {
		leaf := byWorkingLeaf(root, c.claimLeaves())
		if leaf == nil {
			return
		}
		if leaf.runStep(_AutoDenote{comprehension: true}) {
			fired = true
			continue
		}
		break
	}
	if leaf := byWorkingLeaf(root, c.claimLeaves()); leaf != nil {
		if leaf.runStep(_AutoDenote{sizeThreshold: _DENOTE_SIZE_THRES}) {
			fired = true
		}
	}
	if fired {
		if leaf := byWorkingLeaf(root, c.claimLeaves()); leaf != nil {
			if _, cut := leaf.runBasicUntil(c.ctx); cut {
				c.cut = "inside the conditioning stage's Basic(), after its denote"
			}
		}
	}
}

// conditionEach conditions and closes a standalone door's goal leaf by
// leaf: the stage over the working leaf — which splits a conjunctive
// goal, so the leaves are the conjuncts — then closeLeaf on what it
// left, until none is open. Reports false at the first leaf closeLeaf
// declines. The rounds are the conjuncts, so the goal's size bounds
// them.
func conditionEach(c *conditioner, root *GoalStackNode, opts conditionOpts, closeLeaf func(*GoalStackNode) bool) bool {
	for {
		if byWorkingLeaf(root, nil) == nil {
			return true
		}
		c.conditionLeaf(root, opts)
		if c.closed {
			continue // the next leaf is the next conjunct, not yet conditioned
		}
		leaf := byWorkingLeaf(root, nil)
		if leaf == nil {
			return true
		}
		if !closeLeaf(leaf) || byWorkingLeaf(root, nil) == leaf {
			return false
		}
	}
}

// tryApplyClose runs the apply rung and keeps its nearest miss for
// the failure diagnostics.
func (c *conditioner) tryApplyClose(root *GoalStackNode) bool {
	cl := c.claims
	if cl == nil {
		cl = new([]*GoalStackNode)
	}
	closed, diag := applyClose(root, cl, c.heads, c.rung())
	if !closed && diag != "" {
		if c.s4 != nil {
			c.s4.describe = append(c.s4.describe, diag)
		}
		for _, hd := range c.heads {
			if len(hd.named) > 0 {
				c.namedMiss = diag
				break
			}
		}
	}
	return closed
}

func (c *conditioner) groundStage(root *GoalStackNode, bareKey core.PropKey, bareGoal Prop) {
	leaf := byWorkingLeaf(root, c.claimLeaves())
	if leaf == nil {
		return
	}
	// The audit's replay probe applies a plan the audited close touched.
	// Any other plan is a row a recording of the probe's spelling adds to
	// the member's: one the store holds besides is refused here, one the
	// search below would record is refused there (auditReplayProbeKey).
	replay := auditReplayOf(c.ctx)
	svc := c.env.ProofService
	if replay != nil && !replay.rows.holdsPlan(bareKey) && svc != nil && svc.CNFStore != nil &&
		cnfStoreHoldsPlan(svc.CNFStore, bareKey) {
		panic("By[auditReplayProbe]: the leaf reads a plan the audited close does not")
	}
	if svc != nil && svc.CNFStore != nil && (replay == nil || replay.rows.holdsPlan(bareKey)) {
		// A stored plan is the leaf's recorded conditioning and is applied
		// as recorded, whatever it replaces — except for the closer that
		// reads its facts wide, which passes over one that replaces: the
		// search below finds the groundings again, and the close's plan
		// overwrites the stored one.
		if entry := svc.CNFStore.ReadPlan(bareKey); entry != nil && !(c.wide && len(entry.Replaced) > 0) {
			if c.applyPlanEntry(root, leaf, entry) {
				noteCNFGoal(svc.CNFStore, bareKey, bareGoal)
				// A plan applied from the store is a row of this
				// close as one the stage persists is: the recording
				// reads it, or writes it from a blob without it.
				noteRecordPlan(c.ctx, bareKey)
				if replay != nil {
					replay.read.addPlan(bareKey)
				}
				return
			}
			// The entry no longer locates its hyps on this leaf (an
			// engine change since it was recorded — applyPlanEntry
			// panics in strict mode, so reaching here is live mode):
			// fall through to a fresh search, whose success overwrites
			// the stale entry.
		}
	}
	if c.env.RequireCNFCacheHit {
		return
	}
	plans := ematch.GroundPlans(leaf.Goal)
	if len(plans) == 0 {
		return
	}
	canon, _ := prop.CanonicalFreeRenaming(leaf.Goal)
	specs := make([]SpecializeHyp, 0, len(plans))
	applied := make([]ematch.Plan, 0, len(plans))
	for _, pl := range plans {
		idx, err := findHypIndex(leaf.Goal, pl.Hyp)
		if err != nil || !pl.Valid(leaf.Goal.Hyp(idx)) {
			continue
		}
		specs = append(specs, InstHyp(idx, pl.Witnesses...))
		applied = append(applied, pl)
	}
	if len(specs) == 0 || !ApplySpecialize(leaf, specs, true) {
		// Every instance is already resident (the author pre-grounded —
		// their hand wins): the stage has nothing to add, and the
		// wide sources stay exactly as spelled.
		return
	}
	if replay != nil {
		panic("By[auditReplayProbe]: the leaf is grounded by a plan the close would record")
	}
	// The sources a pruning stage replaces: each one every binder of which
	// a match pinned — unless the plan is a GUESS at the instance the
	// close needs (guessedInstance): then the source stays under either
	// stage. Deduplicated by α-key (several plans may share a source).
	var prunable []core.Term
	guessed := map[core.TermKey]core.Term{}
	for _, pl := range applied {
		if !pl.FullyMatched() {
			continue
		}
		if unheld := guessedInstance(leaf.Goal, pl); unheld != nil {
			guessed[pl.Hyp.AlphaKey()] = unheld
			continue
		}
		dup := false
		for _, r := range prunable {
			if r.AlphaEquals(pl.Hyp) {
				dup = true
				break
			}
		}
		if !dup {
			prunable = append(prunable, pl.Hyp)
		}
	}
	// A stage that keeps replaces nothing — the instances join the wide
	// sources — and tells the ladder there is a pruned leaf to go on to.
	var replaced []core.Term
	if c.prune {
		replaced = prunable
	} else {
		c.notePrunable(len(prunable))
		guessed = nil
	}
	c.clearReplaced(root, replaced)
	conditionedKey := core.PropKey("")
	if wl := byWorkingLeaf(root, c.claimLeaves()); wl != nil {
		conditionedKey = planKey(wl.Goal)
	}
	if c.s4 != nil {
		c.s4.pending = append(c.s4.pending, byPendingPlan{
			bareKey:        bareKey,
			bareGoal:       bareGoal,
			groundings:     applied,
			replaced:       replaced,
			canon:          canon,
			conditionedKey: conditionedKey,
		})
		c.s4.describe = append(c.s4.describe, describeGroundings(applied, replaced, guessed)...)
	}
}

// guessedInstance reports whether pl is a GUESS at the instance the
// close needs: its witnesses came from matching the source's conclusion
// alone (ematch.Plan.ViaConclusion) — the leaf spells the instance's
// conclusion, which is where a match through the conclusion always
// lands — and the instance has an antecedent the leaf does not hold.
// Such a plan says nothing about which instance the close wants;
// replacing the source by it loses the wide fact the close may need
// (the pointwise `∀d. d ∈ s ⇒ disjoint(x, d)` at a goal `disjoint(x,
// ⋃s)`, grounded at d := ⋃s), and a pruning stage keeps the source
// instead. A plan matched through an antecedent is triggered by a fact
// the leaf holds, and one whose antecedents are all held is the instance
// the apply rung would have taken: a pruning stage replaces on both.
//
// "Held" is the apply rung's reading of a guard: α-equal to a
// hypothesis as written or conjunct by conjunct, in β-normal form (an
// instance at a λ-witness states its antecedent as a redex). Returns
// the antecedent not held, nil for a plan that is no guess.
func guessedInstance(leaf Prop, pl ematch.Plan) core.Term {
	if !pl.ViaConclusion() {
		return nil
	}
	binders, antecedents, _, _ := ematch.Telescope(pl.Hyp, utils.EmptySet[core.TermName]())
	if len(antecedents) == 0 || len(pl.Witnesses) != len(binders) {
		return nil
	}
	substs := make([]core.TermSubst, len(binders))
	for i, b := range binders {
		substs[i] = core.MakeTermSubst(b, pl.Witnesses[i])
	}
	held := func(t core.Term) bool {
		if leaf.HasHyp(t) {
			return true
		}
		parts := conjuncts(t)
		return len(parts) > 1 && !slices.ContainsFunc(parts, func(p core.Term) bool { return !leaf.HasHyp(p) })
	}
	for _, a := range antecedents {
		instance := a.Substitute(substs...)
		instance = tactic.InstanceNormalTerm(instance)
		if !held(instance) {
			return instance
		}
	}
	return nil
}

// notePrunable tells the By ladder the stage runs under, where it runs
// under one, that it kept n sources a pruning stage replaces
// (byLadderState.prunable).
func (c *conditioner) notePrunable(n int) {
	if st := ladderStateOf(c.ctx); st != nil && n > 0 {
		st.prunable = true
	}
}

// clearReplaced drops the listed wide ∀-sources from the current
// working leaf (located by α-key — the specialize step above changed
// the indices). A source that vanished is skipped silently: the
// specialize's hyp-set dedup can absorb shapes.
func (c *conditioner) clearReplaced(root *GoalStackNode, replaced []core.Term) {
	if len(replaced) == 0 {
		return
	}
	leaf := byWorkingLeaf(root, c.claimLeaves())
	if leaf == nil {
		return
	}
	var idxs []int
	for _, r := range replaced {
		if idx, err := findHypIndex(leaf.Goal, r); err == nil {
			idxs = append(idxs, idx)
		}
	}
	if len(idxs) > 0 {
		ApplyClearHyps(leaf, idxs)
	}
}

// applyPlanEntry replays one recorded conditioning plan on the working
// leaf: locate each grounding's hyp by α-key, apply the batch (sources
// kept), clear the recorded replaced set, and verify the leaf landed
// on the recorded conditioned key. Pre-validates every grounding
// BEFORE mutating, so a stale entry in live mode returns false with
// the leaf untouched (the caller then searches fresh); in strict mode
// any divergence panics — the recorded row's conditioning no longer
// reproduces, which is an engine drift to fix, never to re-search.
func (c *conditioner) applyPlanEntry(root *GoalStackNode,
	leaf *GoalStackNode, entry *ByConditionPlanProto) bool {
	strict := c.env.RequireCNFCacheHit
	var loadMeta func(core.TermName) (core.ConstTermMeta, bool)
	if c.env.ProofService != nil {
		loadMeta = c.env.ProofService.LoadConstMeta
	}
	reader := ext.NewPoolReader(entry.Pool, loadMeta)
	// The entry's terms are under the leaf's canonical free names
	// (prop.CanonicalFreeRenaming); read them back under its own.
	_, back := prop.CanonicalFreeRenaming(leaf.Goal)
	term := func(ref uint32) core.Term {
		t := reader.Term(ref)
		if t == nil {
			return nil
		}
		return t.Substitute(back...)
	}
	fail := func(format string, args ...any) bool {
		if strict {
			panic(fmt.Sprintf("By[S4]: the recorded conditioning plan no longer applies — "+
				format+"\nThe executor no longer reproduces the recorded grounding "+
				"(engine drift): re-record the member; do NOT re-search at replay.", args...))
		}
		return false
	}
	specs := make([]SpecializeHyp, 0, len(entry.Groundings))
	descs := make([]string, 0, len(entry.Groundings))
	for gi, g := range entry.Groundings {
		hypTerm := term(g.Hyp)
		if hypTerm == nil {
			return fail("grounding %d has no hyp term in the plan pool", gi)
		}
		idx, err := findHypIndex(leaf.Goal, hypTerm)
		if err != nil {
			return fail("grounding %d: %v", gi, err)
		}
		wits := make([]core.Term, len(g.Witnesses))
		for i, w := range g.Witnesses {
			wits[i] = term(w)
		}
		pl := ematch.Plan{Hyp: hypTerm, Witnesses: wits}
		if !pl.Valid(leaf.Goal.Hyp(idx)) {
			return fail("grounding %d's witness tuple no longer type-matches %s",
				gi, clipRunes(ext.PrintTerm(hypTerm), 60))
		}
		specs = append(specs, InstHyp(idx, wits...))
		descs = append(descs, fmt.Sprintf("applied recorded grounding of %s",
			clipRunes(ext.PrintTerm(hypTerm), 60)))
	}
	if len(specs) > 0 {
		// A false return means every instance is already resident —
		// deterministic on the recorded leaf, so replay reproduces
		// whichever way record time went; proceed to the clears.
		ApplySpecialize(leaf, specs, true)
	}
	var replaced []core.Term
	for ri, r := range entry.Replaced {
		t := term(r)
		if t == nil {
			return fail("replaced entry %d has no term in the plan pool", ri)
		}
		replaced = append(replaced, t)
	}
	c.clearReplaced(root, replaced)
	if entry.ConditionedGoalKey != "" {
		wl := byWorkingLeaf(root, c.claimLeaves())
		if wl == nil || string(planKey(wl.Goal)) != entry.ConditionedGoalKey {
			got := "<leaf closed>"
			if wl != nil {
				got = string(planKey(wl.Goal))
			}
			// Post-mutation divergence cannot fall back to a fresh
			// search (the leaf is already transformed): loud in both
			// modes, naming the drift.
			panic(fmt.Sprintf("By[S4]: applying the recorded conditioning plan landed on %s, "+
				"but the plan records conditioned key %s — the executor no longer reproduces "+
				"the recorded conditioning (engine drift): re-record the member.",
				got, entry.ConditionedGoalKey))
		}
	}
	if c.s4 != nil {
		c.s4.describe = append(c.s4.describe, descs...)
	}
	return true
}

// persistConditionPlans writes the attempt's live-searched plan
// entries to the CNF store's plan table. Called only after the whole
// composite closed (a failed or fallback attempt records nothing) and
// only outside strict replay. The write-time oracle: each built proto
// is decoded back and compared against what was actually applied —
// the recorder remains the oracle for the plan artifact exactly as it
// is for certificates (meaningful because the stage is deterministic).
func (c *conditioner) persistConditionPlans() {
	if c.s4 == nil || len(c.s4.pending) == 0 ||
		c.env.RequireCNFCacheHit || cnfCacheOnlyProbe(c.ctx) ||
		byAuditProbe(c.ctx) {
		return
	}
	svc := c.env.ProofService
	if svc == nil || svc.CNFStore == nil {
		return
	}
	for _, pend := range c.s4.pending {
		b := ext.NewPoolBuilder()
		entry := &ByConditionPlanProto{
			ConditionedGoalKey: string(pend.conditionedKey),
		}
		for _, g := range pend.groundings {
			gp := &ByGroundingProto{Hyp: b.TermRef(g.Hyp.Substitute(pend.canon...))}
			for _, w := range g.Witnesses {
				gp.Witnesses = append(gp.Witnesses, b.TermRef(w.Substitute(pend.canon...)))
			}
			entry.Groundings = append(entry.Groundings, gp)
		}
		for _, r := range pend.replaced {
			entry.Replaced = append(entry.Replaced, b.TermRef(r.Substitute(pend.canon...)))
		}
		entry.Pool = b.Pool()
		verifyPlanEntryRoundTrip(entry, pend, c.env)
		svc.CNFStore.WritePlan(pend.bareKey, entry)
		noteCNFGoal(svc.CNFStore, pend.bareKey, pend.bareGoal)
		noteRecordPlan(c.ctx, pend.bareKey)
	}
}
