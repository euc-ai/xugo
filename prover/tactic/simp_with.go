// simp_with — the simplifier: rewrite the goal's
// CONCLUSION with an ORDERED lemma set, jointly, to fixpoint — including
// CONDITIONAL rules whose side conditions are discharged from the goal's
// hypotheses, from fact lemmas in the set, or by the set's own
// unconditional rewrites reducing the condition to ⊤.
//
// Rule shapes accepted (per conjunctive clause, after the outer ∀-strip):
//
//   - l = r / l ⇔ r                     unconditional rewrite
//   - P (any other boolean)             fact: oriented to P ⇔ ⊤ by
//     ContextEqRewriteOpt AND usable as a
//     side-condition discharge oracle
//   - C₁ ⇒ … ⇒ Cₖ ⇒ ∀ys. (l = r)       conditional rewrite (Horn form: a
//     telescope of ⇒ chains and ∀ blocks
//     in alternation, every ∀ block met
//     on the way joining the rule's
//     binders — a structure law stated
//     `S(comps) ⇒ ∀x. body`, and a guarded
//     one, `S(comps) ⇒ ∀x. x ∈ c ⇒ body`,
//     whose telescope is two segments)
//   - ¬C₁ ∨ … ∨ ¬Cₖ ∨ (l = r)          conditional rewrite (clause form —
//     the normalized shape)
//   - C₁ ⇒ … ⇒ Cₖ ⇒ ∀ys. A             closure rule (the Horn or clause
//     shape with an ATOM for its
//     matrix — a structure's closure
//     condition `x ∈ c ∧ y ∈ c ⇒
//     x * y ∈ c`): it rewrites nothing
//     and discharges a side condition
//     of the set's conditional
//     rewrites, route (d) below
//
// Conditional rules fire by INSTANCE MINING rather than in-walk discharge:
// each round, l is matched (ext/unify.TermMatchApprox — the deterministic
// HO-pattern fragment plus HOL term_match's first-order reading of a
// ∀-bound head applied to arguments, so a structure law's `op(x, e)`
// matches `add(a, zero)` with op := add) against the conclusion's subterm
// enumeration. The match pins the binders l mentions; a binder l leaves
// free — a component that appears only on the equation's right side, the
// `zero` of `add(neg(x), x) = zero` — is pinned by the SIDE CONDITIONS:
// each condition mentioning an unpinned binder is matched, bindings so
// far in hand, against the goal's hypotheses and then against the ground
// fact rules in the set (an assumption read as a matcher — the
// resident `abelian_group(G)` says what zero is). Every
// complete instantiation so found is a candidate instance; a binder no
// condition pins is never invented. Each side condition Cᵢσ must then
// discharge via
//
//	(a) α-match against a goal hypothesis,
//	(b) full-pin match against a fact clause of the rule set, or
//	(c) the UNCONDITIONAL rewrites reducing Cᵢσ to ⊤ (depth 1 — mined
//	    instances and conditional rules do not participate, so condition
//	    discharge cannot recurse), or
//	(d) a CLOSURE rule of the set whose conclusion matches Cᵢσ, its
//	    remaining binders pinned as a conditional rule's are and each of
//	    its antecedent instances discharged by these same routes — the
//	    carrier-membership decision: `x * inv(x) ∈ c` from `x ∈ c` by the
//	    closure of c under inv and then under *. An antecedent the goal
//	    does not hold must be a smaller term than the condition it
//	    derives, so the chain descends and terminates; no term is
//	    invented, and a rule whose antecedent is not smaller is not
//	    taken.
//
// A conjunctive antecedent (`x ∈ c ∧ y ∈ c ⇒ …`, the spelling of a
// structure's closure conditions) is read as its conjuncts, each a side
// condition discharged on its own, and the antecedent is rebuilt from
// them when the instance is derived.
//
// Mined ground equations join the unconditional rewrites and the loop
// re-runs (a fired unconditional rewrite can expose a conditional redex —
// the pattern of nat_sum's definition unfolding into monoidal.Union — and vice versa) until a
// round mines nothing new and rewrites nothing.
//
// Because SubTerms wraps binder-crossing subterms in their enclosing
// binders, a conditional redex mentioning an enclosing bound variable
// never matches a first-order LHS: conditional rules fire only at
// binder-closed positions. (Side conditions mentioning a bound variable
// could not be discharged from hypotheses anyway.) Unconditional rules
// reach under binders through the ContextEqRewriteOpt machinery as usual.
//
// Orientation: a rule fires in its written direction; the flip bit
// (SimpWithExpandFlipped) fires an equation right-to-left, and it applies
// to the conditional shapes as well as the plain equation — the
// normalizer keeps a bare variable on an equation's LEFT (`x = op(e, x)`),
// which is the expanding direction and a bare-binder LHS besides, so a
// structure law served in its normalized form collapses only flipped,
// while the same law served in its stated form (Go's Simp, the session's
// service of a registry entry) collapses unflipped.
//
// Determinism contract (the record/emit/replay-reuse principle): the
// whole pipeline is a pure function of (goal, rules) — rule order is the
// recorded slice order, subterm enumeration is ext.SubTerms order, goal
// hypotheses are read in the goal's order, all budgets are fixed policy
// constants, and no wall-clock or map iteration influences any decision.
// Replay re-runs THIS code on the recorded rule props and reconstructs
// the identical bridge.
//
// Termination: each round's joint rewrite runs under DeepRewriteWhistled
// (per-fire divergence whistle); the mining loop is bounded by
// simpMaxRounds/simpMaxInstances (policy fuses, cf. the FM byte/work
// budgets) — hitting a fuse stops mining deterministically and commits
// what fired. A round the whistle cuts ends the run and commits nothing:
// the rule set does not terminate on the goal, the term a cut leaves is
// no normal form, and a further round would open a fresh whistle on it,
// its budget the size the divergence had reached. The step is refused,
// and SimpCut says so.

package tactic

import (
	"context"
	"maps"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/ext/unify"
)

const (
	// simpMaxRounds bounds the mine-and-rewrite loop. Each extra round
	// requires the previous one to have mined a NEW conditional instance
	// or rewritten the conclusion; the sum shapes need 2–3.
	simpMaxRounds = 8
	// simpMaxInstances bounds the total mined conditional instances.
	simpMaxInstances = 64
)

// simpUncond is one unconditional clause: an equation/iff (rewrites in
// its written direction) or a boolean fact (oriented to ⇔⊤ by
// ContextEqRewriteOpt; also a discharge oracle via factVars/factBody).
type simpUncond struct {
	ruleIdx int
	clause  Prop
	rw      prop.Rewrite
	// Discharge-oracle view: the clause conclusion's ∀-strip, freshened.
	// factBody is nil when the clause is an equation (equations rewrite;
	// facts discharge — an equation used as a condition must reduce via
	// route (c)).
	factVars []core.VarTerm
	factBody core.Term
}

// _HornSegment is one segment of a Horn matrix's telescope: a chain of
// nImply ⇒ steps and the ∀ block of nInner binders directly below it
// (nInner is 0 when the equation, or the next chain, follows at once).
// Deriving an instance walks the segments in order: each ⇒ step is
// demoted to a hypothesis, then the block's binders are instantiated.
type _HornSegment struct {
	nImply, nInner int
}

// simpCond is one conditional clause (Horn or clause form).
type simpCond struct {
	ruleIdx int
	clause  Prop
	horn    bool
	// segs is the Horn matrix's telescope, in stated order; nil for the
	// clause form.
	segs []_HornSegment
	// Original binders, in binding order: the outer ∀ prefix first
	// (ConclForAllInsts order), then — Horn form only — every ∀ block
	// under an antecedent, segment by segment. nOuter counts the outer
	// ones.
	vars   []core.VarTerm
	nOuter int
	// Freshened matching view: vars α-renamed to collision-free names so
	// unify.TermMatch can treat them as the flexible set.
	freshVars []core.VarTerm
	lhs, rhs  core.Term   // freshened l, r
	conds     []core.Term // freshened side conditions, positive form
}

// simpMined is one mined ground instance of a conditional rule.
type simpMined struct {
	eq    core.Term // ground `lσ = rσ`
	rw    prop.Rewrite
	proof *prop.PropWrapper // Γ ⊆ goal hyps ⊢ lσ = rσ
	used  []int             // rule indexes cited by the instance derivation
}

type simpPipeline struct {
	goal Prop
	// read reads the record equations of the normal form the rewrite
	// hands over (InstanceNormal).
	read    LibraryRead
	rules   []Prop
	unconds []simpUncond
	conds   []simpCond
	// closures are the closure rules, in rule order: a conditional
	// record whose lhs is the conclusion atom and whose rhs is nil,
	// read by dischargeByClosure and never mined.
	closures []simpCond
	// preCNF is the one pre-CNF normalization cache every rule rewrite
	// of this set shares — the rules' and the mined instances' — so a
	// node the rules do not fire on is normalized once per set, not
	// once per rule (prop.ContextEqRewriteOpt). A step hands the one
	// cache to each run it makes of the set (simpWithExpandUnder), so
	// the node is normalized once for the step.
	preCNF *prop.PreCNFCache
	// uncondRws are the unconditional rewrites and the normal form: the
	// leaves of the depth-1 condition-discharge rewriter.
	uncondRws []prop.Rewrite
	// whistle builds the run's whistled rewrites, the rounds' joint
	// rewrite and the discharge rewriter.
	whistle  _WhistleDriver
	mined    []simpMined
	minedKey map[core.PropKey]bool
	// condDecide collapses a COND whose guard the goal's hypotheses
	// decide (prop.CondDecideByHyps under the capture-aware deep walk);
	// nil when the goal has no hypotheses. The resident guard is read
	// here exactly as a conditional rule's side condition is — α-match
	// against a goal hyp — so a rule set that unfolds a definition into
	// its COND (`card(insert(x, s)) = COND(x ∈ s, …)`) under a split's
	// resident guard leaves the decided branch, as def_expand's
	// residual pass does, instead of the COND with its guard beside it.
	condDecide prop.Rewrite
}

type simpResult struct {
	bridge *prop.PropWrapper // Γ ⊆ goal hyps ⊢ concl = newConcl
	used   []int             // rule indexes cited, ascending, deduped
}

// A _WhistleDriver builds a whistled rewrite over leaves:
// prop.DeepRewriteWhistled for a step's run, and its unreported form for
// the run that words a cut the step reported (SimpCut).
type _WhistleDriver func(anyHyp func(func(core.Term) bool) bool, rewrites ...prop.Rewrite) prop.WhistledRewrite

// SimpWithExpand is the zero-flip form of SimpWithExpandFlipped, kept as
// a thin wrapper so the many callers that never flip a rule (every
// pre-flip caller and every unit test) don't have to thread nil through.
func SimpWithExpand(goal Prop, rules []Prop) *SubGoals {
	return SimpWithExpandFlipped(goal, rules, nil)
}

// SimpWithExpandFlipped runs the simp-set pipeline on goal with the
// ordered rule set. flips is a parallel slice: flips[i]=true means the
// driver applies EqSym to rule i BEFORE mining, so `l = r` fires as
// `r → l`. nil / empty flips means all rules
// fire in their written direction — same behaviour as the zero-flip
// SimpWithExpand wrapper.
//
// Returns nil when no rule fires (or a discharge invariant fails — the
// step is progress-or-fail), OR when any flipped rule's ∀-stripped
// conclusion carries no equation to flip: a plain equation/iff, or the
// equation matrix of a conditional rule (Horn or clause form — see
// RuleFlippable). The SubGoals children on success are the
// USED rule statements (ascending rule order) in the NATURAL / stated
// direction — flip is a driver knob, not a rewritten statement, so the
// rule child α-matches the cited entry exactly as an unflipped rule
// would. Reconstruction re-runs the pipeline with proved rules
// substituted in, re-EqSym'ing the flipped ones so the driver-view
// stays consistent.
func SimpWithExpandFlipped(goal Prop, rules []Prop, flips []bool) *SubGoals {
	return SimpWithExpandFlippedReading(goal, rules, flips, nil)
}

// SimpWithExpandFlippedReading is SimpWithExpandFlipped with the record
// equations of the rewrite's normal form (InstanceNormal) read through
// read.
func SimpWithExpandFlippedReading(goal Prop, rules []Prop, flips []bool, read LibraryRead) *SubGoals {
	return simpWithExpandUnder(fullSearch, goal, rules, flips, read)
}

// SimpResidualReading is what the rule set leaves of goal: the last
// child of SimpWithExpandFlippedReading's step — of
// SimpWithExpandFlippedAtReading's at hypothesis *hyp when hyp is
// non-nil — or nil when the step is refused. The step is built as a
// probe's (makeSubGoalsAt): the driver runs once, the reconstruction is
// never run, and the child is read as a statement that no proof folds.
func SimpResidualReading(goal Prop, hyp *int, rules []Prop, flips []bool, read LibraryRead) Prop {
	probe := probeSearch(context.Background())
	var sub *SubGoals
	if hyp != nil {
		sub, _ = simpWithExpandAtUnder(probe, goal, *hyp, rules, flips, read)
	} else {
		sub = simpWithExpandUnder(probe, goal, rules, flips, read)
	}
	if sub == nil || sub.Size() == 0 {
		return nil
	}
	return sub.ChildGoal(sub.Size() - 1)
}

// simpWithExpandUnder is SimpWithExpandFlippedReading's step built
// under mode: gated as every step a proof folds is, or a probe's.
func simpWithExpandUnder(mode _SearchMode, goal Prop, rules []Prop, flips []bool, read LibraryRead) *SubGoals {
	driverRules, ok := simpDriverRules(goal, rules, flips)
	if !ok {
		return nil
	}
	// The step runs the driver here, for its children, and again in its
	// reconstruction, at the gate and for its theorem. The runs are one
	// function of the goal and the rules' statements, so they ask for
	// the normal forms of the same nodes, and share the cache that
	// holds them.
	preCNF := new(prop.PreCNFCache)
	res := runSimpPipeline(preCNF, goal, driverRules, read)
	if res == nil {
		return nil
	}
	newConcl := prop.Rhs(res.bridge)
	child := core.MakeProp(newConcl, goal.Hyps()...)
	// Children stay in the STATED orientation: report the natural-direction
	// rule props as the ministep's rule children so the session's
	// auto-close channels α-match them against the cited entry. The
	// residual keeps every hypothesis; the rule children carry no
	// provenance.
	children := make([]Prop, 0, len(res.used)+1)
	successors := make([][]int, 0, len(res.used)+1)
	for _, i := range res.used {
		children = append(children, rules[i].AsProp())
		successors = append(successors, nil)
	}
	children = append(children, child)
	successors = append(successors, keptSuccessors(goal, child))

	used := res.used
	// Snapshot the flip bits — the reconstruct closure runs later on
	// different Prop instances (proved thms), and must apply the same
	// per-index EqSym to stay in the driver-view.
	flipsCopy := append([]bool(nil), flips...)
	reconstruct := func(thms ...Prop) Prop {
		// thms = used-rule proofs (same order as `used`, natural
		// direction) + child proof last.
		//
		// A residual closed by contradiction concludes ⊥ where it states
		// the rewritten conclusion. It keeps the goal's hypotheses, so
		// that theorem is stronger than the goal as it stands, and the
		// bridge has no conclusion to carry back.
		residual := thms[len(thms)-1]
		if residual.Conclusion().Equals(F) && !newConcl.Equals(F) {
			return residual
		}
		// Substitute the rule proofs into the driver-view effRules:
		// unflipped indices take the proved thm directly; flipped indices
		// EqSym the proved thm to match the driver-view statement
		// classifySimpRules saw at record time.
		effRules := make([]Prop, len(rules))
		copy(effRules, driverRules)
		for k, i := range used {
			// A rule that carries hypotheses, a resident fact or a law
			// read under one, is re-run as the rule states it whatever
			// its child's theorem concludes.
			rule := lemmaAsStated(rules[i], thms[k])
			if i < len(flipsCopy) && flipsCopy[i] {
				effRules[i] = propFlipRule(rule)
			} else {
				effRules[i] = rule
			}
		}
		rb := runSimpPipeline(preCNF, goal, effRules, read)
		if rb == nil || !prop.Rhs(rb.bridge).AlphaEquals(newConcl) {
			// The pipeline is a pure function of (goal, rules-statements);
			// substituting proved rules with identical statements cannot
			// change any decision. Divergence here is an invariant breach.
			panic("SimpWithExpandFlipped: pipeline diverged at reconstruct time")
		}
		return rb.bridge.EqSym().EqMP(residual)
	}
	return makeSubGoalsAt(mode, goal, reconstruct, callSite(), successors, nil, children...)
}

// SimpRefusal is what a failing simp step adds to its no-progress
// message: the rules of the set refused as self-embedding whose left side
// matches one of targets (prop.RewriteRefusedOn), and the spellings that
// work. A conditional rule escapes the refusal because it fires at
// binder-closed positions only (the file comment). Empty when no rule
// was refused where it matches, so that "no rule fired" stands for a
// missing match. It reads the clauses the driver runs, flipped as the
// driver flips them, and decides nothing.
func SimpRefusal(goal Prop, rules []Prop, flips []bool, targets ...core.Term) string {
	driverRules, ok := simpDriverRules(goal, rules, flips)
	if !ok {
		return ""
	}
	var refused []string
	for _, uc := range classifySimpRules(new(prop.PreCNFCache), goal, driverRules, nil).unconds {
		concl := uc.clause.Conclusion()
		if slices.ContainsFunc(targets, func(target core.Term) bool { return prop.RewriteRefusedOn(concl, target) }) {
			if text := ext.PrintTerm(concl); !slices.Contains(refused, text) {
				refused = append(refused, text)
			}
		}
	}
	if len(refused) == 0 {
		return ""
	}
	return "Refused as a rewrite, its right side holding an instance of its left so that rewriting would not end: " +
		strings.Join(refused, "; ") + ". State the other side and close with By citing the rule; " +
		"a law read at a fact, cited bare, is a conditional rule and fires at binder-closed positions."
}

// SimpCut is what a failing simp step says when the divergence whistle
// ended its rewrite of one of targets, each the goal's conclusion or one
// of its hypotheses: that the rule set does not terminate there, at
// which firing it was cut, and what to change. Empty when no target's
// run was cut, so that "no rule fired" stands for a rule set with
// nothing to rewrite. It runs the driver on each target once more,
// unreported — the step has reported its cut — and decides nothing.
func SimpCut(goal Prop, rules []Prop, flips []bool, targets ...core.Term) string {
	for _, target := range targets {
		scratch := goal
		if !target.AlphaEquals(goal.Conclusion()) {
			hyp := slices.IndexFunc(goal.Hyps(), target.AlphaEquals)
			if hyp < 0 {
				continue
			}
			scratch = hypScratchGoal(goal, hyp)
		}
		driverRules, ok := simpDriverRules(scratch, rules, flips)
		if !ok {
			continue
		}
		if _, cut := runSimpPipelineUnder(prop.DeepRewriteWhistledUnreported, new(prop.PreCNFCache), scratch, driverRules, nil); cut != nil {
			return "The divergence whistle cut the rewrite at firing " + itoa(cut.Depth) + ", on a budget of " + itoa(cut.Budget) +
				": the rules went on rewriting what they had produced, so the rewriting would not end, and nothing of it is kept. " +
				"Leave out the rule that restores another rule's left side, or state the result and close with By citing the rules."
		}
	}
	return ""
}

// hypScratchGoal is the goal the driver runs on to rewrite hypothesis hyp
// of goal: the hypothesis as the conclusion, under the others.
func hypScratchGoal(goal Prop, hyp int) Prop {
	all := goal.Hyps()
	others := append(append([]core.Term{}, all[:hyp]...), all[hyp+1:]...)
	return core.MakeProp(goal.Hyp(hyp), others...)
}

// simpDriverRules is the driver's prelude: the rule list checked (non-empty,
// a flip vector of the rules' length, no rule α-equal to the goal — that
// would prove the goal by itself, circular as a rewrite; the agent wants
// `lemma`) and the driver-view rules built, flipped where requested.
// flipRuleLemma EqSym's the equation under ∀ (and under the conditional
// matrix), or returns nil when the rule carries no equation to flip (a
// fact, a conjunction whose body isn't a top-level equation) — a hard
// failure, flip asked for but not applicable.
func simpDriverRules(goal Prop, rules []Prop, flips []bool) ([]Prop, bool) {
	if len(rules) == 0 {
		return nil, false
	}
	if len(flips) != 0 && len(flips) != len(rules) {
		return nil, false
	}
	for _, r := range rules {
		if goal.AlphaEquals(r) {
			return nil, false
		}
	}
	driverRules := rules
	if hasAnyFlip(flips) {
		driverRules = make([]Prop, len(rules))
		for i, r := range rules {
			if flips[i] {
				fr := flipRuleLemma(r)
				if fr == nil {
					return nil, false
				}
				driverRules[i] = fr
			} else {
				driverRules[i] = r
			}
		}
	}
	return driverRules, true
}

// SimpWithExpandFlippedAt is SimpWithExpandFlipped at a HYPOTHESIS — Lean's
// `simp at h`: the rule set rewrites hypothesis hyp (0-based), its side
// conditions discharged against the OTHER hypotheses, and the goal keeps
// the rewritten hypothesis in its place. The driver runs on the scratch
// goal `others ⊢ h`, whose bridge `⊢ h = h'` (under some of the others)
// gives `{h} ⊢ h'`; the children are the used rules, stated, then the goal
// with h' for h; and the reconstruction derives the child's h' from h.
// The second result is h' itself: the kernel keeps a goal's hypotheses
// sorted and merges α-equal ones (core.MakeProp), so h' stands in the
// child wherever its content sorts, not at hyp, and a caller that goes
// on addressing it locates it by this term. Both results are nil when
// hyp is out of range, the rule list is refused, or no rule fires on h.
func SimpWithExpandFlippedAt(goal Prop, hyp int, rules []Prop, flips []bool) (*SubGoals, core.Term) {
	return SimpWithExpandFlippedAtReading(goal, hyp, rules, flips, nil)
}

// SimpWithExpandFlippedAtReading is SimpWithExpandFlippedAt with the
// record equations of the normal form (InstanceNormal) read through read.
func SimpWithExpandFlippedAtReading(goal Prop, hyp int, rules []Prop, flips []bool, read LibraryRead) (*SubGoals, core.Term) {
	return simpWithExpandAtUnder(fullSearch, goal, hyp, rules, flips, read)
}

// simpWithExpandAtUnder is SimpWithExpandFlippedAtReading's step built
// under mode (simpWithExpandUnder).
func simpWithExpandAtUnder(mode _SearchMode, goal Prop, hyp int, rules []Prop, flips []bool, read LibraryRead) (*SubGoals, core.Term) {
	if hyp < 0 || hyp >= goal.NumHyps() {
		return nil, nil
	}
	h := goal.Hyp(hyp)
	scratch := hypScratchGoal(goal, hyp)
	driverRules, ok := simpDriverRules(scratch, rules, flips)
	if !ok {
		return nil, nil
	}
	preCNF := new(prop.PreCNFCache)
	res := runSimpPipeline(preCNF, scratch, driverRules, read)
	if res == nil {
		return nil, nil
	}
	newHyp := prop.Rhs(res.bridge)
	images := hypImages(goal, hyp, newHyp)
	child := makeImageProp(goal.Conclusion(), images)
	// The rewritten hypothesis descends from hyp, every other stands as
	// it stood; the rule children carry no provenance.
	children := make([]Prop, 0, len(res.used)+1)
	successors := make([][]int, 0, len(res.used)+1)
	for _, i := range res.used {
		children = append(children, rules[i].AsProp())
		successors = append(successors, nil)
	}
	children = append(children, child)
	successors = append(successors, hypSuccessorsOf(child, images))
	used := res.used
	flipsCopy := append([]bool(nil), flips...)
	reconstruct := func(thms ...Prop) Prop {
		effRules := make([]Prop, len(rules))
		copy(effRules, driverRules)
		for k, i := range used {
			rule := lemmaAsStated(rules[i], thms[k])
			if i < len(flipsCopy) && flipsCopy[i] {
				effRules[i] = propFlipRule(rule)
			} else {
				effRules[i] = rule
			}
		}
		rb := runSimpPipeline(preCNF, scratch, effRules, read)
		if rb == nil || !prop.Rhs(rb.bridge).AlphaEquals(newHyp) {
			panic("SimpWithExpandFlippedAt: pipeline diverged at reconstruct time")
		}
		fromH := rb.bridge.EqMP(prop.Assume(h)) // {…, h} ⊢ h'
		return prop.WrapProp(fromH.MaybeDeriveTrans(thms[len(thms)-1]))
	}
	return makeSubGoalsAt(mode, goal, reconstruct, callSite(), successors, nil, children...), newHyp
}

// containsCond reports whether t carries a COND anywhere — the cheap
// gate before the capture-aware decide walk, which most rule sets on
// most goals never need.
func containsCond(t core.Term) bool {
	return ext.FindTopSubTerm(t, func(s core.Term) bool {
		_, _, _, ok := ext.MatchesCond(s)
		return ok
	}) != nil
}

func hasAnyFlip(flips []bool) bool {
	for _, f := range flips {
		if f {
			return true
		}
	}
	return false
}

// ClosureSimpClauses names the clauses of rule p that simp_with reads as
// CLOSURE rules: a Horn chain (`C₁ ⇒ … ⇒ Cₖ ⇒ A`) or a clause
// (`¬C₁ ∨ … ∨ A`) whose matrix under the antecedent is an atom
// (`finite(s) ⇒ finite(insert(x, s))`, the insert half of
// finite_set.FiniteRules; a structure's closure conditions). Such a
// clause rewrites nothing: it discharges a side condition of the set's
// conditional rewrites (route (d)). The engine names each such clause
// in the rule-set diagnostics at resolution, beside the multi-instance
// notes, so a no-progress failure is read at the rule set and not at
// the goal. Printed in the clause's own form.
func ClosureSimpClauses(p Prop) []string {
	var closures []string
	for _, c := range splitRuleClauses(p) {
		_, body := ext.DecomposesFORALL(c.Conclusion())
		if m, isCond := matchConditionalMatrix(body); isCond && !m.equation {
			closures = append(closures, prop.PrintProp(c))
		}
	}
	return closures
}

// RuleFlippable reports whether the flip bit applies to rule p: its
// ∀-stripped conclusion is a plain equation/iff, or a conditional matrix
// (Horn `C ⇒ … ⇒ ∀ys. l = r` or clause `¬C ∨ … ∨ l = r`) — in either
// case with l and r distinct. The engine's simp_with dispatch refuses a
// flip on any other shape up front, naming the entry.
func RuleFlippable(p Prop) bool {
	_, body := ext.DecomposesFORALL(p.Conclusion())
	if l, r, ok := MatchesEQ(body); ok {
		return !l.AlphaEquals(r)
	}
	m, isCond := matchConditionalMatrix(body)
	if !isCond || !m.equation {
		return false
	}
	l, r, _ := MatchesEQ(m.matrix)
	return !l.AlphaEquals(r)
}

// flipRuleLemma is the statement-level flip of a rule: the plain
// equation under ∀ through flipEqLemma, else the equation matrix of a
// conditional rule turned around in place. nil when the rule carries no
// equation to flip, or flipping changes nothing.
// FlipRuleLemma is flipRuleLemma for callers outside the driver —
// emit's Simp marker computation, which must turn a served rule around
// exactly as the driver will under Flipped.
func FlipRuleLemma(lemma Prop) Prop { return flipRuleLemma(lemma) }

func flipRuleLemma(lemma Prop) Prop {
	if fr := flipEqLemma(lemma); fr != nil {
		return fr
	}
	_, body := ext.DecomposesFORALL(lemma.Conclusion())
	if _, _, ok := MatchesEQ(body); ok {
		return nil // a plain equation flipEqLemma declined (l α= r, or a binder free in a hyp)
	}
	m, isCond := matchConditionalMatrix(body)
	if !isCond || !m.equation {
		return nil
	}
	l, r, _ := MatchesEQ(m.matrix)
	if l.AlphaEquals(r) {
		return nil
	}
	w := eqSymRewriteAt(m.matrix)(lemma.Conclusion())
	if w == nil {
		return nil
	}
	flipped := prop.Rhs(w)
	if flipped.AlphaEquals(lemma.Conclusion()) {
		return nil
	}
	return MakeProp(flipped, lemma.Hyps()...)
}

// propFlipRule is the proof-level twin of flipRuleLemma: from the PROVED
// rule it derives the flipped statement flipRuleLemma produced for the
// same rule — the plain equation by instantiate / EqSym / generalize,
// the conditional matrix by the same in-place rewrite.
func propFlipRule(thm Prop) Prop {
	_, body := ext.DecomposesFORALL(thm.Conclusion())
	if _, _, ok := MatchesEQ(body); ok {
		return propFlipEqUnderForall(thm)
	}
	m, _ := matchConditionalMatrix(body)
	return WrapProp(thm).RewriteConcl(eqSymRewriteAt(m.matrix))
}

// eqSymRewriteAt is the deep rewrite that turns the one equation α-equal
// to eq around (`l = r` ↦ `r = l`, by ⊢ (l = r) = (r = l)) wherever it
// sits in a statement — under the ∀ prefix, behind the Horn antecedents
// or beside the clause's negated conditions — and touches nothing else.
// Both the statement-level flip and the proof-level flip run this same
// rewrite, so the driver view a flipped rule was classified under and
// the theorem substituted for it at reconstruct time cannot differ.
func eqSymRewriteAt(eq core.Term) prop.Rewrite {
	return prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		if !t.AlphaEquals(eq) {
			return nil
		}
		l, r, ok := MatchesEQ(t)
		if !ok {
			return nil
		}
		// {r = l} ⊢ l = r and {l = r} ⊢ r = l; the deduction rule
		// cancels each hypothesis against the other's conclusion.
		fromRL := core.EqSym(core.Assume(Eq(r, l)))
		fromLR := core.EqSym(core.Assume(Eq(l, r)))
		return prop.WrapProp(core.Deduct(fromRL, fromLR))
	})
}

// anyRewriteHyp reads the hypotheses a rule rewrite carries: its clause
// term or mined equation, assumed until the bridge is discharged. The
// clause's own hypotheses enter at that discharge, after the walk, so no
// binder meets them.
func (pl *simpPipeline) anyRewriteHyp(pred func(core.Term) bool) bool {
	for i := range pl.unconds {
		if pred(pl.unconds[i].clause.Conclusion()) {
			return true
		}
	}
	for i := range pl.mined {
		if pred(pl.mined[i].eq) {
			return true
		}
	}
	return false
}

func runSimpPipeline(preCNF *prop.PreCNFCache, goal Prop, rules []Prop, read LibraryRead) *simpResult {
	res, _ := runSimpPipelineUnder(prop.DeepRewriteWhistled, preCNF, goal, rules, read)
	return res
}

// runSimpPipelineUnder is the driver with its whistled rewrites built by
// whistle, reading the normal forms of the nodes its rules fail on from
// preCNF (simpPipeline.preCNF). The second result is the cut that
// refused the run: the divergence whistle ended a round's joint rewrite,
// and nothing is committed. It is nil when the run ended any other way.
func runSimpPipelineUnder(whistle _WhistleDriver, preCNF *prop.PreCNFCache, goal Prop, rules []Prop, read LibraryRead) (*simpResult, *skeleton.WhistleEvent) {
	pl := classifySimpRules(preCNF, goal, rules, read)
	if pl == nil {
		return nil, nil
	}
	pl.whistle = whistle

	var bridge *prop.PropWrapper
	cur := goal.Conclusion()
	// ruleProgress records that the RULE SET moved the goal (a joint
	// rewrite or an instance mined); the COND decision below is a
	// consequence the context supplies, never progress on its own —
	// progress-or-fail is a statement about the rules.
	ruleProgress := false
	extend := func(u *prop.PropWrapper) {
		if bridge == nil {
			bridge = u
		} else {
			bridge = bridge.EqTrans(u)
		}
		cur = prop.Rhs(bridge)
	}
	for round := 0; round < simpMaxRounds; round++ {
		progressed := false

		// Joint rewrite: unconditional rules + mined instances + β.
		rewrites := make([]prop.Rewrite, 0, len(pl.unconds)+len(pl.mined)+1)
		for i := range pl.unconds {
			rewrites = append(rewrites, pl.unconds[i].rw)
		}
		for i := range pl.mined {
			rewrites = append(rewrites, pl.mined[i].rw)
		}
		rewrites = append(rewrites, InstanceNormal(pl.read))
		u, cut := pl.whistle(pl.anyRewriteHyp, rewrites...)(cur)
		if cut != nil {
			return nil, cut
		}
		if u != nil && !prop.Rhs(u).AlphaEquals(cur) {
			extend(u)
			progressed = true
			ruleProgress = true
		}

		// A COND whose guard the context decides collapses to its
		// branch (simpPipeline.condDecide). The equality carries the
		// deciding hyp, which the discharge below finds among the
		// goal's own; the decided branch may expose the next redex.
		if pl.condDecide != nil && containsCond(cur) {
			if u := pl.condDecide(cur); u != nil && !prop.Rhs(u).AlphaEquals(cur) {
				extend(u)
				progressed = true
			}
		}

		if pl.mineInstances(cur) {
			progressed = true
			ruleProgress = true
		}
		if !progressed {
			break
		}
	}

	if bridge == nil || !ruleProgress || prop.Rhs(bridge).AlphaEquals(goal.Conclusion()) {
		return nil, nil
	}

	// Discharge the bridge's hyps: fired clause terms against their
	// clauses, mined instance equations against their derivations.
	// Whatever remains must be a goal hypothesis.
	usedSet := map[int]bool{}
	for _, h := range bridge.Hyps() {
		if goal.HasHyp(h) {
			continue
		}
		if uc := pl.findUncondByConcl(h); uc != nil {
			bridge = bridge.DeriveHypFrom(uc.clause)
			usedSet[uc.ruleIdx] = true
			continue
		}
		if m := pl.findMinedByEq(h); m != nil {
			bridge = bridge.DeriveHypFrom(m.proof)
			for _, i := range m.used {
				usedSet[i] = true
			}
			continue
		}
		// A hyp we can't attribute (e.g. ContextEqRewrite normalized a
		// clause term into a shape that no longer α-matches it). Bail —
		// never emit an assumption-dependent bridge.
		return nil, nil
	}
	for _, h := range bridge.Hyps() {
		if !goal.HasHyp(h) {
			return nil, nil
		}
	}

	used := make([]int, 0, len(usedSet))
	for i := range rules {
		if usedSet[i] {
			used = append(used, i)
		}
	}
	return &simpResult{bridge: bridge, used: used}, nil
}

// classifySimpRules splits every rule into conjunctive clauses — a Horn
// clause pack under one antecedent included (splitRuleClauses) — and
// sorts each clause into the unconditional or conditional bucket.
// Freshening is deterministic (indexed counter). Returns nil only on an
// empty rule set.
func classifySimpRules(preCNF *prop.PreCNFCache, goal Prop, rules []Prop, read LibraryRead) *simpPipeline {
	pl := &simpPipeline{goal: goal, rules: rules, minedKey: map[core.PropKey]bool{}, preCNF: preCNF, read: read}
	if goal.NumHyps() > 0 {
		pl.condDecide = prop.DeepRewriteWithEnv(goal.AnyHyp, prop.CondDecideByHyps(goal.AnyHyp))
	}
	freshIdx := 0
	for ri, r := range rules {
		// NOT r.AsProp(): at reconstruct time the pipeline re-runs with
		// PROVED rules substituted in, and the clause split must preserve
		// their Thm-backing (the leanRwTacticMultiClause lesson — a bare
		// bridge from Thm inputs trips SubGoals.Reconstruct's assert).
		for _, c := range splitRuleClauses(r) {
			varList, body := ext.DecomposesFORALL(c.Conclusion())
			outer := varList.Section(0, varList.Size())
			m, isCond := matchConditionalMatrix(body)
			vars := append(append([]core.VarTerm(nil), outer...), m.inner...)
			if isCond && (!m.equation || (len(vars) > 0 && !conditionalLhsIsBareBinder(m.matrix, vars))) {
				l, rr := m.matrix, core.Term(nil)
				if m.equation {
					l, rr, _ = MatchesEQ(m.matrix)
				}
				fresh := make([]core.VarTerm, len(vars))
				substs := make([]core.TermSubst, len(vars))
				for i, v := range vars {
					fresh[i] = core.Var(core.TermName(string(v.Name())+"%simp"+itoa(freshIdx)), v.Type())
					freshIdx++
					substs[i] = core.MakeTermSubst(v, fresh[i])
				}
				fconds := make([]core.Term, len(m.conds))
				for i, cd := range m.conds {
					fconds[i] = cd.Substitute(substs...)
				}
				record := simpCond{
					ruleIdx: ri, clause: c, horn: m.horn, segs: m.segs,
					vars: vars, nOuter: len(outer),
					freshVars: fresh,
					lhs:       l.Substitute(substs...),
					conds:     fconds,
				}
				if m.equation {
					record.rhs = rr.Substitute(substs...)
					pl.conds = append(pl.conds, record)
				} else {
					pl.closures = append(pl.closures, record)
				}
				continue
			}
			// rw is filled in the post-pass below: the ordered channel
			// choice per clause (plain ordered vs AC-group ordered) needs
			// the WHOLE unconditional clause set (prop.SimpSetACGates).
			uc := simpUncond{ruleIdx: ri, clause: c}
			if _, _, isEq := MatchesEQ(body); !isEq {
				// Boolean fact — usable as a discharge oracle.
				fresh := make([]core.VarTerm, len(outer))
				substs := make([]core.TermSubst, len(outer))
				for i, v := range outer {
					fresh[i] = core.Var(core.TermName(string(v.Name())+"%simp"+itoa(freshIdx)), v.Type())
					freshIdx++
					substs[i] = core.MakeTermSubst(v, fresh[i])
				}
				uc.factVars = fresh
				uc.factBody = body.Substitute(substs...)
			}
			pl.unconds = append(pl.unconds, uc)
		}
	}
	// Ordered: a permutative clause (COMM/left-comm class) in a simp
	// set is applied with ordered rewriting — the fixpoint driver would
	// otherwise storm on it (the wedge met in a cardinality-of-a-union proof; LC variants slip
	// even the fire whistle's instance classifier). An ASSOC-class
	// rotation paired with a same-operator variants clause (an AC
	// group) is ordered too — ungated it un-sorts what the variants
	// fires sort, cycling around the AC class (the int_add_th storm);
	// a lone rotation keeps its written direction (SimpSetACGates).
	uncondConcls := make([]core.Term, len(pl.unconds))
	for i := range pl.unconds {
		uncondConcls[i] = pl.unconds[i].clause.Conclusion()
	}
	acGates := prop.SimpSetACGates(uncondConcls)
	for i := range pl.unconds {
		if acGates[i] {
			pl.unconds[i].rw = prop.ContextEqRewriteOrderedAC(pl.preCNF, uncondConcls[i], true, true)
		} else {
			pl.unconds[i].rw = prop.ContextEqRewriteOrdered(pl.preCNF, uncondConcls[i], true, true)
		}
	}
	pl.uncondRws = make([]prop.Rewrite, 0, len(pl.unconds)+1)
	for i := range pl.unconds {
		pl.uncondRws = append(pl.uncondRws, pl.unconds[i].rw)
	}
	pl.uncondRws = append(pl.uncondRws, InstanceNormal(pl.read))
	pl.whistle = prop.DeepRewriteWhistled
	return pl
}

// splitRuleClauses is splitConjunctiveClauses for a simp rule: a Horn
// law whose consequent is a conjunction — a clause pack under its
// structure hypothesis, `∀op. monoidal_op(op) ⇒ (iterated_op(op, ∅, f) =
// neutral_elem(op)) ∧ (∀x s. …)` — is one conditional rule per conjunct,
// each keeping the antecedent (⇒ distributed over ∧, under and around
// the ∀-prefixes, to fixpoint). The rule children the driver reports
// stay the pack itself (used rules are reported by index), so nothing
// on the wire changes; only what a pack can fire as does.
func splitRuleClauses(r Prop) []Prop {
	distributed := prop.WrapProp(r).RewriteConcl(prop.DeepRewrite(prop.ForAllANDRewrite, prop.ImplyANDRewrite))
	return splitConjunctiveClauses(distributed)
}

// conditionalLhsIsBareBinder rejects a conditional rule whose equation
// LHS is one of the rule's binders itself — such a pattern matches EVERY
// subterm of the right type (the same wrap-everything hazard unifyEq's
// variable-LHS ban guards against; cf. eq_rewrite.go).
func conditionalLhsIsBareBinder(eq core.Term, vars []core.VarTerm) bool {
	l, _, ok := MatchesEQ(eq)
	if !ok {
		return true
	}
	v, isVar := l.AsVar()
	return isVar && ext.NameInVars(vars, v.Name())
}

// _ConditionalMatrix is a conditional rule's matrix as the reader sees
// it: the positive side conditions in stated order (∧-antecedents
// flattened), the matrix — an equation (a conditional rewrite) or an
// atom (a closure rule), which equation tells apart — and, Horn form
// only, the telescope and the binders of its ∀ blocks in stated order.
type _ConditionalMatrix struct {
	conds    []core.Term
	inner    []core.VarTerm
	segs     []_HornSegment
	matrix   core.Term
	equation bool
	horn     bool
}

// isAtom reports whether t is a boolean atom: an application or a
// variable of type bool that is no connective, quantifier, equation or
// truth constant — what a closure rule concludes.
func isAtom(t core.Term) bool {
	if !ext.IsBool(t) || t.Equals(ext.T.Core()) || t.Equals(ext.F.Core()) {
		return false
	}
	if _, _, ok := MatchesEQ(t); ok {
		return false
	}
	if _, _, ok := ext.MatchesAND(t); ok {
		return false
	}
	if _, _, ok := ext.MatchesOR(t); ok {
		return false
	}
	if _, _, ok := ext.MatchesIMPLY(t); ok {
		return false
	}
	return ext.MatchesNOT(t) == nil && ext.MatchesFORALL(t).IsZero() && ext.MatchesEXISTS(t).IsZero()
}

// matchConditionalMatrix recognizes the two conditional-rule matrices:
// Horn `C₁ ⇒ … ⇒ Cₖ ⇒ ∀ys. C' ⇒ … ⇒ ∀zs. M` — ⇒ chains and ∀ blocks in
// alternation, read by the telescope the By executor's apply-close
// reads a hypothesis by (ematch.Telescope), so a guard stated under a
// structure law's inner ∀ (`S(comps) ⇒ ∀x. x ∈ c ⇒ M`) is a side
// condition like the structure fact before it — and clause
// `¬C₁ ∨ … ∨ ¬Cₖ ∨ M` (exactly one positive disjunct). The matrix M is
// an equation (a conditional rewrite) or an atom (a closure rule).
// Reports false for every other shape.
func matchConditionalMatrix(body core.Term) (_ConditionalMatrix, bool) {
	var m _ConditionalMatrix
	// Horn telescope: body carries no leading ∀ (the outer prefix is the
	// caller's), so each segment opens with at least one ⇒.
	cur := body
	for {
		seg := _HornSegment{}
		for {
			a, b, ok := ext.MatchesIMPLY(cur)
			if !ok {
				break
			}
			m.conds = append(m.conds, ext.DecomposesAND(a)...)
			seg.nImply++
			cur = b
		}
		if seg.nImply == 0 {
			break
		}
		block, rest := ext.DecomposesFORALL(cur)
		seg.nInner = block.Size()
		m.inner = append(m.inner, block.Section(0, block.Size())...)
		m.segs = append(m.segs, seg)
		cur = rest
	}
	if len(m.segs) > 0 {
		if _, _, ok := MatchesEQ(cur); ok {
			m.matrix, m.equation, m.horn = cur, true, true
			return m, true
		}
		if isAtom(cur) {
			m.matrix, m.horn = cur, true
			return m, true
		}
		return _ConditionalMatrix{}, false
	}
	// Clause form.
	ds := ext.DecomposesOR(body)
	if len(ds) < 2 {
		return _ConditionalMatrix{}, false
	}
	for _, d := range ds {
		if n := ext.MatchesNOT(d); n != nil {
			m.conds = append(m.conds, n)
			continue
		}
		if m.matrix != nil {
			return _ConditionalMatrix{}, false
		}
		if _, _, ok := MatchesEQ(d); ok {
			m.matrix, m.equation = d, true
			continue
		}
		if isAtom(d) {
			m.matrix = d
			continue
		}
		return _ConditionalMatrix{}, false
	}
	if m.matrix == nil || len(m.conds) != len(ds)-1 {
		return _ConditionalMatrix{}, false
	}
	return m, true
}

// mineInstances scans cur for new conditional-rule instances. Returns
// whether anything new was mined.
func (pl *simpPipeline) mineInstances(cur core.Term) bool {
	minedNew := false
	for ci := range pl.conds {
		c := &pl.conds[ci]
		if len(pl.mined) >= simpMaxInstances {
			break
		}
		flex := unify.TermNameSet{}
		for _, v := range c.freshVars {
			flex.Add(v.Name())
		}
		for st := range ext.SubTerms(cur) {
			if len(pl.mined) >= simpMaxInstances {
				break
			}
			if !st.Type().Equals(c.lhs.Type()) {
				continue
			}
			b := unify.MatchBindings{}
			if !unify.TermMatchApproxWith(c.lhs, st, flex, b) {
				continue
			}
			// The first-order reading of a flexible head is a candidate
			// the matcher does not verify: keep it only when the pinned
			// LHS is the subterm it matched, read up to β — a binder the
			// LHS applies (a predicate binder at the rule's own bound
			// variable, `∀s. R(s) ⇒ P(s)`) is bound to a λ, and the
			// pinned LHS holds the redex the subterm has reduced.
			if !betaNormal(c.lhs.Substitute(bindingSubsts(c.freshVars, b)...)).AlphaEquals(st) {
				continue
			}
			for _, full := range pl.completeBindings(c, b) {
				if len(pl.mined) >= simpMaxInstances {
					break
				}
				sigma := make([]core.Term, len(c.freshVars))
				substs := make([]core.TermSubst, len(c.freshVars))
				for i, v := range c.freshVars {
					sigma[i] = full[v.Name()]
					substs[i] = core.MakeTermSubst(v, sigma[i])
				}
				// The instance is mined in its β-normal form, the form the
				// conclusion spells; betaL and betaR carry the clause's own
				// instance to it.
				lhsC, rhsC := c.lhs.Substitute(substs...), c.rhs.Substitute(substs...)
				betaL, betaR := prop.DeepBeta(lhsC), prop.DeepBeta(rhsC)
				lhsI, rhsI := lhsC, rhsC
				if betaL != nil {
					lhsI = prop.Rhs(betaL)
				}
				if betaR != nil {
					rhsI = prop.Rhs(betaR)
				}
				if lhsI.AlphaEquals(rhsI) {
					continue
				}
				eqI := ext.WrapTerm(lhsI).Eq(rhsI).Core()
				key := core.MakeProp(eqI).AlphaKey()
				if pl.minedKey[key] {
					continue
				}
				condsI := make([]core.Term, len(c.conds))
				for i, cd := range c.conds {
					condsI[i] = cd.Substitute(substs...)
				}
				proof, usedIdx := pl.dischargeInstance(c, sigma, condsI)
				if proof == nil {
					continue
				}
				if betaL != nil {
					proof = betaL.EqSym().EqTrans(proof)
				}
				if betaR != nil {
					proof = proof.EqTrans(betaR)
				}
				pl.minedKey[key] = true
				pl.mined = append(pl.mined, simpMined{
					eq:    eqI,
					rw:    prop.ContextEqRewriteOpt(pl.preCNF, eqI, true, true),
					proof: proof,
					used:  usedIdx,
				})
				minedNew = true
			}
		}
	}
	return minedNew
}

// betaNormal is t with every β-redex reduced; t itself when it has none.
func betaNormal(t core.Term) core.Term {
	if beta := prop.DeepBeta(t); beta != nil {
		return prop.Rhs(beta)
	}
	return t
}

// bindingSubsts is the substitution the bindings b make on vars, in
// vars' order; a var b does not bind is left alone.
func bindingSubsts(vars []core.VarTerm, b unify.MatchBindings) []core.TermSubst {
	out := make([]core.TermSubst, 0, len(b))
	for _, v := range vars {
		if w, ok := b[v.Name()]; ok {
			out = append(out, core.MakeTermSubst(v, w))
		}
	}
	return out
}

// completeBindings extends the LHS match b to every complete
// instantiation of c's binders the side conditions pin. A condition
// that mentions an unpinned binder is matched, bindings so far in hand,
// against the goal's hypotheses in the goal's order and then against
// the ground fact rules in rule order; each match extends the bindings
// and the walk continues with the next condition. Conditions that
// mention no unpinned binder are discharge's business, not pinning's.
// A binder no condition pins leaves that path empty — the driver never
// invents a witness. Depth-first, in stated condition order; bounded
// by the instance fuse.
func (pl *simpPipeline) completeBindings(c *simpCond, b unify.MatchBindings) []unify.MatchBindings {
	if len(b) == len(c.freshVars) {
		return []unify.MatchBindings{b}
	}
	flex := unify.TermNameSet{}
	for _, v := range c.freshVars {
		flex.Add(v.Name())
	}
	hyps := pl.goal.Hyps()
	var out []unify.MatchBindings
	var walk func(i int, cur unify.MatchBindings)
	walk = func(i int, cur unify.MatchBindings) {
		if len(out) >= simpMaxInstances {
			return
		}
		if len(cur) == len(c.freshVars) {
			out = append(out, cur)
			return
		}
		if i == len(c.conds) {
			return
		}
		cd := c.conds[i]
		if !mentionsUnpinned(cd, c.freshVars, cur) {
			walk(i+1, cur)
			return
		}
		for _, h := range hyps {
			trial := maps.Clone(cur)
			if unify.TermMatchApproxWith(cd, h, flex, trial) {
				walk(i+1, trial)
			}
		}
		for k := range pl.unconds {
			uc := &pl.unconds[k]
			if uc.factBody == nil || len(uc.factVars) != 0 {
				continue
			}
			trial := maps.Clone(cur)
			if unify.TermMatchApproxWith(cd, uc.factBody, flex, trial) {
				walk(i+1, trial)
			}
		}
	}
	walk(0, b)
	return out
}

// mentionsUnpinned reports whether t mentions a var of vars that b does
// not bind.
func mentionsUnpinned(t core.Term, vars []core.VarTerm, b unify.MatchBindings) bool {
	for _, v := range vars {
		if _, ok := b[v.Name()]; ok {
			continue
		}
		if t.HasFree(v) {
			return true
		}
	}
	return false
}

// dischargeInstance builds the proved (or statement-derived) instance
// `Γ ⊆ goal hyps ⊢ lσ = rσ` from the conditional clause. Returns nil when
// any side condition fails all three discharge routes.
func (pl *simpPipeline) dischargeInstance(c *simpCond, sigma []core.Term, condsI []core.Term) (*prop.PropWrapper, []int) {
	used := []int{c.ruleIdx}
	// Per-condition proofs, gathered BEFORE touching the clause so a
	// failed condition costs no derivation work.
	//
	// A condition is discharged in its β-normal form: a binder the rule
	// APPLIES (`∀k x. Q(k(x)) ⇒ …`), bound to a λ by the match, leaves
	// the instance `Q((λy. t)(a))`, and a hypothesis, a fact or a
	// rewrite holds `Q(t[a])`. `back` carries a proof of the normal
	// form to the instance as the clause spells it.
	condProofs := make([]Prop, len(condsI))
	for i, cd := range condsI {
		target := cd
		back := func(p Prop) Prop { return p }
		if beta := prop.DeepBeta(cd); beta != nil {
			target = prop.Rhs(beta)
			back = func(p Prop) Prop { return beta.EqSym().EqMP(p) }
		}
		switch {
		case pl.goal.HasHyp(target):
			// Route (a): the bridge keeps the condition as a hyp —
			// nothing to derive where the instance is already normal.
			if target != cd {
				condProofs[i] = back(prop.Assume(target))
			}
		default:
			if p := pl.hypConjunct(target); p != nil {
				condProofs[i] = back(p)
				continue
			}
			if p := pl.hypRead(target); p != nil {
				condProofs[i] = back(p)
				continue
			}
			if p, ri := pl.dischargeByFact(target); p != nil {
				condProofs[i] = back(p)
				used = append(used, ri)
				continue
			}
			p, ris := pl.dischargeByRewrite(target)
			if p == nil {
				p, ris = pl.dischargeByClosure(target)
			}
			if p == nil {
				return nil, nil
			}
			condProofs[i] = back(p)
			used = append(used, ris...)
		}
	}

	inst := prop.WrapProp(c.clause).ConclForAllInsts(sigma[:c.nOuter]...)
	if c.horn {
		// Walk the telescope: each segment's ⇒ steps become hypotheses,
		// then its ∀ block takes the next slice of the instance.
		pos := c.nOuter
		for _, seg := range c.segs {
			for range seg.nImply {
				inst = inst.DemoteHyp()
			}
			if seg.nInner > 0 {
				inst = inst.ConclForAllInsts(sigma[pos : pos+seg.nInner]...)
				pos += seg.nInner
			}
		}
	} else {
		for _, cd := range condsI {
			inst = inst.MoveConclDisjComponentToHyp(cd)
		}
	}
	for i, cd := range condsI {
		if condProofs[i] != nil && inst.HasHyp(cd) {
			inst = inst.DeriveHypFrom(condProofs[i])
		}
	}
	// A conjunctive antecedent (`x ∈ c ∧ y ∈ c ⇒ …`) was demoted whole
	// while its conjuncts were discharged one by one: rebuild the
	// conjunction from the conjuncts' proofs and derive the hypothesis
	// from it. A conjunct the goal holds stays a hypothesis of the
	// instance, as a route (a) condition does.
	leaf := func(t core.Term) Prop {
		for i, cd := range condsI {
			if !cd.AlphaEquals(t) {
				continue
			}
			if condProofs[i] != nil {
				return condProofs[i]
			}
			return prop.Assume(t)
		}
		if pl.goal.HasHyp(t) {
			return prop.Assume(t)
		}
		if p := pl.hypConjunct(t); p != nil {
			return p
		}
		return pl.hypRead(t)
	}
	for _, h := range inst.Hyps() {
		if pl.goal.HasHyp(h) {
			continue
		}
		if p := proveConjunction(h, leaf); p != nil && inst.HasHyp(h) {
			inst = inst.DeriveHypFrom(p)
		}
	}
	// Every remaining hyp must be a goal hyp (route (a) conditions and
	// any hyps the rule prop itself carried).
	for _, h := range inst.Hyps() {
		if !pl.goal.HasHyp(h) {
			return nil, nil
		}
	}
	return inst, used
}

// hypConjunct discharges a condition that is a CONJUNCT of a goal
// hypothesis — `x ∈ c` where the goal holds `x ∈ c ∧ y ∈ c`, the one
// fact a structure law's proof holds its guards as — by ∧-elimination
// down the hypothesis: the proof `h ⊢ t`, whose hypothesis is the
// goal's. nil when no hypothesis has t as a conjunct; a hypothesis
// equal to t is the caller's case (HasHyp), not read here. The mirror
// of the apply rung's hypothesis split (proof.closeGoal, _SplitHypConj)
// and of the rule side above, where a conjunctive antecedent is read as
// its conjuncts.
func (pl *simpPipeline) hypConjunct(t core.Term) Prop {
	var found Prop
	pl.goal.AnyHyp(func(h core.Term) bool {
		if h.AlphaEquals(t) {
			return false
		}
		found = conjunctOf(h, t)
		return found != nil
	})
	return found
}

// hypRead discharges a condition the goal holds up to the record
// reading of the normal form (InstanceNormal): a hypothesis, or a
// conjunct of one, that spells a projection of a packed value as its
// author wrote it, `u ∈ free_module_record(c, S).carrier`, where the
// condition, a guard of a rule read at an instance, stands at the part,
// `u ∈ finite_supp(c.zero, c.carrier, S)`. Both sides are read, as a
// closer's leaf is (prover/proof, _RecordRead), and the proof runs
// through the kernel's equations read through pl.read, so the step's
// recorded dependencies hold them: `h ⊢ t`, its one hypothesis the
// goal's. nil where no hypothesis meets t in that reading; a pair the
// reading leaves as it is was compared by the routes before this one.
func (pl *simpPipeline) hypRead(t core.Term) Prop {
	nt := InstanceNormalTerm(t)
	var match core.Term
	pl.goal.AnyHyp(func(h core.Term) bool {
		nh := InstanceNormalTerm(h)
		if nh.AlphaEquals(h) && nt.AlphaEquals(t) {
			return false
		}
		if nh.AlphaEquals(nt) || conjunctOf(nh, nt) != nil {
			match = h
			return true
		}
		return false
	})
	if match == nil {
		return nil
	}
	read := InstanceNormal(pl.read)
	bridge := func(x core.Term) *prop.PropWrapper {
		if b := read(x); b != nil && !prop.Rhs(b).AlphaEquals(x) {
			return b
		}
		return nil
	}
	held := prop.Assume(match)
	if b := bridge(match); b != nil {
		held = b.EqMP(held)
	}
	readT, tBridge := t, bridge(t)
	if tBridge != nil {
		readT = prop.Rhs(tBridge)
	}
	var p *prop.PropWrapper
	switch {
	case held.Conclusion().AlphaEquals(readT):
		p = held
	default:
		c := conjunctOf(held.Conclusion(), readT)
		if c == nil {
			// The terms' reading met where the kernel's did not: the
			// two compute one normal form, and a gap between them is
			// the engine's.
			panic("hypRead: the record reading of " + ext.PrintTerm(match) +
				" meets " + ext.PrintTerm(t) + " as a term and not through the equations")
		}
		p = held.DeriveTrans(c)
	}
	if tBridge != nil {
		p = tBridge.EqSym().EqMP(p)
	}
	return p
}

// conjunctOf derives `h ⊢ t` for t a conjunct of the conjunction h, at
// any depth of its ∧-tree; nil when h is no conjunction or t is not in
// it.
func conjunctOf(h, t core.Term) Prop {
	l, r, ok := ext.MatchesAND(h)
	if !ok {
		return nil
	}
	if l.AlphaEquals(t) {
		return prop.HypAND0(l, r)
	}
	if r.AlphaEquals(t) {
		return prop.HypAND1(l, r)
	}
	if p := conjunctOf(l, t); p != nil {
		return prop.HypAND0(l, r).DeriveTrans(p)
	}
	if p := conjunctOf(r, t); p != nil {
		return prop.HypAND1(l, r).DeriveTrans(p)
	}
	return nil
}

// proveConjunction proves the conjunction h from proofs of its leaves:
// `l ∧ r` is proved from l and r by ∧-introduction, each side proved the
// same way down to a leaf, which leaf supplies (nil when it has none —
// then the whole is nil). A term that is not a conjunction is its own
// leaf.
func proveConjunction(h core.Term, leaf func(core.Term) Prop) Prop {
	l, r, ok := ext.MatchesAND(h)
	if !ok {
		return leaf(h)
	}
	pl, pr := proveConjunction(l, leaf), proveConjunction(r, leaf)
	if pl == nil || pr == nil {
		return nil
	}
	w := prop.ConclAND(l, r).DeriveHypFrom(pl)
	if w.HasHyp(r) {
		w = w.DeriveHypFrom(pr)
	}
	return w
}

// dischargeByClosure derives the condition cd from the closure rules,
// route (d): the first rule whose conclusion matches cd, its remaining
// binders pinned by its antecedents against the hypotheses and the
// facts (completeBindings), with every antecedent instance either held
// by the goal or a smaller term than cd — the measure the chain
// descends on — and discharged by the four routes in turn. Returns the
// proof `Γ ⊆ goal hyps ⊢ cd` and the rule indexes it cites, nil when no
// rule derives cd.
func (pl *simpPipeline) dischargeByClosure(cd core.Term) (Prop, []int) {
	for ci := range pl.closures {
		c := &pl.closures[ci]
		flex := unify.TermNameSet{}
		for _, v := range c.freshVars {
			flex.Add(v.Name())
		}
		b := unify.MatchBindings{}
		if !unify.TermMatchApproxWith(c.lhs, cd, flex, b) {
			continue
		}
		if !c.lhs.Substitute(bindingSubsts(c.freshVars, b)...).AlphaEquals(cd) {
			continue
		}
		for _, full := range pl.completeBindings(c, b) {
			sigma := make([]core.Term, len(c.freshVars))
			substs := make([]core.TermSubst, len(c.freshVars))
			for i, v := range c.freshVars {
				sigma[i] = full[v.Name()]
				substs[i] = core.MakeTermSubst(v, sigma[i])
			}
			condsI := make([]core.Term, len(c.conds))
			descends := true
			for i, cond := range c.conds {
				condsI[i] = cond.Substitute(substs...)
				if condsI[i].Size() >= cd.Size() && !pl.goal.HasHyp(condsI[i]) {
					descends = false
					break
				}
			}
			if !descends {
				continue
			}
			proof, usedIdx := pl.dischargeInstance(c, sigma, condsI)
			if proof == nil || !proof.Conclusion().AlphaEquals(cd) {
				continue
			}
			return proof, usedIdx
		}
	}
	return nil, nil
}

// dischargeByFact matches cd against each fact clause (full pin).
func (pl *simpPipeline) dischargeByFact(cd core.Term) (Prop, int) {
	for i := range pl.unconds {
		uc := &pl.unconds[i]
		if uc.factBody == nil || !ext.IsBool(cd) {
			continue
		}
		flex := unify.TermNameSet{}
		for _, v := range uc.factVars {
			flex.Add(v.Name())
		}
		b := unify.MatchBindings{}
		if !unify.TermMatchWith(uc.factBody, cd, flex, b, nil) {
			continue
		}
		if len(b) != len(uc.factVars) {
			continue
		}
		tau := make([]core.Term, len(uc.factVars))
		ok := true
		for k, v := range uc.factVars {
			w, has := b[v.Name()]
			if !has {
				ok = false
				break
			}
			tau[k] = w
		}
		if !ok {
			continue
		}
		p := prop.WrapProp(uc.clause).ConclForAllInsts(tau...)
		if !p.Conclusion().AlphaEquals(cd) || p.NumHyps() != 0 {
			continue
		}
		return p, uc.ruleIdx
	}
	return nil, 0
}

// dischargeByRewrite reduces cd to ⊤ with the UNCONDITIONAL rewrites
// (depth 1). The bridging clause terms are discharged in place; leftover
// hyps must be goal hyps. A rewrite the whistle cut discharges nothing.
func (pl *simpPipeline) dischargeByRewrite(cd core.Term) (Prop, []int) {
	if !ext.IsBool(cd) {
		return nil, nil
	}
	w, cut := pl.whistle(pl.anyRewriteHyp, pl.uncondRws...)(cd)
	if cut != nil || w == nil || !prop.Rhs(w).AlphaEquals(ext.T) {
		return nil, nil
	}
	condProof := w.EqSym().EqMP(prop.DerivesTrue)
	var used []int
	for _, h := range condProof.Hyps() {
		if pl.goal.HasHyp(h) {
			continue
		}
		if uc := pl.findUncondByConcl(h); uc != nil {
			condProof = condProof.DeriveHypFrom(uc.clause)
			used = append(used, uc.ruleIdx)
			continue
		}
		return nil, nil
	}
	for _, h := range condProof.Hyps() {
		if !pl.goal.HasHyp(h) {
			return nil, nil
		}
	}
	return condProof, used
}

func (pl *simpPipeline) findUncondByConcl(h core.Term) *simpUncond {
	for i := range pl.unconds {
		if pl.unconds[i].clause.Conclusion().AlphaEquals(h) {
			return &pl.unconds[i]
		}
	}
	return nil
}

func (pl *simpPipeline) findMinedByEq(h core.Term) *simpMined {
	for i := range pl.mined {
		if pl.mined[i].eq.AlphaEquals(h) {
			return &pl.mined[i]
		}
	}
	return nil
}

func itoa(i int) string {
	if i == 0 {
		return "0"
	}
	var buf [20]byte
	pos := len(buf)
	for i > 0 {
		pos--
		buf[pos] = byte('0' + i%10)
		i /= 10
	}
	return string(buf[pos:])
}
