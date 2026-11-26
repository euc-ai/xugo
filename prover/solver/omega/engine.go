package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// splitBranch is one arm of a 2-way split: an assumed `guard` (a comparison the
// branch may use, discharged at the end via PromoteHyp) plus `facts`, each a
// `{guard} ⊢ X` the engine feeds to the linear prover as a hypothesis and cuts
// back afterwards. The pin (atom = value) is always one of the facts.
type splitBranch struct {
	guard Term
	facts []*prop.PropWrapper
}

// splittableAtom is a recognized atom plus its split: a `⊢ g0 ∨ g1` disjunction
// (LessEqTotal, excluded middle, …) whose two disjuncts are the branch guards.
type splittableAtom struct {
	atom      Term
	disjProof *prop.PropWrapper
	branches  [2]splitBranch
}

// enrichAndCut is the shared core of the forward prover's "introduce a derived
// fact as an extra hyp, prove, then discharge it" pattern (proveLinDivMod /
// proveLinParity / proveSplit branches / proveDivModSplitOnZero). It appends
// each fact's conclusion to `hyps`, runs `prove` on the enriched list, and on
// success cuts every fact back via MaybeDeriveTrans — each fact is `{…} ⊢
// factConcl`, so the cut re-derives factConcl and leaves only the fact's own
// (provenance-preserving) hyps, never the bare injected conclusion. `prove`
// receives the enriched hyp slice and returns its proof or (nil,false).
func enrichAndCut(
	prove func([]Term) (*prop.PropWrapper, bool),
	hyps []Term,
	facts []*prop.PropWrapper,
) (*prop.PropWrapper, bool) {
	hyps2 := slices.Clone(hyps)
	for _, f := range facts {
		hyps2 = append(hyps2, f.Conclusion())
	}
	w, ok := prove(hyps2)
	if !ok {
		return nil, false
	}
	for _, f := range facts {
		w = prop.WrapProp(f.MaybeDeriveTrans(w))
	}
	return w, true
}

// splitByCases runs a 2-way split's branches through `branchProve` (each branch
// enriched with its facts via enrichAndCut) and recombines the two implications
// through ByCases — the shared assembly of every split site (proveSplit /
// proveBoolGoal and their int/real twins).
//
// PROOF-CORE PRUNING (certificate-directed backjumping — exact, threshold-free):
// a branch proof g is a kernel sequent whose hypothesis set is its exact
// dependency core — `Γ ⊢ goal` with Γ ⊆ hyps ∪ {branch guard}, because every
// branch fact is `⊢ X` or `{guard} ⊢ X` and enrichAndCut's cut-back replaces
// the injected conclusions with the facts' own hyps. So if the guard is absent
// from g.Hyps(), then Γ ⊆ hyps and g ALREADY witnesses `{hyps} ⊢ goal` by
// weakening: the case analysis is unnecessary — return g directly, skipping the
// sibling branch and the ByCases assembly. The effect cascades upward: the
// pruned proof's smaller hyp set lets the ENCLOSING split prune in turn, a
// backjump guided by the certificate rather than by any budget. This is what
// collapses the exponential product over irrelevant splits: an EM/hyp split
// whose guard no proof consumes would otherwise DOUBLE the work at every
// level; pruned, it costs one branch, and total cost tracks only the
// certificate-relevant structure. (A gcd-existence step shape: 10 resident
// implication hyps × int_abs guard splits — every hyp-split guard is absent
// from every leaf core, and unpruned each still multiplies the tree by 2. See
// TestIntSplitCorePruning.)
//
// ONE GUARD ON BOTH ARMS: a split can name the same guard twice — a hyp
// `a ≠ a` read as `a < a ∨ a < a`, a hyp `p ∨ p`, a hyp `p ⇒ ¬p` read as
// `¬p ∨ ¬p`. The disjunction is then `g ∨ g` and the analysis has one case:
// `ByCases(goal, g, g)` is `g ∨ g, g ⇒ goal ⊢ goal`, its two implications
// one hypothesis of the kernel's set, so the first arm's proof is the whole
// recombination and the second arm is not run.
//
// AN ARM THE HYPOTHESES DENY: a split's guard can be decided already — a
// second COND on an atom an enclosing split fixed, a hyp `p ∨ q` beside
// `¬p`. The arm whose guard a hypothesis denies holds a statement and its
// negation, which no carrier's prover reads where the statement is none of
// its own (a propositional variable, a membership); the arm is closed by
// that denial (deniedArm) and not handed to the provers.
func splitByCases(
	sa splittableAtom, hyps []Term, goal Term,
	branchProve func(h []Term) (*prop.PropWrapper, bool),
) (*prop.PropWrapper, bool) {
	g0, g1 := sa.branches[0].guard, sa.branches[1].guard
	arms := sa.branches[:]
	if g0.AlphaEquals(g1) {
		arms = arms[:1]
	}
	imps := make([]*prop.PropWrapper, 0, len(arms))
	for _, br := range arms {
		g, gok := deniedArm(hyps, br.guard, goal)
		if !gok {
			g, gok = enrichAndCut(branchProve, hyps, br.facts)
		}
		if !gok {
			return nil, false
		}
		if !slices.ContainsFunc(g.Hyps(), br.guard.AlphaEquals) {
			return g, true // guard-free core: already {hyps} ⊢ goal, no case split needed
		}
		imps = append(imps, g.PromoteHyp(br.guard)) // {hyps} ⊢ guard ⇒ goal
	}
	w := prop.ByCases(goal, g0, g1).DeriveHypFrom(sa.disjProof)
	for _, imp := range imps {
		w = w.DeriveHypFrom(imp)
	}
	return w, true
}

// deniedArm is `{h, guard} ⊢ goal` for a hypothesis h that denies guard:
// h is guard's negation, or guard is h's. ok=false where no hypothesis
// denies it.
func deniedArm(hyps []Term, guard, goal Term) (*prop.PropWrapper, bool) {
	for _, h := range hyps {
		held := guard
		if inner := prop.MatchesNOT(guard); inner != nil && inner.AlphaEquals(h) {
			held = h
		} else if inner := prop.MatchesNOT(h); inner == nil || !inner.AlphaEquals(guard) {
			continue
		}
		return prop.Contradict(held).DeriveTrans(prop.FalseDerives(goal)), true // {¬held, held} ⊢ goal
	}
	return nil, false
}

// caseSplit is one domain's case split: the recognizer of its splittable
// atoms, the two provers its branches are handed to, and the domain whose
// linear reader says where a pin reaches.
//
//   - prove is asked at every branch, before anything else: the pins may
//     already make the branch linear.
//   - leaf is asked at a branch that prove leaves open and that has nothing
//     left to split. It is the domain's handlers that read the hypotheses
//     and prove without re-entering the decide chain: the sign-known
//     nonlinear fragment and the products pass. A split made INSIDE an
//     enrichment passes nil, so the enrichment is not re-entered through
//     its own split.
//
// A branch is the root's question with more facts, and at the root that
// question went through the whole chain before the split was reached. The
// facts are ones no handler of the root's chain could read — a hypothesis
// split's disjunct (`s = &1`), an operator split's guard and pin (`&0 ≤ x`,
// `|x| = x`) — so the hypothesis-reading handlers are owed a second look,
// whichever split made the branch: `|x| ≤ c ∧ &0 ≤ w ⊢ x * w ≤ c * w` is
// the monotone handler's once `x ≤ c` is linear. The chain's goal-only
// handlers have declined the goal already, and the ones that re-enter the
// chain would re-enter the split.
//
// An operator's pin is a linear fact where the operator stands alone in a
// linear form. Where it stands inside an unknown of the linear reader, the
// branch is read at its pins first (pin_reading.go) and both provers are
// asked at the reading.
//
// The price is one run of leaf for a decision that declines, at the first
// branch left open: on the wide ε-δ context of the engine's
// TestInspect_ArithProbeOnWideRealContext, one more model of the products
// pass beside the root's for each such decision.
type caseSplit struct {
	domain *Domain
	first  func(hyps []Term, goal Term, done []Term) (splittableAtom, bool)
	prove  proveFn
	leaf   proveFn
}

// split attempts `{hyps} ⊢ goal` by eliminating ONE splittable atom via its
// disjunction. Each branch feeds its facts (pin + any guard bridge) to the
// provers, cuts them back, discharges the guard (PromoteHyp), and the two
// implications recombine through ByCases (with proof-core pruning — see
// splitByCases). `done` carries the already-split atoms so the recursion
// makes progress and terminates (each split pins one atom; the pins introduce
// no new splittable atom).
func (c caseSplit) split(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	sa, ok := c.first(hyps, goal, done)
	if !ok {
		return nil, false
	}
	return c.splitAt(sa, hyps, goal, splitPath{done: done})
}

// splitPath is what the splits above a branch have fixed: the atoms split,
// and the pin of each operator among them (pin_reading.go).
type splitPath struct {
	done []Term
	pins []Term
}

// splitAt splits sa under path. Each arm's hypotheses are hyps and then the
// arm's facts, a pin of sa.atom among them where sa is an operator's split.
func (c caseSplit) splitAt(sa splittableAtom, hyps []Term, goal Term, path splitPath) (*prop.PropWrapper, bool) {
	path.done = append(slices.Clone(path.done), sa.atom)
	return splitByCases(sa, hyps, goal, func(h []Term) (*prop.PropWrapper, bool) {
		arm := path
		if pin, ok := pinOf(sa.atom, h[len(hyps):]); ok {
			arm.pins = append(slices.Clone(path.pins), pin)
		}
		return c.branch(h, goal, arm)
	})
}

// branch closes one split branch: prove, else a further split, else — with
// nothing left to split — leaf, both provers asked at the branch's reading
// where a pinned operator stands inside an unknown. A branch still open is
// read at the rules its pairs of comparisons make (paired_equation.go): a
// guard of the branch and a comparison beside it may be an equation only
// the branch holds, as it alone holds its pins.
func (c caseSplit) branch(hyps []Term, goal Term, path splitPath) (*prop.PropWrapper, bool) {
	if w, ok := c.prove(slices.Values(hyps), goal); ok {
		return w, true
	}
	if sa, more := c.first(hyps, goal, path.done); more {
		return c.splitAt(sa, hyps, goal, path)
	}
	pins := path.pins
	if !c.domain.pinStandsInAnUnknown(hyps, goal, pins) {
		pins = nil
	}
	if len(pins) > 0 {
		if w, ok := c.atReading(readBranch(hyps, goal, pins, nil)); ok {
			return w, true
		}
	} else if c.leaf != nil {
		if w, ok := c.leaf(slices.Values(hyps), goal); ok {
			return w, true
		}
	}
	if rules := c.pairedRules(hyps); len(rules) > 0 {
		return c.atReading(readBranch(hyps, goal, pins, rules))
	}
	return nil, false
}

// atReading asks both provers at a branch's reading and carries what one
// proves back to the branch as spelled.
func (c caseSplit) atReading(r *pinReading) (*prop.PropWrapper, bool) {
	if w, ok := c.prove(slices.Values(r.hyps), r.goal); ok {
		return r.carryBack(w), true
	}
	if c.leaf == nil {
		return nil, false
	}
	if w, ok := c.leaf(slices.Values(r.hyps), r.goal); ok {
		return r.carryBack(w), true
	}
	return nil, false
}

// pairedRules is the rules the pairs of comparisons among a branch's
// hypotheses make at the split's carrier; none at a carrier that has no
// order.
func (c caseSplit) pairedRules(hyps []Term) []varSubst {
	policy := ArithPolicy{Nat: c.domain == natDomain, Int: c.domain == intDomain, Real: c.domain == realDomain}
	if !policy.Nat && !policy.Int && !policy.Real {
		return nil
	}
	rules := varEqSubsts(hyps, c.domain.isElem, nil, policy)
	return slices.DeleteFunc(rules, func(s varSubst) bool { return len(s.at) != 2 })
}

// proveSplit is the num case split (firstSplittable) with the given provers.
func proveSplit(prove, leaf proveFn, hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return caseSplit{domain: natDomain, first: firstSplittable, prove: prove, leaf: leaf}.split(hyps, goal, done)
}

// natProveLeaf is the num split's leaf prover. ℕ has no products pass, so a
// pin reaches a product by substitution: the branch's variable-sided
// equations are rewritten into the goal (eqHypSubst — the reading the root's
// driver gives a resident equation, which a pin made inside the split never
// met) and the goal so read goes to the ring and the linear prover, `s = 1`
// turning `s * s ≤ 4` into `1 * 1 ≤ 4`. Then the parity enrichment and the
// bounded-variable enumeration, which a pin can feed where the root's
// disjunction could not. An operator's pin is not variable-sided; where it
// stands inside an unknown the split reads the branch at it before this is
// asked (pin_reading.go).
func natProveLeaf(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hs, pred) }
	if w := prop.DeepRewriteWithEnv(anyHyp, eqHypSubst(hs, isNat, ArithPolicy{Nat: true}))(goal); w != nil { // {pins} ⊢ goal = read
		read := prop.Rhs(w)
		if l, r, ok := ext.MatchesEQ(read); ok && isNat(l) {
			if proof, ok := RingProveFull(l, r); ok {
				return w.EqSym().EqMP(proof), true
			}
		}
		if proof, ok := proveLinThenInt(slices.Values(hs), read); ok {
			return w.EqSym().EqMP(proof), true
		}
	}
	if w, ok := proveLinParity(hs, goal); ok {
		return w, true
	}
	// A branch's facts may be what a scaling's comparison or a
	// cancellation's positivity waited for (nat_scaling.go).
	if w, ok := natProveScaled(hs, goal); ok {
		return w, true
	}
	if w, ok := natProveCancelled(hs, goal); ok {
		return w, true
	}
	if cancelled := natCancelFacts(hs); len(cancelled) > 0 {
		if w, ok := enrichAndCut(
			func(h []Term) (*prop.PropWrapper, bool) { return proveLinThenInt(slices.Values(h), goal) },
			hs, cancelled); ok {
			return w, true
		}
	}
	return proveBoundedEnum(hs, goal)
}

// collectRawSubterms returns the distinct subterms (by α-equality, in walk order)
// of `terms` that satisfy pred, via a RAW structural walk over applied/abs nodes.
// Unlike ext.SubTerms it does NOT abstraction-wrap subterms under binders — it
// yields the bare subterm, treating bound and free occurrences identically, which
// is what omega's opaque-atom / variable collectors want (they match atom and
// variable shapes, not binder-aware patterns). The walk descends regardless of a
// match, so inner matches inside a matched subterm are kept. Shared by
// collectDivModAtoms (nat_divmod.go) and freeNumVars (nat.go); the split
// candidate collectors use collectBinderFreeSubterms below.
func collectRawSubterms(terms []Term, pred func(Term) bool) []Term {
	var out []Term
	var walk func(Term)
	walk = func(t Term) {
		if pred(t) && !slices.ContainsFunc(out, t.AlphaEquals) {
			out = append(out, t)
		}
		if app, ok := t.AsAppliedTerm(); ok {
			walk(app.Fun())
			walk(app.Arg())
			return
		}
		if abs, ok := t.AsAbsTerm(); ok {
			walk(abs.Body())
		}
	}
	for _, t := range terms {
		walk(t)
	}
	return out
}

// collectBinderFreeSubterms is collectRawSubterms restricted to subterms with
// NO free occurrence of an enclosing binder's variable. The raw walk still
// descends through abs bodies, but a matched subterm that mentions a variable
// bound by an enclosing λ/∀/∃ is SKIPPED: such an atom is useless as an
// excluded middle split candidate — assuming the capture-stripped atom (or its
// negation) can never decide the quantified formula it sits under, so the
// split burns branches without progress (and the int decide does not
// terminate on `(∃x. -n = d·x) ⇔ (∃x. n = d·x)`). The same
// α-shape occurring binder-free elsewhere in `terms` is still collected. Used
// by every split candidate collection — the bool-split atoms
// (comparisonAtomsOf / realComparisonAtomsOf / intComparisonAtomsOf) and the
// tautology-split operators (collectSplitCandidates / realFirstSplittable /
// intFirstSplittable): an opaque operator under a binder pins a term no
// constraint row mentions, so its split too only spends a level. On a wide
// real ε-δ context the raw walk made the `|·|` terms under the unfolded
// limit definitions' ∀x the FIRST candidates of every atom decision — eight
// useless levels ahead of the first closed one.
func collectBinderFreeSubterms(terms []Term, pred func(Term) bool) []Term {
	var out []Term
	var walk func(Term, []core.VarTerm)
	walk = func(t Term, bound []core.VarTerm) {
		if pred(t) && !slices.ContainsFunc(out, t.AlphaEquals) &&
			!slices.ContainsFunc(bound, t.HasFree) {
			out = append(out, t)
		}
		if app, ok := t.AsAppliedTerm(); ok {
			walk(app.Fun(), bound)
			walk(app.Arg(), bound)
			return
		}
		if abs, ok := t.AsAbsTerm(); ok {
			walk(abs.Body(), append(bound, abs.Var()))
		}
	}
	for _, t := range terms {
		walk(t, nil)
	}
	return out
}

// collectSplitCandidates returns the distinct binder-free subterms of `terms`
// that some tautology kind might split — any `a−b` / `nat_max a b` / `nat_min a b` /
// arith `COND` occurrence (inner ones treated as atoms; the kind constructors
// do the reducibility / guard-shape / supply filtering).
func collectSplitCandidates(terms []Term) []Term {
	return collectBinderFreeSubterms(terms, isSplitCandidate)
}

func isSplitCandidate(t Term) bool {
	if _, _, ok := MatchesMinus(t); ok {
		return true
	}
	if _, _, ok := MatchesMax(t); ok {
		return true
	}
	if _, _, ok := MatchesMin(t); ok {
		return true
	}
	// Raw arith COND `COND(guard, x, y) : num` (condSplittable). The kind
	// constructor does the guard-shape filtering; here we only need the type.
	if _, _, _, ok := ext.MatchesCond(t); ok && isNat(t) {
		return true
	}
	return false
}

// proveFn is the forward-prover shape both LinProve and OmegaProve satisfy.
type proveFn = func(iter.Seq[Term], Term) (*prop.PropWrapper, bool)

// preSimpHyps rewrites each hyp with a HYP-FREE rewrite, returning the simplified
// hyps (or h unchanged when nothing reduces) and the bridges `{h} ⊢ h'` to cut a
// post-decider PropWrapper's reference to h' back to h. Companion of
// bridgeBackHyps; together they extend the per-decider deep+fixpoint rewrite to
// also rewrite hyps under the same hyp-free leaves the goal-side stack already
// fires (the ext/prop `Rewrite` vs `RewriteConcl` distinction), so abs/sgn / pow
// / numeral / identity / sub-neg-move-across folds reach a hyp before linarith's
// shallow parseHypConstraint atomizes whatever's left.
//
// The rewrite MUST be hyp-free (no decideLeaf / eqHypSubst / boolsplit / disj):
// a hyp under its own assumption is trivially ⊤, which would collapse the hyp
// to ⊤ and silently drop a load-bearing assumption. The hyp-free leaves
// (identity-fold / numeral / abs-sgn / pow / div / move-across / β / bool / neg
// / cond / hilbert / quantifier) all return `⊢ h ⇔ h'` with no hyps, so the
// bridge `iff.EqMP(Assume(h))` is exactly `{h} ⊢ h'`.
//
// A hyp the rewrite leaves untouched returns simplified[i] = h, bridges[i] = nil
// — no kernel work, and bridgeBackHyps skips it.
func preSimpHyps(hyps []Term, hypFreeRewrite prop.Rewrite) (simplified []Term, bridges []*prop.PropWrapper) {
	simplified = make([]Term, len(hyps))
	bridges = make([]*prop.PropWrapper, len(hyps))
	for i, h := range hyps {
		w := hypFreeRewrite(h)
		if w == nil {
			simplified[i] = h
			continue
		}
		simplified[i] = prop.Rhs(w)
		bridges[i] = w.EqMP(prop.Assume(h)) // {h} ⊢ h'
	}
	return
}

// bridgeBackHyps cuts each `h' ∈ w.Hyps()` introduced by the simplified-hyp
// decider back to its original `h` via the bridges from preSimpHyps. A bridge
// whose h' doesn't appear in w (the decider didn't carry that hyp into its
// result) is a no-op via MaybeDeriveTrans. A nil bridge (hyp unchanged) is
// skipped. So the result's hyps stay ⊆ the ORIGINAL hyps, preserving the
// IsStronger contract callers (Linarith / Omega / the arith tactic) rely on.
func bridgeBackHyps(w *prop.PropWrapper, bridges []*prop.PropWrapper) *prop.PropWrapper {
	for _, br := range bridges {
		if br == nil {
			continue
		}
		w = prop.WrapProp(br.MaybeDeriveTrans(w))
	}
	return w
}

// ArithDecideWithHyps builds the unified arith deep rewrite under `hyps`.
// Composition (composeArithLeaves): one prop.BasicRewritesWithEnv call — all
// the standard basic rewrites (β / bool / cond / neg / quantifier / hilbert)
// PLUS the identity/numeral fold leaf (arithSimpStep) PLUS atom decision
// (arithDecideLeaf) and the other arith leaves, all driven through the shared
// deep rewrite (deep traversal + fixpoint). So the cascade
//
//	a + Cond(a=a, 0, 1)            ← original
//	→ a + Cond(⊤, 0, 1)            [arithDecideLeaf decides a=a]
//	→ a + 0                        [trivialCondRewrite]
//	→ a                            [arithSimpStep a+0]
//
// happens in a single call, no outer iteration. `hyps` empty → hyp-free
// decider (universally-valid/false atoms only).
//
// UNIFIED num + real dispatch: the leaf set dispatches PER ATOM by
// operand type — nat atoms to the nat leaves, real atoms to the real leaves —
// so a goal mixing both is simplified in one fixpoint pass (the `Domain` seam's
// two instantiations surfacing as one move). The real half is gated on a real
// bundle being installed; see composeArithLeaves.
//
// Capture-safe: this composes via prop.BasicRewritesWithEnv (the capture-aware
// DeepRewriteWithEnv), which threads the binder env and renames any goal binder
// whose bound var collides with a free var of a carried hyp — `anyHyp` reports
// those free vars over the whole `hyps` set. So a hyp-carrying decision (or the
// eqHypSubst leaf) lifting back through a same-named binder does not trip the
// kernel's `v ∉ FV(hyps)` assert during `.Abs()`.
//
// It is the PUBLIC entry — pre-simp + decider + bridge-back.
// Recursive internal callers that augment the hyp set (condPin family,
// proveBoundedEnum, etc.) use arithDecideWithHypsRaw instead; see
// intArithDecideWithHypsRaw for the rationale (pre-simp can fold a branch-pin
// hyp to ⊤ and break identity-keyed termination invariants downstream).
//
// The collapse leaves PLUS the formula-level bool-split deciders (nat.go /
// real.go) are passed as trailing constructors that bind to the
// post-preSimp hyp set inside composeArithLeaves, so all leaves see the same
// hyps. They are LAST so the cheaper leaves and BoolRewrite collapse every
// individually-decidable atom first; a bool leaf only fires on a genuinely
// contingent boolean (no atom decides alone), case-splitting it. They are NOT
// part of arithCollapseRewrite — proveBoolBranch / realProveBoolBranch
// collapse with THAT (bool leaves excluded), so each case-split recursion is
// driven by its own explicit `done` set, never by re-entering itself. The
// real and int bool leaves are gated like the other real and int leaves.
func ArithDecideWithHyps(hyps []Term) prop.Rewrite {
	return NewArithCtx(hyps).Decide
}

// ArithCtx is the reusable pre-simp'd hyp context for the arith decider. Build
// once via NewArithCtx(hyps); call Decide / DecideExcept any number of times.
// The preSimpHyps cost is paid ONCE at construction; each Decide / DecideExcept
// reuses the cached simplifiedHyps + bridges. This is the optimization arith
// callers that decide many targets against overlapping hyp sets (the canonical
// example: arithRewriteTactic, which decides the conclusion under all hyps THEN
// each hyp[i] under hyps\i) need to avoid redoing the per-hyp deep+fixpoint
// rewrite N+1 times. The single-shot ArithDecideWithHyps wrapper above remains
// for callers that only decide one target.
//
// preSimpHyps is hyp-free per hyp — the simplification of hyps[j] depends only
// on hyps[j], not on which OTHER hyps are in the decider's context. So slicing
// simplifiedHyps / bridges to drop index i is sound: it equals what
// preSimpHyps(hyps\i, …) would have produced. DecideExcept exploits this. The
// reading at the definitions depends on the definitions' own equations
// alone, so leaving out a hypothesis that is none of them is sound there
// too.
type ArithCtx struct {
	// hyps as written — the ground-congruence pass (congruence_subst.go)
	// reads its rules off these, not off their pre-simp'd forms.
	hyps           []Term
	simplifiedHyps []Term
	// bridges[j] is `{hyps[j]} ⊢ simplifiedHyps[j]`, nil where the
	// pre-simp left hyps[j] alone.
	bridges []*prop.PropWrapper
	// defs is hyps read at the definitions they hold (variable_subst.go),
	// nil where they hold none: the second reading a decision is tried
	// in. atDefs is its context, built when a decision first needs it.
	defs   *definitionReading
	atDefs *definitionContext
	// hypFreeSimp is the pre-simp of a hypothesis, kept for atDefs.
	hypFreeSimp prop.Rewrite
	policy      ArithPolicy
	// reader is the proof's reading of the record equations, for the
	// structure ring's facts; nil reads through the installed fallback.
	reader *LibraryReader
}

// definitionContext is the hypotheses read at the definitions, as the
// deciders meet them: simplified[j] the pre-simp of defs.read[j], and
// bridges[j] its `{hyps[j], definitions} ⊢ simplified[j]`, nil where
// hyps[j] reached the deciders unchanged.
type definitionContext struct {
	simplified []Term
	bridges    []*prop.PropWrapper
}

// NewArithCtx pre-simplifies hyps once and caches the simplifiedHyps + bridges
// for subsequent Decide / DecideExcept calls. The hyp-free simp matches
// ArithDecideWithHyps's exactly (arithSimpStep + parityBridge, plus
// realArithSimpStep when the real bundle is installed and allowed by policy.
// New corpus/live proof paths call NewArithCtxWithPolicy through ProofScope;
// this wrapper remains for low-level and compatibility callers.
func NewArithCtx(hyps []Term) *ArithCtx {
	return NewArithCtxWithPolicy(hyps, UnscopedArithPolicy(), nil)
}

// NewArithCtxWithPolicy is the lexical-scope constructor; reader is the
// proof's reading of the record equations (LibraryReader), nil for the
// installed fallback.
func NewArithCtxWithPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) *ArithCtx {
	var hypFreeLeaves []prop.Rewrite
	if policy.Nat {
		hypFreeLeaves = append(hypFreeLeaves, arithSimpStep, parityBridge)
	}
	if realLemmaBundle != nil && policy.Real {
		// realMoveAcrossLeaf matches the dedicated real hyp pre-simp
		// (RealArithDecideWithHyps), so a hyp like `a − b ≤ c` reaches
		// linarith's shallow parseHypConstraint in positive two-sided form.
		hypFreeLeaves = append(hypFreeLeaves, realArithSimpStep, realMoveAcrossLeaf)
	}
	if intLemmaBundle != nil && policy.Int {
		hypFreeLeaves = append(hypFreeLeaves, intArithSimpStep)
	}
	if policy.modulus() {
		// A hypothesis's modulus is pushed toward the leaves as the
		// goal's is (modulus.go), so the two meet as the same unknowns.
		hypFreeLeaves = append(hypFreeLeaves, modulusSimpStep)
	}
	hypFreeLeaves = append(hypFreeLeaves, groundComparisonDecide(policy))
	hypFreeSimp := prop.BasicRewritesWith(hypFreeLeaves...)
	simplifiedHyps, bridges := preSimpHyps(hyps, hypFreeSimp)
	return &ArithCtx{
		hyps: hyps, simplifiedHyps: simplifiedHyps, bridges: bridges,
		defs: readAtDefinitions(hyps, policy), hypFreeSimp: hypFreeSimp,
		policy: policy, reader: reader,
	}
}

// LeafReading is a leaf read at the definitions its hypotheses hold
// (variable_subst.go), for a caller that rewrites the leaf itself.
type LeafReading struct {
	// Hyps[j] is hypothesis j with every defined variable replaced; nil
	// for a definition's own equation, which defines a variable the read
	// leaf no longer names.
	Hyps []Term
	// Bridges[j] is `{hyps[j], definitions} ⊢ Hyps[j]`, nil where
	// hypothesis j names no defined variable or is a definition.
	Bridges []*prop.PropWrapper
	// Concl is `{definitions} ⊢ concl = concl′`, nil where the conclusion
	// names no defined variable.
	Concl *prop.PropWrapper
}

// LeafAtDefinitions reads the context's hypotheses and concl at the
// definitions the hypotheses hold; ok=false where they hold none.
func (c *ArithCtx) LeafAtDefinitions(concl Term) (LeafReading, bool) {
	if c.defs == nil {
		return LeafReading{}, false
	}
	leaf := LeafReading{Hyps: make([]Term, len(c.hyps)), Bridges: c.defs.bridges, Concl: c.defs.target(concl)}
	for j := range c.hyps {
		if !c.defs.defines[j] {
			leaf.Hyps[j] = c.defs.read[j]
		}
	}
	return leaf, true
}

// decideAsWritten rewrites t under the hypotheses as written, the one at
// skip (-1 for none) left out, and bridges the result back to them.
func (c *ArithCtx) decideAsWritten(skip int, t Term) *prop.PropWrapper {
	hyps, simplified, bridges := c.hyps, c.simplifiedHyps, c.bridges
	if skip >= 0 {
		hyps = slices.Concat(hyps[:skip:skip], hyps[skip+1:])
		simplified = slices.Concat(simplified[:skip:skip], simplified[skip+1:])
		bridges = slices.Concat(bridges[:skip:skip], bridges[skip+1:])
	}
	w := withCompoundEqSubst(hyps, arithDecideTargetWithHypsRawPolicy(simplified, t, c.policy, c.reader))(t)
	if w == nil {
		return nil
	}
	return bridgeBackHyps(w, bridges)
}

// decideAtDefinitions rewrites t read at the definitions, under the
// hypotheses read there too — the one at skip (-1 for none) and the
// definitions' own equations left out — and carries the result back to t
// and to hyps as written. nil where the decider did nothing with the
// read target: the reading alone is no rewrite.
func (c *ArithCtx) decideAtDefinitions(skip int, t Term) *prop.PropWrapper {
	if c.atDefs == nil {
		simplified, bridges := preSimpHyps(c.defs.read, c.hypFreeSimp)
		// {hyps[j], definitions} ⊢ read[j], then {read[j]} ⊢ simplified[j].
		for j, reading := range c.defs.bridges {
			switch {
			case reading == nil:
			case bridges[j] == nil:
				bridges[j] = reading
			default:
				bridges[j] = prop.WrapProp(reading.MaybeDeriveTrans(bridges[j]))
			}
		}
		c.atDefs = &definitionContext{simplified: simplified, bridges: bridges}
	}
	// The context: as read, which the ground-congruence pass takes its
	// rules off and carries; as pre-simp'd, which the deciders carry;
	// and the bridges from either form back to hyps as written.
	var read, simplified []Term
	var bridges []*prop.PropWrapper
	for j := range c.hyps {
		if j == skip || c.defs.defines[j] {
			continue
		}
		read = append(read, c.defs.read[j])
		simplified = append(simplified, c.atDefs.simplified[j])
		bridges = append(bridges, c.atDefs.bridges[j])
		if c.defs.bridges[j] != nil && !c.atDefs.simplified[j].AlphaEquals(c.defs.read[j]) {
			bridges = append(bridges, c.defs.bridges[j])
		}
	}
	target := t
	reading := c.defs.target(t) // {definitions} ⊢ t = target
	if reading != nil {
		target = prop.Rhs(reading)
	}
	w := withCompoundEqSubst(read, arithDecideTargetWithHypsRawPolicy(simplified, target, c.policy, c.reader))(target)
	if w == nil {
		return nil
	}
	w = bridgeBackHyps(w, bridges)
	if reading != nil {
		w = reading.EqTrans(w)
	}
	return w
}

// decides reports whether w rewrites its target to ⊤ or to ⊥.
func decides(w *prop.PropWrapper) bool {
	return w != nil && (prop.Rhs(w).Equals(prop.T) || prop.Rhs(w).Equals(prop.F))
}

// groundComparisonDecide is the hyp-free decision of a GROUND comparison
// atom — one with no variables: `1 ≤ 2`, `2 ≠ 0`, `&1 ≤ &2` — to ⊤ or ⊥.
// Deciding it consults no hypothesis, which is what makes it legal in the
// hyp pre-simp (preSimpHyps' contract) beside the numeral folds already
// there. It exists for a law's numeral guard: a Horn premise
// `(&1 ≤ x ∧ 1 ≤ 2) ⇒ …` reaches the decider with the guard folded away, so
// the case split on `&1 ≤ x` can use the premise; met unfolded, the split's
// negated antecedent `¬(&1 ≤ x ∧ 1 ≤ 2)` is not a comparison and the
// premise is dead to every branch — while the hyp loop, deciding the
// premise redundant under the others, retains it untouched.
func groundComparisonDecide(policy ArithPolicy) prop.Rewrite {
	var leaves []prop.Rewrite
	if policy.Nat {
		leaves = append(leaves, arithDecideLeaf(nil))
	}
	if realLemmaBundle != nil && policy.Real {
		leaves = append(leaves, realArithDecideLeaf(nil))
	}
	if intLemmaBundle != nil && policy.Int {
		leaves = append(leaves, intArithDecideLeafNoSignSplit(nil))
	}
	anyVar := func(core.VarTerm) bool { return true }
	return func(t Term) *prop.PropWrapper {
		if !isPureArithAtom(t) || len(t.Frees(anyVar)) > 0 {
			return nil
		}
		for _, leaf := range leaves {
			if w := leaf(t); w != nil {
				return w
			}
		}
		return nil
	}
}

// Decide rewrites t against the full pre-simp'd hyp context, then bridges hyps
// in the result back to their originals.
//
// A definition among the hypotheses gives a decision two readings
// (variable_subst.go), and neither is the stronger for a decider that
// searches to a bound: with `d` standing for a difference, `-2s ≤ d ≤ 2s`
// gives `d² ≤ 4s²` as one product of two hypotheses, which the same goal
// written out in the difference's terms does not; `t = &0` beside
// `t * A = &0` is decided only with t read as &0. So t is decided as the
// hypotheses spell it, and, where that does not decide it, with every
// defined variable read at its definition in t and in the context
// together. What that second reading decides is taken; a target it does
// not decide keeps the rewrite the first gave it, if any, so nothing is
// respelled at a definition by a decision.
//
// A target neither reading decides, and that denies a variable a value,
// is decided by the value read into the hypotheses (denied_value.go).
func (c *ArithCtx) Decide(t Term) *prop.PropWrapper {
	w := c.decideAsWritten(-1, t)
	if decides(w) {
		return w
	}
	if c.defs != nil {
		if at := c.decideAtDefinitions(-1, t); decides(at) {
			return at
		}
	}
	if denied := c.decideDeniedValue(t); denied != nil {
		return denied
	}
	return w
}

// DecideExcept rewrites t against the pre-simp'd hyp context with index i
// excluded, then bridges hyps in the result back to their originals. 0 <= i <
// len(hyps).
//
// It is how a hypothesis is read under the others, and the second reading
// (Decide) serves it one way only: a target the hypotheses as written
// leave alone, and that names a defined variable, is read at the
// definitions to find it contradictory. A hypothesis is not found
// redundant there, and is not rewritten there: read at a definition, a
// hypothesis the others then imply would be dropped for a fact the
// deciders may not find again.
func (c *ArithCtx) DecideExcept(i int, t Term) *prop.PropWrapper {
	w := c.decideAsWritten(i, t)
	if w != nil || c.defs == nil || c.defs.defines[i] || c.defs.target(t) == nil {
		return w
	}
	if at := c.decideAtDefinitions(i, t); at != nil && prop.Rhs(at).Equals(prop.F) {
		return at
	}
	return nil
}

// arithDecideTargetWithHypsRaw chooses the full decider only for targets whose
// whole formula has an arithmetic logical spine. Non-arithmetic targets still
// get the deep arithmetic simplifier, but not formula-level bool-split search.
func arithDecideTargetWithHypsRaw(hyps []Term, target Term) prop.Rewrite {
	return arithDecideTargetWithHypsRawPolicy(hyps, target, UnscopedArithPolicy(), nil)
}

func arithDecideTargetWithHypsRawPolicy(hyps []Term, target Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	if isPureArithFormula(target) {
		return arithDecideWithHypsRawPolicy(hyps, policy, reader)
	}
	return arithSimplifyWithHypsRawPolicy(hyps, policy, reader)
}

// arithSimplifyWithHypsRaw keeps the recursive arithmetic simplifier but
// excludes formula-level bool-split leaves.
func arithSimplifyWithHypsRaw(hyps []Term) prop.Rewrite {
	return arithSimplifyWithHypsRawPolicy(hyps, UnscopedArithPolicy(), nil)
}

func arithSimplifyWithHypsRawPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	return composeArithLeavesWithPolicy(hyps, policy, reader)
}

// isPureArithFormula is the gate for running formula-level bool-split. Pure
// arithmetic facts such as
// `∀x y z. x <= y - z ⇔ x + z <= y` may need the full decider so arith can drop
// them as tautological hyps. Higher-order facts with ε/λ predicate
// bodies should still get local arithmetic simplification, but not arbitrary
// case-split proof search inside those bodies.
func isPureArithFormula(t Term) bool {
	if t.AlphaEquals(prop.T) || t.AlphaEquals(prop.F) {
		return true
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		return isPureArithFormula(inner)
	}
	if l, r, ok := prop.MatchesAND(t); ok {
		return isPureArithFormula(l) && isPureArithFormula(r)
	}
	if l, r, ok := prop.MatchesOR(t); ok {
		return isPureArithFormula(l) && isPureArithFormula(r)
	}
	if l, r, ok := prop.MatchesIMPLY(t); ok {
		return isPureArithFormula(l) && isPureArithFormula(r)
	}
	if l, r, ok := ext.MatchesIFF(t); ok {
		return isPureArithFormula(l) && isPureArithFormula(r)
	}
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		return isPureArithFormula(abs.Body())
	}
	if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
		return isPureArithFormula(abs.Body())
	}
	return isPureArithAtom(t)
}

func isPureArithAtom(t Term) bool {
	return isPureArithDomainAtom(natDomain, isNat, t) ||
		isPureArithDomainAtom(realDomain, isRealTerm, t) ||
		isPureArithDomainAtom(intDomain, isIntTerm, t)
}

func isPureArithDomainAtom(d *Domain, isDomainTerm func(Term) bool, t Term) bool {
	if l, r, ok := d.matchLt(t); ok {
		return isPureArithTerm(l) && isPureArithTerm(r)
	}
	if l, r, ok := d.matchLe(t); ok {
		return isPureArithTerm(l) && isPureArithTerm(r)
	}
	if l, r, ok := d.matchGt(t); ok {
		return isPureArithTerm(l) && isPureArithTerm(r)
	}
	if l, r, ok := d.matchGe(t); ok {
		return isPureArithTerm(l) && isPureArithTerm(r)
	}
	if l, r, ok := prop.MatchesEQ(t); ok && isDomainTerm(l) {
		return isPureArithTerm(l) && isPureArithTerm(r)
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		if l, r, ok := prop.MatchesEQ(inner); ok && isDomainTerm(l) {
			return isPureArithTerm(l) && isPureArithTerm(r)
		}
	}
	return false
}

func isPureArithTerm(t Term) bool {
	if !core.MatchesHilbert(t).IsZero() {
		return false
	}
	if _, ok := t.AsAbsTerm(); ok {
		return false
	}
	if app, ok := t.AsAppliedTerm(); ok {
		return isPureArithTerm(app.Fun()) && isPureArithTerm(app.Arg())
	}
	return true
}

// arithDecideWithHypsRaw is ArithDecideWithHyps WITHOUT the hyp pre-simp pass,
// for recursive INTERNAL callers (condPin / proveBoundedEnum / proveBoundedExists)
// that augment the hyp set with a branch-pin or value-pin whose AlphaEquals
// identity downstream paths key on. See intArithDecideWithHypsRaw for the
// termination rationale.
func arithDecideWithHypsRaw(hyps []Term) prop.Rewrite {
	return arithDecideWithHypsRawPolicy(hyps, UnscopedArithPolicy(), nil)
}

func arithDecideWithHypsRawPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	var extra []func([]Term) prop.Rewrite
	if policy.Nat {
		extra = append(extra, func(hyps []Term) prop.Rewrite {
			return arithBoolLeafWithPolicy(hyps, policy, reader)
		})
	}
	if realLemmaBundle != nil && policy.Real {
		extra = append(extra, func(hyps []Term) prop.Rewrite {
			return realArithBoolLeafWithPolicy(hyps, policy, reader)
		})
	}
	if intLemmaBundle != nil && policy.Int {
		extra = append(extra, intArithBoolLeaf)
	}
	return composeArithLeavesWithPolicy(hyps, policy, reader, extra...)
}

// arithCollapseRewrite is ArithDecideWithHyps MINUS arithBoolLeaf: the deep
// atom-decision + bool-simplification used INSIDE the case split to collapse a
// branch's formula under its new atom-hypothesis (nat.go). Excluding the
// bool leaf here is load-bearing — it stops the split recursion from re-entering
// itself with a fresh (empty) `done`, which would defeat termination. Also raw
// (no pre-simp), for the same termination reason as arithDecideWithHypsRaw.
func arithCollapseRewrite(hyps []Term) prop.Rewrite {
	return arithCollapseRewriteWithPolicy(hyps, UnscopedArithPolicy(), nil)
}

func arithCollapseRewriteWithPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	return composeArithLeavesWithPolicy(hyps, policy, reader)
}

// composeArithLeaves builds the deep+fixpoint rewrite from the standard basic
// rewrites plus the arith leaves, optionally extended with `extraCtors`
// trailing-leaf constructors (arithBoolLeaf + optionally realArithBoolLeaf for
// the full decider; none for the in-branch collapse). `extraCtors` are
// CONSTRUCTORS over the hyp set so an extra leaf binds the SAME hyps the inner
// stack sees.
//
//   - eqHypValues  — a variable a hypothesis gives a value, `v = 2`,
//     reads as the value (variable_subst.go), at every carrier: an
//     opaque atom on v becomes an atom on a literal, which the simps
//     then evaluate. A definition by a term over other variables is read
//     by ArithCtx, in the target and the context together;
//   - condByHyps   — a COND whose guard, or its negation, is one of the
//     hyps is read at the arm the hyp selects (prop.CondDecideByHyps).
//     The deciders' own splits read arithmetic guards; this is the
//     guard that is no atom of theirs — a membership, an opaque
//     predicate. The dedicated ℝ and ℤ stacks carry the same leaf.
//   - parityBridge — nat_even/nat_odd → nat_mod-2;
//   - arithSimpStep / arithDecideLeaf — identity/numeral folds + atom decision;
//   - arithDisjLeaf — a disjunction goal `g0∨g1` (totality/trichotomy or a
//     directly-provable disjunct) reduces to ⊤ (nat.go).
//   - arithIffLeaf — a contingent comparison-iff `P⇔Q` reduces to ⊤ via the
//     two-direction Deduct. Last of the nat leaves, so an iff whose
//     side decides alone is folded by arithDecideLeaf + BoolRewrite first.
//   - the real, int and structure-ring leaves (below);
//   - formulaByHyps — a formula no arithmetic layer reads that is one
//     of the hyps reads ⊤, one whose negation is a hyp ⊥
//     (prop.FormulaDecideByHyps): a guard `x ∈ s ⇒ …` beside `x ∈ s`
//     reads as its consequent. A pure arithmetic formula is the
//     layers' alone.
//
// RAW: this function does NOT pre-simp hyps. Pre-simp is layered above it in
// ArithDecideWithHyps only. Recursive internal callers wire to either this
// (via arithDecideWithHypsRaw or arithCollapseRewrite) so an augmented hyp's
// AlphaEquals identity survives the recursion.
func composeArithLeaves(hyps []Term, extraCtors ...func([]Term) prop.Rewrite) prop.Rewrite {
	return composeArithLeavesWithPolicy(hyps, UnscopedArithPolicy(), nil, extraCtors...)
}

// composeArithLeavesWithPolicy composes the leaves policy admits; reader
// is the proof's reading of the record equations for the structure
// ring's facts, nil for the installed fallback.
func composeArithLeavesWithPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader,
	extraCtors ...func([]Term) prop.Rewrite) prop.Rewrite {
	// anyHyp over-approximates the hyps the leaves can carry (each carries a
	// subset of `hyps`): the capture-avoidance renaming fires only on an
	// actual name clash, so over-approximation is sound and cost-free in the
	// common case.
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	leaves := []prop.Rewrite{eqHypValuesUnder(hyps, policy), prop.CondDecideByHyps(anyHyp)}
	// A value a hypothesis gives a variable is read into the target
	// (variable_subst.go). Read off a stated equation the leaf cites no
	// lemma, so it stands at every carrier whatever the policy admits: a
	// proof of a foundation theorem still reads `v = 2` into its target.
	// A value two comparisons give is the linear prover's, and is read at
	// the carriers the policy admits. The bundle-backed leaves below are
	// gated. The COND leaf is bundle-free too.
	if policy.Nat {
		leaves = append(leaves,
			arithSimpStep, parityBridge,
			arithDecideLeaf(hyps), arithDisjLeaf(hyps), arithIffLeaf(hyps),
		)
	}
	// UNIFIED num + real dispatch: a real atom dispatches to the real leaves
	// (real.go), a nat atom to the leaves above — mutually exclusive by operand
	// type, so a goal mixing both is simplified in one fixpoint pass. GATED on
	// a real bundle being installed AND on the proof's ArithPolicy admitting it
	// (circularity.go: a proof in the real bundle's own foundation runs without
	// the real leaves). Both the full decider and the in-branch collapse
	// (arithCollapseRewrite) inherit real dispatch — both route through here.
	// The real bool-split leaf is not in this list: arithDecideWithHypsRaw
	// attaches it through extraCtors, as it does the nat and int ones.
	if realLemmaBundle != nil && policy.Real {
		// realMoveAcrossLeaf sits between simp and decide exactly as in the
		// dedicated real stack (realArithDecideWithHypsRaw): a `≥`/`>` bridge
		// or a subtraction/negation atom is first normalized to the positive
		// two-sided `<`/`≤` form the decide leaf's linear extractor consumes.
		// Without it the unified `arith` move declines goals like
		// `M ≤ M−&1 ⇔ −&1 ≥ &0` that RealArithDecide handles.
		// The decide leaf's prover is the policy's: where the policy reads
		// a modulus, every decision holds its sign, and what the carrier
		// shows of its argument, for the moduli in sight (modulus.go).
		leaves = append(leaves, realArithSimpStep, realMoveAcrossLeaf, realArithDecideLeafWith(hyps, policy.realProver(reader)))
	}
	// A modulus is rewritten by its laws toward the leaves (modulus.go):
	// the same leaf the hypothesis pre-simp carries, so a target and the
	// hypotheses it is decided under spell a modulus one way.
	if policy.modulus() {
		leaves = append(leaves, modulusSimpStep)
	}
	// UNIFIED int dispatch — twin of the real branch above. An int atom routes
	// to the int leaves (intArithSimpStep + intArithDecideLeafNoSignSplit); a
	// nat / real atom routes to its own leaves — mutually exclusive by operand
	// type, so a goal mixing nat/real/int is simplified in one fixpoint pass.
	// GATED on an int bundle being installed AND non-circular for the current
	// target; production today installs all three at startup. The
	// intArithBoolLeaf counterpart is attached via the extraCtors chain in
	// arithDecideWithHypsRaw, mirroring real.
	//
	// Why NoSignSplit (NOT the full intArithDecideLeaf): the full decider runs
	// intImageSplit + intProveBoundedEnum, both flagged in the README as
	// expensive when they "compound with the bool/int_abs splits into expensive
	// search". A deep+fixpoint rewrite over a goal with N nested int atoms (e.g.
	// a case of int_div_rem.DivByZero: many `int_div`/`int_rem`/`int_abs`/COND subterms)
	// fires the decide leaf per atom; with intImageSplit on, each atom can
	// branch on the sign of every int var, and each branch re-enters the full
	// stack with fresh ν vars — 4-way × per-atom × multi-pass explosion. The
	// restricted decider keeps every other handler (linear / ring / divrem /
	// monotone / divides) so common int goals still close; the
	// sign-split + bounded-enum stay reachable via the explicit
	// IntArithDecideWithHyps entry for callers that want them.
	if intLemmaBundle != nil && policy.Int {
		// intMoveAcrossLeaf mirrors the dedicated int stack
		// (intComposeArithLeavesWith) for the same reason as the real branch.
		leaves = append(leaves, intArithSimpStep, intMoveAcrossLeaf, intArithDecideLeafNoSignSplit(hyps))
	}
	// The structure ring (structure_ring.go): an equation at a carrier
	// that is a comm_ring_on, comm_ring or field by a fact resident in
	// hyps or installed — the ring chapters' rings and ℂ. Disjoint from
	// the three layers above by carrier type, so one fixpoint pass serves
	// a goal that mixes them (ℂ's real parts beside its ring).
	// Move-across first, as for real and int.
	if structureLaws != nil && policy.Structure {
		moveAcross, decide := structureLeaves(hyps, policy, reader)
		leaves = append(leaves, moveAcross, decide)
	}
	// A formula the context asserts reads ⊤, one whose negation it
	// asserts ⊥ (prop.FormulaDecideByHyps) — the COND leaf's rule for
	// every formula no arithmetic layer reads: a membership guard, an
	// opaque predicate. A pure arithmetic formula is left to the layers,
	// whose case splits assume such a formula as a branch hypothesis: a
	// branch that contradicts the context would read its own guard as
	// ⊤ here, and the split would decide what the layers do not.
	// Bundle-free like the COND leaf.
	formulaByHyps := prop.FormulaDecideByHyps(anyHyp)
	leaves = append(leaves, func(t Term) *prop.PropWrapper {
		w := formulaByHyps(t)
		if w == nil || isPureArithFormula(t) {
			return nil
		}
		return w
	})
	for _, ctor := range extraCtors {
		leaves = append(leaves, ctor(hyps))
	}
	// Two applications of one head meet where their arguments decide
	// equal (argument_congruence.go). The argument equations are asked of
	// this same rewrite, which the leaf reaches once it is built; the
	// leaf comes last, after every layer has had the formula.
	var whole prop.Rewrite
	leaves = append(leaves, argumentCongruence(hyps, policy, reader, func() prop.Rewrite { return whole }))
	// The decision's context is polled before each leaf is called: one
	// leaf call is the unit a cut waits for, and the argument
	// comparison's questions and the case splits' branches re-enter
	// rewrites built here, so their leaves poll too.
	if stop := utils.Stopper(policy.Stop); stop != nil {
		for i, leaf := range leaves {
			leaves[i] = func(t Term) *prop.PropWrapper {
				stop("inside an arith decision, before one of its leaves")
				return leaf(t)
			}
		}
	}
	whole = prop.BasicRewritesWithEnv(anyHyp, leaves...)
	return whole
}

// ArithDecide is the hyp-free entry point (used by tests and by callers
// without a hypothesis context): the unified deep+fixpoint rewrite with no
// hyps. Returns `⊢ t = t'`, or nil when nothing reduces.
func ArithDecide(t Term) *prop.PropWrapper { return ArithDecideWithHyps(nil)(t) }

// Contingent comparison-iff decision. A goal atom `P ⇔ Q` whose
// two sides are comparison/equality atoms that NEITHER decides alone, but whose
// EQUIVALENCE holds under the hyps — `(a < b) ⇔ (suc a ≤ b)`, `(a ≤ b) ⇔
// (a < suc b)`, `(a ≤ b) ⇔ (b ≤ a) ⊢ a = b` shapes. BoolRewrite only collapses
// an iff once a side has already reduced to ⊤/⊥ (via arithDecideLeaf), so a
// genuinely contingent equivalence — both sides depending on the variables —
// needs a dedicated leaf.
//
// It reuses the engine's iff-introduction, the same Deduct the structural
// ConclIffTactic uses to reconstruct an iff from its two directions: prove
// {hyps,Q} ⊢ P and {hyps,P} ⊢ Q in the comparison fragment, Deduct them to
// {hyps} ⊢ P ⇔ Q, and eqtIntro to `(P ⇔ Q) ⇔ ⊤`. NO new theorem — the
// directions go through the forward prover (proveDecAtom), which returns
// ok=false where a leaf lacks its theorem, so such an attempt declines.

// arithIffLeaf is the shallow leaf for a contingent comparison-iff `P ⇔ Q`:
// returns `⊢ (P ⇔ Q) ⇔ ⊤` when both directions prove, else nil.
func arithIffLeaf(hyps []Term) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		// `⇔` is `=` at bool; the IsLinComparisonGoal guards on BOTH sides pin t to
		// a bool iff of comparison atoms (a comparison is bool-typed), keeping this
		// disjoint from a num equality (handled by arithDecideLeaf).
		p, q, ok := ext.MatchesEQ(t)
		if !ok || !IsLinComparisonGoal(p) || !IsLinComparisonGoal(q) {
			return nil
		}
		if p.AlphaEquals(q) {
			return nil // reflexive iff — BoolRewrite's `(l=l) → ⊤` already folds it.
		}
		prove := proveDecAtom
		q2p, ok1 := prove(slices.Values(append(slices.Clone(hyps), q)), p) // {hyps,Q} ⊢ P
		if !ok1 {
			return nil
		}
		p2q, ok2 := prove(slices.Values(append(slices.Clone(hyps), p)), q) // {hyps,P} ⊢ Q
		if !ok2 {
			return nil
		}
		return eqtIntro(q2p.Deduct(p2q)) // {hyps} ⊢ (P ⇔ Q) ⇔ ⊤
	}
}
