package proof

// apply_close.go — Lean's `apply h; assumption`, run over the leaf's
// own context as the FIRST terminal move, before any closer (the apply rung of
// the manual's §"The conditioning stage of `by`").
//
// The terminal closers are search: the refuter rediscovers by
// saturation that a goal is an instance of a law whose antecedents
// are already resident. Lean never searches for that — `apply` unifies
// the law's conclusion against the goal, treating `∀x̄. A ⇒ ∀ȳ. B ⇒ C`
// as ONE function of x̄, ȳ and two proof arguments, and `assumption`
// discharges the arguments from the context; a binder the conclusion
// does not pin is a metavariable the assumptions solve. Here that is a
// pure kernel move, in two halves:
//
//   - PLAN (pure): telescope a candidate head (ematch.Telescope —
//     binders through guards, antecedents, conclusion), TermMatch the
//     conclusion against the goal, pin the remaining binders by
//     matching antecedents against the context, βη-canonicalize the
//     witnesses.
//   - DRY RUN (pure w.r.t. the real tree): on a scratch stack over the
//     same sequent, Specialize the head at the witnesses (the guarded
//     rung keeps every antecedent in place), read the instantiated
//     antecedents and conclusion off the kernel's own output, and
//     require the conclusion to be the goal — α-equal, or one statement
//     in the rung's normal form (rungReader.normal): βη, so a goal
//     spelled at `λi. F(i)` meets an instance at F, the witnesses
//     η-reduced along their spine, and the membership reading, so a goal
//     `P(a)` meets a conclusion `a ∈ {p | P(p)}`
//     (tactic.MembershipNormal), and the record reading, so a goal
//     spelled with a projection of a packed value,
//     `x ∈ mk_r(c).carrier`, meets a conclusion at the part, `x ∈ c`
//     (tactic.InstanceNormalTerm, the form a cited instance is handed
//     over in), and the numeral reading, so a goal spelled at `X(3)`
//     meets a conclusion at `X(2 + 1)` (omega.NumeralNormal, under the
//     proof's arithmetic policy) — closed by assumption through the kernel's
//     conversion, the leaf read first where a reading is what
//     identifies them (_MembershipRead, _RecordRead) — and every
//     antecedent to be supplied by the context — closed as a
//     goal of its own is (closeGoal): in the context already, up to the
//     same identity, or a conjunction of supplied parts, or a law opened
//     to a supplied conclusion, or the conclusion of one more apply
//     whose own antecedents the context holds.
//
// Only a head whose dry run succeeded is committed, by replaying the
// identical deterministic steps on the real leaf: Specialize, assert
// each antecedent and prove it by assumption, modus ponens down the
// head, close by assumption. No refuter, no CNF key, nothing recorded:
// replay re-runs the same move: it adds no trust and is a pure function of
// the leaf.
//
// Heads come from two places. Resident hypotheses — the goal's own
// antecedents, in the natural form the strips leave them. And the
// named premises' STATED forms: a premise's canonical install is its
// normalized form, which has no telescope (Normalize turns
// `A ⇒ ∀ȳ. B ⇒ C` into a prenex clause with the antecedents negated
// and any ∃! among them Skolemized), so the form the author actually
// named travels beside it as the premise's reference; a stated form
// that fires is installed on the leaf exactly (its types adapted to the
// goal only for an unpinned premise) and the claim that install
// leaves joins the composite's obligations — the By macro certifies it
// from the premise's own reference certificate.
//
// It declines — and the closers run exactly as before — when no head's
// conclusion matches, when a binder stays unpinned (a witness neither
// the goal nor the context spells is not the rung's to invent), or
// when an antecedent is not supplied by the
// context within the depth the rung closes to. A stated form that is
// the By's whole goal is no head at all (rungOpts.statesWhole): its
// claim would be that goal.
// Orientation is syntactic: `a = b` does not match `b = a`; that
// flexibility belongs to the closer's congruence layer.

import (
	"context"
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// applyHead is a named premise's STATED form — carried as the premise's
// reference beside its canonical (normalized) install.
type applyHead struct {
	stated   Prop
	describe string
	// exact preserves an explicitly chosen type instance, including
	// compound types whose remaining letters belong to the goal.
	exact bool
	// named seeds binders of the stated form by name (Fact.Where —
	// Lean's `apply law (R := r)`): the plan starts from these
	// bindings and reads the rest off the goal and the context. A
	// seeded head is an instruction, not a candidate: applyClose tries
	// the seeded heads alone, and a leaf none of them closes is
	// reported with the nearest miss rather than handed to a closer.
	named []NamedWitness
	// tuple is a witnessed premise's positional tuple (`law.At(w…)`),
	// read against the stated binders in order. The executor installs
	// such a premise in its clause form where the stated instance is
	// an ⇔ (the closers want it so), and the clause form has no
	// telescope; the stated form grounded at the tuple is the head the
	// author named. A candidate like any unseeded head: the plan
	// starts from the tuple's bindings, and a leaf it does not close
	// goes on to the closer.
	tuple []core.Term
}

// candidates retains an explicit type instance at every apply depth.
// Only an unpinned source is a schema for goal-driven type inference.
func (hd applyHead) candidates(goal Prop) []core.Prop {
	if hd.exact {
		return []core.Prop{hd.stated}
	}
	return headCandidates(hd.stated, goal)
}

// seeds is what the plan starts from: the binders pinned by name, or
// the positional tuple read against the stated binders.
func (hd applyHead) seeds() []NamedWitness {
	if len(hd.named) > 0 || len(hd.tuple) == 0 {
		return hd.named
	}
	binders, _ := ematch.StripGuardedForalls(hd.stated.Conclusion())
	if len(hd.tuple) > len(binders) {
		return nil
	}
	seeds := make([]NamedWitness, len(hd.tuple))
	for i, w := range hd.tuple {
		seeds[i] = NamedWitness{Binder: string(binders[i].Name()), Witness: w}
	}
	return seeds
}

// applyRun is one validated apply, ready to commit: the head's index
// on the sequent it was validated against, the witnesses, and the
// instantiated antecedents and conclusion as the KERNEL spells them.
type applyRun struct {
	witnesses  []core.Term
	ground     []core.Term
	conclusion core.Term
	// iffSide is the Horn reading of an ⇔-shaped conclusion the plan
	// took (headPlan.iffSide), and iffOther the side the context
	// supplies — the elimination commitApply finishes with.
	iffSide  int
	iffOther core.Term
	// flip is headPlan.flip: the goal is the head's equation read the
	// other way round, and commitApply opens with Symm.
	flip bool
	// conjunct is headPlan.conjunct: the goal is one conjunct of the
	// head's conclusion, which commitApply splits once it is resident.
	conjunct bool
	// through is the second half of a reading THROUGH an ⇔ side
	// (headPlan.through): the side the elimination makes resident, as
	// the kernel spells it, and the validated apply of that side to
	// the goal. nil for a reading that ends at the ⇔.
	through     *applyRun
	throughSide core.Term
	// throughHead is the law applied where the side read through is a
	// CONJUNCTION one of whose conjuncts is the law (headPlan.throughPart):
	// the side is split until it is resident. nil where the side whole
	// is the law.
	throughHead core.Term
	// applies is how many applies deep the antecedents were read — the
	// reading the commit supplies them by.
	applies rungOpts
}

// antecedentApplies is how deep the rung closes an antecedent: by one
// more apply, whose own antecedents are read with none — in the
// context, a conjunction of such, or a law opened to one. So the rung
// closes what is two applies away and no further, and an antecedent is
// closed exactly as a goal one apply shallower would be.
const antecedentApplies = 1

// byAssumption is the closed reading of an antecedent: in the context
// as written (up to βη), as a conjunct of one resident fact
// (heldAsConjunct), or a conjunction of such. The spine reads a
// grounded fact's guards so (dischargeGuards).
const byAssumption = -1

// rungOpts is how the rung reads an antecedent: depth is how many
// applies deep it may be closed (antecedentApplies at the top, one fewer
// inside each apply, byAssumption where only the context as written
// counts); arith says the door's closer is the arithmetic decider, so a
// guard the context does not hold as written may be decided by
// arithmetic under it (closeByArith), scope being the leaf's proof
// scope, which gates that decider as it gates the leaf's own close, and
// ctx the door's context, which cuts that decision off (deadline).
type rungOpts struct {
	depth int
	arith bool
	scope *ProofScope
	// ctx is the context of the request the door runs for; nil for a
	// door that runs for none.
	ctx context.Context
	// heads are the named premises' plain stated forms: the heads an
	// apply inside an antecedent may take beside the hypotheses
	// (closeGoal), each installed on the node it fires on. claims is
	// where the claim obligation such an install leaves is registered:
	// the By executor's list, or a scratch list under a dry run. Both
	// nil for the standalone doors, which read the hypotheses alone.
	heads  []applyHead
	claims *[]*GoalStackNode
	// whole is the goal the claims are obligations of — the By's own
	// (statesWhole). nil for the standalone doors.
	whole Prop
	// plain reads no numeral (reader): the reading of what a listed fact
	// itself states, where the numeral reading would answer for it
	// (_ListedSuppliers.suppliesDischarged).
	plain bool
}

// statesWhole reports whether lemma, a stated head at a type instance,
// is the goal the claims are obligations of. Installed, its claim would
// be that goal again — the goal its own obligation, which a composite
// cannot hand back (tactic.LemmaPreserveTactic declines a lemma that is
// its goal for the same reason). It is then no head of the rung: the
// leaf goes on to the closer, which proves it from the form the premise
// installed in.
func (o rungOpts) statesWhole(lemma core.Prop) bool {
	return o.whole != nil && o.whole.AlphaEquals(lemma)
}

// closed reports whether n is proved up to the claim obligations the
// rung registered under it: every open leaf of n is such a claim.
func (o rungOpts) closed(n *GoalStackNode) bool {
	if n.Proved() {
		return true
	}
	if o.claims == nil {
		return false
	}
	return len(byWorkingLeaves(n, *o.claims)) == 0
}

// deadline is the context an arithmetic decision of the rung polls: the
// door's, or one that is never done where the door has none.
func (o rungOpts) deadline() context.Context {
	if o.ctx == nil {
		return context.Background()
	}
	return o.ctx
}

// shallower is the reading one apply deeper in: one fewer to spend.
func (o rungOpts) shallower() rungOpts { o.depth--; return o }

// withDepth is the same door's reading at another depth.
func (o rungOpts) withDepth(d int) rungOpts { o.depth = d; return o }

// applyClose tries, as the head of an apply, every resident hypothesis
// of the working leaf and then every named premise's stated form.
// closed reports whether the leaf is proved on return (also true when
// there was no open leaf); diag carries the nearest miss for the
// failure diagnostics, empty when nothing came close.
func applyClose(root *GoalStackNode, claims *[]*GoalStackNode, heads []applyHead, rung rungOpts) (closed bool, diag string) {
	leaf := byWorkingLeaf(root, *claims)
	if leaf == nil {
		return true, ""
	}
	if rung.scope == nil {
		rung.scope = leaf.proofScope
	}
	goal := leaf.Goal
	target := goal.Conclusion()

	// A head pinned by name is the author's instruction to apply THAT
	// law: the seeded heads are tried alone, and a leaf none of them
	// closes is reported (the By executor turns the miss into its
	// failure) — never handed to a resident hypothesis or a closer
	// that would leave the instruction dead text.
	var seeded, plain []applyHead
	for _, hd := range heads {
		if len(hd.named) > 0 {
			seeded = append(seeded, hd)
		} else {
			plain = append(plain, hd)
		}
	}
	// An apply inside an antecedent may take a plain stated form as its
	// head too, and registers the claim its install leaves here.
	rung.heads, rung.claims, rung.whole = plain, claims, root.Goal
	if len(seeded) > 0 {
		for _, hd := range seeded {
			ok, miss := applyStatedHead(root, claims, leaf, hd, rung)
			if ok {
				return true, ""
			}
			if miss == "" {
				miss = fmt.Sprintf("apply-close: the conclusion of %s does not match the goal%s", hd.describe, abstractionEquationNote(goal))
			}
			diag = everyEquationNote(hd.stated.Conclusion(), miss)
		}
		return false, diag
	}

	// A goal the context holds is closed by assumption before any head
	// is read — Lean's `exact h`, the degenerate apply, no binders, no
	// antecedents; keyless where the refuter would have minted a key for
	// a sequent already closed. Read first, as closeGoal reads it: a head
	// tried before the resident goal is found can apply to it —
	// transitivity at a middle point equal to its end,
	// `R(a, c) ∧ R(c, c) ⇒ R(a, c)`, with R(a, c) resident and R(c, c)
	// by reflexivity.
	for i := range goal.NumHyps() {
		if rung.reader().same(goal.Hyp(i), target) {
			proveByAssumption(leaf)
			return true, ""
		}
	}
	// Resident hypotheses first: the goal's own antecedents (natural
	// form, where the strips left them) and any premise installed in
	// its stated form.
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		run, miss := planApply(goal, h, clipRunes(ext.PrintTerm(h), 80), nil, rung)
		if run == nil {
			if miss != "" {
				diag = everyEquationNote(h, miss)
			}
			continue
		}
		commitApply(leaf, i, run)
		return true, ""
	}

	// Then the named premises' stated forms, type-adapted to the goal
	// the way the install path adapts them, installed only on a fire.
	for _, hd := range plain {
		ok, miss := applyStatedHead(root, claims, leaf, hd, rung)
		if ok {
			return true, ""
		}
		if miss != "" {
			diag = everyEquationNote(hd.stated.Conclusion(), miss)
		}
	}
	// Last, the one closing procedure (closeGoal) on a leaf that spells a
	// set-builder membership — as an antecedent of its shape is closed: a
	// goal membership whose condition is a conjunction is read and closed
	// conjunct by conjunct, and one conjunct out of a resident such
	// membership by reading and splitting the hypothesis. The strips and
	// the heads above read the leaf as spelled only. Dry run on a clone
	// first: a leaf closeGoal does not close is left as far as it got.
	if leafSpellsMembership(goal) {
		var scratch []*GoalStackNode
		dry := rung
		dry.claims = &scratch
		if closeGoal(leaf.Clone(), dry) {
			if !closeGoal(leaf, rung) {
				panic(fmt.Sprintf("apply-close: the leaf did not close although its clone did (engine invariant)\n  leaf: %s",
					prop.PrintProp(goal)))
			}
			return true, ""
		}
	}
	// Last, a leaf the numeral reading closes — its goal reads ⊤, `0 < 2`,
	// or one of its hypotheses reads ⊥, `2 < 0`: nothing in the context
	// states it and no head applies to it, and there is nothing to find.
	if rung.reader().closes(goal) {
		if !closeByReading(leaf) {
			panic(fmt.Sprintf("apply-close: the numeral reading did not close a leaf it reads as closed (engine invariant)\n  leaf: %s",
				prop.PrintProp(goal)))
		}
		return true, ""
	}
	return false, diag
}

// leafSpellsMembership reports whether the membership reading changes
// the leaf: its conclusion or a hypothesis spells a membership in a
// set-builder.
func leafSpellsMembership(goal Prop) bool {
	if c := goal.Conclusion(); !tactic.MembershipNormal(c).Equals(c) {
		return true
	}
	return goal.AnyHyp(func(h core.Term) bool { return !tactic.MembershipNormal(h).Equals(h) })
}

// everyEquationNote qualifies the miss of a head whose conclusion
// equates two of its own binders — a spelled-out injectivity
// `∀u v. f(u) = f(v) ⇒ u = v`, antisymmetry, extensionality. Such a
// conclusion matches EVERY equation goal, so "matches the goal" is true
// of it at any equation and is no sign that it is the law the step
// needs. The miss stays: where the law was cited to prove this
// equation, the antecedent it names is the one to supply.
func everyEquationNote(head core.Term, miss string) string {
	if miss == "" {
		return miss
	}
	binders, _, concl, _ := ematch.Telescope(head, utils.EmptySet[core.TermName]())
	l, r, ok := ext.MatchesEQ(concl)
	if !ok {
		return miss
	}
	ownBinder := func(t core.Term) bool {
		v, isVar := t.AsVar()
		return isVar && slices.ContainsFunc(binders, func(b core.VarTerm) bool { return b.Name() == v.Name() })
	}
	if !ownBinder(l) || !ownBinder(r) {
		return miss
	}
	return miss + " (its conclusion equates two of its own binders, so it matches every equation: " +
		"that it matched is no sign it is the law this step needs)"
}

// applyStatedHead tries one named premise's stated form as the head of
// an apply on leaf: at the explicit instance, or each type instance
// the goal offers for an unpinned premise, plan
// (seeded by the head's named table, if any), and on a validated plan
// install the stated form exactly and commit. Returns the nearest miss
// when nothing fired.
func applyStatedHead(root *GoalStackNode, claims *[]*GoalStackNode, leaf *GoalStackNode, hd applyHead, rung rungOpts) (bool, string) {
	goal := leaf.Goal
	if hd.stated.NumHyps() > 0 {
		// A sequent-shaped reference — a law read under a resident
		// hypothesis, the sequent `h ⊢ law at h` (readingUnderPremise,
		// the macro's Read at a resident fact) — has no telescope of
		// its own: its hypothesis is not one of the stated conclusion's
		// antecedents. Out of the rung's scope.
		if len(hd.named) > 0 {
			return false, fmt.Sprintf("apply-close: %s states a sequent (hypotheses of its own), which the "+
				"apply rung cannot read as a telescope", hd.describe)
		}
		return false, ""
	}
	candidates := hd.candidates(goal)
	// A seeded head's pinned terms carry types of their own, and a
	// candidate instance that gives a pinned binder a different type
	// can never pass the plan. Keep the consistent candidates when there
	// are any — every instance the goal's anchors reach on their own is
	// still tried first — and only when none is consistent ask the
	// enumerator to complete the instance FROM the pinned types: a law
	// with two carrier letters is a coin toss read from the goal alone.
	seeds := hd.seeds()
	pins := pinnedBinderTypes(seeds)
	if !hd.exact && len(pins) > 0 && ext.PropHasTypeVars(hd.stated) {
		if consistent := consistentWithPins(candidates, pins); len(consistent) > 0 {
			candidates = consistent
		} else if pinnedInstances := typematch.EnumerateLemmaTypeAdaptationsPinned(hd.stated, goal, pins); len(pinnedInstances) > 0 {
			candidates = append(pinnedInstances, candidates...)
		}
	}
	if len(candidates) == 0 {
		if len(hd.named) > 0 {
			return false, fmt.Sprintf("apply-close: the goal offers no type instance of %s", hd.describe)
		}
		return false, ""
	}
	// The miss reported when nothing fires. A candidate whose type
	// instance already fits the pinned terms missed for a reason the
	// author can act on — an antecedent the context lacks, a conclusion
	// that does not match — where an inconsistent candidate's miss is
	// the coin toss itself: a type the goal alone chose, blamed on the
	// pinned term. So a consistent candidate's miss outranks the rest;
	// among misses of one rank the last stands, as it always has.
	diag, consistentMiss := "", ""
	for _, lemma := range candidates {
		stated := lemma.Conclusion()
		if rung.statesWhole(lemma) {
			diag = fmt.Sprintf("apply-close: %s states this goal whole, so its install would leave the goal as its own obligation", hd.describe)
			continue
		}
		if len(seeds) == 0 && goal.AnyHyp(stated.AlphaEquals) {
			// Already resident — the install's own instance of a bare
			// premise (installsAtOneInstance) — and so read by
			// applyClose's pass over the hypotheses.
			continue
		}
		// Validate against the sequent AS IT WILL BE once the
		// stated form is resident: the same goal with that one
		// hypothesis added. Nothing on the real tree moves yet.
		withHead := prop.MakeProp(goal.Conclusion(), append(goal.Hyps(), stated)...)
		run, miss := planApply(withHead, stated, hd.describe, seeds, rung)
		if run == nil {
			if miss != "" {
				diag = miss
				if len(pins) > 0 && len(consistentWithPins([]core.Prop{lemma}, pins)) > 0 {
					consistentMiss = miss
				}
			}
			continue
		}
		if commitStatedHead(leaf, lemma, stated, run, claims) {
			return true, ""
		}
	}
	if consistentMiss != "" {
		return false, consistentMiss
	}
	return false, diag
}

// commitStatedHead installs the stated form lemma on leaf as a
// HYPOTHESIS, verbatim (already at the goal's types) — the plain add
// the witnessed-premise path commits, not the preserving chain: the
// chain's conclusion-match strategy would apply a law whose conclusion
// is a predicate atom BACKWARDS (a projection `G(add, zero, neg) ⇒
// S(add, zero)` at the goal `S(add₀, zero₀)` leaves `G(add₀, zero₀,
// neg)` with neg free instead of the law resident), and the plan just
// validated then has no head to fire on — registers the claim
// obligation the install leaves on claims, and commits the validated
// run on the leaf the install leaves open, at the witnesses of the
// install. Reports false when the install refused, for the caller to
// try its next candidate.
func commitStatedHead(leaf *GoalStackNode, lemma core.Prop, stated core.Term, run *applyRun, claims *[]*GoalStackNode) bool {
	Assert(claims != nil)
	before := leaf.Goal
	sg := tactic.LemmaAddHypTactic(lemma)(leaf.Goal)
	if sg == nil || !leaf.commitStep(_LemmaPreserveTactic{lemma: lemma}, sg) {
		return false
	}
	*claims = append(*claims, collectClaimObligations(leaf)...)
	working := byWorkingLeaf(leaf, *claims)
	if working == nil {
		return true
	}
	idx, err := alphaHypIndex(working.Goal, stated)
	witnesses := run.witnesses
	if err != nil {
		// A statement with free variables installs as its ∀-closure
		// over them, ahead of the stated binders (the general form
		// the add installs). Locate the hyp the install added and
		// bring the closure down by identity — each closure binder
		// at the variable it closed over — so the instance the
		// dry run validated is the one the kernel takes.
		ni, lerr := newHypIndex(before, working.Goal)
		if lerr != nil {
			panic(fmt.Sprintf("apply-close: the stated form was installed but cannot be located (engine invariant): %v", lerr))
		}
		idx = ni
		witnesses = append(closureIdentityWitnesses(working.Goal.Hyp(ni), stated), run.witnesses...)
	}
	// The run as validated, at the witnesses of the install.
	installed := *run
	installed.witnesses = witnesses
	commitApply(working, idx, &installed)
	return true
}

// closureIdentityWitnesses returns identity witnesses for the ∀-prefix
// an install added ahead of a stated form's own leading binders — the
// closure over the statement's free variables — one per closure
// binder, each the binder's variable itself. Empty when the installed
// hyp carries no more leading binders than the stated form.
func closureIdentityWitnesses(installed, stated core.Term) []core.Term {
	leading := func(t core.Term) []core.VarTerm {
		var out []core.VarTerm
		for {
			abs := ext.MatchesFORALL(t)
			if abs.IsZero() {
				return out
			}
			out = append(out, abs.Var())
			t = abs.Body()
		}
	}
	inst, st := leading(installed), leading(stated)
	k := len(inst) - len(st)
	if k <= 0 {
		return nil
	}
	out := make([]core.Term, k)
	for i := range k {
		out[i] = inst[i]
	}
	return out
}

// planApply is the pure half: match head against goal's conclusion,
// pin every binder (from the named seeds, then the conclusion, then
// from antecedents against the context), canonicalize the witnesses,
// and dry-run the instantiation on a scratch stack to read the
// kernel's spellings and check them against the goal exactly. Returns
// the validated run, or nil with the nearest miss (empty when the
// head simply does not apply).
//
// The seeds (Fact.Where) are substituted into the telescope BEFORE the
// match — a binder the author fixed at a λ (a relation, a predicate)
// turns the pattern's flexible head into a β-redex, which reduces to a
// first-order pattern over the remaining binders; the matcher then
// sees exactly what Lean's elaborator sees after `(R := r)`.
func planApply(goal Prop, head core.Term, describe string, named []NamedWitness, rung rungOpts) (*applyRun, string) {
	return planApplyWith(goal, head, describe, named, rung.withDepth(antecedentApplies))
}

// planApplyWith is planApply with the depth its antecedents are read
// to: applies more applies may close an antecedent (closeGoal), so the
// apply inside an antecedent reads its own with one fewer, and the
// innermost with none.
func planApplyWith(goal Prop, head core.Term, describe string, named []NamedWitness, applies rungOpts) (*applyRun, string) {
	plans, miss := matchHeadReadings(applies.reader(), goal, head, describe, named, true)
	if len(plans) == 0 {
		return nil, miss
	}
	// Every reading of the head that matched the goal is pinned and
	// dry-run in turn: an ⇔'s first Horn reading may match the goal at a
	// side whose antecedent the context cannot pin, where its second
	// reading pins everything off the conclusion.
	for _, plan := range plans {
		if m := plan.pinWitnesses(describe); m != "" {
			if !plan.alternative {
				miss = m
			}
			continue
		}
		run, m := dryRunApply(goal, head, describe, plan, applies)
		if run != nil {
			return run, ""
		}
		if m != "" && !plan.alternative {
			miss = m
		}
	}
	return nil, miss
}

// headPlan is what the plan half pins: the telescope's binders and
// antecedents (still over the slots), the slot set, the witnesses read
// off the conclusion and the context in stated binder order, and the
// goal names the telescope was renamed away from.
type headPlan struct {
	binders   []core.VarTerm
	antes     []core.Term
	concl     core.Term
	slots     unify.TermNameSet
	bindings  unify.MatchBindings
	seeded    map[core.TermName]bool
	witnesses []core.Term
	avoid     utils.Set[core.TermName]
	// iffSide reads an ⇔-shaped conclusion as one of its two Horn
	// clauses: 0 the conclusion as stated; 1 `L ⇒ R` — the goal is R
	// and L joins the antecedents; 2 `R ⇒ L`. A cancellation law
	// `x + y = x + z ⇔ y = z` then closes `y = z` with the sum
	// resident, as `apply` reads an iff in either direction.
	iffSide int
	// flip matches an equation goal `a = b` against the reading's
	// `b = a`: the head states the equation the other way round, and
	// the goal is closed from it by symmetry.
	flip bool
	// conjunct reads a conjunctive conclusion `B ∧ C` as the law it is
	// for each conjunct: the goal is matched against the conjunct at
	// this index of the flattened conclusion, 1-based; 0 is the
	// conclusion whole. The conditioning stage splits a conjunctive
	// GOAL, so a law concluding a conjunction meets its goal only so.
	// With iffSide, the index is into the side the goal is read off.
	conjunct int
	// through reads an ⇔ side that is itself a law — `u ∈ T ⇔ ∀x. x ∈ u
	// ⇒ ∃δ. …` — through to that law's conclusion: the goal is an
	// instance of `∃δ. …`, the ⇔'s other side and the side's own
	// antecedents are what the context supplies, and the last `inner`
	// binders are the side's. The head is grounded at the binders
	// before them, the ⇔ eliminated toward the side, and the side
	// applied to the goal as a resident law is.
	through bool
	// throughPart is the 1-based conjunct of the side read through, where
	// the side is a conjunction one of whose conjuncts is the law — a
	// topology read as membership, `u ∈ T ⇔ u ⊆ M ∧ ∀x. x ∈ u ⇒ ∃r. …`;
	// 0 where the side whole is the law.
	throughPart int
	inner       int
	// read marks a plan matched in the membership normal form — the
	// head's pieces and the goal with every `x ∈ {p | φ}` read as
	// φ[x/p] — taken where no reading matched as spelled; its conjunct
	// index counts the conclusion's conjuncts so read.
	read bool
	// reader is the reader of that reading: the plain one where the
	// membership and record readings matched, the door's where it took
	// the numeral reading too.
	reader rungReader
	// alternative marks a pinning after a reading's first
	// (pinAlternatives): tried, and its miss not reported over the
	// first's — it names a pinning the author did not write.
	alternative bool
}

// planHead is the plan half alone — everything planApply decides
// without the kernel: matchHead (the telescope, the seeds, the
// conclusion match, the context pinning), a binder still unpinned
// asked of facts when there is a source (`retrieve` hands the corpus's
// bare facts; `by` hands nothing — a witness neither the goal nor the
// context spells is not the rung's to invent), and then the witnesses,
// one per binder. The shared read behind the rung's dry run and
// behind `retrieve`'s reading of a corpus member (ReadHead).
func planHead(read rungReader, goal Prop, head core.Term, describe string, named []NamedWitness, facts *FactSource) (*headPlan, string) {
	plans, miss := matchHeadAll(read, goal, head, describe, named)
	if len(plans) == 0 {
		return nil, miss
	}
	for _, plan := range plans {
		if facts != nil && plan.unpinned() {
			plan.pinFrom(func(piece core.Term) (unify.MatchBindings, bool) {
				return facts.match(piece, plan.slots, plan.trial)
			})
		}
		if m := plan.pinWitnesses(describe); m != "" {
			miss = m
			continue
		}
		return plan, ""
	}
	return nil, miss
}

// matchHead is the first of matchHeadAll's plans — the reading of the
// head that matches the goal as stated, or its first Horn reading.
func matchHead(read rungReader, goal Prop, head core.Term, describe string, named []NamedWitness) (*headPlan, string) {
	plans, miss := matchHeadAll(read, goal, head, describe, named)
	if len(plans) == 0 {
		return nil, miss
	}
	return plans[0], ""
}

// matchHeadAll telescopes the head, substitutes the seeds, matches
// each reading of the conclusion against the goal — the conclusion as
// stated, then each Horn clause of an ⇔ — and pins what it can of the
// remaining binders from the antecedents against the context. The
// plans it returns, in reading order, may still have binders unpinned.
func matchHeadAll(read rungReader, goal Prop, head core.Term, describe string, named []NamedWitness) ([]*headPlan, string) {
	return matchHeadReadings(read, goal, head, describe, named, false)
}

// matchHeadReadings is matchHeadAll, reading THROUGH an ⇔'s side when
// through is set (the apply rung; `retrieve` reads a member at its own
// binders and stops at the ⇔).
func matchHeadReadings(read rungReader, goal Prop, head core.Term, describe string, named []NamedWitness, through bool) ([]*headPlan, string) {
	target := goal.Conclusion()
	avoid := utils.EmptySet[core.TermName]()
	collect := func(t core.Term) {
		for _, v := range t.Frees(nil) {
			avoid.Add(v.Name())
		}
	}
	for i := range goal.NumHyps() {
		collect(goal.Hyp(i))
	}
	collect(target)

	binders, antes, concl, slots := ematch.Telescope(head, avoid)
	if len(binders) == 0 && len(antes) == 0 {
		// A bare fact: assumption territory, which the closer's own
		// trivial pass already covers — unless the fact is an ⇔, a law
		// grounded at its witnesses, which still reads as its two Horn
		// clauses.
		if _, _, iff := ext.MatchesIFF(concl); !iff {
			return nil, ""
		}
	}
	bindings := unify.MatchBindings{}
	seeded := map[core.TermName]bool{}
	if len(named) > 0 {
		// The seeds name the STATED binders; Telescope renamed them
		// away from the goal's frees position by position, so the
		// stated name at index i is the slot binders[i].
		stated, _ := ematch.StripGuardedForalls(head)
		var subs []core.TermSubst
		for _, nw := range named {
			at := -1
			for i, b := range stated {
				if string(b.Name()) == nw.Binder {
					at = i
					break
				}
			}
			if at < 0 {
				names := make([]string, len(stated))
				for i, b := range stated {
					names[i] = string(b.Name())
				}
				return nil, fmt.Sprintf("apply-close: %s has no ∀-binder named %q — its stated binders are (%s)",
					describe, nw.Binder, strings.Join(names, ", "))
			}
			if !binders[at].Type().Equals(nw.Witness.Type()) {
				return nil, fmt.Sprintf("apply-close: binder %q of %s has type %s at the type instance the goal offered, "+
					"but the term pinned to it has type %s — the instance was inferred from the goal, not from the pinned "+
					"term; if it is not the one you meant, pin it (type_specialize in the session, <Entry>.Inst(TypeBinder.Bind…) in Go)",
					nw.Binder, describe, ext.FormatType(binders[at].Type()), ext.FormatType(nw.Witness.Type()))
			}
			bindings[binders[at].Name()] = nw.Witness
			seeded[binders[at].Name()] = true
			subs = append(subs, core.MakeTermSubst(binders[at], nw.Witness))
		}
		ctx := context.Background()
		concl = tactic.InstanceNormalTerm(ext.BetaCollapse(ctx, concl.Substitute(subs...)))
		for i, a := range antes {
			antes[i] = tactic.InstanceNormalTerm(ext.BetaCollapse(ctx, a.Substitute(subs...)))
		}
	}
	// The head's pieces and the goal are matched as spelled, and, where
	// no reading matches so, in the rung's reading on both sides
	// (rungReader.reading) — every `x ∈ {p | φ}` read as φ[x/p], every
	// record projection of a packed value computed to the part, every
	// variable-free numeral term its value — so a law
	// concluding a membership in a set-builder applies to the condition
	// at the point, and one stated at a record's parts to a goal spelled
	// with its projections. Both sides or neither: a goal read against a
	// head whose set is a binder, `y ∈ s`, would match nothing the
	// spelling matches.
	// The numeral reading is a third spelling, after the other two: a
	// head stated at `m + 1` matches a goal spelled `2 + 1` as spelled,
	// or in the reading that leaves the sum standing, before the goal is
	// read at `3`.
	type spelling struct {
		concl  core.Term
		antes  []core.Term
		target core.Term
		read   bool
		reader rungReader
	}
	spellings := []spelling{{concl: concl, antes: antes, target: target}}
	for _, reader := range []rungReader{plainReader, read} {
		last := spellings[len(spellings)-1]
		next := spelling{concl: reader.reading(concl), antes: make([]core.Term, len(antes)), target: reader.reading(target),
			read: true, reader: reader}
		changed := !next.concl.Equals(last.concl) || !next.target.Equals(last.target)
		for i, a := range antes {
			next.antes[i] = reader.reading(a)
			changed = changed || !next.antes[i].Equals(last.antes[i])
		}
		if changed {
			spellings = append(spellings, next)
		}
	}
	var plans []*headPlan
	for _, sp := range spellings {
		matched := matchHeadSpelling(sp.concl, sp.antes, sp.target, sp.read, binders, slots, bindings, seeded, avoid, through)
		for _, plan := range matched {
			plan.reader = sp.reader
		}
		plans = append(plans, matched...)
	}
	if len(plans) == 0 {
		if len(named) > 0 {
			return nil, fmt.Sprintf("apply-close: with %s, the conclusion of %s reads %s, which does not match the goal %s",
				describeNamedWitnesses(named), describe, clipRunes(ext.PrintTerm(concl), 80), clipRunes(ext.PrintTerm(target), 80))
		}
		return nil, ""
	}
	// Binders the conclusion left unpinned are pinned by the
	// antecedents against the context — `apply` leaving metavariables
	// that `assumption` solves. Deterministic: antecedents in stated
	// order, hypotheses in index order, each as spelled and then in the
	// rung's reading, first consistent extension. Where a piece
	// meets more than one hypothesis, the other pinnings follow as plans
	// of their own (pinAlternatives), after every reading's first.
	var further []*headPlan
	for _, plan := range plans {
		alternatives := plan.pinAlternatives(func(piece core.Term, from unify.MatchBindings) []unify.MatchBindings {
			var out []unify.MatchBindings
			for i := range goal.NumHyps() {
				h := goal.Hyp(i)
				trial := copyBindings(from)
				if unify.TermMatchApproxEtaWith(piece, h, plan.slots, trial) {
					out = append(out, trial)
					continue
				}
				matched, last := false, h
				for _, reader := range []rungReader{plainReader, read} {
					readH := reader.reading(h)
					if matched || readH.Equals(last) {
						continue
					}
					last = readH
					trial = copyBindings(from)
					if unify.TermMatchApproxEtaWith(piece, readH, plan.slots, trial) {
						out = append(out, trial)
						matched = true
					}
				}
			}
			return out
		})
		plan.bindings = alternatives[0]
		for _, b := range alternatives[1:] {
			alt := *plan
			alt.bindings, alt.alternative = b, true
			further = append(further, &alt)
		}
	}
	return append(plans, further...), ""
}

// matchHeadSpelling matches one spelling of the head's pieces against
// one spelling of the goal: the conclusion as stated, then — when it is
// an ⇔ — each of its two Horn readings, the goal matched against one
// side, the other side an antecedent the context must supply, and the
// sides read through when through is set; each against the goal and,
// when the goal is an equation, against the goal read the other way
// round — `apply` up to the symmetry of =, finished by one Symm. A
// failed match may write into the bindings, so each reading starts
// from a copy.
func matchHeadSpelling(concl core.Term, antes []core.Term, target core.Term, read bool,
	binders []core.VarTerm, slots unify.TermNameSet, bindings unify.MatchBindings,
	seeded map[core.TermName]bool, avoid utils.Set[core.TermName], through bool) []*headPlan {
	type reading struct {
		concl core.Term
		antes []core.Term
		side  int
		// conjunct is headPlan.conjunct.
		conjunct int
		// inner and innerSlots are the binders of an ⇔ side read
		// through (headPlan.through).
		inner      []core.VarTerm
		innerSlots unify.TermNameSet
		through    bool
		// throughPart is headPlan.throughPart.
		throughPart int
	}
	readings := []reading{{concl: concl, antes: antes}}
	if parts := conjuncts(concl); len(parts) > 1 {
		for i, part := range parts {
			readings = append(readings, reading{concl: part, antes: antes, conjunct: i + 1})
		}
	}
	if l, r, ok := ext.MatchesIFF(concl); ok {
		withL := append(append([]core.Term{}, antes...), l)
		withR := append(append([]core.Term{}, antes...), r)
		readings = append(readings, reading{concl: r, antes: withL, side: 1}, reading{concl: l, antes: withR, side: 2})
		if through {
			// A side that is itself a law is read through, after the
			// readings that take it whole. Its binders are renamed
			// away from the goal's names and from the head's slots.
			apart := utils.EmptySet[core.TermName]()
			for n := range avoid {
				apart.Add(n)
			}
			for n := range slots {
				apart.Add(n)
			}
			// A side that is a conjunction is read through each conjunct
			// that is a law: the side is split toward that conjunct once
			// the elimination has made it resident.
			for _, sd := range []struct {
				side        int
				law, other  core.Term
				withTheSide []core.Term
			}{{1, r, l, withL}, {2, l, r, withR}} {
				parts := conjuncts(sd.law)
				for pi, part := range parts {
					inner, innerAntes, innerConcl, innerSlots := ematch.Telescope(part, apart)
					if len(inner) == 0 && len(innerAntes) == 0 {
						continue
					}
					throughPart := 0
					if len(parts) > 1 {
						throughPart = pi + 1
					}
					readings = append(readings, reading{concl: innerConcl,
						antes: append(append([]core.Term{}, sd.withTheSide...), innerAntes...),
						side:  sd.side, inner: inner, innerSlots: innerSlots, through: true, throughPart: throughPart})
				}
			}
		}
		// A side that is a conjunction is read, after every reading
		// above, as the law it is for each conjunct: `x ∈ F ⇔ P(x) ∧
		// K(x)` closes `K(a)` with `a ∈ F` held, as a law concluding
		// `P(x) ∧ K(x)` does — on either side, at any conjunct.
		for _, sd := range []struct {
			side        int
			law         core.Term
			withTheSide []core.Term
		}{{1, r, withL}, {2, l, withR}} {
			if parts := conjuncts(sd.law); len(parts) > 1 {
				for i, part := range parts {
					readings = append(readings, reading{concl: part, antes: sd.withTheSide, side: sd.side, conjunct: i + 1})
				}
			}
		}
	}
	targets := []core.Term{target}
	if a, b, ok := ext.MatchesEQ(target); ok && !a.AlphaEquals(b) {
		targets = append(targets, ext.WrapTerm(b).Eq(ext.WrapTerm(a)).Core())
	}
	var plans []*headPlan
	for ti, tgt := range targets {
		for _, rd := range readings {
			trial := make(unify.MatchBindings, len(bindings))
			for k, v := range bindings {
				trial[k] = v
			}
			readBinders, readSlots := binders, slots
			if rd.through {
				if ti == 1 {
					// The side's own apply turns the goal; the reading
					// through it is matched against the goal as stated.
					continue
				}
				readBinders = append(append([]core.VarTerm{}, binders...), rd.inner...)
				readSlots = utils.EmptySet[core.TermName]()
				for n := range slots {
					readSlots.Add(n)
				}
				for n := range rd.innerSlots {
					readSlots.Add(n)
				}
			}
			if unify.TermMatchApproxEtaWith(rd.concl, tgt, readSlots, trial) {
				plans = append(plans, &headPlan{binders: readBinders, antes: rd.antes, concl: rd.concl, slots: readSlots,
					bindings: trial, seeded: seeded, avoid: avoid, iffSide: rd.side, flip: ti == 1,
					through: rd.through, throughPart: rd.throughPart, inner: len(rd.inner), conjunct: rd.conjunct, read: read})
			}
		}
	}
	return plans
}

// unpinned reports whether some binder has no binding yet.
func (plan *headPlan) unpinned() bool {
	for _, b := range plan.binders {
		if _, has := plan.bindings[b.Name()]; !has {
			return true
		}
	}
	return false
}

// trial is a copy of the bindings for one matching attempt: a failed
// match may have written into it, so each attempt starts afresh.
func (plan *headPlan) trial() unify.MatchBindings {
	trial := make(unify.MatchBindings, len(plan.bindings))
	for k, v := range plan.bindings {
		trial[k] = v
	}
	return trial
}

// pinFrom walks the antecedents' conjuncts that still mention an
// unbound binder, in stated order, and adopts the first consistent
// extension the source finds for each. The source matches one piece
// against whatever supplies facts — the context, or for `retrieve`
// the corpus — starting from a trial() of the bindings.
func (plan *headPlan) pinFrom(source func(piece core.Term) (unify.MatchBindings, bool)) {
	for _, a := range plan.antes {
		if !plan.unpinned() {
			return
		}
		for _, piece := range conjuncts(a) {
			if !mentionsUnbound(piece, plan.slots, plan.bindings) {
				continue
			}
			if extended, ok := source(piece); ok {
				plan.bindings = extended
			}
		}
	}
}

// pinningBound bounds the pinnings a reading is planned at: a guard
// such as `subfield(L, M)` meets every subfield in sight, and the first
// it meets need not be the one the law's other antecedents say.
const pinningBound = 4

// pinAlternatives is pinFrom over every choice the context offers. The
// source lists, for one piece, every consistent extension of the given
// bindings, in the order pinFrom takes the first of. The first
// pinning returned is pinFrom's own; where some piece offered more
// than one extension, the others follow — a search that takes, among
// the pieces still mentioning an unbound binder, the one with the
// fewest extensions (`M ⊆ N` before `subfield(L, M)`) and tries each of
// them — pinningBound pinnings in all. A piece no hypothesis meets is
// passed over, as pinFrom passes it.
func (plan *headPlan) pinAlternatives(source func(piece core.Term, from unify.MatchBindings) []unify.MatchBindings) []unify.MatchBindings {
	var pieces []core.Term
	for _, a := range plan.antes {
		pieces = append(pieces, conjuncts(a)...)
	}
	bound := func(b unify.MatchBindings) bool {
		for _, v := range plan.binders {
			if _, has := b[v.Name()]; !has {
				return false
			}
		}
		return true
	}
	same := func(a, b unify.MatchBindings) bool {
		if len(a) != len(b) {
			return false
		}
		for k, v := range a {
			if w, has := b[k]; !has || !v.AlphaEquals(w) {
				return false
			}
		}
		return true
	}
	// Two hypotheses may extend the bindings alike; that is one choice.
	distinct := func(piece core.Term, from unify.MatchBindings) []unify.MatchBindings {
		var out []unify.MatchBindings
		for _, e := range source(piece, from) {
			if !slices.ContainsFunc(out, func(o unify.MatchBindings) bool { return same(o, e) }) {
				out = append(out, e)
			}
		}
		return out
	}
	first, ambiguous := copyBindings(plan.bindings), false
	for _, piece := range pieces {
		if bound(first) {
			break
		}
		if !mentionsUnbound(piece, plan.slots, first) {
			continue
		}
		if extensions := distinct(piece, first); len(extensions) > 0 {
			ambiguous = ambiguous || len(extensions) > 1
			first = extensions[0]
		}
	}
	out := []unify.MatchBindings{first}
	if !ambiguous {
		return out
	}
	var search func(b unify.MatchBindings, passed []bool)
	search = func(b unify.MatchBindings, passed []bool) {
		if len(out) >= pinningBound {
			return
		}
		next, nextExtensions := -1, []unify.MatchBindings(nil)
		passed = slices.Clone(passed)
		for i, piece := range pieces {
			if passed[i] || !mentionsUnbound(piece, plan.slots, b) {
				continue
			}
			extensions := distinct(piece, b)
			if len(extensions) == 0 {
				passed[i] = true
				continue
			}
			if next < 0 || len(extensions) < len(nextExtensions) {
				next, nextExtensions = i, extensions
			}
		}
		if next < 0 {
			if !slices.ContainsFunc(out, func(o unify.MatchBindings) bool { return same(o, b) }) {
				out = append(out, b)
			}
			return
		}
		passed[next] = true
		for _, e := range nextExtensions {
			search(e, passed)
		}
	}
	search(copyBindings(plan.bindings), make([]bool, len(pieces)))
	return out
}

// copyBindings is a copy of b for one matching attempt.
func copyBindings(b unify.MatchBindings) unify.MatchBindings {
	out := make(unify.MatchBindings, len(b))
	for k, v := range b {
		out[k] = v
	}
	return out
}

// pinWitnesses reads the witnesses off the bindings, one per binder in
// stated order — a binder nothing pinned is the miss the rung reports —
// βη-canonicalized unless the author seeded it.
func (plan *headPlan) pinWitnesses(describe string) string {
	witnesses := make([]core.Term, len(plan.binders))
	for j, b := range plan.binders {
		w, has := plan.bindings[b.Name()]
		if !has {
			return fmt.Sprintf("apply-close: the conclusion of %s matches the goal but neither it nor the "+
				"context pins every binder — a witness nothing spells is not the apply rung's to invent "+
				"(binder %q; pin it by name with Where)",
				describe, b.Name())
		}
		if plan.seeded[b.Name()] {
			// The author's spelling stands: a pinned λ is the instance
			// the kernel takes, redexes and all (Specialize β-reduces).
			witnesses[j] = w
			continue
		}
		// One witness, one spelling: the Miller branch of the matcher
		// binds a head applied under a binder as an abstraction
		// (`λy. q(y)`); the kernel instance must be taken at `q` — the
		// resident guard says P(q), the goal says zk(q(b)), and neither
		// is the abstraction's spelling.
		witnesses[j] = etaReduce(w)
	}
	plan.witnesses = witnesses
	return ""
}

// dryRunApply is the kernel half: the plan's instantiation run as a
// statement, the instance read back through the same telescope, and the
// kernel's spellings checked against the goal exactly.
func dryRunApply(goal Prop, head core.Term, describe string, plan *headPlan, applies rungOpts) (*applyRun, string) {
	supplied := func(t core.Term) bool { return len(unsuppliedPieces(goal, t, false, applies)) == 0 }
	target := goal.Conclusion()
	if plan.flip {
		a, b, ok := ext.MatchesEQ(target)
		if !ok {
			return nil, ""
		}
		target = ext.WrapTerm(b).Eq(ext.WrapTerm(a)).Core()
	}
	avoid := plan.avoid
	witnesses := plan.witnesses
	if plan.through {
		// The head takes its own binders; the side's are the side's.
		witnesses = witnesses[:len(witnesses)-plan.inner]
	}

	// The dry run: the kernel's own instantiation, the Specialize step's,
	// read back through the same telescope. Only the instance's
	// statement is read, so the record equations of its normal form are
	// read as statements (tactic.StatedRead).
	instanced := goal
	headIdx, err := alphaHypIndex(goal, head)
	if err != nil {
		return nil, ""
	}
	if len(witnesses) > 0 {
		sub := tactic.SpecializeTacticReading([]SpecializeHyp{InstHyp(headIdx, witnesses...)}, false, tactic.StatedRead)(goal)
		if sub == nil || sub.Size() != 1 {
			return nil, ""
		}
		instanced = sub.ChildGoal(0)
	}
	// Locate the instance: the hypothesis that is not one of the
	// original sequent's and telescopes with no binders left.
	var inst core.Term
	for i := range instanced.NumHyps() {
		h := instanced.Hyp(i)
		if len(witnesses) > 0 && goal.AnyHyp(h.AlphaEquals) {
			continue
		}
		if len(witnesses) == 0 && !h.AlphaEquals(head) {
			continue
		}
		if b, _, _, _ := ematch.Telescope(h, avoid); len(b) == 0 {
			inst = h
			break
		}
	}
	if inst == nil {
		return nil, ""
	}
	_, ground, conclusion, _ := ematch.Telescope(inst, avoid)
	var other core.Term
	if plan.iffSide == 0 {
		read := conclusion
		if plan.conjunct > 0 {
			// The kernel's instance concludes the conjunction; the goal
			// is the conjunct the plan matched, read as the plan read it.
			parts := conjuncts(conclusion)
			if plan.read {
				parts = conjuncts(plan.reader.reading(conclusion))
			}
			if plan.conjunct > len(parts) {
				return nil, ""
			}
			read = parts[plan.conjunct-1]
		}
		if !applies.reader().same(read, target) {
			return nil, fmt.Sprintf("apply-close: %s matches the goal at (%s) only up to a spelling the kernel "+
				"does not identify", describe, describeWitnesses(witnesses))
		}
	} else {
		// The Horn reading of an ⇔: the kernel's instance is the iff,
		// whose one side is the goal and whose other side the context
		// supplies.
		l, r, ok := ext.MatchesIFF(conclusion)
		if !ok {
			return nil, ""
		}
		side := r
		other = l
		if plan.iffSide == 2 {
			side, other = l, r
		}
		if plan.through {
			if !supplied(other) {
				return nil, fmt.Sprintf("apply-close: %s reads its ⇔ toward %s, of which the goal is an instance, "+
					"but the other side %s is not in the context — name the fact that supplies it",
					describe, clipRunes(ext.PrintTerm(side), 80), clipRunes(ext.PrintTerm(other), 80))
			}
			for _, g := range ground {
				if !supplied(g) {
					return nil, fmt.Sprintf("apply-close: %s matches the goal at (%s), but its antecedent %s is "+
						"not in the context — name the fact that supplies it",
						describe, describeWitnesses(witnesses), clipRunes(ext.PrintTerm(g), 80))
				}
			}
			// The side, once the elimination has made it resident, is a
			// law like any other — or a conjunction one of whose conjuncts
			// is, split once it is resident: validated against the sequent
			// as it will be then.
			law, resident := side, []core.Term{side}
			if plan.throughPart > 0 {
				parts := conjuncts(side)
				if plan.throughPart > len(parts) {
					return nil, ""
				}
				law, resident = parts[plan.throughPart-1], parts
			}
			withSide := prop.MakeProp(goal.Conclusion(), append(goal.Hyps(), resident...)...)
			inner, miss := planApplyWith(withSide, law, describe+", read through its ⇔", nil, applies)
			if inner == nil {
				return nil, miss
			}
			run := &applyRun{witnesses: witnesses, ground: ground, conclusion: conclusion, iffSide: plan.iffSide,
				iffOther: other, through: inner, throughSide: side, applies: applies}
			if plan.throughPart > 0 {
				run.throughHead = law
			}
			return run, ""
		}
		read := side
		if plan.conjunct > 0 {
			// The goal is the conjunct the plan matched, read off the
			// side as the plan read it.
			parts := conjuncts(side)
			if plan.read {
				parts = conjuncts(plan.reader.reading(side))
			}
			if plan.conjunct > len(parts) {
				return nil, ""
			}
			read = parts[plan.conjunct-1]
		}
		if !applies.reader().same(read, target) {
			return nil, fmt.Sprintf("apply-close: %s matches the goal at (%s) only up to a spelling the kernel "+
				"does not identify", describe, describeWitnesses(witnesses))
		}
		if !supplied(other) {
			return nil, fmt.Sprintf("apply-close: %s reads its ⇔ toward the goal at (%s), but the other side %s is "+
				"not in the context — name the fact that supplies it",
				describe, describeWitnesses(witnesses), clipRunes(ext.PrintTerm(other), 80))
		}
	}
	for _, g := range ground {
		if !supplied(g) {
			return nil, fmt.Sprintf("apply-close: %s matches the goal at (%s), but its antecedent %s is "+
				"not in the context — name the fact that supplies it",
				describe, describeWitnesses(witnesses), clipRunes(ext.PrintTerm(g), 80))
		}
	}
	return &applyRun{witnesses: witnesses, ground: ground, conclusion: conclusion, iffSide: plan.iffSide, iffOther: other,
		flip: plan.flip, conjunct: plan.conjunct > 0, applies: applies}, ""
}

// rungReader is what the rung reads a statement with: the membership
// reading and the record reading, which every proof has, and the numeral
// reading under the proof's arithmetic policy (numerals), since a
// numeral is evaluated by the theorems of the arithmetic bundles and a
// proof those rest on may not use them. The zero value reads no numeral:
// it is the reader of a door that has no proof at hand — the head
// readings `retrieve` reports, a failure's notes.
type rungReader struct{ numerals omega.ArithPolicy }

// readerOf is the rung's reader in the proof scope is of: its policy, or
// the unscoped one for a session bound to no member, as the arithmetic
// closer reads there.
func readerOf(scope *ProofScope) rungReader {
	if scope == nil {
		return rungReader{numerals: omega.UnscopedArithPolicy()}
	}
	return rungReader{numerals: scope.numeralPolicy()}
}

// reader is the rung's reader at this door.
func (o rungOpts) reader() rungReader {
	if o.plain {
		return rungReader{}
	}
	return readerOf(o.scope)
}

// reading is the rung's reading of a statement: the membership reading —
// every `x ∈ {p | φ}` its condition at the point, tactic.MembershipNormal
// — the record reading — every record projection of a packed value
// computed to the part through the record equations,
// tactic.InstanceNormalTerm, the form a cited instance is handed over
// in — and the numeral reading — a variable-free numeral term its value,
// a variable-free comparison ⊤ or ⊥, omega.NumeralNormal — each taken
// until none changes the term, since a computed part may spell a
// set-builder, a read condition a projection, and a condition read at a
// numeral a comparison. The first two are computed from the statements
// of the equations they read with, nothing proved; a numeral is
// evaluated by the arithmetic closer's evaluators. The kernel's side of
// the reading is a step a reading on the leaf (readLeaf: _MembershipRead,
// _RecordRead, _NumeralRead).
func (r rungReader) reading(t core.Term) core.Term {
	for pass := 0; ; pass++ {
		read := omega.NumeralNormal(r.numerals, tactic.InstanceNormalTerm(tactic.MembershipNormal(t)))
		if read.Equals(t) {
			return t
		}
		if pass == rungReadingPasses {
			panic(fmt.Sprintf("rung reading: no fixpoint after %d passes on %s — the readings feed each other",
				pass, ext.PrintTerm(t)))
		}
		t = read
	}
}

// rungReadingPasses bounds the alternation of the readings; each pass
// computes what the one before exposed.
const rungReadingPasses = 16

// plainReader is the reader with no numeral reading: the membership
// reading and the record reading alone. It is what the rung tries first
// at every decision — a statement the facts supply as they state it is
// supplied so, and the numeral reading answers only for what is left —
// so a proof that closed before a numeral was a value to the rung closes
// by the same steps, and records no use of the arithmetic bundles.
var plainReader = rungReader{}

// readsNumerals reports whether r has a numeral reading at all: a
// policy that admits ℕ's bundle, and the bundle to evaluate with.
func (r rungReader) readsNumerals() bool { return omega.ReadsNumerals(r.numerals) }

// numeralsIn reports whether the numeral reading changes one of ts:
// read as the other two readings read it, it spells a numeral statement.
func (r rungReader) numeralsIn(ts ...core.Term) bool {
	if !r.readsNumerals() {
		return false
	}
	for _, t := range ts {
		if omega.SpellsNumeralStatement(plainReader.reading(t)) {
			return true
		}
	}
	return false
}

// numeralsInSight reports whether the numeral reading changes t or a
// hypothesis of goal: whether a decision about t under goal can come
// out otherwise with it.
func (r rungReader) numeralsInSight(goal Prop, t core.Term) bool {
	return r.readsNumerals() && (r.numeralsIn(t) || goal.AnyHyp(func(h core.Term) bool { return r.numeralsIn(h) }))
}

// readsTrue reports whether t reads ⊤ and its numerals are what make it
// so: a comparison of numerals that holds, alone or with what it is
// joined to. A statement the other readings already read ⊤ is not one.
func (r rungReader) readsTrue(t core.Term) bool {
	return r.numeralsIn(t) && r.reading(t).Equals(T) && !plainReader.reading(t).Equals(T)
}

// readsFalse is readsTrue for ⊥.
func (r rungReader) readsFalse(t core.Term) bool {
	return r.numeralsIn(t) && r.reading(t).Equals(F) && !plainReader.reading(t).Equals(F)
}

// closes reports whether the numeral reading closes goal: its
// conclusion reads ⊤, or one of its hypotheses reads ⊥.
func (r rungReader) closes(goal Prop) bool {
	return r.readsNumerals() && (r.readsTrue(goal.Conclusion()) || goal.AnyHyp(r.readsFalse))
}

// normal is the rung's normal form, the spelling two statements are one
// in: the rung's reading and then βη. A statement resident in that form
// is closed by the assumption step through the kernel's βη conversion,
// after the leaf is read where a reading is what identifies the two
// (proveResident).
func (r rungReader) normal(ctx context.Context, t core.Term) core.Term {
	return ext.BetaEtaNormalize(ctx, r.reading(t))
}

// same is the rung's identity on a conclusion: the goal as spelled, or
// one statement in the rung's normal form.
func (r rungReader) same(a, b core.Term) bool {
	if a.AlphaEquals(b) {
		return true
	}
	ctx := context.Background()
	return r.normal(ctx, a).AlphaEquals(r.normal(ctx, b))
}

// etaReduce strips the η-redexes along a term's λ-spine: `λx̄ y. F(x̄, y)`
// with y not free in F(x̄, ·) is F(x̄), applied innermost-first, so
// `λx.λy. q(x, y)` is q. Only the spine is reduced — a witness is a
// term the rung chose, and the spine is where the matcher's
// abstractions sit.
func etaReduce(t core.Term) core.Term {
	var vars []core.VarTerm
	body := t
	for {
		abs, ok := body.Core().(core.AbsTerm)
		if !ok {
			break
		}
		vars = append(vars, abs.Var())
		body = abs.Body()
	}
	if len(vars) == 0 {
		return t
	}
	reduced := false
	for len(vars) > 0 {
		app, ok := body.Core().(core.AppliedTerm)
		if !ok {
			break
		}
		last := vars[len(vars)-1]
		av, isVar := app.Arg().AsVar()
		if !isVar || !av.Equals(last) || app.Fun().HasFree(last) {
			break
		}
		body = app.Fun()
		vars = vars[:len(vars)-1]
		reduced = true
	}
	if !reduced {
		return t
	}
	if len(vars) == 0 {
		return body
	}
	return ext.ReverseAbsVars(body, vars...)
}

// dischargeGuards is Lean's `f x₀ ‹A›` after a fact is grounded: an
// instance `A₁ ⇒ … ⇒ Aₖ ⇒ R` whose leading antecedents the context
// supplies is brought down to the first consequent it does not, by
// modus ponens (split the resident implication, close the ¬Aᵢ branch,
// continue with the consequent). Returns the leaf the spine continues
// on and the term the fact now names there. A guard the context does
// not supply stops the descent with the implication as it stands —
// nothing is invented.
//
// open is the reading of a By premise, where the grounded fact is one
// input of a close: there a guard is supplied as the apply rung
// supplies an antecedent (guardSuppliedByContext) — closed as a goal
// of its own, one apply deep. On the spine (Fact.At, Cite at
// witnesses, GroundHyp) the reading is closed: the fact a step names
// is the one the author reads off the text, and a guard the context
// would have to prove stays where it was written.
//
// listed names the facts a fact in hand may discharge its guards from
// (_ListedSuppliers): a guard the context supplies through a fact not
// among them is refused, naming the fact to list. It records each guard
// discharged and a stop at one the context does not supply, which its
// surplus check reads after the discharge (refuseSurplus). nil reads
// the whole context — a By's leaf, which holds the listed premises
// alone, and a cite's install.
//
// Whatever is stated to prove a guard is stated inside its ¬guard
// branch (closeNegatedGuard), so the leaf the spine continues on holds
// what it held and the consequent, nothing derived on the way.
//
// The prenex normal form gives this for free: Normalize hoists
// `∀x. A ⇒ ∃y. B` into `∀x. ∃y. ¬A ∨ B`, so a grounded fact stands
// ∃-headed and `Unpack`/`StripQuant` find their binder. The stated
// form keeps the guard where the author wrote it, and the context
// that would absorb it through the disjunction discharges it here.
func dischargeGuards(leaf *GoalStackNode, inst core.Term, open bool, rung rungOpts, listed *_ListedSuppliers) (*GoalStackNode, core.Term) {
	if rung.scope == nil {
		rung.scope = leaf.proofScope
	}
	node := leaf
	for {
		ante, rest, ok := ext.MatchesIMPLY(inst)
		if !ok || ante.AlphaEquals(rest) {
			return node, inst
		}
		idx, err := findHypIndex(node.Goal, inst)
		if err != nil {
			listed.stall()
			return node, inst
		}
		// The guard is discharged when the context SUPPLIES it — as
		// written, up to βη (an instance taken at a λ-witness states
		// its guard as a redex), as a conjunct of one resident fact (a
		// gathered datum), or conjunct by conjunct with each equation
		// in either orientation (Lean's `‹A›`, read by assumption);
		// read open, also closed as a goal of its own, one apply deep.
		// A guard the context would have to SEARCH for stays where the
		// author wrote it, for the closer.
		reading := rung.withDepth(byAssumption)
		if open {
			reading = rung.withDepth(antecedentApplies)
		}
		if len(unsuppliedPieces(node.Goal, ante, true, reading)) > 0 {
			listed.stall()
			return node, inst
		}
		if listed != nil {
			listed.check(node.Goal, ante, reading)
		}
		if !node.runStep(SplitHypImplyAt(idx)) {
			listed.stall()
			return node, inst
		}
		// The modus ponens has a ¬guard branch and a consequent branch,
		// told apart by what they hold: where the context already held
		// what one branch adds, the kernel folds the other into it. A
		// consequent resident before the split — the same law read
		// twice at one point in a By, a member's evidence carried by
		// two cites — leaves the consequent branch alone, and the guard
		// is discharged into it with nothing to close; the guard's
		// negation resident leaves the ¬guard branch alone, which
		// closes on the two, and the leaf with it.
		var negated, consequent *GoalStackNode
		for _, kid := range node.Children() {
			if kid.Goal.AnyHyp(rest.AlphaEquals) {
				consequent = kid
			} else {
				negated = kid
			}
		}
		if negated != nil {
			closeNegatedGuard(negated, ante, reading)
		}
		if consequent == nil {
			return node, rest
		}
		node, inst = consequent, rest
	}
}

// closeNegatedGuard closes the ¬guard branch of a modus ponens, whose
// guard the context supplies at the reading applies: what the context
// closes and does not hold is stated and proved (supplyPieces), the
// guard is then stated in the instance's own spelling from what the
// context holds of it (proveResident), and the branch closes on the
// guard and its negation, one spelling. No step between normalizes. A
// closer that does reads `∀n. 0 ≤ n ⇒ (λN. s(N))(n) ∧ t(n)` and the
// same law reduced as two clause sets that do not meet, and the
// branch stays open on a guard the context has proved.
func closeNegatedGuard(branch *GoalStackNode, guard core.Term, applies rungOpts) {
	node := branch
	if applies.depth >= 0 {
		node = supplyPieces(node, guard, true, applies)
	}
	if !node.Goal.AnyHyp(guard.AlphaEquals) {
		if !node.runStep(_AssertStep{claim: prop.MakeProp(guard)}) {
			panic(fmt.Sprintf("dischargeGuards: stating a guard the context supplies refused (engine invariant): %s",
				ext.PrintTerm(guard)))
		}
		kids := node.Children()
		Assert(len(kids) == 2)
		proveResident(kids[0], true)
		node = kids[1]
	}
	if !node.runStep(_BasicTactic{}) || !branch.Proved() {
		panic(fmt.Sprintf("dischargeGuards: the ¬guard branch did not close on the guard and its negation (engine invariant): %s",
			clipRunes(ext.PrintTerm(guard), 80)))
	}
}

// guardSuppliedByContext reports whether the context supplies the guard
// of a By premise's instance: resident as written up to βη, an equation
// in either orientation, a conjunct of one resident fact, a conjunction
// each of whose sides the context supplies the same way, or closed as a
// goal of its own, one apply deep (closeGoal). A conjunctive guard resident as ONE fact is
// supplied like one resident conjunct by conjunct — read only by its
// conjuncts, the whole fact was missed, and a witnessed cite whose
// bounds were stated as one Have fell to its clause form.
func guardSuppliedByContext(goal Prop, ante core.Term, door rungOpts) bool {
	return len(unsuppliedPieces(goal, ante, true, door.withDepth(antecedentApplies))) == 0
}

// unsuppliedPieces lists the parts of t the context does not supply,
// reading t the way both antecedent tests do, in the rung's reading
// (the door's reader): a part that reads ⊤ at its numerals asks for
// nothing; a part resident in the rung's normal form is supplied; with
// flip, so is an equation resident the other way round (the guard
// reading); a conjunction is its two sides — a membership whose
// condition is a conjunction among them; and with applies ≥ 0, so is a
// part the context closes as a goal, that many applies deep. Read
// byAssumption, the list is what supplyPieces has to make resident.
//
// The statement is read without its numerals first (plainReader), and
// with them only where that leaves a part unsupplied and a numeral is
// in sight: what the facts supply as they state it is supplied so.
func unsuppliedPieces(goal Prop, t core.Term, flip bool, applies rungOpts) []core.Term {
	stated := applies
	stated.plain = true
	missing := unsuppliedPiecesIn(goal, t, flip, stated)
	if len(missing) == 0 || applies.plain || !applies.reader().numeralsInSight(goal, t) {
		return missing
	}
	return unsuppliedPiecesIn(goal, t, flip, applies)
}

// unsuppliedPiecesIn is unsuppliedPieces in the one reading applies
// names.
func unsuppliedPiecesIn(goal Prop, t core.Term, flip bool, applies rungOpts) []core.Term {
	read := applies.reader()
	// A part that reads ⊤ at its numerals — a comparison of numerals that
	// holds — asks the context for nothing.
	if read.readsTrue(t) {
		return nil
	}
	t = read.reading(t)
	if goal.AnyHyp(read.resident(t)) {
		return nil
	}
	if l, r, ok := ext.MatchesEQ(t); flip && ok &&
		goal.AnyHyp(read.resident(ext.WrapTerm(r).Eq(ext.WrapTerm(l)).Core())) {
		return nil
	}
	if read.heldAsConjunct(goal, t, flip) {
		return nil
	}
	if a, b, ok := ext.MatchesAND(t); ok {
		return append(unsuppliedPiecesIn(goal, a, flip, applies), unsuppliedPiecesIn(goal, b, flip, applies)...)
	}
	// A piece that is the goal itself is not closed as a goal: a head
	// that asks for the goal makes no progress on it. Transitivity read
	// at a middle point equal to its end, `R(a, c) ∧ R(c, c) ⇒ R(a, c)`,
	// has its second piece by reflexivity and its first by whatever
	// proves the goal one apply deeper — that head is the one to apply.
	if applies.depth >= 0 && !read.same(t, goal.Conclusion()) && goalCloses(goal, t, applies) {
		return nil
	}
	return []core.Term{t}
}

// suppliedStatement is the spelling an antecedent is proved and made
// resident in: the instance normal form (prover/tactic, InstanceNormal).
// An instance taken at a λ-witness states its pieces as redexes
// (`(λN. inf(T(N)))(n) ≤ …`), and one at a packed record value its
// parts as projections of it, which no resident conclusion matches; the
// normal statement is the same fact, and the context holds it up to βη
// once it is resident.
func suppliedStatement(t core.Term) core.Term {
	return tactic.InstanceNormalTerm(ext.BetaCollapse(context.Background(), t))
}

// heldAsConjunct reports whether t is a conjunct of one resident
// hypothesis, in the rung's normal form — with flip, an equation the
// other way round too. A datum gathered into one resident fact holds
// each of its clauses, and a guard the By executor's split (the
// manual's S1) would have exposed is supplied on the spine as it is
// inside a close: the one reading, so that a fact in hand and a By
// premise discharge their guards from the same context alike. Closed
// by splitting that hypothesis (proveResident).
func (rd rungReader) heldAsConjunct(goal Prop, t core.Term, flip bool) bool {
	same := rd.resident(t)
	var turned func(core.Term) bool
	if l, r, ok := ext.MatchesEQ(t); flip && ok {
		turned = rd.resident(ext.WrapTerm(r).Eq(ext.WrapTerm(l)).Core())
	}
	return goal.AnyHyp(func(h core.Term) bool {
		parts := conjuncts(h)
		if len(parts) < 2 {
			return false
		}
		return slices.ContainsFunc(parts, func(p core.Term) bool {
			return same(p) || (turned != nil && turned(p))
		})
	})
}

// goalCloses reports whether the context closes t as a goal, applies
// applies deep: a dry run of closeGoal on a scratch stack over the same
// hypotheses. supplyPieces is the identical move committed.
func goalCloses(goal Prop, t core.Term, applies rungOpts) bool {
	// The dry run registers the claims its installs would leave on a
	// scratch list: nothing of it reaches the real tree.
	if applies.claims != nil {
		var scratch []*GoalStackNode
		applies.claims = &scratch
	}
	scratch := CreateGoalStack(prop.MakeProp(suppliedStatement(t), goal.Hyps()...))
	scratch.SetProofScope(applies.scope)
	return closeGoal(scratch, applies)
}

// closeGoal is the rung's one closing procedure, for an antecedent as
// for a goal: the rules that lose nothing are applied wherever they
// apply — a conjunction is closed conjunct by conjunct, a ∀ is fixed
// and an antecedent assumed, a conjunctive hypothesis is split — and
// what is left is closed by assumption, or, while applies lasts, by the
// first hypothesis, then the first plain stated form, that applies to
// it with its own antecedents closed the same way one apply shallower
// (applyInside; a structural apply, every antecedent it must close a
// smaller term than its goal, spends no depth). So `∀n. 0 ≤ n ⇒ P(n)`
// and `P(c)` are both supplied by a resident `∀N. P(N)`, an injectivity
// on a set by the injectivity everywhere, the guard of one cited law by
// the consequent of another, and `x * inv(x) ∈ c` by the closure of c
// under * and inv, each a named premise. No binder is left to a
// sub-goal (the plan pins every one from the goal and the context
// before the antecedents are read), so the conjuncts and the
// antecedents are independent and nothing is searched: a head is
// retried only at the context's other pinnings (pinAlternatives).
// Reports whether n is proved up to the claims its installs registered
// (rungOpts.closed); an n it does not close is left as far as it got,
// which is why the dry run is on a scratch stack.
func closeGoal(n *GoalStackNode, applies rungOpts) bool {
	// The node and the door read alike: a scratch stack takes the door's
	// scope, and a door that named none reads as the node's proof does.
	if n.proofScope == nil && applies.scope != nil {
		n.SetProofScope(applies.scope)
	}
	if applies.scope == nil {
		applies.scope = n.proofScope
	}
	goal := n.Goal
	target := goal.Conclusion()
	read := applies.reader()
	if goal.AnyHyp(read.resident(target)) {
		proveByAssumption(n)
		return n.Proved()
	}
	// An equation between one term and itself holds by reflexivity, an
	// antecedent as a goal: a law about a map read at an embedding asks
	// `f(zero) = zero'`, which at complex_of_real is
	// `complex_of_real(&0) = complex_of_real(&0)` — nothing to find in
	// the context, and nothing to prove.
	if l, r, ok := ext.MatchesEQ(target); ok && l.AlphaEquals(r) {
		return n.runStep(_Refl{}) && n.Proved()
	}
	if _, _, ok := ext.MatchesAND(target); ok {
		if !n.runStep(SplitConj()) {
			return false
		}
		for _, k := range n.Children() {
			if !closeGoal(k, applies) {
				return false
			}
		}
		return applies.closed(n)
	}
	// The membership reading is a strip too: a leaf that spells a
	// membership in a set-builder, in its conclusion or a hypothesis, is
	// read before the heads are tried, so the heads and the facts meet
	// in one spelling. The record reading is not: a projection of a
	// defined packed value is computed where it identifies two statements
	// (proveResident, commitApply), and the author's spelling stands in a
	// residual.
	if n.runStep(_StripQuant1{}) || n.runStep(_StripImp{}) || n.runStep(_SplitHypConj{}) || n.runStep(_MembershipRead{}) {
		kids := n.Children()
		if len(kids) != 1 {
			return false
		}
		return closeGoal(kids[0], applies) && applies.closed(n)
	}
	// The arithmetic closer's door: a guard the context does not hold as
	// written but decides by arithmetic under it — `x < 3` from
	// `x + 1 < 3` — is that closer's own, so the rung supplies it through
	// the decider the leaf will be closed by.
	if applies.arith && closeByArith(applies.deadline(), n, applies.scope) {
		return true
	}
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		run := applyInside(goal, h, clipRunes(ext.PrintTerm(h), 80), applies)
		if run == nil {
			continue
		}
		commitApply(n, i, run)
		return applies.closed(n)
	}
	for _, hd := range applies.heads {
		if hd.stated.NumHyps() > 0 {
			continue
		}
		for _, lemma := range hd.candidates(goal) {
			stated := lemma.Conclusion()
			if applies.statesWhole(lemma) {
				continue
			}
			if goal.AnyHyp(stated.AlphaEquals) {
				continue
			}
			withHead := prop.MakeProp(goal.Conclusion(), append(goal.Hyps(), stated)...)
			run := applyInside(withHead, stated, hd.describe, applies)
			if run == nil {
				continue
			}
			if commitStatedHead(n, lemma, stated, run, applies.claims) {
				return applies.closed(n)
			}
		}
	}
	// Last, a goal that reads ⊤ at its numerals holds by that reading, an
	// antecedent as a goal: a law read at a numeral asks `0 < 2` or
	// `1 ≤ 2 + 1`, which nothing in the context states, no head proves,
	// and nothing has to.
	if !applies.plain && read.readsTrue(target) {
		return closeByReading(n)
	}
	return false
}

// applyInside plans an apply of head on goal inside an antecedent: its
// own antecedents are read one apply shallower, or, when the apply is
// structural, at the same depth, which it does not spend — the sizes
// bound that chain. With the depth spent only a structural apply is
// planned.
func applyInside(goal Prop, head core.Term, describe string, applies rungOpts) *applyRun {
	if applies.depth > 0 {
		if run, _ := planApplyWith(goal, head, describe, nil, applies.shallower()); run != nil {
			return run
		}
	}
	if applies.depth < 0 || !structuralApply(goal, head, describe, applies) {
		return nil
	}
	run, _ := planApplyWith(goal, head, describe, nil, applies)
	return run
}

// structuralApply reports whether an apply of head on goal is a
// descent: the head's plain Horn reading matches the goal, the goal
// and the context pin every binder, and some antecedent instance the
// context does not hold — every such one a smaller term than the
// goal's conclusion — is left to close. Such applies close carrier
// membership — `x * inv(x) ∈ c` by the closure of c under *, with
// `inv(x) ∈ c` left to the closure under inv — however deep the term
// nests, and a chain of them terminates by the sizes alone: no depth
// is spent on one. An apply whose antecedents the context all holds
// is the ordinary innermost apply and spends depth as always; an ⇔
// read as a Horn clause, a flipped equation and a conjunct of a
// conjunctive conclusion are not read as descents.
func structuralApply(goal Prop, head core.Term, describe string, applies rungOpts) bool {
	plan, _ := matchHead(applies.reader(), goal, head, describe, nil)
	if plan == nil || plan.iffSide != 0 || plan.through || plan.flip || plan.conjunct > 0 {
		return false
	}
	if plan.pinWitnesses(describe) != "" || len(plan.witnesses) != len(plan.binders) {
		return false
	}
	substs := make([]core.TermSubst, len(plan.binders))
	for i, b := range plan.binders {
		substs[i] = core.MakeTermSubst(b, plan.witnesses[i])
	}
	size := goal.Conclusion().Size()
	descends := false
	for _, ante := range plan.antes {
		// A conjunctive antecedent is closed conjunct by conjunct, and
		// is measured so.
		for _, piece := range conjuncts(suppliedStatement(ante.Substitute(substs...))) {
			if residentByAssumption(goal, piece, applies) {
				continue
			}
			if piece.Size() >= size {
				return false
			}
			descends = true
		}
	}
	return descends
}

// supplyPieces makes resident, on leaf, every part of t the context
// does not hold by assumption and closes as a goal (goalCloses): each
// is asserted in its reduced statement and proved by closeGoal, in the
// order t states them. Returns the leaf the caller continues on, where
// t is supplied by assumption. flip is the caller's reading of t
// (unsuppliedPieces). The caller has checked that the context supplies
// t, applies applies deep.
func supplyPieces(leaf *GoalStackNode, t core.Term, flip bool, applies rungOpts) *GoalStackNode {
	node := leaf
	for _, piece := range unsuppliedPieces(leaf.Goal, t, flip, applies.withDepth(byAssumption)) {
		claim := suppliedStatement(piece)
		if node.Goal.AnyHyp(claim.AlphaEquals) {
			continue
		}
		if !node.runStep(_AssertStep{claim: prop.MakeProp(claim)}) {
			panic(fmt.Sprintf("apply-close: stating an antecedent the context closes refused after its dry run "+
				"succeeded (engine invariant)\n  antecedent: %s", ext.PrintTerm(claim)))
		}
		kids := node.Children()
		Assert(len(kids) == 2)
		if !closeGoal(kids[0], applies) {
			panic(fmt.Sprintf("apply-close: an antecedent did not close although its dry run did "+
				"(engine invariant)\n  antecedent: %s", ext.PrintTerm(claim)))
		}
		node = kids[1]
	}
	return node
}

// residentModuloBetaEta is what the kernel's assumption step closes: a
// statement in the context as written, or up to βη — an instance taken
// at a λ-witness (`WellOrderedBelow` at `λr. ∃q. …`) states its guard
// as a redex, while the fact that supplies it was proved in the reduced
// spelling, and the step carries the one to the other through the
// kernel's conversion.
func residentModuloBetaEta(ante core.Term) func(core.Term) bool {
	ctx := context.Background()
	var normAnte core.Term
	return func(h core.Term) bool {
		if h.AlphaEquals(ante) {
			return true
		}
		if normAnte == nil {
			normAnte = ext.BetaEtaNormalize(ctx, ante)
		}
		return ext.BetaEtaNormalize(ctx, h).AlphaEquals(normAnte)
	}
}

// resident is the guard-discharge test, the rung's identity: the
// antecedent is in the context as written, or as one statement in the
// rung's normal form — up to βη and the reader's readings, so
// `u ∈ {p | polynomial_over(c, p)}` is held by a resident
// `polynomial_over(c, u)` and the other way round, and `x ∈ X(2 + 1)` by
// a resident `x ∈ X(3)`. What is resident up to a reading alone is
// closed after the leaf is read (proveResident).
func (r rungReader) resident(ante core.Term) func(core.Term) bool {
	ctx := context.Background()
	var normAnte core.Term
	return func(h core.Term) bool {
		if h.AlphaEquals(ante) {
			return true
		}
		if normAnte == nil {
			normAnte = r.normal(ctx, ante)
		}
		return r.normal(ctx, h).AlphaEquals(normAnte)
	}
}

// WitnessesNameClosedGoal is witnessesNameClosedGoal for the session's
// witnessed reading cite (`lemma {key, read_at, term_specialize}`),
// whose exact install closed the goal before the tuple grounded it.
func WitnessesNameClosedGoal(ref Prop, witnesses []core.Term, closed core.Term) bool {
	return witnessesNameClosedGoal(ref, witnesses, closed)
}

// witnessesNameClosedGoal is the check behind Lean's `exact foo a b`: a
// witnessed cite whose ∀-form install already closed the goal did not
// APPLY its tuple, so the tuple is unchecked text — unless instantiating
// the stated form at that very tuple (its own binder order, through
// guards) reproduces the goal the install closed with, as the whole
// guarded instance or as its final conclusion. Then the tuple names the
// instance the cite used, and it is checked after all. Each witness is
// read at its binder's type, the reference's letters bound once across
// the tuple: a polymorphic reference is read at the instance the tuple
// took, as FitWitness reads a witness at every other door. Partial
// tuples are not verified.
func witnessesNameClosedGoal(ref Prop, witnesses []core.Term, closed core.Term) bool {
	if ref == nil || ref.NumHyps() > 0 || len(witnesses) == 0 {
		return false
	}
	binders, matrix := ematch.StripGuardedForalls(ref.Conclusion())
	if len(binders) != len(witnesses) {
		return false
	}
	var env []core.TypeSubst
	for i, b := range binders {
		if !core.MatchTypeInto(b.Type(), witnesses[i].Type(), utils.FullPredicate[core.VarType], &env) {
			return false
		}
	}
	if subst := nonIdentityTypeSubst(env); len(subst) > 0 {
		binders, matrix = ematch.StripGuardedForalls(ref.Conclusion().TypeSubstitute(subst...))
	}
	subs := make([]core.TermSubst, len(binders))
	for i, b := range binders {
		subs[i] = ext.MakeTermSubst(b, witnesses[i])
	}
	instance := matrix.Substitute(subs...)
	conclusion := instance
	for {
		_, rest, ok := ext.MatchesIMPLY(conclusion)
		if !ok {
			break
		}
		conclusion = rest
	}
	ctx := context.Background()
	want := ext.BetaEtaNormalize(ctx, closed)
	return ext.BetaEtaNormalize(ctx, instance).AlphaEquals(want) ||
		ext.BetaEtaNormalize(ctx, conclusion).AlphaEquals(want)
}

// statedTupleBinders reads which binders a tuple of n witnesses grounds
// in a stated form, and the body it grounds them in: the whole guarded
// ∀-chain (ematch.StripGuardedForalls) when the tuple is that long,
// else the statement's own leading ∀-prefix when the tuple is exactly
// that long — a card `∀R M N. S(R, M, N) ⇒ ∀p u. …` cited at (R, M, N)
// grounds its own binders and leaves the guarded ∀s of its body
// standing. Any other length is a partial tuple (false). A statement
// with free term variables installs ∀-closed over them ahead of its
// stated binders, a prefix the tuple does not address, so it is read
// against the guarded chain alone.
func statedTupleBinders(stated core.Term, n int) ([]core.VarTerm, core.Term, bool) {
	binders, matrix := ematch.StripGuardedForalls(stated)
	if len(binders) == n {
		return binders, matrix, true
	}
	if n == 0 || len(stated.Frees(nil)) > 0 {
		return nil, nil, false
	}
	var leading []core.VarTerm
	body := stated
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		leading = append(leading, abs.Var())
		body = abs.Body()
	}
	if len(leading) != n {
		return nil, nil, false
	}
	return leading, body, true
}

// statedGuardsSupplied decides whether a witnessed named premise takes
// its STATED form: the tuple grounds every guarded binder, or every
// binder of the statement's own leading prefix (statedTupleBinders),
// and every leading guard of the instance is supplied by the context
// by assumption (guardSuppliedByContext) — the shape Lean's `f x₀ ‹A›`
// names, where the grounding leaves an unguarded fact. A partial
// tuple, an ill-typed one, or a guard the context would have to prove
// answer false: the premise then installs the clause form the closer
// was built and recorded on.
func statedGuardsSupplied(goal Prop, stated Prop, witnesses []core.Term, door rungOpts) bool {
	if stated.NumHyps() > 0 {
		return false
	}
	binders, matrix, ok := statedTupleBinders(stated.Conclusion(), len(witnesses))
	if !ok {
		return false
	}
	wits := permuteByTypeIfIllTyped(binders, witnesses)
	subs := make([]core.TermSubst, len(binders))
	for i, b := range binders {
		if !b.Type().Equals(wits[i].Type()) {
			return false
		}
		subs[i] = ext.MakeTermSubst(b, wits[i])
	}
	inst := matrix.Substitute(subs...)
	for {
		ante, rest, ok := ext.MatchesIMPLY(inst)
		if !ok {
			return true
		}
		if !guardSuppliedByContext(goal, ante, door) {
			return false
		}
		inst = rest
	}
}

// unsuppliedStatedGuard names what statedGuardsSupplied missed: the
// first part of a leading guard of the instance — the guard itself, or
// the conjunct of it — that the context does not hold. nil when the
// stated form was declined for another reason (a partial or ill-typed
// tuple, a sequent-shaped premise) or when every guard is supplied.
// The By failure message carries it, so a cite that fell to its clause
// form says which fact the context was missing.
func unsuppliedStatedGuard(goal Prop, stated Prop, witnesses []core.Term, door rungOpts) core.Term {
	if stated.NumHyps() > 0 {
		return nil
	}
	binders, matrix, ok := statedTupleBinders(stated.Conclusion(), len(witnesses))
	if !ok {
		return nil
	}
	wits := permuteByTypeIfIllTyped(binders, witnesses)
	subs := make([]core.TermSubst, len(binders))
	for i, b := range binders {
		if !b.Type().Equals(wits[i].Type()) {
			return nil
		}
		subs[i] = ext.MakeTermSubst(b, wits[i])
	}
	var missing func(t core.Term) core.Term
	missing = func(t core.Term) core.Term {
		if guardSuppliedByContext(goal, t, door) {
			return nil
		}
		if a, b, ok := ext.MatchesAND(t); ok {
			if m := missing(a); m != nil {
				return m
			}
			return missing(b)
		}
		return t
	}
	inst := matrix.Substitute(subs...)
	for {
		ante, rest, ok := ext.MatchesIMPLY(inst)
		if !ok {
			return nil
		}
		if m := missing(ante); m != nil {
			return ext.BetaEtaNormalize(context.Background(), m)
		}
		inst = rest
	}
}

// conjuncts flattens a ∧-spine.
func conjuncts(t core.Term) []core.Term {
	if a, b, ok := ext.MatchesAND(t); ok {
		return append(conjuncts(a), conjuncts(b)...)
	}
	return []core.Term{t}
}

// mentionsUnbound reports whether t mentions a slot not yet bound.
func mentionsUnbound(t core.Term, slots unify.TermNameSet, bindings unify.MatchBindings) bool {
	for _, v := range t.Frees(nil) {
		if slots.Has(v.Name()) {
			if _, bound := bindings[v.Name()]; !bound {
				return true
			}
		}
	}
	return false
}

// structurallyResident reports whether t is provable from goal's
// hypotheses by assumption alone: resident up to βη, or a conjunction
// whose conjuncts are — the shape the premise split leaves a conjunctive
// antecedent in. The rung's normal form, not α, for the same reason the
// guard test (rungReader.resident) reads that way: the big-operator
// sugar lowers `Σ_{i∈k} u(i)` to `real_sum(k, λi.u(i))` while a law
// binds the bare `u`, so the fact the context holds and the antecedent
// the head asks for differ by an η-expansion the normal form identifies
// — and the conclusion check (rungReader.same) already accepted
// exactly that. Measured: a `real_sum.NonnegEqZero` cite whose every binder
// the rung had pinned fell to the refuter on this check alone.
//
// An antecedent is a goal of its own, and is supplied when the context
// closes it as one (closeGoal), one apply deep: the rung closes
// `∀n. 0 ≤ n ⇒ P(n)` and `P(c)` as GOALS from a resident `∀N. P(N)`,
// and an antecedent of either shape reads the same way. Measured
// before it did: a fact stated for every index, cited into a law that
// reads it from index 0 on, fell to the refuter and cost a plan at each
// site (real_sequences.LimitLessEq), and a chain of cited laws, each
// one's guard the consequent of the ones before, cost a key
// (word_bits.BitsEqAll).
func structurallyResident(goal Prop, t core.Term, door rungOpts) bool {
	return len(unsuppliedPieces(goal, t, false, door.withDepth(antecedentApplies))) == 0
}

// residentByAssumption is structurallyResident read closed: resident up
// to βη, or a conjunction whose conjuncts are — nothing opened, nothing
// applied.
func residentByAssumption(goal Prop, t core.Term, door rungOpts) bool {
	return len(unsuppliedPieces(goal, t, false, door.withDepth(byAssumption))) == 0
}

// commitApply replays a validated run on the real leaf. Every step
// below succeeded on the dry run over the same sequent; a refusal is
// an engine invariant break and panics as one. The head and its
// instance are located as the dry run read them, α-exactly
// (alphaHypIndex): a look-alike up to normal form is not the head.
func commitApply(leaf *GoalStackNode, head int, run *applyRun) {
	must := func(n *GoalStackNode, st _Step, what string) {
		if !n.runStep(st) {
			panic(fmt.Sprintf("apply-close: %s refused after its dry run succeeded (engine invariant)\n  leaf: %s",
				what, prop.PrintProp(n.Goal)))
		}
	}
	sole := func(n *GoalStackNode) *GoalStackNode {
		kids := n.Children()
		Assert(len(kids) == 1)
		return kids[0]
	}
	node := leaf

	// 0. A goal matched the other way round is turned to the head's
	//    orientation first; the hypotheses are untouched, so the head's
	//    index still names it.
	if run.flip {
		must(node, Symm(), "turning the goal to the head's orientation")
		node = sole(node)
	}

	// 0'. An antecedent the context closes and does not hold is made
	//     resident while the context is the one the dry run read — the
	//     head still wide, since the antecedent may be closed by the
	//     head itself. The head is then located again by its statement:
	//     an assertion moves indices.
	headTerm := node.Goal.Hyp(head)
	for _, g := range run.ground {
		node = supplyPieces(node, g, false, run.applies)
	}
	if run.iffSide != 0 {
		node = supplyPieces(node, run.iffOther, false, run.applies)
	}
	if at, err := alphaHypIndex(node.Goal, headTerm); err == nil {
		head = at
	} else {
		panic(fmt.Sprintf("apply-close: the head vanished while its antecedents were supplied (engine invariant): %v", err))
	}

	// 1. Ground the head at the witnesses.
	if len(run.witnesses) > 0 {
		must(node, Specialize(InstHyp(head, run.witnesses...)), "grounding the head")
		node = sole(node)
	}

	// 2. Make each antecedent resident in the head's own spelling — an
	//    assumption where it already is, an assertion proved by
	//    assumption where only its conjuncts are.
	for _, g := range run.ground {
		if node.Goal.AnyHyp(g.AlphaEquals) {
			continue
		}
		must(node, _AssertStep{claim: prop.MakeProp(g)}, "asserting an antecedent")
		kids := node.Children()
		Assert(len(kids) == 2)
		proveByAssumption(kids[0])
		node = kids[1]
	}

	// 3. Modus ponens down the head, one antecedent at a time: the
	//    split leaves the branch holding ¬Aᵢ, closed by the contradiction
	//    with the resident Aᵢ, and continues with the branch holding the
	//    consequent. A branch is known by its statement, not its
	//    position: the split folds a branch into the other where the
	//    other is stronger (makeSubGoalsAt) — the consequent's branch
	//    into ¬Aᵢ's where the leaf already holds ¬Aᵢ beside Aᵢ, so that
	//    the contradiction closes the leaf whole, and ¬Aᵢ's branch into
	//    the consequent's where the leaf already holds the consequent.
	expected := run.conclusion
	for k := len(run.ground) - 1; k >= 0; k-- {
		expected = ext.Apply(ext.IMPLY, run.ground[k], expected).Core()
	}
	for range run.ground {
		idx, err := alphaHypIndex(node.Goal, expected)
		if err != nil {
			panic(fmt.Sprintf("apply-close: the head vanished between steps (engine invariant): %v", err))
		}
		must(node, SplitHypImplyAt(idx), "modus ponens on the head")
		ante, rest, _ := ext.MatchesIMPLY(expected)
		denial := ext.Not(ante).Core()
		var consequent *GoalStackNode
		for _, kid := range node.Children() {
			if kid.Goal.AnyHyp(denial.AlphaEquals) {
				must(kid, _BasicTactic{}, "closing the ¬antecedent branch by contradiction")
				if !kid.Proved() {
					panic("apply-close: the ¬antecedent branch did not close (engine invariant)")
				}
				continue
			}
			Assert(consequent == nil)
			consequent = kid
		}
		if consequent == nil {
			// The consequent's branch folded into ¬Aᵢ's, which the
			// contradiction closed: the leaf is closed with it.
			if !run.applies.closed(leaf) {
				panic("apply-close: the leaf holds an antecedent beside its denial and is still open (engine invariant)")
			}
			return
		}
		node = consequent
		expected = rest
	}

	if run.iffSide != 0 {
		// 4'. The instantiated conclusion is resident as L ⇔ R, the goal
		//     is one side and the context holds the other: make that side
		//     resident in the head's spelling, split the ⇔ into the
		//     branch where both sides hold — the goal is then resident —
		//     and the branch where neither does, a contradiction with the
		//     resident side.
		if !node.Goal.AnyHyp(run.iffOther.AlphaEquals) {
			must(node, _AssertStep{claim: prop.MakeProp(run.iffOther)}, "asserting the ⇔'s other side")
			kids := node.Children()
			Assert(len(kids) == 2)
			proveByAssumption(kids[0])
			node = kids[1]
		}
		idx, err := alphaHypIndex(node.Goal, run.conclusion)
		if err != nil {
			panic(fmt.Sprintf("apply-close: the ⇔ head vanished between steps (engine invariant): %v", err))
		}
		must(node, SplitHypIffAtCases(idx), "splitting the ⇔")
		kids := node.Children()
		Assert(len(kids) == 2)
		l, r, _ := ext.MatchesIFF(run.conclusion)
		iffSide := r
		if run.iffSide == 2 {
			iffSide = l
		}
		for _, kid := range kids {
			if run.through != nil {
				// Read through: in the branch where both sides hold the
				// side is resident, and is applied to the goal as the law
				// it is — or, where the law is one conjunct of the side,
				// the side is split until that conjunct is resident and
				// the conjunct is applied.
				if at, err := alphaHypIndex(kid.Goal, run.throughSide); err == nil {
					node := kid
					if run.throughHead != nil {
						for {
							if at, err = alphaHypIndex(node.Goal, run.throughHead); err == nil {
								break
							}
							must(node, _SplitHypConj{}, "splitting the ⇔'s side toward the conjunct read through")
							node = sole(node)
						}
					}
					commitApply(node, at, run.through)
					continue
				}
			}
			c := kid.Goal.Conclusion()
			if run.conjunct && kid.Goal.AnyHyp(iffSide.AlphaEquals) {
				// The goal is one conjunct of the side, resident in the
				// branch where both sides hold: split it where it stands
				// until the goal is, as step 4 splits a conjunctive
				// conclusion.
				node := kid
				for node != nil && !node.Goal.AnyHyp(run.applies.reader().resident(c)) {
					if !node.runStep(_SplitHypConj{}) {
						mustRead(node, "the ⇔'s side, toward the conjunct the goal is")
					}
					node = readOn(node)
				}
				if node != nil {
					proveByAssumption(node)
				}
				continue
			}
			if kid.Goal.AnyHyp(c.AlphaEquals) || kid.Goal.AnyHyp(run.applies.reader().resident(c)) {
				proveByAssumption(kid)
				continue
			}
			must(kid, _BasicTactic{}, "closing the branch where neither side holds by contradiction")
			if !kid.Proved() {
				panic("apply-close: the ⇔'s neither-branch did not close (engine invariant)")
			}
		}
		if !run.applies.closed(leaf) {
			panic("apply-close: every step of the ⇔ reading ran and the leaf is still open (engine invariant)")
		}
		return
	}
	// 4. The instantiated conclusion is resident and is the goal — or a
	//    conjunction one of whose conjuncts is: split where it stands
	//    until the goal is resident, the leaf read first (readLeaf) where
	//    the conjunction is the conclusion's reading.
	if run.conjunct {
		for node != nil && !node.Goal.AnyHyp(run.applies.reader().resident(node.Goal.Conclusion())) {
			if !node.runStep(_SplitHypConj{}) {
				mustRead(node, "the head's conclusion, toward the conjunct the goal is")
			}
			node = readOn(node)
		}
	}
	if node != nil {
		proveByAssumption(node)
	}
	// Closed up to the claims the antecedents' installs registered.
	if !run.applies.closed(leaf) {
		panic("apply-close: every step ran and the leaf is still open (engine invariant)")
	}
}

// proveByAssumption closes n, whose conclusion residentByAssumption
// accepted: by assumption, or by splitting a conjunction and recursing.
func proveByAssumption(n *GoalStackNode) { proveResident(n, false) }

// readLeaf reads the leaf one step toward the rung's normal form
// (rungReader.normal): its memberships in identity-form set-builders
// (_MembershipRead) where it spells one, else its record projections of
// packed values (_RecordRead) where it spells one, else, with numerals,
// its numerals (_NumeralRead) — the kernel's side of the rung's reading,
// a step a reading. Returns the one child; n itself where the numeral
// reading closed it — its conclusion read ⊤, or a hypothesis ⊥; nil
// where the leaf spells nothing left to read.
func readLeaf(n *GoalStackNode, numerals bool) *GoalStackNode {
	if !n.runStep(_MembershipRead{}) && !n.runStep(_RecordRead{}) {
		if !numerals || !n.runStep(_NumeralRead{}) {
			return nil
		}
		if n.Proved() {
			return n
		}
	}
	kids := n.Children()
	Assert(len(kids) == 1)
	return kids[0]
}

// readOn is the leaf a commit path continues on after a split or a
// reading of n: n's one child, or nil where the numeral reading closed n
// and there is nothing left to continue on.
func readOn(n *GoalStackNode) *GoalStackNode {
	if n.Proved() {
		return nil
	}
	kids := n.Children()
	Assert(len(kids) == 1)
	return kids[0]
}

// closeByReading reads n, a reading a step, until the numeral reading
// closes it: a leaf whose conclusion reads ⊤ or one of whose hypotheses
// reads ⊥ (rungReader.closes), perhaps through a membership or a record
// projection read first. False where the readings are exhausted with
// the leaf open.
func closeByReading(n *GoalStackNode) bool {
	for node := n; ; {
		kid := readLeaf(node, true)
		switch kid {
		case nil:
			return false
		case node:
			return true
		}
		node = kid
	}
}

// mustRead is readLeaf on the commit path, where the dry run read the
// same leaf: a leaf with nothing left to read is an engine invariant
// break.
func mustRead(n *GoalStackNode, what string) {
	if readLeaf(n, true) == nil {
		panic(fmt.Sprintf("apply-close: reading %s refused after its dry run succeeded (engine invariant)\n  leaf: %s",
			what, prop.PrintProp(n.Goal)))
	}
}

// proveResident closes n, whose conclusion the context holds read by
// assumption (unsuppliedPieces at byAssumption, with the same flip), in
// the order that reading tests it: a conclusion resident as written or
// up to βη by the assumption step, which carries the hypothesis over
// through the kernel's own βη conversion; with flip, an equation
// resident the other way round by turning it first; one resident up to
// the rung's reading AS A WHOLE — turned so, or a conjunction that
// one resident `x ∈ {p | φ ∧ ψ}` holds as one fact — by reading the
// leaf first (readLeaf: its memberships, then its record projections,
// a step a reading until none is left) and then as above, before
// any split: split first, neither side alone is anything the context
// holds; then a conjunction by its two sides; and a conjunction only
// once read by reading and then splitting. Nothing else normalizes: a
// closer that does reads a law stated as a redex and the same law
// reduced as two different clause sets once the law concludes a
// conjunction, and the pair no longer meets.
//
// The conclusion is closed without its numerals where the context holds
// it so (plainReader) — the steps a proof took before a numeral was a
// value to the rung — and with the numeral reading only where it does
// not.
func proveResident(n *GoalStackNode, flip bool) {
	read := plainReader
	if len(unsuppliedPieces(n.Goal, n.Goal.Conclusion(), flip, rungOpts{depth: byAssumption, plain: true})) > 0 {
		read = readerOf(n.proofScope)
	}
	proveResidentIn(n, flip, read)
}

// proveResidentIn is proveResident in the one reading read names.
func proveResidentIn(n *GoalStackNode, flip bool, read rungReader) {
	c := n.Goal.Conclusion()
	if n.Goal.AnyHyp(residentModuloBetaEta(c)) {
		if !n.runStep(_Assumption{}) {
			panic(fmt.Sprintf("apply-close: assumption refused a conclusion resident up to βη (engine invariant): %s",
				ext.PrintTerm(c)))
		}
		return
	}
	// A conclusion that reads ⊤ at its numerals was accepted with no
	// supplier (unsuppliedPieces): the reading closes it.
	if read.readsTrue(c) {
		if !closeByReading(n) {
			panic(fmt.Sprintf("apply-close: the numeral reading did not close a conclusion it reads ⊤ (engine invariant): %s",
				ext.PrintTerm(c)))
		}
		return
	}
	var turned core.Term
	if l, r, ok := ext.MatchesEQ(c); flip && ok {
		turned = ext.WrapTerm(r).Eq(ext.WrapTerm(l)).Core()
	}
	if turned != nil && n.Goal.AnyHyp(residentModuloBetaEta(turned)) {
		if !n.runStep(Symm()) {
			panic(fmt.Sprintf("apply-close: turning an equation resident the other way round refused (engine invariant): %s",
				ext.PrintTerm(c)))
		}
		kids := n.Children()
		Assert(len(kids) == 1)
		if !kids[0].runStep(_Assumption{}) {
			panic(fmt.Sprintf("apply-close: assumption refused a turned equation (engine invariant): %s",
				ext.PrintTerm(c)))
		}
		return
	}
	if n.Goal.AnyHyp(read.resident(c)) || (turned != nil && n.Goal.AnyHyp(read.resident(turned))) {
		kid := readLeaf(n, read.readsNumerals())
		if kid == nil {
			panic(fmt.Sprintf("apply-close: the leaf spells nothing left to read for a conclusion resident up to the rung's reading (engine invariant): %s\n  leaf: %s",
				ext.PrintTerm(c), prop.PrintProp(n.Goal)))
		}
		if kid != n {
			proveResident(kid, flip)
		}
		return
	}
	if read.heldAsConjunct(n.Goal, c, flip) {
		// A conjunct of one resident fact: the resident conjunctions are
		// split, one a step, until the conclusion stands alone among
		// the hypotheses, and it closes as above. The hypotheses bound
		// the steps.
		for range n.Goal.NumHyps() {
			if !n.runStep(_SplitHypConj{}) {
				panic(fmt.Sprintf("apply-close: splitting a resident conjunction refused for a conclusion it holds as a conjunct (engine invariant): %s",
					ext.PrintTerm(c)))
			}
			kids := n.Children()
			Assert(len(kids) == 1)
			n = kids[0]
			if !read.heldAsConjunct(n.Goal, c, flip) {
				break
			}
		}
		proveResident(n, flip)
		return
	}
	if _, _, ok := ext.MatchesAND(c); ok {
		if !n.runStep(SplitConj()) {
			panic("apply-close: splitting a conjunctive antecedent refused (engine invariant)")
		}
		for _, k := range n.Children() {
			proveResident(k, flip)
		}
		return
	}
	if kid := readLeaf(n, read.readsNumerals()); kid != nil {
		if kid != n {
			proveResident(kid, flip)
		}
		return
	}
	panic(fmt.Sprintf("apply-close: antecedent accepted as resident is not (engine invariant): %s",
		ext.PrintTerm(c)))
}

func describeWitnesses(ws []core.Term) string {
	parts := make([]string, len(ws))
	for i, w := range ws {
		parts[i] = clipRunes(ext.PrintTerm(w), 40)
	}
	return strings.Join(parts, ", ")
}

// identityInstanceAdmissible reports whether the head's stated form is
// itself a candidate at goal: every type variable of head occurs in
// goal (the goal is polymorphic in the head's own letters, so the
// identity instance — the one typematch's enumerator drops — is one
// the goal offers), and the head is a Horn law — the structure-law
// shape `∀comps. S(comps) ⇒ body`, a set law `finite(t) ∧ s ⊆ t ⇒
// finite(s)` with its antecedent a conjunction, alike — or an ⇔, the
// definition-as-membership shape `u ∈ T ⇔ …` read as its Horn clauses
// and through its sides (a chapter's own OpenIff at the chapter's
// letter, where nothing else offers the instance). The identity
// candidate is then planned, dry-run and committed on the terms of
// every enumerated instance.
func identityInstanceAdmissible(head, goal core.Prop) bool {
	body := head.Conclusion()
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			break
		}
		body = abs.Body()
	}
	if _, _, iff := ext.MatchesIFF(body); !iff {
		if _, _, ok := matchesImply(body); !ok {
			return false
		}
	}
	letters := map[core.TypeName]bool{}
	collect := func(v core.VarType) bool { letters[v.Name()] = true; return false }
	ext.TermAnyTypeVar(head.Conclusion(), collect)
	for i := 0; i < head.NumHyps(); i++ {
		ext.TermAnyTypeVar(head.Hyp(i), collect)
	}
	for name := range letters {
		byName := func(v core.VarType) bool { return v.Name() == name }
		if ext.TermAnyTypeVar(goal.Conclusion(), byName) {
			continue
		}
		found := false
		for i := 0; i < goal.NumHyps() && !found; i++ {
			found = ext.TermAnyTypeVar(goal.Hyp(i), byName)
		}
		if !found {
			return false
		}
	}
	return len(letters) > 0
}

// pinnedBinderTypes reads the type each pinned binder's term has —
// what a `Where` / term_specialize commits the instance to.
func pinnedBinderTypes(named []NamedWitness) map[string]core.HolType {
	if len(named) == 0 {
		return nil
	}
	pins := make(map[string]core.HolType, len(named))
	for _, nw := range named {
		pins[nw.Binder] = nw.Witness.Type()
	}
	return pins
}

// consistentWithPins keeps the candidate instances under which every
// pinned binder has exactly its pinned term's type — the binders read
// through the guards, as matchHead reads them. A binder the candidate
// does not bind is no constraint.
func consistentWithPins(candidates []core.Prop, pins map[string]core.HolType) []core.Prop {
	var out []core.Prop
	for _, cand := range candidates {
		ok := true
		binders, _ := ematch.StripGuardedForalls(cand.Conclusion())
		for _, b := range binders {
			if want, pinned := pins[string(b.Name())]; pinned && !b.Type().Equals(want) {
				ok = false
				break
			}
		}
		if ok {
			out = append(out, cand)
		}
	}
	return out
}

// abstractionEquationNote names the one goal shape an apply plan can
// never fire on and a reader rarely expects: an equation between two
// abstractions, which a preceding Congr on a fold leaves behind (the
// single differing subterm of `iterated_op(op, s, λ₁) = iterated_op(op, s, λ₂)`
// is the λ). Funext opens it to the bodies, where the law matches.
func abstractionEquationNote(goal Prop) string {
	l, r, ok := ext.MatchesEQ(goal.Conclusion())
	if !ok {
		return ""
	}
	if lv, _ := ext.MatchesAbs(l); lv == nil {
		return ""
	}
	if rv, _ := ext.MatchesAbs(r); rv == nil {
		return ""
	}
	return " — the goal is an equation between two abstractions (what Congr on a fold leaves); Funext() opens it to their bodies"
}

// headCandidates is the type-instance enumeration of a stated form at
// a goal — the `by` rung's and `retrieve`'s alike. A polymorphic head
// is tried at EVERY type instance the goal offers
// (typematch.EnumerateLemmaTypeAdaptations — a goal holding two
// instances of one constant, finite at A and at B, makes the first
// guess a coin toss), each validated by the dry run; the chain a
// resident install goes through picks among its candidates the same
// way. The stated form itself is tried LAST when the goal is
// polymorphic in the head's own type variables — a structure law
// applied at its own hypothesis, which is every leaf of an abstract
// chapter — since that goal offers exactly the identity instance,
// which the enumerator drops by contract. A concrete goal never gets
// it: the dry run's match is first-order and lenient about types, so
// the identity would pass the plan there and be refused at the kernel.
// A monomorphic head is its own only candidate.
func headCandidates(stated core.Prop, goal Prop) []core.Prop {
	if !ext.PropHasTypeVars(stated) {
		return []core.Prop{stated}
	}
	candidates := typematch.EnumerateLemmaTypeAdaptations(stated, goal)
	if identityInstanceAdmissible(stated, goal) {
		candidates = append(candidates, stated)
	}
	return candidates
}

// FactSource supplies what the context does not: the corpus's bare
// facts — hyp-free members stated with no leading ∀ and no free
// variable, the structure instances above all — by the constant at
// their head, and which of those heads are structure predicates.
// `retrieve` hands ReadHead one; `by` hands none, since a witness
// neither the goal nor the context spells is not the rung's to invent.
// The facts do two things. An antecedent piece left with an unbound
// binder is matched against the facts at its head (match), so a law
// whose antecedent alone fixes a binder (`comm_ring(R) ⇒ …` at a goal
// that spells only the values of R's add and mul) reads with the
// instance a member states — the premise `by` would name. And a
// structure fact offers the TYPE instance of a head whose antecedent
// states its structure (instances), so a law whose conclusion spells
// no constant the goal shares — `comm_monoid(op, e) ⇒ op(x, y) = op(y,
// x)` at `x * y = y * x` on ℝ, where only the operation's slot stands
// against `real_mul` — is read at the carrier the corpus's instance
// fixes, which the goal's own constants cannot.
type FactSource struct {
	ByHead     map[core.TermName][]core.Term
	Structures map[core.TermName]bool
}

// match extends a trial of the bindings by the first fact at the
// piece's head that matches it; every attempt starts from a fresh
// trial(), since a failed match may write into its copy.
func (f *FactSource) match(piece core.Term, slots unify.TermNameSet, trial func() unify.MatchBindings) (unify.MatchBindings, bool) {
	head, ok := unify.SpineHeadConst(piece)
	if !ok {
		return nil, false
	}
	for _, fact := range f.ByHead[head] {
		bindings := trial()
		if unify.TermMatchApproxEtaWith(piece, fact, slots, bindings) {
			return bindings, true
		}
	}
	return nil, false
}

// instances lists the type instances of a polymorphic head that the
// structure facts offer: for each antecedent piece of the telescoped
// head whose constant is a structure predicate, the head's letters
// matched against the constant's type at each fact stated with it —
// distinct, the identity dropped, in antecedent then fact order. A
// fact that itself carries a type letter fixes nothing and offers
// none.
func (f *FactSource) instances(head core.Prop) []core.Prop {
	if !ext.PropHasTypeVars(head) {
		return nil
	}
	letters := map[core.TypeName]bool{}
	ext.TermAnyTypeVar(head.Conclusion(), func(v core.VarType) bool { letters[v.Name()] = true; return false })
	ofHead := func(v core.VarType) bool { return letters[v.Name()] }
	anyLetter := func(core.VarType) bool { return true }
	_, antes, _, _ := ematch.Telescope(head.Conclusion(), utils.EmptySet[core.TermName]())
	var out []core.Prop
	seen := map[core.PropKey]bool{}
	for _, a := range antes {
		for _, piece := range conjuncts(a) {
			pieceHead, _ := ext.MatchesApply(piece)
			pc, ok := pieceHead.AsConst()
			if !ok || !f.Structures[pc.Name()] {
				continue
			}
			for _, fact := range f.ByHead[pc.Name()] {
				factHead, _ := ext.MatchesApply(fact)
				fc, ok := factHead.AsConst()
				if !ok || ext.TypeAnyVar(fc.Type(), anyLetter) {
					continue
				}
				var env []core.TypeSubst
				if !core.MatchTypeInto(pc.Type(), fc.Type(), ofHead, &env) {
					continue
				}
				if env = nonIdentityTypeSubst(env); len(env) == 0 {
					continue
				}
				inst := core.PropTypeInst(head, env...)
				if key := inst.AlphaKey(); !seen[key] {
					seen[key] = true
					out = append(out, inst)
				}
			}
		}
	}
	return out
}

// HeadReading is a stated form read against a goal by the apply rung's
// plan alone (StatedHead.Read) — no kernel dry run: the witnesses the conclusion, the
// context and the facts pin, in stated binder order, and every
// antecedent instantiated at them, with whether the context already
// supplies it (structurally: α-resident, a conjunct of one resident
// fact, a conjunction of such, or closed one apply deep). It
// is what `retrieve` reports about a corpus member that applies to a
// goal, and it is the reading `by` validates before committing: a head
// that reads is a head the rung fires, up to the kernel's spelling of
// the instance. The witnesses are for reading — a closure binder (a
// free variable of the stated form) is named by that variable, which
// no `term_specialize` table addresses.
type HeadReading struct {
	Witnesses []NamedWitness
	Premises  []HeadPremise
}

// HeadPremise is one antecedent at the witnesses, and whether the
// context supplies it.
type HeadPremise struct {
	Term     core.Term
	Resident bool
}

// closeByArith decides n's goal by the arithmetic closer under its
// context — the door's own closer, applied to an antecedent the rung has
// to supply. The decision runs on a clone of n first and is committed on
// n only when it proves the goal: a decider that only simplifies (an
// arithmetic atom folded inside a resident hypothesis, the goal itself
// not arithmetic) leaves n the bare leaf the rungs after this door run
// on, where a committed simplification would be a ministep the next
// rung's commit runs into. n takes the leaf's scope before the clone is
// made, so the trial and the commit read one policy.
//
// ctx cuts the trial off: the decision polls it before each leaf of the
// decider, and a done context raises a utils.Cut there, which unwinds
// to the door with n as it was. A rung tries this decision on every
// antecedent of every head it weighs, so the trials of one rung can
// outlast any budget where each alone would not. The commit runs to its
// end whatever the context: it is the trial's cost again, and a commit
// the context stopped half way would leave n half closed.
func closeByArith(ctx context.Context, n *GoalStackNode, scope *ProofScope) bool {
	if n.proofScope == nil && scope != nil {
		n.SetProofScope(scope)
	}
	trial := n.Clone()
	if !ApplyArithSimplify(ctx, trial) || !trial.Proved() {
		return false
	}
	// The trial proved the goal: the same deterministic steps on n.
	if !ApplyArithSimplify(context.Background(), n) || !n.Proved() {
		panic(fmt.Sprintf("apply-close: the arithmetic decider refused on the leaf after proving its clone (engine invariant)\n  leaf: %s",
			prop.PrintProp(n.Goal)))
	}
	return true
}
