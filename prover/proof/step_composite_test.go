// step_composite_test.go — the recorded composite ministeps
// (step_composite.go), one section per member.
//

package proof

import (
	"context"
	"slices"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// =======================================================================
// DefExpand
// =======================================================================

// TestApplyDefExpand_HypOccurrence pins the hyp-coverage guarantee for
// def_expand: a definitional-const occurrence inside a HYP is expanded
// alongside occurrences in the conclusion. Pre-change, the fast-path
// walker in prover/tactic/def_expand.go traversed only
// goal.Conclusion(), so a hyp-only occurrence returned nil (and, under
// the IsSimpleDefExpandShape authoritative-skip contract in
// step.go, the entire def_expand tactic reported "did not apply"
// — the "def_expand can't touch hyps" scope gap that walled hyp-driven
// refutation attempts on STEP.A of an iterated-product proof.
//
// Setup:  ⊢ set_member = λu.λv. v(u).  Goal: `set_member(x, s) ⊢ p`
// where p is unrelated. After def_expand(set_member), the residual has hyp
// `s(x)` (β-reduced from set_member(x,s)).
func TestApplyDefExpand_HypOccurrence(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Build set_member : α → (α → bool) → bool with body λu.λv. v(u).
	alpha := core.TypeA()
	setT := core.MakeFun(alpha, core.TypeBool())
	u := ext.Var("u", alpha)
	v := ext.Var("v", setT)
	body := u.To(v.To(v.Apply(u)))
	inConst := core.NewConstDef(body.Core(), "TestDefExpand_IN")
	require.False(t, inConst.DefThm().IsZero(), "set_member def thm must materialize")

	// Goal terms.
	x := ext.Var("x", alpha)
	s := ext.Var("s", setT)
	inXS := ext.WrapTerm(inConst).Apply(x, s) // set_member(x, s)
	p := ext.Var("p", core.TypeBool())

	// Goal: set_member(x, s) ⊢ p
	goal := prop.MakeProp(p.Core(), inXS.Core())

	// Sanity: a hyp-only path would return nil. We call
	// the fast path directly through tactic.TryDefExpand (same
	// interface step.go's _LeanRwTactic.apply hits).
	sg := tactic.TryDefExpand(inConst.DefThm(), goal)
	require.NotNil(t, sg, "fast path must fire when the const appears in a hyp")
	require.Equal(t, 2, sg.Size(), "expected [lemma, subgoal] shape")

	// Subgoal: hyp should be `s(x)` (β-reduced from set_member(x, s)).
	sub := sg.ChildGoal(1)
	require.Equal(t, 1, sub.NumHyps(), "subgoal preserves the (rewritten) hyp count")
	expected := s.Apply(x).Core()
	require.True(t, sub.Hyp(0).AlphaEquals(expected),
		"expected hyp to β-reduce to s(x); got %s", sub.Hyp(0))
	require.True(t, sub.Conclusion().AlphaEquals(p.Core()),
		"conclusion should be unchanged (no set_member there); got %s", sub.Conclusion())
}

// TestApplyDefExpand_HypAndConclOccurrences pins that occurrences in
// BOTH concl and hyp are rewritten in a single fast-path pass, and that
// reconstruction composes correctly.
func TestApplyDefExpand_HypAndConclOccurrences(t *testing.T) {
	defer goleak.VerifyNone(t)

	alpha := core.TypeA()
	setT := core.MakeFun(alpha, core.TypeBool())
	u := ext.Var("u", alpha)
	v := ext.Var("v", setT)
	body := u.To(v.To(v.Apply(u)))
	inConst := core.NewConstDef(body.Core(), "TestDefExpand_IN_both")

	x := ext.Var("x", alpha)
	s := ext.Var("s", setT)
	y := ext.Var("y", alpha)
	t2 := ext.Var("t", setT)
	inXS := ext.WrapTerm(inConst).Apply(x, s)
	inYT := ext.WrapTerm(inConst).Apply(y, t2)

	// Goal: set_member(x, s) ⊢ set_member(y, t)
	goal := prop.MakeProp(inYT.Core(), inXS.Core())

	sg := tactic.TryDefExpand(inConst.DefThm(), goal)
	require.NotNil(t, sg)

	sub := sg.ChildGoal(1)
	require.Equal(t, 1, sub.NumHyps())
	// Hyp should be s(x); conclusion should be t(y).
	require.True(t, sub.Hyp(0).AlphaEquals(s.Apply(x).Core()),
		"hyp expected s(x), got %s", sub.Hyp(0))
	require.True(t, sub.Conclusion().AlphaEquals(t2.Apply(y).Core()),
		"concl expected t(y), got %s", sub.Conclusion())
}

// TestApplyDefExpand_NoOpWhenAbsent pins that fast path returns nil
// when the const appears in neither concl nor hyps — no false-positive
// fast-path fires.
func TestApplyDefExpand_NoOpWhenAbsent(t *testing.T) {
	defer goleak.VerifyNone(t)

	alpha := core.TypeA()
	setT := core.MakeFun(alpha, core.TypeBool())
	u := ext.Var("u", alpha)
	v := ext.Var("v", setT)
	body := u.To(v.To(v.Apply(u)))
	inConst := core.NewConstDef(body.Core(), "TestDefExpand_IN_absent")

	// Goal has no set_member.
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goal := prop.MakeProp(p.Core(), q.Core())

	sg := tactic.TryDefExpand(inConst.DefThm(), goal)
	require.Nil(t, sg, "fast path must return nil when the const is nowhere in the goal")
}

// =======================================================================
// SetTac — membership mode
// =======================================================================

// fullMiniSetTheory extends miniSetTheory with intersection and the
// comprehension plumbing (set_comprehension/comprehension_spec), enough to state `s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}`
// with a real set-builder term.
type fullMiniSetTheory struct {
	miniSetTheory
	inter, setComprehension, comprehensionSpec core.ConstTerm
}

func makeFullMiniSetTheory() fullMiniSetTheory {
	m := makeMiniSetTheory()
	genSetT := core.MakeFun(core.TypeA(), core.TypeBool())

	inG := ext.WrapTerm(m.in) // set_member@[A]

	// intersection := λs.λt.λy. set_member(y, s) ∧ set_member(y, t)
	s := ext.Var("s", genSetT)
	t2 := ext.Var("t", genSetT)
	y := ext.Var("y", core.TypeA())
	interC := core.NewConstDef(
		s.To(t2.To(y.To(inG.Apply(y, s).And(inG.Apply(y, t2))))).Core(), "intersection")

	// set_comprehension := λp. p (the comprehension marker is the identity)
	p := ext.Var("p", genSetT)
	setComprehensionC := core.NewConstDef(p.To(p).Core(), "set_comprehension")

	// comprehension_spec := λv.λP.λt. P ∧ (v = t)
	v := ext.Var("v", core.TypeA())
	P := ext.Var("P", core.TypeBool())
	t3 := ext.Var("t", core.TypeA())
	comprehensionSpecC := core.NewConstDef(
		v.To(P.To(t3.To(P.And(v.Eq(t3))))).Core(), "comprehension_spec")

	return fullMiniSetTheory{miniSetTheory: m, inter: interC, setComprehension: setComprehensionC, comprehensionSpec: comprehensionSpecC}
}

// interUnionsGoal builds the intersection of a union (first conjunct) at the
// ground element type, comprehension and all:
//
//	big_union(s₀) ∩ t₀ = big_union {u ∩ t₀ | u ∈ s₀}
//
// where {u ∩ t₀ | u ∈ s₀} is set_comprehension(λg. ∃u. comprehension_spec(g, u ∈ s₀, u ∩ t₀))
// at the family instance. The ⇒ direction of the pointwise ⇔ needs the
// SET witness `u ∩ t₀` — first-order iff intersection stays opaque.
func (m fullMiniSetTheory) interUnionsGoal() Prop {
	s0 := ext.Var("s0", m.famT)
	t0 := ext.Var("t0", m.setT)

	interI := m.at(m.inter, m.elemT)                      // set ∩ set
	unionsI := m.at(m.unions, m.elemT)                    // family → set
	inSetI := m.at(m.in, m.setT)                          // set ∈ family
	setComprehensionI := m.at(m.setComprehension, m.setT) // family-level comprehension marker
	comprehensionSpecI := m.at(m.comprehensionSpec, m.setT)

	lhs := interI.Apply(unionsI.Apply(s0), t0)

	g := ext.Var("g", m.setT)
	u := ext.Var("u", m.setT)
	comprehension := setComprehensionI.Apply(g.To(ext.Exists(u)(
		comprehensionSpecI.Apply(g, inSetI.Apply(u, s0), interI.Apply(u, t0)))))
	rhs := unionsI.Apply(comprehension)

	return prop.MakeProp(lhs.Eq(rhs).Core())
}

// TestSetTacMembership_InterUnions is THE acceptance test for membership
// mode: the distribution of ∩ over ⋃ closes one-shot. Under LEGACY full expansion this
// goal is structurally out of reach (the ⇒-direction witness becomes a
// λ-term; the first-order refuter cannot synthesize it — verified by the
// negative control below), which is exactly why the mode exists.
func TestSetTacMembership_InterUnions(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = 10 * time.Second

	n := CreateGoalStack(m.interUnionsGoal())
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"membership-mode set_tac must close the distribution of ∩ over ⋃ one-shot")
	assert.True(t, n.Proved())
}

// TestSetTacLegacy_InterUnions_Fails pins the architectural boundary the
// membership mode crosses: LEGACY full expansion cannot close
// that goal (λ-term witness, outside the first-order refuter). If
// this ever starts PASSING, the refuter gained higher-order witness
// synthesis and the membership mode's dispatch priority deserves a
// rethink.
func TestSetTacLegacy_InterUnions_Fails(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = 2 * time.Second

	n := CreateGoalStack(m.interUnionsGoal())
	assert.False(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_LEGACY, nil))
}

// TestSetTacMembership_UnionsInsert pins that membership mode also
// covers the plain set_tac class (no composite witness needed) — the
// dispatch's membership-first ordering must not regress goals legacy
// already closed.
func TestSetTacMembership_UnionsInsert(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()

	n := CreateGoalStack(m.unionsInsertGoal())
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"membership-mode set_tac must close set_algebra.UnionsInsert")
	assert.True(t, n.Proved())
}

// TestSetTacMembership_ModeRecordedInProto pins the replay contract: the
// recorded proto carries the mode, and re-running the recorded (consts,
// mode) pair on the recorded goal closes — the same call emit-time
// verification and Build_X replay execute.
func TestSetTacMembership_ModeRecordedInProto(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = 10 * time.Second

	goal := m.interUnionsGoal()
	n := CreateGoalStack(goal)
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil))

	st := n.miniStep
	require.NotNil(t, st)
	b := ext.NewPoolBuilder()
	pr, ok := st.proto(b).(*StepProto_SetTac)
	require.True(t, ok, "recorded ministep must serialize as StepProto_SetTac")
	require.Equal(t, SetTacMode_SET_TAC_MEMBERSHIP, pr.SetTac.GetMode(),
		"the executor mode must be recorded verbatim")

	// Replay: same consts + same mode on the same goal must close.
	consts := make([]core.TermName, len(pr.SetTac.GetConsts()))
	for i, c := range pr.SetTac.GetConsts() {
		consts[i] = core.TermName(c)
	}
	n2 := CreateGoalStack(goal)
	require.True(t,
		ApplySetTacMode(n2, env, t.Context(), consts, pr.SetTac.GetMode(), nil),
		"replaying the recorded (consts, mode) must close the recorded goal")
	assert.True(t, n2.Proved())
}

// =======================================================================
// SetTac — vocabulary
// =======================================================================

// TestDefaultSetTacConsts_FamilyOps pins the vocabulary extension: the
// family-level operators big_union / big_intersection are part of the default
// set_tac vocabulary, and the list is sorted (SetTacProto contract: recorded order
// is the deterministic processing order).
func TestDefaultSetTacConsts_FamilyOps(t *testing.T) {
	consts := DefaultSetTacConsts()
	for _, want := range []core.TermName{"big_union", "big_intersection"} {
		assert.Contains(t, consts, want)
	}
	assert.True(t, slices.IsSorted(consts), "vocabulary must be recorded sorted")
}

// miniSetTheory is a self-contained polymorphic set layer for
// exercising the set_tac fixpoint without the registry: set_member / union /
// insert / big_union as Type-1 NewConstDef consts (definitionally faithful
// to the corpus's modulo the set_comprehension/comprehension_spec comprehension encoding, which the
// fixpoint would unfold away regardless). Element instances are GROUND
// (TypeInd), so every per-occurrence type instantiation the fixpoint
// performs is occurs-check-free.
type miniSetTheory struct {
	elemT, setT, famT         core.HolType
	in, union, insert, unions core.ConstTerm
}

func makeMiniSetTheory() miniSetTheory {
	genSetT := core.MakeFun(core.TypeA(), core.TypeBool())

	// set_member := λu:A. λv:A→bool. v(u)
	u := ext.Var("u", core.TypeA())
	v := ext.Var("v", genSetT)
	inC := core.NewConstDef(u.To(v.To(v.Apply(u))).Core(), "set_member")
	inG := ext.WrapTerm(inC)                                                             // set_member@[A]
	inSet := ext.WrapTerm(inC.TypeSubstitute(core.MakeTypeSubst(core.TypeA(), genSetT))) // set_member@[A:=A→bool]

	// union := λs.λt.λy. set_member(y, s) ∨ set_member(y, t)
	s := ext.Var("s", genSetT)
	t2 := ext.Var("t", genSetT)
	y := ext.Var("y", core.TypeA())
	unionC := core.NewConstDef(
		s.To(t2.To(y.To(inG.Apply(y, s).Or(inG.Apply(y, t2))))).Core(), "union")

	// insert := λa.λs.λy. (y = a) ∨ set_member(y, s)
	a := ext.Var("a", core.TypeA())
	insertC := core.NewConstDef(
		a.To(s.To(y.To(y.Eq(a).Or(inG.Apply(y, s))))).Core(), "insert")

	// big_union := λf:(A→bool)→bool. λx:A. ∃w:A→bool. set_member(w, f) ∧ set_member(x, w)
	f := ext.Var("f", core.MakeFun(genSetT, core.TypeBool()))
	x := ext.Var("x", core.TypeA())
	w := ext.Var("w", genSetT)
	unionsC := core.NewConstDef(
		f.To(x.To(ext.Exists(w)(inSet.Apply(w, f).And(inG.Apply(x, w))))).Core(),
		"big_union")

	elemT := TypeInd
	return miniSetTheory{
		elemT: elemT,
		setT:  core.MakeFun(elemT, core.TypeBool()),
		famT:  core.MakeFun(core.MakeFun(elemT, core.TypeBool()), core.TypeBool()),
		in:    inC, union: unionC, insert: insertC, unions: unionsC,
	}
}

func (m miniSetTheory) at(c core.ConstTerm, inst core.HolType) *ext.TermWrapper {
	return ext.WrapTerm(c.TypeSubstitute(core.MakeTypeSubst(core.TypeA(), inst)))
}

// unionsInsertGoal builds big_union(s₀ insert f₀) = s₀ union (big_union f₀) at
// the ground element type,
// the smallest big_union goal that needs no composite witness.
func (m miniSetTheory) unionsInsertGoal() Prop {
	s0 := ext.Var("s0", m.setT)
	f0 := ext.Var("f0", m.famT)
	unionsI := m.at(m.unions, m.elemT)
	insertI := m.at(m.insert, m.setT) // inserting a SET into a FAMILY
	unionI := m.at(m.union, m.elemT)

	lhs := unionsI.Apply(insertI.Apply(s0, f0))
	rhs := unionI.Apply(s0, unionsI.Apply(f0))
	return prop.MakeProp(lhs.Eq(rhs).Core())
}

// TestSetTac_UnionsInsert_ClosesWithExtendedVocab is the regression test
// for the big_union vocabulary extension: with big_union in the recorded const
// list, set_tac closes set_algebra.UnionsInsert one-shot (fixpoint unfolds
// big_union/insert/union/set_member, the residual refutes with an ELEMENT-typed
// witness — first-order, unlike the ∩-over-⋃ class). Before the
// extension this exact call failed: big_union stayed an opaque atom and the
// two sides could not bridge (the "did not apply" wall the UnionsInsert
// session agent had to work around with a manual def_expand).
func TestSetTac_UnionsInsert_ClosesWithExtendedVocab(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeMiniSetTheory()
	env := makeStepTestEnv()

	n := CreateGoalStack(m.unionsInsertGoal())
	require.True(t, ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_LEGACY, nil),
		"set_tac must close set_algebra.UnionsInsert with the extended vocabulary")
	assert.True(t, n.Proved())
}

// TestSetTac_UnionsInsert_FailsWithoutUnions is the negative control
// pinning that the vocabulary extension is load-bearing: the SAME goal
// with the pre-extension const list fails (big_union stays opaque, the
// residual cannot refute), and the failure surfaces the residual leaves
// through the diagnostic sink.
func TestSetTac_UnionsInsert_FailsWithoutUnions(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeMiniSetTheory()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = 500 * time.Millisecond // failure path: don't grind

	oldVocab := tactic.SortTermNames([]core.TermName{
		"set_member", "empty_set", "universe", "insert", "delete",
		"union", "intersection", "set_difference", "subset", "proper_subset",
		"disjoint", "image", "set_comprehension", "comprehension_spec",
	})

	var residuals []Prop
	n := CreateGoalStack(m.unionsInsertGoal())
	require.False(t, ApplySetTacMode(n, env, t.Context(), oldVocab, SetTacMode_SET_TAC_LEGACY, &residuals),
		"without big_union in the vocabulary the goal must not close")
	require.NotEmpty(t, residuals,
		"the failing close-or-fail step must surface its residual leaves")
	assert.LessOrEqual(t, len(residuals), maxSetTacResidualDiag)
}

// TestSetTac_CancelledCtxFailsFast pins the live-budget poll: an
// already-cancelled ctx makes the whole composite fail fast (expansion
// stops at the fixpoint loop head, refutes fail immediately on the same
// cancelled ctx) instead of grinding to the refuter timeout per leaf.
// Replay passes context.Background() and is unaffected by construction.
func TestSetTac_CancelledCtxFailsFast(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeMiniSetTheory()
	env := makeStepTestEnv()

	ctx, cancel := context.WithCancel(context.Background())
	cancel()

	start := time.Now()
	n := CreateGoalStack(m.unionsInsertGoal())
	require.False(t, ApplySetTac(n, env, ctx, DefaultSetTacConsts(), nil),
		"a cancelled ctx must fail the close-or-fail composite")
	assert.Less(t, time.Since(start), 2*time.Second,
		"cancelled ctx must abort well below the per-leaf refuter timeout budget")
}

// =======================================================================
// SimpWith
// =======================================================================

// TestApplySimpWithFlipped_DriverEndToEnd exercises the per-rule flip
// contract through the shared driver / proto / replay path:
//
//  1. Rule stored in NATURAL direction (∀x. f(x) = g(x)); goal exposes
//     only the RHS (g(a)). Without flip the rule can't fire.
//     ApplySimpWith returns false — the session is untouched.
//  2. Same rule with flips=[true]. ApplySimpWithFlipped fires the rule
//     right-to-left; the ministep records the natural-direction Prop in
//     SimpWithProto.rules[0] and true in SimpWithProto.rule_flip[0].
//  3. Serializing the recorded step and rebuilding the _SimpWithStep
//     from the proto round-trips the flip bit — the reconstructed
//     step.apply(goal) reproduces the identical rewrite.
//
// This is the prover-layer twin of TestSimpWith_Flip_EngineDispatch
// (engine layer); together they cover the full stack from LemmaWithSpec
// through to the driver-view rewrite.
func TestApplySimpWithFlipped_DriverEndToEnd(t *testing.T) {
	// Fixture: f, g : A → A; P : A → bool; a : A.
	// Natural rule ∀x:A. f(x) = g(x); goal P(g(a)).
	numT := core.TypeA()
	boolT := core.TypeBool()
	fnNum := core.MakeFun(numT, numT)
	pr := core.MakeFun(numT, boolT)

	f := core.Var("f", fnNum)
	g := core.Var("g", fnNum)
	P := core.Var("P", pr)
	a := core.Var("a", numT)
	x := core.Var("x", numT)

	// ∀x:num. f(x) = g(x)
	rule := core.MakeProp(
		ext.ForAll(x)(core.Eq(core.Apply(f, x), core.Apply(g, x))).Core(),
	)
	// ⊢ P(g(a))
	goal := core.MakeProp(core.Apply(P, core.Apply(g, a)))

	// (1) Control: no flip — the natural direction rewrite has no
	// redex in the goal's conclusion (there is no f(·) present).
	{
		n := CreateGoalStack(goal)
		ok := ApplySimpWith(n, []Prop{rule})
		assert.False(t, ok,
			"natural-direction rule must not fire on a goal that only exposes the RHS")
	}

	// (2) Actual: flip fires the rule as g(x) → f(x).
	n := CreateGoalStack(goal)
	require.True(t, ApplySimpWithFlipped(n, []Prop{rule}, []bool{true}),
		"flipped rule must fire on P(g(a))")

	leaves := n.UnsolvedLeaves()
	require.NotEmpty(t, leaves)
	// The rewritten residual is ⊢ P(f(a)) — the flipped rule fired
	// exactly once.
	residual := leaves[len(leaves)-1]
	expected := core.Apply(P, core.Apply(f, a))
	assert.True(t, residual.Goal.Conclusion().AlphaEquals(expected),
		"residual conclusion after flipped rewrite must be P(f(a)); got %v",
		residual.Goal.Conclusion())

	// (3) Serialize the recorded _SimpWithStep and confirm the proto
	// carries the natural-direction rule + [true] in rule_flip.
	pool := ext.NewPoolBuilder()
	step := _SimpWithStep{rules: []Prop{rule}, flips: []bool{true}}
	stepProto := step.proto(pool)
	sw, ok := stepProto.(*StepProto_SimpWith)
	require.True(t, ok)
	require.Len(t, sw.SimpWith.GetRules(), 1)
	require.Equal(t, []bool{true}, sw.SimpWith.GetRuleFlip(),
		"the flip bit must persist verbatim in SimpWithProto.rule_flip")

	// The recorded rule prop is the NATURAL direction — a rule-child
	// close-pass sees exactly the stated form (identical statement,
	// identical α-key).
	poolProto := pool.Pool()
	r := ext.NewPoolReader(poolProto, MockConstMetaService().LoadConstMeta)
	recordedRule, _ := r.Prop(sw.SimpWith.GetRules()[0])
	require.NotNil(t, recordedRule)
	assert.True(t, recordedRule.Conclusion().AlphaEquals(rule.Conclusion()),
		"recorded rule must be the natural direction, not the flipped form")

	// (4) Rebuild _SimpWithStep from the proto (the decode path used
	// by replay). The reconstructed step's apply reproduces the same
	// rewrite on a fresh goal-stack.
	rebuilt := _SimpWithStep{
		rules: []Prop{recordedRule},
		flips: append([]bool(nil), sw.SimpWith.GetRuleFlip()...),
	}
	n2 := CreateGoalStack(goal)
	require.True(t, n2.runStep(rebuilt),
		"replaying the recorded flipped SimpWith step must fire")
	leaves2 := n2.UnsolvedLeaves()
	require.NotEmpty(t, leaves2)
	assert.True(t, leaves2[len(leaves2)-1].Goal.Conclusion().AlphaEquals(expected),
		"replayed rewrite must produce the same residual as the live run")
}

// TestApplySimpWith_BackCompat_NoFlipSlice: the zero-flip form
// (ApplySimpWith with no flips slice) writes an EMPTY rule_flip on the
// wire — a snapshot without the flip field round-trips byte-for-byte to
// the same proto. Guards against an emit regression that would
// materialize a length-N all-false slice on every step.
func TestApplySimpWith_BackCompat_NoFlipSlice(t *testing.T) {
	numT := core.TypeA()
	boolT := core.TypeBool()
	fnNum := core.MakeFun(numT, numT)
	pr := core.MakeFun(numT, boolT)

	f := core.Var("f", fnNum)
	g := core.Var("g", fnNum)
	P := core.Var("P", pr)
	a := core.Var("a", numT)
	x := core.Var("x", numT)

	rule := core.MakeProp(
		ext.ForAll(x)(core.Eq(core.Apply(f, x), core.Apply(g, x))).Core(),
	)
	// Goal now has f(a) — the natural direction fires directly.
	goal := core.MakeProp(core.Apply(P, core.Apply(f, a)))

	n := CreateGoalStack(goal)
	require.True(t, ApplySimpWith(n, []Prop{rule}),
		"natural direction must fire on P(f(a))")

	// The recorded step's proto must carry an EMPTY rule_flip — no
	// false-slice materialized for the zero-flip case, so pre-flip
	// snapshots stay byte-stable on re-emit.
	step := _SimpWithStep{rules: []Prop{rule}} // no flips slice
	pool := ext.NewPoolBuilder()
	stepProto := step.proto(pool)
	sw := stepProto.(*StepProto_SimpWith)
	assert.Empty(t, sw.SimpWith.GetRuleFlip(),
		"back-compat: zero-flip step must NOT materialize a rule_flip slice on the wire")
}

// TestSimpWithExpandFlipped_RejectsNonEquation: flip=true on a fact rule
// (∀x. P(x) — no equation head after ∀-strip) returns nil at the driver
// level. This is the low-level backstop for the resolveSimpWithRules
// upfront validation — even if a caller ever hands the driver a
// flip=true on a non-equation, the session gets no rewrite and no crash.
func TestSimpWithExpandFlipped_RejectsNonEquation(t *testing.T) {
	numT := core.TypeA()
	boolT := core.TypeBool()
	pr := core.MakeFun(numT, boolT)
	P := core.Var("P", pr)
	a := core.Var("a", numT)
	x := core.Var("x", numT)

	// Fact rule ∀x. P(x) — no equation head.
	fact := core.MakeProp(ext.ForAll(x)(core.Apply(P, x)).Core())
	goal := core.MakeProp(core.Apply(P, a))

	n := CreateGoalStack(goal)
	assert.False(t, ApplySimpWithFlipped(n, []Prop{fact}, []bool{true}),
		"flip on a non-equation rule must fail cleanly (no progress, no panic)")
}

// =======================================================================
// PairedBeta
// =======================================================================

// TestPairedBetaStep_ProtoRoundTrip verifies the paired_beta composite
// (proto tag 53) survives serialization with its polymorphic source
// intact — the payload emit renders the step from. The source here
// only needs to be SOME prop (apply is not exercised): the wire
// contract is source-statement fidelity, not driver behavior.
func TestPairedBetaStep_ProtoRoundTrip(t *testing.T) {
	// Const-free source: the pool reader in this test carries no
	// const-meta loader (same convention as the sibling round-trip
	// tests), so the statement must be built from bare vars.
	P := ext.Var("P", core.TypeBool())
	source := core.MakeProp(P.Core())

	step := _PairedBetaStep{source: source}

	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	require.NotNil(t, p)

	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))

	got, _ := ext.NewPoolReader(pb.Pool(), nil).Prop(decoded.GetPairedBeta())
	require.NotNil(t, got, "round-trip should preserve the paired_beta arm")
	assert.True(t, got.AlphaEquals(source),
		"polymorphic source must survive round-trip")
}

// TestPairedBetaStep_RefusesSiteFreeGoal pins the driver's no-op
// contract: a goal without a paired-beta redex must refuse the step
// (nil SubGoals → runStep false), leaving the node untouched.
func TestPairedBetaStep_RefusesSiteFreeGoal(t *testing.T) {
	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	source := core.MakeProp(P.Core())
	goal := core.MakeProp(Q.Core())

	n := CreateGoalStack(goal)
	ok := n.runStep(_PairedBetaStep{source: source})
	assert.False(t, ok, "paired_beta must refuse a goal without a paired-beta site")
	assert.False(t, n.Proved())
}

// =======================================================================
// PairCollapse
// =======================================================================

// pairCollapseTestEnv is the synthetic pair setup shared by the
// PairCollapse tests: fst / snd / "," at the polymorphic pair type
// prod(A, B), with the projection rules as TestThms (acceptable
// inside _test.go only) in the usual orientation — atom on the
// left:
//
//	fstRule: ⊢ ∀y:B. ∀x:A. x = fst(,(x, y))
//	sndRule: ⊢ ∀y:B. ∀x:A. y = snd(,(x, y))
//
// Goals are posed at the concrete instance prod(ind, bool) so the
// per-site rewrite exercises the type-adaptation path (the same one
// the engine's ambient pass and every treal-shaped proof cross).
type pairCollapseTestEnv struct {
	ctx               *Script
	fstRule, sndRule  Prop
	fstC, sndC, pairC *ext.TermWrapper // concrete-instance consts
	c, d              *ext.TermWrapper // concrete pair components
}

func makePairCollapseTestEnv() *pairCollapseTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	pairAB := ext.MakeType("prod", TypeA, TypeB)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("fst", core.MakeFun(pairAB, TypeA)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("snd", core.MakeFun(pairAB, TypeB)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(",", core.MakeFun(TypeA, core.MakeFun(TypeB, pairAB))))

	// Polymorphic wrappers for the rule statements.
	fstP := ctx.Const("fst", core.MakeFun(pairAB, TypeA))
	sndP := ctx.Const("snd", core.MakeFun(pairAB, TypeB))
	pairP := ctx.Const(",", core.MakeFun(TypeA, core.MakeFun(TypeB, pairAB)))
	x := Var("x", TypeA)
	y := Var("y", TypeB)
	e := &pairCollapseTestEnv{ctx: ctx}
	e.fstRule = prop.WrapProp(core.TestThm(ext.ForAll(y)(ext.ForAll(x)(
		x.Eq(fstP.Apply(pairP.Apply(x, y)))))))
	e.sndRule = prop.WrapProp(core.TestThm(ext.ForAll(y)(ext.ForAll(x)(
		y.Eq(sndP.Apply(pairP.Apply(x, y)))))))

	// Concrete instance prod(ind, bool).
	pairCB := ext.MakeType("prod", TypeInd, core.TypeBool())
	e.fstC = ctx.Const("fst", core.MakeFun(pairCB, TypeInd))
	e.sndC = ctx.Const("snd", core.MakeFun(pairCB, core.TypeBool()))
	e.pairC = ctx.Const(",", core.MakeFun(TypeInd, core.MakeFun(core.TypeBool(), pairCB)))
	e.c = Var("c", TypeInd)
	e.d = Var("d", core.TypeBool())
	return e
}

// TestPairCollapse_CollapsesBothProjections: a goal with one fst and
// one snd redex over the same concrete pair literal reduces to the
// projection-free form; the rule-reproduction obligations are closed
// inside the Action (exactly one unsolved leaf remains, carrying the
// non-trivial residual).
//
//	f(fst((c,d)), snd((c,d))) ⇔ Q   —→   f(c, d) ⇔ Q
func TestPairCollapse_CollapsesBothProjections(t *testing.T) {
	e := makePairCollapseTestEnv()
	f := Var("f", core.MakeFun(TypeInd, core.MakeFun(core.TypeBool(), core.TypeBool())))
	Q := Var("Q", core.TypeBool())
	lit := e.pairC.Apply(e.c, e.d)

	sec := e.ctx.Section(prop.MakeProp(
		f.Apply(e.fstC.Apply(lit), e.sndC.Apply(lit)).Eq(Q)))
	sec.Do(PairCollapse(e.fstRule, e.sndRule))

	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1, "collapse must close every rule obligation itself")
	want := f.Apply(e.c, e.d).Eq(Q)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want),
		"residual is not the projection-free goal:\n%s", prop.PrintProp(leaves[0].Goal))
	require.Equal(t, PairProjNone, FindPairProjectionSite(leaves[0].Goal, true, true),
		"residual still contains a projection site")
}

// TestPairCollapse_ReflexiveResidualCloses: when the projection-free
// residual is reflexive, the rewrite's own simplification discharges
// it — the collapse closes the whole section (obligations included).
//
//	f(fst((c,d)), snd((c,d))) ⇔ f(c, d)   —→   proved
func TestPairCollapse_ReflexiveResidualCloses(t *testing.T) {
	e := makePairCollapseTestEnv()
	f := Var("f", core.MakeFun(TypeInd, core.MakeFun(core.TypeBool(), core.TypeBool())))
	lit := e.pairC.Apply(e.c, e.d)

	sec := e.ctx.Section(prop.MakeProp(
		f.Apply(e.fstC.Apply(lit), e.sndC.Apply(lit)).Eq(f.Apply(e.c, e.d))))
	sec.Do(PairCollapse(e.fstRule, e.sndRule))

	require.Empty(t, sec.UnsolvedLeaves())
	sec.Qed()
	require.True(t, sec.Proved())
}

// TestPairCollapse_NestedSite: a projection redex buried under another
// application is still found and collapsed (the walk descends through
// App constructors, mirroring the engine scanner).
//
//	g(h(fst((c,d)))) ⇔ Q
func TestPairCollapse_NestedSite(t *testing.T) {
	e := makePairCollapseTestEnv()
	h := Var("h", core.MakeFun(TypeInd, TypeInd))
	g := Var("g", core.MakeFun(TypeInd, core.TypeBool()))
	Q := Var("Q", core.TypeBool())
	lit := e.pairC.Apply(e.c, e.d)

	sec := e.ctx.Section(prop.MakeProp(
		g.Apply(h.Apply(e.fstC.Apply(lit))).Eq(Q)))
	sec.Do(PairCollapse(e.fstRule, e.sndRule))

	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	want := g.Apply(h.Apply(e.c)).Eq(Q)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want),
		"residual is not the projection-free goal:\n%s", prop.PrintProp(leaves[0].Goal))
}

// TestPairCollapse_SwappedArgsPanics: the construction-time
// swapped-argument guard fires before any goal work.
func TestPairCollapse_SwappedArgsPanics(t *testing.T) {
	e := makePairCollapseTestEnv()
	require.Panics(t, func() { PairCollapse(e.sndRule, e.fstRule) })
	require.Panics(t, func() { PairCollapse(nil, e.sndRule) })
}

// TestPairCollapse_NoSitePanics: applying the collapse to a goal with
// no literal-pair projection redex is an authoring error and panics
// loudly rather than silently no-opping.
func TestPairCollapse_NoSitePanics(t *testing.T) {
	e := makePairCollapseTestEnv()
	P := Var("P", core.TypeBool())
	sec := e.ctx.Section(prop.MakeProp(P.Imply(P)))
	require.Panics(t, func() { sec.Do(PairCollapse(e.fstRule, e.sndRule)) })
}

// TestFindPairProjectionSite_WantFilter: an unwanted site does not
// stop the walk — a wanted site nested deeper is still found (the
// engine pass's partial-cache semantics).
func TestFindPairProjectionSite_WantFilter(t *testing.T) {
	e := makePairCollapseTestEnv()
	// snd((fst((c,d)) , d)) — outer site snd, inner site fst (inside
	// the outer pair literal's first component).
	inner := e.fstC.Apply(e.pairC.Apply(e.c, e.d))
	outer := e.sndC.Apply(e.pairC.Apply(inner, e.d))
	g := Var("g", core.MakeFun(core.TypeBool(), core.TypeBool()))
	p := prop.MakeProp(g.Apply(outer).Eq(g.Apply(e.d)))

	require.Equal(t, PairProjSND, FindPairProjectionSite(p, true, true))
	require.Equal(t, PairProjFST, FindPairProjectionSite(p, true, false),
		"with snd unwanted the walk must continue into the pair literal and find fst")
	require.Equal(t, PairProjNone, FindPairProjectionSite(p, false, false))
}
