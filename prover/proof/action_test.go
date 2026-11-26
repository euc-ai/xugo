package proof

import (
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

// makeStepTestEnv builds a minimal ProverEnv suitable for exercising
// the Step API surface on synthetic goal stacks (no library thms; the
// CNF refuter is available but not relied on by these tests).
func makeStepTestEnv() *ProverEnv {
	var cnfNormalizationCache utils.Map[core.TermKey, Prop]
	return &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     3 * time.Second,
		CnfNormalizationCache: &cnfNormalizationCache,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}
}

// TestStep_InterfaceSatisfaction is a compile-time check that every
// existing Step / Macro constructor's return value satisfies the
// umbrella Action interface. Catches regressions where someone adds a
// new concrete type to step.go / macro.go without the corresponding
// applyAction method.
//
// One representative per concrete type — the uniformity of applyMSStep
// / applyMacro means a single sample per category is sufficient
// to catch interface drift.
func TestStep_InterfaceSatisfaction(t *testing.T) {
	// MiniStep — parameterless
	var _ Action = Basic()
	var _ Action = TrivialSimplify()
	var _ Action = TrivialNormalized()
	var _ Action = CondRewrite()
	var _ Action = RewriteAuto()
	var _ Action = SplitConj()
	var _ Action = SplitDisjCases()
	var _ Action = StripImp()
	var _ Action = StripQuant()
	var _ Action = StripQuant1()
	var _ Action = SplitIffCases()
	var _ Action = SplitHypIffCases()
	var _ Action = SplitHypImply()
	var _ Action = Assumption()
	var _ Action = Refl()
	var _ Action = Left()
	var _ Action = Right()
	var _ Action = Funext()
	var _ Action = ByContra()
	var _ Action = Symm()
	var _ Action = Congr()

	// MiniStep — parameterized
	x := Var("x", TypeA)
	var _ Action = Witness(x)
	var _ Action = Instantiate(x)
	var _ Action = SpecializeKeep(InstHyp(0, x))
	var _ Action = Subst(0)
	var _ Action = Trans(x)
	var _ Action = Denote(8)
	var _ Action = HilbertDenote()

	// MiniStep — env-touching. Constructed via raw struct literals
	// rather than the Script helpers (the helpers panic on missing
	// ProofService entries when run against a MockConstMetaService).
	var _ Action = _CNFRefute{}
	var _ Action = _InductionStep{}

	// MiniStep — Prop / Term carrying
	xb := Var("xb", TypeBool)
	p := MakeProp(xb)
	var _ Action = Lemma(p)
	var _ Action = LeanRw(p)
	var _ Action = TypeInst(p)
	var _ Action = CiteKnown(p)
	var _ Action = ByCaseStep(xb)
	var _ Action = AssertStep(p)
	// AxiomDefStep needs a ConstTerm; construct one inline.
	var _ Action = _AxiomDefStep{}

	// Macros — the one that remains (the `auto` closer); raw struct
	// literal to avoid Script-helper env panics.
	var _ Action = AutoExpand{}

	// Combinators / fused-idiom Step constructors
	var _ Action = Chain(Refl(), StripQuant())
	var _ Action = Chain()
	var _ Action = UseLemma(p)
	var _ Action = UseLemma(ThmCert{})
	var _ Action = UseLemma((*GoalStackNode)(nil))
}

// TestStep_ChainOrderingPreserved verifies that Chain runs its child
// Steps in order against the same section root.
//
// The test injects a sentinel Step that records each invocation;
// after running a 4-step Chain we check the captured sequence
// matches the input order. Uses a manually-built GoalStackNode (not
// Prove) so the test bypasses Normalize / ClaimProved and focuses
// purely on Step dispatch.
func TestStep_ChainOrderingPreserved(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	root := &GoalStackNode{Goal: MakeProp(Var("dummy", TypeBool))}

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	Chain(mk(1), mk(2), mk(3), mk(4)).applyAction(ctx, root)

	assert.Equal(t, []int{1, 2, 3, 4}, trace)
}

// TestCloseIfOpen covers both directions of the ladder terminator:
// it runs its action while a leaf is open, and is a no-op once the
// section is closed. The second half is the point of the combinator —
// a ladder whose lower cite already closed the goal must not go on to
// emit a refutation, which is what the retired hand-written Close flag
// predicted per member.
func TestCloseIfOpen(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	p := Var("p", TypeBool)

	t.Run("runs while a leaf is open", func(t *testing.T) {
		var trace []int
		root := &GoalStackNode{Goal: MakeProp(p)}
		CloseIfOpen(_RecordingAction{id: 1, trace: &trace}).applyAction(ctx, root)
		assert.Equal(t, []int{1}, trace)
	})

	t.Run("no-op once the goal is closed", func(t *testing.T) {
		var trace []int
		root := ctx.Section(MakeProp(p, p))
		ctx.Do(root, CiteKnown(core.TestThm(p, p)))
		assert.True(t, root.Proved())

		CloseIfOpen(_RecordingAction{id: 1, trace: &trace}).applyAction(ctx, root)
		assert.Empty(t, trace)
	})
}

func TestScriptDoCiteUsesExplicitTheoremBeforeCache(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	r := Var("r", TypeBool)

	section := ctx.Section(MakeProp(q, p, r))
	closer := core.TestThm(q, p)
	assert.False(t, TryMatchKnownThm(ctx.LocalThmCache, section))
	assert.False(t, TryMatchKnownThm(&ctx.Env.ThmCache, section))

	ctx.Do(section, CiteKnown(closer))
	section.Qed()

	assert.True(t, section.Proved())
}

// _RecordingAction is a test-only Step that appends its id to a shared
// trace slice on each invocation. Used to verify Chain ordering
// without coupling to any specific ministep / action body.
type _RecordingAction struct {
	id    int
	trace *[]int
}

func (r _RecordingAction) applyAction(s *Script, root *GoalStackNode) {
	*r.trace = append(*r.trace, r.id)
}

// TestStep_UseLemmaTargetDispatch verifies that UseLemma's runtime type
// switch correctly resolves Thm, *GoalStackNode (with a proved
// thm), and Prop arguments to their underlying Prop. Defers actual
// lemma application — we never call applyAction, just constructor +
// type-switch. ApplyStep dispatch is covered by Chain test above.
func TestStep_UseLemmaTargetDispatch(t *testing.T) {
	// Thm path — construct a synthetic proved thm.
	x := Var("x", TypeBool)
	thm := core.TestThm(x.Core(), x.Core())
	useFromThm, ok := UseLemma(thm).(_UseLemmaAction)
	assert.True(t, ok)
	assert.True(t, any(thm) == any(useFromThm.target))

	// *GoalStackNode path — construct a node and inject a proved thm.
	node := &GoalStackNode{Goal: MakeProp(x)}
	node.provedThm = thm
	useFromNode, ok := UseLemma(node).(_UseLemmaAction)
	assert.True(t, ok)
	assert.Same(t, node, useFromNode.target)

	// Prop path — pass a Prop directly.
	p := MakeProp(x)
	useFromProp, ok := UseLemma(p).(_UseLemmaAction)
	assert.True(t, ok)
	// Prop is wrapped via PropWrapper; the underlying target identity
	// match isn't meaningful, just that UseLemma accepted it.
	assert.NotNil(t, useFromProp.target)
}

// TestStep_ChainEmptyIsNoop verifies that an empty Chain is a safe
// no-op when applied — useful for emit-generated code that may emit
// Chain() with zero steps in degenerate corpus cases.
func TestStep_ChainEmptyIsNoop(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	root := &GoalStackNode{Goal: MakeProp(Var("dummy", TypeBool))}

	// Just verify no panic.
	Chain().applyAction(ctx, root)
}

// TestStep_CaseDispatchByCaseStep exercises the runtime Case dispatch
// path: a ByCaseStep with two Case bodies should route each body to
// the matching child after runStep produces children.
//
// Goal: `P(x) ∨ Q(x) ⊢ R(x)`. ByCaseStep on `P(x)` produces:
//
//	child[0]:  P(x), P(x) ∨ Q(x) ⊢ R(x)   (case "pos")
//	child[1]: ¬P(x), P(x) ∨ Q(x) ⊢ R(x)   (case "neg")
//
// Each Case body is a single _RecordingStep that appends its id to a
// shared trace, so we can verify positional dispatch by checking
// the trace order.
func TestStep_CaseDispatchByCaseStep(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	ctx.Do(root, ByCaseStep(P.Apply(x).Core(),
		MakeCase("pos", mk(101)),
		MakeCase("neg", mk(202)),
	))

	assert.Equal(t, []int{101, 202}, trace)
	// Verify dispatch happened on the two children, not the root.
	assert.Equal(t, 2, len(root.children))
}

// TestStep_CaseDispatchEmptyLegacy verifies that the legacy form
// (variadic Case unused) preserves byte-for-byte behavior: the
// ministep applies, children are produced, but no dispatch runs.
func TestStep_CaseDispatchEmptyLegacy(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	// No Case args — same as the legacy `ByCaseStep(t)` call shape.
	ctx.Do(root, ByCaseStep(P.Apply(x).Core()))

	// Children exist but remain unproved.
	assert.Equal(t, 2, len(root.children))
	assert.False(t, root.children[0].Proved())
	assert.False(t, root.children[1].Proved())
}

// TestStep_CaseDispatchArityMismatch panics when the Case count
// doesn't match the kernel-produced subgoal count.
func TestStep_CaseDispatchArityMismatch(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic on Case-count != subgoal-count")
		}
	}()

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	// Only 1 Case for a 2-subgoal split → must panic.
	ctx.Do(root, ByCaseStep(P.Apply(x).Core(), MakeCase("only", mk(1))))
}

// TestStep_WithHypBindsMatchingHyp verifies WithHyp scans the leaf's
// hyp list, matches via predicate, and binds the resulting Hyp
// handle to a closure-local Go variable. The captured handle's Term
// must alpha-equal the actual hyp.
func TestStep_WithHypBindsMatchingHyp(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	// Goal: P(x), Q(x) ⊢ R(x). Two hyps, body picks Q(x).
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x), Q.Apply(x)))

	var captured Hyp
	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	step := WithHyp(
		func(h Term) bool { return h.HasFreeName(core.TermName("Q")) },
		"hQ",
		func(h Hyp) Action {
			captured = h
			return mk(42)
		},
	)
	step.applyAction(ctx, root)

	// Body ran exactly once.
	assert.Equal(t, []int{42}, trace)
	// Handle carries the right hyp.
	assert.Equal(t, "hQ", captured.Name)
	assert.True(t, captured.Term.AlphaEquals(Q.Apply(x).Core()))
}

// TestStep_WithHypNoMatchPanics covers the failure-mode contract:
// no matching hyp → panic with a diagnostic mentioning the name.
func TestStep_WithHypNoMatchPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x)))

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic when no hyp matches predicate")
		}
	}()

	WithHyp(
		func(h Term) bool { return h.HasFreeName(core.TermName("Z")) },
		"hZ",
		func(h Hyp) Action { return _RecordingAction{} },
	).applyAction(ctx, root)
}

// TestStep_WithIHBindsLastHyp verifies WithIH picks the leaf's
// last hyp — the typical position for an induction hypothesis just
// introduced by Induct's step branch.
func TestStep_WithIHBindsLastHyp(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	// Two hyps; WithIH must pick the last one (Q here, since MakeProp
	// sorts hyps and Q's term comes after P alphabetically).
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x), Q.Apply(x)))

	var captured Hyp
	step := WithIH("ih", func(ih Hyp) Action {
		captured = ih
		return _RecordingAction{id: 1, trace: new([]int)}
	})
	step.applyAction(ctx, root)

	assert.Equal(t, "ih", captured.Name)
	// MakeProp sort order: hyps sorted by Term.Compare. Either P or Q
	// could be "last"; the test only asserts the handle holds SOME
	// alpha-equal hyp from the leaf, not which one.
	leafHyps := root.Goal.Hyps()
	last := leafHyps[len(leafHyps)-1]
	assert.True(t, captured.Term.AlphaEquals(last))
}

// TestStep_WithIHNoHypPanics covers the "called on a hyp-free goal"
// contract.
func TestStep_WithIHNoHypPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	root := &GoalStackNode{Goal: MakeProp(Var("x", TypeBool))}

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic on WithIH against hyp-free goal")
		}
	}()

	WithIH("ih", func(ih Hyp) Action { return _RecordingAction{} }).applyAction(ctx, root)
}

// ---------------------------------------------------------------------------
// Expect / Finally — structured fan-out combinators
// ---------------------------------------------------------------------------

// TestStep_ExpectBindsAutoSplitLeaves: Expect around a bare (case-less)
// splitting ministep dispatches each Case body to the corresponding
// unsolved leaf positionally — the same routing the ministep's native
// Case form would give, but available for actions that take no Case
// arguments.
func TestStep_ExpectBindsAutoSplitLeaves(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	Expect(ByCaseStep(P.Apply(x).Core()),
		MakeCase("pos", mk(101)),
		MakeCase("neg", mk(202)),
	).applyAction(ctx, root)

	assert.Equal(t, []int{101, 202}, trace)
	assert.Equal(t, 2, len(root.children))
}

// TestStep_ExpectBindsDeepLeaves: the fan-out binds to the subtree's
// unsolved LEAVES in preorder, not to direct children — a chained pair
// of splits leaves three goals at two different depths.
func TestStep_ExpectBindsDeepLeaves(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	Expect(
		Chain(
			ByCaseStep(P.Apply(x).Core()), // splits the section root
			ByCaseStep(Q.Apply(x).Core()), // splits the first (pos) child
		),
		MakeCase("pos.pos", mk(1)),
		MakeCase("pos.neg", mk(2)),
		MakeCase("neg", mk(3)),
	).applyAction(ctx, root)

	assert.Equal(t, []int{1, 2, 3}, trace)
	// Shape: root → [pos, neg], pos → [pos.pos, pos.neg].
	assert.Equal(t, 2, len(root.children))
	assert.Equal(t, 2, len(root.children[0].children))
	assert.Equal(t, 0, len(root.children[1].children))
}

// TestStep_ExpectCountMismatchPanics: fewer Cases than leaves is a
// structural error, reported at the Expect site.
func TestStep_ExpectCountMismatchPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic on Case-count != unsolved-leaf-count")
		}
	}()

	var trace []int
	mk := func(id int) Action { return _RecordingAction{id: id, trace: &trace} }

	Expect(ByCaseStep(P.Apply(x).Core()), MakeCase("only", mk(1))).applyAction(ctx, root)
}

// TestStep_ExpectZeroCasesAssertsClosure: Expect(action) with no cases
// asserts the action fully closes the leaf it runs on — pass when it
// does, panic when goals remain.
func TestStep_ExpectZeroCasesAssertsClosure(t *testing.T) {
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Closing action: Assumption on hyp-matching goal — no panic.
	ctx := NewScript(makeStepTestEnv())
	closable := ctx.Section(MakeProp(P.Apply(x), P.Apply(x)))
	Expect(Assumption()).applyAction(ctx, closable)
	assert.True(t, closable.Proved())

	// Splitting action leaves 2 goals ≠ 0 cases — panic.
	ctx2 := NewScript(makeStepTestEnv())
	R := Var("R", MakeFun(TypeA, TypeBool))
	splitting := ctx2.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))
	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic: action left 2 unsolved leaves with 0 cases")
		}
	}()
	Expect(ByCaseStep(P.Apply(x).Core())).applyAction(ctx2, splitting)
}

// TestStep_FinallyBroadcastsAndCloses: Finally applies the action to
// every remaining unsolved leaf (leftmost-first) and the section ends
// proved.
func TestStep_FinallyBroadcastsAndCloses(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	disj := P.Apply(x).Or(Q.Apply(x))
	root := ctx.Section(MakeProp(disj, disj))

	// Case-less split: both branches keep the disj hyp, each closable
	// by Assumption.
	ctx.Do(root, ByCaseStep(P.Apply(x).Core()))
	assert.Equal(t, 2, len(root.UnsolvedLeaves()))

	Finally(Assumption()).applyAction(ctx, root)
	assert.True(t, root.Proved())
}

// TestStep_FinallyNonClosingPanics: a broadcast action that leaves its
// leaf open violates Finally's terminator contract.
func TestStep_FinallyNonClosingPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(R.Apply(x), P.Apply(x).Or(Q.Apply(x))))
	ctx.Do(root, ByCaseStep(P.Apply(x).Core()))

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic: broadcast action did not close its leaf")
		}
	}()

	var trace []int
	Finally(_RecordingAction{id: 1, trace: &trace}).applyAction(ctx, root)
}

// TestStep_FinallyNoLeavesPanics: Finally on an already-proved focus is
// a dead step, reported like an extra Chain entry.
func TestStep_FinallyNoLeavesPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(P.Apply(x), P.Apply(x)))
	ctx.Do(root, Assumption())
	assert.True(t, root.Proved())

	defer func() {
		if r := recover(); r == nil {
			t.Fatalf("expected panic: no unsolved leaves remaining")
		}
	}()
	Finally(Assumption()).applyAction(ctx, root)
}

// ---------------------------------------------------------------------------
// Deduce / Have / Show — sequential-fact combinators
// ---------------------------------------------------------------------------

// assertSameGoalTree walks two goal-stack subtrees and requires the
// same shape with alpha-equal goals at every node — the Deduce desugar
// identity (same kernel steps on the same goals ⇒ same tree ⇒ same
// CNF goal-key trajectory).
func assertSameGoalTree(t *testing.T, a, b *GoalStackNode) {
	t.Helper()
	assert.True(t, a.Goal.AlphaEquals(b.Goal),
		"goal mismatch:\n  a: %v\n  b: %v", a.Goal, b.Goal)
	assert.Equal(t, len(a.children), len(b.children))
	if len(a.children) == len(b.children) {
		for i := range a.children {
			assertSameGoalTree(t, a.children[i], b.children[i])
		}
	}
}

// TestStep_DeduceSequenceClosesAndMatchesHandwrittenTree: the happy
// path — interstitial action + two Haves + Show closes the section,
// and the resulting goal tree is node-for-node identical to the
// handwritten nested-AssertStep staircase.
func TestStep_DeduceSequenceClosesAndMatchesHandwrittenTree(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	// Claims must be fresh facts (AssertTactic refuses a claim that is
	// already a hyp or the conclusion) — two Refl-closable equations.
	claimX := MakeProp(x.Eq(x))
	claimY := MakeProp(y.Eq(y))

	// Deduce form.
	ctx := NewScript(makeStepTestEnv())
	root := ctx.Section(MakeProp(Q.Apply(x), P.Apply(x), Q.Apply(x)))
	var trace []int
	Deduce(
		_RecordingAction{id: 1, trace: &trace},
		Have("x equals itself", claimX, Refl()),
		Have("y equals itself", claimY, Refl()),
		Show("the goal is exactly the resident Q", Assumption()),
	).applyAction(ctx, root)
	assert.True(t, root.Proved())
	assert.Equal(t, []int{1}, trace)

	// Handwritten nested-AssertStep staircase of the same argument.
	ctx2 := NewScript(makeStepTestEnv())
	root2 := ctx2.Section(MakeProp(Q.Apply(x), P.Apply(x), Q.Apply(x)))
	Chain(
		_RecordingAction{id: 1, trace: new([]int)},
		AssertStep(claimX,
			MakeCase("claim", Refl()),
			MakeCase("after",
				AssertStep(claimY,
					MakeCase("claim", Refl()),
					MakeCase("after", Assumption())))),
	).applyAction(ctx2, root2)
	assert.True(t, root2.Proved())

	assertSameGoalTree(t, root, root2)
}

// TestStep_DeduceUnclosedHavePanics: a Have whose proof leaves the
// claim child open violates the eager-close contract — reported at the
// Have with its label, not at Qed.
func TestStep_DeduceUnclosedHavePanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(Q.Apply(x), Q.Apply(x)))

	var trace []int
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("expected panic: Have proof left its claim open")
		}
		msg, _ := r.(string)
		assert.Contains(t, msg, `Have("unclosed")`)
	}()
	Deduce(
		Have("unclosed", MakeProp(x.Eq(x)), _RecordingAction{id: 1, trace: &trace}),
		Show("never reached", Assumption()),
	).applyAction(ctx, root)
}

// TestStep_DeduceLinearityPanics: a non-final bare item that fans out
// (case-less ByCase leaves two goals) breaks the exactly-one-residual
// contract.
func TestStep_DeduceLinearityPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	disj := P.Apply(x).Or(Q.Apply(x))
	root := ctx.Section(MakeProp(disj, disj))

	assert.Panics(t, func() {
		Deduce(
			ByCaseStep(P.Apply(x).Core()),
			Show("never reached", Assumption()),
		).applyAction(ctx, root)
	})
}

// TestStep_DeduceTerminalContractPanics: Show is a
// terminal, and a block may not end on an open residual.
func TestStep_DeduceTerminalContractPanics(t *testing.T) {
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// Show before the end.
	ctx := NewScript(makeStepTestEnv())
	root := ctx.Section(MakeProp(P.Apply(x), P.Apply(x)))
	assert.Panics(t, func() {
		Deduce(
			Show("early", Assumption()),
			_RecordingAction{id: 1, trace: new([]int)},
		).applyAction(ctx, root)
	})

	// Final item is a Have — residual left open.
	ctx2 := NewScript(makeStepTestEnv())
	root2 := ctx2.Section(MakeProp(P.Apply(x), P.Apply(x)))
	assert.Panics(t, func() {
		Deduce(
			Have("x equals itself", MakeProp(x.Eq(x)), Refl()),
		).applyAction(ctx2, root2)
	})
}

// TestStep_HaveShowOutsideDeducePanic: Have / Show are Deduce items;
// free-standing application (e.g. inside a plain Chain) is refused at
// run time with a message naming the fix.
func TestStep_HaveShowOutsideDeducePanic(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	root := ctx.Section(MakeProp(P.Apply(x), P.Apply(x)))

	assert.Panics(t, func() {
		Have("stray", MakeProp(P.Apply(x)), Assumption()).applyAction(ctx, root)
	})
	assert.Panics(t, func() {
		Show("stray", Assumption()).applyAction(ctx, root)
	})
}
