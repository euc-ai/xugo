package proof

import (
	"context"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// TestTrivialNormalizedStep_Closes verifies that _TrivialNormalizedStep
// successfully closes any goal whose Normalize-canonical form has conclusion
// ⊤. The example shapes below are taken from ext/prop/normalize_test.go where
// they're demonstrated to normalize to a hyp-free `⊢ ⊤`:
//
//   - x, y ⊢ x ∧ y                (hypotheses absorbed into conclusion)
//   - ⊢ x ∨ ¬x                    (excluded middle)
//   - x, ¬x ⊢ y                   (hypotheses contradict each other)
//   - x ∧ y ⊢ x ∨ y               (entailment via absorption)
//   - ⊢ ⊤                         (already trivial)
func TestTrivialNormalizedStep_Closes(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)

	// Use MakeProp (not TestThm): runStep rejects already-proved goals.
	cases := []struct {
		name string
		goal Prop
	}{
		{"absorbed-hyps", core.MakeProp(x.And(y), x, y)},
		{"excluded-middle", core.MakeProp(x.Or(Not(x)))},
		{"contradiction", core.MakeProp(y, x, Not(x))},
		{"absorption", core.MakeProp(x.Or(y), x.And(y))},
		{"already-true", core.MakeProp(T)},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// Sanity check: the normalize step really does collapse this goal
			// to ⊢ ⊤. If a future change to Normalize stops doing so, the
			// test premise no longer holds and we'd want to know.
			normalized, _ := prop.Normalize(tc.goal)
			require.True(t, normalized.Conclusion().Equals(T),
				"premise: Normalize(goal).Conclusion() should be ⊤")
			require.Equal(t, 0, normalized.NumHyps(),
				"premise: Normalize(goal) should have 0 hyps once concl is ⊤")

			n := CreateGoalStack(tc.goal)
			ok := n.runStep(_TrivialNormalizedStep{})
			require.True(t, ok, "_TrivialNormalizedStep should succeed")
			require.True(t, n.Proved(), "node should be proved after the step")

			thm := n.ProvedThm()
			require.False(t, thm.IsZero())
			assert.True(t, IsStronger(thm, tc.goal),
				"produced thm must be stronger than the original goal")
		})
	}
}

// TestTrivialNormalizedStep_Rejects verifies the step refuses goals that do
// NOT normalize to ⊤. Non-trivial goals must fall through, allowing other
// tactics (or the cache lookup) to handle them.
func TestTrivialNormalizedStep_Rejects(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)

	// ⊢ x ∨ y normalizes to a non-⊤ disjunction (it's not a tautology).
	goal := core.MakeProp(x.Or(y))
	normalized, _ := prop.Normalize(goal)
	require.False(t, normalized.Conclusion().Equals(T),
		"premise: this goal must NOT normalize to ⊤")

	n := CreateGoalStack(goal)
	ok := n.runStep(_TrivialNormalizedStep{})
	assert.False(t, ok, "_TrivialNormalizedStep should refuse non-trivial goals")
	assert.False(t, n.Proved(), "node should remain unproved after a refused step")
}

// TestTrivialNormalizedStep_ProtoRoundTrip mirrors the structural-tactic
// round-trip test: the ministep must serialize and survive
// marshal/unmarshal on its own oneof arm.
func TestTrivialNormalizedStep_ProtoRoundTrip(t *testing.T) {
	step := _TrivialNormalizedStep{}

	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	require.NotNil(t, p)

	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))

	assert.NotNil(t, decoded.GetTrivialNormalized(), "round-trip should preserve the oneof arm")
}

// TestCongrArgStep_ProtoRoundTrip verifies the parameterized congr_arg
// ministep applies and survives serialization with its function term
// and hyp index intact.
func TestCongrArgStep_ProtoRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	Q := Var("Q", TypeBool)
	goal := core.MakeProp(Q.Core(), core.Eq(a.Core(), b.Core()))

	step := _CongrArgStep{fn: f.Core(), hypIndex: 0}

	// (a) record: apply the original step.
	nOrig := CreateGoalStack(goal)
	require.True(t, nOrig.runStep(step), "original congr_arg should apply")

	// (b) serialize → deserialize.
	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	payload := decoded.GetCongrArg()
	require.NotNil(t, payload)
	assert.Equal(t, int32(0), payload.GetHypIndex(), "hyp_index must survive round-trip")
	assert.True(t, ext.NewPoolReader(pb.Pool(), nil).Term(payload.GetFunction()).AlphaEquals(f.Core()),
		"function term must survive round-trip")
}

// TestCongrFunStep_ProtoRoundTrip is the dual of the congr_arg round-trip.
func TestCongrFunStep_ProtoRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	x := Var("x", TypeA)
	Q := Var("Q", TypeBool)
	goal := core.MakeProp(Q.Core(), core.Eq(f.Core(), g.Core()))

	step := _CongrFunStep{arg: x.Core(), hypIndex: 0}

	nOrig := CreateGoalStack(goal)
	require.True(t, nOrig.runStep(step), "original congr_fun should apply")

	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	payload := decoded.GetCongrFun()
	require.NotNil(t, payload)
	assert.Equal(t, int32(0), payload.GetHypIndex(), "hyp_index must survive round-trip")
	assert.True(t, ext.NewPoolReader(pb.Pool(), nil).Term(payload.GetArgument()).AlphaEquals(x.Core()),
		"argument term must survive round-trip")
}

// TestRwStep_ProtoRoundTrip verifies the parameterized rw ministep
// applies and survives serialization with its hyp index and flip flag
// intact. Runs both directions; the flipped case exercises the
// EqSym-discharge cut.
func TestRwStep_ProtoRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", core.MakeFun(TypeA, TypeA))
	P := Var("P", core.MakeFun(TypeA, TypeBool))
	Q := Var("Q", core.MakeFun(TypeA, TypeBool))

	for _, flip := range []bool{false, true} {
		// flip=false: rewrite f(m)→d across hyp P(f(m)) and concl Q(f(m)).
		// flip=true: rewrite d→f(m) across hyp P(d) and concl Q(d).
		eq := core.Eq(f.Apply(m).Core(), d.Core())
		concl, otherHyp := Q.Apply(f.Apply(m).Core()).Core(), P.Apply(f.Apply(m).Core()).Core()
		if flip {
			concl, otherHyp = Q.Apply(d).Core(), P.Apply(d).Core()
		}
		goal := core.MakeProp(concl, eq, otherHyp)
		// MakeProp normalization may reorder hyps — locate the equality.
		hypIdx := -1
		for i := range goal.NumHyps() {
			if goal.Hyp(i).Equals(eq) {
				hypIdx = i
			}
		}
		require.NotEqual(t, -1, hypIdx)

		step := _RwStep{hypIndex: hypIdx, flip: flip}

		// (a) record: apply the original step.
		nOrig := CreateGoalStack(goal)
		require.True(t, nOrig.runStep(step), "original rw (flip=%v) should apply", flip)

		// (b) serialize → deserialize.
		pb := ext.NewPoolBuilder()
		var p isStepProto_Step
		require.NotPanics(t, func() { p = step.proto(pb) })
		bytes, err := proto.Marshal(&StepProto{Step: p})
		require.NoError(t, err)
		var decoded StepProto
		require.NoError(t, proto.Unmarshal(bytes, &decoded))
		payload := decoded.GetRw()
		require.NotNil(t, payload)
		assert.Equal(t, int32(hypIdx), payload.GetHypIndex(), "hyp_index must survive round-trip")
		assert.Equal(t, flip, payload.GetFlip(), "flip must survive round-trip")
	}
}

// TestClearHypsStep_ProtoRoundTrip verifies the batch clear ministep
// survives serialization with its index set intact, and pins the
// one-step shape: a single child whose hyp list lost exactly the dropped
// set. Invalid index sets are clean no-ops.
func TestClearHypsStep_ProtoRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", core.MakeFun(TypeA, TypeBool))
	j1 := Var("j1", TypeBool)
	j2 := Var("j2", TypeBool)
	j3 := Var("j3", TypeBool)

	// Goal: j1, j2, j3, P(x) ⊢ P(x); drop the three junk hyps in one step.
	goal := core.MakeProp(P.Apply(x).Core(), j1.Core(), j2.Core(), j3.Core(), P.Apply(x).Core())
	var drops []int
	for i := range goal.NumHyps() {
		if !goal.Hyp(i).Equals(P.Apply(x).Core()) {
			drops = append(drops, i)
		}
	}
	require.Len(t, drops, 3)

	step := _ClearHypsStep{hypIndices: drops}

	// (a) record: apply the original step — ONE child, junk gone.
	nOrig := CreateGoalStack(goal)
	require.True(t, nOrig.runStep(step))
	require.Len(t, nOrig.UnsolvedLeaves(), 1)
	child := nOrig.UnsolvedLeaves()[0].Goal
	assert.Equal(t, 1, child.NumHyps())

	// (b) serialize → deserialize.
	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	wantIndices := make([]int32, len(drops))
	for i, d := range drops {
		wantIndices[i] = int32(d)
	}
	assert.Equal(t, wantIndices, decoded.GetClearHyps().GetHypIndices(), "index set must survive round-trip")

	// (c) invalid index sets are clean no-ops.
	for _, bad := range [][]int{{}, {0, 0}, {0, 99}, {-1}} {
		n := CreateGoalStack(goal)
		assert.False(t, n.runStep(_ClearHypsStep{hypIndices: bad}), "bad=%v", bad)
	}
}

// Regression coverage for def_expand / lean_rw of a `const = λ...`
// definition. mk_pair is:
//
//	the definition `mk_pair (x:A) (y:B) = \a b. (a=x) /\ (b=y)`
//	  => def thm `mk_pair = \x y a b. (a=x) /\ (b=y)` (: A->B->A->B->bool)
//
// Pair-foundation goals often carry mk_pair(...) buried inside `⇔` chains.
// def_expand must unfold those occurrences whether they appear at top-level,
// under boolean structure, under binders, or inside ordinary applications.
func newMkPairConst() (mkp *ext.TermWrapper) {
	A := ext.TypeA
	B := ext.TypeB
	x := ext.Var("x", A)
	y := ext.Var("y", B)
	a := ext.Var("a", A)
	b := ext.Var("b", B)
	body := x.To(y.To(a.To(b.To(a.Eq(x).And(b.Eq(y)))))) // λx y a b. (a=x)∧(b=y)
	c := core.NewConstDef(body.Core(), "mk_pair")
	return ext.Const(c.Meta(), c.Meta().AbsType())
}

func defExpandFires(goal prop.Prop, mkp *ext.TermWrapper) bool {
	return ApplyDefExpand(CreateGoalStack(goal), mkp.AssertConst())
}

func TestDefExpand_MkPair_PositionMatrix(t *testing.T) {
	mkp := newMkPairConst()
	A := ext.TypeA
	B := ext.TypeB
	x0 := ext.Var("x_0", A)
	y0 := ext.Var("y_0", B)
	a0 := ext.Var("a_0", A)
	b0 := ext.Var("b_0", B)
	a := ext.Var("a", A)
	T := ext.WrapTerm(prop.T)
	Phi := ext.Var("Phi", ext.MakeFun(ext.TypeBool, ext.TypeBool))

	cases := []struct {
		name string
		goal prop.Prop
	}{
		{"top_level", prop.MakeProp(mkp.Apply(x0, y0, a0, b0))},
		{"under_and", prop.MakeProp(mkp.Apply(x0, y0, a0, b0).And(T))},
		{"under_forall", prop.MakeProp(ext.ForAll(a)(mkp.Apply(x0, y0, a, b0)))},
		{"under_app", prop.MakeProp(Phi.Apply(mkp.Apply(x0, y0, a0, b0)))},
		{"under_iff", prop.MakeProp(mkp.Apply(x0, y0, a0, b0).Eq(T))},
		{"under_iff_both", prop.MakeProp(mkp.Apply(a0, b0, a0, b0).Eq(mkp.Apply(x0, y0, a0, b0)))},
		{"under_not", prop.MakeProp(ext.Not(mkp.Apply(x0, y0, a0, b0)))},
	}
	for _, tc := range cases {
		if !defExpandFires(tc.goal, mkp) {
			t.Fatalf("%s: def_expand(mk_pair) did not fire on goal: %s",
				tc.name, ext.FormatTerm(tc.goal.Conclusion(), false))
		}
	}
}

func TestDefExpand_MkPair_UnderIff(t *testing.T) {
	mkp := newMkPairConst()
	A := ext.TypeA
	B := ext.TypeB
	x0 := ext.Var("x_0", A)
	y0 := ext.Var("y_0", B)
	a0 := ext.Var("a_0", A)
	b0 := ext.Var("b_0", B)
	goal := prop.MakeProp(a0.Eq(x0).And(b0.Eq(y0)).Eq(mkp.Apply(x0, y0, a0, b0)))
	if !defExpandFires(goal, mkp) {
		t.Fatalf("def_expand(mk_pair) did not fire under ⇔ on goal: %s",
			ext.FormatTerm(goal.Conclusion(), false))
	}
}

func TestDefExpand_MkPair_UnderNot(t *testing.T) {
	mkp := newMkPairConst()
	A := ext.TypeA
	B := ext.TypeB
	x0 := ext.Var("x_0", A)
	y0 := ext.Var("y_0", B)
	a0 := ext.Var("a_0", A)
	b0 := ext.Var("b_0", B)
	goal := prop.MakeProp(ext.Not(mkp.Apply(x0, y0, a0, b0)))
	if !defExpandFires(goal, mkp) {
		t.Fatalf("def_expand(mk_pair) did not fire under ¬ on goal: %s",
			ext.FormatTerm(goal.Conclusion(), false))
	}
}

// wideForallHyp builds a representative wide multi-quantifier ∀-hyp
// `∀a b c d. a ∧ b ∧ c ∧ d` — the shape that drives the CNF refuter to
// its ceiling when left resident in the hyp context. `clear` exists to
// drop exactly this before `refute`/`auto`.
func wideForallHyp() Term {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	d := Var("d", TypeBool)
	return ForAll(a, b, c, d)(a.And(b).And(c).And(d))
}

// hypIndexOf returns the 0-based index of hyp h in goal (MakeProp
// canonicalizes hyp order, so insertion order is not preserved).
func hypIndexOf(t *testing.T, goal Prop, h Term) int {
	t.Helper()
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaEquals(h) {
			return i
		}
	}
	t.Fatalf("hyp not found in goal")
	return -1
}

// TestClearHypsStep_DropsTargetHyp verifies clear removes exactly the
// indexed hyp and leaves the conclusion and remaining hyps untouched.
func TestClearHypsStep_DropsTargetHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	wide := wideForallHyp()
	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	// goal: wide∀, p, q ⊢ p
	goal := core.MakeProp(p, wide, p, q)

	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_ClearHypsStep{hypIndices: []int{hypIndexOf(t, goal, wide)}}), "clear should apply")

	leaves := n.UnsolvedLeaves()
	require.Len(t, leaves, 1, "clear produces exactly one subgoal")
	child := leaves[0].Goal
	assert.Equal(t, 2, child.NumHyps(), "one hyp dropped")
	assert.True(t, child.Conclusion().AlphaEquals(p), "conclusion unchanged")
	assert.False(t, child.HasHyp(wide), "the wide ∀-hyp is gone")
	assert.True(t, child.HasHyp(p) && child.HasHyp(q), "other hyps retained")
}

// TestClearHypsStep_EndToEndSound drives a full close after clearing the
// poisoning hyp: the residual `p ⊢ p` closes trivially and the root
// reconstructs to a thm that is IsStronger than the original goal —
// the soundness contract MakeSubGoals enforces, exercised end to end.
func TestClearHypsStep_EndToEndSound(t *testing.T) {
	defer goleak.VerifyNone(t)

	wide := wideForallHyp()
	p := Var("p", TypeBool)
	// goal: wide∀, p ⊢ p   (closable; the wide∀ is pure noise)
	goal := core.MakeProp(p, wide, p)

	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_ClearHypsStep{hypIndices: []int{hypIndexOf(t, goal, wide)}}), "clear should apply")

	leaves := n.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	// residual p ⊢ p closes via the trivial `h ⊢ h` rule.
	require.True(t, leaves[0].runStep(_TrivialSimplify{}), "residual should close")

	require.True(t, n.Proved(), "root should be proved after the residual closes")
	got := n.ProvedThm()
	require.False(t, got.IsZero())
	assert.True(t, IsStronger(got, goal),
		"reconstructed thm must prove the original goal")
	assert.True(t, got.Conclusion().AlphaEquals(p), "conclusion preserved")
}

// L2 acceptance: a promise-backed lemma cited into a goal threads all the way
// to the node's provedThm WITHOUT forcing, then snaps to a real Thm when the
// top is forced. This is the goal-stack analogue of the omega force-on-use test
// — it proves the seam (provedThm Prop, _KnownThmStep, MakeEmptySubGoals,
// Reconstruct) carries a promise instead of collapsing it.

// Closing a leaf with a promise closer (what LemmaMacro.Apply emits via
// _KnownThmStep) leaves provedThm a promise; forcing it runs the builder once.
func TestLemmaPromise_ThreadsToProvedThm(t *testing.T) {
	P := Var("P", TypeBool)
	goal := MakeProp(P)

	var built int32
	lemma := core.Promise(MakeProp(P), func(core.Forcer) core.ThmCert {
		atomic.AddInt32(&built, 1)
		return core.TestThm(P)
	})

	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_KnownThmStep{strongerGoal: lemma}))

	require.True(t, n.Proved(), "node closed by the promise closer")
	assert.True(t, core.IsPromised(n.PromisedThm()), "provedThm threaded as a promise")
	assert.False(t, n.PromisedThm().Proved(), "not forced yet")
	assert.Equal(t, int32(0), atomic.LoadInt32(&built), "builder did not run on cite")

	thm := core.Force(context.Background(), n.PromisedThm())
	assert.True(t, thm.Conclusion().AlphaEquals(P))
	assert.Equal(t, int32(1), atomic.LoadInt32(&built), "builder ran once on force")
	assert.True(t, n.PromisedThm().Proved())
}

// A promise on ONE child threads through the parent's reconstruction
// (updateUpwards) as a DERIVED promise; the whole subtree stays unforced until
// the top is forced, at which point only the promised leaf's builder runs.
func TestLemmaPromise_ThreadsThroughParentReconstruct(t *testing.T) {
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	n := CreateGoalStack(goal)
	require.True(t, ApplyAssert(n, MakeProp(P)))
	require.Equal(t, 2, len(n.children)) // child0: ⊢P, child1: P⊢Q

	var built int32
	promiseP := core.Promise(MakeProp(P), func(core.Forcer) core.ThmCert {
		atomic.AddInt32(&built, 1)
		return core.TestThm(P)
	})
	// Close child0 with the promise, child1 with a realized thm. The second
	// close triggers updateUpwards → the parent reconstructs.
	n.children[0].runStep(_KnownThmStep{strongerGoal: promiseP})
	n.children[1].runStep(_KnownThmStep{strongerGoal: core.TestThm(Q, P)})

	require.True(t, n.Proved(), "parent reconstructed once both children closed")
	assert.True(t, core.IsPromised(n.PromisedThm()), "parent provedThm is a derived promise")
	assert.False(t, n.PromisedThm().Proved(), "subtree stays unforced")
	assert.Equal(t, int32(0), atomic.LoadInt32(&built), "builder not run until top is forced")

	thm := core.Force(context.Background(), n.PromisedThm())
	assert.True(t, thm.Conclusion().AlphaEquals(Q), "forced top proves the original goal")
	assert.Equal(t, int32(1), atomic.LoadInt32(&built), "only the promised leaf's builder ran")
	assert.True(t, n.PromisedThm().Proved())
}

// TestSpecializeStep_ProtoRoundTrip verifies the specialize composite
// ministep applies and survives serialization with its per-hyp witness
// lists, hyp indices, and keep_sources flag intact.
func TestSpecializeStep_ProtoRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	P := Var("P", MakeFun(TypeA, TypeBool))
	q := Var("q", TypeBool)

	allR := ForAll(x, y)(R.Apply(x, y)).Core()
	allP := ForAll(x)(P.Apply(x)).Core()
	goal := core.MakeProp(q.Core(), allR, allP)
	findIdx := func(h core.Term) int {
		for i := range goal.NumHyps() {
			if goal.Hyp(i).AlphaEquals(h) {
				return i
			}
		}
		t.Fatalf("hyp not found: %s", h)
		return -1
	}

	step := _SpecializeStep{
		specs: []SpecializeHyp{
			InstHyp(findIdx(allR), a.Core(), b.Core()),
			InstHyp(findIdx(allP), b.Core()),
		},
		keepSources: true,
	}

	// (a) record: apply the original step.
	nOrig := CreateGoalStack(goal)
	require.True(t, nOrig.runStep(step), "original specialize should apply")

	// (b) serialize → deserialize.
	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	payload := decoded.GetSpecialize()
	require.NotNil(t, payload)
	r := ext.NewPoolReader(pb.Pool(), nil)
	hyps := payload.GetHyps()
	require.Len(t, hyps, 2)
	assert.Equal(t, int32(step.specs[0].HypIndex), hyps[0].GetHypIndex())
	assert.Equal(t, int32(step.specs[1].HypIndex), hyps[1].GetHypIndex())
	require.Len(t, hyps[0].GetWitnesses(), 2)
	assert.True(t, r.Term(hyps[0].GetWitnesses()[0]).AlphaEquals(a.Core()))
	assert.True(t, r.Term(hyps[0].GetWitnesses()[1]).AlphaEquals(b.Core()))
	require.Len(t, hyps[1].GetWitnesses(), 1)
	assert.True(t, r.Term(hyps[1].GetWitnesses()[0]).AlphaEquals(b.Core()))
	assert.True(t, payload.GetKeepSources(), "keep_sources must survive round-trip")
}
