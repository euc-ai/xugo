package tactic

import (
	"context"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/assert"
)

func TestCloseByOmegaRetainsPromise(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	cert := core.Refl(x)
	built := false
	promise := core.Promise(cert, func(core.Forcer) core.ThmCert {
		built = true
		return cert
	})
	closed := closeByOmega(cert, prop.WrapProp(promise), true)
	assert.False(t, built, "closing a goal must retain its promise dependencies")
	result := core.AsThm(closed.Reconstruct())
	assert.False(t, built, "reconstruction must remain lazy")
	assert.True(t, core.Force(context.Background(), result).AlphaEquals(cert))
	assert.True(t, built)
}

// Arith tests drives ArithTactic with omega bundles, so omega's bundle-nil
// named leaves fall back to the placeholder seam. Install the fabricator so those
// leaves get statement-correct stand-ins.
func init() {
	omega.SetPlaceholderFabricator(func(concl core.Term) *prop.PropWrapper {
		return prop.WrapProp(core.TestThm(concl))
	})
}

// Tactic-layer adapters over prover/solver/omega. We check the shape gate (declines →
// nil) and that a success closes the goal outright (Size 0) with a Thm that
// MakeEmptySubGoals accepted (IsStronger: concl α-matches, hyps ⊆ goal hyps).
// Leaves are placeholders, so this validates the wiring, not soundness.

var (
	tNatLt   = dsl.NatLtMeta.Term()
	tNatLe   = dsl.NatLeMeta.Term()
	tNatPlus = dsl.NatPlusMeta.Term()
	tNatStar = dsl.NatStarMeta.Term()
)

func aV(name string) Term { return Var(TermName(name), dsl.NumType) }
func aLt(a, b Term) Term  { return ext.Apply(tNatLt, a, b) }
func aLe(a, b Term) Term  { return ext.Apply(tNatLe, a, b) }
func aAdd(a, b Term) Term { return ext.Apply(tNatPlus, a, b) }
func aMul(a, b Term) Term { return ext.Apply(tNatStar, a, b) }
func aEq(a, b Term) Term  { return core.Eq(a, b) }
func aNe(a, b Term) Term  { return ext.Not(aEq(a, b)) }
func aNum(k uint64) Term  { return omega.Numeral(k) }
func unscopedArithTactic(goal Prop) *SubGoals {
	return ArithTactic(goal, omega.UnscopedArithPolicy(), nil)
}

// assertClosed verifies the tactic closed the goal: non-nil, no subgoals, and
// the reconstructed Thm proves the goal (Reconstruct re-asserts IsStronger).
func assertClosed(t *testing.T, name string, sg *SubGoals, goal Prop) {
	t.Helper()
	if sg == nil {
		t.Fatalf("%s: tactic declined, want closed", name)
	}
	assert.Equal(t, 0, sg.Size(), name)
	thm := sg.Reconstruct()
	assert.True(t, thm.Conclusion().AlphaEquals(goal.Conclusion()), name)
}

func closeRing(t *testing.T, name string, goal Prop) {
	t.Helper()
	assertClosed(t, name, RingTactic(goal), goal)
}

func closeLin(t *testing.T, name string, goal Prop) {
	t.Helper()
	assertClosed(t, name, LinarithTactic(goal), goal)
}

func closeOmega(t *testing.T, name string, goal Prop) {
	t.Helper()
	assertClosed(t, name, OmegaTactic(goal), goal)
}

// TestArithTactic_NoHypSelfRewrite pins the fix in arithRewriteTactic: a
// hypothesis is rewritten only under the OTHER hypotheses, never under itself.
// Bundle-free (the behaviour is about CONTEXT, not lemma supply).
func TestArithTactic_NoHypSelfRewrite(t *testing.T) {
	a, b, c := aV("a"), aV("b"), aV("c")

	// `a≤b ⊢ a*b ≤ c`: the conclusion is opaque to linarith (nonlinear, c
	// unbounded) so it cannot be rewritten, and the sole hyp `a≤b` is a
	// comparison. The buggy version decided `a≤b` FROM ITSELF → ⊤, collapsing the
	// hyp and reporting a spurious child. The fix gives a clean decline: the hyp
	// has no OTHER hyps to be simplified by and is not context-free reducible.
	selfOnly := MakeProp(aLe(aMul(a, b), c), aLe(a, b))
	assert.Nil(t, unscopedArithTactic(selfOnly),
		"arith must not self-rewrite the hyp a≤b to ⊤ (clean decline expected)")

	// Sanity: the hyp branch STILL fires for a MEANINGFUL rewrite — a context-free
	// identity fold `(a+0) ≤ b → a ≤ b` — even though the conclusion is opaque.
	// So the fix removes only the self-justifying collapse, not useful hyp simp.
	foldable := MakeProp(aLe(aMul(a, b), c), aLe(aAdd(a, aNum(0)), b))
	sg := unscopedArithTactic(foldable)
	if sg == nil {
		t.Fatal("arith should fold the hyp (a+0)≤b → a≤b (context-free)")
	}
	found := false
	for _, h := range sg.ChildGoal(0).Hyps() {
		if h.AlphaEquals(aLe(a, b)) {
			found = true
		}
	}
	assert.True(t, found, "hyp (a+0)≤b should fold to a≤b in the child")
}

func TestRingTactic(t *testing.T) {
	a, b := aV("a"), aV("b")

	// closes: semiring equalities
	closeRing(t, "comm +", testProp(aEq(aAdd(a, b), aAdd(b, a))))
	closeRing(t, "x*1=x", testProp(aEq(aMul(a, aNum(1)), a)))
	closeRing(t, "distrib", testProp(aEq(aMul(a, aAdd(b, aNum(1))), aAdd(aMul(a, b), a))))

	// declines: not a provable equality / not an equality at all
	assert.Nil(t, RingTactic(testProp(aEq(aAdd(a, b), a))), "a+b=a is false")
	assert.Nil(t, RingTactic(testProp(aLt(a, b))), "a<b is not an equality")
}

func TestLinarithTactic(t *testing.T) {
	a, b, c := aV("a"), aV("b"), aV("c")

	// closes: no-hyp arithmetic facts
	closeLin(t, "a<a+1", testProp(aLt(a, aAdd(a, aNum(1)))))
	closeLin(t, "a<=a", testProp(aLe(a, a)))
	closeLin(t, "a!=a+1", testProp(aNe(a, aAdd(a, aNum(1)))))

	// closes: from hypotheses (hyps must survive on the Thm side ⊆ goal hyps)
	closeLin(t, "trans <=", testProp(aLe(a, c), aLe(a, b), aLe(b, c)))
	closeLin(t, "antisym =", testProp(aEq(a, b), aLe(a, b), aLe(b, a)))

	// declines: not valid, or not a linear comparison
	assert.Nil(t, LinarithTactic(testProp(aLt(a, b))), "a<b unprovable with no hyps")
	assert.Nil(t, LinarithTactic(testProp(aLe(b, a), aLe(a, b))), "b<=a not implied by a<=b")
	assert.Nil(t, LinarithTactic(testProp(Var("p", TypeBool))), "non-arith goal")
}

func TestOmegaTactic(t *testing.T) {
	a, b := aV("a"), aV("b")

	// Pure-linear (no integer reasoning): OmegaTactic closes as a strict
	// superset of LinarithTactic.
	closeOmega(t, "a<a+1", testProp(aLt(a, aAdd(a, aNum(1)))))

	// Integer-only with nothing to round: the strict hypothesis is read as
	// `suc b ≤ a + 1`, and the rows add up to a false constant relation as
	// they stand. No cut leaf is read.
	bLtA1 := testProp(aLe(b, a), aLt(b, aAdd(a, aNum(1)))) // {b<a+1} ⊢ b<=a
	assert.Nil(t, LinarithTactic(bLtA1), "linarith cannot prove b<=a from b<a+1 (rational gap)")
	closeOmega(t, "b<a+1 ⊢ b<=a", bLtA1)

	// Integer-only with a rounding (needs intCut / gcdEqAbsurd / notDivides):
	// the soundness guard makes OmegaTactic DECLINE until those leaves'
	// theorems (ModEqZero / LessEqRightDivEq / …) become real. The omega
	// ALGORITHM still finds the proof (TestOmegaProve covers that) — the
	// tactic refuses to relay a placeholder-tainted cert. When the theorems
	// land, these will close automatically (flip the asserts back to
	// closeOmega).
	assert.Nil(t, OmegaTactic(testProp(aLe(a, aNum(0)), aLe(aMul(aNum(2), a), aNum(1)))),
		"soundness guard: 2a<=1 ⊢ a<=0 needs intCut")
	assert.Nil(t, OmegaTactic(testProp(aNe(aMul(aNum(2), a), aNum(1)))),
		"soundness guard: 2a!=1 needs gcdEqAbsurd / notDivides")

	// Still declines invalid / non-arith goals (algorithm-level rejection).
	assert.Nil(t, OmegaTactic(testProp(aLe(a, b))), "a<=b unprovable with no hyps")
	assert.Nil(t, OmegaTactic(testProp(Var("p", TypeBool))), "non-arith goal")
}

// TestArithTactic_ContentRewriteOutranksDrop pins the hyp loop's firing
// order: a redundancy DROP (hyp ⇔ ⊤ under the others, droppable) is
// deferred behind any CONTENT rewrite. Under the monomial-basis
// extraction the decider proves far more collective redundancies (an
// already-derived `n·a ≤ n·b` re-derives from its sources), and index
// order started spending a one-shot composite's single firing on the
// drop, stranding the load-bearing rewrite — the eudoxus_slope.LessEqTotal
// incident. The drop itself remains intended behavior (arith as a
// simplifier — engine TestArith_HypRewriteContext pins it); only its
// PRIORITY changed.
func TestArithTactic_ContentRewriteOutranksDrop(t *testing.T) {
	x, z, w, q, r, b := aV("x"), aV("z"), aV("w"), aV("q"), aV("r"), Var("b", core.TypeBool())

	// Drop-only: 2x ≤ w is collectively redundant from {2x ≤ z, z ≤ w};
	// nothing else rewrites (conclusion b is opaque). The drop fires —
	// the deferral must not turn into retention.
	dropOnly := MakeProp(b.Core(),
		aLe(aMul(aNum(2), x), z), aLe(z, w), aLe(aMul(aNum(2), x), w))
	sg := unscopedArithTactic(dropOnly)
	if sg == nil {
		t.Fatal("the deferred drop must still fire when it is the only rewrite")
	}
	for _, h := range sg.ChildGoal(0).Hyps() {
		assert.False(t, h.AlphaEquals(aLe(aMul(aNum(2), x), w)),
			"the redundant 2x ≤ w should be dropped")
	}

	// Coexistence: the droppable hyp sits at a LOWER index than a
	// content rewrite (the context-free identity fold (q+0) < r →
	// q < r). The content rewrite must win the firing; the droppable
	// hyp survives this call.
	both := MakeProp(b.Core(),
		aLe(aMul(aNum(2), x), w), aLe(aMul(aNum(2), x), z), aLe(z, w),
		aLt(aAdd(q, aNum(0)), r))
	sg = unscopedArithTactic(both)
	if sg == nil {
		t.Fatal("the content rewrite should fire")
	}
	child := sg.ChildGoal(0)
	foundFold, foundRedundant := false, false
	for _, h := range child.Hyps() {
		if h.AlphaEquals(aLt(q, r)) {
			foundFold = true
		}
		if h.AlphaEquals(aLe(aMul(aNum(2), x), w)) {
			foundRedundant = true
		}
	}
	assert.True(t, foundFold, "the identity fold (q+0)<r → q<r must be the firing")
	assert.True(t, foundRedundant, "the droppable hyp must survive — deferred, not fired")
}

// TestArithTactic_GoalMeetsAHypothesisAtADefinition: the leaf of the
// homotopy_group.HomotopicSym livelock. Under `i = n` the conclusion
// `face(X, j, i, f(j)) = x` is the hypothesis `face(X, j, n, f(j)) = x`,
// and the decision reads both at the one variable, so the first firing is
// the conclusion's, to ⊤. No hypothesis is respelled on the way: the face
// hypothesis and the degeneracy hypothesis `deg(X, n, n, x) = f(j)` —
// whose respelling at i the context already holds, the firing the rounds
// once landed on every round — stand as written.
func TestArithTactic_GoalMeetsAHypothesisAtADefinition(t *testing.T) {
	A := core.MakeVarType("A")
	R := ext.MakeType("zz_arith_rec", A)
	num := dsl.NumType
	op := MakeFun(R, MakeFun(num, MakeFun(num, MakeFun(A, A))))
	face := core.MakeConstTerm(core.MakeConstMeta("zz_arith_face", op), op)
	deg := core.MakeConstTerm(core.MakeConstMeta("zz_arith_deg", op), op)
	X, x := Var("X", R), Var("x", A)
	f := Var("f", MakeFun(num, A))
	n, i, j := aV("n"), aV("i"), aV("j")
	fj := ext.Apply(f, j)
	goal := MakeProp(aEq(ext.Apply(face, X, j, i, fj), x),
		aEq(ext.Apply(face, X, j, n, fj), x),
		aEq(fj, ext.Apply(deg, X, i, i, x)),
		aEq(ext.Apply(deg, X, n, n, x), fj),
		aEq(i, n))
	sg := unscopedArithTactic(goal)
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("one firing with one residual, got %v", sg)
	}
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().Equals(T), "the firing decides the conclusion:\n%s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(aEq(ext.Apply(face, X, j, n, fj), x)),
		"the face hypothesis stands as written:\n%s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(aEq(ext.Apply(deg, X, n, n, x), fj)),
		"the degeneracy hypothesis stands as written:\n%s", prop.PrintProp(child))
}

// definedVariableLeaf is a leaf that holds two definitions and a content
// rewrite: `n = 2 * m` beside `Q(n)`, `p = 2` beside `p * m = n`, and
// `R(q + 0)`, which folds to `R(q)`.
func definedVariableLeaf(concl func(Rq Term) Term) (goal Prop, Qn, Q2m, Rq0, Rq Term) {
	num := dsl.NumType
	Q, R := Var("Q", MakeFun(num, TypeBool)), Var("R", MakeFun(num, TypeBool))
	n, m, p, q := aV("n"), aV("m"), aV("p"), aV("q")
	Qn, Q2m = ext.Apply(Q, n), ext.Apply(Q, aMul(aNum(2), m))
	Rq0, Rq = ext.Apply(R, aAdd(q, aNum(0))), ext.Apply(R, q)
	goal = MakeProp(concl(Rq),
		Qn, Rq0, aEq(n, aMul(aNum(2), m)), aEq(p, aNum(2)), aEq(aMul(p, m), n))
	return
}

// TestArithTactic_ACloseReadsTheLeafAtItsDefinitionsLast: in the rounds of
// a close a leaf is read whole at the definitions its hypotheses hold —
// one firing, every hypothesis, the definitions' own equations gone with
// the variables they defined — and only where nothing else fires: a name
// the author gave a term stands while a firing is left. A firing outside a
// close never reads the leaf.
func TestArithTactic_ACloseReadsTheLeafAtItsDefinitionsLast(t *testing.T) {
	b := Var("b", core.TypeBool())
	goal, Qn, Q2m, Rq0, Rq := definedVariableLeaf(func(Term) Term { return b.Core() })
	policy := omega.UnscopedArithPolicy()
	n, m, p := aV("n"), aV("m"), aV("p")

	// The fold fires first, and Q(n) stands.
	sg, fold := ArithTacticPassingOver(goal, policy, nil, nil)
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("one firing with one residual, got %v", sg)
	}
	assert.True(t, fold.From.AlphaEquals(Rq0) && fold.To.AlphaEquals(Rq),
		"the first firing is the fold of R(q + 0), got %s to %s", ext.PrintTerm(fold.From), ext.PrintTerm(fold.To))
	assert.True(t, sg.ChildGoal(0).HasHyp(Qn), "Q(n) stands as written:\n%s", prop.PrintProp(sg.ChildGoal(0)))

	// With the fold passed over nothing else fires, and the leaf is read.
	sg, reading := ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{fold})
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("past the fold the leaf's reading fires, got %v", sg)
	}
	read := sg.ChildGoal(0)
	assert.True(t, reading.Conclusion && reading.From.AlphaEquals(b) && reading.To.AlphaEquals(b),
		"the firing is the leaf's reading, which leaves this conclusion as it is")
	assert.True(t, read.HasHyp(Q2m) && !read.HasHyp(Qn), "Q(n) is read as Q(2 * m):\n%s", prop.PrintProp(read))
	assert.True(t, read.HasHyp(Rq0), "a hypothesis that names no defined variable stands:\n%s", prop.PrintProp(read))
	assert.False(t, read.HasHyp(aEq(n, aMul(aNum(2), m))) || read.HasHyp(aEq(p, aNum(2))),
		"the definitions are gone with their variables:\n%s", prop.PrintProp(read))
	for _, name := range []core.TermName{"n", "p"} {
		assert.False(t, read.HasFreeName(name), "%s is still named:\n%s", name, prop.PrintProp(read))
	}

	sg, _ = ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{fold, reading})
	assert.Nil(t, sg, "with every rewrite passed over the step declines")

	// Outside a close a leaf with nothing to fire but its reading is left alone.
	bare := MakeProp(b.Core(), Qn, aEq(n, aMul(aNum(2), m)))
	assert.Nil(t, unscopedArithTactic(bare), "a firing outside a close read the leaf")
	sg, _ = ArithTacticPassingOver(bare, policy, nil, nil)
	if sg == nil || sg.Size() != 1 || !sg.ChildGoal(0).HasHyp(Q2m) {
		t.Fatalf("in a close the same leaf is read, got %v", sg)
	}
}

// TestArithTactic_NamedRewriteIsPassedOver: a rewrite the caller names is
// not fired, and the firing goes to the next target, or to none. A
// pass-over names a target and its rewrite together.
func TestArithTactic_NamedRewriteIsPassedOver(t *testing.T) {
	b := Var("b", core.TypeBool())
	goal, _, Q2m, Rq0, Rq := definedVariableLeaf(func(Term) Term { return b.Core() })
	policy := omega.UnscopedArithPolicy()

	_, fold := ArithTacticPassingOver(goal, policy, nil, nil)
	assert.True(t, fold.From.AlphaEquals(Rq0) && fold.To.AlphaEquals(Rq))
	// The fold named with another result is still fired.
	sg, again := ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{{From: Rq0, To: Q2m}})
	assert.NotNil(t, sg)
	assert.True(t, again.From.AlphaEquals(Rq0) && again.To.AlphaEquals(Rq))
	// Named as it fires, it is passed over, and the next firing is another.
	sg, next := ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{fold})
	assert.NotNil(t, sg)
	assert.False(t, next.From.AlphaEquals(Rq0) && next.To.AlphaEquals(Rq), "the fold fired though passed over")
}

// TestArithTactic_ConclusionRewriteIsPassedOver: the conclusion's rewrite
// is reported as a hypothesis's is, and passed over the same way: the
// firing then goes to the first hypothesis with one, the conclusion left
// as it stands. A pass-over names its target, so one that spells the
// conclusion's rewrite as a hypothesis's does not stop it.
func TestArithTactic_ConclusionRewriteIsPassedOver(t *testing.T) {
	a, b, c := aV("a"), aV("b"), aV("c")
	S := Var("S", MakeFun(dsl.NumType, TypeBool))
	concl, folded := ext.Apply(S, aAdd(a, aNum(0))), ext.Apply(S, a)
	hyp, hypFolded := aLe(aAdd(b, aNum(0)), c), aLe(b, c)
	goal := MakeProp(concl, hyp)
	policy := omega.UnscopedArithPolicy()

	sg, fired := ArithTacticPassingOver(goal, policy, nil, nil)
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("the conclusion's fold fires, got %v", sg)
	}
	assert.True(t, sg.ChildGoal(0).Conclusion().AlphaEquals(folded), "the firing is the conclusion's fold")
	assert.True(t, fired.Conclusion, "the firing is reported as the conclusion's")
	assert.True(t, fired.From.AlphaEquals(concl) && fired.To.AlphaEquals(folded))

	sg, next := ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{fired})
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("past the conclusion's rewrite the hypothesis's fold fires, got %v", sg)
	}
	assert.True(t, sg.ChildGoal(0).Conclusion().AlphaEquals(concl), "the conclusion passed over stands as it was")
	assert.False(t, next.Conclusion)
	assert.True(t, next.From.AlphaEquals(hyp) && next.To.AlphaEquals(hypFolded))

	sg, _ = ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{fired, next})
	assert.Nil(t, sg, "with both passed over nothing is left to fire")

	sg, again := ArithTacticPassingOver(goal, policy, nil, []ArithRewrite{{From: concl, To: folded}})
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("a hypothesis's pass-over does not stop the conclusion's rewrite, got %v", sg)
	}
	assert.True(t, again.Conclusion && sg.ChildGoal(0).Conclusion().AlphaEquals(folded))
}

// TestArithTactic_HeldEquationsStand: the closing retention puts the
// equations a redundant hypothesis holds in its place, and a hypothesis
// that is the conjunction of those equations already has no such rewrite.
// It is kept as it stands, however its ∧ associates, and is not dropped
// as an atom the decider proves; the firing goes to the next hypothesis.
func TestArithTactic_HeldEquationsStand(t *testing.T) {
	a, b, c, d, e := aV("a"), aV("b"), aV("c"), aV("d"), aV("e")
	S := Var("S", MakeFun(dsl.NumType, TypeBool))
	opaque := ext.Apply(S, e)
	and := func(l, r Term) Term { return ext.WrapTerm(l).And(r).Core() }
	policy := omega.UnscopedArithPolicy()
	holds := func(goal Prop, h Term) bool {
		return slices.ContainsFunc(goal.Hyps(), h.AlphaEquals)
	}

	// Two equations the decider proves from no hypothesis, and three in
	// either association: nothing fires, and the hypothesis is not dropped.
	x, y, z := aEq(aMul(a, aNum(1)), a), aEq(aAdd(b, aNum(0)), b), aNe(aAdd(c, aNum(1)), c)
	for name, hyp := range map[string]Term{
		"two":                and(x, y),
		"three to the left":  and(and(x, y), z),
		"three to the right": and(x, and(y, z)),
	} {
		sg, _ := ArithTacticPassingOver(MakeProp(opaque, hyp), policy, nil, nil)
		assert.Nil(t, sg, "%s: a conjunction of the equations it holds stands, and nothing fires", name)
	}

	// The equations follow from the other hypotheses: the conjunction
	// stands, and the firing is a drop among the hypotheses it makes
	// redundant.
	both := and(aEq(a, b), aEq(c, d))
	goal := MakeProp(opaque, aLe(a, b), aLe(b, a), aLe(c, d), aLe(d, c), both)
	sg, fired := ArithTacticPassingOver(goal, policy, nil, nil)
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("a hypothesis the conjunction makes redundant is dropped, got %v", sg)
	}
	assert.False(t, fired.Conclusion)
	assert.False(t, fired.From.AlphaEquals(both), "the firing is not the conjunction's")
	assert.True(t, fired.To.Equals(T), "the firing is a drop")
	assert.True(t, holds(sg.ChildGoal(0), both), "the conjunction stands in the child")

	// A conjunct another hypothesis spells is not one of the held
	// equations: the hypothesis is rewritten to the rest.
	nonzero := aNe(a, aNum(0))
	goal = MakeProp(opaque, aLt(aNum(0), a), nonzero, and(nonzero, x))
	sg, fired = ArithTacticPassingOver(goal, policy, nil, nil)
	if sg == nil || sg.Size() != 1 {
		t.Fatalf("a conjunction holding more than its held equations is rewritten, got %v", sg)
	}
	assert.True(t, fired.From.AlphaEquals(and(nonzero, x)) && fired.To.AlphaEquals(x))
	assert.True(t, holds(sg.ChildGoal(0), x) && !holds(sg.ChildGoal(0), and(nonzero, x)))
}

// TestReadByAtoms: a hypothesis is read atom by atom — each atom the
// context settles put at its value, the connectives folded — so a law's
// instance one side of which is settled leaves its other side, where a
// verdict on the instance as a whole would leave nothing.
func TestReadByAtoms(t *testing.T) {
	bool := func(name string) Term { return Var(TermName(name), core.TypeBool()).Core() }
	p, q, a, l, z, e, g, c := bool("p"), bool("q"), bool("a"), bool("l"), bool("z"), bool("e"), bool("g"), bool("c")
	or := func(x, y Term) Term { return ext.Apply(prop.OR, x, y) }
	imply := func(x, y Term) Term { return ext.Apply(prop.IMPLY, x, y) }
	not := func(x Term) Term { return ext.Apply(prop.NOT, x) }
	// settle decides the atoms given and no other: {x = v} ⊢ x = v.
	settle := func(values map[Term]Term) func(Term) *PropWrapper {
		return func(t Term) *PropWrapper {
			for atom, v := range values {
				if t.AlphaEquals(atom) {
					return prop.Assume(core.Eq(atom, v))
				}
			}
			return nil
		}
	}
	for _, row := range []struct {
		name    string
		h       Term
		settled map[Term]Term
		want    Term
	}{
		{"an instance under its guard, the right side false", or(p, core.Eq(a, q)), map[Term]Term{p: F, q: F}, not(a)},
		{"an instance whose left side holds", core.Eq(l, or(z, e)), map[Term]Term{l: T}, or(z, e)},
		{"a guard that holds", imply(g, not(c)), map[Term]Term{g: T}, not(c)},
		{"every atom settled", or(p, core.Eq(a, q)), map[Term]Term{p: F, a: T, q: T}, T},
	} {
		read := readByAtoms(row.h, settle(row.settled))
		if assert.NotNil(t, read, row.name) {
			assert.True(t, prop.Lhs(read).AlphaEquals(row.h), "%s: the reading is of the hypothesis", row.name)
			assert.True(t, Rhs(read).AlphaEquals(row.want), "%s: read %s, want %s",
				row.name, ext.PrintTerm(Rhs(read)), ext.PrintTerm(row.want))
		}
	}
	assert.Nil(t, readByAtoms(or(p, core.Eq(a, q)), settle(nil)), "with no atom settled there is no reading")
	// An atom is read whole: a settled formula under an unsettled atom's
	// own structure is not looked for.
	assert.Nil(t, readByAtoms(a, settle(map[Term]Term{p: T})), "an atom the context does not settle stands")
}
