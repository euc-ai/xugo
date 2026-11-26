package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// Arith tests drives ArithTactic with omega bundles, so omega's bundle-nil
// named leaves fall back to the placeholder seam. Install the fabricator so those
// leaves get statement-correct stand-ins.
func init() {
	omega.SetPlaceholderFabricator(func(concl core.Term) *prop.PropWrapper {
		return prop.WrapProp(core.TestThm(concl))
	})
}

// These cover the unified `_Arith` ministep and the standard agent-facing
// composite (`ApplyArithSimplify` = _Arith + _TrivialSimplify). Leaves come
// from the placeholder bundle (no corpus installed in this unit test), so
// this checks the WIRING: distinct proto records, replay round-trip, and
// that the composite closes the motivating shapes — soundness lands with the
// installed corpus bundle.

func natPlus(x, y core.Term) core.Term { return ext.Apply(dsl.NatPlusMeta.Term(), x, y) }
func natLt(x, y core.Term) core.Term   { return ext.Apply(dsl.NatLtMeta.Term(), x, y) }

// TestArith_ClosesByIdentity: a goal whose only obstacle is `a + 0` closes
// via the unified _Arith rewrite (the a+0→a identity leaf is inside ArithDecide's
// BasicRewritesWith composition) plus trivial — root records `arith=42`.
func TestArith_ClosesByIdentity(t *testing.T) {
	a := Var("a", dsl.NumType)
	goal := core.MakeProp(core.Eq(natPlus(a.Core(), dsl.ZeroMeta.Term()), a.Core())) // a + 0 = a

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "composite should fire on a+0=a")
	require.True(t, n.Proved(), "a+0=a should close (a+0→a, then a=a→⊤ via BoolRewrite's l=l rule)")

	_, ok := n.miniStep.(_Arith)
	require.True(t, ok, "root step must be recorded as _Arith, got %T", n.miniStep)
	assertNoBasicTacticRecord(t, n)
}

// TestArith_ClosesComparison: `a < a+1` closes via _Arith (atom decision → ⊤)
// + trivial. The user's `a+1>a → ⊤` example, end to end.
func TestArith_ClosesComparison(t *testing.T) {
	a := Var("a", dsl.NumType)
	goal := core.MakeProp(natLt(a.Core(), natPlus(a.Core(), omega.Numeral(1)))) // a < a + 1

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "composite should fire on a<a+1")
	require.True(t, n.Proved(), "a<a+1 should close (decide → ⊤ → trivial)")

	_, ok := n.miniStep.(_Arith)
	require.True(t, ok, "root step must be recorded as _Arith, got %T", n.miniStep)
	assertNoBasicTacticRecord(t, n)
}

// TestArith_DeclinesCleanly: nothing reduces → no-op (the composite returns
// false and the node is untouched), not a panic / dangling subgoal.
func TestArith_DeclinesCleanly(t *testing.T) {
	a := Var("a", dsl.NumType)
	b := Var("b", dsl.NumType)
	goal := core.MakeProp(natLt(a.Core(), b.Core())) // a < b : contingent, nothing reduces

	n := CreateGoalStack(goal)
	require.False(t, ApplyArithSimplify(t.Context(), n), "composite should decline on contingent a<b")
	require.Nil(t, n.miniStep, "declined composite must leave the node untouched")
}

func natLe(x, y core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), x, y) }
func imp(p, q core.Term) core.Term   { return ext.Apply(ext.IMPLY, p, q) }

// The leading-wrapper strip: `_Arith` is hyp-aware but blind to a `∀`/`⇒`
// wrapper on the CONCLUSION (the antecedents never reach the decider as hyps).
// ApplyArithSimplify strips those wrappers as a fallback and closes the
// implication / ∀-prenex forms without a manual `strip_imp; arith`. The
// leaves are placeholder-bundle TestThms (no corpus here), so this
// checks the WIRING — that the strip+decide composite closes.

// TestArith_ClosesImplicationTransitivity: `⊢ (a≤b) ⇒ (b≤c) ⇒ (a≤c)` — the
// sequent form `a≤b, b≤c ⊢ a≤c` is the canonical linarith goal, but here the
// facts are ⇒-antecedents. The strip moves them to hyps, then arith closes.
func TestArith_ClosesImplicationTransitivity(t *testing.T) {
	a, b, c := Var("a", dsl.NumType), Var("b", dsl.NumType), Var("c", dsl.NumType)
	goal := core.MakeProp(imp(natLe(a.Core(), b.Core()), imp(natLe(b.Core(), c.Core()), natLe(a.Core(), c.Core()))))

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "arith should close ⇒-form transitivity")
	require.True(t, n.Proved(), "(a≤b)⇒(b≤c)⇒(a≤c) should close")
	// NB: the direct `_Arith` pass closes this via the formula-level
	// decider's atom case-split — the leading-⇒ strip fallback is not
	// reached for a pure comparison-atom implication. We assert closure
	// (the contract), not which internal path took it.
}

// TestArith_ClosesImplicationNonneg: `⊢ (n0+n1 ≤ m0) ⇒ (n0 ≤ m0)` — closes
// from the single antecedent plus the implicit num nonnegativity `0 ≤ n1`.
func TestArith_ClosesImplicationNonneg(t *testing.T) {
	n0, n1, m0 := Var("n0", dsl.NumType), Var("n1", dsl.NumType), Var("m0", dsl.NumType)
	goal := core.MakeProp(imp(natLe(natPlus(n0.Core(), n1.Core()), m0.Core()), natLe(n0.Core(), m0.Core())))

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "strip+arith should close ⇒-form nonneg bound")
	require.True(t, n.Proved(), "(n0+n1≤m0)⇒(n0≤m0) should close via implicit 0≤n1")
}

// TestArith_ClosesForallPrenex: `⊢ ∀a b c. (a≤b) ⇒ (b≤c) ⇒ (a≤c)` — the strip
// peels the ∀ prenex (StripQuant) AND the ⇒ chain (StripImp) to a fixpoint
// before the decider runs. Root records the ∀ strip.
func TestArith_ClosesForallPrenex(t *testing.T) {
	a, b, c := Var("a", dsl.NumType), Var("b", dsl.NumType), Var("c", dsl.NumType)
	body := imp(natLe(a.Core(), b.Core()), imp(natLe(b.Core(), c.Core()), natLe(a.Core(), c.Core())))
	goal := core.MakeProp(ext.ForAll(a.Core(), b.Core(), c.Core())(body).Core())

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "arith should close ∀-prenex transitivity")
	require.True(t, n.Proved(), "∀a b c. (a≤b)⇒(b≤c)⇒(a≤c) should close")
	// As above: the deep rewrite decides the ∀-body in place via the
	// formula-level decider (a tautology over its atoms ⇒ body⇔⊤ under the
	// binder), so closure does not route through the strip-quant fallback.
}

// TestArith_StripUntouchedOnInvalid: the strip is committed ONLY when the
// decider then fully closes. An invalid ⇒-goal (`(a≤b) ⇒ (b≤a)`) must leave the
// node pristine — the strip trial runs on a Clone, so a non-closing arith call
// never leaves a surprising half-stripped residual for the next tactic.
func TestArith_StripUntouchedOnInvalid(t *testing.T) {
	a, b := Var("a", dsl.NumType), Var("b", dsl.NumType)
	goal := core.MakeProp(imp(natLe(a.Core(), b.Core()), natLe(b.Core(), a.Core()))) // b≤a does NOT follow from a≤b

	n := CreateGoalStack(goal)
	require.False(t, ApplyArithSimplify(t.Context(), n), "strip+arith must decline on the invalid ⇒-goal")
	require.Nil(t, n.miniStep, "a non-closing arith call must leave the node fully untouched (no half-strip)")
}

// TestTrivialSimplify_CollapsesNotTrue verifies the boolean-glue half of the
// `≠ → ⊥` story: `_TrivialSimplify` (which embeds prop.BasicRewrite) on its
// own collapses `¬⊤` — `(¬⊤) ⇒ P` reduces (`¬⊤→⊥`, `⊥⇒P→⊤`) and the goal
// closes. So _Arith doesn't need a separate `¬⊤⇔⊥` rule even when
// _TrivialSimplify is the FOLLOW-UP step (in addition, BasicRewritesWith
// inside _Arith collapses `¬⊤→⊥` in the same fixpoint pass — see the
// `(¬(a<a+1))⇒P` test below).
func TestTrivialSimplify_CollapsesNotTrue(t *testing.T) {
	P := Var("P", TypeBool)
	goal := core.MakeProp(Not(T).Imply(P)) // ⊢ (¬⊤) ⇒ P

	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_TrivialSimplify{}), "_TrivialSimplify should fire on (¬⊤)⇒P")
	require.True(t, n.Proved(), "(¬⊤)⇒P should close: ¬⊤→⊥ then ⊥⇒P→⊤")
}

// TestArith_NegatedAtomCollapsesViaComposition: for `(¬(a<a+1)) ⇒ P`, the
// unified _Arith rewrite descends into the inner `a<a+1` (→⊤), and in the
// SAME fixpoint pass BoolRewrite folds `¬⊤→⊥` and `⊥⇒P→⊤`. The composite's
// _TrivialSimplify closes the ⊢⊤ residual.
func TestArith_NegatedAtomCollapsesViaComposition(t *testing.T) {
	a := Var("a", dsl.NumType)
	P := Var("P", TypeBool)
	// a < a + 1
	lt := natLt(a.Core(), natPlus(a.Core(), omega.Numeral(1)))
	goal := core.MakeProp(Not(lt).Imply(P)) // ⊢ (¬(a<a+1)) ⇒ P

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "composite should fire on (¬(a<a+1))⇒P")
	require.True(t, n.Proved(), "should close: decide a<a+1→⊤, ¬⊤→⊥, ⊥⇒P→⊤")
}

// TestArith_HypAwareBuriedClose exercises the hyp-aware path end to end:
// `{a ≤ b} ⊢ (a<b+1) ∨ Q`. The buried `a<b+1` is contingent on its own but
// follows from the hypothesis `a≤b`; ArithTactic threads the goal's hyps in,
// decides it to ⊤, and `⊤ ∨ Q → ⊤` collapses (in the same fixpoint pass) —
// closing the goal. (Pure-ℚ, so bundle-independent.)
func TestArith_HypAwareBuriedClose(t *testing.T) {
	a := Var("a", dsl.NumType)
	b := Var("b", dsl.NumType)
	Q := Var("Q", TypeBool)
	le := ext.Apply(dsl.NatLeMeta.Term(), a.Core(), b.Core())    // a ≤ b
	ltp1 := natLt(a.Core(), natPlus(b.Core(), omega.Numeral(1))) // a < b + 1
	goal := core.MakeProp(ext.WrapTerm(ltp1).Or(Q.Core()), le)   // {a≤b} ⊢ (a<b+1) ∨ Q

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "composite should fire using the a≤b hyp")
	require.True(t, n.Proved(), "{a≤b} ⊢ (a<b+1)∨Q should close: decide a<b+1→⊤, ⊤∨Q→⊤")
}

// assertNoBasicTacticRecord walks the produced subtree and asserts no node was
// recorded as `_BasicTactic` — the anti-circularity invariant: arith-side
// steps must NEVER masquerade as `basic` in the DB, since BasicTactic is what
// replays omega's own foundation theorems and routing arith through it would
// re-enter omega.
func assertNoBasicTacticRecord(t *testing.T, n *GoalStackNode) {
	t.Helper()
	var walk func(*GoalStackNode)
	walk = func(node *GoalStackNode) {
		if node == nil {
			return
		}
		if node.miniStep != nil {
			_, isBasic := node.miniStep.(_BasicTactic)
			assert.False(t, isBasic, "arith step must not record as _BasicTactic")
		}
		for _, c := range node.children {
			walk(c)
		}
	}
	walk(n)
}

// TestLemmaPreserveStep_KeepsGroundInstance verifies the lemma_preserve
// ministep's load-bearing property: a goal hyp that is a ground instance
// of a resident ∀-equation hyp survives the lemma load (it would be
// absorbed to ⊤ and dropped under the plain `lemma` tag's LemmaTactic),
// and the recorded payload carries the lemma.
func TestLemmaPreserveStep_KeepsGroundInstance(t *testing.T) {
	defer goleak.VerifyNone(t)

	// TestConsts for rigid heads (free vars would let conclMatch's
	// unifier instantiate them spuriously); the PoolReader gets a
	// test-local const-meta loader so the consts rehydrate.
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	f := ext.TestConst("f", core.MakeFun(TypeA, TypeA))
	g := ext.TestConst("g", core.MakeFun(TypeA, TypeA))
	R := ext.TestConst("R", core.MakeFun(TypeA, TypeBool))
	C := ext.TestConst("C", TypeBool)
	// MockConstMetaService seeds the logical-const metas (∀, =, …);
	// the test consts register on top.
	svc := MockConstMetaService()
	for n, ht := range map[core.TermName]core.HolType{
		"f": core.MakeFun(TypeA, TypeA),
		"g": core.MakeFun(TypeA, TypeA),
		"R": core.MakeFun(TypeA, TypeBool),
		"C": TypeBool,
	} {
		svc.LoadOrStoreConstMeta(core.MakeConstMeta(n, ht))
	}
	loadMeta := svc.LoadConstMeta

	forallEq := ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))) // ∀x. f(x) = g(x)
	ground := f.Apply(c).Eq(g.Apply(c))                  // f(c) = g(c)
	lemma := core.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := core.MakeProp(C.Core(), forallEq.Core(), ground.Core())

	step := _LemmaPreserveTactic{lemma: lemma}

	// (a) record: apply the original step.
	nOrig := CreateGoalStack(goal)
	require.True(t, nOrig.runStep(step), "original lemma_preserve should apply")

	// (b) serialize → deserialize: the payload is the lemma.
	pb := ext.NewPoolBuilder()
	var p isStepProto_Step
	require.NotPanics(t, func() { p = step.proto(pb) })
	bytes, err := proto.Marshal(&StepProto{Step: p})
	require.NoError(t, err)
	var decoded StepProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	payload, _ := ext.NewPoolReader(pb.Pool(), loadMeta).Prop(decoded.GetLemmaPreserve())
	require.NotNil(t, payload)
	assert.True(t, payload.AlphaEquals(lemma), "lemma must survive the round trip")

	// (c) the ground instance survives the load.
	groundSurvives := false
	for _, leaf := range nOrig.UnsolvedLeaves() {
		if leaf.Goal.HasHyp(ground.Core()) {
			groundSurvives = true
		}
	}
	assert.True(t, groundSurvives,
		"ground instantiation must survive the lemma_preserve load")
}

// ℝ twin of TestArith_Closes — the empirical check that
// nat ministep-level tests carry over to real once the unified
// `_Arith` ministep dispatches real (gated on a real bundle). Each installs an
// (empty) real bundle to flip the gate; the leaves then run on placeholders, so
// these pin the ministep COMPOSITION (the strip / bool-split / collapse path),
// not soundness — exactly as the nat versions pin it on the corpus bundle.

func realLeS(x, y core.Term) core.Term { return ext.Apply(dsl.RealLeMeta.Term(), x, y) }
func realLtS(x, y core.Term) core.Term { return ext.Apply(dsl.RealLtMeta.Term(), x, y) }
func realVarS(n string) core.Term      { return core.Var(core.TermName(n), dsl.RealType) }

// (x≤y) ⇒ (y≤z) ⇒ (x≤z) — the ⇒-form of real linarith transitivity. Closes via
// the formula-level real bool-split (the leading-⇒ strip fallback is not
// reached for a pure comparison-atom implication), the same as the nat twin.
func TestRealArith_ClosesImplicationTransitivity(t *testing.T) {
	omega.SetRealLemmaBundle(&omega.RealLemmaBundle{})
	t.Cleanup(func() { omega.SetRealLemmaBundle(nil) })

	x, y, z := realVarS("x"), realVarS("y"), realVarS("z")
	goal := core.MakeProp(imp(realLeS(x, y), imp(realLeS(y, z), realLeS(x, z))))

	n := CreateGoalStack(goal)
	require.True(t, ApplyArithSimplify(t.Context(), n), "arith should close ⇒-form real transitivity")
	require.True(t, n.Proved(), "(x≤y)⇒(y≤z)⇒(x≤z) should close")
}

// (x+y ≤ z) ⇒ (x ≤ z)  is NOT valid over ℝ (y may be negative) — arith must
// leave it untouched (no false close), the real analogue of the nat
// StripUntouchedOnInvalid contract. (Over num the nat version uses a valid
// nonneg shape; ℝ has no nonnegativity, so we assert the decline.)
func TestRealArith_StripUntouchedOnInvalid(t *testing.T) {
	omega.SetRealLemmaBundle(&omega.RealLemmaBundle{})
	t.Cleanup(func() { omega.SetRealLemmaBundle(nil) })

	x, y := realVarS("x"), realVarS("y")
	goal := core.MakeProp(imp(realLtS(x, y), realLtS(y, x))) // y<x does NOT follow from x<y

	n := CreateGoalStack(goal)
	require.False(t, ApplyArithSimplify(t.Context(), n), "arith must not close an invalid real implication")
	require.False(t, n.Proved(), "(x<y)⇒(y<x) must stay open")
}
