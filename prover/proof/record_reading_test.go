package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// The record reading of the apply rung: a statement spelled with a
// record projection of a packed value, `x ∈ zz_r_carrier(zz_mk_r(c))`,
// and one spelled at the part, `x ∈ c` — what a cited instance spells —
// are one statement to the rung, which reads the leaf's projections
// where the reading is what identifies them (_RecordRead). The author's
// spelling stands in the hypotheses and the goal (#1455, the
// DualizingModuleOn class).

// recordTestScript is the step-test env with a record `zz_mk_r` packing
// one set, its projection `zz_r_carrier`, the projection equation
// installed as a record equation, and a law stating the projection as a
// conjunct.
func recordTestScript(t *testing.T) *Script {
	env := makeStepTestEnv()
	setT := core.MakeFun(ext.NumType, core.TypeBool())
	recT := core.MakeFun(ext.NumType, ext.NumType)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_mk_r", core.MakeFun(setT, recT)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_r_carrier", core.MakeFun(recT, setT)))
	ctx := NewScript(env)
	ctx.Const("zz_mk_r", core.MakeFun(setT, recT))
	ctx.Const("zz_r_carrier", core.MakeFun(recT, setT))
	projection := core.TestThm(ctx.MakePropText("∀c:(num → bool). zz_r_carrier(zz_mk_r(c)) = c").Conclusion())
	serveThm(ctx, "zz_r_carrier_mk", projection)
	tactic.InstallRecordNormal([]tactic.RecordEquation{{
		Head: "zz_r_carrier", Constructor: "zz_mk_r", Entry: "zz_r_carrier_mk", Statement: projection.AsProp(),
	}}, nil, func(string) *prop.PropWrapper { return prop.WrapProp(projection) })
	t.Cleanup(func() { tactic.InstallRecordNormal(nil, nil, nil) })
	serveThm(ctx, "zz_r_law", core.TestThm(ctx.MakePropText(
		"∀S:((num → bool) → bool). ∀P:(num → bool). ∀c:(num → bool). ∀x:num. "+
			"S(c) ⇒ P(x) ∧ zz_r_carrier(zz_mk_r(c)) = c ∧ x ∈ c").Conclusion()))
	return ctx
}

// A conjunct the instance normal form computes to a reflexive equation
// at a grounded cite is KEPT in the installed instance — `c = c` stands
// where the statement said `zz_r_carrier(zz_mk_r(c)) = c` — so the
// statement's conjunct count is the instance's, and Conjuncts labels
// them one for one. The refusal of a wrong count lists the conjuncts as
// the fact states them.
func TestCitedInstance_ReflexiveConjunctIsKept(t *testing.T) {
	ctx := recordTestScript(t)
	var installed core.Term
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀S:((num → bool) → bool). ∀P:(num → bool). ∀c:(num → bool). ∀x:num. S(c) ⇒ x ∈ c ∧ P(x)",
			func(a *Argument, S *ext.Expr[ext.Set[natSet]], P, c *ext.Expr[natSet], x *ext.Expr[ext.Nat], sc Fact) {
				whole := a.Simplified(GroupPremises(sc, At(depName("zz_r_law"), S, P, c, x)))
				installed, _ = whole.BoundContent()
				requirePanicContains(t, "the fact has 3 conjuncts and 2 label(s) were given — one per conjunct, in order; "+
					"the conjuncts as the fact states them (a cited instance is handed over in the instance normal form, so a "+
					"projection of a packed value is computed here):\n  1. P₀(x₀)\n  2. c₀ = c₀\n  3. x₀ ∈ c₀",
					func() { a.Conjuncts(whole, "P at x", "x lies in c") })
				parts := a.Conjuncts(whole, "P at x", "the carrier of the record is c", "x lies in c")
				a.Show("the conjuncts", By(parts[2], parts[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	require.NotNil(t, installed)
	parts := ext.DecomposesAND(installed)
	require.Len(t, parts, 3, "installed: %s", ext.PrintTerm(installed))
	l, r, ok := core.MatchesEQ(parts[1])
	require.True(t, ok && l.AlphaEquals(r), "the reflexive conjunct stands: %s", ext.PrintTerm(parts[1]))
}

// A guard a cited law states at the part, `x ∈ c`, is supplied by a
// hypothesis resident as the author spelled it, `x ∈ zz_r_carrier(zz_mk_r(c))`:
// the hypothesis keeps its spelling, the guard is discharged where the
// law is grounded (Lean's `f x₀ ‹A›`) — on the spine, the membership
// listed beside the instance, where the discharge reads the leaf's
// record projections (_RecordRead) and closes by assumption, keyless —
// and inside a By that names the membership, whose leaf the refuter
// alone could not close.
func TestRecordReading_ResidentProjectionSuppliesAComputedGuard(t *testing.T) {
	ctx := recordTestScript(t)
	const statement = "∀c:(num → bool). ∀x:num. ∀R:(num → bool). x ∈ zz_r_carrier(zz_mk_r(c)) ⇒ (∀y. y ∈ c ⇒ R(y)) ⇒ R(x)"
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, c *ext.Expr[natSet], x *ext.Expr[ext.Nat], R *ext.Expr[natSet], xIn, holds Fact) {
				content, bound := xIn.BoundContent()
				require.True(t, bound)
				require.Equal(t, "x₀ ∈ zz_r_carrier(zz_mk_r(c₀))", ext.PrintTerm(content), "the hypothesis stands as spelled")
				a.Do(GroupPremises(xIn, holds.At(x)))
				// a.Hyp refuses a text no hypothesis spells: the guard is
				// discharged on the spine and the consequent is resident.
				a.Show("R at x, grounded and discharged", By(a.Hyp("R(x)")))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	tree := describeTree(sec)
	require.Contains(t, tree, "RecordRead", "the discharge read the leaf's record projections:\n%s", tree)
	require.NotContains(t, tree, "CNF", "the discharge is keyless:\n%s", tree)
	sec = provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, c *ext.Expr[natSet], x *ext.Expr[ext.Nat], R *ext.Expr[natSet], xIn, holds Fact) {
				a.Show("R at x by the law, its guard the resident membership", By(holds.At(x), xIn))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A goal spelled with a projection, `zz_r_carrier(zz_mk_r(c)) = c`, is
// closed by a cited instance that spells it computed, `c = c` (the #1455
// shape): the refuter, which reads no record equation, cannot close it;
// the rung matches the two in its reading and reads the leaf before the
// assumption step. A Have claim spelled with the projection stands
// resident as spelled, and is closed the same way.
func TestRecordReading_ConclusionSpelledWithAProjectionMeetsTheComputedInstance(t *testing.T) {
	ctx := recordTestScript(t)
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀S:((num → bool) → bool). ∀P:(num → bool). ∀c:(num → bool). ∀x:num. S(c) ⇒ P(x) ∧ zz_r_carrier(zz_mk_r(c)) = c",
			func(a *Argument, S *ext.Expr[ext.Set[natSet]], P, c *ext.Expr[natSet], x *ext.Expr[ext.Nat], sc Fact) {
				parts := a.Conjuncts(a.Simplified(GroupPremises(sc, At(depName("zz_r_law"), S, P, c, x))), "P at x", "the carrier of the record is c", "x lies in c")
				inCarrier := a.Have("x lies in the carrier of the record", "x ∈ zz_r_carrier(zz_mk_r(c))", By(parts[2]))
				content, _ := inCarrier.BoundContent()
				require.Equal(t, "x₀ ∈ zz_r_carrier(zz_mk_r(c₀))", ext.PrintTerm(content), "the claim stands as spelled")
				a.Show("P at x, and the carrier, as spelled, is c", By(parts[0], parts[1]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The stage's record reading (conditionOpts.readRecords): the leaf a
// closer is handed has every record projection of a packed value read as
// the part, as the rung reads it, and the author's spelling stands in
// the hypothesis.
func TestRecordReading_TheStageReadsTheLeaf(t *testing.T) {
	ctx := recordTestScript(t)
	goal := ctx.MakePropText("∀c d:(num → bool). ∀x:num. ∀R:(num → bool). " +
		"(x ∈ zz_r_carrier(zz_mk_r(c)) ∨ x ∈ d) ⇒ R(x)")
	conditioned := func(opts conditionOpts) Prop {
		root := CreateGoalStack(goal)
		c := &conditioner{env: ctx.Env, ctx: t.Context(), s4: &byS4State{}}
		c.conditionLeaf(root, opts)
		leaf := byWorkingLeaf(root, nil)
		require.NotNil(t, leaf)
		return leaf.Goal
	}
	spelled := conditioned(conditionOpts{readMemberships: true})
	require.Equal(t, 1, spelled.NumHyps())
	require.Equal(t, "(x₀ ∈ zz_r_carrier(zz_mk_r(c₀))) ∨ (x₀ ∈ d₀)", ext.PrintTerm(spelled.Hyp(0)),
		"without the reading the hypothesis reaches the closer as spelled")
	read := conditioned(conditionOpts{readMemberships: true, readRecords: true})
	require.Equal(t, 1, read.NumHyps())
	require.Equal(t, "(x₀ ∈ c₀) ∨ (x₀ ∈ d₀)", ext.PrintTerm(read.Hyp(0)), "the projection is read as the part")
	// A part that spells a set-builder is read on as a membership is.
	if ctx.ParseScope.ConstMetas == nil {
		ctx.ParseScope.ConstMetas = map[string]core.ConstTermMeta{}
	}
	for name, meta := range setBuilderVocabulary() {
		ctx.ParseScope.ConstMetas[name] = meta
	}
	nested := ctx.MakePropText("∀c:(num → bool). ∀x:num. ∀R:(num → bool). " +
		"(x ∈ zz_r_carrier(zz_mk_r({y:num | y ∈ c ∧ R(y)})) ∨ R(x)) ⇒ R(x)")
	root := CreateGoalStack(nested)
	c := &conditioner{env: ctx.Env, ctx: t.Context(), s4: &byS4State{}}
	c.conditionLeaf(root, conditionOpts{readMemberships: true, readRecords: true})
	leaf := byWorkingLeaf(root, nil)
	require.NotNil(t, leaf)
	require.Equal(t, "((x₀ ∈ c₀) ∧ R₀(x₀)) ∨ R₀(x₀)", ext.PrintTerm(leaf.Goal.Hyp(0)),
		"the two readings are taken to a fixpoint")
}

// Each leaf below is one the rung does not close — a hypothesis that is
// a disjunction is no law it applies, a disjunctive goal and a sum are no
// identity — so the close is the closer's, on the leaf as read.

// The refuter resolves `x ∈ zz_r_carrier(zz_mk_r(c))` against a law's
// `y ∈ c`.
func TestRecordReading_TheRefuterReadsTheLeaf(t *testing.T) {
	ctx := recordTestScript(t)
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀c d:(num → bool). ∀x:num. ∀R:(num → bool). "+
			"(x ∈ zz_r_carrier(zz_mk_r(c)) ∨ x ∈ d) ⇒ (∀y. y ∈ c ⇒ R(y)) ⇒ (∀y. y ∈ d ⇒ R(y)) ⇒ R(x)",
			func(a *Argument, c, d *ext.Expr[natSet], x *ext.Expr[ext.Nat], R *ext.Expr[natSet], either, onC, onD Fact) {
				content, bound := either.BoundContent()
				require.True(t, bound)
				require.Equal(t, "(x₀ ∈ zz_r_carrier(zz_mk_r(c₀))) ∨ (x₀ ∈ d₀)", ext.PrintTerm(content), "the hypothesis stands as spelled")
				a.Show("R at x, whichever set x lies in", By(either, onC, onD))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The set driver closes a disjunctive goal whose membership spells the
// projection on the resident membership at the part.
func TestRecordReading_TheSetDriverReadsTheLeaf(t *testing.T) {
	ctx := recordTestScript(t)
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀c:(num → bool). ∀x:num. ∀P:(num → bool). "+
			"x ∈ c ⇒ P(x) ∨ x ∈ zz_r_carrier(zz_mk_r(c))",
			func(a *Argument, c *ext.Expr[natSet], x *ext.Expr[ext.Nat], P *ext.Expr[natSet], inC Fact) {
				a.Show("x is in the carrier, read at the part", BySets(inC))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The arithmetic closer adds a part: `zz_n_val(zz_mk_n(k))` is k.
func TestRecordReading_TheArithmeticCloserReadsTheLeaf(t *testing.T) {
	env := makeStepTestEnv()
	recT := core.MakeFun(ext.NumType, ext.NumType)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_mk_n", core.MakeFun(ext.NumType, recT)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_n_val", core.MakeFun(recT, ext.NumType)))
	ctx := NewScript(env)
	ctx.Const("zz_mk_n", core.MakeFun(ext.NumType, recT))
	ctx.Const("zz_n_val", core.MakeFun(recT, ext.NumType))
	projection := core.TestThm(ctx.MakePropText("∀k:num. zz_n_val(zz_mk_n(k)) = k").Conclusion())
	serveThm(ctx, "zz_n_val_mk", projection)
	tactic.InstallRecordNormal([]tactic.RecordEquation{{
		Head: "zz_n_val", Constructor: "zz_mk_n", Entry: "zz_n_val_mk", Statement: projection.AsProp(),
	}}, nil, func(string) *prop.PropWrapper { return prop.WrapProp(projection) })
	t.Cleanup(func() { tactic.InstallRecordNormal(nil, nil, nil) })
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀k m:num. m = k + 1 ⇒ zz_n_val(zz_mk_n(k)) + 1 = m",
			func(a *Argument, k, m *ext.Expr[ext.Nat], eq Fact) {
				a.Show("the value of the record is k", ByArith(eq))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A conditional rule whose guard stands at the part, `y ∈ c`, fires in
// Simp where the goal holds the guard spelled with a projection of a
// packed value, `x ∈ zz_r_carrier(zz_mk_r(c))`, whole or as a conjunct
// of one hypothesis: the discharge reads both sides through the record
// equations, as a closer's leaf is read, and the hypothesis keeps its
// spelling. Unread, the guard met no hypothesis and the rule did not
// fire, so the goal reached the close unrewritten.
func TestRecordReading_SimpGuardMeetsAResidentProjection(t *testing.T) {
	ctx := recordTestScript(t)
	const whole = "∀c:(num → bool). ∀f g:(num → num). ∀P:(num → bool). ∀x:num. " +
		"x ∈ zz_r_carrier(zz_mk_r(c)) ⇒ (∀y:num. y ∈ c ⇒ f(y) = g(y)) ⇒ P(g(x)) ⇒ P(f(x))"
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(whole,
			func(a *Argument, c *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], x *ext.Expr[ext.Nat], xIn, rule, atG Fact) {
				content, bound := xIn.BoundContent()
				require.True(t, bound)
				require.Equal(t, "x₀ ∈ zz_r_carrier(zz_mk_r(c₀))", ext.PrintTerm(content), "the hypothesis stands as spelled")
				a.Show("f is g at x, the guard the resident membership", Simp(Fwd(rule)), By(atG))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	const conjunct = "∀c:(num → bool). ∀f g:(num → num). ∀P Q D:(num → bool). ∀x:num. " +
		"D(x) ⇒ (∀z:num. D(z) ⇒ z ∈ zz_r_carrier(zz_mk_r(c)) ∧ Q(z)) ⇒ (∀y:num. y ∈ c ⇒ f(y) = g(y)) ⇒ P(g(x)) ⇒ P(f(x))"
	sec = provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(conjunct,
			func(a *Argument, c *ext.Expr[natSet], f, g *ext.Expr[natFun], P, Q, D *ext.Expr[natSet], x *ext.Expr[ext.Nat], atX, datum, rule, atG Fact) {
				a.Have("the datum at x", "x ∈ zz_r_carrier(zz_mk_r(c)) ∧ Q(x)", By(atX, datum.At(x)))
				a.Show("f is g at x, the guard a conjunct of the resident datum", Simp(Fwd(rule)), By(atG))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}
