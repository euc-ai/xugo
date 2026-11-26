package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// TestHypHandle_BindAndGround: bind an antecedent ∀-hyp at StripImp,
// ground it by handle — the index is resolved, not spelled.
//
//	(∀x. p(x)) ⇒ p(c)
func TestHypHandle_BindAndGround(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	p := Var("p", core.MakeFun(TypeA, core.TypeBool()))
	c := Var("c", TypeA)
	x := Var("x", TypeA)

	sec := ctx.Section(prop.MakeProp(ext.ForAll(x)(p.Apply(x)).Imply(p.Apply(c))))
	allP := NewHypHandle("allP")
	sec.Do(Chain(
		allP.From(StripImp()),
		allP.Ground(c),
		Assumption(),
	))
	require.True(t, sec.Proved())
}

// TestHypHandle_TracksThroughSkolemization: the handle's hyp is an
// ∃-hyp that StripQuant Skolemizes between bind and use — the exact
// case content addressing (GroundHyp against the install cert) cannot
// reach. The tracker follows the 1-removed/1-added diff.
//
//	(∃b. ∀x. q(b, x)) ⇒ ∃y. q(y, c)
func TestHypHandle_TracksThroughSkolemization(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	q := Var("q", core.MakeFun(TypeA, core.MakeFun(TypeA, core.TypeBool())))
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	x := Var("x", TypeA)
	y := Var("y", TypeA)

	sec := ctx.Section(prop.MakeProp(
		ext.Exists(b)(ext.ForAll(x)(q.Apply(b, x))).Imply(
			ext.Exists(y)(q.Apply(y, c)))))
	bound := NewHypHandle("bound")
	sec.Do(Chain(
		bound.From(StripImp()),     // hyp: ∃b.∀x.q(b,x)
		StripQuant(),               // hyp: ∀x.q(b₀,x) — Skolemized as b_0; handle follows
		bound.Ground(c),            // hyp: q(b₀,c)
		Witness(Var("b_0", TypeA)), // goal: q(b₀,c)
		Assumption(),
	))
	require.True(t, sec.Proved())
}

// TestHypHandle_Clear: two bound antecedents; Clear drops one by
// handle, the other closes the goal. Then verify use-after-consume
// fails loudly.
//
//	P ⇒ (Q ⇒ P)
func TestHypHandle_Clear(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	P := Var("P", core.TypeBool())
	Q := Var("Q", core.TypeBool())

	sec := ctx.Section(prop.MakeProp(P.Imply(Q.Imply(P))))
	hp := NewHypHandle("hp")
	hq := NewHypHandle("hq")
	sec.Do(Chain(
		hp.From(StripImp()),
		hq.From(StripImp()),
		Clear(hq),
	))
	require.Equal(t, 1, sec.unsolvedLeaf(0).Goal.NumHyps())

	// hq's hyp was consumed by the ClearHyps step — using it must fail
	// loudly, naming the consuming step.
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected panic on use-after-consume")
		require.Contains(t, fmt.Sprint(r), "consumed")
	}()
	sec.Do(hq.Ground())
	t.Fatal("expected panic on use-after-consume")
}

// TestHypHandle_NamedHave: `h.From(Have(...))` inside Deduce binds the
// handle to the asserted fact's hyp on the residual branch — verified
// by Clear(h) as a later item (the goal then re-derives the fact).
//
//	hyps P, P⇒Q, Q⇒R ⊢ R
func TestHypHandle_NamedHave(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	P := Var("P", core.TypeBool())
	Q := Var("Q", core.TypeBool())
	R := Var("R", core.TypeBool())

	sec := ctx.Section(prop.MakeProp(R, P, P.Imply(Q), Q.Imply(R)))
	nHyps := sec.Goal.NumHyps()
	hQ := NewHypHandle("hQ")
	sec.Do(Deduce(
		hQ.From(Have("Q from P and P⇒Q", prop.MakeProp(Q), env.AutoExpand())),
		Clear(hQ), // resolves to the claim hyp — drops it again
		Show("R via Q⇒R (re-deriving Q)", env.AutoExpand()),
	))
	require.True(t, sec.Proved())
	// The residual branch saw the claim added and then cleared.
	require.Equal(t, nHyps, sec.children[1].children[0].Goal.NumHyps())
}

// TestHypHandle_FromResident: bind a ByCaseStep branch hypothesis by
// content — the true branch's Q and the false branch's ¬Q have no
// wrappable introducing action.
//
//	hyp P ⊢ P   (by case on Q, clearing the case hyp first in each branch)
func TestHypHandle_FromResident(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	P := Var("P", core.TypeBool())
	Q := Var("Q", core.TypeBool())

	sec := ctx.Section(prop.MakeProp(P, P))
	caseQ := NewHypHandle("caseQ")
	caseNotQ := NewHypHandle("caseNotQ")
	sec.Do(ctx.ByCaseStep(Q,
		MakeCase("true: drop the case hyp, close by assumption",
			caseQ.FromResident(Q),
			Clear(caseQ),
			Assumption(),
		),
		MakeCase("false: same via the negated case hyp",
			caseNotQ.FromResident(ext.Not(Q)),
			Clear(caseNotQ),
			Assumption(),
		),
	))
	require.True(t, sec.Proved())
}

// TestHypHandle_CiteSpecializeKeepAs: the keep-install nets source +
// instance; the two-handle variant binds both, verified by clearing
// them.
//
//	sec1: ⊢ ∀x. p(x) = p(x)    sec2: hyp S ⊢ R (left open — the test is
//	the binding + Clear; no p-atom in sec2 for the iff to fire on)
func TestHypHandle_CiteSpecializeKeepAs(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("pc_keepas_test", core.MakeFun(TypeA, core.TypeBool())))
	pc := ctx.Const("pc_keepas_test", core.MakeFun(TypeA, core.TypeBool()))
	c := Var("c", TypeA)
	x := Var("x", TypeA)
	R := Var("R", core.TypeBool())
	S := Var("S", core.TypeBool())

	sec1 := ctx.Section(prop.MakeProp(ext.ForAll(x)(pc.Apply(x).Eq(pc.Apply(x)))))
	sec1.Do(Chain(StripQuant(), Refl()))
	require.True(t, sec1.Proved())

	src := NewHypHandle("tautAll")
	inst := NewHypHandle("tautAtC")
	sec2 := ctx.Section(prop.MakeProp(R, S))
	sec2.Do(CiteSpecializeKeepAs(src, inst, sec1, c))
	require.Equal(t, 3, sec2.unsolvedLeaf(0).Goal.NumHyps())
	sec2.Do(Clear(src, inst))
	require.Equal(t, 1, sec2.unsolvedLeaf(0).Goal.NumHyps())
}

// TestWithSource_TreeIdentity: WithSource(src, install, body...) closes
// the same section that the hand-written three-line expansion
// (src.From(install), body..., Clear(src)) closes — same ministep
// sequence, same recorded pb, same final proved state.
//
// The shape: two antecedent hyps installed via StripImp; the outer
// wraps the WithSource form, the twin uses the raw expansion. Both
// prove (∀x. p(x)) ⇒ p(c) via bind-source / ground-instance / discard.
func TestWithSource_TreeIdentity(t *testing.T) {
	build := func(useSugar bool) *GoalStackNode {
		ctx := NewScript(makeStepTestEnv())
		p := Var("p", core.MakeFun(TypeA, core.TypeBool()))
		c := Var("c", TypeA)
		x := Var("x", TypeA)
		sec := ctx.Section(prop.MakeProp(ext.ForAll(x)(p.Apply(x)).Imply(p.Apply(c))))
		src := NewHypHandle("src")
		inst := NewHypHandle("inst")
		// Body nets one KEPT ground instance; the goal is closed by a
		// SEPARATE Assumption after Clear(src) fires — the shape real
		// slope usage exhibits (WithSource brackets install/use/clear of
		// a source; goal close happens after the block).
		body := []Action{inst.From(src.GroundKeep(c))}
		if useSugar {
			sec.Do(Chain(
				WithSource(src, StripImp(), body...),
				Assumption(),
			))
		} else {
			steps := make([]Action, 0, len(body)+3)
			steps = append(steps, src.From(StripImp()))
			steps = append(steps, body...)
			steps = append(steps, Clear(src))
			steps = append(steps, Assumption())
			sec.Do(Chain(steps...))
		}
		return sec
	}
	sugar, raw := build(true), build(false)
	require.True(t, sugar.Proved(), "sugar form must prove")
	require.True(t, raw.Proved(), "raw expansion must prove")
	// Tree-identity: WithSource compiles to Chain(src.From(install),
	// body..., Clear(src)), so the recorded ministep sequence at each
	// node in the proof tree matches the hand-written expansion. Walk
	// both trees preorder collecting StepDescription()s and compare.
	require.Equal(t, describeTree(raw), describeTree(sugar),
		"WithSource must desugar tree-identically to Chain(src.From(install), body..., Clear(src))")
}

// describeTree serializes a proof tree's ministep sequence for
// tree-identity comparison in tests. Preorder walk: each node's
// StepDescription() + children, one per line. Two trees returning
// equal strings have identical ministep structure.
func describeTree(n *GoalStackNode) string {
	var b []byte
	var walk func(node *GoalStackNode, depth int)
	walk = func(node *GoalStackNode, depth int) {
		for i := 0; i < depth; i++ {
			b = append(b, ' ')
		}
		b = append(b, node.StepDescription()...)
		b = append(b, '\n')
		for _, c := range node.Children() {
			walk(c, depth+1)
		}
	}
	walk(n, 0)
	return string(b)
}

// TestWithSource_UnclosedSourcePanicsAtClear: if body never binds any
// downstream handle so the source stays resident but then a body step
// mishandles it, the closing Clear catches nothing extra — but if the
// source itself was never actually bound (install action fails to net
// exactly one new hyp), From panics first. This test pins the "Clear
// on unbound source panics" contract inherited natively from Clear:
// pass a fresh handle to Clear via a WithSource whose install nets NO
// hyp (an already-closed leaf via Assumption in the install slot).
func TestWithSource_UnclosedSourcePanicsAtClear(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	P := Var("P", core.TypeBool())
	sec := ctx.Section(prop.MakeProp(P, P))
	src := NewHypHandle("src")
	// Install action is Assumption() — closes the leaf, nets no hyp.
	// src.From requires exactly-one-unsolved-leaf-with-one-new-hyp;
	// zero leaves triggers the loud panic.
	require.Panics(t, func() {
		sec.Do(WithSource(src, Assumption()))
	}, "WithSource with install that fails to bind src must panic loudly")
}

// TestHypHandle_ErrorModes: unbound use, double bind.
func TestHypHandle_ErrorModes(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	P := Var("P", core.TypeBool())
	Q := Var("Q", core.TypeBool())

	sec := ctx.Section(prop.MakeProp(P.Imply(Q.Imply(P))))

	unbound := NewHypHandle("unbound")
	require.Panics(t, func() { sec.Do(unbound.Ground()) })

	h := NewHypHandle("h")
	sec.Do(h.From(StripImp()))
	require.Panics(t, func() { sec.Do(h.From(StripImp())) })
}

// A handle lost across an Unfold is told the two narrower spellings —
// the definition entry as a Simp rule opens the goal alone, Unfolded
// opens one fact — since an Unfold's reach over every hypothesis is
// the step's contract.
func TestTrackHypThrough_UnfoldNamesTheGoalOnlySpellings(t *testing.T) {
	h1 := Var("h1", TypeBool)
	h2 := Var("h2", TypeBool)
	parent := &GoalStackNode{Goal: MakeProp(Var("g", TypeBool), h1, h2)}
	parent.miniStep = _DefExpandStep{constTerm: core.MakeConstTerm(core.MakeConstMeta("group_on", TypeBool), TypeBool)}
	child := &GoalStackNode{Goal: MakeProp(Var("g", TypeBool), Var("h3", TypeBool), Var("h4", TypeBool), Var("h5", TypeBool))}
	_, err := trackHypThrough(parent, child)
	require.Error(t, err)
	require.Contains(t, err.Error(), "2 removed, 3 added")
	require.Contains(t, err.Error(), "Simp(Fwd(<group_on's definition>))")
	require.Contains(t, err.Error(), "a.Unfolded(h, <group_on's definition>)")
	// Any other step keeps the plain repair.
	parent.miniStep = nil
	_, err = trackHypThrough(parent, child)
	require.Error(t, err)
	require.Contains(t, err.Error(), "use the handle before that step, or re-introduce the fact after it")
}
