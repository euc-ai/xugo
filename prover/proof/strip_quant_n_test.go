package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// TestStripQuantN_StripsExactlyN: on ⊢ ∀x.∀y.∀z. q(x,y,z),
// StripQuantN(2) Skolemizes x, y and leaves ∀z quantified.
func TestStripQuantN_StripsExactlyN(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	x0 := Var("x_0", TypeA) // Skolem mints
	y0 := Var("y_0", TypeA)
	q := Var("q", core.MakeFun(TypeA, core.MakeFun(TypeA, core.MakeFun(TypeA, core.TypeBool()))))

	sec := ctx.Section(prop.MakeProp(
		ext.ForAll(x)(ext.ForAll(y)(ext.ForAll(z)(q.Apply(x, y, z))))))
	sec.Do(StripQuantN(2))

	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	want := ext.ForAll(z)(q.Apply(x0, y0, z))
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want),
		"StripQuantN(2) must leave the inner ∀ intact:\n  want %s\n  got  %s",
		ext.PrintTerm(want), prop.PrintProp(leaves[0].Goal))
}

// TestStripQuantN_FullPrefixMatchesStripQuant: StripQuantN(k) with k =
// the full ∀-prefix depth lands verbatim on the goal StripQuant()
// produces — the name-compatibility contract, at the Step layer.
func TestStripQuantN_FullPrefixMatchesStripQuant(t *testing.T) {
	build := func(bounded bool) Term {
		ctx := NewScript(makeStepTestEnv())
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		q := Var("q", core.MakeFun(TypeA, core.MakeFun(TypeA, core.TypeBool())))
		sec := ctx.Section(prop.MakeProp(ext.ForAll(x)(ext.ForAll(y)(q.Apply(x, y)))))
		if bounded {
			sec.Do(StripQuantN(2))
		} else {
			sec.Do(StripQuant())
		}
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		return leaves[0].Goal.Conclusion()
	}
	full, bounded := build(false), build(true)
	require.True(t, bounded.Equals(full),
		"full-depth StripQuantN must mint the same Skolem names as StripQuant:\n  full    %s\n  bounded %s",
		ext.PrintTerm(full), ext.PrintTerm(bounded))
}

// TestStripQuantN_TooFewBindersPanics: the up-front binder count check
// panics naming the actual conclusion.
func TestStripQuantN_TooFewBindersPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	p := Var("p", core.MakeFun(TypeA, core.TypeBool()))

	sec := ctx.Section(prop.MakeProp(ext.ForAll(x)(p.Apply(x))))
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected panic on too-few leading ∀s")
		require.Contains(t, fmt.Sprint(r), "only 1 leading ∀-binder")
		require.Contains(t, fmt.Sprint(r), "p(x)",
			"panic must name the actual conclusion")
	}()
	sec.Do(StripQuantN(2))
	t.Fatal("expected panic")
}

// TestStripQuantN_NonPositivePanics: n < 1 is a caller bug, loudly.
func TestStripQuantN_NonPositivePanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	x := Var("x", TypeA)
	p := Var("p", core.MakeFun(TypeA, core.TypeBool()))

	sec := ctx.Section(prop.MakeProp(ext.ForAll(x)(p.Apply(x))))
	require.PanicsWithValue(t, "StripQuantN: n must be ≥ 1, got 0", func() {
		sec.Do(StripQuantN(0))
	})
}

// TestUseLemmaFlipped_TreeIdentity: UseLemmaFlipped(dep, symDep)
// desugars to EXACTLY UseLemma(dep), UseLemma(symDep), CnfRefute() —
// same ministeps on the same goals (describeTree preorder identity)
// and the same proved state.
//
// The shape mirrors the of_num_add/of_num_mul flip-tail: the goal is
// the dep fact with its (opaque-relation) sides flipped; dep installs
// the fact in its own orientation, symDep the relation's symmetry law,
// and the refute composes them.
func TestUseLemmaFlipped_TreeIdentity(t *testing.T) {
	build := func(useSugar bool) *GoalStackNode {
		env := makeStepTestEnv()
		ctx := NewScript(env)
		// Opaque consts — free vars would let the lemma tactic unify
		// dep's s(a,b) with the flipped goal directly, skipping the
		// symmetry composition the idiom exists for.
		relTy := core.MakeFun(TypeA, core.MakeFun(TypeA, core.TypeBool()))
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("s_fl", relTy))
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("a_fl", TypeA))
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("b_fl", TypeA))
		s := ctx.Const("s_fl", relTy)
		a := ctx.Const("a_fl", TypeA)
		b := ctx.Const("b_fl", TypeA)
		x := Var("x", TypeA)
		y := Var("y", TypeA)

		// dep: ⊢ s(a, b); symDep, in clause form so the install does not
		// auto-close the goal: ⊢ ∀x y. ¬s(x,y) ∨ s(y,x).
		// TestThm is acceptable inside _test.go only.
		dep := prop.WrapProp(core.TestThm(s.Apply(a, b).Core()))
		symDep := prop.WrapProp(core.TestThm(
			ext.ForAll(x)(ext.ForAll(y)(ext.Not(s.Apply(x, y)).Or(s.Apply(y, x)))).Core()))

		// Goal: ⊢ s(b, a) — dep read right-to-left.
		sec := ctx.Section(prop.MakeProp(s.Apply(b, a).Core()))
		if useSugar {
			sec.Do(UseLemmaFlipped(dep, symDep))
		} else {
			sec.Do(Chain(UseLemma(dep), UseLemma(symDep), CnfRefute()))
		}
		return sec
	}
	raw, sugar := build(false), build(true)
	require.True(t, raw.Proved(), "hand-written 3-chain must prove")
	require.True(t, sugar.Proved(), "UseLemmaFlipped must prove")
	require.Equal(t, describeTree(raw), describeTree(sugar),
		"UseLemmaFlipped must desugar tree-identically to UseLemma+UseLemma+CnfRefute")
}
