// membership_declared_test.go — a constant declared to read its
// membership (tactic.DeclareMembershipRead, the define door's
// MembershipRead) reads exactly as the set-builder it names, in every
// closer: By's conditioning reads `a ∈ c(n)` in the goal, in a
// hypothesis and under a binder, and the set driver opens it. Its
// undeclared twin, with the same definiens, stays closed: each
// positive case is run on the twin and refused there, so the reading
// is what closes it.
package proof

import (
	"fmt"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

var (
	declaredBelowOnce  sync.Once
	declaredBelowMetas map[string]core.ConstTermMeta
)

// declaredBelow mints `below = λn. {i:num | i < n}` twice: once declared
// to read its membership, once not.
func declaredBelow(t *testing.T) map[string]core.ConstTermMeta {
	t.Helper()
	declaredBelowOnce.Do(func() {
		res := dsl.ParseTermTextInScope("λn:num. {i:num | i < n}", nil, comprehensionScope(), nil)
		require.Empty(t, res.Errors, "%v", res.Errors)
		declared := core.NewConstDef(res.Term, "zz_declared_below")
		closed := core.NewConstDef(res.Term, "zz_closed_below")
		tactic.DeclareMembershipRead(declared)
		declaredBelowMetas = map[string]core.ConstTermMeta{
			"below":  declared.Meta(),
			"closed": closed.Meta(),
			// The declared constant as a parser's operator meta builds it,
			// with no definition on it (a text's `m .. n`).
			"bare": core.MakeConstMeta(declared.Name(), declared.Meta().AbsType()),
		}
	})
	return declaredBelowMetas
}

var (
	declaredSmallOnce  sync.Once
	declaredSmallMetas map[string]core.ConstTermMeta
)

// declaredSmall mints `small = {i:num | i < 3}`, a named set with no
// parameter, twice: once declared to read its membership, once not.
func declaredSmall(t *testing.T) map[string]core.ConstTermMeta {
	t.Helper()
	declaredSmallOnce.Do(func() {
		res := dsl.ParseTermTextInScope("{i:num | i < 3}", nil, comprehensionScope(), nil)
		require.Empty(t, res.Errors, "%v", res.Errors)
		declared := core.NewConstDef(res.Term, "zz_declared_small")
		closed := core.NewConstDef(res.Term, "zz_closed_small")
		tactic.DeclareMembershipRead(declared)
		declaredSmallMetas = map[string]core.ConstTermMeta{
			"small":  declared.Meta(),
			"closed": closed.Meta(),
		}
	})
	return declaredSmallMetas
}

// declaredSection opens a section on text, read with the set-builder
// vocabulary and the constant spelled `below` bound to which ("below",
// the declared one, "bare", the declared one under a meta that carries
// no definition, or "closed", its twin).
func declaredSection(t *testing.T, which, text string) (*Script, *GoalStackNode) {
	t.Helper()
	return sectionSpelling(t, "below", declaredBelow(t)[which], text)
}

// sectionSpelling opens a section on text, read with the set-builder
// vocabulary and the constant spelled name bound to meta.
func sectionSpelling(t *testing.T, name string, meta core.ConstTermMeta, text string) (*Script, *GoalStackNode) {
	t.Helper()
	scope := comprehensionScope()
	scope.ConstMetas = map[string]core.ConstTermMeta{name: meta}
	for name, meta := range setBuilderVocabulary() {
		scope.ConstMetas[name] = meta
	}
	res := dsl.ParsePropTextInScope(text, scope)
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	ctx := NewScript(makeStepTestEnv())
	for name, ty := range scope.Vars {
		ctx.ParseScope.Vars[name] = ty
	}
	if ctx.ParseScope.ConstMetas == nil {
		ctx.ParseScope.ConstMetas = map[string]core.ConstTermMeta{}
	}
	for name, meta := range scope.ConstMetas {
		ctx.ParseScope.ConstMetas[name] = meta
	}
	return ctx, ctx.Section(res.Prop)
}

// closesBoth runs body on the declared constant, where it must close,
// and on the twin, where it must be refused.
func closesBoth(t *testing.T, text string, body func(a *Argument)) {
	t.Helper()
	ctx, sec := declaredSection(t, "below", text)
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(body).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved(), "the declared constant: %s", text)

	ctx, sec = declaredSection(t, "closed", text)
	refusal := func() (r any) {
		defer func() { r = recover() }()
		Derive(body).applyAction(ctx, sec)
		return nil
	}()
	require.NotNil(t, refusal, "the undeclared twin closed %s — the reading is not what closes it", text)
	t.Logf("the twin's refusal: %.300v", refusal)
	require.Contains(t, fmt.Sprint(refusal), "zz_closed_below",
		"the twin is refused by a closer that met the membership, not by something else")
}

// A named set with no parameter is declared and read as one with
// parameters is: the constant itself is the set-builder it names. Each
// direction closes on the declared constant and is refused on its twin.
func TestMembershipDeclared_NoParameter(t *testing.T) {
	metas := declaredSmall(t)
	for text, body := range map[string]func(a *Argument){
		"a ∈ small ⇒ a < 3": func(a *Argument) {
			in := a.Assume()
			a.Show("the membership is the bound", By(in))
		},
		"a < 3 ⇒ a ∈ small": func(a *Argument) {
			lt := a.Assume()
			a.Show("the bound is the membership", By(lt))
		},
	} {
		ctx, sec := sectionSpelling(t, "small", metas["small"], text)
		ok := provesInHand(t, func() *GoalStackNode {
			Derive(body).applyAction(ctx, sec)
			return sec
		})
		require.True(t, ok != nil && sec.Proved(), "the declared constant: %s", text)

		ctx, sec = sectionSpelling(t, "small", metas["closed"], text)
		refusal := func() (r any) {
			defer func() { r = recover() }()
			Derive(body).applyAction(ctx, sec)
			return nil
		}()
		require.NotNil(t, refusal, "the undeclared twin closed %s — the reading is not what closes it", text)
		require.Contains(t, fmt.Sprint(refusal), "zz_closed_small",
			"the twin is refused by a closer that met the membership, not by something else")
	}
}

func TestMembershipDeclared_HypothesisRead(t *testing.T) {
	closesBoth(t, "a ∈ below(n) ⇒ a < n", func(a *Argument) {
		in := a.Assume()
		a.Show("the membership is the bound", By(in))
	})
}

func TestMembershipDeclared_GoalRead(t *testing.T) {
	closesBoth(t, "a < n ⇒ a ∈ below(n)", func(a *Argument) {
		lt := a.Assume()
		a.Show("the bound is the membership", By(lt))
	})
}

// A cited fact's guard under its binder reads as the condition, so the
// bound supplies it.
func TestMembershipDeclared_GuardUnderABinder(t *testing.T) {
	closesBoth(t, "(∀x:num. x ∈ below(n) ⇒ P(x)) ⇒ a < n ⇒ P(a)", func(a *Argument) {
		law := a.Assume()
		lt := a.Assume()
		a.Show("the law at a", By(law, lt))
	})
}

// The set driver opens the declared constant like the set-builder it
// names: an equation of sets read pointwise, the constant's side read
// through its definition.
func TestMembershipDeclared_SetDriver(t *testing.T) {
	closesBoth(t, "below(n) = {i:num | i < n ∧ i < n}", func(a *Argument) {
		a.Show("the same members", BySets())
	})
}

// The pure reading and the kernel's bridge agree on a declared
// constant, and its twin is its own normal form.
func TestMembershipDeclared_ReadingAndBridgeAgree(t *testing.T) {
	_, sec := declaredSection(t, "below", "a ∈ below(n) ∧ (∀x:num. x ∈ below(a) ⇒ P(x))")
	term := sec.Goal.Conclusion()
	read := tactic.MembershipNormal(term)
	_, want := declaredSection(t, "below", "a < n ∧ (∀x:num. x < a ⇒ P(x))")
	ctx := t.Context()
	require.True(t, ext.BetaEtaNormalize(ctx, read).AlphaEquals(ext.BetaEtaNormalize(ctx, want.Goal.Conclusion())),
		"read %s", ext.PrintTerm(read))
	bridge := tactic.MembershipBridge(term)
	require.NotNil(t, bridge)
	require.True(t, prop.Lhs(bridge).AlphaEquals(term))
	require.True(t, ext.BetaEtaNormalize(ctx, prop.Rhs(bridge)).AlphaEquals(ext.BetaEtaNormalize(ctx, read)))

	_, twin := declaredSection(t, "closed", "a ∈ below(n)")
	require.True(t, tactic.MembershipNormal(twin.Goal.Conclusion()).Equals(twin.Goal.Conclusion()),
		"the undeclared twin is read")
	require.Nil(t, tactic.MembershipBridge(twin.Goal.Conclusion()))
}

// The set driver's vocabulary holds the declared constant and not its
// twin.
func TestMembershipDeclared_InTheSetVocabulary(t *testing.T) {
	declaredBelow(t)
	require.Contains(t, StandardSetVocabulary(), "zz_declared_below")
	require.NotContains(t, StandardSetVocabulary(), "zz_closed_below")
}

// A definiens that is no set-builder is refused at the declaration.
func TestMembershipDeclared_RefusesANonSetBuilder(t *testing.T) {
	res := dsl.ParseTermTextInScope("λn:num. λi:num. i < n", nil, comprehensionScope(), nil)
	require.Empty(t, res.Errors, "%v", res.Errors)
	c := core.NewConstDef(res.Term, "zz_declared_lambda_below")
	_, err := tactic.MembershipReadArity(c)
	require.ErrorContains(t, err, "no set-builder")
	require.Panics(t, func() { tactic.DeclareMembershipRead(c) })
}

// An occurrence whose meta carries no definition — a text's `m .. n`,
// built from the parser's operator meta — is opened through the meta
// the declaration minted, by the reading and by the set driver alike.
func TestMembershipDeclared_OccurrenceWithoutItsDefinition(t *testing.T) {
	for _, c := range []struct {
		text string
		body func(a *Argument)
	}{
		{"a ∈ below(n) ⇒ a < n", func(a *Argument) {
			in := a.Assume()
			a.Show("the membership is the bound", By(in))
		}},
		{"(∀x:num. x ∈ below(n) ⇒ P(x)) ⇒ a < n ⇒ P(a)", func(a *Argument) {
			law := a.Assume()
			lt := a.Assume()
			a.Show("the law at a", By(law, lt))
		}},
		{"below(n) = {i:num | i < n ∧ i < n}", func(a *Argument) {
			a.Show("the same members", BySets())
		}},
	} {
		ctx, sec := declaredSection(t, "bare", c.text)
		require.True(t, sec.Goal.Conclusion().Equals(sec.Goal.Conclusion()))
		ok := provesInHand(t, func() *GoalStackNode {
			Derive(c.body).applyAction(ctx, sec)
			return sec
		})
		require.True(t, ok != nil && sec.Proved(), "the occurrence without its definition: %s", c.text)
	}
}
