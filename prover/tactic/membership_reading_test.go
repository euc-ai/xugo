package tactic

import (
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

var (
	readingVocabOnce  sync.Once
	readingVocabMetas map[string]core.ConstTermMeta
)

// readingVocabulary is the three set-builder constants minted with their
// definitions, as the set_basic chapter defines them, for a parse scope
// that serves no library. Minted once: a constant's name is unique.
func readingVocabulary() map[string]core.ConstTermMeta {
	readingVocabOnce.Do(func() {
		A := core.TypeA()
		set := core.MakeFun(A, core.TypeBool())
		x, s := ext.Var("x", A), ext.Var("s", set)
		member := core.NewConstDef(x.To(s.To(s.Apply(x))), "set_member")
		q := ext.Var("q", set)
		comprehension := core.NewConstDef(q.To(q), "set_comprehension")
		v, condition, t := ext.Var("v", A), ext.Var("condition", core.TypeBool()), ext.Var("t", A)
		spec := core.NewConstDef(v.To(condition.To(t.To(condition.And(v.Eq(t))))), "comprehension_spec")
		readingVocabMetas = map[string]core.ConstTermMeta{
			"set_member":         member.Meta(),
			"set_comprehension":  comprehension.Meta(),
			"comprehension_spec": spec.Meta(),
		}
	})
	return readingVocabMetas
}

func readingScope(withDefinitions bool) *dsl.ParseScope {
	num := ext.NumType
	scope := &dsl.ParseScope{Vars: map[string]core.HolType{
		"P": core.MakeFun(num, core.TypeBool()),
		"K": core.MakeFun(num, core.TypeBool()),
		"R": core.MakeFun(num, core.MakeFun(num, core.TypeBool())),
		"a": num, "b": num, "n": num, "p": num,
		"S": core.MakeFun(core.MakeFun(num, core.TypeBool()), core.TypeBool()),
	}}
	if withDefinitions {
		scope.ConstMetas = readingVocabulary()
	}
	return scope
}

func readingTerm(t *testing.T, scope *dsl.ParseScope, text string) core.Term {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, scope)
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// The pure reading and the kernel's bridge agree: each shape reads to
// the condition at the point, the bridge's left side is the term and its
// right side the reading, up to βη.
func TestMembershipReading_ShapesAgree(t *testing.T) {
	scope := readingScope(true)
	ctx := t.Context()
	same := func(a, b core.Term) bool {
		return ext.BetaEtaNormalize(ctx, a).AlphaEquals(ext.BetaEtaNormalize(ctx, b))
	}
	for _, c := range []struct{ term, read string }{
		{"a ∈ {p:num | P(p)}", "P(a)"},
		{"a ∈ {i:num | i ≤ n}", "a ≤ n"},
		{"a ∈ {p:num | P(p) ∧ K(p)}", "P(a) ∧ K(a)"},
		// The point spells a free variable of the bound variable's name.
		{"p ∈ {p:num | R(p, n)}", "R(p, n)"},
		// Under a binder, and twice in one statement.
		{"∀x:num. x ∈ {p:num | P(p)} ⇒ f(x) ∈ {q:num | K(q)}", "∀x:num. P(x) ⇒ K(f(x))"},
		// Nested: the condition tests a membership of its own.
		{"a ∈ {p:num | p ∈ {q:num | K(q)} ∧ P(p)}", "K(a) ∧ P(a)"},
		// Not a point: a set of sets, the point a set-builder itself.
		{"{p:num | P(p)} ∈ {s:(num → bool) | a ∈ s}", "P(a)"},
		// The condition ends in an equation with the bound variable under
		// an ∃ of its own (a path component's `∃g. … ∧ g(1) = y`): the
		// bridge fuses on the point's equation, as the reading substitutes.
		{"a ∈ {p:num | ∃g:(num → num). P(g(0)) ∧ g(0) = n ∧ g(1) = p}", "∃g:(num → num). P(g(0)) ∧ g(0) = n ∧ g(1) = a"},
	} {
		scope.Vars["f"] = core.MakeFun(ext.NumType, ext.NumType)
		term, want := readingTerm(t, scope, c.term), readingTerm(t, scope, c.read)
		got := MembershipNormal(term)
		require.True(t, same(got, want), "%s reads as %s, want %s", c.term, ext.PrintTerm(got), c.read)
		bridge := MembershipBridge(term)
		require.NotNil(t, bridge, "%s has a bridge", c.term)
		require.Equal(t, 0, bridge.NumHyps())
		require.True(t, prop.Lhs(bridge).AlphaEquals(term), "the bridge's left side is the term")
		require.True(t, same(prop.Rhs(bridge), want), "the bridge's right side is the reading: %s", ext.PrintTerm(prop.Rhs(bridge)))
	}
}

// A point that is a λ-term, in a set of functions: substituting it for
// the binder makes redexes `(λx. …)(y)` inside the condition, which the
// pure reading β-collapses and the bridge's one-point fusion must carry
// across the kernel's raw instantiation. The shape of a map's membership
// in a funspace (`λx. COND(x ∈ u, f(x), d) ∈ {h | ∀x. x ∈ u ⇒ h(x) ∈ t}`).
func TestMembershipReading_LambdaPoint(t *testing.T) {
	scope := readingScope(true)
	scope.Vars["f"] = core.MakeFun(ext.NumType, ext.NumType)
	same := func(a, b core.Term) bool {
		return ext.BetaEtaNormalize(t.Context(), a).AlphaEquals(ext.BetaEtaNormalize(t.Context(), b))
	}
	for _, c := range []struct{ term, want string }{
		{"(λx:num. f(x) + a) ∈ {h:(num → num) | ∀x:num. P(h(x))}", "∀x:num. P(f(x) + a)"},
		{"(λx:num. f(x) + a) ∈ {h:(num → num) | (∀x:num. P(h(x))) ∧ K(h(b))}", "(∀x:num. P(f(x) + a)) ∧ K(f(b) + a)"},
		{"(λx:num. f(x) + a) ∈ {h:(num → num) | ∀x:num. P(h(h(x)))}", "∀x:num. P(f(f(x) + a) + a)"},
	} {
		term, want := readingTerm(t, scope, c.term), readingTerm(t, scope, c.want)
		got := MembershipNormal(term)
		require.True(t, same(got, want), "%s reads as %s, want %s", c.term, ext.PrintTerm(got), c.want)
		var bridge *prop.PropWrapper
		require.NotPanics(t, func() { bridge = MembershipBridge(term) }, "the bridge of %s", c.term)
		require.NotNil(t, bridge, "%s has a bridge", c.term)
		require.True(t, prop.Lhs(bridge).AlphaEquals(term))
		require.True(t, same(prop.Rhs(bridge), want), "the bridge's right side of %s: %s", c.term, ext.PrintTerm(prop.Rhs(bridge)))
	}
}

// The three-part form `x ∈ {t | x̄ | φ}` reads as `∃x̄. φ ∧ x = t`: one
// binder or several, a condition that is itself a membership, and a
// point that spells the binder's name, which the substitution renames
// apart. The pure reading and the kernel's bridge agree.
func TestMembershipReading_ThreePartForm(t *testing.T) {
	scope := readingScope(true)
	same := func(a, b core.Term) bool {
		return ext.BetaEtaNormalize(t.Context(), a).AlphaEquals(ext.BetaEtaNormalize(t.Context(), b))
	}
	for _, c := range []struct{ term, want string }{
		{"a ∈ {b + p:num | p:num | P(p)}", "∃p:num. P(p) ∧ a = b + p"},
		{"a ∈ {p + q:num | p:num, q:num | P(p) ∧ K(q)}", "∃p q:num. (P(p) ∧ K(q)) ∧ a = p + q"},
		{"a ∈ {b + p:num | p:num | p ∈ {q:num | K(q)}}", "∃p:num. K(p) ∧ a = b + p"},
		{"p ∈ {b + p:num | p:num | P(p)}", "∃p':num. P(p') ∧ p = b + p'"},
	} {
		term, want := readingTerm(t, scope, c.term), readingTerm(t, scope, c.want)
		got := MembershipNormal(term)
		require.True(t, same(got, want), "%s reads as %s, want %s", c.term, ext.PrintTerm(got), c.want)
		bridge := MembershipBridge(term)
		require.NotNil(t, bridge, "%s has a bridge", c.term)
		require.Equal(t, 0, bridge.NumHyps())
		require.True(t, prop.Lhs(bridge).AlphaEquals(term), "the bridge's left side is the term")
		require.True(t, same(prop.Rhs(bridge), want), "the bridge's right side is the reading: %s", ext.PrintTerm(prop.Rhs(bridge)))
	}
}

// What is not read: a term without a set-builder membership, a
// membership in a set that is no set-builder, a set-builder whose
// output mentions the hidden λ-binder, and a set-builder spelled with
// surface constants that carry no definition. The pure reading and the
// bridge decline together.
func TestMembershipReading_Declines(t *testing.T) {
	scope := readingScope(true)
	scope.Vars["s"] = core.MakeFun(ext.NumType, core.TypeBool())
	for _, text := range []string{
		"P(a) ∧ K(b)",
		"a ∈ s",
	} {
		term := readingTerm(t, scope, text)
		require.True(t, MembershipNormal(term).AlphaEquals(term), "%s is not read", text)
		require.Nil(t, MembershipBridge(term), "%s has no bridge", text)
	}
	surface := readingTerm(t, readingScope(false), "a ∈ {p:num | P(p)}")
	require.True(t, MembershipNormal(surface).AlphaEquals(surface), "a surface constant without a definition is not read")
	require.Nil(t, MembershipBridge(surface))
}

// The leaf read: the conclusion and every hypothesis in their membership
// normal form, one child, and the parent's proof reconstructed from the
// child's.
func TestMembershipReadTactic_ReadsTheLeaf(t *testing.T) {
	scope := readingScope(true)
	parse := func(text string) core.Term { return readingTerm(t, scope, text) }
	goal := MakeProp(parse("a ∈ {p:num | P(p)}"), parse("P(a)"), parse("b ∈ {p:num | K(p)}"), parse("K(b)"))
	sg := MembershipReadTactic(goal)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	child := sg.ChildGoal(0)
	require.True(t, child.Conclusion().AlphaEquals(parse("P(a)")))
	require.True(t, child.AnyHyp(parse("K(b)").AlphaEquals))
	require.False(t, child.AnyHyp(parse("b ∈ {p:num | K(p)}").AlphaEquals), "the hypothesis is read too")

	closed := AssumptionTactic(child)
	require.NotNil(t, closed, "the child closes by assumption")
	proved := sg.Reconstruct(closed.Reconstruct())
	require.True(t, proved.Conclusion().AlphaEquals(goal.Conclusion()))
	for h := range proved.HypIter() {
		require.True(t, goal.AnyHyp(h.AlphaEquals), "a hypothesis of the proof is the goal's: %s", ext.PrintTerm(h))
	}

	require.Nil(t, MembershipReadTactic(MakeProp(parse("P(a)"), parse("K(b)"))), "nothing to read")
}
