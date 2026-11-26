// Round-trip tests for the function-space surface: `∘` composition.
// Same discipline as setops_test.go — (1) the new form parses; (2) it
// builds the same term as the applied `o(f, g)` spelling; (3) print →
// reparse round-trips; plus the meta-resolution precedence, which for
// `∘` runs through a hook the resolver walk would otherwise miss.
//
// One asymmetry with the set surface is worth stating, because it shapes
// every test here: the DSL does NOT seed `o` into the const scope by
// name. `o` is a one-letter identifier and a plausible binder, so a
// global seed would shadow a variable of that name; the surface meta is
// bound at the `∘` build site instead. Consequence: the applied spelling
// `o(f, g)` resolves only when the caller supplies the const — which is
// why the old-form comparisons below parse in a scope.
package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// composeScope supplies `o` the way a proof's ParseScope does,
// so the applied spelling `o(f, g)` resolves and can be compared against
// the `∘` sugar.
func composeScope() *ParseScope {
	return &ParseScope{ConstMetas: map[string]core.ConstTermMeta{"o": ComposeMeta}}
}

// assertComposeFormsAgree parses the `∘` form scope-less and the applied
// form in composeScope, and requires the two conclusions to be α-equal.
func assertComposeFormsAgree(t *testing.T, sugar, applied string) {
	t.Helper()
	sRes := ParsePropText(sugar)
	require.Empty(t, sRes.Errors,
		"sugar form %q failed to parse: %v", sugar, diagMessages(sRes.Errors))
	aRes := ParsePropTextInScope(applied, composeScope())
	require.Empty(t, aRes.Errors,
		"applied form %q failed to parse: %v", applied, diagMessages(aRes.Errors))
	assert.True(t, sRes.Prop.Conclusion().AlphaEquals(aRes.Prop.Conclusion()),
		"`∘` and `o(...)` must build α-equal terms; sugar=%s applied=%s",
		ext.FormatTermForParser(sRes.Prop.Conclusion()),
		ext.FormatTermForParser(aRes.Prop.Conclusion()))
}

func TestCompose_ParsesAsAppliedO(t *testing.T) {
	assertComposeFormsAgree(t,
		"∀f:(var:B → var:C).∀g:(var:A → var:B).∀x:var:A.((f ∘ g)(x) = f(g(x)))",
		"∀f:(var:B → var:C).∀g:(var:A → var:B).∀x:var:A.(o(f, g)(x) = f(g(x)))")
}

func TestCompose_RoundTrip(t *testing.T) {
	assertRoundTrip(t,
		"∀f:(var:B → var:C).∀g:(var:A → var:B).∀x:var:A.((f ∘ g)(x) = f(g(x)))")
}

// The printer's infix template has arity 2, so it fires on the partial
// application a composition IS. Pinned because the round-trip above
// would also pass if nothing were printed as `∘` at all.
func TestCompose_PrintsInfix(t *testing.T) {
	res := ParsePropText("∀f:(var:B → var:C).∀g:(var:A → var:B).((f ∘ g) = (f ∘ g))")
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	printed := prop.FormatPropForParser(res.Prop)
	assert.Contains(t, printed, "∘",
		"a two-argument `o` must print with the infix sugar; got %s", printed)
}

// Applied to a point, the composition keeps its sugar and the point
// rides outside: `(f ∘ g)(x)`. That is what makes the printed form
// scope-independent — the applied spelling `o(f, g, x)` reparses to a
// free variable wherever `o` is not declared, and the sugar never does.
func TestCompose_AppliedToPointKeepsSugar(t *testing.T) {
	res := ParsePropTextInScope(
		"∀f:(var:B → var:C).∀g:(var:A → var:B).∀x:var:A.(o(f, g, x) = f(g(x)))",
		composeScope())
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	printed := prop.FormatPropForParser(res.Prop)
	assert.Contains(t, printed, "(f ∘ g)(x)",
		"an over-applied `o` must keep the infix head; got %s", printed)
}

// `∘` binds tighter than `*`, so an arithmetic operator never captures a
// composition operand. num-valued functions are the only shape where the
// two layers can meet at all.
func TestCompose_PrecedenceTighterThanStar(t *testing.T) {
	assertComposeFormsAgree(t,
		"∀f g:(num → num).∀n:num.((f ∘ g)(n) * n = n)",
		"∀f g:(num → num).∀n:num.(o(f, g)(n) * n = n)")
}

// Right-associative, matching the mathematical convention.
func TestCompose_RightAssociative(t *testing.T) {
	assertComposeFormsAgree(t,
		"∀f:(var:C → var:D).∀g:(var:B → var:C).∀h:(var:A → var:B).∀x:var:A.((f ∘ g ∘ h)(x) = f(g(h(x))))",
		"∀f:(var:C → var:D).∀g:(var:B → var:C).∀h:(var:A → var:B).∀x:var:A.(o(f, o(g, h))(x) = f(g(h(x))))")
}

// A `∘` surface never mentions `o` as a source-text name, so without the
// walkResolverNames hook the resolver is never asked and the def-less
// surface meta wins by default — a term indistinguishable by name and
// instance type yet answering DefThm() nil, which is what breaks
// def_expand and trips the mixed-meta soundness assert. This is the
// regression test for that hook.
func TestCompose_ResolverMetaWinsOverSurface(t *testing.T) {
	registryMeta := core.MakeConstMeta("o",
		core.MakeFun(
			core.MakeFun(core.MakeVarType("?1"), core.MakeVarType("?2")),
			core.MakeFun(core.MakeVarType("?0"), core.MakeVarType("?1")),
			core.MakeVarType("?0"), core.MakeVarType("?2")))
	scope := &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if name == "o" {
				return registryMeta
			}
			return core.ConstTermMeta{}
		},
	}
	res := ParsePropTextInScope(
		"f : (var:B → var:C), g : (var:A → var:B) ⊢ (f ∘ g) = (f ∘ g)", scope)
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	assert.True(t, any(registryMeta) == any(findConstMeta(res.Prop, "o")), "`∘` must carry the resolver-supplied meta, not the surface fallback")
}

func TestCompose_BareParseFallsBackToSurfaceMeta(t *testing.T) {
	res := ParsePropText(
		"f : (var:B → var:C), g : (var:A → var:B) ⊢ (f ∘ g) = (f ∘ g)")
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	assert.True(t, any(ComposeMeta) == any(findConstMeta(res.Prop, "o")), "scope-less parse must still resolve ∘ via the DSL surface meta")
}

// A binder named `o` stays a variable. This holds for free here — the
// DSL never seeds `o` by name — and is pinned so a later decision to
// seed it would have to confront the shadowing question rather than
// discover it in a statement that silently changed meaning.
func TestCompose_BoundNameStaysAVariable(t *testing.T) {
	res := ParsePropText("∀o:num.(o = o)")
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	assert.True(t, findConstMeta(res.Prop, "o").IsZero(), "a binder named `o` must stay a variable, not resolve to the composition const")
}
