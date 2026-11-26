package unify

// Tests for TermMatch — the deterministic one-sided term_match. Each positive
// case is checked by ROUND-TRIP: σ recovered from the match, applied to the
// pattern and β-normalized, must α-equal the target. That avoids pinning a
// particular (η-variant) witness shape and directly asserts "σ(pattern) = target".

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func inst(names ...TermName) TermNameSet {
	s := TermNameSet{}
	for _, n := range names {
		s.Add(n)
	}
	return s
}

// assertMatchRoundTrips runs TermMatch and verifies σ(pattern) β= target.
func assertMatchRoundTrips(t *testing.T, pattern, target Term, instantiable TermNameSet) MatchBindings {
	t.Helper()
	b, ok := TermMatch(pattern, target, instantiable)
	require.True(t, ok, "expected a match")
	got := ext.BetaCollapse(t.Context(), pattern.Substitute(BindingSubsts(b)...))
	want := ext.BetaCollapse(t.Context(), target)
	assert.True(t, got.AlphaEquals(want),
		"σ(pattern) β-normal = %s\n          want target = %s", got, want)
	return b
}

func assertNoMatch(t *testing.T, pattern, target Term, instantiable TermNameSet) {
	t.Helper()
	_, ok := TermMatch(pattern, target, instantiable)
	assert.False(t, ok, "expected no match")
}

// Bare flexible var matches any term of its type: P ≐ t ⇒ P ↦ t.
func TestTermMatch_BareVar(t *testing.T) {
	P := Var("P", TypeA)
	c := Var("c", TypeA) // rigid (not instantiable)
	b := assertMatchRoundTrips(t, P, c, inst("P"))
	assert.True(t, b["P"].AlphaEquals(c))
}

// Miller pattern under a binder: λx. P(x) ≐ λx. f(x) ⇒ P ↦ λx.f(x) (≡ f).
func TestTermMatch_MillerUnderBinder(t *testing.T) {
	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeA))
	pattern := x.To(P.Apply(x))
	target := x.To(f.Apply(x))
	assertMatchRoundTrips(t, pattern, target, inst("P"))
}

// abstract-all: P applied to a COMPOUND arg. P(mk(y)) ≐ eq(mk(y), c)
// ⇒ P ↦ λz. eq(z, c). The argument mk(y) is abstracted at every occurrence.
func TestTermMatch_AbstractAll(t *testing.T) {
	y := Var("y", TypeA)
	mk := Var("mk", MakeFun(TypeA, TypeA))
	eq := Var("eq", MakeFun(TypeA, TypeA, TypeBool))
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	pattern := y.To(P.Apply(mk.Apply(y)))
	target := y.To(eq.Apply(mk.Apply(y), c))
	assertMatchRoundTrips(t, pattern, target, inst("P"))
}

// THE property that defeated HO unification (the rewrite-executor bug):
// abstract-all must abstract ONLY the arg, leaving a DISTRACTOR subterm (here
// the free var K, same shape `mk(K)`) intact even when it is structurally
// similar to the abstracted `mk(y)`.
//
//	λy. P(mk(y))  ≐  λy. eq(mk(K), mk(y))   ⇒  P ↦ λz. eq(mk(K), z)
//
// (In the real bug the distractor was `mk(x)` where x is an OUTER binder; for
// the matcher's abstract-all that is the same as a free distractor — only the
// arg `mk(y)` is abstracted. Using a free K here keeps the round-trip free of
// the binder-alignment renaming that an outer-binder distractor introduces.)
func TestTermMatch_AbstractAll_WithDistractor(t *testing.T) {
	y := Var("y", TypeA)
	K := Var("K", TypeA)
	mk := Var("mk", MakeFun(TypeA, TypeA))
	eq := Var("eq", MakeFun(TypeA, TypeA, TypeBool))
	P := Var("P", MakeFun(TypeA, TypeBool))
	pattern := y.To(P.Apply(mk.Apply(y)))
	target := y.To(eq.Apply(mk.Apply(K), mk.Apply(y)))
	b := assertMatchRoundTrips(t, pattern, target, inst("P"))
	// The witness must still mention the distractor mk(K) (not be abstracted away).
	assert.True(t, b["P"].HasFreeName("K"), "abstract-all wrongly abstracted the distractor K")
}

// abstract-all requires closed args w.r.t. all rule vars. A not-yet-bound flex
// var nested inside P's arg would require solving a flex-flex shape, so reject.
func TestTermMatch_AbstractAll_RejectsUnboundNestedFlex(t *testing.T) {
	a := Var("a", TypeA)
	Q := Var("Q", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	pattern := P.Apply(Q.Apply(a))
	target := P.Apply(Q.Apply(a))
	assertNoMatch(t, pattern, target, inst("P", "Q"))
}

// Consistency: a flex var occurring twice must get the SAME witness — succeeds
// when the two sites agree, fails when they don't.
func TestTermMatch_RepeatedVar_Consistent(t *testing.T) {
	and := Var("and", MakeFun(TypeBool, TypeBool, TypeBool))
	c := Var("c", TypeBool)
	P := Var("P", TypeBool)
	// and(P, P) ≐ and(c, c) ⇒ P ↦ c.
	assertMatchRoundTrips(t, and.Apply(P, P), and.Apply(c, c), inst("P"))
}

func TestTermMatch_RepeatedVar_Inconsistent(t *testing.T) {
	and := Var("and", MakeFun(TypeBool, TypeBool, TypeBool))
	c := Var("c", TypeBool)
	d := Var("d", TypeBool)
	P := Var("P", TypeBool)
	// and(P, P) ≐ and(c, d): P would have to be both c and d → no match.
	assertNoMatch(t, and.Apply(P, P), and.Apply(c, d), inst("P"))
}

// A vacuous abstract-all (the arg does NOT occur in the target) is rejected —
// otherwise P(c) ≐ d would match with P ↦ λ_.d, a wildcard.
func TestTermMatch_VacuousAbstractAll_Rejected(t *testing.T) {
	mk := Var("mk", MakeFun(TypeA, TypeA))
	a := Var("a", TypeA)
	d := Var("d", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	assertNoMatch(t, P.Apply(mk.Apply(a)), d, inst("P"))
}

// Rigid head mismatch fails (different constants/vars on the rigid side).
func TestTermMatch_RigidMismatch(t *testing.T) {
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))
	a := Var("a", TypeA)
	assertNoMatch(t, f.Apply(a), g.Apply(a), inst()) // no flex vars at all
}

// Type mismatch fails immediately.
func TestTermMatch_TypeMismatch(t *testing.T) {
	P := Var("P", TypeA)
	c := Var("c", TypeBool)
	assertNoMatch(t, P, c, inst("P"))
}

// First-order approximation at a target with MORE arguments than the
// pattern spells: the flexible head binds to the target's head applied
// to the leading arguments the pattern does not have — Lean's
// flex-rigid fallback, `?f ?x ?y =?= g a u v` at ?f := g a. A target
// with fewer arguments than the pattern is no match.
func TestTermMatchApprox_FlexHeadAtAPartialApplication(t *testing.T) {
	num := ext.NumType
	g := Var("g", MakeFun(num, MakeFun(num, MakeFun(num, num)))) // rigid
	f := Var("f", MakeFun(num, MakeFun(num, num)))
	x, y := Var("x", num), Var("y", num)
	a, u, v := Var("a", num), Var("u", num), Var("v", num)
	pattern := f.Apply(x, y)
	target := g.Apply(a, u, v)

	b, ok := TermMatchApprox(pattern, target, inst("f", "x", "y"))
	require.True(t, ok, "the head binds to the partial application")
	require.True(t, b["f"].AlphaEquals(g.Apply(a)), "f := g(a), got %s", ext.PrintTerm(b["f"]))
	require.True(t, b["x"].AlphaEquals(u))
	require.True(t, b["y"].AlphaEquals(v))

	_, ok = TermMatch(pattern, target, inst("f", "x", "y"))
	require.False(t, ok, "the plain matcher takes no approximation")

	// Fewer arguments than the pattern: nothing to bind the head to.
	h := Var("h", MakeFun(num, num))
	_, ok = TermMatchApprox(pattern, h.Apply(a), inst("f", "x", "y"))
	require.False(t, ok)
}
