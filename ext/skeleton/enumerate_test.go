package skeleton

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// boundContains reports whether `it.BoundVars` contains all of `wants`.
func boundContains(it IndexedTerm, wants ...core.VarTerm) bool {
	for _, v := range wants {
		if !it.IsBound(v) {
			return false
		}
	}
	return true
}

// MatchingPoints does NOT descend into AbsTerm bodies — a const-headed
// subterm sitting inside `λx. ...` is invisible to the standard walk.
// MatchingPointsUnderLambda DOES descend, with the under-λ anchor
// carrying empty BoundVars (no slot tracking across λ).
//
// Test shape: ∀f. f(λx:A. c(x))
//   - Standard MatchingPoints: walks past ∀f, descends into the
//     application f(λx. c(x)). Const head `c` lives under λ —
//     not emitted. Only the application itself might be emitted, but
//     its head is a Var (`f`), not a Const — so emit filters it out.
//     Expected: 0 anchors.
//   - MatchingPointsUnderLambda: also descends into `λx. c(x)`'s body,
//     emits `c(x)`. Expected: 1 anchor.
func TestMatchingPoints_UnderLambdaVariantIncludesUnderLambdaAnchors(t *testing.T) {
	cMeta := core.MakeConstMeta("c", core.MakeFun(core.TypeA(), core.TypeBool()))
	cTerm := core.MakeConstTerm(cMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	x := core.Var("x", core.TypeA())
	lambda := core.Abs(x, core.Apply(cTerm, x)) // λx:A. c(x)
	f := core.Var("f", core.MakeFun(core.MakeFun(core.TypeA(), core.TypeBool()), core.TypeBool()))
	body := core.Apply(f, lambda) // f(λx:A. c(x))
	p := core.MakeProp(ext.ForAll(f)(ext.WrapTerm(body)).Core())

	// Standard variant: no const head reachable.
	standard := MatchingPoints(p)
	for _, it := range standard {
		head, _ := ext.MatchesApply(it.Term)
		if hc, ok := head.AsConst(); ok {
			assert.NotEqual(t, core.TermName("c"), hc.Name(),
				"MatchingPoints must skip under-λ const heads (standard variant)")
		}
	}

	// Under-λ variant: c(x) must be emitted.
	underLambda := MatchingPointsUnderLambda(p)
	foundC := false
	for _, it := range underLambda {
		head, _ := ext.MatchesApply(it.Term)
		if hc, ok := head.AsConst(); ok && hc.Name() == core.TermName("c") {
			foundC = true
			assert.Empty(t, it.BoundVars,
				"under-λ anchor must carry empty BoundVars (no slot tracking across λ)")
		}
	}
	assert.True(t, foundC,
		"MatchingPointsUnderLambda must emit the under-λ const-headed subterm c(x)")
}

// Sanity: MatchingPointsUnderLambda is a strict superset of MatchingPoints
// on a prop with no λ-bodies — every anchor produced by the standard
// walk is also produced by the under-λ walk, with the same BoundVars.
func TestMatchingPoints_UnderLambdaVariantSupersetsStandard(t *testing.T) {
	// ∀x. P(x) ∧ Q(x) — no λ-bodies; both variants should agree.
	x := ext.Var("x", ext.TypeA)
	P := ext.Var("P", ext.MakeFun(ext.TypeA, ext.TypeBool))
	Q := ext.Var("Q", ext.MakeFun(ext.TypeA, ext.TypeBool))
	body := P.Apply(x).And(Q.Apply(x))
	p := core.MakeProp(ext.ForAll(x)(body).Core())

	std := MatchingPoints(p)
	under := MatchingPointsUnderLambda(p)
	stdKeys := make(map[core.TermKey]struct{}, len(std))
	for _, it := range std {
		stdKeys[it.Term.AlphaKey()] = struct{}{}
	}
	for k := range stdKeys {
		found := false
		for _, it := range under {
			if it.Term.AlphaKey() == k {
				found = true
				break
			}
		}
		assert.True(t, found, "under-λ variant should be a superset on λ-free input")
	}
}
