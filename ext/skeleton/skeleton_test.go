package skeleton

import (
	"sort"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// boundOf builds the BoundVars set used by IndexedTerm.
func boundOf(vars ...core.VarTerm) map[core.TermKey]struct{} {
	if len(vars) == 0 {
		return nil
	}
	m := make(map[core.TermKey]struct{}, len(vars))
	for _, v := range vars {
		m[v.AlphaKey()] = struct{}{}
	}
	return m
}

func sortedPaths(paths []PathKey) []string {
	out := make([]string, len(paths))
	for i, p := range paths {
		out[i] = string(p)
	}
	sort.Strings(out)
	return out
}

func assertPaths(t *testing.T, got []PathKey, want ...string) {
	t.Helper()
	gotSorted := sortedPaths(got)
	wantSorted := append([]string(nil), want...)
	sort.Strings(wantSorted)
	assert.Equal(t, wantSorted, gotSorted)
}

// Case 1: f(x) where both f and x are free.
func TestExtractPaths_FreeFunFreeArg(t *testing.T) {
	f := ext.Var("f", ext.MakeFun(ext.TypeA, ext.TypeBool))
	x := ext.Var("x", ext.TypeA)
	fx := f.Apply(x)

	paths := ExtractPaths(IndexedTerm{Term: fx.Core()})
	assertPaths(t, paths, "HEAD:*F/1|ARG0|*F/0")
}

// Case 3: f(x, y) — two args, two distinct paths.
func TestExtractPaths_FreeFunTwoArgs(t *testing.T) {
	f := ext.Var("f", ext.MakeFun(ext.TypeA, ext.TypeA, ext.TypeBool))
	x := ext.Var("x", ext.TypeA)
	y := ext.Var("y", ext.TypeA)
	fxy := f.Apply(x, y)

	paths := ExtractPaths(IndexedTerm{Term: fxy.Core()})
	assertPaths(t, paths,
		"HEAD:*F/2|ARG0|*F/0",
		"HEAD:*F/2|ARG1|*F/0",
	)
}

// Case 4: suc(suc n) with n free.
func TestExtractPaths_NestedConstApp(t *testing.T) {
	suc := ext.TestConst("suc", ext.MakeFun(TypeInd, TypeInd))
	n := ext.Var("n", TypeInd)

	t1 := suc.Apply(suc.Apply(n))
	paths := ExtractPaths(IndexedTerm{Term: t1.Core()})
	assertPaths(t, paths,
		"HEAD:C:suc/1|ARG0|HEAD:C:suc/1|ARG0|*F/0",
	)
}

// Case 5: ∀P. P x — after stripping ∀P, the body P(x) has P bound and x
// free. The path should reflect HEAD:*B/1 for the bound-var head.
func TestExtractPaths_BoundFunHead(t *testing.T) {
	P := ext.Var("P", ext.MakeFun(ext.TypeA, ext.TypeBool))
	x := ext.Var("x", ext.TypeA)
	body := P.Apply(x)

	paths := ExtractPaths(IndexedTerm{
		Term:      body.Core(),
		BoundVars: boundOf(P.AssertVar()),
	})
	assertPaths(t, paths, "HEAD:*B/1|ARG0|*F/0")
}

// Case 6: ∃fn. fn(suc 0) = suc(suc(fn 0)) — fn is bound, suc and 0 are
// concrete constants. We construct only the equation body and supply
// fn as bound to test the encoder.
func TestExtractPaths_ExistsFunBody(t *testing.T) {
	fn := ext.Var("fn", ext.MakeFun(TypeInd, TypeInd))
	suc := ext.TestConst("suc", ext.MakeFun(TypeInd, TypeInd))
	zero := ext.TestConst("0", TypeInd)

	// fn(suc 0)
	lhs := fn.Apply(suc.Apply(zero))
	// suc(suc(fn 0))
	rhs := suc.Apply(suc.Apply(fn.Apply(zero)))
	eq := lhs.Eq(rhs)

	paths := ExtractPaths(IndexedTerm{
		Term:      eq.Core(),
		BoundVars: boundOf(fn.AssertVar()),
	})

	// LHS path through fn (bound), reaching the concrete constant 0.
	wantLHS := "HEAD:C:=/2|ARG0|HEAD:*B/1|ARG0|HEAD:C:suc/1|ARG0|C:0/0"
	// RHS path through suc(suc(fn 0)), reaching 0.
	wantRHS := "HEAD:C:=/2|ARG1|HEAD:C:suc/1|ARG0|HEAD:C:suc/1|ARG0|HEAD:*B/1|ARG0|C:0/0"

	assertPaths(t, paths, wantLHS, wantRHS)
}

// Case 7 (extensionality, body): given (∀f g. body) is enumerated and f,
// g become bound, the equation `f = g` produces two paths each ending at
// a *B leaf.
func TestExtractPaths_BoundEquation(t *testing.T) {
	f := ext.Var("f", ext.MakeFun(ext.TypeA, ext.TypeB))
	g := ext.Var("g", ext.MakeFun(ext.TypeA, ext.TypeB))
	eq := f.Eq(g)

	paths := ExtractPaths(IndexedTerm{
		Term:      eq.Core(),
		BoundVars: boundOf(f.AssertVar(), g.AssertVar()),
	})
	assertPaths(t, paths,
		"HEAD:C:=/2|ARG0|*B/0",
		"HEAD:C:=/2|ARG1|*B/0",
	)
}

// LAM appears in the encoder when an AbsTerm is a sub-term itself
// (rather than being stripped by the prop-level enumerator). Verify the
// LAM token + extension of bound vars during encoding.
func TestExtractPaths_AbsTermInEncoder(t *testing.T) {
	x := ext.Var("x", ext.TypeA)
	P := ext.Var("P", ext.MakeFun(ext.TypeA, ext.TypeBool))
	// λx. P(x), encode the lambda directly (no enumerator stripping).
	lam := x.To(P.Apply(x))

	paths := ExtractPaths(IndexedTerm{Term: lam.Core()})
	// LAM token, then the body path: HEAD:*F/1 | ARG0 | *B/0 (x is bound by the lambda)
	assertPaths(t, paths, "LAM|HEAD:*F/1|ARG0|*B/0")
}

// Bare free variable.
func TestExtractPaths_BareFreeVar(t *testing.T) {
	x := ext.Var("x", ext.TypeA)
	paths := ExtractPaths(IndexedTerm{Term: x.Core()})
	assertPaths(t, paths, "*F/0")
}

// Bare bound variable.
func TestExtractPaths_BareBoundVar(t *testing.T) {
	x := ext.Var("x", ext.TypeA)
	paths := ExtractPaths(IndexedTerm{
		Term:      x.Core(),
		BoundVars: boundOf(x.AssertVar()),
	})
	assertPaths(t, paths, "*B/0")
}
