package prop

// Benchmark for the rigid-head pre-filter in unifyEqRewrite. The shape
// is the eqSimplify fixpoint's hot case: a const-headed rule walked
// over a wide boolean goal, where EVERY bool-typed node passes the
// type-chain gate (lTypes suffix [bool] matches trivially) and, without
// the filter, pays a unifyEq attempt whose βη normalization walks the
// node's whole subterm. With the filter each mismatched node costs one
// O(spine) head comparison instead. Compare by running this benchmark
// with and without the headFilter lines in unifyEqRewrite.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// benchWideConj builds d(a₁) ∧ (d(a₂) ∧ (… ∧ d(aₙ))) — n bool-typed
// atoms under n-1 bool-typed ∧-nodes, all const-headed with heads
// (bench_d, ∧) that can never match the benchmark rule's head bench_c.
func benchWideConj(n int) Term {
	typeA := TypeA
	dMeta := core.MakeConstMeta("bench_d", MakeFun(typeA, TypeBool))
	d := core.MakeConstTerm(dMeta, MakeFun(typeA, TypeBool))
	t := Term(ext.Apply(d, Var("a0", typeA)))
	for i := 1; i < n; i++ {
		atom := ext.Apply(d, Var(ext.TermName("a"+string(rune('0'+i%10))), typeA))
		t = ext.WrapTerm(atom).And(t)
	}
	return t
}

func BenchmarkUnifyEqRewriteHeadMiss(b *testing.B) {
	cMeta := core.MakeConstMeta("bench_c", MakeFun(TypeA, TypeBool))
	c := core.MakeConstTerm(cMeta, MakeFun(TypeA, TypeBool))
	x := Var("x", TypeA)
	g := Var("g", MakeFun(TypeA, TypeBool))
	eq := testProp(core.Eq(x.To(ext.Apply(c, x)), g))

	target := benchWideConj(200)
	rewrite := unifyEqRewrite(eq)
	if rewrite(target) != nil {
		b.Fatal("benchmark rule must not fire on the target")
	}

	for b.Loop() {
		rewrite(target)
	}
}
