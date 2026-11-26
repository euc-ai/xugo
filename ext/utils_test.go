package ext

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func assertTermEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.Equals(t1))
}

func assertTermAlphaEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.AlphaEquals(t1))
}

func assertTermsAlphaEqual(t *testing.T, t0 []Term, t1 ...Term) {
	k0 := make([]core.TermKey, len(t0))
	for i, s := range t0 {
		k0[i] = s.AlphaKey()
	}
	k1 := make([]core.TermKey, len(t1))
	for i, s := range t1 {
		k1[i] = s.AlphaKey()
	}
	assert.ElementsMatch(t, k0, k1)
}

func TestFun(t *testing.T) {
	types := MatchesFun(TypeA)
	assert.Equal(t, len(types), 1)
	assert.True(t, types[0].Equals(TypeA))

	types = MatchesFun(MakeFun(TypeA, TypeBool, TypeInd))
	assert.Equal(t, len(types), 3)
	assert.True(t, types[0].Equals(TypeA))
	assert.True(t, types[1].Equals(TypeBool))
	assert.True(t, types[2].Equals(TypeInd))

	types = MatchesFun(MakeFun(MakeFun(TypeA, TypeBool), TypeInd))
	assert.Equal(t, len(types), 2)
	assert.True(t, types[0].Equals(MakeFun(TypeA, TypeBool)))
	assert.True(t, types[1].Equals(TypeInd))

	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeInd))
	R := Var("R", MakeFun(TypeInd, TypeInd))
	f, args := MatchesApply(P.Apply(x, y))
	assertTermEqual(t, P, f)
	assert.Equal(t, len(args), 2)
	assertTermEqual(t, x, args[0])
	assertTermEqual(t, y, args[1])

	f, args = MatchesApply(Q.Apply(R.Apply(x)))
	assertTermEqual(t, Q, f)
	assert.Equal(t, len(args), 1)
	assertTermEqual(t, R.Apply(x), args[0])
}

func TestVarSet(t *testing.T) {
	var x = core.Var("x", TypeInd)
	var y = core.Var("y", TypeInd)
	var z = core.Var("z", TypeInd)
	s0 := VarList{}
	assert.True(t, s0.Add(x)) // s0: {x}
	assert.Equal(t, s0.Size(), 1)
	assert.False(t, s0.Add(x)) // s0: {x}
	assert.Equal(t, s0.Size(), 1)
	assert.True(t, s0.Add(y)) // s0: {x, y}
	assert.Equal(t, s0.Size(), 2)
	assert.True(t, s0.Remove(x))  // s0: {y}
	assert.False(t, s0.Remove(z)) // s0: {y}
	assert.Equal(t, s0.Size(), 1)
	s1 := s0.Clone()          // s1: {y}
	assert.True(t, s1.Add(x)) // s1: {x, y}
	assert.Equal(t, s0.Size(), 1)
	assert.Equal(t, s1.Size(), 2)
	assert.True(t, s0.Add(z))     // s0: {y, z}
	assert.True(t, s1.Add(z))     // s1: {x, y, z}
	assert.True(t, s1.Remove(y))  // s1: {x, z}
	assert.False(t, s1.Remove(y)) // s1: {x, z}
	assert.True(t, s1.Remove(z))  // s1: {x}
	assert.True(t, s0.Add(x))     // s0: {x, y, z}
	assert.False(t, s0.Add(x))    // s0: {x, y, z}
	assert.Equal(t, s0.Size(), 3)
	assert.Equal(t, s1.Size(), 1)
	assert.False(t, s1.Replace(y, z)) // s1: {x}
	assert.Panics(t, func() { s1.Replace(y, x) })
	assert.True(t, s1.Add(z)) // s1: {x, z}
	assert.Equal(t, s1.Size(), 2)
	assert.True(t, s1.Ind(0).Equals(x))
	assert.True(t, s1.Ind(1).Equals(z))
	assert.True(t, s1.Replace(x, y)) // s1: {y, z}
	assert.True(t, s1.Replace(z, x)) // s1: {y, x}
	assert.True(t, s1.Ind(0).Equals(y))
	assert.True(t, s1.Ind(1).Equals(x))
}

func TestTypeVars(t *testing.T) {
	typeB := core.MakeVarType("B")
	typeC := core.MakeVarType("C")
	plus := Const(
		core.MakeConstMeta("Plus", MakeFun(TypeA, typeB, TypeBool)),
		MakeFun(TypeA, typeB, TypeBool))
	x := Var("x", TypeA)
	y := Var("y", typeB)
	fullVarTypePredicate := utils.FullPredicate[VarType]

	assert.True(t, TermHasTypeVar(plus, TypeA))
	assert.True(t, TermHasTypeVar(plus, typeB))
	assert.False(t, TermHasTypeVar(plus, typeC))
	assert.True(t, TermAnyTypeVar(plus, fullVarTypePredicate))
	assert.True(t, TermAnyTypeVar(x.To(y), fullVarTypePredicate))
	assert.True(t, TermHasTypeVar(x.To(y), TypeA))
	assert.True(t, TermHasTypeVar(x.To(y), typeB))
	assert.False(t, TermHasTypeVar(x.To(y), typeC))
	assert.True(t, TermAnyTypeVar(Apply(plus, x, y), fullVarTypePredicate))
	assert.True(t, TermHasTypeVar(Apply(plus, x, y), TypeA))
	assert.True(t, TermHasTypeVar(Apply(plus, x, y), typeB))
	assert.False(t, TermHasTypeVar(Apply(plus, x, y), typeC))
	assert.True(t, TermAnyTypeVar(x.To(Apply(plus, x)), fullVarTypePredicate))
	assert.True(t, TypeAnyVar(Apply(plus, x).Type(), fullVarTypePredicate))
	assert.False(t, TypeAnyVar(Apply(plus, x, y).Type(), fullVarTypePredicate))
	assert.False(t, TypeHasVar(Apply(plus, x, y).Type(), TypeA))
	assert.False(t, TypeHasVar(Apply(plus, x, y).Type(), typeB))
	assert.False(t, TypeHasVar(Apply(plus, x, y).Type(), typeC))

	f := func(v VarType) bool { return v.Name() == "B" }
	assert.True(t, TermAnyTypeVar(plus, f))
	assert.True(t, TermAnyTypeVar(Apply(plus, x), f))
	assert.True(t, TermAnyTypeVar(Apply(plus, x, y), f))
	assert.True(t, TermAnyTypeVar(x.To(Apply(plus, x)), f))
	assert.True(t, TypeAnyVar(Apply(plus, x).Type(), f))

	f = func(v VarType) bool { return v.Name() == "C" }
	assert.False(t, TermAnyTypeVar(plus, f))
	assert.False(t, TermAnyTypeVar(Apply(plus, x), f))
	assert.False(t, TermAnyTypeVar(Apply(plus, x, y), f))
	assert.False(t, TermAnyTypeVar(x.To(Apply(plus, x)), f))
	assert.False(t, TypeAnyVar(Apply(plus, x).Type(), f))
}

// TermHasTypeVar and TermAnyTypeVar over a shared DAG are bounded by
// its nodes: a doubling chain of depth 60 answers for a type variable
// the term lacks, which visits every node, and for one it holds. The
// higher-order unifier asserts, of every pair term and every type
// substitution of a search step, that the substituted variable is
// gone.
func TestSharedDAGTypeVarWalksBounded(t *testing.T) {
	A, B := core.MakeVarType("A"), core.MakeVarType("B")
	andV := core.Var("and", core.MakeFun(A, A, A))
	p := core.Var("p", A)
	chain := core.Term(p)
	for range 60 {
		chain = core.Apply(core.Apply(andV, chain), chain)
	}
	require.True(t, core.NaiveWalkNeedsMemo(chain))
	isA := func(v core.VarType) bool { return v.Equals(A) }
	none := func(core.VarType) bool { return false }
	for _, row := range []struct {
		name string
		call func() bool
		want bool
	}{
		{"a present variable", func() bool { return TermHasTypeVar(chain, A) }, true},
		{"an absent variable", func() bool { return TermHasTypeVar(chain, B) }, false},
		{"a present variable under a binder", func() bool { return TermHasTypeVar(core.Abs(p, chain), A) }, true},
		{"an absent variable under a binder", func() bool { return TermHasTypeVar(core.Abs(p, chain), B) }, false},
		{"any matching", func() bool { return TermAnyTypeVar(chain, isA) }, true},
		{"none matching", func() bool { return TermAnyTypeVar(chain, none) }, false},
	} {
		done := make(chan bool, 1)
		go func() { done <- row.call() }()
		select {
		case got := <-done:
			assert.Equal(t, row.want, got, row.name)
		case <-time.After(2 * time.Second):
			t.Fatalf("%s: the walk over a depth-60 shared DAG did not answer within 2s", row.name)
		}
	}
}

func TestTypeDefSourceThm(t *testing.T) {
	x := core.Var("x", core.TypeA())
	source := core.Refl(core.Abs(x, x))
	_, abs, _ := core.NewTypeDef(source, "ext_source_cert", "ext_source_abs", "ext_source_rep")
	assert.Equal(t, source, TypeDefSourceThm(abs.Meta(), core.Forcer{}),
		"a realized source needs no forcing scope")
	assert.Panics(t, func() { TypeDefSourceThm(core.MetaEq(), core.NewForcer(context.Background())) })

	built := false
	promised := core.Promise(source.AsProp(), func(core.Forcer) core.ThmCert {
		built = true
		return source
	})
	_, abs, _ = core.NewTypeDef(promised, "ext_source_promise", "ext_promise_abs", "ext_promise_rep")
	assert.Equal(t, source, TypeDefSourceThm(abs.Meta(), core.NewForcer(context.Background())))
	assert.True(t, built)

	frontier := core.Promise(source.AsProp(), func(core.Forcer) core.ThmCert { panic("trusted source must not build") })
	_, abs, _ = core.NewTypeDef(frontier, "ext_source_boundary", "ext_boundary_abs", "ext_boundary_rep")
	outerStatement := core.Refl(core.Var("outer", core.TypeBool())).AsProp()
	outer := core.Promise(outerStatement, func(f core.Forcer) core.ThmCert {
		cert := TypeDefSourceThm(abs.Meta(), f)
		// Keep the source assumption on a distinct outer statement.
		return core.DeriveTrans(cert, core.Refl(core.Var("outer", core.TypeBool()))).AsThmCert()
	})
	cert, assumed := core.ForceWithBoundary(context.Background(), outer, source.AlphaEquals)
	require.Len(t, assumed, 1)
	require.Len(t, cert.Assumes(), 1)
	assert.Equal(t, core.BoundaryDoor, cert.Assumes()[0].Door)
	assert.True(t, cert.Assumes()[0].Statement.AlphaEquals(source))
}
