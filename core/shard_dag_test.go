package core

import (
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Frees, AllFree and HasFreeName on a shared DAG are bounded by its
// nodes, not its tree: a doubling chain of depth 60 answers in
// interactive time. The higher-order unifier asks these of its pair
// terms and of its substitution terms at every search node, and
// imitation builds terms of this shape; a walk per tree path ran a
// session `by` past its budget.
func TestSharedDAGFreeVariableWalksBounded(t *testing.T) {
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	p, q := Var("p", TypeBool()), Var("q", TypeBool())
	pInd := Var("p", indType)
	tower := Term(p)
	for range 60 {
		tower = Apply(Apply(andV, tower), tower)
	}
	require.True(t, NaiveWalkNeedsMemo(tower))
	// p is bound in the left copy and free in the right one; the left
	// copy also holds a p of another type, which no binder named p of
	// type bool binds.
	mixed := Apply(Apply(andV, Apply(Apply(andV, tower), Apply(Var("f", MakeFun(indType, TypeBool())), pInd))), tower)
	bound := Apply(Apply(andV, Apply(Abs(p, mixed), q)), tower)
	all := Abs(p, tower)

	within := func(t *testing.T, name string, call func()) {
		t.Helper()
		done := make(chan struct{})
		go func() { defer close(done); call() }()
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			t.Fatalf("%s: the walk over a depth-60 shared DAG did not answer within 2s — it is per tree path, not per node", name)
		}
	}
	names := func(vs []VarTerm) []string {
		out := make([]string, 0, len(vs))
		for _, v := range vs {
			kind := "fun"
			if v.Type().Equals(TypeBool()) {
				kind = "bool"
			} else if v.Type().Equals(indType) {
				kind = "ind"
			}
			out = append(out, fmt.Sprintf("%s:%s", v.Name(), kind))
		}
		return out
	}

	within(t, "Frees of the tower", func() {
		assert.Equal(t, []string{"and:fun", "p:bool"}, names(tower.Frees(nil)),
			"distinct, in order of first occurrence")
		assert.Equal(t, []string{"p:bool"}, names(tower.Frees(func(v VarTerm) bool { return v.Name() == "p" })))
	})
	within(t, "Frees under binders", func() {
		assert.Equal(t, []string{"and:fun", "f:fun", "p:ind", "q:bool", "p:bool"},
			names(bound.Frees(nil)), "the bound copy's p is left out, the free copy's is kept")
		assert.Equal(t, []string{"and:fun"}, names(all.Frees(nil)))
	})
	within(t, "AllFree", func() {
		assert.True(t, tower.AllFree(func(v VarTerm) bool { return v.Name() == "and" || v.Name() == "p" }))
		assert.False(t, tower.AllFree(func(v VarTerm) bool { return v.Name() == "and" }))
		assert.True(t, all.AllFree(func(v VarTerm) bool { return v.Name() == "and" }), "the binder's variable is not free")
	})
	within(t, "HasFreeName", func() {
		assert.True(t, tower.HasFreeName("p"))
		assert.True(t, tower.HasFreeName("and"))
		assert.False(t, tower.HasFreeName("q"))
		assert.False(t, all.HasFreeName("p"), "bound everywhere")
		assert.True(t, bound.HasFreeName("p"), "free on one path")
		assert.True(t, Abs(p, mixed).HasFreeName("p"), "a p of another type stays free under the binder")
	})
}

// Past the gate the three walks read one memoized list; below it they
// recurse as before. On a tree above the gate with no sharing the two
// agree, binders and shadowing included: the reference here is the
// recursion the methods run below the gate.
func TestSharedDAGFreeVariableWalksAgreeWithTheTreeWalk(t *testing.T) {
	var refFrees func(t Term, f VarPredicate) []VarTerm
	refFrees = func(t Term, f VarPredicate) []VarTerm {
		switch t := t.(type) {
		case VarTerm:
			if f == nil || f(t) {
				return []VarTerm{t}
			}
			return nil
		case ConstTerm:
			return nil
		case AppliedTerm:
			inFun := refFrees(t.fun, f)
			inArg := refFrees(t.arg, func(v VarTerm) bool {
				return (f == nil || f(v)) && !anyVar(inFun, v)
			})
			return append(inFun, inArg...)
		case AbsTerm:
			return refFrees(t.body, func(v VarTerm) bool { return (f == nil || f(v)) && !v.Equals(t.v) })
		}
		panic("unreachable")
	}
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	fV := Var("f", MakeFun(indType, TypeBool()))
	leaves := []Term{Var("p", TypeBool()), Var("q", TypeBool()), Apply(fV, Var("p", indType)), Apply(fV, Var("x", indType)), Var("c", TypeBool())}
	// A full binary tree of depth 13 over the leaves (8191 applied
	// nodes, each built afresh), with a binder on p:bool every fourth
	// level on the left and one on x:ind at the root.
	var build func(depth, i int) Term
	build = func(depth, i int) Term {
		if depth == 0 {
			return leaves[i%len(leaves)]
		}
		left, right := build(depth-1, 2*i), build(depth-1, 2*i+1)
		if depth%4 == 0 {
			left = Apply(Abs(Var("p", TypeBool()), left), Var("q", TypeBool()))
		}
		return Apply(Apply(andV, left), right)
	}
	tree := Apply(Apply(andV, build(13, 0)), Apply(fV, Apply(Abs(Var("x", indType), Var("x", indType)), Var("y", indType))))
	require.True(t, NaiveWalkNeedsMemo(tree), "the tree is past the gate")

	for _, row := range []struct {
		name string
		f    VarPredicate
	}{
		{"every variable", nil},
		{"named p", func(v VarTerm) bool { return v.Name() == "p" }},
		{"of type ind", func(v VarTerm) bool { return v.Type().Equals(indType) }},
		{"none", func(VarTerm) bool { return false }},
	} {
		want := refFrees(tree, row.f)
		assert.Equal(t, want, tree.Frees(row.f), "Frees, %s", row.name)
		wantAll := true
		for _, v := range refFrees(tree, nil) {
			if row.f != nil && !row.f(v) {
				wantAll = false
			}
		}
		if row.f != nil {
			assert.Equal(t, wantAll, tree.AllFree(row.f), "AllFree, %s", row.name)
		}
	}
	for _, n := range []TermName{"p", "q", "x", "y", "f", "and", "z"} {
		assert.Equal(t, anyName(refFrees(tree, nil), n), tree.HasFreeName(n), "HasFreeName %s", n)
	}
}

func anyVar(vs []VarTerm, v VarTerm) bool {
	for _, w := range vs {
		if w.Equals(v) {
			return true
		}
	}
	return false
}

func anyName(vs []VarTerm, n TermName) bool {
	for _, w := range vs {
		if w.Name() == n {
			return true
		}
	}
	return false
}

// HasFree on a shared DAG is bounded by its nodes, not its tree: a
// doubling chain of depth 60 (2^60 tree nodes, 61 unique) answers in
// interactive time for a variable the term lacks, which visits every
// node, and for the variables it holds. The higher-order unifier asks
// this of its pair terms at every search node, and imitation builds
// pair terms of this shape; a walk per tree path ran a session `by`
// past its budget with the session locked.
func TestSharedDAGHasFreeBounded(t *testing.T) {
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	p, q := Var("p", TypeBool()), Var("q", TypeBool())
	tower := Term(p)
	for range 60 {
		tower = Apply(Apply(andV, tower), tower)
	}
	assert.True(t, NaiveWalkNeedsMemo(tower), "the tower's tree size is past the gate")
	// The binder cases: p is bound in the left copy and free in the right
	// one; the shared nodes below the binder answer for the right copy.
	bound := Apply(Apply(andV, Apply(Abs(p, tower), q)), tower)
	for _, row := range []struct {
		name string
		term Term
		v    VarTerm
		want bool
	}{
		{"absent variable", tower, q, false},
		{"same name, other type", tower, Var("p", indType), false},
		{"the leaf variable", tower, p, true},
		{"the head variable", tower, andV, true},
		{"bound on one path, free on another", bound, p, true},
		{"bound everywhere", Abs(p, tower), p, false},
		{"the argument of the redex", bound, q, true},
	} {
		done := make(chan bool, 1)
		go func() { done <- row.term.HasFree(row.v) }()
		select {
		case got := <-done:
			assert.Equal(t, row.want, got, row.name)
		case <-time.After(2 * time.Second):
			t.Fatalf("%s: HasFree on a depth-60 shared DAG did not answer within 2s — the walk is per tree path, not per node", row.name)
		}
	}
}

// Substitute on a shared DAG is bounded by its nodes, not its tree: a
// doubling chain of depth 60 (2^60 tree nodes, 61 unique) is rewritten
// in interactive time, and the result is a DAG of the same shape — the
// shared argument is rewritten once and shared again — so it fits in
// memory. The higher-order unifier substitutes into its pair terms at
// every search node, and imitation builds pair terms of this shape; a
// walk per tree path built the whole tree, which ran a session `by`
// past its budget while its serve grew without bound.
func TestSharedDAGSubstituteBounded(t *testing.T) {
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	p, q, r := Var("p", TypeBool()), Var("q", TypeBool()), Var("r", TypeBool())
	const depth = 60
	tower := Term(p)
	for range depth {
		tower = Apply(Apply(andV, tower), tower)
	}
	require.True(t, NaiveWalkNeedsMemo(tower), "the tower's tree size is past the gate")
	// p is bound in the left copy and free in the right one.
	bound := Apply(Apply(andV, Apply(Abs(p, tower), q)), tower)

	within := func(t *testing.T, name string, call func() Term) Term {
		t.Helper()
		done := make(chan Term, 1)
		go func() { done <- call() }()
		select {
		case got := <-done:
			return got
		case <-time.After(2 * time.Second):
			t.Fatalf("%s: Substitute on a depth-60 shared DAG did not answer within 2s — the walk is per tree path, not per node", name)
			return nil
		}
	}
	// leafOf descends the left spine of a doubling chain, checking at
	// every level that both copies are one node — the result kept the
	// input's sharing.
	leafOf := func(t *testing.T, name string, chain Term, levels int) Term {
		t.Helper()
		for i := range levels {
			node, ok := chain.AsAppliedTerm()
			require.True(t, ok, "%s: level %d is an application", name, i)
			left, ok := node.Fun().AsAppliedTerm()
			require.True(t, ok, "%s: level %d applies the head", name, i)
			require.True(t, any(left.Arg()) == any(node.Arg()), "%s: level %d shares its two copies", name, i)
			chain = node.Arg()
		}
		return chain
	}

	t.Run("the leaf variable is rewritten once per node", func(t *testing.T) {
		got := within(t, "p ↦ q", func() Term { return tower.Substitute(MakeTermSubst(p, q)) })
		assert.True(t, got.HasFree(q))
		assert.False(t, got.HasFree(p))
		assert.Equal(t, tower.Size(), got.Size())
		assert.True(t, q.Equals(leafOf(t, "p ↦ q", got, depth)))
	})
	t.Run("an absent variable leaves the term as it is", func(t *testing.T) {
		got := within(t, "r ↦ q", func() Term { return tower.Substitute(MakeTermSubst(r, q)) })
		assert.True(t, any(tower) == any(got))
	})
	t.Run("the head variable is rewritten at every level", func(t *testing.T) {
		orV := Var("or", MakeFun(TypeBool(), TypeBool(), TypeBool()))
		got := within(t, "and ↦ or", func() Term { return tower.Substitute(MakeTermSubst(andV, orV)) })
		assert.True(t, got.HasFree(orV))
		assert.False(t, got.HasFree(andV))
		leafOf(t, "and ↦ or", got, depth)
	})
	t.Run("a binder on one path keeps its own copy", func(t *testing.T) {
		got := within(t, "bound, p ↦ q", func() Term { return bound.Substitute(MakeTermSubst(p, q)) })
		node, ok := got.AsAppliedTerm()
		require.True(t, ok)
		assert.False(t, node.Arg().HasFree(p), "the free copy is rewritten")
		assert.True(t, node.Arg().HasFree(q))
		redex, ok := node.Fun().AsAppliedTerm()
		require.True(t, ok)
		abs, ok := redex.Arg().AsAppliedTerm()
		require.True(t, ok)
		body, ok := abs.Fun().AsAbsTerm()
		require.True(t, ok)
		assert.True(t, body.Body().HasFree(p), "the bound copy is left alone")
		assert.True(t, any(tower) == any(body.Body()))
	})
	t.Run("two variables at once", func(t *testing.T) {
		mixed := Apply(Apply(andV, tower), Apply(Apply(andV, q), tower))
		got := within(t, "p ↦ q, q ↦ r", func() Term {
			return mixed.Substitute(MakeTermSubst(p, q), MakeTermSubst(q, r))
		})
		assert.True(t, got.HasFree(q))
		assert.True(t, got.HasFree(r))
		assert.False(t, got.HasFree(p))
	})
}

// answersWithin runs call and fails the test unless it returns in
// interactive time: a walk over a shared DAG that is per tree path
// never returns.
func answersWithin(t *testing.T, name string, call func()) {
	t.Helper()
	done := make(chan struct{})
	go func() { defer close(done); call() }()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatalf("%s did not answer within 2s: the walk is per tree path, not per node", name)
	}
}

// doublingChain is leaf, head(leaf, leaf), head(…, …), … to depth: a
// tree of 2^depth leaves over depth+2 nodes.
func doublingChain(head, leaf Term, depth int) Term {
	t := leaf
	for range depth {
		t = Apply(Apply(head, t), t)
	}
	return t
}

// sharedBinderChain shares one binder between two applications at
// every level: and((λx.M) q, (λx.M) r) over the level below M, down to
// and(x, p), so x is bound everywhere and p free. A walk that forgets a
// binder it has rewritten walks M once per application, and the tree
// doubles per level.
func sharedBinderChain(depth int) (chain Term, x, p VarTerm) {
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	x, p = Var("x", TypeBool()), Var("p", TypeBool())
	q, r := Var("q", TypeBool()), Var("r", TypeBool())
	chain = Apply(Apply(andV, x), p)
	for range depth {
		abs := Abs(x, chain)
		chain = Apply(Apply(andV, Apply(abs, q)), Apply(abs, r))
	}
	return chain, x, p
}

// sharedLeafOf descends the left spine of a doubling chain, checking
// at every level that the two copies are one node, and returns the
// leaf: the chain kept its sharing.
func sharedLeafOf(t *testing.T, chain Term, depth int) Term {
	t.Helper()
	for i := range depth {
		node, ok := chain.AsAppliedTerm()
		require.True(t, ok, "level %d is an application", i)
		left, ok := node.Fun().AsAppliedTerm()
		require.True(t, ok, "level %d applies the head", i)
		require.True(t, any(left.Arg()) == any(node.Arg()), "level %d shares its two copies", i)
		chain = node.Arg()
	}
	return chain
}

// Every walk over one term is bounded by the term's nodes, not by its
// tree (shared_dag.go): each answers on a depth-60 shared DAG, 2^60
// tree nodes over a few hundred. Three shapes: a doubling chain of
// applications over a type variable, the chain under a binder, and a
// chain that shares a binder between two applications at every level.
func TestSharedDAGEveryWalkBounded(t *testing.T) {
	A, B := MakeVarType("A"), MakeVarType("B")
	pA, qA := Var("p", A), Var("q", A)
	chain := doublingChain(Var("and", MakeFun(A, A, A)), pA, 60)
	binders, x, pBool := sharedBinderChain(60)
	qBool := Var("q", TypeBool())
	for _, shape := range []struct {
		name string
		term Term
		v, w VarTerm
	}{
		{"doubling chain", chain, pA, qA},
		{"chain under a binder", Abs(pA, chain), pA, qA},
		{"shared binders", binders, pBool, qBool},
	} {
		require.True(t, NaiveWalkNeedsMemo(shape.term), "%s is past the gate", shape.name)
		for _, walk := range []struct {
			name string
			call func()
		}{
			{"Substitute", func() { shape.term.Substitute(MakeTermSubst(shape.v, shape.w)) }},
			{"Substitute of a bound variable", func() { shape.term.Substitute(MakeTermSubst(x, qBool)) }},
			{"TypeSubstitute of a present variable", func() { shape.term.TypeSubstitute(MakeTypeSubst(A, TypeBool())) }},
			{"TypeSubstitute of an absent variable", func() { shape.term.TypeSubstitute(MakeTypeSubst(B, TypeBool())) }},
			{"DeBruijn", func() { shape.term.DeBruijn(0) }},
			{"AlphaKey", func() { shape.term.AlphaKey() }},
			{"Frees", func() { shape.term.Frees(nil) }},
			{"HasFree", func() { shape.term.HasFree(shape.w) }},
			{"AllFree", func() { shape.term.AllFree(func(VarTerm) bool { return true }) }},
			{"HasFreeName", func() { shape.term.HasFreeName("absent") }},
			{"HasName", func() { shape.term.HasName("absent") }},
			{"typeVars", func() { shape.term.typeVars() }},
		} {
			answersWithin(t, shape.name+": "+walk.name, walk.call)
		}
	}
}

// TypeSubstitute on a shared DAG rewrites a shared node once and shares
// the result again; an absent variable gives the term back; a binder
// whose variable the substitution makes collide with a free one is
// renamed, as below the gate.
func TestSharedDAGTypeSubstitute(t *testing.T) {
	A, B := MakeVarType("A"), MakeVarType("B")
	andA, pA := Var("and", MakeFun(A, A, A)), Var("p", A)
	andBool, pBool := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool())), Var("p", TypeBool())
	chain := doublingChain(andA, pA, 60)
	toBool := MakeTypeSubst(A, TypeBool())

	var got Term
	answersWithin(t, "A ↦ bool", func() { got = chain.TypeSubstitute(toBool) })
	assert.True(t, pBool.Equals(sharedLeafOf(t, got, 60)))
	assert.Equal(t, doublingChain(andBool, pBool, 60).AlphaKey(), got.AlphaKey())
	assert.True(t, any(chain) == any(chain.TypeSubstitute(MakeTypeSubst(B, TypeBool()))), "B is absent")

	// λx:bool. c(x, and(chain, x:A)): A ↦ bool makes the free x:A the
	// binder's variable, so the binder is renamed.
	xBool, xA := Var("x", TypeBool()), Var("x", A)
	cA := Var("c", MakeFun(TypeBool(), A, A))
	bound := Abs(xBool, Apply(Apply(cA, xBool), Apply(Apply(andA, chain), xA)))
	answersWithin(t, "A ↦ bool under a colliding binder", func() { got = bound.TypeSubstitute(toBool) })
	y := Var("y", TypeBool())
	cBool := Var("c", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	want := Abs(y, Apply(Apply(cBool, y), Apply(Apply(andBool, doublingChain(andBool, pBool, 60)), xBool)))
	assert.Equal(t, want.AlphaKey(), got.AlphaKey())
	abs, ok := got.AsAbsTerm()
	require.True(t, ok)
	assert.NotEqual(t, TermName("x"), abs.Var().Name(), "the binder is renamed away from the free x")
	assert.True(t, abs.Body().HasFree(xBool), "the free x:A is now x:bool")
}

// The de Bruijn conversion of a binder over a shared DAG keeps the
// sharing in its body, and two α-equal binders over the chain have one
// key.
func TestSharedDAGDeBruijn(t *testing.T) {
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))
	p, q := Var("p", TypeBool()), Var("q", TypeBool())
	chain := doublingChain(andV, p, 60)
	var db Term
	answersWithin(t, "DeBruijn", func() { db = Abs(p, chain).DeBruijn(0) })
	abs, ok := db.AsAbsTerm()
	require.True(t, ok)
	assert.Equal(t, 1, abs.Var().DeBruijnIndex())
	assert.True(t, abs.Var().Equals(sharedLeafOf(t, abs.Body(), 60)), "the leaf is the de Bruijn variable")
	var renamed Term
	answersWithin(t, "p ↦ q", func() { renamed = chain.Substitute(MakeTermSubst(p, q)) })
	assert.Equal(t, Abs(p, chain).AlphaKey(), Abs(q, renamed).AlphaKey(), "α-equal binders share a key")
	assert.NotEqual(t, Abs(p, chain).AlphaKey(), Abs(q, chain).AlphaKey(), "p stays free under λq")
}

// A binder shared by two applications is rewritten once, and the
// result shares it again; a variable bound everywhere leaves the term
// as it is.
func TestSharedDAGSubstituteSharedBinder(t *testing.T) {
	chain, x, p := sharedBinderChain(60)
	q := Var("q", TypeBool())
	var got Term
	answersWithin(t, "p ↦ q", func() { got = chain.Substitute(MakeTermSubst(p, q)) })
	assert.False(t, got.HasFree(p))
	assert.True(t, got.HasFree(q))
	level := got
	for i := range 60 {
		node, ok := level.AsAppliedTerm()
		require.True(t, ok)
		head, ok := node.Fun().AsAppliedTerm()
		require.True(t, ok)
		left, ok := head.Arg().AsAppliedTerm()
		require.True(t, ok, "level %d applies the binder on the left", i)
		right, ok := node.Arg().AsAppliedTerm()
		require.True(t, ok, "level %d applies the binder on the right", i)
		require.True(t, any(left.Fun()) == any(right.Fun()), "level %d shares its binder", i)
		abs, ok := left.Fun().AsAbsTerm()
		require.True(t, ok)
		level = abs.Body()
	}
	assert.True(t, any(chain) == any(chain.Substitute(MakeTermSubst(x, q))), "x is bound everywhere")
}
