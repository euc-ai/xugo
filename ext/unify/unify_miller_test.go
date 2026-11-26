package unify

// Tests for the Miller-pattern fast path in matchFlexibleRigid
// (tryMillerPattern). The pattern fragment of higher-order unification
// (Miller 1991; Nipkow 1993) is the decidable, unitary subset: when a
// flexible side has the shape `M(a1,...,an)` with the a_i pairwise-
// distinct in-scope bound variables and M absent from the other side,
// the equation has the unique MGU `M := λa1...λan. t`.
//
// These tests verify both that the success cases return that MGU
// directly and that the refusal cases (repeated args, non-bound-arg
// args, occurs check, capture-avoidance) fall through to the existing
// Huet-style branches rather than producing a Miller-shaped (incorrect)
// answer.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestUnifyMillerPattern_DistinctBoundArgs_Succeeds is the positive
// case: λx.λy. g(x, y) ≐ λx.λy. h(y, x), with g instantiable and h
// ground. The argument flip in h(y, x) rules out η-collapse of the
// witness, so the test verifies the lambda stays. Miller produces the
// MGU `g := λx.λy. h(y, x)` in one step; Huet would imitate-then-
// project-twice for the same result via three substitution layers.
func TestUnifyMillerPattern_DistinctBoundArgs_Succeeds(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(y.To(g.Apply(x, y))),
		x.To(y.To(h.Apply(y, x))),
		ground.HasName)

	// Expected unique MGU: g ↦ λx.λy. h(y, x).
	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(g, x.To(y.To(h.Apply(y, x))))})
}

// TestUnifyMillerPattern_EtaCollapsibleWitness exercises the case
// where the Miller witness happens to η-collapse: g(x, y) ≐ h(x, y)
// admits λx.λy. h(x, y), which η-reduces to h. We verify the
// post-collapse substitution `g ↦ h` is returned.
func TestUnifyMillerPattern_EtaCollapsibleWitness(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(y.To(g.Apply(x, y))),
		x.To(y.To(h.Apply(x, y))),
		ground.HasName)

	// Expected: g ↦ h (the η-collapsed Miller witness).
	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(g, h)})
}

// TestUnifyMillerPattern_BodyMentionsOuterFreeVar verifies that a
// witness body that mentions an outer free variable K (not bound in
// the unification scope) is still correctly abstracted.
//
//	g(x, y) ≐ h(x, K)  ⟹  g := λx.λy. h(x, K)
//
// K is a free variable of the outer term (not in p.boundVars), so it
// is not subject to the Miller capture-avoidance check.
func TestUnifyMillerPattern_BodyMentionsOuterFreeVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	K := Var("K", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())
	ground.Add(K.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(y.To(g.Apply(x, y))),
		x.To(y.To(h.Apply(x, K))),
		ground.HasName)

	// Expected MGU: g ↦ λx.λy. h(x, K).
	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(g, x.To(y.To(h.Apply(x, K))))})
}

// TestUnifyMillerPattern_OccursCheck_RefusesBinding verifies that the
// occurs check refuses the Miller path when M appears free in t:
//
//	g(x) ≐ g(x)  -- α-equal at top, drops out before unify
//	g(x) ≐ h(g(x))  -- g appears in body — Miller refuses (occurs)
//
// We expect unification to fail outright because Huet's imitate would
// also refuse to bind M to a term containing M itself (an infinite
// regress). The absence of any substitution is the contract here.
func TestUnifyMillerPattern_OccursCheck_RefusesBinding(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	h := Var("h", MakeFun(TypeBool, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(g.Apply(x)),
		x.To(h.Apply(g.Apply(x))),
		ground.HasName)

	// Occurs check rules out g ↦ ...g... ; no MGU exists.
	assert.Nil(t, substs)
}

// TestUnifyMillerPattern_RepeatedArg_FallsThroughToHuet verifies that
// when the args are not pairwise-distinct (Miller's distinctness
// precondition fails), tryMillerPattern returns nil and the existing
// Huet imitate/project branches handle the pair.
//
// Setup: λx.λy. g(x, x) ≐ λx.λy. h(x, x) where g, h are instantiable
// (flex/flex). Miller refuses (duplicate args); Huet succeeds via the
// existing flex/flex branches and yields g ↦ h (modulo η).
//
// We don't pin down Huet's exact output set here — only that the path
// is reachable (unification succeeds) rather than dead.
func TestUnifyMillerPattern_RepeatedArg_FallsThroughToHuet(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(y.To(g.Apply(x, x))),
		x.To(y.To(h.Apply(x, x))),
		ground.HasName)

	// Just assert SOME solution exists — we're verifying the
	// non-Miller fallthrough, not the exact Huet output.
	assert.NotNil(t, substs)
}

// TestUnifyMillerPattern_NonBoundArg_FallsThrough verifies that when
// one of the args is not an in-scope bound variable (e.g. a constant
// position or a complex term), tryMillerPattern returns nil and the
// existing branches handle the pair.
//
//	λy. g(K, y) ≐ λy. h(K, y)
//
// K is a free variable in the outer scope (constant from Miller's
// perspective; not in p.boundVars). The Miller precondition "args are
// bound vars" fails on arg 0 (K). Huet imitate produces g ↦ h ; we
// only assert that unification succeeds.
func TestUnifyMillerPattern_NonBoundArg_FallsThrough(t *testing.T) {
	defer goleak.VerifyNone(t)

	y := Var("y", TypeA)
	K := Var("K", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())
	ground.Add(K.AssertVar())

	substs := UnifyTerms(t.Context(),
		y.To(g.Apply(K, y)),
		y.To(h.Apply(K, y)),
		ground.HasName)

	assert.NotNil(t, substs)
}

// TestUnifyMillerPattern_CaptureAvoidanceRefuses verifies that when the
// witness body mentions an in-scope bound variable that is *not* one of
// the Miller args, tryMillerPattern refuses (capture-avoidance side-
// condition fails).
//
//	λx.λy.λz. g(x, y) ≐ λx.λy.λz. h(x, y, z)
//
// Here z is bound but is not an arg of g. A Miller binding
// g ↦ λx.λy. h(x, y, z) would leave z free at the outer substitution
// site, where z is not in scope. Miller correctly refuses; Huet may or
// may not find an answer. We assert the refusal does not produce a
// spurious Miller-shaped solution by checking that the substitution
// set, if non-nil, does not contain the ill-formed `g ↦ λx.λy. h(x,y,z)`.
func TestUnifyMillerPattern_CaptureAvoidanceRefuses(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(),
		x.To(y.To(z.To(g.Apply(x, y)))),
		x.To(y.To(z.To(h.Apply(x, y, z)))),
		ground.HasName)

	// The ill-formed Miller witness is `λx.λy. h(x, y, z)` — z would
	// remain free at the outer level. Any returned substitution must
	// avoid this shape.
	illFormedWitness := x.To(y.To(h.Apply(x, y, z))).Core()
	for _, group := range substs {
		for _, subst := range group {
			if subst.VarTerm.Equals(g) {
				assert.False(t,
					subst.Term.AlphaEquals(illFormedWitness),
					"Miller capture-avoidance failed: returned ill-formed witness %s",
					ext.PrintTerm(subst.Term))
			}
		}
	}
}

// TestTryMillerPattern_CaptureAvoidance_DirectRefuses pins the
// capture-avoidance refusal at the predicate boundary: build the exact
// _TermPair / _UnifyEnv that matchFlexibleRigid would hand to
// tryMillerPattern for the equation `g(x, y) ≐ h(x, y, z)` with all of
// x, y, z bound, and assert the function returns nil.
//
// The UnifyTerms-level test above (CaptureAvoidanceRefuses) checks the
// downstream invariant "no ill-formed witness emitted" — but UnifyTerms
// may return nil for unrelated reasons (Huet timeout / depth limit /
// no closing path), in which case that test passes vacuously. This
// test bypasses the search and asserts the predicate itself behaves.
func TestTryMillerPattern_CaptureAvoidance_DirectRefuses(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA).AssertVar()
	y := Var("y", TypeA).AssertVar()
	z := Var("z", TypeA).AssertVar()
	h := Var("h", MakeFun(TypeA, TypeA, TypeA, TypeBool)).AssertVar()
	g := Var("g", MakeFun(TypeA, TypeA, TypeBool)).AssertVar()

	boundVars := VarList{}
	boundVars.Add(x)
	boundVars.Add(y)
	boundVars.Add(z)

	gApp := Apply(g, x, y)
	hApp := Apply(h, x, y, z)
	pair := &_TermPair{
		t0:        gApp,
		t1:        hApp,
		boundVars: boundVars,
	}

	result := tryMillerPattern(t.Context(), g, []Term{x, y}, pair)
	assert.Nil(t, result,
		"capture-avoidance must refuse: z is bound but not an arg, so "+
			"λx.λy. h(x,y,z) would leak z at the outer substitution site")
}

// TestTryMillerPattern_RhsHasMetaVar_DirectAccepts pins the standard
// Miller-pattern behavior when the rigid side mentions another
// meta-variable.
//
// Setup: `g(x) ≐ h(X, x)` where:
//   - g is the flexible head (meta-variable, head of t0),
//   - x is the single Miller arg (bound),
//   - h is GROUND, AND
//   - X is a free, non-ground variable — i.e. another meta-variable.
//
// Miller's MGU is g := λx. h(X, x). This is still most-general: any
// later substitution for X composes through g's witness.
func TestTryMillerPattern_RhsHasMetaVar_DirectAccepts(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA).AssertVar()
	X := Var("X", TypeA).AssertVar() // free meta-variable
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool)).AssertVar()
	g := Var("g", MakeFun(TypeA, TypeBool)).AssertVar()

	boundVars := VarList{}
	boundVars.Add(x)

	gApp := Apply(g, x)
	hApp := Apply(h, X, x)
	pair := &_TermPair{
		t0:        gApp,
		t1:        hApp,
		boundVars: boundVars,
	}

	result := tryMillerPattern(t.Context(), g, []Term{x}, pair)
	require.NotNil(t, result, "Miller must accept free meta-vars on the rhs")
	assert.Len(t, result.TermSubsts, 1)
	subst := result.TermSubsts[0]
	assert.True(t, subst.VarTerm.Equals(g))
	// makeUnifyTermSubst η-collapses λx. h(X, x) to h(X).
	expected := Var("h", MakeFun(TypeA, TypeA, TypeBool)).Apply(X).Core()
	assert.True(t,
		subst.Term.AlphaEquals(expected),
		"expected witness h(X) (η-collapse of λx. h(X,x)); got %s",
		ext.PrintTerm(subst.Term))
}

// TestTryMillerPattern_RhsAllGround_DirectAccepts is the ground-RHS
// counterpart of the previous test: same shape, but X is now ground.
// Miller MUST still fire and return the MGU g ↦ λx. h(X, x).
func TestTryMillerPattern_RhsAllGround_DirectAccepts(t *testing.T) {
	defer goleak.VerifyNone(t)

	xW := Var("x", TypeA)
	KW := Var("K", TypeA) // ground free variable
	hW := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	gW := Var("g", MakeFun(TypeA, TypeBool))
	x, K, h, g := xW.AssertVar(), KW.AssertVar(), hW.AssertVar(), gW.AssertVar()

	boundVars := VarList{}
	boundVars.Add(x)

	gApp := Apply(g, x)
	hApp := Apply(h, K, x)
	pair := &_TermPair{
		t0:        gApp,
		t1:        hApp,
		boundVars: boundVars,
	}

	result := tryMillerPattern(t.Context(), g, []Term{x}, pair)
	require.NotNil(t, result, "Miller must fire when rhs has no meta-vars")
	assert.Len(t, result.TermSubsts, 1)
	subst := result.TermSubsts[0]
	assert.True(t, subst.VarTerm.Equals(g))
	// makeUnifyTermSubst η-collapses the witness: λx. h(K, x) → h(K).
	// Both forms are kernel-equivalent; we assert the collapsed shape
	// since that's what gets stored in the substitution.
	expected := hW.Apply(K).Core()
	assert.True(t,
		subst.Term.AlphaEquals(expected),
		"expected witness h(K) (η-collapse of λx. h(K, x)); got %s",
		ext.PrintTerm(subst.Term))
}

// TestTryMillerPattern_BaseVar_LargeGroundTerm — the n = 0 pattern on
// a term too large for the imitation chain: a bare variable against a
// ground term of ~500 nodes. Imitation copied the term one constructor
// per recursion level and re-verified every pending pair at each, so
// this match cost seconds and, under the default deterministic work
// budget, FAILED beyond ~250 nodes. The base case commits M ↦ t at
// once; the result set is exactly that, within the default budget.
func TestTryMillerPattern_BaseVar_LargeGroundTerm(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := ext.TestConst("f", MakeFun(TypeInd, TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	var target Term = c
	for range 256 {
		target = f.Apply(target, c)
	}
	m := Var("M", TypeInd)

	substs := UnifyTerms(t.Context(), m, target, utils.EmptyPredicate)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(m.AssertVar(), target)})
}

// TestTryMillerPattern_BaseVar_FirstOrderPatternLargeTarget — the shape
// every first-order rewrite rule takes at the unifier: a pattern whose
// variables are bare arguments, against a ground target that spells
// large subterms for them. Both variables are n = 0 patterns once the
// rigid heads are peeled; one unifier.
func TestTryMillerPattern_BaseVar_FirstOrderPatternLargeTarget(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := ext.TestConst("f", MakeFun(TypeInd, TypeInd, TypeInd))
	g := ext.TestConst("g", MakeFun(TypeInd, TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	d := ext.TestConst("d", TypeInd)
	var big Term = c
	for range 128 {
		big = f.Apply(big, d)
	}
	m, n := Var("M", TypeInd), Var("N", TypeInd)
	pattern := g.Apply(m, n)
	target := g.Apply(big, f.Apply(c, big))

	substs := UnifyTerms(t.Context(), pattern, target, utils.EmptyPredicate)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{
			MakeTermSubst(m.AssertVar(), big),
			MakeTermSubst(n.AssertVar(), f.Apply(c, big)),
		})
}

// TestTryMillerPattern_EtaExpandedBoundArg_DirectAccepts: the unifier
// works in η-long normal form, where a bound variable of function type
// stands as its η-expansion. `g(λy. x(y)) ≐ h(λy. x(y))` with x : B → A
// bound is the pattern `g(x) ≐ h(x)` read modulo η, and its MGU is
// g := λx. h(x), which η-collapses to h. An argument read only as a
// bare variable refuses it and sends the pair to the imitation chain.
func TestTryMillerPattern_EtaExpandedBoundArg_DirectAccepts(t *testing.T) {
	defer goleak.VerifyNone(t)

	fnT := MakeFun(TypeB, TypeA)
	y := Var("y", TypeB)
	x := Var("x", fnT)
	h := Var("h", MakeFun(fnT, TypeBool))
	g := Var("g", MakeFun(fnT, TypeBool))
	expanded := y.To(x.Apply(y)).Core() // λy. x(y), the η-long form of x

	boundVars := VarList{}
	boundVars.Add(x.AssertVar())
	pair := &_TermPair{
		t0:        Apply(g, expanded),
		t1:        Apply(h, expanded),
		boundVars: boundVars,
	}

	result := tryMillerPattern(t.Context(), g.AssertVar(), []Term{expanded}, pair)
	require.NotNil(t, result, "an η-expanded bound variable is a pattern argument")
	assert.Len(t, result.TermSubsts, 1)
	subst := result.TermSubsts[0]
	assert.True(t, subst.VarTerm.Equals(g.AssertVar()))
	assert.True(t, subst.Term.AlphaEquals(h.Core()),
		"expected witness h (η-collapse of λx. h(λy. x(y))); got %s", ext.PrintTerm(subst.Term))
}

// TestUnifyMillerPattern_FunctionTypedBoundArg_LargeTarget — a rule
// variable over sets of functions, `s : (B → A) → bool`, whose η-long
// form applies it to an η-expanded bound variable, against a target
// under nested binders: λx. s(λy. x(y)) ≐ λx. Q(λa b c d e. R(a, b, c,
// d, e, x(k))). Read modulo η the pair is a pattern and the one unifier
// is the target itself. The imitation chain the pair fell to before
// applies every helper to every enclosing binder, and its skeleton
// crosses the substitution size cut before the copy completes, so no
// unifier was found.
func TestUnifyMillerPattern_FunctionTypedBoundArg_LargeTarget(t *testing.T) {
	defer goleak.VerifyNone(t)

	fnT := MakeFun(TypeB, TypeA)
	x := Var("x", fnT)
	k := Var("k", TypeB)
	a, b, c, d, e := Var("a", TypeA), Var("b", TypeA), Var("c", TypeA), Var("d", TypeA), Var("e", TypeA)
	R := Var("R", MakeFun(TypeA, TypeA, TypeA, TypeA, TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(MakeFun(TypeA, TypeA, TypeA, TypeA, TypeA, TypeBool), TypeBool))
	s := Var("s", MakeFun(fnT, TypeBool))
	body := Q.Apply(a.To(b.To(c.To(d.To(e.To(R.Apply(a, b, c, d, e, x.Apply(k))))))))

	ground := VarList{}
	ground.Add(k.AssertVar())
	ground.Add(R.AssertVar())
	ground.Add(Q.AssertVar())

	substs := UnifyTerms(t.Context(), x.To(s.Apply(x)), x.To(body), ground.HasName)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(s.AssertVar(), x.To(body))})
}

// TestMatchFlexibleRigid_BaseVar_BoundVarInGroundTarget_FailsAtOnce —
// λx. f(M, x) ≐ λx. f(g(x, c), x): after the binder is stripped the pair
// M ≐ g(x, c) has x bound and no meta-variable in it, so no unifier
// exists (M's instantiation cannot mention x, and nothing in g(x, c)
// can erase it). The verdict is reached without imitating g(x, c).
func TestMatchFlexibleRigid_BaseVar_BoundVarInGroundTarget_FailsAtOnce(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := ext.TestConst("f", MakeFun(TypeInd, TypeInd, TypeInd))
	g := ext.TestConst("g", MakeFun(TypeInd, TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	x := Var("x", TypeInd)
	m := Var("M", TypeInd)
	// A deep ground payload under the bound variable: the old chain
	// imitated all of it before failing at x.
	var payload Term = c
	for range 128 {
		payload = f.Apply(payload, c)
	}
	lhs := Abs(x.AssertVar(), f.Apply(m, x))
	rhs := Abs(x.AssertVar(), f.Apply(g.Apply(x, payload), x))

	substs := UnifyTerms(t.Context(), lhs, rhs, utils.EmptyPredicate)

	assert.Nil(t, substs)
}

// TestMatchFlexibleRigid_BaseVar_BoundVarBesideMetaVar_FallsThrough —
// the carve-out of the verdict above: with a meta-variable N in the
// target, λx. f(M, x) ≐ λx. f(g(N(x), c), x) IS solvable (N ↦ λy. H
// erases x), so the pair falls through to Huet's branches and finds a
// unifier.
func TestMatchFlexibleRigid_BaseVar_BoundVarBesideMetaVar_FallsThrough(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := ext.TestConst("f", MakeFun(TypeInd, TypeInd, TypeInd))
	g := ext.TestConst("g", MakeFun(TypeInd, TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	x := Var("x", TypeInd)
	m := Var("M", TypeInd)
	n := Var("N", MakeFun(TypeInd, TypeInd))
	lhs := Abs(x.AssertVar(), f.Apply(m, x))
	rhs := Abs(x.AssertVar(), f.Apply(g.Apply(n.Apply(x), c), x))

	substs := UnifyTerms(t.Context(), lhs, rhs, utils.EmptyPredicate)

	assert.NotEmpty(t, substs)
	for _, s := range substs {
		assert.True(t, ext.BetaEtaEquals(context.Background(), lhs.Substitute(s...), rhs.Substitute(s...)))
	}
}
