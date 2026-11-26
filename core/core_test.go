package core

import (
	"context"
	"fmt"
	"math/rand"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

var (
	indType = MakeCompositeType(MakeMetaType("ind", 0))
	intType = MakeCompositeType(MakeMetaType("int", 0))
	plus    = MakeConstTerm(
		MakeConstMeta("Plus", MakeFun(TypeA(), TypeA(), TypeA())),
		MakeFun(intType, intType, intType))
	one   = MakeConstTerm(MakeConstMeta("1", intType), intType)
	plus1 = Apply(plus, one)

	a   = Var("a", TypeA())
	x   = Var("x", intType)
	y   = Var("y", intType)
	z   = Var("z", intType)
	xP1 = Apply(plus1, x)
	yP1 = Apply(plus1, y)
	zP1 = Apply(plus1, z)
	X   = Var("X", intType)
	Y   = Var("Y", intType)
)

func TestTypeMatch(t *testing.T) {
	// fullVarTypePredicate is a predicate function that accepts all type variables
	fullVarTypePredicate := utils.FullPredicate[VarType]

	// Test: Type variable A should match concrete type Ind
	substs, ok := TypeA().Matches(indType, fullVarTypePredicate)
	// Tests that type variable A matches the concrete type Ind
	assert.True(t, ok, "Type variable A should match concrete type Ind")
	// Tests that exactly one substitution is generated: A ↦ Ind
	assert.Equal(t, len(substs), 1, "Should generate one substitution")
	// Tests that the variable in the substitution is A
	assert.True(t, substs[0].VarType.Equals(TypeA()), "Substitution variable should be A")
	// Tests that A is substituted with Ind
	assert.True(t, substs[0].HolType.Equals(indType), "A should be substituted with Ind")

	// Test: Type variable A should also match itself, with empty σ
	// (no substitution required — identity entries are stripped at the
	// producer side, see VarType.Matches).
	substs, ok = TypeA().Matches(TypeA(), fullVarTypePredicate)
	assert.True(t, ok, "Type variable A should match itself")
	assert.Empty(t, substs, "Identical vars need no substitution — empty σ")

	// Test: Concrete type Ind cannot match type variable A
	substs, ok = indType.Matches(TypeA(), fullVarTypePredicate)
	// Tests that concrete type Ind does not match type variable A (not symmetrical)
	assert.False(t, ok, "Concrete type Ind should not match type variable A")
	// Tests that no substitutions are generated for failed matches
	assert.Empty(t, substs, "Should not generate any substitutions")

	// Test: Concrete type Ind can match itself
	substs, ok = indType.Matches(indType, fullVarTypePredicate)
	// Tests that concrete type Ind matches itself
	assert.True(t, ok, "Concrete type Ind can match itself")
	// Tests that no substitutions are needed when matching identical concrete types
	assert.Empty(t, substs, "Matching identical concrete types requires no substitutions")

	// Test: Function type (A→A) can match concrete function type (Ind→Ind)
	substs, ok = MakeFun(TypeA(), TypeA()).Matches(
		MakeFun(indType, indType), fullVarTypePredicate)
	// Tests that function type A→A matches Ind→Ind
	assert.True(t, ok, "Function type (A→A) should match concrete function type (Ind→Ind)")
	// Tests that exactly one substitution is generated: A ↦ Ind
	assert.Equal(t, len(substs), 1, "Should generate one substitution")
	// Tests that the variable in the substitution is A
	assert.True(t, substs[0].VarType.Equals(TypeA()), "Substitution variable should be A")
	// Tests that A is substituted with Ind
	assert.True(t, substs[0].HolType.Equals(indType), "A should be substituted with Ind")

	// Test: Function type with multiple type variables (A→B) can match concrete function type (Ind→Ind)
	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(indType, indType), fullVarTypePredicate)
	// Tests that function type A→B matches Ind→Ind
	assert.True(t, ok, "Function type (A→B) should match concrete function type (Ind→Ind)")
	// Tests that exactly two substitutions are generated: A ↦ Ind, B ↦ Ind
	assert.Equal(t, len(substs), 2, "Should generate two substitutions")
	// Tests that the first variable in the substitution is A
	assert.True(t, substs[0].VarType.Equals(TypeA()), "First substitution variable should be A")
	// Tests that A is substituted with Ind
	assert.True(t, substs[0].HolType.Equals(indType), "A should be substituted with Ind")
	// Tests that the second variable in the substitution is B
	assert.True(t, substs[1].VarType.Equals(MakeVarType("B")), "Second substitution variable should be B")
	// Tests that B is substituted with Ind
	assert.True(t, substs[1].HolType.Equals(indType), "B should be substituted with Ind")

	// Test: Types with same parameter but different return types cannot match
	substs, ok = MakeFun(TypeA(), TypeA()).Matches(
		MakeFun(indType, TypeBool()), fullVarTypePredicate)
	// Tests that function type A→A cannot match Ind→Bool due to inconsistent type structure
	assert.False(t, ok, "Types with consistent structure but different types should not match")
	// Tests that no substitutions are generated for failed matches
	assert.Empty(t, substs, "Should not generate any substitutions")

	// Test: Type variables once bound must remain consistent throughout the pattern
	substs, ok = MakeFun(TypeA(), TypeA()).Matches(
		MakeFun(TypeA(), TypeBool()), fullVarTypePredicate)
	// Tests that A→A cannot match A→Bool since A would need to match both A and Bool
	assert.False(t, ok, "Once A is bound to A, it cannot match Bool")
	// Tests that no substitutions are generated for failed matches
	assert.Empty(t, substs, "Should not generate any substitutions")

	substs, ok = MakeFun(TypeA(), TypeA()).Matches(
		MakeFun(TypeBool(), TypeA()), fullVarTypePredicate)
	// Tests that A→A cannot match Bool→A since A would need to match both Bool and A
	assert.False(t, ok, "Once A is bound to Bool, it cannot match A")
	// Tests that no substitutions are generated for failed matches
	assert.Empty(t, substs, "Should not generate any substitutions")

	substs, ok = MakeFun(TypeA(), TypeBool()).Matches(
		MakeFun(TypeBool(), TypeA()), fullVarTypePredicate)
	// Tests that A→Bool cannot match Bool→A due to incompatible structure
	assert.False(t, ok, "Inconsistent types cannot match")
	// Tests that no substitutions are generated for failed matches
	assert.Empty(t, substs, "Should not generate any substitutions")

	// Test: Type variables can match complex types
	substs, ok = TypeA().Matches(MakeFun(indType, indType), fullVarTypePredicate)
	// Tests that type variable A can match complex type Ind→Ind
	assert.True(t, ok, "Type variable A can match complex type (Ind→Ind)")
	// Tests that exactly one substitution is generated: A ↦ (Ind→Ind)
	assert.Equal(t, len(substs), 1, "Should generate one substitution")
	// Tests that the variable in the substitution is A
	assert.True(t, substs[0].VarType.Equals(TypeA()), "Substitution variable should be A")
	// Tests that A is substituted with Ind→Ind
	assert.True(t, substs[0].HolType.Equals(MakeFun(indType, indType)), "A should be substituted with (Ind→Ind)")

	// Test: Nested type matching
	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(MakeFun(indType, indType), indType), fullVarTypePredicate)
	// Tests that function type A→B matches (Ind→Ind)→Ind
	assert.True(t, ok, "Function type (A→B) should match nested function type ((Ind→Ind)→Ind)")
	// Tests that exactly two substitutions are generated: A ↦ (Ind→Ind), B ↦ Ind
	assert.Equal(t, len(substs), 2, "Should generate two substitutions")
	// Tests that the first variable in the substitution is A
	assert.True(t, substs[0].VarType.Equals(TypeA()), "First substitution variable should be A")
	// Tests that A is substituted with Ind→Ind
	assert.True(t, substs[0].HolType.Equals(MakeFun(indType, indType)), "A should be substituted with (Ind→Ind)")
	// Tests that the second variable in the substitution is B
	assert.True(t, substs[1].VarType.Equals(MakeVarType("B")), "Second substitution variable should be B")
	// Tests that B is substituted with Ind
	assert.True(t, substs[1].HolType.Equals(indType), "B should be substituted with Ind")

	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(MakeFun(indType, indType), indType), TypeA().equalsVar)
	// Tests that matching fails when only A is allowed in the predicate
	assert.False(t, ok)
	assert.Empty(t, substs)

	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(MakeFun(indType, indType), indType), MakeVarType("B").equalsVar)
	// Tests that matching fails when only B is allowed in the predicate
	assert.False(t, ok)
	assert.Empty(t, substs)

	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(MakeFun(indType, indType), indType), MakeVarType("C").equalsVar)
	// Tests that matching fails when only C is allowed in the predicate but not used in the pattern
	assert.False(t, ok)
	assert.Empty(t, substs)

	substs, ok = MakeFun(TypeA(), MakeVarType("B")).Matches(
		MakeFun(MakeFun(indType, indType), indType),
		func(v VarType) bool { return v.Equals(TypeA()) || v.Equals(MakeVarType("B")) })
	// Tests that matching succeeds when both A and B are allowed in the predicate
	assert.True(t, ok)
	assert.Equal(t, len(substs), 2)
	assert.True(t, substs[0].VarType.Equals(TypeA()))
	assert.True(t, substs[0].HolType.Equals(MakeFun(indType, indType)))
	assert.True(t, substs[1].VarType.Equals(MakeVarType("B")))
	assert.True(t, substs[1].HolType.Equals(indType))

	substs, ok = MakeFun(TypeA(), TypeA()).Matches(
		MakeFun(MakeFun(indType, indType), indType), fullVarTypePredicate)
	// Tests that A→A cannot match (Ind→Ind)→Ind because A would need to match both (Ind→Ind) and Ind
	assert.False(t, ok)
	assert.Empty(t, substs)
}

// TestMatchInto exercises MatchTypeInto — the env-threading public
// wrapper that shares one accumulated substitution slice across multiple
// match attempts.
//
// Two behaviors that distinguish MatchTypeInto from the one-shot
// `Matches` are exercised:
//
//  1. **Caller-supplied env**: prior bindings in `env` are consulted
//     for consistency on every VarType encounter. Matches always
//     starts from an empty env.
//  2. **Non-instantiable pattern var accepts target-equals**: when
//     `instantiable(pv)` is false, MatchTypeInto succeeds iff the
//     target literally equals pv. Matches rejects unconditionally.
//
// (2) is the load-bearing semantic that makes the merged walker
// usable: the adaptation sweep substitutes the bindings earlier
// anchors made into a lemma anchor before matching it, so the goal's
// own rigid letters stand in the pattern, and the walker must accept
// "rigid pat ≡ rigid tgt" rather than fall through to false.
func TestMatchInto(t *testing.T) {
	fullPred := utils.FullPredicate[VarType]
	TypeB := MakeVarType("B")
	TypeC := MakeVarType("C")
	onlyB := TypeB.equalsVar

	// Case 1: A vs A, fully instantiable, fresh env.
	// matchesImpl appends an identity {A,A} (intentional — the walker
	// needs identities in-flight for cross-position consistency, see
	// CompositeType.Matches doc). Public callers strip them; here we
	// observe the raw env state.
	{
		var env []TypeSubst
		ok := MatchTypeInto(TypeA(), TypeA(), fullPred, &env)
		assert.True(t, ok, "1: A vs A (fullPred) should succeed")
		assert.Equal(t, 1, len(env))
		assert.True(t, env[0].VarType.Equals(TypeA()) && env[0].HolType.Equals(TypeA()))
	}

	// Case 2: A vs bool, fresh env → bind A → bool.
	{
		var env []TypeSubst
		ok := MatchTypeInto(TypeA(), TypeBool(), fullPred, &env)
		assert.True(t, ok, "2: A vs bool should succeed")
		assert.Equal(t, 1, len(env))
		assert.True(t, env[0].VarType.Equals(TypeA()) && env[0].HolType.Equals(TypeBool()))
	}

	// Case 3: A vs bool, env already has {A,bool} → consistent, env unchanged.
	{
		env := []TypeSubst{{TypeA(), TypeBool()}}
		ok := MatchTypeInto(TypeA(), TypeBool(), fullPred, &env)
		assert.True(t, ok, "3: A vs bool with prior {A,bool} should succeed")
		assert.Equal(t, 1, len(env), "env should not grow on consistent prior")
	}

	// Case 4: A vs num, env already has {A,bool} → inconsistent.
	{
		env := []TypeSubst{{TypeA(), TypeBool()}}
		ok := MatchTypeInto(TypeA(), indType, fullPred, &env)
		assert.False(t, ok, "4: A vs Ind with prior {A,bool} should fail")
	}

	// Case 5: A vs A, only B is instantiable.
	// NEW behavior: rigid pattern var accepts target-literally-equal.
	// Previously matchesImpl returned false; now it returns true with
	// no env change.
	{
		var env []TypeSubst
		ok := MatchTypeInto(TypeA(), TypeA(), onlyB, &env)
		assert.True(t, ok, "5: rigid A vs A should succeed (new accept-on-equal semantic)")
		assert.Empty(t, env, "rigid identity should not extend env")
	}

	// Case 6: A vs B, only B is instantiable → A is rigid, B ≠ A → fail.
	{
		var env []TypeSubst
		ok := MatchTypeInto(TypeA(), TypeB, onlyB, &env)
		assert.False(t, ok, "6: rigid A vs B should fail (different vars)")
		assert.Empty(t, env)
	}

	// Case 7: A vs bool, only B is instantiable → A is rigid, target is
	// composite → fail (rigid pattern var can never match a composite).
	{
		var env []TypeSubst
		ok := MatchTypeInto(TypeA(), TypeBool(), onlyB, &env)
		assert.False(t, ok, "7: rigid A vs bool should fail (composite target)")
		assert.Empty(t, env)
	}

	// Case 8: fun(A,B) vs fun(bool,Ind), fullPred → bind both.
	{
		var env []TypeSubst
		ok := MatchTypeInto(
			MakeFun(TypeA(), TypeB),
			MakeFun(TypeBool(), indType),
			fullPred, &env)
		assert.True(t, ok, "8: fun(A,B) vs fun(bool,Ind) should succeed")
		assert.Equal(t, 2, len(env))
		assert.True(t, env[0].VarType.Equals(TypeA()) && env[0].HolType.Equals(TypeBool()))
		assert.True(t, env[1].VarType.Equals(TypeB) && env[1].HolType.Equals(indType))
	}

	// Case 9: fun(A,A) vs fun(bool,bool), fullPred → A bound once,
	// second encounter is env-lookup hit. Env carries the identity
	// {A,bool} but only once.
	{
		var env []TypeSubst
		ok := MatchTypeInto(
			MakeFun(TypeA(), TypeA()),
			MakeFun(TypeBool(), TypeBool()),
			fullPred, &env)
		assert.True(t, ok, "9: fun(A,A) vs fun(bool,bool) should succeed")
		assert.Equal(t, 1, len(env), "shared var should yield exactly one env entry")
		assert.True(t, env[0].VarType.Equals(TypeA()) && env[0].HolType.Equals(TypeBool()))
	}

	// Case 10: fun(A,A) vs fun(bool,Ind), fullPred → second A conflicts.
	// The env lookup catches it: A's first binding is bool, and the
	// second occurrence must meet that binding literally. The
	// type-only matcher reads its bindings through the same lookup.
	{
		var env []TypeSubst
		ok := MatchTypeInto(
			MakeFun(TypeA(), TypeA()),
			MakeFun(TypeBool(), indType),
			fullPred, &env)
		assert.False(t, ok, "10: fun(A,A) vs fun(bool,Ind) should fail (shared-var inconsistency)")
	}

	// Cross-check: caller-supplied env interacts correctly with composite
	// recursion. fun(A,B) with prior {A,bool} should bind B as new.
	{
		env := []TypeSubst{{TypeA(), TypeBool()}}
		ok := MatchTypeInto(
			MakeFun(TypeA(), TypeB),
			MakeFun(TypeBool(), indType),
			fullPred, &env)
		assert.True(t, ok)
		assert.Equal(t, 2, len(env))
		assert.True(t, env[1].VarType.Equals(TypeB) && env[1].HolType.Equals(indType))
	}

	// Predicate selectivity: ensure we keep distinguishing C from
	// instantiable A/B. fun(A,C) with C not in instantiable, target
	// has C in matching position → succeed via new accept-on-equal.
	{
		var env []TypeSubst
		instAB := func(v VarType) bool { return v.Equals(TypeA()) || v.Equals(TypeB) }
		ok := MatchTypeInto(
			MakeFun(TypeA(), TypeC),
			MakeFun(TypeBool(), TypeC),
			instAB, &env)
		assert.True(t, ok, "rigid C vs C should succeed alongside A→bool")
		assert.Equal(t, 1, len(env))
		assert.True(t, env[0].VarType.Equals(TypeA()))
	}
}

// TestVarTypeMatches_NonInstantiableEquals verifies that the public
// single-shot VarType.Matches respects the same accept-on-equal
// semantic for non-instantiable pattern vars. This keeps Matches and
// matchesImpl behaviorally consistent — the unify package's
// gated callers (simplify.go) get a benign efficiency win (shortcut
// instead of full unification) when the pattern and target are the
// same rigid var.
func TestVarTypeMatches_NonInstantiableEquals(t *testing.T) {
	TypeB := MakeVarType("B")
	onlyB := TypeB.equalsVar

	// Rigid pattern var matched against literal equal → empty σ, true.
	substs, ok := TypeA().Matches(TypeA(), onlyB)
	assert.True(t, ok, "rigid A vs A should succeed")
	assert.Empty(t, substs, "identity match yields empty σ")

	// Rigid pattern var matched against a different var → false.
	substs, ok = TypeA().Matches(TypeB, onlyB)
	assert.False(t, ok, "rigid A vs B should fail")
	assert.Empty(t, substs)

	// Rigid pattern var matched against composite → false.
	substs, ok = TypeA().Matches(TypeBool(), onlyB)
	assert.False(t, ok, "rigid A vs composite should fail")
	assert.Empty(t, substs)

	// Composite with rigid var matched against identical structure
	// (only B instantiable, A appears rigidly in both pat and tgt
	// at the same position) → succeed with B binding.
	substs, ok = MakeFun(TypeA(), TypeB).Matches(MakeFun(TypeA(), indType), onlyB)
	assert.True(t, ok, "fun(A,B) vs fun(A,Ind) with only B instantiable should succeed")
	assert.Equal(t, 1, len(substs))
	assert.True(t, substs[0].VarType.Equals(TypeB) && substs[0].HolType.Equals(indType))
}

func TestLazy(t *testing.T) {
	typeB := MakeVarType("B")
	a, b, c := Var("a", typeB), Var("b", typeB), Var("c", typeB)

	assert.True(t,
		Eq(a, b).Fun().(AppliedTerm).Fun() ==
			Eq(b, c).Fun().(AppliedTerm).Fun())
	assert.True(t,
		Eq(Eq(a, b), Eq(a, b)).Fun().(AppliedTerm).Fun() ==
			Eq(Eq(b, c), Eq(b, c)).Fun().(AppliedTerm).Fun())

	// because Abs(a, b) and Abs(b, c) have same but not identical type ptrs.
	assert.False(t,
		Eq(Abs(a, b), Abs(a, b)).Fun().(AppliedTerm).Fun() ==
			Eq(Abs(b, c), Abs(b, c)).Fun().(AppliedTerm).Fun())

	// A settled lazy is read without allocating: the equality constant of
	// a type and the α-key of a variable are computed once and then only
	// loaded. (A wall-clock ratio stood here before; a sub-microsecond
	// single sample against a loop of a thousand cached reads failed on an
	// idle machine most of the time, so the check is the allocation count,
	// which the cache decides and the scheduler does not.)
	x, y := Var("x", MakeVarType("C")), Var("y", MakeVarType("C"))
	Eq(x, y)
	assert.Zero(t, testing.AllocsPerRun(100, func() { x.holType.eqTerm() }))
	x.AlphaKey()
	assert.Zero(t, testing.AllocsPerRun(100, func() { x.AlphaKey() }))
}

func TestAlpha(t *testing.T) {
	assertAlphaEq := func(s0, s1 Term) {
		assert.True(t, s0.AlphaEquals(s1))
		assert.True(t, s1.AlphaEquals(s0))
		assert.Equal(t, s0.Compare(s1), 0)
		assert.Equal(t, s1.Compare(s0), 0)
		assert.Equal(t, s0.AlphaKey(), s1.AlphaKey())
	}
	assertNotAlphaEq := func(s0, s1 Term) {
		assert.False(t, s0.AlphaEquals(s1))
		assert.False(t, s1.AlphaEquals(s0))
		assert.NotEqual(t, s0.Compare(s1), 0)
		assert.NotEqual(t, s1.Compare(s0), 0)
		assert.Equal(t, s0.Compare(s1)+s1.Compare(s0), 0)
		assert.NotEqual(t, s0.AlphaKey(), s1.AlphaKey())
	}

	assertAlphaEq(x, x)
	assertNotAlphaEq(x, y)

	assertNotAlphaEq(Eq(x, y), Eq(y, x))
	assertAlphaEq(Abs(x, xP1), Abs(y, yP1))
	assertNotAlphaEq(Abs(x, yP1), Abs(y, yP1))
	assertNotAlphaEq(Abs(x, yP1), Abs(y, xP1))
	assertAlphaEq(
		Abs(z, Abs(y, xP1)), Abs(y, Abs(z, xP1)))
	assertAlphaEq(
		Abs(z, Abs(y, xP1)), Abs(y, Abs(y, xP1)))
	assertNotAlphaEq(
		Abs(z, Abs(y, zP1)), Abs(y, Abs(y, yP1)))
	assertAlphaEq(
		Abs(z, Abs(y, zP1)), Abs(y, Abs(z, yP1)))
	assertAlphaEq(
		Abs(y, Abs(z, zP1)), Abs(y, Abs(y, yP1)))
	assertAlphaEq(
		Abs(z, Abs(z, zP1)), Abs(y, Abs(y, yP1)))
	assertNotAlphaEq(
		Hilbert(y, Eq(x, y)), Hilbert(x, Eq(x, x)))
	assertNotAlphaEq(
		Hilbert(y, Eq(x, y)), Hilbert(x, Eq(x, y)))
	assertAlphaEq(
		Hilbert(y, Eq(x, y)), Hilbert(z, Eq(x, z)))
	assertAlphaEq(
		Abs(x, Hilbert(y, Eq(x, y))), Abs(z, Hilbert(x, Eq(z, x))))

	assertNotAlphaEq(TypeBool().eqTerm(), TypeA().eqTerm())

	f := Var("f", MakeFun(intType, TypeBool()))
	fx := Apply(f, x)
	fX := Apply(f, X)
	xfx := Abs(x, fx)
	XfX := Abs(X, fX)
	fxfx := Abs(f, Abs(x, fx))
	fy := Apply(f, y)
	xfy := Abs(x, fy)
	yfy := Abs(y, fy)
	fxfy := Abs(f, Abs(x, fy))
	fyfy := Abs(f, Abs(y, fy))
	xfx_x := Apply(xfx, x)
	xfx_y := Apply(xfx, y)
	yfy_y := Apply(yfy, y)
	xfy_y := Apply(xfy, y)

	assertNotAlphaEq(fx, fy)
	assertAlphaEq(xfx, yfy)
	assertAlphaEq(xfx, XfX)
	assertNotAlphaEq(yfy, xfy)
	assertAlphaEq(Abs(x, xfx), Abs(y, xfx))
	assertAlphaEq(Abs(x, yfy), Abs(y, yfy))
	assertAlphaEq(Abs(x, xfx), Abs(y, yfy))
	assertNotAlphaEq(Abs(x, yfy), Abs(y, xfy))
	assertNotAlphaEq(Abs(x, xfy), Abs(y, xfy))
	assertNotAlphaEq(xfx_y, xfx_x)
	assertNotAlphaEq(yfy_y, xfx_x)
	assertNotAlphaEq(fxfx, fxfy)
	assertAlphaEq(fxfx, fyfy)
	assertAlphaEq(Abs(x, xfx), Abs(y, xfx))
	assertAlphaEq(
		Abs(x, Eq(Eq(x, y), Eq(xfx, xfy))),
		Abs(z, Eq(Eq(z, y), Eq(xfx, xfy))))

	assert.NotEqual(t,
		TestThm(fx).AlphaKey(),
		TestThm(fy).AlphaKey())
	assert.NotEqual(t,
		TestThm(fx, xfx_y).AlphaKey(),
		TestThm(fy, xfx_y).AlphaKey())
	assert.Equal(t,
		TestThm(fx, xfx_y).AlphaKey(),
		TestThm(fx, yfy_y).AlphaKey())
	assert.NotEqual(t,
		TestThm(fx, xfx_y).AlphaKey(),
		TestThm(fy, yfy_y).AlphaKey())
	assert.Equal(t,
		TestThm(fy, xfx_y, xfy_y).AlphaKey(),
		TestThm(fy, xfy_y, xfx_y).AlphaKey())
	assert.Equal(t,
		TestThm(fy, xfx_y, xfy_y).AlphaKey(),
		TestThm(fy, xfy_y, yfy_y).AlphaKey())
	assert.NotEqual(t,
		TestThm(fy, xfx_y, xfy_y).AlphaKey(),
		TestThm(fx, xfy_y, yfy_y).AlphaKey())
	assert.NotEqual(t,
		TestThm(fy, xfx_y, xfx_x).AlphaKey(),
		TestThm(fy, xfx_y, yfy_y).AlphaKey())
	assert.Equal(t,
		TestThm(fy, xfx_y).AlphaKey(),
		TestThm(fy, xfx_y, yfy_y).AlphaKey())
}

func TestTermCompare(t *testing.T) {
	assertLess := func(s0, s1 Term) {
		assert.Equal(t, s0.Compare(s1), -1)
		assert.Equal(t, s1.Compare(s0), 1)
		assert.False(t, s0.AlphaEquals(s1))
		assert.False(t, s1.AlphaEquals(s0))
		assert.NotEqual(t, s0.AlphaKey(), s1.AlphaKey())
	}

	f := Var("f", MakeFun(intType, TypeBool()))
	g := Var("g", MakeFun(intType, TypeBool()))
	fx := Apply(f, x)
	fX := Apply(f, X)
	gx := Apply(g, x)
	xfx := Abs(x, fx)
	XfX := Abs(X, fX)
	xgx := Abs(x, gx)
	fy := Apply(f, y)
	fY := Apply(f, Y)
	fz := Apply(f, z)
	xfy := Abs(x, fy)
	xfY := Abs(x, fY)
	yfy := Abs(y, fy)
	xfz := Abs(x, fz)
	zfy := Abs(z, fy)
	zfz := Abs(z, fz)
	xfx_x := Apply(xfx, x)
	xfx_y := Apply(xfx, y)
	yfy_y := Apply(yfy, y)
	xfy_y := Apply(xfy, y)

	assertLess(a, f)
	assertLess(f, x)
	assertLess(X, x)
	assertLess(x, plus)
	assertLess(x, y)
	assertLess(f, g)
	assertLess(fX, fx)
	assertLess(fx, fy)
	assertLess(fx, gx)
	assertLess(fy, gx)
	assertLess(xfy, xfx)
	assertLess(xfY, xfx)
	assertLess(xfY, XfX)
	assertLess(xfz, xfx)
	assertLess(xfy, xfz)
	assertLess(xfx, xgx)
	assertLess(xfy, zfz)
	assertLess(zfy, zfz)
	assertLess(xfy, yfy)
	assertLess(xfy_y, xfx_y)
	assertLess(xfy_y, yfy_y)
	assertLess(xfx_x, xfx_y)
	assertLess(xfx_x, yfy_y)
	assertLess(Eq(a, a), Eq(x, x))
	assertLess(Eq(X, X), Eq(x, x))
	assertLess(Eq(f, f), Eq(X, X))
	assertLess(Abs(g, gx), Abs(f, fy))
	assertLess(Abs(y, xfy), Abs(y, xfx))
	assertLess(Abs(x, xfz), Abs(y, xfy))
	assertLess(Abs(x, xfy), Abs(x, xfz))
	assertLess(Abs(z, zfy), Abs(x, xfz))
	assertLess(Abs(y, xfz), Abs(y, zfy))
	assertLess(Abs(y, xfz), Abs(z, xfz))
	assertLess(Var("%1", TypeA()), deBruijnVar(1, TypeA()))
	assertLess(deBruijnVar(9, intType), deBruijnVar(10, intType))

	s0 := Abs(x, Abs(y, Apply(Apply(plus, x), y)))
	s1 := Abs(y, Abs(x, Apply(Apply(plus, x), y)))
	s2 := Abs(y, Abs(x, Apply(Apply(plus, z), y)))
	s3 := Abs(x, Abs(x, Apply(Apply(plus, z), x)))
	assertLess(s0, s1)
	assertLess(s2, s0)
	assertLess(s2, s1)
	assertLess(s2, s3)
}

func TestTermFrees(t *testing.T) {
	checkFree := func(term Term, vars ...Term) {
		assert.ElementsMatch(t, term.Frees(nil), vars)
	}

	checkFree(x, x)
	assert.True(t, x.HasFree(x))

	checkFree(plus1)

	checkFree(xP1, x)
	assert.True(t, xP1.HasFree(x))

	checkFree(Abs(x, xP1))

	checkFree(Abs(x, yP1), y)
	assert.True(t, Abs(x, yP1).HasFree(y))

	checkFree(Eq(x, x), x)
	assert.True(t, Eq(x, x).HasFree(x))

	checkFree(Eq(x, y), x, y)
	assert.True(t, Eq(x, y).HasFree(x))
	assert.True(t, Eq(x, y).HasFree(y))

	checkFree(Hilbert(x, Eq(x, x)))

	checkFree(Hilbert(x, Eq(x, y)), y)
	assert.True(t, Hilbert(x, Eq(x, y)).HasFree(y))

	checkFree(Eq(Abs(x, y), Abs(y, yP1)), y)
	assert.True(t, Eq(Abs(x, y), Abs(y, yP1)).HasFree(y))

	assert.ElementsMatch(t,
		Eq(Abs(x, y), Abs(y, yP1)).Frees(x.EqualsVar), nil)
	assert.ElementsMatch(t,
		Eq(Abs(x, y), Abs(y, yP1)).Frees(y.EqualsVar), []Term{y})
	assert.ElementsMatch(t,
		Eq(Abs(x, y), Abs(y, yP1)).Frees(z.EqualsVar), nil)

	assert.True(t, xP1.AllFree(x.EqualsVar))
	assert.False(t, xP1.AllFree(y.EqualsVar))
	assert.True(t, Abs(x, xP1).AllFree(x.EqualsVar))
	assert.True(t, Abs(y, xP1).AllFree(x.EqualsVar))
	assert.False(t, Abs(y, xP1).AllFree(y.EqualsVar))
}

func TestTermHasFreeName(t *testing.T) {
	assert.True(t, xP1.HasFreeName("x"))
	assert.False(t, xP1.HasFreeName("y"))
	assert.False(t, xP1.HasFreeName("1"))
	assert.False(t, Abs(x, xP1).HasFreeName("x"))
	assert.True(t, Apply(Abs(x, xP1), y).HasFreeName("y"))
	assert.False(t, Apply(Abs(x, xP1), y).HasFreeName("x"))
	assert.True(t, Apply(Abs(x, xP1), x).HasFreeName("x"))
	assert.False(t, Abs(x, Apply(Abs(x, xP1), x)).HasFreeName("x"))

	v1 := deBruijnVar(1, intType)
	v2 := deBruijnVar(2, intType)
	assert.False(t, Abs(v1, v2).HasFreeName("%1"))
	assert.True(t, Abs(v1, v2).HasFreeName("%2"))
}

func TestTermSubstitute(t *testing.T) {
	assertTermSubstitute := func(t0, t1 Term, subst ...TermSubst) {
		assert.True(t, t1.Equals(t0.Substitute(subst...)))
	}

	// "x+1 : [x->y] : y+1"
	assertTermSubstitute(xP1, yP1, MakeTermSubst(x, y))
	// Tests that substituting y for x in x+1 produces y+1: (x+1)[y/x] = y+1

	// "λx.x+1 : [x->x] : λx.x+1"
	assertTermSubstitute(Abs(x, xP1), Abs(x, xP1), MakeTermSubst(x, x))
	// Tests that substituting x for x in λx.x+1 doesn't change the term: (λx.x+1)[x/x] = λx.x+1
	// This is because x is bound in λx.x+1, so the substitution doesn't affect it

	// "λx.x+1 : [x->y] : λx.x+1"
	assertTermSubstitute(Abs(x, xP1), Abs(x, xP1), MakeTermSubst(x, y))
	// Tests that substituting y for x in λx.x+1 doesn't change the term: (λx.x+1)[y/x] = λx.x+1
	// Since x is bound in λx.x+1, the substitution [y/x] doesn't affect it

	// "x=y+1 : [y->x] : x=x+1"
	assertTermSubstitute(Eq(x, yP1), Eq(x, xP1), MakeTermSubst(y, x))
	// Tests that substituting x for y in x=y+1 produces x=x+1: (x=y+1)[x/y] = x=x+1

	// "λx.y+1 : [y->x] : λxʹ.x+1"
	freshXFromYToX := x.RenameToAvoid(yP1, xP1, x)
	assertTermSubstitute(
		Abs(x, yP1),
		Abs(freshXFromYToX, xP1),
		MakeTermSubst(y, x))
	// Tests variable capture avoidance: When substituting x for y in λx.y+1, we must rename the bound variable
	// (λx.y+1)[x/y] = λx'.x+1, where x' is a fresh variable to avoid capture

	// "λx.x+1 : [x->y] : λx.x+1"
	assertTermSubstitute(
		Abs(x, xP1),
		Abs(x, xP1),
		MakeTermSubst(x, y))
	// Tests again that substituting y for x in λx.x+1 doesn't change the term
	// Since x is bound in λx.x+1, the substitution [y/x] doesn't affect it

	// "λx.y+1 : [x->y] : λx.y+1"
	assertTermSubstitute(
		Abs(x, yP1),
		Abs(x, yP1),
		MakeTermSubst(x, y))

	// "λx.y+1 : [y->x, x->y] : λxʹ.x+1"
	freshXSwap0 := x.RenameToAvoid(yP1, xP1, x, y)
	assertTermSubstitute(
		Abs(x, yP1),
		Abs(freshXSwap0, xP1),
		MakeTermSubst(y, x), MakeTermSubst(x, y))
	// Tests simultaneous substitution with variable capture avoidance:
	// (λx.y+1)[y->x, x->y] = λx'.x+1, where x' is a fresh variable to avoid capture

	// "λx.y+1 : [x->y, y->x] : λxʹ.x+1"
	freshXSwap1 := x.RenameToAvoid(yP1, xP1, y, x)
	assertTermSubstitute(
		Abs(x, yP1),
		Abs(freshXSwap1, xP1),
		MakeTermSubst(x, y), MakeTermSubst(y, x))
	// Tests that the order of substitutions matters for simultaneous substitution:
	// Even though [x->y, y->x] is specified in a different order from [y->x, x->y],
	// the substitutions are applied simultaneously, giving the same result

	// "x=y+1 : [y->x, x->y] : y=x+1"
	assertTermSubstitute(
		Eq(x, yP1),
		Eq(y, xP1),
		MakeTermSubst(y, x), MakeTermSubst(x, y))
	// Tests simultaneous substitution: (x=y+1)[y->x, x->y] = y=x+1

	// "x=y+1 : [x->y, y->x] : y=x+1"
	assertTermSubstitute(
		Eq(x, yP1),
		Eq(y, xP1),
		MakeTermSubst(x, y), MakeTermSubst(y, x))
	// Tests that the order of substitutions doesn't matter for simultaneous substitution

	// "λx.x+y : [y->z+1] : λx.x+(z+1)"
	assertTermSubstitute(
		Abs(x, Apply(Apply(plus, y), x)),
		Abs(x, Apply(Apply(plus, zP1), x)),
		MakeTermSubst(y, zP1))
	// Tests substitution of a complex term: (λx.x+y)[y->z+1] = λx.x+(z+1)

	// "λx.x+y : [y->x+1] : λxʹ.xʹ+(x+1)"
	freshXFromYToXP1 := x.RenameToAvoid(
		Apply(Apply(plus, y), x),
		Apply(Apply(plus, xP1), x),
		xP1)
	assertTermSubstitute(
		Abs(x, Apply(Apply(plus, y), x)),
		Abs(freshXFromYToXP1,
			Apply(Apply(plus, xP1), freshXFromYToXP1)),
		MakeTermSubst(y, xP1))
	// Tests variable capture avoidance with a complex substitution:
	// (λx.x+y)[y->x+1] = λx'.x'+(x+1), where x' is a fresh variable to avoid capture

	P := Var("P", MakeFun(intType, TypeBool(), intType))
	q := Var("q", TypeBool())
	xBool := Var("x", TypeBool()) // xBool and x have the same name but different types.
	freshXForTypedBody := x.RenameToAvoid(
		y,
		Apply(Apply(P, x), xBool),
		Apply(Apply(P, x), xBool))
	assertTermSubstitute(
		Abs(x, y),
		Abs(freshXForTypedBody, Apply(Apply(P, x), xBool)),
		MakeTermSubst(y, Apply(Apply(P, x), xBool)))
	// Tests substitution with variable renaming due to potential confusion with same-named variables of different types:
	// (λx.y)[y->P(x,xBool)] = λx'.P(x,xBool), where xBool is x:bool (different type from x:int)
	assertTermSubstitute(
		Abs(x, y),
		Abs(x, Apply(Apply(P, y), q)),
		MakeTermSubst(y, Apply(Apply(P, y), q)))
	// Tests substitution that involves a recursive reference to the variable being substituted:
	// (λx.y)[y->P(y,q)] = λx.P(y,q), no renaming needed as x doesn't appear in the replacement
	assertTermSubstitute(
		Abs(x, y),
		Abs(x.Rename().Rename(), Apply(Apply(P, y), xBool)),
		MakeTermSubst(y, Apply(Apply(P, y), xBool)))

	f2 := Var("f", MakeFun(intType, intType, intType))
	nPrime := Var("n", intType)
	kPrime := Var("kʹ", intType)
	bodyWithPrime := Apply(Apply(f2, kPrime), nPrime)
	freshN := nPrime.RenameToAvoid(
		bodyWithPrime,
		Apply(Apply(f2, nPrime), nPrime),
		nPrime)
	assertTermSubstitute(
		Abs(nPrime, bodyWithPrime),
		Abs(freshN, Apply(Apply(f2, nPrime), freshN)),
		MakeTermSubst(kPrime, nPrime))
}

func TestDeBruijn(t *testing.T) {

	abs := Abs(x, x).DeBruijn(0).(AbsTerm)
	xVar0, xVar1 := abs.Var(), abs.Body().(VarTerm)
	assert.True(t, xVar0.Equals(deBruijnVar(1, intType)))
	assert.True(t, xVar1.Equals(deBruijnVar(1, intType)))
	assert.EqualValues(t, xVar0.name, utils.PercentStr+"1")
	assert.Equal(t, xVar0.deBruijn, 1)
	assert.EqualValues(t, xVar1.name, utils.PercentStr+"1")
	assert.Equal(t, xVar1.deBruijn, 1)

	abs = Abs(x, x).ChangeAbsVar(xVar0.name)
	xVar0, xVar1 = abs.Var(), abs.Body().(VarTerm)
	assert.EqualValues(t, xVar0.name, utils.MacronStr+"1")
	assert.Equal(t, xVar0.deBruijn, 0)
	assert.EqualValues(t, xVar1.name, utils.MacronStr+"1")
	assert.Equal(t, xVar1.deBruijn, 0)

	assertDeBruijn := func(s0, s1 Term, endingLevels ...int) {
		endingLevel := 0
		if len(endingLevels) > 0 {
			endingLevel = endingLevels[0]
		}
		assert.True(t, s0.deBruijnImpl(1, endingLevel, nil).Equals(s1))
		assert.True(t, s0.deBruijnImpl(1, endingLevel, nil).deBruijnImpl(1, endingLevel, nil).Equals(s1))
		assert.True(t, s0.deBruijnImpl(1, endingLevel, nil).AlphaEquals(s0))
		assert.Equal(t, s0.deBruijnImpl(1, endingLevel, nil).AlphaKey(), s1.AlphaKey())
		assert.True(t, deBruijnCheck(s0.deBruijnImpl(1, endingLevel, nil), 1, endingLevel))
	}

	v1 := deBruijnVar(1, intType)
	v2 := deBruijnVar(2, intType)
	v3 := deBruijnVar(3, intType)
	g := Var("g", MakeFun(intType, TypeBool()))
	P := Var("P", MakeFun(intType, intType, intType, TypeBool()))
	Q := Var("Q", MakeFun(intType, MakeFun(intType, TypeBool()), intType))
	v2Func := deBruijnVar(2, MakeFun(intType, TypeBool()))
	R := Var("R", MakeFun(MakeFun(intType, intType), intType, TypeBool()))
	s := Abs(z, Abs(y, Apply(Apply(R, Abs(x, y)), z)))

	// Test: λv₁.v₁ → λv₁.v₁ (Identity function with de Bruijn indices)
	assertDeBruijn(
		Abs(v1, v1),
		Abs(v1, v1))
	// Test: λv₁.v₂ → λv₁.v₂ (Function that returns a free variable v₂)
	assertDeBruijn(
		Abs(v1, v2),
		Abs(v1, v2))
	// Test: λv₁.v₃ → λv₁.v₃ (Function that returns a free variable v₃)
	assertDeBruijn(
		Abs(v1, v3),
		Abs(v1, v3))
	// Test: λv₂.v₂ → λv₁.v₁ (Identity function with renamed variables to de Bruijn index)
	assertDeBruijn(
		Abs(v2, v2),
		Abs(v1, v1))
	// Test: λv₃.v₃ → λv₁.v₁ (Identity function with different variable names converted to de Bruijn)
	assertDeBruijn(
		Abs(v3, v3),
		Abs(v1, v1))
	// Test: λv₃.v₂ → λv₁.v₂ (Function returning free variable v₂, with variable renaming)
	assertDeBruijn(
		Abs(v3, v2),
		Abs(v1, v2))
	// Test: λv₂.v₃ → λv₁.v₃ (Function returning free variable v₃, with variable renaming)
	assertDeBruijn(
		Abs(v2, v3),
		Abs(v1, v3))
	// Test: λv₂.v₁ → λv₂.v₁ (Function returning free variable v₁, preserving free variable)
	assertDeBruijn(
		Abs(v2, v1),
		Abs(v2, v1))
	// Test: λv₃.v₁ → λv₂.v₁ (Function returning free variable v₁, with bound variable renaming)
	assertDeBruijn(
		Abs(v3, v1),
		Abs(v2, v1))
	// Test: λv₁.λv₃.v₂ → λv₁.λv₃.v₂ (Nested abstractions with free variable)
	assertDeBruijn(
		Abs(v1, Abs(v3, v2)),
		Abs(v1, Abs(v3, v2)))

	// Test: λv₂.(v₂ + 1) → λv₁.(v₁ + 1) (Function applying plus1 to bound variable)
	assertDeBruijn(
		Abs(v2, Apply(plus1, v2)),
		Abs(v1, Apply(plus1, v1)))
	// Test: λv₃.(v₃ + 1) → λv₁.(v₁ + 1) (Same function with different variable name)
	assertDeBruijn(
		Abs(v3, Apply(plus1, v3)),
		Abs(v1, Apply(plus1, v1)))
	// Test: λv₁.(v₁ + 1) → λv₁.(v₁ + 1) (Function already in de Bruijn form)
	assertDeBruijn(
		Abs(v1, Apply(plus1, v1)),
		Abs(v1, Apply(plus1, v1)))
	// Test: λv₁.λv₂.v₁ → λv₁.λv₂.v₁ (Function returning outer bound variable)
	assertDeBruijn(
		Abs(v1, Abs(v2, v1)),
		Abs(v1, Abs(v2, v1)))
	// Test: λv₁.λv₃.v₁ → λv₁.λv₂.v₁ (Same function with different inner variable name)
	assertDeBruijn(
		Abs(v1, Abs(v3, v1)),
		Abs(v1, Abs(v2, v1)))
	// Test: λv₂.λv₃.v₂ → λv₁.λv₂.v₁ (K combinator with different variable names)
	assertDeBruijn(
		Abs(v2, Abs(v3, v2)),
		Abs(v1, Abs(v2, v1)))
	// Test: λv₂.λv₃.v₃ → λv₁.λv₂.v₂ (Identity function inside abstraction with different names)
	assertDeBruijn(
		Abs(v2, Abs(v3, v3)),
		Abs(v1, Abs(v2, v2)))
	// Test: λv₂.((λv₁.v₁) v₂) → λv₁.((λv₂.v₂) v₁) (Beta-redex with identity function)
	assertDeBruijn(
		Abs(v2, Apply(Abs(v1, v1), v2)),
		Abs(v1, Apply(Abs(v2, v2), v1)))
	// Test: λv₁.((λv₂.v₂) v₁) → λv₁.((λv₂.v₂) v₁) (Same beta-redex already in de Bruijn form)
	assertDeBruijn(
		Abs(v1, Apply(Abs(v2, v2), v1)),
		Abs(v1, Apply(Abs(v2, v2), v1)))
	// Test: λv₁.((λv₃.v₃) v₁) → λv₁.((λv₂.v₂) v₁) (Beta-redex with variable renaming in inner abstraction)
	assertDeBruijn(
		Abs(v1, Apply(Abs(v3, v3), v1)),
		Abs(v1, Apply(Abs(v2, v2), v1)))
	// Test: λv₁.λv₂.λv₃.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₁,v₂,v₃) (Three-level nested abstraction with predicate P)
	assertDeBruijn(
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v1), v2), v3)))))
	// Test: λv₁.λv₃.λv₂.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₁,v₃,v₂) (Three-level nested abstraction with reordered variables)
	assertDeBruijn(
		Abs(v1, Abs(v3, Abs(v2, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v1), v3), v2)))))
	// Test: λv₂.λv₁.λv₃.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₂,v₁,v₃) (Three-level nested abstraction with v₁ and v₂ swapped)
	assertDeBruijn(
		Abs(v2, Abs(v1, Abs(v3, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v2), v1), v3)))))
	// Test: λv₂.λv₃.λv₁.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₃,v₁,v₂) (Three-level nested abstraction with variables rotated)
	assertDeBruijn(
		Abs(v2, Abs(v3, Abs(v1, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v3), v1), v2)))))
	// Test: λv₃.λv₁.λv₂.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₂,v₃,v₁) (Three-level nested abstraction with variables in different positions)
	assertDeBruijn(
		Abs(v3, Abs(v1, Abs(v2, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v2), v3), v1)))))
	// Test: λv₃.λv₂.λv₁.P(v₁,v₂,v₃) → λv₁.λv₂.λv₃.P(v₃,v₂,v₁) (Three-level nested abstraction with v₁ and v₃ swapped)
	assertDeBruijn(
		Abs(v3, Abs(v2, Abs(v1, Apply(Apply(Apply(P, v1), v2), v3)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v3), v2), v1)))))

	// Test: λy.Q(v₁, λx.(g x)) → λv₂.Q(v₁, λv₃.(g v₃)) (Higher-order function with function application)
	assertDeBruijn(
		Abs(y, Apply(Apply(Q, v1), Abs(x, (Apply(g, x))))),
		Abs(v2, Apply(Apply(Q, v1), Abs(v3, (Apply(g, v3))))))
	// Test: λy.Q(v₁, λx.(g x)) → λv₂.Q(v₁, λx.(g x)) (Same expression with endingLevel=2)
	assertDeBruijn(
		Abs(y, Apply(Apply(Q, v1), Abs(x, (Apply(g, x))))),
		Abs(v2, Apply(Apply(Q, v1), Abs(x, (Apply(g, x))))),
		2)
	// Test: λy.Q(v₂, λx.(g x)) → λv₁.Q(v₂, λv₂.(g v₂)) (Higher-order function with different variable v₂)
	assertDeBruijn(
		Abs(y, Apply(Apply(Q, v2), Abs(x, (Apply(g, x))))),
		Abs(v1, Apply(Apply(Q, v2), Abs(v2, (Apply(g, v2))))))
	// Test: λy.Q(v₂, λx.(g x)) → λv₁.Q(v₂, λx.(g x)) (Same expression with endingLevel=2)
	assertDeBruijn(
		Abs(y, Apply(Apply(Q, v2), Abs(x, (Apply(g, x))))),
		Abs(v1, Apply(Apply(Q, v2), Abs(x, (Apply(g, x))))),
		2)

	// Test: λx.λg.λv₁.Q(v₁, g) → λv₁.λv₂ₛ.λv₃.Q(v₃, v₂ₛ) (Complex nested abstraction with function variable g)
	assertDeBruijn(
		Abs(x, Abs(g, Abs(v1, Apply(Apply(Q, v1), g)))),
		Abs(v1, Abs(v2Func, Abs(v3, Apply(Apply(Q, v3), v2Func)))))
	// Test: λx.λg.λv₁.Q(v₁, g) → λx.λg.λv₁.Q(v₁, g) (Same expression with endingLevel=1)
	assertDeBruijn(
		Abs(x, Abs(g, Abs(v1, Apply(Apply(Q, v1), g)))),
		Abs(x, Abs(g, Abs(v1, Apply(Apply(Q, v1), g)))),
		1)
	// Test: λx.λg.λv₁.Q(v₁, g) → λv₁.λg.λv₂.Q(v₂, g) (Partial de Bruijn conversion with endingLevel=2)
	assertDeBruijn(
		Abs(x, Abs(g, Abs(v1, Apply(Apply(Q, v1), g)))),
		Abs(v1, Abs(g, Abs(v2, Apply(Apply(Q, v2), g)))),
		2)
	// Test: λx.λg.λv₁.Q(v₁, g) → λv₁.λv₂ₛ.λv₃.Q(v₃, v₂ₛ) (Complete de Bruijn conversion with endingLevel=3)
	assertDeBruijn(
		Abs(x, Abs(g, Abs(v1, Apply(Apply(Q, v1), g)))),
		Abs(v1, Abs(v2Func, Abs(v3, Apply(Apply(Q, v3), v2Func)))),
		3)

	assert.Panics(t, func() { Abs(v2, v3).deBruijnImpl(1, 2, nil) })

	// Test: λx.(x+1) → λv₁.(v₁+1) (Simple abstraction with addition)
	assertDeBruijn(
		Abs(x, xP1),
		Abs(v1, Apply(plus1, v1)))
	// Test: λy.(x+1) → λv₁.(x+1) (Abstraction where variable doesn't appear in body)
	assertDeBruijn(
		Abs(y, xP1),
		Abs(v1, xP1))
	// Test: λy.(y=x) → λv₁.(v₁=x) (Abstraction with equality between bound and free variable)
	assertDeBruijn(
		Abs(y, Eq(y, x)),
		Abs(v1, Eq(v1, x)))
	// Test: λx.λy.(x=y) → λv₁.λv₂.(v₁=v₂) (Nested abstraction with equality between bound variables)
	assertDeBruijn(
		Abs(x, Abs(y, Eq(x, y))),
		Abs(v1, Abs(v2, Eq(v1, v2))))
	// Test: λx.λy.(y=y) → λv₁.λv₂.(v₂=v₂) (Nested abstraction with equality of inner bound variable)
	assertDeBruijn(
		Abs(x, Abs(y, Eq(y, y))),
		Abs(v1, Abs(v2, Eq(v2, v2))))
	// Test: λx.λy.(x=x) → λv₁.λv₂.(v₁=v₁) (Nested abstraction with equality of outer bound variable)
	assertDeBruijn(
		Abs(x, Abs(y, Eq(x, x))),
		Abs(v1, Abs(v2, Eq(v1, v1))))
	// Test: λx.((λx.x) x) → λv₁.((λv₂.v₂) v₁) (Beta-redex with variable shadowing)
	assertDeBruijn(
		Abs(x, Apply(Abs(x, x), x)),
		Abs(v1, Apply(Abs(v2, v2), v1)))
	// Test: λx.((λy.x) x) → λv₁.((λv₂.v₁) v₁) (Beta-redex where inner abstraction returns outer variable)
	assertDeBruijn(
		Abs(x, Apply(Abs(y, x), x)),
		Abs(v1, Apply(Abs(v2, v1), v1)))

	// Test: λz.λy.R(λx.y, z) → λv₁.λv₂.R(λv₃.v₂, v₁) (Higher-order function with function creation)
	assertDeBruijn(s,
		Abs(v1, Abs(v2, Apply(Apply(R, Abs(v3, v2)), v1))))

	s = Abs(z, Abs(y, Apply(Apply(R, Abs(x, y)), y)))
	// Test: λz.λy.R(λx.y, y) → λv₁.λv₂.R(λv₃.v₂, v₂) (Higher-order function with repeated variable)
	assertDeBruijn(s,
		Abs(v1, Abs(v2, Apply(Apply(R, Abs(v3, v2)), v2))))

	// Test: λy.((λx.x) y) → λv₁.((λx.x) v₁) (Beta-redex with partial de Bruijn conversion)
	assertDeBruijn(
		Abs(y, Apply(Abs(x, x), y)),
		Abs(v1, Apply(Abs(x, x), v1)), 2)
	// Test: λx.λy.λz.P(x,y,z) → λv₁.λy.λz.P(v₁,y,z) (Three-level abstraction with partial conversion)
	assertDeBruijn(
		Abs(x, Abs(y, Abs(z, Apply(Apply(Apply(P, x), y), z)))),
		Abs(v1, Abs(y, Abs(z, Apply(Apply(Apply(P, v1), y), z)))),
		2)
	// Test: λy.λx.λz.P(x,y,z) → λv₁.λv₂.λz.P(v₂,v₁,z) (Three-level abstraction with more conversion)
	assertDeBruijn(
		Abs(y, Abs(x, Abs(z, Apply(Apply(Apply(P, x), y), z)))),
		Abs(v1, Abs(v2, Abs(z, Apply(Apply(Apply(P, v2), v1), z)))),
		3)
	// Test: λy.λz.λx.P(x,y,z) → λv₁.λv₂.λv₃.P(v₃,v₁,v₂) (Complete three-level abstraction conversion)
	assertDeBruijn(
		Abs(y, Abs(z, Abs(x, Apply(Apply(Apply(P, x), y), z)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v3), v1), v2)))),
		4)

	// Test: λx.λy.λv₁.P(x,y,v₁) → λv₁.λy.λv₂.P(v₁,y,v₂) (Three-level abstraction with mixed variables)
	assertDeBruijn(
		Abs(x, Abs(y, Abs(v1, Apply(Apply(Apply(P, x), y), v1)))),
		Abs(v1, Abs(y, Abs(v2, Apply(Apply(Apply(P, v1), y), v2)))),
		2)
	// Test: λy.λx.λv₁.P(x,y,v₁) → λv₁.λv₂.λv₃.P(v₂,v₁,v₃) (Mixed variables with increased conversion)
	assertDeBruijn(
		Abs(y, Abs(x, Abs(v1, Apply(Apply(Apply(P, x), y), v1)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v2), v1), v3)))),
		3)
	// Test: λy.λz.λv₁.P(v₁,y,z) → λv₁.λv₂.λv₃.P(v₃,v₁,v₂) (Complex mixed variables conversion)
	assertDeBruijn(
		Abs(y, Abs(z, Abs(v1, Apply(Apply(Apply(P, v1), y), z)))),
		Abs(v1, Abs(v2, Abs(v3, Apply(Apply(Apply(P, v3), v1), v2)))),
		4)

	// Additional Edge Cases Tests

	// Edge Case 1: Index Collision Avoidance
	// When a term already contains a free De Bruijn variable that would conflict
	db2Free := Var(utils.MacronStr+"2", MakeFun(intType, intType)) // Will appear as ˍ2 (was %2)
	// Test: λx.ˍ2(x) with starting index 2 should adjust to avoid collision
	term1 := Abs(x, Apply(db2Free, x))
	result1 := term1.deBruijnImpl(2, 0, nil)
	// The bound variable should get index 2, and ˍ2 remains as free variable
	assert.True(t, result1.(AbsTerm).Var().Equals(v2))
	assert.True(t, result1.(AbsTerm).Body().(AppliedTerm).Fun().Equals(db2Free))

	// Edge Case 2: Empty Window (start == stop)
	// DeBruijnImpl(1,1) should return the original term unchanged
	term2 := Abs(x, Abs(y, Abs(z, Apply(Apply(Apply(P, x), y), z))))
	result2 := term2.deBruijnImpl(1, 1, nil)
	assert.True(t, result2.Equals(term2))

	// Edge Case 3: Invalid Window (start > stop when stop > 0)
	// DeBruijnImpl(5,3) should return the original term unchanged
	result3 := term2.deBruijnImpl(5, 3, nil)
	assert.True(t, result3.Equals(term2))

	// Edge Case 4: Starting Index Offset
	// DeBruijnImpl(2,4) - starting conversion at index 2
	result4 := term2.deBruijnImpl(2, 4, nil)
	assert.True(t, result4.(AbsTerm).Var().Equals(v2))
	assert.True(t, result4.(AbsTerm).Body().(AbsTerm).Var().Equals(v3))
	// Third level should not be converted (outside window [2,4))
	assert.Equal(t, result4.(AbsTerm).Body().(AbsTerm).Body().(AbsTerm).Var().deBruijn, 0)

	// Edge Case 5: DeBruijnImpl(3,0) - starting at index 3 with no limit
	f := Var("f", MakeFun(intType, intType))
	result5 := Abs(x, Abs(y, Apply(f, x))).deBruijnImpl(3, 0, nil)
	assert.True(t, result5.(AbsTerm).Var().Equals(v3))
	assert.True(t, result5.(AbsTerm).Body().(AbsTerm).Var().Equals(deBruijnVar(4, intType)))

	// Edge Case 6: Alpha-equivalence Preservation
	// λx.x and λy.y should map to the same De Bruijn form
	identity1 := Abs(x, x).DeBruijn(0)
	identity2 := Abs(y, y).DeBruijn(0)
	assert.True(t, identity1.Equals(identity2))
	assert.Equal(t, identity1.AlphaKey(), identity2.AlphaKey())

	// Edge Case 7: Idempotence - running DeBruijn twice returns same object
	normalized := Abs(x, Abs(y, x)).DeBruijn(0)
	normalized2 := normalized.DeBruijn(0)
	assert.True(t, normalized == normalized2) // Object identity check

	// Edge Case 8: Window with starting index offset
	// λa.λb.λc.λd.λe.a with starting index 2
	a := Var("a", intType)
	b := Var("b", intType)
	c := Var("c", intType)
	d := Var("d", intType)
	e := Var("e", intType)
	deepNested := Abs(a, Abs(b, Abs(c, Abs(d, Abs(e, a)))))
	// DeBruijnImpl(2, 5) converts first 3 abstractions using indices 2,3,4
	resultMiddle := deepNested.deBruijnImpl(2, 5, nil)
	firstAbs := resultMiddle.(AbsTerm)
	assert.True(t, firstAbs.Var().Equals(v2)) // First gets index 2
	secondAbs := firstAbs.Body().(AbsTerm)
	assert.True(t, secondAbs.Var().Equals(v3)) // Second gets index 3
	thirdAbs := secondAbs.Body().(AbsTerm)
	assert.True(t, thirdAbs.Var().Equals(deBruijnVar(4, intType))) // Third gets index 4
	// Fourth and fifth abstractions should not be converted (outside window [2,5))
	fourthAbs := thirdAbs.Body().(AbsTerm)
	assert.Equal(t, fourthAbs.Var().deBruijn, 0) // d remains unconverted
	fifthAbs := fourthAbs.Body().(AbsTerm)
	assert.Equal(t, fifthAbs.Var().deBruijn, 0) // e remains unconverted

	// Edge Case 9: Existing De Bruijn Variable as Free Variable
	// Create a term with %3 as a free variable
	db3Free := Var(utils.MacronStr+"3", MakeFun(intType, intType)) // ˍ3 (was %3)
	termWithDB3 := Abs(x, Abs(y, Apply(db3Free, x)))
	// Converting starting at index 1 should handle the existing %3
	resultDB3 := termWithDB3.deBruijnImpl(1, 0, nil)
	assert.True(t, resultDB3.(AbsTerm).Var().Equals(v1))
	assert.True(t, resultDB3.(AbsTerm).Body().(AbsTerm).Var().Equals(v2))
	// The free variable ˍ3 should remain unchanged
	innerApply := resultDB3.(AbsTerm).Body().(AbsTerm).Body().(AppliedTerm)
	assert.True(t, innerApply.Fun().Equals(db3Free))

	// Edge Case 10: Re-conversion of Partially Converted Terms
	// First, partially convert a term
	partial := Abs(x, Abs(y, Abs(z, Apply(g, x)))).deBruijnImpl(1, 3, nil)
	// This converts x->%1, y->%2, but leaves z unconverted
	// Now convert it again with different parameters
	reConverted := partial.deBruijnImpl(3, 5, nil)
	// When we apply DeBruijnImpl(3, 5) to a term that already has %1 and %2,
	// it starts fresh conversion using indices 3,4
	// So the result should be %3, %4 for the first two levels
	assert.True(t, reConverted.(AbsTerm).Var().Equals(v3))
	assert.True(t, reConverted.(AbsTerm).Body().(AbsTerm).Var().Equals(deBruijnVar(4, intType)))
	// The third abstraction (z) should not be converted (outside window [3,5))
	thirdLevel := reConverted.(AbsTerm).Body().(AbsTerm).Body().(AbsTerm)
	assert.Equal(t, thirdLevel.Var().deBruijn, 0)

	// Edge Case 11: Window Boundary Exactly at Abstraction
	// λx.λy.λz.x with window [1,2) - convert only the first abstraction
	boundaryTest := Abs(x, Abs(y, Abs(z, x)))
	boundaryResult := boundaryTest.deBruijnImpl(1, 2, nil)
	assert.True(t, boundaryResult.(AbsTerm).Var().Equals(v1))
	// Second and third should not be converted
	assert.Equal(t, boundaryResult.(AbsTerm).Body().(AbsTerm).Var().deBruijn, 0)
	assert.Equal(t, boundaryResult.(AbsTerm).Body().(AbsTerm).Body().(AbsTerm).Var().deBruijn, 0)

	// Edge Case 12: Shadow Binding with Different Indices
	// λx.(λx.x) with outer x converted to %1, inner x to %2
	shadowBinding := Abs(x, Abs(x, x))
	shadowResult := shadowBinding.DeBruijn(0)
	outerVar := shadowResult.(AbsTerm).Var()
	innerAbs := shadowResult.(AbsTerm).Body().(AbsTerm)
	innerVar := innerAbs.Var()
	// They should have different indices
	assert.True(t, outerVar.Equals(v1))
	assert.True(t, innerVar.Equals(v2))
	assert.NotEqual(t, outerVar.deBruijn, innerVar.deBruijn)

	// Edge Case 13: Complex Gap Scenario for deBruijnCheck
	// Manually create a term with index 4 when we expect 2 (gap exists)
	// This tests whether deBruijnCheck properly validates gaps
	// First create a normal term and convert it
	normalTerm := Abs(x, Abs(y, x)).DeBruijn(0)
	// The deBruijnCheck should validate it's correct
	assert.True(t, deBruijnCheck(normalTerm, 1, 0))
	// Check that re-conversion returns the same object (optimization)
	assert.True(t, normalTerm.DeBruijn(0) == normalTerm)
}

func TestRename(t *testing.T) {
	var varTerms []VarTerm

	for i := 'A'; i <= 'Z'; i++ {
		varTerms = append(varTerms, Var(string(i), TypeA()), Var(string(i)+utils.PrimeStr, TypeA()))
	}
	for i := 'a'; i <= 'z'; i++ {
		varTerms = append(varTerms, Var(string(i), TypeA()), Var(string(i)+utils.PrimeStr, TypeA()))
	}

	// A term that contains names from A, Aʹ, ... to z, zʹ.
	s := Term(varTerms[0])
	for _, v := range varTerms {
		s = Abs(v, s)
	}

	for i := range varTerms {
		if i%2 == 0 {
			assert.Equal(t,
				varTerms[i].RenameToAvoid(s).name,
				varTerms[i+1].RenameToAvoid(s).name)
		}
	}
}

func TestCore(t *testing.T) {
	type typeWrapper0 struct{ HolType }
	type typeWrapper1 struct{ typeWrapper0 }
	type0 := typeWrapper0{TypeA()}
	type1 := typeWrapper0{type0}
	type2 := typeWrapper1{type0}
	type3 := typeWrapper0{TypeBool()}
	assert.True(t, type0.Equals(type1))
	assert.True(t, type0.Equals(type2))
	assert.True(t, type1.Equals(type0))
	assert.True(t, type1.Equals(type2))
	assert.True(t, type2.Equals(type0))
	assert.True(t, type2.Equals(type1))
	assert.False(t, type0.Equals(type3))

	type termWrapper0 struct{ Term }
	type termWrapper1 struct{ termWrapper0 }
	t0 := termWrapper0{x}
	t1 := termWrapper0{t0}
	t2 := termWrapper1{t0}
	t3 := termWrapper0{y}
	assert.True(t, t0.Equals(t1))
	assert.True(t, t0.Equals(t2))
	assert.True(t, t1.Equals(t0))
	assert.True(t, t1.Equals(t2))
	assert.True(t, t2.Equals(t0))
	assert.True(t, t2.Equals(t1))
	assert.False(t, t0.Equals(t3))
	t4 := termWrapper0{Eq(t0, t3)}
	eqT0, eqT3, ok := MatchesEQ(t4)
	assert.True(t, ok)
	_, ok = eqT0.AsVar()
	assert.True(t, ok)
	_, ok = eqT3.AsVar()
	assert.True(t, ok)
	assert.True(t, eqT0.Equals(t0))
	assert.True(t, eqT3.Equals(t3))
	assert.True(t, t0.Equals(eqT0))
	assert.True(t, t3.Equals(eqT3))

	type propWrapper0 struct{ Prop }
	type propWrapper1 struct{ propWrapper0 }
	p := Var("p", TypeBool())
	q := Var("q", TypeBool())
	p0 := propWrapper0{MakeProp(p, q)}
	p1 := propWrapper0{p0}
	p2 := propWrapper1{p0}
	p3 := propWrapper0{MakeProp(q, p)}
	assert.True(t, p0.AlphaEquals(p1))
	assert.True(t, p0.AlphaEquals(p2))
	assert.True(t, p1.AlphaEquals(p0))
	assert.True(t, p1.AlphaEquals(p2))
	assert.True(t, p2.AlphaEquals(p0))
	assert.True(t, p2.AlphaEquals(p1))
	assert.False(t, p0.AlphaEquals(p3))
}

func TestAsThm(t *testing.T) {
	p := Var("p", TypeBool())
	q := Var("q", TypeBool())
	prop := MakeProp(p, q)
	assert.Panics(t, func() { prop.AsThmCert() })
	assert.False(t, prop.Proved())
	assert.False(t, prop.AsProp().Proved())

	thm := Assume(q)
	assert.NotPanics(t, func() { thm.AsThmCert() })
	assert.True(t, thm.Proved())
	assert.False(t, thm.AsProp().Proved())

	assert.Panics(t, func() { Deduct(prop, thm).AsThmCert() })
	assert.NotPanics(t, func() { Deduct(thm, thm).AsThmCert() })
}

func TestThmHyp(t *testing.T) {
	f := Var("f", MakeFun(intType, TypeBool()))
	fx := Apply(f, x)
	fy := Apply(f, y)

	assert.Panics(t, func() { Assume(f) })
	assert.True(t, Assume(fx).HasHyp(fx))
	assert.False(t, Assume(fx).HasHyp(fy))
	assert.True(t, Assume(fx).AnyHyp(func(t Term) bool {
		if t, ok := t.AsAppliedTerm(); ok && t.arg.Equals(x) {
			return true
		}
		return false
	}))
	assert.False(t, Assume(fx).AnyHyp(func(t Term) bool {
		if t, ok := t.AsAppliedTerm(); ok && t.arg.Equals(y) {
			return true
		}
		return false
	}))
	assert.False(t, Assume(fx).AnyHyp(func(t Term) bool {
		if _, ok := t.AsVar(); ok {
			return true
		}
		return false
	}))

	assert.True(t, Select(fx).HasHyp(fx))
	assert.False(t, Select(fx).HasHyp(fy))

	thm0 := Deduct(Assume(fx), Select(fy))

	assert.Equal(t, 2, thm0.NumHyps())
	assert.True(t, thm0.HasHyp(fx))
	assert.True(t, thm0.HasHyp(fy))
	assert.True(t, thm0.AnyHyp(func(t Term) bool {
		if t, ok := t.AsAppliedTerm(); ok && t.arg.Equals(x) {
			return true
		}
		return false
	}))
	assert.True(t, thm0.AnyHyp(func(t Term) bool {
		if t, ok := t.AsAppliedTerm(); ok && t.arg.Equals(y) {
			return true
		}
		return false
	}))
	assert.False(t, Assume(fx).AnyHyp(func(t Term) bool {
		if _, ok := t.AsVar(); ok {
			return true
		}
		return false
	}))

	thm1 := Deduct(Select(fx), Assume(fy))
	assert.Equal(t, 2, thm1.NumHyps())
	assert.False(t, thm0.Conclusion().Equals(thm1.Conclusion()))
	assert.True(t, thm0.Hyp(0).Equals(thm1.Hyp(0)))
	assert.True(t, thm0.Hyp(1).Equals(thm1.Hyp(1)))
}

func TestEquivalentPrimitives(t *testing.T) {
	p := Var("p", TypeBool())
	q := Var("q", TypeBool())
	r := Var("r", TypeBool())

	thm0 := TestThm(q, p)
	thm1 := TestThm(r, q)
	assert.True(t, DeriveTrans(thm0, thm1).AlphaEquals(EqMP(Deduct(thm0, thm1), thm0)))

	thm0 = TestThm(q, p)
	thm1 = TestThm(r)
	assert.True(t, DeriveTrans(thm0, thm1).AlphaEquals(EqMP(Deduct(thm0, thm1), thm0)))

	thm0 = TestThm(Eq(p, q))
	thm1 = TestThm(Eq(q, r))
	assert.True(t, EqTrans(thm0, thm1).
		AlphaEquals(EqMP(PropLeftApply(thm0.Conclusion().(AppliedTerm).Fun(), thm1), thm0)))

	thm0 = TestThm(Eq(p, q))
	eq := thm0.Conclusion().(AppliedTerm).Fun().(AppliedTerm).Fun()
	assert.True(t, EqSym(thm0).
		AlphaEquals(EqMP(PropRightApply(PropLeftApply(eq, thm0), p), Refl(p))))
}

// TestTypeSubstitute tests the type substitution functionality for Term
func TestTypeSubstitute(t *testing.T) {
	// Create test type substitutions
	typeAToBool := MakeTypeSubst(TypeA(), TypeBool())
	typeB := MakeVarType("B")
	typeBToInt := MakeTypeSubst(typeB, intType)

	// We need to manually implement type substitutions, as these functions
	// don't directly modify existing terms

	// Create variables with type variables A and B
	xA := Var("x", TypeA())
	yB := Var("y", typeB)
	zAToB := Var("z", MakeFun(TypeA(), typeB))

	// Test type substitution for variable terms
	xBool := xA.TypeSubstitute(typeAToBool)
	assert.True(t, xBool.Type().Equals(TypeBool()), "x's type should be bool after substitution")

	yInt := yB.TypeSubstitute(typeBToInt)
	assert.True(t, yInt.Type().Equals(intType), "y's type should be int after substitution")

	zBoolInt := zAToB.TypeSubstitute(typeAToBool, typeBToInt)
	assert.True(t, zBoolInt.Type().Equals(MakeFun(TypeBool(), intType)),
		"z's type should be bool→int after substitution")

	// Test type substitution for constant terms
	constTerm := MakeConstTerm(MakeConstMeta("C", TypeA()), TypeA())
	constBool := constTerm.TypeSubstitute(typeAToBool)
	assert.True(t, constBool.Type().Equals(TypeBool()), "Constant's type should be bool after substitution")

	// Test that PropTypeInst does not corrupt the caller's typeSubsts slice.
	// Regression: slices.DeleteFunc was used in-place on the variadic arg,
	// which shares the backing array with ConstTerm.typeSubsts. After one
	// call, identity substitutions were zeroed out, causing nil dereference
	// on subsequent calls.
	TypeC := MakeVarType("C")
	TypeD := MakeVarType("D")
	// absType: (B→C) → (A→B) → (A→C)  (like the "o" / function composition const)
	oAbsType := MakeFun(MakeFun(typeB, TypeC), MakeFun(TypeA(), typeB), MakeFun(TypeA(), TypeC))
	oMeta := MakeConstMeta("o_test", oAbsType)
	// Give it a def thm so DefThm() exercises PropTypeInst.
	oC := MakeConstTerm(oMeta, oAbsType)
	oMeta.def = makeThm(Eq(oC, oC)) // dummy def thm — just needs to be non-nil
	// Instantiate with C→D (A and B stay the same), producing identity substs.
	oHolType := MakeFun(MakeFun(typeB, TypeD), MakeFun(TypeA(), typeB), MakeFun(TypeA(), TypeD))
	oConcrete := MakeConstTerm(oMeta, oHolType)
	assert.False(t, oConcrete.DefThm().IsZero(), "first DefThm call should succeed")
	assert.False(t, oConcrete.DefThm().IsZero(), "second DefThm call must not panic from corrupted typeSubsts")
}

func TestAbsTypeSubstituteClash(t *testing.T) {
	TypeB := MakeVarType("B")
	TypeC := MakeVarType("C")

	xa := Var("x", TypeA())
	xb := Var("x", TypeB)
	xc := Var("x", TypeC)
	Pab := Var("P", MakeFun(TypeA(), TypeB, TypeBool()))
	Pcc := Var("P", MakeFun(TypeC, TypeC, TypeBool()))
	xcPrime := xc.Rename()
	xcPrimePrime := xcPrime.Rename()

	substs := []TypeSubst{
		MakeTypeSubst(TypeA(), TypeC),
		MakeTypeSubst(TypeB, TypeC)}

	var s0, s1 Term

	s0 = Abs(xa, xb)
	s1 = s0.TypeSubstitute(substs...)
	assert.True(t, s1.Type().Equals(MakeFun(TypeC, TypeC)))
	assert.True(t, s1.Equals(Abs(xcPrime, xc)))

	s0 = Abs(xa, Abs(xb, xc))
	s1 = s0.TypeSubstitute(substs...)
	assert.True(t, s1.Type().Equals(MakeFun(TypeC, TypeC, TypeC)))
	assert.True(t, s1.Equals(Abs(xcPrime, Abs(xcPrime, xc))))

	s0 = Abs(xa, Abs(xb, Apply(Apply(Pab, xa), xb)))
	s1 = s0.TypeSubstitute(substs...)
	assert.True(t, s1.Type().Equals(MakeFun(TypeC, TypeC, TypeBool())))
	assert.True(t, s1.Equals(
		Abs(xc, Abs(xcPrime, Apply(Apply(Pcc, xc), xcPrime)))))

	s0 = Abs(xb, Abs(xa, Apply(Apply(Pab, xa), xb)))
	s1 = s0.TypeSubstitute(substs...)
	assert.True(t, s1.Type().Equals(MakeFun(TypeC, TypeC, TypeBool())))
	assert.True(t, s1.Equals(
		Abs(xc, Abs(xcPrime, Apply(Apply(Pcc, xcPrime), xc)))))

	s0 = Abs(xc, Abs(xa, Apply(Apply(Pab, xa), xb)))
	s1 = s0.TypeSubstitute(substs...)

	assert.True(t, s1.Type().Equals(MakeFun(TypeC, TypeC, TypeBool())))
	assert.True(t, s1.Equals(
		Abs(xcPrime, Abs(xcPrimePrime, Apply(Apply(Pcc, xcPrimePrime), xc)))))

}

// ---------------------------------------------------------------------------
// NewTypeDef / TypeDefExpand tests
// ---------------------------------------------------------------------------

// newTypeDefFixture builds a fresh type definition for tests:
//   - source thm ⊢ P(a), where P is a closed const A→bool
//   - metaType "t", abs const "abs", rep const "rep"
func newTypeDefFixture() (srcThm ThmCert, metaType MetaType, abs, rep ConstTerm) {
	PMeta := MakeConstMeta("P", MakeFun(TypeA(), TypeBool()))
	P := MakeConstTerm(PMeta, MakeFun(TypeA(), TypeBool()))
	a := Var("a", TypeA())
	srcThm = TestThm(Apply(P, a))
	metaType, abs, rep = NewTypeDef(srcThm, "t", "abs", "rep")
	return
}

// NewTypeDef mints a type only on a certificate or a promise of one: a
// plain statement is refused, so a recorded source is never a claim
// nobody proved or promised.
func TestNewTypeDef_RefusesAPlainStatement(t *testing.T) {
	PMeta := MakeConstMeta("P", MakeFun(TypeA(), TypeBool()))
	P := MakeConstTerm(PMeta, MakeFun(TypeA(), TypeBool()))
	stmt := MakeProp(Apply(P, Var("a", TypeA())))
	assert.Panics(t, func() { NewTypeDef(stmt, "t_plain", "abs_plain", "rep_plain") },
		"a plain statement must not mint a type")

	promise := Promise(stmt, func(Forcer) ThmCert { return TestThm(Apply(P, Var("a", TypeA()))) })
	_, abs, _ := NewTypeDef(promise, "t_promised", "abs_promised", "rep_promised")
	assert.True(t, Force(context.Background(), AsThm(abs.Meta().DefSource())).AlphaEquals(stmt),
		"a promised source forces to its certificate")
}

func TestNewTypeDef_SetsPairAndSource(t *testing.T) {
	srcThm, metaType, abs, rep := newTypeDefFixture()

	absMeta, repMeta := abs.Meta(), rep.Meta()

	// Basic shape.
	assert.Equal(t, TermName("abs"), absMeta.Name())
	assert.Equal(t, TermName("rep"), repMeta.Name())
	assert.Equal(t, TypeName("t"), metaType.Name())

	// Asymmetric pair pointers: abs meta has repMeta set, rep meta has absMeta set.
	assert.True(t, absMeta.IsTypeDefAbs(), "abs meta should report IsTypeDefAbs")
	assert.False(t, absMeta.IsTypeDefRep())
	assert.True(t, repMeta.IsTypeDefRep(), "rep meta should report IsTypeDefRep")
	assert.False(t, repMeta.IsTypeDefAbs())

	assert.True(t, repMeta == absMeta.TypeDefCounterpart(),
		"abs.TypeDefCounterpart should be the rep meta")
	assert.True(t, absMeta == repMeta.TypeDefCounterpart(),
		"rep.TypeDefCounterpart should be the abs meta")

	// defSource preserves Thm-ness via t.Core() (Deduct-style pattern).
	assert.NotNil(t, absMeta.DefSource())
	assert.NotNil(t, repMeta.DefSource())
	assert.True(t, absMeta.DefSource().Proved(),
		"defSource should be Proved in the minting process (t.Core() preserves Thm under Prop interface)")
	assert.True(t, repMeta.DefSource().Proved())
	assert.True(t, absMeta.DefSource().AlphaEquals(srcThm),
		"defSource should α-equal the input thm")

	// Both metas share the same source pointer.
	assert.True(t, absMeta.DefSource() == repMeta.DefSource(),
		"abs and rep share one defSource instance")

	// Type 2 metas have no DefThm (the abs/rep axioms are derived on demand).
	assert.True(t, absMeta.DefThm().IsZero(), "Type 2 abs should have no DefThm")
	assert.True(t, repMeta.DefThm().IsZero(), "Type 2 rep should have no DefThm")
}

func TestTypeDefExpand_ProvedInput_LiftsToThm(t *testing.T) {
	_, _, abs, rep := newTypeDefFixture()
	absMeta, repMeta := abs.Meta(), rep.Meta()

	// Call on abs meta with its own Proved defSource → Thm outputs.
	out1, out2 := absMeta.TypeDefExpand(absMeta.DefSource())
	assert.True(t, out1.Proved(), "out1 should be Proved when input is Proved")
	assert.True(t, out2.Proved(), "out2 should be Proved when input is Proved")

	// Calling on rep meta produces α-equal outputs (symmetry).
	out1r, out2r := repMeta.TypeDefExpand(repMeta.DefSource())
	assert.True(t, out1.AlphaEquals(out1r), "out1 same regardless of which meta we call on")
	assert.True(t, out2.AlphaEquals(out2r), "out2 same regardless of which meta we call on")

	// out1 shape: ⊢ abs(rep(a)) = a. Conclusion is an equality.
	_, _, ok := MatchesEQ(out1.Conclusion())
	assert.True(t, ok, "out1's conclusion should be an equality (abs(rep(a)) = a)")

	// out2 shape: ⊢ P(r) = (rep(abs(r)) = r) — top-level equality.
	_, _, ok = MatchesEQ(out2.Conclusion())
	assert.True(t, ok, "out2's conclusion should be a top-level equality")
}

func TestTypeDefExpand_UnprovedInput_ReturnsProp(t *testing.T) {
	srcThm, _, abs, _ := newTypeDefFixture()

	// Strip Thm wrapper: MakeProp gives a bare proposition (not Thm),
	// mimicking what hydration from serialized bytes would produce.
	stripped := MakeProp(srcThm.Conclusion(), srcThm.Hyps()...)
	assert.False(t, stripped.Proved(), "stripped source should not be Proved")

	out1, out2 := abs.Meta().TypeDefExpand(stripped)
	assert.False(t, out1.Proved(), "out1 should NOT be Proved when input is unProved")
	assert.False(t, out2.Proved(), "out2 should NOT be Proved when input is unProved")

	// Outputs should still α-equal the Proved-input variant (structural equality).
	out1p, out2p := abs.Meta().TypeDefExpand(abs.Meta().DefSource())
	assert.True(t, out1.AlphaEquals(out1p))
	assert.True(t, out2.AlphaEquals(out2p))
}

func TestTypeDefExpand_AlphaMismatchPanics(t *testing.T) {
	_, _, abs, _ := newTypeDefFixture()

	// Construct a different source thm with a completely different predicate.
	QMeta := MakeConstMeta("Q", MakeFun(TypeA(), TypeBool()))
	Q := MakeConstTerm(QMeta, MakeFun(TypeA(), TypeBool()))
	b := Var("b", TypeA())
	wrongSrc := TestThm(Apply(Q, b))

	assert.Panics(t, func() {
		abs.Meta().TypeDefExpand(wrongSrc)
	}, "TypeDefExpand should panic when input does not α-equal defSource")
}

func TestNewConstDef_NotTypeDef(t *testing.T) {
	// Sanity: NewConstDef-created consts have DefThm but NOT DefSource / pair.
	body := Apply(
		MakeConstTerm(MakeConstMeta("f", MakeFun(TypeA(), TypeA())), MakeFun(TypeA(), TypeA())),
		Var("x", TypeA()))
	c := NewConstDef(Abs(Var("x", TypeA()), body), "g")
	meta := c.Meta()

	assert.False(t, meta.DefThm().IsZero(), "NewConstDef should set .def")
	assert.Nil(t, meta.DefSource(), "NewConstDef should NOT set .defSource")
	assert.False(t, meta.IsTypeDefAbs())
	assert.False(t, meta.IsTypeDefRep())
	assert.True(t, meta.TypeDefCounterpart().IsZero())
}

// stmtEq builds an unproved proposition ⊢ a = b over fresh bool vars, plus a
// genuine (test) certificate for it.
func eqProp(lname, rname string) (Prop, ThmCert) {
	l, r := Var(lname, TypeBool()), Var(rname, TypeBool())
	concl := Eq(l, r)
	return MakeProp(concl), TestThm(concl)
}

func TestBuilderRoot_ForceRunsBuilderOnce(t *testing.T) {
	stmt, cert := eqProp("a", "b")
	var calls atomic.Int32
	p := Promise(stmt, func(Forcer) ThmCert {
		calls.Add(1)
		return cert
	})

	// Proved() is a cheap readiness check: it must NOT run the builder.
	assert.False(t, p.Proved())
	assert.Equal(t, int32(0), calls.Load())

	got := Force(context.Background(), p)
	assert.True(t, got.AlphaEquals(stmt))
	assert.True(t, p.Proved())
	assert.True(t, p.AsThmCert().AlphaEquals(stmt))
	assert.Equal(t, int32(1), calls.Load())

	// Second force is memoized — builder not re-run.
	_ = Force(context.Background(), p)
	assert.Equal(t, int32(1), calls.Load())
}

func TestBuilderRoot_ConcurrentForceDedups(t *testing.T) {
	stmt, cert := eqProp("a", "b")
	var calls atomic.Int32
	start := make(chan struct{})
	p := Promise(stmt, func(Forcer) ThmCert {
		calls.Add(1)
		return cert
	})

	var wg sync.WaitGroup
	for i := 0; i < 16; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			got := Force(context.Background(), p)
			assert.True(t, got.AlphaEquals(stmt))
		}()
	}
	close(start)
	wg.Wait()
	assert.Equal(t, int32(1), calls.Load())
}

// A builder that returns a theorem whose statement does not match the promise
// is a soundness violation — settle panics rather than recording it.
func TestBuilderRoot_WrongThmPanics(t *testing.T) {
	stmt, _ := eqProp("a", "b")
	_, wrong := eqProp("c", "d") // a different statement
	p := Promise(stmt, func(Forcer) ThmCert { return wrong })
	assert.Panics(t, func() { Force(context.Background(), p) })
	assert.False(t, p.Proved())
}

// A builder that cannot produce its theorem panics; the panic propagates out of
// Force (there is no error to hand back).
func TestBuilderRoot_BuilderPanicPropagates(t *testing.T) {
	stmt, _ := eqProp("a", "b")
	p := Promise(stmt, func(Forcer) ThmCert { panic("boom") })
	assert.PanicsWithValue(t, "boom", func() { Force(context.Background(), p) })
	assert.False(t, p.Proved())
}

// A builder panic POISONS the cell: every later Force re-panics with the
// recorded value instead of parking forever on done. A cell left with
// building=true and done never closed would block every later Force
// forever — in a serve session while holding the session mutex, the
// first panic having been recovered at the RPC layer.
func TestBuilderRoot_PanicPoisonsCell(t *testing.T) {
	stmt, _ := eqProp("a", "b")
	p := Promise(stmt, func(Forcer) ThmCert { panic("boom") })
	assert.PanicsWithValue(t, "boom", func() { Force(context.Background(), p) })
	assert.False(t, p.Proved(), "a poisoned cell is not proved")

	// The second Force must fail fast. Run it under a watchdog so a
	// regression to the parked-forever behavior fails instead of hanging the
	// suite.
	recovered := make(chan any, 1)
	go func() {
		defer func() { recovered <- recover() }()
		Force(context.Background(), p)
	}()
	select {
	case r := <-recovered:
		assert.NotNil(t, r, "Force on a poisoned cell must re-panic, not return")
		assert.Contains(t, fmt.Sprint(r), "boom", "the re-panic carries the original panic value")
	case <-time.After(5 * time.Second):
		t.Fatal("Force after a builder panic blocked >5s — the cell is wedged " +
			"(building never cleared, done never closed)")
	}
}

// A WAITER already parked on the cell when the runner's builder panics must be
// woken by the poison (and re-panic), not left parked forever — the
// goroutine-dump shape of the live serve wedge.
func TestBuilderRoot_PanicWakesParkedWaiter(t *testing.T) {
	stmt, _ := eqProp("a", "b")
	release := make(chan struct{})
	p := Promise(stmt, func(Forcer) ThmCert {
		<-release
		panic("boom")
	})

	// Two concurrent forces: one becomes the runner (parked in the builder on
	// release), the other the waiter (parked on <-c.done).
	forceRecovered := func(out chan<- any) {
		defer func() { out <- recover() }()
		Force(context.Background(), p)
	}
	runner, waiter := make(chan any, 1), make(chan any, 1)
	go forceRecovered(runner)
	go forceRecovered(waiter)
	time.Sleep(50 * time.Millisecond) // let both park before the panic fires
	close(release)

	for name, ch := range map[string]chan any{"runner": runner, "waiter": waiter} {
		select {
		case r := <-ch:
			assert.NotNil(t, r, name+" must observe the builder panic")
		case <-time.After(5 * time.Second):
			t.Fatalf("%s still blocked 5s after the builder panicked", name)
		}
	}
}

// A builder that (transitively) forces its own cell would deadlock waiting on
// its own build without the dependency graph; instead the self-force panics,
// naming the cell.
func TestBuilderRoot_SelfCyclePanics(t *testing.T) {
	stmt, _ := eqProp("a", "b")
	var p ThmPromise
	p = Promise(stmt, func(f Forcer) ThmCert {
		return f.Force(p) // re-enter the same cell through its builder
	})
	msg := panicMessage(func() { Force(context.Background(), p) })
	assert.Contains(t, msg, "theorem promise dependency cycle:")
	assertForceCycle(t, msg, p)
}

// A mutual A→B→A builder citation cycle panics (no deadlock) as long as the
// builders use their Forcer for the nested Force, and the panic
// names the path round the cycle.
func TestBuilderRoot_MutualCyclePanics(t *testing.T) {
	stmtA, _ := eqProp("a", "b")
	stmtB, _ := eqProp("c", "d")
	var pA, pB ThmPromise
	pA = Promise(stmtA, func(f Forcer) ThmCert { return f.Force(pB) })
	pB = Promise(stmtB, func(f Forcer) ThmCert { return f.Force(pA) })

	msg := panicMessage(func() { Force(context.Background(), pA) })
	assert.Contains(t, msg, "theorem promise dependency cycle:")
	assertForceCycle(t, msg, pA, pB)
}

// The derived promise d rests on a, and a's builder forces d. The graph
// follows the derived dependency back to the same builder root.
func TestDerivedPromise_CycleThroughBuilderPanics(t *testing.T) {
	l, r := Var("a", TypeBool()), Var("b", TypeBool())
	var d Thm
	a := Promise(MakeProp(Eq(l, r)), func(f Forcer) ThmCert { return f.Force(d) })
	d = AsThm(EqSym(a))

	msg := panicMessage(func() { Force(context.Background(), d) })
	assert.Contains(t, msg, "theorem promise dependency cycle:")
	assertForceCycle(t, msg, a)
}

// panicMessage runs f and returns the text of the panic it raises, or the
// empty string if it returns.
func panicMessage(f func()) (msg string) {
	defer func() {
		if r := recover(); r != nil {
			msg = fmt.Sprint(r)
		}
	}()
	f()
	return ""
}

// IsPromised is a type test: a Thm is not promised, an unproved plain Prop is
// not promised, a promise is — realized or not.
func TestIsPromised(t *testing.T) {
	stmt, cert := eqProp("a", "b")

	assert.False(t, IsPromised(cert), "a *Thm is not a promise")
	assert.False(t, IsPromised(stmt), "a plain unproved Prop is not a promise")

	root := Promise(stmt, func(Forcer) ThmCert { return cert })
	assert.True(t, IsPromised(root), "an unrealized promise is promised")
	assert.False(t, root.Proved())

	Force(context.Background(), root)
	assert.True(t, IsPromised(root), "a realized promise is still a promise (type test)")
	assert.True(t, root.Proved())
}

// A derived promise (produced by a primitive over an unforced promise) snaps to
// proved the moment its dependency is realized — no recompute. Here the root is
// forced directly; the derived promise then settles via the non-blocking
// Proved()/tryRealizeReadyDeps path, not via its own Force.
func TestDerivedPromise_SnapsWhenRootForced(t *testing.T) {
	l, r := Var("a", TypeBool()), Var("b", TypeBool())
	stmt := MakeProp(Eq(l, r)) // ⊢ a = b
	cert := TestThm(Eq(l, r))
	root := Promise(stmt, func(Forcer) ThmCert { return cert })

	// EqSym threads the promise through a kernel primitive → derived promise.
	sym := EqSym(root) // ⊢ b = a, deferred
	_, isPromise := sym.Core().(ThmPromise)
	assert.True(t, isPromise, "EqSym over a promise yields a derived promise")
	assert.False(t, sym.Proved())
	assert.True(t, sym.Conclusion().AlphaEquals(Eq(r, l)), "statement computed eagerly")

	// Force the root; the derived promise snaps without re-running EqSym.
	Force(context.Background(), root)
	assert.True(t, sym.Proved())
	assert.True(t, sym.AsThmCert().Conclusion().AlphaEquals(Eq(r, l)))
}

func TestDerivedPromise_ForcedThroughBuilderRoot(t *testing.T) {
	l, r := Var("a", TypeBool()), Var("b", TypeBool())
	stmt := MakeProp(Eq(l, r))
	cert := TestThm(Eq(l, r))
	root := Promise(stmt, func(Forcer) ThmCert { return cert })

	sym := EqSym(root)
	assert.False(t, sym.Proved())

	got := Force(context.Background(), AsThm(sym))
	assert.True(t, got.Conclusion().AlphaEquals(Eq(r, l)))
	assert.True(t, sym.Proved())
}

// Proved() on a deep SHARED promise DAG must return promptly and false while
// the base is pending: the tryRealizeReadyDeps walk early-returns at the first
// unproved dep, so a doubling EqTrans chain (deps=[p,p], depth 48 → 2^48 naive
// re-walk) stays linear. The exponential walk was once suspected and
// measured absent; this pins it down so a full
// re-walk is never reintroduced. Proved() must also never run the builder.
func TestDerivedPromise_SharedDAGProvedWalkBounded(t *testing.T) {
	v := Var("v", TypeBool())
	stmt := MakeProp(Eq(v, v))
	base := Promise(stmt, func(Forcer) ThmCert {
		panic("Proved must never force the builder")
	})
	p := Prop(base)
	for range 48 {
		p = EqTrans(p, p) // deps = [p, p] — doubles the reference count
	}
	root, ok := p.(ThmPromise)
	assert.True(t, ok, "EqTrans over a promise yields a derived promise")

	done := make(chan bool, 1)
	go func() { done <- root.Proved() }()
	select {
	case proved := <-done:
		assert.False(t, proved, "root proved while the base promise is unresolved")
	case <-time.After(10 * time.Second):
		t.Fatal("Proved() did not return within 10s — exponential re-walk of the shared promise DAG")
	}
}

// Same DAG shape, but the base CAN resolve: after forcing it, Proved() on the
// root must cascade to true — the lazy-realization behavior the walk bound
// must not break.
func TestDerivedPromise_SharedDAGRealizesAfterBase(t *testing.T) {
	v := Var("v", TypeBool())
	concl := Eq(v, v)
	base := Promise(MakeProp(concl), func(Forcer) ThmCert {
		return TestThm(concl)
	})
	p := Prop(base)
	for range 16 {
		p = EqTrans(p, p)
	}
	root := p.(ThmPromise)
	assert.False(t, root.Proved(), "root proved before the base was forced")
	Force(context.Background(), base)
	assert.True(t, root.Proved(), "root did not realize after the base resolved")
}

// Regression for the AppliedTerm/AbsTerm key() and hasAbstraction
// blowup on shared DAGs (the `applied_term.go` key()/hasAbstraction
// hidden debt paid off alongside the ext DAG-memo consolidation).
//
// Build a shared-DAG shape: an AND-doubling chain where each level
// reuses one child pointer as both fun and arg, so the naive tree size
// grows 2^depth while unique-node count stays O(depth). This is
// precisely the set_comprehension/βη shape the whole memo line has been chasing.
//
// Tests key() and hasAbstraction directly — they are same-package
// unexported entries — bypassing the (also uncached) DeBruijn walk that
// AbsTerm.AlphaKey layers on top. That deBruijn walk is a separate
// bug on the same shape; out of scope for this commit.
func TestSharedDAGKeyBounded(t *testing.T) {
	// Var of type Bool→Bool→Bool — a plain Var lets us build any
	// applied shape without stepping through const/meta type checks.
	andV := Var("and", MakeFun(TypeBool(), TypeBool(), TypeBool()))

	// Ground doubling chain: hasAbstraction is the sole cost here
	// (key() falls through to AlphaKey on the ground case). Depth 60
	// = 2^60 naive nodes if hasAbstraction isn't memoized.
	ground := Term(Var("p", TypeBool()))
	for range 60 {
		ground = Apply(Apply(andV, ground), ground)
	}
	deadline := time.Now().Add(2 * time.Second)
	done := make(chan bool, 1)
	go func() { done <- hasAbstraction(ground) }()
	select {
	case v := <-done:
		assert.False(t, v)
	case <-time.After(time.Until(deadline)):
		t.Fatal("hasAbstraction on ground shared-DAG exceeded budget — cache regression")
	}

	// With an Abs sitting somewhere below, hasAbstraction should be
	// true, and now key() itself takes over the DAG walk — recursing
	// through fun/arg at every layer, which blows without lazyKey.
	// The Abs is embedded as the fun of a β-redex so the whole term
	// has type TypeBool and feeds andV cleanly.
	q := Var("q", TypeBool())
	inner := Term(Apply(Abs(q, q), Var("z", TypeBool())))
	for range 60 {
		inner = Apply(Apply(andV, inner), inner)
	}
	deadline = time.Now().Add(2 * time.Second)
	kdone := make(chan TermKey, 1)
	go func() { kdone <- inner.(AppliedTerm).key() }()
	select {
	case k := <-kdone:
		assert.NotEmpty(t, string(k))
	case <-time.After(time.Until(deadline)):
		t.Fatal("key() on binder-carrying shared-DAG exceeded budget — cache regression")
	}
}

// refDeBruijn is the de Bruijn conversion as a rewrite per binder: the
// body is converted first, then the binder's occurrences are
// substituted. deBruijnConvert renames them in the one pass that
// converts, and must build the same term.
func refDeBruijn(t Term, nextFreeIndex, stopAtIndex int) Term {
	switch t := t.(type) {
	case VarTerm, ConstTerm:
		return t
	case AppliedTerm:
		if stopAtIndex > 0 && nextFreeIndex >= stopAtIndex {
			return t
		}
		fun := refDeBruijn(t.fun, nextFreeIndex, stopAtIndex)
		arg := refDeBruijn(t.arg, nextFreeIndex, stopAtIndex)
		if !fun.Equals(t.fun) || !arg.Equals(t.arg) {
			return Apply(fun, arg)
		}
		return t
	case AbsTerm:
		if deBruijnCheck(t, nextFreeIndex, stopAtIndex) {
			return t
		}
		if stopAtIndex > 0 {
			utils.Assert(t.AllFree(func(v VarTerm) bool { return v.deBruijn <= stopAtIndex }))
		}
		for !t.AllFree(func(v VarTerm) bool {
			return v.deBruijn == 0 || v.deBruijn != nextFreeIndex
		}) {
			nextFreeIndex++
			if stopAtIndex > 0 {
				stopAtIndex++
			}
		}
		if t.v.deBruijn == 0 && stopAtIndex > 0 && nextFreeIndex >= stopAtIndex {
			return Abs(t.v, refDeBruijn(t.body, nextFreeIndex, stopAtIndex))
		}
		if t.v.deBruijn > 0 {
			t = t.ChangeAbsVar(Var(t.v.name, t.v.holType).RenameToAvoid(t.body).name)
		}
		v := deBruijnVar(nextFreeIndex, t.v.holType)
		body := refDeBruijn(t.body, nextFreeIndex+1, stopAtIndex)
		utils.Assert(!body.HasName(v.name) && !t.v.Equals(v))
		return Abs(v, body.Substitute(MakeTermSubst(t.v, v)))
	default:
		panic("Wrong term type.")
	}
}

// deBruijnTerms enumerates the ind-typed terms over three ordinary
// variables, three free de Bruijn variables and three function
// symbols, with binders over any of the six variables, to the depth:
// every shape the conversion distinguishes, shadowing, de Bruijn
// binders and free de Bruijn variables among them.
func deBruijnTerms(depth int) []Term {
	x, y, z := Var("x", indType), Var("y", indType), Var("z", indType)
	d1, d2, d3 := deBruijnVar(1, indType), deBruijnVar(2, indType), deBruijnVar(3, indType)
	binders := []VarTerm{x, y, z, d1, d2, d3}
	f := Var("f", MakeFun(indType, indType))
	h := Var("h", MakeFun(indType, indType, indType))
	g := Var("g", MakeFun(MakeFun(indType, indType), indType))
	byDepth := [][]Term{{x, y, z, d1, d2, d3}}
	for d := 1; d <= depth; d++ {
		var terms []Term
		below := byDepth[d-1]
		var all []Term
		for _, level := range byDepth {
			all = append(all, level...)
		}
		for _, s := range below {
			terms = append(terms, Apply(f, s))
			for _, b := range binders {
				terms = append(terms, Apply(g, Abs(b, s)))
			}
			for _, u := range all {
				terms = append(terms, Apply(Apply(h, s), u))
				if len(u.Frees(nil)) > 0 || true {
					terms = append(terms, Apply(Apply(h, u), s))
				}
			}
		}
		byDepth = append(byDepth, terms)
	}
	var all []Term
	for _, level := range byDepth {
		all = append(all, level...)
	}
	return all
}

// randomDeBruijnTerm draws a deeper term over the same symbols.
func randomDeBruijnTerm(r *rand.Rand, depth int) Term {
	x, y, z := Var("x", indType), Var("y", indType), Var("z", indType)
	leaves := []VarTerm{x, y, z, deBruijnVar(1, indType), deBruijnVar(2, indType), deBruijnVar(3, indType)}
	f := Var("f", MakeFun(indType, indType))
	h := Var("h", MakeFun(indType, indType, indType))
	g := Var("g", MakeFun(MakeFun(indType, indType), indType))
	var build func(depth int) Term
	build = func(depth int) Term {
		if depth == 0 {
			return leaves[r.Intn(len(leaves))]
		}
		switch r.Intn(3) {
		case 0:
			return Apply(f, build(depth-1))
		case 1:
			return Apply(Apply(h, build(depth-1)), build(r.Intn(depth)))
		default:
			return Apply(g, Abs(leaves[r.Intn(len(leaves))], build(depth-1)))
		}
	}
	return build(depth)
}

// outcome runs the conversion and reports its result, or that it
// refused the term with a panic.
func outcome(convert func() Term) (t Term, panicked bool) {
	defer func() {
		if recover() != nil {
			panicked = true
		}
	}()
	return convert(), false
}

// show spells a term of the test's grammar: binders as λ, de Bruijn
// variables by their % names.
func show(t Term) string {
	if t == nil {
		return "<none>"
	}
	switch t := t.(type) {
	case VarTerm:
		return string(t.name)
	case ConstTerm:
		return string(t.meta.name)
	case AppliedTerm:
		return show(t.fun) + "(" + show(t.arg) + ")"
	case AbsTerm:
		return "λ" + string(t.v.name) + "." + show(t.body)
	}
	panic("Wrong term type.")
}

// The one-pass conversion builds the term the per-binder rewrite
// built wherever the rewrite built one, converts α-equivalently, and
// gives an abstraction the key the rewrite's result keys to; the
// windows cover the whole-term conversion AlphaKey asks for and the
// partial ones the normalizer asks for. The rewrite also refused a term
// whose de Bruijn binder past the window bore the name of a binder
// converted above it; the one pass converts it, the inner binder
// shadowing the outer, and still refuses a renaming that would capture.
func TestDeBruijnConvertAgreesWithTheRewritePerBinder(t *testing.T) {
	terms := deBruijnTerms(2)
	r := rand.New(rand.NewSource(1))
	for range 3000 {
		terms = append(terms, randomDeBruijnTerm(r, 2+r.Intn(4)))
	}
	windows := [][2]int{{1, 0}, {2, 0}, {1, 2}, {1, 3}, {2, 4}, {3, 5}}
	agreed, refused, convertedWhereRefused := 0, 0, 0
	for _, term := range terms {
		for _, w := range windows {
			name := fmt.Sprintf("%s under window %v", show(term), w)
			want, wantPanicked := outcome(func() Term { return refDeBruijn(term, w[0], w[1]) })
			got, gotPanicked := outcome(func() Term { return deBruijnConvert(term, w[0], w[1], nil, nil) })
			if gotPanicked && !wantPanicked {
				t.Fatalf("%s: the one pass refused a term the rewrite converted to %s", name, show(want))
			}
			if wantPanicked {
				if gotPanicked {
					refused++
				} else {
					require.True(t, got.AlphaEquals(term), "%s: the one pass converted a term the rewrite refused, to %s, which is not α-equivalent", name, show(got))
					convertedWhereRefused++
				}
				continue
			}
			require.True(t, got.AlphaEquals(term), "%s: converted to %s, which is not α-equivalent", name, show(got))
			require.True(t, want.Equals(got), "%s:\n want %s\n got  %s", name, show(want), show(got))
			if want == term {
				require.True(t, any(term) == any(got), "%s: the term the rewrite left as it is comes back as the same pointer", name)
			}
			agreed++
		}
		app, isApp := term.AsAppliedTerm()
		if !isApp {
			continue
		}
		if abs, ok := app.Arg().AsAbsTerm(); ok {
			converted, panicked := outcome(func() Term { return refDeBruijn(abs, 1, 0) })
			if !panicked {
				s := converted.(AbsTerm)
				want := TermKey(_ABS_TERM_KEY_PREFIX + utils.GenerateHash(s.v.AlphaKey(), s.body.key()))
				assert.Equal(t, want, abs.AlphaKey(), "the key of %v", abs)
			}
		}
	}
	t.Logf("%d conversions agree, %d refused by both, %d converted by the one pass alone", agreed, refused, convertedWhereRefused)
	require.Greater(t, agreed, 10000)
}

// deBruijnCheck verifies if a term is already correctly De Bruijn normalized
// within the specified index window [nextFreeIndex, stopAtIndex).
//
// This function serves two purposes:
// 1. OPTIMIZATION: Avoid redundant conversion of already-normalized terms
// 2. VALIDATION: Ensure the conversion algorithm produces correct results
//
// A term is considered correctly normalized if:
// - All bound variables in the window use De Bruijn indices
// - Indices are used consecutively (with special gap handling, see below)
// - The window boundaries are respected
//
// ALGORITHM DETAILS:
//
// The function recursively traverses the term structure and checks:
// 1. For atomic terms (VarTerm, ConstTerm): Always valid
// 2. For applications: Both function and argument must be valid
// 3. For abstractions: Complex validation logic (see inline comments)
//
// GAP HANDLING:
// The function allows gaps in the index sequence ONLY if every skipped index
// is already in use by a free De Bruijn variable in the term. This handles
// cases where a term contains free De Bruijn variables that forced index
// adjustment during conversion.
//
// WINDOW ADJUSTMENT:
// When gaps are detected and validated, the window boundaries are adjusted
// to maintain consistency. This mirrors the adjustment done in DeBruijnImpl.
func deBruijnCheck(t Term, nextFreeIndex, stopAtIndex int) bool {
	return deBruijnCheckIn(t, nextFreeIndex, stopAtIndex, nil)
}

// deBruijnCheckIn is deBruijnCheck over a shared DAG: seen holds the
// nodes checked under this window so far, nil until the shared-DAG
// gate arms it. A node the walk has left behind passed, or the walk
// would have ended there; a binder moves the window for its body,
// which is checked with a set of its own (see shared_dag.go).
func deBruijnCheckIn(t Term, nextFreeIndex, stopAtIndex int, seen map[Term]struct{}) bool {
	switch t := t.(type) {
	case VarTerm, ConstTerm:
		// Atomic terms are always valid (no abstractions to check)
		return true

	case AppliedTerm:
		if seen == nil && NaiveWalkNeedsMemo(t) {
			seen = map[Term]struct{}{}
		}
		if _, ok := seen[t]; ok {
			return true
		}
		if seen != nil {
			seen[t] = struct{}{}
		}
		// Both parts of an application must be valid
		return deBruijnCheckIn(t.fun, nextFreeIndex, stopAtIndex, seen) &&
			deBruijnCheckIn(t.arg, nextFreeIndex, stopAtIndex, seen)

	case AbsTerm:
		if _, ok := seen[t]; ok {
			return true
		}
		if seen != nil {
			seen[t] = struct{}{}
		}
		// CASE 1: Regular variable at or beyond window boundary
		if t.v.deBruijn == 0 && stopAtIndex > 0 && nextFreeIndex >= stopAtIndex {
			// This abstraction should NOT be converted (we've exhausted the window).
			// But its body might contain abstractions that also need checking.
			// This verifies that abstractions beyond the window remain unconverted.
			return deBruijnCheckIn(t.body, nextFreeIndex, stopAtIndex, nil)
		} else if t.v.deBruijn < nextFreeIndex {
			// CASE 2: De Bruijn index less than expected
			// Invalid: using an index that's too small for this level
			// Example: Expecting %3 but found %2
			return false
		} else if t.v.deBruijn == nextFreeIndex {
			// CASE 3: De Bruijn index exactly as expected
			// Perfect match! Check the body with the next index
			return deBruijnCheckIn(t.body, nextFreeIndex+1, stopAtIndex, nil)
		}

		// CASE 4: De Bruijn index greater than expected (gap detected)
		// This is valid ONLY if all skipped indices are already in use.
		// Example: If we expect %2 but find %4, then %2 and %3 must be
		// free variables in the term (forced the shift to %4).
		for i := nextFreeIndex; i < t.v.deBruijn; i++ {
			if t.AllFree(func(v VarTerm) bool { return v.deBruijn != i }) {
				// Index i is NOT used as a free variable, so this gap is invalid
				return false
			}
		}

		// All skipped indices are accounted for as free variables.
		// Adjust the window to reflect the indices we've skipped.
		// This maintains consistency with the window adjustment in DeBruijnImpl.
		if stopAtIndex > 0 {
			stopAtIndex += t.v.deBruijn - nextFreeIndex
		}

		// Continue checking with the adjusted indices
		return deBruijnCheckIn(t.body, t.v.deBruijn+1, stopAtIndex, nil)

	default:
		panic("Wrong term type.")
	}
}
