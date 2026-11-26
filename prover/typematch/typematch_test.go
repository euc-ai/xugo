package typematch

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

// patternVarsByName returns a predicate that selects VarTerms whose names
// appear in the supplied list. Used to define the lemma's stripped binders
// in tests.
func patternVarsByName(names ...core.TermName) core.VarPredicate {
	set := map[core.TermName]struct{}{}
	for _, n := range names {
		set[n] = struct{}{}
	}
	return func(v core.VarTerm) bool {
		_, ok := set[v.Name()]
		return ok
	}
}

// instantiableTypesByName returns a predicate that selects type variables
// whose names appear in the supplied list. Used to define which lemma type
// variables are open for substitution.
func instantiableTypesByName(names ...core.TypeName) core.VarTypePredicate {
	set := map[core.TypeName]struct{}{}
	for _, n := range names {
		set[n] = struct{}{}
	}
	return func(v core.VarType) bool {
		_, ok := set[v.Name()]
		return ok
	}
}

func propHasTypeVarName(p core.Prop, name core.TypeName) bool {
	hasName := func(v core.VarType) bool {
		return v.Name() == name
	}
	return ext.TermAnyTypeVar(p.Conclusion(), hasName) ||
		p.AnyHyp(func(h core.Term) bool {
			return ext.TermAnyTypeVar(h, hasName)
		})
}

// makeUnaryConst returns a polymorphic unary const meta `F : T → bool`.
func makeUnaryConst(name core.TermName, argType core.HolType) core.ConstTermMeta {
	return core.MakeConstMeta(name, core.MakeFun(argType, core.TypeBool()))
}

// makeBinaryConst returns a polymorphic binary const meta `F : T1 → T2 → bool`.
func makeBinaryConst(name core.TermName, t1, t2 core.HolType) core.ConstTermMeta {
	return core.MakeConstMeta(name, core.MakeFun(t1, t2, core.TypeBool()))
}

func substByName(substs []core.TypeSubst, name core.TypeName) (core.HolType, bool) {
	for _, s := range substs {
		if s.VarType.Name() == name {
			return s.HolType, true
		}
	}
	return nil, false
}

// ---------------------------------------------------------------------------
// TypeOnlyMatch tests
// ---------------------------------------------------------------------------

// TestTypeOnlyMatch_SynthesizesCompoundFunctionTypeSubst is the
// adapter-level reproducer for a compound function-type substitution.
//
// Pattern: lemma binder `y : B` (B in patternVars + instantiable).
// Target:  goal witness `q : (C, P) → B'` (compound function type).
// Expected: TypeOnlyMatch returns σ = { B := (C, P) → B' }.
//
// The issue claims the matcher fails this case ("matcher refuses to
// bind B to a compound type"); if so, the gap is in `unifyTypes` /
// `MatchTypeInto`. If it passes, the matcher itself handles compound
// substitution correctly and the live-frontier wall lives elsewhere.
func TestTypeOnlyMatch_SynthesizesCompoundFunctionTypeSubst(t *testing.T) {
	B := core.MakeVarType("B_lemma_compound")
	Cvar := core.MakeVarType("C_goal")
	Pvar := core.MakeVarType("P_goal")
	Bprime := core.MakeVarType("Bprime_goal")
	prodMeta := core.MakeMetaType("prod", 2)
	prodCP := core.MakeCompositeType(prodMeta, Cvar, Pvar)
	witnessType := core.MakeFun(prodCP, Bprime) // (C, P) → B'

	pattern := core.Var("y", B)          // pattern slot, type = B (instantiable)
	target := core.Var("q", witnessType) // any term with compound type

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("y"),
		instantiableTypesByName("B_lemma_compound"),
	)
	t.Logf("substs: %+v ok: %v", substs, ok)
	require.True(t, ok,
		"TypeOnlyMatch must accept pattern y:B against target q:(C,P)→B' "+
			"and synthesize B := (C,P)→B'")
	got, found := substByName(substs, "B_lemma_compound")
	require.True(t, found, "substitution must include B")
	assert.True(t, got.Equals(witnessType),
		"σ[B] must equal (C,P)→B'; got %s", got.Key())
}

func TestTypeOnlyMatch_SinglePatternSlot(t *testing.T) {
	// Pattern: F(l) where l : A is a pattern slot, F : A → bool polymorphic.
	// Target:  F(c) where c : bool.
	// Expected: A := bool.
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(fLemma, l)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	target := core.Apply(fConcrete, c)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	require.True(t, ok)
	got, ok := substByName(substs, "A")
	require.True(t, ok)
	assert.True(t, got.Equals(core.TypeBool()))
}

func TestTypeOnlyMatch_MultiplePatternSlots(t *testing.T) {
	// Pattern: F(l, m) where l : A, m : B; F : A → B → bool polymorphic.
	// Target:  F(c, d) where c : bool, d : ind.
	// Expected: A := bool, B := ind.
	typeB := core.MakeVarType("B")
	fMeta := makeBinaryConst("F", core.TypeA(), typeB)

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), typeB, core.TypeBool()))
	l := core.Var("l", core.TypeA())
	m := core.Var("m", typeB)
	pattern := core.Apply(core.Apply(fLemma, l), m)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), TypeInd, core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	d := core.Var("d", TypeInd)
	target := core.Apply(core.Apply(fConcrete, c), d)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l", "m"),
		instantiableTypesByName("A", "B"),
	)
	require.True(t, ok)
	gotA, _ := substByName(substs, "A")
	gotB, _ := substByName(substs, "B")
	assert.True(t, gotA.Equals(core.TypeBool()))
	assert.True(t, gotB.Equals(TypeInd))
}

func TestTypeOnlyMatch_RepeatedSlotConsistent(t *testing.T) {
	// Pattern: F(l, l) where l : A is a pattern slot.
	// Target:  F(c, c) where c : bool.
	// Expected: A := bool, single binding for both occurrences.
	fMeta := makeBinaryConst("F", core.TypeA(), core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(core.Apply(fLemma, l), l)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	target := core.Apply(core.Apply(fConcrete, c), c)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	require.True(t, ok)
	got, _ := substByName(substs, "A")
	assert.True(t, got.Equals(core.TypeBool()))
}

func TestTypeOnlyMatch_RepeatedSlotInconsistent(t *testing.T) {
	// Pattern: F(l, l).  Target: F(c, d), c ≠ d. Should fail consistency check.
	fMeta := makeBinaryConst("F", core.TypeA(), core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(core.Apply(fLemma, l), l)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	d := core.Var("d", core.TypeBool())
	target := core.Apply(core.Apply(fConcrete, c), d)

	_, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	assert.False(t, ok)
}

func TestTypeOnlyMatch_DifferentConstHeads(t *testing.T) {
	// Pattern: F(l).  Target: G(c). Different const heads → fail.
	fMeta := makeUnaryConst("F", core.TypeA())
	gMeta := makeUnaryConst("G", core.TypeBool())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	pattern := core.Apply(fLemma, core.Var("l", core.TypeA()))

	gConcrete := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	target := core.Apply(gConcrete, core.Var("c", core.TypeBool()))

	_, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	assert.False(t, ok)
}

func TestTypeOnlyMatch_AbstractionAlphaRename(t *testing.T) {
	// Pattern: λx:A. l(x)  where l : A → bool is a pattern slot.
	// Target:  λy:bool. P(y)  where P : bool → bool is a regular const.
	// Match should walk into the abstraction, alpha-rename x↔y, and
	// recover A := bool by unifying l's type with P's.
	pMeta := makeUnaryConst("P", core.TypeBool())

	x := core.Var("x", core.TypeA())
	l := core.Var("l", core.MakeFun(core.TypeA(), core.TypeBool()))
	pattern := core.Abs(x, core.Apply(l, x))

	y := core.Var("y", core.TypeBool())
	pConst := core.MakeConstTerm(pMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	target := core.Abs(y, core.Apply(pConst, y))

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	require.True(t, ok)
	got, _ := substByName(substs, "A")
	assert.True(t, got.Equals(core.TypeBool()))
}

func TestTypeOnlyMatch_BoundVarMismatch(t *testing.T) {
	// Pattern: λx:A. F(x).  Target: λy:bool. F(z), z is a different free
	// variable, not the binder. Bound-var alpha-rename must fail.
	fMeta := makeUnaryConst("F", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	x := core.Var("x", core.TypeA())
	pattern := core.Abs(x, core.Apply(fLemma, x))

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	y := core.Var("y", core.TypeBool())
	z := core.Var("z", core.TypeBool())
	target := core.Abs(y, core.Apply(fConcrete, z))

	_, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName(),
		instantiableTypesByName("A"),
	)
	assert.False(t, ok)
}

func TestTypeOnlyMatch_RigidGoalTypeVar(t *testing.T) {
	// Pattern: F(l)  where l : A is a slot, F : A → bool, A is instantiable.
	// Target:  F(c)  where c : ?goal (a *rigid* goal-side type var).
	// Expected: A := ?goal — the lemma's A should map to the goal's rigid
	// type var (a soft "type-rename" rather than a concrete instantiation).
	rigid := core.MakeVarType("goal_var")
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(fLemma, l)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(rigid, core.TypeBool()))
	c := core.Var("c", rigid)
	target := core.Apply(fConcrete, c)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"), // 'goal_var' is NOT instantiable — rigid.
	)
	require.True(t, ok)
	got, _ := substByName(substs, "A")
	require.True(t, got.Equals(rigid))
}

func TestTypeOnlyMatch_RigidVsRigidAfterChainedSubst(t *testing.T) {
	// Pattern: F(l, m) where l, m : A; F : A → A → bool.
	// Target:  F(c, d) where c : ?goal, d : ?goal.
	// First occurrence binds A := ?goal. Second occurrence revisits A
	// (now ?goal, rigid) against ?goal — must succeed via literal-equality
	// fallback, NOT fail because ?goal is non-instantiable.
	rigid := core.MakeVarType("goal_var")
	fMeta := makeBinaryConst("F", core.TypeA(), core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	m := core.Var("m", core.TypeA())
	pattern := core.Apply(core.Apply(fLemma, l), m)

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(rigid, rigid, core.TypeBool()))
	c := core.Var("c", rigid)
	d := core.Var("d", rigid)
	target := core.Apply(core.Apply(fConcrete, c), d)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l", "m"),
		instantiableTypesByName("A"),
	)
	require.True(t, ok)
	got, _ := substByName(substs, "A")
	assert.True(t, got.Equals(rigid))
}

func TestTypeOnlyMatch_TypeUnificationConflict(t *testing.T) {
	// Pattern: F(l) = G(l)  where l : A is a slot, F, G : A → bool polymorphic.
	// Target:  F(c) = G(d)  where c : bool, d : ind, F instantiated at bool,
	// G instantiated at ind. The two F/G occurrences would force A := bool
	// (from F's instance) and A := ind (from G's instance) — conflict.
	//
	// Note: l consistency would also catch this independently — we deliberately
	// construct a goal where the two l-positions yield non-α-equal targets too
	// (c vs d). The relevant assertion is that TypeOnlyMatch rejects.
	fMeta := makeUnaryConst("F", core.TypeA())
	gMeta := makeUnaryConst("G", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	gLemma := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Eq(core.Apply(fLemma, l), core.Apply(gLemma, l))

	fBool := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	gInd := core.MakeConstTerm(gMeta, core.MakeFun(TypeInd, core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	d := core.Var("d", TypeInd)
	// `core.Eq` requires both sides have equal types — both ends here are bool
	// (F applied returns bool, G applied returns bool), so the target is
	// well-typed despite F at bool / G at ind.
	target := core.Eq(core.Apply(fBool, c), core.Apply(gInd, d))

	_, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A"),
	)
	assert.False(t, ok)
}

func TestTypeOnlyMatch_PolyToPoly(t *testing.T) {
	// Pattern: F(l)  where l : A is a slot, F : A → bool, A is instantiable.
	// Target:  F(c) where c : B (B is *also* instantiable — both lemma and
	// target are polymorphic; the matcher should map A := B).
	typeB := core.MakeVarType("B")
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(fLemma, l)

	fOther := core.MakeConstTerm(fMeta, core.MakeFun(typeB, core.TypeBool()))
	c := core.Var("c", typeB)
	target := core.Apply(fOther, c)

	substs, ok := TypeOnlyMatch(
		pattern, target,
		patternVarsByName("l"),
		instantiableTypesByName("A", "B"),
	)
	require.True(t, ok)
	got, _ := substByName(substs, "A")
	assert.True(t, got.Equals(typeB))
}

// ---------------------------------------------------------------------------
// GoalSubtermIndex tests
// ---------------------------------------------------------------------------

func TestGoalSubtermIndex_BucketsByConstHead(t *testing.T) {
	// Goal: ⊢ F(x) ⇔ G(y). The propositional walk decomposes ⇔ on both
	// sides; F-applications go to bucket "F", G-applications to bucket
	// "G". The iff itself is consumed by the prop walk and does not
	// appear under bucket "=".
	fMeta := makeUnaryConst("F", core.TypeBool())
	gMeta := makeUnaryConst("G", core.TypeBool())
	fConst := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	gConst := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))

	x := core.Var("x", core.TypeBool())
	y := core.Var("y", core.TypeBool())
	fx := core.Apply(fConst, x)
	gy := core.Apply(gConst, y)

	goal := core.MakeProp(core.Eq(fx, gy))

	idx := BuildGoalSubtermIndex(goal)

	// Bucket "F" should contain F(x) and the bare F const.
	fBucket := idx.byHead["F"]
	require.Len(t, fBucket, 2)
	assertIndexedContainsAlpha(t, fBucket, fx)
	assertIndexedContainsAlpha(t, fBucket, fConst)

	// Bucket "G" should similarly contain two entries.
	gBucket := idx.byHead["G"]
	require.Len(t, gBucket, 2)
}

func TestGoalSubtermIndex_LookupByPattern(t *testing.T) {
	// Build a goal containing F at one position; lookup should yield the
	// F-headed subterms.
	fMeta := makeUnaryConst("F", core.TypeA())
	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	x := core.Var("x", core.TypeBool())
	fx := core.Apply(fConcrete, x)
	goal := core.MakeProp(fx)

	idx := BuildGoalSubtermIndex(goal)

	// Pattern F(l) at type A → bool: lookup by head 'F' should return the
	// goal's F-headed subterms.
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	pattern := core.Apply(fLemma, l)

	cands := idx.Candidates(pattern)
	require.NotEmpty(t, cands)
	assertIndexedContainsAlpha(t, cands, fx)
}

func TestGoalSubtermIndex_WalksIntoForall(t *testing.T) {
	// Goal: ⊢ ∀x. F(x). The propositional walk strips the outer ∀x.
	// records x as a bound var, and descends to F(x); F(x) is then
	// term-level descended to emit Apply(F,x) and the bare F const.
	fMeta := makeUnaryConst("F", core.TypeBool())
	fConst := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	x := core.Var("x", core.TypeBool())
	fx := core.Apply(fConst, x)
	body := ext.ForAll(x)(fx)

	goal := core.MakeProp(body)
	idx := BuildGoalSubtermIndex(goal)

	require.NotEmpty(t, idx.byHead["F"])
	assertIndexedContainsAlpha(t, idx.byHead["F"], fx)
}

func TestGoalSubtermIndex_DropsNonConstHeads(t *testing.T) {
	// Goal: ⊢ x (a bare bool variable). The enumerator's emit() drops
	// non-const-headed subterms, so the index has no entries at all —
	// every bucket lookup returns nil.
	x := core.Var("x", core.TypeBool())
	goal := core.MakeProp(x)
	idx := BuildGoalSubtermIndex(goal)

	assert.Empty(t, idx.byHead[""])
	assert.Empty(t, idx.byHead["x"])
	assert.Nil(t, idx.Candidates(core.Var("l", core.TypeBool())))
}

func TestGoalSubtermIndex_DecomposesImply(t *testing.T) {
	// Goal: ⊢ F(a) ⇒ G(b). Both sides of ⇒ should be walked — the
	// matching-points enumerator is symmetric.
	fMeta := makeUnaryConst("F", core.TypeBool())
	gMeta := makeUnaryConst("G", core.TypeBool())
	fConst := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	gConst := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	a := core.Var("a", core.TypeBool())
	b := core.Var("b", core.TypeBool())

	fa := core.Apply(fConst, a)
	gb := core.Apply(gConst, b)
	goal := core.MakeProp(ext.WrapTerm(fa).Imply(gb).Core())

	idx := BuildGoalSubtermIndex(goal)
	assert.NotEmpty(t, idx.byHead["F"], "lhs of ⇒ must be enumerated")
	assert.NotEmpty(t, idx.byHead["G"], "rhs of ⇒ must be enumerated")
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

func assertContainsAlpha(t *testing.T, ts []core.Term, want core.Term) {
	t.Helper()
	for _, c := range ts {
		if c.AlphaEquals(want) {
			return
		}
	}
	t.Errorf("expected slice to contain (α-equiv) %v, got %v", want, ts)
}

func assertIndexedContainsAlpha(t *testing.T, its []skeleton.IndexedTerm, want core.Term) {
	t.Helper()
	for _, it := range its {
		if it.Term.AlphaEquals(want) {
			return
		}
	}
	t.Errorf("expected indexed-term slice to contain (α-equiv) %v", want)
}

// ---------------------------------------------------------------------------
// tryAdaptLemmaTypes — end-to-end integration of TypeOnlyMatch +
// GoalSubtermIndex. Each test constructs a lemma + goal pair and verifies
// the adapter produces the expected lemma-with-types-instantiated (or nil).
// ---------------------------------------------------------------------------

func TestTryAdaptLemmaTypes_NoTypeVars(t *testing.T) {
	// Fully concrete lemma — adapter must return nil (no work to do).
	x := core.Var("x", core.TypeBool())
	lemma := core.MakeProp(core.Eq(x, x))

	y := core.Var("y", core.TypeBool())
	goal := core.MakeProp(core.Eq(y, y))

	got := TryAdaptLemmaTypes(lemma, goal)
	assert.Nil(t, got)
}

func TestTryAdaptLemmaTypes_PolyEqGroundEq(t *testing.T) {
	// Lemma: ⊢ ∀x:A. x = x.   Goal: ⊢ y:bool = y:bool.
	// Adapter should bind A := bool by matching the lhs (or rhs) of the
	// stripped body against the goal's conclusion.
	xA := core.Var("x", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(xA)(ext.WrapTerm(core.Eq(xA, xA))).Core())

	y := core.Var("y", core.TypeBool())
	goal := core.MakeProp(core.Eq(y, y))

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)

	// Adapted lemma should be ∀x:bool. x = x.
	xBool := core.Var("x", core.TypeBool())
	want := core.MakeProp(ext.ForAll(xBool)(ext.WrapTerm(core.Eq(xBool, xBool))).Core())
	assert.True(t, got.AlphaEquals(want), "adapted = %v, want = %v", got, want)
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_PolyConstApplication(t *testing.T) {
	// Lemma: ⊢ ∀l:A. F(l)        where F : A → bool, A is a lemma type var.
	// Goal:  ⊢ F(c)               where c : bool, F instantiated at bool.
	// Adapter binds A := bool by matching the body F(l) against goal's F(c).
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	goal := core.MakeProp(core.Apply(fConcrete, c))

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_BridgeIff(t *testing.T) {
	// Bridge-style lemma: ⊢ ∀l:A. F(l) ⇔ G(l).
	// Goal contains G(c) on its conclusion side at concrete type bool.
	// The adapter must match the *rhs* of the iff (G(l)) against the
	// goal's G(c) subterm to recover A := bool.
	//
	// This is the structural shape const-head matching alone fails on:
	// F and G are both polymorphic, and matching them in
	// isolation gives partial substitutions; matching one *whole side*
	// recovers the full sub.
	fMeta := makeUnaryConst("F", core.TypeA())
	gMeta := makeUnaryConst("G", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	gLemma := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	body := core.Eq(core.Apply(fLemma, l), core.Apply(gLemma, l)) // ⇔ at bool
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(body)).Core())

	gConcrete := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	goal := core.MakeProp(core.Apply(gConcrete, c))

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "adapter must recover A := bool from rhs match")
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_TwoBinders(t *testing.T) {
	// Lemma: ⊢ ∀l:A. ∀m:B. P(l, m)   where P : A → B → bool.
	// Goal:  ⊢ P(c:bool, d:ind).
	// Both A and B should be bound. Adapter produces a fully concrete lemma.
	typeB := core.MakeVarType("B")
	pMeta := makeBinaryConst("P", core.TypeA(), typeB)

	pLemma := core.MakeConstTerm(pMeta, core.MakeFun(core.TypeA(), typeB, core.TypeBool()))
	l := core.Var("l", core.TypeA())
	m := core.Var("m", typeB)
	body := core.Apply(core.Apply(pLemma, l), m)
	lemma := core.MakeProp(
		ext.ForAll(l, m)(ext.WrapTerm(body)).Core(),
	)

	pConcrete := core.MakeConstTerm(pMeta,
		core.MakeFun(core.TypeBool(), TypeInd, core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	d := core.Var("d", TypeInd)
	goal := core.MakeProp(core.Apply(core.Apply(pConcrete, c), d))

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_NoGoalMatch(t *testing.T) {
	// Lemma has type vars but goal contains nothing structurally compatible.
	// Adapter returns nil (caller falls back to unadapted lemma).
	fMeta := makeUnaryConst("F", core.TypeA())
	gMeta := makeUnaryConst("G", core.TypeBool())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	// Goal: ⊢ G(x). G is a different const; F doesn't appear.
	gConst := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	x := core.Var("x", core.TypeBool())
	goal := core.MakeProp(core.Apply(gConst, x))

	got := TryAdaptLemmaTypes(lemma, goal)
	assert.Nil(t, got)
}

func TestTryAdaptLemmaTypes_UselessSelfSubst(t *testing.T) {
	// Lemma and goal share the *same* type variable name. Adapter would
	// produce A := A which `core.PropTypeInst` filters out (uselessTypeSubst).
	// `tryAdaptLemmaTypes` then bails because adapted == lemma.
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	// Goal: ⊢ F(c:A) — same A.
	c := core.Var("c", core.TypeA())
	goal := core.MakeProp(core.Apply(fLemma, c))

	got := TryAdaptLemmaTypes(lemma, goal)
	assert.Nil(t, got, "self-substitution shouldn't be reported as an adaptation")
}

// TestTryAdaptLemmaTypes_SharedPointerIdentityNotHijacked is the
// replay-divergence regression met on associativity of composition. The occurs-check (dropRecursiveTypeSubsts)
// must be keyed by NAME, not VarType pointer, and must KEEP a pure identity
// binding so it locks the var's name.
//
// Shape (o = function composition, o(x,y) = x∘y):
//
//	lemma: ∀f g h x. f(g(h(x))) = o(f, o(g,h), x)        // f ∘ (g∘h)
//	goal:  ∀f g h x. o(o(f,g), h, x) = o(f, o(g,h), x)    // (f∘g)∘h = f∘(g∘h)
//
// The lemma's RHS `o(f, o(g,h), x)` already α-matches the goal's RHS exactly,
// so the correct adaptation is identity → no change → adapter returns nil.
//
// The hazard: emit reuses the SAME VarType pointers across a proof's sections,
// so here the lemma and goal share their A/B/C/D type vars (constructed once,
// used in both). At replay the lemma's big RHS anchor matches the goal's RHS
// with an identity subst `C:=C` (same pointer) — which a POINTER-keyed
// occurs-check would flag as recursive and drop, UNLOCKING C. The smaller
// `o(g,h)` anchor would then match the goal's LHS subterm `o(o(f,g),h)` and
// commit a spurious `C:=D`, corrupting the lemma so that it does not match
// the goal. At record time the lemma (a cited entry) and goal (the session) carry
// DISTINCT pointers, so the identity binding survives and the spurious rebind
// is rejected — a record/replay divergence. The name-keyed
// occurs-check + identity-keep make both sides agree.
func TestTryAdaptLemmaTypes_SharedPointerIdentityNotHijacked(t *testing.T) {
	// Type vars constructed ONCE and shared between lemma and goal — this is
	// the emit pointer-reuse that triggered the bug. With distinct pointers
	// (the record-time situation) the bug does not arise.
	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	C := core.MakeVarType("C")
	D := core.MakeVarType("D")

	// o : (b→c) → (a→b) → (a→c)   — polymorphic function composition.
	oMeta := core.MakeConstMeta("o",
		core.MakeFun(core.MakeFun(B, C), core.MakeFun(core.MakeFun(A, B), core.MakeFun(A, C))))

	// comp(x, y) = x∘y, where x:Q→R and y:P→Q, yielding P→R. The o-instance
	// is materialized at the concrete (P,Q,R) so its printed type carries the
	// right type-var assignment (the thing the AlphaKey divergence was about).
	comp := func(P, Q, R core.HolType, x, y core.Term) core.Term {
		oInst := core.MakeConstTerm(oMeta,
			core.MakeFun(core.MakeFun(Q, R), core.MakeFun(core.MakeFun(P, Q), core.MakeFun(P, R))))
		return core.Apply(core.Apply(oInst, x), y)
	}

	f := core.Var("f", core.MakeFun(C, D)) // f : C→D
	g := core.Var("g", core.MakeFun(B, C)) // g : B→C
	h := core.Var("h", core.MakeFun(A, B)) // h : A→B
	x := core.Var("x", A)                  // x : A

	gh := comp(A, B, C, g, h) // g∘h : A→C

	// lemma RHS: o(f, o(g,h), x) = (f ∘ (g∘h))(x) : D
	rhs := core.Apply(comp(A, C, D, f, gh), x)
	// lemma LHS: f(g(h(x))) : D
	lhs := core.Apply(f, core.Apply(g, core.Apply(h, x)))
	lemma := core.MakeProp(ext.ForAll(f, g, h, x)(ext.WrapTerm(core.Eq(lhs, rhs))).Core())

	// goal LHS: o(o(f,g), h, x) = ((f∘g) ∘ h)(x) : D
	fg := comp(B, C, D, f, g)                      // f∘g : B→D
	goalLHS := core.Apply(comp(A, B, D, fg, h), x) // (f∘g)∘h applied to x
	// goal RHS: identical to the lemma RHS (shared vars) — the identity-match site.
	goalRHS := core.Apply(comp(A, C, D, f, gh), x)
	goal := core.MakeProp(ext.ForAll(f, g, h, x)(ext.WrapTerm(core.Eq(goalLHS, goalRHS))).Core())

	got := TryAdaptLemmaTypes(lemma, goal)

	// The adapter must NOT corrupt the lemma. Correct behavior is nil (the
	// lemma already aligns with the goal); a non-nil result is only acceptable
	// if it is α-equal to the original. A corrupted result carries a
	// spurious C:=D substitution and is NOT α-equal (o⟨B:D,C:D⟩ vs o⟨B:C,C:D⟩).
	if got != nil {
		assert.Truef(t, got.AlphaEquals(lemma),
			"adapter hijacked the lemma with a spurious type subst:\n got  = %v\n want ≈ %v", got, lemma)
	}
}

func TestTryAdaptLemmaTypes_GoalSubtermInsideAbstraction(t *testing.T) {
	// Lemma: ⊢ ∀l:A. F(l).
	// Goal:  ⊢ ∀x:bool. F(x). The F-subterm is *inside* the goal's outer ∀.
	// The adapter must walk into the abstraction (via GoalSubtermIndex)
	// to find the candidate, and recover A := bool.
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	x := core.Var("x", core.TypeBool())
	goal := core.MakeProp(ext.ForAll(x)(ext.WrapTerm(core.Apply(fConcrete, x))).Core())

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_GoalContainsAdapterUnchainsFromHyp(t *testing.T) {
	// Lemma: ⊢ ∀l:A. F(l). Goal has F(c:bool) as a *hypothesis*.
	// The adapter must scan hyps too — GoalSubtermIndex already does this.
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	hyp := core.Apply(fConcrete, c)
	concl := core.Var("dummy", core.TypeBool())
	goal := core.MakeProp(concl, hyp)

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	assert.False(t, ext.PropHasTypeVars(got))
}

func TestTryAdaptLemmaTypes_PolyGoalRigidGoalVar(t *testing.T) {
	// Goal itself is polymorphic: type var ?goal in goal is rigid (not
	// in the lemma's type-var set). The adapter should map A := ?goal
	// (lemma's A specializes to the goal's parametric type), producing
	// an adapted lemma that's *aligned* with the goal but still has
	// type vars (?goal).
	rigid := core.MakeVarType("goal_var")
	fMeta := makeUnaryConst("F", core.TypeA())

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	fGoal := core.MakeConstTerm(fMeta, core.MakeFun(rigid, core.TypeBool()))
	c := core.Var("c", rigid)
	goal := core.MakeProp(core.Apply(fGoal, c))

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "adapter should re-type lemma to use the goal's rigid type var")

	// The adapted lemma should have its A re-bound to ?goal_var. Lemma's
	// type-var set should now be {?goal_var}, no more A.
	hasA := propHasTypeVarName(got, "A")
	hasGoal := propHasTypeVarName(got, "goal_var")
	assert.False(t, hasA, "lemma's A should be gone")
	assert.True(t, hasGoal, "lemma should now reference goal's type var")
}

// TestTryAdaptLemmaTypes_BridgeIffWithSplitHyps reproduces the RCP-style
// failure where a previous (whole-side-only) pattern set could not adapt
// the bridge iff, because the iff's rhs is `ALL(...) ∧ PAIRWISE(...)`
// while the goal carries `ALL(...)` and `PAIRWISE(...)` as SEPARATE
// hypotheses (no combined `ALL ∧ PAIRWISE` subterm). The new
// MatchingPoints enumerator emits the inner conjuncts (PAIRWISE-headed
// alone, ALL-headed alone) as their own anchors, so the adapter
// recovers the type substitution from the PAIRWISE side aligning with
// the goal's PAIRWISE hyp.
func TestTryAdaptLemmaTypes_BridgeIffWithSplitHyps(t *testing.T) {
	// Lemma: ⊢ ∀l:A. lhs(l) ⇔ (P(l) ∧ Q(l))
	//   where P, Q : A → bool, A is a lemma type var. lhs is also a
	//   polymorphic predicate over l, structurally distinct from rhs.
	pMeta := makeUnaryConst("P", core.TypeA())
	qMeta := makeUnaryConst("Q", core.TypeA())
	rMeta := makeUnaryConst("R", core.TypeA()) // for lhs

	pLemma := core.MakeConstTerm(pMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	qLemma := core.MakeConstTerm(qMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	rLemma := core.MakeConstTerm(rMeta, core.MakeFun(core.TypeA(), core.TypeBool()))

	l := core.Var("l", core.TypeA())
	rhs := ext.WrapTerm(core.Apply(pLemma, l)).And(core.Apply(qLemma, l))
	body := ext.WrapTerm(core.Apply(rLemma, l)).Eq(rhs)
	lemma := core.MakeProp(ext.ForAll(l)(body).Core())

	// Goal: ⊢ dummy, with hyps  P(c:bool) and Q(c:bool) — SEPARATE.
	// Crucially, the goal does NOT contain `P ∧ Q` as a single subterm,
	// nor does it contain the lhs `R(...)`. Only the PAIRWISE-analog
	// rhs conjunct can drive the type recovery.
	pConcrete := core.MakeConstTerm(pMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	qConcrete := core.MakeConstTerm(qMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	hypP := core.Apply(pConcrete, c)
	hypQ := core.Apply(qConcrete, c)
	dummy := core.Var("dummy", core.TypeBool())
	goal := core.MakeProp(dummy, hypP, hypQ)

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "adapter must recover A := bool from a single conjunct of rhs")
	assert.False(t, ext.PropHasTypeVars(got))
}

// TestTryAdaptLemmaTypes_MultiAnchorAccumulation models a
// failure mode where the lemma's type variables are scattered across
// multiple non-overlapping subterms — no single anchor's match suffices.
// The adapter must accumulate substitutions across anchors and merge
// them with consistency-checking to fully concretize the lemma's
// binder types.
//
// Lemma: ⊢ ∀l:A. F(l, p_aux:typeP) ∧ G(l, q_aux:typeQ)
// Goal: hyps F(c:bool, p:ind) and G(c:bool, q:bool) (separate hyps).
//
// First-match-wins on the F-anchor recovers (A:=bool, typeP:=ind), but
// typeQ stays polymorphic. Multi-match accumulation also picks up
// typeQ:=bool from the G-anchor. Without accumulation, the resulting
// lemma's binder type would still contain typeQ, breaking downstream
// instantiate even though the lemma is conceptually applicable.
func TestTryAdaptLemmaTypes_MultiAnchorAccumulation(t *testing.T) {
	typeP := core.MakeVarType("P_var")
	typeQ := core.MakeVarType("Q_var")
	fMeta := core.MakeConstMeta("F", core.MakeFun(core.TypeA(), typeP, core.TypeBool()))
	gMeta := core.MakeConstMeta("G", core.MakeFun(core.TypeA(), typeQ, core.TypeBool()))

	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), typeP, core.TypeBool()))
	gLemma := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeA(), typeQ, core.TypeBool()))
	pAuxLemma := core.Var("p_aux", typeP)
	qAuxLemma := core.Var("q_aux", typeQ)
	l := core.Var("l", core.TypeA())
	body := ext.WrapTerm(core.Apply(core.Apply(fLemma, l), pAuxLemma)).
		And(core.Apply(core.Apply(gLemma, l), qAuxLemma))
	lemma := core.MakeProp(ext.ForAll(l)(body).Core())

	fConcrete := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), TypeInd, core.TypeBool()))
	gConcrete := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	pConcrete := core.Var("p", TypeInd)
	qConcrete := core.Var("q", core.TypeBool())
	hypF := core.Apply(core.Apply(fConcrete, c), pConcrete)
	hypG := core.Apply(core.Apply(gConcrete, c), qConcrete)
	dummy := core.Var("dummy", core.TypeBool())
	goal := core.MakeProp(dummy, hypF, hypG)

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "adapter must accumulate (A, P_var, Q_var) substs across both anchors")
	assert.False(t, ext.PropHasTypeVars(got),
		"all three lemma type vars must be bound; first-match-wins would leave one polymorphic")
}

// TestTryAdaptLemmaTypes_GenericConstHeadDoesNotPoison pins the fix
// for the "polymorphic const head matches greedily and corrupts later
// merges" bug. Reproduces a first-component-of-a-pasted-vector scenario
// at the matcher level using a minimal stand-in for the cart-vector
// type machinery: a unary type constructor `box(_)` plays the role
// of cart's "complex" wrapper.
//
// The hazard: when a lemma's polymorphic `=` const has type instance
// T₁ but the goal's outer `=` has type instance T₂ where T₂ is
// structurally richer than T₁ would naturally cover, matching the
// bare `=` heads together produces a binding for the lemma's type
// var that's too complex — and later anchors' merges (the
// structurally-relevant ones) fail.
//
// With anchors processed in natural order, the bare `=` anchor
// (size 1) commits a wrong binding before the size-2 `F(f)` anchor
// has a chance to fix it.
//
// Anchors are sorted size-descending, so the size-2 `F(f)`
// anchor commits the correct binding first; the bare `=` anchor's
// would-be match fails merge and is correctly skipped.
func TestTryAdaptLemmaTypes_GenericConstHeadDoesNotPoison(t *testing.T) {
	// Setup: F is a polymorphic unary endomorphism `A → A` (a single
	// const meta, instantiated at different types in lemma vs goal).
	// c is a polymorphic constant of type `A`.
	fMeta := core.MakeConstMeta("F_typematch_polypoison", core.MakeFun(core.TypeA(), core.TypeA()))
	cMeta := core.MakeConstMeta("c_typematch_polypoison", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeA()))
	cLemma := core.MakeConstTerm(cMeta, core.TypeA())

	// Lemma: ∀f:A. F(f) = c
	// Lemma's polymorphic `=` const has type `A → A → bool`.
	f := core.Var("f", core.TypeA())
	lemmaBody := ext.WrapTerm(core.Apply(fLemma, f)).Eq(cLemma)
	lemma := core.MakeProp(ext.ForAll(f)(lemmaBody).Core())

	// Goal: ⊢ (b1 = b2) ⇒ P(F(i))    where:
	//   b1, b2 : bool                  (the goal's outer `=` is on bool)
	//   F : ind → ind                  (F's instantiation in goal is at ind)
	//   i : ind
	//   P : ind → bool
	//
	// In natural order: the bare `=` anchor (size 1) commits A := bool by
	// matching against `b1 = b2`. The structurally-relevant F(f)
	// anchor (size 2) then fails merge against F(i) which wants
	// A := ind. Result: A bound to wrong type (bool), F still
	// polymorphic — adapted lemma can't actually rewrite F(i).
	//
	// Size-descending: F(f) anchor (size 2) processes first, commits
	// A := ind. The `=` anchor then fails merge (would need A := bool)
	// and is correctly skipped.
	pMeta := core.MakeConstMeta("P_typematch_polypoison", core.MakeFun(TypeInd, core.TypeBool()))
	fGoal := core.MakeConstTerm(fMeta, core.MakeFun(TypeInd, TypeInd))
	pGoal := core.MakeConstTerm(pMeta, core.MakeFun(TypeInd, core.TypeBool()))
	b1 := core.Var("b1", core.TypeBool())
	b2 := core.Var("b2", core.TypeBool())
	i := core.Var("i", TypeInd)
	bEq := core.Eq(b1, b2)
	fi := core.Apply(fGoal, i)
	pfi := core.Apply(pGoal, fi)
	goalConcl := ext.WrapTerm(bEq).Imply(pfi)
	goal := core.MakeProp(goalConcl.Core())

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got,
		"adapter must produce a substitution (the F(f) anchor matches F(i) cleanly under size-desc)")
	assert.False(t, ext.PropHasTypeVars(got),
		"adapted lemma must have no remaining lemma type vars")
	// Decisive: F's adapted type must be ind → ind (matching goal's F),
	// not bool → bool. A greedy bare-`=` match would wrongly bind
	// A := bool.
	adaptedLemmaContainsTypeFor(t, got,
		"F_typematch_polypoison",
		core.MakeFun(TypeInd, TypeInd))
}

// adaptedLemmaContainsTypeFor walks the adapted lemma's terms and
// asserts that the named const appears with the expected type. Used
// as a concrete decisive check for type adaptation tests.
func adaptedLemmaContainsTypeFor(t *testing.T, lemma core.Prop, constName core.TermName, expectedType core.HolType) core.Prop {
	t.Helper()
	found := false
	var walk func(term core.Term)
	walk = func(term core.Term) {
		if ct, ok := term.AsConst(); ok && !ct.IsZero() && ct.Name() == constName {
			if ct.Type().Equals(expectedType) {
				found = true
			} else {
				t.Errorf("const %q has type %s, expected %s",
					constName, ext.FormatType(ct.Type()), ext.FormatType(expectedType))
			}
		}
		if a, ok := term.AsAppliedTerm(); ok && !a.IsZero() {
			walk(a.Fun())
			walk(a.Arg())
		}
		if abs, ok := term.AsAbsTerm(); ok && !abs.IsZero() {
			walk(abs.Body())
		}
	}
	walk(lemma.Conclusion())
	for _, h := range lemma.Hyps() {
		walk(h)
	}
	assert.True(t, found, "const %q not found in adapted lemma", constName)
	return lemma
}

// TestTryAdaptLemmaTypes_InconsistentMatchSkipped verifies the merge
// step rejects an anchor whose substitution conflicts with an already-
// accumulated binding rather than overwriting it. Inconsistent
// candidate is silently skipped and the matcher commits to a
// consistent partial solution.
func TestTryAdaptLemmaTypes_InconsistentMatchSkipped(t *testing.T) {
	// Lemma: ⊢ ∀l:A. F(l) ∧ G(l)   F, G : A → bool.
	// Goal: hyps F(b:bool), G(i:ind).
	// F-anchor matches at A := bool. G-anchor would want A := ind;
	// merge rejects, so G's contribution is dropped. Adapter still
	// returns the lemma adapted with A := bool.
	fMeta := makeUnaryConst("F", core.TypeA())
	gMeta := makeUnaryConst("G", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	gLemma := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	body := ext.WrapTerm(core.Apply(fLemma, l)).And(core.Apply(gLemma, l))
	lemma := core.MakeProp(ext.ForAll(l)(body).Core())

	fBool := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	gInd := core.MakeConstTerm(gMeta, core.MakeFun(TypeInd, core.TypeBool()))
	b := core.Var("b", core.TypeBool())
	i := core.Var("i", TypeInd)
	hypF := core.Apply(fBool, b)
	hypG := core.Apply(gInd, i)
	dummy := core.Var("dummy", core.TypeBool())
	goal := core.MakeProp(dummy, hypF, hypG)

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	assert.False(t, ext.PropHasTypeVars(got),
		"A should be bound to bool; the inconsistent G match is skipped, not propagated")
}

// TestTryAdaptLemmaTypes_LemmaSideUnderLambda exercises the lemma-side
// deep-walk anchor augmentation. The lemma below is constructed so that
// skeleton.MatchingPoints emits NO useful anchor (every const head it
// can reach is mono, and the only polymorphic-const-headed subterm
// lives under a λ that MatchingPoints intentionally skips). Without
// the augmentation, tryAdaptLemmaTypes can recover no type
// substitution and returns nil.
//
// SHAPE
//
//	Lemma: ⊢ ∀f:(A→bool)→bool. f(λx:A. c(x))
//	  - f is a pattern slot (Var with poly type), but a Var doesn't
//	    register as a const head in MatchingPoints' emit, so even
//	    f(λx. c(x)) at the outer position is not emitted.
//	  - c : A→bool is the only polymorphic CONST in the lemma, and it
//	    sits under λx — skeleton.MatchingPoints stops at AbsTerm bodies
//	    so c is invisible to the standard anchor enumeration.
//
//	Goal:  ⊢ f_goal(λp:goal_A. c(p))
//	  - Same shape at a different A-instance.
//
// Without augmentation: MatchingPoints(lemma) returns ∅ useful anchors;
// adapter loop has nothing to match; tryAdaptLemmaTypes returns nil.
// With augmentation: c is added as a supplemental anchor (empty
// BoundVars, rigid var match); goal-side fallback finds c under λp;
// TypeOnlyMatch on bare-const c (size 1) vs bare-const c (size 1)
// unifies their types and recovers A := goal_A.
//
// This is a contrived shape — the type discipline usually
// pushes polymorphism to outer const heads where MatchingPoints does
// find them — but it pins the symmetric-with-goal-side behavior of
// the lemma-side fix. See note in tryAdaptLemmaTypes' godoc for the
// residual gap (slot vars trapped inside under-λ anchors are matched rigidly).
func TestTryAdaptLemmaTypes_LemmaSideUnderLambda(t *testing.T) {
	defA := core.MakeVarType("?def_A_lemma_under_lambda")
	goalA := core.MakeVarType("?goal_A_lemma_under_lambda")

	// Shared const meta for c — poly at A→bool.
	cMeta := makeUnaryConst("c_under_lambda_meta", defA)

	// Lemma side: c at defA, f as ∀-bound slot.
	cLemma := core.MakeConstTerm(cMeta, core.MakeFun(defA, core.TypeBool()))
	x := core.Var("x", defA)
	lambdaLemma := core.Abs(x, core.Apply(cLemma, x)) // λx:def_A. c(x)
	fLemma := core.Var("f", core.MakeFun(core.MakeFun(defA, core.TypeBool()), core.TypeBool()))
	bodyLemma := core.Apply(fLemma, lambdaLemma) // f(λx. c(x))
	lemma := core.MakeProp(ext.ForAll(fLemma)(ext.WrapTerm(bodyLemma)).Core())

	// Sanity: MatchingPoints(lemma) emits no polymorphic-const-headed
	// anchor reachable through its standard walk. We don't assert the
	// EXACT list (could change if MatchingPoints' decomposition
	// evolves), but we assert that NO emitted anchor has the c head —
	// which is exactly what makes this test exercise the
	// deep-walk-augmentation path.
	standardAnchors := skeleton.MatchingPoints(lemma)
	for _, a := range standardAnchors {
		head, _ := ext.MatchesApply(a.Term)
		if hc, isC := head.AsConst(); isC {
			assert.NotEqual(t, core.TermName("c_under_lambda_meta"), hc.Name(),
				"MatchingPoints must NOT find c at this lemma shape — "+
					"if it does, this test no longer exercises the lemma-side "+
					"deep-walk augmentation (rewrite the shape so c stays buried "+
					"under λ, e.g. by making f a Var-slot rather than a const)")
		}
	}

	// Goal side: c at goalA.
	cGoal := core.MakeConstTerm(cMeta, core.MakeFun(goalA, core.TypeBool()))
	p := core.Var("p", goalA)
	lambdaGoal := core.Abs(p, core.Apply(cGoal, p)) // λp:goal_A. c(p)
	fGoal := core.Var("f_goal", core.MakeFun(core.MakeFun(goalA, core.TypeBool()), core.TypeBool()))
	bodyGoal := core.Apply(fGoal, lambdaGoal)
	goal := core.MakeProp(bodyGoal)

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got,
		"adapter must recover def_A := goal_A via lemma-side deep walk + "+
			"goal-side deep-walk fallback — both halves combined catch the "+
			"under-λ-only polymorphic anchor")

	// Verify the substitution went the right way: the adapted lemma's
	// type variables should include `?goal_A_lemma_under_lambda`
	// (carried over from the goal), NOT `?def_A_lemma_under_lambda`
	// (the lemma's original). PropHasTypeVars stays true because
	// goal_A is itself a type variable; what we actually care about
	// is "no def_A remains anywhere".
	containsDefA := propHasTypeVarName(got, "?def_A_lemma_under_lambda")
	containsGoalA := propHasTypeVarName(got, "?goal_A_lemma_under_lambda")
	assert.False(t, containsDefA,
		"adapted lemma must not retain def_A (substitution failed to replace it)")
	assert.True(t, containsGoalA,
		"adapted lemma must contain goal_A (substitution didn't propagate)")
}

// TestTryAdaptLemmaTypes_ExistentialBinderBeatsBareEq is a regression
// test. A polymorphic lemma whose only A-bearing const anchor is the
// ubiquitous bare equality `=` would, under const-anchor matching alone,
// pin A to the goal's `=` operand type. But the lemma's existential witness
// binder (the "output" it provides) demands a different, larger A. The
// existential-binder seed must win.
//
// Minimal faithful shape of ℕ's recursion principle applied to a
// 2-arg primitive-recursion existence goal:
//
//	lemma: ∀e:A. ∃g:ind→A. (e = e)
//	goal:  ∃g:ind→(ind→ind). (d = d)        d:ind
//
//	bare `=` anchor: e=e (e a slot at A) vs d=d (d:ind)  ⇒ A := ind        (wrong)
//	∃-binder anchor: ind→A             vs ind→(ind→ind)  ⇒ A := ind→ind     (right)
//
// The adapter must commit A := ind→ind.
func TestTryAdaptLemmaTypes_ExistentialBinderBeatsBareEq(t *testing.T) {
	A := core.TypeA()
	ind := TypeInd

	e := core.Var("e", A)
	g := core.Var("g", core.MakeFun(ind, A)) // ∃g:ind→A
	lemmaBody := ext.Exists(g)(ext.WrapTerm(core.Eq(e, e)))
	lemma := core.MakeProp(ext.ForAll(e)(lemmaBody).Core())

	d := core.Var("d", ind)
	gGoal := core.Var("g", core.MakeFun(ind, core.MakeFun(ind, ind))) // ∃g:ind→(ind→ind)
	goal := core.MakeProp(ext.Exists(gGoal)(ext.WrapTerm(core.Eq(d, d))).Core())

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "adapter must recover A from the existential binder")
	assert.False(t, ext.PropHasTypeVars(got), "A must be fully resolved")

	// Want: ∀e:ind→ind. ∃g:ind→(ind→ind). (e = e)
	eW := core.Var("e", core.MakeFun(ind, ind))
	gW := core.Var("g", core.MakeFun(ind, core.MakeFun(ind, ind)))
	want := core.MakeProp(ext.ForAll(eW)(ext.Exists(gW)(ext.WrapTerm(core.Eq(eW, eW)))).Core())
	assert.True(t, got.AlphaEquals(want),
		"existential-binder seed must beat the bare `=` anchor\n got = %s\nwant = %s",
		ext.PrintTerm(got.Conclusion()), ext.PrintTerm(want.Conclusion()))
}

// TestTryAdaptLemmaTypes_ExistentialBinderSeedsAlone covers the case where
// NO const anchor carries the type var at all — the existential binder is
// the sole source of the substitution. Without the seed, const-anchor
// matching recovers nothing and the lemma would be introduced polymorphic.
func TestTryAdaptLemmaTypes_ExistentialBinderSeedsAlone(t *testing.T) {
	A := core.TypeA()
	ind := TypeInd

	w := core.Var("w", ind) // fixed-type, carries no A
	g := core.Var("g", A)   // ∃g:A
	lemma := core.MakeProp(ext.Exists(g)(ext.WrapTerm(core.Eq(w, w))).Core())

	gGoal := core.Var("g", core.TypeBool()) // ∃g:bool
	goal := core.MakeProp(ext.Exists(gGoal)(ext.WrapTerm(core.Eq(w, w))).Core())

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got, "existential binder alone must drive A := bool")
	assert.False(t, ext.PropHasTypeVars(got))

	gW := core.Var("g", core.TypeBool())
	want := core.MakeProp(ext.Exists(gW)(ext.WrapTerm(core.Eq(w, w))).Core())
	assert.True(t, got.AlphaEquals(want), "got = %s want = %s",
		ext.PrintTerm(got.Conclusion()), ext.PrintTerm(want.Conclusion()))
}

// TestTryAdaptLemmaTypes_ExistentialBinder_CountMismatch_DoesNotSeedWrongly
// is the set_fold_stage shape: when the lemma's ∃-binder count differs from
// the goal's, the seedExistentialBinderSubsts safety gate must skip the
// seed entirely — positional pairing has no structural meaning across a
// count mismatch and would silently commit B := A (set_fold_stage's
// 2-∃ lemma loaded into its successor lemma's 4-∃ goal).
//
// Construction mirrors the set_fold_stage shape minimally:
//
//	lemma: ∀f:(A,B)→B. ∃x:A. ∃c:B. f(x,c) = c       (2 ∃-binders, mixed A/B)
//	goal:  ∃u:A. ∃v:A. ∃t:B. ∃w:B. (...)            (4 ∃-binders, A's then B's)
//
// Positional pairing: pair[1] (lemma ∃c:B vs goal ∃v:A) commits B := A.
// With the gate: count mismatch → seed returns nil; the const-anchor walk
// runs unbiased; the lemma retains B unchanged.
func TestTryAdaptLemmaTypes_ExistentialBinder_CountMismatch_DoesNotSeedWrongly(t *testing.T) {
	A := core.TypeA()
	B := ext.TypeB
	AB_to_B := core.MakeFun(A, B, B)

	// Lemma: ∀f:(A,B)→B. ∃x:A. ∃c:B. f(x,c) = c
	f := core.Var("f", AB_to_B)
	x := core.Var("x", A)
	c := core.Var("c", B)
	body := ext.Exists(x)(ext.Exists(c)(
		ext.WrapTerm(core.Eq(ext.Apply(f, x, c), c)))).Core()
	lemma := core.MakeProp(ext.ForAll(f)(ext.WrapTerm(body)).Core())

	// Goal: a four-∃ shell with all A's first then all B's.
	// Choose an opaque atom (no const heads pointing at A/B) so the
	// const-anchor walk discovers nothing — the test ISOLATES the
	// existential-seed step.
	u := core.Var("u", A)
	v := core.Var("v", A)
	tt := core.Var("t", B)
	w := core.Var("w", B)
	// Equation across a polymorphic opaque relation R that the const-anchor
	// walk can't structurally inform.
	R := core.Var("R", core.MakeFun(A, A, B, B, core.TypeBool()))
	gconcl := ext.Exists(u)(ext.Exists(v)(ext.Exists(tt)(ext.Exists(w)(
		ext.WrapTerm(ext.Apply(R, u, v, tt, w))))))
	goal := core.MakeProp(gconcl.Core())

	got := TryAdaptLemmaTypes(lemma, goal)

	// The seed must NOT have collapsed B := A. Two acceptable outcomes:
	//   - got == nil (no usable substitution found at all), OR
	//   - got != nil and the residual still has B unchanged (no B→A).
	if got == nil {
		// Acceptable — adaptation found nothing actionable.
		return
	}

	// If adapter returned something, the lemma's `∀f` binder type must
	// still have B in its codomain (no B→A collapse).
	absF := ext.MatchesFORALL(got.Conclusion())
	require.False(t, absF.IsZero(), "adapted lemma must still be ∀-headed")
	fType := absF.Var().Type()
	assert.Truef(t, fType.Equals(AB_to_B),
		"set_fold_stage safety-gate bug: ∀f binder collapsed from %s to %s "+
			"(seed misfired across ∃-count mismatch)",
		ext.FormatType(AB_to_B), ext.FormatType(fType))
}

// TestTryAdaptLemmaTypes_FunctionTypedWitness_Snd_Regression pins
// adapter behavior for the snd projection-style lemma when the
// goal's witness for the ∀-binder has a concrete FUNCTION type.
//
// Setup:
//
//	lemma: ∀y:B x:A. y = snd(,(x, y))
//	goal:  ⊢ snd(,(q, p)) = p   with p : prod(C, P) → B', q : C → P
//
// Expected: adapter resolves B := prod(C, P) → B' (recovered from
// the const-anchor walk on `snd(,(x, y))` against the goal's
// `snd(,(q, p))`, which transitively constrains the `y`-binder's
// type via snd's own polymorphism: `snd : prod(A,B) → B`).
//
// The adapter needs no separate seeding of the binder substitution for
// a function-typed witness: the const-anchor walk resolves it. The
// test is a regression guard for that path.
func TestTryAdaptLemmaTypes_FunctionTypedWitness_Snd_Regression(t *testing.T) {
	A := core.MakeVarType("A_lemma_snd")
	B := core.MakeVarType("B_lemma_snd")
	Cvar := core.MakeVarType("C_w")
	Pvar := core.MakeVarType("P_w")
	Bprime := core.MakeVarType("Bprime_w")

	// Build snd : prod(A, B) → B and , : A → B → prod(A, B) using a
	// local prod meta. The point is to faithfully match the projection
	// lemma shape; the names of constants are kept as "snd" / "," to
	// mirror the library form, though the metas are local.
	prodMeta := core.MakeMetaType("prod", 2)
	prodAB := core.MakeCompositeType(prodMeta, A, B)
	sndType := core.MakeFun(prodAB, B)
	pairType := core.MakeFun(A, core.MakeFun(B, prodAB))
	sndMeta := core.MakeConstMeta("snd", sndType)
	pairMeta := core.MakeConstMeta(",", pairType)
	sndConst := core.MakeConstTerm(sndMeta, sndType)
	pairConst := core.MakeConstTerm(pairMeta, pairType)

	// lemma: ∀y:B. ∀x:A. y = snd(,(x, y))
	y := core.Var("y", B)
	x := core.Var("x", A)
	pair := ext.Apply(pairConst, x, y)
	sndPair := ext.Apply(sndConst, pair)
	body := core.Eq(y, sndPair)
	lemma := core.MakeProp(ext.ForAll(y)(ext.ForAll(x)(ext.WrapTerm(body))).Core())

	// Goal: snd(,(q, p)) = p where p : (C, P) → B', q : C → P.
	// Specialize the local snd/, metas at the goal's concrete types
	// so the kernel sees them as the same metas as in the lemma.
	qType := core.MakeFun(Cvar, Pvar)
	pType := core.MakeFun(core.MakeCompositeType(prodMeta, Cvar, Pvar), Bprime)
	prodQP := core.MakeCompositeType(prodMeta, qType, pType)
	sndQPType := core.MakeFun(prodQP, pType)
	pairQPType := core.MakeFun(qType, core.MakeFun(pType, prodQP))
	sndQP := core.MakeConstTerm(sndMeta, sndQPType)
	pairQP := core.MakeConstTerm(pairMeta, pairQPType)

	q := core.Var("q", qType)
	p := core.Var("p", pType)
	goalPair := ext.Apply(pairQP, q, p)
	goalSndPair := ext.Apply(sndQP, goalPair)
	goalConcl := core.Eq(goalSndPair, p)
	goal := core.MakeProp(goalConcl)

	got := TryAdaptLemmaTypes(lemma, goal)
	t.Logf("lemma:  %s", ext.PrintTerm(lemma.Conclusion()))
	t.Logf("goal:   %s", ext.PrintTerm(goal.Conclusion()))
	if got != nil {
		t.Logf("adapted: %s", ext.PrintTerm(got.Conclusion()))
		yAbs := ext.MatchesFORALL(got.Conclusion())
		if !yAbs.IsZero() {
			t.Logf("adapted ∀y binder type: %s (lemma was %s)",
				yAbs.Var().Type().Key(), B.Key())
		}
	} else {
		t.Logf("adapter returned nil")
	}
	require.NotNil(t, got, "adapter must return non-nil (issue reproducer)")
	yAbs := ext.MatchesFORALL(got.Conclusion())
	require.False(t, yAbs.IsZero())
	assert.False(t, yAbs.Var().Type().Equals(B),
		"adapted ∀y binder type must NOT still be %s — it must specialize "+
			"to the goal's `p` type via value-position seeding", B.Key())

	// Direction-flipped variant — matches the issue's verbatim
	// failure shape `p = snd(,(q, p))` (lemma direction, opposite
	// of `snd(,(q, p)) = p`). The const-anchor walk should still
	// recover B := pType because snd(,(x,y))'s anchor matches
	// either direction of the goal's equation.
	flippedConcl := core.Eq(p, goalSndPair)
	flippedGoal := core.MakeProp(flippedConcl)
	gotFlipped := TryAdaptLemmaTypes(lemma, flippedGoal)
	t.Logf("flipped goal: %s", ext.PrintTerm(flippedGoal.Conclusion()))
	if gotFlipped != nil {
		t.Logf("adapted (flipped): %s", ext.PrintTerm(gotFlipped.Conclusion()))
		if yAbs := ext.MatchesFORALL(gotFlipped.Conclusion()); !yAbs.IsZero() {
			t.Logf("adapted ∀y binder type (flipped): %s", yAbs.Var().Type().Key())
		}
	} else {
		t.Logf("flipped: adapter returned nil")
	}
	require.NotNil(t, gotFlipped, "adapter must handle flipped direction too")
	yAbsFlipped := ext.MatchesFORALL(gotFlipped.Conclusion())
	require.False(t, yAbsFlipped.IsZero())
	assert.False(t, yAbsFlipped.Var().Type().Equals(B),
		"adapted ∀y binder type (flipped) must NOT still be %s", B.Key())
}

func TestTryAdaptLemmaTypes_SkipsSelfImageHypForConcreteSndGoal(t *testing.T) {
	// Regression for the live-chain wall: an already-loaded copy of the same
	// polymorphic snd lemma in the goal's hyps yields only identity type
	// substitutions. That hyp must not win the anchor race over the concrete
	// conclusion site.
	A := core.MakeVarType("A_lemma_snd_self_hyp")
	B := core.MakeVarType("B_lemma_snd_self_hyp")
	Cvar := core.MakeVarType("C_self_hyp")
	Pvar := core.MakeVarType("P_self_hyp")
	Bprime := core.MakeVarType("Bprime_self_hyp")

	prodMeta := core.MakeMetaType("prod", 2)
	prodAB := core.MakeCompositeType(prodMeta, A, B)
	sndType := core.MakeFun(prodAB, B)
	pairType := core.MakeFun(A, core.MakeFun(B, prodAB))
	sndMeta := core.MakeConstMeta("snd", sndType)
	pairMeta := core.MakeConstMeta(",", pairType)
	sndConst := core.MakeConstTerm(sndMeta, sndType)
	pairConst := core.MakeConstTerm(pairMeta, pairType)

	y := core.Var("y", B)
	x := core.Var("x", A)
	lemmaBody := core.Eq(y, ext.Apply(sndConst, ext.Apply(pairConst, x, y)))
	lemma := core.MakeProp(ext.ForAll(y)(ext.ForAll(x)(ext.WrapTerm(lemmaBody))).Core())

	qType := core.MakeFun(Cvar, Pvar)
	pType := core.MakeFun(core.MakeCompositeType(prodMeta, Cvar, Pvar), Bprime)
	prodQP := core.MakeCompositeType(prodMeta, qType, pType)
	sndQPType := core.MakeFun(prodQP, pType)
	pairQPType := core.MakeFun(qType, core.MakeFun(pType, prodQP))
	sndQP := core.MakeConstTerm(sndMeta, sndQPType)
	pairQP := core.MakeConstTerm(pairMeta, pairQPType)
	q := core.Var("q_self_hyp", qType)
	p := core.Var("p_self_hyp", pType)
	goalConcl := core.Eq(p, ext.Apply(sndQP, ext.Apply(pairQP, q, p)))
	goal := core.MakeProp(goalConcl, lemma.Conclusion())

	got := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, got)
	yAbs := ext.MatchesFORALL(got.Conclusion())
	require.False(t, yAbs.IsZero())
	assert.True(t, yAbs.Var().Type().Equals(pType),
		"self-image hyp must not block adapting B to the conclusion's function type")
}

// TestTryAdaptLemmaTypes_FunctionTypedWitness_Snd_CurryApplied_Regression
// is the curry-applied counterpart of the snd regression test above.
// The goal has `snd(,(q, p))(c, x) = body` — snd-of-pair as the HEAD
// of a curried application. Pins that the const-anchor walk's match
// on `snd(,(x,y))` correctly recovers the binder's function type
// even when the matched subterm sits as a function head in a larger
// applied form (the PairCollapse shape; this regression guard keeps
// the adapter side of it working).
//
// The test is a regression guard for this shape.
func TestTryAdaptLemmaTypes_FunctionTypedWitness_Snd_CurryApplied_Regression(t *testing.T) {
	A := core.MakeVarType("A_lemma_snd_curry")
	B := core.MakeVarType("B_lemma_snd_curry")
	Cvar := core.MakeVarType("C_curry")
	Pvar := core.MakeVarType("P_curry")
	Bprime := core.MakeVarType("Bprime_curry")

	prodMeta := core.MakeMetaType("prod", 2)
	prodAB := core.MakeCompositeType(prodMeta, A, B)
	sndType := core.MakeFun(prodAB, B)
	pairType := core.MakeFun(A, core.MakeFun(B, prodAB))
	sndMeta := core.MakeConstMeta("snd", sndType)
	pairMeta := core.MakeConstMeta(",", pairType)
	sndConst := core.MakeConstTerm(sndMeta, sndType)
	pairConst := core.MakeConstTerm(pairMeta, pairType)

	y := core.Var("y", B)
	x := core.Var("x", A)
	pair := ext.Apply(pairConst, x, y)
	sndPair := ext.Apply(sndConst, pair)
	body := core.Eq(y, sndPair)
	lemma := core.MakeProp(ext.ForAll(y)(ext.ForAll(x)(ext.WrapTerm(body))).Core())

	// Goal: snd(,(q, p))(c, x_g) = body_rhs, where snd-of-pair is the
	// head of a curried application.
	qType := core.MakeFun(Cvar, Pvar)
	pType := core.MakeFun(Cvar, core.MakeFun(Pvar, Bprime))
	prodQP := core.MakeCompositeType(prodMeta, qType, pType)
	sndQPType := core.MakeFun(prodQP, pType)
	pairQPType := core.MakeFun(qType, core.MakeFun(pType, prodQP))
	sndQP := core.MakeConstTerm(sndMeta, sndQPType)
	pairQP := core.MakeConstTerm(pairMeta, pairQPType)

	q := core.Var("q", qType)
	p := core.Var("p", pType)
	cG := core.Var("c_g", Cvar)
	xG := core.Var("x_g", Pvar)
	bodyRhs := core.Var("body_rhs", Bprime)

	goalPair := ext.Apply(pairQP, q, p)
	goalSndPair := ext.Apply(sndQP, goalPair)     // snd(,(q,p)) : (C, P) → B'
	goalCurried := ext.Apply(goalSndPair, cG, xG) // snd(,(q,p))(c_g, x_g) : B'
	goalConcl := core.Eq(goalCurried, bodyRhs)
	goal := core.MakeProp(goalConcl)

	got := TryAdaptLemmaTypes(lemma, goal)
	t.Logf("lemma:  %s", ext.PrintTerm(lemma.Conclusion()))
	t.Logf("goal:   %s", ext.PrintTerm(goal.Conclusion()))
	if got != nil {
		t.Logf("adapted: %s", ext.PrintTerm(got.Conclusion()))
		if yAbs := ext.MatchesFORALL(got.Conclusion()); !yAbs.IsZero() {
			t.Logf("adapted ∀y binder type: %s (lemma was %s)",
				yAbs.Var().Type().Key(), B.Key())
		}
	} else {
		t.Logf("adapter returned nil")
	}
	require.NotNil(t, got,
		"adapter must return non-nil for curry-applied snd site (issue reproducer)")
	yAbs := ext.MatchesFORALL(got.Conclusion())
	require.False(t, yAbs.IsZero())
	assert.False(t, yAbs.Var().Type().Equals(B),
		"adapted ∀y binder type must NOT still be %s — the curry-applied "+
			"site's HEAD subterm `snd(,(q,p))` has type (C,P)→B' which "+
			"must specialize B via the const-anchor walk on snd",
		B.Key())
}

// TestTryAdaptLemmaTypes_BareConstAnchorMustNotCollapseDistinctTypeVars:
// loading a lemma of finite_set.FiniteImage's shape must not collapse its two
// distinct type variables.
//
// SHAPE:
//
//	Lemma: ⊢ ∀s:(α→bool).∀f:(α→β). FIN⟨β⟩(IMG(f,s)) ∨ ¬FIN⟨α⟩(s)
//	  α, β are DISTINCT lemma type vars, but NAMED "A"/"B" like a cited
//	  entry's — the goal's ambient type vars carry the same names
//	  (pointer-distinct), exactly as independent decoding produces.
//
//	Goal:  ⊢ (FIN⟨prod(A,B)⟩(u) ∨ ¬FIN⟨A⟩(sg)) ∨ ¬FIN⟨B⟩(w)
//	  Three DISTINCT bare instances of FIN: prod(A,B), A, B.
//
// The lemma's structural anchors either fail (`FIN(IMG(f,s))` — the
// goal has no IMG) or pin only α (`FIN(s)` → α := A). β is then left
// to the BARE `FIN⟨β⟩` const anchor, which matches every bare FIN
// occurrence in the goal in index order:
//
//	FIN⟨prod(A,B)⟩ → β := prod(A,B)  — dropped by the name-collision
//	                                    occurs-check ("B" occurs in it)
//	FIN⟨A⟩         → β := A          — COMMITTED (the bug: collapses
//	                                    f's binder to A→A)
//
// The committed binding is a coin-flip on goal-candidate order, not a
// structural finding. Correct behavior: with AMBIGUOUS bare instances
// the bare anchor must not bind at all — β stays a free/general type
// var, so the installed hyp keeps ∀f:(A→β) with two distinct type
// vars, and downstream instantiate/term_specialize can still pin β.
func TestTryAdaptLemmaTypes_BareConstAnchorMustNotCollapseDistinctTypeVars(t *testing.T) {
	// Lemma-side type vars (named like a cited entry's).
	alpha := core.MakeVarType("A")
	beta := core.MakeVarType("B")

	// FIN : (T → bool) → bool, polymorphic in T (schema var = alpha).
	finMeta := core.MakeConstMeta("FIN_collapse_regression",
		core.MakeFun(core.MakeFun(alpha, core.TypeBool()), core.TypeBool()))
	// IMG : (α→β) → (α→bool) → (β→bool).
	imgMeta := core.MakeConstMeta("IMG_collapse_regression",
		core.MakeFun(core.MakeFun(alpha, beta),
			core.MakeFun(alpha, core.TypeBool()),
			core.MakeFun(beta, core.TypeBool())))

	finAlpha := core.MakeConstTerm(finMeta,
		core.MakeFun(core.MakeFun(alpha, core.TypeBool()), core.TypeBool()))
	finBeta := core.MakeConstTerm(finMeta,
		core.MakeFun(core.MakeFun(beta, core.TypeBool()), core.TypeBool()))
	img := core.MakeConstTerm(imgMeta, imgMeta.AbsType())

	sL := core.Var("s", core.MakeFun(alpha, core.TypeBool()))
	fL := core.Var("f", core.MakeFun(alpha, beta))
	lemmaBody := ext.WrapTerm(ext.Apply(finBeta, ext.Apply(img, fL, sL))).
		Or(ext.Not(ext.Apply(finAlpha, sL)))
	lemma := core.MakeProp(ext.ForAll(sL, fL)(lemmaBody).Core())

	// Goal-side ambient type vars: SAME NAMES, distinct pointers.
	gA := core.MakeVarType("A")
	gB := core.MakeVarType("B")
	prodMeta := core.MakeMetaType("prod", 2)
	prodAB := core.MakeCompositeType(prodMeta, gA, gB)

	finProd := core.MakeConstTerm(finMeta,
		core.MakeFun(core.MakeFun(prodAB, core.TypeBool()), core.TypeBool()))
	finGA := core.MakeConstTerm(finMeta,
		core.MakeFun(core.MakeFun(gA, core.TypeBool()), core.TypeBool()))
	finGB := core.MakeConstTerm(finMeta,
		core.MakeFun(core.MakeFun(gB, core.TypeBool()), core.TypeBool()))

	u := core.Var("u", core.MakeFun(prodAB, core.TypeBool()))
	sg := core.Var("sg", core.MakeFun(gA, core.TypeBool()))
	w := core.Var("w", core.MakeFun(gB, core.TypeBool()))

	goalConcl := ext.WrapTerm(ext.Apply(finProd, u)).
		Or(ext.Not(ext.Apply(finGA, sg))).
		Or(ext.Not(ext.Apply(finGB, w)))
	goal := core.MakeProp(goalConcl.Core())

	got := TryAdaptLemmaTypes(lemma, goal)
	t.Logf("lemma: %s", ext.PrintTermWithPolyBinders(lemma.Conclusion()))
	t.Logf("goal:  %s", ext.PrintTermWithPolyBinders(goal.Conclusion()))

	// nil is a PASS: the lemma is applied as-is, keeping α ≠ β. A
	// non-nil adaptation is fine ONLY if the ∀f binder still has two
	// distinct type vars (domain ≠ codomain, codomain not pinned to
	// the goal's A).
	if got == nil {
		return
	}
	t.Logf("adapted: %s", ext.PrintTermWithPolyBinders(got.Conclusion()))
	sAbs := ext.MatchesFORALL(got.Conclusion())
	require.False(t, sAbs.IsZero(), "adapted lemma must stay ∀s-headed")
	fAbs := ext.MatchesFORALL(sAbs.Body())
	require.False(t, fAbs.IsZero(), "adapted lemma must keep the ∀f binder")
	fType := fAbs.Var().Type()
	fFun, okFun := fType.(core.CompositeType)
	require.True(t, okFun, "∀f binder must stay function-typed; got %s", fType.Key())
	dom, cod := fFun.SubType(0), fFun.SubType(1)
	assert.False(t, dom.Equals(cod),
		"∀f binder collapsed to %s → %s: the lemma's DISTINCT type vars "+
			"α, β were conflated by a bare-const anchor (order-dependent "+
			"goal instance pick), the finite_set.FiniteImage lemma-load collapse bug",
		dom.Key(), cod.Key())
	codVar, codIsVar := cod.(core.VarType)
	require.True(t, codIsVar,
		"∀f binder codomain must remain a free type var (β unpinned); got %s", cod.Key())
	assert.False(t, codVar.Equals(gA),
		"β must not alias the goal's ambient A")
}

// ---------------------------------------------------------------------------
// EnumerateLemmaTypeAdaptations tests
// ---------------------------------------------------------------------------

// TestEnumerateLemmaTypeAdaptations_TwoInstances is the core multi-
// instance contract: a goal carrying the lemma's const at TWO distinct
// type instances yields TWO adaptations — the first being exactly what
// TryAdaptLemmaTypes commits, the second the instance the single-
// adaptation path drops (the zip / two-list-map class in miniature).
func TestEnumerateLemmaTypeAdaptations_TwoInstances(t *testing.T) {
	// Lemma: ⊢ ∀l:A. F⟨A⟩(l)   with F : A → bool.
	fMeta := makeUnaryConst("Fenum2", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	// Goal: ⊢ F⟨bool⟩(c) ∧ F⟨ind⟩(d).
	fBool := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	fInd := core.MakeConstTerm(fMeta, core.MakeFun(TypeInd, core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	d := core.Var("d", TypeInd)
	goal := core.MakeProp(ext.And(core.Apply(fBool, c), core.Apply(fInd, d)).Core())

	got := EnumerateLemmaTypeAdaptations(lemma, goal)
	require.Len(t, got, 2, "two distinct instances in the goal → two adaptations")

	primary := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, primary)
	assert.True(t, got[0].AlphaEquals(primary),
		"result[0] must equal the single-adaptation commit; got %v want %v", got[0], primary)
	assert.False(t, got[0].AlphaEquals(got[1]), "instances must be distinct")
	for i, g := range got {
		assert.False(t, ext.PropHasTypeVars(g), "instance %d must be fully instantiated", i)
	}
}

// TestEnumerateLemmaTypeAdaptations_SingleInstance: on a single-instance
// goal the enumeration degenerates to exactly the TryAdaptLemmaTypes
// result — no phantom alternates.
func TestEnumerateLemmaTypeAdaptations_SingleInstance(t *testing.T) {
	fMeta := makeUnaryConst("Fenum1", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	fBool := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	c := core.Var("c", core.TypeBool())
	goal := core.MakeProp(core.Apply(fBool, c))

	got := EnumerateLemmaTypeAdaptations(lemma, goal)
	require.Len(t, got, 1)
	primary := TryAdaptLemmaTypes(lemma, goal)
	require.NotNil(t, primary)
	assert.True(t, got[0].AlphaEquals(primary))
}

// TestEnumerateLemmaTypeAdaptations_NoMatch mirrors
// TestTryAdaptLemmaTypes_NoGoalMatch: nothing structurally compatible →
// nil (and never a panic / empty-σ instance).
func TestEnumerateLemmaTypeAdaptations_NoMatch(t *testing.T) {
	fMeta := makeUnaryConst("Fenum0", core.TypeA())
	gMeta := makeUnaryConst("Genum0", core.TypeBool())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	gConst := core.MakeConstTerm(gMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	x := core.Var("x", core.TypeBool())
	goal := core.MakeProp(core.Apply(gConst, x))

	assert.Nil(t, EnumerateLemmaTypeAdaptations(lemma, goal))
	// Ground lemma early-out parity.
	assert.Nil(t, EnumerateLemmaTypeAdaptations(goal, goal))
}

// TestEnumerateLemmaTypeAdaptations_FourInstances: the enumerator
// itself does NOT cap (the engine caps at its own rule-copy limit and
// must be able to SEE the overflow to diagnose it). Four distinct
// instances → four adaptations.
func TestEnumerateLemmaTypeAdaptations_FourInstances(t *testing.T) {
	fMeta := makeUnaryConst("Fenum4", core.TypeA())
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	l := core.Var("l", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(l)(ext.WrapTerm(core.Apply(fLemma, l))).Core())

	types := []core.HolType{
		core.TypeBool(), TypeInd,
		core.MakeFun(core.TypeBool(), core.TypeBool()),
		core.MakeFun(TypeInd, core.TypeBool()),
	}
	var conj core.Term
	for i, ty := range types {
		fi := core.MakeConstTerm(fMeta, core.MakeFun(ty, core.TypeBool()))
		vi := core.Var(core.TermName(fmt.Sprintf("v%d", i)), ty)
		app := core.Apply(fi, vi)
		if conj == nil {
			conj = app
		} else {
			conj = ext.And(conj, app).Core()
		}
	}
	goal := core.MakeProp(conj)

	got := EnumerateLemmaTypeAdaptations(lemma, goal)
	require.Len(t, got, 4, "all four distinct instances must be enumerated (cap is the caller's)")
	seen := map[core.PropKey]struct{}{}
	for _, g := range got {
		seen[g.AlphaKey()] = struct{}{}
	}
	assert.Len(t, seen, 4, "instances must be pairwise distinct by AlphaKey")
}

// TestEnumerateLemmaTypeAdaptations_BareConstMultiInstance covers the
// deliberate divergence from TryAdaptLemmaTypes: a BARE polymorphic
// const anchor with multiple distinct goal instances is skipped by the
// single-adaptation path (order-dependent pick — the FiniteImage
// collapse guard, see bareConstAnchorAmbiguous), but for enumeration the
// ambiguity IS the multi-instance signal: each distinct instance becomes
// a branch.
func TestEnumerateLemmaTypeAdaptations_BareConstMultiInstance(t *testing.T) {
	// KC⟨A⟩ : A → bool appears only BARE (as an argument) in the lemma:
	//   lemma: ⊢ ∀g:((A→bool)→bool). g(KC⟨A⟩)
	kcMeta := core.MakeConstMeta("KCenum", core.MakeFun(core.TypeA(), core.TypeBool()))
	kcA := core.MakeConstTerm(kcMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	g := core.Var("g", core.MakeFun(core.MakeFun(core.TypeA(), core.TypeBool()), core.TypeBool()))
	lemma := core.MakeProp(ext.ForAll(g)(ext.WrapTerm(core.Apply(g, kcA))).Core())

	// Goal: ⊢ H1(KC⟨bool⟩) ∧ H2(KC⟨ind⟩) — KC at two distinct instances,
	// under DIFFERENT (monomorphic) heads so no applied anchor can bind A.
	kcBool := core.MakeConstTerm(kcMeta, core.MakeFun(core.TypeBool(), core.TypeBool()))
	kcInd := core.MakeConstTerm(kcMeta, core.MakeFun(TypeInd, core.TypeBool()))
	h1 := core.MakeConstTerm(
		core.MakeConstMeta("H1enum", core.MakeFun(core.MakeFun(core.TypeBool(), core.TypeBool()), core.TypeBool())),
		core.MakeFun(core.MakeFun(core.TypeBool(), core.TypeBool()), core.TypeBool()))
	h2 := core.MakeConstTerm(
		core.MakeConstMeta("H2enum", core.MakeFun(core.MakeFun(TypeInd, core.TypeBool()), core.TypeBool())),
		core.MakeFun(core.MakeFun(TypeInd, core.TypeBool()), core.TypeBool()))
	goal := core.MakeProp(ext.And(core.Apply(h1, kcBool), core.Apply(h2, kcInd)).Core())

	// Single-adaptation path: ambiguous bare-const anchor → no adaptation.
	assert.Nil(t, TryAdaptLemmaTypes(lemma, goal),
		"single-adaptation path must keep the ambiguity skip (order-independence guard)")

	got := EnumerateLemmaTypeAdaptations(lemma, goal)
	require.Len(t, got, 2, "enumeration must branch one instance per distinct bare-const type")
	assert.False(t, got[0].AlphaEquals(got[1]))
	for i, gp := range got {
		assert.False(t, ext.PropHasTypeVars(gp), "instance %d must be fully instantiated", i)
	}
}
