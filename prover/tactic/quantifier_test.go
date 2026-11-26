package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestConclExistsWitness_BasicShape verifies the happy path: concl
// `⊢ ∃x. P(x)`, witness term `y` (free in scope), produces subgoal
// `⊢ P(y)` and the reconstruct successfully derives the original
// goal from the subgoal-thm.
func TestConclExistsWitness_BasicShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// ⊢ ∃x. P(x)
	goal := MakeProp(Exists(x)(P.Apply(x)).Core())
	sg := ConclExistsWitnessTactic(y)(goal)
	assert.NotNil(t, sg, "tactic must apply on top-level ∃ goal")
	assert.Equal(t, 1, sg.Size(), "witness produces exactly one subgoal")

	// Subgoal: ⊢ P(y).
	child := sg.ChildGoal(0)
	assertPropAlphaEqual(t, child, MakeProp(P.Apply(y).Core()))

	// Reconstruct: feeding the subgoal back as a Thm produces a proof
	// of the original ∃-goal.
	assertSubGoals(t, sg, goal)
}

// TestConclExistsWitness_Unique pins the ∃! reading: the witness leaves
// one subgoal, P at the witness and that P holds of nothing else, and the
// reconstruction derives the ∃! goal from it.
func TestConclExistsWitness_Unique(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Q(z) ⊢ ∃!x. R(x, y), witnessed at z
	goal := MakeProp(Unique(x)(R.Apply(x, y)).Core(), Q.Apply(z).Core())
	sg := ConclExistsWitnessTactic(z)(goal)
	require.NotNil(t, sg, "tactic must apply on a top-level ∃! goal")
	require.Equal(t, 1, sg.Size(), "the witness leaves exactly one subgoal")

	// Subgoal: Q(z) ⊢ R(z, y) ∧ ∀x. R(x, y) ⇒ x = z.
	assertPropAlphaEqual(t, sg.ChildGoal(0), MakeProp(
		R.Apply(z, y).And(ForAll(x)(R.Apply(x, y).Imply(x.Eq(z)))).Core(),
		Q.Apply(z).Core()))
	assertSubGoals(t, sg, goal)
}

// TestConclExistsWitness_UniqueWitnessNamesTheBinder pins the capture
// case: a witness spelling the binder's own name is not captured by the
// uniqueness clause's binder.
func TestConclExistsWitness_UniqueWitnessNamesTheBinder(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	xNext := WrapTerm(x.AssertVar().Rename())
	w := Var("w", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	for _, witness := range []*ext.TermWrapper{x, xNext} {
		goal := MakeProp(Unique(x)(P.Apply(x)).Core())
		sg := ConclExistsWitnessTactic(witness)(goal)
		require.NotNil(t, sg)
		assertPropAlphaEqual(t, sg.ChildGoal(0), MakeProp(
			P.Apply(witness).And(ForAll(w)(P.Apply(w).Imply(w.Eq(witness)))).Core()))
		assertSubGoals(t, sg, goal)
	}
}

// TestConclExistsWitness_UniqueLeavesAUniqueHypothesis pins that the
// witness reads the CONCLUSION's ∃!: an ∃! hypothesis beside it stays as
// it stood.
func TestConclExistsWitness_UniqueLeavesAUniqueHypothesis(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// ∃!x. Q(x) ⊢ ∃!x. P(x), witnessed at z
	hyp := Unique(x)(Q.Apply(x)).Core()
	goal := MakeProp(Unique(x)(P.Apply(x)).Core(), hyp)
	sg := ConclExistsWitnessTactic(z)(goal)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	assertPropAlphaEqual(t, sg.ChildGoal(0), MakeProp(
		P.Apply(z).And(ForAll(x)(P.Apply(x).Imply(x.Eq(z)))).Core(), hyp))
	assertSubGoals(t, sg, goal)
}

// TestConclExistsWitness_UniqueFunctionWitness pins the ∃! reading at a
// function-typed binder with a λ witness: the subgoal is β-normal, the
// witness applied inside the body reduced.
func TestConclExistsWitness_UniqueFunctionWitness(t *testing.T) {
	defer goleak.VerifyNone(t)

	fun := MakeFun(TypeA, TypeA)
	f := Var("f", fun)
	g := Var("g", fun)
	v := Var("v", TypeA)
	c := Var("c", TypeA)
	R := Var("R", MakeFun(fun, TypeA, TypeBool))
	identity := v.To(v)

	// ⊢ ∃!f. R(f, f(c)), witnessed at λv. v
	goal := MakeProp(Unique(f)(R.Apply(f, f.Apply(c))).Core())
	sg := ConclExistsWitnessTactic(identity)(goal)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	// Subgoal: ⊢ R(λv. v, c) ∧ ∀g. R(g, g(c)) ⇒ g = λv. v.
	assertPropAlphaEqual(t, sg.ChildGoal(0), MakeProp(
		R.Apply(identity, c).And(ForAll(g)(R.Apply(g, g.Apply(c)).Imply(g.Eq(identity)))).Core()))
	assertSubGoals(t, sg, goal)
}

// TestConclExistsWitness_UniqueTypeMismatch pins the type gate on the ∃!
// reading: a witness of another type leaves the goal alone.
func TestConclExistsWitness_UniqueTypeMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	b := Var("b", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))

	goal := MakeProp(Unique(x)(P.Apply(x)).Core())
	assert.Nil(t, ConclExistsWitnessTactic(b)(goal))
}

// TestConclExistsWitness_PreservesHyps verifies the tactic carries
// arbitrary hypotheses through unchanged.
func TestConclExistsWitness_PreservesHyps(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Q(y) ⊢ ∃x. P(x)
	goal := MakeProp(Exists(x)(P.Apply(x)).Core(), Q.Apply(y).Core())
	sg := ConclExistsWitnessTactic(y)(goal)
	assert.NotNil(t, sg)
	assertSubGoals(t, sg, goal)
}

// TestConclExistsWitness_NotExistsConcl pins the negative shape:
// non-∃ conclusions return nil.
func TestConclExistsWitness_NotExistsConcl(t *testing.T) {
	defer goleak.VerifyNone(t)

	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	goal := MakeProp(P.Apply(y).Core()) // ⊢ P(y), not ∃-headed
	assert.Nil(t, ConclExistsWitnessTactic(y)(goal))
}

// TestConclExistsWitness_TypeMismatch verifies the type-check guard:
// witness whose type doesn't match the bound variable returns nil
// (instead of panicking inside the kernel).
func TestConclExistsWitness_TypeMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeB) // wrong type
	P := Var("P", MakeFun(TypeA, TypeBool))

	goal := MakeProp(Exists(x)(P.Apply(x)).Core())
	assert.Nil(t, ConclExistsWitnessTactic(z)(goal),
		"witness of mismatched type must return nil, not panic")
}

// TestHypForallInstantiate_BasicShape covers the happy path:
// hyp `∀x. P(x)`, witness `y`, produces subgoal that adds `P(y)` to
// hyps and keeps the original ∀ available.
func TestHypForallInstantiate_BasicShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// ∀x. P(x) ⊢ Q(y)
	goal := MakeProp(Q.Apply(y).Core(), ForAll(x)(P.Apply(x)).Core())
	sg := HypForallInstantiateTactic(y)(goal)
	assert.NotNil(t, sg, "tactic must apply when a hyp is ∀-headed")
	assert.Equal(t, 1, sg.Size())

	// Subgoal must contain BOTH the original ∀ and the new P(y).
	child := sg.ChildGoal(0)
	hasForall := false
	hasInstantiated := false
	for h := range child.HypIter() {
		if h.AlphaEquals(ForAll(x)(P.Apply(x)).Core()) {
			hasForall = true
		}
		if h.AlphaEquals(P.Apply(y).Core()) {
			hasInstantiated = true
		}
	}
	assert.True(t, hasForall, "instantiate must keep the original ∀ available")
	assert.True(t, hasInstantiated, "instantiate must add P(t) to hyps")

	assertSubGoals(t, sg, goal)
}

// TestHypForallInstantiate_NoForallHyp pins the negative shape:
// no ∀-headed hyp → returns nil.
func TestHypForallInstantiate_NoForallHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// ⊢ P(y) — no hyps at all.
	goal := MakeProp(P.Apply(y).Core())
	assert.Nil(t, HypForallInstantiateTactic(y)(goal))
}

// TestHypForallInstantiate_TypeMismatch pins the type-check guard.
func TestHypForallInstantiate_TypeMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeB) // wrong type
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeB, TypeBool))

	// Only ∀-hyp is over TypeA, witness is TypeB → no match.
	goal := MakeProp(Q.Apply(z).Core(), ForAll(x)(P.Apply(x)).Core())
	assert.Nil(t, HypForallInstantiateTactic(z)(goal),
		"no ∀-hyp matches witness type → nil")
}

// TestHypForallInstantiate_NoProgress verifies the alpha-equals
// guard: if instantiating produces a subgoal identical to the
// original (e.g. P(t) already present as a hyp), the tactic returns
// nil rather than emitting a degenerate child.
func TestHypForallInstantiate_NoProgress(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// ∀x. P(x), P(y) ⊢ Q(y) — P(y) already in hyps.
	goal := MakeProp(
		Q.Apply(y).Core(),
		ForAll(x)(P.Apply(x)).Core(),
		P.Apply(y).Core(),
	)
	assert.Nil(t, HypForallInstantiateTactic(y)(goal),
		"adding a hyp already in scope makes no progress; tactic must return nil")
}

// TestInstantiateAt_TargetsSpecificHyp pins the index-targeted kernel:
// when two ∀-hyps share the same binder type, the second is reachable
// by its index, while the first-matching tactic reaches only the first.
func TestInstantiateAt_TargetsSpecificHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	x1 := Var("x", TypeA)
	x2 := Var("x", TypeA) // same binder type as the other ∀
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	// Both ∀-hyps quantify over TypeA; only the ones at hyp 1 can be
	// reached without an index selector. Goal R(y) is just there to
	// keep the conclusion non-trivial.
	goal := MakeProp(
		R.Apply(y).Core(),
		ForAll(x1)(P.Apply(x1)).Core(), // hyp 0: ∀x. P(x)
		ForAll(x2)(Q.Apply(x2)).Core(), // hyp 1: ∀x. Q(x)
	)

	// Bare HypForallInstantiateTactic: reaches hyp 0 only.
	sg0 := HypForallInstantiateTactic(y)(goal)
	require.NotNil(t, sg0)
	require.Equal(t, 1, sg0.Size())
	hasPy := false
	hasQy := false
	for h := range sg0.ChildGoal(0).HypIter() {
		if h.AlphaEquals(P.Apply(y).Core()) {
			hasPy = true
		}
		if h.AlphaEquals(Q.Apply(y).Core()) {
			hasQy = true
		}
	}
	assert.True(t, hasPy, "first-matching path must add P(y) (from hyp 0)")
	assert.False(t, hasQy, "first-matching path must NOT reach hyp 1's Q(y)")

	// Indexed at hyp 1: reaches Q.
	sg1 := instantiateAt(goal, 1, y)
	require.NotNil(t, sg1)
	require.Equal(t, 1, sg1.Size())
	hasPy = false
	hasQy = false
	for h := range sg1.ChildGoal(0).HypIter() {
		if h.AlphaEquals(P.Apply(y).Core()) {
			hasPy = true
		}
		if h.AlphaEquals(Q.Apply(y).Core()) {
			hasQy = true
		}
	}
	assert.True(t, hasQy, "indexed path at hyp 1 must add Q(y)")
	assert.False(t, hasPy, "indexed path at hyp 1 must NOT reach hyp 0's P(y)")

	assertSubGoals(t, sg0, goal)
	assertSubGoals(t, sg1, goal)
}

// TestInstantiateAt_NotForallHyp verifies the indexed kernel returns nil
// when hyps[idx] is not ∀-headed.
func TestInstantiateAt_NotForallHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	// hyp 0 is not ∀-headed (a different predicate so instantiating
	// hyp 1 actually makes progress); hyp 1 is.
	goal := MakeProp(
		Q.Apply(y).Core(),
		R.Apply(y).Core(),
		ForAll(x)(P.Apply(x)).Core(),
	)
	assert.Nil(t, instantiateAt(goal, 0, y),
		"hyp 0 (R(y)) is not ∀-headed; must return nil")
	assert.NotNil(t, instantiateAt(goal, 1, y),
		"hyp 1 (∀x.P(x)) is ∀-headed; must succeed")
}

// TestInstantiateAt_TypeMismatch verifies the binder-type check fires
// at the indexed hyp.
func TestInstantiateAt_TypeMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeB) // wrong type
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeB, TypeBool))

	goal := MakeProp(Q.Apply(z).Core(), ForAll(x)(P.Apply(x)).Core())
	assert.Nil(t, instantiateAt(goal, 0, z),
		"binder type TypeA does not match witness type TypeB; nil")
}

// TestStripQuant1_StripsExactlyOne: ⊢ ∀x.∀y. q(x,y) peels ONLY the
// head binder — the child is ⊢ ∀y. q(x₀, y) with the inner ∀ intact —
// and the reconstruct re-derives the original goal.
func TestStripQuant1_StripsExactlyOne(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	x0 := Var("x_0", TypeA) // the Skolem mint
	q := Var("q", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))

	goal := MakeProp(ForAll(x)(ForAll(y)(q.Apply(x, y))).Core())
	sg := StripQuant1Tactic(goal)
	require.NotNil(t, sg, "tactic must apply on ∀-headed conclusion")
	require.Equal(t, 1, sg.Size())

	child := sg.ChildGoal(0)
	want := ForAll(y)(q.Apply(x0, y)).Core()
	assert.True(t, child.Conclusion().AlphaEquals(want),
		"child must keep the inner ∀ intact:\n  want %s\n  got  %s",
		ext.PrintTerm(want), ext.PrintTerm(child.Conclusion()))
	assert.False(t, ext.MatchesFORALL(child.Conclusion()).IsZero(), "inner ∀ must survive the single strip")

	assertSubGoals(t, sg, goal)
}

// TestStripQuant1_InnerExistsIntact: ⊢ ∀x.∃d. r(x,d) strips the ∀ and
// leaves the ∃ under it untouched.
func TestStripQuant1_InnerExistsIntact(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	d := Var("d", TypeA)
	x0 := Var("x_0", TypeA)
	r := Var("r", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))

	goal := MakeProp(ForAll(x)(Exists(d)(r.Apply(x, d))).Core())
	sg := StripQuant1Tactic(goal)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())

	child := sg.ChildGoal(0)
	want := Exists(d)(r.Apply(x0, d)).Core()
	assert.True(t, child.Conclusion().AlphaEquals(want),
		"inner ∃ must survive:\n  want %s\n  got  %s",
		ext.PrintTerm(want), ext.PrintTerm(child.Conclusion()))

	assertSubGoals(t, sg, goal)
}

// TestStripQuant1_ConclusionOnly pins the negative shapes: a non-∀
// conclusion returns nil, and — unlike StripQuantTactic — an ∃-hyp is
// NEVER Skolemized here.
func TestStripQuant1_ConclusionOnly(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Non-∀ conclusion, no hyps.
	assert.Nil(t, StripQuant1Tactic(MakeProp(P.Apply(c).Core())))

	// ∃-hyp present (StripQuantTactic WOULD fire on it) — the bounded
	// variant must still decline: conclusion side only.
	goal := MakeProp(Q.Apply(c).Core(), Exists(x)(P.Apply(x)).Core())
	require.NotNil(t, StripQuantTactic(goal),
		"sanity: the strip-everything tactic fires on the ∃-hyp")
	assert.Nil(t, StripQuant1Tactic(goal),
		"single-binder strip must not touch ∃-hyps")
}

// TestStripQuant1_NameCompatibleWithFullStrip: n successive single
// strips mint exactly the Skolem names ONE StripQuantTactic call
// mints for the same prefix (the name-compatibility contract in the
// doc comment).
func TestStripQuant1_NameCompatibleWithFullStrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	q := Var("q", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))

	goal := MakeProp(ForAll(x)(ForAll(y)(q.Apply(x, y))).Core())

	full := StripQuantTactic(goal)
	require.NotNil(t, full)

	sg1 := StripQuant1Tactic(goal)
	require.NotNil(t, sg1)
	sg2 := StripQuant1Tactic(sg1.ChildGoal(0))
	require.NotNil(t, sg2)

	// Name-sensitive comparison: Equals, not AlphaEquals — the minted
	// frees must MATCH (x_0, y_0), not merely correspond.
	assert.True(t, sg2.ChildGoal(0).Conclusion().Equals(full.ChildGoal(0).Conclusion()),
		"two single strips must land on the full strip's goal verbatim:\n  full %s\n  1+1  %s",
		ext.PrintTerm(full.ChildGoal(0).Conclusion()),
		ext.PrintTerm(sg2.ChildGoal(0).Conclusion()))
}

// TestHypForallConj_RepeatedBinderName splits a prefix that spells one
// name twice, the prefix a definition's binder makes when it unfolds
// under a ∀ of the same name: at one type the decomposer freshens the
// inner binder, at two types the binders are two variables already.
// Each conjunct's bridge rebuilds the goal from the split hypotheses.
func TestHypForallConj_RepeatedBinderName(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	xAtB := Var("x", TypeB)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeB, TypeBool))

	for name, h := range map[string]Term{
		"one type":         ForAll(x)(ForAll(x)(P.Apply(x).And(Q.Apply(x)))).Core(),
		"one type, spaced": ForAll(x)(ForAll(y)(ForAll(x)(P.Apply(x).And(Q.Apply(y))))).Core(),
		"two types":        ForAll(x)(ForAll(xAtB)(P.Apply(x).And(R.Apply(xAtB)))).Core(),
	} {
		t.Run(name, func(t *testing.T) {
			split := HypForallConjTactic(MakeProp(T, h))
			require.NotNil(t, split, "the prefix distributes over the conjuncts")
			conjunct := split.ChildGoal(0).Hyp(0)
			goal := MakeProp(conjunct, h)
			sg := HypForallConjTactic(goal)
			require.NotNil(t, sg)
			assert.True(t, sg.Reconstruct(prop.Assume(conjunct)).AlphaEquals(goal))
		})
	}
}
