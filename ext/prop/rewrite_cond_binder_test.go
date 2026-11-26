package prop

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestWhistleOrderedGate_PassesEtaExpansion pins the ordered gate's
// boundary with the normalizer's η-direction. FunEqRewrite is shallow:
// on `F = λx.b` its first fire is the η-alignment `λx.F(x) = λx.b`, and
// only the rescan produces `∀x. F(x) = b`. The alignment keeps the rigid
// symbol multiset and its two sides are βη-equal, so it reaches the
// gate's administrative branch; the ∀-producing step is new rigid
// material and was never gated. That branch once admitted a βη-equal
// fire only as a raw shrink and so declined the alignment — and
// QuantifierRewrite's `∀P` → `∀x.P(x)` — silently, an ordering decline
// being no counted suppression: routing TrivialNormalize through
// DeepRewriteWhistled returned nil on a plain function equality
// (TestEtaContextRewrite caught it). The gate now passes every βη-equal
// fire; η-direction is the composition's business (etaContextRewrite
// excludes the expanding heads), not a fire-local one. This does NOT
// license a normalizer under the whistle: the growth blade cuts
// legitimate CondElim cascades (94 of 2011 recorded proofs when it was
// tried). The pin makes the classifier's contract explicit so a change
// to it is made on purpose.
func TestWhistleOrderedGate_PassesEtaExpansion(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	F := Var("F", MakeFun(TypeInd, TypeInd))
	G := Var("G", MakeFun(TypeInd, TypeInd, TypeInd))
	H := Var("H", MakeFun(TypeInd, TypeInd))
	P := Var("P", MakeFun(TypeInd, TypeBool))
	forall := Const(FORALL.Meta(), MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	in := F.Eq(x.To(G.Apply(y, x)))
	expected := ForAll(x)(F.Apply(x).Eq(G.Apply(y, x)))

	// The alignment fire: βη-equal sides, raw growth — passed.
	fire := FunEqRewrite(in)
	require.NotNil(t, fire, "the bare leaf fires")
	assert.True(t, Rhs(fire).AlphaEquals(x.To(F.Apply(x)).Eq(x.To(G.Apply(y, x)))),
		"the first fire is the η-alignment, not the expansion")
	assert.True(t, skeleton.PermutationFireAllowed(in, Rhs(fire)),
		"a βη-equal fire is not a permutation; the ordered gate passes it")
	// Through the whistled driver the leaf reaches the expansion — from
	// one bare side, from two (three fires), and for a quantifier's bare
	// predicate.
	assertRewrite(t, uncut(t, DeepRewriteWhistled(noHyps, FunEqRewrite)), in, expected)
	assertRewrite(t, uncut(t, DeepRewriteWhistled(noHyps, FunEqRewrite)), F.Eq(H),
		ForAll(x)(F.Apply(x).Eq(H.Apply(x))))
	assertRewrite(t, uncut(t, DeepRewriteWhistled(noHyps, QuantifierRewrite)), ext.WrapTerm(Apply(forall, P)),
		ForAll(x)(P.Apply(x)))
	// The basic bundle under the whistle expands the same way and is at
	// its fixpoint on the expanded forms — no ping-pong with the
	// η-contracting leaf.
	bundle := uncut(t, DeepRewriteWhistled(noHyps, betaRewrite, etaContextRewrite, hilbertRewrite, BoolRewrite,
		DoubleNegRewrite, PushNegRewrite, QuantifierRewrite, trivialCondRewrite, FunEqRewrite))
	assertRewrite(t, bundle, in, expected)
	assert.Nil(t, bundle(ForAll(x)(P.Apply(x))))
	assert.Nil(t, bundle(x.SuchThat(P.Apply(x))))
	assertRewrite(t, TrivialNormalize, in, expected)
}

// TestCondSwap_UnderBinder_Terminates pins a shape that can cycle: a COND
// of predicates as the direct argument of ∀. The quantifier rule
// η-expands `∀ P` to `∀x. P(x)`; a swap fired at that λ would pull the
// COND back out through it and β-reduce to the original, and the two
// rules would never meet. With the swap declining at an abstraction the sound
// fire is the applied-level one, `COND(c, f, g)(x)` → `COND(c, f(x), g(x))`,
// after which the ∀'s argument is a λ and the quantifier rule rests;
// COND elimination then finishes the normalization in the bool body.
func TestCondSwap_UnderBinder_Terminates(t *testing.T) {
	x := Var("x", TypeInd)
	c := Var("c", TypeBool)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	forall := Const(FORALL.Meta(), MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	// ∀ (COND(c, λx.P(x), λx.Q(x)))
	in := forall.Apply(ext.Cond(c, x.To(P.Apply(x)), x.To(Q.Apply(x))))

	// The swap alone, deep: the quantifier rule η-expands the argument
	// and the swap does NOT fire at the λ it introduced. The applied site
	// inside is bool-typed, so the swap declines there too (elimination
	// is CondElim's job) — a fixpoint, reached in one pass, is what the
	// three rules alone produce. Before the guard this was the 2-cycle.
	step := DeepRewrite(QuantifierRewrite, CondSwapRewrite, betaRewrite)(in)
	require.NotNil(t, step)
	assert.True(t, Rhs(step).AlphaEquals(
		ForAll(x)(ext.Cond(c, x.To(P.Apply(x)), x.To(Q.Apply(x))).Apply(x))),
		"quantifier rule fires once, the swap never, got %s", ext.FormatTerm(Rhs(step), false))

	// The whole normalizer terminates on it and eliminates the COND.
	w := TrivialNormalize(in)
	require.NotNil(t, w)
	assert.True(t, Rhs(w).AlphaEquals(ForAll(x)(Not(c).Or(P.Apply(x)).And(c.Or(Q.Apply(x))))),
		"the normalizer terminates and eliminates the COND in the bool body")
}
