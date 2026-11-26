package unify

// Tests for the n = 0 Miller pattern on a unary-const chain: the pair
// shape is
//
//	f₀ ≐ op(op(...op(M)...))
//
// with op a unary CONST and M not free-mentioning f₀. Its unique MGU is
// f₀ ↦ op^k(M), which tryMillerPattern commits directly — the chain was
// the first shape to need the base case, because Huet's imitate path
// refuses it outright at depth ≥ 2 (containsUnaryOperatorCycle's
// nested-constant guard) where termination is in fact provable.
//
// Distilled from the lifts of double negation and of abs-of-abs to ℤ (where
// op = int_neg or int_abs and M = the loop-free chain bottom), kept
// at unify-level primitives so the test is self-contained.

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// TestUnifyUnaryChain_Depth2_Succeeds — the load-bearing case for the
// extension: f₀ ≐ op(op(c)) where op is a unary const and c is ground.
// Huet's imitate would refuse here via containsUnaryOperatorCycle's
// depth-≥2 guard; the Miller fast-path extension synthesizes the unique
// MGU f₀ ↦ op(op(c)) directly. (This is the shape of those
// two lifts: int_neg(int_neg(x)) or int_abs(int_abs(x)).)
func TestUnifyUnaryChain_Depth2_Succeeds(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd)) // unary const
	c := ext.TestConst("c", TypeInd)                     // ground bottom
	f0 := Var("f0", TypeInd)                             // meta-var

	// p.t0 = f0 (flex), p.t1 = op(op(c)) (rigid depth-2 chain).
	substs := UnifyTerms(t.Context(), f0, op.Apply(op.Apply(c)), utils.EmptyPredicate)

	// Unique MGU: f0 ↦ op(op(c)).
	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(f0.AssertVar(), op.Apply(op.Apply(c)))})
}

// TestUnifyUnaryChain_Depth3_Succeeds — same fast-path, deeper chain.
// Confirms the synthesis isn't accidentally hard-coded to depth 2.
func TestUnifyUnaryChain_Depth3_Succeeds(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	f0 := Var("f0", TypeInd)

	target := op.Apply(op.Apply(op.Apply(c)))
	substs := UnifyTerms(t.Context(), f0, target, utils.EmptyPredicate)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(f0.AssertVar(), target)})
}

// TestUnifyUnaryChain_Depth1_Succeeds — depth 1 is the n = 0 pattern
// like any other depth: f₀ ≐ op(c) has the one unifier f₀ ↦ op(c), and
// the result set is exactly that.
func TestUnifyUnaryChain_Depth1_Succeeds(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	f0 := Var("f0", TypeInd)
	target := op.Apply(c)

	substs := UnifyTerms(t.Context(), f0, target, utils.EmptyPredicate)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(f0.AssertVar(), target)})
}

// TestUnifyUnaryChain_OccursCheck_Refuses — when f₀ appears inside the
// chain bottom, the imitation chain would loop back through f₀'s
// expansion. The fast path's occurs check (p.t1.HasFree(f0)) refuses,
// and Huet's path also refuses (occurs check), so no MGU exists.
//
// Setup: f₀ ≐ op(op(f₀)). With f₀ ↦ op(op(f₀)) the substitution is
// infinite (cyclic). Refusing it is the correct behavior.
func TestUnifyUnaryChain_OccursCheck_Refuses(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd))
	f0 := Var("f0", TypeInd)

	substs := UnifyTerms(t.Context(), f0, op.Apply(op.Apply(f0)), utils.EmptyPredicate)

	assert.Nil(t, substs)
}

// TestUnifyUnaryChain_GroundVarHead — the chain's head is a GROUND
// variable, not a const. Rigid is rigid: the pair is the n = 0 pattern
// and its one unifier is f₀ ↦ h(h(c)).
func TestUnifyUnaryChain_GroundVarHead(t *testing.T) {
	defer goleak.VerifyNone(t)

	// h is a VARIABLE of function type, declared ground.
	h := Var("h", MakeFun(TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	f0 := Var("f0", TypeInd)
	target := h.Apply(h.Apply(c))

	ground := VarList{}
	ground.Add(h.AssertVar())

	substs := UnifyTerms(t.Context(), f0, target, ground.HasName)

	assertTermSubstsGroupEqual(t,
		substs,
		TermSubstsGroup{MakeTermSubst(f0.AssertVar(), target)})
}

// TestUnifyUnaryChain_NonUnaryConstHead — a const head of arity > 1
// is no chain, and is the n = 0 pattern all the same: one unifier,
// f₀ ↦ the target.
func TestUnifyUnaryChain_NonUnaryConstHead(t *testing.T) {
	defer goleak.VerifyNone(t)

	// 2-ary const — not unary, so not in the fast-path's domain.
	pair := ext.TestConst("pair", MakeFun(TypeInd, TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	d := ext.TestConst("d", TypeInd)
	f0 := Var("f0", TypeInd)

	target := pair.Apply(pair.Apply(c, d), d)
	substs := UnifyTerms(t.Context(), f0, target, utils.EmptyPredicate)

	// Huet succeeds with f0 ↦ pair(pair(c, d), d).
	assert.NotNil(t, substs)
	if len(substs) > 0 {
		got := f0.Substitute(substs[0]...)
		assertTermAlphaEqual(t, got, target)
	}
}

// TestUnifyUnaryChain_MixedConstHeads — a depth-2 chain whose inner
// and outer heads are DIFFERENT unary consts; the base case does not
// look at the heads.
func TestUnifyUnaryChain_MixedConstHeads(t *testing.T) {
	defer goleak.VerifyNone(t)

	op1 := ext.TestConst("op1", MakeFun(TypeInd, TypeInd))
	op2 := ext.TestConst("op2", MakeFun(TypeInd, TypeInd))
	c := ext.TestConst("c", TypeInd)
	f0 := Var("f0", TypeInd)

	target := op1.Apply(op2.Apply(c))
	substs := UnifyTerms(t.Context(), f0, target, utils.EmptyPredicate)

	assert.NotNil(t, substs)
	if len(substs) > 0 {
		got := f0.Substitute(substs[0]...)
		assertTermAlphaEqual(t, got, target)
	}
}

// TestUnifyUnaryChain_InsideAbstraction_CaptureAvoidanceRefuses —
// A lambda-scoped variant of the unary-chain shape:
//
//	λx. real_of_int(f0)  ≐  λx. real_of_int(op(op(x)))
//
// After makeBodyPair strips the lambda, the relevant pair is
// f0 ≐ op(op(x)) with boundVars={x}. Because args0=[] cannot abstract
// x, tryMillerPattern must decline rather than emit a substitution that
// leaks the bound variable outside its scope.
func TestUnifyUnaryChain_InsideAbstraction_CaptureAvoidanceRefuses(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd))
	rofi := ext.TestConst("real_of_int", MakeFun(TypeInd, TypeA))
	x := Var("x", TypeInd)
	f0 := Var("f0", TypeInd) // outer meta-var

	// f0 is free in the outer scope; x is bound. After
	// makeBodyPair: f0 ≐ op(op(x)) with boundVars={x}. The fast
	// path's capture-avoidance check sees x free in t1 but not in
	// args0=[] → declines. Confirms the capture-avoidance side of
	// the check works.
	s0 := x.To(rofi.Apply(f0))
	s1 := x.To(rofi.Apply(op.Apply(op.Apply(x))))

	substs := UnifyTerms(t.Context(), s0, s1, utils.EmptyPredicate)

	// Fast path declines (capture violation). Huet's path also
	// can't solve: f0 ↦ op(op(x)) would extrude bound x. No MGU.
	assert.Nil(t, substs)
}

// TestUnifyUnaryChain_AbstractedThroughArgs — the args0 ≠ [] companion:
// when f0 has args and they capture the chain's free bound vars, the
// fast path synthesizes a λ-abstracted witness. This is the args-≥1
// path Miller has always handled; we just verify it still works for
// the unary-chain shape (cross-check that our extension didn't break
// args-≥1).
//
//	λx. f0(x)  ≐  λx. op(op(x))   ⟹   f0 ↦ λx. op(op(x))
//
// (Which η-collapses to f0 ↦ op∘op, but η-collapse of a 2-step
// composition isn't a kernel reduction, so the witness stays λx-form.)
func TestUnifyUnaryChain_AbstractedThroughArgs(t *testing.T) {
	defer goleak.VerifyNone(t)

	op := ext.TestConst("op", MakeFun(TypeInd, TypeInd))
	x := Var("x", TypeInd)
	f0 := Var("f0", MakeFun(TypeInd, TypeInd))

	substs := UnifyTerms(t.Context(),
		x.To(f0.Apply(x)),
		x.To(op.Apply(op.Apply(x))),
		utils.EmptyPredicate)

	assert.NotNil(t, substs)
	if len(substs) > 0 {
		// Apply substitution and check semantic correctness:
		// after substituting and β-reducing f0(x), we should get op(op(x)).
		got := f0.Apply(x).Substitute(substs[0]...)
		assertTermAlphaEqual(t,
			ext.BetaEtaNormalize(t.Context(), got),
			op.Apply(op.Apply(x)))
	}
}
