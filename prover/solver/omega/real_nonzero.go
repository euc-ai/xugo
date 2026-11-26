package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Evidence that a real term is not zero (realProveNeqZero, real_ops.go).
//
// The field layer divides by what it can show nonzero, and the context
// states that in more forms than `¬(z = &0)`. The arith step itself rewrites
// a resident `z ≠ &0` into `&0 < z·z` (realSquarePosSimp, fired on a
// hypothesis by the step's hyp loop), after which the verbatim form is gone:
// `v ≠ &0 ⊢ v · inv v = &1` declined with its premise in plain view. And an
// ε-δ argument never has `x − c ≠ &0` at all — it has `x ≠ c`, or
// `&0 < |x − c|` from the punctured ball.
//
// A POWER is not zero where its base is not: `x ^ n` has the evidence of x
// (realPowerNonzero), whatever n is. A divisor `r ^ n` is the commonest
// one an estimate has, and its base is where the context states a sign.
//
// So the evidence is read by CONTRADICTION: assume `z = &0` and refute a
// resident fact that says some w is not zero — a disequality `¬(p = q)`, a
// square `&0 < w·w` (SquarePos backwards), a positive absolute value
// `&0 < |w|` — by proving p = q (w = &0) linearly from the assumption. The
// square of z itself is the case w = z; `x ≠ c` gives `x − c ≠ &0` this
// way, and `&0 < |x − c|` does.
//
// And a FACTOR of what the context shows nonzero is nonzero: with &0 put
// for z the two sides of a resident disequality, or of a resident strict
// comparison, are one polynomial (realEqUnderZero). `a·b ≠ &0` and
// `&0 < a·b` are each evidence for a and for b — what a divisor a·b needs
// once the inverse basis reads inv(a·b) as inv(a)·inv(b) (quotient_basis.go)
// and the unit facts cancel a factor at a time. In a field the product is
// nonzero exactly where its factors are, so the reading loses no evidence.
//
// The linear step is realLinProveSigned — the signed move-across and
// linarith, nothing that re-enters the decide chain — so the evidence search
// is one pass over the hypotheses and cannot recurse into a handler that asks
// for evidence in turn.

// realNonzeroFact is a resident fact read as `¬(p = q)`.
type realNonzeroFact struct {
	p, q  Term
	proof *prop.PropWrapper // {h} ⊢ ¬(p = q)
}

// realResidentNonzero reads h as a statement that two reals differ: a
// disequality as written, or a square `&0 < w·w` (w differs from &0). A
// positive absolute value is realNeqZeroFromAbs's.
func realResidentNonzero(h Term) (realNonzeroFact, bool) {
	if inner := ext.MatchesNOT(h); inner != nil {
		if p, q, ok := matchRealEq(inner); ok {
			return realNonzeroFact{p: p, q: q, proof: prop.Assume(h)}, true
		}
		return realNonzeroFact{}, false
	}
	l, r, ok := realDomain.matchLt(h)
	if !ok || !isRealZero(l) {
		return realNonzeroFact{}, false
	}
	if x, y, ok := realDomain.matchStar(r); ok && x.AlphaEquals(y) {
		iff := realEqLeaf(realSquarePosThm(), []Term{x}, not(eqT(x, realLit(0))), h)
		return realNonzeroFact{p: x, q: realLit(0), proof: iff.EqSym().EqMP(prop.Assume(h))}, true
	}
	return realNonzeroFact{}, false
}

// realNeqZeroByContradiction proves `{hyps} ⊢ ¬(z = &0)` by assuming z = &0
// and refuting a resident fact: a disequality whose two sides the assumption
// makes equal, or a positive absolute value whose argument it makes zero.
func realNeqZeroByContradiction(hyps []Term, z Term) *prop.PropWrapper {
	zEq0 := eqT(z, realLit(0))
	assumed := append(slices.Clone(hyps), zEq0)
	for _, h := range hyps {
		if fact, ok := realResidentNonzero(h); ok {
			eq, ok := realLinProveSigned(assumed, eqT(fact.p, fact.q)) // {hyps, z=&0} ⊢ p = q
			if !ok {
				eq, ok = realEqUnderZero(z, zEq0, fact.p, fact.q) // {z=&0} ⊢ p = q
			}
			if !ok {
				continue
			}
			contra := prop.WrapProp(prop.Contradict(eqT(fact.p, fact.q)).DeriveHypFrom(eq))
			contra = prop.WrapProp(fact.proof.MaybeDeriveTrans(contra)) // {hyps, z=&0} ⊢ ⊥
			return contra.NegHyp(zEq0)
		}
		if w := realNeqZeroFromAbs(assumed, h, zEq0); w != nil {
			return w
		}
		if w := realNeqZeroFromStrict(h, z, zEq0); w != nil {
			return w
		}
	}
	return nil
}

// realEqUnderZero proves `{z = &0} ⊢ p = q` where &0 put for z makes p and q
// one polynomial (equalWithZeroPut, the ring its prover). ok=false where z
// stands in neither side, where the two sides still differ, and where z is
// &0 itself.
func realEqUnderZero(z, zEq0, p, q Term) (*prop.PropWrapper, bool) {
	return equalWithZeroPut(z, realLit(0), zEq0, p, q, RealRingProveFull)
}

// realNeqZeroFromStrict refutes a resident strict comparison `l < r` under
// the assumption z = &0 where that makes its two sides one polynomial:
// `&0 < a·b` is evidence that a is not zero. The refutation of `l < r`
// beside `l = r` is the linear prover's.
func realNeqZeroFromStrict(h, z, zEq0 Term) *prop.PropWrapper {
	l, r, ok := realDomain.matchLt(h)
	if !ok {
		return nil
	}
	eq, ok := realEqUnderZero(z, zEq0, l, r) // {z=&0} ⊢ l = r
	if !ok {
		return nil
	}
	absurd := realLeT(realLit(1), realLit(0))
	lin, ok := RealLinProve(slices.Values([]Term{h, eqT(l, r)}), absurd) // {l<r, l=r} ⊢ &1 ≤ &0
	if !ok {
		return nil
	}
	isFalse, ok := realNormNatLe(realLit(1), realLit(0)) // ⊢ (&1 ≤ &0) ⇔ ⊥
	if !ok || !prop.Rhs(isFalse).Equals(prop.F) {
		return nil
	}
	contra := prop.WrapProp(eq.MaybeDeriveTrans(isFalse.EqMP(lin))) // {h, z=&0} ⊢ ⊥
	return contra.NegHyp(zEq0)
}

// realNeqZeroFromAbs refutes a resident `&0 < |w|` under the assumption
// z = &0: w = &0 linearly, so |w| = |&0| = &0, and the hypothesis reads
// `&0 < &0`.
func realNeqZeroFromAbs(assumed []Term, h, zEq0 Term) *prop.PropWrapper {
	l, r, ok := realDomain.matchLt(h)
	if !ok || !isRealZero(l) {
		return nil
	}
	w, ok := MatchesRealAbs(r)
	if !ok {
		return nil
	}
	wEq0, ok := realLinProveSigned(assumed, eqT(w, realLit(0))) // {hyps, z=&0} ⊢ w = &0
	if !ok {
		return nil
	}
	absOfZero := prop.DeepRewrite(realArithSimpStep)(realAbsT(realLit(0))) // ⊢ |&0| = &0
	if absOfZero == nil || !isRealZero(prop.Rhs(absOfZero)) {
		return nil
	}
	absEq := wEq0.LeftApply(realAbs).EqTrans(absOfZero)    // ⊢ |w| = &0
	cong := absEq.LeftApply(ext.Apply(realLt, realLit(0))) // ⊢ (&0 < |w|) = (&0 < &0)
	ltZero := cong.EqMP(prop.Assume(h))                    // {…, h} ⊢ &0 < &0
	ltFalse, ok := realNormNatLt(realLit(0), realLit(0))   // ⊢ (&0 < &0) ⇔ ⊥
	if !ok {
		return nil
	}
	return ltFalse.EqMP(ltZero).NegHyp(zEq0)
}

// realPowerNonzero proves `{hyps} ⊢ ¬(x ^ n = &0)` from the evidence that
// the base x is not zero: its absolute value is then positive, a power of
// a positive number is positive (PowPos), and that power is the absolute
// value of `x ^ n` (AbsPow), which `x ^ n = &0` would make zero. nil where
// x has no evidence.
func realPowerNonzero(hyps []Term, x, n Term) *prop.PropWrapper {
	baseNonzero := realProveNeqZero(hyps, x) // Γ ⊢ ¬(x = &0)
	if baseNonzero == nil {
		return nil
	}
	zero, absX, pow := realLit(0), realAbsT(x), realPowT(x, n)
	// {¬(x = &0)} ⊢ &0 < |x|: the split of the disequation and of the
	// absolute value, each arm linear.
	absPositive, ok := realProveSplit(RealLinProve, nil, []Term{baseNonzero.Conclusion()}, realLtT(zero, absX), nil)
	if !ok {
		return nil
	}
	absPositive = prop.WrapProp(baseNonzero.MaybeDeriveTrans(absPositive)) // Γ ⊢ &0 < |x|
	powAbs := realPowT(absX, n)
	powPositive := mp(realImplyLeaf(realPowPosThm(), []Term{absX, n},
		imply(realLtT(zero, absX), realLtT(zero, powAbs))), absPositive) // Γ ⊢ &0 < |x| ^ n
	absPow := realEqLeaf(realAbsPowThm(), []Term{x, n}, realAbsT(pow), powAbs)      // ⊢ |x ^ n| = |x| ^ n
	positive := absPow.EqSym().LeftApply(ext.Apply(realLt, zero)).EqMP(powPositive) // Γ ⊢ &0 < |x ^ n|
	return realNonzeroOfPositiveAbs(pow, positive)
}

// realNonzeroOfPositiveAbs is `Γ ⊢ ¬(w = &0)` from positive, `Γ ⊢ &0 < |w|`:
// w = &0 would make the absolute value `|&0|`, which is &0.
func realNonzeroOfPositiveAbs(w Term, positive *prop.PropWrapper) *prop.PropWrapper {
	isZero := eqT(w, realLit(0))
	absOfZero := prop.DeepRewrite(realArithSimpStep)(realAbsT(realLit(0))) // ⊢ |&0| = &0
	if absOfZero == nil || !isRealZero(prop.Rhs(absOfZero)) {
		return nil
	}
	absEq := prop.Assume(isZero).LeftApply(realAbs).EqTrans(absOfZero)      // {w = &0} ⊢ |w| = &0
	ltZero := absEq.LeftApply(ext.Apply(realLt, realLit(0))).EqMP(positive) // Γ, w = &0 ⊢ &0 < &0
	ltFalse, ok := realNormNatLt(realLit(0), realLit(0))                    // ⊢ (&0 < &0) ⇔ ⊥
	if !ok {
		return nil
	}
	return ltFalse.EqMP(ltZero).NegHyp(isZero)
}

// realProveZeroPower proves `{hyps} ⊢ goal` from a hypothesis that a power
// is zero: `x ^ n = &0`, in either orientation, gives `x = &0` — the
// evidence of realPowerNonzero read from the other side of the turnstile
// — and the goal is asked of the linear prover beside it. nil/false where
// no hypothesis has the shape or the linear run does not close the goal.
func realProveZeroPower(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	for _, h := range hyps {
		power, turned, ok := zeroSidedEq(h, isRealZero)
		if !ok {
			continue
		}
		x, n, ok := MatchesRealPow(power)
		if !ok {
			continue
		}
		baseZero := eqT(x, realLit(0))
		if slices.ContainsFunc(hyps, baseZero.AlphaEquals) {
			continue
		}
		baseNonzero := not(baseZero)
		powerNonzero := realPowerNonzero([]Term{baseNonzero}, x, n) // {¬(x = &0)} ⊢ ¬(x ^ n = &0)
		if powerNonzero == nil {
			continue
		}
		isZero := prop.Assume(h) // {h} ⊢ x ^ n = &0
		if turned != nil {
			isZero = turned.EqMP(isZero)
		}
		contra := prop.WrapProp(prop.Contradict(isZero.Conclusion()).DeriveHypFrom(isZero))
		contra = prop.WrapProp(powerNonzero.MaybeDeriveTrans(contra)) // {h, ¬(x = &0)} ⊢ ⊥
		// x = &0 or not; the second case is the contradiction.
		fact := prop.ByCases(baseZero, baseZero, baseNonzero).
			DeriveHypFrom(prop.ExcludedMiddle(baseZero)).
			DeriveHypFrom(prop.Assume(baseZero).PromoteHyp(baseZero)).
			DeriveHypFrom(contra.DeriveTrans(prop.FalseDerives(baseZero)).PromoteHyp(baseNonzero)) // {h} ⊢ x = &0
		if w, ok := enrichAndCut(func(e []Term) (*prop.PropWrapper, bool) {
			return RealLinProve(slices.Values(e), goal)
		}, hyps, []*prop.PropWrapper{fact}); ok {
			return w, true
		}
	}
	return nil, false
}
