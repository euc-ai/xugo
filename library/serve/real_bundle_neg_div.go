// real_bundle_neg_div.go — derivation of the six negative-divisor
// field-clearing lemmas ({Eq,LessEq,LessThan}DivMul{Left,Right}Neg) that
// no entry proves. Each is the (z<&0)⇒... twin of the corresponding (&0<z)⇒... lemma;
// the iff body is the same as its positive sibling for the `=` variants and
// is sign-flipped for `≤`/`<` (the divisor's sign flips the inequality when
// cleared).
//
// The derivations are kernel composition over a few corpus entries, so each
// output is a SOUND *prop.PropWrapper — no fabricated cert.
//
// Strategy (per variant):
// 1. Instantiate the positive-divisor sibling at (z := -z, y := -y). The result is
// `(&0 < -z) ⇒ (LHSᵢₙₛₜ ⇔ RHSᵢₙₛₜ)` whose body contains `(-y)/(-z)` and
// `x·(-z)` (and equivalents), equal modulo neg-algebra to `y/z` and
// `-(x·z)`.
// 2. Deep-rewrite under a combined reversed bridge set built from
// NegPositiveIffNegative, InvNeg, MulLeftNeg / MulRightNeg, NegNeg,
// LessEqNeg2, and the locally-derived ltNeg2 / eqNeg2,
// plus real_div's def (unfold) so `inv(-z)` becomes reachable; a second
// reversed pass over real_div's def re-folds at the end. The deep rewrite
// pushes every `−` outward and collapses double negs, then the
// relational neg-flip (leNeg2 / ltNeg2 / eqNeg2 reversed) replaces
// `-A ⋈ -B` with `B ⋈ A`.
// 3. Re-generalize `∀z x y`.
//
// The two locally-derived precursors:
// eqNeg2: ⊢ ∀a b. (a = b) = (-a = -b)
// Forward: {a=b} ⊢ -a = -b (LeftApply of real_neg = kernel congruence)
// Backward: {-a=-b} ⊢ a = b (chain ⊢ a = --a, the hyp --a = --b from
// LeftApply, and ⊢ --b = b — via NegNeg)
// Then Deduct.
// ltNeg2: ⊢ ∀x y. (x < y) = (-y < -x)
// `x < y ⇔ ¬(y ≤ x)` (NotLessEq) ⇔ `¬(-x ≤ -y)` (leNeg2 inside the ¬) ⇔
// `-y < -x` (NotLessEq at (-y,-x), reversed).

package serve

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// negDivRel selects which relational neg-flip the iff-RHS rewrite uses.
type negDivRel int

const (
	negDivEq negDivRel = iota
	negDivLe
	negDivLt
)

// negDivDeriver bundles the corpus precursors + derived bridge rewrites
// used to build all six neg-divisor lemmas. Construction is cheap (lazy
// bridge construction lives inside the precursor PropWrappers).
type negDivDeriver struct {
	negNeg *prop.PropWrapper // ⊢ ∀x. x = --x                  NegNeg
	leNeg2 *prop.PropWrapper // ⊢ ∀x y. (x≤y) ⇔ (-y ≤ -x)      real_order_ring.LessEqNeg2
	notLe  *prop.PropWrapper // ⊢ ∀x y. (x<y) ⇔ ¬(y≤x)         NotLessEq / real_lt def
	// Combined deep rewrites.
	pushDeep prop.Rewrite // unfold real_div + push every `-` outward + collapse double negs + (0<-z)→(z<0)
	flipLe   prop.Rewrite // (-y ≤ -x) → (x ≤ y)
	flipLt   prop.Rewrite // (-y < -x) → (x < y)
	flipEq   prop.Rewrite // (-x = -y) → (x = y)
	refold   prop.Rewrite // (a · inv(b)) → a/b
}

// newNegDivDeriver wires up all bridges + derives the two local
// precursors (eqNeg2, ltNeg2). The caller supplies the corpus
// precursors as PropWrappers (each one a fromEntry(...) or defNorm(...)
// from the corpus adapters).
func newNegDivDeriver(
	negPositiveIffNegative, invNeg, mulLneg, mulRneg, negNeg, leNeg2, notLessEq, divDef *prop.PropWrapper,
) *negDivDeriver {
	d := &negDivDeriver{
		negNeg: negNeg,
		leNeg2: leNeg2,
		notLe:  notLessEq,
	}
	eqNeg2 := d.deriveEqNeg2()
	ltNeg2 := d.deriveLtNeg2()
	d.pushDeep = prop.DeepRewrite(
		// Forward: unfold real_div so inv(-) can fire.
		fwdPatternRewrite(divDef),
		// Forward: inv(-x) = -inv(x) — push neg out of inv.
		fwdPatternRewrite(invNeg),
		// Reversed: (-x)·y = -(x·y) — push neg out of mul-left.
		gsymPatternRewriteLocal(mulLneg),
		// Reversed: x·(-y) = -(x·y) — push neg out of mul-right.
		gsymPatternRewriteLocal(mulRneg),
		// Reversed: --x = x — collapse double-neg.
		gsymPatternRewriteLocal(negNeg),
		// Reversed: (&0 < -x) = (x < &0) — sign condition.
		gsymPatternRewriteLocal(negPositiveIffNegative),
	)
	d.flipLe = gsymPatternRewriteLocal(leNeg2)
	d.flipLt = gsymPatternRewriteLocal(ltNeg2)
	d.flipEq = gsymPatternRewriteLocal(eqNeg2)
	d.refold = gsymPatternRewriteLocal(divDef)
	return d
}

// Local clones of omega's gsymPatternRewrite / its forward sibling so this
// file is self-contained (the omega version is unexported). The recipe
// (StripConclForAll, optional EqSym, re-Abs, UnifyEqRewrite) is the same
// shape int_lemmas.go uses for the IntOfRealThm bridges.
func gsymPatternRewriteLocal(bridge *prop.PropWrapper) prop.Rewrite {
	body, vars := bridge.StripConclForAll()
	th := body.EqSym()
	for i := len(vars) - 1; i >= 0; i-- {
		th = th.Abs(vars[i])
	}
	return prop.UnifyEqRewrite(th)
}

func fwdPatternRewrite(bridge *prop.PropWrapper) prop.Rewrite {
	body, vars := bridge.StripConclForAll()
	th := body
	for i := len(vars) - 1; i >= 0; i-- {
		th = th.Abs(vars[i])
	}
	return prop.UnifyEqRewrite(th)
}

// deriveEqNeg2 builds ⊢ ∀a b. (a = b) ⇔ (-a = -b) from NegNeg and
// kernel congruence (LeftApply of real_neg).
func (d *negDivDeriver) deriveEqNeg2() *prop.PropWrapper {
	realT := dsl.RealType
	a := ext.Var("a", realT)
	b := ext.Var("b", realT)
	realNeg := dsl.RealNegMeta.Term()
	rneg := func(t core.Term) core.Term { return ext.Apply(realNeg, t) }
	eqAB := core.Eq(a, b)
	eqNegAB := core.Eq(rneg(a), rneg(b))

	// Forward: {a=b} ⊢ -a = -b via kernel congruence (LeftApply real_neg).
	fwd := prop.Assume(eqAB).LeftApply(realNeg)
	// Backward: chain ⊢ a = --a, {-a=-b} ⊢ --a = --b, ⊢ --b = b.
	aToNNA := d.negNeg.ConclForAllInst(a)           // ⊢ a = --a
	nnBToB := d.negNeg.ConclForAllInst(b).EqSym()   // ⊢ --b = b
	assn := prop.Assume(eqNegAB).LeftApply(realNeg) // {-a=-b} ⊢ --a = --b
	bwd := aToNNA.EqTrans(assn).EqTrans(nnBToB)     // {-a=-b} ⊢ a = b
	// Deduct: ⊢ (a=b) = (-a=-b) — at bool, that IS the iff.
	iff := bwd.Deduct(fwd)
	return iff.ConclForAll(b.AssertVar()).ConclForAll(a.AssertVar())
}

// deriveLtNeg2 builds ⊢ ∀x y. (x < y) ⇔ (-y < -x) from NotLessEq (real_lt's def,
// normalized shape `∀m n. ¬(m ≤ n) ⇔ (n < m)`) and leNeg2 (normal form
// `∀m n. (m ≤ n) ⇔ (-n ≤ -m)`).
//
//	Chain: (x < y) = ¬(y ≤ x) [NotLessEq at (m:=y, n:=x), EqSym]
//	 = ¬(-x ≤ -y) [leNeg2 at (m:=y, n:=x), lifted through ¬]
//	 = -y < -x [NotLessEq at (m:=-x, n:=-y)]
func (d *negDivDeriver) deriveLtNeg2() *prop.PropWrapper {
	realT := dsl.RealType
	x := ext.Var("x", realT)
	y := ext.Var("y", realT)
	realNeg := dsl.RealNegMeta.Term()
	rneg := func(t core.Term) core.Term { return ext.Apply(realNeg, t) }

	// step1: ⊢ (x < y) = ¬(y ≤ x) — NotLessEq at (m:=y, n:=x) gives ¬(y≤x) = (x<y); EqSym.
	step1 := d.notLe.ConclForAllInst(y).ConclForAllInst(x).EqSym()
	// step2: ⊢ (y ≤ x) = (-x ≤ -y) — leNeg2 at (m:=y, n:=x).
	step2 := d.leNeg2.ConclForAllInst(y).ConclForAllInst(x)
	// Lift step2 through `¬` via kernel congruence: ⊢ ¬(y ≤ x) = ¬(-x ≤ -y).
	step2Neg := step2.LeftApply(prop.NOT)
	// step3: ⊢ ¬(-x ≤ -y) = (-y < -x) — NotLessEq at (m:=-x, n:=-y).
	step3 := d.notLe.ConclForAllInst(rneg(x)).ConclForAllInst(rneg(y))
	// Chain: (x<y) = ¬(y≤x) = ¬(-x≤-y) = (-y<-x).
	chain := step1.EqTrans(step2Neg).EqTrans(step3)
	return chain.ConclForAll(y.AssertVar()).ConclForAll(x.AssertVar())
}

// derive constructs the (z<&0)⇒... twin of `posVer` (the matching (&0<z)⇒...
// lemma) given the comparison kind. The instantiation is (z := -z, x := x,
// y := -y) for every variant; the post-rewrite flip uses flipEq / flipLe /
// flipLt.
//
// posVer is the leaf-shape `⊢ ∀z x y. (&0 < z) ⇒ (LHS(z,x,y) ⇔ RHS(z,x,y))`
// shipped by the InstallRealBundle wiring (fromGeneral off the entry proving
// the corresponding {Eq,LessEq,LessThan}DivMul{Left,Right} clause).
func (d *negDivDeriver) derive(posVer *prop.PropWrapper, rel negDivRel) *prop.PropWrapper {
	realT := dsl.RealType
	z := ext.Var("z", realT)
	x := ext.Var("x", realT)
	y := ext.Var("y", realT)
	realNeg := dsl.RealNegMeta.Term()
	rneg := func(t core.Term) core.Term { return ext.Apply(realNeg, t) }

	// Instantiate posVer at (z := -z, x := x, y := -y). posVer's binder order is
	// [z, x, y] (matching the leaf's clearShape ForAll(z, x, y)).
	specialized := posVer.ConclForAllInst(rneg(z)).ConclForAllInst(x).ConclForAllInst(rneg(y))

	// Push every neg outward + collapse double negs + unfold real_div +
	// rewrite (0 < -z) → (z < 0). UnifyEqRewrite leaves un-reduced redexes
	// (its contract — callers β-reduce); pair every bridge pass with DeepBeta
	// to keep the term β-normal so the next bridge can fire (the same
	// fixpoint pattern intOfRealForall uses).
	pushed := iterateToFixpoint(specialized, d.pushDeep)

	// Flip the `-A ⋈ -B` patterns the instantiation produces back to `B ⋈ A`.
	var flipped *prop.PropWrapper
	switch rel {
	case negDivEq:
		flipped = iterateToFixpoint(pushed, d.flipEq)
	case negDivLe:
		flipped = iterateToFixpoint(pushed, d.flipLe)
	case negDivLt:
		flipped = iterateToFixpoint(pushed, d.flipLt)
	default:
		panic("negDivDeriver.derive: unknown rel")
	}

	// Re-fold `a · inv(b)` back to `a/b`.
	refolded := iterateToFixpoint(flipped, d.refold)

	// ∀-re-generalize, outer→inner: z, x, y.
	return refolded.ConclForAll(y.AssertVar()).ConclForAll(x.AssertVar()).ConclForAll(z.AssertVar())
}

// iterateToFixpoint applies (rewrite ; DeepBeta) to the conclusion until
// nothing changes. Mirrors intOfRealForall's loop (prover/solver/omega/
// int_lemmas.go): UnifyEqRewrite leaves un-reduced `(λvars.L)(args)`
// redexes that block subsequent bridge matches, so we β-reduce between
// passes. Both steps strictly shrink (fewer matching subterms / fewer
// redexes), so termination is guaranteed.
func iterateToFixpoint(t *prop.PropWrapper, r prop.Rewrite) *prop.PropWrapper {
	for {
		before := t.Conclusion()
		t = t.RewriteConcl(r).RewriteConcl(prop.DeepBeta)
		if t.Conclusion().AlphaEquals(before) {
			return t
		}
	}
}
