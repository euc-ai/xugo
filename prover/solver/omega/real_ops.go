package omega

import (
	"github.com/euc-ai/xugo/core"
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Real case-split engine — the ℝ twin of the int case split (int_split.go),
// itself the twin of the num nat_max/nat_min handler (nat_sub.go).
//
// `real_abs x = COND(&0 ≤ x, x, −x)` (AbsDef), `real_max`/`real_min`
// (`COND(a ≤ b, …)`), and `real_sgn` (a nested COND) are piecewise-linear by a
// comparison guard, exactly the shape a proof-producing excluded middle
// elimination reduces to a closed `+`-form per branch — and a `−x` branch then
// flows through the real signed normalizer (subneg.go, the shared int/real
// seam) into the positive-linear decider.
//
// The reusable pieces (splittableAtom / splitBranch / enrichAndCut /
// collectRawSubterms / prop.ByCases / prop.ExcludedMiddle) are SHARED with the
// num and int engines; only the recognizers (real_abs/max/min/sgn), the real
// comparison vocabulary (realNegComparison), and the COND collapser (realCondPin,
// over the real decider) are real-specific.
//
// Full int mirror — the hypothesis splits are `p∨q`, the `≠` trichotomy
// (LessThanTrichotomy), the implication `p⇒q`, and the product-zero split (MulEqZero).
// Every leaf binds a corpus theorem (serve.InstallRealBundle).

// realProveSplit is the real case split (realFirstSplittable) with the given
// provers — caseSplit (engine.go) holds the recursion: prove at every branch,
// a further split, and leaf where nothing is left to split.
func realProveSplit(prove, leaf proveFn, hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return caseSplit{domain: realDomain, first: realFirstSplittable, prove: prove, leaf: leaf}.split(hyps, goal, done)
}

// realProveLeaf is the real split's leaf prover: the handlers of the decide
// chain that read the hypotheses and prove without re-entering it — the
// sign-known nonlinear fragment, the cancellation and the products pass. A
// branch's pin `s = &1` reaches `s·s = &1` here; the linear prover alone
// reads s·s as an unknown.
func realProveLeaf(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	for _, handler := range []func([]Term, Term) (*prop.PropWrapper, bool){
		realProveMonotone, realProvePowSign, realProvePowBaseMono, realProvePowExpMono,
		realProveAbsTriangle, realProveStrictSquare, realProveMulEqZeroSquare, realProveZeroPower,
		realProveCancelMul, realProveProducts,
	} {
		if w, ok := handler(hs, goal); ok {
			return w, true
		}
	}
	return nil, false
}

// realFirstSplittable returns the first real splittable atom of hyps∪{goal} not
// already split (in `done`), mirroring intFirstSplittable's two families: a
// HYPOTHESIS-based split (realHypSplittable: `p∨q` / `p⇒q` / product-zero), and a
// TAUTOLOGY-based split (realSplittableKinds: an opaque operator anywhere
// BINDER-FREE in hyps∪{goal} — see collectBinderFreeSubterms: an operator
// term mentioning a variable bound by an enclosing ∀/∃/λ pins nothing any
// constraint row can meet, so its split only spends a level).
func realFirstSplittable(hyps []Term, goal Term, done []Term) (splittableAtom, bool) {
	for _, h := range hyps {
		if slices.ContainsFunc(done, h.AlphaEquals) {
			continue
		}
		if sa, ok := realHypSplittable(h); ok {
			return sa, true
		}
	}
	for _, t := range collectBinderFreeSubterms(append(slices.Clone(hyps), goal), isRealSplitCandidate) {
		if slices.ContainsFunc(done, t.AlphaEquals) {
			continue
		}
		for _, kind := range realSplittableKinds() {
			if sa, ok := kind(t); ok {
				return sa, true
			}
		}
	}
	return splittableAtom{}, false
}

// realSplittableKinds: the tautology-split recognizers (mirror intSplittableKinds).
// A function (not a var) to avoid a static-init cycle (the kinds reach
// realProveSplit, which reads this list).
func realSplittableKinds() []func(Term) (splittableAtom, bool) {
	return []func(Term) (splittableAtom, bool){
		realAbsSplittable, realMaxSplittable, realMinSplittable, realSgnSplittable, realCondSplittable,
	}
}

// isRealSplitCandidate reports whether t is an opaque real operator some tautology
// kind might split (the cheap pre-filter for collectRawSubterms; mirror of
// isIntSplitCandidate).
func isRealSplitCandidate(t Term) bool {
	if _, ok := MatchesRealAbs(t); ok {
		return true
	}
	if _, _, ok := MatchesRealMax(t); ok {
		return true
	}
	if _, _, ok := MatchesRealMin(t); ok {
		return true
	}
	if _, ok := MatchesRealSgn(t); ok {
		return true
	}
	if _, _, _, ok := ext.MatchesCond(t); ok && isRealTerm(t) {
		return true
	}
	return false
}

// realAbsSplittable is the real_abs kind: split `real_abs x` on excluded middle of
// its def guard `&0 ≤ x`, pinning real_abs x to x (resp. −x) per branch via AbsDef.
func realAbsSplittable(m Term) (splittableAtom, bool) {
	x, ok := MatchesRealAbs(m)
	if !ok {
		return splittableAtom{}, false
	}
	return realCondSplit(m, realAbsDef(x), realLeT(realLit(0), x))
}

// realMaxSplittable / realMinSplittable: split on the def guard `a ≤ b`, pinning
// the operator to b/a (resp. a/b). The real twins of intMaxSplittable/intMinSplittable.
func realMaxSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesRealMax(m)
	if !ok {
		return splittableAtom{}, false
	}
	return realCondSplit(m, realMaxDef(a, b), realLeT(a, b))
}

func realMinSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesRealMin(m)
	if !ok {
		return splittableAtom{}, false
	}
	return realCondSplit(m, realMinDef(a, b), realLeT(a, b))
}

// realSgnSplittable is the real_sgn kind: split the OUTER guard `&0 < x` of the
// nested def; the else-branch pins real_sgn x to the inner COND `COND(x<&0,−&1,&0)`,
// which the raw-COND kind (realCondSplittable) then splits in the recursion.
func realSgnSplittable(m Term) (splittableAtom, bool) {
	x, ok := MatchesRealSgn(m)
	if !ok {
		return splittableAtom{}, false
	}
	return realCondSplit(m, realSgnDef(x), realLtT(realLit(0), x))
}

// realCondSplittable is the raw-COND kind: a real-typed `COND(guard, x, y)` whose
// guard is a `<`/`≤` comparison the linear core can't decide is split on
// excluded middle of the guard, each arm pinned by the reflexive def. Catches a
// bare real conditional and the inner COND of real_sgn (mirror of intCondSplittable).
// A guard of any other shape is split by its atoms (compoundCondSplit).
func realCondSplittable(c Term) (splittableAtom, bool) {
	guard, _, _, ok := ext.MatchesCond(c)
	if !ok || !isRealTerm(c) {
		return splittableAtom{}, false
	}
	if realDomain.isOrderAtom(guard) {
		return realCondSplit(c, prop.Refl(c), guard)
	}
	return compoundCondSplit(c, prop.Refl(c), guard, realNegComparison)
}

// ── Hypothesis-based splits (mirror intHypSplittable) ─────────────────────────

// realHypSplittable recognizes a HYPOTHESIS whose structure the linear core cannot
// use directly but a case split can: a disjunction `p∨q`, a real `≠`, a real
// implication `p⇒q`, a product-zero `a·b=&0` (MulEqZero), or a quotient-zero
// `a/b=&0`. The split is sound
// because h is a real hyp. Returns ok=false for any other shape. Mirror of
// intHypSplittable.
func realHypSplittable(h Term) (splittableAtom, bool) {
	// Disjunctive hyp `p ∨ q`: split, feeding each disjunct. No lemma — the
	// disjunction proof is the hyp itself.
	if p, q, ok := prop.MatchesOR(h); ok {
		return splittableAtom{
			atom:      h,
			disjProof: prop.Assume(h), // {p∨q} ⊢ p∨q
			branches: [2]splitBranch{
				{guard: p, facts: []*prop.PropWrapper{prop.Assume(p)}},
				{guard: q, facts: []*prop.PropWrapper{prop.Assume(q)}},
			},
		}, true
	}
	// real `≠` hyp `¬(a=b)`: a<b ∨ b<a (LessThanTrichotomy with the `a=b` disjunct killed
	// under the hyp). The complementary comparisons feed the linear core.
	if inner := ext.MatchesNOT(h); inner != nil {
		if a, b, ok := ext.MatchesEQ(inner); ok && isRealTerm(a) {
			tri := realTrichotomyNeq(a, b)
			if tri == nil {
				return splittableAtom{}, false // LessThanTrichotomy unbundled — decline.
			}
			return splittableAtom{
				atom:      h,
				disjProof: tri, // {¬(a=b)} ⊢ (a<b) ∨ (b<a)
				branches: [2]splitBranch{
					{guard: realLtT(a, b), facts: []*prop.PropWrapper{prop.Assume(realLtT(a, b))}},
					{guard: realLtT(b, a), facts: []*prop.PropWrapper{prop.Assume(realLtT(b, a))}},
				},
			}, true
		}
	}
	// Implication hyp `p ⇒ q` (classically ¬p ∨ q): the ¬p branch bridges to the
	// complementary positive comparison (NotLessThan/NotLessEq) when p is a `<`/`≤` atom.
	if p, q, ok := prop.MatchesIMPLY(h); ok {
		np := not(p)
		b0 := []*prop.PropWrapper{prop.Assume(np)}
		if _, bridge, ok := realNegComparison(p); ok {
			b0 = append(b0, bridge) // {¬p} ⊢ the linear-usable complementary comparison
		}
		return splittableAtom{
			atom:      h,
			disjProof: prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](p, q).EqMP(prop.Assume(h)), // {p⇒q} ⊢ ¬p ∨ q
			branches: [2]splitBranch{
				{guard: np, facts: b0},
				{guard: q, facts: []*prop.PropWrapper{prop.Assume(q)}},
			},
		}, true
	}
	// real product `a·b = &0` hyp with DISTINCT factors: a=&0 ∨ b=&0 (MulEqZero —
	// ℝ is a field, hence an integral domain). Each disjunct pins a factor, closing
	// e.g. `x·y=&0,x≠&0 ⊢ y=&0`. The square case a==b (`x·x=&0`) collapses to a
	// single guard, a fact and no case, so it is handled forward instead
	// (realProveMulEqZeroSquare).
	if a, b, ok := realProductZeroEq(h); ok && !a.AlphaEquals(b) {
		za, zb := eqT(a, realLit(0)), eqT(b, realLit(0))
		return splittableAtom{
			atom:      h,
			disjProof: realMulEqZeroDisj(h, a, b), // {a·b=&0} ⊢ (a=&0) ∨ (b=&0)
			branches: [2]splitBranch{
				{guard: za, facts: []*prop.PropWrapper{prop.Assume(za)}},
				{guard: zb, facts: []*prop.PropWrapper{prop.Assume(zb)}},
			},
		}, true
	}
	// real quotient `a / b = &0` hyp, the zero on either side: a=&0 ∨ b=&0.
	// The quotient is the product a·inv b, and inv b is zero exactly where
	// b is (realQuotientZeroDisj).
	if q, turned, ok := zeroSidedEq(h, isRealZero); ok {
		if a, b, ok := MatchesRealDiv(q); ok {
			quotient := prop.Assume(h) // {h} ⊢ a / b = &0
			if turned != nil {
				quotient = turned.EqMP(quotient)
			}
			za, zb := eqT(a, realLit(0)), eqT(b, realLit(0))
			return splittableAtom{
				atom:      h,
				disjProof: realQuotientZeroDisj(quotient, a, b), // {h} ⊢ (a=&0) ∨ (b=&0)
				branches: [2]splitBranch{
					{guard: za, facts: []*prop.PropWrapper{prop.Assume(za)}},
					{guard: zb, facts: []*prop.PropWrapper{prop.Assume(zb)}},
				},
			}, true
		}
	}
	return splittableAtom{}, false
}

// realQuotientZeroDisj derives `Γ ⊢ (a=&0) ∨ (b=&0)` from quotient,
// `Γ ⊢ a / b = &0`: the quotient unfolds to a·inv b (DivDef), a zero product
// (MulEqZero), and `inv b = &0` reads `b = &0` (InvEqZero).
func realQuotientZeroDisj(quotient *prop.PropWrapper, a, b Term) *prop.PropWrapper {
	invB := realInvT(b)
	product := realQuotientUnfold(a, b).EqSym().EqTrans(quotient) // Γ ⊢ a·inv b = &0
	za := eqT(a, realLit(0))
	factors := realEqLeaf(realMulEqZeroThm(), []Term{a, invB},
		eqT(realLit(0), realStarT(a, invB)), or(za, eqT(invB, realLit(0)))).EqMP(product.EqSym()) // Γ ⊢ (a=&0) ∨ (inv b=&0)
	invZero := realEqLeaf(realInvEqZeroThm(), []Term{b}, eqT(invB, realLit(0)), eqT(b, realLit(0)))
	return invZero.LeftApply(ext.Apply(prop.OR, za)).EqMP(factors)
}

// realProductZeroEq matches a hyp `a·b = &0` / `&0 = a·b` (a genuine real product
// equal to zero), returning its two factors — the MulEqZero-splittable shape
// (mirror of intProductZeroEq).
func realProductZeroEq(h Term) (a, b Term, ok bool) {
	l, r, eok := ext.MatchesEQ(h)
	if !eok || !isRealTerm(l) {
		return nil, nil, false
	}
	if isRealZero(r) {
		if x, y, mok := realDomain.matchStar(l); mok {
			return x, y, true
		}
	}
	if isRealZero(l) {
		if x, y, mok := realDomain.matchStar(r); mok {
			return x, y, true
		}
	}
	return nil, nil, false
}

// realMulEqZeroDisj derives `{h} ⊢ (a=&0) ∨ (b=&0)` from MulEqZero
// (`(&0 = a·b) ⇔ (a=&0 ∨ b=&0)`), where h is the product-zero hyp in either
// orientation. The bound form orients the equation zero-on-LEFT (`&0 = a·b`), so the
// hyp `a·b = &0` is flipped to that before the EqMP (the orientation difference
// from intMulEqZeroDisj, whose MulEqZero is fabricated zero-on-right in tests).
func realMulEqZeroDisj(h, a, b Term) *prop.PropWrapper {
	prodEq0 := eqT(realLit(0), realStarT(a, b)) // &0 = a·b (MulEqZero's LHS orientation)
	hProof := prop.Assume(h)                    // {h} ⊢ h
	if !h.AlphaEquals(prodEq0) {
		hProof = hProof.EqSym() // h is `a·b = &0` → {h} ⊢ &0 = a·b
	}
	iff := realEqLeaf(realMulEqZeroThm(), []Term{a, b}, prodEq0,
		or(eqT(a, realLit(0)), eqT(b, realLit(0)))) // ⊢ (&0=a·b) ⇔ (a=&0 ∨ b=&0)
	return iff.EqMP(hProof) // {h} ⊢ (a=&0) ∨ (b=&0)
}

// realTrichotomyNeq derives `{¬(a=b)} ⊢ (a<b) ∨ (b<a)` from LessThanTrichotomy
// (`((a<b) ∨ (b<a)) ∨ (a=b)`): disjSyllogism removes the `a=b` disjunct (on the
// RIGHT) under the `¬(a=b)` hyp. Mirror of intTrichotomyNeq.
func realTrichotomyNeq(a, b Term) *prop.PropWrapper {
	ltc := realLessThanTrichotomy(a, b) // ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)
	return disjSyllogism(ltc, prop.Assume(not(eqT(a, b))))
}

// realLessThanTrichotomy: ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)   (LessThanTrichotomy). The trichotomy source
// the `≠`-hyp split and strict-square handler consume. Mirror of intLessThanTrichotomy.
func realLessThanTrichotomy(a, b Term) *prop.PropWrapper {
	return realImplyLeaf(realLessThanTrichotomyThm(), []Term{a, b},
		or(or(realLtT(a, b), realLtT(b, a)), eqT(a, b)))
}

// realCondSplit builds the excluded middle split of a real atom whose value is
// piecewise by a comparison `guard`, given `def : ⊢ atom = COND(guard, x, y)`
// (mirror of intCondSplit / condSplit):
//
//	guard ∨ ¬guard                          [excluded middle]
//	guard  branch:  pin atom = x            [COND collapses under guard]
//	¬guard branch:  pin atom = y            [COND collapses under ¬guard's positive form]
//
// The ¬guard branch bridges to the complementary positive comparison
// (realNegComparison via NotLessThan / NotLessEq) so the real prover can both
// consume it and let the COND fold. ok=false when the guard is not a `<`/`≤`
// comparison or a pin fails to fold.
func realCondSplit(atom Term, def *prop.PropWrapper, guard Term) (splittableAtom, bool) {
	_, negBridge, ok := realNegComparison(guard)
	if !ok {
		return splittableAtom{}, false // guard not a `<`/`≤` comparison.
	}
	pinT := realCondPin(def, eqtIntro(prop.Assume(guard)))              // {guard} ⊢ atom = x
	pinFraw := realCondPin(def, eqfIntro(realComplementNegates(guard))) // {negPos} ⊢ atom = y
	if pinT == nil || pinFraw == nil {
		return splittableAtom{}, false
	}
	pinF := prop.WrapProp(negBridge.MaybeDeriveTrans(pinFraw)) // {¬guard} ⊢ atom = y
	return splittableAtom{
		atom:      atom,
		disjProof: prop.ExcludedMiddle(guard), // guard ∨ ¬guard
		branches: [2]splitBranch{
			{guard: guard, facts: []*prop.PropWrapper{prop.Assume(guard), pinT}},
			{guard: not(guard), facts: []*prop.PropWrapper{negBridge, pinF}},
		},
	}, true
}

// (realNegComparison — the `<`/`≤` → complementary-positive bridge via
// NotLessThan/NotLessEq — already lives in real.go; the COND split reuses it.)

// realCondPin collapses the COND on the RHS of `def` under a branch guard,
// returning `{guardHyp} ⊢ (def.lhs) = <branch value>`. guardIff is the
// guard's truth value in the branch — `{guard} ⊢ guard ⇔ ⊤` or
// `{negPos} ⊢ guard ⇔ ⊥` — and the guard IS the COND's condition (every def
// here is built with it: realAbsDef / realMaxDef / realMinDef / realSgnDef,
// and realCondSplittable reads it off the COND), so the collapse is one
// syntactic fold: the guard position rewrites to its truth value and
// trivialCondRewrite selects the branch. No decider runs. The int/nat twins
// (intCondPin / condPin) still fold through their full deep rewrite with the
// guard as a hypothesis — the same theorem, reached by an atom decision (a
// hyp echo for ⊤, a one-hypothesis linarith run for ⊥) plus the value simp
// leaves. Here the value is left as the def wrote it: it is a subterm of a
// hypothesis or goal the decider had already simplified when the split
// candidate was collected, so those leaves had nothing left to fold, and a
// leaf that could rewrite the guard's own subterms before the fold matched
// would cost the pin. On a wide real context the deep rewrite per pin —
// built for both branches at every split level of every linarith run — was
// 9% of an `arith` pass. nil when the fold does not fire.
func realCondPin(def, guardIff *prop.PropWrapper) *prop.PropWrapper {
	return pinUnder(def, guardIff)
}

// realComplementNegates: `{negPos} ⊢ ¬guard` for a `<`/`≤` guard, negPos its
// complementary positive comparison — the converse of realNegComparison's
// bridge (NotLessThan / NotLessEq read right to left), the ⊥ half of a
// branch guard's truth value. nil when the guard is not a `<`/`≤` comparison.
func realComplementNegates(guard Term) *prop.PropWrapper {
	if u, v, ok := realDomain.matchLt(guard); ok { // {v≤u} ⊢ ¬(u<v)
		return realNotLT(u, v).EqSym().EqMP(prop.Assume(realLeT(v, u)))
	}
	if u, v, ok := realDomain.matchLe(guard); ok { // {v<u} ⊢ ¬(u≤v)
		return realNotLE(u, v).EqSym().EqMP(prop.Assume(realLtT(v, u)))
	}
	return nil
}

// ── Piecewise operator definitions (mirror int_lemmas.go's intAbsBySign family) ──

// realAbsDef: ⊢ real_abs x = COND(&0 ≤ x, x, −x)   (AbsDef)
func realAbsDef(x Term) *prop.PropWrapper {
	return realEqLeaf(realAbsDefThm(), []Term{x},
		realAbsT(x), ext.Cond(realLeT(realLit(0), x), x, realNegT(x)))
}

// realMaxDef: ⊢ real_max a b = COND(a ≤ b, b, a)   (real_max def)
func realMaxDef(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realMaxDefThm(), []Term{a, b}, realMaxT(a, b), ext.Cond(realLeT(a, b), b, a))
}

// realMinDef: ⊢ real_min a b = COND(a ≤ b, a, b)   (real_min def)
func realMinDef(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realMinDefThm(), []Term{a, b}, realMinT(a, b), ext.Cond(realLeT(a, b), a, b))
}

// realSgnDef: ⊢ real_sgn x = COND(&0 < x, &1, COND(x < &0, −&1, &0))   (real_sgn def)
func realSgnDef(x Term) *prop.PropWrapper {
	inner := ext.Cond(realLtT(x, realLit(0)), realNegT(realLit(1)), realLit(0))
	return realEqLeaf(realSgnDefThm(), []Term{x}, realSgnT(x), ext.Cond(realLtT(realLit(0), x), realLit(1), inner))
}

// Monotone scaling, sign-of-product, and the integral domain over ℝ — the real
// twin of the int sign-known nonlinear fragment (int.go). These are genuinely
// nonlinear but NOT full RCF: the inputs are sign/order facts, the output is a
// lemma instantiation. The side conditions discharge through the LINEAR forward
// prover (realLinProveSigned = RealLinProve + one move-across pass, so a negated
// goal like `&0 ≤ −x` positivizes) — never the full decider, which could recurse.
//
// Out of this cut: the genuine RCF `a≤b ⊢ a²≤b²` (no sign assumption on the
// factors), and the strict two-sided product bound.

// realProveMonotone tries `{hyps} ⊢ goal` for a `≤` / `<` goal whose sides are
// products (monotone scaling) or whose RHS/LHS is a product compared to &0
// (sign-of-product). nil/false when the goal is not such a shape or a side
// condition does not discharge. Mirror of intProveMonotone.
func realProveMonotone(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := realDomain.matchLe(goal); ok {
		return realMonotoneAtom(hyps, l, r, false)
	}
	if l, r, ok := realDomain.matchLt(goal); ok {
		return realMonotoneAtom(hyps, l, r, true)
	}
	return nil, false
}

// realMonotoneAtom dispatches the (l ⋈ r) atom (strict selects </≤). Mirror of
// intMonotoneAtom.
func realMonotoneAtom(hyps []Term, l, r Term, strict bool) (*prop.PropWrapper, bool) {
	// sign-of-product: &0 ⋈ x·y (nonneg/pos target) or x·y ⋈ &0 (nonpos/neg target).
	if isRealZero(l) {
		if x, y, ok := realDomain.matchStar(r); ok {
			if w, ok := realProveSignedProduct(hyps, x, y, true, strict); ok {
				return w, true
			}
		}
	}
	if isRealZero(r) {
		if x, y, ok := realDomain.matchStar(l); ok {
			if w, ok := realProveSignedProduct(hyps, x, y, false, strict); ok {
				return w, true
			}
		}
	}
	// monotone scaling: l, r both products sharing a factor — or one side a
	// product and the other its bare factor, read as that factor times &1.
	la, ra, okL := realDomain.matchStar(l)
	lb, rb, okR := realDomain.matchStar(r)
	switch {
	case okL && !okR:
		return realMonoScaleOne(hyps, la, ra, r, strict, true)
	case !okL && okR:
		return realMonoScaleOne(hyps, lb, rb, l, strict, false)
	case !okL && !okR:
		return nil, false
	}
	if la.AlphaEquals(lb) { // x·a ⋈ x·b — scale by the shared LEFT factor x = la.
		return realMonoScaleLeft(hyps, la, ra, rb, strict)
	}
	if ra.AlphaEquals(rb) { // a·x ⋈ b·x — scale by the shared RIGHT factor x = ra.
		return realMonoScaleRight(hyps, ra, la, lb, strict)
	}
	// two-sided a·c ≤ b·d (distinct factors), non-strict (derived).
	if !strict {
		return realProveProductMul2(hyps, la, ra, lb, rb)
	}
	return nil, false
}

// realMonoScaleLeft proves `{hyps} ⊢ c·a ⋈ c·b` from `&0 ⋈′ c` and `a ⋈ b`
// (both discharged by RealLinProve) via LessEqMulLeft / LessThanMulLeft. nil/false when
// either side condition fails. Mirror of intMonoScaleLeft.
func realMonoScaleLeft(hyps []Term, c, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	rel, thm := realLeT, realLessEqMulLeftThm()
	if strict {
		rel, thm = realLtT, realLessThanMulLeftThm()
	}
	sideRel := rel(realLit(0), c) // &0 ⋈ c
	side, ok := RealLinProve(slices.Values(hyps), sideRel)
	if !ok {
		return nil, false
	}
	relAB, ok := RealLinProve(slices.Values(hyps), rel(a, b)) // a ⋈ b
	if !ok {
		return nil, false
	}
	// LessEqMulLeft/LessThanMulLeft: ∀c a b. (&0 ⋈ c) ⇒ (a ⋈ b) ⇒ (c·a ⋈ c·b)
	// (binder [c, a, b], the realScale order).
	imp := realImplyLeaf(thm, []Term{c, a, b},
		imply(sideRel, imply(rel(a, b), rel(realStarT(c, a), realStarT(c, b)))))
	return mp(mp(imp, side), relAB), true // ⊢ c·a ⋈ c·b
}

// realMulOne: ⊢ a · &1 = a — MulSym then MulLeftId, so no right-identity
// bundle field is needed.
func realMulOne(a Term) *prop.PropWrapper {
	return realCommuteMUL(a, realLit(1)).EqTrans(realOneMul(a))
}

// realMonoScaleOne proves the monotone scaling whose bare side is the shared
// factor itself: `x·a ⋈ x`, `a·x ⋈ x` (productOnLeft) or `x ⋈ x·b`, `x ⋈ b·x`.
// The bare side is the factor times &1 — `η·η ≤ η` from `&0 < η` and `η ≤ &1` —
// so the goal is the scaling with &1 in the empty slot (realMonoScaleLeft /
// realMonoScaleRight), and the `x·&1` (or `&1·x`) that scaling proves is read
// back as x through the multiplicative identity. left and right are the
// product side's two factors, bare the other side; nil/false when the bare
// side is not one of the factors or a side condition fails. Mirror of
// intMonoScaleOne.
func realMonoScaleOne(hyps []Term, left, right, bare Term, strict, productOnLeft bool) (*prop.PropWrapper, bool) {
	one := realLit(1)
	var factor, other Term
	var scaleRight bool
	switch {
	case left.AlphaEquals(bare): // x·a beside x: scale by the LEFT factor
		factor, other, scaleRight = left, right, false
	case right.AlphaEquals(bare): // a·x beside x: scale by the RIGHT factor
		factor, other, scaleRight = right, left, true
	default:
		return nil, false
	}
	// The scaled comparison, with &1 where the bare side stood.
	a, b := other, one
	if !productOnLeft {
		a, b = one, other
	}
	var scaled *prop.PropWrapper
	var ok bool
	if scaleRight {
		scaled, ok = realMonoScaleRight(hyps, factor, a, b, strict) // ⊢ a·x ⋈ b·x
	} else {
		scaled, ok = realMonoScaleLeft(hyps, factor, a, b, strict) // ⊢ x·a ⋈ x·b
	}
	if !ok {
		return nil, false
	}
	// Read the &1 slot back as the bare factor: (P ⋈ x·&1) = (P ⋈ x) or
	// (x·&1 ⋈ P) = (x ⋈ P), the identity applied under the relation.
	relC := realLe
	if strict {
		relC = realLt
	}
	identity := realMulOne(factor) // ⊢ x·&1 = x
	product := realStarT(factor, other)
	if scaleRight {
		identity = realOneMul(factor) // ⊢ &1·x = x
		product = realStarT(other, factor)
	}
	var cong *prop.PropWrapper
	if productOnLeft {
		cong = identity.LeftApply(ext.Apply(relC, product)) // (product ⋈ x·&1) = (product ⋈ x)
	} else {
		cong = identity.LeftApply(relC).RightApply(product) // (x·&1 ⋈ product) = (x ⋈ product)
	}
	return cong.EqMP(scaled), true
}

// realMonoScaleRight proves `{hyps} ⊢ a·c ⋈ b·c` by scaling on the LEFT (c·a ⋈ c·b)
// and commuting both sides back (realCommuteMUL), so no right-factor leaf is needed.
// Mirror of intMonoScaleRight.
func realMonoScaleRight(hyps []Term, c, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	caCb, ok := realMonoScaleLeft(hyps, c, a, b, strict) // ⊢ c·a ⋈ c·b
	if !ok {
		return nil, false
	}
	relC := realLe
	if strict {
		relC = realLt
	}
	cb, ac := realStarT(c, b), realStarT(a, c)
	// (c·a ⋈ c·b) = (a·c ⋈ b·c): commute the LEFT side, then the RIGHT side.
	cong := realCommuteMUL(c, a).LeftApply(relC).RightApply(cb). // (c·a⋈c·b) = (a·c⋈c·b)
									EqTrans(realCommuteMUL(c, b).LeftApply(ext.Apply(relC, ac))) // = (a·c⋈b·c)
	return cong.EqMP(caCb), true // ⊢ a·c ⋈ b·c
}

// realLinProveSigned proves `{hyps} ⊢ goal` where goal may carry top-level
// subtraction/negation, by first trying plain linarith and, failing that, ONE
// moveAcrossCmp pass to positivize the goal before re-running linarith. It does NOT
// re-enter the monotone/decide handlers (move-across + RealLinProve only), so it is
// safe to call from realProveSignedProduct's side conditions (e.g. `&0 ≤ −x`, whose
// neg the plain RealLinProve goal-side does not see). Mirror of intLinProveSigned.
//
// Also threads realProveAbsNonneg so a sign-of-product side condition `&0 ≤ |t|`
// — opaque to linarith (abs is not a linear atom) — closes directly via
// AbsNonneg. This lets `&0 ≤ |x|·|y|` (after realAbsSgnSimp folds |x·y|)
// reach the both-positive sign-of-product clause without falling into the
// 4-way abs case split.
func realLinProveSigned(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if pf, ok := RealLinProve(slices.Values(hyps), goal); ok {
		return pf, true
	}
	if pf, ok := realProveAbsNonneg(goal); ok {
		return pf, true
	}
	mac := realSubneg.moveAcrossCmp(goal) // ⊢ goal ⇔ positive
	if mac == nil {
		return nil, false
	}
	pf, ok := RealLinProve(slices.Values(hyps), prop.Rhs(mac))
	if !ok {
		return nil, false
	}
	return mac.EqSym().EqMP(pf), true // ⊢ goal
}

// realMulPosLemma proves `{hyps} ⊢ &0 ⋈ a·b` from `&0 ⋈ a` and `&0 ⋈ b` via
// LessEqMul (⋈ = ≤) / MulPos (⋈ = <). The two side conditions
// discharge through realLinProveSigned, so a NEGATED operand `−x` (used by the
// sign-mixed reductions) positivizes. nil/false when a side condition fails. Mirror
// of intMulPosLemma.
func realMulPosLemma(hyps []Term, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	relT, thm := realLeT, realLessEqMulThm()
	if strict {
		relT, thm = realLtT, realMulPosThm()
	}
	a0, ok := realProveFactorSign(hyps, a, strict)
	if !ok {
		return nil, false
	}
	b0, ok := realProveFactorSign(hyps, b, strict)
	if !ok {
		return nil, false
	}
	imp := realImplyLeaf(thm, []Term{a, b},
		imply(relT(realLit(0), a), imply(relT(realLit(0), b), relT(realLit(0), realStarT(a, b)))))
	return mp(mp(imp, a0), b0), true // ⊢ &0 ⋈ a·b
}

// realProveFactorSign discharges a sign-of-product side condition `&0 ⋈ f`
// for one factor f: linarith over the resident facts first (through the
// signed move-across and the abs leaf), and when f is itself a product, the
// sign-of-product handler on ITS factors — so `&0 < &2·(a·b)` closes from
// `&0 < a` and `&0 < b` the way `&0 < a·b` does, the recursion descending
// the product tree (each call strictly on a subterm).
//
// An INVERSE factor descends the same way: the sign of `inv x` is the sign
// of x (InvPos / InvNonneg — the iffs realInvSignSimp already
// applies to a resident atom), so `&0 ⋈ inv x` is proved about x and lifted
// through the iff. This is the direction the hyp pre-simp leaves open:
// it rewrites a resident `&0 ⋈ inv x` INTO `&0 ⋈ x`, after which nothing
// in the context spells the factor's own sign, and a product `a · inv x`
// declined with its argument's sign sitting in plain view (measured on
// `&0 ≤ a, &0 < inv t ⊢ &0 ≤ a · inv t`; the variable-only twin closed).
func realProveFactorSign(hyps []Term, f Term, strict bool) (*prop.PropWrapper, bool) {
	relT := realLeT
	if strict {
		relT = realLtT
	}
	if w, ok := realLinProveSigned(hyps, relT(realLit(0), f)); ok {
		return w, true
	}
	if p, q, ok := realDomain.matchStar(f); ok {
		return realProveSignedProduct(hyps, p, q, true, strict)
	}
	if x, ok := MatchesRealInv(f); ok {
		w, ok := realProveFactorSign(hyps, x, strict)
		if !ok {
			return nil, false
		}
		thm := realInvNonnegThm()
		if strict {
			thm = realInvPosThm()
		}
		// ⊢ (&0 ⋈ inv x) = (&0 ⋈ x); the recursion proved the right side.
		iff := realEqLeaf(thm, []Term{x}, relT(realLit(0), f), relT(realLit(0), x))
		return iff.EqSym().EqMP(w), true
	}
	return nil, false
}

// realProveSignedProduct proves a product's sign from its factors' signs — the
// sign-known nonlinear fragment (NOT full RCF). wantNonneg selects the target:
//
//	wantNonneg:  `&0 ⋈ x·y`  from (&0⋈x ∧ &0⋈y) OR (x⋈&0 ∧ y⋈&0);
//	!wantNonneg: `x·y ⋈ &0`  from (x⋈&0 ∧ &0⋈y) OR (&0⋈x ∧ y⋈&0).
//
// The negated-factor combos reduce to realMulPosLemma on `(−·)` operands, then push
// the negation out with negNegMul / negLmul / mulRightNeg; the nonpositive target then
// flips `&0 ⋈ −(x·y)` to `x·y ⋈ &0` (realFlipNeg). nil/false when no sign
// combination discharges. Mirror of intProveSignedProduct.
func realProveSignedProduct(hyps []Term, x, y Term, wantNonneg, strict bool) (*prop.PropWrapper, bool) {
	rel, relT := realLe, realLeT
	if strict {
		rel, relT = realLt, realLtT
	}
	prod := realStarT(x, y)
	if wantNonneg {
		if w, ok := realMulPosLemma(hyps, x, y, strict); ok { // &0⋈x, &0⋈y
			return w, true
		}
		if w, ok := realMulPosLemma(hyps, realNegT(x), realNegT(y), strict); ok { // x⋈&0, y⋈&0
			eq := realSubneg.negNegMul(x, y)                 // (−x)·(−y) = x·y
			cong := eq.LeftApply(ext.Apply(rel, realLit(0))) // (&0⋈(−x)·(−y)) = (&0⋈x·y)
			return cong.EqMP(w), true                        // ⊢ &0 ⋈ x·y
		}
		return nil, false
	}
	if w, ok := realMulPosLemma(hyps, realNegT(x), y, strict); ok { // x⋈&0, &0⋈y
		return realFlipNeg(w, realSubneg.negLmul(x, y), prod, rel, relT, strict) // (−x)·y = −(x·y)
	}
	if w, ok := realMulPosLemma(hyps, x, realNegT(y), strict); ok { // &0⋈x, y⋈&0
		return realFlipNeg(w, realSubneg.mulRightNeg(x, y), prod, rel, relT, strict) // x·(−y) = −(x·y)
	}
	return nil, false
}

// realFlipNeg turns `w : Γ ⊢ &0 ⋈ negProd` plus `eq : ⊢ negProd = −prod` into
// `Γ ⊢ prod ⋈ &0`: rewrite w to `&0 ⋈ −prod`, then flip to `prod ⋈ &0` via the
// neg-order iff NegNonnegativeIffNonpositive / NegPositiveIffNegative instantiated at the product. The flip is
// at the PROOF level because linarith atomizes `−prod` and `prod` as independent
// opaque atoms and cannot relate them. Mirror of intFlipNeg.
func realFlipNeg(w, eq *prop.PropWrapper, prod, rel Term, relT func(a, b Term) Term, strict bool) (*prop.PropWrapper, bool) {
	cong := eq.LeftApply(ext.Apply(rel, realLit(0))) // (&0 ⋈ negProd) = (&0 ⋈ −prod)
	negFact := cong.EqMP(w)                          // Γ ⊢ &0 ⋈ −prod
	flipThm := realNegNonnegativeIffNonpositiveThm()
	if strict {
		flipThm = realNegPositiveIffNegativeThm()
	}
	flipIff := realEqLeaf(flipThm, []Term{prod},
		relT(realLit(0), realNegT(prod)), relT(prod, realLit(0))) // ⊢ (&0 ⋈ −prod) = (prod ⋈ &0)
	return flipIff.EqMP(negFact), true // Γ ⊢ prod ⋈ &0
}

// realProveProductMul2 proves `{hyps} ⊢ a·c ≤ b·d` from the four
// bounds `&0≤a, a≤b, &0≤c, c≤d` — DERIVED, no new bundle field: scale `a ≤ b` by c
// on the right (realMonoScaleRight, side condition &0≤c) to `a·c ≤ b·c`, scale
// `c ≤ d` by b on the left (realMonoScaleLeft, side condition &0≤b which follows
// from &0≤a ∧ a≤b) to `b·c ≤ b·d`, then transitivity over the opaque product atoms
// (LessEqTrans). nil/false when any bound fails to discharge. Mirror of
// intProveProductMul2.
func realProveProductMul2(hyps []Term, a, c, b, d Term) (*prop.PropWrapper, bool) {
	acbc, ok := realMonoScaleRight(hyps, c, a, b, false) // ⊢ a·c ≤ b·c
	if !ok {
		return nil, false
	}
	bcbd, ok := realMonoScaleLeft(hyps, b, c, d, false) // ⊢ b·c ≤ b·d
	if !ok {
		return nil, false
	}
	// transitivity a·c ≤ b·c ≤ b·d (LessEqTrans; the real path atomizes the
	// product atoms, so plain linarith cannot chain them).
	ac, bc, bd := realStarT(a, c), realStarT(b, c), realStarT(b, d)
	imp := realImplyLeaf(realLessEqTransThm(), []Term{ac, bc, bd},
		imply(realLeT(ac, bc), imply(realLeT(bc, bd), realLeT(ac, bd))))
	return mp(mp(imp, acbc), bcbd), true // Γ ⊢ a·c ≤ b·d
}

// realProveSquareNonneg closes `⊢ &0 ≤ x·x` with NO sign hypothesis (SquareNonneg).
// realProveMonotone needs factor-sign hyps and declines here; a square is nonneg
// outright, so this is a single lemma instantiation — the ℝ analogue of `int`'s
// Image square split of ℤ, but ℝ needs no sign split (a square IS nonneg). ok=false
// when the goal is not `&0 ≤ (square)`.
func realProveSquareNonneg(goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := realDomain.matchLe(goal)
	if !ok || !isRealZero(l) {
		return nil, false // goal must be `&0 ≤ r`
	}
	x, y, ok := realDomain.matchStar(r)
	if !ok || !x.AlphaEquals(y) {
		return nil, false // r must be a square x·x
	}
	// SquareNonneg: ∀x. &0 ≤ x·x — instantiate at x (the leaf is concluded, not
	// hypothetical, so realImplyLeaf gives `⊢ &0 ≤ x·x` directly).
	return realImplyLeaf(realSquareNonnegThm(), []Term{x}, realLeT(realLit(0), realStarT(x, x))), true
}

// realProveAbsNonneg closes `⊢ &0 ≤ real_abs t` for ANY t via AbsNonneg
// (∀x. &0 ≤ real_abs x). Single lemma instantiation, no case split — the bare
// |x| would otherwise reach realProveSplit and burn a two-branch abs def split.
// More importantly, this is invoked from realLinProveSigned (the sign-of-product
// side-condition discharge) so `&0 ≤ |x|·|y|` closes after realAbsSgnSimp folds
// it to `&0 ≤ |x|·|y|` and sign-of-product asks for `&0 ≤ |x|` / `&0 ≤ |y|` —
// linarith can't see abs, but this handler can. ok=false when the goal is not
// `&0 ≤ real_abs(_)`.
func realProveAbsNonneg(goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := realDomain.matchLe(goal)
	if !ok || !isRealZero(l) {
		return nil, false // goal must be `&0 ≤ r`
	}
	x, ok := MatchesRealAbs(r)
	if !ok {
		return nil, false // r must be `real_abs x`
	}
	// AbsNonneg: ∀x. &0 ≤ real_abs x — instantiate at x (concluded, not
	// hypothetical, so realImplyLeaf gives `⊢ &0 ≤ real_abs x` directly).
	return realImplyLeaf(realAbsNonnegThm(), []Term{x}, realLeT(realLit(0), realAbsT(x))), true
}

// Integral-domain (MulEqZero) square specializations — ℝ is a field, hence has no
// zero divisors. The distinct-factor `x·y=&0` is the splittable hyp;
// the square cases a==b are handled here (the split's two guards would coincide).

// realProveMulEqZeroSquare closes a goal from a hyp `x·x = &0`: MulEqZero gives
// `(x=&0) ∨ (x=&0)`, collapsed to the single fact `x = &0` by (p∨p)⇔p (no case
// split — its two guards coincide). The fact is
// added and the goal re-proved by the linear core. nil/false when no square-zero
// hyp helps. Mirror of intProveMulEqZeroSquare.
func realProveMulEqZeroSquare(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	for _, h := range hyps {
		a, b, ok := realProductZeroEq(h)
		if !ok || !a.AlphaEquals(b) {
			continue
		}
		za := eqT(a, realLit(0))
		fact := prop.BooleanThms["p ∨ p"](za).EqMP(realMulEqZeroDisj(h, a, b)) // {h} ⊢ a=&0
		w, ok := RealLinProve(slices.Values(append(slices.Clone(hyps), za)), goal)
		if !ok {
			continue
		}
		return fact.DeriveTrans(w), true // {hyps} ⊢ goal (cut a=&0)
	}
	return nil, false
}

// realProveStrictSquare closes `{hyps} ⊢ &0 < x·x` given a hyp `x ≠ &0`: split x on
// its sign via the trichotomy (LessThanTrichotomy, the same engine the `≠`-hyp split
// uses), and close each branch with the STRICT sign-of-product (both factors the
// same definite sign → MulPos, reusing realProveSignedProduct). The two guards
// `x<&0` / `&0<x` are distinct, so ByCases recombines. x's being nonzero is
// whatever evidence realProveNeqZero reads. nil/false otherwise.
func realProveStrictSquare(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := realDomain.matchLt(goal)
	if !ok || !isRealZero(l) {
		return nil, false // goal must be `&0 < r`
	}
	x, y, ok := realDomain.matchStar(r)
	if !ok || !x.AlphaEquals(y) {
		return nil, false // r must be a square x·x
	}
	neq := realProveNeqZero(hyps, x) // {hyps} ⊢ ¬(x=&0) (else &0 < x·x is not valid)
	if neq == nil {
		return nil, false
	}
	tri := realTrichotomyNeq(x, realLit(0)) // {¬(x=&0)} ⊢ (x<&0) ∨ (&0<x)
	if tri == nil {
		return nil, false
	}
	tri = prop.WrapProp(neq.MaybeDeriveTrans(tri)) // {hyps} ⊢ (x<&0) ∨ (&0<x)
	gNeg, gPos := realLtT(x, realLit(0)), realLtT(realLit(0), x)
	negBr, ok := realProveSignedProduct([]Term{gNeg}, x, x, true, true) // {x<&0} ⊢ &0<x·x
	if !ok {
		return nil, false
	}
	posBr, ok := realProveSignedProduct([]Term{gPos}, x, x, true, true) // {&0<x} ⊢ &0<x·x
	if !ok {
		return nil, false
	}
	return prop.ByCases(goal, gNeg, gPos).
		DeriveHypFrom(tri).
		DeriveHypFrom(negBr.PromoteHyp(gNeg)).
		DeriveHypFrom(posBr.PromoteHyp(gPos)), true // {¬(x=&0)} ⊢ &0 < x·x
}

// The real FIELD layer (real_div / real_inv) — ℝ-specific, no int twin (ℤ has
// Euclidean int_div/int_rem instead). It closes the field fragment that reduces to the
// already-built ring/linear/sign layer WITHOUT full RCF:
//
//   - simp folds (hyp-free, realArithSimpStep): `x/&1 → x` (DivOne),
//     `inv &1 → &1` (InvOne);
//   - inverse cancellation (hyp-aware): `y · inv y → &1`, `inv y · y → &1`,
//     `y / y → &1` when `y ≠ &0` is derivable (MulRightInverse / MulLeftInverse / DivRefl);
//   - denominator clearing (hyp-aware): a comparison/equality atom with a division
//     `x ⋈ y/z` (or `x/z ⋈ y`, ⋈ ∈ {=,≤,<}) is cleared to a division-free
//     `x·z ⋈ y` (or `x ⋈ y·z`) via {Eq,LessEq,LessThan}DivMul{Left,Right}, discharging the
//     divisor's sign: `&0 < z` (incl. a positive literal, via the of_num bridge)
//     applies the positive lemma; `z < &0` applies the sign-flipped negative lemma;
//     an unknown-sign `z ≠ &0` (an explicit hyp, or a derivable strict sign) splits
//     on `z < &0 ∨ &0 < z` (LessThanTrichotomy). The cleared atom recurses through the
//     full decider (so its `x·z` product reaches monotone scaling / linarith).
//
// Out of scope (the field frontier): multiple / nested denominators in one atom,
// and a divisor whose sign/nonzeroness is not derivable. The negative-divisor
// lemmas have no entry of their own: serve.InstallRealBundle derives each from
// its positive-divisor sibling.

// ── Field leaves (macro instantiations of the bundle fields) ─────────────────

// realInvOne: ⊢ inv &1 = &1   (InvOne).
func realInvOne() *prop.PropWrapper {
	return realEqLeaf(realInvOneThm(), nil, realInvT(realLit(1)), realLit(1))
}

// realDivOne: ⊢ x/&1 = x   (DivOne).
func realDivOne(x Term) *prop.PropWrapper {
	return realEqLeaf(realDivOneThm(), []Term{x}, realDivT(x, realLit(1)), x)
}

// realMulRightInverseDisj / realMulLeftInverseDisj / realDivReflDisj: the `(x=&0) ∨ eq` clauses
// (MulRightInverse / MulLeftInverse / DivRefl); the cancellation extracts the eq under a
// `¬(x=&0)` proof (disjSyllogism, the intRemNonneg pattern).
func realMulRightInverseDisj(x Term) *prop.PropWrapper {
	return realImplyLeaf(realMulRightInverseThm(), []Term{x},
		or(eqT(x, realLit(0)), eqT(realLit(1), realStarT(x, realInvT(x)))))
}
func realMulLeftInverseDisj(x Term) *prop.PropWrapper {
	return realImplyLeaf(realMulLeftInverseThm(), []Term{x},
		or(eqT(x, realLit(0)), eqT(realLit(1), realStarT(realInvT(x), x))))
}
func realDivReflDisj(x Term) *prop.PropWrapper {
	return realImplyLeaf(realDivReflThm(), []Term{x},
		or(eqT(x, realLit(0)), eqT(realLit(1), realDivT(x, x))))
}

// ── Sign helpers ─────────────────────────────────────────────────────────────

// realSignPos / realSignNeg prove `{hyps} ⊢ &0 < z` / `{hyps} ⊢ z < &0` through
// the linear forward prover (an explicit hyp, a linear consequence, or a
// positive/negative literal via the of_num bridge), the goal positivized
// first where z carries a subtraction — so a divisor `b − a` has its sign
// from `a < b`. nil when undischarged.
func realSignPos(hyps []Term, z Term) *prop.PropWrapper {
	if w, ok := realLinProveSigned(hyps, realLtT(realLit(0), z)); ok {
		return w
	}
	return nil
}
func realSignNeg(hyps []Term, z Term) *prop.PropWrapper {
	if w, ok := realLinProveSigned(hyps, realLtT(z, realLit(0))); ok {
		return w
	}
	return nil
}

// realProveNeqZero proves `{hyps} ⊢ ¬(z=&0)` from the evidence the context
// holds (real_nonzero.go): the fact itself, as written or in the square form
// the arith step rewrites a resident `z ≠ &0` into; a strict sign of z; a
// resident disequality or a positive absolute value that z = &0 would
// contradict; and for a power, the evidence of its base. nil otherwise.
// Mirror of intProveNeqZero for the first two.
func realProveNeqZero(hyps []Term, z Term) *prop.PropWrapper {
	neq := not(eqT(z, realLit(0)))
	if slices.ContainsFunc(hyps, neq.AlphaEquals) {
		return prop.Assume(neq)
	}
	if zeroLt := realSignPos(hyps, z); zeroLt != nil {
		if w := realNeqZeroFromPos(z, zeroLt); w != nil {
			return w
		}
	}
	if ltZero := realSignNeg(hyps, z); ltZero != nil {
		if w := realNeqZeroFromNeg(z, ltZero); w != nil {
			return w
		}
	}
	if w := realNeqZeroByContradiction(hyps, z); w != nil {
		return w
	}
	if base, exponent, ok := MatchesRealPow(z); ok {
		return realPowerNonzero(hyps, base, exponent)
	}
	return nil
}

// realNeqZeroFromPos / FromNeg derive `¬(z=&0)` from `&0<z` / `z<&0`: assume z=&0,
// substitute into the strict sign to get the false `&0<&0`, refute. Mirror of
// intNeqZeroFromPos / FromNeg.
func realNeqZeroFromPos(z Term, zeroLt *prop.PropWrapper) *prop.PropWrapper {
	zEq0 := eqT(z, realLit(0))
	cong := prop.Assume(zEq0).LeftApply(ext.Apply(realLt, realLit(0))) // ⊢ (&0<z) = (&0<&0)
	ltZero := cong.EqMP(zeroLt)                                        // {hyps, z=&0} ⊢ &0<&0
	ltFalse, ok := realNormNatLt(realLit(0), realLit(0))               // ⊢ (&0<&0) ⇔ ⊥
	if !ok {
		return nil
	}
	return ltFalse.EqMP(ltZero).NegHyp(zEq0) // {hyps} ⊢ ¬(z=&0)
}
func realNeqZeroFromNeg(z Term, ltZero *prop.PropWrapper) *prop.PropWrapper {
	zEq0 := eqT(z, realLit(0))
	cong := prop.Assume(zEq0).LeftApply(realLt).RightApply(realLit(0)) // ⊢ (z<&0) = (&0<&0)
	zZero := cong.EqMP(ltZero)                                         // {hyps, z=&0} ⊢ &0<&0
	ltFalse, ok := realNormNatLt(realLit(0), realLit(0))
	if !ok {
		return nil
	}
	return ltFalse.EqMP(zZero).NegHyp(zEq0)
}

// ── Inverse cancellation (hyp-aware) ─────────────────────────────────────────

// realCancelRewrite folds a cancellable inverse product to `&1`: `y · inv y → &1`
// (MulRightInverse), `inv y · y → &1` (MulLeftInverse), `y / y → &1` (DivRefl),
// each gated on `y ≠ &0` being derivable from hyps.
func realCancelRewrite(hyps []Term) prop.Rewrite {
	cancel := func(y Term, disj func(Term) *prop.PropWrapper) *prop.PropWrapper {
		neq0 := realProveNeqZero(hyps, y)
		if neq0 == nil {
			return nil
		}
		rest := disjSyllogism(disj(y), neq0) // {hyps} ⊢ &1 = <prod>
		if rest == nil {
			return nil
		}
		return rest.EqSym() // {hyps} ⊢ <prod> = &1
	}
	return func(t Term) *prop.PropWrapper {
		if a, b, ok := realDomain.matchStar(t); ok {
			if inv, ok := MatchesRealInv(b); ok && inv.AlphaEquals(a) { // a · inv a
				return cancel(a, realMulRightInverseDisj)
			}
			if inv, ok := MatchesRealInv(a); ok && inv.AlphaEquals(b) { // inv b · b
				return cancel(b, realMulLeftInverseDisj)
			}
		}
		if a, b, ok := MatchesRealDiv(t); ok && a.AlphaEquals(b) { // a / a
			return cancel(a, realDivReflDisj)
		}
		return nil
	}
}

// ── relation-kind helper ─────────────────────────────────────────────────────

type relKind int

const (
	relEq relKind = iota
	relLe
	relLt
)

// matchRealRel decomposes a real `=` / `≤` / `<` atom into its relation kind and
// sides (the `>`/`≥` atoms are already bridged to swapped `<`/`≤` by realDecideCmp
// before realProveDecAtom, so only these three reach here).
func matchRealRel(t Term) (relKind, Term, Term, bool) {
	if l, r, ok := realDomain.matchLe(t); ok {
		return relLe, l, r, true
	}
	if l, r, ok := realDomain.matchLt(t); ok {
		return relLt, l, r, true
	}
	if l, r, ok := matchRealEq(t); ok {
		return relEq, l, r, true
	}
	return 0, nil, nil, false
}

// ── Denominator clearing ─────────────────────────────────────────────────────

// realClearAtom clears a single division from the comparison/equality atom `goal`
// (`x ⋈ y/z` or `x/z ⋈ y`), returning `⊢ goal` by reducing to the division-free
// cleared atom (recursing through the decider) under the divisor's sign. nil/false
// when the atom carries no clearable division or the sign does not settle.
func realClearAtom(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	rel, l, r, ok := matchRealRel(goal)
	if !ok {
		return nil, false
	}
	if y, z, ok := MatchesRealDiv(r); ok { // division on the RIGHT: l ⋈ y/z
		return realClearWith(hyps, goal, rel, l, y, z, true)
	}
	if y, z, ok := MatchesRealDiv(l); ok { // division on the LEFT: y/z ⋈ r
		return realClearWith(hyps, goal, rel, r, y, z, false)
	}
	return nil, false
}

// realClearWith clears the division by `z` under its sign and recurses. `rightDiv`
// selects which side held the quotient; `other` is the non-quotient side, `num` the
// quotient's numerator.
func realClearWith(hyps []Term, goal Term, rel relKind, other, num, z Term, rightDiv bool) (*prop.PropWrapper, bool) {
	if pos := realSignPos(hyps, z); pos != nil { // &0 < z
		return realClearSigned(hyps, goal, rel, other, num, z, pos, true, rightDiv)
	}
	if neg := realSignNeg(hyps, z); neg != nil { // z < &0
		return realClearSigned(hyps, goal, rel, other, num, z, neg, false, rightDiv)
	}
	// Unknown sign: split on z<&0 ∨ &0<z (z ≠ &0 derivable), each branch clears.
	neq0 := realProveNeqZero(hyps, z)
	if neq0 == nil {
		return nil, false
	}
	tri := realTrichotomyNeq(z, realLit(0)) // {¬(z=&0)} ⊢ (z<&0) ∨ (&0<z)
	if tri == nil {
		return nil, false
	}
	gNeg, gPos := realLtT(z, realLit(0)), realLtT(realLit(0), z)
	negBr, ok := realClearAtom(append(slices.Clone(hyps), gNeg), goal)
	if !ok {
		return nil, false
	}
	posBr, ok := realClearAtom(append(slices.Clone(hyps), gPos), goal)
	if !ok {
		return nil, false
	}
	out := prop.ByCases(goal, gNeg, gPos).
		DeriveHypFrom(tri).
		DeriveHypFrom(negBr.PromoteHyp(gNeg)).
		DeriveHypFrom(posBr.PromoteHyp(gPos))
	return out.DeriveHypFrom(neq0), true // {hyps} ⊢ goal
}

// realClearSigned clears with a KNOWN-sign divisor: the *DivMul{Left,Right} (isPos) or their Neg twins
// (z<0, sign-flipped) iff, modus-ponens'd with the sign proof, gives `⊢ goal ⇔
// cleared`; prove the cleared atom and bridge back. signProof : {hyps} ⊢ signCond.
func realClearSigned(hyps []Term, goal Term, rel relKind, other, num, z Term, signProof *prop.PropWrapper, isPos, rightDiv bool) (*prop.PropWrapper, bool) {
	thm, cleared := realClearLemma(rel, isPos, rightDiv, other, num, z)
	if cleared == nil { // unhandled (rel, side) combo; thm itself may be nil (→ placeholder)
		return nil, false
	}
	signCond := realLtT(realLit(0), z)
	if !isPos {
		signCond = realLtT(z, realLit(0))
	}
	imp := realImplyLeaf(thm, []Term{z, other, num}, imply(signCond, eqT(goal, cleared)))
	iff := signProof.DeriveTrans(imp.DemoteHyp()) // {hyps} ⊢ goal ⇔ cleared
	proof, ok := realProveDecAtom(slices.Values(hyps), cleared)
	if !ok {
		return nil, false
	}
	return iff.EqSym().EqMP(proof), true // ⊢ goal
}

// realClearLemma selects the clearing bundle field + the cleared (division-free)
// atom for a (rel, sign, side). The iff each field carries is `goal ⇔ cleared` (the
// leaf builds it at the call-site goal). `prod = other·z`. The </≤ directions flip
// for a negative divisor; `=` never flips.
func realClearLemma(rel relKind, isPos, rightDiv bool, other, num, z Term) (*prop.PropWrapper, Term) {
	prod := realStarT(other, z)
	switch {
	case rightDiv && isPos: // other ⋈ num/z  →  other·z ⋈ num   (= : num = other·z)
		switch rel {
		case relLe:
			return realLessEqDivMulLeftThm(), realLeT(prod, num)
		case relLt:
			return realLessThanDivMulLeftThm(), realLtT(prod, num)
		case relEq:
			return realEqDivMulLeftThm(), eqT(num, prod)
		}
	case rightDiv && !isPos: // other ⋈ num/z, z<0  →  flipped: num ⋈ other·z   (= : num = other·z)
		switch rel {
		case relLe:
			return realLessEqDivMulLeftNegThm(), realLeT(num, prod)
		case relLt:
			return realLessThanDivMulLeftNegThm(), realLtT(num, prod)
		case relEq:
			return realEqDivMulLeftNegThm(), eqT(num, prod)
		}
	case !rightDiv && isPos: // num/z ⋈ other  →  num ⋈ other·z   (= : num = other·z)
		switch rel {
		case relLe:
			return realLessEqDivMulRightThm(), realLeT(num, prod)
		case relLt:
			return realLessThanDivMulRightThm(), realLtT(num, prod)
		case relEq:
			return realEqDivMulRightThm(), eqT(num, prod)
		}
	case !rightDiv && !isPos: // num/z ⋈ other, z<0  →  flipped: other·z ⋈ num   (= : num = other·z)
		switch rel {
		case relLe:
			return realLessEqDivMulRightNegThm(), realLeT(prod, num)
		case relLt:
			return realLessThanDivMulRightNegThm(), realLtT(prod, num)
		case relEq:
			return realEqDivMulRightNegThm(), eqT(num, prod)
		}
	}
	return nil, nil
}

// realClearLiteralDivSimp clears a division by a positive LITERAL divisor out of
// a comparison atom, as a hypothesis-FREE rewrite: `⊢ (x/&k ⋈ y) = (x ⋈ y·&k)`.
//
// The field handler below does the same clearing, but it PROVES a goal — it
// recurses into the decider on the cleared atom — so it reaches a division only
// where the division sits in the GOAL. A division in a HYPOTHESIS never met it,
// and linarith reads `x/&2` as an opaque atom unrelated to `x`, so
// `x/&2 ≤ y ⊢ x ≤ &2·y` failed while its goal-side mirror closed. As a rewrite
// this fires wherever the simp step runs — on hypotheses in the pre-simp and on
// goals in the deep rewrite alike — and needs no sign hypothesis, the divisor's
// positivity being a numeral evaluation.
//
// Only a literal divisor: a symbolic one needs its sign from the context, which
// is a proof obligation and therefore the handler's business, not a rewrite's.
// Strictly removes one `real_div` node, so the fixpoint converges.
func realClearLiteralDivSimp(t Term) *prop.PropWrapper {
	rel, l, r, ok := matchRealRel(t)
	if !ok {
		return nil
	}
	var other, num, z Term
	rightDiv := false
	if y, d, ok := MatchesRealDiv(r); ok {
		other, num, z, rightDiv = l, y, d, true
	} else if y, d, ok := MatchesRealDiv(l); ok {
		other, num, z = r, y, d
	} else {
		return nil
	}
	// A POSITIVE literal divisor, so the direction never flips and the sign is
	// a numeral fact rather than a context one.
	v, shaped, exact := realDomain.asLiteral(z)
	if !shaped || !exact || v.isZero() {
		return nil
	}
	pos, ok := realNormNatLt(realLit(0), z) // ⊢ (&0 < &k) ⇔ ⊤
	if !ok || !prop.Rhs(pos).Equals(prop.T) {
		return nil
	}
	thm, cleared := realClearLemma(rel, true, rightDiv, other, num, z)
	if cleared == nil {
		return nil
	}
	imp := realImplyLeaf(thm, []Term{z, other, num},
		imply(realLtT(realLit(0), z), eqT(t, cleared)))
	return mp(imp, iffTrueElim(pos)) // ⊢ t = cleared
}

// ── the field handler entry ──────────────────────────────────────────────────

// realProveDivField is the field-layer entry the decide leaf calls (after the
// linear/monotone handlers): first try inverse cancellation (fold a cancellable
// `y·inv y` / `y/y` to &1, then re-decide), then denominator clearing. nil/false
// when the goal carries no field structure these close.
func realProveDivField(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if w := prop.DeepRewrite(realCancelRewrite(hyps))(goal); w != nil {
		if proof, ok := realProveDecAtom(slices.Values(hyps), prop.Rhs(w)); ok {
			return w.EqSym().EqMP(proof), true // ⊢ goal
		}
	}
	return realClearAtom(hyps, goal)
}

// real_pow (real exponentiation `real_pow : real → num → real`) — the real twin of
// int_pow (int.go) / the num nat_pow layer (nat_exp.go). real_pow is opaque to
// linarith/ring in general; the only tractable case is a LITERAL num exponent c,
// unfolded to a product chain `m · m · … · m` (c copies, `&1` for c=0) feeding the
// real ring/linear core. A strictly-shrinking c≤1 fold auto-fires inside
// realArithSimpStep, and ExpandRealPowRewrite unfolds every literal-exponent atom
// (the agent-controlled c≥2 surface, since `real_pow(complex, c)` grows term size).
//
// The exponent is `num` (suc/Numeral/sucBits are the num successor machinery,
// reused unchanged); only the base and the result are real. Like the int twin.

// realPowZero: ⊢ real_pow x 0 = &1   (real_pow's base clause).
func realPowZero(x Term) *prop.PropWrapper {
	return realEqLeaf(realPowZeroThm(), []Term{x}, realPowT(x, natZero), realLit(1))
}

// realPowSuc: ⊢ real_pow x (suc n) = x · real_pow x n   (real_pow's step clause).
func realPowSuc(x, n Term) *prop.PropWrapper {
	return realEqLeaf(realPowSucThm(), []Term{x, n}, realPowT(x, sucT(n)), realStarT(x, realPowT(x, n)))
}

// realPowUnfold proves `⊢ real_pow m c = <unfolded product>` for a literal c ≥ 0.
// nil when c exceeds expUnfoldMax (the shared cap). Mirror of intPowUnfold.
func realPowUnfold(m Term, c uint64) *prop.PropWrapper {
	if c > expUnfoldMax {
		return nil
	}
	if c == 0 {
		return realPowZero(m) // ⊢ real_pow m 0 = &1
	}
	return realPowStep(m, c)
}

// realPowStep is the recursive case: build `⊢ real_pow m c = m · P` from inner
// `real_pow m (c-1) = P` and the PowSuc recursion at n = c-1. Mirror of
// intPowStep (the PowSuc is already in the `pow(suc n) = m·pow(n)` orientation,
// so no EqSym of the recursion clause is needed).
func realPowStep(m Term, c uint64) *prop.PropWrapper {
	inner := realPowUnfold(m, c-1) // ⊢ real_pow m (c-1) = P
	if inner == nil {
		return nil
	}
	cMinus1 := Numeral(c - 1)
	// powSuc: ⊢ real_pow m (suc(c-1)) = m · real_pow m (c-1)   [PowSuc]
	powSuc := realPowSuc(m, cMinus1)
	// sucEq: ⊢ suc(c-1) = c   [numeric, via sucBits on the bit-tree]
	sucEq := sucBits(cMinus1)
	if sucEq == nil {
		return nil
	}
	// cong: ⊢ real_pow m (suc(c-1)) = real_pow m c   [congruence under real_pow m _]
	cong := sucEq.LeftApply(ext.Apply(realPow, m))
	// step2: ⊢ real_pow m c = m · real_pow m (c-1)   [cong⁻¹ ∘ powSuc]
	step2 := cong.EqSym().EqTrans(powSuc)
	// congMul: ⊢ m · real_pow m (c-1) = m · P   [congruence under m·_]
	congMul := inner.LeftApply(ext.Apply(realStar, m))
	// result: ⊢ real_pow m c = m · P
	return step2.EqTrans(congMul)
}

// realPowSimp is the realArithSimpStep entry: ONLY the strictly size-reducing
// literal cases c ≤ 1 (`real_pow m 0 → &1`, `real_pow m 1 → m`). Higher exponents
// are NOT auto-unfolded (a complex base to a high power explodes); the agent drives
// those through ExpandRealPowRewrite. Mirror of intPowSimp.
//
// The OfNumPow bridge — `real_pow(&m, n) → &(nat_pow(m, n))` when the
// base is `&_`. The wrapped num expression `nat_pow(m, n)` is then folded by the num-
// side expSimp (NormNatExp for literal m,n; ExpandEXPRewrite + ring for symbolic).
// GATED on the OfNumPow bundle field being non-nil: when the field is unbound,
// the clause silently falls through and the agent-driven ExpandRealPowRewrite
// path stays in effect. Strict size-shrinks at the real head (replaces real_pow with
// real_of_num + num nat_pow), so the DeepRewrite fixpoint converges.
func realPowSimp(t Term) *prop.PropWrapper {
	m, n, ok := MatchesRealPow(t)
	if !ok {
		return nil
	}
	if c, ok := BitsToUint(n); ok && c <= 1 {
		return realPowUnfold(m, c)
	}
	// OfNumPow: base is `&inner` → bridge to num nat_pow. Fires for symbolic n too
	// (the lemma is universally quantified in n). Gated on the bundle so an
	// unbound field is a clean no-op rather than a production panic.
	if realOfNumPowThm() == nil {
		return nil
	}
	// Carve-out: `&1 pow n` is handled cleanly by PowLawSimp's OnePow clause
	// (`&1 pow n = &1`, OnePow). Going through OfNumPow would land at
	// `real_of_num(nat_pow(1, n))` whose num-side nat_pow fold needs a literal exponent;
	// for symbolic n that path is a dead end and OnePow never gets a turn.
	if isRealOne(m) {
		return nil
	}
	if inner, isOfNum := MatchesRealOfNum(m); isOfNum {
		return realOfNumPow(inner, n)
	}
	return nil
}

// realOfNumPow: ⊢ real_pow(&m, n) = &(nat_pow(m, n))   (OfNumPow). The real_pow
// sibling of the OfNumAdd/Mul bridges in real_lemmas.go. Used by realPowSimp's
// OfNumPow clause above. Placeholder-routed when the bundle field is nil (and
// the caller pre-gates so this is only reached when it is bound).
func realOfNumPow(m, n Term) *prop.PropWrapper {
	return realEqLeaf(realOfNumPowThm(), []Term{m, n},
		realPowT(realOfNumT(m), n), realOfNumT(expT(m, n)))
}

// realPowUnfoldLeaf unfolds a single `real_pow m c` atom for any literal c ≥ 0 (no
// c ≤ 1 restriction). Mirror of intPowUnfoldLeaf.
func realPowUnfoldLeaf(t Term) *prop.PropWrapper {
	m, n, ok := MatchesRealPow(t)
	if !ok {
		return nil
	}
	c, ok := BitsToUint(n)
	if !ok {
		return nil
	}
	return realPowUnfold(m, c)
}

// ExpandRealPowRewrite is the deep+fixpoint rewrite that unfolds every literal-
// exponent real_pow atom anywhere in a term into a product chain — the real twin of
// ExpandIntPowRewrite / ExpandEXPRewrite. The agent decides when to pay the
// term-growth cost.
func ExpandRealPowRewrite() prop.Rewrite { return prop.DeepRewrite(realPowUnfoldLeaf) }

// ── real_pow sign / monotone (the sign-known fragment, NOT full RCF) ──────────

// realProvePowSign closes a sign goal on a real_pow atom from the BASE's sign — the
// real_pow twin of the sign-of-product layer. The input is a
// base-sign fact, the output a single lemma instantiation. For `&0 ⋈ (x pow n)`,
// n any num term:
//
//	&0 ≤ x pow n  from  &0 ≤ x   (PowNonneg, symbolic n);
//	&0 ≤ x pow 2  with NO hyp    (PowTwoNonneg — an even square is nonneg);
//	&0 < x pow n  from  &0 < x   (PowPos).
//
// ok=false when the goal is not such a shape or the base sign does not discharge.
func realProvePowSign(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := realDomain.matchLe(goal); ok && isRealZero(l) {
		if x, n, ok := MatchesRealPow(r); ok {
			return realPowNonneg(hyps, x, n, r)
		}
	}
	if l, r, ok := realDomain.matchLt(goal); ok && isRealZero(l) {
		if x, n, ok := MatchesRealPow(r); ok {
			return realPowPos(hyps, x, n, r)
		}
	}
	return nil, false
}

// realPowNonneg proves `{hyps} ⊢ &0 ≤ pow` (pow = x pow n): from `&0 ≤ x` via
// PowNonneg (any n), or unconditionally when n is the literal 2 via PowTwoNonneg,
// or unconditionally when n is a literal even ≥ 4 via the perfect-square split
// `x^(2k) = x^k · x^k` (PowAdd + SquareNonneg).
func realPowNonneg(hyps []Term, x, n, pow Term) (*prop.PropWrapper, bool) {
	zero := realLit(0)
	if base, ok := RealLinProve(slices.Values(hyps), realLeT(zero, x)); ok {
		imp := realImplyLeaf(realPowNonnegThm(), []Term{x, n},
			imply(realLeT(zero, x), realLeT(zero, pow)))
		return mp(imp, base), true // ⊢ &0 ≤ x pow n
	}
	if c, ok := BitsToUint(n); ok && c == 2 {
		return realImplyLeaf(realPowTwoNonnegThm(), []Term{x}, realLeT(zero, pow)), true // ⊢ &0 ≤ x pow 2
	}
	if w, ok := realEvenPowNonneg(x, n, pow); ok {
		return w, true // ⊢ &0 ≤ x pow &(2k), k ≥ 2 — perfect-square split
	}
	if w, ok := realSymbolicEvenPowNonneg(hyps, x, n, pow); ok {
		return w, true // ⊢ &0 ≤ x pow n  from  nat_even n  (symbolic exponent)
	}
	return nil, false
}

// realEvenPowNonneg closes `⊢ &0 ≤ x pow &(2k)` for literal even 2k ≥ 4 (the
// `c == 2` case is taken upstream by PowTwoNonneg). Recipe with NO sign hypothesis:
// PowAdd at (x, &k, &k) gives `⊢ x^k · x^k = x^(&k + &k)`; NormNatAdd
// folds `&k + &k = &(2k)` and we lift it under `real_pow x _`; transitivity
// gives `⊢ x^k · x^k = pow`; SquareNonneg closes `⊢ &0 ≤ x^k · x^k`; EqMP
// gives `⊢ &0 ≤ pow`. Declines on a non-literal exponent or odd exponent. The
// SYMBOLIC even-n case (`nat_even n ⊢ &0 ≤ x pow n`) is handled separately by
// realSymbolicEvenPowNonneg below.
func realEvenPowNonneg(x, n, pow Term) (*prop.PropWrapper, bool) {
	c, ok := BitsToUint(n)
	if !ok || c < 4 || c%2 != 0 {
		return nil, false // literal even ≥ 4 only (2 handled by PowTwoNonneg)
	}
	k := c / 2
	kLit := Numeral(k)
	xPowK := realPowT(x, kLit)
	square := realStarT(xPowK, xPowK)
	// PowAdd at (x, &k, &k): ⊢ x^k · x^k = x^(&k + &k)
	powAdd := realEqLeaf(realPowAddThm(), []Term{x, kLit, kLit},
		square, realPowT(x, plus(kLit, kLit)))
	// NormNatAdd: ⊢ &k + &k = &(2k). Lift under `real_pow x _` via congruence so
	// the RHS realPow(x, &k+&k) rewrites to realPow(x, n) = pow.
	addNorm, ok := NormNatAdd(kLit, kLit)
	if !ok {
		return nil, false // should always succeed for literal kLit
	}
	expCong := addNorm.LeftApply(ext.Apply(realPow, x)) // ⊢ x^(&k+&k) = x^n
	eq := powAdd.EqTrans(expCong)                       // ⊢ x^k · x^k = x^n = pow
	sq, ok := realProveSquareNonneg(realLeT(realLit(0), square))
	if !ok {
		return nil, false // SquareNonneg should always close
	}
	// congruence under `&0 ≤ _`: ⊢ (&0 ≤ square) = (&0 ≤ pow), then EqMP `sq`.
	congEq := eq.LeftApply(ext.Apply(realLe, realLit(0)))
	return congEq.EqMP(sq), true // ⊢ &0 ≤ pow
}

// realSymbolicEvenPowNonneg closes `{nat_even n, …} ⊢ &0 ≤ x pow n` for a SYMBOLIC
// exponent n (literal exponents are handled upstream by PowTwoNonneg / the literal
// perfect-square handler). Recipe:
//
//	EvenIffDouble at n:  ⊢ nat_even n ⇔ (∃m. n = 2·m).
//	EqMP with the nat_even n hyp:  {nat_even n} ⊢ ∃m. n = 2·m.
//	Choose a fresh m₀ + body hyp n = 2·m₀; under that hyp, ⊢ &0 ≤ x pow n by:
//	  PowPow(x, 2, m₀):  ⊢ x pow (2·m₀) = (x pow 2) pow m₀;
//	  PowTwoNonneg(x):        ⊢ &0 ≤ x pow 2;
//	  PowNonneg(x pow 2, m₀) + MP: ⊢ &0 ≤ (x pow 2) pow m₀;
//	  bridge through n = 2·m₀ (lifted under `&0 ≤ x pow _`): ⊢ &0 ≤ x pow n.
//	chooseElim discharges the ∃, leaving only the original {nat_even n} hyp.
//
// Declines when n is a literal (upstream handles those), no `nat_even n` hyp is
// present, or any needed bundle field is absent.
func realSymbolicEvenPowNonneg(hyps []Term, x, n, pow Term) (*prop.PropWrapper, bool) {
	if _, ok := BitsToUint(n); ok {
		return nil, false // literals are handled by PowTwoNonneg / realEvenPowNonneg
	}
	var evenHyp Term
	for _, h := range hyps {
		if arg, ok := MatchesEven(h); ok && arg.AlphaEquals(n) {
			evenHyp = h
			break
		}
	}
	if evenHyp == nil {
		return nil, false
	}
	two := Numeral(2)
	zero := realLit(0)
	// Fresh num var m₀ — free in NEITHER any hyp nor the goal pow, so the ∃-elimination
	// substitution touches only the body hyp `n = 2·m₀`.
	m0 := freshNumVar(append(slices.Clone(hyps), n, x, pow))
	twoM0 := star(two, m0)
	body := eqT(n, twoM0)
	existsBody := prop.Exists(m0)(body) // ∃m. n = 2·m

	// EvenIffDouble at n: ⊢ nat_even n = ∃m. n = 2·m. EqMP with the nat_even n hyp.
	evenIff := eqLeaf(evenIffDoubleThm(), []Term{n}, evenT(n), existsBody)
	existsProof := evenIff.EqMP(prop.Assume(evenHyp)) // {nat_even n} ⊢ ∃m. n = 2·m

	// Branch: under hyp `n = 2·m₀`, prove `&0 ≤ x pow n`.
	xPow2 := realPowT(x, two)
	pow2PowM0 := realPowT(xPow2, m0)
	powPow := realEqLeaf(realPowPowThm(), []Term{x, two, m0},
		realPowT(x, twoM0), pow2PowM0) // ⊢ x pow (2·m₀) = (x pow 2) pow m₀
	powTwoNonneg := realImplyLeaf(realPowTwoNonnegThm(), []Term{x}, realLeT(zero, xPow2))
	powNonnegImp := realImplyLeaf(realPowNonnegThm(), []Term{xPow2, m0},
		imply(realLeT(zero, xPow2), realLeT(zero, pow2PowM0)))
	nonnegRhs := mp(powNonnegImp, powTwoNonneg) // ⊢ &0 ≤ (x pow 2) pow m₀

	// Bridge `(x pow 2) pow m₀ = x pow n` via PowPow + the body hyp.
	eqHyp := prop.Assume(body) // {n = 2·m₀} ⊢ n = 2·m₀
	// eqHyp.LeftApply(realPow x): {n = 2·m₀} ⊢ x pow n = x pow (2·m₀).
	powEqHyp := eqHyp.LeftApply(ext.Apply(realPow, x))
	// powPow.EqSym(): ⊢ (x pow 2) pow m₀ = x pow (2·m₀); EqTrans powEqHyp.EqSym():
	bridge := powPow.EqSym().EqTrans(powEqHyp.EqSym()) // {n = 2·m₀} ⊢ (x pow 2) pow m₀ = x pow n
	bridgeLe := bridge.LeftApply(ext.Apply(realLe, zero))
	branchProof := bridgeLe.EqMP(nonnegRhs) // {n = 2·m₀} ⊢ &0 ≤ x pow n

	return chooseElim(existsProof, m0, body, branchProof), true // {nat_even n} ⊢ &0 ≤ x pow n
}

// realPowPos proves `{hyps} ⊢ &0 < pow` (pow = x pow n) from `&0 < x` via PowPos.
func realPowPos(hyps []Term, x, n, pow Term) (*prop.PropWrapper, bool) {
	zero := realLit(0)
	base, ok := RealLinProve(slices.Values(hyps), realLtT(zero, x))
	if !ok {
		return nil, false
	}
	imp := realImplyLeaf(realPowPosThm(), []Term{x, n},
		imply(realLtT(zero, x), realLtT(zero, pow)))
	return mp(imp, base), true // ⊢ &0 < x pow n
}

// realProvePowBaseMono closes a base-monotonicity goal on real_pow with the SAME
// exponent on both sides — `x pow n ⋈ y pow n` from `&0 ≤ x` plus `x ⋈ y`. The
// sub-RCF base-monotone fragment (sign-known nonlinear, NOT full RCF):
//
//	x^n ≤ y^n  from  &0 ≤ x ∧ x ≤ y               (PowMonoBase);
//	x^n < y^n  from  ~(n = 0) ∧ &0 ≤ x ∧ x < y    (PowMonoBaseStrict).
//
// Side conditions discharge through RealLinProve (real) and LinProve (num for
// `~(n = 0)`). Mirror of realProvePowSign for the monotonicity tier.
func realProvePowBaseMono(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := realDomain.matchLe(goal); ok {
		return realPowBaseMono(hyps, l, r, goal, false)
	}
	if l, r, ok := realDomain.matchLt(goal); ok {
		return realPowBaseMono(hyps, l, r, goal, true)
	}
	return nil, false
}

func realPowBaseMono(hyps []Term, l, r, goal Term, strict bool) (*prop.PropWrapper, bool) {
	xb, xe, ok := MatchesRealPow(l)
	if !ok {
		return nil, false
	}
	yb, ye, ok := MatchesRealPow(r)
	if !ok || !xe.AlphaEquals(ye) {
		return nil, false // need same exponent
	}
	zero := realLit(0)
	relT := realLeT
	if strict {
		relT = realLtT
	}
	base, ok := RealLinProve(slices.Values(hyps), realLeT(zero, xb)) // `&0 ≤ x`
	if !ok {
		return nil, false
	}
	ord, ok := RealLinProve(slices.Values(hyps), relT(xb, yb)) // `x ⋈ y`
	if !ok {
		return nil, false
	}
	if !strict {
		imp := realImplyLeaf(realPowMonoBaseThm(), []Term{xe, xb, yb},
			imply(realLeT(zero, xb), imply(realLeT(xb, yb), goal)))
		return mp(mp(imp, base), ord), true
	}
	// strict — also discharge `~(n = 0)`. LinProve drops `~(eq)` hyps (the linarith
	// constraint parser only takes positive-form linear comparisons), so the hyp
	// echo path picks up the common shape where the user states `n ≠ 0` directly;
	// fall through to LinProve for shapes reducible to a linear contradiction (e.g.
	// a hyp `&1 ≤ n`).
	nNonZero := prop.Not(eqT(xe, Numeral(0)))
	var nz *prop.PropWrapper
	if slices.ContainsFunc(hyps, nNonZero.AlphaEquals) {
		nz = prop.Assume(nNonZero)
	} else if w, lok := LinProve(slices.Values(hyps), nNonZero); lok {
		nz = w
	} else {
		return nil, false
	}
	imp := realImplyLeaf(realPowMonoBaseStrictThm(), []Term{xe, xb, yb},
		imply(nNonZero, imply(realLeT(zero, xb), imply(realLtT(xb, yb), goal))))
	return mp(mp(mp(imp, nz), base), ord), true
}

// realProvePowExpMono closes an exponent-monotonicity goal on real_pow with the
// SAME base on both sides — `x pow m ≤ x pow n` from `&1 ≤ x` plus `m ≤ n`. The
// sub-RCF exponent-monotone fragment.
//
//	x^m ≤ x^n  from  &1 ≤ x ∧ m ≤ n   (PowMonoExp).
//
// Side conditions discharge through RealLinProve (real `&1 ≤ x`) and LinProve
// (num `m ≤ n`).
func realProvePowExpMono(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := realDomain.matchLe(goal)
	if !ok {
		return nil, false
	}
	xb, m, ok := MatchesRealPow(l)
	if !ok {
		return nil, false
	}
	yb, n, ok := MatchesRealPow(r)
	if !ok || !xb.AlphaEquals(yb) {
		return nil, false // need same base
	}
	if m.AlphaEquals(n) {
		return nil, false // reflexive — let elsewhere catch it
	}
	base, ok := RealLinProve(slices.Values(hyps), realLeT(realLit(1), xb)) // `&1 ≤ x`
	if !ok {
		return nil, false
	}
	expOrd, ok := LinProve(slices.Values(hyps), le(m, n)) // num `m ≤ n`
	if !ok {
		return nil, false
	}
	imp := realImplyLeaf(realPowMonoExpThm(), []Term{m, n, xb},
		imply(realLeT(realLit(1), xb), imply(le(m, n), goal)))
	return mp(mp(imp, base), expOrd), true
}

// realProveAbsTriangle closes a goal `|sum| ≤ rhs` where sum is a right-
// associated n-ary sum `t1 + (t2 + (... + tn))` (n ≥ 2). Three stages:
//
// 1. Decompose sum into [t1, ..., tn]; build absSum = |t1| + (|t2| + (... + |tn|)).
// 2. Iterated AbsTriangle + LessEqAdd2 + LessEqTrans to prove |sum| ≤ absSum.
// 3. RealLinProve to prove absSum ≤ rhs (when |tᵢ| bounds appear in hyps).
// 4. Transitivity LessEqTrans.
//
// The binary case (`|x+y| ≤ |x|+|y|` directly or with a linarith-derivable rhs)
// is the recursion's base. n-ary closes when each |tᵢ| has a derivable bound and
// linarith can sum them — the corpus's primary triangle use case. Left-
// associated sums are NOT decomposed past the head (ring AC normalization is
// the agent's hammer for that).
func realProveAbsTriangle(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, rhs, ok := realDomain.matchLe(goal)
	if !ok {
		return nil, false
	}
	inner, ok := MatchesRealAbs(l)
	if !ok {
		return nil, false
	}
	terms := decomposeRealPlusRight(inner)
	if len(terms) < 2 {
		return nil, false // not a sum — nothing to triangle
	}
	absSum, triangleProof := iteratedAbsTriangle(terms)
	if rhs.AlphaEquals(absSum) {
		return triangleProof, true // goal is exactly the bound
	}
	boundLeRhs, ok := RealLinProve(slices.Values(hyps), realLeT(absSum, rhs))
	if !ok {
		return nil, false
	}
	return realLessEqTransProof(triangleProof, boundLeRhs), true
}

// decomposeRealPlusRight flattens a right-associated real_add chain.
// `a + (b + (c + d))` → [a, b, c, d]; a non-sum t → [t].
func decomposeRealPlusRight(t Term) []Term {
	if a, b, ok := realDomain.matchPlus(t); ok {
		return append([]Term{a}, decomposeRealPlusRight(b)...)
	}
	return []Term{t}
}

// buildRealPlusRight rebuilds a right-associated sum from a list. len ≥ 1.
func buildRealPlusRight(terms []Term) Term {
	if len(terms) == 1 {
		return terms[0]
	}
	return realPlusT(terms[0], buildRealPlusRight(terms[1:]))
}

// iteratedAbsTriangle returns (absSum, ⊢ |sum| ≤ absSum) for a list of n ≥ 2
// terms, where sum = buildRealPlusRight(terms) and absSum =
// buildRealPlusRight([|t1|, ..., |tn|]) (so both right-associated). Recursive
// over the tail; the n=2 base is one AbsTriangle.
func iteratedAbsTriangle(terms []Term) (Term, *prop.PropWrapper) {
	t1 := terms[0]
	abst1 := realAbsT(t1)
	if len(terms) == 2 {
		t2 := terms[1]
		absSum := realPlusT(abst1, realAbsT(t2))
		proof := realImplyLeaf(realAbsTriangleThm(), []Term{t1, t2},
			realLeT(realAbsT(realPlusT(t1, t2)), absSum))
		return absSum, proof
	}
	tail := terms[1:]
	tailSum := buildRealPlusRight(tail)
	tailAbsSum, tailProof := iteratedAbsTriangle(tail) // ⊢ |tailSum| ≤ tailAbsSum
	absSum := realPlusT(abst1, tailAbsSum)             // |t1| + tailAbsSum
	// Step 1: AbsTriangle(t1, tailSum) — `|t1 + tailSum| ≤ |t1| + |tailSum|`.
	step1Bound := realPlusT(abst1, realAbsT(tailSum))
	step1 := realImplyLeaf(realAbsTriangleThm(), []Term{t1, tailSum},
		realLeT(realAbsT(realPlusT(t1, tailSum)), step1Bound))
	// Step 2: Pad tailProof with `|t1| ≤ |t1|` via LessEqAdd2 to get
	// `|t1| + |tailSum| ≤ |t1| + tailAbsSum`. Reflexivity discharges trivially.
	refl, _ := RealLinProve(slices.Values([]Term{}), realLeT(abst1, abst1))
	add2 := realImplyLeaf(realLessEqAdd2Thm(), []Term{abst1, abst1, realAbsT(tailSum), tailAbsSum},
		imply(realLeT(abst1, abst1),
			imply(realLeT(realAbsT(tailSum), tailAbsSum),
				realLeT(step1Bound, absSum))))
	step2 := mp(mp(add2, refl), tailProof)
	// Step 3: Transit step1 + step2.
	proof := realLessEqTransProof(step1, step2)
	return absSum, proof
}

// realLessEqTransProof builds ⊢ a ≤ c from `ab: a ≤ b` and `bc: b ≤ c` via LessEqTrans.
func realLessEqTransProof(ab, bc *prop.PropWrapper) *prop.PropWrapper {
	a, b, _ := realDomain.matchLe(ab.Conclusion())
	_, c, _ := realDomain.matchLe(bc.Conclusion())
	imp := realImplyLeaf(realLessEqTransThm(), []Term{a, b, c},
		imply(realLeT(a, b), imply(realLeT(b, c), realLeT(a, c))))
	return mp(mp(imp, ab), bc)
}

// abs / sgn algebraic laws — the homomorphism / identity rewrites that push real_abs
// and real_sgn toward the leaves. Distinct from the case split,
// which eliminates a PIECEWISE-by-guard `abs x` / `real_sgn x` at a leaf: these are
// pure equational rewrites over the OPERATOR STRUCTURE (`abs(x·y) = abs x · abs y`,
// `real_sgn(−x) = −real_sgn x`, …).
//
// Wired as a leaf in realArithSimpStep, so the deep+fixpoint rewrite folds every
// abs/sgn redex anywhere in the goal. This makes `|x·y| = |x|·|y|` close as
// reflexivity (both sides normalize to `|x|·|y|`) and `|x·y| ≤ |x|·|y|` close as a
// reflexive `≤` — WITHOUT the cross-sign sign-of-product a brute multi-atom split
// would need (the contradictory `0≤x,0≤y,x·y<0` branch). The fold only fires on
// abs/sgn of a COMPOUND argument (product / neg / abs / div / inv / pow / of_num);
// a bare `abs(variable)` / `real_sgn(variable)` is left for the leaf case split.
//
// Every leaf is unconditional (the laws hold even at the degenerate points, e.g.
// `abs(x/&0) = abs x / abs &0` since `inv &0 = &0`).

// realAbsSgnSimp folds one abs/sgn algebraic redex at t's head, or nil when t is not
// such a redex. Mirror in spirit of realPowSimp; DeepRewrite drives it deep + to
// fixpoint via realArithSimpStep.
func realAbsSgnSimp(t Term) *prop.PropWrapper {
	if x, ok := MatchesRealAbs(t); ok {
		return realAbsLaw(x)
	}
	if x, ok := MatchesRealSgn(t); ok {
		return realSgnLaw(x)
	}
	return nil
}

// realAbsLaw folds `abs(x)` when x is a product / neg / abs / div / inv / pow /
// of_num — pushing the abs inward (or removing it). nil for a bare abs(variable),
// which the leaf case split handles.
func realAbsLaw(x Term) *prop.PropWrapper {
	if a, b, ok := realDomain.matchStar(x); ok { // abs(a·b) = abs a · abs b
		return realEqLeaf(realAbsMulThm(), []Term{a, b},
			realAbsT(realStarT(a, b)), realStarT(realAbsT(a), realAbsT(b)))
	}
	if a, ok := MatchesRealNeg(x); ok { // abs(−a) = abs a
		return realEqLeaf(realAbsEvenThm(), []Term{a}, realAbsT(realNegT(a)), realAbsT(a))
	}
	if a, ok := MatchesRealAbs(x); ok { // abs(abs a) = abs a
		return realEqLeaf(realAbsIdempotentThm(), []Term{a}, realAbsT(realAbsT(a)), realAbsT(a))
	}
	if a, b, ok := MatchesRealDiv(x); ok { // abs(a/b) = abs a / abs b
		return realEqLeaf(realAbsDivThm(), []Term{a, b},
			realAbsT(realDivT(a, b)), realDivT(realAbsT(a), realAbsT(b)))
	}
	if a, ok := MatchesRealInv(x); ok { // abs(inv a) = inv(abs a)
		return realEqLeaf(realAbsInvThm(), []Term{a}, realAbsT(realInvT(a)), realInvT(realAbsT(a)))
	}
	if a, n, ok := MatchesRealPow(x); ok { // abs(a pow n) = abs a pow n
		return realEqLeaf(realAbsPowThm(), []Term{a, n},
			realAbsT(realPowT(a, n)), realPowT(realAbsT(a), n))
	}
	if n, ok := MatchesRealOfNum(x); ok { // abs(&n) = &n
		return realEqLeaf(realAbsOfNumThm(), []Term{n}, realAbsT(realOfNumT(n)), realOfNumT(n))
	}
	return nil
}

// realSgnLaw folds `real_sgn(x)` when x is a product / neg / inv / div / pow.
// nil otherwise (a bare real_sgn(variable) is the leaf case split's; the literal
// `sgn &0 → &0` fires separately in realArithSimpStep).
func realSgnLaw(x Term) *prop.PropWrapper {
	if a, b, ok := realDomain.matchStar(x); ok { // sgn(a·b) = sgn a · sgn b
		return realEqLeaf(realSgnMulThm(), []Term{a, b},
			realSgnT(realStarT(a, b)), realStarT(realSgnT(a), realSgnT(b)))
	}
	if a, ok := MatchesRealNeg(x); ok { // sgn(−a) = −(sgn a)
		return realEqLeaf(realSgnOddThm(), []Term{a}, realSgnT(realNegT(a)), realNegT(realSgnT(a)))
	}
	if a, ok := MatchesRealInv(x); ok { // sgn(inv a) = sgn a
		return realEqLeaf(realSgnPreservedByInvThm(), []Term{a}, realSgnT(realInvT(a)), realSgnT(a))
	}
	if a, b, ok := MatchesRealDiv(x); ok { // sgn(a/b) = sgn a / sgn b
		return realEqLeaf(realSgnDivThm(), []Term{a, b},
			realSgnT(realDivT(a, b)), realDivT(realSgnT(a), realSgnT(b)))
	}
	if a, n, ok := MatchesRealPow(x); ok { // sgn(a pow n) = sgn a pow n
		return realEqLeaf(realSgnPowThm(), []Term{a, n},
			realSgnT(realPowT(a, n)), realPowT(realSgnT(a), n))
	}
	return nil
}

// realInvSimp folds one inv algebraic redex at t's head, or nil when t is not
// such a redex. The inv twin of realAbsSgnSimp: pushes real_inv toward the leaves
// over operator structure, so `inv(x·y) = inv x·inv y` and `inv(inv x) = x` close
// as reflexivity after normalization. Every fold strictly shrinks (InvInv) or
// pushes inv past one operator (InvMul/InvNeg/InvDiv), so the DeepRewrite fixpoint
// converges. Unconditional (the `inv &0 = &0` convention). The fold
// only fires on inv of a COMPOUND
// argument (product / inv / neg / div); a bare `inv(variable)` is left for the
// field handler. The `inv &1 → &1` fold is handled separately in realArithSimpStep.
func realInvSimp(t Term) *prop.PropWrapper {
	x, ok := MatchesRealInv(t)
	if !ok {
		return nil
	}
	if a, ok := MatchesRealInv(x); ok { // inv(inv a) = a
		return realEqLeaf(realInvInvThm(), []Term{a}, realInvT(realInvT(a)), a)
	}
	if a, b, ok := realDomain.matchStar(x); ok { // inv(a·b) = inv a · inv b
		return realEqLeaf(realInvMulThm(), []Term{a, b},
			realInvT(realStarT(a, b)), realStarT(realInvT(a), realInvT(b)))
	}
	if a, ok := MatchesRealNeg(x); ok { // inv(−a) = −(inv a)
		return realEqLeaf(realInvNegThm(), []Term{a}, realInvT(realNegT(a)), realNegT(realInvT(a)))
	}
	if a, b, ok := MatchesRealDiv(x); ok { // inv(a/b) = b/a
		return realEqLeaf(realInvDivThm(), []Term{a, b}, realInvT(realDivT(a, b)), realDivT(b, a))
	}
	if a, n, ok := MatchesRealPow(x); ok { // inv(a pow n) = inv a pow n
		return realEqLeaf(realInvPowThm(), []Term{a, n},
			realInvT(realPowT(a, n)), realPowT(realInvT(a), n))
	}
	return nil
}

// realInvSignSimp folds an inv-rooted comparison atom — `&0 < inv x` → `&0 < x`,
// `&0 ≤ inv x` → `&0 ≤ x`, `inv x = &0` → `x = &0` — at t's head, or nil otherwise.
// The dual to realFlipNeg: sign is PRESERVED through inv (the `sgn(0)=0`
// convention makes the iff hold at the degenerate point), via InvPos /
// InvNonneg / InvEqZero. Without these the linarith atomization of
// `inv x` blocks any sign/nonzero reasoning on inv. A comparison is matched
// with `&0` on the left; an equation with `&0` on either side (zeroSidedEq).
func realInvSignSimp(t Term) *prop.PropWrapper {
	if a, b, ok := realDomain.matchLt(t); ok && isRealZero(a) {
		if x, ok := MatchesRealInv(b); ok { // (&0 < inv x) ⇔ (&0 < x)
			return realEqLeaf(realInvPosThm(), []Term{x},
				realLtT(realLit(0), realInvT(x)), realLtT(realLit(0), x))
		}
	}
	if a, b, ok := realDomain.matchLe(t); ok && isRealZero(a) {
		if x, ok := MatchesRealInv(b); ok { // (&0 ≤ inv x) ⇔ (&0 ≤ x)
			return realEqLeaf(realInvNonnegThm(), []Term{x},
				realLeT(realLit(0), realInvT(x)), realLeT(realLit(0), x))
		}
	}
	if l, turned, ok := zeroSidedEq(t, isRealZero); ok {
		return afterTurn(turned, realZeroTestFold(l))
	}
	// SquarePos's goal-only direction (`~(x=&0) → &0 < x·x`) is split into
	// realSquarePosSimp — see its docstring for why hyp pre-simp must skip it.
	return nil
}

// realZeroTestFold carries the zero test `l = &0` through l's head: `⊢ (inv
// x = &0) ⇔ (x = &0)` (InvEqZero) or `⊢ (−x = &0) ⇔ (x = &0)` (NegEqZero);
// nil for any other l.
func realZeroTestFold(l Term) *prop.PropWrapper {
	if x, ok := MatchesRealInv(l); ok {
		return realEqLeaf(realInvEqZeroThm(), []Term{x},
			eqT(realInvT(x), realLit(0)), eqT(x, realLit(0)))
	}
	if x, ok := MatchesRealNeg(l); ok {
		return realEqLeaf(realNegEqZeroThm(), []Term{x},
			eqT(realNegT(x), realLit(0)), eqT(x, realLit(0)))
	}
	return nil
}

// realSquarePosSimp is SquarePos's goal-only direction `~(x = &0) → &0 < x·x`
// — derives nonzeroness from a square positivity hyp, the iff side
// realProveStrictSquare doesn't carry. DELIBERATELY EXCLUDED from hyp pre-simp
// (realArithSimpStepHypSafe): rewriting a hyp `z ≠ &0` into `&0 < z·z` destroys
// the canonical nonzero shape that the field handler's unknown-sign-split
// (realProveDivField) and the sign-of-product handlers (realProveSignedProduct)
// consume — the same shape of regression d9350352 calls out for intMoveAcrossLeaf
// (the symmetry `~(eq)` ↔ a richer equivalent term cuts both ways). Goal side
// still closes goals of form `x ≠ &0` against a `&0 < x·x` hyp.
//
// The reverse direction (`&0 < x·x → ~(x=&0)`) is redundant: realProveStrictSquare
// already proves `&0 < x·x` from a `~(x=&0)` hyp directly. The equation is
// matched with `&0` on either side (zeroSidedEq).
//
// The square is taken of the term the zero test's own folds leave: under an
// inverse or a negation the equation is realInvSignSimp's first (`−x = &0`
// to `x = &0`), and the leaf declines until it has been. `&0 < (−x)·(−x)` is
// a square no handler reads through the negation.
func realSquarePosSimp(t Term) *prop.PropWrapper {
	inner := ext.MatchesNOT(t)
	if inner == nil {
		return nil
	}
	l, turned, ok := zeroSidedEq(inner, isRealZero)
	if !ok || !isRealTerm(l) || realZeroTestFold(l) != nil {
		return nil
	}
	fold := realEqLeaf(realSquarePosThm(), []Term{l},
		prop.Not(eqT(l, realLit(0))), realLtT(realLit(0), realStarT(l, l)))
	if turned == nil || fold == nil {
		return fold
	}
	return turned.LeftApply(prop.NOT).EqTrans(fold) // ¬(&0 = l) ⇔ ¬(l = &0) ⇔ &0 < l·l
}

// realAbsLessEqIffPowTwoLessEqSimp folds a square-ordering atom `x pow 2 ≤ y pow 2` to the
// abs-ordering form `|x| ≤ |y|` via AbsLessEqIffPowTwoLessEq. Goal-side direction —
// pushes toward the canonical LHS form (`abs(x) ≤ abs(y)`). Composes
// with SquareOfAbs (`|x|^2 → x^2`): a goal `|x|^2 ≤ |y|^2` strips abs first via
// SquareOfAbs to `x^2 ≤ y^2`, then this simp converts to `|x| ≤ |y|`; the cascade
// terminates since neither produces the other's input shape. Only fires for the
// literal exponent &2 (the lemma is square-specific; the general `x^n ≤ y^n`
// monotonicity is realProvePowBaseMono / PowMonoBase below).
func realAbsLessEqIffPowTwoLessEqSimp(t Term) *prop.PropWrapper {
	l, r, ok := realDomain.matchLe(t)
	if !ok {
		return nil
	}
	xb, xe, okx := MatchesRealPow(l)
	if !okx || !xe.AlphaEquals(Numeral(2)) {
		return nil
	}
	yb, ye, oky := MatchesRealPow(r)
	if !oky || !ye.AlphaEquals(Numeral(2)) {
		return nil
	}
	return realEqLeaf(realAbsLessEqIffPowTwoLessEqThm(), []Term{xb, yb},
		realLeT(realPowT(xb, Numeral(2)), realPowT(yb, Numeral(2))),
		realLeT(realAbsT(xb), realAbsT(yb)))
}

// realPowLawSimp folds `(base) pow n` when base is a compound — the BASE-side
// dual of InvPow / AbsPow (which push the unary op past pow). MulPowDistrib /
// DivPow distribute pow over the product / quotient; PowPow flattens
// nested pow into a single pow with NUM-multiplied exponents (`m·n` is num multiplication,
// shared with the nat layer's `star`); OnePow collapses a `&1` base. All
// unconditional. Strict-decrease termination: distribution
// pushes pow one operator inward; PowPow shrinks two pow nodes to one; OnePow
// removes pow entirely. The literal-exp unfold (realPowSimp) handles the nat_pow side
// independently — both fold layers converge to the same fixpoint.
func realPowLawSimp(t Term) *prop.PropWrapper {
	base, exp, ok := MatchesRealPow(t)
	if !ok {
		return nil
	}
	// abs x pow 2 = x pow 2 (SquareOfAbs) — fires only for literal exponent &2.
	// Strict size-reduce (removes abs); placed first so it pre-empts PowLaw's
	// generic clauses on the same abs-base shape.
	if a, ok := MatchesRealAbs(base); ok && exp.AlphaEquals(Numeral(2)) {
		return realEqLeaf(realSquareOfAbsThm(), []Term{a},
			realPowT(realAbsT(a), Numeral(2)), realPowT(a, Numeral(2)))
	}
	if isRealOne(base) { // &1 pow n = &1
		return realEqLeaf(realOnePowThm(), []Term{exp},
			realPowT(realLit(1), exp), realLit(1))
	}
	if a, b, ok := realDomain.matchStar(base); ok { // (a·b) pow n = a^n · b^n
		return realEqLeaf(realMulPowDistribThm(), []Term{a, b, exp},
			realPowT(realStarT(a, b), exp),
			realStarT(realPowT(a, exp), realPowT(b, exp)))
	}
	if a, b, ok := MatchesRealDiv(base); ok { // (a/b) pow n = a^n / b^n
		return realEqLeaf(realDivPowThm(), []Term{a, b, exp},
			realPowT(realDivT(a, b), exp),
			realDivT(realPowT(a, exp), realPowT(b, exp)))
	}
	if a, m, ok := MatchesRealPow(base); ok { // (a pow m) pow n = a pow (m·n)
		return realEqLeaf(realPowPowThm(), []Term{a, m, exp},
			realPowT(realPowT(a, m), exp), realPowT(a, star(m, exp)))
	}
	return nil
}

// The real_of_num homomorphism collapse — the ℝ twin of the int_of_num collapse
// (int.go intOfNumNormalize / intProveOfNum). `&n` (n a num *variable*) is opaque
// to linarith (real vars carry no default bound) and the ring atomizes it, so
// neither sees `&n·&n = &(n·n)` nor `&0 ≤ &n`. This collapses a real term whose
// leaves are `&`-coerced nums (combined by real_neg / real_mul / same-sign
// real_add) to a SIGNED num image `±&(num expr)`, running the OfNumAdd/OfNumMul
// homomorphism as proof rewrites (over arbitrary num args, not just literals) and
// tracking the sign through MulRightNeg / NegNeg.
//
// The decide hook realProveOfNum:
//   - an `=` goal closes when both sides collapse to the same signed image (the
//     of_num twin of RealRingProveFull, which atomizes `&n` and can't see it);
//   - a `≤` / `<` goal whose sides are NONNEGATIVE images drops to the num
//     comparison via OfNumLessEq/OfNumLessThan, closed by num's default-nonneg bound — so
//     `&0 ≤ &n·&n` reduces to `0 ≤ n·n`, and the bare `&0 ≤ &n` to `0 ≤ n`.
//
// Sign-mixed addition declines (it is real subtraction — the signed normalizer's
// linear job, not this). Reuses the bundle's OfNumAdd/OfNumMul/OfNumLessEq/OfNumLessThan/
// OfNumEq + the signed-normalizer's Neg{Neg,Rmul} leaves — no new bundle field.

// Notation in the comments below: `realSignWrap(neg, x)` denotes −x when neg,
// else x (the ℝ twin of `signWrap`). Used purely as a symbolic shorthand — the
// actual term construction inlines to realNegT(x) / x at each call site.

// realLiftUnderSign lifts ⊢ A = B to ⊢ signWrap(neg,A) = signWrap(neg,B). Twin of
// liftUnderSign.
func realLiftUnderSign(neg bool, w *prop.PropWrapper) *prop.PropWrapper {
	if neg {
		return w.LeftApply(realNeg)
	}
	return w
}

// realOfNumNormalize reduces t to (neg, u, ⊢ t = realSignWrap(neg, &u)), u a num
// term, when every leaf is real_of_num and the structure is real_neg / real_mul /
// same-sign real_add. ok=false otherwise (t is left for the other leaves). Mirror
// of intOfNumNormalize.
func realOfNumNormalize(t Term) (neg bool, u Term, w *prop.PropWrapper, ok bool) {
	if m, isOfNum := MatchesRealOfNum(t); isOfNum {
		return false, m, prop.Refl(t), true // &m = realSignWrap(false, &m)
	}
	if a, isNeg := MatchesRealNeg(t); isNeg {
		na, ua, wa, okA := realOfNumNormalize(a)
		if !okA {
			return false, nil, nil, false
		}
		inner := wa.LeftApply(realNeg) // ⊢ −a = −(realSignWrap(na, &ua))
		if !na {                       // a = &ua ⇒ −a = realSignWrap(true, &ua)
			return true, ua, inner, true
		}
		// na: a = −&ua ⇒ −a = −(−&ua) = &ua  (NegNeg)
		nn := realSubneg.negNeg(realOfNumT(ua)) // ⊢ −(−&ua) = &ua
		return false, ua, inner.EqTrans(nn), true
	}
	if l, r, isMul := realDomain.matchStar(t); isMul {
		nl, ul, wl, okl := realOfNumNormalize(l)
		nr, ur, wr, okr := realOfNumNormalize(r)
		if !okl || !okr {
			return false, nil, nil, false
		}
		cong := wl.LeftApply(realStar).Apply(wr) // ⊢ l·r = sw(nl,&ul)·sw(nr,&ur)
		sx, resNeg := realMulSignExtract(nl, realOfNumT(ul), nr, realOfNumT(ur))
		bridge := realOfNumMulLeaf(ul, ur)          // ⊢ &ul·&ur = &(ul·ur)
		lifted := realLiftUnderSign(resNeg, bridge) // under the result sign
		return resNeg, star(ul, ur), cong.EqTrans(sx).EqTrans(lifted), true
	}
	if l, r, isAdd := realDomain.matchPlus(t); isAdd {
		nl, ul, wl, okl := realOfNumNormalize(l)
		nr, ur, wr, okr := realOfNumNormalize(r)
		if !okl || !okr || nl != nr {
			return false, nil, nil, false // sign-mixed add = subtraction: decline
		}
		lu, ru := realOfNumT(ul), realOfNumT(ur)
		cong := wl.LeftApply(realPlus).Apply(wr) // ⊢ l+r = sw(nl,&ul)+sw(nr,&ur)
		bridge := realOfNumAddLeaf(ul, ur)       // ⊢ &ul+&ur = &(ul+ur)
		if !nl {
			return false, plus(ul, ur), cong.EqTrans(bridge), true
		}
		// both neg: (−&ul)+(−&ur) = −(&ul+&ur) [NegAdd, reversed] = −&(ul+ur)
		negAdd := realSubneg.negAdd(lu, ru).EqSym() // ⊢ (−&ul)+(−&ur) = −(&ul+&ur)
		lifted := bridge.LeftApply(realNeg)         // ⊢ −(&ul+&ur) = −&(ul+ur)
		return true, plus(ul, ur), cong.EqTrans(negAdd).EqTrans(lifted), true
	}
	return false, nil, nil, false
}

// realMulSignExtract proves ⊢ sw(nl,lu)·sw(nr,ru) = sw(nl⊕nr, lu·ru), pushing the
// negations out of a product via MulRightNeg (+ its derived left-factor twin, NegNeg). Mirror of
// intMulSignExtract.
func realMulSignExtract(nl bool, lu Term, nr bool, ru Term) (*prop.PropWrapper, bool) {
	switch {
	case !nl && !nr: // lu·ru
		return prop.Refl(realStarT(lu, ru)), false
	case !nl && nr: // lu·(−ru) = −(lu·ru)
		return realSubneg.mulRightNeg(lu, ru), true
	case nl && !nr: // (−lu)·ru = −(lu·ru)
		return realMulLnegProof(lu, ru), true
	default: // (−lu)·(−ru) = lu·ru
		step1 := realSubneg.mulRightNeg(realNegT(lu), ru)    // (−lu)·(−ru) = −((−lu)·ru)
		step2 := realMulLnegProof(lu, ru).LeftApply(realNeg) // −((−lu)·ru) = −(−(lu·ru))
		step3 := realSubneg.negNeg(realStarT(lu, ru))        // −(−(lu·ru)) = lu·ru
		return step1.EqTrans(step2).EqTrans(step3), false
	}
}

// realMulLnegProof: ⊢ (−a)·b = −(a·b), derived (the bundle carries only the
// MulRightNeg form): (−a)·b = b·(−a) [MulSym] = −(b·a) [MulRightNeg] = −(a·b) [MulSym under neg]. Mirror of
// intMulLnegProof.
func realMulLnegProof(a, b Term) *prop.PropWrapper {
	return realCommuteMUL(realNegT(a), b). // (−a)·b = b·(−a)
						EqTrans(realSubneg.mulRightNeg(b, a)).           // = −(b·a)
						EqTrans(realCommuteMUL(b, a).LeftApply(realNeg)) // = −(a·b)
}

// realOfNumMulLeaf: ⊢ &a·&b = &(a·b)   (OfNumMul, the homomorphism).
func realOfNumMulLeaf(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realOfNumMulThm(), []Term{a, b}, realStarT(realOfNumT(a), realOfNumT(b)), realOfNumT(star(a, b)))
}

// realOfNumAddLeaf: ⊢ &a+&b = &(a+b)   (OfNumAdd).
func realOfNumAddLeaf(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realOfNumAddThm(), []Term{a, b}, realPlusT(realOfNumT(a), realOfNumT(b)), realOfNumT(plus(a, b)))
}

// realProveOfNum closes a comparison/equality goal whose sides are real_of_num
// images (mirror of intProveOfNum). Hyp-free: the num facts the context
// holds reach a real refutation as ROWS over the images (domain.go liftHyp),
// so `a ≤ b ⊢ &a ≤ &b` is the linear layer's; this drop serves what a row
// cannot, `&0 ≤ &n·&n` and `&n·&n = &(n·n)`. Hyp-free on purpose: the arith
// step drops a hypothesis decided ⊤ under the others, and a comparison of
// images decided from num facts the rows do not hold would take with it what
// the refutation still needs (measured on real_trigonometry.CosTaylorBounds,
// whose divisor's bound `&4 ≤ &n` was decided away from under the field
// handler). ok=false on any non-collapsing or (for `≤`/`<`) negative-sided
// shape.
func realProveOfNum(goal Term) (*prop.PropWrapper, bool) {
	// Equality: collapse both sides; close if their signed images coincide,
	// else — both nonnegative — as the num equality under the num facts.
	if l, r, ok := ext.MatchesEQ(goal); ok && isRealTerm(l) {
		nl, _, wl, okl := realOfNumNormalize(l)
		nr, _, wr, okr := realOfNumNormalize(r)
		if !okl || !okr {
			return nil, false
		}
		if nl == nr && prop.Rhs(wl).AlphaEquals(prop.Rhs(wr)) {
			return wl.EqTrans(wr.EqSym()), true // ⊢ l = signWrap = r
		}
		if nl || nr {
			return nil, false
		}
		return realDropCmp(l, r, eqConstOf(l), eqT, realOfNumEqThm())
	}
	// `≤` / `<`: drop two nonnegative images to the num comparison.
	if l, r, ok := realDomain.matchLe(goal); ok {
		return realDropCmp(l, r, realLe, le, realOfNumLessEqThm())
	}
	if l, r, ok := realDomain.matchLt(goal); ok {
		return realDropCmp(l, r, realLt, lt, realOfNumLessThanThm())
	}
	return nil, false
}

// realDropCmp proves ⊢ (l ⋈ r) when l,r are NONNEGATIVE real_of_num images: collapse
// each to `&uL`,`&uR`, rewrite the relation, drop to the num goal `uL ⋈ uR` via the
// OfNum* bridge, and close it with the num prover. ok=false if a side is
// negative / non-collapsing or the num goal does not close. Mirror of intDropCmp.
func realDropCmp(l, r, relConst Term, numRel func(a, b Term) Term, bridgeThm *prop.PropWrapper) (*prop.PropWrapper, bool) {
	nl, ul, wl, okl := realOfNumNormalize(l)
	nr, ur, wr, okr := realOfNumNormalize(r)
	if !okl || !okr || nl || nr { // need both sides nonnegative
		return nil, false
	}
	numGoal := numRel(ul, ur)
	numW, ok := LinProve(slices.Values([]Term(nil)), numGoal) // ⊢ uL ⋈ uR  (num)
	if !ok {
		return nil, false
	}
	cong := wl.LeftApply(relConst).Apply(wr)                                 // ⊢ (l ⋈ r) = (&uL ⋈ &uR)
	bridge := realEqLeaf(bridgeThm, []Term{ul, ur}, prop.Rhs(cong), numGoal) // ⊢ (&uL ⋈ &uR) ⇔ (uL ⋈ uR)
	return cong.EqTrans(bridge).EqSym().EqMP(numW), true                     // ⊢ (l ⋈ r)
}

// eqConstOf is the equality constant at the type of t — the operator of the
// equation `t = t` — for a congruence under `=` (LeftApply wants the term).
func eqConstOf(t Term) Term {
	head, _ := ext.MatchesApply(core.Eq(t, t))
	return head
}

// realLiftNumHyp is realDomain.liftHyp: a num comparison hypothesis read
// as its real image through the OfNum* bridges.
func realLiftNumHyp(h Term) []*prop.PropWrapper {
	return liftNumHyp(h, realOfNumT, realLeT, realLtT, realOfNumLessEqThm, realOfNumLessThanThm, realOfNumEqThm, realEqLeaf,
		realOfNumAddLeaf, realOfNumMulLeaf)
}

// liftNumHyp is the shared lift behind realLiftNumHyp and intLiftNumHyp:
// `{h} ⊢ A ⋈ B` for h = `a ⋈ b` over num — ≤, <, = as written, ≥ and >
// through the num bridge to the swapped comparison — from the domain's
// `(img(a) ⋈ img(b)) ⇔ (a ⋈ b)` theorem (the bundle's OfNumLessEq / OfNumLessThan /
// OfNumEq, bound in production), the cast pushed to the leaves on both
// sides (pushCast: `img(a + 1)` is `img(a) + img(1)`, so the row meets the
// atoms the refutation reads), and for a strict h the second row
// `{h} ⊢ A + img(1) ≤ B`: a < b over num is suc a ≤ b (SucLessEqIffLessThan) and suc a
// is a + 1 — the integrality a refutation over the images cannot see
// otherwise. nil for any other h.
func liftNumHyp(h Term, img func(Term) Term, leT, ltT func(a, b Term) Term,
	leThm, ltThm, eqThm func() *prop.PropWrapper,
	leaf func(thm *prop.PropWrapper, args []Term, lhs, rhs Term) *prop.PropWrapper,
	addLeaf, mulLeaf func(a, b Term) *prop.PropWrapper) []*prop.PropWrapper {
	base := prop.Assume(h) // {h} ⊢ h
	var a, b Term
	strict := false
	var rel func(a, b Term) Term
	var numRel func(a, b Term) Term
	var thm *prop.PropWrapper
	switch {
	case func() bool { var ok bool; a, b, ok = MatchesLe(h); return ok && isNat(a) }():
		rel, numRel, thm = leT, le, leThm()
	case func() bool { var ok bool; a, b, ok = MatchesLt(h); return ok && isNat(a) }():
		rel, numRel, thm, strict = ltT, lt, ltThm(), true
	case func() bool { var ok bool; a, b, ok = MatchesGe(h); return ok && isNat(a) }():
		base = geBridge(a, b).EqMP(base) // {h} ⊢ b ≤ a
		a, b = b, a
		rel, numRel, thm = leT, le, leThm()
	case func() bool { var ok bool; a, b, ok = MatchesGt(h); return ok && isNat(a) }():
		base = gtBridge(a, b).EqMP(base) // {h} ⊢ b < a
		a, b = b, a
		rel, numRel, thm, strict = ltT, lt, ltThm(), true
	case func() bool { var ok bool; a, b, ok = ext.MatchesEQ(h); return ok && isNat(a) }():
		rel, numRel, thm = eqT, eqT, eqThm()
	default:
		return nil
	}
	// imageRow turns `{…} ⊢ x ⋈ y` over num into `{…} ⊢ X ⋈ Y` over the
	// images, the cast pushed to the leaves.
	imageRow := func(w *prop.PropWrapper, x, y Term, rel, numRel func(a, b Term) Term, thm *prop.PropWrapper) *prop.PropWrapper {
		bridge := leaf(thm, []Term{x, y}, rel(img(x), img(y)), numRel(x, y)) // ⊢ (img x ⋈ img y) ⇔ (x ⋈ y)
		row := bridge.EqSym().EqMP(w)                                        // {…} ⊢ img x ⋈ img y
		head, _ := ext.MatchesApply(rel(img(x), img(y)))
		px, py := pushCast(x, img, addLeaf, mulLeaf), pushCast(y, img, addLeaf, mulLeaf)
		return px.LeftApply(head).Apply(py).EqMP(row) // {…} ⊢ X ⋈ Y
	}
	rows := []*prop.PropWrapper{imageRow(base, a, b, rel, numRel, thm)}
	if strict {
		sucLe := base.DeriveTrans(sucLessEqIffLessThan(a, b).LeftAssume()) // {h} ⊢ suc a ≤ b
		leHead, _ := ext.MatchesApply(le(a, b))
		plusOne := sucAdd1(a).LeftApply(leHead).RightApply(b).EqMP(sucLe) // {h} ⊢ a + 1 ≤ b
		rows = append(rows, imageRow(plusOne, plus(a, Numeral(1)), b, leT, le, leThm()))
	}
	return rows
}

// pushCast proves `⊢ img(t) = T` with the cast pushed through the sums and
// products of the num term t to its leaves (OfNumAdd / OfNumMul read right
// to left); a leaf is its own image.
func pushCast(t Term, img func(Term) Term, addLeaf, mulLeaf func(a, b Term) *prop.PropWrapper) *prop.PropWrapper {
	if l, r, ok := MatchesPlus(t); ok {
		split := addLeaf(l, r).EqSym() // ⊢ img(l + r) = img l + img r
		head, _ := ext.MatchesApply(prop.Rhs(split))
		return split.EqTrans(pushCast(l, img, addLeaf, mulLeaf).LeftApply(head).Apply(pushCast(r, img, addLeaf, mulLeaf)))
	}
	if l, r, ok := MatchesStar(t); ok {
		split := mulLeaf(l, r).EqSym() // ⊢ img(l · r) = img l · img r
		head, _ := ext.MatchesApply(prop.Rhs(split))
		return split.EqTrans(pushCast(l, img, addLeaf, mulLeaf).LeftApply(head).Apply(pushCast(r, img, addLeaf, mulLeaf)))
	}
	return prop.Refl(img(t))
}
