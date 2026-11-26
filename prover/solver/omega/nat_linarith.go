package omega

import (
	"iter"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// linarith certificate replay: replay a Farkas certificate (from refute) as a real refutation
// proof `{h₁ … hₙ} ⊢ ⊥`. Scale each active hypothesis inequality by its λ,
// sum them pairwise, ring-normalize both sides to `P + cL ⋈ P + cR` (the var
// part P cancels by Farkas), cancel P, and close on the numerically false
// constant relation `cL ⋈ cR` via norm_num. The leaves read the NatLemmaBundle
// (below); the composition here is real kernel work.

// mp applies an implication theorem (⊢ A ⇒ B) to a proof of A, yielding B,
// threading A's hypotheses through.
func mp(impl, arg *prop.PropWrapper) *prop.PropWrapper {
	return arg.DeriveTrans(impl.DemoteHyp())
}

// canonAssume returns `{prov} ⊢ (lhs op rhs)` for op ∈ {opLE, opLT}. With hyp nil
// it assumes the canonical comparison directly; with hyp set (a `>`/`≥` origin,
// whose lhs/rhs are already the swapped operands) it assumes the original term
// and bridges it — `rhs > lhs ⟝ lhs < rhs` (resp `≥`/`≤`) — via gt/geBridge, so
// the carried hypothesis is the original `>`/`≥` term, not the rebuilt `<`/`≤`.
//
// base, when non-nil, replaces the default `prop.Assume(...)` of the assumption
// term (the canonical comparison for hyp nil, else the `>`/`≥` term): it proves
// the same term but from arbitrary provenance hyps (a conjunction projection),
// keeping the proof's hyps a subset of the goal's. nil ⇒ build the Assume.
func canonAssume(lhs, rhs Term, op relOp, hyp Term, base *prop.PropWrapper) *prop.PropWrapper {
	if hyp == nil {
		if base != nil {
			return base // proves the canonical lhs op rhs already
		}
		if op == opLT {
			return prop.Assume(lt(lhs, rhs))
		}
		return prop.Assume(le(lhs, rhs))
	}
	if base == nil {
		base = prop.Assume(hyp)
	}
	if op == opLT {
		return gtBridge(rhs, lhs).EqMP(base) // ⊢ (rhs>lhs)=(lhs<rhs)
	}
	return geBridge(rhs, lhs).EqMP(base) // ⊢ (rhs≥lhs)=(lhs≤rhs)
}

// assumeEq is the EQ-row analog of canonAssume's base handling: the precomputed
// HypProof (a conjunction projection `{p∧q} ⊢ (a=b)`) when set, else a plain
// `Assume(a=b)`.
func (c LinConstraint) assumeEq() *prop.PropWrapper {
	if c.HypProof != nil {
		return c.HypProof
	}
	return prop.Assume(eqT(c.Lhs, c.Rhs))
}

// provRow is an expanded row's two-sided inequality `L ⋈ R` plus a deferred
// builder for its theorem provenance. FM operates only on the numeric rows;
// replay invokes build only for rows whose final certificate has lambda[j] > 0.
// Thus failed searches and unused input rows never materialize their row proof
// beyond any HypProof that the caller had already supplied.
type provRow struct {
	L, R   Term
	strict bool
	build  func() (*prop.PropWrapper, bool)
}

// lazyProvRow adapts the common infallible proof builders to provRow's fallible
// contract. Genuine integer cuts use the contract directly because an absent
// bundle theorem may make their builder decline.
func lazyProvRow(L, R Term, strict bool, build func() *prop.PropWrapper) provRow {
	return provRow{L: L, R: R, strict: strict, build: func() (*prop.PropWrapper, bool) {
		return build(), true
	}}
}

// proof materializes a row's provenance. (nil, false) means the builder
// declined; replay then rejects the refutation rather than fabricating a row.
// It is intentionally not memoized: replay touches each row at most once.
func (pr provRow) proof() (*prop.PropWrapper, bool) {
	if pr.build != nil {
		return pr.build()
	}
	return nil, false
}

// buildAll mirrors buildRows but also produces, index-aligned, the provenance
// of every expanded row (hyp assumption / EQ→LE / 0≤x).
func buildAll(cs []LinConstraint) (*atomTable, []row, []provRow, bool) {
	tbl := &atomTable{}
	var signed []row
	var prs []provRow
	for _, c := range cs {
		rs, ok := extractRow(tbl, c)
		if !ok {
			return nil, nil, nil, false
		}
		signed = append(signed, rs...)
		switch c.Op {
		case opLE:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return canonAssume(c.Lhs, c.Rhs, opLE, c.Hyp, c.HypProof)
			}))
		case opLT:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, true, func() *prop.PropWrapper {
				return canonAssume(c.Lhs, c.Rhs, opLT, c.Hyp, c.HypProof)
			}))
		case opEQ:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return mp(lessEqOfEq(c.Lhs, c.Rhs), c.assumeEq())
			}))
			prs = append(prs, lazyProvRow(c.Rhs, c.Lhs, false, func() *prop.PropWrapper {
				return mp(lessEqOfEqSwapped(c.Lhs, c.Rhs), c.assumeEq())
			}))
		}
	}
	for i := 0; i < tbl.n(); i++ {
		x := tbl.atoms[i]
		signed = append(signed, unitRow(tbl.n(), i, integerOf(-1)))
		prs = append(prs, lazyProvRow(Numeral(0), x, false, func() *prop.PropWrapper {
			return zeroLe(x)
		}))
	}
	for i := range signed {
		signed[i] = signed[i].padCoeffs(tbl.n())
	}
	return tbl, signed, prs, true
}

// scaledIneq is `L ⋈ R` with its proof, during the summation fold.
type scaledIneq struct {
	ineq   *prop.PropWrapper
	L, R   Term
	strict bool
}

// addLemma picks the inequality-addition lemma for the strictness combination,
// instantiated at (A,B,C,D).
func addLemma(accStrict, itStrict bool, a, b, c, d Term) *prop.PropWrapper {
	switch {
	case !accStrict && !itStrict:
		return addLe2(a, b, c, d)
	case accStrict && itStrict:
		return addLt2(a, b, c, d)
	case accStrict && !itStrict:
		return addLtLe(a, b, c, d)
	default:
		return addLeLt(a, b, c, d)
	}
}

// sumRows adds the rows of prs that λ takes, each scaled by its multiplier,
// into one inequality `hyps ⊢ accL ⋈ accR`, strict when a row taken is. It
// materializes each used row's proof on demand via pr.proof(), so a row with
// lambda=0 never builds its theorem provenance. ok=false if λ takes no row
// or a lazy build declines (a cut row whose proof is unsupported under the
// current bundle).
func sumRows(prs []provRow, lambda []_Integer) (acc scaledIneq, ok bool) {
	var items []scaledIneq
	for j, lam := range lambda {
		if lam.sign() <= 0 {
			continue
		}
		pr := prs[j]
		prov, ok := pr.proof()
		if !ok {
			return scaledIneq{}, false // a needed lazy cut proof is unsupported
		}
		if lam.isOne() {
			items = append(items, scaledIneq{prov, pr.L, pr.R, pr.strict})
			continue
		}
		var sc *prop.PropWrapper
		if pr.strict {
			sc = mp(ltScale(lam, pr.L, pr.R), prov)
		} else {
			sc = mp(leScale(lam, pr.L, pr.R), prov)
		}
		c := numeralOf(lam)
		items = append(items, scaledIneq{sc, star(c, pr.L), star(c, pr.R), pr.strict})
	}
	if len(items) == 0 {
		return scaledIneq{}, false
	}
	acc = items[0]
	for _, it := range items[1:] {
		lem := addLemma(acc.strict, it.strict, acc.L, acc.R, it.L, it.R)
		comb := mp(mp(lem, acc.ineq), it.ineq)
		acc = scaledIneq{comb, plus(acc.L, it.L), plus(acc.R, it.R), acc.strict || it.strict}
	}
	return acc, true
}

// replay turns a Farkas certificate λ over prs into `hyps ⊢ ⊥`: the rows
// summed (sumRows), the sum's two sides normalized, their common variable
// part cancelled, and the constant relation left evaluated to false.
// (nil, false) if a lazy build declines.
func replay(prs []provRow, lambda []_Integer) (*prop.PropWrapper, bool) {
	acc, ok := sumRows(prs, lambda)
	if !ok {
		return nil, false
	}

	// ring-normalize both sides: accL = toTerm(lfL), accR = toTerm(lfR).
	lfL, wL, _ := natRing.normalizeProof(acc.L)
	lfR, wR, _ := natRing.normalizeProof(acc.R)
	PL := lfL.toTerm()
	PR := lfR.toTerm()

	opC := natLe
	if acc.strict {
		opC = natLt
	}
	// ⊢ (accL ⋈ accR) = (PL ⋈ PR)
	cong := wL.LeftApply(opC).RightApply(acc.R).
		EqTrans(wR.LeftApply(ext.Apply(opC, PL)))
	transported := cong.EqMP(acc.ineq) // hyps ⊢ (PL ⋈ PR)

	// cancel the common variable part, leaving a constant relation cL ⋈ cR.
	var cmpProof *prop.PropWrapper
	var cL, cR Term
	if len(lfL.monos) > 0 {
		P := natRing.monoChainTerm(lfL.monos)
		cL = numeralOf(lfL.konst)
		cR = numeralOf(lfR.konst)
		var cancel *prop.PropWrapper
		if acc.strict {
			cancel = addLcancelLt(P, cL, cR)
		} else {
			cancel = addLcancelLe(P, cL, cR)
		}
		cmpProof = cancel.EqMP(transported) // hyps ⊢ (cL ⋈ cR)
	} else {
		cmpProof = transported
		cL, cR = PL, PR // both Numeral(konst)
	}

	// norm_num: the constant relation is numerically false ⇒ ⊥.
	var g4 *prop.PropWrapper
	if acc.strict {
		g4, ok = NormNatLt(cL, cR)
	} else {
		g4, ok = NormNatLe(cL, cR)
	}
	if !ok || !prop.Rhs(g4).Equals(prop.F) {
		return nil, false // certificate did not yield a false constant relation
	}
	return g4.EqMP(cmpProof), true // hyps ⊢ ⊥
}

// LinRefuteProof decides unsatisfiability and, on success, returns a real
// refutation `{h₁ … hₙ} ⊢ ⊥` (the constraint terms appear as hypotheses).
// ok=false ⇒ nonlinear input or not ℚ-Farkas refutable.
func LinRefuteProof(cs []LinConstraint) (*prop.PropWrapper, bool) {
	tbl, signed, prs, built := buildAll(cs)
	if !built {
		return nil, false
	}
	lambda, ok := refute(tbl.n(), signed)
	if !ok {
		return nil, false
	}
	return replay(prs, lambda)
}

// Leaves for the linarith certificate replay (monotone scaling, inequality addition,
// cancellation, EQ/0 facts). Each binds the bundle's named theorem instantiated
// to the stated shape; a nil bundle field degrades to a placeholder stand-in
// (bundle.go), which panics in a non-test build (no fabricator). The replay
// COMPOSITION is
// real kernel work. Real names: LessEqMulMono-class, LessEqAdd2/LessThanAdd2/LessThanLessEqAdd2/
// LessEqLessThanAdd2, LessEqAddCancel/LessThanAddCancel, LessEqOfEq, ZeroLessEq.

func imply(a, b Term) Term { return ext.Apply(prop.IMPLY, a, b) }
func not(a Term) Term      { return ext.Apply(prop.NOT, a) }
func or(a, b Term) Term    { return ext.Apply(prop.OR, a, b) }

// ── goal-negation duality (used by LinProve) ──────────────

// Each leaf is the bundle's named theorem instantiated (and oriented, for the
// iff ones) to the stated shape, else the placeholder.

// notLT: ⊢ ¬(M<N) ⇔ (N≤M)   (real: NotLessThan, `~(m<n) <=> n<=m`)
func notLT(m, n Term) *prop.PropWrapper {
	return eqLeaf(notLessThanThm(), []Term{m, n}, not(lt(m, n)), le(n, m))
}

// notLE: ⊢ ¬(M≤N) ⇔ (N<M)   (real: NotLessEq, `~(m<=n) <=> n<m`)
func notLE(m, n Term) *prop.PropWrapper {
	return eqLeaf(notLessEqThm(), []Term{m, n}, not(le(m, n)), lt(n, m))
}

// lessEqAntisym: ⊢ (A≤B) ⇒ (B≤A) ⇒ (A=B)   (real: LessEqAntisym)
func lessEqAntisym(a, b Term) *prop.PropWrapper {
	return implyLeaf(lessEqAntisymThm(), []Term{a, b}, imply(le(a, b), imply(le(b, a), eqT(a, b))))
}

// ── provenance of expanded rows ──────────────────────────────────────────────

// lessEqOfEq: ⊢ (A = B) ⇒ (A ≤ B)   (real: LessEqOfEq)
func lessEqOfEq(a, b Term) *prop.PropWrapper {
	return implyLeaf(lessEqOfEqThm(), []Term{a, b}, imply(eqT(a, b), le(a, b)))
}

// lessEqOfEqSwapped: ⊢ (A = B) ⇒ (B ≤ A)   (real: LessEqOfEq on the swapped equality)
func lessEqOfEqSwapped(a, b Term) *prop.PropWrapper {
	return implyLeaf(lessEqOfEqSwappedThm(), []Term{a, b}, imply(eqT(a, b), le(b, a)))
}

// zeroLe: ⊢ 0 ≤ x   (real: ZeroLessEq; the implicit ℕ nonnegativity)
func zeroLe(x Term) *prop.PropWrapper {
	return implyLeaf(zeroLessEqThm(), []Term{x}, le(Numeral(0), x))
}

// ── monotone scaling by a positive numeral ───────────────────────────────────

// leScale: ⊢ (A ≤ B) ⇒ (c·A ≤ c·B)   (c ≥ 1; real: LessEqMulMono-class)
func leScale(c _Integer, a, b Term) *prop.PropWrapper {
	cN := numeralOf(c)
	return implyLeaf(lessEqMulMonoThm(), []Term{cN, a, b},
		imply(le(a, b), le(star(cN, a), star(cN, b))))
}

// ltScale: ⊢ (A < B) ⇒ (c·A < c·B)   (c ≥ 1; real: LessThanMulMono-class).
// Unlike leScale, the strict lemma needs c ≠ 0: the bundle field LessThanMulMono is
// the 2-premise form ∀m n p. (m≠0) ⇒ (n<p) ⇒ (m·n < m·p) (CurryIffConj of the
// corpus cancel-iff). We instantiate at the concrete coefficient and discharge the
// `c≠0` premise numerically — c is a Farkas multiplier (>1 here; lam==1 rows skip
// scaling), so it is always nonzero. A bundle-nil/mis-shaped field falls through
// to the placeholder seam (panics in production, bundle.go).
func ltScale(c _Integer, a, b Term) *prop.PropWrapper {
	cN := numeralOf(c)
	want := imply(lt(a, b), lt(star(cN, a), star(cN, b)))
	thm := lessThanMulMonoThm()
	if thm != nil {
		inst := instAll(thm, []Term{cN, a, b}) // (cN≠0) ⇒ (a<b) ⇒ (cN·a < cN·b)
		if cNe, ok := NormNatNe(cN, natZero); ok {
			// iffTrueElim(cNe) = ⊢ ¬(cN=0); discharge the field's first premise.
			res := inst.DemoteHyp().DeriveHypFrom(iffTrueElim(cNe))
			if res.Conclusion().AlphaEquals(want) {
				return res
			}
		}
	}
	return placeholderConcl(thm, want)
}

// ── pairwise inequality addition (strictness combinations) ───────────────────

// addLe2: ⊢ (A≤B) ⇒ (C≤D) ⇒ (A+C ≤ B+D)   (real: LessEqAdd2)
func addLe2(a, b, c, d Term) *prop.PropWrapper {
	return implyLeaf(lessEqAdd2Thm(), []Term{a, b, c, d},
		imply(le(a, b), imply(le(c, d), le(plus(a, c), plus(b, d)))))
}

// addLt2: ⊢ (A<B) ⇒ (C<D) ⇒ (A+C < B+D)   (real: LessThanAdd2)
func addLt2(a, b, c, d Term) *prop.PropWrapper {
	return implyLeaf(lessThanAdd2Thm(), []Term{a, b, c, d},
		imply(lt(a, b), imply(lt(c, d), lt(plus(a, c), plus(b, d)))))
}

// addLeLt: ⊢ (A≤B) ⇒ (C<D) ⇒ (A+C < B+D)   (real: LessEqLessThanAdd2)
func addLeLt(a, b, c, d Term) *prop.PropWrapper {
	return implyLeaf(lessEqLessThanAdd2Thm(), []Term{a, b, c, d},
		imply(le(a, b), imply(lt(c, d), lt(plus(a, c), plus(b, d)))))
}

// addLtLe: ⊢ (A<B) ⇒ (C≤D) ⇒ (A+C < B+D)   (real: LessThanLessEqAdd2)
func addLtLe(a, b, c, d Term) *prop.PropWrapper {
	return implyLeaf(lessThanLessEqAdd2Thm(), []Term{a, b, c, d},
		imply(lt(a, b), imply(le(c, d), lt(plus(a, c), plus(b, d)))))
}

// ── left cancellation of a common addend ─────────────────────────────────────

// addLcancelLe: ⊢ (P + x ≤ P + y) ⇔ (x ≤ y)   (real: LessEqAddCancel)
func addLcancelLe(p, x, y Term) *prop.PropWrapper {
	return eqLeaf(lessEqAddCancelThm(), []Term{p, x, y}, le(plus(p, x), plus(p, y)), le(x, y))
}

// addLcancelLt: ⊢ (P + x < P + y) ⇔ (x < y)   (real: LessThanAddCancel)
func addLcancelLt(p, x, y Term) *prop.PropWrapper {
	return eqLeaf(lessThanAddCancelThm(), []Term{p, x, y}, lt(plus(p, x), plus(p, y)), lt(x, y))
}

// LinProve is the forward `{hyps} ⊢ goal` wrapper around the refutation core
// (LinRefuteProof). A linear comparison goal is proved by refuting its negation:
//
//	{hyps, ¬goal} ⊢ ⊥   (LinRefuteProof)
//	────────────────────────────────────  NegHyp peels ¬goal back to the concl,
//	{hyps} ⊢ goal        a duality lemma (NotLessThan/NotLessEq) rewrites it to goal.
//
// Goal shapes handled (over num): `<`, `≤`, `≠` directly; `>`/`≥` by the
// definitional flip to swapped `<`/`≤`; `=` by antisymmetry of two `≤` proofs.
// Hyps that are not linear comparisons are silently ignored (they carry no
// information linarith can use). ok=false ⇒ the goal is not a recognized linear
// comparison, or its negation is ℚ-Farkas satisfiable (so unprovable here).
//
// hyps is consumed once (via HypIter, no slice clone) into a []LinConstraint
// that the internal recursion reuses. The discharge bottoms out in the same
// bundle leaves as the rest of omega; the composition is real kernel work.
func LinProve(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return proveWith(LinRefuteProof, hypConstraints(hyps), goal)
}

// OmegaProve is LinProve over the sound integer core (IntRefuteProof: ℚ-Farkas
// strengthened with the GCD-equality test and rank-1 gcd rounding cuts). Same
// `{hyps} ⊢ goal` contract and same negate→refute→peel structure, but it
// additionally closes goals that need integrality, e.g. `{b < a+1} ⊢ b ≤ a`
// (over ℤ, b<a+1 ⟺ b≤a) or `2*a ≠ 1` (GCD test). The hyp-subset invariant
// holds identically: IntRefuteProof's ⊥ carries the original constraint terms
// as hypotheses (the rounding cut moves only the conclusion side).
func OmegaProve(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return proveWith(IntRefuteProof, hypConstraints(hyps), goal)
}

// refuteFn decides unsatisfiability of a constraint set and, on success, returns
// the real `{constraint-terms} ⊢ ⊥`. Both LinRefuteProof (ℚ) and IntRefuteProof
// (ℤ) satisfy it and share the hypothesis shape proveWith depends on (each used
// constraint appears verbatim as a hyp; nonnegativity rows are proven, not
// assumed), so the negate→peel transport works unchanged for either.
type refuteFn = func([]LinConstraint) (*prop.PropWrapper, bool)

// proveWith is the recursive core over already-parsed hypothesis constraints,
// parameterized by the refutation engine (ℚ for LinProve, ℤ for OmegaProve).
func proveWith(refute refuteFn, hypCs []LinConstraint, goal Term) (*prop.PropWrapper, bool) {
	// `>` / `≥`: reduce to swapped `<` / `≤` via the definitional bridge.
	//   prove {hyps} ⊢ b<a, then (a>b ⇔ b<a) flips it to {hyps} ⊢ a>b.
	if a, b, ok := MatchesGt(goal); ok {
		inner, iok := proveWith(refute, hypCs, lt(b, a))
		if !iok {
			return nil, false
		}
		return gtBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := MatchesGe(goal); ok {
		inner, iok := proveWith(refute, hypCs, le(b, a))
		if !iok {
			return nil, false
		}
		return geBridge(a, b).EqSym().EqMP(inner), true
	}

	// `=`: a=b from (a≤b) and (b≤a) by antisymmetry. ext.MatchesEQ also fires on
	// bool `⇔` and non-num `=`; the linOf guard keeps us on linear num equalities.
	if a, b, ok := ext.MatchesEQ(goal); ok {
		if !isLinear(a) || !isLinear(b) {
			return nil, false
		}
		g1, ok1 := proveWith(refute, hypCs, le(a, b))
		g2, ok2 := proveWith(refute, hypCs, le(b, a))
		if !ok1 || !ok2 {
			return nil, false
		}
		return mp(mp(lessEqAntisym(a, b), g1), g2), true
	}

	// `<` / `≤` / `≠`: refute the negated goal, then peel it back.
	neg, nTerm, finish, ok := negateGoal(goal)
	if !ok {
		return nil, false
	}
	// fresh slice: the `=` branch calls proveWith twice with the same hypCs,
	// so we must not append into hypCs's shared backing array.
	cs := make([]LinConstraint, len(hypCs), len(hypCs)+1)
	copy(cs, hypCs)
	cs = append(cs, neg)
	R, rok := refute(cs)
	if !rok {
		return nil, false
	}
	return finish(R.NegHyp(nTerm)), true // R: {hyps, nTerm} ⊢ ⊥
}

// negateGoal turns a `<`/`≤`/`≠` goal into the constraint to add for refutation,
// the term that constraint contributes as a hypothesis (so NegHyp can peel it),
// and the finisher that rewrites `⊢ ¬nTerm` back into `⊢ goal`.
func negateGoal(goal Term) (neg LinConstraint, nTerm Term, finish func(*prop.PropWrapper) *prop.PropWrapper, ok bool) {
	// a<b : add b≤a; ⊢ ¬(b≤a) ──NotLessEq──▸ ⊢ a<b
	if a, b, m := MatchesLt(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLE}, le(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return notLE(b, a).EqMP(g) }, true
	}
	// a≤b : add b<a; ⊢ ¬(b<a) ──NotLessThan──▸ ⊢ a≤b
	if a, b, m := MatchesLe(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLT}, lt(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return notLT(b, a).EqMP(g) }, true
	}
	// a≠b (=¬(a=b)) : add a=b; ⊢ ¬(a=b) IS the goal, no rewrite needed.
	if inner := ext.MatchesNOT(goal); inner != nil {
		if a, b, m := ext.MatchesEQ(inner); m && isLinear(a) && isLinear(b) {
			return LinConstraint{Lhs: a, Rhs: b, Op: opEQ}, eqT(a, b),
				func(g *prop.PropWrapper) *prop.PropWrapper { return g }, true
		}
	}
	return LinConstraint{}, nil, nil, false
}

// hypConstraints / parseHypConstraint / linConstraint / isLinear are the `num`
// entry points to the domain-generic constraint extraction (domain.go `*Domain`
// methods). They keep the original call sites untouched; the real domain reaches
// the same logic through realDomain.
func hypConstraints(hyps iter.Seq[Term]) []LinConstraint { return natDomain.hypConstraints(hyps) }

// isLinear reports whether t is a linear form over num (the gate linOf
// provides). Since the monomial-basis extraction (domain.go polyMul), a
// nonlinear product reads as a polynomial over canonical monomial atoms, so
// this succeeds on `m·p` too — exactly what the constraint builders want (they
// then reason about each monomial as a nonnegative unknown in a basis shared
// across every spelling of the same polynomial).
func isLinear(t Term) bool { return natDomain.isLinear(t) }

// genuinelyLinear is the STRICT linearity test the enumeration gate needs: t is
// linear AND its form carries no nonlinear-product atom. It diverges from
// isLinear precisely on products — `m·p` is isLinear (atomized) but NOT
// genuinelyLinear — so `x·x ≤ 4` is still recognized as worth enumerating rather
// than handed to a linarith that cannot relate the opaque `x·x` to x's bound.
// (linOf never atomizes `c·a` to a product atom — that scales to a monomial with
// atom `a` — so any `*`-headed atom here is genuinely nonlinear.)
func genuinelyLinear(t Term) bool { return natDomain.genuinelyLinear(t) }

// isNat reports whether t has type num.
func isNat(t Term) bool { return t.Type().Equals(dsl.NumType) }

// IsNatEqGoal is the cheap syntactic shape gate for the ring tactic: t is an
// equality `l = r` over num with distinct sides (refl handles l ≡ r). Accepts
// nonlinear polynomials (RingProveFull handles them), so it gates on the operand
// type rather than linearity. Does not attempt a proof.
func IsNatEqGoal(t Term) bool {
	l, r, ok := ext.MatchesEQ(t)
	return ok && !l.AlphaEquals(r) && isNat(l)
}

// ComparisonSidesLinear reports whether t is a num comparison/equality whose two
// sides are both linear forms. Lets the engine tell a nonlinear-fragment failure
// (`a*b < …` — out of scope, try ring/lemmas) apart from a "linear but not
// derivable" failure (the goal does not follow from the hypotheses, or needs
// reasoning beyond the sound integer core). Returns false if t is not a
// recognized comparison at all.
func ComparisonSidesLinear(t Term) bool {
	var l, r Term
	switch {
	case match2(MatchesLt, t, &l, &r):
	case match2(MatchesLe, t, &l, &r):
	case match2(MatchesGt, t, &l, &r):
	case match2(MatchesGe, t, &l, &r):
	default:
		eqT := t
		if inner := ext.MatchesNOT(t); inner != nil {
			eqT = inner
		}
		a, b, ok := ext.MatchesEQ(eqT)
		if !ok {
			return false
		}
		l, r = a, b
	}
	return genuinelyLinear(l) && genuinelyLinear(r)
}

// match2 adapts a (Term,Term,bool) matcher into a switch-friendly predicate that
// writes the two operands through out-pointers on success.
func match2(m func(Term) (Term, Term, bool), t Term, l, r *Term) bool {
	a, b, ok := m(t)
	if ok {
		*l, *r = a, b
	}
	return ok
}

// IsLinComparisonGoal is the cheap syntactic shape gate for the linarith tactic:
// t is a comparison over num that LinProve recognizes as a goal — `<`/`≤`/`>`/`≥`
// (operand type implied by the matcher), or a num `=` / `≠`. A true verdict does
// not guarantee LinProve succeeds (e.g. nonlinear `<`, or not ℚ-Farkas valid);
// it is a fast over-approximation so the enumerator need not run the procedure.
func IsLinComparisonGoal(t Term) bool {
	if _, _, ok := MatchesLt(t); ok {
		return true
	}
	if _, _, ok := MatchesLe(t); ok {
		return true
	}
	if _, _, ok := MatchesGt(t); ok {
		return true
	}
	if _, _, ok := MatchesGe(t); ok {
		return true
	}
	if l, _, ok := ext.MatchesEQ(t); ok {
		return isNat(l)
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		if l, _, ok := ext.MatchesEQ(inner); ok {
			return isNat(l)
		}
	}
	return false
}
