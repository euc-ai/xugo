package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// linarith certificate replay over ℤ — the proof-producing twin of real_linarith.go. The
// structure is identical (scale → sum → ring-normalize → cancel → close, plus
// the forward negate→refute→peel); only the builders and leaves are int. As with
// ℝ, intBuildAll injects NO `&0 ≤ x` rows (int variables are free), and the
// scaling leaf's `&0 ≤ c` side condition is discharged on the concrete c.
//
// This is the ℚ-Farkas LINEAR fragment over ℤ: it proves exactly the goals real
// linarith would on the same atoms — it does NOT yet use integrality (the
// Discrete cut `x < y ⇔ x + &1 ≤ y` and gcd rounding are the int-specific
// "omega" extension, deferred). All leaves are IntLemmaBundle placeholders; the
// composition here is real kernel work, sound once the bundle is populated. The
// decision core (refute / atomTable / row) and the generic prop combinators are
// shared with num/real unchanged.

// intCanonAssume returns `{prov} ⊢ (lhs op rhs)` for op ∈ {opLE, opLT}, bridging
// a `>`/`≥` origin via intGt/GeBridge (mirror of realCanonAssume). base, when
// set, replaces the default Assume of the assumption term (conjunction projection).
func intCanonAssume(lhs, rhs Term, op relOp, hyp Term, base *prop.PropWrapper) *prop.PropWrapper {
	if hyp == nil {
		if base != nil {
			return base // proves the canonical lhs op rhs already
		}
		if op == opLT {
			return prop.Assume(intLtT(lhs, rhs))
		}
		return prop.Assume(intLeT(lhs, rhs))
	}
	if base == nil {
		base = prop.Assume(hyp)
	}
	if op == opLT {
		return intGtBridge(rhs, lhs).EqMP(base) // ⊢ (rhs>lhs)=(lhs<rhs)
	}
	return intGeBridge(rhs, lhs).EqMP(base) // ⊢ (rhs≥lhs)=(lhs≤rhs)
}

// intBuildAll mirrors realBuildAll over ℤ, minus the nonnegativity rows.
func intBuildAll(cs []LinConstraint) (*atomTable, []row, []provRow, bool) {
	tbl := &atomTable{}
	var signed []row
	var prs []provRow
	for _, c := range cs {
		rs, ok := intDomain.extractRow(tbl, c)
		if !ok {
			return nil, nil, nil, false
		}
		switch c.Op {
		case opLE:
			signed = append(signed, rs...)
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return intCanonAssume(c.Lhs, c.Rhs, opLE, c.Hyp, c.HypProof)
			}))
		case opLT:
			// ℤ discreteness: `a < b ⟺ a + &1 ≤ b`. Strengthen the
			// strict row to the non-strict konst+1 row — the integer-tight bound —
			// and carry the `a + &1 ≤ b` proof via Discrete, so ℚ-Farkas
			// closes off-by-one / consecutive-integer goals (`x < y ⊢ x + &1 ≤ y`)
			// it cannot over ℚ. The `num` mirror is nat_omega.go's
			// sucLessEqIffLessThan. NOT a gcd cut (no nat_div/nat_mod, no provenance DAG). Sound because
			// every int row sum is an integer, so `Σ < 0 ⟺ Σ + 1 ≤ 0`.
			rs[0].konst = rs[0].konst.add(integerOne)
			rs[0].strict = false
			signed = append(signed, rs[0])
			prs = append(prs, lazyProvRow(intPlusT(c.Lhs, intLit(1)), c.Rhs, false, func() *prop.PropWrapper {
				lt := intCanonAssume(c.Lhs, c.Rhs, opLT, c.Hyp, c.HypProof) // {..} ⊢ a < b
				return intDiscrete(c.Lhs, c.Rhs).EqSym().EqMP(lt)           // {..} ⊢ (a+&1) ≤ b
			}))
		case opEQ:
			signed = append(signed, rs...)
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return mp(intLessEqOfEq(c.Lhs, c.Rhs), c.assumeEq())
			}))
			prs = append(prs, lazyProvRow(c.Rhs, c.Lhs, false, func() *prop.PropWrapper {
				return mp(intLessEqOfEqSwapped(c.Lhs, c.Rhs), c.assumeEq())
			}))
		}
	}
	// No `&0 ≤ x` rows over ℤ: int variables are unconstrained (like ℝ).
	for i := range signed {
		signed[i] = signed[i].padCoeffs(tbl.n())
	}
	return tbl, signed, prs, true
}

// intAddLemma picks the inequality-addition leaf for the strictness combination.
func intAddLemma(accStrict, itStrict bool, a, b, c, d Term) *prop.PropWrapper {
	switch {
	case !accStrict && !itStrict:
		return intAddLe2(a, b, c, d)
	case accStrict && itStrict:
		return intAddLt2(a, b, c, d)
	case accStrict && !itStrict:
		return intAddLtLe(a, b, c, d)
	default:
		return intAddLeLt(a, b, c, d)
	}
}

// intSumRows is sumRows over ℤ: the rows of prs that λ takes, each scaled by
// its multiplier, added into one inequality `hyps ⊢ accL ⋈ accR`.
func intSumRows(prs []provRow, lambda []_Integer) (acc scaledIneq, ok bool) {
	var items []scaledIneq
	for j, lam := range lambda {
		if lam.sign() <= 0 {
			continue
		}
		pr := prs[j]
		prov, ok := pr.proof()
		if !ok {
			return scaledIneq{}, false
		}
		if lam.isOne() {
			items = append(items, scaledIneq{prov, pr.L, pr.R, pr.strict})
			continue
		}
		var sc *prop.PropWrapper
		if pr.strict {
			sc = mp(intLtScale(lam, pr.L, pr.R), prov)
		} else {
			sc = mp(intLeScale(lam, pr.L, pr.R), prov)
		}
		items = append(items, scaledIneq{sc, intMonoTerm(lam, pr.L), intMonoTerm(lam, pr.R), pr.strict})
	}
	if len(items) == 0 {
		return scaledIneq{}, false
	}
	acc = items[0]
	for _, it := range items[1:] {
		lem := intAddLemma(acc.strict, it.strict, acc.L, acc.R, it.L, it.R)
		comb := mp(mp(lem, acc.ineq), it.ineq)
		acc = scaledIneq{comb, intPlusT(acc.L, it.L), intPlusT(acc.R, it.R), acc.strict || it.strict}
	}
	return acc, true
}

// intReplay turns a Farkas certificate λ over prs into `hyps ⊢ ⊥` over ℤ:
// the rows summed (intSumRows), normalized, cancelled and evaluated.
func intReplay(prs []provRow, lambda []_Integer) (*prop.PropWrapper, bool) {
	acc, ok := intSumRows(prs, lambda)
	if !ok {
		return nil, false
	}

	// ring-normalize both sides: accL = buildTerm(lfL), accR = buildTerm(lfR).
	lfL, wL, _ := intNormalizeProof(acc.L)
	lfR, wR, _ := intNormalizeProof(acc.R)
	PL := intDomain.buildTerm(lfL)
	PR := intDomain.buildTerm(lfR)

	opC := intLe
	if acc.strict {
		opC = intLt
	}
	// ⊢ (accL ⋈ accR) = (PL ⋈ PR)
	cong := wL.LeftApply(opC).RightApply(acc.R).
		EqTrans(wR.LeftApply(ext.Apply(opC, PL)))
	transported := cong.EqMP(acc.ineq) // hyps ⊢ (PL ⋈ PR)

	// cancel the common variable part, leaving a constant relation cL ⋈ cR.
	var cmpProof *prop.PropWrapper
	var cL, cR Term
	if len(lfL.monos) > 0 {
		P := intMonoChainTerm(lfL.monos)
		cL = intLitOf(lfL.konst)
		cR = intLitOf(lfR.konst)
		var cancel *prop.PropWrapper
		if acc.strict {
			cancel = intAddLcancelLt(P, cL, cR)
		} else {
			cancel = intAddLcancelLe(P, cL, cR)
		}
		cmpProof = cancel.EqMP(transported) // hyps ⊢ (cL ⋈ cR)
	} else {
		cmpProof = transported
		cL, cR = PL, PR // both intLit(konst)
	}

	// close: the constant relation is numerically false ⇒ ⊥.
	var g4 *prop.PropWrapper
	if acc.strict {
		g4, ok = intNormNatLt(cL, cR)
	} else {
		g4, ok = intNormNatLe(cL, cR)
	}
	if !ok || !prop.Rhs(g4).Equals(prop.F) {
		return nil, false // certificate did not yield a false constant relation
	}
	return g4.EqMP(cmpProof), true // hyps ⊢ ⊥
}

// IntLinRefuteProof decides unsatisfiability of an int constraint set and, on
// success, returns `{h₁ … hₙ} ⊢ ⊥`. It tries, in cost order: the rank-1
// GCD-equality test (integer-unsat single equalities like `2·x = &1`
// that are ℚ-satisfiable), plain ℚ-Farkas + ℤ-discreteness (intFarkasRefute), then
// the rank-1 gcd ROUNDING CUT (non-strict systems with a
// ℚ-nonempty-but-ℤ-empty solution, e.g. `&4 ≤ 3·x ∧ 3·x ≤ &5`), then the
// elimination of equations (intEliminationRefute: `n = &2·q + &1` beside
// `&1 < n < &3`, where the contradiction is the rounding of a substituted
// row). ok=false ⇒ nonlinear input or not refutable by this (sound,
// incomplete) procedure. Satisfies refuteFn, so intProveWith transports it.
func IntLinRefuteProof(cs []LinConstraint) (*prop.PropWrapper, bool) {
	cs = intPositivizeConstraints(cs) // peel top-level sub/neg so the gcd test / cut see real coeffs
	// The monomials' sign rows (int_sign_rows.go): over ℤ a product atom is an
	// unknown with no sign, so a refutation that turns on `&0 ≤ a·b` — from the
	// factors' stated signs, or because the monomial is a square — has no row
	// to combine until this pass supplies one. After the positivization, so the
	// atoms it reads are the ones the rows below are extracted over.
	if extra := intMonomialSignConstraints(cs); len(extra) > 0 {
		cs = append(slices.Clone(cs), extra...)
	}
	if w, ok := intGcdEqRefute(cs); ok {
		return w, true
	}
	if w, ok := intFarkasRefute(cs); ok {
		return w, true
	}
	if w, ok := intRoundingCutRefute(cs); ok {
		return w, true
	}
	return intEliminationRefute(cs)
}

// intEliminationRefute refutes cs with its equations eliminated
// (equation_elimination.go): the rows of intBuildAll, each rounded by the gcd of
// its coefficients, every equation with an atom of coefficient ±1 solved and
// substituted, then ℚ-Farkas on what is left. It is what closes
// `n = &2·q + &1 ∧ &1 < n ⊢ &3 ≤ n`, where neither equation alone is
// gcd-unsat and no input row rounds. ok=false where no equation has such an
// atom — the passes before this one have then said all there is.
func intEliminationRefute(cs []LinConstraint) (*prop.PropWrapper, bool) {
	tbl, rows, prs, built := intBuildAll(cs)
	if !built {
		return nil, false
	}
	e, eliminated := eliminateEquations(tbl, rows, prs, intEliminationLeaves)
	if !eliminated {
		return nil, false
	}
	lambda, refuted := refute(tbl.n(), e.system())
	if !refuted {
		return nil, false
	}
	return intReplay(e.nodes, e.certificate(lambda))
}

// intPositivizeConstraints rewrites every constraint whose sides still carry
// total sub/neg into the equivalent positive two-sided form, via the signed
// normalizer's relation-level move-across (subneg.go), bridging the carried
// proof. It is the refuter-boundary twin of hypConstraints' moveAcrossHyp pass
// (domain.go): the hyp path positivizes comparison HYPOTHESES, but two kinds of
// constraint reach the refuter WITHOUT passing through it —
//
//   - the negated GOAL added by intProveWith: a `≠` goal contributes the equality
//     `a − b = k`, and the goal-side move-across leaf is blind to the `¬(=)` shape,
//     so the sub survives into the constraint;
//   - any constraint a direct IntLinRefuteProof caller builds.
//
// linOf ATOMIZES a raw `a − b` (a carrier-typed non-operator subterm) into one
// opaque atom, collapsing the coefficient gcd to 1 — which masks integer-unsat
// systems the GCD-equality test and the rounding cut would otherwise catch
// (`2·x − 2·y = &1`, `&4 ≤ 3·(x−y) ≤ &5`). Positivizing first exposes the true
// coefficients. A sub/neg-free constraint (incl. a nonlinear-with-sub one the
// move-across declines) passes through untouched, so this only ever adds reach.
// The carried `{origAtom} ⊢ positiveAtom` keeps the refutation's hypotheses ⊆ the
// goal's (the IsStronger contract).
func intPositivizeConstraints(cs []LinConstraint) []LinConstraint {
	out := make([]LinConstraint, len(cs))
	for i, c := range cs {
		if pc, ok := intPositivizeConstraint(c); ok {
			out[i] = pc
		} else {
			out[i] = c
		}
	}
	return out
}

// intPositivizeConstraint positivizes ONE constraint carrying sub/neg, returning
// the sub-free constraint and ok=true; (c, false) when it has no sub/neg or the
// move-across declines (nonlinear with subtraction — linOf will atomize, as
// before, with no regression).
func intPositivizeConstraint(c LinConstraint) (LinConstraint, bool) {
	if !intSubneg.hasSubNeg(c.Lhs) && !intSubneg.hasSubNeg(c.Rhs) {
		return c, false
	}
	atom, base := intConstraintAtom(c)
	iff := intSubneg.moveAcrossCmp(atom) // ⊢ atom ⇔ positiveAtom
	if iff == nil {
		return c, false
	}
	pc, ok := intDomain.parseHypConstraint(prop.Rhs(iff))
	if !ok {
		return c, false
	}
	pc.Hyp = nil
	pc.HypProof = iff.EqMP(base) // {provenance} ⊢ positiveAtom
	return pc, true
}

// intConstraintAtom rebuilds a constraint's canonical comparison/equality term
// and the base proof of it that canonAssume / assumeEq would feed downstream, so
// a positivizing iff can be EqMP'd onto it — preserving the provenance, including
// a `>`/`≥` Hyp or a conjunction-projection HypProof.
func intConstraintAtom(c LinConstraint) (Term, *prop.PropWrapper) {
	switch c.Op {
	case opLT:
		return intLtT(c.Lhs, c.Rhs), intCanonAssume(c.Lhs, c.Rhs, opLT, c.Hyp, c.HypProof)
	case opLE:
		return intLeT(c.Lhs, c.Rhs), intCanonAssume(c.Lhs, c.Rhs, opLE, c.Hyp, c.HypProof)
	default: // opEQ
		return eqT(c.Lhs, c.Rhs), c.assumeEq()
	}
}

// intFarkasRefute is the pure ℚ-Farkas + ℤ-discreteness refutation (no GCD
// test): build rows, find the Farkas certificate, replay it. The GCD-equality
// branches recurse here (NOT through IntLinRefuteProof) so the gcd test never
// re-fires on its own residual equality.
func intFarkasRefute(cs []LinConstraint) (*prop.PropWrapper, bool) {
	tbl, signed, prs, built := intBuildAll(cs)
	if !built {
		return nil, false
	}
	lambda, ok := refute(tbl.n(), signed)
	if !ok {
		return nil, false
	}
	return intReplay(prs, lambda)
}

// IntLinProve is the forward `{hyps} ⊢ goal` wrapper over ℤ — the mirror of
// RealLinProve. Goal shapes: `<`/`≤`/`≠` directly; `>`/`≥` by the definitional
// flip; `=` by antisymmetry of two `≤` proofs. Non-comparison / nonlinear hyps
// are dropped. ok=false ⇒ goal not a recognized int linear comparison, or its
// negation is ℚ-Farkas satisfiable.
func IntLinProve(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return intProveWith(intDomain.hypConstraints(hyps), goal)
}

func intProveWith(hypCs []LinConstraint, goal Term) (*prop.PropWrapper, bool) {
	// `>` / `≥`: reduce to swapped `<` / `≤` via the definitional bridge.
	if a, b, ok := intDomain.matchGt(goal); ok {
		inner, iok := intProveWith(hypCs, intLtT(b, a))
		if !iok {
			return nil, false
		}
		return intGtBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := intDomain.matchGe(goal); ok {
		inner, iok := intProveWith(hypCs, intLeT(b, a))
		if !iok {
			return nil, false
		}
		return intGeBridge(a, b).EqSym().EqMP(inner), true
	}

	// `=`: a=b from (a≤b) and (b≤a) by antisymmetry.
	if a, b, ok := ext.MatchesEQ(goal); ok && intDomain.isElem(a) {
		if !intDomain.isLinear(a) || !intDomain.isLinear(b) {
			return nil, false
		}
		g1, ok1 := intProveWith(hypCs, intLeT(a, b))
		g2, ok2 := intProveWith(hypCs, intLeT(b, a))
		if !ok1 || !ok2 {
			return nil, false
		}
		return mp(mp(intLessEqAntisym(a, b), g1), g2), true
	}

	// `<` / `≤` / `≠`: refute the negated goal, then peel it back.
	neg, nTerm, finish, ok := intNegateGoal(goal)
	if !ok {
		return nil, false
	}
	cs := make([]LinConstraint, len(hypCs), len(hypCs)+1)
	copy(cs, hypCs)
	cs = append(cs, neg)
	R, rok := IntLinRefuteProof(cs)
	if !rok {
		return nil, false
	}
	return finish(R.NegHyp(nTerm)), true // R: {hyps, nTerm} ⊢ ⊥
}

// intNegateGoal is the ℤ mirror of realNegateGoal: the constraint to add for
// refutation, the term it contributes as a hypothesis, and the finisher that
// rewrites `⊢ ¬nTerm` back into `⊢ goal`.
func intNegateGoal(goal Term) (neg LinConstraint, nTerm Term, finish func(*prop.PropWrapper) *prop.PropWrapper, ok bool) {
	// a<b : add b≤a; ⊢ ¬(b≤a) ──NotLessEq──▸ ⊢ a<b
	if a, b, m := intDomain.matchLt(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLE}, intLeT(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return intNotLE(b, a).EqMP(g) }, true
	}
	// a≤b : add b<a; ⊢ ¬(b<a) ──NotLessThan──▸ ⊢ a≤b
	if a, b, m := intDomain.matchLe(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLT}, intLtT(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return intNotLT(b, a).EqMP(g) }, true
	}
	// a≠b (=¬(a=b)) : add a=b; ⊢ ¬(a=b) IS the goal, no rewrite needed.
	if inner := ext.MatchesNOT(goal); inner != nil {
		if a, b, m := ext.MatchesEQ(inner); m && intDomain.isElem(a) &&
			intDomain.isLinear(a) && intDomain.isLinear(b) {
			return LinConstraint{Lhs: a, Rhs: b, Op: opEQ}, eqT(a, b),
				func(g *prop.PropWrapper) *prop.PropWrapper { return g }, true
		}
	}
	return LinConstraint{}, nil, nil, false
}

// The rank-1 GCD-equality test over the `int` type — the integer-completeness
// piece that closes single equalities `Σcᵢxᵢ = k` with gcd(cᵢ) ∤ k, which pure
// ℚ-Farkas misses because they are ℚ-SATISFIABLE (e.g. `2·x = &1` has the ℚ
// solution x = 1/2, but no integer one).
//
// This is the `int`-type twin of the num side's gcd-equality contradiction
// (nat_omega.go: eqGCDUnsat / groundedGcdEq), but it needs
// NO divisibility predicate. The integer content is supplied entirely by the
// machinery the int layer already has — ℤ-discreteness + ℚ-Farkas — via a sign
// case split on the reduced variable form:
//
//	V = c,  g = gcd(coeffs(V)),  g ∤ c,  M = V/g,  q = ⌊c/g⌋
//	  M ≤ q     ⟹  g·M ≤ g·q = c−r < c = g·M    (Farkas: 0 < r ≤ 0)
//	  q < M     ⟹  q+&1 ≤ M (discreteness), g·M ≥ g·(q+1) = c+(g−r) > c    (Farkas)
//
// Each branch, combined with the original equality, is an honest ℚ-Farkas
// contradiction — the atoms of M are exactly the atoms of V (M = V/g as a form),
// so the scaled equality cancels the variables and lands a false numeric bound.
// The split `M ≤ q ∨ ¬(M ≤ q)` is excluded middle; the `¬(M ≤ q)` arm becomes the
// usable `q+&1 ≤ M` through Discrete (the same strict-row strengthening
// intBuildAll already applies). So this reuses the discharge wholesale and adds
// no new leaf, no nat_div/nat_mod, no provenance DAG — it is strictly rank-1, below the
// gcd-cut / Cooper-QE frontier.
//
// It handles the GENERAL `Σcᵢxᵢ = k` (any two-sided int_add/literal equality, not
// just the num-side common shape of one pure-constant side): the signed COMBINED
// form `Σcᵢxᵢ + konst = 0` is computed directly, and the split condition
// `Σ(cᵢ/g)·x ≤ q` is written sub-free as a positive two-sided comparison
// `left ≤ right` (positive reduced coeffs and `max(−q,0)` on the left, negative
// reduced coeffs and `max(q,0)` on the right) — so the same machinery handles
// `2·x = &1` and `2·x = 2·y + &1` alike. (A side carrying top-level int_sub/int_neg
// is positivized first by intPositivizeConstraints (IntLinRefuteProof), so it reaches
// the test with its real coefficients instead of one atomized `a−b` whose gcd
// collapses to 1; only a nonlinear sub/neg like x·(a−b) still atomizes.) Both
// branch refutations route through intFarkasRefute, NOT IntLinRefuteProof, so the
// gcd test never re-fires on its own residual.

// intGcdEqRefute scans the constraints for an equality the GCD test refutes in
// the common shape and, on the first hit, returns its `{eqTerm} ⊢ ⊥`. ok=false
// if no constraint qualifies (the caller then falls through to ℚ-Farkas).
func intGcdEqRefute(cs []LinConstraint) (*prop.PropWrapper, bool) {
	for _, c := range cs {
		if c.Op != opEQ {
			continue
		}
		if w, ok := intGroundedGcdEq(c); ok {
			return w, true
		}
	}
	return nil, false
}

// intGroundedGcdEq builds `{eqTerm} ⊢ ⊥` for an int equality constraint whose GCD
// test fails: the combined form `Σcᵢxᵢ = k` has g = gcd(cᵢ) > 1 with g ∤ k. The
// split condition `Σ(cᵢ/g)·x ≤ q` (q = ⌊k/g⌋) is the positive two-sided `left ≤
// right`. ok=false ⇒ not gcd-unsat, or the branch refutations did not close.
func intGroundedGcdEq(c LinConstraint) (*prop.PropWrapper, bool) {
	tbl := &atomTable{}
	coeffs, konst, ok := intCombinedForm(tbl, c.Lhs, c.Rhs)
	if !ok {
		return nil, false
	}
	g := vecGCD(coeffs)
	rhsVal := konst.neg() // the equality is `Σ coeffs·x = rhsVal`
	if g.cmp(integerOne) <= 0 {
		return nil, false
	}
	q, remainder := rhsVal.divMod(g) // q = ⌊rhsVal/g⌋
	if remainder.isZero() {
		return nil, false
	}
	// `Σ(coeffs/g)·x ≤ q` ⟺ `P − N ≤ q`, written sub-free as `left ≤ right`:
	// positive reduced coeffs (+ |q| when q<0) on the left, negative reduced
	// coeffs (+ q when q≥0) on the right.
	left, right := intReducedLe(coeffs, g, q, tbl)
	g0 := intLeT(left, right)
	g1 := not(g0)

	// The equality, carrying its original provenance `{eqTerm}` into both branches.
	eqC := LinConstraint{Lhs: c.Lhs, Rhs: c.Rhs, Op: opEQ, HypProof: c.assumeEq()}

	// branch 0: {eqTerm, left ≤ right} ⊢ ⊥   (ℚ-Farkas: g·(left≤right) vs the equality).
	leC := LinConstraint{Lhs: left, Rhs: right, Op: opLE, HypProof: prop.Assume(g0)}
	r0, ok := intFarkasRefute([]LinConstraint{eqC, leC})
	if !ok {
		return nil, false
	}
	// branch 1: {eqTerm, ¬(left ≤ right)} ⊢ ⊥
	// (¬(left≤right) ⟺ right<left ⟹ right+&1 ≤ left by discreteness).
	rLtL := intNotLE(left, right).EqMP(prop.Assume(g1)) // {¬(left≤right)} ⊢ right < left
	ltC := LinConstraint{Lhs: right, Rhs: left, Op: opLT, HypProof: rLtL}
	r1, ok := intFarkasRefute([]LinConstraint{eqC, ltC})
	if !ok {
		return nil, false
	}

	imp0 := r0.PromoteHyp(g0) // {eqTerm} ⊢ (left≤right) ⇒ ⊥
	imp1 := r1.PromoteHyp(g1) // {eqTerm} ⊢ ¬(left≤right) ⇒ ⊥
	return prop.ByCases(prop.F, g0, g1).
		DeriveHypFrom(prop.ExcludedMiddle(g0)).
		DeriveHypFrom(imp0).
		DeriveHypFrom(imp1), true
}

// intReducedLe builds the sub-free two-sided `left ≤ right` equivalent to
// `Σ(coeffs/g)·x ≤ q`: positive reduced coeffs (and |q| when q<0) go left,
// negative reduced coeffs (and q when q≥0) go right. Atoms are tbl.atoms[i],
// so they align with the equality's atoms for ℚ-Farkas cancellation.
func intReducedLe(coeffs []_Integer, g, q _Integer, tbl *atomTable) (left, right Term) {
	var pos, neg []monomialL
	for i, cf := range coeffs {
		switch r, _ := cf.divMod(g); r.sign() {
		case 1:
			pos = append(pos, monomialL{coeff: r, atom: tbl.atoms[i]})
		case -1:
			neg = append(neg, monomialL{coeff: r.neg(), atom: tbl.atoms[i]})
		}
	}
	var lk, rk _Integer
	if q.sign() < 0 {
		lk = q.neg() // P + |q| ≤ N
	} else {
		rk = q // P ≤ q + N
	}
	return intDomain.buildTerm(linForm{konst: lk, monos: pos}),
		intDomain.buildTerm(linForm{konst: rk, monos: neg})
}

// intCombinedForm computes the signed combined linear form of `lhs − rhs` over
// int: coeffs[i] is the coefficient of tbl.atoms[i] and konst the constant, so
// `lhs = rhs` is `Σ coeffs·x + konst = 0` and `lhs ≤ rhs` is `Σ coeffs·x + konst
// ≤ 0`. ok=false if a side is nonlinear over int. Shared by the GCD-equality test
// and the rounding cut.
func intCombinedForm(tbl *atomTable, lhs, rhs Term) (coeffs []_Integer, konst _Integer, ok bool) {
	lf, ok1 := intDomain.linOf(lhs)
	rf, ok2 := intDomain.linOf(rhs)
	if !ok1 || !ok2 {
		return nil, _Integer{}, false
	}
	coeffs, konst = signedDifference(tbl, lf, rf)
	return coeffs, konst, true
}

// The rank-1 gcd ROUNDING CUT over the `int` type — the inequality companion of
// the GCD-equality test. It closes the integer-frontier gap pure
// ℚ-Farkas + discreteness leaves open: a system of NON-STRICT inequalities whose
// ℚ-solution set is non-empty but contains no integer, e.g. `&4 ≤ 3·x ∧ 3·x ≤ &5`
// (x ∈ [4/3, 5/3] over ℚ, no integer). Discreteness tightens only STRICT rows and
// the negated goal, so it cannot reach this; the rounding cut can.
//
// It is the int twin of the num side's `roundedCut` (`tightenLe` + `LessEqRightDivEq` +
// `DivModUniq`), but it needs NO int division: the tightened row
// `g·Σ ≤ b ⟹ Σ ≤ ⌊b/g⌋` is exactly a forward goal the int layer ALREADY proves
// via discreteness (negating `Σ ≤ ⌊b/g⌋` gives a strict bound the discrete
// strengthening closes against `g·Σ ≤ b`). So the cut is a FORWARD ENRICHMENT:
// for each non-strict constraint whose coefficient gcd > 1 with a genuine
// rounding, derive the tightened constraint via `intFarkasRefute` (discreteness),
// add it, and re-refute. No new leaf, no nat_div/nat_mod, no provenance DAG — strictly
// rank-1. (Iterated rank-k cuts, where a cut feeds another, are the open
// completeness frontier and need the provenance-DAG shape this deliberately avoids.)
//
// Soundness rides on the per-cut proof: a tightened row is added ONLY with a real
// `{origConstraint} ⊢ Lt ≤ Rt` derivation, so a miscomputed cut yields no proof
// and is simply dropped. The proof routes through `intFarkasRefute` (NOT
// `IntLinRefuteProof`), so the cut never re-enters itself.

// intRoundingCutRefute tightens each non-strict constraint by its coefficient gcd
// (when the rounding is genuine), augments the set with the tightened rows, and
// re-refutes by plain ℚ-Farkas + discreteness. ok=false when nothing tightened or
// the augmented set is still ℚ-Farkas satisfiable.
func intRoundingCutRefute(cs []LinConstraint) (*prop.PropWrapper, bool) {
	var extra []LinConstraint
	for _, c := range cs {
		if c.Op != opLE {
			continue // strict `<` is handled by discreteness; `=` by the GCD test.
		}
		if tc, ok := intRoundingCut(c); ok {
			extra = append(extra, tc)
		}
	}
	if len(extra) == 0 {
		return nil, false
	}
	return intFarkasRefute(append(slices.Clone(cs), extra...))
}

// intRoundingCut derives the gcd-tightened constraint of a non-strict `c` (`Lhs ≤
// Rhs`): the combined row `Σcᵢxᵢ + konst ≤ 0` with g = gcd > 1 rounds to
// `Σ(cᵢ/g)xᵢ ≤ ⌊−konst/g⌋`, written sub-free as `Lt ≤ Rt`, proved `{c} ⊢ Lt ≤ Rt`
// by discreteness. ok=false when g ≤ 1, the rounding is exact (no tightening), or
// the proof did not close.
func intRoundingCut(c LinConstraint) (LinConstraint, bool) {
	tbl := &atomTable{}
	coeffs, konst, ok := intCombinedForm(tbl, c.Lhs, c.Rhs)
	if !ok || vecGCD(coeffs).cmp(integerOne) <= 0 {
		return LinConstraint{}, false
	}
	nc, nk, changed := tightenLe(coeffs, konst)
	if !changed {
		return LinConstraint{}, false // exact division — the tightened row adds nothing.
	}
	lt, rt := intSignedToLe(nc, nk, tbl)
	proof, ok := intProveLe(c, lt, rt)
	if !ok {
		return LinConstraint{}, false
	}
	return LinConstraint{Lhs: lt, Rhs: rt, Op: opLE, HypProof: proof}, true
}

// intProveLe proves `{prov_c} ⊢ Lt ≤ Rt` from a single constraint `c` by the
// negate-and-refute the int forward prover uses (negating `Lt ≤ Rt` adds the
// strict `Rt < Lt`, which discreteness closes against `c`). It calls
// intFarkasRefute directly, so the rounding cut never re-enters itself.
func intProveLe(c LinConstraint, lt, rt Term) (*prop.PropWrapper, bool) {
	neg := LinConstraint{Lhs: rt, Rhs: lt, Op: opLT} // ¬(Lt ≤ Rt) ⟿ Rt < Lt
	r, ok := intFarkasRefute([]LinConstraint{c, neg})
	if !ok {
		return nil, false // {prov_c, Rt<Lt} not refutable — no tightening proof.
	}
	g := r.NegHyp(intLtT(rt, lt))         // {prov_c} ⊢ ¬(Rt < Lt)
	return intNotLT(rt, lt).EqMP(g), true // {prov_c} ⊢ Lt ≤ Rt
}

// intSignedToLe rebuilds a sub-free two-sided `Lt ≤ Rt` from a signed row
// `Σ coeffs·x + konst ≤ 0`: positive coeffs and a positive constant go left,
// negatives go right. The int twin of signedToLe (nat_omega.go), over
// int_of_num terms via intDomain.buildTerm.
func intSignedToLe(coeffs []_Integer, konst _Integer, tbl *atomTable) (lt, rt Term) {
	var lm, rm []monomialL
	for i, c := range coeffs {
		switch c.sign() {
		case 1:
			lm = append(lm, monomialL{coeff: c, atom: tbl.atoms[i]})
		case -1:
			rm = append(rm, monomialL{coeff: c.neg(), atom: tbl.atoms[i]})
		}
	}
	var lk, rk _Integer
	switch konst.sign() {
	case 1:
		lk = konst
	case -1:
		rk = konst.neg()
	}
	return intDomain.buildTerm(linForm{konst: lk, monos: lm}),
		intDomain.buildTerm(linForm{konst: rk, monos: rm})
}
