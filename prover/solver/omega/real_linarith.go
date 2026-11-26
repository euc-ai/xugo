package omega

import (
	"iter"
	"slices"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// linarith certificate replay over ℝ — the proof-producing twin of the num discharge
// (nat_linarith.go). The structure is identical (scale → sum → ring-normalize →
// cancel → close); only the builders and leaves are real, and two ℝ-specific
// shape differences apply: realBuildAll injects NO `0 ≤ x` rows (real variables
// are free), and the scaling leaf's `0 ≤ c` side-condition is discharged on the
// concrete c.
//
// All leaves read the RealLemmaBundle (real_lemmas.go); the composition here is
// real kernel work, sound once the bundle is populated
// (serve.InstallRealBundle). The decision core (refute / atomTable / row) and the generic
// prop combinators are shared with num unchanged.

// realCanonAssume returns `{prov} ⊢ (lhs op rhs)` for op ∈ {opLE, opLT}, bridging
// a `>`/`≥` origin via realGt/GeBridge (mirror of canonAssume). base, when set,
// replaces the default Assume of the assumption term (conjunction projection).
func realCanonAssume(lhs, rhs Term, op relOp, hyp Term, base *prop.PropWrapper) *prop.PropWrapper {
	if hyp == nil {
		if base != nil {
			return base // proves the canonical lhs op rhs already
		}
		if op == opLT {
			return prop.Assume(realLtT(lhs, rhs))
		}
		return prop.Assume(realLeT(lhs, rhs))
	}
	if base == nil {
		base = prop.Assume(hyp)
	}
	if op == opLT {
		return realGtBridge(rhs, lhs).EqMP(base) // ⊢ (rhs>lhs)=(lhs<rhs)
	}
	return realGeBridge(rhs, lhs).EqMP(base) // ⊢ (rhs≥lhs)=(lhs≤rhs)
}

// realBuildAll mirrors buildAll over ℝ, minus the nonnegativity rows.
func realBuildAll(cs []LinConstraint) (*atomTable, []row, []provRow, bool) {
	tbl := &atomTable{}
	var signed []row
	var prs []provRow
	for _, c := range cs {
		rs, ok := realDomain.extractRow(tbl, c)
		if !ok {
			return nil, nil, nil, false
		}
		signed = append(signed, rs...)
		switch c.Op {
		case opLE:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return realCanonAssume(c.Lhs, c.Rhs, opLE, c.Hyp, c.HypProof)
			}))
		case opLT:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, true, func() *prop.PropWrapper {
				return realCanonAssume(c.Lhs, c.Rhs, opLT, c.Hyp, c.HypProof)
			}))
		case opEQ:
			prs = append(prs, lazyProvRow(c.Lhs, c.Rhs, false, func() *prop.PropWrapper {
				return mp(realLessEqOfEq(c.Lhs, c.Rhs), c.assumeEq())
			}))
			prs = append(prs, lazyProvRow(c.Rhs, c.Lhs, false, func() *prop.PropWrapper {
				return mp(realLessEqOfEqSwapped(c.Lhs, c.Rhs), c.assumeEq())
			}))
		}
	}
	// No `0 ≤ x` rows over ℝ: real variables are unconstrained.
	for i := range signed {
		signed[i] = signed[i].padCoeffs(tbl.n())
	}
	return tbl, signed, prs, true
}

// realAddLemma picks the inequality-addition leaf for the strictness combination.
func realAddLemma(accStrict, itStrict bool, a, b, c, d Term) *prop.PropWrapper {
	switch {
	case !accStrict && !itStrict:
		return realAddLe2(a, b, c, d)
	case accStrict && itStrict:
		return realAddLt2(a, b, c, d)
	case accStrict && !itStrict:
		return realAddLtLe(a, b, c, d)
	default:
		return realAddLeLt(a, b, c, d)
	}
}

// realReplay turns a Farkas certificate λ over prs into `hyps ⊢ ⊥` over ℝ.
// Materializes each used row's proof via pr.proof().
func realReplay(prs []provRow, lambda []_Integer) (*prop.PropWrapper, bool) {
	var items []scaledIneq
	for j, lam := range lambda {
		if lam.sign() <= 0 {
			continue
		}
		pr := prs[j]
		prov, ok := pr.proof()
		if !ok {
			return nil, false
		}
		if lam.isOne() {
			items = append(items, scaledIneq{prov, pr.L, pr.R, pr.strict})
			continue
		}
		var sc *prop.PropWrapper
		if pr.strict {
			sc = mp(realLtScale(lam, pr.L, pr.R), prov)
		} else {
			sc = mp(realLeScale(lam, pr.L, pr.R), prov)
		}
		items = append(items, scaledIneq{sc, realMonoTerm(lam, pr.L), realMonoTerm(lam, pr.R), pr.strict})
	}
	if len(items) == 0 {
		return nil, false
	}

	// sum: fold items into one `accL ⋈ accR`.
	acc := items[0]
	for _, it := range items[1:] {
		lem := realAddLemma(acc.strict, it.strict, acc.L, acc.R, it.L, it.R)
		comb := mp(mp(lem, acc.ineq), it.ineq)
		acc = scaledIneq{comb, realPlusT(acc.L, it.L), realPlusT(acc.R, it.R), acc.strict || it.strict}
	}

	// ring-normalize both sides: accL = buildTerm(lfL), accR = buildTerm(lfR).
	lfL, wL, _ := realNormalizeProof(acc.L)
	lfR, wR, _ := realNormalizeProof(acc.R)
	PL := realDomain.buildTerm(lfL)
	PR := realDomain.buildTerm(lfR)

	opC := realLe
	if acc.strict {
		opC = realLt
	}
	// ⊢ (accL ⋈ accR) = (PL ⋈ PR)
	cong := wL.LeftApply(opC).RightApply(acc.R).
		EqTrans(wR.LeftApply(ext.Apply(opC, PL)))
	transported := cong.EqMP(acc.ineq) // hyps ⊢ (PL ⋈ PR)

	// cancel the common variable part, leaving a constant relation cL ⋈ cR.
	var cmpProof *prop.PropWrapper
	var cL, cR Term
	if len(lfL.monos) > 0 {
		P := realMonoChainTerm(lfL.monos)
		cL = realLitOf(lfL.konst)
		cR = realLitOf(lfR.konst)
		var cancel *prop.PropWrapper
		if acc.strict {
			cancel = realAddLcancelLt(P, cL, cR)
		} else {
			cancel = realAddLcancelLe(P, cL, cR)
		}
		cmpProof = cancel.EqMP(transported) // hyps ⊢ (cL ⋈ cR)
	} else {
		cmpProof = transported
		cL, cR = PL, PR // both realLit(konst)
	}

	// close: the constant relation is numerically false ⇒ ⊥.
	var g4 *prop.PropWrapper
	var ok bool
	if acc.strict {
		g4, ok = realNormNatLt(cL, cR)
	} else {
		g4, ok = realNormNatLe(cL, cR)
	}
	if !ok || !prop.Rhs(g4).Equals(prop.F) {
		return nil, false // certificate did not yield a false constant relation
	}
	return g4.EqMP(cmpProof), true // hyps ⊢ ⊥
}

// RealLinRefuteProof decides unsatisfiability of a real linear-constraint set
// and, on success, returns `{h₁ … hₙ} ⊢ ⊥`. ok=false ⇒ nonlinear input or not
// ℚ-Farkas refutable. Satisfies refuteFn, so realProveWith transports it.
func RealLinRefuteProof(cs []LinConstraint) (*prop.PropWrapper, bool) {
	// The monomials' sign rows (real_sign_rows.go): over ℝ a product atom is
	// an unknown with no sign, so a refutation that turns on `&0 ≤ a·b` — from
	// the factors' stated signs, or because the monomial is a square — has no
	// row to combine until this pass supplies one.
	if extra := realMonomialSignConstraints(cs); len(extra) > 0 {
		cs = append(slices.Clone(cs), extra...)
	}
	tbl, signed, prs, built := realBuildAll(cs)
	if !built {
		return nil, false
	}
	lambda, ok := refute(tbl.n(), signed)
	if !ok {
		return nil, false
	}
	return realReplay(prs, lambda)
}

// RealLinProve is the forward `{hyps} ⊢ goal` wrapper over ℝ — the mirror of
// LinProve/proveWith. Goal shapes: `<`/`≤`/`≠` directly; `>`/`≥` by the
// definitional flip; `=` by antisymmetry of two `≤` proofs. Non-comparison /
// nonlinear hyps are dropped. ok=false ⇒ goal not a recognized real linear
// comparison, or its negation is ℚ-Farkas satisfiable.
func RealLinProve(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	key := linQuestionKey(hs, goal)
	if e, ok := realLinMemo.lookup(key, hs, goal); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := realProveWith(realDomain.hypConstraints(slices.Values(hs)), goal)
	if !ok {
		proof = nil
	}
	realLinMemo.store(key, linAnswer{hyps: hs, goal: goal, proof: proof})
	return proof, ok
}

// linProveMemo memoizes RealLinProve per question — the hypotheses in
// their order and the goal. The field layer asks the same questions of one
// context again and again: the sign of a divisor is wanted by the unit
// facts, by the clearing of a quotient and by the cancellation, at the top
// of every atom decision and again at its re-entry, and the case split
// asks its branch questions once per atom per direction. On a thirteen-hypothesis ε-δ context whose
// quotients the basis reads as products, nine questions in ten had been
// asked before (42 000 runs, 3 976 questions). The answer is a function of
// the question and the lemma bundle: a proof is a sequent over the
// question's own hypotheses, a decline says the negated goal is satisfiable
// beside them, and the bundle setters drop the memo with the constraint
// memos (resetConstraintMemos). The hit test is EXACT equality, term by
// term — the constraint memo's, for its reason; the joined AlphaKeys are
// only the bucket. The entries serve ONE arith step — the questions repeat
// inside a step, over one context — and are released when it ends
// (ReleaseStepMemos); within the step each tier is bounded.
type linProveMemo struct {
	mu       sync.Mutex
	proofs   map[string]linAnswer
	declines map[string]linAnswer
}

// A proof is a kernel derivation and a decline is a key and a list of terms
// the context holds anyway, so the two are bounded apart. The repeated
// questions that are answered by a proof are few and close together — the
// sign of a divisor, asked by one handler after another — and a small tier
// serves them as well as an unbounded one (measured on the wide context:
// the same time either way, and a third more with no proof kept); the
// declines are what a failing decision repeats in the thousands.
const (
	linMemoProofCap   = 256
	linMemoDeclineCap = 8192
)

type linAnswer struct {
	hyps  []Term
	goal  Term
	proof *prop.PropWrapper // nil: declined
}

var realLinMemo linProveMemo

func linQuestionKey(hyps []Term, goal Term) string {
	var b strings.Builder
	b.WriteString(string(goal.AlphaKey()))
	for _, h := range hyps {
		b.WriteByte('|')
		b.WriteString(string(h.AlphaKey()))
	}
	return b.String()
}

func (m *linProveMemo) lookup(key string, hyps []Term, goal Term) (linAnswer, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	e, ok := m.proofs[key]
	if !ok {
		e, ok = m.declines[key]
	}
	if !ok || !e.goal.Equals(goal) || !slices.EqualFunc(e.hyps, hyps, Term.Equals) {
		return linAnswer{}, false
	}
	return e, true
}

func (m *linProveMemo) store(key string, e linAnswer) {
	m.mu.Lock()
	defer m.mu.Unlock()
	tier, limit := &m.declines, linMemoDeclineCap
	if e.proof != nil {
		tier, limit = &m.proofs, linMemoProofCap
	}
	if len(*tier) >= limit {
		*tier = nil
	}
	if *tier == nil {
		*tier = make(map[string]linAnswer)
	}
	(*tier)[key] = e
}

func (m *linProveMemo) reset() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.proofs, m.declines = nil, nil
}

func realProveWith(hypCs []LinConstraint, goal Term) (*prop.PropWrapper, bool) {
	// `>` / `≥`: reduce to swapped `<` / `≤` via the definitional bridge.
	if a, b, ok := realDomain.matchGt(goal); ok {
		inner, iok := realProveWith(hypCs, realLtT(b, a))
		if !iok {
			return nil, false
		}
		return realGtBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := realDomain.matchGe(goal); ok {
		inner, iok := realProveWith(hypCs, realLeT(b, a))
		if !iok {
			return nil, false
		}
		return realGeBridge(a, b).EqSym().EqMP(inner), true
	}

	// `=`: a=b from (a≤b) and (b≤a) by antisymmetry.
	if a, b, ok := ext.MatchesEQ(goal); ok && realDomain.isElem(a) {
		if !realDomain.isLinear(a) || !realDomain.isLinear(b) {
			return nil, false
		}
		g1, ok1 := realProveWith(hypCs, realLeT(a, b))
		g2, ok2 := realProveWith(hypCs, realLeT(b, a))
		if !ok1 || !ok2 {
			return nil, false
		}
		return mp(mp(realLessEqAntisym(a, b), g1), g2), true
	}

	// `<` / `≤` / `≠`: refute the negated goal, then peel it back.
	neg, nTerm, finish, ok := realNegateGoal(goal)
	if !ok {
		return nil, false
	}
	cs := make([]LinConstraint, len(hypCs), len(hypCs)+1)
	copy(cs, hypCs)
	cs = append(cs, neg)
	R, rok := RealLinRefuteProof(cs)
	if !rok {
		return nil, false
	}
	return finish(R.NegHyp(nTerm)), true // R: {hyps, nTerm} ⊢ ⊥
}

// realNegateGoal is the ℝ mirror of negateGoal: the constraint to add for
// refutation, the term it contributes as a hypothesis, and the finisher that
// rewrites `⊢ ¬nTerm` back into `⊢ goal`.
func realNegateGoal(goal Term) (neg LinConstraint, nTerm Term, finish func(*prop.PropWrapper) *prop.PropWrapper, ok bool) {
	// a<b : add b≤a; ⊢ ¬(b≤a) ──NotLessEq──▸ ⊢ a<b
	if a, b, m := realDomain.matchLt(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLE}, realLeT(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return realNotLE(b, a).EqMP(g) }, true
	}
	// a≤b : add b<a; ⊢ ¬(b<a) ──NotLessThan──▸ ⊢ a≤b
	if a, b, m := realDomain.matchLe(goal); m {
		return LinConstraint{Lhs: b, Rhs: a, Op: opLT}, realLtT(b, a),
			func(g *prop.PropWrapper) *prop.PropWrapper { return realNotLT(b, a).EqMP(g) }, true
	}
	// a≠b (=¬(a=b)) : add a=b; ⊢ ¬(a=b) IS the goal, no rewrite needed.
	if inner := ext.MatchesNOT(goal); inner != nil {
		if a, b, m := ext.MatchesEQ(inner); m && realDomain.isElem(a) &&
			realDomain.isLinear(a) && realDomain.isLinear(b) {
			return LinConstraint{Lhs: a, Rhs: b, Op: opEQ}, eqT(a, b),
				func(g *prop.PropWrapper) *prop.PropWrapper { return g }, true
		}
	}
	return LinConstraint{}, nil, nil, false
}
