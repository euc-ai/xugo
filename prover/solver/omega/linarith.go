package omega

import (
	"encoding/binary"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/ext/prop"
)

// linarith's untrusted decision core: extract linear constraints over
// num and refute an unsatisfiable conjunction via ℝ≥0-Farkas, found by
// Fourier–Motzkin elimination with multiplier tracking. The multiplier vector
// (λ over the input rows) is the Farkas certificate the replay
// (nat_linarith.go) turns into a real refutation proof. This file proves nothing —
// it decides and produces the certificate, which the replay re-checks.
//
// Soundness of refutation: FM combines rows with NON-NEGATIVE multipliers, so a
// derived all-zero-coefficient row `k ⋈ 0` with k infeasible is a genuine
// positive combination witnessing unsat over ℝ≥0 ⊇ ℕ. (Completeness is only
// ℚ-Farkas — integrality / the implicit xᵢ≥0 beyond what we add is out of
// scope here; the integer layer, nat_omega.go, adds integrality.)

type relOp int

const (
	opLE relOp = iota // ≤
	opLT              // <
	opEQ              // =
)

// atomTable assigns stable dense indices to atoms, deduping by AlphaEquals.
type atomTable struct{ atoms []Term }

func (t *atomTable) index(a Term) int {
	for i, x := range t.atoms {
		if x.AlphaEquals(a) {
			return i
		}
	}
	t.atoms = append(t.atoms, a)
	return len(t.atoms) - 1
}

func (t *atomTable) n() int { return len(t.atoms) }

// row is `Σ coeffs[i]·atom_i + konst ⋈ 0` (⋈ = `<` if strict else `≤`). lambda is
// nil during the decision pass; the certificate pass seeds and propagates its
// non-negative combination over the input rows.
type row struct {
	coeffs _Vector
	konst  _Integer
	strict bool
	lambda _Vector
}

// padCoeffs fixes a row's coefficient width without attaching certificate
// state. FM's first pass operates exclusively on rows in this form.
func (r row) padCoeffs(nAtoms int) row {
	return row{coeffs: r.coeffs.padded(nAtoms), konst: r.konst, strict: r.strict}
}

// wideBytes is what r's coefficients and constant hold beyond their words —
// nothing while every one of them is in the int64 range.
func (r row) wideBytes() int { return r.coeffs.wideBytes() + r.konst.wideBytes() }

// signedDifference is the signed coefficient vector and constant of lf − rf
// over tbl's atoms, entering the atoms tbl has not met: coeffs[i] is the
// coefficient of tbl.atoms[i], and len(coeffs) is tbl.n() on return.
func signedDifference(tbl *atomTable, lf, rf linForm) (coeffs []_Integer, konst _Integer) {
	coeffs = make([]_Integer, tbl.n())
	at := func(a Term) int {
		i := tbl.index(a)
		for len(coeffs) <= i {
			coeffs = append(coeffs, _Integer{})
		}
		return i
	}
	for _, m := range lf.monos {
		i := at(m.atom)
		coeffs[i] = coeffs[i].add(m.coeff)
	}
	for _, m := range rf.monos {
		i := at(m.atom)
		coeffs[i] = coeffs[i].sub(m.coeff)
	}
	return coeffs, lf.konst.sub(rf.konst)
}

// negated is the vector of −c for c in coeffs.
func negated(coeffs []_Integer) []_Integer {
	out := make([]_Integer, len(coeffs))
	for i, c := range coeffs {
		out[i] = c.neg()
	}
	return out
}

// unitRow is the row whose only nonzero coefficient is c at atom i of nAtoms.
func unitRow(nAtoms, i int, c _Integer) row {
	coeffs := make([]_Integer, nAtoms)
	coeffs[i] = c
	return row{coeffs: vectorOf(coeffs)}
}

// LinConstraint is an input constraint `lhs ⋈ rhs` over num.
type LinConstraint struct {
	Lhs, Rhs Term
	Op       relOp
	// Hyp, when non-nil, is the ORIGINAL hypothesis term to assume and carry
	// instead of the canonical `Lhs Op Rhs`. It is set for a `>`/`≥` hypothesis,
	// whose canonical form is the swapped `<`/`≤` (Lhs/Rhs already swapped, Op =
	// opLT/opLE) but whose proof must keep the original `>`/`≥` term as its
	// hypothesis, so the refutation's hyps stay a subset of the goal's (the
	// IsStronger contract a tactic closes through). canonAssume bridges Hyp to the
	// canonical comparison via gt/geBridge. nil ⇒ assume `Lhs Op Rhs` directly.
	Hyp Term
	// HypProof, when non-nil, is the precomputed base proof of the assumption
	// term — `{provenance} ⊢ T` where T is Hyp if Hyp != nil else the canonical
	// comparison (`Lhs Op Rhs`, or `eqT(Lhs,Rhs)` for opEQ). It replaces the
	// default `prop.Assume(T)` that canonAssume / the EQ branch would build, so
	// the carried hypotheses can differ from T itself. Set for a conjunction-
	// flattened conjunct: T is the conjunct, but the provenance is the whole `∧`
	// hyp (the projection `{p∧q} ⊢ p`), keeping the refutation's hyps a subset of
	// the goal's. nil ⇒ assume T directly (the plain / `>`/`≥` paths, unchanged).
	HypProof *prop.PropWrapper
}

// extractRow turns `lhs ⋈ rhs` into rows `Σcᵢxᵢ+k ⋈ 0` (an `=` yields two ≤
// rows). ok=false if either side is nonlinear. The package-level wrapper uses
// natDomain; the real refutation calls realDomain.extractRow.
func extractRow(tbl *atomTable, c LinConstraint) ([]row, bool) {
	return natDomain.extractRow(tbl, c)
}

// extractRow is the domain-generic decision-row extraction (the row coefficients
// come from d.linOf). The atomTable / row representation is domain-agnostic.
func (d *Domain) extractRow(tbl *atomTable, c LinConstraint) ([]row, bool) {
	lf, ok1 := d.linOf(c.Lhs)
	rf, ok2 := d.linOf(c.Rhs)
	if !ok1 || !ok2 {
		return nil, false
	}
	coeffs, konst := signedDifference(tbl, lf, rf)

	mk := func(cf []_Integer, k _Integer, strict bool) row {
		return row{coeffs: vectorOf(cf), konst: k, strict: strict}
	}
	switch c.Op {
	case opLE:
		return []row{mk(coeffs, konst, false)}, true
	case opLT:
		return []row{mk(coeffs, konst, true)}, true
	case opEQ:
		return []row{mk(coeffs, konst, false), mk(negated(coeffs), konst.neg(), false)}, true
	}
	return nil, false
}

// buildRows extracts all constraints and appends xᵢ≥0 (i.e. -xᵢ ≤ 0) for every
// atom. It returns decision-only rows; refute owns certificate materialization.
//
// The xᵢ≥0 injection is `num`-specific (every nat is non-negative). The ℝ and ℤ
// twins build their own rows (realBuildAll, intBuildAll) and inject none — their
// variables are free — so they have no `zeroLe`/`ZeroLessEq` discharge leaf either.
func buildRows(cs []LinConstraint) (*atomTable, []row, bool) {
	tbl := &atomTable{}
	var rows []row
	for _, c := range cs {
		rs, ok := extractRow(tbl, c)
		if !ok {
			return nil, nil, false
		}
		rows = append(rows, rs...)
	}
	// nonnegativity of each atom over ℕ: -xᵢ ≤ 0
	for i := 0; i < tbl.n(); i++ {
		rows = append(rows, unitRow(tbl.n(), i, integerOf(-1)))
	}
	// Fix the coefficient width. Certificate vectors are deliberately absent:
	// refute seeds them only after a certificate-free pass finds a contradiction.
	for i := range rows {
		rows[i] = rows[i].padCoeffs(tbl.n())
	}
	return tbl, rows, true
}

// infeasibleConst reports whether an all-zero-coefficient row is unsatisfiable.
func (r row) infeasibleConst() bool {
	if r.strict {
		return r.konst.sign() >= 0 // konst < 0 required, but konst ≥ 0
	}
	return r.konst.sign() > 0 // konst ≤ 0 required, but konst > 0
}

// Resource fuses for one fmRefute pass. Fourier–Motzkin is doubly-exponential
// in the worst case even with the direction dedup and the greedy order below;
// a pathological satisfiable system (the failing-to-refute direction runs ALL
// rounds with no early infeasible-row exit) can otherwise grow a round to
// ~10⁹ rows → OOM (a dist triangle with equality hyps:
// 64k live rows at the second-to-last
// dimension, each carrying an O(nRows) λ vector). Hitting either fuse
// declines the refutation (nil,false) — sound, merely incomplete.
//
// The budgets are stated in RESOURCE units and sized by policy ("how much of
// the host process may a single decider call consume"), NOT calibrated to any
// particular goal class — row count is a bad unit because a row's cost varies
// with its width (nAtoms coeffs + nRows λ entries):
//   - fmByteBudget bounds the transient row memory of a round: each row is
//     charged its actual width, so wide systems get proportionally fewer rows
//     and narrow ones more, plus whatever its coefficients hold beyond their
//     words (row.wideBytes) — elimination multiplies coefficients, and their
//     growth past the int64 range is memory the same budget pays for.
//   - fmWorkBudget bounds total combineRows calls — the dominant operation —
//     across the whole call: a deterministic CPU fuse (~a second, vs the
//     incident's ~10⁹-combine round). A COUNTER, not a deadline, on purpose:
//     decline decisions must be deterministic or proof search and replay
//     diverge (cf. the CNF replay unify-timeout flake).
//
// Healthy loads sit 3–5 orders of magnitude below both (measured maxima
// across the omega + engine arith suites under the greedy order: 88 combines
// and 42 pre-dedup rows per call) — verified headroom, not the sizing basis.
const (
	fmByteBudget = 128 << 20  // transient row bytes per round
	fmWorkBudget = 16_000_000 // combineRows per FM pass
)

// refute runs Fourier–Motzkin in two deterministic passes. The first pass carries
// no lambda vectors: failure therefore pays only for the decision model. On
// success, seedCertificateRows attaches unit lambdas to the ORIGINAL rows and
// the exact same fmRefute function runs again to produce the Farkas certificate.
// Sharing one implementation makes elimination order, dedup, and resource fuses
// identical by construction rather than maintaining a separate replay algorithm.
func refute(nAtoms int, rows []row) (lambda []_Integer, ok bool) {
	if _, found := fmRefute(nAtoms, rows); !found {
		return nil, false
	}
	certificate, replayed := fmRefute(nAtoms, seedCertificateRows(rows))
	if !replayed {
		panic("omega: deterministic FM certificate replay diverged from search")
	}
	return certificate.entries(), true
}

// seedCertificateRows returns a shallow copy of rows with one unit lambda per
// input row. Coefficients are immutable during FM and may be shared; only the
// certificate vectors are new. This O(nRows²) state is allocated on success.
func seedCertificateRows(rows []row) []row {
	seeded := make([]row, len(rows))
	for i, r := range rows {
		r.lambda = _Vector{words: make([]int64, len(rows))}
		r.lambda.words[i] = 1
		seeded[i] = r
	}
	return seeded
}

// fmRefute is the single Fourier–Motzkin engine used by both passes. When the
// input lambdas are empty, combineRows keeps every derived lambda empty; when
// they are seeded, it propagates the complete Farkas certificate.
//
// Dimensions are eliminated in GREEDY order — each round picks the remaining
// dimension minimizing |pos|·|neg|, the classic FM heuristic — rather than
// atom-index order. The certificate is order-independent (λ is tracked over
// the ORIGINAL rows), but the intermediate row growth is wildly order-
// dependent: the incident system above blows up past 64k rows in index order
// yet never exceeds ~10³ rows greedily (and the proveSplit client then CLOSES
// the goal instead of diverging). The greedy scan itself is O(dims²·rows) —
// noise next to one elimination round.
func fmRefute(nAtoms int, rows []row) (lambda _Vector, ok bool) {
	// check existing all-zero rows first
	for _, r := range rows {
		if r.coeffs.isZero() && r.infeasibleConst() {
			return r.lambda, true
		}
	}
	// Prune the input before the first greedy scan. Besides avoiding redundant
	// pair products in round one, this lets the greedy cost see the actual live
	// direction set rather than duplicate hypotheses. dedupRows is stable by
	// first-seen direction and keeps the selected original row's lambda, so the
	// decision and certificate passes remain identical and certificate indices
	// still refer to the original, unpruned input rows.
	cur := dedupRows(rows)
	// Per-call fuses (see the budget consts): a row's charge deliberately
	// includes the eventual lambda width even during the certificate-free pass,
	// and counts the wide storage of its coefficients and constant only, never
	// of its lambda. Both passes therefore take the same path and hit the same
	// resource boundary; work counts every combineRows.
	rowBytes := 8 * (nAtoms + len(rows) + 2)
	work := 0
	remaining := make([]int, nAtoms)
	for i := range remaining {
		remaining[i] = i
	}
	for len(remaining) > 0 {
		bestIdx, bestCost := -1, int64(-1)
		for i, cand := range remaining {
			var np, nn int64
			for _, r := range cur {
				switch r.coeffs.sign(cand) {
				case 1:
					np++
				case -1:
					nn++
				}
			}
			cost := np * nn
			if bestCost < 0 || cost < bestCost {
				bestCost, bestIdx = cost, i
			}
		}
		v := remaining[bestIdx]
		remaining = slices.Delete(remaining, bestIdx, bestIdx+1)
		var pos, neg, zero []row
		for _, r := range cur {
			switch r.coeffs.sign(v) {
			case 1:
				pos = append(pos, r)
			case -1:
				neg = append(neg, r)
			default:
				zero = append(zero, r)
			}
		}
		next := zero
		roundBytes := len(next) * rowBytes
		for _, r := range next {
			roundBytes += r.wideBytes()
		}
		for _, p := range pos {
			for _, nrow := range neg {
				work++
				if work > fmWorkBudget {
					return _Vector{}, false // CPU fuse — decline, don't spin
				}
				mp := nrow.coeffs.at(v).neg() // > 0
				mn := p.coeffs.at(v)          // > 0
				comb := combineRows(p, nrow, mp, mn)
				if comb.coeffs.isZero() {
					if comb.infeasibleConst() {
						return comb.lambda, true
					}
					// feasible constant row: drop (no information)
					continue
				}
				next = append(next, comb)
				roundBytes += rowBytes + comb.wideBytes()
				if roundBytes > fmByteBudget {
					return _Vector{}, false // memory fuse — decline, don't OOM
				}
			}
		}
		// Redundancy elimination — the load-bearing curb on Fourier–Motzkin's
		// doubly-exponential row growth. Each elimination round produces up to
		// |pos|·|neg| new rows; without pruning, the next round squares that and
		// the count blows up super-exponentially (a 6-monus / 9-atom goal hits
		// >10⁸ combineRows). Two cheap, SOUND prunings keep the live set linear in
		// the distinct constraint DIRECTIONS rather than exponential:
		//   - GCD-reduce each row's coefficient direction for keying (a row and its
		//     scalar multiple are the same half-plane);
		//   - per direction keep only the STRONGEST constraint (a same-direction row
		//     with a weaker konst is implied — dropping it preserves the feasible
		//     set, so FM stays complete and the kept row's lambda is a valid Farkas
		//     certificate). reduceForKey divides coeffs by their gcd and compares
		//     konst/g exactly, making "strongest" scale-invariant.
		//
		// A round that appended no combination left a subset of the rows it
		// began with, in their order, and those were pruned already.
		if len(next) == len(zero) {
			cur = next
			continue
		}
		cur = dedupRows(next)
	}
	return _Vector{}, false
}

type scaledKonst struct {
	num _Integer
	den _Integer // positive
}

func (k scaledKonst) cmp(o scaledKonst) int {
	return k.num.mul(o.den).cmp(o.num.mul(k.den))
}

// dedupRows collapses Fourier–Motzkin rows that denote the same or a weaker
// half-plane, keeping one representative per coefficient DIRECTION — the
// strongest (largest scale-normalized konst; strict beats non-strict at a tie).
// Output direction order is first-seen order, even when a later row replaces
// that direction's representative, so equal numeric passes remain deterministic.
// Sound for refutation: a same-direction row with a smaller konst is implied by
// the kept one (`Σcx+k₁ ⋈ 0` with k₁ ≥ k₂ ⇒ the k₂ row holds wherever the k₁ row
// does), so removing it changes neither the feasible set nor refutability, and
// the surviving row carries a valid Farkas λ. This is what keeps FM's row set
// bounded by the number of distinct directions instead of exploding.
func dedupRows(rows []row) []row {
	type best struct {
		idx    int
		konst  scaledKonst // konst/g, for scale-invariant "strongest" compare
		strict bool
	}
	seen := make(map[string]best, len(rows))
	order := make([]string, 0, len(rows))
	for i, r := range rows {
		key, k := reduceForKey(r.coeffs, r.konst)
		prev, ok := seen[key]
		if !ok {
			seen[key] = best{idx: i, konst: k, strict: r.strict}
			order = append(order, key)
			continue
		}
		// keep the STRONGER row: larger reduced konst, or strict at an equal konst.
		cmp := k.cmp(prev.konst)
		if cmp > 0 || (cmp == 0 && r.strict && !prev.strict) {
			seen[key] = best{idx: i, konst: k, strict: r.strict}
		}
	}
	out := make([]row, 0, len(order))
	for _, key := range order {
		out = append(out, rows[seen[key].idx])
	}
	return out
}

// reduceForKey returns a canonical string key for a row's coefficient DIRECTION
// (coeffs divided by gcd(coeffs)) plus konst/gcd(coeffs), so two rows that are
// positive scalar multiples of each other share a key and their konsts are
// compared on the same scale. gcd 0 can occur only for a feasible constant input
// row (fmRefute returns on infeasible ones, while derived constant rows are
// dropped before dedup); divisor 1 gives those rows one canonical direction.
func reduceForKey(coeffs _Vector, konst _Integer) (string, scaledKonst) {
	g := coeffs.gcd()
	if g.isZero() {
		g = integerOne
	}
	// Each entry's encoding is self-delimiting (_Integer.appendKey), hence the
	// stream is canonical for the coefficient vector without separators.
	var b strings.Builder
	b.Grow(2 * coeffs.len()) // an entry occupies at least two bytes
	if coeffs.wide == nil && g.wide == nil {
		var buf [binary.MaxVarintLen64]byte
		for _, w := range coeffs.words {
			b.WriteByte(0)
			b.Write(buf[:binary.PutVarint(buf[:], w/g.word)])
		}
	} else {
		for i := range coeffs.words {
			reduced, _ := coeffs.at(i).divMod(g)
			reduced.appendKey(&b)
		}
	}
	return b.String(), scaledKonst{num: konst, den: g}
}

// combineRows = mp·p + mn·n (both multipliers > 0), summing coeffs/konst/lambda.
//
// The rows are not divided by their gcd, which would curb Fourier–Motzkin
// coefficient growth: lambda must stay the true certificate over the input
// rows and cannot be scaled with them. The entries are exact at any size, and
// fmRefute charges their growth to its byte budget.
func combineRows(p, n row, mp, mn _Integer) row {
	comb := row{
		coeffs: combination(mp, p.coeffs, mn, n.coeffs),
		konst:  mp.mul(p.konst).add(mn.mul(n.konst)),
		strict: p.strict || n.strict,
	}
	if p.lambda.len() != 0 {
		comb.lambda = combination(mp, p.lambda, mn, n.lambda)
	}
	return comb
}

// LinRefute decides whether the conjunction of constraints is unsatisfiable over
// ℕ by ℚ≥0-Farkas. Returns the input rows (post =-split + nonneg) and the Farkas
// multiplier vector λ (same length/order as rows) on success. ok=false ⇒ either
// nonlinear input or not refutable by ℚ-Farkas. The certificate is UNTRUSTED;
// the replay re-derives the contradiction as a real proof.
func LinRefute(cs []LinConstraint) (rows []row, lambda []_Integer, ok bool) {
	tbl, rows, built := buildRows(cs)
	if !built {
		return nil, nil, false
	}
	lambda, ok = refute(tbl.n(), rows)
	if !ok {
		return nil, nil, false
	}
	return rows, lambda, true
}
