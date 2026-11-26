package omega

import (
	"strings"

	"github.com/euc-ai/xugo/ext/prop"
)

// Exact elimination of equations: the integer core's step before
// Fourier–Motzkin, the same over ℕ and ℤ.
//
// Fourier–Motzkin projects over ℚ, and an equation reaches it as two `≤`
// rows. Eliminating between them an atom whose coefficient is not ±1 keeps
// the rational shadow and loses what the integers add: from `n = 2·q + r`,
// `r = 1` and `2 ≤ n ≤ 2`, projecting q away leaves a system with a
// solution, where q = 1/2 was the only one. Solving the equation for an atom
// of coefficient ±1 and substituting loses nothing — that atom is an integer
// whenever the others are — and each substituted row is then rounded by the
// gcd of its own coefficients (`2·q ≤ 1` to `q ≤ 0`, `1 ≤ 2·q` to `1 ≤ q`),
// which is where the contradiction shows.
//
// An equation is two rows `Σcx + k ≤ 0` and `−Σcx − k ≤ 0`, whether an input
// equation gave them or two inequalities meet (`1 ≤ r` and `r ≤ 1`). One
// with no atom of coefficient ±1 is left to its own two rounded rows.
//
// A row is held as a non-negative combination of NODES: the input rows, and
// the rows a rounding produced. Substituting adds combinations — arithmetic
// on multipliers, no proof. Only a rounding makes a node, and its proof (the
// combination summed, then the domain's rounding step) is built when the
// final refutation takes that node.

// _EliminationLeaves are the proof steps of a domain the elimination composes.
type _EliminationLeaves struct {
	// sum adds the nodes λ takes, each scaled by its multiplier, into one
	// inequality (sumRows, intSumRows).
	sum func(nodes []provRow, lambda []_Integer) (scaledIneq, bool)
	// rounded is the node of the row `Σ nc·x + nk ≤ 0` over tbl's atoms: the
	// rounding by g > 1, with remainder s ∈ [0, g), of the inequality sum
	// proves, whose signed form is `Σ g·nc·x + (g·nk − s) ≤ 0`.
	rounded func(tbl *atomTable, sum func() (scaledIneq, bool), nc []_Integer, nk, g, s _Integer) provRow
}

// natEliminationLeaves rounds through the rank-1 cut (cutProv).
var natEliminationLeaves = &_EliminationLeaves{
	sum: sumRows,
	rounded: func(tbl *atomTable, sum func() (scaledIneq, bool), nc []_Integer, nk, g, s _Integer) provRow {
		lfL, lt2, lfR, rt := signedToLe(nc, nk, tbl)
		return provRow{L: lt2, R: rt, build: func() (*prop.PropWrapper, bool) {
			acc, ok := sum()
			if !ok {
				return nil, false
			}
			return cutProv(acc.ineq, acc.L, acc.R, lt2, rt, lfL, lfR, g, s)
		}}
	},
}

// intEliminationLeaves rounds through discreteness (intProveLe), as the rank-1
// rounding cut over ℤ does.
var intEliminationLeaves = &_EliminationLeaves{
	sum: intSumRows,
	rounded: func(tbl *atomTable, sum func() (scaledIneq, bool), nc []_Integer, nk, _, _ _Integer) provRow {
		lt2, rt := intSignedToLe(nc, nk, tbl)
		return provRow{L: lt2, R: rt, build: func() (*prop.PropWrapper, bool) {
			acc, ok := sum()
			if !ok {
				return nil, false
			}
			return intProveLe(LinConstraint{Lhs: acc.L, Rhs: acc.R, Op: opLE, HypProof: acc.ineq}, lt2, rt)
		}}
	},
}

// _EliminatedRow is one row `Σ coeffs·x + konst ≤ 0` of the system under
// elimination, with the combination of nodes that proves it: cert[j] is the
// multiplier of node j, and a node past its end has multiplier 0.
type _EliminatedRow struct {
	coeffs []_Integer
	konst  _Integer
	cert   []_Integer
}

// _EquationElimination is a system of non-strict rows with its equations
// eliminated: the nodes its rows are combinations of, and the rows.
type _EquationElimination struct {
	tbl    *atomTable
	leaves *_EliminationLeaves
	nodes  []provRow
	rows   []_EliminatedRow
}

// eliminateEquations eliminates the equations of the non-strict rows fm,
// index-aligned with their proofs prs. ok=false, and nothing to read, where
// no equation of the system has an atom of coefficient ±1: the caller
// refutes the rows it gave.
func eliminateEquations(tbl *atomTable, fm []row, prs []provRow, leaves *_EliminationLeaves) (*_EquationElimination, bool) {
	e := &_EquationElimination{tbl: tbl, leaves: leaves, nodes: make([]provRow, len(prs))}
	for j, pr := range prs {
		if pr.strict {
			panic("omega: equation elimination was handed a strict row")
		}
		e.nodes[j] = memoizedRow(pr)
	}
	n := tbl.n()
	for j, r := range fm {
		cert := make([]_Integer, j+1)
		cert[j] = integerOne
		if kept, ok := e.rounded(_EliminatedRow{coeffs: r.padCoeffs(n).coeffs.entries(), konst: r.konst, cert: cert}); ok {
			e.rows = append(e.rows, kept)
		}
	}
	fired := false
	for {
		upper, lower, atom, found := e.unitEquation()
		if !found {
			return e, fired
		}
		fired = true
		e.substitute(upper, lower, atom)
	}
}

// substitute eliminates atom, of coefficient +1 in the row upper and −1 in
// the row lower, the two an equation: every other row holding the atom takes
// the multiple of upper or lower that cancels it, and the equation leaves
// the system with the atom.
func (e *_EquationElimination) substitute(upper, lower, atom int) {
	next := make([]_EliminatedRow, 0, len(e.rows))
	for i, r := range e.rows {
		if i == upper || i == lower {
			continue
		}
		c := r.coeffs[atom]
		if c.isZero() {
			next = append(next, r)
			continue
		}
		partner, mult := e.rows[lower], c
		if c.sign() < 0 {
			partner, mult = e.rows[upper], c.neg()
		}
		sum := _EliminatedRow{
			coeffs: make([]_Integer, len(r.coeffs)),
			konst:  r.konst.add(mult.mul(partner.konst)),
			cert:   make([]_Integer, max(len(r.cert), len(partner.cert))),
		}
		for a := range sum.coeffs {
			sum.coeffs[a] = r.coeffs[a].add(mult.mul(partner.coeffs[a]))
		}
		copy(sum.cert, r.cert)
		for j, m := range partner.cert {
			sum.cert[j] = sum.cert[j].add(mult.mul(m))
		}
		if kept, ok := e.rounded(sum); ok {
			next = append(next, kept)
		}
	}
	e.rows = next
}

// rounded is r divided by the gcd g of its coefficients, the constant
// rounded: r itself where g ≤ 1, and where g > 1 a row of its own node,
// whose proof is r's combination summed and rounded. ok=false for the row
// `k ≤ 0` with k ≤ 0, which says nothing; with k > 0 it is the
// contradiction, and it is kept.
func (e *_EquationElimination) rounded(r _EliminatedRow) (_EliminatedRow, bool) {
	g := vecGCD(r.coeffs)
	if g.isZero() {
		return r, r.konst.sign() > 0
	}
	if g.isOne() {
		return r, true
	}
	nc, nk, _ := tightenLe(r.coeffs, r.konst)
	cert := r.cert
	sum := func() (scaledIneq, bool) {
		acc, ok := e.leaves.sum(e.nodes, cert)
		if ok && acc.strict {
			panic("omega: a sum of non-strict rows is strict")
		}
		return acc, ok
	}
	e.nodes = append(e.nodes, memoizedRow(e.leaves.rounded(e.tbl, sum, nc, nk, g, g.mul(nk).sub(r.konst))))
	unit := make([]_Integer, len(e.nodes))
	unit[len(e.nodes)-1] = integerOne
	return _EliminatedRow{coeffs: nc, konst: nk, cert: unit}, true
}

// unitEquation finds two rows that state one equation — opposite
// coefficients and opposite constants — with an atom of coefficient ±1, and
// returns the row holding +1 at that atom, the row holding −1, and the atom.
// Every row is divided by the gcd of its coefficients, so the two halves of
// an equation are opposite as written.
func (e *_EquationElimination) unitEquation() (upper, lower, atom int, found bool) {
	key := func(r _EliminatedRow, negate bool) string {
		var b strings.Builder
		for _, c := range r.coeffs {
			if negate {
				c = c.neg()
			}
			c.appendKey(&b)
		}
		k := r.konst
		if negate {
			k = k.neg()
		}
		k.appendKey(&b)
		return b.String()
	}
	at := make(map[string]int, len(e.rows))
	for i, r := range e.rows {
		if _, seen := at[key(r, false)]; !seen {
			at[key(r, false)] = i
		}
	}
	for i, r := range e.rows {
		o, ok := at[key(r, true)]
		if !ok || o == i {
			continue
		}
		for a, c := range r.coeffs {
			switch {
			case c.isOne():
				return i, o, a, true
			case c.neg().isOne():
				return o, i, a, true
			}
		}
	}
	return 0, 0, 0, false
}

// system is the eliminated rows as Fourier–Motzkin reads them.
func (e *_EquationElimination) system() []row {
	out := make([]row, len(e.rows))
	for i, r := range e.rows {
		out[i] = row{coeffs: vectorOf(r.coeffs), konst: r.konst}
	}
	return out
}

// certificate turns λ over the eliminated rows into the multipliers of the
// nodes: each row's combination scaled by its λ, added up.
func (e *_EquationElimination) certificate(lambda []_Integer) []_Integer {
	out := make([]_Integer, len(e.nodes))
	for i, lam := range lambda {
		if lam.sign() <= 0 {
			continue
		}
		for j, m := range e.rows[i].cert {
			out[j] = out[j].add(lam.mul(m))
		}
	}
	return out
}

// memoizedRow is pr with its proof built once: a node is read by every
// rounding whose combination takes it and by the final refutation.
func memoizedRow(pr provRow) provRow {
	build := pr.build
	var proof *prop.PropWrapper
	var ok, built bool
	pr.build = func() (*prop.PropWrapper, bool) {
		if !built {
			proof, ok = build()
			built = true
		}
		return proof, ok
	}
	return pr
}
