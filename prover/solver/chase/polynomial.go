package chase

// polynomial.go — integer polynomial modules: vectors whose
// coefficients are integer polynomials in the scalar atoms, the strong
// standard basis over ℤ that decides membership in the submodule a list
// of them spans, and the elimination that computes a preimage. Every
// basis row keeps its expression over the input rows, so a decision
// returns the combination the certificate spells. Coefficients stay
// integral: an S-pair cancels two leading terms, a G-pair keeps their
// gcd, and no row is ever divided by a nonunit.

import (
	"fmt"
	"math/big"
	"sort"
	"strings"
)

// _Monomial is a product of scalar variables: the sorted sequence of
// their eight-digit hexadecimal identifiers, the empty string for 1.
type _Monomial string

// monomialVariable is the monomial of the i-th scalar variable.
func monomialVariable(i int) _Monomial { return _Monomial(fmt.Sprintf("%08x", i)) }

// monomialProduct is a·b: the merge of the two sorted sequences.
func monomialProduct(a, b _Monomial) _Monomial {
	var out strings.Builder
	for len(a) != 0 && len(b) != 0 {
		if a[:8] <= b[:8] {
			out.WriteString(string(a[:8]))
			a = a[8:]
		} else {
			out.WriteString(string(b[:8]))
			b = b[8:]
		}
	}
	out.WriteString(string(a))
	out.WriteString(string(b))
	return _Monomial(out.String())
}

// monomialQuotient is a/b, and whether b divides a.
func monomialQuotient(a, b _Monomial) (_Monomial, bool) {
	var out strings.Builder
	for len(a) != 0 {
		if len(b) != 0 && a[:8] == b[:8] {
			a, b = a[8:], b[8:]
			continue
		}
		if len(b) != 0 && a[:8] > b[:8] {
			return "", false
		}
		out.WriteString(string(a[:8]))
		a = a[8:]
	}
	return _Monomial(out.String()), len(b) == 0
}

// monomialLCM is the least common multiple of a and b.
func monomialLCM(a, b _Monomial) _Monomial {
	var out strings.Builder
	for len(a) != 0 && len(b) != 0 {
		switch {
		case a[:8] == b[:8]:
			out.WriteString(string(a[:8]))
			a, b = a[8:], b[8:]
		case a[:8] < b[:8]:
			out.WriteString(string(a[:8]))
			a = a[8:]
		default:
			out.WriteString(string(b[:8]))
			b = b[8:]
		}
	}
	out.WriteString(string(a))
	out.WriteString(string(b))
	return _Monomial(out.String())
}

// _PolynomialTerm is one coordinate of a polynomial vector: a position
// (a base atom of a module, or an input row) and a monomial.
type _PolynomialTerm struct {
	pos  int
	mono _Monomial
}

// _PolynomialVector is a vector with integer polynomial coefficients:
// the nonzero integer at each (position, monomial).
type _PolynomialVector map[_PolynomialTerm]*big.Int

// polynomialUnit is the unit vector at pos.
func polynomialUnit(pos int) _PolynomialVector {
	return _PolynomialVector{_PolynomialTerm{pos: pos}: big.NewInt(1)}
}

// add is v + c·m·w, as a new vector.
func (v _PolynomialVector) add(w _PolynomialVector, m _Monomial, c *big.Int) _PolynomialVector {
	out := _PolynomialVector{}
	for t, x := range v {
		out[t] = new(big.Int).Set(x)
	}
	for t, x := range w {
		t.mono = monomialProduct(t.mono, m)
		z := new(big.Int).Mul(x, c)
		if old := out[t]; old != nil {
			z.Add(z, old)
		}
		if z.Sign() == 0 {
			delete(out, t)
		} else {
			out[t] = z
		}
	}
	return out
}

// scale is c·m·v.
func (v _PolynomialVector) scale(m _Monomial, c *big.Int) _PolynomialVector {
	return _PolynomialVector{}.add(v, m, c)
}

// termGreater orders terms by position first, then by the monomial's
// degree, then by its spelling: a position-over-term order whose
// monomial part is graded and compatible with multiplication, so the
// leading term of m·v is m times the leading term of v, and a row whose
// leading term is at a lower position has no term at a higher one.
func termGreater(a, b _PolynomialTerm) bool {
	if a.pos != b.pos {
		return a.pos > b.pos
	}
	if len(a.mono) != len(b.mono) {
		return len(a.mono) > len(b.mono)
	}
	return a.mono > b.mono
}

// terms lists v's terms in decreasing order.
func (v _PolynomialVector) terms() []_PolynomialTerm {
	ts := make([]_PolynomialTerm, 0, len(v))
	for t := range v {
		ts = append(ts, t)
	}
	sort.Slice(ts, func(i, j int) bool { return termGreater(ts[i], ts[j]) })
	return ts
}

// lead is v's greatest term and its coefficient, nil for the zero vector.
func (v _PolynomialVector) lead() (_PolynomialTerm, *big.Int) {
	var t _PolynomialTerm
	var c *big.Int
	for k, x := range v {
		if c == nil || termGreater(k, t) {
			t, c = k, x
		}
	}
	return t, c
}

// constants reports whether every coefficient of v is an integer: no
// term carries a monomial.
func (v _PolynomialVector) constants() bool {
	for t := range v {
		if t.mono != "" {
			return false
		}
	}
	return true
}

// _PolynomialRow is a basis row v with its expression trans over the
// input rows: v = Σ trans[i]·input[i].
type _PolynomialRow struct{ v, trans _PolynomialVector }

// _PolynomialBasis is a strong standard basis over ℤ of the submodule
// the input rows span. work counts the reductions of the operation in
// progress: the construction, or one expression against the basis.
type _PolynomialBasis struct {
	rows []_PolynomialRow
	work int
}

// polynomialWorkCap bounds the reductions of one basis construction and
// of one expression against a basis; polynomialTermCap bounds the terms
// of one vector and the atoms of one scalar module. Past either, the
// computation stops with a _PolynomialLimit.
const polynomialWorkCap = 20000
const polynomialTermCap = 4096

// _PolynomialLimit is the resource limit a polynomial computation
// raises: a panic that Close turns into the report of a failed chase.
type _PolynomialLimit struct{ what string }

func (e _PolynomialLimit) Error() string { return "chase polynomial resource limit: " + e.what }

// tick counts one reduction of v and checks both caps.
func (b *_PolynomialBasis) tick(v _PolynomialVector) {
	b.work++
	if b.work > polynomialWorkCap {
		panic(_PolynomialLimit{"more than 20000 reduction operations"})
	}
	if len(v) > polynomialTermCap {
		panic(_PolynomialLimit{"more than 4096 terms in one polynomial vector"})
	}
}

// reduce is the remainder of r by the basis, its expression kept: the
// leading term is reduced by the first row whose leading monomial
// divides it at the same position and whose leading coefficient
// Euclidean-divides into it (the coefficient drops to its remainder,
// never below zero); a leading term no row reduces moves to the
// remainder. A row is never divided by a nonunit.
func (b *_PolynomialBasis) reduce(r _PolynomialRow) _PolynomialRow {
	remainder := _PolynomialVector{}
	for len(r.v) != 0 {
		b.tick(r.v)
		t, c := r.v.lead()
		reduced := false
		for _, s := range b.rows {
			u, d := s.v.lead()
			if t.pos != u.pos {
				continue
			}
			m, ok := monomialQuotient(t.mono, u.mono)
			if !ok {
				continue
			}
			q := new(big.Int).Div(c, d)
			if q.Sign() == 0 {
				continue
			}
			q.Neg(q)
			r.v = r.v.add(s.v, m, q)
			r.trans = r.trans.add(s.trans, m, q)
			reduced = true
			break
		}
		if !reduced {
			remainder[t] = new(big.Int).Set(c)
			delete(r.v, t)
		}
	}
	r.v = remainder
	return r
}

// append adds a reduced row, its leading coefficient made positive; a
// zero row is dropped.
func (b *_PolynomialBasis) append(r _PolynomialRow) {
	if len(r.v) == 0 {
		return
	}
	_, c := r.v.lead()
	if c.Sign() < 0 {
		r.v = r.v.scale("", big.NewInt(-1))
		r.trans = r.trans.scale("", big.NewInt(-1))
	}
	b.rows = append(b.rows, r)
}

// buildPolynomialBasis completes the input rows to a strong standard
// basis over ℤ: every pair of rows with leading terms at one position
// contributes its G-pair (the Bézout combination whose leading
// coefficient is the gcd of theirs) and its S-pair (the combination
// cancelling their leading terms), each reduced and appended when
// nonzero. Pairs are examined in one deterministic order, new rows
// joining the end of the queue.
func buildPolynomialBasis(input []_PolynomialVector) *_PolynomialBasis {
	b := &_PolynomialBasis{}
	for i, v := range input {
		b.append(b.reduce(_PolynomialRow{v: v.scale("", big.NewInt(1)), trans: polynomialUnit(i)}))
	}
	for j := 0; j < len(b.rows); j++ {
		for i := 0; i < j; i++ {
			a, c := b.rows[i], b.rows[j]
			leadA, coeffA := a.v.lead()
			leadC, coeffC := c.v.lead()
			if leadA.pos != leadC.pos {
				continue
			}
			lcm := monomialLCM(leadA.mono, leadC.mono)
			multA, _ := monomialQuotient(lcm, leadA.mono)
			multC, _ := monomialQuotient(lcm, leadC.mono)
			gcd, s, t := new(big.Int), new(big.Int), new(big.Int)
			gcd.GCD(s, t, coeffA, coeffC)
			gPair := _PolynomialRow{v: a.v.scale(multA, s).add(c.v, multC, t), trans: a.trans.scale(multA, s).add(c.trans, multC, t)}
			b.append(b.reduce(gPair))
			quotA := new(big.Int).Quo(coeffC, gcd)
			quotC := new(big.Int).Neg(new(big.Int).Quo(coeffA, gcd))
			sPair := _PolynomialRow{v: a.v.scale(multA, quotA).add(c.v, multC, quotC), trans: a.trans.scale(multA, quotA).add(c.trans, multC, quotC)}
			b.append(b.reduce(sPair))
		}
	}
	return b
}

// express is v as a combination of the input rows, when v lies in the
// submodule they span: the coefficient at (row i, monomial m) is the
// multiple m·input[i] the combination takes. Each call has the
// reduction budget to itself.
func (b *_PolynomialBasis) express(v _PolynomialVector) (_PolynomialVector, bool) {
	b.work = 0
	r := b.reduce(_PolynomialRow{v: v.scale("", big.NewInt(1)), trans: _PolynomialVector{}})
	if len(r.v) != 0 {
		return nil, false
	}
	return r.trans.scale("", big.NewInt(-1)), true
}

// polynomialPreimage is a generating set of the vectors u over the
// first sourceSize positions with f(u) in the submodule the relations
// span: the graph rows eᵢ + f(eᵢ), with the target coordinates shifted
// above the source ones and the relations beside them, are completed
// to a basis, and the rows whose leading term is at a source position
// have no target coordinate (termGreater), so they are the preimage.
func polynomialPreimage(f, relations []_PolynomialVector, sourceSize int) []_PolynomialVector {
	var rows []_PolynomialVector
	embed := func(v _PolynomialVector) _PolynomialVector {
		out := _PolynomialVector{}
		for t, c := range v {
			t.pos += sourceSize
			out[t] = new(big.Int).Set(c)
		}
		return out
	}
	for i, v := range f {
		rows = append(rows, polynomialUnit(i).add(embed(v), "", big.NewInt(1)))
	}
	for _, v := range relations {
		rows = append(rows, embed(v))
	}
	b := buildPolynomialBasis(rows)
	var out []_PolynomialVector
	for _, r := range b.rows {
		t, _ := r.v.lead()
		if t.pos < sourceSize {
			out = append(out, r.v)
		}
	}
	return out
}
