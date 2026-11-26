package chase

// lattice.go — integer linear algebra for the chase: a lattice in ℤⁿ
// held as a row echelon basis reached by unimodular row operations
// (the Hermite form), with every basis row expressed over the rows it
// was built from. Three questions are asked of it, each a few small
// matrices wide: whether a vector lies in the lattice and with which
// integer coefficients (the ℤ-linear step's certificate), the integer
// kernel of a matrix (the elements a homomorphism sends to zero), and
// the preimage of a lattice under a matrix (the kernel modulo the
// target's relations). Gaussian elimination over ℚ is not used: a
// module may have torsion, so 2x = 0 does not give x = 0, and only
// integer combinations of the relations are consequences.
//
// Every operation is a deterministic function of its input: rows are
// processed in order and pivots chosen by position.

import (
	"math/big"
)

// _Echelon is a lattice basis in row echelon form over the integers:
// rows[i] has its first nonzero entry (positive) at pivot[i], the
// pivots strictly increase, and trans[i] expresses rows[i] as an
// integer combination of the input rows the echelon was built from.
type _Echelon struct {
	rows  [][]*big.Int
	pivot []int
	trans [][]*big.Int
	cols  int
	n     int // the number of input rows
}

func newInt(x int64) *big.Int { return big.NewInt(x) }

func zeroRow(n int) []*big.Int {
	r := make([]*big.Int, n)
	for i := range r {
		r[i] = new(big.Int)
	}
	return r
}

func cloneRow(r []*big.Int) []*big.Int {
	out := make([]*big.Int, len(r))
	for i, x := range r {
		out[i] = new(big.Int).Set(x)
	}
	return out
}

func isZeroRow(r []*big.Int) bool {
	for _, x := range r {
		if x.Sign() != 0 {
			return false
		}
	}
	return true
}

// buildEchelon reduces the input rows (each of length cols) to echelon
// form by unimodular row operations, tracking each echelon row's
// expression over the input rows.
func buildEchelon(input [][]*big.Int, cols int) *_Echelon {
	n := len(input)
	rows := make([][]*big.Int, n)
	trans := make([][]*big.Int, n)
	for i, r := range input {
		rows[i] = cloneRow(r)
		trans[i] = zeroRow(n)
		trans[i][i].SetInt64(1)
	}
	e := &_Echelon{cols: cols, n: n}
	top := 0 // the next echelon row to fill
	for col := 0; col < cols && top < n; col++ {
		// Fold every row at or below top with a nonzero entry in col into
		// row top, by the extended Euclidean 2×2 transform, which is
		// unimodular and leaves the lattice unchanged.
		for i := top + 1; i < n; i++ {
			if rows[i][col].Sign() == 0 {
				continue
			}
			if rows[top][col].Sign() == 0 {
				rows[top], rows[i] = rows[i], rows[top]
				trans[top], trans[i] = trans[i], trans[top]
				continue
			}
			combine(rows, trans, top, i, col)
		}
		if rows[top][col].Sign() == 0 {
			continue
		}
		if rows[top][col].Sign() < 0 {
			negateRow(rows[top])
			negateRow(trans[top])
		}
		// Reduce the rows above top modulo the pivot, for a canonical
		// basis (the Hermite form's upper reduction).
		for i := 0; i < top; i++ {
			if rows[i][col].Sign() == 0 {
				continue
			}
			q := new(big.Int).Div(rows[i][col], rows[top][col]) // floor division
			if q.Sign() != 0 {
				subtractMultiple(rows[i], rows[top], q)
				subtractMultiple(trans[i], trans[top], q)
			}
		}
		e.rows = append(e.rows, rows[top])
		e.pivot = append(e.pivot, col)
		e.trans = append(e.trans, trans[top])
		top++
	}
	return e
}

// combine replaces rows a and b by an integer unimodular combination
// such that rows[a][col] becomes the gcd of the two entries and
// rows[b][col] zero (the same transform applied to trans).
func combine(rows, trans [][]*big.Int, a, b, col int) {
	x, y := rows[a][col], rows[b][col]
	g, s, t := new(big.Int), new(big.Int), new(big.Int)
	g.GCD(s, t, new(big.Int).Abs(x), new(big.Int).Abs(y))
	if x.Sign() < 0 {
		s.Neg(s)
	}
	if y.Sign() < 0 {
		t.Neg(t)
	}
	// [ s  t ] [a]   [g]          [ -y/g  x/g ] is the second row of the
	// [-y/g x/g] [b] = [0]  —  the matrix has determinant s·x/g + t·y/g = 1.
	u := new(big.Int).Div(x, g)
	v := new(big.Int).Div(y, g)
	v.Neg(v)
	apply := func(m [][]*big.Int) {
		ra, rb := m[a], m[b]
		na := make([]*big.Int, len(ra))
		nb := make([]*big.Int, len(ra))
		for i := range ra {
			na[i] = new(big.Int).Add(new(big.Int).Mul(s, ra[i]), new(big.Int).Mul(t, rb[i]))
			nb[i] = new(big.Int).Add(new(big.Int).Mul(v, ra[i]), new(big.Int).Mul(u, rb[i]))
		}
		m[a], m[b] = na, nb
	}
	apply(rows)
	apply(trans)
}

func negateRow(r []*big.Int) {
	for _, x := range r {
		x.Neg(x)
	}
}

// subtractMultiple sets r := r − q·s.
func subtractMultiple(r, s []*big.Int, q *big.Int) {
	for i := range r {
		r[i].Sub(r[i], new(big.Int).Mul(q, s[i]))
	}
}

// express reduces v against the echelon: when v lies in the lattice,
// ok is true and coeffs (over the INPUT rows) satisfy v = Σ coeffs[i]·input[i];
// otherwise residue is the reduced vector (nonzero) and ok is false.
func (e *_Echelon) express(v []*big.Int) (coeffs []*big.Int, residue []*big.Int, ok bool) {
	w := cloneRow(v)
	coeffs = zeroRow(e.n)
	for i, p := range e.pivot {
		if w[p].Sign() == 0 {
			continue
		}
		q, rem := new(big.Int).QuoRem(w[p], e.rows[i][p], new(big.Int))
		if rem.Sign() != 0 {
			return nil, w, false
		}
		subtractMultiple(w, e.rows[i], q)
		for k := range coeffs {
			coeffs[k].Add(coeffs[k], new(big.Int).Mul(q, e.trans[i][k]))
		}
	}
	if !isZeroRow(w) {
		return nil, w, false
	}
	return coeffs, nil, true
}

// integerKernel is a basis of {x ∈ ℤⁿ : M·x = 0} for the m×n matrix M
// (rows of length n): the row echelon of [Mᵀ | I] by unimodular
// operations, whose rows with a zero left part carry a kernel basis in
// their right parts.
func integerKernel(m [][]*big.Int, n int) [][]*big.Int {
	rowsT := make([][]*big.Int, n)
	k := len(m)
	for j := 0; j < n; j++ {
		r := zeroRow(k + n)
		for i := 0; i < k; i++ {
			r[i].Set(m[i][j])
		}
		r[k+j].SetInt64(1)
		rowsT[j] = r
	}
	e := buildEchelon(rowsT, k+n)
	var kernel [][]*big.Int
	for i, r := range e.rows {
		if e.pivot[i] < k {
			continue // a row with a nonzero left part
		}
		kernel = append(kernel, cloneRow(r[k:]))
	}
	// The rows of e below the pivots that are entirely zero do not
	// appear in e.rows; the left-zero rows are exactly those with pivot ≥ k.
	return kernel
}

// preimageLattice is a basis of {x ∈ ℤᵃ : F·x ∈ span(relations)} for
// F (a b×a matrix, column j the image of the j-th generator, written
// as rows[j] of length b) and the relation rows at the target (each of
// length b): the x-parts of the integer kernel of [F | −R].
func preimageLattice(f [][]*big.Int, a, b int, relations [][]*big.Int) [][]*big.Int {
	r := len(relations)
	// m is b × (a + r): column j < a is F's j-th column, column a + i is −relations[i].
	m := make([][]*big.Int, b)
	for row := 0; row < b; row++ {
		m[row] = zeroRow(a + r)
		for j := 0; j < a; j++ {
			m[row][j].Set(f[j][row])
		}
		for i := 0; i < r; i++ {
			m[row][a+i].Neg(relations[i][row])
		}
	}
	kernel := integerKernel(m, a+r)
	var out [][]*big.Int
	for _, kv := range kernel {
		x := cloneRow(kv[:a])
		if !isZeroRow(x) {
			out = append(out, x)
		}
	}
	if len(out) == 0 {
		return nil
	}
	// A canonical, reduced basis of the projected lattice.
	e := buildEchelon(out, a)
	basis := make([][]*big.Int, len(e.rows))
	for i, row := range e.rows {
		basis[i] = cloneRow(row)
	}
	return basis
}
