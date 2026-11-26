package chase

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

func rowsOf(xs ...[]int64) [][]*big.Int {
	out := make([][]*big.Int, len(xs))
	for i, r := range xs {
		out[i] = make([]*big.Int, len(r))
		for j, x := range r {
			out[i][j] = big.NewInt(x)
		}
	}
	return out
}

func ints(xs ...int64) []*big.Int { return rowsOf(xs)[0] }

// combination is Σ coeffs[i]·rows[i].
func combination(coeffs []*big.Int, rows [][]*big.Int, cols int) []*big.Int {
	out := zeroRow(cols)
	for i, c := range coeffs {
		for j := range out {
			out[j].Add(out[j], new(big.Int).Mul(c, rows[i][j]))
		}
	}
	return out
}

func TestLattice_TorsionIsKept(t *testing.T) {
	// 2x = 0 does not give x = 0.
	e := buildEchelon(rowsOf([]int64{2}), 1)
	_, _, ok := e.express(ints(1))
	require.False(t, ok, "x must not follow from 2x = 0")
	coeffs, _, ok := e.express(ints(4))
	require.True(t, ok)
	require.Equal(t, int64(2), coeffs[0].Int64())
}

func TestLattice_IntegerCombinationBeyondRationalElimination(t *testing.T) {
	// 2x = 0 and 3x = 0 give x = 0 (x = 3x − 2x), which an elimination
	// over ℚ followed by an integrality check misses (½·(2x) = x).
	rows := rowsOf([]int64{2, 0}, []int64{3, 0})
	e := buildEchelon(rows, 2)
	coeffs, _, ok := e.express(ints(1, 0))
	require.True(t, ok)
	require.Equal(t, ints(1, 0), combination(coeffs, rows, 2))
}

func TestLattice_ExpressReproducesTheVector(t *testing.T) {
	rows := rowsOf([]int64{2, 3, 1}, []int64{4, 0, -2}, []int64{0, 6, 0})
	e := buildEchelon(rows, 3)
	for _, c := range [][]int64{{1, 0, 0}, {0, 1, 0}, {0, 0, 1}, {1, -2, 3}, {-5, 4, 7}} {
		v := combination(ints(c...), rows, 3)
		coeffs, _, ok := e.express(v)
		require.True(t, ok, "%v", c)
		require.Equal(t, v, combination(coeffs, rows, 3))
	}
	_, residue, ok := e.express(ints(1, 0, 0))
	require.False(t, ok)
	require.False(t, isZeroRow(residue))
}

func TestLattice_IntegerKernel(t *testing.T) {
	kernel := integerKernel(rowsOf([]int64{1, 1}), 2)
	require.Len(t, kernel, 1)
	require.Equal(t, int64(0), new(big.Int).Add(kernel[0][0], kernel[0][1]).Int64())
	require.NotEqual(t, 0, kernel[0][0].Sign())

	kernel = integerKernel(rowsOf([]int64{2, 4}), 2)
	require.Len(t, kernel, 1)
	// 2a + 4b = 0 over ℤ: (2, −1) generates.
	require.Equal(t, int64(0), new(big.Int).Add(new(big.Int).Mul(big.NewInt(2), kernel[0][0]), new(big.Int).Mul(big.NewInt(4), kernel[0][1])).Int64())
	require.Equal(t, int64(1), new(big.Int).Abs(kernel[0][1]).Int64())

	// A full-rank square matrix has a trivial kernel.
	require.Nil(t, integerKernel(rowsOf([]int64{1, 2}, []int64{3, 5}), 2))
}

func TestLattice_PreimageOfRelations(t *testing.T) {
	// f(e₁) = y, f(e₂) = 2y at a target where 2y = 0: the preimage of the
	// relations is {x₁ even} — e₂ alone is sent to zero, e₁ is not.
	f := rowsOf([]int64{1}, []int64{2}) // rows[j] = the image of generator j
	basis := preimageLattice(f, 2, 1, rowsOf([]int64{2}))
	e := buildEchelon(basis, 2)
	_, _, ok := e.express(ints(0, 1))
	require.True(t, ok, "e₂ is sent to 2y = 0")
	_, _, ok = e.express(ints(2, 0))
	require.True(t, ok, "2e₁ is sent to 2y = 0")
	_, _, ok = e.express(ints(1, 0))
	require.False(t, ok, "e₁ is sent to y ≠ 0")

	// Without relations at the target the preimage is the kernel.
	basis = preimageLattice(rowsOf([]int64{1, 0}, []int64{1, 0}), 2, 2, nil)
	e = buildEchelon(basis, 2)
	_, _, ok = e.express(ints(1, -1))
	require.True(t, ok)
	_, _, ok = e.express(ints(1, 0))
	require.False(t, ok)
}
