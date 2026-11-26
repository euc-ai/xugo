package chase

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestPolynomialModule_IntegralCombinations(t *testing.T) {
	a, b := monomialVariable(0), monomialVariable(1)
	x := polynomialUnit(0).scale(a, big.NewInt(1))
	y := polynomialUnit(0).scale(b, big.NewInt(1))
	rows := []_PolynomialVector{x.scale("", big.NewInt(2)), x.scale("", big.NewInt(3)), y.add(polynomialUnit(1), "", big.NewInt(1))}
	basis := buildPolynomialBasis(rows)
	target := x.scale(b, big.NewInt(1)).add(rows[2], a, big.NewInt(7))
	coeffs, ok := basis.express(target)
	require.True(t, ok)
	actual := _PolynomialVector{}
	for m, c := range coeffs {
		actual = actual.add(rows[m.pos], m.mono, c)
	}
	require.Equal(t, target, actual)
	_, ok = buildPolynomialBasis(rows[:1]).express(x)
	require.False(t, ok, "2a does not generate a over the integers")
	_, ok = buildPolynomialBasis([]_PolynomialVector{x}).express(polynomialUnit(0))
	require.False(t, ok, "a is not invertible")
}

func TestPolynomialModule_KernelModuloRelations(t *testing.T) {
	a, b := monomialVariable(0), monomialVariable(1)
	f := []_PolynomialVector{polynomialUnit(0).scale(a, big.NewInt(1)), polynomialUnit(0).scale(b, big.NewInt(1))}
	kernel := polynomialPreimage(f, nil, 2)
	wanted := polynomialUnit(0).scale(b, big.NewInt(1)).add(polynomialUnit(1), a, big.NewInt(-1))
	_, ok := buildPolynomialBasis(kernel).express(wanted)
	require.True(t, ok)
	for _, k := range kernel {
		image := _PolynomialVector{}
		for m, c := range k {
			image = image.add(f[m.pos], m.mono, c)
		}
		require.Empty(t, image)
	}
	rels := []_PolynomialVector{polynomialUnit(0).scale("", big.NewInt(2))}
	kernel = polynomialPreimage([]_PolynomialVector{polynomialUnit(0)}, rels, 1)
	_, ok = buildPolynomialBasis(kernel).express(polynomialUnit(0))
	require.False(t, ok)
	_, ok = buildPolynomialBasis(kernel).express(polynomialUnit(0).scale("", big.NewInt(2)))
	require.True(t, ok)
}

// A basis is cached at its node and answers many expressions; the
// reduction budget is each expression's own, not the basis's lifetime.
func TestPolynomialModule_ExpressionBudgetIsPerCall(t *testing.T) {
	a := monomialVariable(0)
	x := polynomialUnit(0).scale(a, big.NewInt(1))
	basis := buildPolynomialBasis([]_PolynomialVector{x.scale("", big.NewInt(2)), x.scale("", big.NewInt(3))})
	require.NotPanics(t, func() {
		for i := 0; i < 2*polynomialWorkCap; i++ {
			_, ok := basis.express(x)
			require.True(t, ok)
		}
	})
}
