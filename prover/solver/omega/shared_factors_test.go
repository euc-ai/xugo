package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// TestSharedFactors: the two sides of a comparison are read as multisets
// of factors — up to the order and the grouping of the products, a factor
// as often as both sides hold it, a literal never shared — and a side
// that is one of the other's factors leaves the empty product, 1.
func TestSharedFactors(t *testing.T) {
	x, y, z, w := numVar("x"), numVar("y"), numVar("z"), numVar("w")
	two := Numeral(2)
	spell := func(factors []Term) string { return ext.PrintTerm(natDomain.productOf(factors)) }
	for _, row := range []struct {
		name                string
		l, r                Term
		shared, left, right Term
	}{
		{"a left factor", star(x, y), star(x, z), x, y, z},
		{"the factor on opposite sides", star(x, y), star(z, x), x, y, z},
		{"another grouping", star(star(x, y), w), star(w, star(x, z)), star(x, w), y, z},
		{"a repeated factor, shared once", star(x, x), star(x, y), x, x, y},
		{"a repeated factor, shared twice", star(star(x, x), y), star(x, star(z, x)), star(x, x), y, z},
		{"the other side's own factor", star(x, y), x, x, y, Numeral(1)},
		{"a literal is a coefficient", star(two, star(x, y)), star(two, star(x, z)), x, star(two, y), star(two, z)},
	} {
		shared, left, right := natDomain.sharedFactors(row.l, row.r)
		require.Equal(t, ext.PrintTerm(row.shared), spell(shared), "%s: the shared factors", row.name)
		require.Equal(t, ext.PrintTerm(row.left), spell(left), "%s: what is left of the left side", row.name)
		require.Equal(t, ext.PrintTerm(row.right), spell(right), "%s: what is left of the right side", row.name)
	}
	shared, _, _ := natDomain.sharedFactors(star(x, y), star(z, w))
	require.Empty(t, shared, "two products with no factor in common share none")
	shared, _, _ = natDomain.sharedFactors(star(two, y), star(two, z))
	require.Empty(t, shared, "a literal alone is not a shared factor")
}
