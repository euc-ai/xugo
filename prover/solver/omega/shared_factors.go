package omega

import "slices"

// The factors two products share.
//
// The linear core reads a product up to the order and the grouping of its
// factors, so `x * y * w` and `w * (x * z)` hold the factors x and w in
// common however each is spelled. The handlers that scale a comparison by a
// common factor, or cancel one, read the two sides as multisets of factors
// and hand the linear prover the comparison respelled `P * a ⋈ P * b`, P
// the product of the shared factors and a, b the products of the rest.

// factors lists the factors of t, the leaves of its tree of products.
func (d *Domain) factors(t Term) []Term {
	if a, b, ok := d.matchStar(t); ok {
		return append(d.factors(a), d.factors(b)...)
	}
	return []Term{t}
}

// productOf is the product of factors in order, and the literal 1 for
// none.
func (d *Domain) productOf(factors []Term) Term {
	if len(factors) == 0 {
		return d.numeral(integerOne)
	}
	t := factors[0]
	for _, f := range factors[1:] {
		t = d.star(t, f)
	}
	return t
}

// sharedFactors splits the factors of l and of r into the ones the two
// sides share, each as often as both hold it, and what is left of each. A
// literal factor is a coefficient, to a linear core and to a structure
// ring's combination alike, and is never taken for a shared one.
func (d *Domain) sharedFactors(l, r Term) (shared, restL, restR []Term) {
	restR = d.factors(r)
	for _, f := range d.factors(l) {
		i := -1
		if _, literal, _ := d.asLiteral(f); !literal {
			i = slices.IndexFunc(restR, f.AlphaEquals)
		}
		if i < 0 {
			restL = append(restL, f)
			continue
		}
		shared = append(shared, f)
		restR = slices.Delete(restR, i, i+1)
	}
	return shared, restL, restR
}
