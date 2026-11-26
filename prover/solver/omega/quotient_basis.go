package omega

import "github.com/euc-ai/xugo/ext/prop"

// The quotient basis: `u / v` with a SYMBOLIC divisor read as the monomial
// u·inv(v), so a quotient and a written-out product with the inverse meet as
// one unknown in the linear layer, and quotients over one divisor combine —
// `(a + b) / v = a / v + b / v` is a ring identity once both sides are read.
//
// It is the pow basis's move (pow_basis.go): the TERM is untouched, only its
// reading changes, in the three readers that must agree — the model
// (domain.go linOf), the certificate (ring.go normalizeProof and
// normalizeFull) and the signed normalizer (subneg.go), where a quotient
// whose numerator carries a subtraction is FOILed as the product is. The
// field handlers (real_ops.go: clearing `x ⋈ y/z` under z's sign, a / a)
// go on meeting the `/` the author wrote.
//
// A LITERAL divisor is out: `y / &k` is a linear unknown tied to y by its
// defining equation (real_quotient.go), which is the stronger reading — it
// cancels `&k · (y / &k)`, where inv(&k) would be one more atom.
//
// Nothing about the divisor's sign or its being nonzero is read or needed:
// x / y = x · inv y is real_div's definition, unconditional. Cancelling
// `v · inv(v)` stays a premise's business.
//
// The inverse basis is the same move one step down: `inv(a·b)` read as the
// product inv(a)·inv(b) (Domain.inverseProduct, the readers' fieldProduct),
// so a quotient by a product meets the product of two quotients —
// `x / a · (y / b) = x · y / (a · b)` is a ring identity once both sides
// are read — and each factor's inverse is an atom the unit facts can cancel
// against that factor. inv(x·y) = inv x · inv y holds of every pair, zero
// included (InvMul), so nothing is read here either.
func init() {
	realRing.quotientUnfold = realQuotientUnfold
	realRing.inverseUnfold = realInverseUnfold
}

// realQuotientUnfold: ⊢ u / v = u · inv v.
func realQuotientUnfold(u, v Term) *prop.PropWrapper {
	return realEqLeaf(realDivDefThm(), []Term{u, v}, realDivT(u, v), realStarT(u, realInvT(v)))
}

// realInverseUnfold: ⊢ inv(a · b) = inv a · inv b.
func realInverseUnfold(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realInvMulThm(), []Term{a, b}, realInvT(realStarT(a, b)), realStarT(realInvT(a), realInvT(b)))
}
