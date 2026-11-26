// family.go — the complex_polynomial family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.

package complex_polynomial

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_polynomial.cnf.pb
var familyCNF []byte

// family is the family handle. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real, since a modulus is one.
var family = registry.NewFamily("complex/complex_polynomial", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_ring.CommRing, complex_field.CommRing).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
