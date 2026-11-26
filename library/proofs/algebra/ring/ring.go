// Package ring is the aggregator for the ring-like structures: the
// commutative ring (two operations joined by distributivity), the
// integral domain (the ring with no zero divisors), and
// commutative algebra over a ring on a set — its ideals, its
// homomorphisms, its quotient rings, its rings of fractions, the
// local rings, and the polynomials over it — plus the fractional ideals
// of a subring of a field, a ring carried along
// an injection, the free commutative algebra on a set of variables, its
// partial derivatives and Jacobians, the module of Kähler
// differentials, and the square-zero extensions of an algebra by a
// module. Each is one family; every definition above the ring
// conjoins or reads the ring's predicate, so its package imports the
// ring's and the ring's constant is minted first.
package ring

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/euclidean_domain"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/kaehler"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/multilinear_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/zariski_cotangent"
)
