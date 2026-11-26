// integral_domain.go — ℝ as an integral domain: the instance at which the
// chapter, and the chapters above it, read the laws of polynomials and
// formal series over a domain.

package real_formal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// RealIntegralDomain — ℝ is an integral domain on its carrier: the
// commutative ring on its carrier (real_ring.CommRingOn), whose one is not
// its zero and in which a product of reals vanishes only when a factor does.
var RealIntegralDomain = realIntegralDomainThm{family.Add(registry.ProofEntry{
	Name: "RealIntegralDomain",
	Key:  "prop_83e8ef701a21f008",
	Build: family.Instance(integral_domain.IntegralDomainOn, "integral_domain_on(real_ring)",
		Case(
			"the real ring is commutative on its carrier",
			Cite(real_ring.CommRingOn)),
		Case(
			"one differs from zero, the numerals 1 and 0 being distinct",
			By(real_construction.OfNumEq, nat_arith.OneIsSucZero, peano.SucNotZero)),
		Case(
			"a real product vanishes only when a factor vanishes",
			By(real_ring.MulEqZero))),
})}
