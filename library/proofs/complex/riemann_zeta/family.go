// family.go — the riemann_zeta family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=riemann_zeta.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/riemann_zeta go test -run TestRecordFamilyCNF ./library/integrity/gates/

package riemann_zeta

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed riemann_zeta.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `riemann_zeta.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power. Its table names «xiTerm», the regularized
// term (s − 1)·(n + 1)^(−s) − ((n + 1)^(1−s) − (n + 2)^(1−s)); «xi», the
// regularized series 1 + Σ_n «xiTerm»(s, n) whose quotient by s − 1 is ζ:
// the series itself, which is 1 at s = 1, and not the product
// (s − 1)·ζ(s); and «regularDomain», the open set of Re s > 0 where «xi»
// does not vanish, on which −ξ′/ξ is holomorphic.
var family = registry.NewFamily("complex/riemann_zeta", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).
	WithAbbrev(Abbrev{
		{Name: "xiTerm", Text: "λs:complex. λn:num. " +
			"    (s - &1) * complex_cpow(&(&(n + 1)), -s) - " +
			"    (complex_cpow(&(&(n + 1)), &1 - s) - complex_cpow(&(&(n + 2)), &1 - s))"},
		{Name: "xi", Text: "λs:complex. &1 + (εv:complex. complex_sums(«xiTerm»(s), v))"},
		{Name: "regularDomain", Text: "{s:complex | &0 < re(s) ∧ «xi»(s) ≠ &0}"},
	})
