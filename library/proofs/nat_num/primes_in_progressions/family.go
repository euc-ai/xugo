// family.go — the primes_in_progressions family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=primes_in_progressions.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/primes_in_progressions go test -run TestRecordFamilyCNF ./library/integrity/gates/

package primes_in_progressions

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_l_function"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed primes_in_progressions.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `primes_in_progressions.<Member>`. The domain is ℝ: a bare `&n` is a
// real, and a complex number is written with complex_of_real.
var family = registry.NewFamily("nat_num/primes_in_progressions", familyCNF).WithCoerceDomain(
	RealDomain)
