// family.go — the vec_integral family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=vec_integral.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/vec_integral go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package vec_integral

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed vec_integral.cnf.pb
var familyCNF []byte

// family is the family handle, bound to the real ring as the euclidean
// chapters are; an unanchored numeral `&k` is a real one. It reads
// vec_smooth's table, which carries euclidean_topology's `«append»(x, t)`,
// and adds four spellings of its own:
//
//   - `«rapid»(k, g)`: g is continuous on ℝᵏ and decreases rapidly, every
//     power of 1 + ⟪x, x⟫ times |g| being bounded — the functions the
//     calculus of the integral is stated for;
//   - `«Cc»(k, g)`: g is continuous on ℝᵏ with compact support, the
//     functions the change of variables on open sets is stated for;
//   - `«join»(x, y)`: the vector of ℝⁿ⁺ᵐ whose first n coordinates are
//     those of x and whose next ones are those of y;
//   - `«polar»(r, θ)`: the point of the plane at distance r and angle θ.
var family = registry.NewFamily("vector/vec_integral", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(vec_smooth.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "rapid", Text: "λk:num. λg:((num → real) → real). " +
			"    continuous_map(euclidean_topology(k), real_topology, g) ∧ " +
			"    (∀p:num. ∃C:real. ∀x:(num → real). vec⟨k⟩(x) ⇒ real_pow(&1 + ⟪x, x⟫_k, p) * |g(x)| ≤ C)"},
		{Name: "Cc", Text: "λk:num. λg:((num → real) → real). " +
			"    continuous_map(euclidean_topology(k), real_topology, g) ∧ " +
			"    vec_compactly_supported_in⟨k⟩({u:num → real | vec⟨k⟩(u)}, g)"},
		{Name: "join", Text: "λx:(num → real). λy:(num → real). λi:num. COND(i < n, x(i), y(i - n))"},
		{Name: "polar", Text: "λr:real. λθ:real. λi:num. " +
			"    COND(i = 0, r * cos(θ), COND(i = 1, r * sin(θ), &0))"},
	})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
