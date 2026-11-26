package real_polynomial_geometry

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_polynomial_geometry.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `real_polynomial_geometry.<Member>`. It binds the real ring's components
// and reads an unanchored numeral as a real, as euclidean_topology does, and
// reads that chapter's table, whose «append»(a, t) appends t to an n-vector
// a; its own «box»(k, b) is the tuples of length k whose coordinates lie in
// ⟦−b, b⟧.
var family = registry.NewFamily("real/real_polynomial_geometry", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(euclidean_topology.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "box", Text: "λk:num. λb:real. " +
			"    {x:(num → real) | ring_tuple(real_ring, k, x) ∧ (∀j:num. j < k ⇒ -b ≤ x(j) ∧ x(j) ≤ b)}"},
	})
