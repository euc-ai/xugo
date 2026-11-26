package manifold_critical_point

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed manifold_critical_point.cnf.pb
var familyCNF []byte

// family reads the atlas chapter's table: a critical point is read in
// the coordinate map of a pair of charts.
var family = registry.NewFamily("manifold/manifold_critical_point", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(smooth_manifold.ChapterAbbrev)
