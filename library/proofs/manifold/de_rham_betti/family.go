package de_rham_betti

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_betti.cnf.pb
var familyCNF []byte

// family reads the cover chapter's table: the Euler characteristic of
// a two-open cover is stated over its exact sequence.
var family = registry.NewFamily("manifold/de_rham_betti", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(de_rham_cover.ChapterAbbrev)
