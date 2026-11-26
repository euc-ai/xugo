package de_rham_comparison

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_singular"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/thom_form"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_comparison.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/de_rham_comparison", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(de_rham_cover.ChapterAbbrev)
