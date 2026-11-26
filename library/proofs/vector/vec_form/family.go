package vec_form

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed vec_form.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("vector/vec_form", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(euclidean_topology.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "zero", Text: "λx:(num → real). λP:(num → num → real). &0"},
		{Name: "unit", Text: "λx:(num → real). λP:(num → num → real). COND(x ∈ U, &1, &0)"},
		{Name: "empty frame", Text: "λi:num. λj:num. &0"},
		{Name: "zero matrix", Text: "λi:num. λj:num. λx:(num → real). λP:(num → num → real). &0"},
	})

// ChapterAbbrev supplies the Euclidean form normalization notation to
// chapters that construct compatible families of these forms.
var ChapterAbbrev = family.ChapterAbbrev()
