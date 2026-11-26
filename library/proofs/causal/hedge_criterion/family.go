// family.go — the hedge_criterion family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=hedge_criterion.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/hedge_criterion go test -run TestRecordFamilyCNF ./library/integrity/gates/

package hedge_criterion

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_semantics"
	_ "github.com/euc-ai/xugo/library/proofs/causal/id_derivation"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed hedge_criterion.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the positive class over
// the graph (V, E) with observed nodes O and carriers D; the sign of a
// bit, −1 where it is set; over a set of edges Ed, adjacency in either
// order, the edges at a vertex, the ends of an edge in S and the spin of a
// vertex, over one set of edges σ or one track k of labelled edges; and,
// over a forest F stepping along τ with roots R, the vertices stepping to
// v, the term of v on a set T of vertices taking W, the tracks (the subsets
// of U), the share of a track in the mean at v, and the forest's sign mean.
var family = registry.NewFamily("causal/hedge_criterion", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "positiveClass", Text: "λM:scm_model(A, B, I). positive_scm(V, E, O, D, M)"},
	{Name: "sgn", Text: "λb:bool. COND(b, -&1, &1)"},
	{Name: "adjacent", Text: "λa:I. λb:I. (a, b) ∈ Ed ∨ (b, a) ∈ Ed"},
	{Name: "edgesAt", Text: "λv:I. {e:prod(I, I) | e ∈ Ed ∧ (fst(e) = v ∨ snd(e) = v)}"},
	{Name: "ends", Text: "λe:prod(I, I). {v:I | v ∈ S ∧ (fst(e) = v ∨ snd(e) = v)}"},
	{Name: "spin", Text: "λσ:set(prod(I, I)). λv:I. Π_{e∈«edgesAt»(v)} «sgn»(e ∈ σ)"},
	{Name: "trackSpin", Text: "λσ:set(prod(prod(I, I), C)). λk:C. λv:I. " +
		"    Π_{e∈«edgesAt»(v)} «sgn»((e, k) ∈ σ)"},
	{Name: "stepsTo", Text: "λT:set(I). λv:I. {w:I | w ∈ F ∧ w ∉ R ∧ w ∉ T ∧ τ(w) = v}"},
	{Name: "term", Text: "λv:I. λT:set(I). " +
		"    «sgn»(v ∈ z) * " +
		"    α(v) * " +
		"    (Π_{w∈«stepsTo»(T, v)} «sgn»(w ∈ z)) * " +
		"    COND(v ∈ T, W(v, z), COND(v ∈ R, κ(v, z), &1))"},
	{Name: "tracks", Text: "{A:set(I) | A ⊆ U}"},
	{Name: "share", Text: "λσ:set(prod(prod(I, I), set(I))). λv:I. λT:set(I). " +
		"    «trackSpin»(σ, T, v) * " +
		"    (Π_{w∈«stepsTo»(T, v)} «sgn»(w ∈ z)) * " +
		"    COND(v ∈ T, W(v, z), COND(v ∈ R, κ(v, z), &1))"},
	{Name: "mean", Text: "c_forest_sign_mean(W, κ, α, F, R, U, Ed, τ)"},
})
