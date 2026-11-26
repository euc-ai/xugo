// family.go — the kernel_do_calculus family manifest: the registry
// handle every member registers into and the family's shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=kernel_do_calculus.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/kernel_do_calculus go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kernel_do_calculus

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	_ "github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	_ "github.com/euc-ai/xugo/library/proofs/probability/conditional_distribution"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kernel_do_calculus.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the product σ-algebras
// on the configurations of the node groups X, Y, Z and W of a model M,
// and the probability space of the randomized regime of
// do(Z = ·) with the intervened values drawn from ρ: its samples, events
// and probability, and the σ-algebra of its root, which carries the
// drawn values and the coin.
var family = registry.NewFamily("causal/kernel_do_calculus", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "Xsigma", Text: "indexed_product_sigma(X, M.default, M.states, M.state_sigma)"},
	{Name: "Ysigma", Text: "indexed_product_sigma(Y, M.default, M.states, M.state_sigma)"},
	{Name: "Zsigma", Text: "indexed_product_sigma(Z, M.default, M.states, M.state_sigma)"},
	{Name: "Wsigma", Text: "indexed_product_sigma(W, M.default, M.states, M.state_sigma)"},
	{Name: "rsample", Text: "set_cross( " +
		"    set_cross(M.sample, indexed_functions(Z, M.default, M.states)), 𝕌⟨A:bool⟩)"},
	{Name: "revents", Text: "bool_mixture_sigma( " +
		"    set_cross(M.sample, indexed_functions(Z, M.default, M.states)), " +
		"    product_sigma(M.sample, " +
		"        M.events, " +
		"        indexed_functions(Z, M.default, M.states), " +
		"        indexed_product_sigma(Z, M.default, M.states, M.state_sigma)))"},
	{Name: "rprob", Text: "bool_mixture_measure(product_measure(M.sample, M.events, M.prob, ρ))"},
	{Name: "root", Text: "pullback_sigma( " +
		"    set_cross(set_cross(M.sample, indexed_functions(Z, M.default, M.states)), 𝕌⟨A:bool⟩), " +
		"    λp:prod(prod(A, I → B), bool). (snd(fst(p)), snd(p)), " +
		"    product_sigma(indexed_functions(Z, M.default, M.states), " +
		"        indexed_product_sigma(Z, M.default, M.states, M.state_sigma), " +
		"        𝕌⟨A:bool⟩, " +
		"        𝕌⟨A:set(bool)⟩))"},
})
