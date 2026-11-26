// example.go — two concrete graphs with a latent common cause of X and
// Y. The bow graph U → X, U → Y, X → Y with U latent carries two models
// that agree on every observation and differ under do(X = ⊥): the
// background is two independent fair coins on bool × bool; U outputs
// the first, Y's noise is the second, and X copies U; Y is its noise when
// X equals U, and the constant c otherwise, and in the natural run X
// always equals U, so c is never seen. The front-door graph U → X,
// U → Y, X → Z → Y with U latent has its vertices here; the effect is
// identifiable on it.

package identifiability

import (
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// BowNodeData — the three vertices of the bow graph: the latent bow_u and
// the observed bow_x and bow_y.
var BowNodeData = family.DefineData(registry.DataEntry{
	Name: "BowNode",
	Type: "bow_node",
	Constructors: []proof.DataConstructorSpec{
		{Name: "bow_u"}, {Name: "bow_x"}, {Name: "bow_y"},
	},
	Principles: registry.DataPrinciples{
		Induction: "BowNodeInduction",
		Recursion: "BowNodeRecursion",
		Distinct:  "BowNodeDistinct",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
		peano.SucInjective,
	},
})

// BowNodeInduction — a property of each of the three vertices holds of
// every vertex.
var BowNodeInduction = bowNodeInductionThm{BowNodeData.Induct}

// BowNodeRecursion — a function on the vertices is fixed by its three
// values.
var BowNodeRecursion = bowNodeRecursionThm{BowNodeData.Recursion}

// BowNodeDistinct — the three vertices are pairwise distinct.
var BowNodeDistinct = bowNodeDistinctThm{BowNodeData.Distinct}

// BowModelDef — `bow_model(c)`: on bool × bool with the uniform discrete
// probability, bow_u = fst(u) with noise σ(fst), bow_x = bow_u with
// trivial noise, and bow_y = snd(u) when bow_x = bow_u and c otherwise,
// with noise σ(snd). Every state carrier is bool with all its subsets.
var BowModelDef = bowModelDefThm{family.Define(registry.DefEntry{
	Name:  "BowModelDef",
	Key:   "prop_309bdeeca0660a48",
	Const: "bow_model",
	Type:  "bool → scm_model(prod(bool, bool), bool, bow_node)",
	Equations: []string{
		"∀c:bool. " +
			"    bow_model(c) = " +
			"    mk_scm(𝕌⟨A:prod(bool, bool)⟩, " +
			"        𝕌⟨A:set(prod(bool, bool))⟩, " +
			"        discrete_measure(𝕌⟨A:prod(bool, bool)⟩, " +
			"            λu:prod(bool, bool). extended_of_real(&1 / &4)), " +
			"        {bow_u, bow_x, bow_y}, " +
			"        pair_relation({(bow_u, bow_x), (bow_u, bow_y), (bow_x, bow_y)}), " +
			"        λi:bow_node. 𝕌⟨A:bool⟩, " +
			"        λi:bow_node. 𝕌⟨A:set(bool)⟩, " +
			"        λi:bow_node. ⊥, " +
			"        λi:bow_node. " +
			"            COND(i = bow_u, " +
			"                pullback_sigma(𝕌⟨A:prod(bool, bool)⟩, fst, 𝕌⟨A:set(bool)⟩), " +
			"                COND(i = bow_y, " +
			"                    pullback_sigma(𝕌⟨A:prod(bool, bool)⟩, snd, 𝕌⟨A:set(bool)⟩), " +
			"                    {∅, 𝕌⟨A:prod(bool, bool)⟩})), " +
			"        λi:bow_node. λp:(bow_node → bool). λu:prod(bool, bool). " +
			"            COND(i = bow_u, " +
			"                fst(u), " +
			"                COND(i = bow_x, p(bow_u), COND(p(bow_x) = p(bow_u), snd(u), c))))",
	},
})}

// FdNodeData — the four vertices of the front-door graph U → X, U → Y,
// X → Z → Y: the latent common cause fd_u, the treatment fd_x, the
// mediator fd_z and the outcome fd_y.
var FdNodeData = family.DefineData(registry.DataEntry{
	Name: "FdNode",
	Type: "fd_node",
	Constructors: []proof.DataConstructorSpec{
		{Name: "fd_u"}, {Name: "fd_x"}, {Name: "fd_z"}, {Name: "fd_y"},
	},
	Principles: registry.DataPrinciples{
		Induction: "FdNodeInduction",
		Recursion: "FdNodeRecursion",
		Distinct:  "FdNodeDistinct",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
		peano.SucInjective,
	},
})

// FdNodeInduction — a property of each of the four vertices holds of
// every vertex.
var FdNodeInduction = fdNodeInductionThm{FdNodeData.Induct}

// FdNodeRecursion — a function on the vertices is fixed by its four
// values.
var FdNodeRecursion = fdNodeRecursionThm{FdNodeData.Recursion}

// FdNodeDistinct — the four vertices are pairwise distinct.
var FdNodeDistinct = fdNodeDistinctThm{FdNodeData.Distinct}
