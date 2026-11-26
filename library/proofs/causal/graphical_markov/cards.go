package graphical_markov

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/probability/conditional_independence"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var SigmaFamilySemigraphoid = sigmaFamilySemigraphoidThm{family.Add(registry.ProofEntry{
	Name: "SigmaFamilySemigraphoid",
	Reading: "G(j) ⊆ S is load-bearing: cond_independent_sigma " +
		"carries the sub-σ-algebra conditions. The join over ∅ is {∅, Ω}.",
	Key: "prop_9285d961ca4d5018",
	Deps: []registry.EntryLike{
		conditional_independence.CondIndepTrivial,
		conditional_independence.CondIndepSymmetric,
		conditional_independence.CondIndepMonoRight,
		conditional_independence.CondIndepWeakUnion,
		conditional_independence.CondIndepContraction,
		sigma_algebra.SigmaJoinUnion,
		sigma_algebra.SigmaJoinEmpty,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(I). " +
			"∀G:(I → set(set(A))).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"∀j:I. j ∈ V ⇒ sigma_algebra_on(Ω, G(j)) ∧ G(j) ⊆ S",
		},
		Conclusion: "semigraphoid_on(V, " +
			"    λX:set(I). λY:set(I). λZ:set(I). " +
			"        cond_independent_sigma(Ω, " +
			"            S, " +
			"            μ, " +
			"            sigma_join(Ω, G, X), " +
			"            sigma_join(Ω, G, Y), " +
			"            sigma_join(Ω, G, Z)))",
	},
		"The five axioms are the σ-algebra laws of conditional independence read on joins: "+
			"the join over ∅ is trivial (SigmaJoinEmpty, CondIndepTrivial), the join over a "+
			"union is the σ-algebra the two joins generate (SigmaJoinUnion), so decomposition "+
			"is CondIndepMonoRight, weak union CondIndepWeakUnion and contraction "+
			"CondIndepContraction. They hold without the disjointness the axioms allow."),
})}

var StructuralFamilyLocalMarkov = structuralFamilyLocalMarkovThm{family.Add(registry.ProofEntry{
	Name: "StructuralFamilyLocalMarkov",
	Key:  "prop_f63c9080a8f5e795",
	Deps: []registry.EntryLike{
		independence.IndependentFamilyGroups,
		conditional_independence.CondIndepUnconditional,
		conditional_independence.CondIndepWeakUnion,
		conditional_independence.CondIndepAbsorbLeft,
		conditional_independence.CondIndepMonoLeft,
		conditional_independence.CondIndepMonoRight,
		dag.DagWellfounded,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀G N:(I → set(set(A))). " +
			"∀i:I.",
		Hypotheses: []string{"structural_sigma_family(Ω, S, μ, V, E, G, N)", "i ∈ V"},
		Conclusion: "cond_independent_sigma(Ω, " +
			"    S, " +
			"    μ, " +
			"    sigma_join(Ω, G, {i}), " +
			"    sigma_join(Ω, G, V ∖ dag_descendants(E, {i}) ∖ dag_parents(E, i)), " +
			"    sigma_join(Ω, G, dag_parents(E, i)))",
	},
		"By well-founded induction each G(j) lies in the join of the noise of j's "+
			"ancestors, so the information of the non-descendants of i lies in the join of the "+
			"noise of non-descendants, a block of the noise family disjoint from {i}: N(i) is "+
			"independent of it (IndependentFamilyGroups, CondIndepUnconditional). Weak union "+
			"conditions on the parents' information, which lies in that block; left absorption "+
			"adds the parents to N(i); and G(i) lies in the join of the parents' information "+
			"with N(i). No kernel and no pointwise integration of mechanisms enters."),
})}

var StructuralFamilyGlobalMarkov = structuralFamilyGlobalMarkovThm{family.Add(registry.ProofEntry{
	Name: "StructuralFamilyGlobalMarkov",
	Reading: "structural_sigma_family does not state G(j) ⊆ S; it follows by induction along " +
		"the DAG from N(j) ⊆ S, inside the independent family, and SigmaFamilySemigraphoid needs it.",
	Key: "prop_73574b9bbfc31178",
	Deps: []registry.EntryLike{
		StructuralFamilyLocalMarkov,
		SigmaFamilySemigraphoid,
		d_separation.LocalToGlobalMarkov,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀G N:(I → set(set(A))). " +
			"∀X Y Z:set(I).",
		Hypotheses: []string{
			"structural_sigma_family(Ω, S, μ, V, E, G, N)",
			"X ⊆ V",
			"Y ⊆ V",
			"Z ⊆ V",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"d_separated(E, X, Y, Z)",
		},
		Conclusion: "cond_independent_sigma(Ω, " +
			"    S, " +
			"    μ, " +
			"    sigma_join(Ω, G, X), " +
			"    sigma_join(Ω, G, Y), " +
			"    sigma_join(Ω, G, Z))",
	},
		"The one bridge from graph to probability, for any state spaces: the joins form a "+
			"semigraphoid (SigmaFamilySemigraphoid, each G(j) inside the events), it has the "+
			"local Markov property (StructuralFamilyLocalMarkov), and LocalToGlobalMarkov "+
			"reads separation into it. It needs the Markov direction only, not faithfulness."),
})}

var SCMStructuralFamily = sCMStructuralFamilyThm{family.Add(registry.ProofEntry{
	Name: "SCMStructuralFamily",
	Reading: "No induction is needed: each node σ-algebra lies in the one the " +
		"parents' pullbacks and its noise generate, by pairing with the mechanism's " +
		"joint measurability; ScmSolutionStates makes the pullbacks σ-algebras.",
	Key: "prop_19895cee12dbf16a",
	Deps: []registry.EntryLike{
		structural_model.ScmSolution,
		structural_model.ScmSolutionStates,
		structural_model.ScmSolutionMeasurable,
		measurable_space.PairedMeasurableIff,
		measurable_space.IndexedProductMeasurableIff,
		measurable_space.PullbackSigmaAlgebra,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I).",
		Hypotheses: []string{"scm_on(M)", "scm_noise_independent(M)"},
		Conclusion: "structural_sigma_family(M.sample, " +
			"    M.events, " +
			"    M.prob, " +
			"    M.nodes, " +
			"    M.edges, " +
			"    λi:I. pullback_sigma(M.sample, λu:A. scm_solve(M, u, i), M.state_sigma(i)), " +
			"    M.noise)",
	},
		"A legal model with independent noise is a structural family on its own graph: by "+
			"the structural equation V_i is the mechanism applied to the parents' restriction "+
			"and the sample, which is measurable for the σ-algebra the parents' variables and "+
			"N(i) generate (PairedMeasurableIff, IndexedProductMeasurableIff, the mechanism's "+
			"joint measurability). An intervened model is a legal model on the intervened "+
			"graph, so this one member covers every interventional distribution."),
})}

var SCMGlobalMarkov = sCMGlobalMarkovThm{family.Add(registry.ProofEntry{
	Name: "SCMGlobalMarkov",
	Key:  "prop_9f3a19a92825f97c",
	Deps: []registry.EntryLike{SCMStructuralFamily, StructuralFamilyGlobalMarkov},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z:set(I).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"d_separated(M.edges, X, Y, Z)",
		},
		Conclusion: "cond_independent_sigma(M.sample, " +
			"    M.events, " +
			"    M.prob, " +
			"    scm_sigma(M, X), " +
			"    scm_sigma(M, Y), " +
			"    scm_sigma(M, Z))",
	},
		"The global Markov property of a model, Rule 1 of the do-calculus in its independence "+
			"form: the joins of the node σ-algebras of SCMStructuralFamily are the σ-algebras of "+
			"the variable groups by the definitions of scm_sigma and coordinate_sigma."),
})}

var RegimeStructuralFamily = regimeStructuralFamilyThm{family.Add(registry.ProofEntry{
	Name: "RegimeStructuralFamily",
	Reading: "z(i) ∈ M.states(i) on Z makes the intervened model legal, so each G(some(i)) " +
		"is a σ-algebra; Z ⊆ M.nodes puts the edges from none inside the vertex set; the root " +
		"graph keeps the edges into Z, so a node of Z reads its parents on the face F = ⊥.",
	Key: "prop_9ed95e2404494945",
	Deps: []registry.EntryLike{
		SCMStructuralFamily,
		independence.BinaryMixtureExtension,
		intervention.DoLegal,
		dag.AddRootDag,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀Z:set(I). " +
			"∀z:(I → B). " +
			"∀G N:(option(I) → set(set(prod(A, bool)))).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"Z ⊆ M.nodes",
			"∀i:I. i ∈ Z ⇒ z(i) ∈ M.states(i)",
			"G(none) = pullback_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), snd, 𝕌⟨A:set(bool)⟩)",
			"∀i:I. " +
				"    G(some(i)) = " +
				"    pullback_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), " +
				"        λp:prod(A, bool). regime_solve(M, Z, z, p, i), " +
				"        M.state_sigma(i))",
			"N(none) = pullback_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), snd, 𝕌⟨A:set(bool)⟩)",
			"∀i:I. N(some(i)) = pullback_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), fst, M.noise(i))",
		},
		Conclusion: "structural_sigma_family(set_cross(M.sample, 𝕌⟨A:bool⟩), " +
			"    bool_mixture_sigma(M.sample, M.events), " +
			"    bool_mixture_measure(M.prob), " +
			"    {none} ∪ image(some, M.nodes), " +
			"    dag_add_root(M.edges, Z), " +
			"    G, " +
			"    N)",
	},
		"The regime family is a structural family on the graph with the regime root none above Z: "+
			"the pulled-back noise with the coin is independent (BinaryMixtureExtension). A node "+
			"outside Z has the same mechanism on both faces, so its variable is that mechanism of its "+
			"parents' variables and its pulled-back noise; a node of Z is z(i) on one face and its "+
			"mechanism on the other, read through the coin, which is its extra parent. The shared "+
			"noise and the shared inclusions are what tie the two interventional distributions."),
})}
