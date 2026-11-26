package structural_model

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var ScmSolution = scmSolutionThm{family.Add(registry.ProofEntry{
	Name: "ScmSolution",
	Reading: "dag_on alone suffices: finite V with every edge inside V makes the edges well " +
		"founded on the whole type. With no nodes, the edges are empty and the solution is M.default.",
	Key: "prop_7c8157498a978696",
	Deps: []registry.EntryLike{
		dag.DagWellfounded,
		well_founded.Recursion,
		well_founded.RecursionUnique,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I).",
		Hypotheses: []string{"dag_on(M.nodes, M.edges)"},
		Conclusion: "(∀u:A. scm_equations(M, u, scm_solve(M, u))) ∧ " +
			"(∀u:A. ∀v:(I → B). scm_equations(M, u, v) ⇒ v = scm_solve(M, u))",
	},
		"At every sample the structural equations have exactly one solution, by well-founded "+
			"recursion along the edges (DagWellfounded): the step at i reads the configuration only "+
			"through its restriction to the parents, which is defined for any total map and reads "+
			"only the parents' values, so Recursion applies directly and RecursionUnique gives "+
			"uniqueness; off the nodes the value is fixed. No measurability and no carrier is used."),
})}

var ScmSolutionStates = scmSolutionStatesThm{family.Add(registry.ProofEntry{
	Name: "ScmSolutionStates",
	Reading: "u ∈ M.sample is load-bearing: the image half of a mechanism's measurability " +
		"covers only samples in M.sample. A root's parent configurations are {M.default}.",
	Key: "prop_a749c83a5929a90d",
	Deps: []registry.EntryLike{
		ScmSolution,
		well_founded.RecursionInvariant,
		indexed_functions.OverrideIndexedFunctions,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀u:A.",
		Hypotheses: []string{"scm_on(M)", "u ∈ M.sample"},
		Conclusion: "scm_solve(M, u) ∈ indexed_functions(M.nodes, M.default, M.states)",
	},
		"At a background sample the solution lies in the state carriers, by induction along the graph: "+
			"the restriction to the parents is a parent configuration (OverrideIndexedFunctions), and the "+
			"mechanism maps it with u into the node's states — the image half of its measurability. Off "+
			"the nodes it is the fixed value. So every node's state carrier is nonempty."),
})}

var ScmSolutionMeasurable = scmSolutionMeasurableThm{family.Add(registry.ProofEntry{
	Name: "ScmSolutionMeasurable",
	Key:  "prop_74c0e112b4536ba",
	Deps: []registry.EntryLike{
		ScmSolution,
		ScmSolutionStates,
		measurable_space.IndexedProductMeasurableIff,
		measurable_space.PairedMeasurableIff,
		measurable_space.MeasurableCompose,
		dag.DagWellfounded,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I).",
		Hypotheses: []string{"scm_on(M)"},
		Conclusion: "measurable_map(M.sample, " +
			"    M.events, " +
			"    indexed_functions(M.nodes, M.default, M.states), " +
			"    «configSigma», " +
			"    scm_solve(M))",
	},
		"By IndexedProductMeasurableIff it is enough that each coordinate is measurable, which is "+
			"proved by well-founded induction along the graph: the restriction to the parents is measurable "+
			"into the parent configurations by the same criterion and the induction hypothesis, its pair "+
			"with the identity is measurable for the product with the noise σ-algebra (PairedMeasurableIff, "+
			"the noise lying in the events), and the mechanism is jointly measurable (MeasurableCompose)."),
})}

var ScmDistributionProbability = scmDistributionProbabilityThm{family.Add(registry.ProofEntry{
	Name: "ScmDistributionProbability",
	Reading: "configSigma is a σ-algebra on the configurations, its generators being preimages " +
		"inside them; mass one comes from the solution landing in the configurations (ScmSolutionStates).",
	Key:  "prop_279dd5c11d1f5ea2",
	Deps: []registry.EntryLike{ScmSolutionMeasurable, random_variable.DistributionProbability},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I).",
		Hypotheses: []string{"scm_on(M)"},
		Conclusion: "probability_on(indexed_functions(M.nodes, M.default, M.states), " +
			"    «configSigma», " +
			"    scm_distribution(M))",
	},
		"The distribution of a legal model is a probability on the configurations: "+
			"the solution is a random variable (ScmSolutionMeasurable), and "+
			"DistributionProbability pushes the background probability forward along it."),
})}

var CoinModelLegal = coinModelLegalThm{family.Add(registry.ProofEntry{
	Name: "CoinModelLegal",
	Key:  "prop_f0255dce3269266",
	Reading: "The hypotheses describe a model on finitely many fair coins: c(u) is the set of " +
		"coins of K showing heads at the sample u, one sample for each set, the law is uniform, every " +
		"state carrier is finite and discrete, and node i owns the coins L(i) — its noise is the " +
		"events they decide, and its mechanism reads the sample through them alone. Disjointness of " +
		"the blocks is what makes the noises independent. A mechanism is constrained only at parent " +
		"configurations in the carriers and samples in M.sample. A block may reach outside K, where no " +
		"coin shows heads. dag_on does more than give the first clause of scm_on: it puts every parent " +
		"among the nodes, finitely many, which makes the parent configurations finite and discrete.",
	Deps: []registry.EntryLike{
		ScmOn,
		NoiseIndependentDef,
		probability_space.UniformProbability,
		independence.CoinBlocksIndependent,
		measurable_space.IndexedProductSigmaDiscrete,
		measurable_space.DiscreteSectionsMeasurable,
		measurable_space.PullbackSigmaAlgebra,
		indexed_functions.IndexedFunctionsFinite,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀K:set(C). ∀c:(A → set(C)). ∀L:(I → set(C)).",
		Hypotheses: []string{
			"dag_on(M.nodes, M.edges)",
			"finite(K)",
			"injective_on(M.sample, c)",
			"image(c, M.sample) = {t:set(C) | t ⊆ K}",
			"M.events = {D:set(A) | D ⊆ M.sample}",
			"M.prob = uniform_measure(M.sample)",
			"∀i:I. i ∈ M.nodes ⇒ finite(M.states(i)) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ M.states(i)}",
			"∀i j:I. i ∈ M.nodes ∧ j ∈ M.nodes ∧ i ≠ j ⇒ L(i) ∩ L(j) = ∅",
			"∀i:I. i ∈ M.nodes ⇒ M.noise(i) = pullback_sigma(M.sample, λu:A. c(u) ∩ L(i), 𝕌)",
			"∀i:I. ∀p:(I → B). ∀u:A. " +
				"    i ∈ M.nodes ∧ " +
				"    p ∈ indexed_functions(dag_parents(M.edges, i), M.default, M.states) ∧ " +
				"    u ∈ M.sample ⇒ " +
				"    M.mech(i, p, u) ∈ M.states(i)",
			"∀i:I. ∀p:(I → B). ∀u u':A. " +
				"    i ∈ M.nodes ∧ " +
				"    p ∈ indexed_functions(dag_parents(M.edges, i), M.default, M.states) ∧ " +
				"    u ∈ M.sample ∧ " +
				"    u' ∈ M.sample ∧ " +
				"    c(u) ∩ L(i) = c(u') ∩ L(i) ⇒ " +
				"    M.mech(i, p, u) = M.mech(i, p, u')",
		},
		Conclusion: "scm_on(M) ∧ scm_noise_independent(M)",
	},
		"A model on finitely many fair coins is legal and has independent noise. The sample is finite "+
			"and nonempty, an injective copy of the assignments, so the background is a probability space "+
			"(UniformProbability). A node's noise is a pullback of a discrete σ-algebra, inside the events "+
			"(PullbackSigmaAlgebra). Its mechanism is measurable: the parent configurations are finitely "+
			"many and their product σ-algebra is discrete (IndexedFunctionsFinite, "+
			"IndexedProductSigmaDiscrete), so it is enough that each section u ↦ M.mech(i, p, u) is "+
			"measurable for the noise (DiscreteSectionsMeasurable), and the inverse image of a set of "+
			"states is decided by the node's coins. The noises are independent by CoinBlocksIndependent at "+
			"the nodes. The state σ-algebras and the noises are fixed at the nodes only, which is all that "+
			"a product σ-algebra over the parents and the independence of a family over the nodes read."),
})}
