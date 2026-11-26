package kernel_do_calculus

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	"github.com/euc-ai/xugo/library/proofs/causal/graphical_markov"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/probability/conditional_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_kernel"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var RandomRegimeFaces = randomRegimeFacesThm{family.Add(registry.ProofEntry{
	Name: "RandomRegimeFaces",
	Key:  "prop_a6910f8a4b987b7f",
	Reading: "E ∈ the product σ-algebra and C ∈ «Zsigma» are load-bearing: the face masses are " +
		"product masses, integrals of section masses, and the intervened solution is jointly measurable " +
		"in the sample and the drawn values (DoSolveJointMeasurable), so z ↦ P_z(E) is measurable.",
	Deps: []registry.EntryLike{
		intervention.DoSolveJointMeasurable,
		structural_model.ScmSolutionMeasurable,
		product_measure.ProductNonnegIntegral,
		product_measure.ProductMeasureRectangle,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀Z:set(I). " +
			"∀ρ:(set(I → B) → extended_nonneg_real). " +
			"∀E C:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"probability_on(indexed_functions(Z, M.default, M.states), «Zsigma», ρ)",
			"E ∈ indexed_product_sigma(M.nodes, M.default, M.states, M.state_sigma)",
			"C ∈ «Zsigma»",
		},
		Conclusion: "«rprob»({p:prod(prod(A, I → B), bool) | " +
			"        p ∈ «rsample» ∧ snd(p) ∧ snd(fst(p)) ∈ C ∧ random_regime_solve(M, Z, p) ∈ E}) = " +
			"extended_of_real(&1 / &2) * " +
			"nonneg_integral(indexed_functions(Z, M.default, M.states), " +
			"    «Zsigma», " +
			"    restricted_measure(ρ, C), " +
			"    λz:(I → B). scm_distribution(scm_do(M, Z, z), E)) ∧ " +
			"«rprob»({p:prod(prod(A, I → B), bool) | " +
			"        p ∈ «rsample» ∧ ¬snd(p) ∧ snd(fst(p)) ∈ C ∧ random_regime_solve(M, Z, p) ∈ E}) = " +
			"extended_of_real(&1 / &2) * (ρ(C) * scm_distribution(M, E))",
	},
		"On the face F = ⊤ the randomized regime draws z from ρ and solves the model intervened at z, so "+
			"its variables have the ρ-mixture of the interventional distributions; on F = ⊥ they are M's "+
			"solution, independent of the drawn values. The ⊤-face set has one nonempty slice, the pairs (u, "+
			"z) with z ∈ C whose intervened solution lies in E, whose product mass is the ρ-integral over C "+
			"of P_z(E) (ProductNonnegIntegral, the slice being measurable by DoSolveJointMeasurable); the "+
			"⊥-face slice is the rectangle of M's preimage of E with C (ProductMeasureRectangle)."),
})}

var RandomRegimeStructuralFamily = randomRegimeStructuralFamilyThm{family.Add(registry.ProofEntry{
	Name: "RandomRegimeStructuralFamily",
	Key:  "prop_16d72e9354492d40",
	Reading: "ρ ranges over the configurations of Z, so every drawn value is " +
		"legal and each intervened model a model; Z ⊆ M.nodes puts the root's edges " +
		"inside the vertex set. The root carries the drawn values and the coin, a " +
		"node of Z reading the drawn value on F = ⊤ and its parents on F = ⊥.",
	Deps: []registry.EntryLike{
		graphical_markov.SCMStructuralFamily,
		independence.BinaryMixtureExtension,
		independence.IndependentFamilyGroups,
		product_measure.ProductMeasureRectangle,
		intervention.DoSolveJointMeasurable,
		intervention.DoCoordinate,
		dag.AddRootDag,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀Z:set(I). " +
			"∀ρ:(set(I → B) → extended_nonneg_real). " +
			"∀G N:(option(I) → set(set(prod(prod(A, I → B), bool)))).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"Z ⊆ M.nodes",
			"probability_on(indexed_functions(Z, M.default, M.states), «Zsigma», ρ)",
			"G(none) = «root»",
			"∀i:I. " +
				"    G(some(i)) = " +
				"    pullback_sigma(«rsample», " +
				"        λp:prod(prod(A, I → B), bool). random_regime_solve(M, Z, p, i), " +
				"        M.state_sigma(i))",
			"N(none) = «root»",
			"∀i:I. " +
				"    N(some(i)) = " +
				"    pullback_sigma(«rsample», λp:prod(prod(A, I → B), bool). fst(fst(p)), M.noise(i))",
		},
		Conclusion: "structural_sigma_family(«rsample», " +
			"    «revents», " +
			"    «rprob», " +
			"    {none} ∪ image(some, M.nodes), " +
			"    dag_add_root(M.edges, Z), " +
			"    G, " +
			"    N)",
	},
		"The randomized regime is a structural family on the graph with a root above Z. The "+
			"background noise pulled back to the regime samples is independent of the root: the drawn "+
			"values are independent of the background under the product with ρ "+
			"(ProductMeasureRectangle on the rectangles), the coin of both (BinaryMixtureExtension on "+
			"the product space), and the drawn values and the coin group into the root's σ-algebra by "+
			"π–λ (IndependentFamilyGroups). A node outside Z has the same mechanism on both faces, "+
			"applied to its parents' variables and its noise; a node of Z is the drawn value z(i) on "+
			"F = ⊤ (DoCoordinate) and its mechanism on F = ⊥, read through the root, its extra parent."),
})}

var RandomRegimeExchangeIndependence = randomRegimeExchangeIndependenceThm{family.Add(registry.ProofEntry{
	Name: "RandomRegimeExchangeIndependence",
	Key:  "prop_892e3b9a778e611c",
	Reading: "Unlike the two-point regime, the root here carries the drawn values, so " +
		"its independence from V'_Y given V'_{Z ∪ W} says the kernel of Y given (Z, W) is " +
		"shared by the faces even where the observational law of V_Z is null at every point.",
	Deps: []registry.EntryLike{
		RandomRegimeStructuralFamily,
		graphical_markov.StructuralFamilyGlobalMarkov,
		d_separation.RegimeSeparationExchange,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀Y Z W:set(I). ∀ρ:(set(I → B) → extended_nonneg_real).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"probability_on(indexed_functions(Z, M.default, M.states), «Zsigma», ρ)",
			"d_separated(dag_delete_out(M.edges, Z), Y, Z, W)",
		},
		Conclusion: "cond_independent_sigma(«rsample», " +
			"    «revents», " +
			"    «rprob», " +
			"    coordinate_sigma(«rsample», random_regime_solve(M, Z), M.state_sigma, Y), " +
			"    «root», " +
			"    coordinate_sigma(«rsample», random_regime_solve(M, Z), M.state_sigma, Z ∪ W))",
	},
		"Rule 2's independence on the randomized regime: separation with Z's out-edges "+
			"deleted gives separation of Y from the root by Z ∪ W (RegimeSeparationExchange), "+
			"which StructuralFamilyGlobalMarkov reads on RandomRegimeStructuralFamily."),
})}

var KernelDoObserve = kernelDoObserveThm{family.Add(registry.ProofEntry{
	Name: "KernelDoObserve",
	Key:  "prop_e7075ba51bc05d60",
	Reading: "No standard Borel hypothesis: the kernel is given, and one interventional distribution " +
		"is read, so no version question arises. A (Z ∪ W)-configuration is read through its W-part.",
	Deps: []registry.EntryLike{
		graphical_markov.SCMGlobalMarkov,
		intervention.DoLegal,
		intervention.DoCoordinate,
		conditional_distribution.CondIndepDisintegration,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀X Y Z W:set(I). " +
			"∀v:(I → B). " +
			"∀K:((I → B) → set(I → B) → extended_nonneg_real).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"d_separated(dag_delete_in(M.edges, X), Y, Z, X ∪ W)",
			"scm_cond_kernel(scm_do(M, X, v), W, Y, K)",
		},
		Conclusion: "scm_cond_kernel(scm_do(M, X, v), " +
			"    Z ∪ W, " +
			"    Y, " +
			"    λc:(I → B). K(override_on(W, c, M.default)))",
	},
		"Rule 1 in kernel form: under P_x any conditional distribution of V_Y given V_W, "+
			"read on (Z ∪ W)-configurations through their W-part, is one given V_{Z ∪ W}. "+
			"SCMGlobalMarkov on the legal intervened model gives V_Y ⊥ V_Z | V_{X ∪ W}, the "+
			"X-coordinates constant (DoCoordinate); CondIndepDisintegration turns it into the "+
			"kernel statement, a (Z ∪ W)-configuration being the pair of its W- and Z-parts."),
})}

var KernelDoExchange = kernelDoExchangeThm{family.Add(registry.ProofEntry{
	Name: "KernelDoExchange",
	Key:  "prop_7613e48913cca9c",
	Reading: "Stated for a common version, not for every one: a version under " +
		"P_x is free on P_x-null sets of (Z, W)-configurations, which may carry " +
		"mass under P_{x,z}. Y's states standard Borel give the kernel; W's give " +
		"the countable generators along which almost every z is taken at once.",
	Deps: []registry.EntryLike{
		RandomRegimeExchangeIndependence,
		RandomRegimeFaces,
		conditional_distribution.DisintegrationExists,
		conditional_distribution.CondIndepDisintegration,
		polish_space.IndexedProductStandardBorel,
		probability_kernel.KernelJointIntegral,
		intervention.DoCompose,
		intervention.DoLegal,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Y ∪ W ⇒ standard_borel_on(M.states(i), M.state_sigma(i))",
			"d_separated(dag_delete_out(dag_delete_in(M.edges, X), Z), Y, Z, X ∪ W)",
		},
		Conclusion: "∃K:((I → B) → set(I → B) → extended_nonneg_real). " +
			"    scm_cond_kernel(scm_do(M, X, v), Z ∪ W, Y, K) ∧ " +
			"    measure_ae(indexed_functions(Z, M.default, M.states), " +
			"        «Zsigma», " +
			"        scm_marginal(scm_do(M, X, v), Z), " +
			"        λz:(I → B). " +
			"            scm_cond_kernel(scm_do(M, X ∪ Z, override_on(Z, z, v)), " +
			"                W, " +
			"                Y, " +
			"                λw:(I → B). K(override_on(Z, z, w))))",
	},
		"Rule 2 in kernel form: some conditional distribution K of V_Y given V_{Z ∪ W} under P_x is, at "+
			"almost every z for the law of V_Z under P_x, a conditional distribution of V_Y given V_W under "+
			"P_{x,z}. Take the randomized regime of M_x with ρ that law: Y is independent of the root given "+
			"Z ∪ W (RandomRegimeExchangeIndependence), so a disintegration of the regime's law of (V'_{Z ∪ "+
			"W}, V'_Y) (DisintegrationExists) serves given the root too (CondIndepDisintegration). On F = ⊥ "+
			"that is the P_x statement; on F = ⊤ the law is the ρ-mixture of the P_{x,z} with V'_Z = z "+
			"(RandomRegimeFaces), and the identity on rectangles from countable generators of the W- and "+
			"Y-configurations holds at almost every z at once, then on all rectangles."),
})}

var KernelDoExchangeVersion = kernelDoExchangeVersionThm{family.Add(registry.ProofEntry{
	Name: "KernelDoExchangeVersion",
	Key:  "prop_dafd9a97ff71e25c",
	Reading: "The absolute continuity is load-bearing: it is what lets any version under P_x " +
		"stand for the common one. The comparison measure is the ρ-mixture of the interventional " +
		"laws of V_W beside the drawn z, the law of (V'_Z, V'_W) on the face F = ⊤.",
	Deps: []registry.EntryLike{
		KernelDoExchange,
		conditional_distribution.DisintegrationUnique,
		probability_kernel.KernelJointIntegral,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀X Y Z W:set(I). " +
			"∀v:(I → B). " +
			"∀K:((I → B) → set(I → B) → extended_nonneg_real).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Y ∪ W ⇒ standard_borel_on(M.states(i), M.state_sigma(i))",
			"d_separated(dag_delete_out(dag_delete_in(M.edges, X), Z), Y, Z, X ∪ W)",
			"scm_cond_kernel(scm_do(M, X, v), Z ∪ W, Y, K)",
			"∀E:set(prod(I → B, I → B)). " +
				"    E ∈ " +
				"    product_sigma(indexed_functions(Z, M.default, M.states), " +
				"        «Zsigma», " +
				"        indexed_functions(W, M.default, M.states), " +
				"        «Wsigma») ∧ " +
				"    scm_joint_law(scm_do(M, X, v), Z, W, E) = &0 ⇒ " +
				"    kernel_joint(indexed_functions(Z, M.default, M.states), " +
				"        «Zsigma», " +
				"        scm_marginal(scm_do(M, X, v), Z), " +
				"        λz:(I → B). scm_marginal(scm_do(M, X ∪ Z, override_on(Z, z, v)), W), " +
				"        E) = " +
				"    &0",
		},
		Conclusion: "measure_ae(indexed_functions(Z, M.default, M.states), " +
			"    «Zsigma», " +
			"    scm_marginal(scm_do(M, X, v), Z), " +
			"    λz:(I → B). " +
			"        scm_cond_kernel(scm_do(M, X ∪ Z, override_on(Z, z, v)), " +
			"            W, " +
			"            Y, " +
			"            λw:(I → B). K(override_on(Z, z, w))))",
	},
		"Where the interventional laws of V_W, mixed over the drawn z, are absolutely continuous "+
			"with respect to the law of (V_Z, V_W) under P_x, every conditional distribution K of "+
			"V_Y given V_{Z ∪ W} under P_x does what KernelDoExchange asks of one. K agrees with the "+
			"common version K* almost everywhere under P_x (DisintegrationUnique), so almost "+
			"everywhere under the mixture; integrating over z (KernelJointIntegral), at almost every "+
			"z the two agree almost everywhere under P_{x,z}'s law of V_W, and a disintegration "+
			"changed on a null set of its first marginal is one still."),
})}

var KernelDoDelete = kernelDoDeleteThm{family.Add(registry.ProofEntry{
	Name: "KernelDoDelete",
	Key:  "prop_8fdcfcd1f7d0f18d",
	Reading: "Stated for a common version, as Rule 2 is; Y's states " +
		"standard Borel give it. Z is never conditioned on, so it needs " +
		"legal values only, and the two-point regime of do(Z = v) suffices.",
	Deps: []registry.EntryLike{
		do_calculus.RegimeDeleteIndependence,
		intervention.RegimeFaces,
		conditional_distribution.DisintegrationExists,
		conditional_distribution.CondIndepDisintegration,
		polish_space.IndexedProductStandardBorel,
		intervention.DoCompose,
		intervention.DoLegal,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ∪ Z ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Y ⇒ standard_borel_on(M.states(i), M.state_sigma(i))",
			"d_separated( " +
				"    dag_delete_in(dag_delete_in(M.edges, X), Z ∖ dag_ancestors(dag_delete_in(M.edges, X), W)), " +
				"    Y, " +
				"    Z, " +
				"    X ∪ W)",
		},
		Conclusion: "∃K:((I → B) → set(I → B) → extended_nonneg_real). " +
			"    scm_cond_kernel(scm_do(M, X, v), W, Y, K) ∧ scm_cond_kernel(scm_do(M, X ∪ Z, v), W, Y, K)",
	},
		"Rule 3 in kernel form: one kernel is a conditional distribution of V_Y given V_W under "+
			"both P_x and P_{x,z}. On the regime family of M_x and do(Z = v), Y is independent of the "+
			"coin given W (RegimeDeleteIndependence); a disintegration of the regime's law of (V'_W, "+
			"V'_Y) (DisintegrationExists) serves given the coin too (CondIndepDisintegration), and "+
			"each face has mass one half, its law being P_x's or P_{x,z}'s (RegimeFaces, DoCompose)."),
})}

var KernelDoDeleteVersion = kernelDoDeleteVersionThm{family.Add(registry.ProofEntry{
	Name: "KernelDoDeleteVersion",
	Key:  "prop_41f9c184e2334ee6",
	Reading: "The absolute continuity is load-bearing: without it a version under " +
		"P_x is free on the P_x-null sets of W-configurations where P_{x,z} puts mass.",
	Deps: []registry.EntryLike{KernelDoDelete, conditional_distribution.DisintegrationUnique},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀X Y Z W:set(I). " +
			"∀v:(I → B). " +
			"∀K:((I → B) → set(I → B) → extended_nonneg_real).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ∪ Z ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Y ⇒ standard_borel_on(M.states(i), M.state_sigma(i))",
			"d_separated( " +
				"    dag_delete_in(dag_delete_in(M.edges, X), Z ∖ dag_ancestors(dag_delete_in(M.edges, X), W)), " +
				"    Y, " +
				"    Z, " +
				"    X ∪ W)",
			"scm_cond_kernel(scm_do(M, X, v), W, Y, K)",
			"∀b:set(I → B). " +
				"    b ∈ «Wsigma» ∧ scm_marginal(scm_do(M, X, v), W, b) = &0 ⇒ " +
				"    scm_marginal(scm_do(M, X ∪ Z, v), W, b) = &0",
		},
		Conclusion: "scm_cond_kernel(scm_do(M, X ∪ Z, v), W, Y, K)",
	},
		"Where the law of V_W under P_{x,z} is absolutely continuous with respect to its "+
			"law under P_x, every conditional distribution of V_Y given V_W under P_x is one "+
			"under P_{x,z}: it agrees with the common version of KernelDoDelete almost "+
			"everywhere under P_x (DisintegrationUnique), so almost everywhere under P_{x,z}."),
})}

var BackdoorAdjustmentKernel = backdoorAdjustmentKernelThm{family.Add(registry.ProofEntry{
	Name: "BackdoorAdjustmentKernel",
	Key:  "prop_bffbc6d6e12a7c7b",
	Reading: "The overlap is load-bearing: it moves the almost-everywhere agreement of " +
		"two versions from the joint law of (X, Z) to the product of the marginals the " +
		"formula integrates against. The formula holds for almost every x only: at a single " +
		"point of a continuous X the conditional distribution is unconstrained. Z's states " +
		"standard Borel give the countable generators of the exchange; X's are unrestricted.",
	Deps: []registry.EntryLike{
		KernelDoExchange,
		intervention.DoNonDescendant,
		intervention.DoEmpty,
		dag.DescendantsAncestorsDual,
		conditional_distribution.DisintegrationUnique,
		product_measure.ProductNonnegIntegral,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). " +
			"∀X Y Z:set(I). " +
			"∀K:((I → B) → set(I → B) → extended_nonneg_real).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"backdoor_criterion(M.edges, X, Y, Z)",
			"∀i:I. i ∈ Y ∪ Z ⇒ standard_borel_on(M.states(i), M.state_sigma(i))",
			"scm_cond_kernel(M, X ∪ Z, Y, K)",
			"∀E:set(prod(I → B, I → B)). " +
				"    E ∈ " +
				"    product_sigma(indexed_functions(X, M.default, M.states), " +
				"        «Xsigma», " +
				"        indexed_functions(Z, M.default, M.states), " +
				"        «Zsigma») ∧ " +
				"    scm_joint_law(M, X, Z, E) = &0 ⇒ " +
				"    product_measure(indexed_functions(X, M.default, M.states), " +
				"        «Xsigma», " +
				"        scm_marginal(M, X), " +
				"        scm_marginal(M, Z), " +
				"        E) = " +
				"    &0",
		},
		Conclusion: "measure_ae(indexed_functions(X, M.default, M.states), " +
			"    «Xsigma», " +
			"    scm_marginal(M, X), " +
			"    λx:(I → B). ∀a:set(I → B). " +
			"        a ∈ «Ysigma» ⇒ " +
			"        scm_marginal(scm_do(M, X, x), Y, a) = " +
			"        nonneg_integral(indexed_functions(Z, M.default, M.states), " +
			"            «Zsigma», " +
			"            scm_marginal(M, Z), " +
			"            λz:(I → B). K(override_on(X, x, z), a)))",
	},
		"The back-door adjustment for continuous variables: for almost every x, P_x(V_Y ∈ a) = ∫ "+
			"K((x, z), a) P^Z(dz), K a conditional distribution of V_Y given V_{X ∪ Z}. Rule 2 in "+
			"kernel form at the groups (∅, Y, X, Z) gives a common version K* (KernelDoExchange, its "+
			"separation the criterion's): at almost every x, K*(x, ·) is a conditional distribution of "+
			"V_Y given V_Z under P_x, so P_x(V_Y ∈ a) = ∫ K*((x, z), a) P_x^Z(dz), and P_x^Z = P^Z "+
			"since no point of X is an ancestor of Z (DoNonDescendant). K = K* almost everywhere under "+
			"the joint law of (X, Z) (DisintegrationUnique), so under the product of the marginals by "+
			"the overlap, and by Tonelli (ProductNonnegIntegral) at almost every x for almost every z."),
})}
