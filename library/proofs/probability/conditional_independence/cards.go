package conditional_independence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/conditional_projection"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var CondIndepTrivial = condIndepTrivialThm{family.Add(registry.ProofEntry{
	Name: "CondIndepTrivial",
	Key:  "prop_1510d9d5bb8fa3e0",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G K:set(set(A)).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"sigma_algebra_on(Ω, K)",
			"G ⊆ S",
			"K ⊆ S",
		},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, {∅, Ω}, K)",
	},
		"Joining the trivial σ-algebra to K gives K back, so each version "+
			"given K is a version given the join; {∅, Ω} is a sub-σ-algebra of S."),
})}

var CondIndepMonoLeft = condIndepMonoLeftThm{family.Add(registry.ProofEntry{
	Name: "CondIndepMonoLeft",
	Key:  "prop_e5feb40a8c807ddf",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G G' H K:set(set(A)).",
		Hypotheses: []string{
			"cond_independent_sigma(Ω, S, μ, G, H, K)",
			"sigma_algebra_on(Ω, G')",
			"G' ⊆ G",
		},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G', H, K)",
	},
		"The definition quantifies over the events of the left side, so a smaller left side asks less."),
})}

var CondIndepMonoRight = condIndepMonoRightThm{family.Add(registry.ProofEntry{
	Name: "CondIndepMonoRight",
	Key:  "prop_2c2e45e4e6fd5312",
	Deps: []registry.EntryLike{sigma_algebra.GeneratedSigmaLeast, sigma_algebra.GeneratedSigmaAlgebra},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H H' K:set(set(A)).",
		Hypotheses: []string{
			"cond_independent_sigma(Ω, S, μ, G, H, K)",
			"sigma_algebra_on(Ω, H')",
			"H' ⊆ H",
		},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, H', K)",
	},
		"A version Y given K is measurable for σ(K ∪ H') ⊆ σ(K ∪ H), and the "+
			"event-integral identity on the larger σ-algebra restricts to the smaller one."),
})}

var CondIndepAbsorbRight = condIndepAbsorbRightThm{family.Add(registry.ProofEntry{
	Name:    "CondIndepAbsorbRight",
	Reading: "The hypotheses on H serve ⇐ only; ⇒ uses σ(K ∪ σ(H ∪ K)) = σ(H ∪ K).",
	Key:     "prop_5581ea9832a87f16",
	Deps: []registry.EntryLike{
		sigma_algebra.GeneratedSigmaLeast,
		sigma_algebra.GeneratedSigmaAlgebra,
	},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H K:set(set(A)).",
		Hypotheses: []string{"sigma_algebra_on(Ω, H)", "H ⊆ S"},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, H, K) ⇔ " +
			"cond_independent_sigma(Ω, S, μ, G, generated_sigma(Ω, H ∪ K), K)",
	},
		"The definition reads the right side only through σ(K ∪ H), and σ(K ∪ σ(H "+
			"∪ K)) is σ(K ∪ H). The hypotheses on H give the right-to-left direction "+
			"the σ-algebra condition on H that the left side's definition asks for."),
})}

var CondIndepWeakUnion = condIndepWeakUnionThm{family.Add(registry.ProofEntry{
	Name: "CondIndepWeakUnion",
	Key:  "prop_ba52f8d12e1fe678",
	Deps: []registry.EntryLike{
		conditional_projection.CondExpExists,
		conditional_expectation.CondExpUnique,
		conditional_expectation.CondExpAE,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H L K:set(set(A)).",
		Hypotheses: []string{
			"cond_independent_sigma(Ω, S, μ, G, generated_sigma(Ω, H ∪ L), K)",
			"sigma_algebra_on(Ω, H)",
			"sigma_algebra_on(Ω, L)",
			"H ⊆ S",
			"L ⊆ S",
		},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, H, generated_sigma(Ω, K ∪ L))",
	},
		"Take E ∈ G and a version Y given σ(K ∪ L). A version Y₀ given K exists "+
			"(CondExpExists) and is, by the hypothesis, a version given σ(K ∪ H ∪ L); it is "+
			"σ(K ∪ L)-measurable, so it is a version given σ(K ∪ L), and Y = Y₀ almost "+
			"everywhere (CondExpUnique). Hence Y is a version given σ(K ∪ L ∪ H) (CondExpAE)."),
})}

var CondIndepContraction = condIndepContractionThm{family.Add(registry.ProofEntry{
	Name: "CondIndepContraction",
	Key:  "prop_883d1fee49aab949",
	Deps: []registry.EntryLike{
		conditional_projection.CondExpExists,
		conditional_expectation.CondExpUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H L K:set(set(A)).",
		Hypotheses: []string{
			"cond_independent_sigma(Ω, S, μ, G, H, generated_sigma(Ω, K ∪ L))",
			"cond_independent_sigma(Ω, S, μ, G, L, K)",
		},
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, generated_sigma(Ω, H ∪ L), K)",
	},
		"Use the definition twice: a version given K is a version given σ(K ∪ L) "+
			"by the second hypothesis, hence a version given σ(K ∪ L ∪ H) by the first."),
})}

var CondIndepProduct = condIndepProductThm{family.Add(registry.ProofEntry{
	Name: "CondIndepProduct",
	Reading: "Quantifying over every version is harmless both ways: versions " +
		"exist (CondExpExists) and agree almost everywhere. A version lies in [0, 1] " +
		"only almost everywhere, which the a.e. bound of CondExpKnownFactor accepts.",
	Key: "prop_d732147906cd9634",
	Deps: []registry.EntryLike{
		conditional_projection.CondExpExists,
		conditional_expectation.CondExpMono,
		conditional_expectation.CondExpKnownFactor,
		integral_convergence.DominatedConvergenceAE,
		sigma_algebra.PiLambda,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H K:set(set(A)).",
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, H, K) ⇔ " +
			"probability_on(Ω, S, μ) ∧ " +
			"sigma_algebra_on(Ω, G) ∧ " +
			"sigma_algebra_on(Ω, H) ∧ " +
			"sigma_algebra_on(Ω, K) ∧ " +
			"G ⊆ S ∧ " +
			"H ⊆ S ∧ " +
			"K ⊆ S ∧ " +
			"(∀E D:set(A). ∀Y Z:(A → real). " +
			"    E ∈ G ∧ " +
			"    D ∈ H ∧ " +
			"    is_cond_exp(Ω, S, μ, K, λx:A. COND(x ∈ E, &1, &0), Y) ∧ " +
			"    is_cond_exp(Ω, S, μ, K, λx:A. COND(x ∈ D, &1, &0), Z) ⇒ " +
			"    is_cond_exp(Ω, S, μ, K, λx:A. COND(x ∈ E ∩ D, &1, &0), λx:A. Y(x) * Z(x)))",
	},
		"The product of versions is a version for the intersection. ⇒: the integral of the "+
			"indicator of E ∩ D over C ∈ K is that of Y on C ∩ D, and Y is K-measurable with "+
			"values in [0, 1] almost everywhere (CondExpMono), so CondExpKnownFactor turns it into "+
			"the integral of Y Z. ⇐: fix E and a version Y; the events F with ∫_F 1_E = ∫_F Y form "+
			"a λ-system (DominatedConvergenceAE for disjoint unions) containing the π-system of "+
			"the C ∩ D, which generates σ(K ∪ H) (PiLambda). The only use of π–λ in the chapter."),
})}

var CondIndepSymmetric = condIndepSymmetricThm{family.Add(registry.ProofEntry{
	Name: "CondIndepSymmetric",
	Key:  "prop_d6905a3db041a7e2",
	Deps: []registry.EntryLike{CondIndepProduct},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H K:set(set(A)).",
		Hypotheses: []string{"cond_independent_sigma(Ω, S, μ, G, H, K)"},
		Conclusion: "cond_independent_sigma(Ω, S, μ, H, G, K)",
	},
		"The product characterization reads the same with the two sides exchanged."),
})}

var CondIndepAbsorbLeft = condIndepAbsorbLeftThm{family.Add(registry.ProofEntry{
	Name: "CondIndepAbsorbLeft",
	Key:  "prop_427a1dee83839a27",
	Deps: []registry.EntryLike{CondIndepSymmetric, CondIndepAbsorbRight},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H K:set(set(A)).",
		Hypotheses: []string{"cond_independent_sigma(Ω, S, μ, G, H, K)"},
		Conclusion: "cond_independent_sigma(Ω, S, μ, generated_sigma(Ω, G ∪ K), H, K)",
	},
		"Exchange the sides, absorb K into what is now the right side, and exchange back."),
})}

var CondIndepUnconditional = condIndepUnconditionalThm{family.Add(registry.ProofEntry{
	Name: "CondIndepUnconditional",
	Reading: "Ω ≠ ∅ by probability, so a {∅, Ω}-measurable version is " +
		"constant on Ω; σ({∅, Ω} ∪ H) = H because H is a σ-algebra on Ω.",
	Key: "prop_96f24e8d218389f2",
	Deps: []registry.EntryLike{
		independence.IndependentSigmaDef,
		conditional_projection.CondExpExists,
	},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H:set(set(A)).",
		Conclusion: "cond_independent_sigma(Ω, S, μ, G, H, {∅, Ω}) ⇔ independent_sigma(Ω, S, μ, G, H)",
	},
		"Given the trivial σ-algebra a version of the indicator of E is the constant μ(E) "+
			"on Ω, and joining the trivial σ-algebra to H gives H: the version property on D ∈ "+
			"H is μ(E ∩ D) = μ(E) μ(D). The structure conditions are the same on both sides. "+
			"This is the bridge from probability/independence, which does not read this chapter."),
})}

var CondIndepPointFiber = condIndepPointFiberThm{family.Add(registry.ProofEntry{
	Name: "CondIndepPointFiber",
	Reading: "{w} ∈ T alone puts the fibre in the pullback; T need not be a σ-algebra, since the " +
		"hypothesis makes the pullback one. A null fibre makes both sides 0; every mass is at most 1.",
	Key:  "prop_be1253893955e867",
	Deps: []registry.EntryLike{conditional_projection.CondExpExists},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G H:set(set(A)). " +
			"∀W:(A → B). " +
			"∀T:set(set(B)). " +
			"∀w:B. " +
			"∀E D:set(A).",
		Hypotheses: []string{
			"cond_independent_sigma(Ω, S, μ, G, H, pullback_sigma(Ω, W, T))",
			"{w} ∈ T",
			"E ∈ G",
			"D ∈ H",
		},
		Conclusion: "μ(E ∩ D ∩ preimage_on(Ω, W, {w})) * μ(preimage_on(Ω, W, {w})) = " +
			"μ(E ∩ preimage_on(Ω, W, {w})) * μ(D ∩ preimage_on(Ω, W, {w}))",
	},
		"Conditional independence read on one fibre of the conditioning variable. A version Y of "+
			"the indicator of E given σ(W) exists (CondExpExists) and is constant, c, on the fibre F "+
			"= {W = w}, which is an event of σ(W); its integral over F gives μ(E ∩ F) = c μ(F), and "+
			"as a version given σ(σ(W) ∪ H) its integral over F ∩ D gives μ(E ∩ D ∩ F) = c μ(D ∩ F). "+
			"A null fibre makes both sides zero. No finiteness or countability of the target is used."),
})}
