package probability_kernel

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var DiracKernel = diracKernelThm{family.Add(registry.ProofEntry{
	Name: "DiracKernel",
	Key:  "prop_88bc87af99f97b53",
	Reading: "The image half of f's measurability puts f(x) in V, where the point mass is a " +
		"probability; the preimage half makes x ↦ dirac_measure(f(x), t) an indicator of an event.",
	Deps: []registry.EntryLike{measure_space.DiracMeasure, measurable_function.RealMeasurableIndicator},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀V:set(B). ∀T:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"sigma_algebra_on(V, T)",
			"measurable_map(Ω, S, V, T, f)",
		},
		Conclusion: "probability_kernel_on(Ω, S, V, T, λx:A. dirac_measure(f(x)))",
	},
		"The deterministic kernel of a measurable map: at x it is the point "+
			"mass at f(x) ∈ V, a probability on (V, T) (DiracMeasure); the mass "+
			"of t ∈ T is the indicator of the event f⁻¹(t), a measurable function."),
})}

var KernelMixtureProbability = kernelMixtureProbabilityThm{family.Add(registry.ProofEntry{
	Name: "KernelMixtureProbability",
	Key:  "prop_abab6f23bdf2e72d",
	Reading: "Countable additivity of the mixture is " +
		"monotone convergence; its total mass is ∫ 1 dμ = 1.",
	Deps: []registry.EntryLike{
		nonneg_integral.MonotoneConvergence,
		nonneg_integral.NonnegIntegralZero,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real).",
		Hypotheses: []string{"probability_on(Ω, S, μ)", "probability_kernel_on(Ω, S, V, T, K)"},
		Conclusion: "probability_on(V, T, kernel_mixture(Ω, S, μ, K))",
	},
		"Mixing a probability kernel against a probability gives a probability: the empty set has "+
			"mass 0 at every point, a disjoint sequence has at each point the series of its masses, "+
			"which MonotoneConvergence exchanges with the integral, and V has mass 1 at every point of Ω."),
})}

var KernelMixtureDirac = kernelMixtureDiracThm{family.Add(registry.ProofEntry{
	Name: "KernelMixtureDirac",
	Key:  "prop_601b7d0def32034d",
	Reading: "No probability hypothesis: any measure. t ∈ T is load-bearing, " +
		"making the preimage an event whose indicator integrates to its measure.",
	Deps: []registry.EntryLike{
		measure_simple.SimpleIntegralIndicator,
		nonneg_integral.NonnegIntegralSimple,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀f:(A → B). " +
			"∀t:set(B).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measurable_map(Ω, S, V, T, f)",
			"t ∈ T",
		},
		Conclusion: "kernel_mixture(Ω, S, μ, λx:A. dirac_measure(f(x)), t) = " +
			"pushforward_measure(Ω, μ, f, t)",
	},
		"Mixing the deterministic kernel of f is pushing forward along f: the "+
			"integrand is the indicator of f⁻¹(t) ∩ Ω, an event, and its integral is "+
			"the measure of that event (SimpleIntegralIndicator, NonnegIntegralSimple)."),
})}

var KernelJointProbability = kernelJointProbabilityThm{family.Add(registry.ProofEntry{
	Name: "KernelJointProbability",
	Key:  "prop_2f253e6ecc9b708c",
	Reading: "The kernel's section masses x ↦ K(x, E_x) are measurable for every E of " +
		"the product σ-algebra, by the π–λ argument of ProductSectionMassMeasurable with " +
		"the kernel in place of ν; the masses being probabilities, no σ-finiteness is asked.",
	Deps: []registry.EntryLike{
		product_measure.ProductSectionMeasurable,
		product_measure.ProductSectionMassMeasurable,
		sigma_algebra.PiLambda,
		nonneg_integral.MonotoneConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real).",
		Hypotheses: []string{"probability_on(Ω, S, μ)", "probability_kernel_on(Ω, S, V, T, K)"},
		Conclusion: "(∀E:set(prod(A, B)). " +
			"    E ∈ product_sigma(Ω, S, V, T) ⇒ " +
			"    extended_measurable(Ω, S, λx:A. K(x, {y:B | (x, y) ∈ E}))) ∧ " +
			"probability_on(set_cross(Ω, V), product_sigma(Ω, S, V, T), kernel_joint(Ω, S, μ, K)) ∧ " +
			"(∀s:set(A). ∀t:set(B). " +
			"    s ∈ S ∧ t ∈ T ⇒ " +
			"    kernel_joint(Ω, S, μ, K, set_cross(s, t)) = " +
			"    nonneg_integral(Ω, S, restricted_measure(μ, s), λx:A. K(x, t)))",
	},
		"A probability joined with a probability kernel is a probability on the product "+
			"σ-algebra, giving a rectangle s × t the integral of K(·, t) over s. The section of a "+
			"measurable set at x is measurable and its kernel mass measurable in x (the π–λ argument "+
			"of the product measure); countable additivity is MonotoneConvergence, and Ω × V has "+
			"mass ∫ K(x, V) μ(dx) = 1. On a rectangle the section mass is K(x, t) on s and 0 off it."),
})}

var KernelJointIntegral = kernelJointIntegralThm{family.Add(registry.ProofEntry{
	Name: "KernelJointIntegral",
	Key:  "prop_9f2266824f0d9a74",
	Deps: []registry.EntryLike{
		KernelJointProbability,
		measure_simple.SimpleApproximation,
		nonneg_integral.MonotoneConvergence,
		nonneg_integral.NonnegIntegralAdd,
		nonneg_integral.NonnegIntegralScale,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀f:(A → B → extended_nonneg_real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"probability_kernel_on(Ω, S, V, T, K)",
			"extended_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). f(fst(p), snd(p)))",
		},
		Conclusion: "nonneg_integral(set_cross(Ω, V), " +
			"    product_sigma(Ω, S, V, T), " +
			"    kernel_joint(Ω, S, μ, K), " +
			"    λp:prod(A, B). f(fst(p), snd(p))) = " +
			"nonneg_integral(Ω, S, μ, λx:A. nonneg_integral(V, T, K(x), λy:B. f(x, y)))",
	},
		"Integrating against μ ⊗ K is integrating against K(x) and then against μ. For "+
			"an indicator it is the definition; simple functions follow by additivity and "+
			"scaling, and measurable f by SimpleApproximation with MonotoneConvergence on "+
			"both sides, the inner integrals increasing in x as measurable functions."),
})}

var KernelJointMarginals = kernelJointMarginalsThm{family.Add(registry.ProofEntry{
	Name: "KernelJointMarginals",
	Key:  "prop_e259f6bed9452ef1",
	Reading: "The first marginal reads K(x, V) = 1 on Ω, so only the kernel's total " +
		"masses matter; the second is the mixture by the definition on the rectangle Ω × t.",
	Deps: []registry.EntryLike{KernelJointProbability},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real).",
		Hypotheses: []string{"probability_on(Ω, S, μ)", "probability_kernel_on(Ω, S, V, T, K)"},
		Conclusion: "(∀s:set(A). " +
			"    s ∈ S ⇒ pushforward_measure(set_cross(Ω, V), kernel_joint(Ω, S, μ, K), fst, s) = μ(s)) ∧ " +
			"(∀t:set(B). " +
			"    t ∈ T ⇒ " +
			"    pushforward_measure(set_cross(Ω, V), kernel_joint(Ω, S, μ, K), snd, t) = " +
			"    kernel_mixture(Ω, S, μ, K, t))",
	},
		"The marginals of μ ⊗ K are μ and μK: the preimage of s under the first projection "+
			"is s × V, whose kernel mass is 1 on s, and that of t under the second is Ω × t, "+
			"whose kernel mass is K(x, t) (KernelJointProbability on the rectangles)."),
})}

var KernelCompose = kernelComposeThm{family.Add(registry.ProofEntry{
	Name: "KernelCompose",
	Key:  "prop_fc1066c50d21915e",
	Reading: "Measurability of x ↦ ∫ L(y, u) K(x, dy) is the kernel analogue of a section " +
		"integral: approximate L(·, u) by simple functions, each giving a finite sum of kernel masses.",
	Deps: []registry.EntryLike{
		KernelMixtureProbability,
		measure_simple.SimpleApproximation,
		nonneg_integral.MonotoneConvergence,
		measurable_function.ExtendedMeasurableSup,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀W:set(C). " +
			"∀U:set(set(C)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀L:(B → set(C) → extended_nonneg_real).",
		Hypotheses: []string{
			"probability_kernel_on(Ω, S, V, T, K)",
			"probability_kernel_on(V, T, W, U, L)",
		},
		Conclusion: "probability_kernel_on(Ω, S, W, U, kernel_compose(V, T, K, L))",
	},
		"Two probability kernels compose into one: at each x ∈ Ω the composite is the mixture "+
			"of L against the probability K(x), a probability (KernelMixtureProbability); for u ∈ "+
			"U the mass x ↦ ∫ L(y, u) K(x, dy) is the supremum of the integrals of simple "+
			"functions below L(·, u), each a finite combination of the measurable K(·, t) "+
			"(SimpleApproximation, MonotoneConvergence, ExtendedMeasurableSup)."),
})}

var KernelComposeAssoc = kernelComposeAssocThm{family.Add(registry.ProofEntry{
	Name: "KernelComposeAssoc",
	Key:  "prop_c2a470627d8a50d1",
	Deps: []registry.EntryLike{
		KernelCompose,
		measure_simple.SimpleApproximation,
		nonneg_integral.MonotoneConvergence,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀W:set(C). " +
			"∀U:set(set(C)). " +
			"∀R:set(D). " +
			"∀Q:set(set(D)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀L:(B → set(C) → extended_nonneg_real). " +
			"∀N:(C → set(D) → extended_nonneg_real). " +
			"∀x:A. " +
			"∀r:set(D).",
		Hypotheses: []string{
			"probability_kernel_on(Ω, S, V, T, K)",
			"probability_kernel_on(V, T, W, U, L)",
			"probability_kernel_on(W, U, R, Q, N)",
			"x ∈ Ω",
			"r ∈ Q",
		},
		Conclusion: "kernel_compose(W, U, kernel_compose(V, T, K, L), N, x, r) = " +
			"kernel_compose(V, T, K, kernel_compose(W, U, L, N), x, r)",
	},
		"Composition of kernels is associative, so finitely many kernels compose in any "+
			"bracketing. Both sides integrate N(·, r) against the two-step mixture: for an indicator "+
			"N(·, r) both are ∫ L(y, w) K(x, dy) for the corresponding set w, and the general case "+
			"follows by simple approximation and monotone convergence through both integrals."),
})}

var KernelMixtureCompose = kernelMixtureComposeThm{family.Add(registry.ProofEntry{
	Name: "KernelMixtureCompose",
	Key:  "prop_95f1590711658670",
	Deps: []registry.EntryLike{
		KernelCompose,
		KernelMixtureProbability,
		measure_simple.SimpleApproximation,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀W:set(C). " +
			"∀U:set(set(C)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀L:(B → set(C) → extended_nonneg_real). " +
			"∀u:set(C).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"probability_kernel_on(Ω, S, V, T, K)",
			"probability_kernel_on(V, T, W, U, L)",
			"u ∈ U",
		},
		Conclusion: "kernel_mixture(V, T, kernel_mixture(Ω, S, μ, K), L, u) = " +
			"kernel_mixture(Ω, S, μ, kernel_compose(V, T, K, L), u)",
	},
		"Mixing in two steps is mixing the composite: (μK)L = μ(K ; L). For L(·, u) "+
			"an indicator both sides are the μK-mass of a set; the general case is simple "+
			"approximation of L(·, u) and monotone convergence, the integral against μK "+
			"of a measurable function being the μ-average of its K(x)-integrals."),
})}

var KernelComposeDirac = kernelComposeDiracThm{family.Add(registry.ProofEntry{
	Name: "KernelComposeDirac",
	Key:  "prop_7e71d77edb71f4b7",
	Reading: "x ∈ Ω and t ∈ T are load-bearing: integrating against the point mass at x reads the " +
		"integrand at x only when the integrand is measurable, and the indicator of t is measurable.",
	Deps: []registry.EntryLike{
		DiracKernel,
		measure_space.DiracMeasure,
		nonneg_integral.NonnegIntegralSimple,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀x:A. " +
			"∀t:set(B).",
		Hypotheses: []string{
			"probability_kernel_on(Ω, S, V, T, K)",
			"x ∈ Ω",
			"t ∈ T",
		},
		Conclusion: "kernel_compose(Ω, S, λy:A. dirac_measure(y), K, x, t) = K(x, t) ∧ " +
			"kernel_compose(V, T, K, λy:B. dirac_measure(y), x, t) = K(x, t)",
	},
		"The identity kernel is a unit on both sides: the K(·, t)-integral against the point mass at x "+
			"is K(x, t), K(·, t) being measurable; and the K(x)-integral of the indicator of t is K(x, t)."),
})}
