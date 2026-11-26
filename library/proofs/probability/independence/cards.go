package independence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var IndependentProductExpectation = independentProductExpectationThm{family.Add(registry.ProofEntry{
	Name: "IndependentProductExpectation",
	Deps: []registry.EntryLike{
		IndependentNonnegIntegral,
		integral_convergence.MonotoneConvergenceAE,
		nonneg_integral.MonotoneConvergence,
		measure_integral.IntegralAdd,
		measure_integral.IntegralScale,
	},
	Key: "prop_c331712fd9bcda",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀X Y:(A → real).",
		Hypotheses: []string{
			"independent_variables(Ω, S, μ, X, Y)",
			"real_integrable(Ω, S, μ, X)",
			"real_integrable(Ω, S, μ, Y)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. X(x) * Y(x)) ∧ " +
			"expectation(Ω, S, μ, λx:A. X(x) * Y(x)) = expectation(Ω, S, μ, X) * expectation(Ω, S, μ, Y)",
	},
		"IndependentNonnegIntegral gives the identity with an indicator of an event "+
			"of one σ-algebra in place of Y. Simple combinations of such indicators and "+
			"monotone approximation in Y prove the nonnegative identity, including for "+
			"absolute values; separate signs for the integrable real variables."),
})}

var BinaryMixtureExtension = binaryMixtureExtensionThm{family.Add(registry.ProofEntry{
	Name: "BinaryMixtureExtension",
	Reading: "F'(none) is {∅, Ω × {⊤}, Ω × {⊥}, Ω × bool} and F'(some(i)) " +
		"is {s × bool | s ∈ F(i)}; probability_on forces Ω ≠ ∅. A finite " +
		"product reindexes over image(some, K) because some is injective.",
	Key:  "prop_20d36d5da4f8675e",
	Deps: []registry.EntryLike{IndependentFamilyDef, BoolMixtureSigmaDef, BoolMixtureMeasureDef},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀J:set(I). " +
			"∀F:(I → set(set(A))). " +
			"∀F':(option(I) → set(set(prod(A, bool)))).",
		Hypotheses: []string{
			"independent_sigma_family(Ω, S, μ, J, F)",
			"F'(none) = pullback_sigma(set_cross(Ω, 𝕌⟨A:bool⟩), snd, 𝕌⟨A:set(bool)⟩)",
			"∀i:I. F'(some(i)) = pullback_sigma(set_cross(Ω, 𝕌⟨A:bool⟩), fst, F(i))",
		},
		Conclusion: "probability_on(set_cross(Ω, 𝕌⟨A:bool⟩), " +
			"    bool_mixture_sigma(Ω, S), " +
			"    bool_mixture_measure(μ)) ∧ " +
			"independent_sigma_family(set_cross(Ω, 𝕌⟨A:bool⟩), " +
			"    bool_mixture_sigma(Ω, S), " +
			"    bool_mixture_measure(μ), " +
			"    {none} ∪ image(some, J), " +
			"    F')",
	},
		"A fair coin tossed beside a probability space: the sets with both slices in S form a "+
			"σ-algebra, and the average of the slice measures is countably additive with mass one. A "+
			"cylinder E × bool has the mass of E, so the pulled-back family keeps its finite products, and "+
			"a face of the coin cuts each cylinder's mass in half: the coin is independent of every finite "+
			"intersection of cylinders. The σ-algebras are written by slices; no product measure enters."),
})}

var CoinBlocksProbability = coinBlocksProbabilityThm{family.Add(registry.ProofEntry{
	Name: "CoinBlocksProbability",
	Key:  "prop_ba27468465f37c5b",
	Reading: "c(u) is the set of coins of K that show heads at the sample u, one sample for each " +
		"set of coins, so Ω is finite and nonempty and its uniform law is that of card(K) fair coins. " +
		"Every hypothesis is load-bearing. Disjointness: two blocks sharing a coin are not " +
		"independent. L(i) ⊆ K: a coin outside K never shows heads and still counts in 2 ^ card(L(i)). " +
		"finite(J): over infinitely many empty blocks the product reads 1 whatever the event. With J " +
		"empty both sides are 1; an empty block contributes 1 or 0 as the empty set lies in T(i) or not.",
	Deps: []registry.EntryLike{probability_space.UniformProbability, cardinality.CardPowerset},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀K:set(C). " +
			"∀c:(A → set(C)). " +
			"∀J:set(I). " +
			"∀L:(I → set(C)). " +
			"∀T:(I → set(set(C))).",
		Hypotheses: []string{
			"finite(K)",
			"injective_on(Ω, c)",
			"image(c, Ω) = {t:set(C) | t ⊆ K}",
			"finite(J)",
			"∀i:I. i ∈ J ⇒ L(i) ⊆ K",
			"∀i j:I. i ∈ J ∧ j ∈ J ∧ i ≠ j ⇒ L(i) ∩ L(j) = ∅",
		},
		Conclusion: "uniform_measure(Ω, {u:A | u ∈ Ω ∧ (∀i:I. i ∈ J ⇒ (c(u) ∩ L(i)) ∈ T(i))}) = " +
			"extended_of_real(Π_{i∈J} &(card(T(i) ∩ {t:set(C) | t ⊆ L(i)})) / &(2 ^ card(L(i))))",
	},
		"Events decided by disjoint blocks of fair coins have the product of their frequencies. "+
			"Through c the event is a family of subsets of K, and its mass is its size over 2^card(K) "+
			"(UniformProbability, CardPowerset). A subset of K is a choice of a subset of each block and "+
			"one of the coins outside the blocks, the blocks being disjoint inside K: the event has Π "+
			"card(T(i) ∩ …) · 2^(card(K) − Σ card(L(i))) members. Induct on J, splitting off one block."),
})}

var CoinBlocksIndependent = coinBlocksIndependentThm{family.Add(registry.ProofEntry{
	Name: "CoinBlocksIndependent",
	Key:  "prop_51b6ecab7ddc8f21",
	Reading: "The σ-algebra of block i is every event its coins decide. A block may reach " +
		"outside K: a coin there never shows heads and decides nothing. Disjointness is " +
		"load-bearing: two indices sharing a coin of K give an event and its complement. J may be " +
		"infinite: all but finitely many of its blocks then miss K and their σ-algebras are trivial.",
	Deps: []registry.EntryLike{
		CoinBlocksProbability,
		IndependentFamilyDef,
		probability_space.UniformProbability,
		measurable_space.PullbackSigmaAlgebra,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀K:set(C). ∀c:(A → set(C)). ∀J:set(I). ∀L:(I → set(C)).",
		Hypotheses: []string{
			"finite(K)",
			"injective_on(Ω, c)",
			"image(c, Ω) = {t:set(C) | t ⊆ K}",
			"∀i j:I. i ∈ J ∧ j ∈ J ∧ i ≠ j ⇒ L(i) ∩ L(j) = ∅",
		},
		Conclusion: "independent_sigma_family(Ω, " +
			"    {D:set(A) | D ⊆ Ω}, " +
			"    uniform_measure(Ω), " +
			"    J, " +
			"    λi:I. pullback_sigma(Ω, λu:A. c(u) ∩ L(i), 𝕌))",
	},
		"Disjoint blocks of fair coins generate independent σ-algebras. Each is a pullback "+
			"of a discrete σ-algebra, a sub-σ-algebra of the events (PullbackSigmaAlgebra), "+
			"and the uniform law is a probability (UniformProbability). An event of block i is "+
			"the set of samples whose heads inside the block lie in some T(i), and c(u) lies "+
			"in K; so the product rule over a finite subfamily is CoinBlocksProbability at the "+
			"blocks L(i) ∩ K, read at the subfamily and at each of its blocks alone."),
})}
