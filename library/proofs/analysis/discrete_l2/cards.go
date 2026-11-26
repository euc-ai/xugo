package discrete_l2

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/l2_space"
	"github.com/euc-ai/xugo/library/proofs/measure/almost_everywhere_function"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/registry"
)

var DiscreteComplexIntegral = discreteComplexIntegralThm{family.Add(registry.ProofEntry{
	Name: "DiscreteComplexIntegral",
	Deps: []registry.EntryLike{integral_convergence.DiscreteNonnegIntegral},
	Key:  "prop_f478f5a7c4fa8344",
	Build: family.Card(Statement{Binders: "∀J:set(I). ∀w:(I → real). ∀f:(I → complex).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ &0 ≤ w(i)",
			"complex_integrable(J, {E:set(I) | E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), f)",
		},
		Conclusion: "unordered_complex_sums(J, " +
			"    λi:I. complex_of_real(w(i)) * f(i), " +
			"    complex_measure_integral(J, " +
			"        {E:set(I) | E ⊆ J}, " +
			"        discrete_measure(J, λi:I. extended_of_real(w(i))), " +
			"        f))"},
		"The absolute-value integral is the supremum of finite weighted "+
			"absolute subsums, so the unordered complex series is absolutely "+
			"summable. Approximate its integral by finite-support restrictions."),
})}

var SequenceL2Isometry = sequenceL2IsometryThm{family.Add(registry.ProofEntry{
	Name: "SequenceL2Isometry",
	Deps: []registry.EntryLike{
		integral_convergence.DiscreteNonnegIntegral,
		DiscreteComplexIntegral,
		almost_everywhere_function.ClassEqIffAE,
		l2_space.L2InnerClasses,
	},
	Key: "prop_5be64e8dcf6e48b9",
	Reading: "The index set may be uncountable. Strict positivity is essential for injectivity into " +
		"the existing pointwise sequence representation; zero weights would require another quotient.",
	Build: family.Card(Statement{Binders: "∀J:set(I). ∀w:(I → real).",
		Hypotheses: []string{"∀i:I. i ∈ J ⇒ &0 < w(i)"},
		Conclusion: "module_isomorphism(complex_ring, " +
			"    weighted_sequence_module(J, w), " +
			"    lp_module(J, {E:set(I) | E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), &2), " +
			"    ae_class(J, {E:set(I) | E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))))) ∧ " +
			"(∀u v:(I → complex). " +
			"    u ∈ weighted_sequence_module(J, w).carrier ∧ v ∈ weighted_sequence_module(J, w).carrier ⇒ " +
			"    l2_inner(J, " +
			"        {E:set(I) | E ⊆ J}, " +
			"        discrete_measure(J, λi:I. extended_of_real(w(i))), " +
			"        ae_class(J, {E:set(I) | E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), u), " +
			"        ae_class(J, " +
			"            {E:set(I) | E ⊆ J}, " +
			"            discrete_measure(J, λi:I. extended_of_real(w(i))), " +
			"            v)) = " +
			"    weighted_sequence_inner(J, w, u, v))"},
		"The nonnegative integral identity equates square summability with the L2 "+
			"function carrier. Strictly positive weights make each singleton have positive "+
			"mass, so normalized a.e.-equal functions are pointwise equal; the quotient map "+
			"is a bijection. The complex integral identity identifies the two inner products."),
})}
