// parameter_integral.go — integrals over ⟦0, 1⟧ of a function of a point
// and a parameter: their partial derivatives are the integrals of the
// partial derivatives, so they are as smooth as the integrand. Hadamard's
// lemma follows: a smooth function on a convex open set is its value at a
// point plus a combination of the coordinate increments with smooth
// coefficients, the coefficients at the point being the partial
// derivatives there.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/registry"
)

// PartialDerivativeUnderIntegral — differentiation under the integral
// sign along a coordinate, for an integrand of class C¹.
var PartialDerivativeUnderIntegral = partialDerivativeUnderIntegralThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeUnderIntegral",
	Key:  "prop_5771806e46324b8",
	Reading: "W is open in ℝⁿ⁺¹ and holds every point «append»(y, t) with " +
		"y ∈ U and t ∈ ⟦0, 1⟧, the parameter t sitting at coordinate n; j < n " +
		"differentiates along a coordinate of the point, not of the parameter.",
	Deps: []registry.EntryLike{
		real_derivative.MeanValue,
		complete_metric.HeineCantor,
		real_integral.HasIntegralNearConstant,
		real_integral.ContinuousIntegrable,
		PartialDerivativeValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U W:((num → real) → bool). " +
			"∀H:((num → real) → real). " +
			"∀j:num. " +
			"∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"W ∈ euclidean_topology(n + 1)",
			"∀y:(num → real). ∀t:real. y ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(y, t) ∈ W",
			"vec_continuously_differentiable_on⟨n + 1⟩(W, 1, H)",
			"j < n",
			"x ∈ U",
		},
		Conclusion: "partial_derivative_at( " +
			"    λy:(num → real). real_integral(λt:real. H(«append»(y, t)), &0, &1), " +
			"    j, " +
			"    x, " +
			"    real_integral(λt:real. partial_derivative(H, j, «append»(x, t)), &0, &1))",
	},
		"the difference quotient of the integral at step s is the integral over t of the difference "+
			"quotients of H along e_j; by the mean value theorem (real_derivative.MeanValue) each is ∂ⱼH "+
			"at a point between «append»(x, t) and «append»(x + s·e_j, t), within ε of ∂ⱼH(«append»(x, t)) "+
			"for every t once s is small, ∂ⱼH being uniformly continuous on the compact tube of the points "+
			"«append»(y, t) with ‖y − x‖ ≤ ρ and t ∈ ⟦0, 1⟧ inside W (complete_metric.HeineCantor); "+
			"real_integral.HasIntegralNearConstant bounds the difference of the integrals by ε"),
})}

// SmoothParameterIntegral — the integral over ⟦0, 1⟧ of a smooth function
// of a point and a parameter is smooth in the point.
var SmoothParameterIntegral = smoothParameterIntegralThm{family.Add(registry.ProofEntry{
	Name: "SmoothParameterIntegral",
	Key:  "prop_b918e9cab873cb25",
	Deps: []registry.EntryLike{
		PartialDerivativeUnderIntegral,
		SmoothPartial,
		ContinuouslyDifferentiableCongruence,
		complete_metric.HeineCantor,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U W:((num → real) → bool). ∀H:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"W ∈ euclidean_topology(n + 1)",
			"∀y:(num → real). ∀t:real. y ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(y, t) ∈ W",
			"vec_smooth_on⟨n + 1⟩(W, H)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, " +
			"    λy:(num → real). real_integral(λt:real. H(«append»(y, t)), &0, &1))",
	},
		"class k on U for every H smooth on W, by induction on k: the integral is continuous at "+
			"x, H being uniformly continuous on a compact tube about x (complete_metric.HeineCantor); "+
			"its j-th partial derivative is the integral of ∂ⱼH (PartialDerivativeUnderIntegral), ∂ⱼH "+
			"being smooth on W (SmoothPartial), and the induction hypothesis at ∂ⱼH gives its class"),
})}

// Hadamard — Hadamard's lemma: on a convex open set a smooth function is
// g(a) + Σⱼ (xⱼ − aⱼ)·hⱼ(x) with each hⱼ smooth and hⱼ(a) = ∂ⱼg(a).
var Hadamard = hadamardThm{family.Add(registry.ProofEntry{
	Name: "Hadamard",
	Key:  "prop_d800ac3be30e5f3",
	Reading: "Convexity is what puts the segment from a to x inside U; a star-shaped " +
		"U about a would do as well, and this is the form the corpus has a constant for.",
	Deps: []registry.EntryLike{
		SmoothParameterIntegral,
		PartialDerivativeChain,
		real_integral.NewtonLeibnizContinuous,
		convex.ConvexDef,
		SmoothPartial,
		SmoothCompose,
		SmoothConst,
		SmoothCoordinate,
		SmoothAdd,
		SmoothSub,
		SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real). ∀a:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"convex(U)",
			"a ∈ U",
			"vec_smooth_on⟨n⟩(U, g)",
		},
		Conclusion: "∃h:(num → (num → real) → real). " +
			"    (∀j:num. j < n ⇒ vec_smooth_on⟨n⟩(U, h(j)) ∧ h(j)(a) = partial_derivative(g, j, a)) ∧ " +
			"    ∀x:(num → real). x ∈ U ⇒ g(x) = g(a) + Σ_{j<n} (x(j) - a(j)) * h(j)(x)",
	},
		"h(j)(x) = ∫₀¹ ∂ⱼg(a + t·(x − a)) dt. The map M(w) = λi. COND(i < n, a(i) + w(n)·(w(i) − a(i)), "+
			"&0) of ℝⁿ⁺¹ into ℝⁿ, M(«append»(x, t)) = a + t·(x − a), is polynomial in the coordinates and "+
			"so a smooth map on ℝⁿ⁺¹ (SmoothConst, SmoothCoordinate, SmoothSub, SmoothMul, SmoothAdd); W, "+
			"the (n + 1)-vectors M carries into U, is open, M being continuous, and holds U × ⟦0, 1⟧ by "+
			"convexity; ∂ⱼg ∘ M is smooth on W (SmoothPartial, SmoothCompose), so h(j) is smooth "+
			"(SmoothParameterIntegral) and h(j)(a) = ∂ⱼg(a). The identity is the fundamental theorem of "+
			"calculus for t ↦ g(a + t·(x − a)) on ⟦0, 1⟧ (real_integral.NewtonLeibnizContinuous), whose "+
			"derivative is Σⱼ ∂ⱼg(a + t·(x − a))·(x(j) − a(j)) (PartialDerivativeChain)"),
})}
