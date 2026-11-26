// Integrating the dt component gives the chain homotopy between the
// two endpoint restrictions. Time is the last coordinate and first slot.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// HomotopyDef — integrate contraction with the time vector over [0, 1].
var HomotopyDef = homotopyDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopyDef",
	Key:   "prop_891deb1134d7aa09",
	Const: "vec_form_homotopy",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"((num → real) → (num → num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "The argument k is the output degree: K takes (k+1)-forms in dimension n+1 " +
		"to k-forms in dimension n. The parameter is coordinate n but its vector occupies the " +
		"first input column, fixing dK+Kd = j₁*−j₀*. A degree-zero input has a separate " +
		"chain-homotopy statement; no negative degree is encoded by truncated subtraction.",
	Equations: []string{
		"∀n k:num. " +
			"∀U:set(num → real). " +
			"∀ω:((num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_homotopy⟨n⟩(U, k, ω, x, P) = " +
			"    COND(x ∈ U, " +
			"        real_integral(λt:real. " +
			"                ω(«append»(x, t), " +
			"                    λi:num. λj:num. " +
			"                        COND(j = 0, " +
			"                            basis_vector(n, i), " +
			"                            COND(i < n ∧ j < k + 1, P(i, j - 1), &0))), " +
			"            &0, " +
			"            &1), " +
			"        &0)",
	},
})}

var HomotopyForm = homotopyFormThm{family.Add(registry.ProofEntry{
	Name: "HomotopyForm",
	Key:  "prop_53ffa3e100106279",
	Reading: "The input lives on an open neighbourhood W of U×[0,1], not merely on the closed " +
		"strip. Openness and compactness of the parameter interval give the local tubes needed " +
		"for smooth parameter integration; no compact support or global uniform tube is required.",
	Deps: []registry.EntryLike{HomotopyDef, FormOnDef, vec_smooth.SmoothParameterIntegral},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀U W:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_form_on⟨n + 1⟩(W, k + 1, ω)",
			"∀x:(num → real). ∀t:real. x ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(x, t) ∈ W",
		},
		Conclusion: "vec_form_on⟨n⟩(U, k, vec_form_homotopy⟨n⟩(U, k, ω))",
	},
		"Contract the finite coordinate expansion with the first column e_n and integrate its "+
			"coefficients. Each surviving coefficient is, up to its ordering sign, an integral of "+
			"a smooth coefficient over [0,1], so SmoothParameterIntegral applies; the remaining "+
			"columns give the k-form expansion and the outer guard gives zero off U."),
})}

var HomotopyLinear = homotopyLinearThm{family.Add(registry.ProofEntry{
	Name: "HomotopyLinear",
	Key:  "prop_552eb1e63bfd25ea",
	Deps: []registry.EntryLike{
		HomotopyForm,
		FormModule,
		real_integral.ContinuousIntegrable,
		real_integral.HasIntegralAdd,
		real_integral.HasIntegralScale,
		real_integral.HasIntegralValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀U W:set(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "W ∈ euclidean_topology(n + 1)",
			"∀x:(num → real). ∀t:real. x ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(x, t) ∈ W",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    vec_form_module⟨n + 1⟩(W, k + 1), " +
			"    vec_form_module⟨n⟩(U, k), " +
			"    vec_form_homotopy⟨n⟩(U, k))",
	},
		"Smooth coefficient functions restricted to the parameter interval are continuous and "+
			"integrable. Linearity of the real integral gives addition and scalar multiplication pointwise, "+
			"while HomotopyForm gives the target carrier and FormModule gives both module structures."),
})}

var HomotopyOperator = homotopyOperatorThm{family.Add(registry.ProofEntry{
	Name: "HomotopyOperator",
	Key:  "prop_fd34923410bf3399",
	Deps: []registry.EntryLike{
		HomotopyForm,
		ExteriorDerivativeForm,
		PullbackForm,
		vec_smooth.PartialDerivativeUnderIntegral,
		real_integral.NewtonLeibnizContinuous,
		real_integral.HasIntegralValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀U W:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "vec_form_on⟨n + 1⟩(W, k + 1, ω)",
			"∀x:(num → real). ∀t:real. x ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(x, t) ∈ W",
		},
		Conclusion: "(λx:(num → real). λP:(num → num → real). " +
			"    vec_exterior_derivative⟨n⟩(U, k, vec_form_homotopy⟨n⟩(U, k, ω), x, P) + " +
			"    vec_form_homotopy⟨n⟩(U, k + 1, vec_exterior_derivative⟨n + 1⟩(W, k + 1, ω), x, P)) = " +
			"(λx:(num → real). λP:(num → num → real). " +
			"    vec_form_pullback⟨n, n + 1⟩(U, k + 1, λy:(num → real). «append»(y, &1), ω, x, P) - " +
			"    vec_form_pullback⟨n, n + 1⟩(U, k + 1, λy:(num → real). «append»(y, &0), ω, x, P))",
	},
		"Write ω locally as dt∧α+β, with β using only base directions. Then the "+
			"time contraction of dω is ∂ₜβ−dₓα; PartialDerivativeUnderIntegral cancels "+
			"the dₓα terms against dKω, and NewtonLeibnizContinuous integrates ∂ₜβ to "+
			"the two endpoint pullbacks. Zero normalization extends the equality off U."),
})}

var HomotopyOperatorZeroDegree = homotopyOperatorZeroDegreeThm{family.Add(registry.ProofEntry{
	Name: "HomotopyOperatorZeroDegree",
	Key:  "prop_8f9f56de9bf41030",
	Deps: []registry.EntryLike{
		HomotopyDef,
		FormZeroDegree,
		ExteriorDerivativeDef,
		PullbackDef,
		real_integral.NewtonLeibnizContinuous,
		real_integral.HasIntegralValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U W:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "vec_form_on⟨n + 1⟩(W, 0, ω)",
			"∀x:(num → real). ∀t:real. x ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «append»(x, t) ∈ W",
		},
		Conclusion: "vec_form_homotopy⟨n⟩(U, 0, vec_exterior_derivative⟨n + 1⟩(W, 0, ω)) = " +
			"(λx:(num → real). λP:(num → num → real). " +
			"    vec_form_pullback⟨n, n + 1⟩(U, 0, λy:(num → real). «append»(y, &1), ω, x, P) - " +
			"    vec_form_pullback⟨n, n + 1⟩(U, 0, λy:(num → real). «append»(y, &0), ω, x, P))",
	},
		"A zero-form is a smooth scalar coefficient independent of its matrix argument. "+
			"Contracting its derivative with e_n gives its time derivative, whose integral is the "+
			"endpoint difference by NewtonLeibnizContinuous; there is no dK term in degree zero."),
})}
