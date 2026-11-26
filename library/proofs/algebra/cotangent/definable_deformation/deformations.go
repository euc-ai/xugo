package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var DeformationCodesDef = deformationCodesDefThm{family.Define(registry.DefEntry{
	Name:  "DeformationCodesDef",
	Key:   "prop_531613d0560a679a",
	Const: "deformation_codes",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"ring_ops(B) → " +
		"(F → B) → " +
		"module_ops(B, D) → " +
		"(A → D) → " +
		"set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p:(A → F). " +
			"∀S:ring_ops(B). " +
			"∀g:(F → B). " +
			"∀N:module_ops(B, D). " +
			"∀v:(A → D). " +
			"    deformation_codes(R, R₀, p, S, g, N, v) = " +
			"    {z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) | " +
			"        z ∈ factor_set_codes(R, S, λr:A. g(p(r)), N) ∧ " +
			"        (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ snd(snd(z), j) = v(j))}",
	},
	Deps: []registry.EntryLike{FactorSetCodesDef},
	Reading: "Codes whose structure defect restricts " +
		"to the prescribed map on the thickening ideal."})}

var deformationCodeKernelDef = deformationCodeKernelDefThm{family.Define(registry.DefEntry{
	Name:  "deformationCodeKernelDef",
	Key:   "prop_4506084389b80e4f",
	Const: "deformation_code_kernel",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"ring_ops(B) → " +
		"(F → B) → " +
		"module_ops(B, D) → " +
		"set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀R₀:ring_ops(F). ∀p:(A → F). ∀S:ring_ops(B). ∀g:(F → B). ∀N:module_ops(B, D). " +
			"    deformation_code_kernel(R, R₀, p, S, g, N) = " +
			"    {z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) | " +
			"        z ∈ factor_set_codes(R, S, λr:A. g(p(r)), N) ∧ " +
			"        (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ snd(snd(z), j) = N.zero)}",
	},
	Deps:    []registry.EntryLike{FactorSetCodesDef},
	Reading: "The subgroup of codes whose base structure map factors through R₀."})}

var DeformationCodesCoset = deformationCodesCosetThm{family.Add(registry.ProofEntry{
	Name: "DeformationCodesCoset",
	Key:  "prop_fa013bbe568b1757",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p:(A → F). " +
				"∀S:ring_ops(B). " +
				"∀g:(F → B). " +
				"∀N:module_ops(B, D). " +
				"∀v:(A → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, R₀, p)",
				"image(p, R.carrier) = R₀.carrier",
				"∀x y:A. " +
					"    x ∈ ring_kernel(R₀.zero, R.carrier, p) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ " +
					"    R.mul(x, y) = R.zero",
				"ring_homomorphism(R₀, S, g)",
				"module_on(S, N)",
				"module_homomorphism(R₀, thickening_kernel(R, R₀, p), scalar_restriction(g, N), v)",
			},
			Conclusion: "closed_in(factor_set_topology(R, S, N), deformation_codes(R, R₀, p, S, g, N, v)) ∧ " +
				"subgroup(factor_set_ambient(R, S, N), deformation_code_kernel(R, R₀, p, S, g, N)) ∧ " +
				"(∀z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"    z ∈ deformation_codes(R, R₀, p, S, g, N, v) ⇒ " +
				"    deformation_codes(R, R₀, p, S, g, N, v) = " +
				"    left_coset(factor_set_ambient(R, S, N).mul, " +
				"        z, " +
				"        deformation_code_kernel(R, R₀, p, S, g, N))) ∧ " +
				"(∀z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"    z ∈ factor_set_codes(R, S, λr:A. g(p(r)), N) ⇒ " +
				"    (z ∈ deformation_codes(R, R₀, p, S, g, N, v) ⇔ " +
				"        algebra_deformation(R, R₀, p, S, g, N, v, factor_set_extension(S, λr:A. g(p(r)), N, z))))",
		},
		"The rho conditions are closed affine coordinate equations. Subtracting two solutions "+
			"yields the zero-kernel equations; translating by any solution recovers all solutions."),
	Deps: []registry.EntryLike{DeformationCodesDef, deformationCodeKernelDef, FactorSetCodesClosed},
	Reading: "The rho conditions are closed affine coordinate equations. Subtracting two solutions " +
		"yields the zero-kernel equations; translating by any solution recovers all solutions.",
})}

var DeformationKernelIsReducedBase = deformationKernelIsReducedBaseThm{family.Add(registry.ProofEntry{
	Name: "DeformationKernelIsReducedBase",
	Key:  "prop_57153908fa8ca355",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p:(A → F). " +
				"∀S:ring_ops(B). " +
				"∀g:(F → B). " +
				"∀N:module_ops(B, D). " +
				"∀v:(A → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, R₀, p)",
				"image(p, R.carrier) = R₀.carrier",
				"∀x y:A. " +
					"    x ∈ ring_kernel(R₀.zero, R.carrier, p) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ " +
					"    R.mul(x, y) = R.zero",
				"ring_homomorphism(R₀, S, g)",
				"module_on(S, N)",
				"module_homomorphism(R₀, thickening_kernel(R, R₀, p), scalar_restriction(g, N), v)",
			},
			Conclusion: "group_homomorphism(factor_set_group(R₀, S, g, N), " +
				"    restrict_group(factor_set_ambient(R, S, N), deformation_code_kernel(R, R₀, p, S, g, N)), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)). " +
				"        (fst(z), (fst(snd(z)), λr:A. COND(r ∈ R.carrier, snd(snd(z), p(r)), N.zero)))) ∧ " +
				"homeomorphic_map(subtopology(factor_set_topology(R₀, S, N), factor_set_codes(R₀, S, g, N)), " +
				"    subtopology(factor_set_topology(R, S, N), deformation_code_kernel(R, R₀, p, S, g, N)), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)). " +
				"        (fst(z), (fst(snd(z)), λr:A. COND(r ∈ R.carrier, snd(snd(z), p(r)), N.zero)))) ∧ " +
				"image(λz:prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)). " +
				"        (fst(z), (fst(snd(z)), λr:A. COND(r ∈ R.carrier, snd(snd(z), p(r)), N.zero))), " +
				"    factor_set_boundaries(R₀, S, g, N)) = " +
				"factor_set_boundaries(R, S, λr:A. g(p(r)), N)",
		},
		"Inflate rho along the surjection p. A rho vanishing on its kernel descends uniquely; fixed "+
			"representatives of R₀ give a continuous inverse. Gauge coboundaries inflate by the same formula."),
	Deps: []registry.EntryLike{
		deformationCodeKernelDef,
		FactorSetCoboundaryDef,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Inflate rho along the surjection p. A rho vanishing on " +
		"its kernel descends uniquely; fixed representatives of R₀ give a " +
		"continuous inverse. Gauge coboundaries inflate by the same formula.",
})}

var DeformationCodesNonemptyIffObstruction = deformationCodesNonemptyIffObstructionThm{family.Add(registry.ProofEntry{
	Name: "DeformationCodesNonemptyIffObstruction",
	Key:  "prop_3d56c2e4e36a63d1",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p:(A → F). " +
				"∀S:ring_ops(B). " +
				"∀g:(F → B). " +
				"∀N:module_ops(B, D). " +
				"∀v:(A → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, R₀, p)",
				"image(p, R.carrier) = R₀.carrier",
				"∀x y:A. " +
					"    x ∈ ring_kernel(R₀.zero, R.carrier, p) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ " +
					"    R.mul(x, y) = R.zero",
				"ring_homomorphism(R₀, S, g)",
				"module_on(S, N)",
				"module_homomorphism(R₀, thickening_kernel(R, R₀, p), scalar_restriction(g, N), v)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
			},
			Conclusion: "¬(deformation_codes(R, R₀, p, S, g, N, v) = ∅) ⇔ " +
				"algebra_deformation_obstruction⟨U:U⟩(R, R₀, p, S, g, N, v) = " +
				"cotangent_cohomology⟨U:U⟩(R₀, S, g, S, λy:B. y, N, 2).zero",
		},
		"Use DeformationObstruction and extract a code from the "+
			"resulting marked extension along a zero-preserving section."),
	Deps: []registry.EntryLike{
		DeformationCodesCoset,
		FactorSetRealization,
		algebra_deformation.DeformationObstruction,
	},
	Reading: "Use DeformationObstruction and extract a code from " +
		"the resulting marked extension along a zero-preserving section.",
})}

var DeformationCodeAutomorphisms = deformationCodeAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "DeformationCodeAutomorphisms",
	Key:  "prop_b710e28af0f459ed",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p:(A → F). " +
				"∀S:ring_ops(B). " +
				"∀g:(F → B). " +
				"∀N:module_ops(B, D). " +
				"∀v:(A → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, R₀, p)",
				"image(p, R.carrier) = R₀.carrier",
				"∀x y:A. " +
					"    x ∈ ring_kernel(R₀.zero, R.carrier, p) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, p) ⇒ " +
					"    R.mul(x, y) = R.zero",
				"ring_homomorphism(R₀, S, g)",
				"module_on(S, N)",
				"module_homomorphism(R₀, thickening_kernel(R, R₀, p), scalar_restriction(g, N), v)",
			},
			Conclusion: "{h:(B → D) | " +
				"    h ∈ factor_set_gauge(S, N).carrier ∧ " +
				"    factor_set_coboundary(R, S, λr:A. g(p(r)), N, h) = factor_set_ambient(R, S, N).one} = " +
				"{h:(B → D) | h ∈ factor_set_gauge(S, N).carrier ∧ derivation_on(R₀, S, g, N, h)}",
		},
		"The zero additive and multiplicative defects are additivity and the Leibniz "+
			"rule; the zero rho defect forces vanishing on g(R₀) because p is onto. "+
			"Shears identify this kernel with automorphisms of every deformation code."),
	Deps: []registry.EntryLike{
		FactorSetShear,
		DeformationKernelIsReducedBase,
		algebra_deformation.DeformationAutomorphisms,
	},
	Reading: "The zero additive and multiplicative defects are additivity and the " +
		"Leibniz rule; the zero rho defect forces vanishing on g(R₀) because p is " +
		"onto. Shears identify this kernel with automorphisms of every deformation code.",
})}
