package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var FactorSetCodesClosed = factorSetCodesClosedThm{family.Add(registry.ProofEntry{
	Name: "FactorSetCodesClosed",
	Key:  "prop_95f5dba33913831a",
	Build: family.Card(
		Statement{
			Binders:    "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{"ring_homomorphism(R, S, f)", "module_on(S, N)"},
			Conclusion: "subgroup(factor_set_ambient(R, S, N), factor_set_codes(R, S, f, N)) ∧ " +
				"closed_in(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N))",
		},
		"Expand the explicit ring and marking axioms. Every defect equation is linear in alpha, beta "+
			"and rho and reads finitely many discrete coordinates; the solution set is a closed subgroup."),
	Deps: []registry.EntryLike{
		FactorSetCodesDef,
		factorSetRingDef,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Expand the explicit ring and marking axioms. Every defect equation is linear in alpha, " +
		"beta and rho and reads finitely many discrete coordinates; the solution set is a closed subgroup.",
})}

var FactorSetCoboundaryContinuous = factorSetCoboundaryContinuousThm{family.Add(registry.ProofEntry{
	Name: "FactorSetCoboundaryContinuous",
	Key:  "prop_2b6614c8df570148",
	Build: family.Card(
		Statement{
			Binders:    "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{"ring_homomorphism(R, S, f)", "module_on(S, N)"},
			Conclusion: "group_homomorphism(factor_set_gauge(S, N), " +
				"    factor_set_group(R, S, f, N), " +
				"    factor_set_coboundary(R, S, f, N)) ∧ " +
				"continuous_map(subtopology(indexed_discrete_topology(S.carrier, λs:B. N.zero, λs:B. N.carrier), " +
				"        factor_set_gauge(S, N).carrier), " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_coboundary(R, S, f, N))",
		},
		"Changing the split extension section by a zero-preserving h gives the displayed "+
			"coboundary. Each coordinate is a finite linear expression, hence continuous."),
	Deps: []registry.EntryLike{
		FactorSetCodesClosed,
		FactorSetCoboundaryDef,
		FactorSetGaugeDef,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Changing the split extension section by a zero-preserving h gives the " +
		"displayed coboundary. Each coordinate is a finite linear expression, hence continuous.",
})}

var FactorSetCodesPolishCover = factorSetCodesPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "FactorSetCodesPolishCover",
	Key:  "prop_f3137d6ee151ce6c",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "polish_cover_on(factor_set_group(R, S, f, N), " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_boundaries(R, S, f, N))",
		},
		"The ambient countable discrete products and the closed gauge subgroup are Polish. Apply "+
			"ClosedSubgroupPolish and ContinuousHomImagePolishable to the coboundary homomorphism."),
	Deps: []registry.EntryLike{
		FactorSetCodesClosed,
		FactorSetCoboundaryContinuous,
		polish_group.DiscreteProductGroupPolish,
		polish_group.ClosedSubgroupPolish,
		polish_group.ContinuousHomImagePolishable,
	},
	Reading: "The ambient countable discrete products and the closed gauge subgroup are Polish. " +
		"Apply ClosedSubgroupPolish and ContinuousHomImagePolishable to the coboundary homomorphism.",
})}

var FactorSetShear = factorSetShearThm{family.Add(registry.ProofEntry{
	Name: "FactorSetShear",
	Key:  "prop_4a0bf6c676908b60",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀z w:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"∀h:(B → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"z ∈ factor_set_codes(R, S, f, N)",
				"w ∈ factor_set_codes(R, S, f, N)",
				"h ∈ factor_set_gauge(S, N).carrier",
			},
			Conclusion: "(w = factor_set_ambient(R, S, N).mul(z, factor_set_coboundary(R, S, f, N, h))) ⇔ " +
				"square_zero_isomorphism(R, " +
				"    N, " +
				"    factor_set_extension(S, f, N, w), " +
				"    factor_set_extension(S, f, N, z), " +
				"    λx:prod(D, B). (N.add(fst(x), h(snd(x))), snd(x)))",
		},
		"Expand additivity, multiplication and the structure map of the shear. "+
			"The displayed sign convention maps the changed section code w back to z."),
	Deps: []registry.EntryLike{FactorSetCoboundaryDef, FactorSetExtensionDef},
	Reading: "Expand additivity, multiplication and the structure map of the " +
		"shear. The displayed sign convention maps the changed section code w back to z.",
})}

var FactorSetIsoIffBoundary = factorSetIsoIffBoundaryThm{family.Add(registry.ProofEntry{
	Name: "FactorSetIsoIffBoundary",
	Key:  "prop_96c7e5d1512ed63b",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀z w:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"z ∈ factor_set_codes(R, S, f, N)",
				"w ∈ factor_set_codes(R, S, f, N)",
			},
			Conclusion: "(∃p:(prod(D, B) → prod(D, B)). " +
				"    square_zero_isomorphism(R, " +
				"        N, " +
				"        factor_set_extension(S, f, N, z), " +
				"        factor_set_extension(S, f, N, w), " +
				"        p)) ⇔ " +
				"factor_set_ambient(R, S, N).mul(z, factor_set_ambient(R, S, N).inv(w)) ∈ " +
				"factor_set_boundaries(R, S, f, N)",
		},
		"Every marked isomorphism is a unique normalized shear on the "+
			"carrier. FactorSetShear identifies its defect with a coboundary."),
	Deps: []registry.EntryLike{FactorSetShear, FactorSetBoundariesDef},
	Reading: "Every marked isomorphism is a unique normalized shear on " +
		"the carrier. FactorSetShear identifies its defect with a coboundary.",
})}

var factorSetExtractDef = factorSetExtractDefThm{family.Define(registry.DefEntry{
	Name:  "factorSetExtractDef",
	Key:   "prop_25337f6158bc8488",
	Const: "factor_set_extract",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"module_ops(B, D) → " +
		"square_zero_ops(A, B, I, D) → " +
		"(B → I) → " +
		"prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, I, D). " +
			"∀s:(B → I). " +
			"    factor_set_extract(R, S, N, E, s) = " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            inverse_on(N.carrier, E.inclusion)( " +
			"                E.ring.sub(E.ring.add(s(fst(p)), s(snd(p))), s(S.add(fst(p), snd(p))))), " +
			"            N.zero), " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            inverse_on(N.carrier, E.inclusion)( " +
			"                E.ring.sub(E.ring.mul(s(fst(p)), s(snd(p))), s(S.mul(fst(p), snd(p))))), " +
			"            N.zero), " +
			"    λr:A. " +
			"        COND(r ∈ R.carrier, " +
			"            inverse_on(N.carrier, E.inclusion)( " +
			"                E.ring.sub(E.structure(r), s(E.projection(E.structure(r))))), " +
			"            N.zero)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Read additive, multiplicative and base-map defects through the inverse " +
		"of the fixed inclusion. The section must preserve zero in realization statements."})}

var FactorSetRealization = factorSetRealizationThm{family.Add(registry.ProofEntry{
	Name: "FactorSetRealization",
	Key:  "prop_f815efef8feab7c",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀E:square_zero_ops(A, B, I, D). " +
				"∀s:(B → I).",
			Hypotheses: []string{
				"square_zero_extension(R, S, f, N, E)",
				"s(S.zero) = E.ring.zero",
				"∀y:B. y ∈ S.carrier ⇒ s(y) ∈ E.ring.carrier ∧ E.projection(s(y)) = y",
			},
			Conclusion: "factor_set_extract(R, S, N, E, s) ∈ factor_set_codes(R, S, f, N) ∧ " +
				"square_zero_isomorphism(R, " +
				"    N, " +
				"    factor_set_extension(S, f, N, factor_set_extract(R, S, N, E, s)), " +
				"    E, " +
				"    λx:prod(D, B). E.ring.add(E.inclusion(fst(x)), s(snd(x))))",
		},
		"Each extension element has a unique kernel component relative to the "+
			"section. Expand the three defects to verify the marked ring isomorphism."),
	Deps: []registry.EntryLike{factorSetExtractDef, FactorSetExtensionDef},
	Reading: "Each extension element has a unique kernel component relative to " +
		"the section. Expand the three defects to verify the marked ring isomorphism.",
})}

var factorSetClassDef = factorSetClassDefThm{family.Define(registry.DefEntry{
	Name:  "factorSetClassDef",
	Key:   "prop_cfd03631c282f7f2",
	Const: "factor_set_class",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"set(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    factor_set_class(R, S, f, N) = " +
			"    induced_map(λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
			"            square_zero_class(R, S, f, N, factor_set_extension(S, f, N, z)))",
	},
	Deps:    []registry.EntryLike{FactorSetExtensionDef},
	Reading: "The code quotient class maps to the existing AQ degree-one class."})}

var FactorSetAQDefinableIso = factorSetAQDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "FactorSetAQDefinableIso",
	Key:  "prop_faf9a8c57a9be555",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
			},
			Conclusion: "borel_cover_iso(factor_set_group(R, S, f, N), " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_boundaries(R, S, f, N), " +
				"    cocycle_group(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    cocycle_topology(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"        aq_topologies(R, S, N), " +
				"        1), " +
				"    coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    factor_set_class(R, S, f, N))",
		},
		"Evaluate a reduced conormal map on the three relation families. Subtract the free "+
			"derivation supported at the zero generator to reduce arbitrary conormal maps. Both "+
			"maps are continuous, preserve actual boundaries and induce the classification "+
			"bijection; FactorSetConormalAgreement and continuous reduction give the inverse lift."),
	Deps: []registry.EntryLike{
		FactorSetCodesPolishCover,
		FactorSetIsoIffBoundary,
		FactorSetRealization,
		FactorSetConormalAgreement,
		definable_andre_quillen.ConormalModelHomeomorphism,
		definable_andre_quillen.ConormalCoboundariesCorrespond,
		square_zero_classification.ExtensionRealizeClass,
	},
	Reading: "The homeomorphic model uses h(x_0)=0. The full conormal model contains " +
		"a contractible coefficient summand; only the quotients are identified here.",
})}
