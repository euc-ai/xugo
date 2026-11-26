package curve_valuation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/filtered_space"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/registry"
)

var StructureRingHasPoleAtOrigin = structureRingHasPoleAtOriginThm{family.Add(registry.ProofEntry{
	Name: "StructureRingHasPoleAtOrigin",
	Key:  "prop_82373508f11a2f7d",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		elliptic_curve.OriginRegular,
		elliptic_curve.WeierstrassBasisZero,
	},
	Reading: "k need not be finite: the pole bounds of x and y at the " +
		"origin and the constants in L(0O) hold over any field of constants.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b g:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"g ∈ weierstrass_chart_zero(field_ring(L), k, x, y)",
		},
		Conclusion: "∃n:num. g ∈ elliptic_pole_space(L, k, x, y, n).carrier",
	},
		"The affine generators x and y lie in L(2O) and L(3O). Write g=p(x)+q(x)y "+
			"and use the largest monomial pole bound; constants lie in L(0O)."),
})}

var OriginPoleData = originPoleDataThm{family.Add(registry.ProofEntry{
	Name: "OriginPoleData",
	Key:  "prop_f0a2ff5a70094295",
	Reading: "The model data the regular-point chapter asks for at the origin: " +
		"WeierstrassIsCurve makes the model a curve over the line inside its own function field, " +
		"and OriginRegular makes the origin a regular rational point; nothing about the constant " +
		"field enters. The pole spaces are one expression read twice, and the pole order of a " +
		"nonzero member of the chart ring is minus its order at the origin, which is never positive " +
		"there: a nonzero affine function vanishing at the origin would be a nonzero constant.",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		poleOrderDef,
		StructureRingHasPoleAtOrigin,
		regular_point.SinglePointPoleSpaceDef,
		regular_point.RegularPointOrderAndFiltration,
		regular_point.RegularPointOrderDef,
		valuation_order.ValuationOrderDef,
		elliptic_curve.WeierstrassIsCurve,
		elliptic_curve.OriginRegular,
		elliptic_curve.WeierstrassGlobalSections,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∀n:num. " +
			"    elliptic_pole_space(L, k, x, y, n) = " +
			"    single_point_pole_space(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        n)) ∧ " +
			"(∀g:A. " +
			"    g ∈ weierstrass_chart_zero(field_ring(L), k, x, y) ∧ g ≠ L.zero ⇒ " +
			"    regular_point_order(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        g) = " +
			"    -int_of_num(elliptic_pole_order(L, k, x, y, g)))",
	},
		"Pole spaces: poleSpaceDef and SinglePointPoleSpaceDef are one expression at the "+
			"Weierstrass charts and the origin, H⁰ of the n-th power of the inverse of the origin's "+
			"pair. Order: WeierstrassIsCurve makes the model a curve over the line inside L and the "+
			"origin is a regular rational point (OriginRegular), so RegularPointOrderAndFiltration "+
			"applies at L and P the origin; a nonzero g ∈ A₀ lies in some L(mO) "+
			"(StructureRingHasPoleAtOrigin), where its membership clause reads g ∈ L(nO) ⇔ −n ≤ "+
			"ord(g) for n ≤ m; ord(g) ≤ 0, since ord(g) > 0 would put g in L(0) = A₀ ∩ A₁ = k "+
			"(WeierstrassGlobalSections), a nonzero constant, of order zero as a unit of the local "+
			"ring (ValuationOrderDef); so the least n with g ∈ L(nO) (poleOrderDef) is −ord(g)."),
})}

var PoleSpaceMembership = poleSpaceMembershipThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceMembership",
	Key:  "prop_996cd03d209a072",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		poleOrderDef,
		StructureRingHasPoleAtOrigin,
		nat_order.WellOrdering,
		elliptic_curve.OriginRegular,
	},
	Reading: "",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b g:A. ∀n:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
			"g ∈ weierstrass_chart_zero(field_ring(L), k, x, y)",
			"g ≠ L.zero",
		},
		Conclusion: "g ∈ elliptic_pole_space(L, k, x, y, n).carrier ⇔ " +
			"elliptic_pole_order(L, k, x, y, g) ≤ n",
	},
		"Existence comes from StructureRingHasPoleAtOrigin; well-ordering "+
			"gives the minimal n. The pole-space filtration is increasing because "+
			"the origin ideal is integral, proving the converse for all n."),
})}

var PoleOrderAdditive = poleOrderAdditiveThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderAdditive",
	Key:  "prop_e099bff43bd4c945",
	Deps: []registry.EntryLike{
		OriginPoleData,
		regular_point.RegularPointOrderAndFiltration,
		valuation_order.ValuationOrderDef,
		field.MulEqZeroOn,
	},
	Reading: "The pole order is minus the order at the origin on the " +
		"nonzero members of A₀ (OriginPoleData), and that order is a valuation " +
		"on L; the affine and nonzero guards are where the identification holds.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b g h:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
			"g ∈ weierstrass_chart_zero(field_ring(L), k, x, y)",
			"h ∈ weierstrass_chart_zero(field_ring(L), k, x, y)",
			"g ≠ L.zero",
			"h ≠ L.zero",
		},
		Conclusion: "elliptic_pole_order(L, k, x, y, g * h) = " +
			"elliptic_pole_order(L, k, x, y, g) + elliptic_pole_order(L, k, x, y, h)",
	},
		"g · h is a nonzero member of A₀ (MulEqZeroOn), so OriginPoleData reads the three pole orders "+
			"as minus the orders at the origin, and the valuation law of RegularPointOrderAndFiltration "+
			"there gives ord(g · h) = ord(g) + ord(h) (ValuationOrderDef); negate."),
})}

var PoleOrderFiltrationStep = poleOrderFiltrationStepThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderFiltrationStep",
	Key:  "prop_d039035b0cc6f5f7",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		OriginPoleData,
		regular_point.RegularPointOrderAndFiltration,
		PoleSpaceMembership,
		elliptic_curve.OriginRegular,
		elliptic_curve.WeierstrassIsCurve,
		algebraic_curve.TwistFinite,
		lattice_pair_twist.LatticePairTwistDef,
		module_dimension.SubmoduleDim,
	},
	Reading: "Finite dimensionality of the section spaces must be established " +
		"before comparing their total natural-valued dimensions. The increment by " +
		"at most one is the regular-point chapter's, read at the origin.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀n:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "module_dim(restrict_ring(field_ring(L), k), elliptic_pole_space(L, k, x, y, n)) ≤ " +
			"module_dim(restrict_ring(field_ring(L), k), elliptic_pole_space(L, k, x, y, n + 1)) ∧ " +
			"module_dim(restrict_ring(field_ring(L), k), elliptic_pole_space(L, k, x, y, n + 1)) ≤ " +
			"module_dim(restrict_ring(field_ring(L), k), elliptic_pole_space(L, k, x, y, n)) + 1",
	},
		"L(nO) is H⁰ of the structure pair twisted n times at the origin (poleSpaceDef, "+
			"LatticePairTwistDef), a regular point (OriginRegular) of the curve "+
			"WeierstrassIsCurve, so finite-dimensional (TwistFinite, once per twist); L(nO) ⊆ "+
			"L((n + 1)O) by PoleSpaceMembership on nonzero members, so the first inequality is "+
			"SubmoduleDim; the second is the increment clause of RegularPointOrderAndFiltration "+
			"at the origin, through OriginPoleData's identification of the pole spaces."),
})}

var PoleOrderBasisExists = poleOrderBasisExistsThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderBasisExists",
	Key:  "prop_9fa82dc339db088d",
	Deps: []registry.EntryLike{
		poleOrderBasisDef,
		poleSpaceDef,
		PoleOrderFiltrationStep,
		PoleSpaceMembership,
		PoleSpaceDimension,
		elliptic_curve.WeierstrassGlobalSections,
		filtered_space.FilteredSpaceAdaptedBasis,
	},
	Reading: "The pole spaces L(0) = k ⊆ L(O) ⊆ … ⊆ L(nO), preceded by {zero}, are a " +
		"filtration of L(nO) rising by at most one at each step; the adapted basis of such " +
		"a filtration has one vector per step that rises, and the step is its pole order.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀n:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "∃S:set(A). elliptic_pole_basis(L, k, x, y, n, S)",
	},
		"filtered_space.FilteredSpaceAdaptedBasis at V = L(nO) with F(0) = {zero} and F(i) = "+
			"L((i − 1)O) for 0 < i ≤ n + 1: the pole spaces increase (PoleSpaceMembership), L(0) "+
			"is H⁰(O) = k (poleSpaceDef, WeierstrassGlobalSections), one-dimensional, each later "+
			"step rises by at most one (PoleOrderFiltrationStep) and V is finite-dimensional "+
			"(PoleSpaceDimension at n ≥ 1, k at n = 0); a basis vector of layer i lies in L((i − "+
			"1)O) and not in L((i − 2)O), so its pole order is i − 1 (PoleSpaceMembership), and "+
			"distinct layers are distinct pole orders (poleOrderBasisDef)."),
})}

var PoleSpacePolynomialForm = poleSpacePolynomialFormThm{family.Add(registry.ProofEntry{
	Name: "PoleSpacePolynomialForm",
	Key:  "prop_f9d13912b6eb9727",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		OriginPoleData,
		regular_point.RegularPointOrderAndFiltration,
		valuation_order.ValuationOrderDef,
		valuation_order.UniqueExtremeOrderNonzero,
		elliptic_curve.WeierstrassBasisZero,
		elliptic_curve.UniformizerAtOrigin,
		PoleOrderAdditive,
		PoleSpaceMembership,
	},
	Reading: "Zero polynomials are excluded from their weight bounds. The nonzero " +
		"polynomial parts have even and odd pole weights, so their largest poles cannot cancel.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀n:num. ∀g:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "g ∈ elliptic_pole_space(L, k, x, y, n).carrier ⇔ " +
			"∃p q:(num → A). " +
			"    polynomial_over(k, p) ∧ " +
			"    polynomial_over(k, q) ∧ " +
			"    g = polynomial_eval(p, x) + polynomial_eval(q, x) * y ∧ " +
			"    (p ≠ vec_zero ⇒ 2 * polynomial_degree(p) ≤ n) ∧ " +
			"    (q ≠ vec_zero ⇒ 2 * polynomial_degree(q) + 3 ≤ n)",
	},
		"The structure-ring basis gives a unique expression p(x) + q(x) · y (WeierstrassBasisZero). "+
			"UniformizerAtOrigin gives pole orders 2 for x and 3 for y, so the monomials xⁱ and xʲ · y "+
			"have pole orders 2i and 2j + 3 (PoleOrderAdditive), all distinct, and a nonzero combination "+
			"has the pole order of its largest monomial by the unequal-order clause of the valuation ord "+
			"at the origin (RegularPointOrderAndFiltration, ValuationOrderDef, UniqueExtremeOrderNonzero, "+
			"read through OriginPoleData): 2 deg p for p ≠ vec_zero, 2 deg q + 3 for q ≠ vec_zero, and "+
			"the two parities never meet; g ∈ L(nO) iff that pole order is at most n "+
			"(PoleSpaceMembership). Zero polynomials are omitted from the corresponding weight bound."),
})}

var PoleSpaceDimension = poleSpaceDimensionThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceDimension",
	Key:  "prop_92c91009dd03d801",
	Deps: []registry.EntryLike{
		poleSpaceDef,
		PoleSpacePolynomialForm,
		elliptic_curve.WeierstrassBasisZero,
		module_dimension.DimBasis,
	},
	Reading: "At n=1 only constants occur, giving dimension one. The " +
		"n≥1 condition is essential because L(0O) also has dimension one.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀n:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
			"1 ≤ n",
		},
		Conclusion: "finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    elliptic_pole_space(L, k, x, y, n)) ∧ " +
			"module_dim(restrict_ring(field_ring(L), k), elliptic_pole_space(L, k, x, y, n)) = n",
	},
		"The weighted polynomial description gives basis monomials of weights "+
			"0,2,3,4,... through n. There are n such monomials for n≥1; their "+
			"independence follows from the chart-zero basis and transcendence."),
})}
