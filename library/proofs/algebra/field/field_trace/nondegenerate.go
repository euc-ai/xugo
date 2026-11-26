// nondegenerate.go — the chapter's nondegenerate statements.

package field_trace

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// LinearFactorQuotient — The minimal polynomial factors by T−y with its monic cofactor.
var LinearFactorQuotient = linearFactorQuotientThm{family.Add(registry.ProofEntry{
	Name: "LinearFactorQuotient",
	Key:  "prop_7bfc1f0430adc330",
	Deps: []registry.EntryLike{
		algebraic_element.MinimalPolynomialSpec,
		polynomial_roots.FactorTheorem,
		polynomial_division.DivisionExists,
		traceCofactorDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
		},
		Conclusion: "polynomial_over(L.carrier, trace_cofactor(L, K, y)) ∧ " +
			"polynomial_monic(trace_cofactor(L, K, y)) ∧ " +
			"polynomial_degree(trace_cofactor(L, K, y)) + 1 = " +
			"polynomial_degree(minimal_polynomial(L, K, y)) ∧ " +
			"polynomial_mul(vec_sub(basis_vector(1), vec_scalar_mul(y, basis_vector(0))), " +
			"    trace_cofactor(L, K, y)) = " +
			"minimal_polynomial(L, K, y)",
	},
		"The minimal polynomial vanishes at y. Divide by T−y; the monic "+
			"quotient is unique and is the cofactor selected by the definition."),
})}

// CofactorAtRoot — The cofactor at y is the derivative of the minimal polynomial at y.
var CofactorAtRoot = cofactorAtRootThm{family.Add(registry.ProofEntry{
	Name: "CofactorAtRoot",
	Key:  "prop_ae149298b5c22be5",
	Deps: []registry.EntryLike{LinearFactorQuotient, polynomial.DerivativeMul},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
		},
		Conclusion: "polynomial_eval(trace_cofactor(L, K, y), y) = «ftDerivative»",
	},
		"Differentiate μ=(T−y)q and evaluate at y; the product term containing T−y vanishes."),
})}

// CofactorAtRootUnit — Separability makes the derivative value a nonzero field element.
var CofactorAtRootUnit = cofactorAtRootUnitThm{family.Add(registry.ProofEntry{
	Name: "CofactorAtRootUnit",
	Key:  "prop_4f756e5639b91750",
	Deps: []registry.EntryLike{
		algebraic_element.MinimalPolynomialSpec,
		algebraic_element.MinimalPolynomialIrreducible,
		separable_polynomial.SeparableIffDerivative,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "«ftDerivative» ∈ L.carrier ∧ «ftDerivative» ≠ L.zero",
	},
		"For the irreducible minimal polynomial, separability makes the derivative "+
			"nonzero and relatively prime to μ. A common root would contradict minimality."),
})}

// CofactorCoefficients — The cofactor coefficients satisfy the descending monic recurrence.
var CofactorCoefficients = cofactorCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "CofactorCoefficients",
	Key:  "prop_7e9516f280cec20b",
	Deps: []registry.EntryLike{LinearFactorQuotient, polynomial.PolynomialMulDef},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
		},
		Conclusion: "trace_cofactor(L, K, y, polynomial_degree(minimal_polynomial(L, K, y)) - 1) = " +
			"L.one ∧ " +
			"(∀j:num. " +
			"    0 < j ∧ j < polynomial_degree(minimal_polynomial(L, K, y)) ⇒ " +
			"    trace_cofactor(L, K, y, j - 1) = " +
			"    y * trace_cofactor(L, K, y, j) + minimal_polynomial(L, K, y, j))",
	},
		"Compare coefficients of (T−y)q with μ, beginning at the leading term and descending."),
})}

// IdempotentAnnihilatesLinear — Multiplication by the variable on the idempotent agrees with multiplication by y.
var IdempotentAnnihilatesLinear = idempotentAnnihilatesLinearThm{family.Add(registry.ProofEntry{
	Name: "IdempotentAnnihilatesLinear",
	Key:  "prop_2bca683c691a6d8f",
	Deps: []registry.EntryLike{
		LinearFactorQuotient,
		CofactorAtRootUnit,
		polynomial_quotient.PolynomialPrincipalIdealDivides,
		quotient_ring.IdealQuotientProjection,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "trace_idempotent(L, K, y) ∈ «ftQuotient».carrier ∧ " +
			"«ftQuotient».mul(ideal_quotient_projection(mk_ring(vec_add, " +
			"            vec_zero, " +
			"            vec_neg, " +
			"            polynomial_mul, " +
			"            basis_vector(0), " +
			"            vec_sub, " +
			"            {h:num → A | polynomial_over(L.carrier, h)}), " +
			"        ideal_span(mk_ring(vec_add, " +
			"                vec_zero, " +
			"                vec_neg, " +
			"                polynomial_mul, " +
			"                basis_vector(0), " +
			"                vec_sub, " +
			"                {h:num → A | polynomial_over(L.carrier, h)}), " +
			"            {minimal_polynomial(L, K, y)}), " +
			"        basis_vector(1)), " +
			"    trace_idempotent(L, K, y)) = " +
			"«ftQuotient».mul(ideal_quotient_projection(mk_ring(vec_add, " +
			"            vec_zero, " +
			"            vec_neg, " +
			"            polynomial_mul, " +
			"            basis_vector(0), " +
			"            vec_sub, " +
			"            {h:num → A | polynomial_over(L.carrier, h)}), " +
			"        ideal_span(mk_ring(vec_add, " +
			"                vec_zero, " +
			"                vec_neg, " +
			"                polynomial_mul, " +
			"                basis_vector(0), " +
			"                vec_sub, " +
			"                {h:num → A | polynomial_over(L.carrier, h)}), " +
			"            {minimal_polynomial(L, K, y)}), " +
			"        vec_scalar_mul(y, basis_vector(0))), " +
			"    trace_idempotent(L, K, y))",
	},
		"Project (T−y)q=μ into the quotient and multiply by the constant class of μ′(y) inverse."),
})}

// IdempotentIsIdempotent — The scaled cofactor class is an idempotent.
var IdempotentIsIdempotent = idempotentIsIdempotentThm{family.Add(registry.ProofEntry{
	Name: "IdempotentIsIdempotent",
	Key:  "prop_2ff03ff500492b8b",
	Deps: []registry.EntryLike{IdempotentAnnihilatesLinear, CofactorAtRoot, CofactorAtRootUnit},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "«ftQuotient».mul(trace_idempotent(L, K, y), trace_idempotent(L, K, y)) = " +
			"trace_idempotent(L, K, y)",
	},
		"T·e=y·e implies q(T)e=q(y)e; CofactorAtRoot and μ′(y)≠0 then give e²=e."),
})}

// IdempotentImageIsLine — The idempotent is nonzero and its multiplication image is a line.
var IdempotentImageIsLine = idempotentImageIsLineThm{family.Add(registry.ProofEntry{
	Name: "IdempotentImageIsLine",
	Key:  "prop_30030c21f80d1218",
	Deps: []registry.EntryLike{
		PolynomialQuotientPowerBasis,
		polynomial_quotient.PolynomialPrincipalIdealDivides,
		IdempotentAnnihilatesLinear,
		CofactorAtRootUnit,
		module_dimension.DimBasis,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "trace_idempotent(L, K, y) ≠ «ftQuotient».zero ∧ " +
			"image(λv:set(num → A). " +
			"        COND(v ∈ «ftQuotient».carrier, " +
			"            «ftQuotient».mul(trace_idempotent(L, K, y), v), " +
			"            «ftQuotient».zero), " +
			"    «ftQuotient».carrier) = " +
			"{«ftQuotientModule».smul(a, trace_idempotent(L, K, y)) | a:A | a ∈ L.carrier} ∧ " +
			"module_dim(field_ring(L), " +
			"    restrict_module(«ftQuotientModule», " +
			"        image(λv:set(num → A). " +
			"                COND(v ∈ «ftQuotient».carrier, " +
			"                    «ftQuotient».mul(trace_idempotent(L, K, y), v), " +
			"                    «ftQuotient».zero), " +
			"            «ftQuotient».carrier))) = " +
			"1",
	},
		"The class q/μ′ has degree n−1<n and is nonzero by the principal ideal criterion. Every quotient "+
			"class is a polynomial in T, and T·e=y·e reduces its product with e to a scalar multiple of e."),
})}

// IdempotentTraceOne — Multiplication by the trace idempotent has trace one.
var IdempotentTraceOne = idempotentTraceOneThm{family.Add(registry.ProofEntry{
	Name: "IdempotentTraceOne",
	Key:  "prop_e697bd67575c34f4",
	Deps: []registry.EntryLike{
		IdempotentIsIdempotent,
		IdempotentImageIsLine,
		PolynomialQuotientPowerBasis,
		module_dimension.IdempotentTraceIsRank,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "module_trace(field_ring(L), " +
			"    «ftQuotientModule», " +
			"    λv:set(num → A). " +
			"        COND(v ∈ «ftQuotient».carrier, " +
			"            «ftQuotient».mul(trace_idempotent(L, K, y), v), " +
			"            «ftQuotient».zero)) = " +
			"L.one",
	},
		"Multiplication by e is an idempotent linear map with "+
			"one-dimensional image; apply IdempotentTraceIsRank."),
})}

// QuotientPowerTraceAgrees — Variable powers in the polynomial quotient and generator powers in the field have the same trace.
var QuotientPowerTraceAgrees = quotientPowerTraceAgreesThm{family.Add(registry.ProofEntry{
	Name: "QuotientPowerTraceAgrees",
	Key:  "prop_647bb8235080398e",
	Deps: []registry.EntryLike{
		polynomial_quotient.PolynomialQuotientRemainder,
		PolynomialQuotientPowerBasis,
		algebraic_element.AdjoinPowerBasis,
		module_dimension.TraceFromBasis,
		FieldTraceFromBasis,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A. ∀m:num.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
		},
		Conclusion: "module_trace(field_ring(L), " +
			"    «ftQuotientModule», " +
			"    λv:set(num → A). " +
			"        COND(v ∈ «ftQuotient».carrier, " +
			"            «ftQuotient».mul(ideal_quotient_projection(mk_ring(vec_add, " +
			"                        vec_zero, " +
			"                        vec_neg, " +
			"                        polynomial_mul, " +
			"                        basis_vector(0), " +
			"                        vec_sub, " +
			"                        {h:num → A | polynomial_over(L.carrier, h)}), " +
			"                    ideal_span(mk_ring(vec_add, " +
			"                            vec_zero, " +
			"                            vec_neg, " +
			"                            polynomial_mul, " +
			"                            basis_vector(0), " +
			"                            vec_sub, " +
			"                            {h:num → A | polynomial_over(L.carrier, h)}), " +
			"                        {minimal_polynomial(L, K, y)}), " +
			"                    basis_vector(m)), " +
			"                v), " +
			"            «ftQuotient».zero)) = " +
			"field_trace(L, K, monoid_pow(L.mul, L.one, y, m))",
	},
		"For every i<n, divide T^(m+i) by μ over K. The same short remainder "+
			"represents its quotient class over L and its value y^(m+i). Uniqueness of "+
			"coordinates makes the diagonal coefficients, hence the finite traces, equal."),
})}

// TraceIdentityPower — The cofactor-weighted trace identity holds on every power of the primitive element.
var TraceIdentityPower = traceIdentityPowerThm{family.Add(registry.ProofEntry{
	Name: "TraceIdentityPower",
	Key:  "prop_d5bd3bb2d1a3fc34",
	Deps: []registry.EntryLike{
		IdempotentTraceOne,
		IdempotentAnnihilatesLinear,
		QuotientPowerTraceAgrees,
		module_dimension.TraceAdd,
		module_dimension.TraceScale,
		CofactorAtRootUnit,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A. ∀m:num.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "module_sum(L.add, " +
			"    L.zero, " +
			"    {j:num | j < polynomial_degree(minimal_polynomial(L, K, y))}, " +
			"    λj:num. " +
			"        trace_cofactor(L, K, y, j) * " +
			"        field_trace(L, K, monoid_pow(L.mul, L.one, y, m) * monoid_pow(L.mul, L.one, y, j))) = " +
			"monoid_pow(L.mul, L.one, y, m) * «ftDerivative»",
	},
		"Compute the trace of multiplication by T^m e in two ways: T^m e=y^m e gives y^m; expanding "+
			"e as q(T)/μ′ and using QuotientPowerTraceAgrees gives the displayed sum divided by μ′."),
})}

// TraceIdentity — The cofactor-weighted trace identity reconstructs every field element.
var TraceIdentity = traceIdentityThm{family.Add(registry.ProofEntry{
	Name: "TraceIdentity",
	Key:  "prop_443c212167612b52",
	Deps: []registry.EntryLike{
		TraceIdentityPower,
		algebraic_element.AdjoinPowerBasis,
		FieldTraceLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y z:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
			"z ∈ L.carrier",
		},
		Conclusion: "module_sum(L.add, " +
			"    L.zero, " +
			"    {j:num | j < polynomial_degree(minimal_polynomial(L, K, y))}, " +
			"    λj:num. " +
			"        trace_cofactor(L, K, y, j) * field_trace(L, K, z * monoid_pow(L.mul, L.one, y, j))) = " +
			"z * «ftDerivative»",
	},
		"Expand z in the power basis of L over K and combine TraceIdentityPower by FieldTraceLinear."),
})}

// TraceNondegenerate — Vanishing trace pairings against the power basis force a field element to vanish.
var TraceNondegenerate = traceNondegenerateThm{family.Add(registry.ProofEntry{
	Name: "TraceNondegenerate",
	Key:  "prop_16bf05ab72aedfb",
	Deps: []registry.EntryLike{TraceIdentity, CofactorAtRootUnit},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y z:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
			"z ∈ L.carrier",
			"∀j:num. " +
				"    j < polynomial_degree(minimal_polynomial(L, K, y)) ⇒ " +
				"    field_trace(L, K, z * monoid_pow(L.mul, L.one, y, j)) = L.zero",
		},
		Conclusion: "z = L.zero",
	},
		"TraceIdentity makes z μ′(y)=0, and CofactorAtRootUnit permits cancellation."),
})}

// TraceDualBasis — The scaled cofactor coefficients are trace-dual to the power basis.
var TraceDualBasis = traceDualBasisThm{family.Add(registry.ProofEntry{
	Name: "TraceDualBasis",
	Key:  "prop_cf15c77d1210583b",
	Deps: []registry.EntryLike{
		TraceIdentity,
		CofactorCoefficientsBasis,
		module_dimension.BasisCoordinatesUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A. ∀i j:num.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
			"i < polynomial_degree(minimal_polynomial(L, K, y))",
			"j < polynomial_degree(minimal_polynomial(L, K, y))",
		},
		Conclusion: "field_trace(L, " +
			"    K, " +
			"    monoid_pow(L.mul, L.one, y, i) * (trace_cofactor(L, K, y, j) * L.inv(«ftDerivative»))) = " +
			"COND(i = j, L.one, L.zero)",
	},
		"The scaled cofactor coefficients form a K-basis by "+
			"CofactorCoefficientsBasis at S=K. Apply TraceIdentity to each member of "+
			"this basis; uniqueness of its coefficients gives Tr(y^i q_j/μ′)=δ_ij."),
})}

// TraceDualityIso — Trace pairing identifies the extension with its base-field linear dual.
var TraceDualityIso = traceDualityIsoThm{family.Add(registry.ProofEntry{
	Name: "TraceDualityIso",
	Key:  "prop_66b3e40f32801d72",
	Reading: "The nested guards are part of the map. A member of hom_set is zero outside its " +
		"source carrier; unguarded multiplication followed by trace would not be a functional in this " +
		"encoding. The isomorphism is the duality of a nondegenerate pairing on a finite-dimensional " +
		"space, at the trace pairing; no dual basis is computed, and TraceDualBasis is not read.",
	Deps: []registry.EntryLike{
		TraceNondegenerate,
		FieldTraceLinear,
		linear_pairing.NondegeneratePairingDualityIso,
		linear_pairing.BilinearPairingDef,
		linear_pairing.PairingNondegenerateDef,
		algebraic_element.AdjoinPowerBasis,
		module_dimension.FiniteDimensionalDef,
		field.SubfieldFieldOn,
		field_extension.ExtensionModuleOn,
		hom_module.HomSetModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, y))",
		},
		Conclusion: "module_isomorphism(restrict_ring(field_ring(L), K), " +
			"    regular_module(field_ring(L)), " +
			"    hom_module(restrict_ring(field_ring(L), K), " +
			"        regular_module(field_ring(L)), " +
			"        restrict_module(regular_module(field_ring(L)), K)), " +
			"    λz:A. " +
			"        COND(z ∈ L.carrier, " +
			"            λx:A. COND(x ∈ L.carrier, field_trace(L, K, z * x), L.zero), " +
			"            λx:A. L.zero))",
	},
		"The trace pairing (z, x) ↦ Tr(zx) on L over K is bilinear (FieldTraceLinear, "+
			"BilinearPairingDef) and nondegenerate in the sense of PairingNondegenerateDef: a nonzero z "+
			"has Tr(z · yʲ) ≠ zero for some power of the generator, the contrapositive of "+
			"TraceNondegenerate; L = K(y) is finite-dimensional over K by its power basis "+
			"(AdjoinPowerBasis, FiniteDimensionalDef); K is a field on its set (SubfieldFieldOn) and L "+
			"a K-module (ExtensionModuleOn), as the general statement asks. "+
			"NondegeneratePairingDualityIso gives the isomorphism; its map agrees with the displayed "+
			"one on L, where module_isomorphism reads it, and the outer guard supplies the values off L."),
})}

// CofactorCoefficientsBasis — Cofactor coefficients form a subring basis of the monogenic algebra.
var CofactorCoefficientsBasis = cofactorCoefficientsBasisThm{family.Add(registry.ProofEntry{
	Name: "CofactorCoefficientsBasis",
	Key:  "prop_1a0f96c54f5780d4",
	Deps: []registry.EntryLike{
		CofactorCoefficients,
		integral_element.MonicSubringPowerBasis,
		linear_independence.IndependentUniqueCoefficients,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"polynomial_over(S, minimal_polynomial(L, K, y))",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, y)), " +
			"    {trace_cofactor(L, K, y, j) | " +
			"        j:num | " +
			"        j < polynomial_degree(minimal_polynomial(L, K, y))}) ∧ " +
			"has_size( " +
			"    {trace_cofactor(L, K, y, j) | j:num | j < polynomial_degree(minimal_polynomial(L, K, y))}, " +
			"    polynomial_degree(minimal_polynomial(L, K, y)))",
	},
		"The recurrence makes q_j=y^(n−1−j)+c_(n−1)y^(n−2−j)+⋯+c_(j+1). This reversed unitriangular "+
			"change from the power basis is invertible over S, without dividing any coefficient."),
})}
