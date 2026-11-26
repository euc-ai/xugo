package multivariate_rational_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_ordering"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	_ "github.com/euc-ai/xugo/library/proofs/real/rational"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// RationalFunctionFieldDef — The fraction field record of the polynomial algebra in n variables.
var RationalFunctionFieldDef = rationalFunctionFieldDefThm{family.Define(registry.DefEntry{
	Name:  "RationalFunctionFieldDef",
	Const: "multivariate_rational_field",
	Type:  "field_ops(A) → num → field_ops(set(prod((num → num) → A, (num → num) → A)))",
	Key:   "prop_e94e1db6940130b9",
	Equations: []string{
		"∀F:field_ops(A). ∀n:num. " +
			"    multivariate_rational_field(F, n) = " +
			"    fraction_field_record(polynomial_algebra_ring(field_ring(F), {i:num | i < n}))",
	},
})}

// PolynomialFractionDef — A polynomial as its fraction with denominator one.
var PolynomialFractionDef = polynomialFractionDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialFractionDef",
	Const: "polynomial_fraction",
	Type:  "field_ops(A) → num → (((num → num) → A)) → set(prod((num → num) → A, (num → num) → A))",
	Key:   "prop_ef5ba63fb28071f7",
	Equations: []string{
		"∀F:field_ops(A). ∀n:num. ∀p:((num → num) → A). " +
			"    polynomial_fraction(F, n, p) = " +
			"    fraction_class(polynomial_algebra_ring(field_ring(F), {i:num | i < n}).mul, " +
			"        polynomial_algebra_ring(field_ring(F), {i:num | i < n}).carrier, " +
			"        polynomial_algebra_ring(field_ring(F), {i:num | i < n}).carrier ∖ " +
			"        {polynomial_algebra_ring(field_ring(F), {i:num | i < n}).zero}, " +
			"        p, " +
			"        polynomial_algebra_ring(field_ring(F), {i:num | i < n}).one)",
	},
})}

// rationalConstantDef — A base coefficient as a constant rational function.
var rationalConstantDef = rationalConstantDefThm{family.Define(registry.DefEntry{
	Name:  "rationalConstantDef",
	Const: "rational_function_constant",
	Type:  "field_ops(A) → num → A → set(prod((num → num) → A, (num → num) → A))",
	Key:   "prop_1172b7b9fe6a97b1",
	Equations: []string{
		"∀F:field_ops(A). ∀n:num. ∀a:A. " +
			"    rational_function_constant(F, n, a) = " +
			"    polynomial_fraction(F, n, polynomial_algebra_const(field_ring(F), a))",
	},
	Deps: []registry.EntryLike{PolynomialFractionDef},
})}

// genericPointDef — The variable fractions below n, zero above n.
var genericPointDef = genericPointDefThm{family.Define(registry.DefEntry{
	Name:  "genericPointDef",
	Const: "rational_generic_point",
	Type:  "field_ops(A) → num → num → set(prod((num → num) → A, (num → num) → A))",
	Key:   "prop_29124465329e211b",
	Equations: []string{
		"∀F:field_ops(A). ∀n j:num. " +
			"    rational_generic_point(F, n, j) = " +
			"    COND(j < n, " +
			"        polynomial_fraction(F, n, polynomial_algebra_var(field_ring(F), j)), " +
			"        multivariate_rational_field(F, n).zero)",
	},
	Deps: []registry.EntryLike{PolynomialFractionDef, RationalFunctionFieldDef},
})}

// RationalSOSDef — A nonzero common denominator turns f into a finite sum of polynomial squares.
var RationalSOSDef = rationalSOSDefThm{family.Define(registry.DefEntry{
	Name:  "RationalSOSDef",
	Const: "polynomial_rational_sos",
	Type:  "field_ops(A) → num → (((num → num) → A)) → bool",
	Key:   "prop_876a014c1400c0e1",
	Equations: []string{
		"∀F:field_ops(A). ∀n:num. ∀f:((num → num) → A). " +
			"    polynomial_rational_sos(F, n, f) ⇔ " +
			"    ∃h:((num → num) → A). ∃k:num. ∃g:(num → ((num → num) → A)). " +
			"        h ∈ polynomial_algebra_ring(field_ring(F), {i:num | i < n}).carrier ∧ " +
			"        h ≠ polynomial_algebra_ring(field_ring(F), {i:num | i < n}).zero ∧ " +
			"        (∀j:num. " +
			"            j < k ⇒ g(j) ∈ polynomial_algebra_ring(field_ring(F), {i:num | i < n}).carrier) ∧ " +
			"        polynomial_algebra_ring(field_ring(F), {i:num | i < n}).mul( " +
			"            polynomial_algebra_ring(field_ring(F), {i:num | i < n}).mul(h, h), f) = " +
			"        module_sum(polynomial_algebra_ring(field_ring(F), {i:num | i < n}).add, " +
			"            polynomial_algebra_ring(field_ring(F), {i:num | i < n}).zero, " +
			"            {j:num | j < k}, " +
			"            λj:num. polynomial_algebra_ring(field_ring(F), {i:num | i < n}).mul(g(j), g(j)))",
	},
})}

// RationalField — The multivariate fraction-field record is a field with an injective coefficient embedding.
var RationalField = rationalFieldThm{family.Add(registry.ProofEntry{
	Name: "RationalField",
	Key:  "prop_c7ea86a449b79d66",
	Deps: []registry.EntryLike{
		integral_domain.FieldIntegralDomain,
		polynomial_algebra.PolynomialAlgebraDomain,
		ring_localization.FractionField,
		ring_localization.NonzeroMultiplicative,
		polynomial_algebra.PolynomialAlgebraConstHom,
		ring_localization.ToFractionHomomorphism,
		ring_localization.ToFractionInjective,
		ring_homomorphism.RingHomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀n:num.",
		Hypotheses: []string{
			"field_on(F)",
		},
		Conclusion: "field_on(multivariate_rational_field(F, n)) ∧ " +
			"ring_homomorphism(field_ring(F), " +
			"    field_ring(multivariate_rational_field(F, n)), " +
			"    rational_function_constant(F, n)) ∧ " +
			"injective_on(F.carrier, rational_function_constant(F, n))",
	},
		"Real closed field transfer design, rational function field. A field is an integral domain "+
			"(FieldIntegralDomain), so is a polynomial algebra over it (PolynomialAlgebraDomain), and its "+
			"fraction-field record is a field (FractionField). rational_function_constant is the constant "+
			"polynomial (PolynomialAlgebraConstHom) followed by to_fraction over the nonzero elements, a "+
			"multiplicative set by NonzeroMultiplicative (ToFractionHomomorphism, ToFractionInjective, "+
			"RingHomCompose); the constant polynomial is injective, read at the zero monomial."),
})}

// NonzeroPolynomialValue — A nonzero multivariate polynomial over an ordered field is nonzero at some finite tuple.
var NonzeroPolynomialValue = nonzeroPolynomialValueThm{family.Add(registry.ProofEntry{
	Name: "NonzeroPolynomialValue",
	Key:  "prop_14ee071f321e9792",
	Deps: []registry.EntryLike{polynomial_roots.RootBound, ordered_field.DenseOrder},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"p ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"p ≠ λm:(num → num). F.zero",
		},
		Conclusion: "∃x:(num → A). " +
			"    ring_tuple(field_ring(F), n, x) ∧ polynomial_value(field_ring(F), p, x) ≠ F.zero",
	},
		"Real closed field transfer design, formal reality. Induct on n, choose "+
			"a point where a nonzero coefficient polynomial does not vanish, then "+
			"avoid the finitely many univariate roots in the infinite ordered field."),
})}

// RationalFormallyReal — The rational function field over an ordered field is formally real.
var RationalFormallyReal = rationalFormallyRealThm{family.Add(registry.ProofEntry{
	Name: "RationalFormallyReal",
	Key:  "prop_2582563db96fe5c7",
	Deps: []registry.EntryLike{
		RationalField,
		NonzeroPolynomialValue,
		field_ordering.OrderedFormallyReal,
	},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
		},
		Conclusion: "formally_real_field(multivariate_rational_field(F, n))",
	},
		"Real closed field transfer design, rational formal reality. If minus one "+
			"were a sum of rational squares, clear denominators and evaluate at a base "+
			"tuple where their product is nonzero, contradicting the ordered base field."),
})}

// GenericPointEvaluation — Evaluation at the generic variable fractions equals polynomial inclusion.
var GenericPointEvaluation = genericPointEvaluationThm{family.Add(registry.ProofEntry{
	Name: "GenericPointEvaluation",
	Key:  "prop_6948ace989aa86a",
	Deps: []registry.EntryLike{
		RationalField,
		polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural,
	},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀n:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"field_on(F)",
			"p ∈ polynomial_algebra(field_ring(F), {j:num | j < n})",
		},
		Conclusion: "ring_tuple(field_ring(multivariate_rational_field(F, n)), " +
			"    n, " +
			"    rational_generic_point(F, n)) ∧ " +
			"polynomial_value(field_ring(multivariate_rational_field(F, n)), " +
			"    λm:(num → num). rational_function_constant(F, n, p(m)), " +
			"    rational_generic_point(F, n)) = " +
			"polynomial_fraction(F, n, p)",
	},
		"Real closed field transfer design, Artin generic point. The evaluation "+
			"homomorphism fixing coefficients and taking variables to their own "+
			"fractions is the polynomial inclusion into the fraction field."),
})}

// ClearDenominators — Rational sums of squares are exactly polynomial square identities after a nonzero common denominator.
var ClearDenominators = clearDenominatorsThm{family.Add(registry.ProofEntry{
	Name: "ClearDenominators",
	Key:  "prop_18886ab47b6d0a4d",
	Deps: []registry.EntryLike{RationalField},
	Reading: "Polynomial membership includes zero coefficients off valid " +
		"monomials. The denominator is nonzero in the polynomial domain. For " +
		"the empty square sum the polynomial is zero and h = 1 is a witness.",
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀n:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"field_on(F)",
			"p ∈ polynomial_algebra(field_ring(F), {j:num | j < n})",
		},
		Conclusion: "polynomial_rational_sos(F, n, p) ⇔ " +
			"polynomial_fraction(F, n, p) ∈ field_sums_squares(multivariate_rational_field(F, n))",
	},
		"Real closed field transfer design, denominators. A finite sum of rational squares has a nonzero "+
			"product denominator; conversely divide the polynomial identity by h². The empty sum covers zero."),
})}
