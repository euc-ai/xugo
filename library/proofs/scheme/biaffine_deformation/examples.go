// examples.go — the two curves the chapter computes, both inside a field
// L over its constants k and both smooth over k. The projective line,
// charts k[t] and k[1/t]: its charts are polynomial rings, so every
// extension of the line by O over k splits on the charts, and its
// derivation pair is O(2), d ↦ d(t), with no H¹; the line is rigid —
// every extension is the trivial one, and over a square-zero thickening
// of k a deformation exists and is unique up to isomorphism. The
// Weierstrass cubic y² = x³ + ax + b with 2 ≠ 0 and 4a³ + 27b² ≠ 0: its
// charts are smooth, being their models in the free algebras, and its
// derivation pair is the structure pair O, a derivation d being d(x)/2y
// times the vector field θ dual to dx/2y, so the extensions are the
// trivial ones glued by a class of H¹(𝒟⁰) ≅ H¹(O), of dimension g = 1, and
// the deformations over a thickening are a torsor under that line.
//
// Every ring is a subset of L under L's operations: the base is k through
// the identity, the overlap A₀[1/t] is the overlap ring, and the field
// itself is the container of the coefficients, O = (A₀, A₁). The
// cohomology of a chart is read in the host set(prod(num, D)), which holds
// L, a thickening's ring and the models of the charts.

package biaffine_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/registry"
)

// LineChartsSmooth — the charts k[t] and k[1/t] of the line are smooth
// over k: no cohomology above degree 0, with every coefficients.
var LineChartsSmooth = lineChartsSmoothThm{family.Add(registry.ProofEntry{
	Name: "LineChartsSmooth",
	Key:  "prop_301b70aec4172a76",
	Reading: "Transcendence is load-bearing: it makes k[t] the polynomial ring in one variable, " +
		"and k[1/t] too, 1/t being transcendental as well. For t algebraic and inseparable over k — " +
		"t^p = c in k with c no p-th power, in characteristic p — k[t] is the field k(t), and " +
		"D¹(k(t)/k, k(t)) is k(t) itself, the derivative of x^p − c being zero. The host holds L " +
		"and so k, both charts and their polynomials; the cohomology of a chart is read there.",
	Deps: []registry.EntryLike{
		cotangent_examples.PolynomialCohomologyVanishes,
		cotangent_complex.CotangentIsomorphismInvariance,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		free_complex_duality.FreeDualQuasiIsomorphism,
		algebra_deformation.CohomologyCoefficientRestriction,
		simplicial_ring.PowerSetUniverse,
		simplicial_ring.FreeAlgebraCotangentUniverse,
		cardinal.CardLeSubset,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.PolynomialOneVariableInjective,
		free_algebra.PolynomialOneVariableOnto,
		algebraic_element.EvalInjectiveTranscendental,
		algebraic_element.TranscendentalInverse,
		ring_homomorphism.RingIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"card_le(L.carrier, 𝕌⟨A:set(prod(num, D))⟩)",
		},
		Conclusion: "(∀N:module_ops(A, E). " +
			"    module_on(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
			"            λc:A. c, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
			"                λc:A. c, " +
			"                N, " +
			"                n).zero}) ∧ " +
			"(∀N:module_ops(A, E). " +
			"    module_on(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))), N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            λc:A. c, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))), " +
			"                λc:A. c, " +
			"                N, " +
			"                n).zero})",
	},
		"evaluation at t, the constants kept, is a ring map from the free algebra over k on one name ξ "+
			"of the host onto k[t] (FreeAlgebraEvalHom, FreeAlgebraEvalVar, FreeAlgebraEvalConst, "+
			"PolynomialOneVariableOnto), one-to-one as t is transcendental (EvalInjectiveTranscendental "+
			"through PolynomialOneVariableInjective): an isomorphism fixing k (RingIsomorphismDef); 1/t is "+
			"transcendental too (TranscendentalInverse), so the same at k[1/t]. The free algebra has room "+
			"in the host (FreeAlgebraCotangentUniverse), and so have k and the chart, subsets of L "+
			"(PowerSetUniverse, CardLeSubset). PolynomialCohomologyVanishes gives the free algebra no "+
			"cohomology above degree 0 with coefficients N read over it through the isomorphism, the same "+
			"classes as with N over the chart (CohomologyCoefficientRestriction); "+
			"CotangentIsomorphismInvariance with coefficients in the chart makes the two cotangent "+
			"complexes chain-isomorphic, both based (CotangentScalarBased), so their duals with "+
			"coefficients in N have isomorphic cohomology (FreeDualQuasiIsomorphism, CotangentDualAgreement)"),
})}

// LineChartsFinitelyGenerated — k[t] is generated as a ring over k by t,
// and k[1/t] by 1/t: finitely many members each, as DerivationPairIsLattice
// asks.
var LineChartsFinitelyGenerated = lineChartsFinitelyGeneratedThm{family.Add(registry.ProofEntry{
	Name: "LineChartsFinitelyGenerated",
	Key:  "prop_1f67081874af6c29",
	Reading: "Spelled as DerivationPairIsLattice reads finite generation at the " +
		"base k through the identity, image(λc:A. c, k) being k. No transcendence and " +
		"no t ≠ 0: a ring holding k and t holds the value at t of every polynomial " +
		"over k; at t = zero chart 1 is k itself, generated by inv(zero) = zero.",
	Deps: []registry.EntryLike{
		algebraic_element.PolynomialImageDef,
		algebraic_element.PolynomialImageRing,
		polynomial_evaluation.PolynomialEvalDef,
		polynomial_evaluation.EvalBasisVector,
		field.InvIn,
		algebraic_element.PolynomialImageLeast,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "(∃K:set(A). " +
			"    finite(K) ∧ " +
			"    K ⊆ polynomial_image(field_ring(L), k, t) ∧ " +
			"    (∀Q:set(A). " +
			"        comm_ring_on(restrict_ring(field_ring(L), Q)) ∧ image(λc:A. c, k) ⊆ Q ∧ K ⊆ Q ⇒ " +
			"        polynomial_image(field_ring(L), k, t) ⊆ Q)) ∧ " +
			"(∃K:set(A). " +
			"    finite(K) ∧ " +
			"    K ⊆ polynomial_image(field_ring(L), k, L.inv(t)) ∧ " +
			"    (∀Q:set(A). " +
			"        comm_ring_on(restrict_ring(field_ring(L), Q)) ∧ image(λc:A. c, k) ⊆ Q ∧ K ⊆ Q ⇒ " +
			"        polynomial_image(field_ring(L), k, L.inv(t)) ⊆ Q))",
	},
		"K = {t} and K = {inv(t)}, finite and inside the charts (PolynomialImageRing, InvIn); "+
			"a member of k[t] is the value at t of a polynomial over k (PolynomialImageDef), a "+
			"finite sum of members of k times powers of t (PolynomialEvalDef, EvalBasisVector), "+
			"so it lies in every ring Q holding k and t; the same at inv(t)"),
})}

// LineDerivationPair — the derivation pair of the line with coefficients O
// is O(2): a derivation d of k[t, 1/t] over k has d(1/t) = −t⁻²·d(t), and
// d ↦ d(t) is an isomorphism of lattice pairs from 𝒟⁰ onto O(2).
var LineDerivationPair = lineDerivationPairThm{family.Add(registry.ProofEntry{
	Name: "LineDerivationPair",
	Key:  "prop_55e453fe020c83a7",
	Reading: "d ↦ d(t) reads the coefficient of d/dt. Chart 0 of 𝒟⁰, the derivations carrying " +
		"k[t] into k[t], goes onto k[t]·d/dt; chart 1, those carrying k[1/t] into itself, onto the d " +
		"with −t⁻²·d(t) in k[1/t], that is t²·k[1/t]: d/d(1/t) = −t²·d/dt. So the tangent pair of the " +
		"line is O(2), with H¹ zero (LineH1Dim) and H⁰ of dimension 3. Transcendence is load-bearing: " +
		"it makes k[t] a polynomial ring, so a derivation over k may take any value at t and is fixed " +
		"by it. Any characteristic. The COND makes the map zero off the derivations, as a map of " +
		"lattice pairs is off the ambient, which here is every derivation (DerivationPairIsLattice).",
	Deps: []registry.EntryLike{
		DerivationPairIsLattice,
		ChartDerivationsExtend,
		LineChartsFinitelyGenerated,
		biaffineOverlapDerivationsDef,
		biaffineDerivationPairDef,
		partial_derivative.DerivationOn,
		partial_derivative.DerivationExtendsUniquely,
		partial_derivative.FreeAlgebraDerivationFromValues,
		algebraic_element.EvalInjectiveTranscendental,
		projective_line.ProjectiveLineBiaffine,
		projective_line.LinePairInvertible,
		projective_line.LinePairZero,
		projective_line.LineGlobalSections,
		laurent_polynomial.LaurentMonomialProduct,
		projective_line.ProjectiveLinePairDef,
		lattice_pair_map.LatticePairIsomorphismDef,
		lattice_pair_map.LatticePairMapsDef,
		lattice_pair.LatticePairAmbientDef,
		hom_module.HomSetDef,
		field.MulRightInverseOn,
		algebraic_element.PolynomialImageLeast,
		algebraic_element.TranscendentalInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "(∀d:(A → A). " +
			"    d ∈ " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), " +
			"            polynomial_image(field_ring(L), k, L.inv(t)))).carrier ⇒ " +
			"    d(L.inv(t)) = L.neg(L.inv(t) * L.inv(t) * d(t))) ∧ " +
			"lattice_pair(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"    polynomial_image(field_ring(L), k, t), " +
			"    polynomial_image(field_ring(L), k, L.inv(t)), " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), polynomial_image(field_ring(L), k, L.inv(t)))), " +
			"    biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        polynomial_image(field_ring(L), k, t), " +
			"        polynomial_image(field_ring(L), k, L.inv(t)), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), " +
			"            polynomial_image(field_ring(L), k, L.inv(t))))) ∧ " +
			"lattice_pair_isomorphism(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), polynomial_image(field_ring(L), k, L.inv(t)))), " +
			"    biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        polynomial_image(field_ring(L), k, t), " +
			"        polynomial_image(field_ring(L), k, L.inv(t)), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), polynomial_image(field_ring(L), k, L.inv(t)))), " +
			"    regular_module(field_ring(L)), " +
			"    projective_line_pair(L, k, t, int_of_num(2)), " +
			"    λd:(A → A). " +
			"        COND(d ∈ " +
			"            biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"                regular_module(field_ring(L)), " +
			"                (polynomial_image(field_ring(L), k, t), " +
			"                    polynomial_image(field_ring(L), k, L.inv(t)))).carrier, " +
			"            d(t), " +
			"            L.zero))",
	},
		"the datum is biaffine and O = O(0) a lattice pair, k inside both charts "+
			"(ProjectiveLineBiaffine, LinePairInvertible, LinePairZero, LineGlobalSections); both charts are "+
			"finitely generated (LineChartsFinitelyGenerated), so DerivationPairIsLattice gives the lattice "+
			"pair and its ambient, every derivation. A derivation kills one ∈ k (DerivationOn), so the "+
			"Leibniz rule at t · inv(t) = one gives d(inv(t)) = −inv(t)²·d(t) (MulRightInverseOn). A "+
			"derivation of k[t] over k is fixed by its value at t and takes any value in k[t, 1/t] there "+
			"(FreeAlgebraDerivationFromValues through the polynomial ring, EvalInjectiveTranscendental), and "+
			"extends uniquely to the overlap (DerivationExtendsUniquely, ChartDerivationsExtend): so d ↦ "+
			"d(t) is linear over the overlap, one-to-one and onto k[t, 1/t] (HomSetDef, LatticePairMapsDef). "+
			"d carries k[t] into itself exactly when d(t) ∈ k[t], as d(p(t)) = p'(t)·d(t), and k[1/t] into "+
			"itself exactly when −inv(t)²·d(t) ∈ k[1/t], that is d(t) ∈ t²·k[1/t] (LaurentMonomialProduct): "+
			"the charts of O(2) (ProjectiveLinePairDef, LatticePairIsomorphismDef)"),
})}

// ProjectiveLineRigid — the projective line is rigid: every extension of
// the line by O over k is isomorphic to the split extensions glued
// trivially, and over a square-zero thickening of k the line has a
// deformation, any two being isomorphic.
var ProjectiveLineRigid = projectiveLineRigidThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveLineRigid",
	Key:  "prop_6c22aadc696f516b",
	Reading: "Two vanishings make the line rigid: the charts are smooth, so every extension " +
		"splits on both charts, and H¹(𝒟⁰) = H¹(O(2)) = 0, so every gluing of the split " +
		"extensions is the trivial one up to isomorphism. Over a thickening both obstructions " +
		"vanish and the deformations are an H¹(𝒟⁰)-torsor, a single point. Transcendence is " +
		"load-bearing through both: k[t] is a polynomial ring. The thickening is any ring R onto " +
		"k whose kernel J has square zero, with ι a k-linear map from J into k = H⁰(O); the host " +
		"holds L and R, the room the cohomology of the charts is read in, and the deformation " +
		"asserted lives on the realizations' type there. The first half needs no host: the " +
		"extensions are over k. H¹(O(2)) vanishes because k[t] + t²·k[1/t] is all of k[t, 1/t].",
	Deps: []registry.EntryLike{
		LocallyTrivialIsH1D0,
		GluedTrivialIsoIffCoboundary,
		GluedTrivialIsExtension,
		SmoothChartsUnobstructed,
		BiaffineIsomorphismDef,
		LineChartsSmooth,
		LineDerivationPair,
		projective_line.LineH1Dim,
		projective_line.ProjectiveLineBiaffine,
		projective_line.LinePairInvertible,
		projective_line.LinePairZero,
		projective_line.LineGlobalSections,
		lattice_pair_map.IsomorphismInverse,
		lattice_pair_map.IsomorphismSameEuler,
		lattice_pair.LatticePairH1Def,
		module_dimension.DimZero,
		square_zero_extension.SquareZeroIsomorphismDef,
		module_homomorphism.HomCompose,
		simplicial_ring.PowerSetUniverse,
		cardinal.CardLeSubset,
		projective_line.LineEuler,
		algebraic_element.TranscendentalInverse,
		cardinal.LeftFactorIntoPowerSet,
		cardinal.CardLeTrans,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "(∀E₀:square_zero_ops(A, A, I, A). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, A, H, A). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    biaffine_extension(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        polynomial_image(field_ring(L), k, t), " +
			"        polynomial_image(field_ring(L), k, L.inv(t)), " +
			"        t, " +
			"        L.inv(t), " +
			"        regular_module(field_ring(L)), " +
			"        (polynomial_image(field_ring(L), k, t), polynomial_image(field_ring(L), k, L.inv(t))), " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        φ) ⇒ " +
			"    ∃ψ₀:(prod(A, A) → I). ∃ψ₁:(prod(A, A) → H). " +
			"        biaffine_isomorphism(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"            regular_module(field_ring(L)), " +
			"            (polynomial_image(field_ring(L), k, t), " +
			"                polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                polynomial_image(field_ring(L), k, t), " +
			"                                t)), " +
			"                        polynomial_image(field_ring(L), k, t)), " +
			"                    λw:A. w, " +
			"                    restrict_module(regular_module(field_ring(L)), " +
			"                        polynomial_image(field_ring(L), k, t))), " +
			"                λr:A. (r, L.zero), " +
			"                λm:A. (L.zero, m), " +
			"                λz:prod(A, A). fst(z)), " +
			"            (t, L.zero), " +
			"            mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                polynomial_image(field_ring(L), k, t), " +
			"                                t)), " +
			"                        polynomial_image(field_ring(L), k, L.inv(t))), " +
			"                    λw:A. w, " +
			"                    restrict_module(regular_module(field_ring(L)), " +
			"                        polynomial_image(field_ring(L), k, L.inv(t)))), " +
			"                λr:A. (r, L.zero), " +
			"                λm:A. (L.zero, m), " +
			"                λz:prod(A, A). fst(z)), " +
			"            (L.inv(t), L.zero), " +
			"            biaffine_shear_gluing(restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"                polynomial_image(field_ring(L), k, L.inv(t)), " +
			"                L.inv(t), " +
			"                regular_module(field_ring(L)), " +
			"                (polynomial_image(field_ring(L), k, t), " +
			"                    polynomial_image(field_ring(L), k, L.inv(t))), " +
			"                λz:A. L.zero), " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ, " +
			"            ψ₀, " +
			"            ψ₁)) ∧ " +
			"(∀R:ring_ops(B). ∀f ι:(B → A). " +
			"    card_le(L.carrier, 𝕌⟨A:set(prod(num, D))⟩) ∧ " +
			"    card_le(R.carrier, 𝕌⟨A:set(prod(num, D))⟩) ∧ " +
			"    ring_homomorphism(R, restrict_ring(field_ring(L), k), f) ∧ " +
			"    image(f, R.carrier) = k ∧ " +
			"    (∀j j':B. " +
			"        j ∈ ring_kernel(L.zero, R.carrier, f) ∧ j' ∈ ring_kernel(L.zero, R.carrier, f) ⇒ " +
			"        R.mul(j, j') = R.zero) ∧ " +
			"    module_homomorphism(restrict_ring(field_ring(L), k), " +
			"        thickening_kernel(R, restrict_ring(field_ring(L), k), f), " +
			"        restrict_module(regular_module(field_ring(L)), k), " +
			"        ι) ⇒ " +
			"    (∃E₀:square_zero_ops(B, A, set(prod(set(prod(num, D)), A)), A). " +
			"    ∃t₀:set(prod(set(prod(num, D)), A)). " +
			"    ∃E₁:square_zero_ops(B, A, set(prod(set(prod(num, D)), A)), A). " +
			"    ∃t₁:set(prod(set(prod(num, D)), A)). " +
			"    ∃φ:(set(prod(set(prod(set(prod(num, D)), A)), set(prod(set(prod(num, D)), A)))) → " +
			"            set(prod(set(prod(set(prod(num, D)), A)), set(prod(set(prod(num, D)), A))))). " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"            polynomial_image(field_ring(L), k, t), " +
			"            polynomial_image(field_ring(L), k, L.inv(t)), " +
			"            t, " +
			"            L.inv(t), " +
			"            regular_module(field_ring(L)), " +
			"            (polynomial_image(field_ring(L), k, t), " +
			"                polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ)) ∧ " +
			"    (∀E₀:square_zero_ops(B, A, I, A). " +
			"    ∀t₀:I. " +
			"    ∀E₁:square_zero_ops(B, A, H, A). " +
			"    ∀t₁:H. " +
			"    ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    ∀E_0':square_zero_ops(B, A, G, A). " +
			"    ∀t_0':G. " +
			"    ∀E_1':square_zero_ops(B, A, F, A). " +
			"    ∀t_1':F. " +
			"    ∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"            polynomial_image(field_ring(L), k, t), " +
			"            polynomial_image(field_ring(L), k, L.inv(t)), " +
			"            t, " +
			"            L.inv(t), " +
			"            regular_module(field_ring(L)), " +
			"            (polynomial_image(field_ring(L), k, t), " +
			"                polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ) ∧ " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"            polynomial_image(field_ring(L), k, t), " +
			"            polynomial_image(field_ring(L), k, L.inv(t)), " +
			"            t, " +
			"            L.inv(t), " +
			"            regular_module(field_ring(L)), " +
			"            (polynomial_image(field_ring(L), k, t), " +
			"                polynomial_image(field_ring(L), k, L.inv(t))), " +
			"            ι, " +
			"            E_0', " +
			"            t_0', " +
			"            E_1', " +
			"            t_1', " +
			"            φ') ⇒ " +
			"        ∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"            biaffine_isomorphism(R, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"                regular_module(field_ring(L)), " +
			"                (polynomial_image(field_ring(L), k, t), " +
			"                    polynomial_image(field_ring(L), k, L.inv(t))), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                φ, " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                ψ₀, " +
			"                ψ₁)))",
	},
		"the datum, O and the base: ProjectiveLineBiaffine, LinePairInvertible at 0 with LinePairZero, "+
			"k = k[t] ∩ k[1/t] (LineGlobalSections). Take the host set(prod(num, prod(A, A))) for the "+
			"extensions over k (PowerSetUniverse; A embeds in it by LeftFactorIntoPowerSet and "+
			"CardLeTrans). The charts have no D¹ with coefficients in themselves (LineChartsSmooth), so "+
			"every extension has chart classes zero and is isomorphic to the split ones glued by the shear "+
			"of some derivation d (LocallyTrivialIsH1D0). H¹(𝒟⁰) is zero: 𝒟⁰ ≅ O(2) (LineDerivationPair, "+
			"inverted by IsomorphismInverse), whose H¹ has dimension max(−3, 0) = 0 (LineH1Dim), so the "+
			"same holds of H¹(𝒟⁰) (IsomorphismSameEuler), a module of dimension zero is its zero alone "+
			"(DimZero), and d lies in fst(𝒟⁰) + snd(𝒟⁰) (LatticePairH1Def). GluedTrivialIsoIffCoboundary "+
			"then gives an isomorphism from the trivial gluing to the gluing by d, the shears by the two "+
			"parts of d; compose the two isomorphisms chartwise (BiaffineIsomorphismDef, "+
			"SquareZeroIsomorphismDef, HomCompose; the maps of localizations compose). Over the "+
			"thickening, SmoothChartsUnobstructed with the charts smooth over k (LineChartsSmooth) gives a "+
			"deformation, and any two related by a regluing by some d; d is a coboundary as above, so the "+
			"regluing is isomorphic to the regluing by zero, which is the deformation itself"),
})}

// ---------------------------------------------------------------------------
// The Weierstrass cubic
// ---------------------------------------------------------------------------

// ChartsSmoothOnImage — where the cubic is smooth, its two charts inside
// the field are smooth over k: no cohomology above degree 0, with every
// coefficients.
var ChartsSmoothOnImage = chartsSmoothOnImageThm{family.Add(registry.ProofEntry{
	Name: "ChartsSmoothOnImage",
	Key:  "prop_a548bb48ef4e6f20",
	Reading: "WeierstrassChartsSmooth read on the charts as subrings of the field, through the " +
		"isomorphisms from the model rings; the hypotheses are its own and load-bearing as there: " +
		"on the cusp a = b = 0, chart 0 has D¹(A₀/k, A₀/(x, y)) = A₀/(x, y), both partials acting " +
		"as zero, and in characteristic 2 the partials are x² + a and zero. The host holds L, so k " +
		"and both charts, and the model rings on names of the host (WeierstrassRingInUniverse).",
	Deps: []registry.EntryLike{
		elliptic_curve.WeierstrassChartsSmooth,
		elliptic_curve.WeierstrassImageIsomorphism,
		elliptic_curve.WeierstrassChartOneEmbeds,
		elliptic_curve.WeierstrassRingInUniverse,
		cotangent_complex.CotangentIsomorphismInvariance,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		free_complex_duality.FreeDualQuasiIsomorphism,
		algebra_deformation.CohomologyCoefficientRestriction,
		simplicial_ring.PowerSetUniverse,
		cardinal.CardLeSubset,
		field.SubfieldFieldOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"card_le(L.carrier, 𝕌⟨A:set(prod(num, D))⟩)",
		},
		Conclusion: "(∀N:module_ops(A, E). " +
			"    module_on(restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                λc:A. c, " +
			"                N, " +
			"                n).zero}) ∧ " +
			"(∀N:module_ops(A, E). " +
			"    module_on(restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"                λc:A. c, " +
			"                N, " +
			"                n).zero})",
	},
		"k is a field with L's operations (SubfieldFieldOn) and has room in the host, as have both "+
			"charts, subsets of L (PowerSetUniverse, CardLeSubset); take two distinct names of the host "+
			"for each model ring, which has room there too (WeierstrassRingInUniverse). "+
			"WeierstrassImageIsomorphism and WeierstrassChartOneEmbeds give ring isomorphisms from the "+
			"model rings onto the charts fixing k. CotangentIsomorphismInvariance with coefficients in the "+
			"chart makes the cotangent complexes of the model and of the chart over k chain-isomorphic, "+
			"both based (CotangentScalarBased), so their duals with coefficients in N have isomorphic "+
			"cohomology (FreeDualQuasiIsomorphism, CotangentDualAgreement); on the model side N is read "+
			"over the model ring through the isomorphism (CohomologyCoefficientRestriction), a module over "+
			"it, where WeierstrassChartsSmooth gives one class in every degree n ≥ 1"),
})}

// WeierstrassChartsFinitelyGenerated — chart 0 is generated as a ring over
// k by x and y, chart 1 by s = 1/x and u = y/x², as DerivationPairIsLattice
// asks.
var WeierstrassChartsFinitelyGenerated = weierstrassChartsFinitelyGeneratedThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartsFinitelyGenerated",
	Key:  "prop_91bd85b4d3d65b21",
	Reading: "Spelled as DerivationPairIsLattice reads finite generation at the base k through the " +
		"identity, image(λc:A. c, k) being k. No characteristic and no discriminant: a member of chart " +
		"0 is p(x) + q(x)·y with p and q polynomials over k, which every ring holding k, x and y holds.",
	Deps: []registry.EntryLike{
		elliptic_curve.WeierstrassDef,
		elliptic_curve.WeierstrassChartZeroDef,
		elliptic_curve.WeierstrassChartOneDef,
		elliptic_curve.WeierstrassBasisZero,
		elliptic_curve.WeierstrassBasisOne,
		algebraic_element.PolynomialImageDef,
		algebraic_element.PolynomialImageRing,
		polynomial_evaluation.PolynomialEvalDef,
		algebraic_element.PolynomialImageLeast,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∃K:set(A). " +
			"    finite(K) ∧ " +
			"    K ⊆ weierstrass_chart_zero(field_ring(L), k, x, y) ∧ " +
			"    (∀Q:set(A). " +
			"        comm_ring_on(restrict_ring(field_ring(L), Q)) ∧ image(λc:A. c, k) ⊆ Q ∧ K ⊆ Q ⇒ " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y) ⊆ Q)) ∧ " +
			"(∃K:set(A). " +
			"    finite(K) ∧ " +
			"    K ⊆ weierstrass_chart_one(L, k, x, y) ∧ " +
			"    (∀Q:set(A). " +
			"        comm_ring_on(restrict_ring(field_ring(L), Q)) ∧ image(λc:A. c, k) ⊆ Q ∧ K ⊆ Q ⇒ " +
			"        weierstrass_chart_one(L, k, x, y) ⊆ Q))",
	},
		"K = {x, y} and K = {inv(x), u}, finite and inside the charts (WeierstrassBasisZero, "+
			"WeierstrassBasisOne, PolynomialImageRing); a member of chart 0 is p(x) + q(x)·y with "+
			"p(x), q(x) values of polynomials over k (WeierstrassChartZeroDef, PolynomialImageDef), "+
			"finite sums of members of k times powers of x (PolynomialEvalDef), so it lies in every "+
			"ring Q holding k, x and y; chart 1 the same in inv(x) and u (WeierstrassChartOneDef)"),
})}

// WeierstrassDerivationPair — where the cubic is smooth, its derivation
// pair with coefficients O is O itself: the vector field θ with θ(x) = 2y
// and θ(y) = 3x² + a is a derivation of both charts, θ(s) = −2u and θ(u) =
// −(1 + 3as² + 4bs³), every derivation d is d(x)/2y times θ, and d ↦
// d(x)/2y is an isomorphism of lattice pairs from 𝒟⁰ onto O.
var WeierstrassDerivationPair = weierstrassDerivationPairThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassDerivationPair",
	Key:  "prop_1890b71680c19300",
	Reading: "θ is dual to the invariant differential dx/2y (WeierstrassKaehlerCharts, " +
		"KaehlerCanonical): the tangent pair of the curve is trivial, T ≅ O, so H¹(𝒟⁰) ≅ H¹(O) has " +
		"dimension g = 1 and H⁰(𝒟⁰) is k·θ. The coefficient of θ is read as d(x)/2y, 2y being a nonzero " +
		"member of the field. 2 ≠ 0 and 4a³ + 27b² ≠ 0 are load-bearing: on the cusp a = b = 0 the Euler " +
		"field, x ↦ 2x and y ↦ 3y, carries chart 0 into itself while its coefficient x/y lies outside " +
		"chart 0; in characteristic 2, y + y = zero. θ(s) and θ(u) are −∂_u and ∂_s of the chart-one " +
		"relation u² − s − as³ − bs⁴, so θ is a derivation of chart 1 as well, the same field on both " +
		"charts. c = d(x)/2y lies in the overlap only through the cofactors of WeierstrassPartialsUnit, " +
		"1/y not being in A₀[1/x]; d = c • θ holds off the overlap because both sides are zero there.",
	Deps: []registry.EntryLike{
		DerivationPairIsLattice,
		ChartDerivationsExtend,
		WeierstrassChartsFinitelyGenerated,
		biaffineOverlapDerivationsDef,
		biaffineDerivationPairDef,
		lattice_pair.LatticePairH0Def,
		lattice_pair_map.LatticePairIsomorphismDef,
		lattice_pair_map.LatticePairMapsDef,
		hom_module.HomSetDef,
		partial_derivative.DerivationOn,
		partial_derivative.DerivationExtendsUniquely,
		partial_derivative.FreeAlgebraDerivationFromValues,
		elliptic_curve.WeierstrassPartialsUnit,
		elliptic_curve.WeierstrassImageIsomorphism,
		elliptic_curve.WeierstrassChartOneEmbeds,
		elliptic_curve.WeierstrassChartOneEquation,
		elliptic_curve.WeierstrassKaehlerCharts,
		elliptic_curve.WeierstrassIsCurve,
		elliptic_curve.WeierstrassGlobalSections,
		algebraic_curve.CurveLatticeData,
		field.MulRightInverseOn,
		field.MulEqZeroOn,
		algebraic_element.PolynomialImageLeast,
		simplicial_ring.ConcreteUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∃θ:(A → A). " +
			"    θ ∈ " +
			"    lattice_pair_h0(biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))), " +
			"        biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)))).carrier ∧ " +
			"    θ(x) = y + y ∧ " +
			"    θ(y) = monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a ∧ " +
			"    θ(L.inv(x)) = L.neg(y * (L.inv(x) * L.inv(x)) + y * (L.inv(x) * L.inv(x))) ∧ " +
			"    θ(y * (L.inv(x) * L.inv(x))) = " +
			"    L.neg(L.one + " +
			"        monoid_pow(L.add, L.zero, L.one, 3) * a * (L.inv(x) * L.inv(x)) + " +
			"        monoid_pow(L.add, L.zero, L.one, 4) * b * (L.inv(x) * (L.inv(x) * L.inv(x)))) ∧ " +
			"    (∀d:(A → A). " +
			"        d ∈ " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).carrier ⇒ " +
			"        d = " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).smul(d(x) * L.inv(y + y), θ))) ∧ " +
			"lattice_pair(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))), " +
			"    biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y)))) ∧ " +
			"lattice_pair_isomorphism(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))), " +
			"    biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))), " +
			"    regular_module(field_ring(L)), " +
			"    (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y)), " +
			"    λd:(A → A). " +
			"        COND(d ∈ " +
			"            biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y))).carrier, " +
			"            d(x) * L.inv(y + y), " +
			"            L.zero))",
	},
		"θ: the values 2y at x and 3x² + a at y give a derivation of chart 0 over k, the relation's "+
			"derivative 2y·(3x² + a) − (3x² + a)·2y vanishing (FreeAlgebraDerivationFromValues through "+
			"WeierstrassImageIsomorphism), extended to the overlap by the quotient rule and zero off it "+
			"(DerivationExtendsUniquely, ChartDerivationsExtend); at s = inv(x) and u the Leibniz rule "+
			"and y² = x³ + ax + b (WeierstrassChartOneEquation, MulRightInverseOn) give −2u and −(1 + "+
			"3as² + 4bs³), members of chart 1, so θ lies in both charts of 𝒟⁰ (LatticePairH0Def). A "+
			"derivation d is fixed on chart 0 by d(x) and d(y), chart 0 being generated by x and y "+
			"(WeierstrassChartsFinitelyGenerated), and on the overlap by its restriction "+
			"(ChartDerivationsExtend); 2y·d(y) = (3x² + a)·d(x) from the relation, and 2y ≠ zero "+
			"(MulEqZeroOn: 2 ≠ 0, and y ≠ zero as x is transcendental), so d = c • θ with c = d(x)/2y. "+
			"c lies in chart 0 exactly when d carries chart 0 into itself: c = β·d(x) − α·d(y) for the "+
			"cofactors α, β of WeierstrassPartialsUnit read in the field (WeierstrassImageIsomorphism); "+
			"likewise c = α₁·d(u) − β₁·d(s) at chart 1 with its cofactors (WeierstrassChartOneEmbeds). "+
			"The datum is a curve and O a lattice pair, k in both charts (WeierstrassIsCurve, "+
			"CurveLatticeData, WeierstrassGlobalSections); DerivationPairIsLattice gives the lattice "+
			"pair and its ambient, every derivation, on which d ↦ c is linear and one-to-one "+
			"(HomSetDef, LatticePairMapsDef, LatticePairIsomorphismDef)"),
})}

// EllipticDeformationsDimOne — where the cubic is smooth, its extensions
// by O over k are, up to isomorphism, the split extensions glued by the
// shear of a derivation d, two isomorphic exactly when the derivations
// differ by fst(𝒟⁰) + snd(𝒟⁰), and H¹(𝒟⁰) has dimension one; over a
// square-zero thickening of k the curve has a deformation, and its
// deformations are an H¹(𝒟⁰)-torsor under regluing.
var EllipticDeformationsDimOne = ellipticDeformationsDimOneThm{family.Add(registry.ProofEntry{
	Name: "EllipticDeformationsDimOne",
	Key:  "prop_58418c8287c3c967",
	Reading: "The classification is d ↦ the split extensions glued by the shear of d, from " +
		"H¹(𝒟⁰) onto the extensions up to isomorphism: onto because every extension splits on " +
		"the smooth charts, one-to-one by the coboundary condition. H¹(𝒟⁰) ≅ H¹(O) through the " +
		"coefficient of θ (WeierstrassDerivationPair), of dimension g = 1 (GenusOne): the " +
		"curve has a line of first-order deformations. Over any thickening R onto k with " +
		"square-zero kernel J and ι a k-linear map from J into k = H⁰(O), both obstructions " +
		"vanish and the deformations move freely and transitively under H¹(𝒟⁰) by regluing. 2 " +
		"≠ 0 and 4a³ + 27b² ≠ 0 are load-bearing: on the cusp the charts are not smooth and 𝒟⁰ " +
		"is not O. The host holds L and R; the deformation asserted lives on the realizations' " +
		"type there. The dimension one needs O finite as a lattice pair (lattice_pair_finite, " +
		"EulerStructureZero) and the genus read at the overlap's ring and the field module.",
	Deps: []registry.EntryLike{
		LocallyTrivialIsH1D0,
		GluedTrivialIsoIffCoboundary,
		GluedTrivialIsExtension,
		SmoothChartsUnobstructed,
		ChartsSmoothOnImage,
		WeierstrassDerivationPair,
		lattice_pair_map.IsomorphismInverse,
		lattice_pair_map.IsomorphismSameEuler,
		lattice_pair.LatticePairH1DimDef,
		elliptic_curve.GenusOne,
		elliptic_curve.EulerStructureZero,
		elliptic_curve.WeierstrassIsCurve,
		elliptic_curve.WeierstrassGlobalSections,
		algebraic_curve.CurveLatticeData,
		algebraic_curve.CurveGenusDef,
		module_record.RestrictRingDef,
		simplicial_ring.PowerSetUniverse,
		cardinal.CardLeSubset,
		cardinal.LeftFactorIntoPowerSet,
		cardinal.CardLeTrans,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∀E₀:square_zero_ops(A, A, I, A). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, A, H, A). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    biaffine_extension(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        x, " +
			"        L.inv(x), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y)), " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        φ) ⇒ " +
			"    ∃d:(A → A). " +
			"        d ∈ " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).carrier ∧ " +
			"        (∃ψ₀:(prod(A, A) → I). ∃ψ₁:(prod(A, A) → H). " +
			"            biaffine_isomorphism(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y)), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (x, L.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_one(L, k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (L.inv(x), L.zero), " +
			"                biaffine_shear_gluing(restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    L.inv(x), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)), " +
			"                    d), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                φ, " +
			"                ψ₀, " +
			"                ψ₁))) ∧ " +
			"(∀d d':(A → A). " +
			"    d ∈ " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y))).carrier ∧ " +
			"    d' ∈ " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y))).carrier ⇒ " +
			"    ((∃ψ₀ ψ₁:(prod(A, A) → prod(A, A)). " +
			"            biaffine_isomorphism(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y)), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (x, L.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_one(L, k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (L.inv(x), L.zero), " +
			"                biaffine_shear_gluing(restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    L.inv(x), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)), " +
			"                    d), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (x, L.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(restrict_ring(field_ring(L), " +
			"                                ring_away(field_ring(L), " +
			"                                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                    x)), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        λw:A. w, " +
			"                        restrict_module(regular_module(field_ring(L)), " +
			"                            weierstrass_chart_one(L, k, x, y))), " +
			"                    λr:A. (r, L.zero), " +
			"                    λm:A. (L.zero, m), " +
			"                    λz:prod(A, A). fst(z)), " +
			"                (L.inv(x), L.zero), " +
			"                biaffine_shear_gluing(restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    L.inv(x), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)), " +
			"                    d'), " +
			"                ψ₀, " +
			"                ψ₁)) ⇔ " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).add(d, " +
			"            biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y))).neg(d')) ∈ " +
			"        set_mul(biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y))).add, " +
			"            fst(biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"                    λc:A. c, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)))), " +
			"            snd(biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"                    λc:A. c, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y))))))) ∧ " +
			"finite_dimensional(restrict_ring(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        k), " +
			"    lattice_pair_h1(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))), " +
			"        biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))))) ∧ " +
			"lattice_pair_h1_dim(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    k, " +
			"    biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))), " +
			"    biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"        λc:A. c, " +
			"        restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        regular_module(field_ring(L)), " +
			"        (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y)))) = " +
			"1 ∧ " +
			"(∀R:ring_ops(B). ∀f ι:(B → A). " +
			"    card_le(L.carrier, 𝕌⟨A:set(prod(num, D))⟩) ∧ " +
			"    card_le(R.carrier, 𝕌⟨A:set(prod(num, D))⟩) ∧ " +
			"    ring_homomorphism(R, restrict_ring(field_ring(L), k), f) ∧ " +
			"    image(f, R.carrier) = k ∧ " +
			"    (∀j j':B. " +
			"        j ∈ ring_kernel(L.zero, R.carrier, f) ∧ j' ∈ ring_kernel(L.zero, R.carrier, f) ⇒ " +
			"        R.mul(j, j') = R.zero) ∧ " +
			"    module_homomorphism(restrict_ring(field_ring(L), k), " +
			"        thickening_kernel(R, restrict_ring(field_ring(L), k), f), " +
			"        restrict_module(regular_module(field_ring(L)), k), " +
			"        ι) ⇒ " +
			"    (∃E₀:square_zero_ops(B, A, set(prod(set(prod(num, D)), A)), A). " +
			"    ∃t₀:set(prod(set(prod(num, D)), A)). " +
			"    ∃E₁:square_zero_ops(B, A, set(prod(set(prod(num, D)), A)), A). " +
			"    ∃t₁:set(prod(set(prod(num, D)), A)). " +
			"    ∃φ:(set(prod(set(prod(set(prod(num, D)), A)), set(prod(set(prod(num, D)), A)))) → " +
			"            set(prod(set(prod(set(prod(num, D)), A)), set(prod(set(prod(num, D)), A))))). " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            x, " +
			"            L.inv(x), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ)) ∧ " +
			"    (∀E₀:square_zero_ops(B, A, I, A). " +
			"    ∀t₀:I. " +
			"    ∀E₁:square_zero_ops(B, A, H, A). " +
			"    ∀t₁:H. " +
			"    ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    ∀E_0':square_zero_ops(B, A, G, A). " +
			"    ∀t_0':G. " +
			"    ∀E_1':square_zero_ops(B, A, F, A). " +
			"    ∀t_1':F. " +
			"    ∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            x, " +
			"            L.inv(x), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ) ∧ " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            x, " +
			"            L.inv(x), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)), " +
			"            ι, " +
			"            E_0', " +
			"            t_0', " +
			"            E_1', " +
			"            t_1', " +
			"            φ') ⇒ " +
			"        ∃d:(A → A). " +
			"            d ∈ " +
			"            biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y))).carrier ∧ " +
			"            (∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"                biaffine_isomorphism(R, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)), " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    biaffine_regluing(restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                x)), " +
			"                        regular_module(field_ring(L)), " +
			"                        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        E₀, " +
			"                        t₀, " +
			"                        φ, " +
			"                        d), " +
			"                    E_0', " +
			"                    t_0', " +
			"                    E_1', " +
			"                    t_1', " +
			"                    φ', " +
			"                    ψ₀, " +
			"                    ψ₁))) ∧ " +
			"    (∀E₀:square_zero_ops(B, A, I, A). " +
			"    ∀t₀:I. " +
			"    ∀E₁:square_zero_ops(B, A, H, A). " +
			"    ∀t₁:H. " +
			"    ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    ∀d d':(A → A). " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            x, " +
			"            L.inv(x), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ) ∧ " +
			"        d ∈ " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).carrier ∧ " +
			"        d' ∈ " +
			"        biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y))).carrier ⇒ " +
			"        biaffine_deformation(R, " +
			"            restrict_ring(field_ring(L), k), " +
			"            f, " +
			"            λc:A. c, " +
			"            restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            x, " +
			"            L.inv(x), " +
			"            regular_module(field_ring(L)), " +
			"            (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y)), " +
			"            ι, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            biaffine_regluing(restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y)), " +
			"                E₀, " +
			"                t₀, " +
			"                φ, " +
			"                d)) ∧ " +
			"        ((∃ψ₀:(I → I). ∃ψ₁:(H → H). " +
			"                biaffine_isomorphism(R, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y)), " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    biaffine_regluing(restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                x)), " +
			"                        regular_module(field_ring(L)), " +
			"                        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        E₀, " +
			"                        t₀, " +
			"                        φ, " +
			"                        d), " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    biaffine_regluing(restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                x)), " +
			"                        regular_module(field_ring(L)), " +
			"                        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            weierstrass_chart_one(L, k, x, y)), " +
			"                        E₀, " +
			"                        t₀, " +
			"                        φ, " +
			"                        d'), " +
			"                    ψ₀, " +
			"                    ψ₁)) ⇔ " +
			"            biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                λc:A. c, " +
			"                restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                regular_module(field_ring(L)), " +
			"                (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y))).add(d, " +
			"                biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                    λc:A. c, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y))).neg(d')) ∈ " +
			"            set_mul(biaffine_overlap_derivations(restrict_ring(field_ring(L), k), " +
			"                    λc:A. c, " +
			"                    restrict_ring(field_ring(L), " +
			"                        ring_away(field_ring(L), " +
			"                            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            x)), " +
			"                    regular_module(field_ring(L)), " +
			"                    (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y))).add, " +
			"                fst(biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"                        λc:A. c, " +
			"                        restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                x)), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y), " +
			"                        regular_module(field_ring(L)), " +
			"                        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            weierstrass_chart_one(L, k, x, y)))), " +
			"                snd(biaffine_derivation_pair(restrict_ring(field_ring(L), k), " +
			"                        λc:A. c, " +
			"                        restrict_ring(field_ring(L), " +
			"                            ring_away(field_ring(L), " +
			"                                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                                x)), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        weierstrass_chart_one(L, k, x, y), " +
			"                        regular_module(field_ring(L)), " +
			"                        (weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                            weierstrass_chart_one(L, k, x, y))))))))",
	},
		"the datum is a curve, O a lattice pair and k = A₀ ∩ A₁ (WeierstrassIsCurve, "+
			"CurveLatticeData, WeierstrassGlobalSections); take the host set(prod(num, prod(A, A))) for "+
			"the extensions over k (PowerSetUniverse; A embeds in it by LeftFactorIntoPowerSet and "+
			"CardLeTrans). The charts have no D¹ with coefficients in themselves (ChartsSmoothOnImage), "+
			"so every extension has chart classes zero and LocallyTrivialIsH1D0 gives the d; the second "+
			"conjunct is GluedTrivialIsoIffCoboundary at the curve. H¹(𝒟⁰): WeierstrassDerivationPair, "+
			"inverted (IsomorphismInverse), is an isomorphism from O, finite with dim H¹(O) = "+
			"curve_genus = 1 (EulerStructureZero, CurveGenusDef, GenusOne), so IsomorphismSameEuler "+
			"carries finiteness and the dimension to 𝒟⁰ (LatticePairH1DimDef, restrict_ring at k by "+
			"RestrictRingDef). Over the thickening, the charts are smooth over k with every coefficients "+
			"on A (ChartsSmoothOnImage, the chart rings read by RestrictRingDef), the rings have room in "+
			"the host (PowerSetUniverse, CardLeSubset), and SmoothChartsUnobstructed gives the "+
			"deformation, the regluing relating any two, and the regluings' isomorphism condition"),
})}
