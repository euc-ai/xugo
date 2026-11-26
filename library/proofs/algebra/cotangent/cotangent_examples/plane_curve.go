// plane_curve.go — the cotangent complex of a plane curve: A = R[x, y]/(F)
// for a commutative ring R and a member F of the free algebra on two
// names that is no zero divisor there. The tower R → R[x, y] → A has
// R[x, y] free on dx and dy in degree 0 and A, over R[x, y], free on the
// conormal class of F in degree 1, and the connecting map sends that
// class to dF = F_x dx + F_y dy; so L_{A/R} is quasi-isomorphic to the
// two-term complex [A → A²], 1 ↦ (F_x, F_y). Both are based, and its
// dual with coefficients in a module N is [N² → N], (n_x, n_y) ↦
// F_x·n_x + F_y·n_y: D⁰(A/R, N) is the kernel, the derivations,
// D¹(A/R, N) the cokernel N/(F_x·N + F_y·N), and every Dⁿ above degree 1
// vanishes.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The cotangent complex of a plane curve
// ---------------------------------------------------------------------------

// PlaneCurveCotangentComplex — for F no zero divisor in R[x, y], the
// cotangent complex of A = R[x, y]/(F) over R is quasi-isomorphic to the
// two-term complex [A → A²], 1 ↦ (F_x, F_y).
var PlaneCurveCotangentComplex = planeCurveCotangentComplexThm{family.Add(registry.ProofEntry{
	Name: "PlaneCurveCotangentComplex",
	Key:  "prop_ef9e4a56b9c50716",
	Reading: "The two-term complex is the conormal module (F)/(F²), free over A on the class " +
		"of F because F is regular, mapped by d into Ω_{P/R} ⊗ A, free on dx and dy: its generator " +
		"F in degree 1 goes to F_x at x and F_y at y. The cotangent complex is taken with " +
		"coefficients in A itself, so both sides are based complexes (FreeComplexBased, " +
		"CotangentScalarBased) and the quasi-isomorphism dualizes to every coefficient module " +
		"(PlaneCurveCohomologyLowDegrees). F regular is load-bearing: at F = 0 over a nonzero ring " +
		"A is the free algebra P, whose cotangent complex is A² in degree 0, while the two-term " +
		"complex has the homology A in degree 1. Of x and y only that they are names is read: at x " +
		"= y the generators of degree 0 are {x} and the complex is [A → A], 1 ↦ F_x, the " +
		"hypersurface in one variable. F a unit makes A the zero ring, and both complexes are zero.",
	Deps: []registry.EntryLike{
		PolynomialCotangentDegreeZero,
		PolynomialCotangentVanishes,
		RegularQuotientCotangent,
		RegularQuotientFirstHomology,
		TransitivityConnectingConormal,
		StandardDifferentialBoundaryOne,
		ConormalDegreeZero,
		KoszulQuotientIdealQuotient,
		transitivity.TransitivityExactAtMiddle,
		transitivity.TransitivityExactAtLeft,
		transitivity.TransitivityExactAtRight,
		transitivity.TransitivityEnd,
		cotangent_complex.CotangentCoefficientRestriction,
		cotangent_complex.CotangentHomologyDef,
		cotangent_complex.CotangentChainComplex,
		resolution.FreeComplexOf,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.ChainMapDef,
		chain_complex.HomologyModuleDef,
		chain_complex.HomologyMapCoset,
		partial_derivative.PartialSupportFinite,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀x y F:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, {x, y}), 𝕌⟨A:U⟩)",
			"cotangent_universe(koszul_quotient(universe_algebra_ring(R, {x, y}), F), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"F ∈ universe_algebra_ring(R, {x, y}).carrier",
			"∀p:U. " +
				"    p ∈ universe_algebra_ring(R, {x, y}).carrier ∧ " +
				"    universe_algebra_ring(R, {x, y}).mul(F, p) = universe_algebra_ring(R, {x, y}).zero ⇒ " +
				"    p = universe_algebra_ring(R, {x, y}).zero",
		},
		Conclusion: "∃φ:(num → (U → set(U)) → U → set(U)). " +
			"    quasi_isomorphism(koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        free_complex(koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"            λn:num. COND(n = 0, {x, y}, COND(n = 1, {F}, ∅)), " +
			"            λn:num. λc:(U → set(U)). λv:U. " +
			"                COND(n = 1 ∧ v = x, " +
			"                    koszul_quotient(universe_algebra_ring(R, {x, y}), F).mul(koszul_projection( " +
			"                            universe_algebra_ring(R, {x, y}), " +
			"                            F, " +
			"                            free_algebra_partial(universe_embedding(R), R, x, F)), " +
			"                        c(F)), " +
			"                    COND(n = 1 ∧ v = y, " +
			"                        koszul_quotient(universe_algebra_ring(R, {x, y}), F).mul( " +
			"                            koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                                F, " +
			"                                free_algebra_partial(universe_embedding(R), R, y, F)), " +
			"                            c(F)), " +
			"                        koszul_quotient(universe_algebra_ring(R, {x, y}), F).zero))), " +
			"        cotangent_complex⟨U:U⟩(R, " +
			"            koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"            λc:A. " +
			"                koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                    F, " +
			"                    universe_algebra_const(R, c)), " +
			"            koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"            λz:set(U). z, " +
			"            mk_module(koszul_quotient(universe_algebra_ring(R, {x, y}), F).add, " +
			"                koszul_quotient(universe_algebra_ring(R, {x, y}), F).zero, " +
			"                koszul_quotient(universe_algebra_ring(R, {x, y}), F).neg, " +
			"                koszul_quotient(universe_algebra_ring(R, {x, y}), F).mul, " +
			"                koszul_quotient(universe_algebra_ring(R, {x, y}), F).carrier)), " +
			"        φ)",
	},
		"read the homology on the tower R → P → A with coefficients in A (TransitivityExactAtMiddle, "+
			"TransitivityExactAtLeft, TransitivityExactAtRight, TransitivityEnd): D_n(P/R, A) is A on dx "+
			"and dy in degree 0 and zero above (PolynomialCotangentDegreeZero, PolynomialCotangentVanishes, "+
			"the coefficients restricted along the projection by CotangentCoefficientRestriction), D_n(A/P, "+
			"A) is A on the conormal class of F in degree 1 and zero elsewhere (RegularQuotientCotangent, "+
			"RegularQuotientFirstHomology at P, ConormalDegreeZero), and the connecting map sends that "+
			"class to the class of d(tag F), which is F_x·[dx] + F_y·[dy] (TransitivityConnectingConormal, "+
			"then StandardDifferentialBoundaryOne at F read in the tags of x̄ and ȳ). So 0 → D_1(A/R) → A → "+
			"A² → D_0(A/R) → 0 is exact with the middle map 1 ↦ (F_x, F_y), and D_n(A/R) = 0 for n ≥ 2. "+
			"Take φ sending the generators x and y to the basis differentials at the tags of x̄ and ȳ and "+
			"the generator F to the differential of the 1-simplex lifting F less that of the constant zero, "+
			"a chain map by StandardDifferentialBoundaryOne; it matches the sequence degree by degree, an "+
			"isomorphism on homology (QuasiIsomorphismDef, HomologyMapCoset)"),
})}

// PlaneCurveCohomologyLowDegrees — for F no zero divisor in R[x, y] and
// A = R[x, y]/(F), D¹(A/R, N) ≅ N/(F_x·N + F_y·N), and D⁰(A/R, N) is
// the pairs (n_x, n_y) of N with F_x·n_x + F_y·n_y = 0 — the
// derivations, read at x and y.
var PlaneCurveCohomologyLowDegrees = planeCurveCohomologyLowDegreesThm{family.Add(registry.ProofEntry{
	Name: "PlaneCurveCohomologyLowDegrees",
	Key:  "prop_d98bd10795a55a22",
	Reading: "Hom_A of [A → A²], 1 ↦ (F_x, F_y), into N is [N² → N], (n_x, n_y) ↦ F_x•n_x + " +
		"F_y•n_y, so D¹ is its cokernel and D⁰ its kernel. D⁰ is the derivations of A over R into N, " +
		"a derivation D read as the pair (D(x̄), D(ȳ)), on which the relation imposes F_x•D(x̄) + " +
		"F_y•D(ȳ) = 0. When F_x and F_y generate the unit ideal of A, D¹ vanishes for every N: A is " +
		"smooth over R. At F = y² − x³ over a field and N = A/(x̄, ȳ) both partials act as zero and " +
		"D¹ is N. x ≠ y is read by the second conjunct only: at x = y the function on {x, y} is one " +
		"value w(x) and the condition would double F_x•w(x); the first holds there too, as N/F_x·N.",
	Deps: []registry.EntryLike{
		PlaneCurveCotangentComplex,
		free_complex_duality.FreeComplexBased,
		cotangent_complex.CotangentScalarBased,
		free_complex_duality.FreeDualQuasiIsomorphism,
		cotangent_complex.CotangentDualAgreement,
		tor_ext.HomComplexDualAgreement,
		cotangent_complex.CotangentCohomologyDef,
		tor_ext.HomComplexOf,
		tor_ext.HomCoboundaryDef,
		function_module.FunModuleDef,
		function_module.FunctionModuleDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
		submodule.QuotientModuleDef,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀x y F:U. ∀N:module_ops(set(U), D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, {x, y}), 𝕌⟨A:U⟩)",
			"cotangent_universe(koszul_quotient(universe_algebra_ring(R, {x, y}), F), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"F ∈ universe_algebra_ring(R, {x, y}).carrier",
			"∀p:U. " +
				"    p ∈ universe_algebra_ring(R, {x, y}).carrier ∧ " +
				"    universe_algebra_ring(R, {x, y}).mul(F, p) = universe_algebra_ring(R, {x, y}).zero ⇒ " +
				"    p = universe_algebra_ring(R, {x, y}).zero",
			"x ≠ y",
			"module_on(koszul_quotient(universe_algebra_ring(R, {x, y}), F), N)",
		},
		Conclusion: "module_isomorphic(koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"    cotangent_cohomology⟨U:U⟩(R, " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                F, " +
			"                universe_algebra_const(R, c)), " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λz:set(U). z, " +
			"        N, " +
			"        1), " +
			"    quotient_module(N, " +
			"        {m:D | " +
			"            ∃v w:D. " +
			"                v ∈ N.carrier ∧ " +
			"                w ∈ N.carrier ∧ " +
			"                m = " +
			"                N.add(N.smul(koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                            F, " +
			"                            free_algebra_partial(universe_embedding(R), R, x, F)), " +
			"                        v), " +
			"                    N.smul(koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                            F, " +
			"                            free_algebra_partial(universe_embedding(R), R, y, F)), " +
			"                        w))})) ∧ " +
			"module_isomorphic(koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"    cotangent_cohomology⟨U:U⟩(R, " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                F, " +
			"                universe_algebra_const(R, c)), " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λz:set(U). z, " +
			"        N, " +
			"        0), " +
			"    restrict_module(function_module(N, {x, y}), " +
			"        {w:U → D | " +
			"            w ∈ fun_module(N.zero, N.carrier, {x, y}) ∧ " +
			"            N.add(N.smul(koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                        F, " +
			"                        free_algebra_partial(universe_embedding(R), R, x, F)), " +
			"                    w(x)), " +
			"                N.smul(koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                        F, " +
			"                        free_algebra_partial(universe_embedding(R), R, y, F)), " +
			"                    w(y))) = " +
			"            N.zero}))",
	},
		"dualize PlaneCurveCotangentComplex: the two-term complex is based by the identity "+
			"(FreeComplexBased) and the cotangent complex with coefficients in A by its standard names "+
			"(CotangentScalarBased), so the dual of the quasi-isomorphism with coefficients in N is an "+
			"isomorphism on cohomology (FreeDualQuasiIsomorphism); the dual of the cotangent complex is "+
			"cotangent_cochain (CotangentDualAgreement) and that of the two-term complex hom_complex "+
			"(HomComplexDualAgreement). There the coboundary out of degree 0 sends w to the function at "+
			"F with value F_x•w(x) + F_y•w(y) (HomCoboundaryDef), so the cocycles of degree 0 are the "+
			"kernel, and evaluation at F carries the classes of degree 1 onto the cosets of F_x·N + "+
			"F_y·N (CohomologyModuleDef, CocyclesDef, CoboundariesDef, QuotientModuleDef, HomCompose)"),
})}

// PlaneCurveCohomologyVanishes — for F no zero divisor in R[x, y] and
// A = R[x, y]/(F), Dⁿ(A/R, N) = 0 for every n ≥ 2 and every module N over
// A.
var PlaneCurveCohomologyVanishes = planeCurveCohomologyVanishesThm{family.Add(registry.ProofEntry{
	Name: "PlaneCurveCohomologyVanishes",
	Key:  "prop_cf684f775c1c848d",
	Reading: "No hypothesis on F_x and F_y: a plane curve cut out by one regular equation has " +
		"no cohomology above degree 1, smooth or not, its cotangent complex having amplitude ⟦−1, " +
		"0⟧. Regularity is read through PlaneCurveCotangentComplex, that is through " +
		"RegularQuotientCotangent: at a zero divisor F the Koszul algebra does not resolve P/(F), " +
		"and its homology over P need not stop at degree 1. Over the zero ring every N is one point.",
	Deps: []registry.EntryLike{
		PlaneCurveCotangentComplex,
		free_complex_duality.FreeComplexBased,
		cotangent_complex.CotangentScalarBased,
		free_complex_duality.FreeDualQuasiIsomorphism,
		cotangent_complex.CotangentDualAgreement,
		tor_ext.HomComplexDualAgreement,
		cotangent_complex.CotangentCohomologyDef,
		tor_ext.HomComplexOf,
		function_module.FunModuleDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀x y F:U. ∀N:module_ops(set(U), D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, {x, y}), 𝕌⟨A:U⟩)",
			"cotangent_universe(koszul_quotient(universe_algebra_ring(R, {x, y}), F), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"F ∈ universe_algebra_ring(R, {x, y}).carrier",
			"∀p:U. " +
				"    p ∈ universe_algebra_ring(R, {x, y}).carrier ∧ " +
				"    universe_algebra_ring(R, {x, y}).mul(F, p) = universe_algebra_ring(R, {x, y}).zero ⇒ " +
				"    p = universe_algebra_ring(R, {x, y}).zero",
			"module_on(koszul_quotient(universe_algebra_ring(R, {x, y}), F), N)",
			"2 ≤ n",
		},
		Conclusion: "cotangent_cohomology⟨U:U⟩(R, " +
			"    koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"    λc:A. koszul_projection(universe_algebra_ring(R, {x, y}), F, universe_algebra_const(R, c)), " +
			"    koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"    λz:set(U). z, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_cohomology(R, " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(R, {x, y}), " +
			"                F, " +
			"                universe_algebra_const(R, c)), " +
			"        koszul_quotient(universe_algebra_ring(R, {x, y}), F), " +
			"        λz:set(U). z, " +
			"        N, " +
			"        n).zero}",
	},
		"dualize PlaneCurveCotangentComplex as in PlaneCurveCohomologyLowDegrees (FreeComplexBased, "+
			"CotangentScalarBased, FreeDualQuasiIsomorphism, CotangentDualAgreement, "+
			"HomComplexDualAgreement): above degree 1 the two-term complex has no generators, so the "+
			"hom complex holds the zero function alone there (HomComplexOf, FunModuleDef), and so does "+
			"its cohomology; a bijection of carriers keeps a carrier one point (ModuleIsomorphismDef)"),
})}
