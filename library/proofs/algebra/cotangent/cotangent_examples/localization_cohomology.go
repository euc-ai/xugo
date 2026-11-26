// localization_cohomology.go — the cohomology side of a localization. A
// localization S' of S at the powers of t has no André–Quillen cohomology
// over S, D^n(S'/S, N) = 0 in every degree: its homology vanishes with
// coefficients in S' itself, where the cotangent complex is a based
// complex of free modules, so the complex contracts and its dual with any
// coefficients is acyclic. In the sequence of a tower R → S → S' the
// right map D^n(S'/R, N) → D^n(S/R, N) is then an isomorphism, and its
// inverse after the coefficient map is the restriction of a class from S
// to S'. The restriction is linear, and it commutes with the left map of
// a tower R → R₀ → T and so with the action of D^1(T/R₀, M) on
// D^1(T/R, M) by which the deformations of T are a torsor.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The vanishing and the isomorphism
// ---------------------------------------------------------------------------

// LocalizationCohomologyVanishes — a localization S' of S at the powers
// of t has no André–Quillen cohomology over S: D^n(S'/S, N) = 0 for every
// n and every module N over S'.
var LocalizationCohomologyVanishes = localizationCohomologyVanishesThm{family.Add(registry.ProofEntry{
	Name: "LocalizationCohomologyVanishes",
	Key:  "prop_54fd0d622e397b74",
	Reading: "Any localization at the powers of t, the fraction model or a subring of a " +
		"ring where t is a unit, and any host with room for S and S'; the polynomials over S " +
		"and their quotient by t·x − 1 have room wherever S does. In degree 0 it says the " +
		"derivations of S' over S vanish. t nilpotent makes S' the zero ring and N one point. " +
		"The based form is load-bearing: the homology vanishes with coefficients in S' itself, " +
		"where the cotangent complex is a complex of free modules with a basis, and only such " +
		"an acyclic complex contracts, so that its dual with any coefficients is acyclic.",
	Deps: []registry.EntryLike{
		LocalizationCotangentVanishes,
		EtaleHypersurfaceVanishes,
		FxMinusOneIsLocalization,
		FxMinusOneRegular,
		FxMinusOneSeparable,
		HypersurfaceConstantHomomorphism,
		ring_localization.LocalizationIsomorphism,
		cotangent_complex.CotangentIsomorphismInvariance,
		cotangent_complex.CotangentCoefficientRestriction,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		cotangent_complex.CotangentCohomologyDef,
		free_complex_duality.BasedAcyclicContractible,
		free_complex_duality.FreeDualHomotopy,
		free_complex_duality.FreeDualQuasiIsomorphism,
		chain_complex.HomotopicSameCohomologyMap,
		module.RegularModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀S:ring_ops(B). ∀t:B. ∀S':ring_ops(C). ∀ρ:(B → C). ∀N:module_ops(C, D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"module_on(S', N)",
		},
		Conclusion: "cotangent_cohomology⟨U:U⟩(S, S', ρ, S', λc:C. c, N, n).carrier = " +
			"{cotangent_cohomology(S, S', ρ, S', λc:C. c, N, n).zero}",
	},
		"S' is isomorphic over S to S[x]/(t·x − 1) (LocalizationIsomorphism at "+
			"FxMinusOneIsLocalization, the constants a ring map by HypersurfaceConstantHomomorphism), whose "+
			"homology over S vanishes with every coefficients (EtaleHypersurfaceVanishes, t·x − 1 regular "+
			"and separable by FxMinusOneRegular and FxMinusOneSeparable); CotangentIsomorphismInvariance "+
			"and CotangentCoefficientRestriction carry it to S'; both need room in the host U for S[x] and "+
			"S[x]/(t·x − 1), which the universe cards give only at powerset hosts: here card_le(𝕌⟨prod(num, "+
			"U)⟩, U) makes U infinite, so U ⊔ {x} embeds in U, renaming variables embeds the polynomials "+
			"over S[x] in polynomial_algebra(S, 𝕌⟨U⟩), which fits in U by S's polynomial clause, and the "+
			"quotient fits by a choice of coset representatives sending zero to zero, as "+
			"LocalizationCotangentVanishes does at the fraction model. With coefficients in S' itself "+
			"(RegularModuleOn) the cotangent complex of S' over S is based by the identity on its names "+
			"(CotangentScalarBased) and acyclic in every degree, degree 0 included, so it contracts "+
			"(BasedAcyclicContractible). Transposed, the contraction makes the identity of the dual with "+
			"coefficients in N homotopic to zero (FreeDualHomotopy, HomotopicSameCohomologyMap; "+
			"equivalently FreeDualQuasiIsomorphism at the zero map onto the zero complex), and that dual is "+
			"cotangent_cochain (CotangentDualAgreement, CotangentCohomologyDef)"),
})}

// LocalizationRightMapIsomorphism — for a localization S' of S at the
// powers of t and a module N over S', the right map D^n(S'/R, N) →
// D^n(S/R, N) of the sequence of the tower R → S → S' is an isomorphism
// of modules over S' in every degree.
var LocalizationRightMapIsomorphism = localizationRightMapIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "LocalizationRightMapIsomorphism",
	Key:  "prop_dfd02ec7acdae2c2",
	Reading: "The cohomology is contravariant in the algebra: the right map runs from the " +
		"localization to S, and it is the one inverted, so that a class on S restricts to S' " +
		"(cotangent_cohomology_restriction). On the right N is read over S through ρ. In degree 0 it is " +
		"the restriction of the derivations of S' over R to S, a bijection by DerivationExtendsUniquely.",
	Deps: []registry.EntryLike{
		LocalizationCohomologyVanishes,
		transitivity.CotangentCohomologyTransitivity,
		transitivity.CoTransitivityRightMapDef,
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_complex.CotangentCohomologyModuleOn,
		chain_complex.CohomologyMapHom,
		module_homomorphism.ExactAtDef,
		module_homomorphism.KernelTrivialIffInjective,
		module_homomorphism.ModuleIsomorphismDef,
		group_homomorphism.GroupKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀t:B. " +
			"∀S':ring_ops(C). " +
			"∀ρ:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"module_on(S', N)",
		},
		Conclusion: "module_isomorphism(S', " +
			"    cotangent_cohomology⟨U:U⟩(R, S', λa:A. ρ(f(a)), S', λc:C. c, N, n), " +
			"    cotangent_cohomology(R, S, f, S', ρ, N, n), " +
			"    co_transitivity_right_map(R, S, f, S', ρ, N, n))",
	},
		"in the sequence of R → S → S' with coefficients N (CotangentCohomologyTransitivity) every "+
			"D^n(S'/S, N) is its zero class (LocalizationCohomologyVanishes). Exactness at D^n(S'/R, "+
			"N) makes the right map's kernel the left map's image, the zero alone, so the right map, a "+
			"homomorphism of modules over S' (CoTransitivityRightMapDef, CotangentMapsDualAgreement, "+
			"CohomologyMapHom, CotangentCohomologyModuleOn), is injective (KernelTrivialIffInjective); "+
			"exactness at D^n(S/R, N) makes its image the kernel of the connecting map, which is "+
			"everything because the connecting map lands in the carrier of D^(n+1)(S'/S, N), its zero "+
			"class alone (the exactness at D^(n+1)(S'/S, N) in CotangentCohomologyTransitivity; "+
			"ExactAtDef, GroupKernelDef); so it is an isomorphism (ModuleIsomorphismDef)"),
})}

// ---------------------------------------------------------------------------
// The restriction
// ---------------------------------------------------------------------------

// CotangentCohomologyRestrictionHom — for a localization S' of S at the
// powers of t and a map ν from a module N over S into a module N' over
// S', linear over S, the restriction D^n(S/R, N) → D^n(S'/R, N') is
// linear over S, and the right map takes the restriction of a class back
// to its image under composition with ν.
var CotangentCohomologyRestrictionHom = cotangentCohomologyRestrictionHomThm{family.Add(registry.ProofEntry{
	Name: "CotangentCohomologyRestrictionHom",
	Key:  "prop_fbfc9af3df2a36",
	Reading: "ν need only be linear over S; that N' is the localization of N is not " +
		"read. D^n(S'/R, N') is a module over S', read over S through ρ to compare it " +
		"with D^n(S/R, N). The second conjunct is the definition read back: the right map " +
		"undoes the restriction, which is what a computation with a restricted class cites.",
	Deps: []registry.EntryLike{
		transitivity.CotangentCohomologyRestrictionDef,
		LocalizationRightMapIsomorphism,
		transitivity.CotangentCohomologyTransitivityCoefficientNatural,
		cotangent_complex.CotangentCochainComplex,
		cotangent_complex.CotangentCohomologyModuleOn,
		chain_complex.CohomologyMapHom,
		chain_complex.CohomologyMapDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomCompose,
		module_homomorphism.IsomorphismInverse,
		functions.InverseOnRight,
		functions.InverseOnIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀t:B. " +
			"∀S':ring_ops(C). " +
			"∀ρ:(B → C). " +
			"∀N':module_ops(C, E). " +
			"∀ν:(D → E). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"module_on(S, N)",
			"module_on(S', N')",
			"module_homomorphism(S, N, scalar_restriction(ρ, N'), ν)",
		},
		Conclusion: "module_homomorphism(S, " +
			"    cotangent_cohomology(R, S, f, S, λy:B. y, N, n), " +
			"    scalar_restriction(ρ, cotangent_cohomology(R, S', λa:A. ρ(f(a)), S', λc:C. c, N', n)), " +
			"    λx:set(U → D). cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n, x)) ∧ " +
			"(∀x:set(U → D). " +
			"    x ∈ cotangent_cohomology(R, S, f, S, λy:B. y, N, n).carrier ⇒ " +
			"    co_transitivity_right_map(R, " +
			"        S, " +
			"        f, " +
			"        S', " +
			"        ρ, " +
			"        N', " +
			"        n, " +
			"        cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n, x)) = " +
			"    cohomology_map(cotangent_cochain(R, S, f, S', ρ, N'), " +
			"        λk:num. λw:(U → D). λu:U. ν(w(u)), " +
			"        n, " +
			"        x))",
	},
		"composition with ν carries the cochains with values in N to those with values in N' read over "+
			"S through ρ and commutes with the coboundaries, ν passing the finite sums of scalars acting "+
			"(HomSum, HomSmul, as in CotangentCohomologyTransitivityCoefficientNatural; "+
			"CotangentCochainComplex), so it carries classes to classes linearly (CohomologyMapDef, "+
			"CohomologyMapHom). The right map is an isomorphism from D^n(S'/R, N') "+
			"(LocalizationRightMapIsomorphism), so its inverse on the classes is linear over S' "+
			"(IsomorphismInverse), hence over S through ρ, and lands in the classes (InverseOnIn); the "+
			"composite is the restriction (CotangentCohomologyRestrictionDef, HomCompose, "+
			"CotangentCohomologyModuleOn), and the right map at it is the coefficient image (InverseOnRight)"),
})}

// RestrictionCompatibleTorsor — over a tower R → R₀ → T and a
// localization T' of T at the powers of t, the restrictions from T to T'
// over R₀ and over R commute with the left maps D^1(T/R₀) → D^1(T/R), and
// so with the action ζ ↦ ζ + i*(η) of D^1(T/R₀, M) on D^1(T/R, M).
var RestrictionCompatibleTorsor = restrictionCompatibleTorsorThm{family.Add(registry.ProofEntry{
	Name: "RestrictionCompatibleTorsor",
	Key:  "prop_1b8ad36b88ee9533",
	Reading: "The square res_R ∘ i* = i*' ∘ res_{R₀}, i* the left map of R → R₀ → T and " +
		"i*' that of R → R₀ → T'; with the linearity of the restriction it carries the action " +
		"ζ ↦ ζ + i*(η) by which the deformations of T over R are a torsor under D^1(T/R₀, M) " +
		"to the one for T', the localization of a deformation moved by η being the localized " +
		"deformation moved by res(η). No hypothesis on f beyond a ring map: the square is the " +
		"functoriality of D^1 in the pair (R → R₀, T → T'), not a fact of thickenings. Both " +
		"restrictions carry M by ν into M', any linear map; M' need not localize M.",
	Deps: []registry.EntryLike{
		CotangentCohomologyRestrictionHom,
		LocalizationRightMapIsomorphism,
		transitivity.CotangentCohomologyRestrictionDef,
		transitivity.CoTransitivityLeftMapDef,
		transitivity.CoTransitivityRightMapDef,
		transitivity.CotangentCohomologyTransitivityCoefficientNatural,
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_complex.CotangentCohomologyModuleOn,
		chain_complex.CohomologyMapCompose,
		chain_complex.CohomologyMapCongruence,
		chain_complex.CohomologyMapHom,
		module_homomorphism.HomAdd,
		functions.InjectiveOnDef,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀t:C. " +
			"∀T':ring_ops(F). " +
			"∀ρ:(C → F). " +
			"∀M':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"cotangent_universe(T', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, R₀, f)",
			"ring_homomorphism(R₀, T, g)",
			"is_localization_on(T, monoid_powers(T.mul, T.one, t), T', ρ)",
			"module_on(T, M)",
			"module_on(T', M')",
			"module_homomorphism(T, M, scalar_restriction(ρ, M'), ν)",
		},
		Conclusion: "(∀η:set(U → D). " +
			"    η ∈ cotangent_cohomology(R₀, T, g, T, λc:C. c, M, 1).carrier ⇒ " +
			"    cotangent_cohomology_restriction(R, " +
			"        T, " +
			"        λa:A. g(f(a)), " +
			"        T', " +
			"        ρ, " +
			"        M', " +
			"        ν, " +
			"        1, " +
			"        co_transitivity_left_map(R, R₀, f, T, g, M, 1, η)) = " +
			"    co_transitivity_left_map(R, " +
			"        R₀, " +
			"        f, " +
			"        T', " +
			"        λb:B. ρ(g(b)), " +
			"        M', " +
			"        1, " +
			"        cotangent_cohomology_restriction(R₀, T, g, T', ρ, M', ν, 1, η))) ∧ " +
			"(∀ζ η:set(U → D). " +
			"    ζ ∈ cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, M, 1).carrier ∧ " +
			"    η ∈ cotangent_cohomology(R₀, T, g, T, λc:C. c, M, 1).carrier ⇒ " +
			"    cotangent_cohomology_restriction(R, " +
			"        T, " +
			"        λa:A. g(f(a)), " +
			"        T', " +
			"        ρ, " +
			"        M', " +
			"        ν, " +
			"        1, " +
			"        cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, M, 1).add(ζ, " +
			"            co_transitivity_left_map(R, R₀, f, T, g, M, 1, η))) = " +
			"    cotangent_cohomology(R, T', λa:A. ρ(g(f(a))), T', λy:F. y, M', 1).add( " +
			"        cotangent_cohomology_restriction(R, T, λa:A. g(f(a)), T', ρ, M', ν, 1, ζ), " +
			"        co_transitivity_left_map(R, " +
			"            R₀, " +
			"            f, " +
			"            T', " +
			"            λb:B. ρ(g(b)), " +
			"            M', " +
			"            1, " +
			"            cotangent_cohomology_restriction(R₀, T, g, T', ρ, M', ν, 1, η))))",
	},
		"apply the right map of R → T → T', injective on D^1(T'/R, M') "+
			"(LocalizationRightMapIsomorphism), to both sides of the square. On the left it gives the "+
			"coefficient image of i*(η) (CotangentCohomologyRestrictionHom's second conjunct), which "+
			"is i* of the coefficient image of η (CotangentCohomologyTransitivityCoefficientNatural, "+
			"M' read over T through ρ). On the right the right map after i*' is i* after the right "+
			"map of R₀ → T → T': the transposed Jacobians of the base change from R to R₀ and of the "+
			"map T → T' compose either way to the transpose of one map of resolutions, a tag x of T "+
			"going to the tag of ρ(x) with coefficients moved along f (CoTransitivityLeftMapDef, "+
			"CoTransitivityRightMapDef, CotangentMapsDualAgreement, CohomologyMapCompose, "+
			"CohomologyMapCongruence), and the right map of R₀ → T → T' at res_{R₀}(η) is the "+
			"coefficient image of η (CotangentCohomologyRestrictionHom). The torsor conjunct is the "+
			"square with the additivity of res_R (CotangentCohomologyRestrictionHom, HomAdd)"),
})}
