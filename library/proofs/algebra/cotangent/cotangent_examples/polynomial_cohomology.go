// polynomial_cohomology.go — the cohomology side of a free algebra. The
// free algebra R[W] on a set of names is smooth over R: its cotangent
// complex with coefficients in R[W] itself is a based complex whose
// homology is the free module on W in degree 0 and nothing above, so its
// dual with coefficients in any module N has cohomology in degree 0
// alone, Dⁿ(R[W]/R, N) = 0 for every n ≥ 1.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialCohomologyVanishes — the free algebra on W over R has
// Dⁿ(R[W]/R, N) = 0 for every n ≥ 1 and every module N over R[W].
var PolynomialCohomologyVanishes = polynomialCohomologyVanishesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCohomologyVanishes",
	Key:  "prop_f03fd3a0bc03f0f6",
	Reading: "The universe hypotheses are PolynomialCotangentVanishes's, and W and N are " +
		"arbitrary: at W = ∅ the algebra is the constants of R, over the zero ring N is one point. " +
		"In degree 0 the cohomology is the derivations of R[W] over R into N, one free value at " +
		"each name, so the bound n ≥ 1 is load-bearing. The vanishing is not read off the homology " +
		"with coefficients in N: it is the dual of the complex with coefficients in R[W] itself, " +
		"based and exact above degree 0 with a free module in degree 0, and a complex of that " +
		"shape stays exact above degree 0 under Hom into any N. Degree 1 holds because δ¹ is the " +
		"identity on the dual of the constant complex; at W = ∅, R[∅] ≅ R and every Dⁿ vanishes.",
	Deps: []registry.EntryLike{
		PolynomialCotangentVanishes,
		PolynomialCotangentDegreeZero,
		ConstantDifferentialComplex,
		simplicial_ring.ConstantPolynomialResolution,
		cotangent_complex.CotangentResolutionIndependence,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		cotangent_complex.CotangentCohomologyDef,
		free_complex_duality.FreeDualQuasiIsomorphism,
		free_complex_duality.FreeDualHomotopy,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.HomotopicSameCohomologyMap,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀W:set(U). ∀N:module_ops(U, D). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(universe_algebra_ring(R, W), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"module_on(universe_algebra_ring(R, W), N)",
			"1 ≤ n",
		},
		Conclusion: "cotangent_cohomology⟨U:U⟩(R, " +
			"    universe_algebra_ring(R, W), " +
			"    universe_algebra_const(R), " +
			"    universe_algebra_ring(R, W), " +
			"    λu:U. u, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_cohomology(R, " +
			"        universe_algebra_ring(R, W), " +
			"        universe_algebra_const(R), " +
			"        universe_algebra_ring(R, W), " +
			"        λu:U. u, " +
			"        N, " +
			"        n).zero}",
	},
		"with coefficients in R[W] itself the cotangent complex is based by its standard names "+
			"(CotangentScalarBased) and chain homotopy equivalent to the differential complex of the "+
			"constant algebra on W (ConstantPolynomialResolution, CotangentResolutionIndependence), which is "+
			"based too, finite_supp on W in every degree, with boundary zero out of degree 1 and the "+
			"identity and zero alternating above (ConstantDifferentialComplex). A homotopy equivalence of "+
			"based complexes transposes to one of their duals with coefficients in N (FreeDualHomotopy, "+
			"HomotopicSameCohomologyMap; equivalently FreeDualQuasiIsomorphism), and the dual of the "+
			"cotangent complex is cotangent_cochain (CotangentDualAgreement, CotangentCohomologyDef). The "+
			"dual of the constant complex has the functions W → N in every degree, its coboundary zero out "+
			"of degree 0, the identity out of every odd degree and zero out of every even degree above 0: "+
			"each degree n ≥ 1 has its cocycles equal to its coboundaries (CohomologyModuleDef, CocyclesDef, "+
			"CoboundariesDef), and a bijection of carriers keeps a carrier one point (ModuleIsomorphismDef)"),
})}
