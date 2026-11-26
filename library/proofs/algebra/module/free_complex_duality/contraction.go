// contraction.go — contractions of acyclic based complexes and homotopy
// inverses of quasi-isomorphisms between based complexes. Over a basis a
// map out of a degree lifts, generator by generator, along any map whose
// image contains its image; so an exact based complex has a contraction
// built degree by degree, and the cone of a quasi-isomorphism, exact and
// based, yields a homotopy inverse and both homotopies.

package free_complex_duality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Contractions and homotopy inverses
// ---------------------------------------------------------------------------

// BasedAcyclicContractible — an acyclic based complex, exact in every
// degree including 0, has a contraction.
var BasedAcyclicContractible = basedAcyclicContractibleThm{family.Add(registry.ProofEntry{
	Name: "BasedAcyclicContractible",
	Key:  "prop_29f37edee802bb47",
	Reading: "Acyclic includes degree 0: H₀ = 0 is P.d(1) onto P.terms(0), which " +
		"starts the recursion and gives the degree-0 clause P.d(1) ∘ h(0) = id, where " +
		"no boundary out of degree 0 is read. The basis is what makes each step a " +
		"choice per generator; without it an exact complex of modules need not contract.",
	Deps: []registry.EntryLike{
		free_module.FreeModuleLift,
		BasedComplexChain,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedExpandCoordinates,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.ComplexBoundaryHom,
		chain_complex.ComplexBoundaryTwice,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Hypotheses: []string{
			"∀n:num. cycles(P, n) = boundaries(P, n)",
		},
		Conclusion: "∃h:(num → B → B). " +
			"    (∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(P, n + 1), h(n))) ∧ " +
			"    (∀x:B. x ∈ P.terms(0) ⇒ P.d(1)(h(0)(x)) = x) ∧ " +
			"    (∀n:num. ∀x:B. x ∈ P.terms(n + 1) ⇒ P.add(P.d(n + 2)(h(n + 1)(x)), h(n)(P.d(n + 1)(x))) = x)",
	}),
		"Build h by recursion on n with FreeModuleLift composed with the coordinates. Degree 0: "+
			"exactness at 0 says P.d(1) maps P.terms(1) onto P.terms(0) (cycles(P, 0) = P.terms(0): "+
			"CyclesDef, BoundariesDef), so e(0) lifts along P.d(1) to h' and h(0) = h' ∘ r(0) "+
			"satisfies P.d(1) ∘ h(0) = id on P.terms(0) (BasedExpandCoordinates). Degree n + 1, given "+
			"P.d(n + 1) ∘ h(n) = id − h(n − 1) ∘ P.d(n) (= id at n = 0): for x ∈ P.terms(n + 1), x − "+
			"h(n)(P.d(n + 1)(x)) is a cycle — its boundary is P.d(n + 1)(x) − (P.d(n + 1)(x) − h(n − "+
			"1)(P.d(n)(P.d(n + 1)(x)))) = P.zero by ComplexBoundaryTwice — hence a boundary; the map "+
			"x ↦ x − h(n)(P.d(n + 1)(x)) after e(n + 1) lifts along P.d(n + 2), and h(n + 1) is that "+
			"lift after r(n + 1). The recursion carries the identity just used as its invariant."),
})}

// BasedQuasiIsomorphismHomotopyEquivalence — a quasi-isomorphism between
// based complexes is a chain homotopy equivalence.
var BasedQuasiIsomorphismHomotopyEquivalence = basedQuasiIsomorphismHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "BasedQuasiIsomorphismHomotopyEquivalence",
	Key:  "prop_edccbe7523a293b9",
	Reading: "The generator types of P and Q may differ, which is why " +
		"the cone's tags are chosen in the proof and not in the statement.",
	Deps: []registry.EntryLike{
		ChainConeBased,
		chain_complex.ConeContractibleHomotopyInverse,
		BasedAcyclicContractible,
		BasedComplexChain,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.ConeChainComplex,
		chain_complex.ConeQuasiIffAcyclic,
		chain_complex.ChainHomotopyEquivalenceDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"∀Q:complex_ops(A, C). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → C). " +
			"∀r':(num → C → E → A). " +
			"∀f:(num → B → C).",
		Hypotheses: []string{
			"based_chain_complex(R, P, S, e, r)",
			"based_chain_complex(R, Q, S', e', r')",
			"quasi_isomorphism(R, P, Q, f)",
		},
		Conclusion: "∃g:(num → C → B). chain_homotopy_equivalence(R, P, Q, f, g)",
	},
		"Tag the two kinds of generators apart in prod(bool, prod(I, E)) — ι x = (T, (x, εy. "+
			"T)), κ y = (F, (εx. T, y)), one-to-one with disjoint images; then the cone of f is "+
			"based (ChainConeBased), a complex (ConeChainComplex), and exact in every degree "+
			"since f is a quasi-isomorphism (ConeQuasiIffAcyclic). BasedAcyclicContractible "+
			"contracts it, and ConeContractibleHomotopyInverse reads a homotopy inverse and both "+
			"homotopies off the contraction (ChainHomotopyEquivalenceDef)."),
})}
