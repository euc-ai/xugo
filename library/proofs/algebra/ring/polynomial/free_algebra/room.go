// room.go — the room a host needs: the polynomials over R in the
// variables of a powerset, and the polynomials over R in one variable,
// inject into that powerset when the carrier of R does.

package free_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialCarrierIntoPowerSet — the polynomials over R whose variables
// are the subsets of prod(num, B) inject into those subsets when R's
// carrier does.
var PolynomialCarrierIntoPowerSet = polynomialCarrierIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCarrierIntoPowerSet",
	Key:  "prop_a38832ef0da64d1b",
	Reading: "The room is asked of the carrier, not of the coefficient type A, and " +
		"no ring law is read: a ring on set(A) whose carrier injects, a quotient of a " +
		"ring on the powerset among them, has its polynomials in the powerset too. It " +
		"is the polynomial clause of the cotangent domain's universe at a powerset host.",
	Deps: []registry.EntryLike{
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.MonomialsDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		cardinal.PolynomialsIntoPowerSet,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"card_le(R.carrier, 𝕌⟨A:set(prod(num, B))⟩)",
		},
		Conclusion: "card_le(polynomial_algebra(R, 𝕌⟨A:set(prod(num, B))⟩), 𝕌⟨A:set(prod(num, B))⟩)",
	},
		"a polynomial over R in the variables of the powerset is finitely supported, takes its values "+
			"in the carrier and is R.zero off the finitely supported monomials (PolynomialAlgebraDef, "+
			"FiniteSuppDef, MonomialsDef, FiniteSupportDef), so it lies in the set "+
			"PolynomialsIntoPowerSet injects at C = R.carrier and zero = R.zero; CardLeSubset, CardLeTrans"),
})}

// UnivariatePolynomialCarrierCardLe — the corpus's polynomials over R
// inject into the subsets of prod(num, B) when R's carrier does.
var UnivariatePolynomialCarrierCardLe = univariatePolynomialCarrierCardLeThm{family.Add(registry.ProofEntry{
	Name: "UnivariatePolynomialCarrierCardLe",
	Key:  "prop_cd665c757593057a",
	Reading: "No ring and no embedding is read: the room is the carrier's, so the " +
		"polynomial ring R[x] on num → A has a powerset host chosen from R alone, which " +
		"the type num → A need not fit. The zero R.zero lies in the carrier whenever " +
		"some polynomial does, as the value of every polynomial from some index on.",
	Deps: []registry.EntryLike{
		PolynomialCarrierIntoPowerSet,
		polynomial.PolynomialOverDef,
		vec_space.VecDef,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.MonomialsDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		finite_set.FiniteImageInjGeneral,
		functions.InjectiveOnDef,
		cardinal.CardLeDef,
		cardinal.CardLeTrans,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"card_le(R.carrier, 𝕌⟨A:set(prod(num, B))⟩)",
		},
		Conclusion: "card_le(«corpusPolynomials», 𝕌⟨A:set(prod(num, B))⟩)",
	},
		"fix the variable ∅ of the powerset; p goes to the coefficient function reading p "+
			"at the exponent of ∅ on the monomials of {∅} and R.zero elsewhere, a polynomial "+
			"over R in the variables of the powerset: its values are p's, R.zero among them, "+
			"all in the carrier, and nonzero at finitely many monomials n·∅ "+
			"(PolynomialOverDef, VecDef, FiniteImageInjGeneral); p is read back at those "+
			"monomials, so the map is injective; PolynomialCarrierIntoPowerSet and CardLeTrans"),
})}
