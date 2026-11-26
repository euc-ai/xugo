// one_variable.go — the corpus's polynomials in one variable and the
// free algebra on one variable: a sequence of coefficients p goes to the
// coefficient function that reads p at the exponent of x on the
// monomials of {x} and is zero elsewhere, carried into the host by ι.
// Along an embedding the map is a ring isomorphism from the polynomials
// over R, under their convolution product, onto the algebra on {x}: the
// monomial xⁿ is the exponent function with n at x and zero elsewhere,
// and both products are convolutions of coefficients.

package free_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialOneVariableHomomorphism — along an embedding, the map from
// the corpus's polynomials over R to the algebra on {x} is a ring
// homomorphism from the polynomials under their convolution product.
var PolynomialOneVariableHomomorphism = polynomialOneVariableHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOneVariableHomomorphism",
	Key:  "prop_171565356b639cd9",
	Reading: "The guard m ∈ monomials({x}) is load-bearing: without it p(m(x)) would be read at " +
		"every exponent function, a nonzero coefficient would sit at monomials with exponents at " +
		"other variables, and the image would not be a polynomial of {x}. It is also why the map is " +
		"multiplicative: at a finitely supported m with an exponent at some y ≠ x, every split m₁ + " +
		"(m − m₁) leaves that exponent in one part, so each term of the convolution has a zero " +
		"factor. The source ring is polynomial_ring(R), the corpus's polynomials over R's carrier, " +
		"the target the record free_algebra_ring(ι, R, {x}) on the algebra on {x}. Over the zero ring " +
		"both are one point and the map sends the zero sequence to ι of the zero coefficient function.",
	Deps: []registry.EntryLike{
		polynomial.PolynomialRingOn,
		polynomial.PolynomialOverDef,
		polynomial.PolynomialMulDef,
		vec_space.VecDef,
		vec_space.VecAddDef,
		vec_space.BasisVectorDef,
		FreeAlgebraCommRingOn,
		FreeAlgebraRingDef,
		FreeAlgebraDef,
		FreeAlgebraEmbeddingDef,
		polynomial_algebra.PolynomialAlgebraRingDef,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.PolynomialAlgebraMulDef,
		polynomial_algebra.PolynomialAlgebraOneDef,
		polynomial_algebra.MonomialsDef,
		ring_transport.TransportRingDef,
		ring_transport.TransportBinaryOpDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		function_module.FunAddDef,
		free_module.DeltaAtDef,
		FreeAlgebraEmbeddingDecode,
		polynomial_algebra.PolynomialAlgebraSubset,
		finite_set.FiniteImageInjGeneral,
		finite_set.FiniteSubset,
		module.ModuleSumImage,
		module.ModuleSumSupport,
		comm_ring.ZeroIn,
		comm_ring.AddMonoidOn,
		comm_ring.MulLeftZeroOn,
		comm_ring.MulRightZeroOn,
		ring_homomorphism.RingHomomorphism,
		set_basic.InImage,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "ring_homomorphism(polynomial_ring(R), " +
			"    free_algebra_ring(ι, R, {x}), " +
			"    λp:(num → A). ι(λm:(D → num). COND(m ∈ monomials({x}), p(m(x)), R.zero)))",
	},
		"the image of p is ι of a polynomial of {x}: its values are p's, in the carrier, and R.zero "+
			"(ZeroIn), nonzero only at the monomials n·x with p(n) ≠ R.zero, finitely many "+
			"(FiniteImageInjGeneral, p being zero from some index on, VecDef); that polynomial is a "+
			"polynomial in every variable (PolynomialAlgebraSubset), so it is the preimage the "+
			"transported operations choose (FreeAlgebraEmbeddingDecode). Sums: pointwise on both sides, "+
			"R.zero + R.zero = R.zero off the monomials of {x}. Products: at a monomial m of {x} the "+
			"monomials m₁ below m are those of {x} with m₁(x) ≤ m(x), and m₁ ↦ m₁(x) reindexes the "+
			"convolution of the coefficient functions into polynomial_mul's sum over i ≤ m(x) "+
			"(ModuleSumImage); at any other finitely supported m every split m₁ + (m − m₁) puts an "+
			"exponent at a variable other than x in one part, where that factor is R.zero (MulLeftZeroOn, "+
			"MulRightZeroOn), and at an m of infinite support both sides are R.zero. One: basis_vector(0) "+
			"goes to the coefficient function with R.one at the exponent zero, polynomial_algebra_one(R). "+
			"Both rings are commutative (PolynomialRingOn, FreeAlgebraCommRingOn)"),
})}

// PolynomialOneVariableInjective — along an embedding, the map from the
// corpus's polynomials over R to the algebra on {x} is one-to-one.
var PolynomialOneVariableInjective = polynomialOneVariableInjectiveThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOneVariableInjective",
	Key:  "prop_dc7758a41b8309cb",
	Reading: "The coefficient function of p is a polynomial over R in every variable — " +
		"its values are p's, in R's carrier, and R.zero, there by the ring hypothesis — so it " +
		"lies in the set ι is injective on, and p is read back from it at the monomials n·x.",
	Deps: []registry.EntryLike{
		PolynomialOneVariableHomomorphism,
		FreeAlgebraEmbeddingDef,
		polynomial_algebra.MonomialsDef,
		polynomial.PolynomialOverDef,
		vec_space.VecDef,
		function_module.FiniteSupportDef,
		finite_set.FiniteImageInjGeneral,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "injective_on(«corpusPolynomials», " +
			"    λp:(num → A). ι(λm:(D → num). COND(m ∈ monomials({x}), p(m(x)), R.zero)))",
	},
		"the coefficient functions of two polynomials p and q are polynomials over R in every "+
			"variable, their values p's or q's and R.zero, in the carrier, so in the set the embedding is "+
			"injective on (FreeAlgebraEmbeddingDef), and equal images make them equal; at the monomial λy. "+
			"COND(y = x, n, 0), a monomial of {x} with exponent n at x, they read p(n) and q(n), so p = q"),
})}

// PolynomialOneVariableOnto — along an embedding, the map from the
// corpus's polynomials over R covers the algebra on {x}: its image is
// that algebra.
var PolynomialOneVariableOnto = polynomialOneVariableOntoThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOneVariableOnto",
	Key:  "prop_50d7b59b1f71d9b1",
	Reading: "With PolynomialOneVariableHomomorphism and PolynomialOneVariableInjective the map is " +
		"ring_isomorphism from polynomial_ring(R), the corpus's polynomials, onto free_algebra_ring(ι, " +
		"R, {x}) (RingIsomorphismDef): the bridge between the corpus's A[x] and the free algebra on one " +
		"variable. The inverse is p(n) = f(n·δ_x), finitely supported because n ↦ n·δ_x is injective.",
	Deps: []registry.EntryLike{
		PolynomialOneVariableHomomorphism,
		FreeAlgebraDef,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.MonomialsDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		polynomial.PolynomialOverDef,
		vec_space.VecDef,
		finite_set.FiniteImageInjGeneral,
		set_basic.InImage,
		set_basic.ImageDef,
		ring_homomorphism.RingIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "image(λp:(num → A). ι(λm:(D → num). COND(m ∈ monomials({x}), p(m(x)), R.zero)), " +
			"    «corpusPolynomials») = " +
			"free_algebra(ι, R, {x})",
	},
		"the image lies in the algebra on {x} (the carrier conjunct of "+
			"PolynomialOneVariableHomomorphism). Conversely a member is ι(f) with f a polynomial of {x}: "+
			"p(n) := f(λy. COND(y = x, n, 0)) is in the carrier and nonzero at finitely many n, the "+
			"exponent functions n·x being distinct (FiniteImageInjGeneral), so a polynomial over R's "+
			"carrier; a monomial m of {x} is the exponent function m(x)·x, so the image of p reads f "+
			"there, and off the monomials of {x} f is R.zero (FiniteSuppDef), so the image of p is ι(f)"),
})}
