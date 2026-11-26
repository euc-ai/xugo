package curve_zeta

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve_riemann_roch"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

//go:embed curve_zeta.cnf.pb
var familyCNF []byte

// _LatticePair is the Go type of a pair of subsets of the field: a lattice pair,
// an invertible pair or a closed point.
type _LatticePair = Prod[Set[A], Set[A]]

// _Class is the Go type of a divisor class, a set of lattice pairs.
type _Class = Set[_LatticePair]

// _Divisor is the Go type of a closed divisor, an integer at each lattice pair.
type _Divisor = Fun[_LatticePair, Int]

// family is the family handle. The names M, K, k, t, A₀, A₁, A₀₁ are the
// statements' binders, so a statement that binds one of them further in writes the
// term out. K sits inside M, which is taken algebraically closed where extension
// counts are needed, A₀ and A₁ are the two charts and A₀₁ their overlap, and a
// "pair" is a lattice pair. A member that needs no closed field states the curve
// at one field L, in smooth_curve's «sc…» names; a member that reads extension
// counts keeps M and K.
var family = registry.NewFamily("scheme/curve_zeta", familyCNF).WithCoerceDomain(
	proof.RealDomain).WithOuterAbbrev(
	smooth_curve_riemann_roch.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "scGenus", Text: "curve_genus(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "scEffective", Text: "curve_effective_count(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "scZeta", Text: "λn:num. «scEffective»(n)"},
	{Name: "scIndex", Text: "curve_divisor_index(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "scClasses", Text: "curve_degree_classes(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "scPicZero", Text: "curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "scPoints", Text: "{P:prod(set(A), set(A)) | «scPoint»(P)}"},
	{Name: "scClass", Text: "λD:(prod(set(A), set(A)) → int). " +
		"    curve_pair_class(field_ring(L), «scPair»(D))"},
	{Name: "scEffectiveInClass", Text: "λc:set(prod(set(A), set(A))). " +
		"    {E:prod(set(A), set(A)) → int | " +
		"        «scDivisor»(E) ∧ (∀P:prod(set(A), set(A)). int_of_num(0) ≤ E(P)) ∧ «scClass»(E) = c}"},
	{Name: "scOfDegree", Text: "λn:int. " +
		"    {E:prod(set(A), set(A)) → int | " +
		"        «scDivisor»(E) ∧ (∀P:prod(set(A), set(A)). int_of_num(0) ≤ E(P)) ∧ «scDegree»(E) = n}"},
	{Name: "scPairDegree", Text: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "functionRing", Text: "restrict_ring(field_ring(M), K)"},
	{Name: "curve", Text: "smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)"},
	{Name: "genus", Text: "curve_genus(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "numerator", Text: "curve_zeta_numerator(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "effective", Text: "curve_effective_count(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "zeta", Text: "λn:num. «effective»(n)"},
	{Name: "complexZeta", Text: "λn:num. complex_of_real(«effective»(n))"},
	{Name: "count", Text: "curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁)"},
	{Name: "q", Text: "real_of_num(card(k))"},
	{Name: "index", Text: "curve_divisor_index(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "classes", Text: "curve_degree_classes(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "picZero", Text: "curve_pic_zero(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "point", Text: "curve_closed_point(«functionRing», A₀, A₁, A₀₁)"},
	{Name: "points", Text: "{P:prod(set(A), set(A)) | «point»(P)}"},
	{Name: "pointDegree", Text: "curve_closed_degree(«functionRing», k, A₀, A₁)"},
	{Name: "divisor", Text: "closed_divisor(«functionRing», A₀, A₁, A₀₁)"},
	{Name: "pair", Text: "closed_divisor_pair(«functionRing», A₀, A₁, A₀₁)"},
	{Name: "degree", Text: "closed_divisor_degree(«functionRing», k, A₀, A₁)"},
	{Name: "class", Text: "λD:(prod(set(A), set(A)) → int). " +
		"    curve_pair_class(«functionRing», «pair»(D))"},
	{Name: "effectiveInClass", Text: "λc:set(prod(set(A), set(A))). " +
		"    {E:prod(set(A), set(A)) → int | " +
		"        «divisor»(E) ∧ (∀P:prod(set(A), set(A)). int_of_num(0) ≤ E(P)) ∧ «class»(E) = c}"},
	{Name: "sections", Text: "λD:(prod(set(A), set(A)) → int). " +
		"    module_dim(restrict_ring(field_ring(M), k), " +
		"        lattice_pair_h0(restrict_module(regular_module(field_ring(M)), K), «pair»(D)))"},
	{Name: "reciprocalRoots", Text: "λa:(num → complex). " +
		"    curve_reciprocal_roots(«functionRing», k, A₀, A₁, A₀₁, a)"},
	{Name: "1−T", Text: "vec_sub(real_sub, " +
		"    basis_vector(real_of_num(0), real_of_num(1), 0), " +
		"    basis_vector(real_of_num(0), real_of_num(1), 1))"},
	{Name: "1−qT", Text: "vec_sub(real_sub, " +
		"    basis_vector(real_of_num(0), real_of_num(1), 0), " +
		"    vec_scalar_mul(real_mul, «q», basis_vector(real_of_num(0), real_of_num(1), 1)))"},
	{Name: "1−Tᵈ", Text: "λd:num. " +
		"    vec_sub(real_sub, " +
		"        basis_vector(real_of_num(0), real_of_num(1), 0), " +
		"        basis_vector(real_of_num(0), real_of_num(1), d))"},
	{Name: "1−qᵈTᵈ", Text: "λd:num. " +
		"    vec_sub(real_sub, " +
		"        basis_vector(real_of_num(0), real_of_num(1), 0), " +
		"        vec_scalar_mul(real_mul, «q» ^ d, basis_vector(real_of_num(0), real_of_num(1), d)))"},
	{Name: "linearFactor", Text: "λr:complex. λn:num. " +
		"    COND(n = 0, complex_of_real(&1), COND(n = 1, complex_neg(r), complex_of_real(&0)))"},
	{Name: "denominator", Text: "λq:num. " +
		"    polynomial_mul(complex_add, " +
		"        complex_of_real(&0), " +
		"        complex_mul, " +
		"        «linearFactor»(complex_of_real(&1)), " +
		"        «linearFactor»(complex_of_real(&q)))"},
	{Name: "constants", Text: "λr:num. finite_constants(field_ring(M), card(k), r)"},
	{Name: "constantChart", Text: "λr:num. λS:set(A). " +
		"    constant_chart(field_ring(M), «constants»(r), S)"},
	{Name: "composite", Text: "λr:num. constant_composite(M, K, «constants»(r))"},
	{Name: "extendedEffective", Text: "λr:num. " +
		"    curve_effective_count(restrict_ring(field_ring(M), «composite»(r)), " +
		"        «constants»(r), " +
		"        «constantChart»(r, A₀), " +
		"        «constantChart»(r, A₁), " +
		"        «constantChart»(r, A₀₁))"},
	{Name: "extendedZeta", Text: "λr:num. λn:num. «extendedEffective»(r)(int_of_num(n))"},
	{Name: "extendedNumerator", Text: "λr:num. " +
		"    curve_zeta_numerator(restrict_ring(field_ring(M), «composite»(r)), " +
		"        «constants»(r), " +
		"        «constantChart»(r, A₀), " +
		"        «constantChart»(r, A₁), " +
		"        «constantChart»(r, A₀₁))"},
	{Name: "extendedCount", Text: "λr:num. " +
		"    curve_extension_count(field_ring(M), " +
		"        «constants»(r), " +
		"        «constantChart»(r, A₀), " +
		"        «constantChart»(r, A₁), " +
		"        «constantChart»(r, A₀₁))"},
})
