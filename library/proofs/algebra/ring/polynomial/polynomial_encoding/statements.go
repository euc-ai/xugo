// statements.go — the encoding's vocabulary: zero-padded ring tuples, the
// monomials of bounded dimension and degree with their fixed listing and
// slots, the coefficient count, the value of a polynomial at a tuple, with a
// polynomial in one variable read as one in the variable 0, and the
// definitions of the codes, the decoding and the encoding.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/listing"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// RingTupleDef — a finite tuple is carrier-valued below n and padded by the ring zero above it.
var RingTupleDef = ringTupleDefThm{family.Define(registry.DefEntry{
	Name: "RingTupleDef", Const: "ring_tuple", Type: "ring_ops(A) → num → (num → A) → bool",
	Key: "prop_4874c6afe5aea3f9",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀x:(num → A). " +
			"    ring_tuple(R, n, x) ⇔ vec⟨n⟩(R.zero, x) ∧ (∀i:num. i < n ⇒ x(i) ∈ R.carrier)",
	},
})}

// BoundedMonomialsDef — monomials in n variables of total degree at most d.
var BoundedMonomialsDef = boundedMonomialsDefThm{family.Define(registry.DefEntry{
	Name: "BoundedMonomialsDef", Const: "bounded_monomials", Type: "num → num → set(num → num)",
	Key: "prop_9c540199f849f6a6",
	Equations: []string{
		"∀n d:num. " +
			"    bounded_monomials(n, d) = " +
			"    {m:(num → num) | (∀i:num. n ≤ i ⇒ m(i) = 0) ∧ nat_sum({i:num | i < n}, m) ≤ d}",
	},
})}

// monomialListingDef — choose a distinct finite listing of the bounded monomials.
var monomialListingDef = monomialListingDefThm{family.Define(registry.DefEntry{
	Name: "monomialListingDef", Const: "monomial_listing", Type: "num → num → list(num → num)",
	Key: "prop_258de3a7fce0a498",
	Equations: []string{
		"∀n d:num. " +
			"    monomial_listing(n, d) = " +
			"    εl:list(num → num). " +
			"        list_distinct(l) ∧ {m:(num → num) | list_member(m, l)} = bounded_monomials(n, d)",
	},
	Deps: []registry.EntryLike{BoundedMonomialsDef},
})}

// monomialSlotDef — the position of a monomial in the fixed listing: an index below the listing's
// length at which the listing holds the monomial, specified only on the bounded monomials.
var monomialSlotDef = monomialSlotDefThm{family.Define(registry.DefEntry{
	Name: "monomialSlotDef", Const: "monomial_slot", Type: "num → num → (num → num) → num",
	Key: "prop_42b306be850713fa",
	Equations: []string{
		"∀n d:num. ∀m:(num → num). " +
			"    monomial_slot(n, d, m) = " +
			"    εj:num. j < list_length(monomial_listing(n, d)) ∧ list_nth(monomial_listing(n, d), j) = m",
	},
	Deps: []registry.EntryLike{monomialListingDef},
})}

// coefficientCountDef — the number of coefficient slots for a degree-bounded polynomial.
var coefficientCountDef = coefficientCountDefThm{family.Define(registry.DefEntry{
	Name: "coefficientCountDef", Const: "coefficient_count", Type: "num → num → num",
	Key:       "prop_67138189b3952a56",
	Equations: []string{"∀n d:num. coefficient_count(n, d) = list_length(monomial_listing(n, d))"},
	Deps:      []registry.EntryLike{monomialListingDef},
})}

// PolynomialBoundDef — a polynomial in n variables supported in total degree at most d.
var PolynomialBoundDef = polynomialBoundDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialBoundDef",
	Const: "polynomial_bound",
	Type:  "ring_ops(A) → num → num → ((num → num) → A) → bool",
	Key:   "prop_bef89828252ef47c",
	Equations: []string{
		"∀R:ring_ops(A). ∀n d:num. ∀p:((num → num) → A). " +
			"    polynomial_bound(R, n, d, p) ⇔ " +
			"    p ∈ polynomial_algebra(R, {i:num | i < n}) ∧ fun_support(R.zero, p) ⊆ bounded_monomials(n, d)",
	},
	Deps: []registry.EntryLike{BoundedMonomialsDef},
})}

// PolynomialValueDef — polynomial evaluation along the identity coefficient map.
var PolynomialValueDef = polynomialValueDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialValueDef",
	Const: "polynomial_value",
	Type:  "ring_ops(A) → ((num → num) → A) → (num → A) → A",
	Key:   "prop_eae4d92610c4f6b3",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:((num → num) → A). ∀x:(num → A). " +
			"    polynomial_value(R, p, x) = polynomial_algebra_eval(R, R, λa:A. a, x, p)",
	},
})}

// UnivariatePolynomialValue — a polynomial in one variable over a commutative ring is a polynomial
// in the variable 0 that takes, at every tuple whose first coordinate lies in the carrier, the
// polynomial's value at that coordinate: the polynomial with the constants p(i) as coefficients,
// evaluated at the variable 0 among the polynomials in that variable, is one of them, and
// evaluation at a tuple, a ring homomorphism, sends it to the value of p, each constant to itself
// and the variable to the first coordinate.
var UnivariatePolynomialValue = univariatePolynomialValueThm{family.Add(registry.ProofEntry{
	Name: "UnivariatePolynomialValue",
	Key:  "prop_c46735ec440f0ad2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀p:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "∃P:((num → num) → A). " +
			"    P ∈ polynomial_algebra(R, {i:num | i < 1}) ∧ " +
			"    (∀x:(num → A). x(0) ∈ R.carrier ⇒ polynomial_value(R, P, x) = polynomial_eval(p, x(0)))",
		Abbrev: Abbrev{
			{Name: "line", Text: "polynomial_algebra_ring(R, {i:num | i < 1})"},
			{Name: "constants", Text: "λi:num. polynomial_algebra_const(R, p(i))"},
			{Name: "P", Text: "polynomial_eval(«line».add, " +
				"    «line».zero, " +
				"    «line».mul, " +
				"    «line».one, " +
				"    «constants», " +
				"    polynomial_algebra_var(R, 0))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		p *Arrow[Nat, A],
		ring comm_ring.CommRingFact[on.R],
		over Fact,
	) {
		type multivariate = Fun[_Monomial, A]
		line := a.TermAs[RingOps[multivariate]]("«line»")
		variables := a.TermAs[Set[Nat]]("{i:num | i < 1}")
		origin := a.TermAs[Nat]("0")
		constants := a.TermAs[Fun[Nat, multivariate]]("«constants»")
		X := a.TermAs[multivariate]("polynomial_algebra_var(R, 0)")
		lineRing := a.Have(
			"the polynomials in the variable 0 form a commutative ring",
			"comm_ring_on(«line»)",
			By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn.At(R, variables)))
		embedding := a.Have(
			"the constants embed R in it",
			"ring_homomorphism(R, «line», polynomial_algebra_const(R))",
			By(ring, polynomial_algebra.PolynomialAlgebraConstHom.At(R, variables)))
		carrier := a.Have(
			"its carrier is the polynomials in the variable 0",
			"«line».carrier = polynomial_algebra(R, {i:num | i < 1})",
			Simp(Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
			Refl())
		variable := a.Have(
			"the variable 0 is one of them",
			"polynomial_algebra_var(R, 0) ∈ «line».carrier",
			carrier.Rw(),
			By(ring, polynomial_algebra.PolynomialAlgebraVarIn.At(R, variables, origin)))
		coefficients := a.Have(
			"the constants p(i) are the coefficients of a polynomial over it",
			"polynomial_over(«line».zero, «line».carrier, «constants»)",
			By(
				over,
				ring_homomorphism.MapZero.Read(embedding),
				ring_homomorphism.MapIn.Read(embedding),
				polynomial.PolynomialOverMap.At(
					a.TermAs[Fun[A, multivariate]]("polynomial_algebra_const(R)"),
					a.TermAs[A]("R.zero"),
					a.TermAs[multivariate]("«line».zero"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Set[multivariate]]("«line».carrier"),
					p)))
		evaluated := a.Have(
			"evaluation at the variable is a ring homomorphism from the polynomials over it",
			"ring_homomorphism(polynomial_ring(«line»), "+
				"    «line», "+
				"    λq:(num → (num → num) → A). "+
				"        polynomial_eval(«line».add, "+
				"            «line».zero, "+
				"            «line».mul, "+
				"            «line».one, "+
				"            q, "+
				"            polynomial_algebra_var(R, 0)))",
			By(variable, polynomial_evaluation.EvalHomomorphism.Read(lineRing).AsFact().At(X)))
		inLine := a.Have(
			"evaluation at the variable keeps the carrier, so «P» is a polynomial in the variable 0",
			"«P» ∈ polynomial_algebra(R, {i:num | i < 1})",
			carrier.RwRev(),
			By(
				variable,
				coefficients,
				evaluated,
				polynomial.PolynomialRingDef,
				ring_homomorphism.MapIn.Read(evaluated)))
		a.Take(a.TermAs[multivariate]("«P»"))
		values := a.Have(
			"at a tuple with a carrier value first, «P» takes the value of p there",
			Statement{
				Binders: "∀x:(num → A).",
				Hypotheses: []string{
					"x(0) ∈ R.carrier",
				},
				Conclusion: "polynomial_value(R, «P», x) = polynomial_eval(R.add, R.zero, R.mul, R.one, p, x(0))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, A]]("x")
				first := b.Assume()
				identity := b.TermAs[Fun[A, A]]("λa:A. a")
				evaluate := b.Have(
					"evaluation at x is a ring homomorphism from the polynomials in the variable 0 to R",
					"ring_homomorphism(«line», R, polynomial_algebra_eval(R, R, λa:A. a, x))",
					By(ring, first, polynomial_algebra_evaluation.TupleEvaluationHom.At(R, x)))
				back := b.Have(
					"evaluation at x sends each constant p(i) back to p(i)",
					"(λi:num. polynomial_algebra_eval(R, R, λa:A. a, x, polynomial_algebra_const(R, p(i)))) = p",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						c.Show(
							"a coefficient of p is a carrier value, and a constant evaluates to itself",
							By(
								over,
								polynomial.PolynomialOverDef,
								ring_homomorphism.RingHomIdentity.Read(ring),
								polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
									R, R, identity, x, c.TermAs[A]("p(i)"))))
					}))
				b.Show(
					"evaluation carries «P» to the value of the evaluated constants at the evaluated variable",
					Simp(Fwd(PolynomialValueDef)),
					By(
						evaluate,
						coefficients,
						variable,
						back,
						first,
						ring_homomorphism.RingHomIdentity.Read(ring),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(R, R, identity, x, origin),
						polynomial_evaluation.EvalAlongHomomorphism.At(
							line,
							R,
							b.TermAs[Fun[multivariate, A]]("polynomial_algebra_eval(R, R, λa:A. a, x)"),
							constants,
							X)))
			}))
		a.Show(
			"«P» is a polynomial in the variable 0 with the values of p",
			By(inLine, values))
	}),
})}

// polynomialCodeDef — an integer polynomial whose coefficient slots and coordinate slots are variables.
var polynomialCodeDef = polynomialCodeDefThm{family.Define(registry.DefEntry{
	Name:  "polynomialCodeDef",
	Const: "polynomial_code",
	Type:  "num → num → num → num → (num → num) → int",
	Key:   "prop_19fbbbe4baaea3d",
	Equations: []string{
		"∀n d c x:num. " +
			"    polynomial_code(n, d, c, x) = " +
			"    module_sum(fun_add(int_ring.add), fun_zero(int_ring.zero), bounded_monomials(n, d), «term»)",
	},
	Deps: []registry.EntryLike{BoundedMonomialsDef, monomialSlotDef},
})}

// univariateCodeDef — an integer polynomial in one coordinate slot whose coefficient slots are a
// block of n variables: the sum over i below n of the coefficient variable at c + i times the
// coordinate variable at x to the power i.
var univariateCodeDef = univariateCodeDefThm{family.Define(registry.DefEntry{
	Name: "univariateCodeDef", Const: "univariate_code", Type: "num → num → num → (num → num) → int",
	Key: "prop_8f93e1a0c0ea645e",
	Equations: []string{
		"∀n c x:num. " +
			"    univariate_code(n, c, x) = " +
			"    module_sum(fun_add(int_ring.add), " +
			"        fun_zero(int_ring.zero), " +
			"        {i:num | i < n}, " +
			"        λi:num. " +
			"            polynomial_algebra_mul(int_ring, " +
			"                polynomial_algebra_var(int_ring, c + i), " +
			"                monoid_pow(polynomial_algebra_mul(int_ring), " +
			"                    polynomial_algebra_one(int_ring), " +
			"                    polynomial_algebra_var(int_ring, x), " +
			"                    i)))",
	},
})}

// decodePolynomialDef — substitute a coefficient block to obtain a polynomial over the target ring.
var decodePolynomialDef = decodePolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "decodePolynomialDef",
	Const: "decode_polynomial",
	Type:  "ring_ops(A) → num → num → num → (num → A) → (num → num) → A",
	Key:   "prop_dd7a1fd5bb7b6939",
	Equations: []string{
		"∀R:ring_ops(A). ∀n d c:num. ∀ρ:(num → A). ∀m:(num → num). " +
			"    decode_polynomial(R, n, d, c, ρ, m) = " +
			"    COND(m ∈ bounded_monomials(n, d), ρ(c + monomial_slot(n, d, m)), R.zero)",
	},
	Deps: []registry.EntryLike{BoundedMonomialsDef, monomialSlotDef},
})}

// DecodePolynomialsDef — decode consecutive coefficient blocks from the slot c on, the j-th polynomial from the j-th block.
var DecodePolynomialsDef = decodePolynomialsDefThm{family.Define(registry.DefEntry{
	Name:  "DecodePolynomialsDef",
	Const: "decode_polynomials",
	Type:  "ring_ops(A) → num → num → num → (num → A) → num → (num → num) → A",
	Key:   "prop_5ea67a9818fda932",
	Equations: []string{
		"∀R:ring_ops(A). ∀n d c:num. ∀ρ:(num → A). ∀j:num. " +
			"    decode_polynomials(R, n, d, c, ρ, j) = " +
			"    decode_polynomial(R, n, d, c + j * coefficient_count(n, d), ρ)",
	},
	Deps: []registry.EntryLike{decodePolynomialDef, coefficientCountDef},
})}

// DecodeTupleDef — read a coordinate block as a zero-padded tuple.
var DecodeTupleDef = decodeTupleDefThm{family.Define(registry.DefEntry{
	Name:  "DecodeTupleDef",
	Const: "decode_tuple",
	Type:  "ring_ops(A) → num → num → (num → A) → num → A",
	Key:   "prop_80a70822167679db",
	Equations: []string{
		"∀R:ring_ops(A). ∀n x:num. ∀ρ:(num → A). ∀i:num. " +
			"    decode_tuple(R, n, x, ρ, i) = COND(i < n, ρ(x + i), R.zero)",
	},
})}

// EncodePolynomialDef — write a polynomial's coefficients into a block of an environment, slot by
// slot, and leave every other name as it was.
var EncodePolynomialDef = encodePolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "EncodePolynomialDef",
	Const: "encode_polynomial",
	Type:  "num → num → num → ((num → num) → A) → (num → A) → num → A",
	Key:   "prop_19675fbd66b80393",
	Equations: []string{
		"∀n d c:num. ∀p:((num → num) → A). ∀ρ:(num → A). ∀v:num. " +
			"    encode_polynomial(n, d, c, p, ρ, v) = " +
			"    COND(c ≤ v ∧ v < c + coefficient_count(n, d), " +
			"        p(εm:(num → num). m ∈ bounded_monomials(n, d) ∧ monomial_slot(n, d, m) = v - c), " +
			"        ρ(v))",
	},
	Deps: []registry.EntryLike{BoundedMonomialsDef, monomialSlotDef, coefficientCountDef},
})}

// BoundedMonomialsFinite — there are finitely many monomials in bounded dimension and degree: an
// exponent below n is one summand of the total degree, so at most d, and the exponents from n on
// are zero. A bounded monomial therefore lies below the corner monomial, d at each variable below n
// and zero from n on; the corner is supported below n, and a finitely supported monomial has
// finitely many monomials below it.
var BoundedMonomialsFinite = boundedMonomialsFiniteThm{family.Add(registry.ProofEntry{
	Name: "BoundedMonomialsFinite",
	Key:  "prop_d8b410be8aab0ed7",
	Build: family.Theorem(Statement{
		Binders:    "∀n d:num.",
		Conclusion: "finite(bounded_monomials(n, d))",
		Abbrev: Abbrev{
			{Name: "corner", Text: "λi:num. COND(i < n, d, 0)"},
			{Name: "box", Text: "{m:(num → num) | ∀i:num. m(i) ≤ COND(i < n, d, 0)}"},
		},
	},
		func(a *Argument, n, d *Expr[Nat]) {
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			boxFinite := a.Have(
				"the monomials below the corner form a finite box",
				"finite(«box»)",
				Derive(func(b *Argument) {
					nonzeroBelow := b.Have(
						"the corner is nonzero only at the variables below n",
						"fun_support(0, «corner») ⊆ {i:num | i < n}",
						BySets())
					cornerFinite := b.Have(
						"so the corner has finite support",
						"finite_support(0, «corner»)",
						By(
							nonzeroBelow,
							function_module.FiniteSupportDef,
							finite_set.FiniteSubset.At(b.TermAs[Set[Nat]]("fun_support(0, «corner»)"), below),
							num_segment.FiniteBelowStrict))
					b.Show(
						"a finitely supported monomial has finitely many monomials below it",
						By(cornerFinite, polynomial_algebra.MonomialsBelowFinite.At(b.TermAs[_Monomial]("«corner»"))))
				}))
			inBox := a.Have(
				"every bounded monomial lies in the box",
				"bounded_monomials(n, d) ⊆ «box»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					bounds := b.Conjuncts(
						b.Unfolded(b.Assume(), BoundedMonomialsDef),
						"m vanishes from n on",
						"and its exponents below n sum to at most d")
					vanishes, degree := bounds[0], bounds[1]
					exponents := b.Have(
						"below n an exponent of m is one summand of its total degree, and from n on it is zero",
						"∀i:num. m(i) ≤ COND(i < n, d, 0)",
						b.ForEach(func(i *Expr[Nat]) Action {
							return ByArith(
								vanishes.At(i),
								degree,
								nat_sum.TermLeSum.At(m, below, i),
								num_segment.FiniteBelowStrict.At(n))
						}))
					b.Show(
						"so m lies below the corner",
						By(exponents))
				}))
			a.Show(
				"a part of a finite set is finite",
				By(boxFinite, inBox, finite_set.FiniteSubset))
		}),
})}

// MonomialSlots — the fixed monomial listing gives distinct bounded coefficient slots: the bounded
// monomials are finitely many, so their enumeration lists each of them once, and the fixed listing
// is chosen among such lists. A member of a list stands at a position of it, so every bounded
// monomial has a slot, a position below the length of the listing at which the listing holds it,
// and two monomials at one slot are the one entry the listing holds there.
var MonomialSlots = monomialSlotsThm{family.Add(registry.ProofEntry{
	Name: "MonomialSlots",
	Key:  "prop_18324728245a81ea",
	Reading: "At dimension zero or degree zero there is one monomial, " +
		"the zero exponent function, so the coefficient count is one.",
	Build: family.Theorem(Statement{
		Binders: "∀n d:num.",
		Conclusion: "list_distinct(monomial_listing(n, d)) ∧ " +
			"{m:(num → num) | list_member(m, monomial_listing(n, d))} = bounded_monomials(n, d) ∧ " +
			"(∀m:(num → num). " +
			"    m ∈ bounded_monomials(n, d) ⇒ monomial_slot(n, d, m) < coefficient_count(n, d)) ∧ " +
			"injective_on(bounded_monomials(n, d), monomial_slot(n, d))",
		Abbrev: Abbrev{
			{Name: "enumeration", Text: "list_of_set(bounded_monomials(n, d))"},
		},
	},
		func(a *Argument, n, d *Expr[Nat]) {
			type monomialList = list.List[_Monomial]
			bounded := a.TermAs[Set[_Monomial]]("bounded_monomials(n, d)")
			fixed := a.TermAs[monomialList]("monomial_listing(n, d)")

			distinctLists := a.Have(
				"some list holds each bounded monomial once: the enumeration of the finitely many of them",
				"∃l:list(num → num). "+
					"    list_distinct(l) ∧ {m:(num → num) | list_member(m, l)} = bounded_monomials(n, d)",
				Derive(func(b *Argument) {
					enumeration := b.TermAs[monomialList]("«enumeration»")
					finite := BoundedMonomialsFinite.At(n, d)
					b.Take(enumeration)
					enumerated := b.Have(
						"the enumeration lists the bounded monomials and is as long as they are many",
						"set_of_list(«enumeration») = bounded_monomials(n, d) ∧ "+
							"list_length(«enumeration») = card(bounded_monomials(n, d))",
						By(listing.ListOfSetProperties.At(bounded), finite))
					distinct := b.Have(
						"a list whose set has as many points as the list is long repeats nothing",
						"list_distinct(«enumeration»)",
						By(
							enumerated,
							listing.HasSizeSetOfListIffDistinct.At(enumeration),
							cardinality.HasSizeDef.At(bounded, b.TermAs[Nat]("list_length(«enumeration»)")),
							finite))
					members := b.Have(
						"the members of the enumeration are the points of its set",
						"{m:(num → num) | list_member(m, «enumeration»)} = bounded_monomials(n, d)",
						Simp(Rev(listing.InSetOfList)),
						BySets(enumerated))
					b.Show(
						"so the enumeration is such a list",
						By(distinct, members))
				}))
			listed := a.Conjuncts(
				a.Have(
					"the fixed listing is chosen among those lists, so it is one of them",
					"list_distinct(monomial_listing(n, d)) ∧ "+
						"{m:(num → num) | list_member(m, monomial_listing(n, d))} = bounded_monomials(n, d)",
					By(HilbertDenoted, distinctLists, monomialListingDef.At(n, d))),
				"the listing repeats nothing",
				"and its members are the bounded monomials")

			slotted := a.Have(
				"every bounded monomial is the entry of the listing at its slot, a position of the listing",
				Statement{
					Binders: "∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ bounded_monomials(n, d)",
					},
					Conclusion: "monomial_slot(n, d, m) < list_length(monomial_listing(n, d)) ∧ " +
						"list_nth(monomial_listing(n, d), monomial_slot(n, d, m)) = m",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					inListing := b.Have(
						"m is a member of the listing",
						"list_member(m, monomial_listing(n, d))",
						BySets(b.Assume(), listed[1]))
					b.Show(
						"so it stands at a position of the listing, and the slot of m is chosen among its positions",
						By(inListing, list.MemberNth.At(m, fixed), monomialSlotDef.At(n, d, m)))
				}))
			below := a.Have(
				"so a slot is less than the coefficient count, the length of the listing",
				"∀m:(num → num). m ∈ bounded_monomials(n, d) ⇒ monomial_slot(n, d, m) < coefficient_count(n, d)",
				By(Normalized, slotted, coefficientCountDef.At(n, d)))
			injective := a.Have(
				"two bounded monomials with one slot are the one entry the listing holds there",
				"injective_on(bounded_monomials(n, d), monomial_slot(n, d))",
				Unfold(functions.InjectiveOnDef),
				By(slotted))
			a.Show(
				"the listing is distinct and lists the bounded monomials, "+
					"and their slots lie below the count and tell them apart",
				By(listed[0], listed[1], below, injective))
		}),
})}

// BoundedMonomialsAreMonomials — a bounded monomial is a monomial of the
// variables below n: its exponents vanish from n on, so its support lies
// below n and is finite.
var BoundedMonomialsAreMonomials = boundedMonomialsAreMonomialsThm{family.Add(registry.ProofEntry{
	Name: "BoundedMonomialsAreMonomials",
	Key:  "prop_b849f86091383f15",
	Build: family.Theorem("∀n d:num. bounded_monomials(n, d) ⊆ monomials({i:num | i < n})",
		func(a *Argument, n, d *Expr[Nat]) {
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			a.Do(Unfold(set_basic.SubsetDef))
			m := a.FixAs[_Monomial]("m")
			bounds := a.Conjuncts(
				a.Unfolded(a.Assume(), BoundedMonomialsDef),
				"m vanishes from n on",
				"and its total degree is at most d")
			support := a.Have(
				"so the support of m lies below n",
				"fun_support(0, m) ⊆ {i:num | i < n}",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inSupport := b.Assume()
					b.Show(
						"an exponent of m that is nonzero is below n",
						ByArith(bounds[0].At(i), inSupport))
				}))
			a.Show(
				"a finitely supported exponent function supported below n is a monomial of those variables",
				By(
					support,
					finite_set.FiniteSubset.At(a.TermAs[Set[Nat]]("fun_support(0, m)"), below),
					num_segment.FiniteBelowStrict.At(n),
					polynomial_algebra.MonomialsMember.At(below, m)))
		}),
})}
