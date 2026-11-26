package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_class_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// FractionalIdealInvertibleIffBounded — when every nonzero integral ideal
// of S is invertible, the invertible fractional ideals are the bounded
// ones: an invertible ideal holds a nonzero principal ideal and has a
// common denominator, and a denominator scales a bounded ideal to a
// nonzero integral one, from which the nonzero scalar comes back off.
var FractionalIdealInvertibleIffBounded = fractionalIdealInvertibleIffBoundedThm{family.Add(registry.ProofEntry{
	Name: "FractionalIdealInvertibleIffBounded",
	Key:  "prop_9822432d9599ac5a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    invertible_fractional(field_ring(L), S, H)",
		},
		Conclusion: "invertible_fractional(field_ring(L), S, I) ⇔ bounded_fractional(field_ring(L), S, I)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, I *Expr[Set[A]],
		subring, fractions, idealsInvertible Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		inField := a.Have(
			"S lies in the field",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		a.Iff()
		a.Forward(
			"an invertible ideal is nonzero and has a common denominator",
			func(b *Argument, invertible Fact) {
				fractional := b.Conjuncts(
					b.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
					"I is an S-submodule of L",
					"whose product with its inverse is S")[0]
				c, principal := b.ObtainAs[A](
					"I holds a nonzero principal ideal c · S",
					"∃c:A. c ∈ S ∧ c ≠ L.zero ∧ image(L.mul(c), S) ⊆ I",
					By(
						invertible_fractional_ideal.InvertibleContainsPrincipal.Read(L).At(S, I),
						subring,
						fractions,
						invertible))
				nonzero := b.Have(
					"1 lies in S, so I holds the nonzero c = c * 1",
					"I ≠ {L.zero}",
					BySets(
						principal,
						inField,
						comm_ring.SubringOne.Read(subring),
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))).AsFact().At(c)))
				b.Show(
					"I is a nonzero fractional ideal with a common denominator",
					By(
						fractional,
						nonzero,
						invertible_fractional_ideal.InvertibleCommonDenominator.Read(L).At(S, I),
						subring,
						fractions,
						invertible,
						integral_element.BoundedFractionalDef.At(fieldRing, S, I)))
			})
		a.Backward(
			"clear a denominator to a nonzero integral ideal and undo the scalar",
			func(b *Argument, bounded Fact) {
				parts := b.Conjuncts(
					b.Unfolded(bounded, integral_element.BoundedFractionalDef),
					"I is an S-submodule of L",
					"I is not zero",
					"some nonzero d of S carries I into S")
				fractional, nonzero := parts[0], parts[1]
				d, denominator := b.UnpackAs[A](parts[2])
				dInField := b.Have(
					"the denominator lies in the field",
					"d ∈ L.carrier",
					BySets(denominator, inField))
				iInField := b.Have(
					"I lies in the field",
					"I ⊆ L.carrier",
					By(submodule.SubmoduleSubset.Read(fractional)))
				scaled := b.TermAs[Set[A]]("image(L.mul(d), I)")
				scaledFractional := b.Have(
					"scaling keeps a fractional ideal",
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), image(L.mul(d), I))",
					By(subring, dInField, fractional, fractional_ideal.ScaleSubmodule.Read(L).AsFact().At(S, I, d)))
				ideal := b.Have(
					"the scaled fractional ideal lies in S, so it is an integral ideal",
					"ring_ideal(restrict_ring(field_ring(L), S), image(L.mul(d), I))",
					By(
						subring,
						denominator,
						scaledFractional,
						fractional_ideal.IntegralIdealFractional.Read(L).At(S, scaled)))
				e, eData := b.ObtainAs[A](
					"a submodule other than zero holds a nonzero element",
					"∃e:A. e ∈ I ∧ e ≠ L.zero",
					BySets(nonzero, submodule.SubmoduleZero.Read(fractional)))
				scaledNonzero := b.Have(
					"the field has no zero divisors, so the scaled ideal holds the nonzero d * e",
					"image(L.mul(d), I) ≠ {L.zero}",
					BySets(dInField, iInField, denominator, eData, field.MulEqZeroOn.Read(L).AsFact().At(d, e)))
				invertibleScaled := b.Have(
					"the hypothesis makes this nonzero integral ideal invertible",
					"invertible_fractional(field_ring(L), S, image(L.mul(d), I))",
					By(ideal, scaledNonzero, idealsInvertible.At(scaled)))
				b.Show(
					"nonzero scaling preserves invertibility",
					By(
						subring,
						dInField,
						denominator,
						iInField,
						invertibleScaled,
						fractional_ideal.InvertibleScale.Read(L).AsFact().At(S, I, d)))
			})
	}),
})}

// InvertibleIdealsIntegrallyClosed — a subring of L whose field of fractions
// is L and whose nonzero ideals are all invertible is integrally closed in L.
// For z integral over S, finitely many powers of z span S[z], so one nonzero
// denominator clears S[z] into S: S[z] is a bounded fractional ideal, hence
// invertible, and z, multiplying S[z] into itself, lies in the ring of
// multipliers of an invertible ideal, which is S.
var InvertibleIdealsIntegrallyClosed = invertibleIdealsIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIdealsIntegrallyClosed",
	Key:  "prop_1173d3fb25c11306",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"∀I:set(A). ring_ideal(«R», I) ∧ I ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), S, I)",
		},
		Conclusion: "integrally_closed_in(«R», L.carrier)",
		Abbrev: Abbrev{
			// The powers of z below the degree of p: z and its monic polynomial p
			// are bound by the proof, the integral element and its equation.
			{Name: "powers", Text: "{monoid_pow(L.mul, L.one, z, i) | i:num | i < polynomial_degree(p)}"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		subring, fractions, idealsInvertible Fact,
	) {
		a.Show(
			"an element of L integral over S lies in S",
			Unfold(integral_element.IntegrallyClosedDef),
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				given := b.Conjuncts(
					b.Assume(),
					"z lies in L",
					"z is integral over S")
				zIn, integral := given[0], given[1]
				zm := b.MemberOf[on.L](z, zIn)
				p, relation := b.UnpackAs[Fun[Nat, A]](b.Unfolded(integral, integral_element.IntegralOverDef), "p")
				adjoined := b.TermAs[Set[A]]("polynomial_image(field_ring(L), S, z)")
				powers := b.TermAs[Set[A]]("«powers»")
				spanned := b.Have(
					"the powers of z below the degree of p span S[z]",
					"polynomial_image(field_ring(L), S, z) ⊆ module_span(«R», regular_module(field_ring(L)), «powers»)",
					BySets(subring, relation, integral_element.IntegralPowerSpan.Read(L).At(S, zm, p)))
				finitePowers := b.Have(
					"there are finitely many such powers",
					"finite(«powers»)",
					Derive(func(c *Argument) {
						segmentImage := c.Have(
							"they are the image of an initial segment of the exponents",
							"«powers» = image(λi:num. monoid_pow(L.mul, L.one, z, i), {i:num | i < polynomial_degree(p)})",
							BySets())
						c.Show(
							"a finite image is finite",
							segmentImage.Rw(),
							By(num_segment.FiniteBelowStrict, finite_set.FiniteImage))
					}))
				powersIn := b.Have(
					"the powers of z lie in L",
					"«powers» ⊆ L.carrier",
					BySets(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))), zIn))
				cleared := b.Have(
					"one nonzero denominator in S clears all of S[z] into S",
					"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), polynomial_image(field_ring(L), S, z)) ⊆ S",
					By(
						subring,
						fractions,
						finitePowers,
						powersIn,
						spanned,
						fractional_ideal.SubringSubmodule.Read(L).At(S),
						integral_element.FiniteSpanCommonDenominator.Read(L).At(S, S, powers, adjoined)))
				adjoinedRing := b.Conjuncts(
					GroupPremises(subring, algebraic_element.PolynomialImageSubring.Read(L).At(S, zm)),
					"S[z] is a subring of L",
					"S lies in S[z]",
					"z lies in S[z]")
				nonzero := b.Have(
					"S[z] holds one, so it is not {zero}",
					"polynomial_image(field_ring(L), S, z) ≠ {L.zero}",
					BySets(comm_ring.SubringOne.Read(adjoinedRing[0]), field.OneNotZeroOn.Read(L)))
				bounded := b.Have(
					"S[z] is a bounded fractional ideal of S",
					"bounded_fractional(field_ring(L), S, polynomial_image(field_ring(L), S, z))",
					By(
						nonzero,
						cleared,
						subring,
						integral_element.BoundedFractionalDef,
						integral_element.PolynomialImageSubmodule.Read(L).At(S, zm)))
				invertible := b.Have(
					"so S[z] is invertible",
					"invertible_fractional(field_ring(L), S, polynomial_image(field_ring(L), S, z))",
					By(
						subring,
						fractions,
						idealsInvertible,
						bounded,
						FractionalIdealInvertibleIffBounded.Read(L).At(S, adjoined)))
				b.Show(
					"z multiplies the invertible S[z] into itself, so z lies in its ring of multipliers, which is S",
					BySets(
						comm_ring.SubringMul.Read(adjoinedRing[0]),
						subring,
						invertible,
						zIn,
						adjoinedRing[2],
						invertible_fractional_ideal.InvertibleSelfColon.Read(L).At(S, adjoined)))
			}))
	}),
})}

var FractionalExponentArithmetic = fractionalExponentArithmeticThm{family.Add(registry.ProofEntry{
	Name: "FractionalExponentArithmetic",
	Key:  "prop_9f6f04b3b975990b",
	Deps: []registry.EntryLike{
		fractionalExponentProductDef,
		maximalExponentVectorsDef,
		IdealContainmentByExponents,
		FractionalIdealInvertibleIffBounded,
		NonzeroIdealInvertible,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀v w:(set(A) → int).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite_ideal_height(restrict_ring(field_ring(L), S), H)",
			"∀m:set(A). " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ m ≠ {L.zero} ⇒ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"v ∈ maximal_exponent_vectors(restrict_ring(field_ring(L), S))",
			"w ∈ maximal_exponent_vectors(restrict_ring(field_ring(L), S))",
		},
		Conclusion: "bounded_fractional(field_ring(L), " +
			"    S, " +
			"    fractional_exponent_product(field_ring(L), S, v)) ∧ " +
			"fractional_mul(field_ring(L), " +
			"    S, " +
			"    fractional_exponent_product(field_ring(L), S, v), " +
			"    fractional_exponent_product(field_ring(L), S, w)) = " +
			"fractional_exponent_product(field_ring(L), S, λm:set(A). v(m) + w(m)) ∧ " +
			"fractional_inverse(field_ring(L), S, fractional_exponent_product(field_ring(L), S, v)) = " +
			"fractional_exponent_product(field_ring(L), S, λm:set(A). -v(m)) ∧ " +
			"(ring_ideal(restrict_ring(field_ring(L), S), " +
			"        fractional_exponent_product(field_ring(L), S, v)) ⇔ " +
			"    ∀m:set(A). 0 ≤ v(m))",
	},
		"Split positive and negative exponents into integral products and cancel common maximal "+
			"factors. Integral containment is exactly nonnegativity, by the exponent containment theorem."),
})}

var FractionalExponentsUnique = fractionalExponentsUniqueThm{family.Add(registry.ProofEntry{
	Name: "FractionalExponentsUnique",
	Key:  "prop_59111e1dfd45c52f",
	Deps: []registry.EntryLike{
		FractionalExponentArithmetic,
		fractionalExponentsDef,
		IdealFactorizationExists,
		IdealFactorizationUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite_ideal_height(restrict_ring(field_ring(L), S), H)",
			"∀m:set(A). " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ m ≠ {L.zero} ⇒ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"bounded_fractional(field_ring(L), S, I)",
		},
		Conclusion: "fractional_exponents(field_ring(L), S, I) ∈ " +
			"maximal_exponent_vectors(restrict_ring(field_ring(L), S)) ∧ " +
			"fractional_exponent_product(field_ring(L), S, fractional_exponents(field_ring(L), S, I)) = I ∧ " +
			"(∀v:(set(A) → int). " +
			"    v ∈ maximal_exponent_vectors(restrict_ring(field_ring(L), S)) ∧ " +
			"    fractional_exponent_product(field_ring(L), S, v) = I ⇒ " +
			"    v = fractional_exponents(field_ring(L), S, I))",
	},
		"Clear a common denominator and subtract the exponent functions of the "+
			"resulting integral ideal and denominator ideal. Clear negative exponents "+
			"in any competing representation and invoke integral uniqueness."),
})}

var FractionalIdealsFreeAbelian = fractionalIdealsFreeAbelianThm{family.Add(registry.ProofEntry{
	Name: "FractionalIdealsFreeAbelian",
	Key:  "prop_ec07c2ec2f6e58be",
	Deps: []registry.EntryLike{
		FractionalExponentsUnique,
		FractionalExponentArithmetic,
		ideal_class_group.InvertibleIdealsAbelianGroup,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite_ideal_height(restrict_ring(field_ring(L), S), H)",
			"∀m:set(A). " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ m ≠ {L.zero} ⇒ " +
				"    invertible_fractional(field_ring(L), S, m)",
		},
		Conclusion: "group_isomorphism(mk_group(fractional_mul(field_ring(L), S), " +
			"        S, " +
			"        fractional_inverse(field_ring(L), S), " +
			"        invertible_ideals(field_ring(L), S)), " +
			"    mk_group(λv:(set(A) → int). λw:(set(A) → int). λm:set(A). v(m) + w(m), " +
			"        λm:set(A). 0, " +
			"        λv:(set(A) → int). λm:set(A). -v(m), " +
			"        maximal_exponent_vectors(restrict_ring(field_ring(L), S))), " +
			"    fractional_exponents(field_ring(L), S))",
	},
		"The unique finite integer exponent function is inverse to the product map. Product and "+
			"inverse laws make this bijection an isomorphism with the direct sum of copies of Z."),
})}
