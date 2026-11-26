// fraction_field.go — the field of fractions of an integral domain: the
// ring of fractions with every nonzero denominator, its inverse, and
// the embedding of the domain into it; inside a field, a one-to-one ring
// map out of a subring extends to the subfield of its fractions.

package ring_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The inverse of a fraction, and the field of fractions
// ---------------------------------------------------------------------------

// FractionInvDef — `fraction_inv(zero, mul, one, c, s, X)`: the pairs of
// X turned round, the class of u / r for the class of r / u; the zero
// class is sent to itself, as a field's convention asks. At a class
// r / u with r and u nonzero in an integral domain the turned pairs are
// exactly the class of u / r (FractionInvClass); elsewhere they are a
// set nothing is said about.
var FractionInvDef = fractionInvDefThm{family.Define(registry.DefEntry{
	Name:     "FractionInvDef",
	Key:      "prop_24f2f5c913a1305a",
	Const:    "fraction_inv",
	Type:     "A → (A → A → A) → A → set(A) → set(A) → set(prod(A, A)) → set(prod(A, A))",
	Implicit: []string{"zero", "mul", "one"},
	Equations: []string{
		"∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀c s:set(A). ∀X:set(prod(A, A)). " +
			"    fraction_inv(zero, mul, one, c, s, X) = " +
			"    COND(X = fraction_zero(zero, mul, one, c, s), " +
			"        fraction_zero(zero, mul, one, c, s), " +
			"        {(y, x) | x:A, y:A | (x, y) ∈ X})",
	},
	Deps: []registry.EntryLike{FractionZeroDef},
})}

// FractionDivDef — `fraction_div(zero, mul, one, c, s, X, Y)`: X times
// the inverse of Y.
var FractionDivDef = fractionDivDefThm{family.Define(registry.DefEntry{
	Name:  "FractionDivDef",
	Key:   "prop_4a2e033b303e3da0",
	Const: "fraction_div",
	Type: "A → " +
		"(A → A → A) → " +
		"A → " +
		"set(A) → " +
		"set(A) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A))",
	Implicit: []string{"zero", "mul", "one"},
	Equations: []string{
		"∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀c s:set(A). ∀X Y:set(prod(A, A)). " +
			"    fraction_div(zero, mul, one, c, s, X, Y) = " +
			"    fraction_mul(mul, c, s, X, fraction_inv(zero, mul, one, c, s, Y))",
	},
	Deps: []registry.EntryLike{FractionMulDef, FractionInvDef},
})}

// FractionFieldDef — `fraction_field(zero, mul, c)`: the fractions of c
// with every nonzero member as a denominator, the field of fractions of
// an integral domain.
var FractionFieldDef = fractionFieldDefThm{family.Define(registry.DefEntry{
	Name:     "FractionFieldDef",
	Key:      "prop_14e1cde4e9e0861b",
	Const:    "fraction_field",
	Type:     "A → (A → A → A) → set(A) → set(set(prod(A, A)))",
	Implicit: []string{"zero", "mul"},
	Equations: []string{
		"∀zero:A. ∀mul:(A → A → A). ∀c:set(A). " +
			"    fraction_field(zero, mul, c) = ring_localization(mul, c, c ∖ {zero})",
	},
	Deps: []registry.EntryLike{RingLocalizationDef},
})}

// FractionFieldRecordDef — `fraction_field_record(R)`: the fractions of
// R with every nonzero denominator as a field record, its eight
// operations on the classes fraction_field(R.zero, R.mul, R.carrier).
var FractionFieldRecordDef = fractionFieldRecordDefThm{family.Define(registry.DefEntry{
	Name:  "FractionFieldRecordDef",
	Key:   "prop_98fcd4a3f191b4f7",
	Const: "fraction_field_record",
	Type:  "ring_ops(A) → field_ops(set(prod(A, A)))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    fraction_field_record(R) = " +
			"    mk_field(fraction_add(R.add, R.mul, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_zero(R.zero, R.mul, R.one, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_neg(R.neg, R.mul, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_mul(R.mul, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_one(R.mul, R.one, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_sub(R.add, R.neg, R.mul, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_inv(R.zero, R.mul, R.one, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_div(R.zero, R.mul, R.one, R.carrier, R.carrier ∖ {R.zero}), " +
			"        fraction_field(R.zero, R.mul, R.carrier))",
	},
	Deps: []registry.EntryLike{
		FractionFieldDef,
		FractionAddDef,
		FractionZeroDef,
		FractionNegDef,
		FractionMulDef,
		FractionOneDef,
		FractionSubDef,
		FractionInvDef,
		FractionDivDef,
	},
})}

// NonzeroMultiplicative — in an integral domain the nonzero members form
// a multiplicative set: one is nonzero, and a product of nonzero members
// is nonzero.
var NonzeroMultiplicative = nonzeroMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "NonzeroMultiplicative",
	Key:  "prop_cfa02e320da86ef7",
	Reading: "In the zero ring the nonzero members are empty and hold no one; " +
		"where zero divisors exist a product of two nonzero members can be zero.",
	Build: integral_domain.IntegralDomainOn.Law("multiplicative_set(R.carrier, «nonzero»(R))",
		func(a *Argument, R integral_domain.IntegralDomainFact[on.R]) {
			ring := integral_domain.Ring.Read(R)
			a.Do(Unfold(MultiplicativeSetDef), SplitConjAll(
				Case(
					"the nonzero members lie in the carrier",
					BySets()),
				Case(
					"one lies in the carrier and is nonzero",
					BySets(comm_ring.OneIn.Read(ring), integral_domain.OneNotZero.Read(R))),
				Case(
					"the product of two nonzero members is nonzero",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						nonzero := b.Assume()
						b.Show(
							"the carrier is closed under the product and no factor can vanish",
							BySets(
								nonzero,
								comm_ring.MulIn.Read(ring).AsFact().At(u, v),
								integral_domain.NoZeroDivisors.Read(R).AsFact().At(u, v)))
					})),
			))
		}),
})}

// DomainFractionClassMember — in the fractions of an integral domain a
// pair lies in the class of (r, u) exactly when both its parts lie in the
// carrier, its denominator is nonzero and its cross product with (r, u) agrees: the witness of the fraction
// relation cancels, and one witnesses it back.
var DomainFractionClassMember = domainFractionClassMemberThm{family.Add(registry.ProofEntry{
	Name: "DomainFractionClassMember",
	Key:  "prop_7d3f075377c0d509",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders:    "∀r u x y:A.",
		Hypotheses: []string{"r ∈ R.carrier", "u ∈ R.carrier"},
		Conclusion: "(x, y) ∈ fraction_class(R.carrier, «nonzero»(R), r, u) ⇔ " +
			"x ∈ R.carrier ∧ y ∈ R.carrier ∧ y ≠ R.zero ∧ r * y = x * u",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		r, u *Member[A, on.R],
		x, y *Expr[A],
	) {
		ring := integral_domain.Ring.Read(R)
		member := a.Simplified(FractionClassMember.At(
			a.TermAs[Op[A]]("R.mul"), a.TermAs[Set[A]]("R.carrier"),
			a.TermAs[Set[A]]("«nonzero»(R)"), r, u, x, y))
		a.Iff()
		a.Forward(
			"Cancel the nonzero witness in the cross product",
			func(b *Argument, inClass Fact) {
				t, witnessed := b.ObtainAs[A](
					"The fraction relation supplies a nonzero witness",
					"∃t:A. t ∈ «nonzero»(R) ∧ t * (r * y) = t * (x * u)",
					By(member, inClass))
				parts := b.Conjuncts(
					b.Have(
						"The components and the witness lie in the carrier",
						"x ∈ R.carrier ∧ y ∈ R.carrier ∧ y ≠ R.zero ∧ t ∈ R.carrier ∧ t ≠ R.zero",
						BySets(member, inClass, witnessed)),
					"x lies in the carrier",
					"y lies in the carrier",
					"the denominator is nonzero",
					"the witness lies in the carrier",
					"the witness is nonzero")
				xm := b.MemberOf[on.R](x, parts[0])
				ym := b.MemberOf[on.R](y, parts[1])
				tm := b.MemberOf[on.R](t, parts[3])
				b.Show(
					"Cancellation leaves equality of the cross products",
					By(
						parts[2],
						parts[4],
						witnessed,
						integral_domain.MulCancelLeft.Read(R).At(tm,
							comm_ring.MulIn.Read(ring).At(r, ym), comm_ring.MulIn.Read(ring).At(xm, u))))
			})
		a.Backward(
			"One witnesses the fraction relation",
			func(b *Argument, cross Fact) {
				b.Do(Simp(Fwd(FractionClassMember)), SplitConjAll(
					Case(
						"The numerator lies in the carrier",
						By(cross)),
					Case(
						"The denominator is a nonzero member of the carrier",
						BySets(cross)),
					Case(
						"One is the witness",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[A]("R.one"))
							c.Show(
								"One is a nonzero member of the carrier and keeps the equation",
								BySets(cross, comm_ring.OneIn.Read(ring), integral_domain.OneNotZero.Read(R)))
						})),
				))
			})
	}),
})}

// DomainFractionZeroIff — in the fractions of an integral domain a class
// is zero exactly when its numerator is: a nonzero denominator annihilates
// the numerator only if the numerator vanishes, and one annihilates a zero
// numerator.
var DomainFractionZeroIff = domainFractionZeroIffThm{family.Add(registry.ProofEntry{
	Name: "DomainFractionZeroIff",
	Key:  "prop_912bb555945bc5ae",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders:    "∀r u:A.",
		Hypotheses: []string{"r ∈ R.carrier", "u ∈ R.carrier", "u ≠ R.zero"},
		Conclusion: "fraction_class(R.carrier, «nonzero»(R), r, u) = " +
			"fraction_zero(R.carrier, «nonzero»(R)) ⇔ " +
			"r = R.zero",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		r, u *Member[A, on.R],
		nonzero Fact,
	) {
		ring := integral_domain.Ring.Read(R)
		criterion := a.Have(
			"The class is zero exactly when a nonzero denominator annihilates the numerator",
			"fraction_class(R.carrier, «nonzero»(R), r, u) = fraction_zero(R.carrier, «nonzero»(R)) ⇔ "+
				"∃t:A. t ∈ «nonzero»(R) ∧ t * r = R.zero",
			BySets(
				NonzeroMultiplicative.Read(R),
				nonzero,
				FractionZeroIff.Read(ring).At(a.TermAs[Set[A]]("«nonzero»(R)"), r, u)))
		a.Iff()
		a.Forward(
			"A nonzero annihilator leaves the numerator zero",
			func(b *Argument, isZero Fact) {
				t, annihilates := b.ObtainAs[A](
					"The zero criterion supplies an annihilating denominator",
					"∃t:A. t ∈ «nonzero»(R) ∧ t * r = R.zero",
					By(criterion, isZero))
				b.Show(
					"A vanishing product with a nonzero factor has its other factor zero",
					BySets(annihilates, r, integral_domain.NoZeroDivisors.Read(R).AsFact().At(t, r)))
			})
		a.Backward(
			"One annihilates a zero numerator",
			func(b *Argument, isZero Fact) {
				one := b.MemberOf[on.R](b.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
				b.Show(
					"The zero criterion is witnessed by one",
					BySets(
						criterion,
						isZero,
						integral_domain.OneNotZero.Read(R),
						comm_ring.MulRightZeroOn.Read(ring).At(one)))
			})
	}),
})}

// DomainFractionEqIff — in the fractions of an integral domain two classes
// are equal exactly when the cross products of their pairs agree: (r', u')
// lies in its own class, and membership of the class of (r, u) is the cross
// product (DomainFractionClassMember); agreeing cross products have one
// class (FractionClassCross).
var DomainFractionEqIff = domainFractionEqIffThm{family.Add(registry.ProofEntry{
	Name: "DomainFractionEqIff",
	Key:  "prop_c4b0dc1eda43516a",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀r u r' u':A.",
		Hypotheses: []string{
			"r ∈ R.carrier",
			"u ∈ R.carrier",
			"r' ∈ R.carrier",
			"u' ∈ R.carrier",
			"u ≠ R.zero",
			"u' ≠ R.zero",
		},
		Conclusion: "fraction_class(R.carrier, «nonzero»(R), r, u) = " +
			"fraction_class(R.carrier, «nonzero»(R), r', u') ⇔ " +
			"r * u' = r' * u",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		r, u, r2, u2 *Member[A, on.R],
		nonzero Fact,
	) {
		ring := integral_domain.Ring.Read(R)
		denominators := a.TermAs[Set[A]]("«nonzero»(R)")
		a.Iff()
		a.Forward(
			"(r', u') lies in its own class, and so in the class of (r, u)",
			func(b *Argument, equal Fact) {
				b.Show(
					"Membership of the class of (r, u) is the cross product",
					By(
						equal,
						nonzero,
						DomainFractionClassMember.Read(R).At(r2, u2, r2, u2),
						DomainFractionClassMember.Read(R).At(r, u, r2, u2)))
			})
		a.Backward(
			"Agreeing cross products have one class",
			func(b *Argument, cross Fact) {
				b.Show(
					"One witnesses the fraction relation",
					BySets(
						cross,
						nonzero,
						NonzeroMultiplicative.Read(R),
						FractionClassCross.Read(ring).At(denominators, r, u, r2, u2)))
			})
	}),
})}

// FractionInvClass — the inverse of the class of r / u, both nonzero, is
// the class of u / r: a pair (x, y) is equivalent to (r, u) exactly when
// r * y = x * u, a domain cancelling the witness, and that is the same
// condition for (y, x) against (u, r) once x is a denominator. That is
// the one step that is not formal: r and y being nonzero, r * y = x * u
// makes x nonzero, where r's hypothesis is spent; u's does the same for
// y on the way back.
var FractionInvClass = fractionInvClassThm{family.Add(registry.ProofEntry{
	Name: "FractionInvClass",
	Key:  "prop_e827001672c940c",
	Reading: "Both hypotheses are needed: with r = R.zero the left side is the zero class " +
		"while u / r is ∅, and with u = R.zero the class r / u is ∅, which turns round to ∅.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀r u:A.",
		Hypotheses: []string{
			"r ∈ R.carrier",
			"u ∈ R.carrier",
			"r ≠ R.zero",
			"u ≠ R.zero",
		},
		Conclusion: "fraction_inv(R.carrier, " +
			"    «nonzero»(R), " +
			"    fraction_class(R.carrier, «nonzero»(R), r, u)) = " +
			"fraction_class(R.carrier, «nonzero»(R), u, r)",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		r, u *Member[A, on.R],
		nonzero Fact,
	) {
		ring := integral_domain.Ring.Read(R)
		monoid := comm_ring.MulMonoidOn.Read(ring)
		turnRound := a.Have(
			"A pair of the class of p / q, turned round, lies in the class of q / p when p is nonzero",
			Statement{
				Binders: "∀p q x y:A.",
				Hypotheses: []string{
					"p ∈ R.carrier",
					"q ∈ R.carrier",
					"p ≠ R.zero",
					"(x, y) ∈ fraction_class(R.carrier, «nonzero»(R), p, q)",
				},
				Conclusion: "(y, x) ∈ fraction_class(R.carrier, «nonzero»(R), q, p)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[A]("p")
				q := b.FixAs[A]("q")
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				parts := b.Conjuncts(
					b.Assume(),
					"p lies in the carrier",
					"q lies in the carrier",
					"p is nonzero",
					"(x, y) lies in the class of p / q")
				pm := b.MemberOf[on.R](p, parts[0])
				qm := b.MemberOf[on.R](q, parts[1])
				pNonzero, inClass := parts[2], parts[3]
				cross := b.Have(
					"The cross products of (x, y) and (p, q) agree",
					"x ∈ R.carrier ∧ y ∈ R.carrier ∧ y ≠ R.zero ∧ p * y = x * q",
					By(inClass, DomainFractionClassMember.Read(R).At(pm, qm, x, y)))
				xNonzero := b.Have(
					"x is nonzero, as p and y are",
					"x ≠ R.zero",
					By(
						Normalized,
						pm,
						qm,
						pNonzero,
						cross,
						integral_domain.NoZeroDivisors.Read(R).AsFact().At(p, y),
						comm_ring.MulLeftZeroOn.Read(ring).At(qm)))
				b.Show(
					"Commutativity gives the cross products of (y, x) and (q, p)",
					By(
						xNonzero,
						cross,
						DomainFractionClassMember.Read(R).At(qm, pm, y, x),
						comm_monoid.CommOn.Read(monoid).AsFact().At(p, y),
						comm_monoid.CommOn.Read(monoid).AsFact().At(x, q)))
			}))
		swapped := a.Have(
			"Turning round goes both ways: r and u are both nonzero",
			"∀x y:A. "+
				"    (x, y) ∈ fraction_class(R.carrier, «nonzero»(R), r, u) ⇔ "+
				"    (y, x) ∈ fraction_class(R.carrier, «nonzero»(R), u, r)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				b.Show(
					"Each direction is the step above",
					By(r, u, nonzero, turnRound.At(r, u, x, y), turnRound.At(u, r, y, x)))
			}))
		turned := a.Have(
			"A set of pairs is read by extensionality, one pair at a time",
			"{(y, x) | x:A, y:A | (x, y) ∈ fraction_class(R.carrier, «nonzero»(R), r, u)} = "+
				"fraction_class(R.carrier, «nonzero»(R), u, r)",
			Simp(Fwd(set_basic.Extension)),
			Simp(Fwd(pairs.ForallPair)),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				b.Show(
					"The two sets have the same pairs, a pair equation reading its components",
					BySets(swapped.At(y, x), pairs.PairEq.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()).At(x, y)))
			}))
		a.Show(
			"The class is nonzero, so the inverse turns its pairs round",
			By(
				nonzero,
				DomainFractionZeroIff.Read(R).At(r, u),
				turned,
				FractionInvDef.At(a.TermAs[A]("R.zero"), a.TermAs[Op[A]]("R.mul"), a.TermAs[A]("R.one"),
					a.TermAs[Set[A]]("R.carrier"), a.TermAs[Set[A]]("«nonzero»(R)"),
					a.TermAs[Set[Prod[A, A]]]("fraction_class(R.carrier, «nonzero»(R), r, u)"))))
	}),
})}

// FractionField — the fractions of an integral domain with every nonzero
// denominator form a field on their set: the ring of fractions, whose
// nonzero classes are the r / u with r nonzero and whose inverses turn
// them round.
var FractionField = fractionFieldThm{family.Add(registry.ProofEntry{
	Name: "FractionField",
	Key:  "prop_e9620697d19d8191",
	Reading: "The zero class is 0 / 1, and the definition's COND makes the inverse of the zero " +
		"class itself; 1 / 1 ≠ 0 / 1 because in a domain a class is zero only with its numerator.",
	Build: integral_domain.IntegralDomainOn.Law("field_on(fraction_field_record(R))",
		func(a *Argument, R integral_domain.IntegralDomainFact[on.R]) {
			ring := integral_domain.Ring.Read(R)
			zero := a.TermAs[A]("R.zero")
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			mul := a.TermAs[Op[A]]("R.mul")
			carrier := a.TermAs[Set[A]]("R.carrier")
			denominators := a.TermAs[Set[A]]("«nonzero»(R)")
			representatives := a.Have(
				"A nonzero fraction is the class of a nonzero numerator over a nonzero denominator",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, «nonzero»(R))",
						"X ≠ fraction_zero(R.carrier, «nonzero»(R))",
					},
					Conclusion: "∃r u:A. " +
						"    r ∈ R.carrier ∧ " +
						"    u ∈ R.carrier ∧ " +
						"    r ≠ R.zero ∧ " +
						"    u ≠ R.zero ∧ " +
						"    X = fraction_class(R.carrier, «nonzero»(R), r, u)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					hypotheses := b.Assume()
					r, u, represents := b.Obtain2As[A, A](
						"Write the fraction as the class of a numerator over a denominator",
						"∃r u:A. r ∈ R.carrier ∧ u ∈ «nonzero»(R) ∧ X = fraction_class(R.carrier, «nonzero»(R), r, u)",
						By(hypotheses, RingLocalizationMember.At(mul, carrier, denominators, X)))
					numeratorNonzero := b.Have(
						"A zero numerator would make the fraction zero",
						"r ≠ R.zero",
						BySets(hypotheses, represents, DomainFractionZeroIff.Read(R).AsFact().At(r, u)))
					b.Take(r)
					b.Take(u)
					b.Show(
						"This class has a nonzero numerator, and its denominator is nonzero",
						BySets(numeratorNonzero, represents))
				}))
			a.Do(Unfold(field.FieldOn),
				Simp(Fwd(FractionFieldRecordDef), Fwd(FractionFieldDef), Fwd(field.FieldRingDef)),
				SplitConjAll(
					Case(
						"The fractions form a commutative ring",
						By(NonzeroMultiplicative.Read(R), LocalizationRing.Read(ring).At(denominators))),
					Case(
						"The inverse of a fraction is a fraction",
						Derive(func(b *Argument) {
							X := b.FixAs[Set[Prod[A, A]]]("X")
							inFractions := b.Assume()
							b.Cases(b.TermAs[Bool]("X = fraction_zero(R.carrier, «nonzero»(R))"))
							b.When(
								"The zero fraction is its own inverse",
								func(c *Argument, isZero Fact) {
									c.Show(
										"Its inverse is itself, a fraction",
										By(isZero, inFractions, FractionInvDef.At(zero, mul, one, carrier, denominators, X)))
								})
							b.Otherwise(
								"The inverse of a nonzero fraction is its class turned round",
								func(c *Argument, notZero Fact) {
									r, u, represents := c.Unpack2As[A, A](
										GroupPremises(inFractions, notZero, representatives.At(X)), "r", "u")
									turned := c.Have(
										"The inverse of the class of r / u is the class of u / r",
										"fraction_inv(R.carrier, «nonzero»(R), X) = fraction_class(R.carrier, «nonzero»(R), u, r)",
										By(Normalized, represents, FractionInvClass.Read(R).AsFact().At(r, u)))
									c.Do(turned.Rw(), Simp(Fwd(RingLocalizationMember)))
									c.Take(u)
									c.Take(r)
									c.Show(
										"The class of u / r is a fraction, r being nonzero and so a denominator",
										BySets(represents))
								})
						})),
					Case(
						"One and zero are distinct fractions",
						Simp(Fwd(FractionOneDef)),
						By(integral_domain.OneNotZero.Read(R), DomainFractionZeroIff.Read(R).At(one, one))),
					Case(
						"Every nonzero fraction has a left inverse",
						Derive(func(b *Argument) {
							X := b.FixAs[Set[Prod[A, A]]]("X")
							inFractions := b.Assume()
							notZero := b.Assume()
							r, u, represents := b.Unpack2As[A, A](
								GroupPremises(inFractions, notZero, representatives.At(X)), "r", "u")
							bothDenominators := b.Have(
								"r and u are nonzero, so both serve as denominators",
								"r ∈ «nonzero»(R) ∧ u ∈ «nonzero»(R)",
								BySets(represents))
							product := b.Have(
								"The product of X and its inverse is the class of (u * r, r * u)",
								"fraction_mul(R.carrier, «nonzero»(R), fraction_inv(R.carrier, «nonzero»(R), X), X) = "+
									"fraction_class(R.carrier, «nonzero»(R), u * r, r * u)",
								By(
									Normalized,
									NonzeroMultiplicative.Read(R),
									represents,
									bothDenominators,
									FractionInvClass.Read(R).AsFact().At(r, u),
									FractionMulClass.Read(ring).AsFact().At(denominators, u, r, r, u)))
							cross := b.Have(
								"The cross products of (u * r, r * u) and (one, one) agree",
								"(u * r) * R.one = R.one * (r * u)",
								ByArith(ring, represents))
							unit := b.Have(
								"So that class is one over one",
								"fraction_class(R.carrier, «nonzero»(R), u * r, r * u) = "+
									"fraction_class(R.carrier, «nonzero»(R), R.one, R.one)",
								By(
									cross,
									represents,
									one,
									integral_domain.OneNotZero.Read(R),
									comm_ring.MulIn.Read(ring).AsFact().At(u, r),
									comm_ring.MulIn.Read(ring).AsFact().At(r, u),
									integral_domain.NoZeroDivisors.Read(R).AsFact().At(r, u),
									DomainFractionEqIff.Read(R).AsFact().At(
										b.TermAs[A]("u * r"), b.TermAs[A]("r * u"), one, one)))
							b.Show(
								"One over one is the one fraction",
								By(product, unit, FractionOneDef.At(mul, one, carrier, denominators)))
						})),
					Case(
						"The inverse of zero is zero",
						Simp(Fwd(FractionInvDef)),
						Basic()),
					Case(
						"Division is multiplication by the inverse",
						Simp(Fwd(FractionDivDef)),
						Basic()),
				))
		}),
})}

// ToFractionInjective — the embedding r ↦ r / one of a domain into its
// fractions is injective on the carrier: r / one = r' / one says their cross
// products agree (DomainFractionEqIff), and those are r and r'.
var ToFractionInjective = toFractionInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ToFractionInjective",
	Key:  "prop_e57040846ea6bfa3",
	Reading: "With zero divisors the map can fail to be injective: r " +
		"/ R.one = r' / R.one only says t * r = t * r' for some nonzero t.",
	Build: integral_domain.IntegralDomainOn.Law("injective_on(R.carrier, "+
		"    to_fraction(R.carrier, «nonzero»(R)))",
		func(a *Argument, R integral_domain.IntegralDomainFact[on.R]) {
			ring := integral_domain.Ring.Read(R)
			a.Do(Unfold(functions.InjectiveOnDef))
			x := a.FixAs[A]("x")
			y := a.FixAs[A]("y")
			equal := a.Assume()
			parts := a.Conjuncts(
				equal,
				"x lies in the carrier",
				"y lies in the carrier",
				"the two images agree")
			xIn, yIn, sameImage := parts[0], parts[1], parts[2]
			classes := a.Unfolded(sameImage, ToFractionDef)
			xm := a.MemberOf[on.R](x, xIn)
			ym := a.MemberOf[on.R](y, yIn)
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			cross := a.Have(
				"over the denominator one the cross products are the numerators times one",
				"x * R.one = y * R.one",
				By(classes, integral_domain.OneNotZero.Read(R), DomainFractionEqIff.Read(R).At(xm, one, ym, one)))
			a.Show(
				"one is the identity of the product",
				ByArith(ring, xm, ym, cross))
		}),
})}

// FractionFieldLift — a one-to-one ring map φ from a subring S of a field
// into a field extends to a subfield K that is the field of fractions of S:
// K is the localization of S at its nonzero elements, and φ sends each of
// them to a nonzero element, a unit of the target.
var FractionFieldLift = fractionFieldLiftThm{family.Add(registry.ProofEntry{
	Name: "FractionFieldLift",
	Key:  "prop_cdf196996ce961b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:field_on(B). ∀S K:set(A). ∀φ:(A → B).",
		Hypotheses: []string{
			"subfield(L, K)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), S)",
			"ring_homomorphism(restrict_ring(field_ring(L), S), field_ring(T), φ)",
			"injective_on(S, φ)",
		},
		Conclusion: "∃ψ:(A → B). " +
			"    ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(T), ψ) ∧ " +
			"    (∀x:A. x ∈ S ⇒ ψ(x) = φ(x))",
		Abbrev: Abbrev{
			{Name: "denominators", Text: "S ∖ {L.zero}"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		T field.FieldFact[on.T],
		S, K *Expr[Set[A]],
		φ *Arrow[A, B],
		subK, fractions, hom, injective Fact,
	) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		source := ring_homomorphism.Source.Read(hom)
		inclusions := a.Have(
			"S lies in K, and K in L",
			"S ⊆ K ∧ K ⊆ L.carrier",
			BySets(subK, fractions, field.FractionFieldCarrierDef, field.SubfieldSubset.At(fieldL, K)))
		ringK := a.Have(
			"K is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), K))",
			By(subK, field.SubfieldCommRing.Read(L).At(K)))
		domain := a.Have(
			"S, a subring of the field L, is an integral domain",
			"integral_domain_on(restrict_ring(field_ring(L), S))",
			BySets(
				source,
				inclusions,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S),
				integral_domain.SubringOfFieldDomain.Read(L).At(S)))
		localization := a.Have(
			"K is the localization of S at its nonzero elements",
			"is_localization_on(restrict_ring(field_ring(L), S), "+
				"    «denominators», "+
				"    restrict_ring(field_ring(L), K), "+
				"    λx:A. x)",
			Simp(Fwd(IsLocalizationOnDef)),
			SplitConjAll(
				Case(
					"the nonzero elements of S, a domain, form a multiplicative set",
					By(NonzeroMultiplicative.Read(domain))),
				Case(
					"the inclusion of S in K is a ring map",
					Simp(Fwd(ring_homomorphism.RingHomomorphism)),
					BySets(source, ringK, inclusions)),
				Case(
					"a nonzero element s of S is a unit of K, with the inverse L.inv(s)",
					Derive(func(b *Argument) {
						s := b.FixAs[A]("s")
						member := b.Assume()
						nonzero := b.Have(
							"s is a nonzero element of K, so of L",
							"s ∈ K ∧ s ∈ L.carrier ∧ s ≠ L.zero",
							BySets(member, inclusions))
						b.Show(
							"s lies in K, and so does its inverse",
							Simp(Fwd(ring_ideal.RingUnitDef)),
							SplitConj(
								Case(
									"s lies in K",
									By(nonzero)),
								Case(
									"L.inv(s) lies in K and inverts s",
									Witness(b.TermAs[A]("L.inv(s)")),
									By(nonzero, subK, field.SubfieldInv.At(fieldL, K, s), At(field.MulRightInverseOn.Read(L), s)))))
					})),
				Case(
					"every element of K is a fraction over S",
					BySets(fractions, field.FractionFieldCarrierDef)),
				Case(
					"an element of S sent to zero is zero, which the denominator one kills",
					BySets(
						comm_ring.OneIn.Read(source),
						field.OneNotZeroOn.Read(L),
						comm_ring.MulRightZeroOn.Read(field.RingOn.Read(L)),
						comm_ring.OneIn.Read(field.RingOn.Read(L))))))
		units := a.Have(
			"φ sends a nonzero element of S to a nonzero element of T, a unit there",
			"∀s:A. s ∈ «denominators» ⇒ ring_unit(field_ring(T), φ(s))",
			Derive(func(b *Argument) {
				b.FixAs[A]("s")
				member := b.Assume()
				parts := b.Have(
					"s is a nonzero element of S",
					"s ∈ S ∧ s ≠ L.zero",
					BySets(member))
				nonzero := b.Have(
					"φ(s) is not zero: φ is one-to-one and sends zero to zero",
					"φ(s) ≠ T.zero",
					By(
						parts,
						injective,
						functions.InjectiveOnDef.At(S, φ),
						ring_homomorphism.MapZero.Read(hom),
						comm_ring.ZeroIn.Read(source)))
				b.Show(
					"φ(s) lies in T, and T.inv(φ(s)) inverts it",
					By(
						nonzero,
						parts,
						ring_ideal.RingUnitDef.At(b.TermAs[RingOps[B]]("field_ring(T)"), b.TermAs[B]("φ(s)")),
						ring_homomorphism.MapIn.Read(hom),
						field.InvIn.Read(T),
						field.MulRightInverseOn.Read(T)))
			}))
		a.Show(
			"the universal property of the localization extends φ to K",
			By(
				units,
				hom,
				localization,
				LocalizationUniversal.At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"),
					a.TermAs[Set[A]]("«denominators»"),
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)"),
					a.TermAs[Fun[A, A]]("λx:A. x"),
					a.TermAs[RingOps[B]]("field_ring(T)"),
					φ)))
	}),
})}
