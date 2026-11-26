// signed_powers.go — the integer powers of a unit of a commutative monoid, and
// the integer powers of an invertible fractional ideal they give in the monoid
// of fractional ideals: their laws and the inverse of a power; for a proper
// ideal inside the ring, the powers decrease strictly and are distinct, and an
// exponent the principal ideals take among them is a valuation.

package signed_ideal_power

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SignedPowerLaws — the integer powers of a unit of a commutative monoid: with
// x and y inverse, the power at n is y^n for n ≥ 0 and x^(−n) for n < 0. Each
// integer is a difference m − n, where the power is y^m x^n by cancelling the
// common part, so the exponents add. The power at 0 is e, and every power
// lies in c.
var SignedPowerLaws = signedPowerLawsThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerLaws",
	Key:  "prop_4af0cdba3183b3a2",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c ∧ y ∈ c",
			"op(x, y) = e",
		},
		Conclusion: "«signedPower»(int_of_num(0)) = e ∧ " +
			"«signedPower»(-int_of_num(1)) = x ∧ " +
			"(∀n:int. «signedPower»(n) ∈ c) ∧ " +
			"(∀i j:int. «signedPower»(i + j) = op(«signedPower»(i), «signedPower»(j)))",
		Abbrev: Abbrev{
			{Name: "signedPower", Text: "λn:int. COND(&0 ≤ n, y ^ num_of_int(n), x ^ num_of_int(-n))"},
		},
	},
		func(a *Argument, monoid comm_monoid.CommMonoidFact[on.C], x, y *Member[A, on.C], inverse Fact) {
			power := comm_monoid.PowIn.Read(monoid)
			cancel := a.Have(
				"y^n cancels x^n, y and x being inverse in either order",
				"∀n:num. op(y ^ n, x ^ n) = e",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						inverse,
						comm_monoid.CommOn.Read(monoid).At(y, x),
						comm_monoid.PowInverseOn.Read(monoid).At(y, x, n))
				}))
			shiftDown := a.Have(
				"y^(d + n) x^n leaves y^d",
				"∀d n:num. op(y ^ (d + n), x ^ n) = y ^ d",
				Derive(func(b *Argument) {
					d, n := b.FixAs[Nat]("d"), b.FixAs[Nat]("n")
					yd, yn, xn := power.At(y, d), power.At(y, n), power.At(x, n)
					b.Show(
						"the common power cancels",
						CalcEq(
							Leg(
								b.TermAs[A]("op(op(y ^ d, y ^ n), x ^ n)"),
								"the exponents add",
								By(comm_monoid.PowAddOn.Read(monoid).At(y, d, n))),
							Leg(
								b.TermAs[A]("op(y ^ d, op(y ^ n, x ^ n))"),
								"op associates on c",
								By(comm_monoid.AssocOn.Read(monoid).At(yd, yn, xn))),
							Leg(
								b.TermAs[A]("op(y ^ d, e)"),
								"y^n cancels x^n",
								By(Normalized, cancel.At(n))),
							FinalLeg(
								"e is the unit",
								By(comm_monoid.RightIdentityOn.Read(monoid).At(yd)))))
				}))
			shiftUp := a.Have(
				"y^n x^(d + n) leaves x^d",
				"∀d n:num. op(y ^ n, x ^ (d + n)) = x ^ d",
				Derive(func(b *Argument) {
					d, n := b.FixAs[Nat]("d"), b.FixAs[Nat]("n")
					xd, yn, xn := power.At(x, d), power.At(y, n), power.At(x, n)
					b.Show(
						"the common power cancels",
						CalcEq(
							Leg(
								b.TermAs[A]("op(y ^ n, op(x ^ d, x ^ n))"),
								"the exponents add",
								By(comm_monoid.PowAddOn.Read(monoid).At(x, d, n))),
							Leg(
								b.TermAs[A]("op(x ^ d, op(y ^ n, x ^ n))"),
								"x^d passes y^n, op associating and commuting on c",
								By(comm_monoid.LeftCommOn.Read(monoid).At(yn, xd, xn))),
							Leg(
								b.TermAs[A]("op(x ^ d, e)"),
								"y^n cancels x^n",
								By(Normalized, cancel.At(n))),
							FinalLeg(
								"e is the unit",
								By(comm_monoid.RightIdentityOn.Read(monoid).At(xd)))))
				}))
			nonnegative := a.Have(
				"at a natural number d the power is y^d",
				"∀d:num. «signedPower»(int_of_num(d)) = y ^ d",
				a.ForEach(func(d *Expr[Nat]) Action {
					return By(int_embed.EmbedNonneg, int_embed.OfNumRetract)
				}))
			negative := a.Have(
				"at −d, for d ≠ 0, the power is x^d",
				"∀d:num. d ≠ 0 ⇒ «signedPower»(-int_of_num(d)) = x ^ d",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					nonzero := b.Assume()
					negated := b.Have(
						"−d is negative",
						"¬(0 ≤ -int_of_num(d))",
						ByArith(nonzero, int_embed.OfNumLe.At(d, b.TermAs[Nat]("0"))))
					exponent := b.Have(
						"and its negative is d again",
						"num_of_int(- -int_of_num(d)) = d",
						Simp(Fwd(int_real_lift.NegNeg), Fwd(int_embed.OfNumRetract)),
						Refl())
					b.Show(
						"so the power takes its second branch",
						By(Normalized, negated, exponent))
				}))
			difference := a.Have(
				"at m − n the power is y^m x^n",
				"∀m n:num. «signedPower»(int_of_num(m) - int_of_num(n)) = op(y ^ m, x ^ n)",
				Derive(func(b *Argument) {
					m, n := b.FixAs[Nat]("m"), b.FixAs[Nat]("n")
					b.Cases(b.TermAs[Bool]("n ≤ m"))
					b.When(
						"m exceeds n by some d, and m − n is d",
						func(c *Argument, atMost Fact) {
							d, excess := c.ObtainAs[Nat](
								"m is d more than n",
								"∃d:num. m = d + n",
								Witness(c.TermAs[Nat]("m - n")),
								ByArith(atMost))
							gap := c.Have(
								"so m − n is the integer d",
								"int_of_num(m) - int_of_num(n) = int_of_num(d)",
								ByArith(excess, int_embed.OfNumAdd.At(d, n)))
							c.Show(
								"the common power cancels",
								gap.Rw(),
								By(excess, nonnegative.At(d), shiftDown.At(d, n)))
						})
					b.Otherwise(
						"n exceeds m by some nonzero d, and m − n is −d",
						func(c *Argument, exceeds Fact) {
							d, excess := c.ObtainAs[Nat](
								"n is d more than m",
								"∃d:num. n = d + m ∧ d ≠ 0",
								Witness(c.TermAs[Nat]("n - m")),
								ByArith(exceeds))
							parts := c.Conjuncts(
								excess,
								"n is d more than m",
								"d is not zero")
							gap := c.Have(
								"so m − n is the integer −d",
								"int_of_num(m) - int_of_num(n) = -int_of_num(d)",
								ByArith(parts[0], int_embed.OfNumAdd.At(d, m)))
							c.Show(
								"the common power cancels",
								gap.Rw(),
								By(parts[0], parts[1], negative.At(d), shiftUp.At(d, m)))
						})
				}))
			differences := a.Have(
				"every integer is a difference of natural numbers",
				"∀z:int. ∃m n:num. z = m - &n",
				Derive(func(b *Argument) {
					z := b.FixAs[Int]("z")
					b.Cases(b.TermAs[Bool]("&0 ≤ z"))
					b.When(
						"a nonnegative z is itself natural",
						func(c *Argument, nonneg Fact) {
							c.Show(
								"z is its own natural number less 0",
								Witness(c.TermAs[Nat]("num_of_int(z)")),
								Witness(c.TermAs[Nat]("0")),
								ByArith(int_embed.NumOfIntSection.At(z), nonneg))
						})
					b.Otherwise(
						"a negative z is the negative of a natural number",
						func(c *Argument, neg Fact) {
							c.Show(
								"z is 0 less the natural number −z",
								Witness(c.TermAs[Nat]("0")),
								Witness(c.TermAs[Nat]("num_of_int(-z)")),
								ByArith(int_embed.NumOfIntSection.At(c.TermAs[Int]("-z")), neg))
						})
				}))
			zero := a.Have(
				"the power at 0 is e",
				"«signedPower»(int_of_num(0)) = e",
				By(nonnegative.At(a.TermAs[Nat]("0")), comm_monoid.MonoidPowDef))
			oneNonzero := a.Have(
				"1 is not 0",
				"1 ≠ 0",
				ByArith())
			minusOne := a.Have(
				"the power at −1 is x",
				"«signedPower»(-int_of_num(1)) = x",
				By(oneNonzero, negative.At(a.TermAs[Nat]("1")), comm_monoid.PowOneOn.Read(monoid).At(x)))
			member := a.Have(
				"every power lies in c",
				"∀n:int. «signedPower»(n) ∈ c",
				Derive(func(b *Argument) {
					b.FixAs[Int]("n")
					b.Cases(b.TermAs[Bool]("&0 ≤ n"))
					b.When(
						"at n ≥ 0 a power of y",
						func(c *Argument, nonneg Fact) {
							c.Show(
								"a power of y lies in c",
								By(nonneg, power.At(y, c.TermAs[Nat]("num_of_int(n)"))))
						})
					b.Otherwise(
						"at n < 0 a power of x",
						func(c *Argument, neg Fact) {
							c.Show(
								"a power of x lies in c",
								By(neg, power.At(x, c.TermAs[Nat]("num_of_int(-n)"))))
						})
				}))
			additive := a.Have(
				"the exponents add",
				"∀i j:int. «signedPower»(i + j) = op(«signedPower»(i), «signedPower»(j))",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					m1, n1, iDifference := b.Unpack2As[Nat, Nat](differences.At(i), "m₁", "n₁")
					m2, n2, jDifference := b.Unpack2As[Nat, Nat](differences.At(j), "m₂", "n₂")
					sum := b.Have(
						"i + j is the difference of the two sums",
						"i + j = int_of_num(m₁ + m₂) - int_of_num(n₁ + n₂)",
						ByArith(iDifference, jDifference, int_embed.OfNumAdd.At(m1, m2), int_embed.OfNumAdd.At(n1, n2)))
					ym1, ym2 := power.At(y, m1), power.At(y, m2)
					xn1, xn2 := power.At(x, n1), power.At(x, n2)
					b.Show(
						"both sides are y^(m₁ + m₂) x^(n₁ + n₂)",
						CalcEq(
							Leg(
								b.TermAs[A]("op(y ^ (m₁ + m₂), x ^ (n₁ + n₂))"),
								"i + j is that difference",
								By(sum, difference.At(b.TermAs[Nat]("m₁ + m₂"), b.TermAs[Nat]("n₁ + n₂")))),
							Leg(
								b.TermAs[A]("op(op(y ^ m₁, y ^ m₂), op(x ^ n₁, x ^ n₂))"),
								"the exponents add",
								By(
									comm_monoid.PowAddOn.Read(monoid).At(y, m1, m2),
									comm_monoid.PowAddOn.Read(monoid).At(x, n1, n2))),
							Leg(
								b.TermAs[A]("op(op(y ^ m₁, x ^ n₁), op(y ^ m₂, x ^ n₂))"),
								"the two middle terms exchange, op associating and commuting on c",
								By(
									comm_monoid.AssocOn.Read(monoid).At(ym1, ym2, comm_monoid.OpIn.Read(monoid).At(xn1, xn2)),
									comm_monoid.LeftCommOn.Read(monoid).At(ym2, xn1, xn2),
									comm_monoid.AssocOn.Read(monoid).At(ym1, xn1, comm_monoid.OpIn.Read(monoid).At(ym2, xn2)))),
							FinalLeg(
								"i and j are the two differences",
								By(iDifference, jDifference, difference.At(m1, n1), difference.At(m2, n2)))))
				}))
			a.Show(
				"the powers at 0 and −1, their membership in c, and the sum of exponents",
				By(zero, minusOne, member, additive))
		}),
})}

// SignedIdealPowerLaws — the integer powers of an invertible fractional ideal
// N of S are SignedPowerLaws read in the monoid of fractional ideals of S, N
// and its inverse being inverse members there: the power at 0 is S, at 1 it is
// N, at a natural number it is the natural power, every power is a fractional
// ideal, and exponents add.
var SignedIdealPowerLaws = signedIdealPowerLawsThm{family.Add(registry.ProofEntry{
	Name: "SignedIdealPowerLaws",
	Key:  "prop_911e66b95e85c74c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
		},
		Conclusion: "«power»(0) = S ∧ " +
			"«power»(1) = N ∧ " +
			"(∀n:num. «power»(n) = monoid_pow(«product», S, N, n)) ∧ " +
			"(∀n:int. «fractional»(«power»(n))) ∧ " +
			"(∀i j:int. «power»(i + j) = «product»(«power»(i), «power»(j)))",
		Abbrev: Abbrev{
			{Name: "product", Text: "λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y)"},
			{Name: "inverse", Text: "fractional_inverse(field_ring(L), S, N)"},
			{Name: "fractional", Text: "submodule(restrict_ring(field_ring(L), S), " +
				"    regular_module(field_ring(L)))"},
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible")
			subring, invertible := given[0], given[1]
			clauses := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"N is a fractional ideal",
				"it multiplies with its inverse to S")
			fractional, cancels := clauses[0], clauses[1]
			nInL := a.Have(
				"N lies in L",
				"N ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			monoid := a.Have(
				"the fractional ideals of S are a commutative monoid",
				"comm_monoid_on({X:set(A) | «fractional»(X)}, «product», S)",
				By(subring, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
			inverseFractional := a.Have(
				"the inverse of N is a fractional ideal",
				"«fractional»(«inverse»)",
				By(subring, nInL, fractional_ideal.FractionalInverseSubmodule.Read(L).At(S, N)))
			inverseMembers := a.Have(
				"N and its inverse are inverse members of the monoid",
				"«inverse» ∈ {X:set(A) | «fractional»(X)} ∧ "+
					"N ∈ {X:set(A) | «fractional»(X)} ∧ "+
					"«product»(«inverse», N) = S",
				By(
					Normalized,
					fractional,
					inverseFractional,
					cancels,
					nInL,
					fractional_ideal.FractionalInverseSubset.Read(L).At(S, N),
					fractional_ideal.FractionalMulComm.Read(L).At(S, N, a.TermAs[Set[A]]("«inverse»"))))
			laws := a.Conjuncts(
				GroupPremises(inverseMembers, Read(SignedPowerLaws, monoid).At(a.TermAs[Set[A]]("«inverse»"), N)),
				"the power at 0 is S",
				"the power at −1 is the inverse",
				"every power is a fractional ideal",
				"the exponents add")
			atZero := a.Simplified(laws[0], Rev(SignedIdealPowerDef))
			members := a.Simplified(laws[2], Rev(SignedIdealPowerDef))
			additive := a.Simplified(laws[3], Rev(SignedIdealPowerDef))
			natural := a.Have(
				"at a natural exponent the power is the natural power",
				"∀n:num. «power»(n) = monoid_pow(«product», S, N, n)",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(int_embed.EmbedNonneg, int_embed.OfNumRetract, SignedIdealPowerDef)
				}))
			first := a.Have(
				"the power at 1 is N",
				"«power»(1) = N",
				By(
					natural.At(a.TermAs[Nat]("1")),
					inverseMembers,
					comm_monoid.PowOneOn.Read(monoid).AsFact().At(N)))
			a.Show(
				"the five laws",
				By(atZero, first, natural, members, additive))
		}),
})}

// SignedPowerInverse — the (−j)-th power of an invertible fractional ideal N
// of S is the inverse of its j-th power: the two powers are fractional ideals
// whose product is the 0-th power, S (SignedIdealPowerLaws), and a fractional
// ideal multiplying to S is the inverse (fractional_ideal.FractionalInverseUnique).
var SignedPowerInverse = signedPowerInverseThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerInverse",
	Key:  "prop_3e555d01b209bc40",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀j:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
		},
		Conclusion: "«power»(-j) = fractional_inverse(field_ring(L), S, «power»(j))",
		Abbrev: Abbrev{
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], j *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible over S")
			cancel := a.Have(
				"j and −j cancel",
				"j + -j = &0",
				ByArith())
			product := a.Have(
				"the j-th and (−j)-th powers are fractional ideals whose product is the 0-th power, S",
				"fractional_mul(field_ring(L), S, «power»(j), «power»(-j)) = S ∧ "+
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «power»(j)) ∧ "+
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «power»(-j))",
				By(cancel, given[0], given[1], SignedIdealPowerLaws.Read(L).At(S, N)))
			a.Show(
				"so the (−j)-th power is the inverse of the j-th",
				By(
					given[0],
					product,
					fractional_ideal.FractionalInverseUnique.Read(L).At(
						S, a.TermAs[Set[A]]("«power»(j)"), a.TermAs[Set[A]]("«power»(-j)"))))
		}),
})}

// SignedPowerOfRing — every signed power of a subring S at S itself is S: S is
// the unit of the monoid of fractional ideals of S and its own inverse there,
// and every power of the unit is the unit.
var SignedPowerOfRing = signedPowerOfRingThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerOfRing",
	Key:  "prop_de63e9ef7588e7ed",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S:set(A). ∀j:int.",
		Hypotheses: []string{"subring(field_ring(L), S)"},
		Conclusion: "signed_ideal_power(field_ring(L), S, S, j) = S",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], j *Expr[Int], subring Fact) {
			monoid := a.Have(
				"the fractional ideals of S are a commutative monoid with unit S",
				"comm_monoid_on( "+
					"    {X:set(A) | submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), X)}, "+
					"    λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), "+
					"    S)",
				By(subring, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
			a.Show(
				"S is its own inverse, and every power of the unit is the unit",
				Simp(
					Fwd(SignedIdealPowerDef),
					Fwd(fractional_ideal.SubringInvertible.Read(L)),
					Fwd(comm_monoid.IdentityPowOn.Read(monoid))),
				Basic())
		}),
})}

// SignedPowerHoldsPrincipal — a signed power of an invertible fractional
// ideal N of S holds a function f exactly when it holds the principal ideal
// fS: f is f·1 with one in S, and the power, a fractional ideal of S, holds
// every multiple t·f of its member f.
var SignedPowerHoldsPrincipal = signedPowerHoldsPrincipalThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerHoldsPrincipal",
	Key:  "prop_9473a3914d8679d2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀f:A. ∀n:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
			"f ∈ L.carrier",
		},
		Conclusion: "image(L.mul(f), S) ⊆ «power»(n) ⇔ f ∈ «power»(n)",
		Abbrev: Abbrev{
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], f *Expr[A], n *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible",
				"f lies in L")
			subring, invertible, fInL := given[0], given[1], given[2]
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			fm := a.MemberOf[on.L](f, fInL)
			power := a.TermAs[Set[A]]("«power»(n)")
			multiply := a.TermAs[Fun[A, A]]("L.mul(f)")
			a.Iff()
			a.Forward(
				"f is f times one, and one lies in S",
				func(b *Argument, inside Fact) {
					unit := b.Have(
						"f · 1 = f",
						"f * L.one = f",
						ByArith(L, fm))
					b.Show(
						"so f lies among its multiples, inside the power",
						BySets(inside, unit, subring, comm_ring.SubringOne.At(ring, S)))
				})
			a.Backward(
				"the power is a fractional ideal of S, holding every S-multiple of its member f",
				func(b *Argument, fIn Fact) {
					multiples := b.Have(
						"each multiple f · t with t in S lies in the power",
						"∀t:A. t ∈ S ⇒ f * t ∈ «power»(n)",
						Derive(func(c *Argument) {
							t := c.FixAs[A]("t")
							tIn := c.Assume()
							tm := c.MemberOf[on.L](t, c.Have(
								"t lies in L",
								"t ∈ L.carrier",
								BySets(tIn, subring, comm_ring.SubringSubset.At(ring, S))))
							commuted := c.Have(
								"f · t = t · f",
								"f * t = t * f",
								ByArith(L, fm, tm))
							c.Show(
								"t · f is a S-multiple in the fractional ideal",
								commuted.Rw(),
								By(
									tIn,
									fIn,
									subring,
									invertible,
									SignedIdealPowerLaws.Read(L).At(S, N),
									submodule.SubmoduleSmul.At(
										c.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"),
										c.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
										power,
										t,
										f)))
						}))
					b.Show(
						"so fS lies in the power",
						By(multiples, set_image.ImageSubsetIff.At(multiply, S, power)))
				})
		}),
})}

// SignedPowerAntitone — the integer powers of a proper invertible ideal N of S
// decrease strictly: N^i ⊆ N^j exactly when j ≤ i. For j ≤ i, N^i is N^j
// times the natural power N^(i−j), which lies in S. For i < j, N^i ⊆ N^j
// would give S = N^i·N^(−i) ⊆ N^j·N^(−i) = N·N^(j−i−1) ⊆ N, which misses one.
var SignedPowerAntitone = signedPowerAntitoneThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerAntitone",
	Key:  "prop_cd550d1d5b0b20cd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀i j:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
			"N ⊆ S",
			"L.one ∉ N",
		},
		Conclusion: "«power»(i) ⊆ «power»(j) ⇔ j ≤ i",
		Abbrev: Abbrev{
			{Name: "product", Text: "λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y)"},
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], i, j *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible",
				"N lies in S",
				"N misses one")
			subring, invertible, inS, proper := given[0], given[1], given[2], given[3]
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			laws := a.Conjuncts(
				GroupPremises(subring, invertible, SignedIdealPowerLaws.Read(L).At(S, N)),
				"the power at 0 is S",
				"the power at 1 is N",
				"at a natural exponent the power is the natural power",
				"every power is a fractional ideal",
				"the exponents add")
			atZero, first, members, additive := laws[0], laws[1], laws[3], laws[4]
			fractional := a.Have(
				"N is a fractional ideal",
				"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), N)",
				By(invertible, fractional_ideal.InvertibleFractionalDef.At(ring, S, N)))
			nInL := a.Have(
				"N lies in L",
				"N ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.At(ring, S), subring))
			powersInL := a.Have(
				"every power of N is a fractional ideal, so it lies in L",
				"∀n:int. «power»(n) ⊆ L.carrier",
				Derive(func(b *Argument) {
					n := b.FixAs[Int]("n")
					b.Show(
						"a fractional ideal lies in L",
						By(
							members.At(n),
							submodule.SubmoduleSubset.At(
								b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"),
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
								b.TermAs[Set[A]]("«power»(n)"))))
				}))
			absorbs := a.Have(
				"N absorbs a multiple from any part of S",
				"∀X:set(A). X ⊆ S ⇒ «product»(N, X) ⊆ N",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					inside := b.Assume()
					multiples := b.Have(
						"a member of N times a member of X lies in N",
						"∀u v:A. u ∈ N ∧ v ∈ X ⇒ u * v ∈ N",
						Derive(func(c *Argument) {
							u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
							parts := c.Conjuncts(
								c.Assume(),
								"u lies in N",
								"v lies in X")
							vInS := c.Have(
								"v lies in S",
								"v ∈ S",
								BySets(inside, parts[1]))
							memberships := c.Have(
								"u and v lie in L",
								"u ∈ L.carrier ∧ v ∈ L.carrier",
								BySets(nInL, sInL, parts[0], vInS))
							commuted := c.Have(
								"u · v = v · u",
								"u * v = v * u",
								ByArith(L, memberships))
							c.Show(
								"and v · u is a multiple in the S-module N",
								commuted.Rw(),
								By(parts[0], vInS, submodule.SubmoduleSmul.Read(fractional).AsFact().At(v, u)))
						}))
					b.Show(
						"so their span lies in N",
						By(fractional, multiples, fractional_ideal.FractionalMulLeast.Read(L).At(S, N, X, N)))
				}))
			nonnegative := a.Have(
				"a power at a nonnegative exponent is a natural power, so it lies in S",
				"∀d:int. &0 ≤ d ⇒ «power»(d) ⊆ S",
				Derive(func(b *Argument) {
					b.FixAs[Int]("d")
					atLeastZero := b.Assume()
					value := b.Have(
						"at a nonnegative d the power is the natural power",
						"«power»(d) = monoid_pow(«product», S, N, num_of_int(d))",
						Simp(Fwd(SignedIdealPowerDef)),
						By(atLeastZero))
					b.Show(
						"which lies in S, a natural power of an invertible ideal inside S",
						value.Rw(),
						By(
							subring,
							invertible,
							inS,
							fractional_ideal.InvertibleIdealPowers.Read(L).At(S, N, b.TermAs[Nat]("num_of_int(d)"))))
				}))
			unitRight := a.Have(
				"S is a unit on the right of a power",
				"∀n:int. «product»(«power»(n), S) = «power»(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Int]("n")
					power := b.TermAs[Set[A]]("«power»(n)")
					b.Show(
						"S is the unit of the fractional product",
						By(
							members.At(n),
							subring,
							powersInL.At(n),
							sInL,
							fractional_ideal.FractionalMulComm.Read(L).At(S, power, S),
							fractional_ideal.FractionalMulOne.Read(L).At(S, power)))
				}))
			a.Iff()
			a.Backward(
				"for j ≤ i the power at i is the power at j times a natural power, which lies in S",
				func(b *Argument, atMost Fact) {
					gap := b.TermAs[Int]("i + -j")
					split := b.Have(
						"j and i − j add to i",
						"j + (i + -j) = i",
						ByArith())
					product := b.Have(
						"the power at i is the product of the powers at j and i − j",
						"«power»(i) = «product»(«power»(j), «power»(i + -j))",
						By(split, additive.At(j, gap)))
					gapNonnegative := b.Have(
						"i − j is nonnegative",
						"&0 ≤ i + -j",
						ByArith(atMost))
					inside := b.Have(
						"the power at i − j lies in S",
						"«power»(i + -j) ⊆ S",
						By(gapNonnegative, nonnegative.At(gap)))
					b.Show(
						"so the product lies in the power at j",
						product.Rw(),
						By(
							inside,
							set_order.SubsetRefl,
							unitRight.At(j),
							fractional_ideal.FractionalMulMono.Read(L).At(
								S,
								b.TermAs[Set[A]]("«power»(j)"),
								b.TermAs[Set[A]]("«power»(j)"),
								b.TermAs[Set[A]]("«power»(i + -j)"),
								S)))
				})
			a.Forward(
				"for i < j the inclusion would put S inside N, which misses one",
				func(b *Argument, inclusion Fact) {
					below := b.SupposeNot()
					minusI := b.TermAs[Int]("-i")
					rest := b.TermAs[Int]("j + -i + -1")
					opposite := b.Have(
						"i and −i add to 0",
						"i + -i = 0",
						ByArith())
					whole := b.Have(
						"S is the product of the powers at i and −i",
						"S = «product»(«power»(i), «power»(-i))",
						By(atZero, opposite, additive.At(i, minusI)))
					enlarged := b.Have(
						"which lies in the product of the powers at j and −i",
						"«product»(«power»(i), «power»(-i)) ⊆ «product»(«power»(j), «power»(-i))",
						By(
							inclusion,
							set_order.SubsetRefl,
							fractional_ideal.FractionalMulMono.Read(L).At(
								S,
								b.TermAs[Set[A]]("«power»(i)"),
								b.TermAs[Set[A]]("«power»(j)"),
								b.TermAs[Set[A]]("«power»(-i)"),
								b.TermAs[Set[A]]("«power»(-i)"))))
					shift := b.Have(
						"j − i is one more than j − i − 1",
						"j + -i = 1 + (j + -i + -1)",
						ByArith())
					gap := b.Have(
						"the product of the powers at j and −i is N times the power at j − i − 1",
						"«product»(«power»(j), «power»(-i)) = «product»(N, «power»(j + -i + -1))",
						By(first, shift, additive.At(j, minusI), additive.At(b.TermAs[Int]("1"), rest)))
					restNonnegative := b.Have(
						"j − i − 1 is nonnegative, as i < j",
						"&0 ≤ j + -i + -1",
						ByArith(below))
					absorbed := b.Have(
						"so that product lies in N",
						"«product»(N, «power»(j + -i + -1)) ⊆ N",
						By(restNonnegative, nonnegative.At(rest), absorbs.At(b.TermAs[Set[A]]("«power»(j + -i + -1)"))))
					oneInS := b.Have(
						"one lies in S",
						"L.one ∈ S",
						By(subring, comm_ring.SubringOne.At(ring, S)))
					b.Show(
						"so one would lie in N",
						BySets(oneInS, whole, enlarged, gap, absorbed, proper))
				})
		}),
})}

// SignedPowerInjective — the integer powers of a proper invertible ideal are
// distinct: two equal powers each lie in the other, so by SignedPowerAntitone
// each exponent is at most the other.
var SignedPowerInjective = signedPowerInjectiveThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerInjective",
	Key:  "prop_a7632b9ed3b4c2e4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀m n:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
			"N ⊆ S",
			"L.one ∉ N",
			"signed_ideal_power(field_ring(L), S, N, m) = signed_ideal_power(field_ring(L), S, N, n)",
		},
		Conclusion: "m = n",
		Abbrev: Abbrev{
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], m, n *Expr[Int], h Fact) {
			below := a.Have(
				"the power at m lies in the power at n, so n ≤ m",
				"n ≤ m",
				By(h, set_order.SubsetRefl, SignedPowerAntitone.Read(L).At(S, N, m, n)))
			above := a.Have(
				"and the power at n lies in the power at m, so m ≤ n",
				"m ≤ n",
				By(h, set_order.SubsetRefl, SignedPowerAntitone.Read(L).At(S, N, n, m)))
			a.Show(
				"so m = n",
				ByArith(below, above))
		}),
})}

// SignedPowerValuation — an exponent v with fS = N^v(f) for every nonzero f is
// a valuation. A nonzero f lies in N^n exactly when fS = N^v(f) does
// (SignedPowerHoldsPrincipal), that is when n ≤ v(f), the
// powers decreasing strictly (SignedPowerAntitone). Principal
// ideals multiply, so v adds over products; each power is closed under sums and
// negatives, which gives the bound on a sum and its exactness when the two
// orders differ.
var SignedPowerValuation = signedPowerValuationThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerValuation",
	Key:  "prop_1aa68a60bc617e17",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀v:(A → int).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, N)",
			"N ⊆ S",
			"L.one ∉ N",
			"∀f:A. f ∈ L.carrier ∧ f ≠ L.zero ⇒ image(L.mul(f), S) = «power»(v(f))",
		},
		Conclusion: "valuation_order(field_ring(L), v)",
		Abbrev: Abbrev{
			{Name: "product", Text: "λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y)"},
			{Name: "power", Text: "signed_ideal_power(field_ring(L), S, N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], v *Arrow[A, Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible",
				"N lies in S",
				"N misses one",
				"each nonzero f generates the power of N at v(f)")
			subring, invertible, inS, proper, generates := given[0], given[1], given[2], given[3], given[4]
			ringL := field.RingOn.Read(L)
			laws := a.Conjuncts(
				GroupPremises(subring, invertible, SignedIdealPowerLaws.Read(L).At(S, N)),
				"the power at 0 is S",
				"the power at 1 is N",
				"at a natural exponent the power is the natural power",
				"every power is a fractional ideal",
				"the exponents add")
			members, additive := laws[3], laws[4]
			membership := a.Have(
				"a nonzero f lies in the power at n exactly when n ≤ v(f)",
				"∀f:A. ∀n:int. f ∈ L.carrier ∧ f ≠ L.zero ⇒ (f ∈ «power»(n) ⇔ n ≤ v(f))",
				Derive(func(b *Argument) {
					f, n := b.FixAs[A]("f"), b.FixAs[Int]("n")
					nonzero := b.Conjuncts(
						b.Assume(),
						"f lies in L",
						"f is not zero")
					fm := b.MemberOf[on.L](f, nonzero[0])
					b.Show(
						"f lies in the power at n exactly when fS, the power "+
							"at v(f), does, and the powers decrease strictly",
						By(
							fm,
							nonzero[1],
							generates.At(f),
							subring,
							invertible,
							inS,
							proper,
							SignedPowerHoldsPrincipal.Read(L).At(S, N, fm, n),
							SignedPowerAntitone.Read(L).At(S, N, v.Apply(f), n)))
				}))
			multiplicative := a.Have(
				"v adds over products: principal ideals multiply, and the powers are distinct",
				"∀x y:A. x ∈ L.carrier ∧ y ∈ L.carrier ∧ x ≠ L.zero ∧ y ≠ L.zero ⇒ v(x * y) = v(x) + v(y)",
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					parts := b.Conjuncts(
						b.Assume(),
						"x lies in L",
						"y lies in L",
						"x is not zero",
						"y is not zero")
					xm, ym := b.MemberOf[on.L](x, parts[0]), b.MemberOf[on.L](y, parts[1])
					xy := comm_ring.MulIn.Read(ringL).At(xm, ym)
					nonzero := b.Have(
						"x · y is not zero",
						"x * y ≠ L.zero",
						By(parts[2], parts[3], field.MulEqZeroOn.Read(L).At(xm, ym)))
					principal := b.Have(
						"the principal ideal of x · y is the product of those of x and y",
						"image(L.mul(x * y), S) = «product»(image(L.mul(x), S), image(L.mul(y), S))",
						By(subring, xm, ym, fractional_ideal.PrincipalProduct.Read(L).At(S, xm, ym)))
					powers := b.Have(
						"so the power at v(x · y) is the power at v(x) + v(y)",
						"«power»(v(x * y)) = «power»(v(x) + v(y))",
						By(
							xy,
							nonzero,
							parts[0],
							parts[1],
							parts[2],
							parts[3],
							principal,
							generates.At(b.TermAs[A]("x * y")),
							generates.At(x),
							generates.At(y),
							additive.At(v.Apply(x), v.Apply(y))))
					b.Show(
						"the powers are distinct",
						By(
							powers,
							subring,
							invertible,
							inS,
							proper,
							SignedPowerInjective.Read(L).At(S, N, v.Apply(b.TermAs[A]("x * y")), b.TermAs[Int]("v(x) + v(y)"))))
				}))
			lower := a.Have(
				"with v(x) ≤ v(y), a nonzero x + y has order at least v(x), exactly v(x) when v(x) < v(y)",
				Statement{
					Binders:    "∀x y:A.",
					Hypotheses: []string{"x ∈ L.carrier", "y ∈ L.carrier", "x ≠ L.zero", "y ≠ L.zero", "v(x) ≤ v(y)"},
					Conclusion: "(x + y ≠ L.zero ⇒ v(x) ≤ v(x + y)) ∧ (v(x) ≠ v(y) ⇒ x + y ≠ L.zero ∧ v(x + y) = v(x))",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					parts := b.Conjuncts(
						b.Assume(),
						"x lies in L",
						"y lies in L",
						"x is not zero",
						"y is not zero",
						"v(x) ≤ v(y)")
					xm, ym := b.MemberOf[on.L](x, parts[0]), b.MemberOf[on.L](y, parts[1])
					sum := comm_ring.AddIn.Read(ringL).At(xm, ym)
					vx := v.Apply(x)
					power := b.TermAs[Set[A]]("«power»(v(x))")
					scalars := b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
					vectors := b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
					reflexive := b.Have(
						"v(x) ≤ v(x)",
						"v(x) ≤ v(x)",
						ByArith())
					xIn := b.Have(
						"x lies in the power at v(x)",
						"x ∈ «power»(v(x))",
						By(parts[0], parts[2], reflexive, membership.At(x, vx)))
					yIn := b.Have(
						"y lies in the power at v(x)",
						"y ∈ «power»(v(x))",
						By(parts[1], parts[3], parts[4], membership.At(y, vx)))
					sumIn := b.Have(
						"so does x + y",
						"x + y ∈ «power»(v(x))",
						By(xIn, yIn, members.At(vx), submodule.SubmoduleAdd.At(scalars, vectors, power, x, y)))
					atLeast := b.Have(
						"a nonzero x + y has order at least v(x)",
						"x + y ≠ L.zero ⇒ v(x) ≤ v(x + y)",
						Derive(func(c *Argument) {
							nonzeroSum := c.Assume()
							c.Show(
								"x + y lies in the power at v(x)",
								By(sum, nonzeroSum, sumIn, membership.At(c.TermAs[A]("x + y"), vx)))
						}))
					exact := b.Have(
						"when v(x) < v(y), x + y is not zero and has order v(x)",
						"v(x) ≠ v(y) ⇒ x + y ≠ L.zero ∧ v(x + y) = v(x)",
						Derive(func(c *Argument) {
							differ := c.Assume()
							vy := v.Apply(y)
							next := c.TermAs[Int]("v(x) + &1")
							nextPower := c.TermAs[Set[A]]("«power»(v(x) + 1)")
							above := c.Have(
								"v(x) + 1 ≤ v(y)",
								"v(x) + 1 ≤ v(y)",
								ByArith(parts[4], differ))
							yAbove := c.Have(
								"y lies in the power at v(x) + 1",
								"y ∈ «power»(v(x) + 1)",
								By(parts[1], parts[3], above, membership.At(y, next)))
							negAbove := c.Have(
								"so does −y",
								"-y ∈ «power»(v(x) + 1)",
								By(yAbove, members.At(next), submodule.SubmoduleNeg.At(scalars, vectors, nextPower, y)))
							vyAtLeast := c.Have(
								"v(y) ≤ v(y)",
								"v(y) ≤ v(y)",
								ByArith())
							yOwn := c.Have(
								"y lies in the power at v(y)",
								"y ∈ «power»(v(y))",
								By(parts[1], parts[3], vyAtLeast, membership.At(y, vy)))
							negOwn := c.Have(
								"and so does −y",
								"-y ∈ «power»(v(y))",
								By(
									yOwn,
									members.At(vy),
									submodule.SubmoduleNeg.At(scalars, vectors, c.TermAs[Set[A]]("«power»(v(y))"), y)))
							nonzeroSum := c.Have(
								"x + y is not zero: else x = −y would lie in the power at v(y)",
								"x + y ≠ L.zero",
								Derive(func(d *Argument) {
									zeroSum := d.SupposeNot()
									negated := d.Have(
										"x is −y",
										"x = -y",
										ByArith(L, xm, ym, zeroSum))
									xHigh := d.Have(
										"so x lies in the power at v(y)",
										"x ∈ «power»(v(y))",
										negated.Rw(),
										By(negOwn))
									ordered := d.Have(
										"which gives v(y) ≤ v(x)",
										"v(y) ≤ v(x)",
										By(parts[0], parts[2], xHigh, membership.At(x, vy)))
									d.Show(
										"against v(x) < v(y)",
										ByArith(above, ordered))
								}))
							bounded := c.Have(
								"v(x + y) is at most v(x): else x = (x + y) − y would lie in the power at v(x) + 1",
								"v(x + y) ≤ v(x)",
								Derive(func(d *Argument) {
									exceeds := d.SupposeNot()
									higher := d.Have(
										"v(x) + 1 ≤ v(x + y)",
										"v(x) + 1 ≤ v(x + y)",
										ByArith(exceeds))
									sumAbove := d.Have(
										"x + y lies in the power at v(x) + 1",
										"x + y ∈ «power»(v(x) + 1)",
										By(sum, nonzeroSum, higher, membership.At(d.TermAs[A]("x + y"), next)))
									regroup := d.Have(
										"x = (x + y) + −y",
										"x = (x + y) + -y",
										ByArith(L, xm, ym))
									xAbove := d.Have(
										"so x lies in the power at v(x) + 1",
										"x ∈ «power»(v(x) + 1)",
										By(
											regroup,
											sumAbove,
											negAbove,
											members.At(next),
											submodule.SubmoduleAdd.At(scalars, vectors, nextPower, d.TermAs[A]("x + y"), d.TermAs[A]("-y"))))
									ordered := d.Have(
										"which gives v(x) + 1 ≤ v(x)",
										"v(x) + 1 ≤ v(x)",
										By(parts[0], parts[2], xAbove, membership.At(x, next)))
									d.Show(
										"a contradiction",
										ByArith(ordered))
								}))
							lowered := c.Have(
								"and at least v(x)",
								"v(x) ≤ v(x + y)",
								By(nonzeroSum, atLeast))
							c.Show(
								"so x + y is nonzero of order v(x)",
								ByArith(nonzeroSum, bounded, lowered))
						}))
					b.Show(
						"both bounds",
						By(atLeast, exact))
				}))
			a.Show(
				"the order is a valuation",
				Unfold(valuation_order.ValuationOrderDef),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("a"), b.FixAs[A]("b")
					parts := b.Conjuncts(
						b.Assume(),
						"a lies in L",
						"b lies in L",
						"a is not zero",
						"b is not zero")
					xm, ym := b.MemberOf[on.L](x, parts[0]), b.MemberOf[on.L](y, parts[1])
					product := b.Have(
						"v adds over the product",
						"v(a * b) = v(a) + v(b)",
						By(parts[0], parts[1], parts[2], parts[3], multiplicative.At(x, y)))
					b.Cases(b.TermAs[Bool]("v(a) ≤ v(b)"))
					b.When(
						"a has the smaller order",
						func(c *Argument, atMost Fact) {
							c.Show(
								"read the bounds at a and b",
								By(product, atMost, parts[0], parts[1], parts[2], parts[3], lower.At(x, y)))
						})
					b.Otherwise(
						"b has the smaller order",
						func(c *Argument, exceeds Fact) {
							atMost := c.Have(
								"v(b) ≤ v(a)",
								"v(b) ≤ v(a)",
								ByArith(exceeds))
							swap := c.Have(
								"b + a = a + b",
								"b + a = a + b",
								ByArith(L, xm, ym))
							c.Show(
								"read the bounds at b and a",
								By(product, exceeds, atMost, swap, parts[0], parts[1], parts[2], parts[3], lower.At(y, x)))
						})
				}))
		}),
})}
