// euler_criterion.go — the Legendre symbol read in a field of p elements;
// Euler's criterion, a^((p−1)/2) ≡ (a/p) mod an odd prime p, read there; and
// the symbol's laws: values, congruence, products, powers, (−1/p).

package quadratic_residue

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// LegendreInField — for a field F with a prime number p of elements, the
// Legendre symbol (a/p) maps to zero when a maps to zero, to one when a maps
// to the square of a nonzero element, and to −1 otherwise. Unfolding the
// symbol, its values 0, 1 and −1 map to zero, one and −1; p divides a exactly
// when a maps to zero; and a is a square mod p exactly when its image is a
// square in F, which for a nonzero image is a square of a nonzero element.
var LegendreInField = legendreInFieldThm{family.Add(registry.ProofEntry{
	Name: "LegendreInField",
	Key:  "prop_b90d4e451fa15dbc",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀a:int.",
		Hypotheses: []string{
			"nat_prime(p)",
			"has_size(F.carrier, p)",
		},
		Conclusion: "integer_map(field_ring(F), legendre_symbol(a, p)) = " +
			"COND(integer_map(field_ring(F), a) = F.zero, " +
			"    F.zero, " +
			"    COND(integer_map(field_ring(F), a) ∈ {z * z | z:A | z ∈ F.carrier ∧ z ≠ F.zero}, " +
			"        F.one, " +
			"        -F.one))",
	}, func(arg *Argument, F field.FieldFact[on.F], p *Expr[Nat], a *Expr[Int], prime, size Fact) {
		ring := field.RingOn.Read(F)
		integers := characteristic_zero.IntegerMapHomomorphism.Read(ring)
		one := arg.TermAs[Int]("1")
		nonzeroSquares := arg.Have(
			"a nonzero square is the square of a nonzero element, zero squaring to zero",
			Statement{
				Hypotheses: []string{"integer_map(field_ring(F), a) ≠ F.zero"},
				Conclusion: "(∃z:A. z ∈ F.carrier ∧ z * z = integer_map(field_ring(F), a)) ⇔ " +
					"integer_map(field_ring(F), a) ∈ {z * z | z:A | z ∈ F.carrier ∧ z ≠ F.zero}",
			},
			BySets(comm_ring.MulLeftZeroOn.Read(ring)))
		arg.Show(
			"the symbol's values 0, 1 and −1 map to zero, one "+
				"and −1, and its conditions are the ones on the right",
			Simp(Fwd(LegendreSymbolDef)),
			By(
				prime,
				size,
				finite_field.PrimeSizeCharacteristic.Read(F).At(p),
				finite_field.IntegerMapKernel.Read(F).At(p, a),
				finite_field.SquareModIff.Read(F).At(p, a),
				nonzeroSquares,
				ring_homomorphism.MapZero.Read(integers),
				ring_homomorphism.MapOne.Read(integers),
				ring_homomorphism.MapNeg.Read(integers).AsFact().At(one),
				set_basic.InUniv.At(one)))
	}),
})}

// EulerCriterion — Euler's criterion: for an odd prime p, a^((p−1)/2) is
// congruent to the Legendre symbol (a/p) modulo p. Both sides are read in a
// field F of p elements through the integers' map. F has characteristic p,
// so 2 ≠ 0 in F and two integers are congruent exactly when their images
// agree. If a maps to zero, so do a^h (h ≥ 1) and (a/p); otherwise the image
// d of a satisfies d^h = 1 when d is a nonzero square and d^h = −1 when it is
// not, which is the image of (a/p). The integers modulo p are such a field.
var EulerCriterion = eulerCriterionThm{family.Add(registry.ProofEntry{
	Name: "EulerCriterion",
	Key:  "prop_d61e4730f06b8bac",
	Build: family.Sections(Statement{
		Binders: "∀p:num. ∀a:int.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "a ^ «h»(p) ≡ legendre_symbol(a, p) (mod p)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		inField := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p:num. ∀a:int.",
			Hypotheses: []string{
				"nat_prime(p)",
				"p ≠ 2",
				"has_size(F.carrier, p)",
			},
			Conclusion: "a ^ «h»(p) ≡ legendre_symbol(a, p) (mod p)",
		}, func(arg *Argument, F field.FieldFact[on.F], p *Expr[Nat], a *Expr[Int], prime, odd, size Fact) {
			ring := field.RingOn.Read(F)
			powers := comm_ring.MulMonoidOn.Read(ring)
			half := arg.TermAs[Nat]("«h»(p)")
			image := arg.TermAs[A]("integer_map(field_ring(F), a)")
			characteristic := arg.Have(
				"F has characteristic p",
				"field_characteristic(F, p)",
				By(prime, size, finite_field.PrimeSizeCharacteristic.Read(F).At(p)))
			power := arg.Have(
				"a^h maps to the h-th power of the image of a",
				"integer_map(field_ring(F), a ^ «h»(p)) = "+
					"monoid_pow(F.mul, F.one, integer_map(field_ring(F), a), «h»(p))",
				By(characteristic_zero.IntegerMapPow.Read(ring).At(a, half)))
			images := arg.Have(
				"a^h and (a/p) have the same image in F",
				"integer_map(field_ring(F), a ^ «h»(p)) = integer_map(field_ring(F), legendre_symbol(a, p))",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("integer_map(field_ring(F), a) = F.zero"))
					b.When(
						"when a maps to zero, so do its positive power a^h and the symbol",
						func(c *Argument, zero Fact) {
							zeroM := c.MemberOf[on.F](c.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
							less := c.TermAs[Nat]("«h»(p) - 1")
							one := c.TermAs[Nat]("1")
							positive := c.Have(
								"h is positive, p being at least 3",
								"«h»(p) = «h»(p) - 1 + 1",
								ByArith(
									prime,
									odd,
									nat_prime.PrimeAtLeastTwo.At(p),
									nat_div_mod.LessEqRightDivEq.At(c.TermAs[Nat]("2"), c.TermAs[Nat]("p - 1"), one)))
							vanishes := c.Have(
								"a positive power of zero is zero",
								"monoid_pow(F.mul, F.one, F.zero, «h»(p)) = F.zero",
								ByArith(
									F,
									positive,
									comm_monoid.PowAddOn.Read(powers).At(zeroM, less, one),
									comm_monoid.PowOneOn.Read(powers).At(zeroM),
									comm_monoid.PowIn.Read(powers).At(zeroM, less)))
							c.Show(
								"the symbol of a multiple of p maps to zero",
								By(prime, size, zero, power, vanishes, LegendreInField.Read(F).At(p, a)))
						})
					b.Otherwise(
						"when a maps to a nonzero element, Euler's criterion "+
							"in F gives its h-th power ±1 as it is a square or not",
						func(c *Argument, nonzero Fact) {
							c.Show(
								"F has p elements, so h is half of its nonzero count",
								By(
									prime,
									odd,
									characteristic,
									finite_field.OddCharacteristicTwoNonzero.Read(F).At(p),
									nonzero,
									power,
									size,
									cardinality.HasSizeDef.At(c.TermAs[Set[A]]("F.carrier"), p),
									finite_field.FiniteFieldEulerCriterion.Read(F).At(
										c.MemberOf[on.F](image, characteristic_zero.IntegerMapInCarrier.Read(ring).At(a))),
									LegendreInField.Read(F).At(p, a)))
						})
				}))
			arg.Show(
				"integers with the same image are congruent mod p",
				By(
					characteristic,
					images,
					finite_field.IntegerMapEqIff.Read(F).At(
						p, arg.TermAs[Int]("a ^ «h»(p)"), arg.TermAs[Int]("legendre_symbol(a, p)"))))
		})

		return ctx.Theorem(headline, func(arg *Argument, p *Expr[Nat], a *Expr[Int], prime, odd Fact) {
			arg.Show(
				"the integers modulo p are a field with p elements",
				By(
					prime,
					odd,
					finite_field.PrimeFieldOn.At(p),
					finite_field.FiniteFieldDef,
					At(
						inField,
						arg.TermAs[FieldOps[Set[Int]]](
							"ideal_quotient_field(int_ring, ideal_span(int_ring, {int_of_num(p)}))"),
						p,
						a)))
		})
	}),
})}

// LegendreValues — the Legendre symbol takes only the values 0, 1 and −1, the
// three branches of its definition.
var LegendreValues = legendreValuesThm{family.Add(registry.ProofEntry{
	Name: "LegendreValues",
	Key:  "prop_94d1154b259f4c0b",
	Build: family.Theorem("∀a:int. ∀p:num. "+
		"    legendre_symbol(a, p) = 0 ∨ legendre_symbol(a, p) = 1 ∨ legendre_symbol(a, p) = -1",
		func(arg *Argument, a *Expr[Int], p *Expr[Nat]) {
			arg.Show(
				"each branch of the definition is one of them",
				By(LegendreSymbolDef.At(a, p)))
		}),
})}

// LegendreOne — (1/p) = 1 for every p other than 1: p does not divide 1, and
// 1 = 1·1 is a square modulo p, so the definition takes its middle branch.
var LegendreOne = legendreOneThm{family.Add(registry.ProofEntry{
	Name: "LegendreOne",
	Key:  "prop_9087c62fbea3fb59",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"p ≠ 1",
		},
		Conclusion: "legendre_symbol(1, p) = 1",
	}, func(arg *Argument, p *Expr[Nat], notOne Fact) {
		one := arg.TermAs[Int]("1")
		square := arg.Have(
			"1 = 1·1 is a square modulo p, the two sides leaving one remainder",
			"1 * &1 ≡ 1 (mod int_of_num(p))",
			By(int_congruence.CongruentIffSameRem.At(arg.TermAs[Int]("1 * &1"), one, arg.TermAs[Int]("p"))))
		arg.Show(
			"p divides 1 only when p = 1, so the symbol is the value at a nonzero square",
			By(
				notOne,
				square,
				LegendreSymbolDef.At(one, p),
				int_divides.OfNumDivides.At(p, arg.Ctx().Nat(1)),
				nat_divides.DividesOne.At(p)))
	}),
})}

// LegendreCongruent — integers congruent modulo p have the same Legendre
// symbol: congruent integers leave one remainder, so p divides both or
// neither, and x·x is congruent to one exactly when it is to the other.
var LegendreCongruent = legendreCongruentThm{family.Add(registry.ProofEntry{
	Name: "LegendreCongruent",
	Key:  "prop_38ae82e7f9c8bee0",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:int. ∀p:num.",
		Hypotheses: []string{"a ≡ b (mod p)"},
		Conclusion: "legendre_symbol(a, p) = legendre_symbol(b, p)",
	}, func(arg *Argument, a, b *Expr[Int], p *Expr[Nat], congruent Fact) {
		modulus := arg.TermAs[Int]("p")
		divides := arg.Have(
			"p divides a exactly when it divides b, the two leaving one remainder",
			"p ∣ a ⇔ p ∣ b",
			By(
				Normalized,
				congruent,
				int_congruence.CongruentIffSameRem.At(a, b, modulus),
				int_div_rem.DividesIffRemZero.At(a, modulus),
				int_div_rem.DividesIffRemZero.At(b, modulus)))
		squares := arg.Have(
			"a square is congruent to a exactly when it is to b",
			"(∃x:int. x * x ≡ a (mod p)) ⇔ (∃x:int. x * x ≡ b (mod p))",
			By(congruent, int_congruence.CongruentIffSameRem))
		arg.Show(
			"so the symbol's two conditions agree at a and at b",
			By(divides, squares, LegendreSymbolDef.At(a, p), LegendreSymbolDef.At(b, p)))
	}),
})}

// LegendreMul — the Legendre symbol modulo an odd prime is multiplicative:
// by Euler's criterion (ab/p) and (a/p)(b/p) are both congruent to
// (ab)^h = a^h·b^h, and two values between −1 and 1 congruent modulo p are
// equal.
var LegendreMul = legendreMulThm{family.Add(registry.ProofEntry{
	Name: "LegendreMul",
	Key:  "prop_d60031c877aed2d2",
	Build: family.Theorem(Statement{
		Binders: "∀a b:int. ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "legendre_symbol(a * b, p) = legendre_symbol(a, p) * legendre_symbol(b, p)",
	}, func(arg *Argument, a, b *Expr[Int], p *Expr[Nat], prime, odd Fact) {
		half := arg.TermAs[Nat]("«h»(p)")
		product := arg.TermAs[Int]("a * b")
		symbolA := arg.TermAs[Int]("legendre_symbol(a, p)")
		symbolB := arg.TermAs[Int]("legendre_symbol(b, p)")
		congruent := arg.Have(
			"(ab/p) and (a/p)(b/p) are both congruent to (ab)^h = a^h·b^h",
			"legendre_symbol(a * b, p) ≡ legendre_symbol(a, p) * legendre_symbol(b, p) (mod p)",
			By(
				prime,
				odd,
				EulerCriterion.At(p, a),
				EulerCriterion.At(p, b),
				EulerCriterion.At(p, product),
				int_pow.MulPow.At(a, b, half),
				int_congruence.MulCongruent.At(
					arg.TermAs[Int]("a ^ «h»(p)"),
					symbolA,
					arg.TermAs[Int]("b ^ «h»(p)"),
					symbolB,
					arg.TermAs[Int]("p")),
				int_congruence.CongruentIffSameRem))
		bounds := arg.Have(
			"each symbol lies between −1 and 1",
			"-1 ≤ legendre_symbol(a * b, p) ∧ "+
				"legendre_symbol(a * b, p) ≤ 1 ∧ "+
				"-1 ≤ legendre_symbol(a, p) ∧ "+
				"legendre_symbol(a, p) ≤ 1 ∧ "+
				"-1 ≤ legendre_symbol(b, p) ∧ "+
				"legendre_symbol(b, p) ≤ 1",
			ByArith(LegendreValues.At(product, p), LegendreValues.At(a, p), LegendreValues.At(b, p)))
		productBounds := arg.Have(
			"so does the product of two of them",
			"-1 ≤ legendre_symbol(a, p) * legendre_symbol(b, p) ∧ "+
				"legendre_symbol(a, p) * legendre_symbol(b, p) ≤ 1",
			ByArith(bounds))
		arg.Show(
			"two congruent values between −1 and 1 are equal",
			By(
				prime,
				odd,
				bounds,
				productBounds,
				congruent,
				int_congruence.EqOfCongruentSigns.At(p, arg.TermAs[Int]("legendre_symbol(a * b, p)"),
					arg.TermAs[Int]("legendre_symbol(a, p) * legendre_symbol(b, p)"))))
	}),
})}

// LegendrePow — the symbol of a power is the power of the symbol: for an
// odd prime p, (aᵏ/p) = (a/p)ᵏ. By induction on k. At k = 0 both sides
// are 1; one more factor a splits off by multiplicativity.
var LegendrePow = legendrePowThm{family.Add(registry.ProofEntry{
	Name: "LegendrePow",
	Key:  "prop_38172cbb26abbea7",
	Build: family.Theorem(Statement{
		Binders: "∀a:int. ∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "legendre_symbol(a ^ k, p) = legendre_symbol(a, p) ^ k",
	}, func(arg *Argument, a *Expr[Int], p *Expr[Nat], prime, odd Fact) {
		arg.Induct("k")
		arg.Base(
			"a⁰ = 1 and (a/p)⁰ = 1, so this is (1/p) = 1, the prime p not being 1",
			Simp(Fwd(int_pow.PowClauses)),
			By(prime, nat_prime.PrimeDef.At(p), LegendreOne.At(p)))
		arg.Step(
			"aᵏ⁺¹ = a·aᵏ, and the symbol splits over the product",
			func(b *Argument, power Fact) {
				b.Show(
					"(a·aᵏ/p) = (a/p)·(aᵏ/p), and (aᵏ/p) = (a/p)ᵏ",
					Simp(Fwd(int_pow.PowClauses)),
					power.RwRev(),
					By(prime, odd, LegendreMul.At(a, b.TermAs[Int]("a ^ k"), p)))
			})
	}),
})}

// LegendreMinusOne — for an odd prime p, (−1/p) = (−1)^((p−1)/2): Euler's
// criterion at −1, both sides lying between −1 and 1.
var LegendreMinusOne = legendreMinusOneThm{family.Add(registry.ProofEntry{
	Name: "LegendreMinusOne",
	Key:  "prop_75ff9b9082cfe19a",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "legendre_symbol(-1, p) = (-1) ^ «h»(p)",
	}, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
		minusOne := arg.TermAs[Int]("-1")
		symbol := arg.TermAs[Int]("legendre_symbol(-1, p)")
		power := arg.TermAs[Int]("(-&1) ^ «h»(p)")
		bounds := arg.Have(
			"the symbol and the power of −1 lie between −1 and 1",
			"-int_of_num(1) ≤ legendre_symbol(-int_of_num(1), p) ∧ "+
				"legendre_symbol(-int_of_num(1), p) ≤ int_of_num(1) ∧ "+
				"-int_of_num(1) ≤ (-int_of_num(1)) ^ «h»(p) ∧ "+
				"(-int_of_num(1)) ^ «h»(p) ≤ int_of_num(1)",
			ByArith(LegendreValues.At(minusOne, p), int_pow.NegOnePowValues.At(arg.TermAs[Nat]("«h»(p)"))))
		arg.Show(
			"congruent by Euler's criterion, they are equal",
			By(
				prime,
				odd,
				bounds,
				EulerCriterion.At(p, minusOne),
				int_congruence.EqOfCongruentSigns.At(p, power, symbol)))
	}),
})}
