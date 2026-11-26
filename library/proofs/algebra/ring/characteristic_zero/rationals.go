// rationals.go — the rational map into a field of characteristic zero: rationals as integer
// fractions, the rational image as a subfield on which rational_value inverts the map, common
// denominators of finitely many rational values, and integer weighted sums and their bounds.

package characteristic_zero

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// RationalIntegerFraction — a rational is a native integer divided by a
// positive natural. A signed natural denominator supplies the magnitude, and
// its sign moves into the numerator.
var RationalIntegerFraction = rationalIntegerFractionThm{family.Add(registry.ProofEntry{
	Name: "RationalIntegerFraction",
	Key:  "prop_b2620f22e2cf07c",
	Build: family.Theorem(Statement{
		Binders: "∀r:real.",
		Hypotheses: []string{
			"rational(r)",
		},
		Conclusion: "∃a:int. ∃d:num. 0 < d ∧ r = real_of_int(a) / real_of_num(d)",
	}, func(a *Argument, r *Expr[Real], _ Fact) {
		m, n, fraction := a.Obtain2As[Real, Real](
			"write the rational as a quotient of real integers",
			"∃m n:real. integer(m) ∧ integer(n) ∧ n ≠ real_of_num(0) ∧ r = m / n",
			Unfold(rational.RationalDef))
		d, signed := a.ObtainAs[Nat](
			"write the denominator as a signed natural",
			"∃d:num. n = real_of_num(d) ∨ n = -real_of_num(d)",
			By(fraction, int_construction.IntegerIffPlusMinusNat.At(n)))
		positive := a.Have(
			"the nonzero denominator has positive magnitude",
			"0 < d",
			Derive(func(b *Argument) {
				b.Cases(b.Term("d = 0"))
				b.When(
					"zero magnitude would make the denominator vanish",
					func(c *Argument, zero Fact) {
						c.Show(
							"the zero magnitude is impossible",
							ByArith(zero, fraction, signed))
					})
				b.Otherwise(
					"a nonzero natural is positive",
					func(c *Argument, nonzero Fact) {
						c.Show(
							"the magnitude is positive",
							ByArith(nonzero))
					})
			}))
		a.Show(
			"choose the numerator according to the denominator's sign",
			signed.SplitDisj(
				LeftHolds(
					"a positive denominator keeps the numerator",
					Given(func(b *Argument, denominator Fact) {
						b.Take(b.TermAs[Int]("int_of_real(m)"))
						b.Take(d)
						b.Show(
							"the integer representative gives the required fraction",
							By(Normalized, positive, denominator, fraction, At(int_construction.IntDef.Membership, m)))
					})),
				RightHolds(
					"a negative denominator negates the numerator",
					Given(func(b *Argument, denominator Fact) {
						b.Take(b.TermAs[Int]("int_of_real(-m)"))
						b.Take(d)
						b.Show(
							"the denominator magnitude is positive and the quotient is unchanged",
							SplitConj(
								Case(
									"the magnitude stays positive",
									By(positive)),
								Case(
									"transfer the denominator's minus sign into the numerator",
									CalcEq(
										Leg(
											b.Term("m / n"),
											"the original integer quotient",
											By(fraction)),
										Leg(
											b.Term("-m / real_of_num(d)"),
											"move the minus sign",
											CalcEq(
												Leg(
													b.Term("m / (-real_of_num(d))"),
													"substitute the signed denominator",
													By(Normalized, denominator)),
												FinalLeg(
													"inverse and multiplication preserve the sign transfer",
													Simp(
														Fwd(real_field.RealDivDef),
														Fwd(field.InvNeg.Read(real_field.Field)),
														Fwd(real_ring.MulLeftNeg),
														Fwd(real_ring.MulRightNeg)),
													Basic()))),
										FinalLeg(
											"replace the negated integer by its native representative",
											By(
												Normalized,
												fraction,
												int_construction.IntegerClosedUnderNeg.At(m),
												At(int_construction.IntDef.Membership, b.TermAs[Real]("-m"))))))))
					}))))
	}),
})}

// RationalMapFraction — in characteristic zero the rational map sends an
// integer fraction with a positive natural denominator to the corresponding
// fraction in the field.
// Cross multiplication makes the value independent of the integer
// presentation the definition selects.
var RationalMapFraction = rationalMapFractionThm{family.Add(registry.ProofEntry{
	Name: "RationalMapFraction",
	Key:  "prop_8498e6c748f9bf2c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀m:int. ∀d:num.",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"0 < d",
		},
		Conclusion: "rational_map(L, real_of_int(m) / real_of_num(d)) = " +
			"integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d))",
	}, func(a *Argument, L field.FieldFact[on.L], m *Expr[Int], d *Expr[Nat], data Fact) {
		ring := field.RingOn.Read(L)
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		dn := a.TermAs[Int]("d")
		zeroNat := a.TermAs[Nat]("0")
		zeroInt := a.TermAs[Int]("0")
		independent := a.Have(
			"equal integer fractions give equal field values",
			Statement{
				Binders: "∀p n:int.",
				Hypotheses: []string{
					"n ≠ 0",
					"real_of_int(m) / real_of_num(d) = real_of_int(p) / real_of_int(n)",
				},
				Conclusion: "integer_map(field_ring(L), p) * L.inv(integer_map(field_ring(L), n)) = " +
					"integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d))",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Int]("p")
				n := b.FixAs[Int]("n")
				fraction := b.Assume()
				realNonzero := b.Have(
					"both real denominator representatives are nonzero",
					"real_of_int(n) ≠ real_of_num(0) ∧ real_of_int(d) ≠ real_of_num(0)",
					ByArith(
						data,
						fraction,
						int_construction.RepresentativeInjective.At(n, zeroInt),
						int_construction.OfNumBridge.At(zeroNat),
						real_order_ring.OfNumLessThan.At(zeroNat, d),
						int_construction.OfNumBridge.At(d)))
				realCross := b.Have(
					"clear the two real denominators",
					"real_of_int(m) * real_of_int(n) = real_of_int(p) * real_of_num(d)",
					Derive(func(c *Argument) {
						parts := c.Conjuncts(
							fraction,
							"the signed denominator is nonzero",
							"the real fractions agree")
						c.Show(
							"multiplication by both denominators clears the inverses",
							ByArith(
								realNonzero,
								Scaled(c.TermAs[Real]("real_of_num(d) * real_of_int(n)"), parts[1]),
								Scaled(c.TermAs[Real]("real_of_int(p) * real_of_num(d)"),
									field.MulRightInverse.Read(real_field.Field).At(c.TermAs[Real]("real_of_int(n)"))),
								Scaled(c.TermAs[Real]("real_of_int(m) * real_of_int(n)"),
									field.MulRightInverse.Read(real_field.Field).At(c.TermAs[Real]("real_of_int(d)"))),
								int_construction.OfNumBridge.At(d)))
					}))
				nativeCross := b.Have(
					"reflect cross multiplication into native integers",
					"m * n = p * d",
					By(
						realCross,
						int_construction.MulBridge.At(m, n),
						int_construction.MulBridge.At(p, dn),
						int_construction.OfNumBridge.At(d),
						int_construction.RepresentativeInjective.At(b.TermAs[Int]("m * n"), b.TermAs[Int]("p * &d"))))
				hostCross := b.Have(
					"transport cross multiplication into the field",
					"integer_map(field_ring(L), m) * integer_map(field_ring(L), n) = "+
						"integer_map(field_ring(L), p) * integer_map(field_ring(L), d)",
					By(L, nativeCross, ring, IntegerMapHom.Read(ring)))
				hostNonzero := b.Have(
					"both integer denominator images are nonzero",
					"integer_map(field_ring(L), n) ≠ L.zero ∧ integer_map(field_ring(L), d) ≠ L.zero",
					Derive(func(c *Argument) {
						injective := c.Have(
							"characteristic zero makes the integer map injective",
							"injective_on(𝕌, integer_map(field_ring(L)))",
							By(L, data, ring, IntegerMapInjective.At(R)))
						mapZero := c.Have(
							"the integer zero maps to the field zero",
							"integer_map(field_ring(L), 0) = L.zero",
							By(L, ring, IntegerMapHom.Read(ring)))
						c.Show(
							"injectivity handles the signed denominator and characteristic zero handles the positive one",
							SplitConj(
								Case(
									"the nonzero signed denominator has nonzero image",
									BySets(
										mapZero,
										injective,
										fraction,
										functions.InjectiveOnDef.At(
											c.TermAs[Set[Int]]("𝕌"), c.TermAs[Fun[Int, A]]("integer_map(field_ring(L))")))),
								Case(
									"characteristic zero keeps the positive denominator's image nonzero",
									By(data, IntegerMapPositiveNonzero.Read(ring).At(d)))))
					}))
				inCarrier := IntegerMapInCarrier.Read(ring)
				b.Show(
					"cancel both denominator images in the transported equation",
					ByArith(
						L,
						hostNonzero,
						Scaled(
							b.TermAs[A]("L.inv(integer_map(field_ring(L), n)) * L.inv(integer_map(field_ring(L), d))"),
							hostCross),
						inCarrier.At(m),
						inCarrier.At(n),
						inCarrier.At(p),
						inCarrier.At(dn),
						field.InvIn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), n)")),
						field.InvIn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), d)")),
						Scaled(b.TermAs[A]("integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d))"),
							field.MulRightInverseOn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), n)"))),
						Scaled(b.TermAs[A]("integer_map(field_ring(L), p) * L.inv(integer_map(field_ring(L), n))"),
							field.MulRightInverseOn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), d)")))))
			}))
		isRational := a.Have(
			"the given integer fraction is rational",
			"rational(real_of_int(m) / real_of_num(d))",
			By(
				rational.RationalDiv.At(a.TermAs[Real]("real_of_int(m)"), a.TermAs[Real]("real_of_num(d)")),
				rational.IntegerRational.At(a.TermAs[Real]("real_of_int(m)")),
				int_construction.RepresentativeIsInteger.At(m),
				rational.OfNumRational.At(d)))
		candidate := a.Have(
			"the canonical numerator and denominator realize the proposed value",
			"∃p n:int. "+
				"    n ≠ 0 ∧ "+
				"    real_of_int(m) / real_of_num(d) = real_of_int(p) / real_of_int(n) ∧ "+
				"    integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d)) = "+
				"    integer_map(field_ring(L), p) * L.inv(integer_map(field_ring(L), n))",
			Derive(func(b *Argument) {
				b.Take(m)
				b.Take(dn)
				b.Show(
					"the positive denominator supplies a valid presentation",
					ByArith(data, int_construction.OfNumBridge.At(d), int_embed.OfNumEq.At(d, zeroNat)))
			}))
		a.Do(Unfold(rationalMapDef))
		_, selected := a.ObtainChosen(
			"the canonical fraction value inhabits the defining choice",
			"∃a:A. ∃p n:int. "+
				"    n ≠ 0 ∧ "+
				"    real_of_int(m) / real_of_num(d) = real_of_int(p) / real_of_int(n) ∧ "+
				"    a = integer_map(field_ring(L), p) * L.inv(integer_map(field_ring(L), n))",
			candidate)
		p, n, chosenFraction := a.Unpack2As[Int, Int](selected, "p", "n")
		a.Show(
			"the selected presentation has the common fraction value",
			By(isRational, chosenFraction, independent.At(p, n)))
	}),
})}

// RationalEmbedding — in characteristic zero the rational map embeds the
// rational numbers as a subfield, agreeing with the integer map. Common
// denominators transfer arithmetic and injectivity from the integer map, and
// rational_value is the inverse on the image.
var RationalEmbedding = rationalEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "RationalEmbedding",
	Key:  "prop_71dd09e4962a529",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
		},
		Conclusion: "subfield(L, rational_image(L)) ∧ " +
			"injective_on({r:real | rational(r)}, rational_map(L)) ∧ " +
			"(∀z:int. rational_map(L, real_of_int(z)) = integer_map(field_ring(L), z)) ∧ " +
			"(∀r s:real. " +
			"    rational(r) ∧ rational(s) ⇒ " +
			"    rational_map(L, r + s) = rational_map(L, r) + rational_map(L, s) ∧ " +
			"    rational_map(L, r * s) = rational_map(L, r) * rational_map(L, s)) ∧ " +
			"(∀r:real. rational(r) ⇒ rational_value(L, rational_map(L, r)) = r) ∧ " +
			"(∀a:A. a ∈ rational_image(L) ⇒ rational_map(L, rational_value(L, a)) = a)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerValues := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀z:int. rational_map(L, real_of_int(z)) = integer_map(field_ring(L), z)",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, z *Expr[Int]) {
			l := a.TermAs[FieldOps[A]]("L")
			integerIn := IntegerMapInCarrier.Read(field.RingOn.Read(L))
			one := a.TermAs[Nat]("1")
			fraction := a.Have(
				"an integer is its fraction with denominator one",
				"real_of_int(z) = real_of_int(z) / real_of_num(1)",
				ByArith())
			a.Show(
				"evaluate the denominator-one fraction",
				CalcEq(
					Leg(
						a.TermAs[A]("rational_map(L, real_of_int(z) / real_of_num(1))"),
						"use the denominator-one presentation",
						By(Normalized, fraction)),
					Leg(
						a.TermAs[A]("integer_map(field_ring(L), z) * L.inv(integer_map(field_ring(L), 1))"),
						"apply the fraction formula",
						By(L, characteristic, RationalMapFraction.At(l, z, one))),
					FinalLeg(
						"the image and inverse of one are one",
						ByArith(L, integerIn.At(z), IntegerMapHom.Read(field.RingOn.Read(L)), field.InvOneOn.Read(L)))))
		})
		rationalIn := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀r:real. rational(r) ⇒ rational_map(L, r) ∈ L.carrier",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, r *Expr[Real], isRational Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			integerIn := IntegerMapInCarrier.Read(field.RingOn.Read(L))
			m, d, fraction := a.Obtain2As[Int, Nat](
				"choose an integer fraction with positive denominator",
				"∃m:int. ∃d:num. 0 < d ∧ r = real_of_int(m) / real_of_num(d)",
				By(isRational, RationalIntegerFraction.At(r)))
			a.Show(
				"integer multiplication and field inversion keep the value in the carrier",
				By(
					L,
					characteristic,
					fraction,
					RationalMapFraction.At(l, m, d),
					integerIn.At(m),
					integerIn.At(a.TermAs[Int]("d")),
					field.InvIn.Read(L).AsFact().At(a.TermAs[A]("integer_map(field_ring(L), d)")),
					comm_ring.MulIn.Read(field.RingOn.Read(L)).AsFact().At(a.TermAs[A]("integer_map(field_ring(L), m)"),
						a.TermAs[A]("L.inv(integer_map(field_ring(L), d))"))))
		})
		pairFractions := ctx.Lemma(Statement{
			Binders:    "∀r s:real.",
			Hypotheses: []string{"rational(r)", "rational(s)"},
			Conclusion: "∃d:num. ∃m n:int. " +
				"    0 < d ∧ r = real_of_int(m) / real_of_num(d) ∧ s = real_of_int(n) / real_of_num(d)",
		}, func(a *Argument, r, s *Expr[Real], rationals Fact) {
			finitePair := a.Have(
				"the two-point set is finite",
				"finite({r, s})",
				Simp(Fwd(finite_set.FiniteInsert)),
				Cite(finite_set.FiniteRules.Inst[Real]()))
			rationalPair := a.Have(
				"each point of the pair is rational",
				"∀x:real. x ∈ {r, s} ⇒ rational(x)",
				BySets(rationals))
			d, common := a.ObtainAs[Nat](
				"clear the denominators of the two rational points",
				"∃d:num. 0 < d ∧ (∀x:real. x ∈ {r, s} ⇒ ∃z:int. real_of_num(d) * x = real_of_int(z))",
				By(finitePair, rationalPair, RationalCommonDenominator.At(a.TermAs[Set[Real]]("{r, s}"))))
			parts := a.Conjuncts(
				common,
				"the common denominator is positive",
				"the common denominator clears both points")
			m, clearR := a.ObtainAs[Int](
				"choose the first native numerator",
				"∃m:int. real_of_num(d) * r = real_of_int(m)",
				BySets(parts[1].At(r)))
			n, clearS := a.ObtainAs[Int](
				"choose the second native numerator",
				"∃n:int. real_of_num(d) * s = real_of_int(n)",
				BySets(parts[1].At(s)))
			a.Take(d)
			a.Take(m)
			a.Take(n)
			a.Show(
				"divide the two cleared equations by the positive common denominator",
				ByArith(
					parts[0],
					clearR,
					clearS,
					real_order_ring.OfNumLessThan.At(a.TermAs[Nat]("0"), d),
					real_order_field.EqDivMulLeft.At(
						r, a.TermAs[Real]("real_of_int(m)"), a.TermAs[Real]("real_of_num(d)")),
					real_order_field.EqDivMulLeft.At(
						s, a.TermAs[Real]("real_of_int(n)"), a.TermAs[Real]("real_of_num(d)"))))
		})
		add := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀r s:real. " +
				"    rational(r) ∧ rational(s) ⇒ rational_map(L, r + s) = rational_map(L, r) + rational_map(L, s)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			characteristic Fact,
			r, s *Expr[Real],
			rationals Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			integerIn := IntegerMapInCarrier.Read(field.RingOn.Read(L))
			d, m, n, fractions := a.Obtain3As[Nat, Int, Int](
				"write both rational arguments over one positive denominator",
				"∃d:num. ∃m n:int. "+
					"    0 < d ∧ r = real_of_int(m) / real_of_num(d) ∧ s = real_of_int(n) / real_of_num(d)",
				By(rationals, At(pairFractions, r, s)))
			sumFraction := a.Have(
				"the numerator of the sum is the native numerator sum",
				"r + s = real_of_int(m + n) / real_of_num(d)",
				ByArith(
					fractions,
					Scaled(a.TermAs[Real]("real_inv(real_of_num(d))"), int_construction.AddBridge.At(m, n))))
			a.Show(
				"a common denominator transports addition",
				CalcEq(
					Leg(
						a.TermAs[A]("integer_map(field_ring(L), m + n) * L.inv(integer_map(field_ring(L), d))"),
						"evaluate the sum fraction",
						By(
							L,
							characteristic,
							fractions,
							sumFraction,
							RationalMapFraction.At(l, a.TermAs[Int]("m + n"), d))),
					Leg(
						a.TermAs[A](
							"integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d)) + "+
								"integer_map(field_ring(L), n) * L.inv(integer_map(field_ring(L), d))"),
						"distribute the common inverse across the numerator sum",
						Derive(func(b *Argument) {
							integerSum := b.Have(
								"the integer map preserves the numerator sum",
								"integer_map(field_ring(L), m + n) = integer_map(field_ring(L), m) + integer_map(field_ring(L), n)",
								By(IntegerMapHom.Read(field.RingOn.Read(L))))
							b.Show(
								"distributivity gives the two evaluated fractions",
								ByArith(
									L,
									Scaled(b.TermAs[A]("L.inv(integer_map(field_ring(L), d))"), integerSum),
									integerIn.At(m),
									integerIn.At(n),
									integerIn.At(b.TermAs[Int]("m + n")),
									integerIn.At(b.TermAs[Int]("d")),
									field.InvIn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), d)"))))
						})),
					FinalLeg(
						"recognize the two rational images",
						By(
							L,
							characteristic,
							fractions,
							RationalMapFraction.At(l, m, d),
							RationalMapFraction.At(l, n, d)))))
		})
		mul := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀r s:real. " +
				"    rational(r) ∧ rational(s) ⇒ rational_map(L, r * s) = rational_map(L, r) * rational_map(L, s)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			characteristic Fact,
			r, s *Expr[Real],
			rationals Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			integerIn := IntegerMapInCarrier.Read(field.RingOn.Read(L))
			d, m, n, fractions := a.Obtain3As[Nat, Int, Int](
				"write the factors over one positive denominator",
				"∃d:num. ∃m n:int. "+
					"    0 < d ∧ r = real_of_int(m) / real_of_num(d) ∧ s = real_of_int(n) / real_of_num(d)",
				By(rationals, At(pairFractions, r, s)))
			productFraction := a.Have(
				"multiply native numerators and square the denominator",
				"r * s = real_of_int(m * n) / real_of_num(d * d)",
				Derive(func(b *Argument) {
					parts := b.Conjuncts(
						fractions,
						"the denominator is positive",
						"the first factor is its fraction",
						"the second factor is its fraction")
					b.Show(
						"the real inverse of the squared denominator splits into two inverses",
						Simp(
							Fwd(parts[1]),
							Fwd(parts[2]),
							Fwd(real_field.RealDivDef),
							Fwd(int_construction.MulBridge),
							Fwd(real_construction.OfNumMul),
							Fwd(field.InvMul.Read(real_field.Field))),
						ByArith())
				}))
			positiveSquare := a.Have(
				"the product denominator remains positive",
				"0 < d * d",
				ByArith(fractions, nat_order.LessThanMulCancel.At(d, a.TermAs[Nat]("0"), d)))
			a.Show(
				"the fraction formula transports multiplication",
				CalcEq(
					Leg(
						a.TermAs[A](
							"integer_map(field_ring(L), m * n) * L.inv(integer_map(field_ring(L), int_of_num(d * d)))"),
						"evaluate the product fraction",
						By(
							L,
							characteristic,
							positiveSquare,
							productFraction,
							RationalMapFraction.At(l, a.TermAs[Int]("m * n"), a.TermAs[Nat]("d * d")))),
					Leg(
						a.TermAs[A](
							"(integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d))) * "+
								"(integer_map(field_ring(L), n) * L.inv(integer_map(field_ring(L), d)))"),
						"split the numerator and inverse denominator products",
						Derive(func(b *Argument) {
							integerProduct := b.Have(
								"the integer map preserves the numerator product",
								"integer_map(field_ring(L), m * n) = integer_map(field_ring(L), m) * integer_map(field_ring(L), n)",
								By(IntegerMapHom.Read(field.RingOn.Read(L))))
							denominatorProduct := b.Have(
								"the squared natural denominator maps to the square of its image",
								"integer_map(field_ring(L), int_of_num(d * d)) = "+
									"integer_map(field_ring(L), d) * integer_map(field_ring(L), d)",
								By(IntegerMapHom.Read(field.RingOn.Read(L)), int_embed.OfNumMul.At(d, d)))
							denominatorIn := b.Have(
								"the denominator image belongs to the field",
								"integer_map(field_ring(L), d) ∈ L.carrier",
								By(L, integerIn.At(b.TermAs[Int]("d"))))
							inverseProduct := b.Have(
								"the inverse denominator square is the square of its inverse",
								"L.inv(integer_map(field_ring(L), int_of_num(d * d))) = "+
									"L.inv(integer_map(field_ring(L), d)) * L.inv(integer_map(field_ring(L), d))",
								By(
									denominatorProduct,
									denominatorIn,
									field.InvMulOn.Read(L).AsFact().At(
										b.TermAs[A]("integer_map(field_ring(L), d)"), b.TermAs[A]("integer_map(field_ring(L), d)"))))
							b.Show(
								"regroup the two evaluated factors",
								Simp(Fwd(integerProduct), Fwd(inverseProduct)),
								ByArith(
									L,
									denominatorIn,
									integerIn.At(m),
									integerIn.At(n),
									field.InvIn.Read(L).AsFact().At(b.TermAs[A]("integer_map(field_ring(L), d)"))))
						})),
					FinalLeg(
						"recognize the images of the two factors",
						By(
							L,
							characteristic,
							fractions,
							RationalMapFraction.At(l, m, d),
							RationalMapFraction.At(l, n, d)))))
		})
		injective := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "injective_on({r:real | rational(r)}, rational_map(L))",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			a.Do(Simp(Fwd(functions.InjectiveOnDef)))
			x := a.FixAs[Real]("x")
			y := a.FixAs[Real]("y")
			equalImages := a.Assume()
			rationals := a.Have(
				"the two arguments are rational",
				"rational(x) ∧ rational(y)",
				BySets(equalImages))
			integerIn := IntegerMapInCarrier.Read(field.RingOn.Read(L))
			d, m, n, fractions := a.Obtain3As[Nat, Int, Int](
				"put both arguments over a common denominator",
				"∃d:num. ∃m n:int. "+
					"    0 < d ∧ x = real_of_int(m) / real_of_num(d) ∧ y = real_of_int(n) / real_of_num(d)",
				By(rationals, At(pairFractions, x, y)))
			equalFractions := a.Have(
				"the evaluated fractions agree",
				"integer_map(field_ring(L), m) * L.inv(integer_map(field_ring(L), d)) = "+
					"integer_map(field_ring(L), n) * L.inv(integer_map(field_ring(L), d))",
				By(
					L,
					characteristic,
					equalImages,
					fractions,
					RationalMapFraction.At(l, m, d),
					RationalMapFraction.At(l, n, d)))
			denominatorNonzero := a.Have(
				"characteristic zero makes the positive denominator image nonzero",
				"integer_map(field_ring(L), d) ≠ L.zero",
				By(characteristic, fractions, IntegerMapPositiveNonzero.Read(field.RingOn.Read(L)).At(d)))
			equalNumerators := a.Have(
				"cancel the common denominator image",
				"integer_map(field_ring(L), m) = integer_map(field_ring(L), n)",
				ByArith(
					L,
					denominatorNonzero,
					Scaled(a.TermAs[A]("integer_map(field_ring(L), d)"), equalFractions),
					integerIn.At(m),
					integerIn.At(n),
					integerIn.At(a.TermAs[Int]("d")),
					field.InvIn.Read(L).AsFact().At(a.TermAs[A]("integer_map(field_ring(L), d)")),
					Scaled(a.TermAs[A]("integer_map(field_ring(L), m) - integer_map(field_ring(L), n)"),
						field.MulRightInverseOn.Read(L).AsFact().At(a.TermAs[A]("integer_map(field_ring(L), d)")))))
			integerInjective := a.Have(
				"the integer map is injective",
				"injective_on(𝕌, integer_map(field_ring(L)))",
				By(
					L,
					characteristic,
					field.RingOn.Read(L),
					IntegerMapInjective.At(a.TermAs[RingOps[A]]("field_ring(L)"))))
			nativeEqual := a.Have(
				"the native numerators agree",
				"m = n",
				Derive(func(b *Argument) {
					pointwise := b.Unfolded(integerInjective, functions.InjectiveOnDef)
					b.Show(
						"read injectivity at the two native numerators",
						BySets(equalNumerators, pointwise.At(m, n)))
				}))
			a.Show(
				"the common-denominator fractions are equal",
				By(Normalized, nativeEqual, fractions))
		})
		zeroOne := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "rational_map(L, real_of_num(0)) = L.zero ∧ rational_map(L, real_of_num(1)) = L.one",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			a.Show(
				"the rational map agrees with the integer map at zero and one",
				By(
					Normalized,
					L,
					characteristic,
					IntegerMapHom.Read(field.RingOn.Read(L)),
					At(integerValues, l, a.TermAs[Int]("0")),
					At(integerValues, l, a.TermAs[Int]("1")),
					int_construction.OfNumBridge.At(a.TermAs[Nat]("0")),
					int_construction.OfNumBridge.At(a.TermAs[Nat]("1"))))
		})
		neg := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀r:real. rational(r) ⇒ rational_map(L, -r) = -rational_map(L, r)",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, r *Expr[Real], isRational Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			negativeRational := a.Have(
				"the negative argument is rational",
				"rational(-r)",
				By(isRational, rational.RationalNeg.At(r)))
			realZero := a.Have(
				"opposite real arguments add to zero",
				"r + (-r) = real_of_num(0)",
				ByArith())
			imageZero := a.Have(
				"the images of opposite arguments add to the field zero",
				"rational_map(L, r) + rational_map(L, -r) = L.zero",
				By(
					L,
					characteristic,
					isRational,
					negativeRational,
					realZero,
					At(add, l, r, a.TermAs[Real]("-r")),
					At(zeroOne, l)))
			a.Show(
				"the two image values are additive opposites",
				ByArith(
					L,
					characteristic,
					isRational,
					negativeRational,
					imageZero,
					At(rationalIn, l, r),
					At(rationalIn, l, a.TermAs[Real]("-r"))))
		})
		inv := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "∀r:real. rational(r) ⇒ rational_map(L, real_inv(r)) = L.inv(rational_map(L, r))",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, r *Expr[Real], isRational Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			nonzero := a.Unless(
				a.Term("r = real_of_num(0)"),
				"inversion fixes zero on both sides",
				Derive(func(b *Argument) {
					zero := b.Hyp("r = real_of_num(0)")
					b.Show(
						"the zero values and their inverses agree",
						By(
							L,
							characteristic,
							isRational,
							zero,
							At(zeroOne, l),
							field.InvZero.Read(real_field.Field),
							field.InvZeroOn.Read(L)))
				}))
			inverseRational := a.Have(
				"the reciprocal argument is rational",
				"rational(real_inv(r))",
				By(isRational, rational.RationalInv.At(r)))
			realOne := a.Have(
				"a nonzero real times its reciprocal is one",
				"r * real_inv(r) = real_of_num(1)",
				By(nonzero, field.MulRightInverse.Read(real_field.Field).At(r)))
			imageOne := a.Have(
				"the two rational images multiply to the field one",
				"rational_map(L, r) * rational_map(L, real_inv(r)) = L.one",
				By(
					L,
					characteristic,
					isRational,
					inverseRational,
					realOne,
					At(mul, l, r, a.TermAs[Real]("real_inv(r)")),
					At(zeroOne, l)))
			a.Show(
				"the inverse is determined by its product with the original image",
				By(
					L,
					characteristic,
					isRational,
					inverseRational,
					imageOne,
					At(rationalIn, l, r),
					At(rationalIn, l, a.TermAs[Real]("real_inv(r)")),
					field.InvRightUniqueOn.Read(L).AsFact().At(
						a.TermAs[A]("rational_map(L, r)"), a.TermAs[A]("rational_map(L, real_inv(r))"))))
		})
		subfield := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "subfield(L, rational_image(L))",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			a.Do(Simp(Fwd(RationalImageDef)), Unfold(field.SubfieldDef))
			a.Show(
				"the rational image satisfies all subfield closure conditions",
				SplitConjAll(
					Case(
						"rational values lie in the ambient field",
						BySets(L, characteristic, At(rationalIn, l))),
					Case(
						"zero is the image of the rational zero",
						BySets(L, characteristic, At(zeroOne, l), rational.OfNumRational.At(a.TermAs[Nat]("0")))),
					Case(
						"one is the image of the rational one",
						BySets(L, characteristic, At(zeroOne, l), rational.OfNumRational.At(a.TermAs[Nat]("1")))),
					Case(
						"the sum of two images is the image of the rational sum",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							members := b.Assume()
							r, first := b.ObtainAs[Real](
								"choose a rational preimage of the first value",
								"∃r:real. rational(r) ∧ x = rational_map(L, r)",
								BySets(members))
							s, second := b.ObtainAs[Real](
								"choose a rational preimage of the second value",
								"∃s:real. rational(s) ∧ y = rational_map(L, s)",
								BySets(members))
							b.Show(
								"the rational sum supplies a preimage of the field sum",
								BySets(L, characteristic, first, second, At(add, l, r, s), rational.RationalAdd.At(r, s)))
						})),
					Case(
						"the negative of an image is the image of its rational negative",
						BySets(L, characteristic, At(neg, l), rational.RationalNeg)),
					Case(
						"the product of two images is the image of the rational product",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							members := b.Assume()
							r, first := b.ObtainAs[Real](
								"choose a rational preimage of the first factor",
								"∃r:real. rational(r) ∧ x = rational_map(L, r)",
								BySets(members))
							s, second := b.ObtainAs[Real](
								"choose a rational preimage of the second factor",
								"∃s:real. rational(s) ∧ y = rational_map(L, s)",
								BySets(members))
							b.Show(
								"the rational product supplies a preimage of the field product",
								BySets(L, characteristic, first, second, At(mul, l, r, s), rational.RationalMul.At(r, s)))
						})),
					Case(
						"the inverse of an image is the image of its rational reciprocal",
						BySets(L, characteristic, At(inv, l), rational.RationalInv))))
		})
		inverses := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "(∀r:real. rational(r) ⇒ rational_value(L, rational_map(L, r)) = r) ∧ " +
				"(∀a:A. a ∈ rational_image(L) ⇒ rational_map(L, rational_value(L, a)) = a)",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			Q := a.TermAs[Set[Real]]("{r:real | rational(r)}")
			phi := a.TermAs[Fun[Real, A]]("rational_map(L)")
			a.Show(
				"rational_value is inverse to the rational map on its domain and image",
				SplitConj(
					Case(
						"injectivity gives the inverse identity on rational arguments",
						Derive(func(b *Argument) {
							r := b.FixAs[Real]("r")
							isRational := b.Assume()
							b.Show(
								"read the left inverse law on the rational domain",
								BySets(
									L,
									characteristic,
									isRational,
									At(injective, l),
									RationalValueDef.At(l, b.TermAs[A]("rational_map(L, r)")),
									functions.InverseOnDef.At(Q, phi, b.TermAs[A]("rational_map(L, r)")),
									functions.InverseOnLeft.At(Q, phi, r)))
						})),
					Case(
						"the image gives the inverse identity on field values",
						Derive(func(b *Argument) {
							a := b.FixAs[A]("a")
							inImage := b.Assume()
							b.Show(
								"read the right inverse law on the rational image",
								BySets(inImage, RationalImageDef.At(l), RationalValueDef.At(l, a)))
						}))))
		})
		return ctx.Theorem(headline, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			a.Show(
				"assemble the rational subfield, embedding laws, and the two inverse identities",
				By(
					L,
					characteristic,
					At(subfield, l),
					At(injective, l),
					At(integerValues, l),
					At(add, l),
					At(mul, l),
					At(inverses, l)))
		})
	}),
})}

// RationalValueRational — in characteristic zero, rational_value takes a
// point of the rational image to a rational number: the point is the image
// of a rational r, and rational_value inverts the embedding there.
var RationalValueRational = rationalValueRationalThm{family.Add(registry.ProofEntry{
	Name: "RationalValueRational",
	Key:  "prop_db0e041d2a6a2e06",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x:A.",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"x ∈ rational_image(L)",
		},
		Conclusion: "rational(rational_value(L, x))",
	}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, x *Expr[A], inImage Fact) {
		l := a.TermAs[FieldOps[A]]("L")
		_, preimage := a.ObtainAs[Real](
			"choose a rational preimage",
			"∃r:real. rational(r) ∧ rational_map(L, r) = x",
			BySets(inImage, RationalImageDef.At(l)))
		a.Show(
			"the inverse returns that rational preimage",
			By(RationalEmbedding.Read(L), characteristic, preimage))
	}),
})}

// RationalValueAddMul — in characteristic zero, rational_value keeps sums
// and products of points of the rational image: their values are rational,
// the embedding carries the sum and the product of the values to x + y and
// x * y, and rational_value inverts the embedding at those rationals.
var RationalValueAddMul = rationalValueAddMulThm{family.Add(registry.ProofEntry{
	Name: "RationalValueAddMul",
	Key:  "prop_5ed2db083ef9c2dc",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x y:A.",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"x ∈ rational_image(L)",
			"y ∈ rational_image(L)",
		},
		Conclusion: "rational_value(L, x + y) = rational_value(L, x) + rational_value(L, y) ∧ " +
			"rational_value(L, x * y) = rational_value(L, x) * rational_value(L, y)",
	}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact, x, y *Expr[A], members Fact) {
		embedding := RationalEmbedding.Read(L)
		rationalValues := a.Have(
			"both values are rational",
			"rational(rational_value(L, x)) ∧ rational(rational_value(L, y))",
			By(characteristic, L, members, RationalValueRational))
		back := a.Have(
			"the values map back to the two operands",
			"rational_map(L, rational_value(L, x)) = x ∧ rational_map(L, rational_value(L, y)) = y",
			By(characteristic, embedding, members))
		arithmetic := a.Have(
			"the embedding carries their sum and product",
			"rational_map(L, rational_value(L, x) + rational_value(L, y)) = x + y ∧ "+
				"rational_map(L, rational_value(L, x) * rational_value(L, y)) = x * y",
			By(characteristic, embedding, rationalValues, back))
		hx, hy := a.TermAs[Real]("rational_value(L, x)"), a.TermAs[Real]("rational_value(L, y)")
		a.Show(
			"invert the rational sum and product",
			By(
				characteristic,
				embedding,
				rationalValues,
				arithmetic,
				rational.RationalAdd.At(hx, hy),
				rational.RationalMul.At(hx, hy)))
	}),
})}

// RationalValueZeroOneNegOne — in characteristic zero, rational_value takes
// the field's zero, one and minus one to 0, 1 and -1: the integer map keeps
// the three constants, the embedding agrees with it on integers, and
// rational_value inverts the embedding at the three rationals.
var RationalValueZeroOneNegOne = rationalValueZeroOneNegOneThm{family.Add(registry.ProofEntry{
	Name: "RationalValueZeroOneNegOne",
	Key:  "prop_1fe0d0b3e662bd1c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
		},
		Conclusion: "rational_value(L, L.zero) = &0 ∧ " +
			"rational_value(L, L.one) = &1 ∧ " +
			"rational_value(L, -L.one) = -&1",
	}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
		zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
		integers := a.Have(
			"the integer map keeps zero and the signed units",
			"integer_map(field_ring(L), 0) = L.zero ∧ "+
				"integer_map(field_ring(L), 1) = L.one ∧ "+
				"integer_map(field_ring(L), -1) = -L.one",
			By(IntegerMapHom.Read(field.RingOn.Read(L))))
		mapped := a.Have(
			"the rational embedding keeps zero and the signed units",
			"rational_map(L, &0) = L.zero ∧ rational_map(L, &1) = L.one ∧ rational_map(L, -&1) = -L.one",
			By(
				RationalEmbedding.Read(L),
				characteristic,
				integers,
				int_construction.OfNumBridge.At(zero),
				int_construction.OfNumBridge.At(one),
				int_construction.NegBridge.At(a.TermAs[Int]("1"))))
		a.Show(
			"invert the three rational constants",
			By(
				RationalEmbedding.Read(L),
				characteristic,
				mapped,
				rational.OfNumRational.At(zero),
				rational.OfNumRational.At(one),
				rational.RationalNeg.At(a.TermAs[Real]("&1"))))
	}),
})}

// RationalCommonDenominator — a finite set of rationals has a common positive
// denominator. On inserting a rational, multiply the previous common
// denominator by its positive denominator and scale the integer numerators
// accordingly.
var RationalCommonDenominator = rationalCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "RationalCommonDenominator",
	Key:  "prop_66d397e7c43327f9",
	Build: family.Theorem(Statement{
		Binders: "∀E:set(real).",
		Hypotheses: []string{
			"finite(E)",
			"∀r:real. r ∈ E ⇒ rational(r)",
		},
		Conclusion: "∃d:num. 0 < d ∧ (∀r:real. r ∈ E ⇒ ∃z:int. real_of_num(d) * r = real_of_int(z))",
	}, func(a *Argument) {
		a.Show(
			"finite induction carries a common denominator through insertion",
			ByInduction(finite_set.FiniteInductFreshOn,
				Case(
					"one clears the empty set",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[Nat]("1"))
						b.Show(
							"one is positive and there are no elements to clear",
							SplitConj(
								Case(
									"one is positive",
									ByArith()),
								Case(
									"the empty set has no elements",
									By(set_basic.NotInEmpty))))
					})),
				Case(
					"multiply the old denominator by the inserted point's denominator",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]("x")
						t := b.FixAs[Set[Real]]("t")
						data := b.Assume()
						parts := b.Conjuncts(
							data,
							"the old set has a common denominator",
							"the point is new",
							"the old set is finite",
							"the inserted point is rational",
							"the old points are rational")
						d, old := b.UnpackAs[Nat](parts[0], "d")
						numerator, e, fraction := b.Obtain2As[Int, Nat](
							"choose a positive denominator for the new rational",
							"∃a:int. ∃e:num. 0 < e ∧ x = real_of_int(a) / real_of_num(e)",
							By(parts[3], RationalIntegerFraction.At(x)))
						scaled := b.Have(
							"clear the new rational's positive denominator",
							"x * real_of_num(e) = real_of_int(a)",
							By(
								fraction,
								real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), e),
								real_order_field.EqDivMulLeft.At(
									x, b.TermAs[Real]("real_of_int(a)"), b.TermAs[Real]("real_of_num(e)"))))
						b.Take(b.TermAs[Nat]("d * e"))
						b.Show(
							"the product clears the enlarged set",
							SplitConj(
								Case(
									"the product of the two positive denominators is positive",
									Derive(func(c *Argument) {
										oldParts := c.Conjuncts(
											old,
											"the old denominator is positive",
											"the old multiples are integers")
										newParts := c.Conjuncts(
											fraction,
											"the new denominator is positive",
											"the fraction represents the new point")
										c.Show(
											"multiplication preserves positivity",
											ByArith(oldParts[0], newParts[0], nat_order.LessThanMulCancel.At(d, c.TermAs[Nat]("0"), e)))
									})),
								Case(
									"scale the integer witness for each element",
									Derive(func(c *Argument) {
										r := c.FixAs[Real]("r")
										inInsert := c.Assume()
										c.Cases(c.Term("r = x"))
										c.When(
											"the inserted point uses the old denominator as its scale",
											func(f *Argument, equal Fact) {
												f.Take(f.TermAs[Int]("&d * a"))
												f.Show(
													"the product denominator gives the scaled native numerator",
													CalcEq(
														Leg(
															f.Term("real_of_num(d) * (x * real_of_num(e))"),
															"substitute the inserted point and regroup",
															Simp(Fwd(real_construction.OfNumMul)),
															equal.Rw(),
															ByArith()),
														Leg(
															f.Term("real_of_num(d) * real_of_int(a)"),
															"use its cleared denominator",
															By(Normalized, scaled)),
														FinalLeg(
															"read the product as a native integer",
															By(
																Normalized,
																int_construction.OfNumBridge.At(d),
																int_construction.MulBridge.At(f.TermAs[Int]("d"), numerator)))))
											})
										c.Otherwise(
											"an old point uses the new denominator as its scale",
											func(f *Argument, different Fact) {
												inOld := f.Have(
													"a point distinct from the inserted point lies in the old set",
													"r ∈ t",
													By(different, inInsert, set_basic.InInsert.At(t, x, r)))
												z, oldInteger := f.ObtainAs[Int](
													"take the previous integer witness",
													"∃z:int. real_of_num(d) * r = real_of_int(z)",
													By(inOld, old))
												f.Take(f.TermAs[Int]("&e * z"))
												f.Show(
													"scaling the old integer witness clears the larger denominator",
													CalcEq(
														Leg(
															f.Term("real_of_num(e) * (real_of_num(d) * r)"),
															"regroup the product denominator",
															Simp(Fwd(real_construction.OfNumMul)),
															ByArith()),
														Leg(
															f.Term("real_of_num(e) * real_of_int(z)"),
															"use the previous integer witness",
															By(Normalized, oldInteger)),
														FinalLeg(
															"read the scaled witness as a native integer",
															By(
																Normalized,
																int_construction.OfNumBridge.At(e),
																int_construction.MulBridge.At(f.TermAs[Int]("e"), z)))))
											})
									}))))
					}))))
	}),
})}

// FiniteRationalDenominator — a finite set of rational elements has one
// positive integer denominator putting every scaled element in the integer
// image: clear its rational values and transport multiplication through the
// rational embedding.
var FiniteRationalDenominator = finiteRationalDenominatorThm{family.Add(registry.ProofEntry{
	Name: "FiniteRationalDenominator",
	Key:  "prop_d6c8bb1b08a55ff",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀C:set(A).",
		Hypotheses: []string{"characteristic_zero(field_ring(L))", "finite(C)", "C ⊆ rational_image(L)"},
		Conclusion: "∃d:num. " +
			"    0 < d ∧ (∀a:A. a ∈ C ⇒ integer_map(field_ring(L), d) * a ∈ integer_image(field_ring(L)))",
	}, func(a *Argument, L field.FieldFact[on.L], C *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"L has characteristic zero",
			"C is finite",
			"C consists of rational elements")
		charZero, finiteC, inQ := parts[0], parts[1], parts[2]
		embedding := a.Have(
			"the rational embedding preserves integers and products and has the rational-value inverse",
			"(∀z:int. rational_map(L, real_of_int(z)) = integer_map(field_ring(L), z)) ∧ "+
				"(∀r s:real. "+
				"    rational(r) ∧ rational(s) ⇒ "+
				"    rational_map(L, r * s) = rational_map(L, r) * rational_map(L, s)) ∧ "+
				"(∀r:real. rational(r) ⇒ rational_value(L, rational_map(L, r)) = r)",
			By(charZero, RationalEmbedding.Read(L)))
		laws := a.Conjuncts(
			embedding,
			"integer reals map to their integer images",
			"rational products map to products",
			"rational values recover rational reals")
		extendsIntegerMap, multiplicative, inverse := laws[0], laws[1], laws[2]
		values := a.Have(
			"rational values of C are rational and map back to C",
			"∀a:A. a ∈ C ⇒ rational(rational_value(L, a)) ∧ rational_map(L, rational_value(L, a)) = a",
			Derive(func(b *Argument) {
				b.FixAs[A]("a")
				elementIn := b.Assume()
				r, preimage := b.ObtainAs[Real](
					"choose a rational real mapping to this element",
					"∃r:real. rational(r) ∧ rational_map(L, r) = a",
					BySets(elementIn, inQ, RationalImageDef))
				recovered := b.Have(
					"the inverse embedding recovers this rational preimage",
					"rational_value(L, a) = r",
					By(Normalized, preimage, inverse.At(r)))
				b.Show(
					"the rational value is rational and maps back",
					By(Normalized, preimage, recovered))
			}))
		V, defV := a.LetAs[Set[Real]]("V", "image(rational_value(L), C)")
		finiteV := a.Have(
			"the rational values form a finite image",
			"finite(V)",
			By(
				Normalized,
				finiteC,
				defV,
				finite_set.FiniteImage.At(a.TermAs[Fun[A, Real]]("rational_value(L)"), C)))
		rationalV := a.Have(
			"each value in that image is rational",
			"∀r:real. r ∈ V ⇒ rational(r)",
			BySets(defV, values))
		d, clears := a.ObtainAs[Nat](
			"choose a common positive denominator for those rational values",
			"∃d:num. 0 < d ∧ (∀r:real. r ∈ V ⇒ ∃z:int. real_of_num(d) * r = real_of_int(z))",
			By(finiteV, rationalV, RationalCommonDenominator.At(V)))
		defD := a.Let("D", a.TermAs[A]("integer_map(field_ring(L), d)"))
		rationalD := a.Have(
			"the natural denominator is rational",
			"rational(real_of_num(d))",
			By(rational.OfNumRational.At(d)))
		denominatorImage := a.Have(
			"the rational image of d is its integer image",
			"rational_map(L, real_of_num(d)) = D",
			defD.Rw(),
			Simp(Rev(int_construction.OfNumBridge)),
			By(extendsIntegerMap))
		scaled := a.Have(
			"the common denominator puts every scaled element in the integer image",
			"∀a:A. a ∈ C ⇒ D * a ∈ integer_image(field_ring(L))",
			Derive(func(b *Argument) {
				element := b.FixAs[A]("a")
				elementIn := b.Assume()
				value := b.Have(
					"the element is recovered from its rational value",
					"rational(rational_value(L, a)) ∧ rational_map(L, rational_value(L, a)) = a",
					By(elementIn, values.At(element)))
				valueIn := b.Have(
					"its rational value lies in V",
					"rational_value(L, a) ∈ V",
					BySets(elementIn, defV))
				_, equation := b.ObtainAs[Int](
					"the denominator makes this rational value an integer",
					"∃z:int. real_of_num(d) * rational_value(L, a) = real_of_int(z)",
					By(valueIn, clears))
				valueParts := b.Conjuncts(
					value,
					"this value is rational",
					"its rational image is the element")
				multiplication := b.Have(
					"the embedding preserves multiplication by d",
					"rational_map(L, real_of_num(d) * rational_value(L, a)) = "+
						"rational_map(L, real_of_num(d)) * rational_map(L, rational_value(L, a))",
					By(
						rationalD,
						valueParts[0],
						multiplicative.At(b.TermAs[Real]("real_of_num(d)"), b.TermAs[Real]("rational_value(L, a)"))))
				transported := b.Have(
					"transporting the cleared value gives an integer image",
					"D * a = integer_map(field_ring(L), z)",
					Simp(
						Rev(extendsIntegerMap),
						Rev(equation),
						Fwd(multiplication),
						Fwd(denominatorImage),
						Fwd(valueParts[1])),
					Basic())
				b.Show(
					"the scaled element therefore lies in the integer image",
					BySets(transported, IntegerImageDef))
			}))
		a.Take(d)
		a.Show(
			"d clears the finite rational set",
			By(Normalized, clears, scaled, defD))
	}),
})}

// IntegerWeightedSumBound — an integer linear combination with uniformly
// bounded coefficients is bounded by that coefficient bound times the sum
// of the absolute weights: carry an integer representative and its bound
// through the finite sum, then transport the estimate to rational values.
var IntegerWeightedSumBound = integerWeightedSumBoundThm{family.Add(registry.ProofEntry{
	Name: "IntegerWeightedSumBound",
	Key:  "prop_4b3aefa9076ee42c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀s:set(num). ∀c d:(num → int). ∀H:num.",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"finite(s)",
			"∀i:num. i ∈ s ⇒ int_abs(c(i)) ≤ H",
		},
		Conclusion: "real_abs(rational_value(L, " +
			"        module_sum(L.add, " +
			"            L.zero, " +
			"            s, " +
			"            λi:num. integer_map(field_ring(L), c(i)) * integer_map(field_ring(L), d(i))))) ≤ " +
			"real_of_num(H * nat_sum(s, λi:num. num_of_int(int_abs(d(i)))))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		s *Expr[Set[Nat]],
		c, d *Arrow[Nat, Int],
		H *Expr[Nat],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"L has characteristic zero",
			"the index set is finite",
			"the coefficients are bounded by H")
		charZero, finiteS, coefficientsBounded := parts[0], parts[1], parts[2]
		integerMap := a.Have(
			"integer maps preserve zero, addition and multiplication and land in L",
			"integer_map(field_ring(L), 0) = L.zero ∧ "+
				"(∀a b:int. "+
				"    integer_map(field_ring(L), a + b) = "+
				"    integer_map(field_ring(L), a) + integer_map(field_ring(L), b) ∧ "+
				"    integer_map(field_ring(L), a * b) = "+
				"    integer_map(field_ring(L), a) * integer_map(field_ring(L), b)) ∧ "+
				"(∀z:int. integer_map(field_ring(L), z) ∈ L.carrier)",
			BySets(IntegerMapHom.Read(field.RingOn.Read(L))))
		rationalEmbedding := a.Have(
			"the rational embedding maps integer reals to their "+
				"integer images and has its rational-value inverse",
			"(∀z:int. rational_map(L, real_of_int(z)) = integer_map(field_ring(L), z)) ∧ "+
				"(∀r:real. rational(r) ⇒ rational_value(L, rational_map(L, r)) = r)",
			By(charZero, RationalEmbedding.Read(L)))
		embeddingParts := a.Conjuncts(
			rationalEmbedding,
			"integer reals map to integer images",
			"rational values invert the rational embedding")
		integerEmbedding, inverseEmbedding := embeddingParts[0], embeddingParts[1]
		integerValues := a.Have(
			"the rational value of an integer image is its real representative",
			"∀z:int. rational_value(L, integer_map(field_ring(L), z)) = real_of_int(z)",
			By(
				Normalized,
				integerEmbedding,
				inverseEmbedding,
				rational.IntegerRational,
				int_construction.RepresentativeIsInteger))
		F, defF := a.LetAs[Fun[Nat, A]](
			"F", "λi:num. integer_map(field_ring(L), c(i)) * integer_map(field_ring(L), d(i))")
		defW := a.Let("w", a.TermAs[Fun[Nat, Nat]]("λi:num. num_of_int(int_abs(d(i)))"))
		integerParts := a.Conjuncts(
			integerMap,
			"zero maps to zero",
			"integer sums and products are preserved",
			"every integer image lies in L")
		integerArithmetic, integerIn := integerParts[1], integerParts[2]
		summands := a.Have(
			"each summand is the integer image of the product and lies in L",
			"∀i:num. integer_map(field_ring(L), c(i) * d(i)) = F(i) ∧ F(i) ∈ L.carrier",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Show(
					"the product law and the carrier law apply to this summand",
					By(defF, integerArithmetic.At(c.Apply(i), d.Apply(i)), integerIn.At(b.TermAs[Int]("c(i) * d(i)"))))
			}))
		weights := a.Have(
			"the natural weights represent the absolute integer weights",
			"∀i:num. int_of_num(w(i)) = int_abs(d(i))",
			By(Normalized, defW, int_real_lift.AbsNonneg, int_embed.NumOfIntSection))
		boundedSums := a.Have(
			"every finite sum has an integer representative with the weighted bound",
			"∀t:set(num). "+
				"    finite(t) ⇒ "+
				"    (∀i:num. i ∈ t ⇒ int_abs(c(i)) ≤ H) ⇒ "+
				"    ∃z:int. "+
				"        integer_map(field_ring(L), z) = module_sum(L.add, L.zero, t, F) ∧ "+
				"        int_abs(z) ≤ int_of_num(H * nat_sum(t, w))",
			ByInduction(finite_set.FiniteInductFresh,
				Case(
					"the empty sum has integer representative zero",
					Derive(func(b *Argument) {
						b.Assume()
						b.Take(b.TermAs[Int]("0"))
						b.Show(
							"both empty sums are zero",
							ByArith(
								integerMap,
								module.ModuleSumEmpty.At(b.TermAs[Op[A]]("L.add"), b.TermAs[A]("L.zero"), F),
								nat_sum.Clauses.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindC[Nat]()),
								int_real_lift.AbsOfZero))
					})),
				Case(
					"adjoin a fresh index and add its integer summand",
					Derive(func(b *Argument) {
						x := b.FixAs[Nat]("x")
						t := b.FixAs[Set[Nat]]("t")
						inductionData := b.Assume()
						onInsert := b.Assume()
						inductionParts := b.Conjuncts(
							inductionData,
							"the smaller sum has a bounded integer representative",
							"x is fresh",
							"the smaller set is finite")
						ih, fresh, finiteT := inductionParts[0], inductionParts[1], inductionParts[2]
						coefficientBounds := b.Have(
							"the coefficient at x and those on the smaller set satisfy the same bound",
							"int_abs(c(x)) ≤ H ∧ (∀i:num. i ∈ t ⇒ int_abs(c(i)) ≤ H)",
							BySets(onInsert))
						z, smallerSum := b.ObtainAs[Int](
							"choose the bounded integer representative of the smaller sum",
							"∃z:int. "+
								"    integer_map(field_ring(L), z) = module_sum(L.add, L.zero, t, F) ∧ "+
								"    int_abs(z) ≤ int_of_num(H * nat_sum(t, w))",
							By(coefficientBounds, ih))
						weightSum := b.Have(
							"a fresh index adds its natural weight",
							"nat_sum(insert(x, t), w) = w(x) + nat_sum(t, w)",
							By(
								Normalized,
								finiteT,
								fresh,
								nat_sum.Clauses.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindC[Nat]())))
						fieldSum := b.Have(
							"a fresh index adds its field summand",
							"module_sum(L.add, L.zero, insert(x, t), F) = F(x) + module_sum(L.add, L.zero, t, F)",
							By(
								finiteT,
								fresh,
								summands,
								module.ModuleSumInsertMonoid.Read(comm_ring.AddMonoidOn.Read(field.RingOn.Read(L))).At(t, x, F)))
						represented := b.Have(
							"adding the integer product represents the enlarged sum",
							"integer_map(field_ring(L), c(x) * d(x) + z) = module_sum(L.add, L.zero, insert(x, t), F)",
							By(integerMap, summands.At(x), smallerSum, fieldSum))
						productBound := b.Have(
							"multiplication by the nonnegative absolute weight preserves the coefficient bound",
							"int_abs(c(x) * d(x)) ≤ H * int_abs(d(x))",
							ByArith(
								coefficientBounds,
								int_real_lift.AbsNonneg.At(b.TermAs[Int]("d(x)")),
								int_real_lift.AbsMul.At(b.TermAs[Int]("c(x)"), b.TermAs[Int]("d(x)")),
								int_real_lift.LessEqMulLeft.At(
									b.TermAs[Int]("int_abs(d(x))"), b.TermAs[Int]("int_abs(c(x))"), b.TermAs[Int]("H"))))
						enlargedBound := b.Have(
							"the natural weight bound expands into the new and old integer bounds",
							"H * nat_sum(insert(x, t), w) = H * int_abs(d(x)) + H * nat_sum(t, w)",
							Simp(
								Fwd(weightSum),
								Fwd(weights),
								Fwd(int_embed.OfNumMul),
								Fwd(int_embed.OfNumAdd),
								Fwd(int_real_lift.LeftDistrib)),
							Basic())
						sumBound := b.Have(
							"the triangle inequality bounds the enlarged integer representative",
							"int_abs(c(x) * d(x) + z) ≤ int_of_num(H * nat_sum(insert(x, t), w))",
							ByArith(
								productBound,
								smallerSum,
								enlargedBound,
								int_real_lift.AbsTriangle.At(b.TermAs[Int]("c(x) * d(x)"), z)))
						b.Take(b.TermAs[Int]("c(x) * d(x) + z"))
						b.Show(
							"the enlarged sum has the required representative and bound",
							By(represented, sumBound))
					}))))
		z, representative := a.ObtainAs[Int](
			"choose the bounded integer representative for s",
			"∃z:int. "+
				"    integer_map(field_ring(L), z) = module_sum(L.add, L.zero, s, F) ∧ "+
				"    int_abs(z) ≤ int_of_num(H * nat_sum(s, w))",
			By(finiteS, coefficientsBounded, boundedSums.At(s)))
		realBound := a.Have(
			"the integer inequality transfers to real absolute values",
			"real_abs(real_of_int(z)) ≤ real_of_num(H * nat_sum(s, w))",
			By(
				representative,
				int_construction.IntLeDef.At(a.TermAs[Int]("int_abs(z)"), a.TermAs[Int]("H * nat_sum(s, w)")),
				int_construction.AbsBridge.At(z),
				int_construction.OfNumBridge.At(a.TermAs[Nat]("H * nat_sum(s, w)"))))
		a.Show(
			"the rational value of the weighted sum satisfies the same bound",
			By(Normalized, representative, realBound, integerValues.At(z)))
	}),
})}
