// integers.go — the integer map into a commutative ring: its values at signed naturals, its values
// in the carrier and the ring operations it keeps, the integer image as a subring the map is a
// ring homomorphism into, the integer sums and powers it carries to sums and powers, and
// integer_value inverting the map on that image; in characteristic zero the map is injective and
// integer_value undoes it; and the integer ring itself as a module over itself.

package characteristic_zero

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerMapOfNum — natural integers map to additive powers of one.
var IntegerMapOfNum = integerMapOfNumThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapOfNum",
	Key:  "prop_e336204cf515cdb6",
	Build: family.Theorem("∀R:comm_ring_on(A). ∀n:num. "+
		"    integer_map(R, n) = monoid_pow(R.add, R.zero, R.one, n)",
		func(a *Argument, R comm_ring.CommRingFact[on.R], n *Expr[Nat]) {
			a.Show(
				"the nonnegative branch computes the natural value",
				By(Normalized, IntegerMapDef, int_embed.EmbedNonneg, int_embed.OfNumRetract))
		}),
})}

// IntegerMapNegOfNum — negative natural integers map to the negatives of
// the additive powers: zero is fixed, and a positive natural has negative opposite.
var IntegerMapNegOfNum = integerMapNegOfNumThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapNegOfNum",
	Key:  "prop_6a1cbe39f7f70fca",
	Build: family.Theorem("∀R:comm_ring_on(A). ∀n:num. "+
		"    integer_map(R, -n) = -monoid_pow(R.add, R.zero, R.one, n)",
		func(a *Argument, R comm_ring.CommRingFact[on.R], n *Expr[Nat]) {
			a.Do(Unfold(IntegerMapDef))
			a.Cases(a.TermAs[Bool]("n = 0"))
			a.When(
				"zero and its opposite have zero additive power",
				func(b *Argument, zero Fact) {
					b.Show(
						"both values reduce to the ring zero",
						Simp(Fwd(int_real_lift.NegNeg), Fwd(int_embed.OfNumRetract)),
						zero.Rw(),
						Simp(
							Fwd(int_real_lift.NegZero),
							Fwd(int_embed.OfNumRetract),
							Fwd(comm_monoid.MonoidPowDef),
							Fwd(int_real_lift.LessEqRefl)),
						ByArith(R))
				})
			a.Otherwise(
				"the opposite of a nonzero natural is negative",
				func(b *Argument, nonzero Fact) {
					negative := b.Have(
						"the negative branch of the definition applies",
						"¬(0 ≤ -int_of_num(n))",
						Simp(Rev(int_real_lift.NegNonneg), Fwd(int_embed.OfNumLe)),
						ByArith(nonzero))
					b.Show(
						"the two natural retractions compute the negative value",
						By(Normalized, negative, int_real_lift.NegNeg.At(b.TermAs[Int]("n")), int_embed.OfNumRetract.At(n)))
				})
		}),
})}

// IntegerMapInCarrier — every integer maps into the ring: its image is a
// signed additive power of one.
var IntegerMapInCarrier = integerMapInCarrierThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapInCarrier",
	Key:  "prop_7c75f6476c8e344c",
	Build: family.Theorem("∀R:comm_ring_on(A). ∀z:int. integer_map(R, z) ∈ R.carrier",
		func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int]) {
			a.Show(
				"both signed powers belong to the ring",
				By(
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(R)),
					comm_ring.OneIn.Read(R),
					comm_ring.NegIn.Read(R),
					IntegerMapDef.At(a.TermAs[RingOps[A]]("R"), z)))
		}),
})}

// IntegerMapHom — repeated addition of one gives the unique additive map
// preserving one, and this map also preserves products and negatives.
var IntegerMapHom = integerMapHomThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapHom",
	Key:  "prop_cd01ece5406e88ce",
	Build: family.Sections(Statement{
		Binders:    "∀R:ring_ops(A).",
		Hypotheses: []string{"comm_ring_on(R)"},
		Conclusion: "image(integer_map(R), 𝕌) ⊆ R.carrier ∧ " +
			"integer_map(R, 0) = R.zero ∧ " +
			"integer_map(R, 1) = R.one ∧ " +
			"(∀a b:int. " +
			"    integer_map(R, a + b) = R.add(integer_map(R, a), integer_map(R, b)) ∧ " +
			"    integer_map(R, a * b) = R.mul(integer_map(R, a), integer_map(R, b))) ∧ " +
			"(∀a:int. integer_map(R, -a) = R.neg(integer_map(R, a))) ∧ " +
			"(∀f:(int → A). " +
			"    image(f, 𝕌) ⊆ R.carrier ∧ f(1) = R.one ∧ (∀a b:int. f(a + b) = R.add(f(a), f(b))) ⇒ " +
			"    f = integer_map(R))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		negate := ctx.Lemma("∀R:comm_ring_on(A). ∀z:int. integer_map(R, -z) = -integer_map(R, z)",
			func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int]) {
				r := a.TermAs[RingOps[A]]("R")
				n, signs := a.ObtainAs[Nat](
					"write the integer with a natural magnitude",
					"∃n:num. z = int_of_num(n) ∨ z = -n",
					By(int_embed.Image.At(z)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"negating a natural gives its negative additive power",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"the signed value formulas agree",
								By(R, positive, IntegerMapOfNum.At(r, n), IntegerMapNegOfNum.At(r, n)))
						})),
					RightHolds(
						"negating a negative natural returns the natural",
						Given(func(b *Argument, negative Fact) {
							b.Show(
								"the double negatives cancel",
								negative.Rw(),
								Simp(Fwd(IntegerMapOfNum), Fwd(IntegerMapNegOfNum), Fwd(int_real_lift.NegNeg)),
								ByArith(R))
						})),
				))
			})

		successor := ctx.Lemma("∀R:comm_ring_on(A). ∀z:int. "+
			"    integer_map(R, z + 1) = integer_map(R, z) + R.one",
			func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int]) {
				n, signs := a.ObtainAs[Nat](
					"write the integer with a natural magnitude",
					"∃n:num. z = int_of_num(n) ∨ z = -n",
					By(int_embed.Image.At(z)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"a nonnegative successor adds one copy of one",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"the natural successor is the power recursion",
								positive.Rw(),
								Simp(Rev(int_embed.OfNumSuc), Fwd(IntegerMapOfNum), Fwd(comm_monoid.MonoidPowDef)),
								ByArith(R))
						})),
					RightHolds(
						"a negative successor removes one negative copy",
						Given(func(b *Argument, negative Fact) {
							b.Do(negative.Rw())
							zeroOrSuccessor := b.Have(
								"the magnitude n is 0 or a successor",
								"n = 0 ∨ ∃m:num. n = suc(m)",
								By(peano.Cases.At(n)))
							b.Do(zeroOrSuccessor.SplitDisj(
								LeftHolds(
									"at magnitude 0 the integer is 0, and the image of one is one",
									Given(func(c *Argument, zero Fact) {
										c.Show(
											"both sides reduce to one",
											zero.Rw(),
											Simp(
												Fwd(int_real_lift.NegZero),
												Fwd(int_real_lift.AddLeftIdentity),
												Fwd(IntegerMapOfNum),
												Fwd(comm_monoid.MonoidPowDef)),
											ByArith(R))
									})),
								RightHolds(
									"at magnitude suc(m) adding one leaves the magnitude m",
									Given(func(c *Argument, successor Fact) {
										m, isSuccessor := c.UnpackAs[Nat](successor, "m")
										previous := c.Have(
											"adding one cancels the last negative unit",
											"-suc(m) + 1 = -int_of_num(m)",
											ByArith(int_embed.OfNumSuc.At(m)))
										c.Show(
											"the negative power recursion cancels one copy",
											isSuccessor.Rw(),
											previous.Rw(),
											Simp(Fwd(IntegerMapNegOfNum), Fwd(comm_monoid.MonoidPowDef)),
											ByArith(R))
									})),
							))
						})),
				))
			})

		translate := ctx.Lemma("∀R:comm_ring_on(A). ∀z:int. ∀n:num. "+
			"    integer_map(R, z + n) = integer_map(R, z) + monoid_pow(R.add, R.zero, R.one, n)",
			func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int], n *Expr[Nat]) {
				a.Induct(n)
				a.Base(
					"translation by zero fixes the image",
					Simp(Fwd(int_real_lift.AddRightIdentity), Fwd(comm_monoid.MonoidPowDef)),
					ByArith(R, IntegerMapInCarrier.Read(R).At(z)))
				a.Step(
					"each natural successor translates by one more copy",
					func(b *Argument, ih Fact) {
						b.Show(
							"the successor recurrence and the induction hypothesis agree",
							Simp(
								Fwd(int_embed.OfNumSuc),
								Fwd(int_real_lift.AddAssoc),
								Fwd(successor),
								Fwd(comm_monoid.MonoidPowDef)),
							ih.Rw(),
							ByArith(R, IntegerMapInCarrier.Read(R).At(z)))
					})
			})

		add := ctx.Lemma("∀R:comm_ring_on(A). ∀x y:int. "+
			"    integer_map(R, x + y) = integer_map(R, x) + integer_map(R, y)",
			func(a *Argument, R comm_ring.CommRingFact[on.R], x, y *Expr[Int]) {
				r := a.TermAs[RingOps[A]]("R")
				n, signs := a.ObtainAs[Nat](
					"write the second summand with a natural magnitude",
					"∃n:num. y = int_of_num(n) ∨ y = -n",
					By(int_embed.Image.At(y)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"a natural summand is the translation formula",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"translate by its additive power",
								By(R, positive, IntegerMapOfNum.At(r, n), At(translate, r, x, n)))
						})),
					RightHolds(
						"a negative summand is recovered by cancellation",
						Given(func(b *Argument, negative Fact) {
							restore := b.Have(
								"its natural magnitude restores the first summand",
								"(x + y) + int_of_num(n) = x",
								ByArith(negative))
							translated := b.Have(
								"translate the sum back to the first image",
								"integer_map(R, x) = integer_map(R, x + y) + monoid_pow(R.add, R.zero, R.one, n)",
								By(R, restore, At(translate, r, b.TermAs[Int]("x + y"), n)))
							negativeValue := b.Have(
								"the second image is the negative additive power",
								"integer_map(R, y) = -monoid_pow(R.add, R.zero, R.one, n)",
								By(R, negative, IntegerMapNegOfNum.At(r, n)))
							b.Show(
								"cancel the common additive power",
								ByArith(
									R,
									translated,
									negativeValue,
									IntegerMapInCarrier.Read(R).At(x),
									IntegerMapInCarrier.Read(R).At(y),
									IntegerMapInCarrier.Read(R).At(b.TermAs[Int]("x + y"))))
						})),
				))
			})

		multiplyNatural := ctx.Lemma("∀R:comm_ring_on(A). ∀z:int. ∀n:num. "+
			"    integer_map(R, z * n) = integer_map(R, z) * monoid_pow(R.add, R.zero, R.one, n)",
			func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int], n *Expr[Nat]) {
				a.Induct(n)
				a.Base(
					"multiplication by zero gives zero",
					Simp(Fwd(int_real_lift.MulRightZero), Fwd(IntegerMapOfNum), Fwd(comm_monoid.MonoidPowDef)),
					ByArith(R, IntegerMapInCarrier.Read(R).At(z)))
				a.Step(
					"distribute over one more natural unit",
					func(b *Argument, ih Fact) {
						b.Show(
							"additivity and distributivity give the next product",
							Simp(
								Fwd(int_embed.OfNumSuc),
								Fwd(int_real_lift.LeftDistrib),
								Fwd(int_real_lift.MulRightIdentity),
								Fwd(add),
								Fwd(comm_monoid.MonoidPowDef)),
							ih.Rw(),
							ByArith(R, IntegerMapInCarrier.Read(R).At(z)))
					})
			})

		multiply := ctx.Lemma("∀R:comm_ring_on(A). ∀x y:int. "+
			"    integer_map(R, x * y) = integer_map(R, x) * integer_map(R, y)",
			func(a *Argument, R comm_ring.CommRingFact[on.R], x, y *Expr[Int]) {
				r := a.TermAs[RingOps[A]]("R")
				n, signs := a.ObtainAs[Nat](
					"write the second factor with a natural magnitude",
					"∃n:num. y = int_of_num(n) ∨ y = -n",
					By(int_embed.Image.At(y)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"a natural factor is repeated addition",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"the natural product and value formulas agree",
								By(R, positive, IntegerMapOfNum.At(r, n), At(multiplyNatural, r, x, n)))
						})),
					RightHolds(
						"the negative sign passes through the product",
						Given(func(b *Argument, negative Fact) {
							b.Show(
								"negation and the natural product formula agree",
								negative.Rw(),
								Simp(Fwd(int_real_lift.MulRightNeg), Fwd(negate), Fwd(multiplyNatural), Fwd(IntegerMapNegOfNum)),
								Simp(Fwd(IntegerMapOfNum)),
								ByArith(R, IntegerMapInCarrier.Read(R).At(x)))
						})),
				))
			})

		unique := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀f:(int → A).",
			Hypotheses: []string{
				"image(f, 𝕌) ⊆ R.carrier",
				"f(1) = R.one",
				"∀x y:int. f(x + y) = f(x) + f(y)",
			},
			Conclusion: "f = integer_map(R)",
		},
			func(a *Argument, R comm_ring.CommRingFact[on.R], f *Arrow[Int, A], hom Fact) {
				r := a.TermAs[RingOps[A]]("R")
				parts := a.Conjuncts(
					hom,
					"the range lies in the ring",
					"one is preserved",
					"addition is preserved")
				image, one, additive := parts[0], parts[1], parts[2]
				valuesIn := a.Have(
					"every value lies in the ring",
					"∀z:int. f(z) ∈ R.carrier",
					BySets(image))
				zero := a.Have(
					"an additive map sends zero to zero",
					"f(0) = R.zero",
					Derive(func(b *Argument) {
						zeroTerm := b.TermAs[Int]("0")
						idempotent := b.Have(
							"the value at zero is additively idempotent",
							"f(0) = f(0) + f(0)",
							By(additive.At(zeroTerm, zeroTerm), int_real_lift.AddLeftIdentity.At(zeroTerm)))
						b.Show(
							"cancel one copy of the value",
							ByArith(R, valuesIn.At(zeroTerm), idempotent))
					}))
				natural := a.Have(
					"one determines every natural value",
					"∀n:num. f(n) = monoid_pow(R.add, R.zero, R.one, n)",
					Derive(func(b *Argument) {
						b.Induct("n")
						b.Base(
							"the value at zero is the zero power",
							By(Normalized, zero, comm_monoid.MonoidPowDef))
						b.Step(
							"add one more copy of one",
							func(c *Argument, ih Fact) {
								cn := c.TermAs[Int]("n")
								c1 := c.TermAs[Int]("1")
								cn1 := c.TermAs[Int]("&n + 1")
								c.Show(
									"the additive recursion matches the power recursion",
									Simp(Fwd(int_embed.OfNumSuc), Fwd(comm_monoid.MonoidPowDef)),
									ByArith(R, additive.At(cn, c1), valuesIn.At(cn), valuesIn.At(cn1), valuesIn.At(c1), ih, one))
							})
					}))
				negativeValues := a.Have(
					"additivity determines every negative value",
					"∀z:int. f(-z) = -f(z)",
					Derive(func(b *Argument) {
						z := b.FixAs[Int]()
						nz := b.TermAs[Int]("-z")
						opposites := b.Have(
							"opposite inputs have values summing to zero",
							"f(z) + f(-z) = R.zero",
							By(Normalized, additive.At(z, nz), zero, int_real_lift.AddRightInverse.At(z)))
						b.Show(
							"the two values are additive inverses",
							ByArith(R, opposites, valuesIn.At(z), valuesIn.At(nz)))
					}))
				a.Do(Funext())
				z := a.FixAs[Int]("z")
				n, signs := a.ObtainAs[Nat](
					"write an arbitrary integer with its natural magnitude",
					"∃n:num. z = int_of_num(n) ∨ z = -n",
					By(int_embed.Image.At(z)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"the maps agree on natural integers",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"both maps give the same additive power",
								By(R, natural.At(n), positive, IntegerMapOfNum.At(r, n)))
						})),
					RightHolds(
						"the maps agree on negative natural integers",
						Given(func(b *Argument, negative Fact) {
							b.Show(
								"both maps give the negative additive power",
								By(R, negativeValues.At(b.TermAs[Int]("n")), natural.At(n), negative, IntegerMapNegOfNum.At(r, n)))
						})),
				))
			})

		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
		) {
			image := a.Have(
				"the integer map takes values in the ring",
				"image(integer_map(R), 𝕌) ⊆ R.carrier",
				BySets(IntegerMapInCarrier.Read(ring)))
			units := a.Have(
				"zero and one are preserved",
				"integer_map(R, 0) = R.zero ∧ integer_map(R, 1) = R.one",
				Simp(Fwd(IntegerMapOfNum)),
				ByArith(ring))
			a.Show(
				"the ring laws and uniqueness hold together",
				By(ring, image, units, negate, add, multiply, unique))
		})
	}),
})}

// IntegerImageCommRing — the integer image is a commutative subring: it
// holds zero and one and is closed under sums, products and negatives, each
// witnessed by the corresponding integer.
var IntegerImageCommRing = integerImageCommRingThm{family.Add(registry.ProofEntry{
	Name: "IntegerImageCommRing",
	Key:  "prop_385a282eddd97807",
	Build: family.Theorem("∀R:comm_ring_on(A). comm_ring_on(restrict_ring(R, integer_image(R)))",
		func(a *Argument, R comm_ring.CommRingFact[on.R]) {
			r := a.TermAs[RingOps[A]]("R")
			a.Do(Cite(IntegerMapHom.Read(R)))
			inCarrier := a.Hyp("image(integer_map(R), 𝕌) ⊆ R.carrier")
			zero := a.Hyp("integer_map(R, 0) = R.zero")
			one := a.Hyp("integer_map(R, 1) = R.one")
			addAndMul := a.Hyp(
				"∀m n:int. " +
					"    integer_map(R, m + n) = R.add(integer_map(R, m), integer_map(R, n)) ∧ " +
					"    integer_map(R, m * n) = R.mul(integer_map(R, m), integer_map(R, n))")
			neg := a.Hyp("∀m:int. integer_map(R, -m) = R.neg(integer_map(R, m))")
			membership := a.Have(
				"integer image membership is an integer witness",
				"∀x:A. x ∈ integer_image(R) ⇔ ∃m:int. x = integer_map(R, m)",
				BySets(IntegerImageDef.At(r)))
			units := a.Have(
				"the image lies in the ring and contains zero and one",
				"integer_image(R) ⊆ R.carrier ∧ R.zero ∈ integer_image(R) ∧ R.one ∈ integer_image(R)",
				BySets(zero, one, inCarrier, IntegerImageDef.At(r)))
			addAndMultiply := a.Have(
				"integer witnesses are closed under addition and multiplication",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ integer_image(R)",
						"y ∈ integer_image(R)",
					},
					Conclusion: "R.add(x, y) ∈ integer_image(R) ∧ R.mul(x, y) ∈ integer_image(R)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					inImage := b.Assume()
					m, n, representatives := b.Obtain2As[Int, Int](
						"take integer representatives",
						"∃m n:int. x = integer_map(R, m) ∧ y = integer_map(R, n)",
						By(membership.At(x), membership.At(y), inImage))
					b.Show(
						"the sum and product have the corresponding integer witnesses",
						By(
							membership.At(b.TermAs[A]("R.add(x, y)")),
							membership.At(b.TermAs[A]("R.mul(x, y)")),
							addAndMul.At(m, n),
							representatives))
				}))
			negate := a.Have(
				"negating an integer witness stays in the image",
				"∀x:A. x ∈ integer_image(R) ⇒ R.neg(x) ∈ integer_image(R)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inImage := b.Assume()
					m, representative := b.ObtainAs[Int](
						"take an integer representative",
						"∃m:int. x = integer_map(R, m)",
						By(membership.At(x), inImage))
					b.Show(
						"the negative image is represented by the negative integer",
						By(membership.At(b.TermAs[A]("R.neg(x)")), neg.At(m), representative))
				}))
			a.Show(
				"the closed subset inherits the commutative ring structure",
				By(
					addAndMultiply,
					negate,
					units,
					comm_ring.ClosedSubsetRingOn.Read(R).At(a.TermAs[Set[A]]("integer_image(R)"))))
		}),
})}

// IntegerMapIntoImage — the integer map is a ring homomorphism from the
// integer ring into the integer image, read as a ring: it keeps integer
// sums, products and one, and its values lie in the image.
var IntegerMapIntoImage = integerMapIntoImageThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapIntoImage",
	Key:  "prop_d4317a78e4f45595",
	Build: family.Theorem("∀R:comm_ring_on(A). "+
		"    ring_homomorphism(int_ring, restrict_ring(R, integer_image(R)), integer_map(R))",
		func(a *Argument, R comm_ring.CommRingFact[on.R]) {
			r := a.TermAs[RingOps[A]]("R")
			// Open the cited bundle so only the preservation components enter the close.
			a.Do(Cite(IntegerMapHom, r), Basic())
			preserves := a.Hyp(
				"∀a b:int. " +
					"    integer_map(R, a + b) = R.add(integer_map(R, a), integer_map(R, b)) ∧ " +
					"    integer_map(R, a * b) = R.mul(integer_map(R, a), integer_map(R, b))")
			unit := a.Hyp("integer_map(R, 1) = R.one")
			a.Show(
				"integer addition, multiplication and one are preserved",
				Simp(
					Fwd(ring_homomorphism.RingHomomorphism),
					Fwd(module_record.RestrictRingDef),
					Fwd(int_real_lift.IntRingDef),
					Fwd(IntegerImageDef)),
				By(
					Normalized,
					IntegerImageCommRing.Read(R),
					preserves,
					unit,
					int_real_lift.CommRingOn,
					int_real_lift.IntRingDef,
					module_record.RestrictRingDef.At(r, a.TermAs[Set[A]]("integer_image(R)")),
					IntegerImageDef.At(r),
					set_basic.InImage,
					set_basic.InUniv))
		}),
})}

// IntegerMapHomomorphism — the integer map is a ring homomorphism from the integers into any
// commutative ring: it is one into its image, which lies in the carrier.
var IntegerMapHomomorphism = integerMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapHomomorphism",
	Key:  "prop_7e799c8e38334918",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "ring_homomorphism(int_ring, R, integer_map(R))",
	},
		func(a *Argument, R *Expr[RingOps[A]], ring Fact) {
			a.Show(
				"the image of the integers is a part of the carrier, so the target of the map extends to R",
				By(
					ring,
					IntegerMapIntoImage.At(R),
					ring_homomorphism.RingHomExtendTarget.At(
						a.TermAs[RingOps[Int]]("int_ring"),
						R,
						a.TermAs[Fun[Int, A]]("integer_map(R)"),
						a.TermAs[Set[A]]("integer_image(R)")),
					IntegerMapHom.At(R),
					IntegerImageDef))
		}),
})}

// IntegerMapSum — the integers' map into a commutative ring carries an
// integer sum over a finite set to the sum of the images. An integer sum is
// the fold of integer addition, which the map turns into the ring's
// addition, keeping zero; such a map passes through a fold.
var IntegerMapSum = integerMapSumThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapSum",
	Key:  "prop_69bf4420e078345a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(B). ∀f:(B → int).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "integer_map(R, Σ_{x∈s} f(x)) = " +
			"module_sum(R.add, R.zero, s, λx:B. integer_map(R, f(x)))",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[B]],
			f *Arrow[B, Int],
			finite Fact,
		) {
			homomorphism := IntegerMapHomomorphism.Read(ring)
			arg.Do(Unfold(int_sum.IntSumDef))
			arg.Show(
				"the integer sum is the fold of integer addition, which the map carries to the ring's",
				By(
					finite,
					int_real_lift.AddMonoid,
					int_real_lift.IntegerRingCarrierUniversal,
					ring_homomorphism.MapZero.Read(homomorphism),
					ring_homomorphism.MapAdd.Read(homomorphism),
					module.ModuleSumIteratedOp.At(
						arg.TermAs[Op[Int]]("int_add"),
						arg.TermAs[Int]("0"),
						s,
						f),
					module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(int_real_lift.CommRingOn)).At(
						arg.TermAs[Op[A]]("R.add"),
						arg.TermAs[A]("R.zero"),
						arg.TermAs[Fun[Int, A]]("integer_map(R)"),
						s,
						f)))
		}),
})}

// IntegerMapPow — the integers' map into a ring takes the n-th power of an
// integer to the n-th power of its image: by induction on n, a⁰ = 1 maps to
// one and a^(n+1) = a·aⁿ maps to the product of the images.
var IntegerMapPow = integerMapPowThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapPow",
	Key:  "prop_cda0d2c1b94c27f2",
	Build: family.Theorem("∀R:comm_ring_on(A). ∀a:int. ∀n:num. "+
		"    integer_map(R, a ^ n) = monoid_pow(R.mul, R.one, integer_map(R, a), n)",
		func(arg *Argument, R comm_ring.CommRingFact[on.R], a *Expr[Int]) {
			homomorphism := IntegerMapHom.Read(R)
			arg.Induct("n")
			arg.Base(
				"a⁰ = 1 maps to one, the empty product",
				By(int_pow.PowClauses, homomorphism, comm_monoid.MonoidPowDef))
			arg.Step(
				"a^(n+1) = a·aⁿ maps to the image of a times that of aⁿ",
				func(b *Argument, power Fact) {
					b.Show(
						"by the power clauses on both sides and the inductive hypothesis",
						By(power, int_pow.PowClauses, homomorphism, comm_monoid.MonoidPowDef))
				})
		}),
})}

// IntegerValueRightInverse — integer_value chooses an integer preimage, so
// on the integer image the integer map undoes it.
var IntegerValueRightInverse = integerValueRightInverseThm{family.Add(registry.ProofEntry{
	Name: "IntegerValueRightInverse",
	Key:  "prop_9b613bf735a1894b",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀c:A.",
		Hypotheses: []string{"c ∈ integer_image(R)"},
		Conclusion: "integer_map(R, integer_value(R, c)) = c",
	}, func(a *Argument, R *Expr[RingOps[A]], c *Expr[A], inImage Fact) {
		a.Have(
			"a point of the integer image has an integer preimage",
			"∃z:int. integer_map(R, z) = c",
			BySets(inImage, IntegerImageDef.At(R)))
		a.Show(
			"integer_value chooses such a preimage",
			Unfold(IntegerValueDef))
	}),
})}

// IntegerMapPositiveNonzero — in characteristic zero a positive natural
// number maps to a nonzero element: its image is a positive additive power
// of one.
var IntegerMapPositiveNonzero = integerMapPositiveNonzeroThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapPositiveNonzero",
	Key:  "prop_74653cecb874f077",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀n:num.",
		Hypotheses: []string{"characteristic_zero(R)", "0 < n"},
		Conclusion: "integer_map(R, n) ≠ R.zero",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], n *Expr[Nat], h Fact) {
		a.Show(
			"a positive additive power of one is nonzero",
			By(
				Normalized,
				h,
				comm_ring.CharacteristicZeroDef.At(a.TermAs[RingOps[A]]("R")),
				IntegerMapOfNum.Read(R).At(n)))
	}),
})}

// IntegerMapInjective — characteristic zero makes the integer map injective:
// a signed natural magnitude in its kernel is zero, as is any difference
// whose two images agree.
var IntegerMapInjective = integerMapInjectiveThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapInjective",
	Key:  "prop_c90c1d2ae43fa81",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"characteristic_zero(R)",
		},
		Conclusion: "injective_on(𝕌, integer_map(R))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		kernelZero := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀z:int.",
			Hypotheses: []string{"characteristic_zero(R)", "integer_map(R, z) = R.zero"},
			Conclusion: "z = 0",
		},
			func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int], hypotheses Fact) {
				parts := a.Conjuncts(
					hypotheses,
					"the ring has characteristic zero",
					"z maps to zero")
				charZero, zeroImage := parts[0], parts[1]
				positivePowers := a.Have(
					"a positive number of copies of one cannot vanish",
					"∀n:num. 0 < n ⇒ monoid_pow(R.add, R.zero, R.one, n) ≠ R.zero",
					By(charZero, comm_ring.CharacteristicZeroDef.At(a.TermAs[RingOps[A]]("R"))))
				n, signs := a.ObtainAs[Nat](
					"write the integer with a natural magnitude",
					"∃n:num. z = n ∨ z = -n",
					By(int_embed.Image.At(z)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"a nonnegative integer in the kernel has zero magnitude",
						Given(func(b *Argument, positive Fact) {
							powerZero := b.Have(
								"its additive power is zero",
								"monoid_pow(R.add, R.zero, R.one, n) = R.zero",
								By(zeroImage, positive, IntegerMapOfNum.Read(R).At(n)))
							magnitudeZero := b.Have(
								"characteristic zero rules out a positive magnitude",
								"n = 0",
								ByArith(powerZero, positivePowers.At(n)))
							b.Show(
								"the integer is zero",
								ByArith(positive, magnitudeZero))
						})),
					RightHolds(
						"a negative integer in the kernel has zero magnitude",
						Given(func(b *Argument, negative Fact) {
							negativePowerZero := b.Have(
								"its negative additive power is zero",
								"-monoid_pow(R.add, R.zero, R.one, n) = R.zero",
								By(zeroImage, negative, IntegerMapNegOfNum.Read(R).At(n)))
							powerZero := b.Have(
								"additive cancellation makes the power zero",
								"monoid_pow(R.add, R.zero, R.one, n) = R.zero",
								ByArith(
									R,
									negativePowerZero,
									comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(R)),
									comm_ring.OneIn.Read(R)))
							magnitudeZero := b.Have(
								"characteristic zero rules out a positive magnitude",
								"n = 0",
								ByArith(powerZero, positivePowers.At(n)))
							b.Show(
								"the integer is zero",
								ByArith(negative, magnitudeZero))
						})),
				))
			})

		return ctx.Theorem(headline, func(a *Argument, R *Expr[RingOps[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"the operations form a ring",
				"the ring has characteristic zero")
			ring := parts[0]
			a.Do(Simp(Fwd(functions.InjectiveOnDef)))
			a.FixAs[Int]("x")
			a.FixAs[Int]("y")
			equalImages := a.Assume()
			imagesIn := a.Have(
				"the two images lie in the ring",
				"integer_map(R, x) ∈ R.carrier ∧ integer_map(R, y) ∈ R.carrier",
				BySets(ring, IntegerMapHom.At(R)))
			differenceImage := a.Have(
				"the integer map preserves the difference",
				"integer_map(R, x + -y) = integer_map(R, x) + -integer_map(R, y)",
				Simp(Fwd(IntegerMapHom)),
				Basic())
			zeroImage := a.Have(
				"equality of the images kills the difference",
				"integer_map(R, x + -y) = R.zero",
				differenceImage.Rw(),
				ByArith(ring, imagesIn, equalImages))
			zeroDifference := a.Have(
				"the difference lies in the zero kernel",
				"x + -y = 0",
				By(hypotheses, zeroImage, At(kernelZero, R, a.TermAs[Int]("x + -y"))))
			a.Show(
				"the two integers agree",
				ByArith(zeroDifference))
		})
	}),
})}

// IntegerValueLeftInverse — in characteristic zero, integer_value undoes
// the integer map: the defining choice picks an integer with the same image,
// and injectivity makes it the original integer.
var IntegerValueLeftInverse = integerValueLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "IntegerValueLeftInverse",
	Key:  "prop_6c6523cd8e4773e3",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀z:int.",
		Hypotheses: []string{"characteristic_zero(R)"},
		Conclusion: "integer_value(R, integer_map(R, z)) = z",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], z *Expr[Int], charZero Fact) {
		injective := a.Have(
			"the integer map is injective",
			"injective_on(𝕌, integer_map(R))",
			By(R, charZero, IntegerMapInjective.At(a.TermAs[RingOps[A]]("R"))))
		ownImage := a.Have(
			"z is a preimage of its own image",
			"∃w:int. integer_map(R, w) = integer_map(R, z)",
			Witness(z),
			Refl())
		a.Show(
			"injectivity identifies the chosen preimage with z",
			Unfold(IntegerValueDef),
			BySets(
				HilbertDenoted,
				injective,
				ownImage,
				functions.InjectiveOnDef.At(a.TermAs[Set[Int]]("𝕌"), a.TermAs[Fun[Int, A]]("integer_map(R)"))))
	}),
})}

// IntegerRingRegularModule — the integer ring is a module over itself:
// the regular module of a commutative ring, at the integers.
var IntegerRingRegularModule = integerRingRegularModuleThm{family.Add(registry.ProofEntry{
	Name: "IntegerRingRegularModule",
	Key:  "prop_9f4b63ddd4141539",
	Build: family.Theorem("module_on(int_ring, regular_module(int_ring))", func(a *Argument) {
		a.Show(
			"the integers form their regular module",
			By(int_real_lift.CommRingOn, module.RegularModuleOn))
	}),
})}
