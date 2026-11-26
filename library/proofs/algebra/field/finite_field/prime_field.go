// prime_field.go — the field of p elements: the integers modulo a prime
// p, the cosets of the multiples of p; and congruences mod p read in any
// field of p elements, where a factor p does not divide cancels and a
// square mod p is a square of the field.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// principalSpanIdeal builds the section IntegerPrincipalIdeal,
// IntegerPrimeIdealMaximal and PrimeFieldOn cite: the ideal span of a
// natural integer is an ideal of the integers, a commutative ring on
// the whole type.
func principalSpanIdeal(ctx *Script) *GoalStackNode {
	return ctx.Lemma("∀p:num. ring_ideal(int_ring, «integerIdeal»(p))", func(
		a *Argument,
		p *Expr[Nat],
	) {
		a.Show(
			"the span of a set of integers is an ideal of the integer ring",
			BySets(
				ring_ideal.SpanIdeal.Read(int_real_lift.CommRingOn).At(a.TermAs[Set[Int]]("{int_of_num(p)}"))))
	})
}

// integerResidueClassCount builds the residue-class count PrimeFieldOn
// and PrimeSubfield both read: a map f out of the integers whose fibres
// are the cosets of the multiples of a positive p — two integers share a
// value exactly when their difference is a multiple of p — takes each of
// its values at a natural residue below p and separates those residues,
// so its image is the residues' image and has p points.
func integerResidueClassCount(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀p:num. ∀f:(int → A).",
		Hypotheses: []string{
			"0 < p",
			"∀x y:int. f(x) = f(y) ⇔ x - y ∈ «integerIdeal»(p)",
		},
		Conclusion: "image(λr:num. f(int_of_num(r)), «residues»(p)) = image(f, 𝕌) ∧ " +
			"has_size(image(f, 𝕌), p)",
	}, func(a *Argument, p *Expr[Nat], f *Expr[Fun[Int, A]], positive, fibres Fact) {
		modulus := a.TermAs[Int]("p")
		residues := a.TermAs[Set[Nat]]("«residues»(p)")
		onResidues := a.TermAs[Fun[Nat, A]]("λr:num. f(int_of_num(r))")
		congruent := a.Have(
			"two integers share a value exactly when they are congruent modulo p",
			"∀x y:int. f(x) = f(y) ⇔ x ≡ y (mod int_of_num(p))",
			Derive(func(b *Argument) {
				x := b.FixAs[Int]("x")
				y := b.FixAs[Int]("y")
				difference := b.TermAs[Int]("x - y")
				b.Show(
					"a difference lies in the principal ideal exactly when p divides it",
					BySets(
						fibres.At(x, y),
						At(IntegerPrincipalIdeal, p),
						int_divides.IntDividesDef.At(modulus, difference),
						int_congruence.IntCongDef.At(x, y, modulus)))
			}))
		naturalNonzero := a.Have(
			"the positive modulus is nonzero",
			"p ≠ 0",
			ByArith(positive))
		nonzero := a.Have(
			"so it stays nonzero as an integer",
			"int_of_num(p) ≠ 0",
			By(naturalNonzero, int_embed.OfNumEq.At(p, a.TermAs[Nat]("0"))))
		representatives := a.Have(
			"each value of f is taken at a residue below p",
			"∀z:int. ∃r:num. r < p ∧ f(int_of_num(r)) = f(z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Int]("z")
				y, remainder := b.ObtainAs[Int](
					"choose the remainder of z in its nonnegative range",
					"∃y:int. 0 ≤ y ∧ y < abs(p) ∧ y ≡ z (mod int_of_num(p))",
					By(nonzero, int_congruence.ResidueInRange.At(z, modulus)))
				natural := b.Have(
					"the nonnegative remainder is a natural integer",
					"num_of_int(y) = y",
					By(remainder, int_embed.NumOfIntSection.At(y)))
				r := b.TermAs[Nat]("num_of_int(y)")
				b.Take(r)
				b.Show(
					"the natural remainder lies below p and, congruent to z, has z's value",
					By(
						Normalized,
						natural,
						remainder,
						int_embed.OfNumAbs.At(p),
						int_embed.OfNumLt.At(r, p),
						congruent.At(y, z)))
			}))
		injective := a.Have(
			"f separates the residues below p",
			"injective_on(«residues»(p), λr:num. f(int_of_num(r)))",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				r := b.FixAs[Nat]("r")
				s := b.FixAs[Nat]("s")
				same := b.Assume()
				congruent := b.Have(
					"equal values make the two residues congruent",
					"int_of_num(r) ≡ int_of_num(s) (mod int_of_num(p))",
					By(same, congruent.At(b.TermAs[Int]("r"), b.TermAs[Int]("s"))))
				b.Show(
					"two congruent residues below p have one remainder, so they are equal",
					By(
						same,
						congruent,
						int_congruence.OfNumCongruent.At(r, s, p),
						nat_congruence.CongDef.At(r, s, p),
						nat_div_mod.ModInjectiveBelow.At(r, s, p)))
			}))
		values := a.Have(
			"the residues below p take every value of f",
			"image(λr:num. f(int_of_num(r)), «residues»(p)) = image(f, 𝕌)",
			BySets(representatives))
		a.Show(
			"the p residues have p distinct values, which are all of f's",
			By(
				values,
				injective,
				num_segment.HasSizeBelowStrict.At(p),
				cardinality.HasSizeImageInj.At(onResidues, residues, p)))
	})
}

// IntegerPrincipalIdeal — the ideal generated by a natural integer is
// exactly its integer multiples: ideal absorption and span minimality.
var IntegerPrincipalIdeal = integerPrincipalIdealThm{family.Add(registry.ProofEntry{
	Name: "IntegerPrincipalIdeal",
	Key:  "prop_5a0e3051ee8ba479",
	Build: family.Sections(Statement{
		Binders:    "∀p:num.",
		Conclusion: "ideal_span(int_ring, {int_of_num(p)}) = image(λz:int. p * z, 𝕌)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		spanIdeal := principalSpanIdeal(ctx)

		multiplesIdeal := ctx.Lemma("∀d:int. ring_ideal(int_ring, «multiplesOf»(d))", func(
			a *Argument,
			d *Expr[Int],
		) {
			a.Show(
				"multiples are closed under zero, sums and integer multiplication",
				Simp(Fwd(ring_ideal.RingIdealDef)),
				BySets(
					int_real_lift.MulRightZero,
					int_real_lift.LeftDistrib,
					int_real_lift.MulAssoc,
					int_real_lift.MulSym))
		})

		return ctx.Theorem(headline, func(a *Argument, p *Expr[Nat]) {
			R := a.TermAs[RingOps[Int]]("int_ring")
			span := a.TermAs[Set[Int]]("«integerIdeal»(p)")
			generator := a.TermAs[Int]("p")
			singleton := a.TermAs[Set[Int]]("{int_of_num(p)}")
			containsGenerator := a.Have(
				"the principal span contains its generator",
				"int_of_num(p) ∈ «integerIdeal»(p)",
				BySets(ring_ideal.SpanContains.At(R, singleton)))
			absorbs := a.Have(
				"multiplication by any integer stays in the principal span",
				"∀z:int. int_of_num(p) * z ∈ «integerIdeal»(p)",
				Derive(func(b *Argument) {
					z := b.FixAs[Int]("z")
					b.Show(
						"ideal absorption includes each multiple of the generator",
						BySets(
							At(spanIdeal, p),
							containsGenerator,
							ring_ideal.IdealMul.At(R, span, z, generator),
							int_real_lift.MulSym.At(generator, z)))
				}))
			containsMultiples := a.Have(
				"every multiple of the generator belongs to the span",
				"«multiplesOf»(int_of_num(p)) ⊆ «integerIdeal»(p)",
				BySets(absorbs))
			a.Show(
				"minimality of ideal span gives the reverse containment",
				BySets(
					containsMultiples,
					At(multiplesIdeal, generator),
					ring_ideal.SpanLeast.At(R, singleton, a.TermAs[Set[Int]]("«multiplesOf»(int_of_num(p))")),
					int_real_lift.MulRightIdentity.At(generator)))
		})
	}),
})}

// IntegerPrimeIdealMaximal — a prime generates a maximal ideal of the
// integers: a containing ideal's nonnegative generator divides the prime.
var IntegerPrimeIdealMaximal = integerPrimeIdealMaximalThm{family.Add(registry.ProofEntry{
	Name: "IntegerPrimeIdealMaximal",
	Key:  "prop_cfef71b16b1e4e3",
	Reading: "nat_prime excludes 0 and 1 (2 divides 0): the " +
		"ideal of 0 is not maximal and that of 1 is the whole ring.",
	Build: family.Sections(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "maximal_ideal(int_ring, ideal_span(int_ring, {int_of_num(p)}))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		spanIdeal := principalSpanIdeal(ctx)

		nonnegativeGenerator := ctx.Lemma(Statement{
			Binders:    "∀I:set(int).",
			Hypotheses: []string{"ring_ideal(int_ring, I)"},
			Conclusion: "∃d:num. I = «multiplesOf»(int_of_num(d))",
		}, func(a *Argument, I *Expr[Set[Int]], ideal Fact) {
			additiveSubgroup := a.Have(
				"an integer ideal is an additive subgroup",
				"subgroup(additive_group(int_ring), I)",
				By(ideal, quotient_ring.IdealSubgroup.Read(int_real_lift.CommRingOn).At(I)))
			a.Show(
				"the subgroup's nonnegative generator generates the ideal",
				By(additiveSubgroup, int_div_rem.IntegerSubgroupPrincipal.At(I)))
		})

		return ctx.Theorem(headline, func(a *Argument, p *Expr[Nat], prime Fact) {
			R := a.TermAs[RingOps[Int]]("int_ring")
			generator := a.TermAs[Int]("p")
			one := a.TermAs[Int]("1")
			singleton := a.TermAs[Set[Int]]("{int_of_num(p)}")
			notDividesOne := a.Have(
				"a prime cannot divide one",
				"¬(p ∣ 1)",
				By(prime, nat_prime.PrimeDef.At(p), nat_divides.DividesOne.At(p)))
			proper := a.Have(
				"one is not a multiple of the prime",
				"int_of_num(1) ∉ «integerIdeal»(p)",
				BySets(
					notDividesOne,
					At(IntegerPrincipalIdeal, p),
					int_divides.OfNumDivides.At(p, a.TermAs[Nat]("1")),
					int_divides.IntDividesDef.At(generator, one)))
			overIdeals := a.Have(
				"a containing ideal is the principal ideal or contains one",
				Statement{
					Binders: "∀J:set(int).",
					Hypotheses: []string{
						"ring_ideal(int_ring, J)",
						"«integerIdeal»(p) ⊆ J",
					},
					Conclusion: "J = «integerIdeal»(p) ∨ int_of_num(1) ∈ J",
				},
				Derive(func(b *Argument) {
					J := b.FixAs[Set[Int]]("J")
					over := b.Assume()
					d, generated := b.ObtainAs[Nat](
						"choose the containing ideal's nonnegative generator",
						"∃d:num. J = «multiplesOf»(int_of_num(d))",
						By(over, At(nonnegativeGenerator, J)))
					divides := b.Have(
						"the containing ideal's generator divides the prime",
						"d ∣ p",
						BySets(
							generated,
							over,
							ring_ideal.SpanContains.At(R, singleton),
							int_divides.IntDividesDef.At(b.TermAs[Int]("d"), generator),
							int_divides.OfNumDivides.At(d, p)))
					different := b.Unless(
						b.Term("d = p"),
						"the same generator gives the original principal ideal",
						Given(func(c *Argument, same Fact) {
							c.Show(
								"equal generators give equal ideals",
								By(Normalized, generated, same, At(IntegerPrincipalIdeal, p)))
						}))
					unitGenerator := b.Have(
						"the other divisor of a prime is one",
						"d = 1",
						By(prime, different, divides, nat_prime.PrimeDef.At(p)))
					b.Show(
						"the ideal generated by one contains one",
						BySets(generated, unitGenerator, int_real_lift.MulRightIdentity.At(one)))
				}))
			a.Show(
				"properness and the containing-ideal classification give maximality",
				Simp(Fwd(ring_ideal.MaximalIdealDef)),
				By(proper, overIdeals, At(spanIdeal, p)))
		})
	}),
})}

// PrimeFieldOn — the integers modulo a prime p are a finite field of p
// elements: the residues below p represent its cosets exactly once.
var PrimeFieldOn = primeFieldOnThm{family.Add(registry.ProofEntry{
	Name:    "PrimeFieldOn",
	Key:     "prop_9e8f83ab5dc77c2c",
	Reading: "The field's points are cosets, sets of integers.",
	Build: family.Sections(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "finite_field(«primeField»(p)) ∧ has_size(«primeField»(p).carrier, p)",
		Abbrev: Abbrev{
			{Name: "cosets", Text: "λn:num. left_cosets(int_add, 𝕌, «integerIdeal»(n))"},
			{Name: "primeField", Text: "λn:num. ideal_quotient_field(int_ring, «integerIdeal»(n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		residueClasses := integerResidueClassCount(ctx)
		spanIdeal := principalSpanIdeal(ctx)

		cosetCongruence := ctx.Lemma(
			"∀p:num. ∀x y:int. "+
				"    coset_map(int_add, «integerIdeal»(p), x) = coset_map(int_add, «integerIdeal»(p), y) ⇔ "+
				"    x - y ∈ «integerIdeal»(p)",
			func(a *Argument, p *Expr[Nat], x, y *Expr[Int]) {
				I := a.TermAs[Set[Int]]("«integerIdeal»(p)")
				a.Show(
					"two cosets of an ideal agree exactly when the difference of their representatives lies in it",
					Simp(Fwd(group.CosetMapDef)),
					By(
						At(spanIdeal, p),
						set_basic.InUniv.At(x),
						set_basic.InUniv.At(y),
						quotient_ring.CosetEqIff.Read(int_real_lift.CommRingOn).AsFact().At(I, x, y)))
			})

		return ctx.Theorem(headline, func(a *Argument, p *Expr[Nat], prime Fact) {
			R := a.TermAs[RingOps[Int]]("int_ring")
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(int_real_lift.CommRingOn))
			I := a.TermAs[Set[Int]]("«integerIdeal»(p)")
			F := a.TermAs[FieldOps[Set[Int]]]("«primeField»(p)")
			cosetOf := a.TermAs[Fun[Int, Set[Int]]]("coset_map(int_add, «integerIdeal»(p))")
			positive := a.Have(
				"a prime modulus is positive",
				"0 < p",
				ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			quotientField := a.Have(
				"the quotient by the prime's maximal ideal is a field",
				"field_on(«primeField»(p))",
				By(
					prime,
					IntegerPrimeIdealMaximal.At(p),
					quotient_ring.QuotientFieldOn.Read(int_real_lift.CommRingOn).At(I)))
			cosets := a.Have(
				"the additive cosets are the image of the integers under the coset map",
				"«cosets»(p) = image(coset_map(int_add, «integerIdeal»(p)), 𝕌)",
				By(set_order.SubsetUniv.At(I), quotient_group.LeftCosetsImage.Read(additive).At(I)))
			counted := a.Have(
				"two integers share a coset exactly when congruent modulo p, so the cosets number p",
				"has_size(«cosets»(p), p)",
				By(positive, cosets, At(cosetCongruence, p), At(residueClasses, p, cosetOf)))
			size := a.Have(
				"the quotient field's carrier is the set of its additive cosets",
				"has_size(«primeField»(p).carrier, p)",
				By(counted, quotient_ring.IdealQuotientFieldDef.At(R, I)))
			a.Show(
				"the quotient is a finite field with the stated number of points",
				By(
					quotientField,
					size,
					FiniteFieldDef.At(F),
					cardinality.HasSizeDef.At(a.TermAs[Set[Set[Int]]]("«primeField»(p).carrier"), p)))
		})
	}),
})}

// CongruenceCancel — modulo a prime p, a factor that p does not divide
// cancels from a congruence. Read in a field F of p elements: c·x and c·y
// have one image, the image of c is not zero, and a field cancels a nonzero
// factor, so x and y have one image and are congruent. The integers modulo p
// are such a field.
var CongruenceCancel = congruenceCancelThm{family.Add(registry.ProofEntry{
	Name: "CongruenceCancel",
	Key:  "prop_d7605510854f007e",
	Build: family.Sections(Statement{
		Binders: "∀p:num. ∀c x y:int.",
		Hypotheses: []string{
			"nat_prime(p)",
			"¬(p ∣ c)",
			"c * x ≡ c * y (mod p)",
		},
		Conclusion: "x ≡ y (mod p)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		inField := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p:num. ∀c x y:int.",
			Hypotheses: []string{
				"nat_prime(p)",
				"has_size(F.carrier, p)",
				"¬(int_of_num(p) ∣ c)",
				"c * x ≡ c * y (mod int_of_num(p))",
			},
			Conclusion: "x ≡ y (mod int_of_num(p))",
		}, func(
			arg *Argument,
			F field.FieldFact[on.F],
			p *Expr[Nat],
			c, x, y *Expr[Int],
			prime, size, notDivides, congruent Fact,
		) {
			ring := field.RingOn.Read(F)
			multiplies := ring_homomorphism.MapMul.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring))
			inCarrier := characteristic_zero.IntegerMapInCarrier.Read(ring)
			characteristic := arg.Have(
				"F has characteristic p",
				"field_characteristic(F, p)",
				By(prime, size, PrimeSizeCharacteristic.Read(F).At(p)))
			images := arg.Have(
				"c·x and c·y have one image, the product of the images",
				"integer_map(field_ring(F), c) * integer_map(field_ring(F), x) = "+
					"integer_map(field_ring(F), c) * integer_map(field_ring(F), y)",
				By(
					characteristic,
					congruent,
					IntegerMapEqIff.Read(F).At(p, arg.TermAs[Int]("c * x"), arg.TermAs[Int]("c * y")),
					multiplies.AsFact().At(c, x),
					multiplies.AsFact().At(c, y),
					set_basic.InUniv))
			cancelled := arg.Have(
				"the image of c is not zero, as p does not divide c, and a field cancels it",
				"integer_map(field_ring(F), x) = integer_map(field_ring(F), y)",
				By(
					notDivides,
					images,
					characteristic,
					IntegerMapKernel.Read(F).At(p, c),
					inCarrier,
					integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(F)).AsFact().At(
						arg.TermAs[A]("integer_map(field_ring(F), c)"),
						arg.TermAs[A]("integer_map(field_ring(F), x)"),
						arg.TermAs[A]("integer_map(field_ring(F), y)"))))
			arg.Show(
				"integers with one image are congruent",
				By(characteristic, cancelled, IntegerMapEqIff.Read(F).At(p, x, y)))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			p *Expr[Nat],
			c, x, y *Expr[Int],
			prime, notDivides, congruent Fact,
		) {
			arg.Show(
				"the integers modulo p are a field with p elements",
				By(
					prime,
					notDivides,
					congruent,
					PrimeFieldOn.At(p),
					FiniteFieldDef,
					At(
						inField,
						arg.TermAs[FieldOps[Set[Int]]](
							"ideal_quotient_field(int_ring, ideal_span(int_ring, {int_of_num(p)}))"),
						p,
						c,
						x,
						y)))
		})
	}),
})}

// SquareModIff — for a field F with a prime number p of elements, an integer
// a is a square mod p exactly when its image in F is a square there. A square
// root x of a mod p maps to a square root of a's image, since the integers'
// map is multiplicative and images agree exactly for integers congruent mod
// p; conversely a square root in F is the image of some integer x, and then
// x·x and a have the same image, so x·x ≡ a.
var SquareModIff = squareModIffThm{family.Add(registry.ProofEntry{
	Name: "SquareModIff",
	Key:  "prop_ba9bdc2c7d6621ef",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀a:int.",
		Hypotheses: []string{
			"nat_prime(p)",
			"has_size(F.carrier, p)",
		},
		Conclusion: "(∃x:int. x * x ≡ a (mod p)) ⇔ " +
			"(∃z:A. z ∈ F.carrier ∧ z * z = integer_map(field_ring(F), a))",
	}, func(arg *Argument, F field.FieldFact[on.F], p *Expr[Nat], a *Expr[Int], prime, size Fact) {
		ring := field.RingOn.Read(F)
		multiplies := ring_homomorphism.MapMul.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring))
		characteristic := arg.Have(
			"F has characteristic p",
			"field_characteristic(F, p)",
			By(prime, size, PrimeSizeCharacteristic.Read(F).At(p)))
		arg.Iff()
		arg.Forward(
			"a square root of a mod p maps to a square root of a's image",
			func(b *Argument, squareMod Fact) {
				x, root := b.UnpackAs[Int](squareMod, "x")
				b.Take(b.TermAs[A]("integer_map(field_ring(F), x)"))
				b.Show(
					"the image of x lies in F, and its square is the image of x·x, which is a's as x·x ≡ a",
					By(
						characteristic,
						root,
						IntegerMapEqIff.Read(F).At(p, b.TermAs[Int]("x * x"), a),
						characteristic_zero.IntegerMapInCarrier.Read(ring).At(x),
						multiplies.AsFact().At(x, x),
						set_basic.InUniv))
			})
		arg.Backward(
			"a square root in F is the image of an integer whose square is a mod p",
			func(b *Argument, squareInField Fact) {
				z, root := b.UnpackAs[A](squareInField, "z")
				parts := b.Conjuncts(
					root,
					"z lies in F",
					"z·z is the image of a")
				x, preimage := b.ObtainAs[Int](
					"z is the image of an integer x",
					"∃x:int. integer_map(field_ring(F), x) = z",
					By(prime, size, IntegerMapOnto.Read(F).At(p, b.MemberOf[on.F](z, parts[0]))))
				b.Take(x)
				b.Show(
					"x·x maps to z·z, the image of a, and equal images make x·x ≡ a",
					By(
						Normalized,
						characteristic,
						preimage,
						parts[1],
						multiplies.AsFact().At(x, x),
						set_basic.InUniv,
						IntegerMapEqIff.Read(F).At(p, b.TermAs[Int]("x * x"), a)))
			})
	}),
})}
