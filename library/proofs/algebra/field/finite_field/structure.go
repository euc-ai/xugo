// structure.go — the characteristic of a field, and the prime subfield of a
// finite field, its size and the powers that fix its elements: either no
// positive multiple of one vanishes or the least one that does is prime, an
// integer maps to zero exactly when the characteristic divides it and two
// integers have one image exactly when they are congruent modulo it, so
// 1 + 1 ≠ 0 in odd characteristic and two fields of one characteristic send
// the same integers to zero, the
// multiples of one form a subfield of p elements, a finite field of
// characteristic p has a power of p elements, each positive power of p
// exceeds one and annihilates one, a field of a prime number p of elements
// has characteristic p and each of its elements is the image of an integer,
// a nonzero element raised to one less than
// the size is one, every element is fixed by raising it to the size, a finite
// subfield has a power of the characteristic of elements, and a finite
// subfield of q elements is the set of points the q-th power fixes.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldCharacteristicCases — a field has characteristic zero or a prime
// characteristic: when some positive multiple of one vanishes, the least such
// multiple is prime, since a field has no zero divisors, so a factorization of
// it makes the multiple at one factor vanish, and no smaller multiple does.
var FieldCharacteristicCases = fieldCharacteristicCasesThm{family.Add(registry.ProofEntry{
	Name: "FieldCharacteristicCases",
	Key:  "prop_b1b68414fbd3a736",
	Build: family.Theorem(
		"∀F:field_on(A). "+
			"    characteristic_zero(field_ring(F)) ∨ (∃p:num. ring_prime_characteristic(field_ring(F), p))",
		func(a *Argument, F field.FieldFact[on.F]) {
			ring := field.RingOn.Read(F)
			additive := comm_ring.AddMonoidOn.Read(ring)
			R := a.TermAs[RingOps[A]]("field_ring(F)")
			vanishing := a.Assuming(
				a.Term("∃n:num. 0 < n ∧ «numeral»(F, n) = F.zero"),
				"we may assume some positive multiple of one vanishes",
				Given(func(b *Argument, none Fact) {
					b.Show(
						"a field with no such multiple has characteristic zero",
						By(none, comm_ring.CharacteristicZeroDef.At(R)))
				}))
			p, least := a.ObtainAs[Nat](
				"take the least positive multiple of one that vanishes",
				"∃p:num. 0 < p ∧ «numeral»(F, p) = F.zero ∧ (∀m:num. 0 < m ∧ m < p ⇒ «numeral»(F, m) ≠ F.zero)",
				By(
					vanishing,
					nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λn:num. 0 < n ∧ «numeral»(F, n) = F.zero"))))
			parts := a.Conjuncts(
				least,
				"p is positive",
				"the multiple of one at p vanishes",
				"no smaller positive multiple does")
			positive, annihilates, minimal := parts[0], parts[1], parts[2]
			one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
			notOne := a.Have(
				"p is not 1, since one itself is nonzero",
				"p ≠ 1",
				By(annihilates, field.OneNotZeroOn.Read(F), comm_monoid.PowOneOn.Read(additive).At(one)))
			divisors := a.Have(
				"a divisor of p is 1 or p",
				"∀x:num. x ∣ p ⇒ x = 1 ∨ x = p",
				Derive(func(b *Argument) {
					x := b.FixAs[Nat]("x")
					divides := b.Assume()
					y, factorization := b.ObtainAs[Nat](
						"write p as x * y",
						"∃y:num. p = x * y",
						By(divides, nat_divides.DividesFactor))
					factorVanishes := b.Have(
						"the multiples at x and y multiply to the one at "+
							"p, which is zero, and a field has no zero divisors",
						"«numeral»(F, x) = F.zero ∨ «numeral»(F, y) = F.zero",
						By(
							annihilates,
							factorization,
							comm_ring.AddPowMulOn.Read(ring).At(x, y),
							field.MulEqZeroOn.Read(F).At(
								comm_monoid.PowIn.Read(additive).At(one, x),
								comm_monoid.PowIn.Read(additive).At(one, y))))
					factorsPositive := b.Have(
						"the factors of the positive p are positive",
						"0 < x ∧ 0 < y",
						ByArith(positive, factorization, nat_arith.MulEqZero.At(x, y)))
					b.Show(
						"by minimality the factor that vanishes is at least p: at x "+
							"this gives x = p, and at y it gives x * y ≤ 1 * y, so x = 1",
						ByArith(
							minimal.At(x),
							minimal.At(y),
							factorization,
							factorsPositive,
							factorVanishes,
							nat_order.LessEqMulNonzero.At(x, y),
							nat_order.LessEqMulRightCancel.At(x, b.TermAs[Nat]("1"), y)))
				}))
			prime := a.Have(
				"so the least positive multiple of one that vanishes is prime",
				"nat_prime(p)",
				By(notOne, divisors, nat_prime.PrimeDef))
			a.Show(
				"a prime multiple of one that vanishes is a prime characteristic",
				By(prime, annihilates, PrimeCharacteristicDef.At(R, p)))
		}),
})}

// IntegerMapKernel — in a field of characteristic p, an integer maps to zero
// exactly when p divides it. In characteristic zero the integer map is an
// injective ring homomorphism, which sends only zero to zero. At a prime p, p
// maps to zero and so do its multiples; and when z maps to zero, the natural
// common divisor of p and z that Bézout writes as a combination of the two maps
// to zero as well, so it is not one, and as a divisor of the prime it is p
// itself.
var IntegerMapKernel = integerMapKernelThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapKernel",
	Key:  "prop_a769ae565b5a081b",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀p:num. ∀z:int.",
		Hypotheses: []string{
			"field_on(F)",
			"field_characteristic(F, p)",
		},
		Conclusion: "integer_map(field_ring(F), z) = F.zero ⇔ &p ∣ z",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		p *Expr[Nat],
		z *Expr[Int],
		isField field.FieldFact[on.F],
		characteristic Fact,
	) {
		ring := field.RingOn.Read(isField)
		a.Do(a.Unfolded(characteristic, FieldCharacteristicDef).SplitDisj(
			LeftHolds(
				"in characteristic zero only zero maps to zero, and zero is the only multiple of zero",
				Given(func(b *Argument, zero Fact) {
					parts := b.Conjuncts(
						zero,
						"p is zero",
						"the field has characteristic zero")
					injective := b.Have(
						"characteristic zero makes the integer map injective",
						"injective_on(𝕌, integer_map(field_ring(F)))",
						By(characteristic_zero.IntegerMapInjective, ring, parts[1]))
					zeroMultiples := b.Have(
						"zero is the only multiple of zero",
						"&0 ∣ z ⇔ z = &0",
						ByArith(int_divides.IntDividesDef.At(b.TermAs[Int]("&0"), z)))
					integers := characteristic_zero.IntegerMapHomomorphism.Read(ring)
					b.Show(
						"an injective ring homomorphism sends only zero to zero",
						By(
							parts[0],
							injective,
							zeroMultiples,
							int_real_lift.IntegerRingCarrierUniversal.At(z),
							ring_homomorphism.ZeroIffImageZero.Read(integers).AsFact().At(z)))
				})),
			RightHolds(
				"at a prime p the integers mapping to zero are the multiples of p",
				Given(func(b *Argument, prime Fact) {
					parts := b.Conjuncts(
						b.Unfolded(prime, PrimeCharacteristicDef),
						"p is positive",
						"p is prime",
						"p copies of one vanish")
					pZero := b.Have(
						"p maps to zero",
						"integer_map(field_ring(F), &p) = F.zero",
						By(parts[2], characteristic_zero.IntegerMapOfNum.Read(ring).At(p)))
					b.Iff()
					b.Forward(
						"an integer mapping to zero is a multiple of p",
						func(c *Argument, killed Fact) {
							m, common := c.ObtainAs[Nat](
								"p and z have a natural common divisor that is an integer combination of them",
								"∃m:num. int_of_num(m) ∣ &p ∧ int_of_num(m) ∣ z ∧ (∃x y:int. int_of_num(m) = &p * x + z * y)",
								By(
									int_divides.BezoutNonneg.At(c.TermAs[Int]("&p"), z),
									int_embed.ExistsNonneg.At(c.TermAs[Set[Int]](
										"λd:int. d ∣ &p ∧ d ∣ z ∧ (∃x y:int. d = &p * x + z * y)"))))
							divisor := c.Conjuncts(
								common,
								"m divides p",
								"m divides z",
								"m is a combination of p and z")
							x, y, combination := c.Unpack2As[Int, Int](divisor[2])
							mZero := c.Have(
								"the combination maps to zero",
								"integer_map(field_ring(F), &m) = F.zero",
								combination.Rw(),
								Simp(Fwd(characteristic_zero.IntegerMapHom.Read(ring))),
								ByArith(
									killed,
									pZero,
									characteristic_zero.IntegerMapInCarrier.Read(ring).At(x),
									characteristic_zero.IntegerMapInCarrier.Read(ring).At(y)))
							notOne := c.Have(
								"one does not map to zero, so m is not one",
								"m ≠ 1",
								By(mZero, characteristic_zero.IntegerMapHom.Read(ring), field.OneNotZeroOn.Read(isField)))
							isP := c.Have(
								"a divisor of the prime p other than one is p",
								"m = p",
								By(parts[1], notOne, divisor[0], int_divides.OfNumDivides.At(m, p), nat_prime.PrimeDef.At(p)))
							c.Show(
								"p is m, which divides z",
								By(Normalized, isP, divisor[1]))
						})
					b.Backward(
						"a multiple of p maps to zero",
						func(c *Argument, divides Fact) {
							k, multiple := c.UnpackAs[Int](c.Unfolded(divides, int_divides.IntDividesDef), "k")
							c.Show(
								"z maps to the image of p, zero, times the image of k",
								multiple.Rw(),
								Simp(Fwd(characteristic_zero.IntegerMapHom.Read(ring))),
								ByArith(pZero, characteristic_zero.IntegerMapInCarrier.Read(ring).At(k)))
						})
				})),
		))
	}),
})}

// IntegerMapEqIff — in a field of characteristic p two integers have the same
// image exactly when they are congruent mod p: the integers' map is additive,
// so the images agree exactly when a − b maps to zero, and the integers that
// map to zero are the multiples of p.
var IntegerMapEqIff = integerMapEqIffThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapEqIff",
	Key:  "prop_f0d9eea296ba52aa",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀p:num. ∀a b:int.",
		Hypotheses: []string{"field_characteristic(F, p)"},
		Conclusion: "integer_map(field_ring(F), a) = integer_map(field_ring(F), b) ⇔ a ≡ b (mod p)",
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		p *Expr[Nat],
		a, b *Expr[Int],
		characteristic Fact,
	) {
		ring := field.RingOn.Read(F)
		inCarrier := characteristic_zero.IntegerMapInCarrier.Read(ring)
		difference := arg.TermAs[Int]("a - b")
		subtracts := arg.Have(
			"the integers' map takes a − b to the difference of the images",
			"integer_map(field_ring(F), a - b) = integer_map(field_ring(F), a) - integer_map(field_ring(F), b)",
			By(
				ring_homomorphism.MapSub.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring)),
				set_basic.InUniv))
		kernel := arg.Have(
			"a − b maps to zero exactly when p divides it, which is a ≡ b",
			"integer_map(field_ring(F), a - b) = F.zero ⇔ a ≡ b (mod p)",
			By(characteristic, IntegerMapKernel.Read(F).At(p, difference), int_congruence.IntCongDef))
		arg.Iff()
		arg.Forward(
			"equal images make a − b map to zero",
			func(c *Argument, equal Fact) {
				c.Show(
					"so a ≡ b",
					ByArith(F, kernel, equal, subtracts, inCarrier.At(a), inCarrier.At(b), inCarrier.At(difference)))
			})
		arg.Backward(
			"when a ≡ b the difference of the images is the image of a − b, zero",
			func(c *Argument, congruent Fact) {
				c.Show(
					"so the images agree",
					ByArith(F, kernel, congruent, subtracts, inCarrier.At(a), inCarrier.At(b)))
			})
	}),
})}

// OddCharacteristicTwoNonzero — in a field of odd prime characteristic p,
// 2 = 1 + 1 is not zero: 1 + 1 is the image of the integer 2, which maps to
// zero exactly when p divides it, and a prime dividing the prime 2 is 2.
var OddCharacteristicTwoNonzero = oddCharacteristicTwoNonzeroThm{family.Add(registry.ProofEntry{
	Name: "OddCharacteristicTwoNonzero",
	Key:  "prop_225fd676df05e20d",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"field_characteristic(F, p)",
		},
		Conclusion: "F.one + F.one ≠ F.zero",
	}, func(a *Argument, F field.FieldFact[on.F], p *Expr[Nat], prime, odd, characteristic Fact) {
		ring := field.RingOn.Read(F)
		two := a.TermAs[Nat]("2")
		a.Show(
			"1 + 1 is the image of 2, which p would divide only by being 2",
			By(
				prime,
				odd,
				characteristic,
				characteristic_zero.IntegerMapOfNum.Read(ring).At(two),
				comm_monoid.PowTwoOn.Read(comm_ring.AddMonoidOn.Read(ring)).At(
					a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))),
				IntegerMapKernel.Read(F).At(p, a.TermAs[Int]("2")),
				int_divides.OfNumDivides.At(p, two),
				nat_prime.PrimeDividesPrime.At(p, two),
				nat_prime.PrimeTwo))
	}),
})}

// SameCharacteristicFromCharacteristic — two fields of one characteristic send the same integers to
// zero: in each field an integer maps to zero exactly when the characteristic divides it.
var SameCharacteristicFromCharacteristic = sameCharacteristicFromCharacteristicThm{family.Add(registry.ProofEntry{
	Name: "SameCharacteristicFromCharacteristic",
	Key:  "prop_af858136aa5a06d0",
	Reading: "Field axioms and primality are both load-bearing: the zero ring " +
		"satisfies ring_prime_characteristic at every prime and sends every integer " +
		"to zero, and GF(2) and GF(3) both annihilate 6 while disagreeing at 2.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀G:field_ops(B). ∀p:num.",
		Hypotheses: []string{
			"field_on(F)",
			"field_on(G)",
			"field_characteristic(F, p)",
			"field_characteristic(G, p)",
		},
		Conclusion: "same_characteristic(F, G)",
	}, func(a *Argument, F *Expr[FieldOps[A]], G *Expr[FieldOps[B]], p *Expr[Nat], hypotheses Fact) {
		a.Show(
			"both kernels are the multiples of p",
			By(
				hypotheses,
				SameCharacteristicDef,
				IntegerMapKernel.Inst[A]().At(F, p),
				IntegerMapKernel.Inst[B]().At(G, p)))
	}),
})}

// FiniteFieldCharacteristic — a finite field has a prime characteristic:
// the integers do not embed in a finite carrier, so its characteristic is not
// zero, and a field's characteristic is zero or prime.
var FiniteFieldCharacteristic = finiteFieldCharacteristicThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldCharacteristic",
	Key:  "prop_74bea39c238886af",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A).",
		Hypotheses: []string{
			"finite(k.carrier)",
		},
		Conclusion: "∃p:num. ring_prime_characteristic(field_ring(k), p)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerInfinite := ctx.Lemma("infinite(𝕌⟨A:int⟩)", func(a *Argument) {
			embedding := a.TermAs[Fun[Nat, Int]]("int_of_num")
			naturals := a.TermAs[Set[Nat]]("𝕌")
			integers := a.TermAs[Set[Int]]("𝕌")
			injective := a.Have(
				"natural numbers embed injectively into the integers",
				"injective_on(𝕌⟨A:num⟩, int_of_num)",
				BySets(functions.InjectiveOnDef.At(naturals, embedding), int_embed.OfNumEq))
			a.Show(
				"the integer universe contains an infinite injective image",
				BySets(
					injective,
					num_segment.Infinite,
					finite_set.InfiniteImage.At(embedding, naturals),
					finite_set.InfiniteSuperset.At(a.TermAs[Set[Int]]("image(int_of_num, 𝕌⟨A:num⟩)"), integers)))
		})

		notZeroCharacteristic := ctx.Lemma(Statement{
			Binders:    "∀k:field_on(A).",
			Hypotheses: []string{"finite(k.carrier)"},
			Conclusion: "¬characteristic_zero(field_ring(k))",
		}, func(a *Argument, k, finite Fact) {
			zeroCharacteristic := a.SupposeNot()
			ring := field.RingOn.Read(k)
			ringValue := a.TermAs[RingOps[A]]("field_ring(k)")
			integerMap := a.TermAs[Fun[Int, A]]("«integerMap»(k)")
			integers := a.TermAs[Set[Int]]("𝕌")
			injective := a.Have(
				"the integer map is injective in characteristic zero",
				"injective_on(𝕌⟨A:int⟩, «integerMap»(k))",
				By(ring, zeroCharacteristic, characteristic_zero.IntegerMapInjective.At(ringValue)))
			finiteImage := a.Have(
				"the integer image lies inside the finite field carrier",
				"finite(image(«integerMap»(k), 𝕌⟨A:int⟩))",
				BySets(
					characteristic_zero.IntegerMapInCarrier.Read(ring),
					finite,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[A]]("image(«integerMap»(k), 𝕌⟨A:int⟩)"), a.TermAs[Set[A]]("k.carrier"))))
			a.Show(
				"an injective finite image would make the integer universe finite",
				By(
					finiteImage,
					injective,
					integerInfinite,
					finite_set.FiniteImageInjEq.At(integerMap, integers),
					finite_set.InfiniteDef.At(integers)))
		})

		return ctx.Theorem(headline, func(a *Argument, k, finite Fact) {
			a.Show(
				"a field's characteristic is zero or prime, and a finite field's is not zero",
				By(Normalized, finite, Read(notZeroCharacteristic, k), FieldCharacteristicCases.Read(k)))
		})
	}),
})}

// PrimeSubfield — the natural multiples of one form a subfield with p
// elements: the integer map has kernel (p), and its finite image is a field.
var PrimeSubfield = primeSubfieldThm{family.Add(registry.ProofEntry{
	Name: "PrimeSubfield",
	Key:  "prop_50fb3e28b40a6f13",
	Reading: "Prime annihilation of one is the genuine characteristic " +
		"because the field is nonzero. No additional minimality premise is needed.",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀p:num.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"ring_prime_characteristic(field_ring(k), p)",
		},
		Conclusion: "subfield(k, «numerals»(k)) ∧ has_size(«numerals»(k), p)",
		Abbrev: Abbrev{
			{Name: "image", Text: "λF:field_ops(A). integer_image(field_ring(F))"},
			{Name: "kernel", Text: "λF:field_ops(A). ring_kernel(F.zero, 𝕌⟨A:int⟩, «integerMap»(F))"},
			{Name: "numerals", Text: "λF:field_ops(A). {monoid_pow(F.add, F.zero, F.one, n) | n:num | ⊤}"},
			{Name: "imageRing", Text: "λF:field_ops(A). restrict_ring(field_ring(F), «image»(F))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerMapHomomorphism := ctx.Lemma("∀k:field_on(A). "+
			"    ring_homomorphism(int_ring, «imageRing»(k), «integerMap»(k))",
			func(a *Argument, k Fact) {
				ring := field.RingOn.Read(k)
				R := a.TermAs[RingOps[A]]("field_ring(k)")
				a.Show(
					"the integer map is a ring homomorphism into its image",
					By(ring, characteristic_zero.IntegerMapIntoImage.At(R)))
			})
		integerKernel := ctx.Lemma(Statement{
			Binders:    "∀k:field_on(A). ∀p:num.",
			Hypotheses: []string{"ring_prime_characteristic(field_ring(k), p)"},
			Conclusion: "«kernel»(k) = «integerIdeal»(p)",
		}, func(a *Argument, k Fact, p *Expr[Nat], characteristic Fact) {
			ring := field.RingOn.Read(k)
			R := a.TermAs[RingOps[A]]("field_ring(k)")
			integers := a.TermAs[Set[Int]]("𝕌")
			integerMap := a.TermAs[Fun[Int, A]]("«integerMap»(k)")
			Z := a.TermAs[RingOps[Int]]("int_ring")
			kernel := a.TermAs[Set[Int]]("«kernel»(k)")
			hom := Read(integerMapHomomorphism, k)
			ideal := a.Have(
				"the integer-map kernel is an ideal",
				"ring_ideal(int_ring, «kernel»(k))",
				By(ring_homomorphism.KernelIdeal.Read(hom)))
			generatorIn := a.Have(
				"the characteristic maps to zero",
				"int_of_num(p) ∈ «kernel»(k)",
				BySets(
					characteristic,
					ring,
					PrimeCharacteristicDef.At(R, p),
					characteristic_zero.IntegerMapOfNum.At(R, p),
					ring_homomorphism.RingKernelDef.At(a.TermAs[A]("k.zero"), integers, integerMap)))
			contains := a.Have(
				"the kernel contains the characteristic's principal ideal",
				"«integerIdeal»(p) ⊆ «kernel»(k)",
				BySets(
					ideal,
					generatorIn,
					ring_ideal.SpanLeast.At(Z, a.TermAs[Set[Int]]("{int_of_num(p)}"), kernel)))
			proper := a.Have(
				"one is outside the kernel because its image is nonzero",
				"int_of_num(1) ∉ «kernel»(k)",
				BySets(
					field.OneNotZeroOn.Read(k),
					ring_homomorphism.MapOne.Read(hom),
					ring_homomorphism.RingKernelDef.At(a.TermAs[A]("k.zero"), integers, integerMap)))
			a.Show(
				"maximality forces the proper containing ideal to be the principal ideal",
				By(
					proper,
					ideal,
					characteristic,
					contains,
					PrimeCharacteristicDef.At(R, p),
					IntegerPrimeIdealMaximal.At(p),
					ring_ideal.MaximalIdealMaximal.At(Z, a.TermAs[Set[Int]]("«integerIdeal»(p)"), kernel)))
		})

		imageEquality := ctx.Lemma(
			"∀k:field_on(A). ∀x y:int. "+
				"    «integerMap»(k, x) = «integerMap»(k, y) ⇔ «integerMap»(k, x - y) = k.zero",
			func(a *Argument, k Fact, x, y *Expr[Int]) {
				hom := Read(integerMapHomomorphism, k)
				a.Show(
					"equal images are characterized by the additive kernel of their difference",
					BySets(
						group_homomorphism.EqIffInKernel.Read(ring_homomorphism.AdditiveHomomorphism.Read(hom)).AsFact().At(
							y, x),
						group_homomorphism.GroupKernelDef.At(
							a.TermAs[A]("k.zero"), a.TermAs[Set[Int]]("𝕌"), a.TermAs[Fun[Int, A]]("«integerMap»(k)")),
						int_real_lift.SubAddNeg.At(x, y),
						int_real_lift.AddSym.At(x, a.TermAs[Int]("-y"))))
			})

		residueClasses := integerResidueClassCount(ctx)

		integerImageSubfield := ctx.Lemma(Statement{
			Binders:    "∀k:field_on(A).",
			Hypotheses: []string{"finite(k.carrier)"},
			Conclusion: "subfield(k, «image»(k))",
		}, func(a *Argument, k, finite Fact) {
			ring := field.RingOn.Read(k)
			R := a.TermAs[RingOps[A]]("field_ring(k)")
			image := a.TermAs[Set[A]]("«image»(k)")
			carrier := a.TermAs[Set[A]]("k.carrier")
			imageRing := characteristic_zero.IntegerImageCommRing.Read(ring)
			inCarrier := a.Have(
				"the integer image lies in the field carrier",
				"«image»(k) ⊆ k.carrier",
				BySets(
					characteristic_zero.IntegerMapInCarrier.Read(ring),
					characteristic_zero.IntegerImageDef.At(R)))
			subring := a.Have(
				"the integer image is a subring: the field's ring restricted to it is a ring",
				"subring(field_ring(k), «image»(k))",
				By(ring, inCarrier, imageRing, comm_ring.SubringRingOn.At(R, image)))
			finiteImage := a.Have(
				"the integer image is finite as a subset of the finite carrier",
				"finite(«image»(k))",
				By(finite, inCarrier, finite_set.FiniteSubset.At(image, carrier)))
			domain := a.Have(
				"inside a field the integer image has no zero divisors, so it is an integral domain",
				"integral_domain_on(«imageRing»(k))",
				Unfold(integral_domain.IntegralDomainOn),
				By(
					field.OneNotZeroOn.Read(k),
					field.MulEqZeroOn.Read(k),
					imageRing,
					inCarrier,
					set_basic.SubsetDef))
			inverseClosed := a.Have(
				"the integer image contains the inverse of each of its elements",
				"∀x:A. x ∈ «image»(k) ⇒ k.inv(x) ∈ «image»(k)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inImage := b.Assume()
					nonzero := b.Unless(
						b.Term("x = k.zero"),
						"zero's inverse is zero and belongs to the image subring",
						Given(func(c *Argument, zero Fact) {
							c.Show(
								"the zero element remains inside the integer image under inverse",
								By(Normalized, zero, subring, field.InvZeroOn.Read(k), comm_ring.SubringZero.At(R, image)))
						}))
					y, inverse := b.ObtainAs[A](
						"a finite integral domain is a field, so x has an inverse in the image",
						"∃y:A. y ∈ «image»(k) ∧ k.mul(x, y) = k.one",
						By(finiteImage, inImage, nonzero, integral_domain.FiniteDomainIsField.Read(domain)))
					ambientInverse := field.InvRightUniqueOn.Read(k).AsFact().At(x, y)
					b.Show(
						"that inverse is the field's inverse of x",
						BySets(inImage, inverse, inCarrier, ambientInverse))
				}))
			a.Show(
				"the subring and inverse closure give a subfield",
				SimpAll(Fwd(comm_ring.SubringDef), Fwd(field.SubfieldDef)),
				By(inverseClosed, subring))
		})

		return ctx.Theorem(headline, func(a *Argument, k Fact, p *Expr[Nat], finite, characteristic Fact) {
			ring := field.RingOn.Read(k)
			R := a.TermAs[RingOps[A]]("field_ring(k)")
			zero := a.TermAs[A]("k.zero")
			integers := a.TermAs[Set[Int]]("𝕌")
			integerMap := a.TermAs[Fun[Int, A]]("«integerMap»(k)")
			positive := a.Have(
				"the prime characteristic is positive",
				"0 < p",
				ByArith(characteristic, PrimeCharacteristicDef.At(R, p), nat_prime.PrimeAtLeastTwo.At(p)))
			fibres := a.Have(
				"two integers have one image exactly when their difference lies in the kernel, the multiples of p",
				"∀x y:int. «integerMap»(k, x) = «integerMap»(k, y) ⇔ x - y ∈ «integerIdeal»(p)",
				Derive(func(b *Argument) {
					x := b.FixAs[Int]("x")
					y := b.FixAs[Int]("y")
					differenceIn := b.Have(
						"the difference belongs to the kernel exactly when it belongs to the principal ideal",
						"x - y ∈ «kernel»(k) ⇔ x - y ∈ «integerIdeal»(p)",
						By(Normalized, characteristic, Read(integerKernel, k).At(p)))
					b.Show(
						"equal images are a difference the integer map sends to zero",
						BySets(
							differenceIn,
							Read(imageEquality, k).At(x, y),
							ring_homomorphism.RingKernelDef.At(zero, integers, integerMap)))
				}))
			counted := a.Have(
				"the residues below p take every value of the integer map, and there are p of them",
				"image(λr:num. «integerMap»(k, int_of_num(r)), «residues»(p)) = «image»(k) ∧ "+
					"has_size(«image»(k), p)",
				By(positive, fibres, characteristic_zero.IntegerImageDef.At(R), At(residueClasses, p, integerMap)))
			multiples := a.Have(
				"the natural multiples of one are the integer image",
				"«numerals»(k) = «image»(k)",
				BySets(
					counted,
					characteristic_zero.IntegerImageDef.At(R),
					characteristic_zero.IntegerMapOfNum.Read(ring)))
			subfield := a.Have(
				"the finite integer image is a subfield",
				"subfield(k, «image»(k))",
				By(finite, Read(integerImageSubfield, k)))
			a.Show(
				"the p-element integer image is the subfield of natural multiples of one",
				By(multiples, counted, subfield))
		})
	}),
})}

// FiniteFieldSizePower — a finite field of prime characteristic p has a
// positive power of p elements: the natural multiples of one form its prime
// subfield of p elements, over which the field is a finite-dimensional
// vector space, and a space of dimension e over p scalars has p^e vectors.
var FiniteFieldSizePower = finiteFieldSizePowerThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldSizePower",
	Key:  "prop_e688be84668299f0",
	Reading: "The exponent is positive: a finite basis of k over " +
		"its prime subfield is nonempty since zero and one differ.",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀p:num.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"ring_prime_characteristic(field_ring(k), p)",
		},
		Conclusion: "∃e:num. 0 < e ∧ card(k.carrier) = p ^ e",
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteCarrierDimensional := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, A).",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"finite(M.carrier)",
			},
			Conclusion: "finite_dimensional(field_ring(F), M)",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, A]],
			h Fact,
		) {
			R := a.TermAs[RingOps[A]]("field_ring(F)")
			inverse := a.TermAs[Fun[A, A]]("F.inv")
			E, basis := a.ObtainAs[Set[A]](
				"choose a basis over the field",
				"∃E:set(A). module_basis(field_ring(F), M, E)",
				By(fieldOn, h, field.FieldRingSubfield.At(F), linear_independence.BasisExists.At(R, M, inverse)))
			finiteE := a.Have(
				"the basis is finite because it lies in the finite carrier",
				"finite(E)",
				By(
					fieldOn,
					h,
					basis,
					linear_independence.BasisInCarrier.At(R, M, E),
					finite_set.FiniteSubset.At(E, a.TermAs[Set[A]]("M.carrier"))))
			a.Do(Unfold(module_dimension.FiniteDimensionalDef))
			a.Take(E)
			a.Show(
				"this finite basis witnesses finite dimension",
				By(finiteE, basis))
		})

		return ctx.Theorem(headline, func(a *Argument, k Fact, p *Expr[Nat], h Fact) {
			K := a.TermAs[FieldOps[A]]("k")
			C, primeCarrierDef := a.LetAs[Set[A]]("C", "{monoid_pow(k.add, k.zero, k.one, n) | n:num | ⊤}")
			primeData := a.Have(
				"the natural multiples of one form a subfield with p elements",
				"subfield(k, C) ∧ has_size(C, p)",
				By(k, primeCarrierDef, h, PrimeSubfield.At(K, p)))
			F, scalarFieldDef := a.LetAs[FieldOps[A]]("F", "restrict_field(k, C)")
			scalarField := a.Have(
				"restricting to the prime subfield gives a field",
				"field_on(F)",
				By(Normalized, k, scalarFieldDef, primeData, field.SubfieldFieldOn.At(K, C)))
			scalarCarrier := a.Have(
				"its carrier is the prime subfield",
				"F.carrier = C",
				Simp(Fwd(scalarFieldDef), Fwd(field.RestrictFieldDef), Fwd(field.FieldCarrierDef)),
				Refl())
			scalarSize := a.Have(
				"the scalar field is finite and has size p",
				"finite_field(F) ∧ field_size(F) = p",
				By(
					Normalized,
					scalarField,
					scalarCarrier,
					primeData,
					cardinality.HasSizeDef.At(C, p),
					FiniteFieldDef.At(F),
					FieldSizeDef.At(F)))
			R, scalarRingDef := a.LetAs[RingOps[A]]("R", "field_ring(F)")
			V, regularDef := a.LetAs[ModuleOps[A, A]]("V", "regular_module(field_ring(k))")
			originalRing := a.TermAs[RingOps[A]]("field_ring(k)")
			regularModule := a.Have(
				"the field is a module over its own ring",
				"module_on(field_ring(k), V)",
				By(Normalized, field.RingOn.Read(k), regularDef, module.RegularModuleOn.At(originalRing)))
			primeModule := a.Have(
				"restriction of scalars makes it a module over the prime field",
				"module_on(R, V)",
				By(
					Normalized,
					scalarFieldDef,
					scalarRingDef,
					regularModule,
					primeData,
					field.SubfieldSubring.Read(k).At(C),
					field.RestrictFieldRing.At(K, C),
					module.ModuleRestrictScalars.At(originalRing, V, C)))
			carrierData := a.Have(
				"the regular module has k's carrier and zero",
				"V.carrier = k.carrier ∧ V.zero = k.zero",
				Simp(
					Fwd(regularDef),
					Fwd(module_record.RegularModuleDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RingCarrierDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.ModCarrierDef),
					Fwd(module_record.ModZeroDef)),
				Basic())
			finiteDimensional := a.Have(
				"the finite carrier gives finite dimension over the prime field",
				"finite_dimensional(R, V)",
				By(
					Normalized,
					scalarField,
					scalarRingDef,
					primeModule,
					h,
					carrierData,
					At(finiteCarrierDimensional, F, V)))
			vectorCount := a.Have(
				"the vector count is p raised to this dimension",
				"has_size(V.carrier, p ^ module_dim(R, V))",
				By(
					Normalized,
					scalarRingDef,
					finiteDimensional,
					primeModule,
					scalarSize,
					FiniteDimensionalSpaceSize.At(F, V)))
			inverse := a.TermAs[Fun[A, A]]("F.inv")
			zeroDimension := a.Have(
				"the dimension is zero exactly when zero is the only vector",
				"module_dim(R, V) = 0 ⇔ V.carrier = {V.zero}",
				Derive(func(b *Argument) {
					ringField := b.Have(
						"module_dimension states 'is a field' as ring_subfield over "+
							"the scalar ring's operations, so restate F in that form",
						"ring_subfield(R, F.inv, R.carrier)",
						Simp(Fwd(scalarRingDef)),
						By(field.FieldRingSubfield.Read(scalarField)))
					b.Show(
						"the dimension-zero criterion applies to this scalar field",
						By(ringField, finiteDimensional, primeModule, module_dimension.DimZero.At(R, V, inverse)))
				}))
			nontrivial := a.Have(
				"the carrier contains one, distinct from zero",
				"V.carrier ≠ {V.zero}",
				BySets(comm_ring.OneIn.Read(field.RingOn.Read(k)), field.OneNotZeroOn.Read(k), carrierData))
			positiveDimension := a.Have(
				"the dimension over the prime field is positive",
				"0 < module_dim(R, V)",
				ByArith(nontrivial, zeroDimension))
			vectorCarrier := a.TermAs[Set[A]]("V.carrier")
			power := a.TermAs[Nat]("p ^ module_dim(R, V)")
			cardinalityPower := a.Have(
				"the module count is the cardinality of k",
				"card(k.carrier) = p ^ module_dim(R, V)",
				By(Normalized, vectorCount, carrierData, cardinality.CardOfSized.At(vectorCarrier, power)))
			dimension := a.TermAs[Nat]("module_dim(R, V)")
			a.Take(dimension)
			a.Show(
				"this dimension is a positive exponent for the field size",
				By(positiveDimension, cardinalityPower))
		})
	}),
})}

// PrimePowerVanishes — a positive power of the prime characteristic exceeds
// one and annihilates one: it is the characteristic times a smaller power,
// and the characteristic annihilates one.
var PrimePowerVanishes = primePowerVanishesThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerVanishes",
	Key:  "prop_cde53bca6f3ccb8e",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p n:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(R, p)",
			"0 < n",
		},
		Conclusion: "1 < p ^ n ∧ monoid_pow(R.add, R.zero, R.one, p ^ n) = R.zero",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		p, n *Expr[Nat],
		characteristic, positive Fact,
	) {
		additive := comm_ring.AddMonoidOn.Read(R)
		j, predecessor := a.ObtainAs[Nat](
			"a positive exponent is a successor",
			"∃j:num. n = j + 1",
			ByArith(positive, nat_arith.NonzeroIsSucc.At(n)))
		multiple := a.Have(
			"the power is the characteristic times a smaller power",
			"p ^ n = p * p ^ j",
			By(Normalized, predecessor, nat_arith.Add1.At(j), nat_arith.NatPow))
		primeData := a.Have(
			"the characteristic is at least two and annihilates one",
			"2 ≤ p ∧ monoid_pow(R.add, R.zero, R.one, p) = R.zero",
			By(
				characteristic,
				PrimeCharacteristicDef.At(a.TermAs[RingOps[A]]("R"), p),
				nat_prime.PrimeAtLeastTwo.At(p)))
		smaller := a.TermAs[Nat]("p ^ j")
		a.Show(
			"the power exceeds one and annihilates one",
			SplitConj(
				Case(
					"the power exceeds one",
					ByArith(
						multiple,
						primeData,
						nat_order.PowPositive.At(p, j),
						nat_order.LessEqSelfMul.At(p, smaller))),
				Case(
					"a multiple of the characteristic annihilates one",
					By(
						comm_ring.OneIn.Read(R),
						multiple,
						primeData,
						comm_ring.AddPowMulOn.Read(R).AsFact().At(p, smaller),
						comm_monoid.PowIn.Read(additive).AsFact().At(a.TermAs[A]("R.one"), smaller),
						comm_ring.MulLeftZeroOn.Read(R).AsFact().At(
							a.TermAs[A]("monoid_pow(R.add, R.zero, R.one, p ^ j)"))))))
	}),
})}

// PrimeSizeCharacteristic — a field with a prime number p of elements has
// characteristic p: a finite field has a prime characteristic q and q^e
// elements for some e > 0, so p = q^e, and p copies of one vanish as q^e
// copies do; a prime that annihilates one is the characteristic.
var PrimeSizeCharacteristic = primeSizeCharacteristicThm{family.Add(registry.ProofEntry{
	Name: "PrimeSizeCharacteristic",
	Key:  "prop_31df3c4ce6e93fd",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"has_size(F.carrier, p)",
		},
		Conclusion: "field_characteristic(F, p)",
	}, func(a *Argument, F field.FieldFact[on.F], p *Expr[Nat], prime, size Fact) {
		count := a.Have(
			"the carrier is finite with p elements",
			"finite(F.carrier) ∧ card(F.carrier) = p",
			By(size, cardinality.HasSizeDef))
		q, qCharacteristic := a.ObtainAs[Nat](
			"a finite field has a prime characteristic q",
			"∃q:num. ring_prime_characteristic(field_ring(F), q)",
			By(count, FiniteFieldCharacteristic.Read(F)))
		e, power := a.ObtainAs[Nat](
			"its size p is a positive power of q",
			"∃e:num. 0 < e ∧ p = q ^ e",
			By(Normalized, count, qCharacteristic, FiniteFieldSizePower.Read(F).At(q)))
		vanishes := a.Have(
			"p copies of one vanish, as q^e copies do",
			"monoid_pow(F.add, F.zero, F.one, p) = F.zero",
			By(Normalized, qCharacteristic, power, PrimePowerVanishes.Read(field.RingOn.Read(F)).At(q, e)))
		a.Show(
			"a prime, which is positive, annihilating one is the characteristic",
			ByArith(
				prime,
				vanishes,
				PrimeCharacteristicDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(F)"), p),
				nat_prime.PrimeAtLeastTwo.At(p),
				FieldCharacteristicDef.At(a.TermAs[FieldOps[A]]("F"), p)))
	}),
})}

// IntegerMapOnto — in a field with a prime number p of elements every element
// is the image of an integer: the multiples of one form the prime subfield,
// which has p elements, as many as the whole finite carrier, so it is the
// carrier, and n copies of one are the image of the integer n.
var IntegerMapOnto = integerMapOntoThm{family.Add(registry.ProofEntry{
	Name: "IntegerMapOnto",
	Key:  "prop_65b39366513ba43b",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀z:A.",
		Hypotheses: []string{
			"nat_prime(p)",
			"has_size(F.carrier, p)",
			"z ∈ F.carrier",
		},
		Conclusion: "∃a:int. integer_map(field_ring(F), a) = z",
		Abbrev: Abbrev{
			{Name: "numerals", Text: "{monoid_pow(F.add, F.zero, F.one, n) | n:num | ⊤}"},
		},
	}, func(a *Argument, F field.FieldFact[on.F], p *Expr[Nat], prime, size Fact, z *Member[A, on.F]) {
		ring := field.RingOn.Read(F)
		pCharacteristic := a.Have(
			"the field's characteristic p is a positive prime, so it is the prime characteristic of its ring",
			"ring_prime_characteristic(field_ring(F), p)",
			ByArith(
				prime,
				size,
				PrimeSizeCharacteristic.Read(F).At(p),
				FieldCharacteristicDef.At(a.TermAs[FieldOps[A]]("F"), p),
				nat_prime.PrimeAtLeastTwo.At(p)))
		numerals := a.Have(
			"the multiples of one form a subfield with p elements",
			"subfield(F, «numerals») ∧ has_size(«numerals», p)",
			By(size, pCharacteristic, cardinality.HasSizeDef, PrimeSubfield.Read(F).At(p)))
		fill := a.Have(
			"a subset with as many elements as the finite carrier is all of it",
			"«numerals» = F.carrier",
			By(size, numerals, cardinality.CardSubsetEq, field.SubfieldSubset, cardinality.HasSizeDef))
		numeral := a.Have(
			"so z is a multiple of one",
			"z ∈ «numerals»",
			By(Normalized, fill, z))
		n, copies := a.UnpackAs[Nat](numeral, "n")
		a.Take(a.TermAs[Int]("n"))
		a.Show(
			"the integer n maps to n copies of one, which is z",
			By(Normalized, copies, characteristic_zero.IntegerMapOfNum.Read(ring).At(n)))
	}),
})}

// FiniteFieldLagrange — a nonzero element raised to the number of nonzero
// elements is one: multiplication by it permutes the nonzero elements, so
// their product equals the product of their multiples, which is that power
// times the product itself, and the product, being nonzero, cancels.
var FiniteFieldLagrange = finiteFieldLagrangeThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldLagrange",
	Key:  "prop_e62d3dd34ff6abe4",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀z:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"z ∈ k.carrier",
			"z ≠ k.zero",
		},
		Conclusion: "monoid_pow(k.mul, k.one, z, card(k.carrier) - 1) = k.one",
	}, func(a *Argument, k Fact, z *Expr[A], given Fact) {
		ring := field.RingOn.Read(k)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		carrier, zero := a.TermAs[Set[A]]("k.carrier"), a.TermAs[A]("k.zero")
		scaling := a.TermAs[Fun[A, A]]("k.mul(z)")
		N, nonzeroDef := a.LetAs[Set[A]]("N", "delete(k.carrier, k.zero)")
		nonzeroMonoid := a.Have(
			"the nonzero elements are a commutative monoid under "+
				"multiplication: one is nonzero, and a field has no zero divisors",
			"comm_monoid_on(N, k.mul, k.one)",
			Unfold(comm_monoid.CommMonoidOn),
			nonzeroDef.Rw(),
			Simp(Fwd(set_basic.InDelete)),
			By(
				field.OneNotZeroOn.Read(k),
				field.MulEqZeroOn.Read(k),
				comm_monoid.IdentityIn.Read(multiplicative),
				comm_monoid.OpIn.Read(multiplicative),
				comm_monoid.CommOn.Read(multiplicative),
				comm_monoid.AssocOn.Read(multiplicative),
				comm_monoid.LeftIdentityOn.Read(multiplicative)))
		count := a.Have(
			"N is finite, holds z, and has one element fewer than the carrier, which holds zero",
			"finite(N) ∧ card(N) = card(k.carrier) - 1 ∧ z ∈ N",
			By(
				Normalized,
				nonzeroDef,
				given,
				comm_ring.ZeroIn.Read(ring),
				finite_set.FiniteDeleteImp.At(carrier, zero),
				cardinality.CardDelete.At(carrier, zero),
				set_basic.InDelete.At(carrier, z, zero)))
		bijective := field.MulBijective.Read(k).AsFact().At(z)
		permutes := a.Have(
			"multiplication by z maps N onto N: it maps the carrier one-to-one onto itself, and keeps zero",
			"image(k.mul(z), N) = N",
			By(
				nonzeroDef,
				given,
				bijective,
				field.MulEqZeroOn.Read(k),
				comm_ring.MulRightZeroOn.Read(ring).AsFact().At(z),
				set_image.ImageDeleteInj.At(scaling, carrier, zero)))
		inCarrier := a.Have(
			"N lies in the carrier",
			"N ⊆ k.carrier",
			nonzeroDef.Rw(),
			By(set_order.DeleteSubset.At(carrier, zero)))
		oneToOne := a.Have(
			"multiplication by the nonzero z cancels on the carrier, so in particular on N",
			"injective_on(N, k.mul(z))",
			By(given, bijective, inCarrier, functions.InjectiveOnSubset.At(scaling, N, carrier)))
		P, productDef := a.LetAs[A]("P", "module_sum(k.mul, k.one, N, λx:A. x)")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		productIn := a.Have(
			"P, a product of members of the monoid N, lies in N",
			"P ∈ N",
			By(
				Normalized,
				productDef,
				count,
				module.ModuleSumInMonoid.Read(nonzeroMonoid).AsFact().At(N, identity)))
		power := a.TermAs[A]("monoid_pow(k.mul, k.one, z, card(N))")
		scaled := a.Have(
			"P is also the product of the multiples z * x, which is z once for each factor, times P",
			"P = monoid_pow(k.mul, k.one, z, card(N)) * P",
			CalcEq(
				Leg(
					a.TermAs[A]("module_sum(k.mul, k.one, image(k.mul(z), N), λx:A. x)"),
					"multiplication by z maps N onto N",
					By(Normalized, productDef, permutes)),
				Leg(
					a.TermAs[A]("module_sum(k.mul, k.one, N, λx:A. z * x)"),
					"and is one-to-one there, so the product over the image is the product of the multiples",
					By(
						count,
						oneToOne,
						comm_monoid.OpIn.Read(nonzeroMonoid),
						module.ModuleSumImageMonoid.Read(nonzeroMonoid).AsFact().At(N, scaling, identity))),
				Leg(
					a.TermAs[A]("module_sum(k.mul, k.one, N, λx:A. z) * P"),
					"the product of the multiples splits into the product of the constant z and P",
					By(
						productDef,
						count,
						module.ModuleSumAddMonoid.Read(nonzeroMonoid).AsFact().At(
							N, a.TermAs[Fun[A, A]]("λx:A. z"), identity))),
				FinalLeg(
					"and the product of the constant z is its power",
					By(count, module.ModuleSumConstantMonoid.Read(nonzeroMonoid).AsFact().At(N, z))),
			))
		nonzero := a.Have(
			"so P is a nonzero element",
			"P ∈ k.carrier ∧ P ≠ k.zero",
			By(Normalized, nonzeroDef, productIn, set_basic.InDelete.At(carrier, P, zero)))
		one := a.TermAs[A]("k.one")
		a.Show(
			"canceling the nonzero P leaves the power one, and card(N) is card(k.carrier) - 1",
			By(
				scaled,
				given,
				nonzero,
				count,
				integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(k)).AsFact().At(
					P, power, one),
				comm_monoid.CommOn.Read(multiplicative).AsFact().At(P, power),
				comm_monoid.RightIdentityOn.Read(multiplicative).AsFact().At(P),
				comm_monoid.PowIn.Read(multiplicative).AsFact().At(z, a.TermAs[Nat]("card(N)")),
				comm_monoid.IdentityIn.Read(multiplicative)))
	}),
})}

// FiniteFieldFixedByFrobenius — every element of a finite field is fixed
// by raising it to the size of the field: zero is immediate, and a
// nonzero element satisfies Lagrange's power identity.
var FiniteFieldFixedByFrobenius = finiteFieldFixedByFrobeniusThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldFixedByFrobenius",
	Key:  "prop_affa82ec5ef9668c",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀z:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"z ∈ k.carrier",
		},
		Conclusion: "monoid_pow(k.mul, k.one, z, card(k.carrier)) = z",
	}, func(a *Argument, k Fact, z *Expr[A], h Fact) {
		carrier := a.TermAs[Set[A]]("k.carrier")
		predecessor := a.TermAs[Nat]("card(k.carrier) - 1")
		ring := field.RingOn.Read(k)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		nonempty := a.Have(
			"the carrier contains z and has nonzero size",
			"card(k.carrier) ≠ 0",
			BySets(h, cardinality.CardEqZero.At(carrier)))
		successor := a.Have(
			"a nonzero size is the successor of its predecessor",
			"card(k.carrier) = suc(card(k.carrier) - 1)",
			ByArith(nonempty))
		powerStep := a.Have(
			"separate one factor from the positive power",
			"monoid_pow(k.mul, k.one, z, card(k.carrier)) = "+
				"z * monoid_pow(k.mul, k.one, z, card(k.carrier) - 1)",
			By(successor, comm_monoid.MonoidPowDef))
		a.Cases(a.Term("z = k.zero"))
		a.When(
			"zero times a carrier element is zero",
			func(b *Argument, isZero Fact) {
				previousPower := b.TermAs[A]("monoid_pow(k.mul, k.one, z, card(k.carrier) - 1)")
				b.Show(
					"the positive power of zero is zero",
					By(
						isZero,
						powerStep,
						h,
						comm_monoid.PowIn.Read(multiplicative).AsFact().At(z, predecessor),
						comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(previousPower)))
			})
		a.Otherwise(
			"a nonzero element has predecessor power one",
			func(b *Argument, notZero Fact) {
				b.Show(
					"Lagrange's identity leaves the original element",
					By(
						notZero,
						powerStep,
						h,
						FiniteFieldLagrange.Read(k).AsFact().At(z),
						comm_monoid.RightIdentityOn.Read(multiplicative).AsFact().At(z)))
			})
	}),
})}

// FiniteSubfieldPrimePower — a finite subfield has a prime power of elements,
// the prime being the characteristic of the ambient field: the subfield is a
// finite field, and it shares its zero, one and addition with M.
var FiniteSubfieldPrimePower = finiteSubfieldPrimePowerThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldPrimePower",
	Key:  "prop_424b8106943f3125",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
		},
		Conclusion: "∃p n:num. " +
			"    ring_prime_characteristic(field_ring(M), p) ∧ 0 < n ∧ card(k) = p ^ n ∧ 2 ≤ card(k)",
	},
		func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], subK, finiteK Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
			restricted := a.Have(
				"k is a finite field on its own carrier",
				"field_on(restrict_field(M, k)) ∧ finite(restrict_field(M, k).carrier)",
				By(M, subK, finiteK, field.SubfieldSubset.At(m, k), field.SubfieldFieldOn.At(m, k)))
			p, characteristicK := a.ObtainAs[Nat](
				"it has a prime characteristic",
				"∃p:num. ring_prime_characteristic(field_ring(restrict_field(M, k)), p)",
				By(restricted, FiniteFieldCharacteristic.At(fieldK)))
			n, size := a.ObtainAs[Nat](
				"so its size is a positive power of that prime",
				"∃n:num. 0 < n ∧ card(k) = p ^ n",
				By(characteristicK, restricted, FiniteFieldSizePower.At(fieldK, p)))
			characteristic := a.Have(
				"the characteristic is that of M, whose zero, one and addition k shares",
				"ring_prime_characteristic(field_ring(M), p)",
				By(Normalized, characteristicK, PrimeCharacteristicDef))
			sizeParts := a.Conjuncts(
				size,
				"the exponent is positive",
				"k has p^n elements")
			large := a.Have(
				"a positive power of a prime exceeds one",
				"1 < p ^ n",
				By(
					characteristic,
					sizeParts[0],
					field.RingOn.Read(M),
					PrimePowerVanishes.Read(field.RingOn.Read(M)).At(p, n)))
			a.Take(p)
			a.Take(n)
			a.Show(
				"p is the characteristic of M, and k has p^n elements, n positive, at least two",
				ByArith(characteristic, sizeParts[0], sizeParts[1], large))
		}),
})}

// SubfieldFrobeniusPoints — a point of M is fixed by the q-power exactly when it
// lies in the finite subfield k with q elements: k is fixed, by Fermat in k
// (FiniteFieldFixedByFrobenius), and the q-power has at most q fixed
// points in a field (FiniteConstantsBound).
var SubfieldFrobeniusPoints = subfieldFrobeniusPointsThm{family.Add(registry.ProofEntry{
	Name: "SubfieldFrobeniusPoints",
	Key:  "prop_e80026921e844e9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"x ∈ M.carrier",
		},
		Conclusion: "monoid_pow(M.mul, M.one, x, card(k)) = x ⇔ x ∈ k",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			x *Expr[A],
			subK, finiteK, inCarrier Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
			q := a.TermAs[Nat]("card(k)")
			one := a.TermAs[Nat]("1")
			points := a.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), 1)")
			kInCarrier := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subK, field.SubfieldSubset.At(m, k)))
			restricted := a.Have(
				"k is a finite field on its own carrier",
				"field_on(restrict_field(M, k)) ∧ finite(restrict_field(M, k).carrier)",
				By(M, subK, finiteK, kInCarrier, field.SubfieldFieldOn.At(m, k)))
			_, _, atLeastTwo := a.Obtain2As[Nat, Nat](
				"k has at least two elements",
				"∃c n:num. ring_prime_characteristic(field_ring(M), c) ∧ 0 < n ∧ card(k) = c ^ n ∧ 2 ≤ card(k)",
				By(M, subK, finiteK, At(FiniteSubfieldPrimePower, m, k)))
			fixed := a.Have(
				"every point of k is fixed by the q-power",
				"k ⊆ finite_constants(field_ring(M), card(k), 1)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(FiniteConstantsDef), Fwd(nat_arith.PowOne), Fwd(set_basic.SubsetDef)))
					y := b.FixAs[A]("y")
					inK := b.Assume()
					b.Show(
						"the q-th power of a point of a field with q elements is that point",
						BySets(Normalized, restricted, inK, kInCarrier, FiniteFieldFixedByFrobenius.At(fieldK, y)))
				}))
			large := a.Have(
				"the exponent q^1 exceeds one",
				"1 < card(k) ^ 1",
				ByArith(atLeastTwo, nat_arith.PowOne.At(q)))
			bound := a.Have(
				"the q-power has at most q fixed points",
				"finite(finite_constants(field_ring(M), card(k), 1)) ∧ "+
					"card(finite_constants(field_ring(M), card(k), 1)) ≤ card(k) ^ 1",
				By(large, FiniteConstantsBound.Read(M).At(q, one)))
			count := a.Have(
				"so k has as many points as there are fixed points",
				"card(k) = card(finite_constants(field_ring(M), card(k), 1))",
				ByArith(
					fixed,
					bound,
					nat_arith.PowOne.At(q),
					cardinality.BoundedCountOfSubset.At(
						k, points, a.TermAs[Nat]("card(finite_constants(field_ring(M), card(k), 1))"))))
			equal := a.Have(
				"so k is all of them",
				"k = finite_constants(field_ring(M), card(k), 1)",
				By(fixed, bound, count, cardinality.CardSubsetEq.At(k, points)))
			pointIff := a.Have(
				"a point of M is a fixed point exactly when x^q = x",
				"x ∈ finite_constants(field_ring(M), card(k), 1) ⇔ monoid_pow(M.mul, M.one, x, card(k)) = x",
				Simp(Fwd(FiniteConstantsDef), Fwd(nat_arith.PowOne), Fwd(field.FieldRingDef)),
				BySets(inCarrier))
			a.Show(
				"k is the set of those points",
				BySets(equal, pointIff))
		}),
})}

// FrobeniusFixedField — a finite subfield k of L, of q elements, is the set
// of points of L that the q-th power fixes: k lies in L, and a point of L is
// fixed exactly when it lies in k (SubfieldFrobeniusPoints).
var FrobeniusFixedField = frobeniusFixedFieldThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusFixedField",
	Key:  "prop_d81fadaa0fe1e832",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"finite(k)",
		},
		Conclusion: "{z:A | z ∈ L.carrier ∧ monoid_pow(L.mul, L.one, z, card(k)) = z} = k",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], subK, finiteK Fact) {
			fieldL := a.TermAs[FieldOps[A]]("L")
			a.Show(
				"k lies in L, and a point of L is fixed by the q-th power exactly when it lies in k",
				BySets(subK, finiteK, field.SubfieldSubset.At(fieldL, k), SubfieldFrobeniusPoints.Read(L).AsFact()))
		}),
})}

// FrobeniusConstantAutomorphism — on a finite extension l of a finite subfield
// k with q elements, c ↦ c^q is an automorphism over k: the q-power is a ring
// endomorphism of M, since q is a power of the characteristic; it fixes k
// (SubfieldFrobeniusPoints) and keeps the subfield l, which holds the powers
// of its members.
var FrobeniusConstantAutomorphism = frobeniusConstantAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusConstantAutomorphism",
	Key:  "prop_2bb67c06d0936de9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "∃p:permutation(A). " +
			"    p ∈ field_automorphisms(M, k, l) ∧ " +
			"    (∀c:A. c ∈ l ⇒ permutation_map(p, c) = monoid_pow(M.mul, M.one, c, card(k)))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			subK, finiteK, subL, kInL, finiteL Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			ring := field.RingOn.Read(M)
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), card(k))")
			c, n, data := a.Obtain2As[Nat, Nat](
				"q is a power of the characteristic",
				"∃c n:num. ring_prime_characteristic(field_ring(M), c) ∧ 0 < n ∧ card(k) = c ^ n ∧ 2 ≤ card(k)",
				By(M, subK, finiteK, At(FiniteSubfieldPrimePower, m, k)))
			homomorphism := a.Have(
				"the q-power is a ring endomorphism of M",
				"ring_homomorphism(field_ring(M), field_ring(M), frobenius_power(field_ring(M), card(k)))",
				By(Normalized, data, ring, FrobeniusRingHomomorphism.Read(ring).At(c, n)))
			lInCarrier := a.Have(
				"l lies in M",
				"l ⊆ M.carrier",
				By(subL, field.SubfieldSubset.At(m, l)))
			spelled := a.Have(
				"the q-power is multiplication q times",
				"∀x:A. frobenius_power(field_ring(M), card(k), x) = monoid_pow(M.mul, M.one, x, card(k))",
				Simp(Fwd(FrobeniusPowerDef), Fwd(field.FieldRingDef)),
				Basic())
			sums := a.Have(
				"it keeps sums on l",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ l",
						"y ∈ l",
					},
					Conclusion: "frobenius_power(field_ring(M), card(k), x + y) = " +
						"frobenius_power(field_ring(M), card(k), x) + frobenius_power(field_ring(M), card(k), y)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					members := b.Assume()
					b.Show(
						"(x + y)^q = x^q + y^q",
						BySets(members, lInCarrier, ring_homomorphism.MapAdd.Read(homomorphism).AsFact().At(x, y)))
				}))
			products := a.Have(
				"it keeps products on l",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ l",
						"y ∈ l",
					},
					Conclusion: "frobenius_power(field_ring(M), card(k), x * y) = " +
						"frobenius_power(field_ring(M), card(k), x) * frobenius_power(field_ring(M), card(k), y)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					members := b.Assume()
					b.Show(
						"(x y)^q = x^q y^q",
						BySets(members, lInCarrier, ring_homomorphism.MapMul.Read(homomorphism).AsFact().At(x, y)))
				}))
			kInCarrier := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subK, field.SubfieldSubset.At(m, k)))
			fixesK := a.Have(
				"it fixes k",
				"∀x:A. x ∈ k ⇒ frobenius_power(field_ring(M), card(k), x) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					inside := b.Have(
						"x lies in M",
						"x ∈ M.carrier",
						BySets(member, kInCarrier))
					b.Show(
						"a point of k is fixed by the q-power",
						By(member, inside, subK, finiteK, spelled, Read(SubfieldFrobeniusPoints, M).At(k, x)))
				}))
			into := a.Have(
				"it keeps l",
				"∀x:A. x ∈ l ⇒ frobenius_power(field_ring(M), card(k), x) ∈ l",
				BySets(subL, spelled, field.SubfieldPowerIn.Read(M).AsFact()))
			u, automorphism := a.ObtainAs[symmetric_group.Permutation[A]](
				"so it comes from an automorphism of l over k",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, k, l) ∧ "+
					"    (∀x:A. x ∈ l ⇒ permutation_map(u, x) = frobenius_power(field_ring(M), card(k), x))",
				By(
					M,
					subK,
					subL,
					kInL,
					finiteL,
					sums,
					products,
					ring_homomorphism.MapOne.Read(homomorphism),
					fixesK,
					into,
					At(field_automorphism.FiniteSubfieldAutomorphism, m, k, l, power)))
			a.Take(u)
			a.Show(
				"which is the q-power on l",
				By(automorphism, spelled))
		}),
})}
