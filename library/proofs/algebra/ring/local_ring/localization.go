// localization.go — units and locality in an abstract localization at a prime ideal.

package local_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeComplementMultiplicative — the complement of a prime ideal in c
// is a multiplicative set: one lies outside p since p is proper, and a
// product of two members of c outside p lies outside p since p is prime.
var PrimeComplementMultiplicative = primeComplementMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "PrimeComplementMultiplicative",
	Key:  "prop_28d49067bf460190",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:set(A).",
		Hypotheses: []string{
			"prime_ideal(R, p)",
		},
		Conclusion: "multiplicative_set(R.carrier, R.carrier ∖ p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Expr[Set[A]], prime Fact) {
			a.Do(Unfold(ring_localization.MultiplicativeSetDef), SplitConjAll(
				Case(
					"c ∖ p lies in c",
					BySets()),
				Case(
					"one lies in c, and not in p, which is proper",
					BySets(comm_ring.OneIn.Read(ring), ring_ideal.PrimeIdealProper.Read(prime))),
				Case(
					"c ∖ p is closed under the product",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						outside := b.Assume()
						members := b.Have(
							"u and v lie in c and not in p",
							"u ∈ R.carrier ∧ u ∉ p ∧ v ∈ R.carrier ∧ v ∉ p",
							BySets(outside))
						notIn := b.Have(
							"p is prime and holds neither factor, so it does not hold u * v",
							"u * v ∉ p",
							By(members, At(ring_ideal.PrimeIdealPrime.Read(prime), u, v)))
						b.Show(
							"and u * v lies in c, which is closed under the product",
							BySets(comm_ring.MulIn.Read(ring), notIn, members))
					})),
			))
		}),
})}

// LocalizationAtPrimeUnit — an inverse supplies a fraction whose cross
// products agree after multiplication by a denominator. Primeness then
// excludes the numerator from p; outside p its image already has an inverse.
var LocalizationAtPrimeUnit = localizationAtPrimeUnitThm{family.Add(registry.ProofEntry{
	Name: "LocalizationAtPrimeUnit",
	Key:  "prop_bd78eeb7c783cb40",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀L:ring_ops(B). ∀p:set(A). ∀ι:(A → B). ∀a s:A. ∀y:B.",
		Hypotheses: []string{
			"is_localization_on(R, R.carrier ∖ p, L, ι)",
			"prime_ideal(R, p)",
			"a ∈ R.carrier",
			"s ∈ R.carrier ∖ p",
			"y ∈ L.carrier",
			"L.mul(y, ι(s)) = ι(a)",
		},
		Conclusion: "ring_unit(L, y) ⇔ a ∉ p",
	},
		func(
			arg *Argument,
			R *Expr[module_record.RingOps[A]],
			L *Expr[module_record.RingOps[B]],
			p *Expr[Set[A]],
			ι *Arrow[A, B],
			a, s *Expr[A],
			y *Expr[B],
			hypotheses Fact,
		) {
			arg.Do(Unfold(ring_localization.IsLocalizationOnDef))
			hom := arg.Hyp("ring_homomorphism(R, L, ι)")
			prime := arg.Hyp("prime_ideal(R, p)")
			aIn := arg.Hyp("a ∈ R.carrier")
			sIn := arg.Hyp("s ∈ R.carrier ∖ p")
			yIn := arg.Hyp("y ∈ L.carrier")
			fraction := arg.Hyp("L.mul(y, ι(s)) = ι(a)")
			denominators := arg.Hyp("∀s:A. s ∈ R.carrier ∖ p ⇒ ring_unit(L, ι(s))")
			representations := arg.Hyp(Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ L.carrier",
				},
				Conclusion: "∃a s:A. a ∈ R.carrier ∧ s ∈ R.carrier ∖ p ∧ L.mul(y, ι(s)) = ι(a)",
			})
			kernel := arg.Hyp(Statement{
				Binders: "∀a:A.",
				Hypotheses: []string{
					"a ∈ R.carrier",
					"ι(a) = L.zero",
				},
				Conclusion: "∃s:A. s ∈ R.carrier ∖ p ∧ R.mul(s, a) = R.zero",
			})
			source := arg.Have(
				"the source is a commutative ring",
				"comm_ring_on(R)",
				By(ring_homomorphism.Source.Read(hom)))
			target := arg.Have(
				"the target is a commutative ring",
				"comm_ring_on(L)",
				By(ring_homomorphism.Target.Read(hom)))
			sOutside := arg.Have(
				"s lies in the source and outside p",
				"s ∈ R.carrier ∧ s ∉ p",
				BySets(sIn))
			images := arg.Have(
				"the numerator and denominator images lie in the target",
				"ι(a) ∈ L.carrier ∧ ι(s) ∈ L.carrier",
				By(ring_homomorphism.MapIn.Read(hom), aIn, sOutside))
			arg.Iff()
			arg.Backward(
				"a numerator outside p supplies an inverse",
				func(q *Argument, aOutside Fact) {
					aDenominator := q.Have(
						"a is an allowed denominator",
						"a ∈ R.carrier ∖ p",
						BySets(aOutside, aIn))
					aUnit := q.Have(
						"the image of a is a unit",
						"ring_unit(L, ι(a))",
						By(aDenominator, denominators.At(a)))
					v, inverse := q.ObtainAs[B](
						"take an inverse of the image of a",
						"∃v:B. v ∈ L.carrier ∧ L.mul(ι(a), v) = L.one",
						By(aUnit, ring_ideal.RingUnitDef))
					inverts := q.Have(
						"multiplying v by the denominator image inverts y",
						"L.mul(y, L.mul(ι(s), v)) = L.one",
						ByArith(target, yIn, inverse, images, Scaled(v, fraction)))
					inverseIn := q.Have(
						"this inverse lies in the target",
						"L.mul(ι(s), v) ∈ L.carrier",
						By(comm_ring.MulIn.Read(target), inverse, images))
					q.Show(
						"the displayed product witnesses that y is a unit",
						Unfold(ring_ideal.RingUnitDef),
						SplitConj(
							Case(
								"y lies in the target",
								By(yIn)),
							Case(
								"and the displayed product is an inverse of it",
								Witness(q.TermAs[B]("L.mul(ι(s), v)")),
								By(inverseIn, inverts)),
						))
				})
			arg.Forward(
				"an inverse forces the numerator outside p",
				func(q *Argument, unit Fact) {
					v, inverse := q.ObtainAs[B](
						"take an inverse of y",
						"∃v:B. v ∈ L.carrier ∧ L.mul(y, v) = L.one",
						By(unit, ring_ideal.RingUnitDef))
					b, t, represented := q.Obtain2As[A, A](
						"represent the inverse as b over t",
						"∃b t:A. b ∈ R.carrier ∧ t ∈ R.carrier ∖ p ∧ L.mul(v, ι(t)) = ι(b)",
						By(inverse, representations.At(v)))
					members := q.Have(
						"b and t lie in the source, and t lies outside p",
						"b ∈ R.carrier ∧ t ∈ R.carrier ∧ t ∉ p",
						BySets(represented))
					inverseImages := q.Have(
						"their images lie in the target",
						"ι(b) ∈ L.carrier ∧ ι(t) ∈ L.carrier",
						By(ring_homomorphism.MapIn.Read(hom), members))
					cleared := q.Have(
						"multiplying the inverse representation by y clears v",
						"L.mul(y, ι(b)) = ι(t)",
						Derive(func(r *Argument) {
							unitProduct := r.Have(
								"y times v is one",
								"L.mul(y, v) = L.one",
								By(inverse))
							inverseFraction := r.Have(
								"v times the denominator image is the numerator image",
								"L.mul(v, ι(t)) = ι(b)",
								By(represented))
							r.Show(
								"the inverse cancels after multiplication by y",
								ByArith(
									target,
									yIn,
									inverseImages,
									inverse,
									Scaled(ι.Apply(t), unitProduct),
									Scaled(y, inverseFraction)))
						}))
					crossProducts := q.Have(
						"the two fraction equations give equal cross products",
						"L.mul(ι(a), ι(b)) = L.mul(ι(s), ι(t))",
						ByArith(
							target,
							yIn,
							inverseImages,
							images,
							Scaled(ι.Apply(b), fraction),
							Scaled(ι.Apply(s), cleared)))
					mappedProducts := q.Have(
						"the map preserves these cross products",
						"ι(R.mul(a, b)) = ι(R.mul(s, t))",
						By(
							Normalized,
							aIn,
							sOutside,
							members,
							crossProducts,
							At(ring_homomorphism.MapMul.Read(hom), a, b),
							At(ring_homomorphism.MapMul.Read(hom), s, t)))
					productsIn := q.Have(
						"both cross products lie in the source",
						"R.mul(a, b) ∈ R.carrier ∧ R.mul(s, t) ∈ R.carrier",
						By(comm_ring.MulIn.Read(source), aIn, sOutside, members))
					d, difference := q.LetAs[A]("d", "R.sub(R.mul(a, b), R.mul(s, t))")
					dIn := q.Have(
						"their difference lies in the source",
						"d ∈ R.carrier",
						By(Normalized, comm_ring.SubIn.Read(source), difference, productsIn))
					differenceSum := q.Have(
						"adding the denominator product recovers the numerator product",
						"R.add(d, R.mul(s, t)) = R.mul(a, b)",
						ByArith(difference, dIn, aIn, sOutside, members, source))
					mappedMembers := q.Have(
						"the difference and both product images lie in the target",
						"ι(d) ∈ L.carrier ∧ ι(R.mul(a, b)) ∈ L.carrier ∧ ι(R.mul(s, t)) ∈ L.carrier",
						By(ring_homomorphism.MapIn.Read(hom), dIn, productsIn))
					mappedSum := q.Have(
						"the map preserves the displayed sum",
						"L.add(ι(d), ι(R.mul(s, t))) = ι(R.mul(a, b))",
						By(
							dIn,
							productsIn,
							differenceSum,
							At(ring_homomorphism.MapAdd.Read(hom), d, q.TermAs[A]("R.mul(s, t)"))))
					killed := q.Have(
						"the difference maps to zero",
						"ι(d) = L.zero",
						ByArith(target, mappedMembers, mappedSum, mappedProducts))
					u, annihilator := q.ObtainAs[A](
						"a denominator annihilates the difference",
						"∃u:A. u ∈ R.carrier ∖ p ∧ R.mul(u, d) = R.zero",
						By(dIn, killed, kernel.At(d)))
					uOutside := q.Have(
						"u lies in the source and outside p",
						"u ∈ R.carrier ∧ u ∉ p",
						BySets(annihilator))
					stOutside := q.Have(
						"the product of s and t lies outside the prime",
						"R.mul(s, t) ∉ p",
						By(sOutside, members, At(ring_ideal.PrimeIdealPrime.Read(prime), s, t)))
					ustOutside := q.Have(
						"multiplication by u keeps this product outside the prime",
						"R.mul(u, R.mul(s, t)) ∉ p",
						By(
							uOutside,
							stOutside,
							productsIn,
							At(ring_ideal.PrimeIdealPrime.Read(prime), u, q.TermAs[A]("R.mul(s, t)"))))
					equalProducts := q.Have(
						"annihilating the difference equates a denominator product with a multiple of a",
						"R.mul(u, R.mul(s, t)) = R.mul(R.mul(u, b), a)",
						ByArith(source, aIn, sOutside, members, uOutside, dIn, annihilator, Scaled(u, difference)))
					ubIn := q.Have(
						"the multiplier of a lies in the source",
						"R.mul(u, b) ∈ R.carrier",
						By(comm_ring.MulIn.Read(source), uOutside, members))
					q.Show(
						"if a lay in p, ideal absorption would put the denominator product in p",
						By(
							ubIn,
							ustOutside,
							equalProducts,
							At(
								ring_ideal.IdealMul.Read(ring_ideal.PrimeIdealIdeal.Read(prime)), q.TermAs[A]("R.mul(u, b)"), a)))
				})
		}),
})}

// LocalizationAtPrimeLocal — the kernel condition keeps one distinct from
// zero, and adding fractions whose numerators lie in the prime again gives
// a numerator in the prime over an allowed denominator.
var LocalizationAtPrimeLocal = localizationAtPrimeLocalThm{family.Add(registry.ProofEntry{
	Name: "LocalizationAtPrimeLocal",
	Key:  "prop_39ff1cd9938ef185",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀L:ring_ops(B). ∀p:set(A). ∀ι:(A → B).",
		Hypotheses: []string{
			"is_localization_on(R, R.carrier ∖ p, L, ι)",
			"prime_ideal(R, p)",
		},
		Conclusion: "local_ring_on(L)",
	},
		func(
			arg *Argument,
			R *Expr[module_record.RingOps[A]],
			L *Expr[module_record.RingOps[B]],
			p *Expr[Set[A]],
			ι *Arrow[A, B],
			hypotheses Fact,
		) {
			hom := arg.Have(
				"the localization map is a ring homomorphism",
				"ring_homomorphism(R, L, ι)",
				Unfold(ring_localization.IsLocalizationOnDef))
			source := arg.Have(
				"the source is a commutative ring",
				"comm_ring_on(R)",
				By(ring_homomorphism.Source.Read(hom)))
			target := arg.Have(
				"the target is a commutative ring",
				"comm_ring_on(L)",
				By(ring_homomorphism.Target.Read(hom)))
			prime := arg.Have(
				"p is a prime ideal",
				"prime_ideal(R, p)",
				By(hypotheses))
			kernel := arg.Have(
				"each element of the kernel is annihilated by a denominator",
				"∀a:A. a ∈ R.carrier ∧ ι(a) = L.zero ⇒ ∃s:A. s ∈ R.carrier ∖ p ∧ R.mul(s, a) = R.zero",
				Unfold(ring_localization.IsLocalizationOnDef))
			representations := arg.Have(
				"each target element has a numerator and denominator",
				"∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ R.carrier ∖ p ∧ L.mul(y, ι(s)) = ι(a)",
				Unfold(ring_localization.IsLocalizationOnDef))
			distinct := arg.Have(
				"one is distinct from zero in the localization",
				"¬(L.one = L.zero)",
				Derive(func(q *Argument) {
					collapsed := q.SupposeNot()
					killed := q.Have(
						"the source one would map to zero",
						"ι(R.one) = L.zero",
						By(Normalized, ring_homomorphism.MapOne.Read(hom), collapsed))
					oneIn := q.Have(
						"the source one lies in its carrier",
						"R.one ∈ R.carrier",
						By(comm_ring.OneIn.Read(source)))
					_, annihilator := q.ObtainAs[A](
						"a denominator would annihilate one",
						"∃s:A. s ∈ R.carrier ∖ p ∧ R.mul(s, R.one) = R.zero",
						By(killed, oneIn, kernel.At(q.TermAs[A]("R.one"))))
					outside := q.Have(
						"this denominator lies in the source and outside p",
						"s ∈ R.carrier ∧ s ∉ p",
						BySets(annihilator))
					zero := q.Have(
						"annihilating one makes the denominator zero",
						"s = R.zero",
						ByArith(source, outside, annihilator))
					q.Show(
						"zero belongs to the prime, contradicting the choice of denominator",
						By(Normalized, outside, zero, ring_ideal.IdealZero.Read(ring_ideal.PrimeIdealIdeal.Read(prime))))
				}))
			nonunits := arg.Have(
				"a sum of two nonunits is a nonunit",
				Statement{
					Binders: "∀x y:B.",
					Hypotheses: []string{
						"x ∈ L.carrier",
						"y ∈ L.carrier",
						"¬ring_unit(L, x)",
						"¬ring_unit(L, y)",
					},
					Conclusion: "¬ring_unit(L, L.add(x, y))",
				},
				Derive(func(q *Argument) {
					x := q.FixAs[B]("x")
					y := q.FixAs[B]("y")
					nonunits := q.Assume()
					a, s, xRepresentation := q.Obtain2As[A, A](
						"represent the first nonunit",
						"∃a s:A. a ∈ R.carrier ∧ s ∈ R.carrier ∖ p ∧ L.mul(x, ι(s)) = ι(a)",
						By(nonunits, representations.At(x)))
					b, t, yRepresentation := q.Obtain2As[A, A](
						"represent the second nonunit",
						"∃b t:A. b ∈ R.carrier ∧ t ∈ R.carrier ∖ p ∧ L.mul(y, ι(t)) = ι(b)",
						By(nonunits, representations.At(y)))
					numerators := q.Have(
						"both numerators lie in the prime",
						"a ∈ p ∧ b ∈ p",
						By(
							hypotheses,
							xRepresentation,
							yRepresentation,
							nonunits,
							LocalizationAtPrimeUnit.At(R, L, p, ι, a, s, x),
							LocalizationAtPrimeUnit.At(R, L, p, ι, b, t, y)))
					members := q.Have(
						"the fraction data lie in the source, with denominators outside p",
						"a ∈ R.carrier ∧ b ∈ R.carrier ∧ s ∈ R.carrier ∧ t ∈ R.carrier ∧ s ∉ p ∧ t ∉ p",
						BySets(xRepresentation, yRepresentation))
					productOutside := q.Have(
						"the product of the denominators lies outside the prime",
						"R.mul(s, t) ∉ p",
						By(members, At(ring_ideal.PrimeIdealPrime.Read(prime), s, t)))
					denominator := q.Have(
						"the product is an allowed denominator",
						"R.mul(s, t) ∈ R.carrier ∖ p",
						BySets(members, productOutside, comm_ring.MulIn.Read(source)))
					numeratorInPrime := q.Have(
						"ideal absorption and addition put the sum numerator in p",
						"R.add(R.mul(t, a), R.mul(s, b)) ∈ p",
						By(
							numerators,
							members,
							ring_ideal.IdealAdd.Read(ring_ideal.PrimeIdealIdeal.Read(prime)),
							ring_ideal.IdealMul.Read(ring_ideal.PrimeIdealIdeal.Read(prime))))
					numeratorIn := q.Have(
						"the sum numerator lies in the source",
						"R.add(R.mul(t, a), R.mul(s, b)) ∈ R.carrier",
						By(members, comm_ring.AddIn.Read(source), comm_ring.MulIn.Read(source)))
					images := q.Have(
						"the numerator and denominator images lie in the target",
						"ι(a) ∈ L.carrier ∧ ι(b) ∈ L.carrier ∧ ι(s) ∈ L.carrier ∧ ι(t) ∈ L.carrier",
						By(members, ring_homomorphism.MapIn.Read(hom)))
					xEquation := q.Have(
						"the first denominator clears x",
						"L.mul(x, ι(s)) = ι(a)",
						By(xRepresentation))
					yEquation := q.Have(
						"the second denominator clears y",
						"L.mul(y, ι(t)) = ι(b)",
						By(yRepresentation))
					cleared := q.Have(
						"multiply each fraction equation by the other denominator and add",
						"L.mul(L.add(x, y), L.mul(ι(s), ι(t))) = L.add(L.mul(ι(t), ι(a)), L.mul(ι(s), ι(b)))",
						ByArith(target, nonunits, images, Scaled(ι.Apply(t), xEquation), Scaled(ι.Apply(s), yEquation)))
					sumFraction := q.Have(
						"the homomorphism identifies the sum numerator and product denominator",
						"L.mul(L.add(x, y), ι(R.mul(s, t))) = ι(R.add(R.mul(t, a), R.mul(s, b)))",
						Simp(
							Fwd(ring_homomorphism.MapAdd.Read(hom)),
							Fwd(ring_homomorphism.MapMul.Read(hom)),
							Fwd(comm_ring.MulIn.Read(source))),
						By(cleared))
					sumIn := q.Have(
						"the sum lies in the target",
						"L.add(x, y) ∈ L.carrier",
						By(nonunits, comm_ring.AddIn.Read(target)))
					q.Show(
						"the numerator in p makes the sum a nonunit",
						By(
							hypotheses,
							numeratorInPrime,
							numeratorIn,
							denominator,
							sumFraction,
							sumIn,
							LocalizationAtPrimeUnit.At(
								R,
								L,
								p,
								ι,
								q.TermAs[A]("R.add(R.mul(t, a), R.mul(s, b))"),
								q.TermAs[A]("R.mul(s, t)"),
								q.TermAs[B]("L.add(x, y)"))))
				}))
			arg.Show(
				"these are the defining properties of a local ring",
				Unfold(LocalRingOn),
				By(target, distinct, nonunits))
		}),
})}
