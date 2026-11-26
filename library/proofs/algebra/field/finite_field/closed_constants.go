// closed_constants.go — the finite fields inside an algebraically closed
// field: above a finite subfield of q elements, the points fixed by the
// q^m-th power form the subfield of q^m elements, which holds every subfield
// of q^m elements; these fields grow along divisibility of the exponent,
// their points are algebraic over every subfield, and an element of degree
// at most D over k lies in the field of q^s elements once every positive
// m ≤ D divides s. A closed field is itself infinite: were it finite, with q
// elements, the subfield of q² elements above it would be the field itself.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteConstantsSubfield — inside an algebraically closed field, above
// a finite subfield k, the points fixed by the card(k)^m-th power, m > 0,
// form a subfield holding k with card(k)^m points: Q = card(k)^m is a
// positive power of the characteristic, so the Q-power is a ring
// endomorphism (FiniteSubfieldPowerEndomorphism) whose fixed points form a
// subfield; k is fixed by the q-power, q = card(k)
// (FiniteFieldFixedByFrobenius), hence by the Q-power (FiniteConstantsMono,
// as 1 ∣ m); and the fixed points are the roots of X^Q − X, separable with
// derivative −1, which splits in the closed field into Q distinct roots.
var FiniteConstantsSubfield = finiteConstantsSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsSubfield",
	Key:  "prop_3def19bafd1c306d",
	Reading: "m > 0 is load-bearing: at m = 0 the power is the first and the set is all " +
		"of M. No characteristic is stated: finite(k) makes card(k) a positive power of " +
		"M's, and q ≥ 2 holds of every subfield, its zero and one being distinct. The " +
		"algebraically closed field carries no field axiom of its own; field_on(M) supplies " +
		"them, inv(zero) = zero among them, which closes the set under inverse at zero. A " +
		"finite M is never closed, 1 + ∏(X − a) having no root, so k = M does not occur.",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"0 < m",
		},
		Conclusion: "subfield(M, finite_constants(field_ring(M), card(k), m)) ∧ " +
			"k ⊆ finite_constants(field_ring(M), card(k), m) ∧ " +
			"has_size(finite_constants(field_ring(M), card(k), m), card(k) ^ m)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		fixedField := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀q m:num.",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(M), field_ring(M), frobenius_power(field_ring(M), q ^ m))",
			},
			Conclusion: "subfield(M, finite_constants(field_ring(M), q, m))",
		}, func(a *Argument, M field.FieldFact[on.M], q, m *Expr[Nat], endomorphism Fact) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			ring := field.RingOn.Read(M)
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), q ^ m)")
			mapZero := a.Have(
				"the q^m-power fixes zero",
				"frobenius_power(field_ring(M), q ^ m, M.zero) = M.zero",
				By(ring_homomorphism.MapZero.Read(endomorphism)))
			mapInverse := a.Have(
				"the q^m-power commutes with field inverses",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ M.carrier"},
					Conclusion: "frobenius_power(field_ring(M), q ^ m, M.inv(x)) = " +
						"M.inv(frobenius_power(field_ring(M), q ^ m, x))",
				},
				By(
					ring_homomorphism.MapIn.Read(endomorphism),
					ring_homomorphism.MapOne.Read(endomorphism),
					ring_homomorphism.MapMul.Read(endomorphism),
					M,
					mapZero,
					field.MapInv.Read(M).AsFact().At(fieldM, power)))
			a.Do(Simp(Fwd(field.SubfieldDef), Fwd(FiniteConstantsDef), Rev(FrobeniusPowerDef)))
			y := a.FixAs[A]("y")
			z := a.FixAs[A]("z")
			a.Show(
				"the fixed points meet every condition of a subfield",
				SplitConj(
					Case(
						"the fixed set holds zero and one, lies in the carrier, "+
							"and is closed under inverses, negatives and sums",
						SplitConjAll(
							Case(
								"one is fixed",
								By(comm_ring.OneIn.Read(ring), ring_homomorphism.MapOne.Read(endomorphism))),
							Case(
								"zero is fixed",
								By(comm_ring.ZeroIn.Read(ring), mapZero)),
							Case(
								"every fixed point lies in the carrier",
								SetTacMembership()),
							Case(
								"inverses of fixed points are fixed",
								By(Normalized, mapInverse, M, field.InvIn.At(fieldM, y))),
							Case(
								"negatives of fixed points are fixed",
								By(
									comm_ring.NegIn.Read(ring).AsFact().At(y),
									ring_homomorphism.MapNeg.Read(endomorphism).AsFact().At(y))),
							Case(
								"sums of fixed points are fixed",
								By(
									comm_ring.AddIn.Read(ring).AsFact().At(z, y),
									ring_homomorphism.MapAdd.Read(endomorphism).AsFact().At(z, y))))),
					Case(
						"products of fixed points are fixed",
						By(
							comm_ring.MulIn.Read(ring).AsFact().At(z, y),
							ring_homomorphism.MapMul.Read(endomorphism).AsFact().At(z, y)))))
		})
		return ctx.Theorem(headline,
			func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], m *Expr[Nat], hypotheses Fact) {
				fieldM := a.TermAs[FieldOps[A]]("M")
				fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
				q := a.TermAs[Nat]("card(k)")
				Q := a.TermAs[Nat]("card(k) ^ m")
				H := a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(M, card(k) ^ m)")
				ring := field.RingOn.Read(M)

				restricted := a.Have(
					"the finite subfield is a field on its own carrier",
					"field_on(restrict_field(M, k)) ∧ finite(restrict_field(M, k).carrier)",
					By(M, hypotheses, field.SubfieldFieldOn.At(fieldM, k)))
				power := a.Conjuncts(
					GroupPremises(M, hypotheses, FiniteSubfieldPowerEndomorphism.At(fieldM, k, m)),
					"the Q-power is a ring endomorphism",
					"Q exceeds one",
					"and is zero in M")
				powerMap := power[0]
				fixedSubfield := a.Have(
					"the fixed points of the Q-power form a subfield",
					"subfield(M, finite_constants(field_ring(M), card(k), m))",
					By(M, powerMap, At(fixedField, fieldM, q, m)))
				fixedOnce := a.Have(
					"the finite subfield is fixed by the q-power",
					"k ⊆ finite_constants(field_ring(M), card(k), 1)",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(FiniteConstantsDef), Fwd(nat_arith.PowOne), Fwd(set_basic.SubsetDef)))
						x := b.FixAs[A]("x")
						inK := b.Assume()
						b.Show(
							"the finite field's Frobenius equation is the ambient equation",
							BySets(
								Normalized,
								restricted,
								inK,
								hypotheses,
								field.SubfieldSubset.At(fieldM, k),
								FiniteFieldFixedByFrobenius.At(fieldK, x)))
					}))
				inclusion := a.Have(
					"the finite subfield is fixed by the q^m-th power, since one divides m",
					"k ⊆ finite_constants(field_ring(M), card(k), m)",
					BySets(
						fixedOnce,
						nat_divides.OneDivides.At(m),
						FiniteConstantsMono.Read(ring).At(q, a.TermAs[Nat]("1"), m)))
				size := a.Have(
					"the fixed points are the Q roots of the separable split polynomial X^Q − X",
					"has_size(finite_constants(field_ring(M), card(k), m), card(k) ^ m)",
					Simp(Fwd(XPowerMinusXRoots)),
					By(
						M,
						hypotheses,
						power[1],
						power[2],
						XPowerMinusXOver.Read(field.RingOn.Read(M)).At(Q),
						XPowerMinusXDegree.At(fieldM, Q),
						XPowerMinusXSeparable.At(fieldM, Q),
						algebraic_closure.ClosedFieldSplits.At(fieldM, H),
						separable_polynomial.SeparableSplitsRoots.At(fieldM, H)))
				a.Show(
					"the fixed points contain k and have the required size",
					By(size, fixedSubfield, inclusion))
			})
	}),
})}

// ClosedFieldInfinite — an algebraically closed field is infinite. Were F
// finite, with q elements, q ≥ 2, it would be a finite subfield of itself, and
// a closed field holds, over a finite subfield of q elements, a subfield of q²
// elements containing it (FiniteConstantsSubfield). Lying in F and containing
// it, that subfield is F, so q = q², which no q ≥ 2 satisfies.
var ClosedFieldInfinite = closedFieldInfiniteThm{family.Add(registry.ProofEntry{
	Name: "ClosedFieldInfinite",
	Key:  "prop_471236445b7bc29e",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A).",
		Hypotheses: []string{
			"algebraically_closed_field(F)",
		},
		Conclusion: "infinite(F.carrier)",
		Abbrev: Abbrev{
			{Name: "quadraticExtension", Text: "finite_constants(field_ring(F), card(F.carrier), 2)"},
		},
	},
		func(a *Argument, F field.FieldFact[on.F], closed Fact) {
			fieldF := a.TermAs[FieldOps[A]]("F")
			carrier := a.TermAs[Set[A]]("F.carrier")
			size := a.TermAs[Nat]("card(F.carrier)")
			quadraticExtension := a.TermAs[Set[A]]("«quadraticExtension»")
			notInfinite := a.SupposeNot()
			finite := a.Have(
				"suppose F finite",
				"finite(F.carrier)",
				By(notInfinite, finite_set.InfiniteDef))
			atLeastTwo := a.Have(
				"F is a finite subfield of itself, so it has at least two elements",
				"2 ≤ card(F.carrier)",
				By(finite, field.CarrierSubfield.Read(F), FiniteSubfieldAtLeastTwo.Read(F).At(carrier)))
			larger := a.Have(
				"so F, closed, holds a subfield of q² elements containing it, q its size",
				"subfield(F, «quadraticExtension») ∧ "+
					"F.carrier ⊆ «quadraticExtension» ∧ "+
					"has_size(«quadraticExtension», card(F.carrier) ^ 2)",
				By(
					closed,
					finite,
					field.CarrierSubfield.Read(F),
					FiniteConstantsSubfield.Read(F).At(carrier, a.TermAs[Nat]("2"))))
			itself := a.Have(
				"that subfield lies in F and contains it, so it is F",
				"«quadraticExtension» = F.carrier",
				By(
					larger,
					field.SubfieldSubset.At(fieldF, quadraticExtension),
					set_order.SubsetAntisym.At(quadraticExtension, carrier)))
			square := a.Have(
				"so F has q² elements",
				"card(F.carrier) = card(F.carrier) ^ 2",
				By(
					larger,
					itself,
					cardinality.HasSizeDef.At(quadraticExtension, a.TermAs[Nat]("card(F.carrier) ^ 2"))))
			a.Show(
				"but q < q² for q ≥ 2",
				ByArith(square, atLeastTwo, nat_order.LessThanPow.At(size, a.TermAs[Nat]("1"), a.TermAs[Nat]("2"))))
		}),
})}

// FiniteConstantsImage — a ring map ι of an algebraically closed field M into a
// field N carries the subfield of Q = card(k)^m elements of M onto the points of
// N fixed by the Q-th power, k a finite subfield of M and m > 0: ι keeps powers,
// so it carries a fixed point to a fixed point; it is one-to-one, so the image
// has the Q points of the source (FiniteConstantsSubfield); and N has at most Q
// such points (FiniteConstantsBound), so the image is all of them.
var FiniteConstantsImage = finiteConstantsImageThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsImage",
	Key:  "prop_8610ed0054df030a",
	Reading: "N need not be algebraically closed, only M is: the bound of Q fixed points holds in " +
		"any field, and the image supplies Q of them. M closed is load-bearing, for it gives the source " +
		"its Q points; m > 0 is too, since at m = 0 both sides are whole carriers and ι need not be onto.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀N:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"finite(k)",
			"0 < m",
		},
		Conclusion: "image(ι, finite_constants(field_ring(M), card(k), m)) = " +
			"finite_constants(field_ring(N), card(k), m)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		N field.FieldFact[on.N],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		m *Expr[Nat],
		closed, hom, subK, finiteK, positive Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldN := a.TermAs[FieldOps[B]]("N")
		q := a.TermAs[Nat]("card(k)")
		Q := a.TermAs[Nat]("card(k) ^ m")
		source := a.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), m)")
		image := a.TermAs[Set[B]]("image(ι, finite_constants(field_ring(M), card(k), m))")
		target := a.TermAs[Set[B]]("finite_constants(field_ring(N), card(k), m)")
		inclusion := a.Have(
			"ι keeps the Q-th power, so it carries a point of M "+
				"that the power fixes to a point of N that it fixes",
			"image(ι, finite_constants(field_ring(M), card(k), m)) ⊆ "+
				"finite_constants(field_ring(N), card(k), m)",
			BySets(
				FiniteConstantsDef.At(a.TermAs[RingOps[A]]("field_ring(M)"), q, m),
				FiniteConstantsDef.At(a.TermAs[RingOps[B]]("field_ring(N)"), q, m),
				ring_homomorphism.MapIn.Read(hom),
				ring_homomorphism.RingMapPower.Read(hom).AsFact().At(Q)))
		imageSize := a.Have(
			"ι is one-to-one on M, so the image has the Q points of the source",
			"has_size(image(ι, finite_constants(field_ring(M), card(k), m)), card(k) ^ m)",
			By(
				M,
				N,
				closed,
				hom,
				subK,
				finiteK,
				positive,
				FiniteConstantsSubfield.At(fieldM, k, m),
				field.SubfieldSubset.At(fieldM, source),
				ring_homomorphism.FieldHomomorphismInjective.At(fieldM, fieldN, ι),
				functions.InjectiveOnSubset.At(ι, source, a.TermAs[Set[A]]("M.carrier")),
				cardinality.HasSizeImageInj.At(ι, source, Q)))
		bound := a.Have(
			"Q exceeds one, so the Q-th power fixes at most Q points of N",
			"finite(finite_constants(field_ring(N), card(k), m)) ∧ "+
				"card(finite_constants(field_ring(N), card(k), m)) ≤ card(k) ^ m",
			By(
				M,
				N,
				subK,
				finiteK,
				positive,
				FiniteSubfieldPowerEndomorphism.At(fieldM, k, m),
				FiniteConstantsBound.At(fieldN, q, m)))
		a.Show(
			"a subset of Q points of a finite set of at most Q points is the whole set",
			By(
				imageSize,
				inclusion,
				bound,
				cardinality.HasSizeDef.At(image, Q),
				cardinality.CardSubsetLe.At(image, target)))
	}),
})}

// FiniteSubfieldPowerEndomorphism — above a finite subfield k, m > 0, the
// power card(k)^m exceeds one, its power map is a ring endomorphism, and it is
// zero as a numeral of M: k has a positive power of its characteristic for size,
// the characteristic of M, and card(k)^m is such a power too.
var FiniteSubfieldPowerEndomorphism = finiteSubfieldPowerEndomorphismThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldPowerEndomorphism",
	Key:  "prop_f77045bde722b4cc",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀m:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"0 < m",
		},
		Conclusion: "ring_homomorphism(field_ring(M), " +
			"    field_ring(M), " +
			"    frobenius_power(field_ring(M), card(k) ^ m)) ∧ " +
			"1 < card(k) ^ m ∧ " +
			"«numeral»(M, card(k) ^ m) = M.zero",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		m *Expr[Nat],
		subfieldK, finiteK, positiveM Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		R := a.TermAs[RingOps[A]]("field_ring(M)")
		restricted := a.Have(
			"the finite subfield is a field on its own carrier",
			"field_on(restrict_field(M, k)) ∧ finite(restrict_field(M, k).carrier)",
			By(M, subfieldK, finiteK, field.SubfieldFieldOn.At(fieldM, k)))
		p, e, characteristicSize := a.Obtain2As[Nat, Nat](
			"the characteristic of k is that of M, and k has a positive power of it as size",
			"∃p e:num. ring_prime_characteristic(field_ring(M), p) ∧ 0 < e ∧ card(k) = p ^ e",
			Derive(func(b *Argument) {
				p, characteristicK := b.ObtainAs[Nat](
					"the finite subfield has a prime characteristic",
					"∃p:num. ring_prime_characteristic(field_ring(restrict_field(M, k)), p)",
					By(restricted, FiniteFieldCharacteristic.At(fieldK)))
				e, size := b.ObtainAs[Nat](
					"the finite carrier has positive prime-power size",
					"∃e:num. 0 < e ∧ card(k) = p ^ e",
					By(characteristicK, restricted, FiniteFieldSizePower.At(fieldK, p)))
				b.Show(
					"the characteristic equation uses the same zero, one and addition",
					Witness(p),
					Witness(e),
					By(Normalized, characteristicK, size, PrimeCharacteristicDef))
			}))
		positive := a.Have(
			"the exponent e·m is positive",
			"0 < e * m",
			ByArith(characteristicSize, positiveM, nat_order.LessEqSelfMul.At(e, m)))
		a.Show(
			"card(k)^m is the power p^(e·m) of the characteristic",
			By(
				Normalized,
				M,
				characteristicSize,
				positive,
				field.RingOn.At(fieldM),
				nat_arith.PowPow.At(p, e, m),
				FrobeniusRingHomomorphism.At(R, p, a.TermAs[Nat]("e * m")),
				PrimePowerVanishes.Read(field.RingOn.Read(M)).At(p, a.TermAs[Nat]("e * m"))))
	}),
})}

// FiniteSubfieldInConstants — a finite subfield l of M with q^m points lies in
// finite_constants(field_ring(M), q, m): l is a field on its own carrier, and
// FiniteFieldFixedByFrobenius fixes each of its points by the card(l)-th power.
var FiniteSubfieldInConstants = finiteSubfieldInConstantsThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldInConstants",
	Key:  "prop_596d9ca3f34481bc",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀l:set(A). ∀q m:num.",
		Hypotheses: []string{"subfield(M, l)", "finite(l)", "card(l) = q ^ m"},
		Conclusion: "l ⊆ finite_constants(field_ring(M), q, m)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l *Expr[Set[A]],
			q, m *Expr[Nat],
			subfieldL, finiteL, size Fact,
		) {
			ownField := a.Have(
				"l lies in M and is a field on its own carrier",
				"l ⊆ M.carrier ∧ field_on(restrict_field(M, l))",
				By(M, subfieldL, field.SubfieldFieldOn.At(a.TermAs[FieldOps[A]]("M"), l)))
			a.Show(
				"each point of l is a point of M fixed by the q^m-th power",
				BySets(
					size,
					ownField,
					finiteL,
					At(FiniteFieldFixedByFrobenius, a.TermAs[FieldOps[A]]("restrict_field(M, l)")),
					FiniteConstantsDef.At(a.TermAs[RingOps[A]]("field_ring(M)"), q, m)))
		}),
})}

// FiniteConstantsMono — along divisibility of the exponent, the fixed
// points of the powers of a commutative ring grow: write n = m·j; a point
// fixed by the q^m-th power is fixed by each of its iterates, and the j-th
// iterate is the q^n-th power.
var FiniteConstantsMono = finiteConstantsMonoThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsMono",
	Key:  "prop_8778de2f24755cfe",
	Reading: "No condition on q, m or n: m ∣ n is ∃j. n = m · j, so 0 ∣ n forces n = 0; at q = 0 a " +
		"positive exponent leaves the carrier's points equal to one, and exponent zero the whole carrier.",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀q m n:num.",
		Hypotheses: []string{
			"m ∣ n",
		},
		Conclusion: "finite_constants(R, q, m) ⊆ finite_constants(R, q, n)",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], q, m, n *Expr[Nat], divides Fact) {
		multiplicative := comm_ring.MulMonoidOn.Read(R)
		j, multiple := a.UnpackAs[Nat](a.Unfolded(divides, nat_divides.DividesFactor), "j")
		a.Do(Simp(Fwd(FiniteConstantsDef), Fwd(set_basic.SubsetDef)))
		x := a.FixAs[A]("x")
		inFixed := a.Assume()
		point := a.Have(
			"x is a point of the carrier fixed by the q^m-th power",
			"x ∈ R.carrier ∧ monoid_pow(R.mul, R.one, x, q ^ m) = x",
			BySets(inFixed))
		iterates := a.Have(
			"every iterate of the q^m-th power fixes x",
			"∀i:num. monoid_pow(R.mul, R.one, x, (q ^ m) ^ i) = x",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Induct(i)
				b.Base(
					"the zeroth iterate is the identity",
					By(Normalized, point, nat_arith.NatPow, comm_monoid.PowOneOn.Read(multiplicative).AsFact().At(x)))
				b.Step(
					"a further q^m-th power keeps x fixed",
					func(c *Argument, ih Fact) {
						c.Show(
							"x^((q^m)^(i+1)) is (x^(q^m))^((q^m)^i), which is x",
							By(
								Normalized,
								ih,
								point,
								nat_arith.NatPow,
								comm_monoid.PowPowOn.Read(multiplicative).AsFact().At(
									x, c.TermAs[Nat]("q ^ m"), c.TermAs[Nat]("(q ^ m) ^ i"))))
					})
			}))
		a.Show(
			"the q^n-th power is the j-th iterate of the q^m-th",
			BySets(Normalized, point, iterates.At(j), multiple, nat_arith.PowPow.At(q, m, j)))
	}),
})}

// FiniteConstantsInClosure — the points fixed by the q^m-th power, q = |k|, m > 0,
// lie in the algebraic closure of k in M: they lie in M, and q^m exceeds one, so
// each is algebraic over k (FiniteConstantsAlgebraic).
var FiniteConstantsInClosure = finiteConstantsInClosureThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsInClosure",
	Key:  "prop_484951c87b64e741",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀m:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"0 < m",
		},
		Conclusion: "finite_constants(field_ring(M), card(k), m) ⊆ algebraic_elements(M, k)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		m *Expr[Nat],
		subfieldK, finiteK, positive Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		ring := a.TermAs[RingOps[A]]("field_ring(M)")
		size := a.TermAs[Nat]("card(k)")
		exceeds := a.Conjuncts(
			GroupPremises(M, subfieldK, finiteK, positive, At(FiniteSubfieldPowerEndomorphism, ops, k, m)),
			"the power map is a ring endomorphism",
			"the power exceeds one",
			"and is zero in M")
		notOne := a.Have(
			"so it is not one",
			"card(k) ^ m ≠ 1",
			ByArith(exceeds[1]))
		a.Do(Unfold(set_basic.SubsetDef))
		y := a.FixAs[A]("y")
		fixed := a.Assume()
		algebraic := a.Have(
			"y is algebraic over k",
			"algebraic_over(M, k, y)",
			By(M, subfieldK, notOne, fixed, FiniteConstantsAlgebraic.At(ops, k, size, m, y)))
		a.Show(
			"and it lies in M",
			BySets(
				fixed,
				algebraic,
				FiniteConstantsDef.At(ring, size, m),
				algebraic_element.AlgebraicElementsDef.At(ops, k)))
	}),
})}

// FiniteConstantsShiftedPower — where e divides m - 1, the q^m-th power acts as
// the q-th power on the points fixed by the q^e-th power: such a point is fixed
// by the q^(m-1)-th power (FiniteConstantsMono), and q^m = q^(m-1)·q.
var FiniteConstantsShiftedPower = finiteConstantsShiftedPowerThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsShiftedPower",
	Key:  "prop_109bb1eb80b69f06",
	Reading: "0 < m is load-bearing: m - 1 is truncated, " +
		"and at m = 0 the left side is the first power.",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀q e m:num. ∀c:A.",
		Hypotheses: []string{
			"0 < m",
			"e ∣ m - 1",
			"c ∈ finite_constants(R, q, e)",
		},
		Conclusion: "monoid_pow(R.mul, R.one, c, q ^ m) = monoid_pow(R.mul, R.one, c, q)",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		q, e, m *Expr[Nat],
		c *Expr[A],
		positive, divides, member Fact,
	) {
		ringR := a.TermAs[RingOps[A]]("R")
		shift := a.TermAs[Nat]("m - 1")
		one := a.TermAs[Nat]("1")
		power := a.TermAs[Nat]("q ^ (m - 1)")
		shifted := a.Have(
			"c is fixed by the q^(m-1)-th power",
			"c ∈ finite_constants(R, q, m - 1)",
			BySets(divides, member, FiniteConstantsMono.Read(R).At(q, e, shift)))
		fixed := a.Conjuncts(
			a.Have(
				"which reads, by the definition",
				"c ∈ R.carrier ∧ monoid_pow(R.mul, R.one, c, q ^ (m - 1)) = c",
				BySets(shifted, FiniteConstantsDef.At(ringR, q, shift))),
			"c lies in R",
			"the q^(m-1)-th power fixes it")
		successor := a.Have(
			"m is one more than m - 1",
			"m - 1 + 1 = m",
			ByArith(positive))
		exponent := a.Have(
			"so q^m is q^(m-1)·q",
			"q ^ m = q ^ (m - 1) * q",
			By(Normalized, successor, nat_arith.PowAdd.At(q, shift, one), nat_arith.PowOne.At(q)))
		iterated := a.Have(
			"the q-th power of the q^(m-1)-th power is the power at the product",
			"monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, c, q ^ (m - 1)), q) = "+
				"monoid_pow(R.mul, R.one, c, q ^ (m - 1) * q)",
			By(fixed[0], comm_monoid.PowPowOn.Read(comm_ring.MulMonoidOn.Read(R)).AsFact().At(c, power, q)))
		a.Show(
			"so the q^m-th power of c is its q-th power",
			By(Normalized, fixed[1], iterated, exponent))
	}),
})}

// FiniteConstantsFermat — on the points fixed by the q^s-th power, q^s > 1,
// a positive multiple of q^s − 1 as exponent sends zero to zero and every
// other point to one: c·c^(q^s − 1) = c^(q^s) = c, so off zero c^(q^s − 1)
// is one and so are its powers, while zero to a positive power is zero.
var FiniteConstantsFermat = finiteConstantsFermatThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsFermat",
	Key:  "prop_e0e75fbb0d27f453",
	Reading: "1 < q^s is load-bearing at zero: at q^s = 1 the exponent is zero " +
		"and zero to the zeroth power is one. No finiteness is read: the points " +
		"fixed by the q^s-th power are what the statement speaks of, and in a field " +
		"each of them other than zero is a root of unity of order dividing q^s − 1.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀q s t:num. ∀c:A.",
		Hypotheses: []string{
			"1 < q ^ s",
			"0 < t",
			"c ∈ finite_constants(field_ring(M), q, s)",
		},
		Conclusion: "monoid_pow(M.mul, M.one, c, (q ^ s - 1) * t) = COND(c = M.zero, M.zero, M.one)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		q, s, t *Expr[Nat],
		c *Expr[A],
		large, positive, fixed Fact,
	) {
		ring := field.RingOn.Read(M)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		unitExponent := a.TermAs[Nat]("q ^ s - 1")
		parts := a.Conjuncts(
			a.Have(
				"c lies in M and is fixed by the q^s-th power",
				"c ∈ M.carrier ∧ monoid_pow(M.mul, M.one, c, q ^ s) = c",
				BySets(fixed, FiniteConstantsDef.At(fieldRing, q, s))),
			"c lies in M",
			"the q^s-th power fixes it")
		cm := a.MemberOf[on.M](c, parts[0])
		successor := a.Have(
			"q^s is one more than q^s − 1",
			"suc(q ^ s - 1) = q ^ s",
			ByArith(large))
		absorbed := a.Have(
			"so c times c^(q^s − 1) is c^(q^s), which is c",
			"c * monoid_pow(M.mul, M.one, c, q ^ s - 1) = c",
			By(parts[1], successor, comm_monoid.MonoidPowDef))
		a.Cases(a.Term("c = M.zero"))
		a.When(
			"zero to a positive power is zero",
			func(b *Argument, zero Fact) {
				split := b.Have(
					"the exponent is a successor, both its factors being positive",
					"suc((q ^ s - 1) * t - 1) = (q ^ s - 1) * t",
					ByArith(large, positive, nat_arith.MulEqZero.At(unitExponent, t)))
				factor := b.Have(
					"so the power splits off one factor c",
					"monoid_pow(M.mul, M.one, c, (q ^ s - 1) * t) = "+
						"c * monoid_pow(M.mul, M.one, c, (q ^ s - 1) * t - 1)",
					By(split, comm_monoid.MonoidPowDef))
				b.Show(
					"and that factor is zero",
					By(
						zero,
						factor,
						comm_ring.MulLeftZeroOn.Read(ring),
						comm_monoid.PowIn.Read(multiplicative).At(cm, b.TermAs[Nat]("(q ^ s - 1) * t - 1"))))
			})
		a.Otherwise(
			"off zero c^(q^s − 1) is one, and so is every power of it",
			func(b *Argument, nonzero Fact) {
				unitPower := b.MemberOf[on.M](
					b.TermAs[A]("monoid_pow(M.mul, M.one, c, q ^ s - 1)"),
					comm_monoid.PowIn.Read(multiplicative).At(cm, unitExponent))
				oneM := b.MemberOf[on.M](b.TermAs[A]("M.one"), comm_ring.OneIn.Read(ring))
				unit := b.Have(
					"cancelling c from c·c^(q^s − 1) = c = c·1",
					"monoid_pow(M.mul, M.one, c, q ^ s - 1) = M.one",
					By(
						nonzero,
						absorbed,
						comm_monoid.RightIdentityOn.Read(multiplicative).At(cm),
						integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(M)).At(
							cm, unitPower, oneM)))
				b.Show(
					"c^((q^s − 1)·t) is the t-th power of one",
					By(
						nonzero,
						unit,
						comm_monoid.PowPowOn.Read(multiplicative).At(cm, unitExponent, t),
						comm_monoid.IdentityPowOn.Read(multiplicative).At(t)))
			})
	}),
})}

// FiniteConstantsAlgebraic — where q^m is not one, a point fixed by the
// q^m-th power is algebraic over every subfield: it is a root of
// X^(q^m) − X, a difference of two basis vectors, so a polynomial over any
// subfield, and not the zero polynomial, its coefficient at q^m being one.
var FiniteConstantsAlgebraic = finiteConstantsAlgebraicThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsAlgebraic",
	Key:  "prop_4d0a821f60f1b500",
	Reading: "q^m ≠ 1 is load-bearing: at q^m = 1 the polynomial is X − X, zero, and " +
		"the set is the whole carrier, transcendental points included. Nothing else is " +
		"read: k need not be finite nor lie among the fixed points, since the coefficients " +
		"are 0, 1 and −1, which every subfield holds, and M need not be closed.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀q m:num. ∀y:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"q ^ m ≠ 1",
			"y ∈ finite_constants(field_ring(M), q, m)",
		},
		Conclusion: "algebraic_over(M, k, y)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		q, m *Expr[Nat],
		y *Expr[A],
		subfieldK, notOne, fixed Fact,
	) {
		ring := field.RingOn.Read(M)
		baseRing := a.Have(
			"k is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), k))",
			By(subfieldK, field.SubfieldCommRing.Read(M).At(k)))
		exponent := a.TermAs[Nat]("q ^ m")
		exponentOne := a.TermAs[Nat]("1")
		power := a.TermAs[Fun[Nat, A]]("basis_vector(q ^ m)")
		variable := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
		overK := a.Have(
			"X^(q^m) − X is a polynomial over k, a difference of two basis vectors",
			"polynomial_over(k, «xPowerMinusX»(M, q ^ m))",
			By(
				baseRing,
				polynomial.BasisVectorOver.Read(baseRing).At(exponent),
				polynomial.BasisVectorOver.Read(baseRing).At(exponentOne),
				comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(baseRing)).AsFact().At(power, variable)))
		leading := a.Have(
			"at the index q^m only X^(q^m) contributes, q^m not being one",
			"«xPowerMinusX»(M, q ^ m, q ^ m) = M.one",
			Simp(Fwd(XPowerMinusXCoefficient)),
			ByArith(Normalized, M, notOne))
		nonzero := a.Have(
			"so it is not the zero polynomial, one not being zero",
			"«xPowerMinusX»(M, q ^ m) ≠ vec_zero",
			By(leading, field.OneNotZeroOn.Read(M), vec_space.VecZeroDef.At(a.TermAs[A]("M.zero"), exponent)))
		point := a.Have(
			"y is a point of M fixed by the q^m-th power",
			"y ∈ M.carrier ∧ monoid_pow(M.mul, M.one, y, q ^ m) = y",
			BySets(fixed, FiniteConstantsDef.At(a.TermAs[RingOps[A]]("field_ring(M)"), q, m)))
		root := a.Have(
			"y is a root of X^(q^m) − X: its value there is y^(q^m) − y",
			"polynomial_eval(«xPowerMinusX»(M, q ^ m), y) = M.zero",
			ByArith(M, point, XPowerMinusXEval.Read(ring).AsFact().At(exponent, y)))
		a.Do(Unfold(algebraic_element.AlgebraicOverDef))
		a.Take(a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(M, q ^ m)"))
		a.Show(
			"X^(q^m) − X is a nonzero polynomial over k vanishing at y",
			By(overK, nonzero, root))
	}),
})}

// FiniteSubfieldAlgebraic — a member of a finite subfield l is algebraic over every
// subfield: l is fixed by the power card(l) (FiniteSubfieldInConstants), and card(l)
// is not 1, so each member is a root of X^card(l) - X (FiniteConstantsAlgebraic).
var FiniteSubfieldAlgebraic = finiteSubfieldAlgebraicThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldAlgebraic",
	Key:  "prop_137f376b0fc4993a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"finite(l)",
			"y ∈ l",
		},
		Conclusion: "algebraic_over(M, k, y)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			y *Expr[A],
			subfieldK, subfieldL, finiteL, yIn Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			count := a.TermAs[Nat]("card(l)")
			one := a.TermAs[Nat]("1")
			large := a.Have(
				"l has at least two elements",
				"2 ≤ card(l)",
				By(M, subfieldL, finiteL, At(FiniteSubfieldPrimePower, fieldM, l)))
			exponent := a.Have(
				"card(l) is its own first power",
				"card(l) = card(l) ^ 1",
				By(nat_arith.PowOne.At(count)))
			constant := a.Have(
				"l is fixed by the power card(l), so y is",
				"y ∈ finite_constants(field_ring(M), card(l), 1)",
				BySets(
					yIn,
					GroupPremises(
						M, subfieldL, finiteL, exponent, FiniteSubfieldInConstants.At(fieldM, l, count, one))))
			notOne := a.Have(
				"and the power is not one",
				"card(l) ^ 1 ≠ 1",
				exponent.RwRev(),
				ByArith(large))
			a.Show(
				"so y is a root of X^(card l) - X",
				By(M, subfieldK, notOne, constant, FiniteConstantsAlgebraic.At(fieldM, k, count, one, y)))
		}),
})}

// BoundedDegreeInConstants — over a finite subfield k of q elements, an
// element algebraic of degree at most D lies in the field of q^s elements
// for every s that each positive m ≤ D divides: k(y) is a subfield of
// q^m elements, m = [k(y) : k] positive and at most D (FiniteExtensionSize),
// so it lies in the field of q^m elements (FiniteSubfieldInConstants),
// which lies in the field of q^s elements as m divides s
// (FiniteConstantsMono).
var BoundedDegreeInConstants = boundedDegreeInConstantsThm{family.Add(registry.ProofEntry{
	Name: "BoundedDegreeInConstants",
	Key:  "prop_46778c3082591e1",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀D s:num. ∀y:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"y ∈ M.carrier",
			"algebraic_over(M, k, y)",
			"extension_degree(M, k, field_adjoin(M, k, {y})) ≤ D",
			"∀m:num. 0 < m ∧ m ≤ D ⇒ m ∣ s",
		},
		Conclusion: "y ∈ finite_constants(field_ring(M), card(k), s)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		D, s *Expr[Nat],
		y *Expr[A],
		subfieldK, finiteK, yIn, algebraic, bounded, divides Fact,
	) {
		ym := a.MemberOf[on.M](y, yIn)
		adjoined := a.TermAs[Set[A]]("field_adjoin(M, k, {y})")
		degree := a.TermAs[Nat]("extension_degree(M, k, field_adjoin(M, k, {y}))")
		q := a.TermAs[Nat]("card(k)")
		between := a.Conjuncts(
			GroupPremises(subfieldK, algebraic_element.AdjoinElementSubfield.Read(M).At(k, ym)),
			"k(y) is a subfield of M",
			"holding k",
			"and y")
		finiteExtension := a.Conjuncts(
			GroupPremises(subfieldK, algebraic, algebraic_element.AdjoinDegree.Read(M).At(k, ym)),
			"k(y) is finite over k",
			"of the degree of the minimal polynomial of y")
		positive := a.Have(
			"which is positive",
			"0 < extension_degree(M, k, field_adjoin(M, k, {y}))",
			By(
				subfieldK,
				algebraic,
				finiteExtension[1],
				algebraic_element.MinimalPolynomialPositive.Read(M).At(k, ym)))
		size := a.Have(
			"so k(y) has q^m elements, m its degree over k",
			"finite(field_adjoin(M, k, {y})) ∧ "+
				"card(field_adjoin(M, k, {y})) = card(k) ^ extension_degree(M, k, field_adjoin(M, k, {y}))",
			By(
				subfieldK,
				between[0],
				between[1],
				finiteK,
				finiteExtension[0],
				cardinality.HasSizeDef,
				FiniteExtensionSize.Read(M).At(k, adjoined)))
		inConstants := a.Have(
			"so it lies in the field of q^m elements",
			"field_adjoin(M, k, {y}) ⊆ "+
				"finite_constants(field_ring(M), card(k), extension_degree(M, k, field_adjoin(M, k, {y})))",
			By(between[0], size, FiniteSubfieldInConstants.Read(M).At(adjoined, q, degree)))
		grows := a.Have(
			"which lies in the field of q^s elements, m dividing s",
			"finite_constants(field_ring(M), card(k), extension_degree(M, k, field_adjoin(M, k, {y}))) ⊆ "+
				"finite_constants(field_ring(M), card(k), s)",
			By(
				positive,
				bounded,
				divides.At(degree),
				FiniteConstantsMono.Read(field.RingOn.Read(M)).At(q, degree, s)))
		a.Show(
			"so y lies there",
			BySets(between[2], inConstants, grows))
	}),
})}

// FiniteConstantsTower — the q^e-th-power fixed points over q^r are the fixed
// points of the q^(r·e)-th power: the two powers are one number.
var FiniteConstantsTower = finiteConstantsTowerThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsTower",
	Key:  "prop_24c785c2cc31329a",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀q r e:num. finite_constants(R, q ^ r, e) = finite_constants(R, q, r * e)",
		func(a *Argument, R *Expr[RingOps[A]], q, r, e *Expr[Nat]) {
			a.Do(Simp(Fwd(FiniteConstantsDef), Fwd(nat_arith.PowPow)), Basic())
		}),
})}

// FiniteSubfieldAtLeastTwo — a finite subfield has at least two elements: one is
// left when zero is counted out.
var FiniteSubfieldAtLeastTwo = finiteSubfieldAtLeastTwoThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldAtLeastTwo",
	Key:  "prop_316c857c0ec06203",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
		},
		Conclusion: "2 ≤ card(k)",
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], subK, finiteK Fact) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		one := a.TermAs[A]("M.one")
		rest := a.TermAs[Set[A]]("delete(k, M.zero)")
		oneLeft := a.Have(
			"one stays when zero is deleted from k",
			"M.one ∈ delete(k, M.zero)",
			By(
				subK,
				field.SubfieldOne.At(fieldM, k),
				field.OneNotZeroOn.Read(M),
				set_basic.InDelete.At(k, one, zero)))
		counted := a.Have(
			"counting zero out of k",
			"card(k) = suc(card(delete(k, M.zero)))",
			By(subK, finiteK, field.SubfieldZero.At(fieldM, k), cardinality.CountsOneMore.At(k, zero)))
		nonempty := a.Have(
			"what is left is not empty",
			"card(delete(k, M.zero)) ≠ 0",
			By(
				Normalized,
				oneLeft,
				finiteK,
				finite_set.FiniteDeleteImp.At(k, zero),
				cardinality.CardEqZero.At(rest),
				set_basic.MemberNotEmpty))
		a.Show(
			"zero and one are two elements",
			ByArith(counted, nonempty))
	}),
})}

// FiniteConstantsContained — inside a closed field, over a finite subfield k,
// the subfield with q^d elements lies in the one with q^n elements exactly when d
// divides n: the larger is a vector space over the smaller, so q^n is a power
// of q^d, and powers of q ≥ 2 are equal only at equal exponents.
var FiniteConstantsContained = finiteConstantsContainedThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsContained",
	Key:  "prop_d89f911563bd0f6a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀d n:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"0 < d",
			"0 < n",
		},
		Conclusion: "(finite_constants(field_ring(M), card(k), d) ⊆ " +
			"    finite_constants(field_ring(M), card(k), n) ⇔ " +
			"    d ∣ n)",
		Abbrev: Abbrev{
			{Name: "degree", Text: "extension_degree(M, " +
				"    finite_constants(field_ring(M), card(k), d), " +
				"    finite_constants(field_ring(M), card(k), n))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		d, n *Expr[Nat],
		closed, subK, finiteK, positiveD, positiveN Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		q := a.TermAs[Nat]("card(k)")
		a.Iff()
		a.Forward(
			"an inclusion of the subfields makes the degree of "+
				"the larger over the smaller a quotient of n by d",
			func(b *Argument, contained Fact) {
				smaller := b.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), d)")
				larger := b.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), n)")
				e := b.TermAs[Nat]("«degree»")
				product := b.TermAs[Nat]("d * «degree»")
				sizeD := b.Have(
					"the smaller set is a subfield with q^d elements",
					"subfield(M, finite_constants(field_ring(M), card(k), d)) ∧ "+
						"has_size(finite_constants(field_ring(M), card(k), d), card(k) ^ d)",
					By(M, closed, subK, finiteK, positiveD, FiniteConstantsSubfield.At(fieldM, k, d)))
				sizeN := b.Have(
					"the larger set is a subfield with q^n elements",
					"subfield(M, finite_constants(field_ring(M), card(k), n)) ∧ "+
						"has_size(finite_constants(field_ring(M), card(k), n), card(k) ^ n)",
					By(M, closed, subK, finiteK, positiveN, FiniteConstantsSubfield.At(fieldM, k, n)))
				tower := b.Have(
					"the larger is a finite space over the smaller",
					"card(finite_constants(field_ring(M), card(k), n)) = "+
						"card(finite_constants(field_ring(M), card(k), d)) ^ «degree»",
					By(
						M,
						contained,
						sizeD,
						sizeN,
						FiniteSubfieldSize.At(fieldM, smaller, larger),
						cardinality.HasSizeDef))
				powers := b.Have(
					"so q^n is q to the d times the degree",
					"card(k) ^ n = card(k) ^ (d * «degree»)",
					By(tower, sizeD, sizeN, cardinality.HasSizeDef, nat_arith.PowPow.At(q, d, e)))
				two := b.Have(
					"q is at least two",
					"2 ≤ card(k)",
					By(M, subK, finiteK, FiniteSubfieldAtLeastTwo.At(fieldM, k)))
				exponents := b.Have(
					"powers of q are equal only at equal exponents",
					"n = d * «degree»",
					ByArith(
						two,
						powers,
						nat_order.LessThanPow.At(q, n, product),
						nat_order.LessThanPow.At(q, product, n)))
				b.Show(
					"d divides n",
					By(exponents, nat_divides.DividesOwnMultiple))
			})
		a.Backward(
			"along divisibility the fixed points grow",
			func(b *Argument, divides Fact) {
				b.Show(
					"d divides n, so an element fixed by the q^d-th power is fixed by the q^n-th",
					By(divides, FiniteConstantsMono.Read(field.RingOn.Read(M)).At(q, d, n)))
			})
	}),
})}

// FrobeniusOfFiniteSubfield — the card(k)-th power is a ring endomorphism of M
// for a finite subfield k: card(k) is a positive power of the characteristic.
var FrobeniusOfFiniteSubfield = frobeniusOfFiniteSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusOfFiniteSubfield",
	Key:  "prop_26b40c5d33044c76",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
		},
		Conclusion: "ring_homomorphism(field_ring(M), " +
			"    field_ring(M), " +
			"    frobenius_power(field_ring(M), card(k)))",
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], subK, finiteK Fact) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		kField := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(M, subK, field.SubfieldFieldOn.At(fieldM, k)))
		p, characteristicK := a.ObtainAs[Nat](
			"the finite field k has a prime characteristic p",
			"∃p:num. ring_prime_characteristic(field_ring(restrict_field(M, k)), p)",
			By(kField, finiteK, FiniteFieldCharacteristic.At(fieldK)))
		e, size := a.ObtainAs[Nat](
			"and card(k) is a positive power of p",
			"∃e:num. 0 < e ∧ card(k) = p ^ e",
			By(kField, finiteK, characteristicK, FiniteFieldSizePower.At(fieldK, p)))
		characteristicM := a.Have(
			"M has the characteristic of k: the same zero, one and addition",
			"ring_prime_characteristic(field_ring(M), p)",
			By(Normalized, characteristicK, PrimeCharacteristicDef))
		a.Show(
			"a power of the characteristic is a ring map",
			By(
				Normalized,
				size,
				characteristicM,
				FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, e)))
	}),
})}

// FiniteConstantsAutomorphisms — the subfield with q^d elements is an extension of
// k of degree d, with d automorphisms over k: the q-th power is one of them, its
// fixed points are k, so the extension is Galois.
var FiniteConstantsAutomorphisms = finiteConstantsAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsAutomorphisms",
	Key:  "prop_55e17110803150f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀d:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"0 < d",
		},
		Conclusion: "finite_extension(M, k, finite_constants(field_ring(M), card(k), d)) ∧ " +
			"extension_degree(M, k, finite_constants(field_ring(M), card(k), d)) = d ∧ " +
			"has_size(field_automorphisms(M, k, finite_constants(field_ring(M), card(k), d)), d)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		d *Expr[Nat],
		closed, subK, finiteK, positive Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		ambient := a.TermAs[RingOps[A]]("field_ring(M)")
		q := a.TermAs[Nat]("card(k)")
		E, EDef := a.LetAs[Set[A]]("E", "finite_constants(field_ring(M), card(k), d)")
		G, GDef := a.LetAs[Set[symmetric_group.Permutation[A]]]("G", "field_automorphisms(M, k, E)")
		frobenius := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), card(k))")
		constants := a.Have(
			"E is a subfield of q^d elements holding k",
			"subfield(M, E) ∧ k ⊆ E ∧ has_size(E, card(k) ^ d)",
			By(Normalized, EDef, M, closed, subK, finiteK, positive, FiniteConstantsSubfield.At(fieldM, k, d)))
		sized := a.Have(
			"E is a finite extension of k of q to the degree elements",
			"finite_extension(M, k, E) ∧ card(E) = card(k) ^ extension_degree(M, k, E)",
			By(M, subK, constants, FiniteSubfieldSize.At(fieldM, k, E), cardinality.HasSizeDef))
		two := a.Have(
			"q is at least two",
			"2 ≤ card(k)",
			By(M, subK, finiteK, FiniteSubfieldAtLeastTwo.At(fieldM, k)))
		e := a.TermAs[Nat]("extension_degree(M, k, E)")
		degree := a.Have(
			"powers of q are equal only at equal exponents, so the degree is d",
			"extension_degree(M, k, E) = d",
			ByArith(
				two,
				constants,
				sized,
				nat_order.LessThanPow.At(q, d, e),
				nat_order.LessThanPow.At(q, e, d),
				cardinality.HasSizeDef.At(E, a.TermAs[Nat]("card(k) ^ d"))))
		onE := a.Have(
			"the q-th power is a ring map on E",
			"ring_homomorphism(restrict_ring(field_ring(M), E), "+
				"    field_ring(M), "+
				"    frobenius_power(field_ring(M), card(k)))",
			By(
				M,
				subK,
				finiteK,
				constants,
				FrobeniusOfFiniteSubfield.At(fieldM, k),
				ring_homomorphism.RingHomRestrictSource.At(ambient, ambient, frobenius, E),
				field.SubfieldSubring.At(fieldM, E)))
		kField := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(M, subK, field.SubfieldFieldOn.At(fieldM, k)))
		fixesK := a.Have(
			"the q-th power fixes k",
			"∀x:A. x ∈ k ⇒ frobenius_power(field_ring(M), card(k), x) = x",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inK := b.Assume()
				b.Show(
					"k has q elements",
					By(Normalized, kField, finiteK, inK, FiniteFieldFixedByFrobenius.At(fieldK, x), FrobeniusPowerDef))
			}))
		eRing := a.Have(
			"E is a commutative ring",
			"comm_ring_on(restrict_ring(field_ring(M), E))",
			By(constants, field.SubfieldCommRing.Read(M).At(E)))
		intoE := a.Have(
			"the q-th power keeps E",
			"∀x:A. x ∈ E ⇒ frobenius_power(field_ring(M), card(k), x) ∈ E",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inE := b.Assume()
				b.Show(
					"a power of an element of the ring E lies in E",
					By(
						inE,
						eRing,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(eRing)).AsFact().At(x, q),
						FrobeniusPowerDef))
			}))
		inside := a.Have(
			"so the image of E lies in E",
			"image(frobenius_power(field_ring(M), card(k)), E) ⊆ E",
			BySets(intoE))
		onto := a.Have(
			"a map of a finite extension into itself is onto",
			"image(frobenius_power(field_ring(M), card(k)), E) = E",
			By(
				M,
				subK,
				constants,
				sized,
				onE,
				fixesK,
				inside,
				field_extension.FiniteEmbeddingOnto.At(fieldM, k, E, frobenius)))
		_, automorphism := a.ObtainAs[symmetric_group.Permutation[A]](
			"so the q-th power is an automorphism p of E over k",
			"∃p:permutation(A). "+
				"    p ∈ G ∧ (∀x:A. x ∈ E ⇒ permutation_map(p, x) = frobenius_power(field_ring(M), card(k), x))",
			By(
				GDef,
				M,
				constants,
				onE,
				fixesK,
				onto,
				field_automorphism.EmbeddingPermutation.At(fieldM, k, E, frobenius)))
		fixedPoints := a.Have(
			"what the automorphisms fix, the q-th power fixes, and that is k",
			"∀x:A. x ∈ fixed_field(E, G) ⇒ x ∈ k",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				fixed := b.Assume()
				byAll := b.Have(
					"x is an element of E fixed by p",
					"x ∈ E ∧ permutation_map(p, x) = x",
					BySets(fixed, automorphism, field_automorphism.FixedFieldDef.At(E, G)))
				power := b.Have(
					"so x is an element of M fixed by the q-th power",
					"x ∈ M.carrier ∧ monoid_pow(M.mul, M.one, x, card(k)) = x",
					BySets(
						byAll,
						constants,
						automorphism,
						field.SubfieldSubset.At(fieldM, E),
						FrobeniusPowerDef.At(ambient, q, x)))
				b.Show(
					"the fixed points of the q-th power are k",
					BySets(power, subK, finiteK, M, FrobeniusFixedField.At(fieldM, k)))
			}))
		fixedField := a.Have(
			"the fixed field of the automorphisms is k",
			"fixed_field(E, G) = k",
			BySets(M, fixedPoints, constants, GDef, field_automorphism.SubfieldFixed.At(fieldM, k, E)))
		galois := a.Have(
			"so E is Galois over k",
			"galois_over(M, k, E)",
			By(
				Normalized,
				GDef,
				M,
				subK,
				constants,
				sized,
				fixedField,
				galois_correspondence.GaloisIffFixed.At(fieldM, k, E)))
		counted := a.Have(
			"and the automorphisms number the degree",
			"finite(G) ∧ card(G) = extension_degree(M, k, E)",
			By(
				Normalized,
				GDef,
				M,
				subK,
				constants,
				sized,
				galois,
				galois_correspondence.GaloisIffCard.At(fieldM, k, E),
				field_automorphism.AutomorphismsBound.At(fieldM, k, E)))
		size := a.Have(
			"so there are d of them",
			"has_size(G, d)",
			By(Normalized, counted, degree, cardinality.HasSizeDef.At(G, d)))
		a.Show(
			"E is an extension of degree d with d automorphisms",
			By(sized, degree, size, GDef))
	}),
})}
