// integer_scalars.go — the integers as a principal ideal domain, restriction to integer
// scalars, and the integer and rational scalar rings inside a field.

package int_lattice

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerRingPrincipalIdealDomain — the integers form a principal ideal
// domain: each ideal is an additive subgroup, whose nonnegative generator
// also generates the ideal under multiplication by integers.
var IntegerRingPrincipalIdealDomain = integerRingPrincipalIdealDomainThm{family.Add(registry.ProofEntry{
	Name: "IntegerRingPrincipalIdealDomain",
	Key:  "prop_ac0ef2fa36e55fa4",
	Build: family.Sections("principal_ideal_domain(int_ring)", func(
		ctx *Script,
		headline string,
	) *GoalStackNode {
		domain := ctx.Lemma("integral_domain_on(int_ring)", func(a *Argument) {
			a.Show(
				"one is nonzero and an integer product vanishes only with a zero factor",
				Simp(Fwd(int_real_lift.IntRingDef), Fwd(integral_domain.IntegralDomainOn)),
				By(
					int_real_lift.CommRingOn,
					int_real_lift.IntRingDef,
					int_real_lift.MulEqZero,
					int_real_lift.ZeroLessThanOne,
					int_real_lift.NotEqualOfLessThan.At(a.TermAs[Int]("0"), a.TermAs[Int]("1"))))
		})

		return ctx.Theorem(headline, func(a *Argument) {
			a.Show(
				"the integer domain has a generator for each ideal",
				Simp(Fwd(principal_ideal_domain.PrincipalIdealDomainDef)),
				SplitConj(
					Case(
						"the integer ring is an integral domain",
						Cite(domain)),
					Case(
						"an additive subgroup generator generates the ideal",
						Derive(func(b *Argument) {
							I := b.FixAs[Set[Int]]("I")
							ideal := b.Assume()
							_, generated := b.ObtainAs[Nat](
								"choose the ideal's nonnegative additive generator",
								"∃d:num. I = image(λz:int. d * z, 𝕌)",
								By(
									ideal,
									quotient_ring.IdealSubgroup.Read(int_real_lift.CommRingOn).At(I),
									int_div_rem.IntegerSubgroupPrincipal.At(I)))
							b.Take(b.TermAs[Int]("d"))
							b.Show(
								"the generator lies in the integer carrier and has the required multiples",
								BySets(generated))
						})),
				))
		})
	}),
})}

// IntegerScalarRestriction — restriction along the integer map preserves
// submodules, spans, bases and finite generation: finite relations transport
// through its bijection onto the integer image.
var IntegerScalarRestriction = integerScalarRestrictionThm{family.Add(registry.ProofEntry{
	Name: "IntegerScalarRestriction",
	Key:  "prop_8392d818baf0a4af",
	Reading: "The restriction keeps M's carrier, addition, zero and negation, and lets an integer " +
		"z act as integer_map(R, z). Characteristic zero is used only for bases: integer_map is then " +
		"injective, so an integer coefficient vanishes exactly when its image in R does, which " +
		"carries independence across; submodules, spans and finite generation transfer without it.",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"characteristic_zero(R)",
			"module_on(restrict_ring(R, integer_image(R)), M)",
		},
		Conclusion: "module_on(int_ring, scalar_restriction(integer_map(R), M)) ∧ " +
			"(∀N:set(B). " +
			"    submodule(restrict_ring(R, integer_image(R)), M, N) ⇔ " +
			"    submodule(int_ring, scalar_restriction(integer_map(R), M), N)) ∧ " +
			"(∀E:set(B). " +
			"    module_span(restrict_ring(R, integer_image(R)), M, E) = " +
			"    module_span(int_ring, scalar_restriction(integer_map(R), M), E) ∧ " +
			"    (module_basis(restrict_ring(R, integer_image(R)), M, E) ⇔ " +
			"        module_basis(int_ring, scalar_restriction(integer_map(R), M), E))) ∧ " +
			"(module_finitely_generated(restrict_ring(R, integer_image(R)), M) ⇔ " +
			"    module_finitely_generated(int_ring, scalar_restriction(integer_map(R), M)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		submodules := ctx.Lemma("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:set(B). "+
			"    submodule(restrict_ring(R, integer_image(R)), M, N) ⇔ "+
			"    submodule(int_ring, scalar_restriction(integer_map(R), M), N)",
			func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[Set[B]]) {
				a.Show(
					"stability under image scalars is stability under all their integer representatives",
					Simp(
						Fwd(submodule.SubmoduleDef),
						Fwd(module_record.RestrictRingDef),
						Fwd(int_real_lift.IntRingDef),
						Fwd(characteristic_zero.IntegerImageDef),
						Fwd(module_record.ScalarRestrictionDef),
						Fwd(module_record.ModuleAdditiveGroupDef)),
					BySets())
			})

		spans := ctx.Lemma("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B). "+
			"    module_span(restrict_ring(R, integer_image(R)), M, E) = "+
			"    module_span(int_ring, scalar_restriction(integer_map(R), M), E)",
			func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], E *Expr[Set[B]]) {
				a.Show(
					"the two spans intersect the same family of submodules",
					Unfold(submodule.ModuleSpanDef),
					Congr(),
					Cite(submodules))
			})

		kernel := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A).",
			Hypotheses: []string{"characteristic_zero(R)"},
			Conclusion: "∀z:int. integer_map(R, z) = R.zero ⇔ z = 0",
		}, func(a *Argument, R comm_ring.CommRingFact[on.R], charZero Fact) {
			r := a.TermAs[RingOps[A]]("R")
			z := a.FixAs[Int]("z")
			a.Show(
				"characteristic zero makes the integer map, a ring "+
					"homomorphism, injective, and such a map sends only zero to zero",
				By(
					charZero,
					R,
					characteristic_zero.IntegerMapInjective.At(r),
					int_real_lift.IntegerRingCarrierUniversal.At(z),
					int_real_lift.IntRingDef,
					ring_homomorphism.ZeroIffImageZero.Read(
						characteristic_zero.IntegerMapHomomorphism.Read(R)).AsFact().At(
						z)))
		})

		toIntegers := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{
				"characteristic_zero(R)",
				"module_independent(restrict_ring(R, integer_image(R)), M, E)",
			},
			Conclusion: "module_independent(int_ring, scalar_restriction(integer_map(R), M), E)",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			M *Expr[ModuleOps[A, B]],
			E *Expr[Set[B]],
			h Fact,
		) {
			r := a.TermAs[RingOps[A]]("R")
			parts := a.Conjuncts(
				h,
				"characteristic zero",
				"independence over the image")
			charZero, independent := parts[0], parts[1]
			a.Do(Simp(
				Fwd(linear_independence.ModuleIndependentDef),
				Fwd(module_record.ScalarRestrictionDef),
				Fwd(int_real_lift.IntRingDef)))
			a.Do(SplitConj(
				Case(
					"the vectors lie in the unchanged module carrier",
					By(
						independent,
						linear_independence.IndependentInCarrier.At(
							a.TermAs[RingOps[A]]("restrict_ring(R, integer_image(R))"), M, E))),
				Case(
					"map a finite integer relation into the image ring",
					Derive(func(b *Argument) {
						T := b.FixAs[Set[B]]("T")
						b.FixAs[Fun[B, Int]]("a")
						relation := b.Assume()
						inImage := b.Have(
							"every mapped integer coefficient lies in the image carrier",
							"∀x:B. x ∈ T ⇒ integer_map(R, a(x)) ∈ restrict_ring(R, integer_image(R)).carrier",
							Simp(Fwd(module_record.RestrictRingDef), Fwd(characteristic_zero.IntegerImageDef)),
							BySets())
						vanish := b.Have(
							"image independence kills every mapped coefficient",
							"∀x:B. x ∈ T ⇒ integer_map(R, a(x)) = R.zero",
							By(
								inImage,
								relation,
								independent,
								At(
									linear_independence.IndependentVanishingCombination,
									b.TermAs[RingOps[A]]("restrict_ring(R, integer_image(R))"),
									M,
									E,
									T,
									b.TermAs[Fun[B, A]]("λx:B. integer_map(R, a(x))")),
								module_record.RestrictRingDef.At(r, b.TermAs[Set[A]]("integer_image(R)"))))
						b.Show(
							"injectivity kills the original integer coefficients",
							By(charZero, R, vanish, At(kernel, r)))
					})),
			))
		})

		fromIntegers := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{
				"characteristic_zero(R)",
				"module_independent(int_ring, scalar_restriction(integer_map(R), M), E)",
			},
			Conclusion: "module_independent(restrict_ring(R, integer_image(R)), M, E)",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			M *Expr[ModuleOps[A, B]],
			E *Expr[Set[B]],
			h Fact,
		) {
			r := a.TermAs[RingOps[A]]("R")
			parts := a.Conjuncts(
				h,
				"characteristic zero",
				"independence over the integers")
			charZero, independent := parts[0], parts[1]
			a.Do(Simp(Fwd(linear_independence.ModuleIndependentDef), Fwd(module_record.RestrictRingDef)))
			a.Do(SplitConj(
				Case(
					"the vectors still lie in the same carrier",
					By(
						independent,
						linear_independence.IndependentInCarrier.At(a.TermAs[RingOps[Int]]("int_ring"),
							a.TermAs[ModuleOps[Int, B]]("scalar_restriction(integer_map(R), M)"), E),
						module_record.ScalarRestrictionDef.At(a.TermAs[Fun[Int, A]]("integer_map(R)"), M))),
				Case(
					"lift a finite image relation to integer coefficients",
					Derive(func(b *Argument) {
						T := b.FixAs[Set[B]]("T")
						b.FixAs[Fun[B, A]]("a")
						relation := b.Assume()
						representatives := b.Have(
							"the chosen integers recover the image coefficients",
							"∀x:B. x ∈ T ⇒ integer_map(R, integer_value(R, a(x))) = a(x)",
							By(relation, At(characteristic_zero.IntegerValueRightInverse, r)))
						equalSums := b.Have(
							"the lifted and original finite relations have equal sums",
							"module_sum(M.add, M.zero, T, λx:B. integer_map(R, integer_value(R, a(x))) • x) = "+
								"module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
							By(
								representatives,
								module.ModuleSumCongruence.At(
									b.TermAs[Op[B]]("M.add"),
									b.TermAs[B]("M.zero"),
									T,
									b.TermAs[Fun[B, B]]("λx:B. integer_map(R, integer_value(R, a(x))) • x"),
									b.TermAs[Fun[B, B]]("λx:B. a(x) • x"))))
						vanish := b.Have(
							"integer independence kills the lifted coefficients",
							"∀x:B. x ∈ T ⇒ integer_value(R, a(x)) = 0",
							By(
								equalSums,
								relation,
								independent,
								At(
									linear_independence.IndependentVanishingCombination,
									b.TermAs[RingOps[Int]]("int_ring"),
									b.TermAs[ModuleOps[Int, B]]("scalar_restriction(integer_map(R), M)"),
									E,
									T,
									b.TermAs[Fun[B, Int]]("λx:B. integer_value(R, a(x))")),
								module_record.ScalarRestrictionDef.At(b.TermAs[Fun[Int, A]]("integer_map(R)"), M),
								int_real_lift.IntRingDef,
								set_basic.InUniv))
						b.Show(
							"the original image coefficients therefore vanish",
							By(Normalized, charZero, R, representatives, vanish, At(kernel, r)))
					})),
			))
		})

		bases := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{"characteristic_zero(R)"},
			Conclusion: "module_basis(restrict_ring(R, integer_image(R)), M, E) ⇔ " +
				"module_basis(int_ring, scalar_restriction(integer_map(R), M), E)",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			M *Expr[ModuleOps[A, B]],
			E *Expr[Set[B]],
			charZero Fact,
		) {
			r := a.TermAs[RingOps[A]]("R")
			a.Show(
				"spanning and independence are both preserved",
				Simp(Fwd(linear_independence.ModuleBasisDef), Fwd(spans), Fwd(module_record.ScalarRestrictionDef)),
				By(
					Normalized,
					R,
					charZero,
					At(toIntegers, r, M, E),
					At(fromIntegers, r, M, E),
					module_record.ScalarRestrictionDef.At(a.TermAs[Fun[Int, A]]("integer_map(R)"), M)))
		})

		finiteGeneration := ctx.Lemma("∀R:ring_ops(A). ∀M:module_ops(A, B). "+
			"    module_finitely_generated(restrict_ring(R, integer_image(R)), M) ⇔ "+
			"    module_finitely_generated(int_ring, scalar_restriction(integer_map(R), M))",
			func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]]) {
				carrier := a.Have(
					"restricting the scalars keeps the carrier",
					"scalar_restriction(integer_map(R), M).carrier = M.carrier",
					Simp(Fwd(module_record.ScalarRestrictionDef), Fwd(module_record.ModCarrierDef)),
					Refl())
				a.Show(
					"the same finite sets span the same carrier",
					Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef), Fwd(spans), Fwd(carrier)),
					Basic())
			})

		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"the ambient ring laws",
				"characteristic zero",
				"the original module laws")
			a.Do(SplitConjAll(
				Case(
					"restriction along the scalar ring map gives an integer module",
					By(
						parts[0],
						parts[2],
						characteristic_zero.IntegerMapIntoImage.At(R),
						hom_module.RestrictScalarsModuleOn.At(
							a.TermAs[RingOps[Int]]("int_ring"),
							a.TermAs[RingOps[A]]("restrict_ring(R, integer_image(R))"),
							a.TermAs[Fun[Int, A]]("integer_map(R)"),
							M),
						module_record.ScalarRestrictionDef.At(a.TermAs[Fun[Int, A]]("integer_map(R)"), M))),
				Case(
					"submodule stability is unchanged",
					By(At(submodules, R, M))),
				Case(
					"every generating set has the same span and basis property",
					By(parts[1], parts[0], At(spans, R, M), At(bases, R, M))),
				Case(
					"finite generation uses the same finite spanning sets",
					By(At(finiteGeneration, R, M))),
			))
		})
	}),
})}

// IntegerRationalImagesStructure — the integer image of a field of
// characteristic zero is a principal ideal domain inside the rational image,
// whose fraction carrier it is. Its ideals are images of ideals of the
// integers, and rational fractions supply the denominators.
var IntegerRationalImagesStructure = integerRationalImagesStructureThm{family.Add(registry.ProofEntry{
	Name: "IntegerRationalImagesStructure",
	Key:  "prop_5addc29668b64398",
	Reading: "The principal ideal domain is the integer image as a ring on a subset " +
		"of L's carrier, not the native integers. Characteristic zero is used only by " +
		"the rational half, the integer image lying in the rational image and being its " +
		"fraction carrier; the integer image of any field is a principal ideal domain.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
		},
		Conclusion: "integer_image(field_ring(L)) ⊆ rational_image(L) ∧ " +
			"subring(field_ring(L), integer_image(field_ring(L))) ∧ " +
			"principal_ideal_domain(«ℤ») ∧ " +
			"fraction_field_carrier(«ℚ», integer_image(field_ring(L)))",
		Abbrev: Abbrev{
			{Name: "ℤ", Text: "restrict_ring(field_ring(L), integer_image(field_ring(L)))"},
			{Name: "ℚ", Text: "restrict_ring(field_ring(L), rational_image(L))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerSubset := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "integer_image(field_ring(L)) ⊆ rational_image(L)",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			R := a.TermAs[RingOps[A]]("field_ring(L)")
			integerValues := a.Have(
				"the rational embedding agrees with the integer map",
				"∀m:int. rational_map(L, real_of_int(m)) = integer_map(field_ring(L), m)",
				By(characteristic_zero.RationalEmbedding.Read(L), characteristic))
			rationalIntegers := a.Have(
				"native integer representatives are rational",
				"∀m:int. rational(real_of_int(m))",
				By(int_construction.RepresentativeIsInteger, rational.IntegerRational))
			a.Show(
				"each integer value is a rational value",
				BySets(
					rationalIntegers,
					integerValues,
					characteristic_zero.IntegerImageDef.At(R),
					characteristic_zero.RationalImageDef.At(l)))
		})
		integerDomain := ctx.Lemma("∀L:field_on(A). "+
			"    integral_domain_on(restrict_ring(field_ring(L), integer_image(field_ring(L))))",
			func(a *Argument, L field.FieldFact[on.L]) {
				R := a.TermAs[RingOps[A]]("field_ring(L)")
				ring := field.RingOn.Read(L)
				inField := a.Have(
					"integer values lie in the field carrier",
					"integer_image(field_ring(L)) ⊆ L.carrier",
					BySets(
						characteristic_zero.IntegerMapInCarrier.Read(ring),
						characteristic_zero.IntegerImageDef.At(R)))
				a.Show(
					"the field supplies distinct zero and one and excludes zero divisors",
					Unfold(integral_domain.IntegralDomainOn),
					By(
						field.OneNotZeroOn.Read(L),
						field.MulEqZeroOn.Read(L),
						characteristic_zero.IntegerImageCommRing.Read(ring),
						inField,
						set_basic.SubsetDef))
			})
		fractionCarrier := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"characteristic_zero(field_ring(L))"},
			Conclusion: "fraction_field_carrier(restrict_ring(field_ring(L), rational_image(L)), " +
				"    integer_image(field_ring(L)))",
		}, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			R := a.TermAs[RingOps[A]]("field_ring(L)")
			ring := field.RingOn.Read(L)
			a.Do(Unfold(field.FractionFieldCarrierDef))
			a.Show(
				"integer values lie in the rational image and supply every rational fraction",
				SplitConj(
					Case(
						"integer values belong to the rational image",
						By(characteristic, L, At(integerSubset, l))),
					Case(
						"a rational value has an integer numerator and nonzero integer denominator",
						Derive(func(b *Argument) {
							b.FixAs[A]("z")
							inImage := b.Assume()
							u, represented := b.ObtainAs[Real](
								"choose a rational representative",
								"∃u:real. rational(u) ∧ z = rational_map(L, u)",
								BySets(inImage, characteristic_zero.RationalImageDef.At(l)))
							m, d, fraction := b.Obtain2As[Int, Nat](
								"write the representative as an integer fraction",
								"∃m:int. ∃d:num. 0 < d ∧ u = real_of_int(m) / real_of_num(d)",
								By(represented, characteristic_zero.RationalIntegerFraction.At(u)))
							numerator := b.TermAs[A]("integer_map(field_ring(L), m)")
							denominator := b.TermAs[A]("integer_map(field_ring(L), d)")
							value := b.Have(
								"evaluate the fraction in the host field",
								"z = L.mul(integer_map(field_ring(L), m), L.inv(integer_map(field_ring(L), d)))",
								By(characteristic, represented, fraction, characteristic_zero.RationalMapFraction.Read(L).At(m, d)))
							nonzero := b.Have(
								"characteristic zero keeps the positive denominator nonzero",
								"integer_map(field_ring(L), d) ≠ L.zero",
								By(characteristic, fraction, characteristic_zero.IntegerMapPositiveNonzero.Read(ring).At(d)))
							integerValues := b.Have(
								"the numerator and denominator are integer values",
								"integer_map(field_ring(L), m) ∈ integer_image(field_ring(L)) ∧ "+
									"integer_map(field_ring(L), d) ∈ integer_image(field_ring(L))",
								BySets(characteristic_zero.IntegerImageDef.At(R)))
							inCarrier := characteristic_zero.IntegerMapInCarrier.Read(ring)
							numeratorIn, denominatorIn := inCarrier.At(m), inCarrier.At(b.TermAs[Int]("d"))
							inverse := field.InvIn.Read(L).AsFact().At(denominator)
							inField := b.Have(
								"the represented rational value lies in the field carrier",
								"z ∈ L.carrier",
								By(Normalized, comm_ring.MulIn.Read(ring), value, numeratorIn, denominatorIn, inverse))
							cleared := b.Have(
								"multiply the represented value by its denominator",
								"L.mul(z, integer_map(field_ring(L), d)) = integer_map(field_ring(L), m)",
								ByArith(
									L,
									nonzero,
									Scaled(denominator, value),
									inField,
									numeratorIn,
									denominatorIn,
									inverse,
									Scaled(numerator, field.MulLeftInverseOn.Read(L).AsFact().At(denominator))))
							b.Take(numerator)
							b.Take(denominator)
							b.Show(
								"these integer values give the fraction carrier witnesses",
								By(nonzero, cleared, integerValues))
						}))))
		})
		return ctx.Theorem(headline, func(a *Argument, L field.FieldFact[on.L], characteristic Fact) {
			l := a.TermAs[FieldOps[A]]("L")
			domain := a.Have(
				"the integer image is an integral domain",
				"integral_domain_on(restrict_ring(field_ring(L), integer_image(field_ring(L))))",
				By(L, At(integerDomain, l)))
			R := a.TermAs[RingOps[A]]("field_ring(L)")
			integerMap := a.Have(
				"the integer map is a ring homomorphism from the integers to the integer image",
				"ring_homomorphism(int_ring, "+
					"    restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
					"    integer_map(field_ring(L)))",
				By(characteristic_zero.IntegerMapIntoImage.Read(field.RingOn.Read(L))))
			onto := a.Have(
				"its values are the whole integer image",
				"image(integer_map(field_ring(L)), ring_carrier(int_ring)) = integer_image(field_ring(L))",
				BySets(characteristic_zero.IntegerImageDef.At(R)))
			principal := a.Have(
				"so every ideal of the integer image is principal, as every ideal of the integers is",
				"principal_ideal_domain(restrict_ring(field_ring(L), integer_image(field_ring(L))))",
				Unfold(principal_ideal_domain.PrincipalIdealDomainDef),
				By(
					domain,
					onto,
					IntegerRingPrincipalIdealDomain,
					principal_ideal_domain.SurjectiveImageIdealsPrincipal.Read(integerMap)))
			ring := field.RingOn.Read(L)
			inField := a.Have(
				"integer values lie in the field carrier",
				"integer_image(field_ring(L)) ⊆ L.carrier",
				BySets(
					characteristic_zero.IntegerMapInCarrier.Read(ring),
					characteristic_zero.IntegerImageDef.At(R)))
			subring := a.Have(
				"so the integer image, a ring under the field's operations, is a subring of the field",
				"subring(field_ring(L), integer_image(field_ring(L)))",
				By(
					inField,
					integral_domain.Ring.Read(domain),
					comm_ring.SubringRingOn.Read(ring).At(a.TermAs[Set[A]]("integer_image(field_ring(L))"))))
			a.Show(
				"assemble the integer ring and its rational fraction carrier",
				SplitConj(
					Case(
						"the integer image is a principal ideal domain inside the rational image",
						By(subring, characteristic, L, principal, At(integerSubset, l))),
					Case(
						"the rational image is the fraction carrier of the integer image",
						By(characteristic, L, At(fractionCarrier, l)))))
		})
	}),
})}

// IntegerRationalImageModules — a field of characteristic zero is a module
// over its integer image and a vector space over its rational image: both
// images are subrings of the field (the rational one a subfield), and
// restricting the scalars of the field's regular module to either keeps a
// module.
var IntegerRationalImageModules = integerRationalImageModulesThm{family.Add(registry.ProofEntry{
	Name: "IntegerRationalImageModules",
	Key:  "prop_f83c0ea29acad726",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A).",
		Hypotheses: []string{"characteristic_zero(field_ring(L))"},
		Conclusion: "module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"    regular_module(field_ring(L))) ∧ " +
			"module_on(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)))",
	}, func(a *Argument, L field.FieldFact[on.L], h Fact) {
		integers := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		rationals := a.TermAs[Set[A]]("rational_image(L)")
		images := a.Have(
			"the integer scalars form a ring inside the rational subfield",
			"subfield(L, rational_image(L)) ∧ "+
				"integer_image(field_ring(L)) ⊆ rational_image(L) ∧ "+
				"subring(field_ring(L), integer_image(field_ring(L)))",
			By(characteristic_zero.RationalEmbedding.Read(L), IntegerRationalImagesStructure.Read(L), h))
		rationalSubring := a.Have(
			"the rational subfield is a subring of the field",
			"subring(field_ring(L), rational_image(L))",
			By(images, field.SubfieldSubring.Read(L).At(rationals)))
		integerModule := a.Have(
			"the ambient field is a module over its integer image",
			"module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)))",
			By(images, module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(integers)))
		rationalModule := a.Have(
			"the ambient field is a module over its rational image",
			"module_on(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)))",
			By(rationalSubring, module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(rationals)))
		a.Show(
			"the field is a module over both images",
			By(integerModule, rationalModule))
	}),
})}
