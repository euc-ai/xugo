// rationality.go — the numerator of the zeta series, from the class-count tail,
// and its functional equation, from the canonical pairing of classes.

package curve_zeta

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve_riemann_roch"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ZetaNumeratorRationality — the numerator of the zeta function of a smooth
// curve over a finite field is an integer polynomial of degree at most 2g with
// constant term one, its value at one is the class number, and it is (1 − T)(1 −
// qT) times the series of effective counts. The counts start at one, vanish in
// negative degrees and, the divisor index being one, follow the Riemann–Roch tail
// in every degree past 2g − 2, which are the hypotheses of the general numerator
// law; the counts being natural numbers, the coefficient formula writes each
// coefficient of the numerator as the value of an integer.
var ZetaNumeratorRationality = zetaNumeratorRationalityThm{family.Add(registry.ProofEntry{
	Name: "ZetaNumeratorRationality",
	Key:  "prop_35109559a394ce4c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "polynomial_over(real_of_num(0), image(real_of_int, 𝕌), «numerator») ∧ " +
			"«numerator»(0) = real_of_num(1) ∧ " +
			"polynomial_degree(real_of_num(0), «numerator») ≤ 2 * «genus» ∧ " +
			"(∀n:num. 2 * «genus» < n ⇒ «numerator»(n) = real_of_num(0)) ∧ " +
			"polynomial_eval(real_add, " +
			"    real_of_num(0), " +
			"    real_mul, " +
			"    real_of_num(1), " +
			"    «numerator», " +
			"    real_of_num(1)) = " +
			"real_of_num(card(«picZero»)) ∧ " +
			"polynomial_mul(real_add, " +
			"    real_of_num(0), " +
			"    real_mul, " +
			"    polynomial_mul(real_add, real_of_num(0), real_mul, «1−T», «1−qT»), " +
			"    «zeta») = " +
			"«numerator»",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		functionField := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		atLeastTwo := a.Have(
			"k is a finite subfield of M, so it has more than one element",
			"1 < card(k)",
			By(curve, ConstantsAtLeastTwo.Read(functionField).At(k, A0, A1, A01, t)))
		startsAtOne := a.Have(
			"the series of effective counts starts at one",
			"«effective»(0) = real_of_num(1)",
			By(
				algebraicallyClosed,
				inField,
				curve,
				ZetaEulerProductAndLogDerivative.Read(M).At(K, k, A0, A1, A01, t),
				formal_series.SeriesRecurrenceDef,
				real_ring.RealRingDef))
		noNegativeDegree := a.Have(
			"no effective divisor has negative degree",
			"∀n:int. n < 0 ⇒ «effective»(n) = real_of_num(0)",
			By(CurveEffectiveCountDef))
		riemannRochTail := a.Have(
			"past 2g − 2 the effective counts follow the Riemann–Roch tail",
			Statement{
				Binders: "∀n:int.",
				Hypotheses: []string{
					"2 * «genus» - int_of_num(2) < n",
				},
				Conclusion: "real_of_num(card(k) - 1) * «effective»(n) = " +
					"real_of_num(card(«picZero»)) * " +
					"(real_zpow(«q», n + int_of_num(1) - int_of_num(«genus»)) - real_of_num(1))",
			},
			Derive(func(b *Argument) {
				n := b.FixAs[Int]("n")
				past := b.Assume()
				multiple := b.Have(
					"the divisor index is one, so every degree is a multiple of it",
					"int_of_num(«index») ∣ n",
					Simp(Fwd(int_divides.IntDividesDef)),
					Witness(n),
					ByArith(
						algebraicallyClosed,
						inField,
						curve,
						DegreeOneDivisorExists.Read(M).At(K, k, A0, A1, A01, t)))
				b.Show(
					"a degree the index divides has h classes, each counted by one geometric term",
					By(
						curve,
						multiple,
						past,
						b.Simplified(
							EffectiveCountTail.Read(functionField).At(k, A0, A1, A01, t, n),
							curve_point_count.InAmbient)))
			}))
		riemannRoch := a.Conjuncts(
			GroupPremises(atLeastTwo, startsAtOne, noNegativeDegree, riemannRochTail, real_formal_series.RiemannRochNumerator.At(
				a.TermAs[Nat]("card(k)"),
				a.TermAs[Nat]("«genus»"),
				a.TermAs[Nat]("card(«picZero»)"),
				a.TermAs[Fun[Int, Real]]("«effective»"))),
			"the coefficient sequence vanishes past 2g",
			"it is the product of (1 − T)(1 − qT) and the effective series",
			"its constant term is one",
			"its value at one is h")
		numerator := a.Have(
			"the numerator is that coefficient sequence",
			"«numerator» = zeta_numerator_coefficient(card(k), «effective»)",
			Cite(CurveZetaNumeratorDef))
		vanishing := a.Have(
			"the numerator vanishes past 2g",
			"∀n:num. 2 * «genus» < n ⇒ «numerator»(n) = real_of_num(0)",
			numerator.Rw(),
			By(riemannRoch[0]))
		bounded := a.Have(
			"so it is a vector of length 2g + 1",
			"vec⟨suc(2 * «genus»)⟩(real_of_num(0), «numerator»)",
			By(vanishing, vec_space.VecDef, nat_order.SucLessEqIffLessThan))
		naturals := a.Have(
			"each effective count is a natural number",
			"∀z:int. ∃m:num. «effective»(z) = real_of_num(m)",
			a.ForEach(func(_ *Expr[Int]) Action {
				return By(CurveEffectiveCountDef)
			}))
		integers := a.Have(
			"so each coefficient of the numerator is an integer",
			"∀n:num. «numerator»(n) ∈ image(real_of_int, 𝕌)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				_, first := b.UnpackAs[Nat](naturals.At(b.TermAs[Int]("n")), "m₀")
				_, second := b.UnpackAs[Nat](naturals.At(b.TermAs[Int]("&n - 1")), "m₁")
				_, third := b.UnpackAs[Nat](naturals.At(b.TermAs[Int]("&n - 2")), "m₂")
				w, wDef := b.LetAs[Int](
					"w", "int_of_num(m₀) - (card(k) + 1) * int_of_num(m₁) + int_of_num(card(k)) * int_of_num(m₂)")
				value := b.Have(
					"the coefficient formula at these three counts is the image of the integer w",
					"«numerator»(n) = real_of_int(w)",
					wDef.Rw(),
					numerator.Rw(),
					Simp(
						Fwd(real_formal_series.ZetaNumeratorCoefficientDef),
						Fwd(first),
						Fwd(second),
						Fwd(third),
						Fwd(int_construction.AddBridge),
						Fwd(int_construction.SubBridge),
						Fwd(int_construction.MulBridge),
						Fwd(int_construction.OfNumBridge)),
					Basic())
				b.Show(
					"and a value of real_of_int lies in its range",
					By(value, set_image.FunInRange.At(b.TermAs[Fun[Int, Real]]("real_of_int"), w)))
			}))
		a.Show(
			"the six clauses of the statement",
			SplitConjAll(
				Case(
					"the numerator is a polynomial with integer coefficients",
					By(bounded, integers, polynomial.PolynomialOverDef)),
				Case(
					"its constant term is one",
					numerator.Rw(),
					By(riemannRoch[2])),
				Case(
					"its degree is at most 2g, the least index past which it vanishes",
					By(bounded, polynomial.DegreeLeast)),
				Case(
					"it vanishes past 2g",
					By(vanishing)),
				Case(
					"its value at one is the class number",
					numerator.Rw(),
					By(riemannRoch[3])),
				Case(
					"it is (1 − T)(1 − qT) times the effective series",
					numerator.Rw(),
					By(riemannRoch[1]))))
	}),
})}

// CanonicalClassCountingSymmetry — the effective counts in degrees n and 2g − 2 − n
// determine each other through the class number: the Riemann–Roch symmetry summed
// over classes. The divisor index is one, so there are h classes of degree n, and
// the class of the canonical divisor κ times the inverse of a class pairs them with
// the classes of the reflected degree. On the class of a closed divisor D the two
// counts are the lines of sections of D and of κ − D, and Riemann–Roch relates the
// sizes of those spaces by the factor z = q^(n + 1 − g), so each class contributes
// z − 1 to the sum over the h classes.
var CanonicalClassCountingSymmetry = canonicalClassCountingSymmetryThm{family.Add(registry.ProofEntry{
	Name: "CanonicalClassCountingSymmetry",
	Key:  "prop_557f86447ddb92e8",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "«lessOne» * («effective»(n) - «z» * «effective»(«reflected»)) = " +
			"real_of_num(card(«picZero»)) * («z» - real_of_num(1))",
		Abbrev: Abbrev{
			{Name: "z", Text: "real_zpow(«q», n + int_of_num(1) - int_of_num(«genus»))"},
			{Name: "reflected", Text: "2 * «genus» - int_of_num(2) - n"},
			{Name: "lessOne", Text: "real_of_num(card(k) - 1)"},
			{Name: "canonical", Text: "curve_canonical_divisor(restrict_field(M, K), k, t, A₀, A₁, A₀₁)"},
			{Name: "complement", Text: "λc:set(prod(set(A), set(A))). " +
				"    curve_class_mul(«functionRing», " +
				"        A₀, " +
				"        A₁, " +
				"        «class»(«canonical»), " +
				"        curve_class_inverse(«functionRing», A₀, A₁, c))"},
			{Name: "inClass", Text: "λc:set(prod(set(A), set(A))). card(«effectiveInClass»(c))"},
			{Name: "inComplement", Text: "λc:set(prod(set(A), set(A))). " +
				"    card(«effectiveInClass»(«complement»(c)))"},
			{Name: "realInClass", Text: "λc:set(prod(set(A), set(A))). real_of_num(«inClass»(c))"},
			{Name: "realInComplement", Text: "λc:set(prod(set(A), set(A))). real_of_num(«inComplement»(c))"},
			{Name: "scaledComplement", Text: "λc:set(prod(set(A), set(A))). «z» * «realInComplement»(c)"},
			{Name: "gap", Text: "λc:set(prod(set(A), set(A))). «realInClass»(c) - «z» * «realInComplement»(c)"},
			{Name: "scaledGap", Text: "λc:set(prod(set(A), set(A))). «lessOne» * «gap»(c)"},
			{Name: "contribution", Text: "λc:set(prod(set(A), set(A))). «z» - real_of_num(1)"},
			{Name: "canonicalMinus", Text: "λD:(prod(set(A), set(A)) → int). λP:prod(set(A), set(A)). " +
				"    «canonical»(P) - D(P)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Int],
			algebraicallyClosed, inField, curve Fact,
		) {
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			canonical := a.TermAs[_Divisor]("«canonical»")
			model := a.Conjuncts(
				a.Simplified(
					GroupPremises(
						curve, smooth_curve_riemann_roch.CanonicalDivisorModel.Read(functionField).At(k, A0, A1, A01, t)),
					curve_point_count.InAmbient),
				"the canonical divisor κ is a closed divisor",
				"its pair is a dualizing model",
				"of degree 2g − 2",
				"and the dual of a closed divisor D has the dimension of the sections of κ − D")
			multiple := a.Have(
				"the divisor index is one, so every degree is a multiple of it",
				"int_of_num(«index») ∣ n",
				Simp(Fwd(int_divides.IntDividesDef)),
				Witness(n),
				ByArith(
					algebraicallyClosed,
					inField,
					curve,
					DegreeOneDivisorExists.Read(M).At(K, k, A0, A1, A01, t)))
			sized := a.Conjuncts(
				a.Have(
					"so there are h classes of degree n",
					"finite(«classes»(n)) ∧ card(«classes»(n)) = card(«picZero»)",
					By(
						curve,
						multiple,
						a.Simplified(
							GroupPremises(curve, DivisorDegreeClasses.Read(functionField).At(k, A0, A1, A01, t)),
							curve_point_count.InAmbient))),
				"finitely many classes have degree n",
				"namely h")
			bijection := a.Conjuncts(
				a.Have(
					"the complement in κ carries them one-to-one onto the classes of degree 2g − 2 − n",
					"injective_on(«classes»(n), «complement») ∧ "+
						"image(«complement», «classes»(n)) = «classes»(«reflected»)",
					By(
						model[2],
						curve,
						model[0],
						a.Simplified(
							ClassComplementBijection.Read(functionField).At(k, A0, A1, A01, t, canonical, n),
							curve_point_count.InAmbient))),
				"the complement is one-to-one on the classes of degree n",
				"its image is the classes of degree 2g − 2 − n")
			atLeastTwo := a.Have(
				"the constants are a finite subfield, of at least two elements",
				"1 < card(k)",
				By(curve, ConstantsAtLeastTwo.Read(functionField).At(k, A0, A1, A01, t)))
			q := a.TermAs[Real]("«q»")
			constantCount := a.TermAs[Nat]("card(k)")
			cast := a.Have(
				"so subtracting one from a power of q is exact, and casts to ℝ",
				"∀s:num. real_of_num(card(k) ^ s - 1) = «q» ^ s - real_of_num(1)",
				Derive(func(b *Argument) {
					s := b.FixAs[Nat]("s")
					exact := b.Have(
						"q^s is at least one",
						"card(k) ^ s = (card(k) ^ s - 1) + 1",
						ByArith(atLeastTwo, nat_order.PowPositive.At(constantCount, s)))
					b.Show(
						"the cast crosses the sum and the power",
						ByArith(
							exact,
							real_pow.OfNumPow.At(constantCount, s),
							real_construction.OfNumAdd.At(b.TermAs[Nat]("card(k) ^ s - 1"), b.TermAs[Nat]("1"))))
				}))
			counted := a.Have(
				"in ℝ, q − 1 times the effective divisors of the class of a closed divisor E is q^ℓ(E) − 1",
				Statement{
					Binders:    "∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"«divisor»(E)"},
					Conclusion: "«lessOne» * «realInClass»(«class»(E)) = «q» ^ «sections»(E) - real_of_num(1)",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[_Divisor]("E")
					divisor := b.Assume()
					b.Show(
						"the lines of sections count them in ℕ, and the cast crosses the product",
						By(
							curve,
							divisor,
							b.Simplified(
								EffectiveDivisorsInClass.Read(functionField).At(k, A0, A1, A01, t, E),
								curve_point_count.InAmbient),
							cast.At(b.TermAs[Nat]("«sections»(E)")),
							real_construction.OfNumMul.At(
								b.TermAs[Nat]("card(k) - 1"),
								b.TermAs[Nat]("card(«effectiveInClass»(«class»(E)))"))))
				}))
			nonzero := a.Have(
				"q is not zero",
				"«q» ≠ real_of_num(0)",
				ByArith(atLeastTwo))
			pointwise := a.Have(
				"each class of degree n contributes z − 1",
				"∀c:set(prod(set(A), set(A))). c ∈ «classes»(n) ⇒ «lessOne» * «gap»(c) = «z» - real_of_num(1)",
				Derive(func(b *Argument) {
					c := b.FixAs[_Class]("c")
					D, represented := b.ObtainAs[_Divisor](
						"c is the class of a closed divisor D of degree n",
						"∃D:prod(set(A), set(A)) → int. «divisor»(D) ∧ «degree»(D) = n ∧ «class»(D) = c",
						By(
							b.Assume(),
							curve,
							b.Simplified(
								GroupPremises(curve, InDegreeClasses.Read(functionField).At(k, A0, A1, A01, t, n, c)),
								curve_point_count.InAmbient)))
					given := b.Conjuncts(
						represented,
						"D is a closed divisor",
						"of degree n",
						"c is its class")
					canonicalMinusD := b.TermAs[_Divisor]("«canonicalMinus»(D)")
					divisorCanonicalMinusD := b.Have(
						"κ − D is a closed divisor",
						"«divisor»(«canonicalMinus»(D))",
						By(
							curve,
							model[0],
							given[0],
							b.Simplified(
								closed_divisor.ClosedDivisorSub.Read(functionField).At(k, A0, A1, A01, t, canonical, D),
								curve_point_count.InAmbient)))
					complementary := b.Have(
						"the complement of c is the class of κ − D",
						"«complement»(c) = «class»(«canonicalMinus»(D))",
						given[2].RwRev(),
						By(
							curve,
							model[0],
							given[0],
							b.Simplified(
								smooth_curve_riemann_roch.ClassOfDifference.Read(functionField).At(k, A0, A1, A01, t, canonical, D),
								curve_point_count.InAmbient)))
					atD := b.Have(
						"the count of c",
						"«lessOne» * «realInClass»(c) = «q» ^ «sections»(D) - real_of_num(1)",
						By(counted.At(D), given[2], given[0]))
					atComplement := b.Have(
						"the count of its complement",
						"«lessOne» * «realInComplement»(c) = «q» ^ «sections»(«canonicalMinus»(D)) - real_of_num(1)",
						By(counted.At(canonicalMinusD), complementary, divisorCanonicalMinusD))
					riemannRoch := b.Have(
						"Riemann–Roch for D: ℓ(D) is n + 1 − g more than ℓ(κ − D)",
						"int_of_num(«sections»(D)) = "+
							"(n + 1 - int_of_num(«genus»)) + int_of_num(«sections»(«canonicalMinus»(D)))",
						ByArith(
							given[1],
							curve,
							given[0],
							b.Simplified(
								smooth_curve_riemann_roch.RiemannRochClosedDivisors.Read(functionField).At(k, A0, A1, A01, t, D),
								curve_point_count.InAmbient)))
					power := b.Have(
						"so the integer power z scales q^ℓ(κ−D) to q^ℓ(D)",
						"«z» * «q» ^ «sections»(«canonicalMinus»(D)) = «q» ^ «sections»(D)",
						By(
							riemannRoch,
							nonzero,
							real_zpow.ZpowAdd.At(
								q,
								b.TermAs[Int]("n + &1 - int_of_num(«genus»)"),
								b.TermAs[Int]("«sections»(«canonicalMinus»(D))")),
							real_zpow.ZpowOfNum.At(q, b.TermAs[Nat]("«sections»(«canonicalMinus»(D))")),
							real_zpow.ZpowOfNum.At(q, b.TermAs[Nat]("«sections»(D)"))))
					b.Show(
						"(q^ℓ(D) − 1) − z·(q^ℓ(κ−D) − 1) is z − 1",
						ByArith(atD, Scaled(b.TermAs[Real]("«z»"), atComplement), power))
				}))
			classes := a.TermAs[Set[_Class]]("«classes»(n)")
			complement := a.TermAs[Fun[_Class, _Class]]("«complement»")
			inClass := a.TermAs[Fun[_Class, Nat]]("«inClass»")
			throughImage := a.Have(
				"a sum over the image of a one-to-one map runs over its source",
				"sum(image(«complement», «classes»(n)), «inClass») = sum(«classes»(n), «inClass» ∘ «complement»)",
				By(bijection[0], nat_sum.Image.At(classes, complement, inClass)))
			reindexed := a.Have(
				"so the classes of degree 2g − 2 − n count as their complements "+
					"of degree n, the composite with the complement read pointwise",
				"sum(«classes»(«reflected»), «inClass») = sum(«classes»(n), «inComplement»)",
				bijection[1].RwRev(),
				throughImage.Rw(),
				Unfold(functions.ComposeApply))
			total := a.Have(
				"the effective count of degree n is the sum over its classes",
				"«effective»(n) = sum(«classes»(n), «realInClass»)",
				By(
					sized[0],
					curve,
					a.Simplified(
						GroupPremises(curve, EffectiveCountOverClasses.Read(functionField).At(k, A0, A1, A01, t, n)),
						curve_point_count.InAmbient),
					real_sum.RealOfNatSum.At(classes, inClass)))
			totalReflected := a.Have(
				"and that of degree 2g − 2 − n the same sum over the complements",
				"«effective»(«reflected») = sum(«classes»(n), «realInComplement»)",
				By(
					reindexed,
					sized[0],
					curve,
					a.Simplified(
						GroupPremises(
							curve,
							EffectiveCountOverClasses.Read(functionField).At(k, A0, A1, A01, t, a.TermAs[Int]("«reflected»"))),
						curve_point_count.InAmbient),
					real_sum.RealOfNatSum.At(classes, a.TermAs[Fun[_Class, Nat]]("«inComplement»"))))
			z := a.TermAs[Real]("«z»")
			lessOne := a.TermAs[Real]("«lessOne»")
			realInClass := a.TermAs[Fun[_Class, Real]]("«realInClass»")
			realInComplement := a.TermAs[Fun[_Class, Real]]("«realInComplement»")
			scaledComplement := a.TermAs[Fun[_Class, Real]]("«scaledComplement»")
			gap := a.TermAs[Fun[_Class, Real]]("«gap»")
			scaledGap := a.TermAs[Fun[_Class, Real]]("«scaledGap»")
			contribution := a.TermAs[Fun[_Class, Real]]("«contribution»")
			difference := a.Have(
				"the sum of the differences is the difference of the sums",
				"sum(«classes»(n), «realInClass») - «z» * sum(«classes»(n), «realInComplement») = "+
					"sum(«classes»(n), «gap»)",
				By(
					sized[0],
					real_sum.ScalarLeft.At(z, realInComplement, classes),
					real_sum.Sub.At(classes, realInClass, scaledComplement)))
			a.Show(
				"the linear combination is a sum over the h classes of the constant z − 1",
				CalcEq(
					Leg(
						a.TermAs[Real]("«lessOne» * sum(«classes»(n), «gap»)"),
						"the counts are the sums, and their combination is the sum of the differences",
						By(total, totalReflected, difference)),
					Leg(
						a.TermAs[Real]("sum(«classes»(n), «scaledGap»)"),
						"q − 1 enters the sum",
						Cite(real_sum.ScalarLeft, lessOne, gap, classes)),
					Leg(
						a.TermAs[Real]("sum(«classes»(n), «contribution»)"),
						"each term is z − 1",
						By(pointwise, real_sum.Congruence.At(classes, scaledGap, contribution))),
					FinalLeg(
						"a constant over h classes is h times it",
						By(sized[0], sized[1], real_sum.Const.At(classes, a.TermAs[Real]("«z» - real_of_num(1)"))))))
		}),
})}

// CurveZetaFunctionalEquation — the numerator of the zeta function of a smooth
// curve over a finite field has degree exactly 2g, its top coefficient is q^g,
// and its coefficients pair across 2g by powers of q. The class-count symmetry of
// the canonical class is the hypothesis of coefficient reciprocity, which gives
// the pairing; at n = 0 the constant term one makes the top coefficient q^g, and
// that does not vanish, so the degree, which is at most 2g, is 2g, the genus-zero
// case included.
var CurveZetaFunctionalEquation = curveZetaFunctionalEquationThm{family.Add(registry.ProofEntry{
	Name: "CurveZetaFunctionalEquation",
	Key:  "prop_9d4820baa30448a3",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "polynomial_degree(real_of_num(0), «numerator») = 2 * «genus» ∧ " +
			"«numerator»(2 * «genus») = «q» ^ «genus» ∧ " +
			"(∀n:num. " +
			"    n ≤ 2 * «genus» ⇒ «q» ^ «genus» * «numerator»(n) = «q» ^ n * «numerator»(2 * «genus» - n))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		rational := a.Conjuncts(
			GroupPremises(inField, curve, ZetaNumeratorRationality.Read(M).At(K, k, A0, A1, A01, t)),
			"the numerator is a polynomial with integer coefficients",
			"its constant term is one",
			"its degree is at most 2g",
			"it vanishes past 2g",
			"its value at one is the class number",
			"it is (1 − T)(1 − qT) times the effective series")
		functionField := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		large := a.Have(
			"k is a finite subfield of M, so it has more than one element",
			"1 < card(k)",
			By(curve, ConstantsAtLeastTwo.Read(functionField).At(k, A0, A1, A01, t)))
		numerator := a.Have(
			"the numerator is the coefficient sequence of the effective counts",
			"«numerator» = zeta_numerator_coefficient(card(k), «effective»)",
			Cite(CurveZetaNumeratorDef))
		genus := a.TermAs[Nat]("«genus»")
		reciprocity := a.Have(
			"the class-count symmetry pairs the coefficients of the numerator across 2g",
			"∀n:num. n ≤ 2 * «genus» ⇒ «q» ^ «genus» * «numerator»(n) = «q» ^ n * «numerator»(2 * «genus» - n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				low := b.Assume()
				b.Show(
					"coefficient reciprocity reads the symmetry of the canonical class in every degree",
					By(
						algebraicallyClosed,
						inField,
						curve,
						numerator,
						large,
						low,
						CanonicalClassCountingSymmetry.Read(M),
						real_formal_series.RiemannRochReciprocity.At(
							b.TermAs[Nat]("card(k)"),
							genus,
							b.TermAs[Nat]("card(«picZero»)"),
							b.TermAs[Fun[Int, Real]]("«effective»"),
							n)))
			}))
		top := a.Have(
			"at n = 0 the constant term one makes the top coefficient q^g",
			"«numerator»(2 * «genus») = «q» ^ «genus»",
			ByArith(reciprocity.At(a.TermAs[Nat]("0")), rational[1], real_pow.PowExpZeroClause))
		nonzero := a.Have(
			"which is a positive power, so it does not vanish",
			"«numerator»(2 * «genus») ≠ real_of_num(0)",
			ByArith(top, large, real_pow.PowPos.At(a.TermAs[Real]("«q»"), genus)))
		bounded := a.Have(
			"the numerator vanishes past 2g, so it is a vector of length 2g + 1",
			"vec⟨suc(2 * «genus»)⟩(real_of_num(0), «numerator»)",
			By(rational[3], vec_space.VecDef, nat_order.SucLessEqIffLessThan))
		degree := a.Have(
			"hence 2g is the index of its last nonzero coefficient",
			"polynomial_degree(real_of_num(0), «numerator») = 2 * «genus»",
			By(rational[0], bounded, nonzero, polynomial.DegreeExact))
		a.Show(
			"these are the three clauses of the statement",
			By(degree, top, reciprocity))
	}),
})}
