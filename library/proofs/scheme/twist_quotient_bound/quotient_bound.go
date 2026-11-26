package twist_quotient_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/fixed_twist_models"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/scheme/twisted_count"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// subgroupAverageBounds — the real estimate of InvariantChartPointsNearPower, which
// reads it at a subgroup H of G and the rest of G: gc, h and rc are |G|, |H| ≥ 1 and
// the size of the rest; SG, SH and SR the sums of the twisted counts over G, over H
// and over the rest; n the points of the invariant chart and g the good base points,
// the sums over H and over G being h·n and gc·g; q is Q = card(k)^m, b the constant
// B₁, p = √Q and d = deg a. If each twisted count is at most c = q + b·p and
// q ≤ g + d, then n is within c above and gc·d + gc·(b·p) below q. Above, the sum
// over H is at most h·c. Below, gc·q ≤ gc·g + gc·d, and taking the rest off at c
// leaves h·q ≤ h·n + rc·(b·p) + gc·d.
var subgroupAverageBounds = subgroupAverageBoundsThm{family.Add(registry.ProofEntry{
	Name: "subgroupAverageBounds",
	Key:  "prop_d9909ad1544eaee5",
	Build: family.Theorem(Statement{
		Binders: "∀gc h rc SH SG SR n g q b p d:real.",
		Hypotheses: []string{
			"gc = h + rc",
			"real_of_num(1) ≤ h",
			"real_of_num(0) ≤ rc",
			"SH = h * n",
			"SG = gc * g",
			"SG = SH + SR",
			"SH ≤ h * (q + b * p)",
			"SR ≤ rc * (q + b * p)",
			"q ≤ g + d",
			"real_of_num(0) ≤ b",
			"real_of_num(1) ≤ p",
			"real_of_num(0) ≤ d",
		},
		Conclusion: "n ≤ q + b * p ∧ q ≤ n + gc * d + gc * (b * p)",
	},
		func(
			a *Argument,
			gc, h, rc, SH, SG, SR, n, g, q, b, p, d *Expr[Real],
			total, large, restSign, sumH, sumG, split, boundH, boundRest, lower, bSign, pLarge, dSign Fact,
		) {
			product := a.TermAs[Real]("b * p")
			scaled := a.Have(
				"q ≤ g + d scales by gc",
				"gc * q ≤ gc * g + gc * d",
				ByArith(lower, total, large, restSign))
			cross := a.Have(
				"taking the rest off at c leaves the part",
				"h * q ≤ h * n + rc * (b * p) + gc * d",
				ByArith(scaled, split, sumG, sumH, Scaled(q, total), boundRest))
			sign := a.Have(
				"b p is not negative",
				"real_of_num(0) ≤ b * p",
				ByArith(bSign, pLarge))
			smaller := a.Have(
				"so the rest of it lies under gc",
				"rc * (b * p) ≤ gc * (b * p)",
				ByArith(Scaled(product, total), large, sign))
			errorSign := a.Have(
				"the error is not negative",
				"real_of_num(0) ≤ gc * d + gc * (b * p)",
				ByArith(Scaled(d, total), Scaled(product, total), large, restSign, sign, dSign))
			grown := a.Have(
				"so it lies under its multiple by h",
				"gc * d + gc * (b * p) ≤ h * (gc * d + gc * (b * p))",
				ByArith(large, errorSign))
			crossed := a.Have(
				"so h q is at most h times n and the error",
				"h * q ≤ h * (n + gc * d + gc * (b * p))",
				ByArith(cross, smaller, grown))
			above := a.Have(
				"the sum over the part is at most h c",
				"h * n ≤ h * (q + b * p)",
				ByArith(sumH, boundH))
			a.Do(SplitConj(
				Case(
					"h cancels above",
					ByArith(above, large)),
				Case(
					"and below",
					ByArith(crossed, large))))
		}),
})}

// GoodBaseCountLower — all but at most deg a points of the field of card(k)^m
// elements are good base points, a nonzero polynomial having at most its degree many
// roots.
var GoodBaseCountLower = goodBaseCountLowerThm{family.Add(registry.ProofEntry{
	Name: "GoodBaseCountLower",
	Key:  "prop_e47062ec9e4269f8",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀a:(num → A). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"polynomial_over(k, a)",
			"a ≠ vec_zero",
			"0 < m",
		},
		Conclusion: "card(k) ^ m ≤ " +
			"good_base_count(field_ring(M), k, a, card(k) ^ m) + polynomial_degree(a)",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "good", Text: "{x:A | " +
				"    x ∈ M.carrier ∧ " +
				"    monoid_pow(M.mul, M.one, x, card(k) ^ m) = x ∧ " +
				"    polynomial_eval(a, x) ≠ M.zero}"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			a *Arrow[Nat, A],
			m *Expr[Nat],
			closed, subfieldK, finiteK, over, nonzero, positive Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
			zero := arg.TermAs[A]("M.zero")
			constants := arg.TermAs[Set[A]]("«constants»")
			goodSet := arg.TermAs[Set[A]]("«good»")
			rootSet := arg.TermAs[Set[A]]("polynomial_roots(M.carrier, a)")
			order := arg.TermAs[Nat]("card(k)")
			kInField := arg.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subfieldK, field.SubfieldSubset.At(fieldM, k)))
			overField := arg.Have(
				"a is a polynomial over M",
				"polynomial_over(M.carrier, a)",
				By(kInField, over, polynomial.PolynomialOverMono.At(zero, k, arg.TermAs[Set[A]]("M.carrier"), a)))
			rootBound := arg.Conjuncts(
				arg.Have(
					"a has at most its degree many roots",
					"finite(polynomial_roots(M.carrier, a)) ∧ "+
						"card(polynomial_roots(M.carrier, a)) ≤ polynomial_degree(a)",
					By(
						overField,
						nonzero,
						polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(M)).At(a))),
				"the roots are finite",
				"they number at most deg a")
			finiteRoots, rootCount := rootBound[0], rootBound[1]
			size := arg.Conjuncts(
				arg.Have(
					"the field of the power has card(k)^m elements",
					"finite(«constants») ∧ card(«constants») = card(k) ^ m",
					By(
						closed,
						subfieldK,
						finiteK,
						positive,
						finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
						cardinality.HasSizeDef)),
				"it is finite",
				"it has card(k)^m elements")
			finiteConstants, constantsCount := size[0], size[1]
			membership := finite_field.FiniteConstantsDef.At(R, order, m)
			goodInside := arg.Have(
				"the good points lie in it",
				"«good» ⊆ «constants»",
				BySets(membership))
			finiteGood := arg.Have(
				"so they are finite",
				"finite(«good»)",
				By(finiteConstants, goodInside, finite_set.FiniteSubset.At(goodSet, constants)))
			cover := arg.Have(
				"and each of its points is good or a root of a",
				"«constants» ⊆ «good» ∪ polynomial_roots(M.carrier, a)",
				Unfold(polynomial_roots.PolynomialRootsDef),
				BySets(membership))
			finiteUnion := arg.Have(
				"the good points and the roots are finitely many",
				"finite(«good» ∪ polynomial_roots(M.carrier, a))",
				By(finiteGood, finiteRoots, finite_set.FiniteUnion.At(goodSet, rootSet)))
			union := arg.TermAs[Set[A]]("«good» ∪ polynomial_roots(M.carrier, a)")
			covered := arg.Have(
				"so they are at least as many",
				"card(«constants») ≤ card(«good» ∪ polynomial_roots(M.carrier, a))",
				By(finiteUnion, cover, cardinality.CardSubset.At(constants, union)))
			sum := arg.Have(
				"and at most the sum",
				"card(«good» ∪ polynomial_roots(M.carrier, a)) ≤ "+
					"card(«good») + card(polynomial_roots(M.carrier, a))",
				By(finiteGood, finiteRoots, cardinality.CardUnionLe.At(goodSet, rootSet)))
			arg.Show(
				"the good points are counted by good_base_count",
				Unfold(twisted_count.GoodBaseCountDef),
				ByArith(constantsCount, covered, sum, rootCount))
		}),
})}

// rootPowerAtLeastOne reads off that the root of card(k)^m is at least one, k having
// at least two elements.
func rootPowerAtLeastOne(a *Argument, k *Expr[Set[A]], m *Expr[Nat], sizeNonzero Fact) Fact {
	order := a.TermAs[Nat]("card(k)")
	positive := a.Have(
		"card(k)^m is positive",
		"0 < card(k) ^ m",
		By(sizeNonzero, nat_order.PowPositive.At(order, m)))
	cast := a.Have(
		"so at least one in ℝ",
		"real_of_num(1) ≤ real_of_num(card(k) ^ m)",
		ByArith(positive))
	square := a.Have(
		"one squared lies under it",
		"real_of_num(1) ^ 2 ≤ real_of_num(card(k) ^ m)",
		ByArith(cast))
	return a.Have(
		"so its root is at least one",
		"real_of_num(1) ≤ real_sqrt(real_of_num(card(k) ^ m))",
		By(
			square,
			real_sqrt.SqrtLowerBound.At(
				a.TermAs[Real]("real_of_num(1)"), a.TermAs[Real]("real_of_num(card(k) ^ m)"))))
}

// InvariantChartPointsNearPower — for a subgroup H over a square field, the
// number of points of the invariant chart in the field of Q = card(k)^m
// elements is within B√Q of Q, for m past m₀ with 2|G| dividing m - 1. The
// twisted counts over H sum to |H| times that number, and those over G to |G|
// times the good base points (twisted_count.GoodFibreTwistCounting), which are
// all but deg a of the points of the field (GoodBaseCountLower). Each twisted
// count is at most Q + B₁√Q (fixed_twist_models.FixedTwistedUpperBound), so the
// sum over H gives the number from above, and taking the sum over the rest of G
// off the sum over G gives it from below (subgroupAverageBounds).
var InvariantChartPointsNearPower = invariantChartPointsNearPowerThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartPointsNearPower",
	Key:  "prop_40f24747355c73f5",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"∃r:num. card(k) = r * r",
		},
		Conclusion: "∃B:real. ∃m₀:num. " +
			"    real_of_num(0) ≤ B ∧ " +
			"    (∀m:num. " +
			"        0 < m ∧ m₀ ≤ m ∧ 2 * card(«G») ∣ m - 1 ⇒ " +
			"        real_abs(real_of_num(«chartCount»(m)) - real_of_num(card(k) ^ m)) ≤ B * «root»(m))",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "chartCount", Text: "λm:num. " +
				"    card(algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), " +
				"            restrict_ring(field_ring(M), finite_constants(field_ring(M), card(k), m)), " +
				"            k, " +
				"            λx:A. x))"},
			{Name: "twisted", Text: "λm:num. λs:permutation(A). " +
				"    twisted_evaluation_count(M, k, C, card(k) ^ m, s)"},
			{Name: "rest", Text: "{s:permutation(A) | s ∈ «G» ∧ s ∉ H}"},
			{Name: "root", Text: "λm:num. real_sqrt(real_of_num(card(k) ^ m))"},
			{Name: "ceiling", Text: "λB:real. λm:num. real_of_num(card(k) ^ m) + B * «root»(m)"},
			{Name: "constant", Text: "λB:real. " +
				"    real_of_num(card(«G»)) * real_of_num(polynomial_degree(a)) + real_of_num(card(«G»)) * B"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			closed, good, subgroupH, square Fact,
		) {
			G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
			rest := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«rest»")
			groupTerm := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]](
				"galois_group(M, «base», L)")
			B1, m1, upper := arg.Unpack2As[Real, Nat](
				GroupPremises(good, square, fixed_twist_models.FixedTwistedUpperBound.Read(M).At(k, L, t, C, a)),
				"B₁",
				"m₁")
			parts := arg.Conjuncts(
				upper,
				"B₁ is not negative",
				"each twisted count obeys the upper bound")
			B1Sign, twistedUpper := parts[0], parts[1]
			finiteGroup := GroupPremises(good, galois_good_open.GoodOpenGroupFinite.Read(M).At(k, L, C, t, a))
			subfieldK, finiteK :=
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				galois_good_open.GoodOpenConstantsFinite.Read(good)
			atLeastTwo := arg.Have(
				"k is a finite subfield, so it has at least two elements",
				"2 ≤ card(k)",
				By(subfieldK, finiteK, finite_field.FiniteSubfieldPrimePower.Read(M).At(k)))
			sizeNonzero := arg.Have(
				"so its size is not zero",
				"card(k) ≠ 0",
				ByArith(atLeastTwo))
			insideG := arg.Have(
				"H lies in G",
				"H ⊆ «G»",
				By(subgroupH, group.SubgroupSubset.At(groupTerm, H)))
			finiteH := arg.Have(
				"so H is finite",
				"finite(H)",
				By(finiteGroup, insideG, finite_set.FiniteSubset.At(H, G)))
			identityIn := arg.Have(
				"H holds the identity",
				"permutation_identity ∈ H",
				By(subgroupH, group.SubgroupOne.At(groupTerm, H)))
			nonempty := arg.Have(
				"so H is not empty",
				"H ≠ ∅",
				BySets(identityIn))
			atLeastOne := arg.Have(
				"so it has at least one element",
				"1 ≤ card(H)",
				ByArith(finiteH, nonempty, cardinality.CardEqZero.At(H)))
			joined := arg.Have(
				"H and the rest make up G",
				"H ∪ «rest» = «G»",
				BySets(insideG))
			disjoint := arg.Have(
				"and do not meet",
				"H ∩ «rest» = ∅",
				BySets())
			cardSplit := arg.Have(
				"so G counts H and the rest",
				"card(«G») = card(H) + card(«rest»)",
				By(finiteGroup, joined, disjoint, cardinality.CardOfDisjointParts.At(H, rest, G)))
			finiteRest := arg.Have(
				"and the rest is finite",
				"finite(«rest»)",
				By(
					finiteGroup,
					finite_set.FiniteRestrict.At(
						G, arg.TermAs[Set[symmetric_group.Permutation[A]]]("λs:permutation(A). s ∉ H"))))
			total := arg.Have(
				"in ℝ",
				"real_of_num(card(«G»)) = real_of_num(card(H)) + real_of_num(card(«rest»))",
				ByArith(cardSplit))
			hLarge := arg.Have(
				"and H counts at least one in ℝ",
				"real_of_num(1) ≤ real_of_num(card(H))",
				By(atLeastOne, real_construction.OfNumLessEq.At(arg.TermAs[Nat]("1"), arg.TermAs[Nat]("card(H)"))))
			gLarge := arg.Have(
				"so does G",
				"real_of_num(1) ≤ real_of_num(card(«G»))",
				ByArith(total, hLarge))
			degreeSign := arg.Have(
				"the degree of a is not negative",
				"real_of_num(0) ≤ real_of_num(polynomial_degree(a))",
				ByArith())
			restSign := arg.Have(
				"nor the size of the rest",
				"real_of_num(0) ≤ real_of_num(card(«rest»))",
				ByArith())
			arg.Take(arg.TermAs[Real]("«constant»(B₁)"))
			arg.Take(m1)
			arg.Do(SplitConj(
				Case(
					"the constant is not negative",
					ByArith(B1Sign, gLarge, degreeSign)),
				Case(
					"the bound at m",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						assumed := b.Conjuncts(
							b.Assume(),
							"m is positive",
							"m is past the threshold",
							"2|G| divides m - 1")
						positive, past, divides := assumed[0], assumed[1], assumed[2]
						f := b.TermAs[Fun[symmetric_group.Permutation[A], Nat]]("«twisted»(m)")
						ceiling := b.TermAs[Real]("«ceiling»(B₁, m)")
						each := b.Have(
							"each twisted count is at most Q + B₁√Q",
							"∀s:permutation(A). s ∈ «G» ⇒ real_of_num(«twisted»(m, s)) ≤ «ceiling»(B₁, m)",
							Derive(func(d *Argument) {
								s := d.FixAs[symmetric_group.Permutation[A]]("s")
								inG := d.Assume()
								d.Show(
									"at each member of G",
									By(inG, positive, past, divides, twistedUpper.At(s, m)))
							}))
						restricted := b.Conjuncts(
							b.Have(
								"in particular over H and over the rest, both inside G",
								"(∀s:permutation(A). s ∈ H ⇒ real_of_num(«twisted»(m, s)) ≤ «ceiling»(B₁, m)) ∧ "+
									"(∀s:permutation(A). s ∈ «rest» ⇒ real_of_num(«twisted»(m, s)) ≤ «ceiling»(B₁, m))",
								BySets(each, insideG)),
							"over H",
							"over the rest")
						onH, onRest := restricted[0], restricted[1]
						counts := b.Conjuncts(
							GroupPremises(
								closed,
								good,
								subgroupH,
								positive,
								twisted_count.GoodFibreTwistCounting.Read(M).At(k, L, t, C, a, H, m)),
							"the sum over G is |G| times the good base points",
							"the sum over H is |H| times the points of the invariant chart")
						sumOverG, sumOverH := counts[0], counts[1]
						boundH := b.Have(
							"the sum over H is at most |H| times the bound",
							"real_of_num(nat_sum(H, «twisted»(m))) ≤ real_of_num(card(H)) * «ceiling»(B₁, m)",
							By(finiteH, onH, real_sum.NatSumBound.At(H, f, ceiling)))
						boundRest := b.Have(
							"the sum over the rest at most its size times the bound",
							"real_of_num(nat_sum(«rest», «twisted»(m))) ≤ real_of_num(card(«rest»)) * «ceiling»(B₁, m)",
							By(finiteRest, onRest, real_sum.NatSumBound.At(rest, f, ceiling)))
						split := b.Have(
							"the sum over G splits",
							"nat_sum(H, «twisted»(m)) + nat_sum(«rest», «twisted»(m)) = nat_sum(«G», «twisted»(m))",
							By(finiteGroup, joined, disjoint, nat_sum.UnionEq.At(H, rest, G, f)))
						lower := b.Have(
							"all but deg a points of the field are good base points",
							"card(k) ^ m ≤ good_base_count(field_ring(M), k, a, card(k) ^ m) + polynomial_degree(a)",
							By(
								closed,
								subfieldK,
								finiteK,
								galois_good_open.GoodOpenDenominatorOver.Read(good),
								galois_good_open.GoodOpenDenominatorNonzero.Read(good),
								positive,
								GoodBaseCountLower.Read(M).At(k, a, m)))
						sumHIs := b.Have(
							"in ℝ the sum over H is |H| times the count",
							"real_of_num(nat_sum(H, «twisted»(m))) = real_of_num(card(H)) * real_of_num(«chartCount»(m))",
							ByArith(sumOverH, real_construction.OfNumMul))
						sumGIs := b.Have(
							"and the sum over G |G| times the good base points",
							"real_of_num(nat_sum(«G», «twisted»(m))) = "+
								"real_of_num(card(«G»)) * real_of_num(good_base_count(field_ring(M), k, a, card(k) ^ m))",
							ByArith(sumOverG, real_construction.OfNumMul))
						splitIn := b.Have(
							"and the sums add",
							"real_of_num(nat_sum(«G», «twisted»(m))) = "+
								"real_of_num(nat_sum(H, «twisted»(m))) + real_of_num(nat_sum(«rest», «twisted»(m)))",
							ByArith(split))
						lowerCast := b.Have(
							"and the base points' bound reads in ℝ",
							"real_of_num(card(k) ^ m) ≤ "+
								"real_of_num(good_base_count(field_ring(M), k, a, card(k) ^ m)) + "+
								"real_of_num(polynomial_degree(a))",
							ByArith(lower))
						rootLarge := rootPowerAtLeastOne(b, k, m, sizeNonzero)
						estimates := b.Conjuncts(
							b.Have(
								"so the count is within the two bounds of Q",
								"real_of_num(«chartCount»(m)) ≤ «ceiling»(B₁, m) ∧ "+
									"real_of_num(card(k) ^ m) ≤ "+
									"real_of_num(«chartCount»(m)) + "+
									"real_of_num(card(«G»)) * real_of_num(polynomial_degree(a)) + "+
									"real_of_num(card(«G»)) * (B₁ * «root»(m))",
								By(
									total,
									hLarge,
									restSign,
									sumHIs,
									sumGIs,
									splitIn,
									boundH,
									boundRest,
									lowerCast,
									B1Sign,
									rootLarge,
									degreeSign,
									subgroupAverageBounds.At(b.TermAs[Real]("real_of_num(card(«G»))"),
										b.TermAs[Real]("real_of_num(card(H))"),
										b.TermAs[Real]("real_of_num(card(«rest»))"),
										b.TermAs[Real]("real_of_num(nat_sum(H, «twisted»(m)))"),
										b.TermAs[Real]("real_of_num(nat_sum(«G», «twisted»(m)))"),
										b.TermAs[Real]("real_of_num(nat_sum(«rest», «twisted»(m)))"),
										b.TermAs[Real]("real_of_num(«chartCount»(m))"),
										b.TermAs[Real]("real_of_num(good_base_count(field_ring(M), k, a, card(k) ^ m))"),
										b.TermAs[Real]("real_of_num(card(k) ^ m)"),
										B1,
										b.TermAs[Real]("«root»(m)"),
										b.TermAs[Real]("real_of_num(polynomial_degree(a))")))),
							"the count is at most the bound",
							"Q is at most the count and the error")
						countAbove, countBelow := estimates[0], estimates[1]
						rootSign := b.Have(
							"B₁√Q is not negative",
							"real_of_num(0) ≤ B₁ * «root»(m)",
							ByArith(B1Sign, rootLarge))
						degreeProduct := b.Have(
							"nor is |G| deg a",
							"real_of_num(0) ≤ real_of_num(card(«G»)) * real_of_num(polynomial_degree(a))",
							ByArith(gLarge, degreeSign))
						spread := b.Have(
							"which √Q ≥ 1 only enlarges",
							"real_of_num(card(«G»)) * real_of_num(polynomial_degree(a)) ≤ "+
								"real_of_num(card(«G»)) * real_of_num(polynomial_degree(a)) * «root»(m)",
							ByArith(degreeProduct, rootLarge))
						spreadBound := b.Have(
							"and |G| only enlarges B₁√Q",
							"B₁ * «root»(m) ≤ real_of_num(card(«G»)) * (B₁ * «root»(m))",
							ByArith(rootSign, gLarge))
						above := b.Have(
							"the count exceeds Q by at most the constant times √Q",
							"real_of_num(«chartCount»(m)) - real_of_num(card(k) ^ m) ≤ «constant»(B₁) * «root»(m)",
							ByArith(countAbove, spread, spreadBound, degreeProduct))
						below := b.Have(
							"and falls short of Q by at most as much",
							"-(«constant»(B₁) * «root»(m)) ≤ real_of_num(«chartCount»(m)) - real_of_num(card(k) ^ m)",
							ByArith(countBelow, spread))
						b.Show(
							"so the distance is at most the constant times √Q",
							By(
								above,
								below,
								real_sgn_abs.AbsBounds.At(
									b.TermAs[Real]("real_of_num(«chartCount»(m)) - real_of_num(card(k) ^ m)"),
									b.TermAs[Real]("«constant»(B₁) * «root»(m)"))))
					}))))
		}),
})}

// QuotientTwoSidedCoarseBound — over a square field, the fixed field K of a subgroup
// H has |N_m - (Q + 1)| ≤ B√Q for Q = card(k)^m, N_m its count over the field of Q
// elements, and m past a threshold with 2|G| dividing m - 1. The count differs from
// the number of points of the invariant chart by at most B₀
// (InvariantChartCountAgrees), that number differs from Q by at most B₂√Q
// (InvariantChartPointsNearPower), and √Q ≥ 1 absorbs the constants.
var QuotientTwoSidedCoarseBound = quotientTwoSidedCoarseBoundThm{family.Add(registry.ProofEntry{
	Name: "QuotientTwoSidedCoarseBound",
	Key:  "prop_27f3fc9f86da3f6",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀K k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀L C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"finite(k)",
			"regular_function_field(M, k, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, field_adjoin(M, k, {t}), L), H)",
			"K = fixed_field(L, H)",
			"∃r:num. card(k) = r * r",
		},
		Conclusion: "∃B:real. ∃m₀:num. " +
			"    real_of_num(0) ≤ B ∧ " +
			"    (∀m:num. " +
			"        0 < m ∧ m₀ ≤ m ∧ 2 * card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) ∣ m - 1 ⇒ " +
			"        real_abs(real_of_num(curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m)) - " +
			"            real_of_num(card(k) ^ m + 1)) ≤ " +
			"        B * real_sqrt(real_of_num(card(k) ^ m)))",
		Abbrev: Abbrev{
			{Name: "constants", Text: "λm:num. finite_constants(field_ring(M), card(k), m)"},
			{Name: "count", Text: "λm:num. " +
				"    curve_rational_point_count(field_ring(M), k, «constants»(m), A₀, A₁, A₀₁)"},
			{Name: "chartCount", Text: "λm:num. " +
				"    card(algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), " +
				"            restrict_ring(field_ring(M), «constants»(m)), " +
				"            k, " +
				"            λx:A. x))"},
			{Name: "root", Text: "λm:num. real_sqrt(real_of_num(card(k) ^ m))"},
			{Name: "chartError", Text: "λm:num. real_of_num(«chartCount»(m)) - real_of_num(card(k) ^ m)"},
			{Name: "countError", Text: "λm:num. " +
				"    real_of_num(«count»(m)) - (real_of_num(card(k) ^ m) + real_of_num(1))"},
			{Name: "constant", Text: "λB₀:num. λB₂:real. real_of_num(B₀) + real_of_num(1) + B₂"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			L, C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			closed, subfieldK, curve, finiteK, regular, good, subgroupH, fixedIs, square Fact,
		) {
			gap, comparison := arg.UnpackAs[Nat](
				GroupPremises(
					subfieldK,
					curve,
					regular,
					good,
					subgroupH,
					fixedIs,
					InvariantChartCountAgrees.Read(M).At(K, k, A0, A1, A01, t, L, C, a, H)),
				"B₀")
			_, m0, near := arg.Unpack2As[Real, Nat](
				GroupPremises(good, subgroupH, square, InvariantChartPointsNearPower.Read(M).At(k, L, t, C, a, H)),
				"B₂",
				"m₀")
			nearParts := arg.Conjuncts(
				near,
				"B₂ is not negative",
				"the points of the invariant chart are near Q")
			B2Sign, chartNear := nearParts[0], nearParts[1]
			subfieldConstants := galois_good_open.GoodOpenConstantsSubfield.Read(good)
			atLeastTwo := arg.Have(
				"k is a finite subfield, so it has at least two elements",
				"2 ≤ card(k)",
				By(subfieldConstants, finiteK, finite_field.FiniteSubfieldPrimePower.Read(M).At(k)))
			sizeNonzero := arg.Have(
				"so its size is not zero",
				"card(k) ≠ 0",
				ByArith(atLeastTwo))
			arg.Take(arg.TermAs[Real]("«constant»(B₀, B₂)"))
			arg.Take(m0)
			arg.Do(SplitConj(
				Case(
					"the constant is not negative",
					ByArith(B2Sign)),
				Case(
					"the bound at m",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						assumed := b.Conjuncts(
							b.Assume(),
							"m is positive",
							"m is past the threshold",
							"2|G| divides m - 1")
						positive, past, divides := assumed[0], assumed[1], assumed[2]
						l := b.TermAs[Set[A]]("«constants»(m)")
						constants := b.Have(
							"l, the field of card(k)^m elements of M, is a finite subfield",
							"subfield(M, «constants»(m)) ∧ finite(«constants»(m))",
							By(
								closed,
								subfieldConstants,
								finiteK,
								positive,
								finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
								cardinality.HasSizeDef))
						count := b.TermAs[Nat]("«count»(m)")
						chartCount := b.TermAs[Nat]("«chartCount»(m)")
						compared := b.Conjuncts(
							b.Have(
								"the count at l is near the points of the invariant chart",
								"«count»(m) ≤ «chartCount»(m) + B₀ ∧ «chartCount»(m) ≤ «count»(m) + B₀",
								By(constants, comparison.At(l), nat_monus.DistLessEqCases.At(count, chartCount, gap))),
							"the count is at most the points and B₀",
							"the points are at most the count and B₀")
						countUnder, pointsUnder := compared[0], compared[1]
						notZero := b.Have(
							"m is not zero",
							"m ≠ 0",
							ByArith(positive))
						extension := b.Have(
							"the count at m is the count at l",
							"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m) = «count»(m)",
							Simp(Fwd(curve_point_count.CurveExtensionCountDef)),
							By(notZero))
						chartError := b.TermAs[Real]("«chartError»(m)")
						rootBound := b.TermAs[Real]("B₂ * «root»(m)")
						nearAt := b.Conjuncts(
							b.Have(
								"which are near Q",
								"-(B₂ * «root»(m)) ≤ «chartError»(m) ∧ «chartError»(m) ≤ B₂ * «root»(m)",
								By(positive, past, divides, chartNear.At(m), real_sgn_abs.AbsBounds.At(chartError, rootBound))),
							"they fall short of Q by at most B₂√Q",
							"and exceed it by at most B₂√Q")
						shortBy, exceedBy := nearAt[0], nearAt[1]
						rootLarge := rootPowerAtLeastOne(b, k, m, sizeNonzero)
						constantUnder := b.Have(
							"√Q ≥ 1 absorbs B₀",
							"real_of_num(B₀) ≤ real_of_num(B₀) * «root»(m)",
							ByArith(rootLarge))
						comparedUp := b.Have(
							"the comparison reads in ℝ above",
							"real_of_num(«count»(m)) ≤ real_of_num(«chartCount»(m)) + real_of_num(B₀)",
							ByArith(countUnder))
						comparedDown := b.Have(
							"and below",
							"real_of_num(«chartCount»(m)) ≤ real_of_num(«count»(m)) + real_of_num(B₀)",
							ByArith(pointsUnder))
						successor := b.Have(
							"Q + 1 reads in ℝ",
							"real_of_num(card(k) ^ m + 1) = real_of_num(card(k) ^ m) + real_of_num(1)",
							ByArith())
						above := b.Have(
							"the count exceeds Q + 1 by at most B√Q",
							"«countError»(m) ≤ «constant»(B₀, B₂) * «root»(m)",
							ByArith(comparedUp, exceedBy, constantUnder, rootLarge))
						below := b.Have(
							"and falls short of it by at most as much",
							"-(«constant»(B₀, B₂) * «root»(m)) ≤ «countError»(m)",
							ByArith(comparedDown, shortBy, constantUnder, rootLarge))
						b.Show(
							"so the distance is at most B√Q",
							extension.Rw(),
							successor.Rw(),
							By(
								above,
								below,
								real_sgn_abs.AbsBounds.At(
									b.TermAs[Real]("«countError»(m)"),
									b.TermAs[Real]("«constant»(B₀, B₂) * «root»(m)"))))
					}))))
		}),
})}
