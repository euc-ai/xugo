// invariant_count.go — the invariant chart of a subgroup H of a good open is a model
// of the fixed field K of H: finite over k[t] with the denominator inverted, with
// K as its field of fractions. It agrees with a plane model of K off a denominator,
// so the two count the same points up to the finitely many fibres removed.

package twist_quotient_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_fibres"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/scheme/twisted_count"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// _invariantChart is InvariantChartRing read apart, one fact per conjunct: the
// invariant chart D is a subring inside K, K holds k(t) and lies in L, D holds k, t,
// k[t] with a(t) inverted and the inverse of a(t), that ring is a subring inside K,
// and D holds what lies in C and in K.
type _invariantChart struct {
	subring, insideK, baseInK, KInL, holdsK, holdsT, holdsScalars, holdsInverse, scalarsSubring, scalarsInK, meet Fact
}

// readInvariantChart reads InvariantChartRing apart at the subgroup H of a good open.
func readInvariantChart(
	arg *Argument,
	M field.FieldFact[on.M],
	K, k, L *Expr[Set[A]],
	t *Expr[A],
	C *Expr[Set[A]],
	a *Arrow[Nat, A],
	H *Expr[Set[symmetric_group.Permutation[A]]],
	subfieldK, good, subgroupH, fixedIs Fact,
) _invariantChart {
	parts := arg.Conjuncts(
		GroupPremises(
			subfieldK, good, subgroupH, fixedIs, InvariantChartRing.Read(M).At(K, k, L, t, C, a, H)),
		"the invariants are a subring",
		"they lie in K",
		"K holds k(t)",
		"K lies in L",
		"they hold k",
		"they hold t",
		"they hold k[t] with a(t) inverted",
		"they hold the inverse of a(t)",
		"k[t] with a(t) inverted is a subring",
		"it lies in K",
		"they hold what lies in C and in K")
	return _invariantChart{
		parts[0],
		parts[1],
		parts[2],
		parts[3],
		parts[4],
		parts[5],
		parts[6],
		parts[7],
		parts[8],
		parts[9],
		parts[10],
	}
}

// InvariantChartRing — on a good open with K the fixed field of a subgroup H, the
// invariant chart D of H is C ∩ K, a subring of K holding k, t and k[t] with the
// denominator inverted.
var InvariantChartRing = invariantChartRingThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartRing",
	Key:  "prop_93c6f43541297fa5",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(M, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
		},
		Conclusion: "subring(field_ring(M), invariant_chart(C, H)) ∧ " +
			"invariant_chart(C, H) ⊆ K ∧ " +
			"«base» ⊆ K ∧ " +
			"K ⊆ L ∧ " +
			"k ⊆ invariant_chart(C, H) ∧ " +
			"t ∈ invariant_chart(C, H) ∧ " +
			"«scalars» ⊆ invariant_chart(C, H) ∧ " +
			"M.inv(polynomial_eval(a, t)) ∈ invariant_chart(C, H) ∧ " +
			"subring(field_ring(M), «scalars») ∧ " +
			"«scalars» ⊆ K ∧ " +
			"(∀y:A. y ∈ C ∧ y ∈ K ⇒ y ∈ invariant_chart(C, H))",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "scalars", Text: "ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			subfieldK, good, subgroupH, fixedIs Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			base := arg.TermAs[Set[A]]("«base»")
			polynomials := arg.TermAs[Set[A]]("«polynomials»")
			value := arg.TermAs[A]("polynomial_eval(a, t)")
			CInL := galois_good_open.GoodOpenChartInField.Read(good)
			HInG := arg.Have(
				"H lies in G",
				"H ⊆ «G»",
				By(subgroupH, field_automorphism.GaloisGroupSubgroup.At(fieldM, base, L, H)))
			invariants := arg.Conjuncts(
				arg.Have(
					"the invariants of C are a subring of C holding what lies in C and in k(t)",
					"subring(field_ring(M), invariant_chart(C, H)) ∧ "+
						"invariant_chart(C, H) ⊆ C ∧ "+
						"(∀y:A. y ∈ C ∧ y ∈ «base» ⇒ y ∈ invariant_chart(C, H))",
					By(
						galois_good_open.GoodOpenFieldSubfield.Read(good),
						good,
						galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a),
						CInL,
						HInG,
						galois_good_open.InvariantChartFacts.Read(M).At(base, L, C, H))),
				"the invariants of C are a subring",
				"they lie in C",
				"they hold what lies in C and in k(t)")
			subringD, holdsCommon := invariants[0], invariants[2]
			meet := arg.Have(
				"the invariants of C are C ∩ K",
				"∀y:A. y ∈ invariant_chart(C, H) ⇔ y ∈ C ∧ y ∈ K",
				fixedIs.Rw(),
				BySets(
					CInL,
					galois_good_open.InvariantChartDef.At(C, H),
					field_automorphism.FixedFieldDef.At(L, H)))
			fixedInL := arg.Have(
				"K lies in L",
				"K ⊆ L",
				fixedIs.Rw(),
				BySets(field_automorphism.FixedFieldDef.At(L, H)))
			fixed := arg.Have(
				"H fixes k(t), which lies in L",
				"∀y:A. y ∈ «base» ⇒ y ∈ L ∧ (∀p:permutation(A). p ∈ H ⇒ permutation_map(p, y) = y)",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					inBase := b.Assume()
					b.Do(SplitConj(
						Case(
							"k(t) lies in L",
							BySets(inBase, galois_good_open.GoodOpenRationalInField.Read(good))),
						Case(
							"a member of H lies in G, which fixes k(t)",
							Derive(func(c *Argument) {
								c.FixAs[symmetric_group.Permutation[A]]("p")
								inH := c.Assume()
								c.Show(
									"by the definition of G",
									BySets(inH, inBase, HInG, field_automorphism.FieldAutomorphismsDef.At(fieldM, base, L)))
							}))))
				}))
			baseFixed := arg.Have(
				"so k(t) lies in K",
				"«base» ⊆ K",
				fixedIs.Rw(),
				BySets(fixed, field_automorphism.FixedFieldDef.At(L, H)))
			tm := galois_good_open.GoodParameterInField(arg, t, good)
			away := arg.Conjuncts(
				arg.Have(
					"k[t] with a(t) inverted is a subring inside k(t)",
					"subring(field_ring(M), «scalars») ∧ «polynomials» ⊆ «scalars» ∧ «scalars» ⊆ «base»",
					By(
						M,
						good,
						galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
						galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
						GroupPremises(
							galois_good_open.GoodOpenConstantsSubfield.Read(good),
							algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
						galois_good_open.GoodOpenDenominatorInPolynomials.Read(good),
						galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
						ring_away.RingAwayInSubfield.Read(M).At(polynomials, base, value))),
				"it is a subring",
				"it holds k[t]",
				"it lies in k(t)")
			scalarsSubring, scalarsInBase := away[0], away[2]
			arg.Show(
				"so the invariants hold them, and K holds what H fixes",
				BySets(
					subringD,
					holdsCommon,
					meet,
					fixedInL,
					baseFixed,
					good,
					galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenDenominatorInverseInChart.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenDenominatorInverseInRational.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenConstantsInRational.Read(good),
					galois_good_open.GoodOpenParameterInRational.Read(good),
					galois_good_open.GoodOpenChartHoldsBase.Read(good),
					scalarsSubring,
					scalarsInBase))
		}),
})}

// InvariantChartFractions — K is the field of fractions of its invariant chart D. A
// member x of K lies in L, so x v = u with u, v in C and v nonzero. v is algebraic
// over k(t), so its inverse lies in k(t)(v), and a nonzero d of k[t] carries the
// inverse into k[t][v] (integral_element.AdjoinCommonDenominator), which lies in C.
// Then x d is u times a member of C, so it lies in C and in K, which is D.
var InvariantChartFractions = invariantChartFractionsThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartFractions",
	Key:  "prop_e5dd72718ecdce7",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(M, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
		},
		Conclusion: "fraction_field_carrier(restrict_ring(field_ring(M), K), invariant_chart(C, H))",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			subfieldK, good, subgroupH, fixedIs Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			ring := field.RingOn.Read(M)
			base := arg.TermAs[Set[A]]("«base»")
			polynomials := arg.TermAs[Set[A]]("«polynomials»")
			CInL := galois_good_open.GoodOpenChartInField.Read(good)
			subfieldBase := GroupPremises(
				good, galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a))
			polynomialsInC := GroupPremises(
				good, galois_good_open.GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a))
			tm := galois_good_open.GoodParameterInField(arg, t, good)
			polynomialsInBase := GroupPremises(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm))
			chart := readInvariantChart(arg, M, K, k, L, t, C, a, H, subfieldK, good, subgroupH, fixedIs)
			fractions := arg.Have(
				"every member of L is a fraction over C",
				"∀z:A. z ∈ L ⇒ ∃p q:A. p ∈ C ∧ q ∈ C ∧ q ≠ M.zero ∧ z * q = p",
				By(arg.Unfolded(galois_good_open.GoodOpenFractionField.Read(good), field.FractionFieldCarrierDef)))
			lInM := arg.Have(
				"L and K lie in M",
				"L ⊆ M.carrier ∧ K ⊆ M.carrier",
				By(
					galois_good_open.GoodOpenFieldSubfield.Read(good),
					subfieldK,
					field.SubfieldSubset.At(fieldM, L),
					field.SubfieldSubset.At(fieldM, K)))
			cOpen := arg.Unfolded(
				GroupPremises(good, galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a)),
				comm_ring.SubringDef)
			kOpen := arg.Unfolded(subfieldK, field.SubfieldDef)
			separable := arg.Have(
				"every member of L is separable over k(t)",
				"∀y:A. y ∈ L ⇒ separable_over(M, «base», y)",
				By(
					galois_good_open.GoodOpenGalois.Read(good),
					galois_correspondence.GaloisOverDef.At(fieldM, base, L)))
			rational := arg.Have(
				"k(t) is the field of fractions of k[t]",
				"fraction_field_carrier(restrict_ring(field_ring(M), «base»), «polynomials»)",
				By(
					galois_good_open.GoodOpenConstantsSubfield.Read(good),
					tm,
					integral_element.RationalFunctionsFractionField.Read(M).AsFact().At(k, t)))
			denominators := arg.Have(
				"each member of K has a nonzero denominator in k[t] bringing it into C and K",
				"∀x:A. x ∈ K ⇒ ∃d:A. d ∈ «polynomials» ∧ d ≠ M.zero ∧ x * d ∈ C ∧ x * d ∈ K",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xInK := b.Assume()
					xInL := b.Have(
						"x lies in L",
						"x ∈ L",
						BySets(xInK, chart.KInL))
					_, v, fraction := b.Unpack2As[A, A](
						b.Have(
							"x is a fraction over C",
							"∃p q:A. p ∈ C ∧ q ∈ C ∧ q ≠ M.zero ∧ x * q = p",
							By(xInL, fractions.At(x))),
						"u",
						"v")
					data := b.Conjuncts(
						fraction,
						"u lies in C",
						"v lies in C",
						"v is not zero",
						"x v = u")
					uInC, vInC, vNonzero, equation := data[0], data[1], data[2], data[3]
					vInL := b.Have(
						"v lies in L",
						"v ∈ L",
						BySets(vInC, CInL))
					members := b.Have(
						"x, u and v lie in M",
						"x ∈ M.carrier ∧ u ∈ M.carrier ∧ v ∈ M.carrier",
						BySets(xInL, vInL, uInC, CInL, lInM))
					inverse := b.TermAs[A]("M.inv(v)")
					algebraic := b.Have(
						"v is algebraic over k(t)",
						"algebraic_over(M, «base», v)",
						By(separable.At(v), vInL, galois_correspondence.SeparableOverDef))
					adjoined := b.Conjuncts(
						b.Have(
							"k(t)(v) is a subfield holding v",
							"subfield(M, field_adjoin(M, «base», {v})) ∧ v ∈ field_adjoin(M, «base», {v})",
							By(subfieldBase, members, algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(base, v))),
						"k(t)(v) is a subfield",
						"it holds v")
					subfieldAdjoined, vAdjoined := adjoined[0], adjoined[1]
					adjoinedSet := b.TermAs[Set[A]]("field_adjoin(M, «base», {v})")
					inverseAdjoined := b.Have(
						"so it holds the inverse of v",
						"M.inv(v) ∈ field_adjoin(M, «base», {v})",
						By(subfieldAdjoined, vAdjoined, vNonzero, field.SubfieldInv.At(fieldM, adjoinedSet, v)))
					d, cleared := b.ObtainAs[A](
						"a nonzero d in k[t] carries the inverse of v into k[t][v]",
						"∃d:A. "+
							"    d ∈ «polynomials» ∧ "+
							"    d ≠ M.zero ∧ "+
							"    d * M.inv(v) ∈ polynomial_image(field_ring(M), «polynomials», v)",
						By(
							subfieldBase,
							good,
							galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
							rational,
							members,
							algebraic,
							inverseAdjoined,
							integral_element.AdjoinCommonDenominator.Read(M).AsFact().At(base, polynomials, v, inverse)))
					clearedParts := b.Conjuncts(
						cleared,
						"d lies in k[t]",
						"d is not zero",
						"d times the inverse of v lies in k[t][v]")
					dInPolynomials, dNonzero, quotientAtV := clearedParts[0], clearedParts[1], clearedParts[2]
					polynomialsAtV := b.Have(
						"k[t][v] lies in C",
						"polynomial_image(field_ring(M), «polynomials», v) ⊆ C",
						By(
							galois_good_open.GoodOpenChartRing.Read(good),
							polynomialsInC,
							vInC,
							algebraic_element.PolynomialImageLeast.Read(M).At(polynomials, C, v)))
					quotientInC := b.Have(
						"so d v⁻¹ lies in C",
						"d * M.inv(v) ∈ C",
						BySets(quotientAtV, polynomialsAtV))
					dInK := b.Have(
						"d lies in K and in M",
						"d ∈ K ∧ d ∈ M.carrier",
						BySets(dInPolynomials, polynomialsInBase, chart.baseInK, lInM))
					inverseFacts := b.Have(
						"the inverse of v lies in M and inverts v",
						"M.inv(v) ∈ M.carrier ∧ v * M.inv(v) = M.one",
						By(members, vNonzero, field.InvIn.Read(M), field.MulRightInverseOn.Read(M)))
					inverts := b.Have(
						"v times its inverse is one",
						"v * M.inv(v) = M.one",
						By(inverseFacts))
					product := b.Have(
						"x d is u times d v⁻¹",
						"x * d = u * (d * M.inv(v))",
						ByArith(
							ring,
							members,
							dInK,
							inverseFacts,
							Scaled(b.TermAs[A]("d * M.inv(v)"), equation),
							Scaled(b.TermAs[A]("x * d"), inverts)))
					inC := b.Have(
						"so x d lies in C",
						"x * d ∈ C",
						product.Rw(),
						By(uInC, quotientInC, cOpen))
					inK := b.Have(
						"and in K",
						"x * d ∈ K",
						By(xInK, dInK, kOpen))
					b.Take(d)
					b.Show(
						"d is the denominator",
						By(dInPolynomials, dNonzero, inC, inK))
				}))
			arg.Show(
				"the invariants lie in K, and each member of K is a fraction over them",
				Simp(Fwd(field.FractionFieldCarrierDef)),
				SplitConj(
					Case(
						"the invariants lie in K",
						By(chart.insideK)),
					Case(
						"x d and d lie in C and in K",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xInK := b.Assume()
							d, data := b.ObtainAs[A](
								"x has a denominator d",
								"∃d:A. d ∈ «polynomials» ∧ d ≠ M.zero ∧ x * d ∈ C ∧ x * d ∈ K",
								By(xInK, denominators.At(x)))
							parts := b.Conjuncts(
								data,
								"d lies in k[t]",
								"d is not zero",
								"x d lies in C",
								"x d lies in K")
							dInPolynomials, dNonzero, productInC, productInK := parts[0], parts[1], parts[2], parts[3]
							numerator := b.TermAs[A]("x * d")
							dBoth := b.Have(
								"d lies in C and in K",
								"d ∈ C ∧ d ∈ K",
								BySets(dInPolynomials, polynomialsInC, polynomialsInBase, chart.baseInK))
							b.Take(numerator)
							b.Take(d)
							b.Show(
								"both lie in the invariants",
								By(dNonzero, productInC, productInK, dBoth, chart.meet.At(numerator), chart.meet.At(d)))
						}))))
		}),
})}

// InvariantChartFinite — the invariant chart D is a finite module over k[t] with
// a(t) inverted: inverting a(t) keeps a principal ideal domain (k[t] is one), and D
// is a submodule of the finite module C over it.
var InvariantChartFinite = invariantChartFiniteThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartFinite",
	Key:  "prop_9a60c6ea35be47ad",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(M, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
		},
		Conclusion: "module_finitely_generated(restrict_ring(field_ring(M), «scalars»), " +
			"    restrict_module(regular_module(field_ring(M)), invariant_chart(C, H)))",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "scalars", Text: "ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))"},
			{Name: "regular", Text: "regular_module(field_ring(M))"},
			{Name: "scalarRing", Text: "restrict_ring(field_ring(M), «scalars»)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			subfieldK, good, subgroupH, fixedIs Fact,
		) {
			polynomials := arg.TermAs[Set[A]]("«polynomials»")
			scalars := arg.TermAs[Set[A]]("«scalars»")
			value := arg.TermAs[A]("polynomial_eval(a, t)")
			scalarRing := arg.TermAs[module_record.RingOps[A]]("«scalarRing»")
			regular := arg.TermAs[module_record.ModuleOps[A, A]]("«regular»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«regular», C)")
			invariants := arg.TermAs[Set[A]]("invariant_chart(C, H)")
			chart := readInvariantChart(arg, M, K, k, L, t, C, a, H, subfieldK, good, subgroupH, fixedIs)
			tm := galois_good_open.GoodParameterInField(arg, t, good)
			polynomialsPrincipal := arg.Have(
				"k[t] is a principal ideal domain",
				"principal_ideal_domain(restrict_ring(field_ring(M), «polynomials»))",
				By(
					galois_good_open.GoodOpenConstantsSubfield.Read(good),
					tm,
					principal_ideal_domain.PolynomialImagePrincipalIdealDomain.Read(M).AsFact().At(k, t)))
			scalarsPrincipal := arg.Have(
				"and stays one with a(t) inverted",
				"principal_ideal_domain(«scalarRing»)",
				By(
					good,
					galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
					polynomialsPrincipal,
					galois_good_open.GoodOpenDenominatorInPolynomials.Read(good),
					galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
					ring_away.AwayPrincipalIdealDomain.Read(M).At(polynomials, value)))
			ambient := arg.Have(
				"M is a module over the scalars",
				"module_on(«scalarRing», «regular»)",
				By(chart.scalarsSubring, fractional_ideal.FieldModuleOn.Read(M).At(scalars)))
			chartSubmodule := arg.Have(
				"C is a submodule over the scalars",
				"submodule(«scalarRing», «regular», C)",
				By(
					good,
					galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenChartHoldsBase.Read(good),
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(scalars, C)))
			chartModule := arg.Have(
				"so C is a module over them",
				"module_on(«scalarRing», restrict_module(«regular», C))",
				By(ambient, chartSubmodule, submodule.SubmoduleModuleOn.At(scalarRing, regular, C)))
			invariantSubmodule := arg.Have(
				"so are the invariants",
				"submodule(«scalarRing», «regular», invariant_chart(C, H))",
				By(
					chart.subring,
					chart.holdsScalars,
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(scalars, invariants)))
			inside := arg.Have(
				"the invariants lie in C",
				"invariant_chart(C, H) ⊆ C",
				BySets(galois_good_open.InvariantChartDef.At(C, H)))
			inChart := arg.Have(
				"so they are a submodule of C",
				"submodule(«scalarRing», restrict_module(«regular», C), invariant_chart(C, H))",
				By(invariantSubmodule, inside, submodule.SubmoduleRestrict.At(scalarRing, regular, C, invariants)))
			finite := arg.Have(
				"and a submodule of a finite module over a principal ideal domain is finite",
				"module_finitely_generated(«scalarRing», "+
					"    restrict_module(restrict_module(«regular», C), invariant_chart(C, H)))",
				By(
					scalarsPrincipal,
					chartModule,
					galois_good_open.GoodOpenChartFinite.Read(good),
					inChart,
					principal_ideal_domain.FinitelyGeneratedSubmodule.At(scalarRing, vectors, invariants)))
			arg.Show(
				"as the invariants, restricted once",
				By(finite, module_record.RestrictModuleTwice.At(regular, C, invariants)))
		}),
})}

// InvariantPointsOverBase — the points of the invariant chart in a finite subfield l
// holding k over one value y of t number at most the order of the group: a point
// makes y algebraic with a(y) not zero, so the good open reads over y, and there the
// points of the invariant chart are the restrictions of the fibre of C.
var InvariantPointsOverBase = invariantPointsOverBaseThm{family.Add(registry.ProofEntry{
	Name: "InvariantPointsOverBase",
	Key:  "prop_27c8fd4e0703be26",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀K k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)). " +
			"∀l:set(A). " +
			"∀y:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
			"subfield(M, l)",
			"finite(l)",
		},
		Conclusion: "finite(«over») ∧ card(«over») ≤ card(«G»)",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "source", Text: "restrict_ring(field_ring(M), invariant_chart(C, H))"},
			{Name: "points", Text: "λU:set(A). " +
				"    algebra_points(«source», restrict_ring(field_ring(M), U), k, λx:A. x)"},
			{Name: "over", Text: "{e:A → A | e ∈ «points»(l) ∧ e(t) = y}"},
			{Name: "fibre", Text: "geometric_fibre(M, k, C, t, y)"},
			{Name: "restriction", Text: "λev:(A → A). λz:A. COND(z ∈ invariant_chart(C, H), ev(z), M.zero)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			l *Expr[Set[A]],
			y *Expr[A],
			subfieldK, good, subgroupH, fixedIs, subfieldL, finiteL Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ring := field.RingOn.Read(M)
			D := arg.TermAs[Set[A]]("invariant_chart(C, H)")
			source := arg.TermAs[module_record.RingOps[A]]("«source»")
			target := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), l)")
			identity := arg.TermAs[Fun[A, A]]("λx:A. x")
			closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
			over := arg.TermAs[Set[Fun[A, A]]]("«over»")
			fibre := arg.TermAs[Set[Fun[A, A]]]("«fibre»")
			restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			chart := readInvariantChart(arg, M, K, k, L, t, C, a, H, subfieldK, good, subgroupH, fixedIs)
			subfieldConstants := galois_good_open.GoodOpenConstantsSubfield.Read(good)
			closureField := arg.Conjuncts(
				GroupPremises(subfieldConstants, algebraic_element.AlgebraicElementsSubfield.Read(M).At(k)),
				"the algebraic points form a subfield",
				"they hold k")
			closureSubfield := closureField[0]
			subringClosure := arg.Have(
				"so they form a subring",
				"subring(field_ring(M), algebraic_elements(M, k))",
				By(closureSubfield, field.SubfieldSubring.Read(M)))
			lInField := arg.Have(
				"l lies in M",
				"l ⊆ M.carrier",
				By(subfieldL, field.SubfieldSubset.At(fieldM, l)))
			lInClosure := arg.Have(
				"l lies among the algebraic points",
				"∀x:A. x ∈ l ⇒ x ∈ algebraic_elements(M, k)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inL := b.Assume()
					algebraic := b.Have(
						"a member of a finite subfield is algebraic",
						"algebraic_over(M, k, x)",
						By(
							subfieldConstants,
							subfieldL,
							finiteL,
							inL,
							finite_field.FiniteSubfieldAlgebraic.Read(M).At(k, l, x)))
					b.Show(
						"and lies in M",
						BySets(inL, lInField, algebraic, algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
				}))
			arg.Cases(arg.Term("«over» = ∅"))
			arg.When(
				"no point lies over y",
				func(b *Argument, empty Fact) {
					b.Do(empty.Rw())
					b.Do(SplitConj(
						Case(
							"the empty set is finite",
							By(finite_set.FiniteRules)),
						Case(
							"and has no point",
							ByArith(cardinality.CardClauses.Inst[Fun[A, A]]()))))
				})
			arg.Otherwise(
				"a point over y puts the good open over y",
				func(b *Argument, nonempty Fact) {
					e, chosen := b.ObtainAs[Fun[A, A]](
						"some point lies over y",
						"∃e:(A → A). e ∈ «over»",
						BySets(nonempty))
					data := b.Conjuncts(
						b.Have(
							"e is a point of the invariant chart sending t to y",
							"e ∈ «points»(l) ∧ e(t) = y",
							BySets(chosen)),
						"e is a point",
						"e sends t to y")
					ePoint, eSendsT := data[0], data[1]
					valuesIn := b.Have(
						"each point sends the invariant chart into l",
						"∀f:(A → A). ∀x:A. f ∈ «points»(l) ∧ x ∈ invariant_chart(C, H) ⇒ f(x) ∈ l",
						Derive(func(c *Argument) {
							f := c.FixAs[Fun[A, A]]("f")
							x := c.FixAs[A]("x")
							given := c.Conjuncts(
								c.Assume(),
								"f is a point",
								"x lies in the invariant chart")
							fPoint, xInChart := given[0], given[1]
							homomorphism := c.Have(
								"f is a ring map into l",
								"ring_homomorphism(«source», restrict_ring(field_ring(M), l), f)",
								By(fPoint, algebra_points.AlgebraPointsMember.At(source, target, k, identity, f)))
							c.Show(
								"so it sends x into l",
								By(xInChart, ring_homomorphism.MapIn.Read(homomorphism).AsFact().At(x)))
						}))
					yInL := b.Have(
						"so y lies in l",
						"y ∈ l",
						eSendsT.RwRev(),
						By(ePoint, chart.holdsT, valuesIn.At(e, t)))
					yInClosure := b.Have(
						"so it is algebraic over k",
						"y ∈ algebraic_elements(M, k)",
						By(yInL, lInClosure.At(y)))
					nonvanishing := b.Have(
						"and a does not vanish at y",
						"polynomial_eval(a, y) ≠ M.zero",
						eSendsT.RwRev(),
						By(
							good,
							chart.holdsK,
							chart.holdsT,
							chart.holdsInverse,
							ePoint,
							twisted_count.GoodPointKeepsDenominator.Read(M).At(k, L, t, C, a, D, l, e)))
					overY := galois_good_open.ReadGoodFibre(b, good, y, yInClosure, nonvanishing)
					onH := b.Have(
						"the fibre of C restricts onto the points of the invariant chart over y",
						"image(«restriction», «fibre») = geometric_fibre(M, k, invariant_chart(C, H), t, y)",
						By(overY.Quotients.At(H), subgroupH))
					freeFacts := b.Conjuncts(
						b.Unfolded(overY.Free, twisted_counting.FreeFiniteActionDef),
						"G is a group",
						"G is finite",
						"the fibre is finite",
						"the identity acts trivially",
						"G acts freely")
					finiteFibre := freeFacts[2]
					inside := b.Have(
						"so every point over y restricts a point of the fibre",
						"«over» ⊆ image(«restriction», «fibre»)",
						onH.Rw(),
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(set_basic.SubsetDef)))
							f := c.FixAs[Fun[A, A]]("f")
							inOver := c.Assume()
							parts := c.Conjuncts(
								c.Have(
									"f is a point in l sending t to y",
									"f ∈ «points»(l) ∧ f(t) = y",
									BySets(inOver)),
								"f is a point",
								"f sends t to y")
							fPoint, fSendsT := parts[0], parts[1]
							values := c.Have(
								"its values lie among the algebraic points",
								"∀u:A. u ∈ «source».carrier ⇒ f(u) ∈ algebraic_elements(M, k)",
								Derive(func(d *Argument) {
									u := d.FixAs[A]("u")
									inChart := d.Assume()
									d.Show(
										"they lie in l",
										By(fPoint, inChart, valuesIn.At(f, u), lInClosure.At(d.TermAs[A]("f(u)"))))
								}))
							moved := c.Have(
								"so it is a point with algebraic values",
								"f ∈ «points»(algebraic_elements(M, k))",
								By(
									ring,
									lInField,
									subringClosure,
									values,
									fPoint,
									algebra_points.AlgebraPointsChangeTarget.At(R, source, k, identity, f, l, closure)))
							c.Show(
								"over y",
								BySets(
									moved,
									fSendsT,
									galois_good_open.GeometricFibreDef.At(fieldM, k, D, t, y),
									galois_good_open.GeometricEvaluationPointsDef.At(fieldM, k, D)))
						}))
					image := b.TermAs[Set[Fun[A, A]]]("image(«restriction», «fibre»)")
					imageFinite := b.Have(
						"the image is finite",
						"finite(image(«restriction», «fibre»))",
						By(finiteFibre, finite_set.FiniteImage.At(restriction, fibre)))
					imageCount := b.Have(
						"with at most as many points as the fibre",
						"card(image(«restriction», «fibre»)) ≤ card(«fibre»)",
						By(finiteFibre, cardinality.CardImageLe.At(restriction, fibre)))
					finiteOver := b.Have(
						"so the points over y are finite",
						"finite(«over»)",
						By(imageFinite, inside, finite_set.FiniteSubset.At(over, image)))
					counted := b.Have(
						"and at most as many",
						"card(«over») ≤ card(image(«restriction», «fibre»))",
						By(imageFinite, inside, cardinality.CardSubset.At(over, image)))
					b.Show(
						"the fibre has the size of the group",
						ByArith(finiteOver, counted, imageCount, overY.Card))
				})
		}),
})}

// PlaneChartMeetsInvariantChart — a plane model of K and the invariant chart agree
// off the zeros of one nonzero polynomial u over k. Over k[t] with a(t) inverted the
// invariant chart and the chart of the model with a(t) inverted are both finite with
// fraction field K, so they agree with one nonzero scalar d inverted
// (ModelsAgreeInSubfield). A power of the unit a(t) clears d into k[t], and u is the
// value of a(t) times that. The unit factor changes neither ring, and the extra a(t)
// is there so that inverting u(t) on the chart also inverts a(t): the chart with
// u(t) inverted is the localized chart with d inverted.
var PlaneChartMeetsInvariantChart = planeChartMeetsInvariantChartThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartMeetsInvariantChart",
	Key:  "prop_d9e0b8cff6748499",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀K k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)). " +
			"∀z:A. " +
			"∀F:(num → A). " +
			"∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "∃u:(num → A). " +
			"    polynomial_over(k, u) ∧ " +
			"    u ≠ vec_zero ∧ " +
			"    «value»(u) ≠ M.zero ∧ " +
			"    «value»(u) ∈ «polynomials» ∧ " +
			"    ring_away(field_ring(M), invariant_chart(C, H), «value»(u)) = " +
			"    ring_away(field_ring(M), «chart», «value»(u))",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "value", Text: "λf:(num → A). polynomial_eval(f, t)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "scalars", Text: "ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))"},
			{Name: "chart", Text: "plane_chart_zero(restrict_ring(field_ring(M), K), k, t, z)"},
			{Name: "generated", Text: "polynomial_image(field_ring(M), «polynomials», z)"},
			{Name: "localized", Text: "ring_away(field_ring(M), «chart», polynomial_eval(a, t))"},
			{Name: "power", Text: "λn:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n)"},
			{Name: "inversePower", Text: "λn:num. monoid_pow(M.mul, M.one, M.inv(polynomial_eval(a, t)), n)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			H *Expr[Set[symmetric_group.Permutation[A]]],
			z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			subfieldK, good, subgroupH, fixedIs, model Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			scalars := arg.TermAs[Set[A]]("«scalars»")
			invariants := arg.TermAs[Set[A]]("invariant_chart(C, H)")
			localized := arg.TermAs[Set[A]]("«localized»")
			chartSet := arg.TermAs[Set[A]]("«chart»")
			polynomials := arg.TermAs[Set[A]]("«polynomials»")
			value := arg.TermAs[A]("polynomial_eval(a, t)")
			inverseValue := arg.TermAs[A]("M.inv(polynomial_eval(a, t))")
			chart := readInvariantChart(arg, M, K, k, L, t, C, a, H, subfieldK, good, subgroupH, fixedIs)
			tm := galois_good_open.GoodParameterInField(arg, t, good)
			kAndTInK := arg.Have(
				"k and t lie in K",
				"k ⊆ K ∧ t ∈ K",
				BySets(
					galois_good_open.GoodOpenConstantsInRational.Read(good),
					galois_good_open.GoodOpenParameterInRational.Read(good),
					chart.baseInK))
			zInK := arg.Have(
				"z lies in K",
				"z ∈ K",
				By(arg.Unfolded(model, plane_model.IntegralPlaneModelDef)))
			sameChart := arg.Conjuncts(
				plane_model.PlaneChartsInAmbient.At(fieldM, K, k, t, z, b),
				"the first chart is k[t][z]",
				"the second chart is k[1/t][t^(-b) z]")
			firstChartIs := sameChart[0]
			plane := arg.Conjuncts(
				arg.Simplified(
					arg.Have(
						"k[t][z] is a subring holding k[t], and inverting a(t) stays in K",
						"subring(field_ring(M), «generated») ∧ "+
							"«polynomials» ⊆ «generated» ∧ "+
							"subring(field_ring(M), ring_away(field_ring(M), «generated», polynomial_eval(a, t))) ∧ "+
							"«generated» ⊆ ring_away(field_ring(M), «generated», polynomial_eval(a, t)) ∧ "+
							"ring_away(field_ring(M), «generated», polynomial_eval(a, t)) ⊆ K",
						By(
							galois_good_open.GoodOpenConstantsSubfield.Read(good),
							subfieldK,
							kAndTInK,
							zInK,
							galois_good_open.GoodOpenDenominatorOver.Read(good),
							galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
							galois_good_fibres.ChartFacts.Read(M).At(k, K, t, z, a))),
					Rev(firstChartIs)),
				"the chart is a subring",
				"it holds k[t]",
				"its localization is a subring",
				"the localization holds the chart",
				"the localization lies in K")
			subringChart, polynomialsInChart, subringLocalized, chartInLocalized, localizedInK :=
				plane[0], plane[1], plane[2], plane[3], plane[4]
			scalarData := arg.Conjuncts(
				arg.Have(
					"the scalars hold k[t] and the inverse of a(t)",
					"«polynomials» ⊆ «scalars» ∧ M.inv(polynomial_eval(a, t)) ∈ «scalars»",
					By(
						M,
						good,
						galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
						galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
						GroupPremises(
							galois_good_open.GoodOpenConstantsSubfield.Read(good),
							algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
						galois_good_open.GoodOpenDenominatorInPolynomials.Read(good),
						galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
						ring_away.RingAwayInSubfield.Read(M).At(polynomials, arg.TermAs[Set[A]]("«base»"), value))),
				"the scalars hold k[t]",
				"they hold the inverse of a(t)")
			polynomialsInScalars, inverseInScalars := scalarData[0], scalarData[1]
			scalarsInLocalized := arg.Have(
				"the scalars lie in the localized chart",
				"«scalars» ⊆ «localized»",
				BySets(
					polynomialsInChart,
					ring_away.RingAwayDef.At(R, polynomials, value),
					ring_away.RingAwayDef.At(R, chartSet, value)))
			d, found := arg.ObtainAs[A](
				"both rings are finite over the scalars with fraction "+
					"field K, so one nonzero scalar d makes them agree",
				"∃d:A. "+
					"    d ∈ «scalars» ∧ "+
					"    d ≠ M.zero ∧ "+
					"    ring_away(field_ring(M), invariant_chart(C, H), d) = ring_away(field_ring(M), «localized», d)",
				Derive(func(c *Argument) {
					curve := c.Conjuncts(
						GroupPremises(
							subfieldK, model, plane_model.PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)),
						"the charts of the model are a curve",
						"the powers of z are a basis of the chart over k[t]")
					curveOverLine, powersBasis := curve[0], curve[1]
					E, basisData := c.UnpackAs[Set[A]](powersBasis, "E")
					basisParts := c.Conjuncts(
						basisData,
						"E is finite",
						"E is the powers of z",
						"E is a basis")
					finiteE, basisE := basisParts[0], basisParts[2]
					basisLocalized := c.Have(
						"the powers of z are a basis of the localized chart over k[t] with a(t) inverted",
						"module_basis(restrict_ring(field_ring(M), «scalars»), "+
							"    restrict_module(regular_module(field_ring(M)), «localized»), "+
							"    E)",
						By(
							good,
							galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
							subringChart,
							polynomialsInChart,
							galois_good_open.GoodOpenDenominatorInPolynomials.Read(good),
							galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
							basisE,
							ring_away.BasisAway.Read(M).At(polynomials, chartSet, value, E)))
					onBasis := c.Conjuncts(
						c.Unfolded(basisLocalized, linear_independence.ModuleBasisDef),
						"E is independent",
						"E spans the localized chart")
					independent, spanning := onBasis[0], onBasis[1]
					finiteLocalized := c.Have(
						"so the localized chart is finite over the scalars",
						"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), "+
							"    restrict_module(regular_module(field_ring(M)), «localized»))",
						Unfold(principal_ideal_domain.FinitelyGeneratedDef),
						Witness(E),
						By(finiteE, spanning, linear_independence.IndependentInCarrier.Read(independent)))
					chartFractions := c.Have(
						"K is the fraction field of the chart",
						"fraction_field_carrier(restrict_ring(field_ring(M), K), «chart»)",
						By(
							c.Unfolded(curveOverLine, algebraic_curve.CurveOverLineDef),
							field.RestrictFieldRing.At(fieldM, K)))
					fractionsLocalized := c.Have(
						"so of the localized chart, which holds the chart and lies in K",
						"fraction_field_carrier(restrict_ring(field_ring(M), K), «localized»)",
						By(
							chartFractions,
							chartInLocalized,
							localizedInK,
							field.FractionFieldCarrierMono.At(
								c.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)"), chartSet, localized)))
					fractionsInvariant := c.Have(
						"K is the fraction field of the invariants",
						"fraction_field_carrier(restrict_ring(field_ring(M), K), invariant_chart(C, H))",
						By(subfieldK, good, subgroupH, fixedIs, InvariantChartFractions.Read(M).At(K, k, L, t, C, a, H)))
					finiteInvariant := c.Have(
						"and they are finite over the scalars",
						"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), "+
							"    restrict_module(regular_module(field_ring(M)), invariant_chart(C, H)))",
						By(subfieldK, good, subgroupH, fixedIs, InvariantChartFinite.Read(M).At(K, k, L, t, C, a, H)))
					c.Show(
						"two such rings agree with one nonzero scalar inverted",
						By(
							subfieldK,
							chart.scalarsSubring,
							chart.subring,
							subringLocalized,
							chart.holdsScalars,
							scalarsInLocalized,
							chart.insideK,
							localizedInK,
							fractionsInvariant,
							fractionsLocalized,
							finiteInvariant,
							finiteLocalized,
							good_localization.ModelsAgreeInSubfield.Read(M).At(K, scalars, invariants, localized)))
				}))
			dParts := arg.Conjuncts(
				found,
				"d lies in the scalars",
				"d is not zero",
				"inverting d makes them agree")
			dInScalars, dNonzero, agree := dParts[0], dParts[1], dParts[2]
			member := arg.Have(
				"d lies in M, and a power of a(t) brings it into k[t]",
				"d ∈ M.carrier ∧ (∃n:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * d ∈ «polynomials»)",
				By(dInScalars, ring_away.RingAwayMember.At(R, polynomials, value, d)))
			memberParts := arg.Conjuncts(
				member,
				"d lies in M",
				"a power of a(t) brings it into k[t]")
			dInField, clears := memberParts[0], memberParts[1]
			n, cleared := arg.UnpackAs[Nat](clears, "n")
			polynomialsOpen := arg.Unfolded(
				GroupPremises(good, galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a)),
				comm_ring.SubringDef)
			inPolynomials := arg.Have(
				"a(t) times the cleared d lies in k[t]",
				"polynomial_eval(a, t) * («power»(n) * d) ∈ «polynomials»",
				By(galois_good_open.GoodOpenDenominatorInPolynomials.Read(good), cleared, polynomialsOpen))
			u, valueIs := arg.ObtainAs[Fun[Nat, A]](
				"so it is the value at t of a polynomial u over k",
				"∃u:(num → A). polynomial_over(k, u) ∧ polynomial_eval(a, t) * («power»(n) * d) = «value»(u)",
				BySets(inPolynomials, algebraic_element.PolynomialImageDef.At(R, k, t)))
			uParts := arg.Conjuncts(
				valueIs,
				"u is a polynomial over k",
				"its value is a(t) times the cleared d")
			uOverK, uValue := uParts[0], uParts[1]
			atU := arg.Conjuncts(
				arg.Have(
					"u(t) is a unit times d, so it is not zero, and the "+
						"unit factor and the extra a(t) change neither ring",
					"«value»(u) ≠ M.zero ∧ "+
						"ring_away(field_ring(M), invariant_chart(C, H), «value»(u)) = "+
						"ring_away(field_ring(M), «chart», «value»(u))",
					Derive(func(c *Argument) {
						scalarRing := c.Have(
							"the scalars are a ring on their set",
							"comm_ring_on(restrict_ring(field_ring(M), «scalars»))",
							By(chart.scalarsSubring, comm_ring.SubringRingOn.Read(ring).At(scalars)))
						scalarMonoid := comm_ring.MulMonoidOn.Read(scalarRing)
						scalarsOpen := c.Unfolded(chart.scalarsSubring, comm_ring.SubringDef)
						denominatorIn := c.Have(
							"a(t) is a scalar",
							"polynomial_eval(a, t) ∈ «scalars»",
							BySets(galois_good_open.GoodOpenDenominatorInPolynomials.Read(good), polynomialsInScalars))
						powersIn := c.Have(
							"its powers and those of its inverse are scalars",
							"«power»(n) ∈ «scalars» ∧ «inversePower»(n) ∈ «scalars»",
							By(
								denominatorIn,
								inverseInScalars,
								comm_monoid.PowIn.Read(scalarMonoid).AsFact().At(value, n),
								comm_monoid.PowIn.Read(scalarMonoid).AsFact().At(inverseValue, n)))
						scalarsInField := c.Have(
							"the scalars lie in M",
							"«scalars» ⊆ M.carrier",
							By(comm_ring.SubringSubset.Read(chart.scalarsSubring)))
						inField := c.Have(
							"so these lie in M",
							"polynomial_eval(a, t) ∈ M.carrier ∧ "+
								"M.inv(polynomial_eval(a, t)) ∈ M.carrier ∧ "+
								"«power»(n) ∈ M.carrier ∧ "+
								"«inversePower»(n) ∈ M.carrier",
							BySets(denominatorIn, inverseInScalars, powersIn, scalarsInField))
						inverts := c.Have(
							"a(t) times its inverse is one",
							"polynomial_eval(a, t) * M.inv(polynomial_eval(a, t)) = M.one",
							By(
								inField,
								galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
								field.MulRightInverseOn.Read(M)))
						invertsPower := c.Have(
							"so their powers invert each other",
							"«power»(n) * «inversePower»(n) = M.one",
							By(inField, inverts, comm_monoid.PowInverseOn.Read(monoid).AsFact().At(value, inverseValue, n)))
						unitProduct := c.Have(
							"a(t) times its power has the inverse the inverse of a(t) times the power of that",
							"(polynomial_eval(a, t) * «power»(n)) * (M.inv(polynomial_eval(a, t)) * «inversePower»(n)) = M.one",
							ByArith(
								ring,
								inField,
								invertsPower,
								Scaled(c.TermAs[A]("«power»(n) * «inversePower»(n)"), inverts)))
						productsIn := c.Have(
							"both products are scalars",
							"polynomial_eval(a, t) * «power»(n) ∈ «scalars» ∧ "+
								"M.inv(polynomial_eval(a, t)) * «inversePower»(n) ∈ «scalars»",
							By(denominatorIn, inverseInScalars, powersIn, scalarsOpen))
						regroup := c.Have(
							"regrouping the product",
							"polynomial_eval(a, t) * («power»(n) * d) = (polynomial_eval(a, t) * «power»(n)) * d",
							ByArith(ring, inField, dInField))
						nonzeroValue := c.Have(
							"the value is not zero, d being nonzero and the other factor a unit",
							"«value»(u) ≠ M.zero",
							Derive(func(e *Argument) {
								vanishes := e.SupposeNot()
								inverse := e.TermAs[A]("M.inv(polynomial_eval(a, t)) * «inversePower»(n)")
								zeroProduct := e.Have(
									"the cleared product vanishes",
									"(polynomial_eval(a, t) * «power»(n)) * d = M.zero",
									By(vanishes, uValue, regroup))
								vanishing := e.Have(
									"so d vanishes",
									"d = M.zero",
									ByArith(ring, inField, dInField, Scaled(d, unitProduct), Scaled(inverse, zeroProduct)))
								e.Show(
									"but d is not zero",
									By(vanishing, dNonzero))
							}))
						inInvariants := c.Have(
							"the products and d lie in the invariants",
							"polynomial_eval(a, t) * «power»(n) ∈ invariant_chart(C, H) ∧ "+
								"M.inv(polynomial_eval(a, t)) * «inversePower»(n) ∈ invariant_chart(C, H) ∧ "+
								"d ∈ invariant_chart(C, H)",
							BySets(productsIn, dInScalars, chart.holdsScalars))
						inLocalized := c.Have(
							"the powers and d lie in the localized chart",
							"«power»(n) ∈ «localized» ∧ «inversePower»(n) ∈ «localized» ∧ d ∈ «localized»",
							BySets(powersIn, dInScalars, scalarsInLocalized))
						atInvariants := c.Have(
							"the unit factor does not matter in the invariants",
							"ring_away(field_ring(M), invariant_chart(C, H), (polynomial_eval(a, t) * «power»(n)) * d) = "+
								"ring_away(field_ring(M), invariant_chart(C, H), d)",
							By(
								M,
								chart.subring,
								inInvariants,
								unitProduct,
								ring_away.RingAwayUnitFactor.Read(M).At(invariants,
									c.TermAs[A]("polynomial_eval(a, t) * «power»(n)"),
									c.TermAs[A]("M.inv(polynomial_eval(a, t)) * «inversePower»(n)"),
									d)))
						atLocalized := c.Have(
							"nor in the localized chart",
							"ring_away(field_ring(M), «localized», «power»(n) * d) = ring_away(field_ring(M), «localized», d)",
							By(
								M,
								subringLocalized,
								inLocalized,
								invertsPower,
								ring_away.RingAwayUnitFactor.Read(M).At(localized,
									c.TermAs[A]("«power»(n)"),
									c.TermAs[A]("«inversePower»(n)"),
									d)))
						denominatorInChart := c.Have(
							"a(t) and the cleared d lie in the chart",
							"polynomial_eval(a, t) ∈ «chart» ∧ «power»(n) * d ∈ «chart»",
							BySets(galois_good_open.GoodOpenDenominatorInPolynomials.Read(good), cleared, polynomialsInChart))
						twice := c.Have(
							"the extra a(t): inverting it and then the cleared d inverts their product on the chart",
							"ring_away(field_ring(M), «localized», «power»(n) * d) = "+
								"ring_away(field_ring(M), «chart», polynomial_eval(a, t) * («power»(n) * d))",
							By(
								M,
								subringChart,
								denominatorInChart,
								ring_away.RingAwayTwice.Read(M).At(chartSet,
									value,
									c.TermAs[A]("«power»(n) * d"))))
						same := c.Have(
							"so the two rings agree off a(t) times the cleared d",
							"ring_away(field_ring(M), invariant_chart(C, H), polynomial_eval(a, t) * («power»(n) * d)) = "+
								"ring_away(field_ring(M), «chart», polynomial_eval(a, t) * («power»(n) * d))",
							By(regroup, atInvariants, atLocalized, twice, agree))
						c.Show(
							"which is u(t)",
							By(nonzeroValue, same, uValue))
					})),
				"u(t) is not zero",
				"the two rings agree with u(t) inverted")
			valueNonzero, agreeAtU := atU[0], atU[1]
			uNonzero := arg.Have(
				"so u is not the zero polynomial",
				"u ≠ vec_zero",
				Derive(func(c *Argument) {
					same := c.SupposeNot()
					zeroValue := c.Have(
						"the zero polynomial takes the value zero at t",
						"«value»(vec_zero) = M.zero",
						By(tm, polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(t)))
					c.Show(
						"which u does not",
						By(Normalized, same, zeroValue, valueNonzero))
				}))
			arg.Take(u)
			arg.Show(
				"u is the polynomial",
				By(uOverK, uValue, uNonzero, valueNonzero, inPolynomials, agreeAtU))
		}),
})}

// InvariantChartCountAgrees — the rational point count of a model of the fixed field
// K of H and the number of points of the invariant chart D in a finite subfield l
// differ by a bound B independent of l. K has an integral plane model
// (plane_model.IntegralPlaneModelExists), whose count is near the given curve's
// (plane_model.FunctionFieldModelsAgreeOffFiniteSet) and near the number of points of
// its first chart P (plane_model.PlaneCountNearChart). P and D agree off the zeros of
// one polynomial u over k, so their points differ by those killing u(t), boundedly
// many over each of the roots of u.
var InvariantChartCountAgrees = invariantChartCountAgreesThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartCountAgrees",
	Key:  "prop_7b123fd6e8dfa322",
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
			"regular_function_field(M, k, K)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, «base», L), H)",
			"K = fixed_field(L, H)",
		},
		Conclusion: "∃B:num. ∀l:set(A). " +
			"    subfield(M, l) ∧ finite(l) ⇒ dist((«count»(l), card(«points»(invariant_chart(C, H), l)))) ≤ B",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "count", Text: "λl:set(A). curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁)"},
			{Name: "points", Text: "λX:set(A). λl:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), k, λx:A. x)"},
			{Name: "chart", Text: "λz:A. plane_chart_zero(restrict_ring(field_ring(M), K), k, t, z)"},
			{Name: "second", Text: "λz:A. λb:num. plane_chart_one(restrict_field(M, K), k, t, z, b)"},
			{Name: "overlap", Text: "λz:A. ring_away(restrict_ring(field_ring(M), K), «chart»(z), t)"},
			{Name: "planeCount", Text: "λz:A. λb:num. λl:set(A). " +
				"    curve_rational_point_count(field_ring(M), k, l, «chart»(z), «second»(z, b), «overlap»(z))"},
			{Name: "value", Text: "λf:(num → A). polynomial_eval(f, t)"},
			{Name: "killed", Text: "λX:set(A). λl:set(A). λv:A. " +
				"    {e:A → A | e ∈ «points»(X, l) ∧ e(v) = M.zero}"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "scalars", Text: "ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))"},
			{Name: "localized", Text: "λz:A. λf:(num → A). ring_away(field_ring(M), «chart»(z), «value»(f))"},
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
			closed, subfieldK, curve, regular, good, subgroupH, fixedIs Fact,
		) {
			fieldM := arg.TermAs[FieldOps[A]]("M")
			base := arg.TermAs[Set[A]]("«base»")
			invariants := arg.TermAs[Set[A]]("invariant_chart(C, H)")
			chart := readInvariantChart(arg, M, K, k, L, t, C, a, H, subfieldK, good, subgroupH, fixedIs)
			tm := galois_good_open.GoodParameterInField(arg, t, good)
			tInK := arg.Have(
				"t lies in K",
				"t ∈ K",
				BySets(galois_good_open.GoodOpenParameterInRational.Read(good), chart.baseInK))
			kOverBase := arg.Have(
				"K lies between k(t) and L, so it is finite over k(t)",
				"finite_extension(M, «base», K)",
				By(
					good,
					galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
					subfieldK,
					galois_good_open.GoodOpenFieldSubfield.Read(good),
					chart.baseInK,
					chart.KInL,
					galois_good_open.GoodOpenFiniteExtension.Read(good),
					field_extension.IntermediateDegree.Read(M).At(base, K, L)))
			separableOnL := arg.Have(
				"every member of L is separable over k(t)",
				"∀y:A. y ∈ L ⇒ separable_over(M, «base», y)",
				By(
					galois_good_open.GoodOpenGalois.Read(good),
					galois_correspondence.GaloisOverDef.At(fieldM, base, L)))
			separable := arg.Have(
				"so is every member of K",
				"∀y:A. y ∈ K ⇒ separable_over(M, «base», y)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inK := b.Assume()
					b.Show(
						"K lies in L",
						By(separableOnL.At(y), inK, chart.KInL, set_basic.SubsetDef))
				}))
			z, F, weight, model := arg.Unpack3As[A, Fun[Nat, A], Nat](
				GroupPremises(
					galois_good_open.GoodOpenParameterTranscendental.Read(good),
					regular,
					tInK,
					kOverBase,
					separable,
					plane_model.IntegralPlaneModelExists.Read(M).At(K, k, t)),
				"z",
				"F",
				"b")
			degree := arg.TermAs[Nat]("polynomial_degree(F)")
			zInK := arg.Have(
				"z lies in K",
				"z ∈ K",
				By(arg.Unfolded(model, plane_model.IntegralPlaneModelDef)))
			polynomials := arg.TermAs[Set[A]]("«polynomials»")
			_, gap, compared := arg.Unpack2As[Fun[Nat, A], Nat](
				GroupPremises(
					subfieldK,
					curve,
					model,
					plane_model.FunctionFieldModelsAgreeOffFiniteSet.Read(M).At(K, k, A0, A1, A01, t, z, F, weight)),
				"c",
				"B₀")
			comparison := arg.Conjuncts(
				compared,
				"c is a polynomial over k",
				"c is not zero",
				"the first charts agree off c",
				"the counts lie within B₀")
			countsAgree := comparison[3]
			u, agreement := arg.UnpackAs[Fun[Nat, A]](
				GroupPremises(
					subfieldK,
					good,
					subgroupH,
					fixedIs,
					model,
					PlaneChartMeetsInvariantChart.Read(M).At(K, k, L, t, C, a, H, z, F, weight)),
				"u")
			agreed := arg.Conjuncts(
				agreement,
				"u is a polynomial over k",
				"u is not the zero polynomial",
				"its value is not zero",
				"its value lies in k[t]",
				"the invariants and the chart agree with it inverted")
			uOverK, uNonzero, valueNonzero, valueInPolynomials, invariantsAgree :=
				agreed[0], agreed[1], agreed[2], agreed[3], agreed[4]
			value := arg.TermAs[A]("«value»(u)")
			order := arg.TermAs[Nat]("card(«G»)")
			arg.Take(arg.TermAs[Nat](
				"B₀ + " +
					"polynomial_degree(F) + " +
					"polynomial_degree(u) * polynomial_degree(F) + " +
					"polynomial_degree(u) * card(«G»)"))
			l := arg.FixAs[Set[A]]("l")
			given := arg.Conjuncts(
				arg.Assume(),
				"l is a subfield",
				"l is finite")
			subfieldL, finiteL := given[0], given[1]
			chartSet := arg.TermAs[Set[A]]("«chart»(z)")
			secondSet := arg.TermAs[Set[A]]("«second»(z, b)")
			overlapSet := arg.TermAs[Set[A]]("«overlap»(z)")
			sameChart := arg.Conjuncts(
				plane_model.PlaneChartsInAmbient.At(fieldM, K, k, t, z, weight),
				"the first chart is k[t][z]",
				"the second chart is k[1/t][t^(-b) z]")
			firstChartIs := sameChart[0]
			planeCurve := arg.Conjuncts(
				GroupPremises(
					subfieldK, model, plane_model.PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, weight)),
				"the charts of the model are a curve",
				"the powers of z are a basis of the chart over k[t]")
			modelCurve := planeCurve[0]
			count := arg.TermAs[Nat]("«count»(l)")
			planeCount := arg.TermAs[Nat]("«planeCount»(z, b, l)")
			comparedAt := arg.Conjuncts(
				arg.Have(
					"the count of the curve is near that of the plane model",
					"«count»(l) ≤ «planeCount»(z, b, l) + B₀ ∧ «planeCount»(z, b, l) ≤ «count»(l) + B₀",
					By(subfieldL, finiteL, countsAgree.At(l), nat_monus.DistLessEqCases.At(count, planeCount, gap))),
				"the count is at most that of the plane model plus B₀",
				"and that of the plane model at most the count plus B₀")
			countBelowPlane, planeBelowCount := comparedAt[0], comparedAt[1]
			nearChart := arg.Conjuncts(
				arg.Have(
					"which is near the number of points of its first chart",
					"card(«points»(«chart»(z), l)) ≤ «planeCount»(z, b, l) ∧ "+
						"«planeCount»(z, b, l) ≤ card(«points»(«chart»(z), l)) + polynomial_degree(F)",
					By(
						subfieldK,
						model,
						subfieldL,
						finiteL,
						plane_model.PlaneCountNearChart.Read(M).At(K, k, t, z, F, weight, l))),
				"the first chart's points are at most that count",
				"which is at most those points and deg F")
			chartBelowPlane, planeBelowChart := nearChart[0], nearChart[1]
			finiteChart := arg.Have(
				"the first chart has finitely many points in l",
				"finite(«points»(«chart»(z), l))",
				By(
					subfieldK,
					modelCurve,
					finiteL,
					curve_point_count.CurvePointSetsFinite.Read(M).At(K, k, chartSet, secondSet, overlapSet, t, l)))
			zInField := arg.Have(
				"z lies in M",
				"z ∈ M.carrier",
				BySets(zInK, subfieldK, field.SubfieldSubset.At(fieldM, K)))
			chartData := arg.Conjuncts(
				arg.Simplified(
					arg.Have(
						"k[t][z] is a subring holding k[t]",
						"subring(field_ring(M), polynomial_image(field_ring(M), «polynomials», z)) ∧ "+
							"«polynomials» ⊆ polynomial_image(field_ring(M), «polynomials», z)",
						By(
							good,
							galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
							zInField,
							algebraic_element.PolynomialImageSubring.Read(M).AsFact().At(polynomials, z))),
					Rev(firstChartIs)),
				"the first chart is a subring",
				"it holds k[t]")
			subringChart, polynomialsInChart := chartData[0], chartData[1]
			chartHolds := arg.Have(
				"so it holds k and the value of u",
				"k ⊆ «chart»(z) ∧ «value»(u) ∈ «chart»(z)",
				BySets(
					good,
					galois_good_open.GoodOpenConstantsInPolynomials.Read(M).At(k, L, C, t, a),
					valueInPolynomials,
					polynomialsInChart))
			tInChart := arg.Have(
				"and t",
				"t ∈ «chart»(z)",
				BySets(
					good,
					galois_good_open.GoodOpenParameterInPolynomials.Read(M).At(k, L, C, t, a),
					polynomialsInChart))
			polynomialsInScalars := arg.Have(
				"the scalars hold k[t]",
				"«polynomials» ⊆ «scalars»",
				By(
					M,
					good,
					galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
					galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
					GroupPremises(
						galois_good_open.GoodOpenConstantsSubfield.Read(good),
						algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
					galois_good_open.GoodOpenDenominatorInPolynomials.Read(good),
					galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
					ring_away.RingAwayInSubfield.Read(M).At(polynomials, base, arg.TermAs[A]("polynomial_eval(a, t)"))))
			invariantHolds := arg.Have(
				"the invariants hold the value of u",
				"«value»(u) ∈ invariant_chart(C, H)",
				BySets(valueInPolynomials, polynomialsInScalars, chart.holdsScalars))
			offU := arg.Have(
				"a ring agreeing with the common localization off "+
					"u(t) counts it plus at most deg u · m killed points",
				Statement{
					Binders: "∀X:set(A). ∀m:num.",
					Hypotheses: []string{
						"subring(field_ring(M), X)",
						"k ⊆ X",
						"t ∈ X",
						"«value»(u) ∈ X",
						"ring_away(field_ring(M), X, «value»(u)) = «localized»(z, u)",
						"∀y:A. " +
							"    finite({e:A → A | e ∈ «points»(X, l) ∧ e(t) = y}) ∧ " +
							"    card({e:A → A | e ∈ «points»(X, l) ∧ e(t) = y}) ≤ m",
					},
					Conclusion: "(finite(«points»(X, l)) ⇔ finite(«points»(«localized»(z, u), l))) ∧ " +
						"(finite(«points»(X, l)) ⇒ " +
						"    card(«points»(X, l)) = " +
						"    card(«points»(«localized»(z, u), l)) + card(«killed»(X, l, «value»(u)))) ∧ " +
						"card(«killed»(X, l, «value»(u))) ≤ polynomial_degree(u) * m",
				},
				Derive(func(c *Argument) {
					X := c.FixAs[Set[A]]("X")
					m := c.FixAs[Nat]("m")
					given := c.Conjuncts(
						c.Assume(),
						"X is a subring",
						"it holds k",
						"it holds t",
						"it holds u(t)",
						"inverting u(t) in X gives the common localization",
						"at most m of its points lie over each value of t")
					subringX, kInX, tInX, valueInX, agreesX, fibresX :=
						given[0], given[1], given[2], given[3], given[4], given[5]
					away := c.Conjuncts(
						c.Have(
							"inverting u(t) on X loses the points killing it",
							"(finite(«points»(X, l)) ⇔ "+
								"    finite(«points»(«localized»(z, u), l)) ∧ finite(«killed»(X, l, «value»(u)))) ∧ "+
								"(finite(«points»(X, l)) ⇒ "+
								"    card(«points»(X, l)) = "+
								"    card(«points»(«localized»(z, u), l)) + card(«killed»(X, l, «value»(u))))",
							agreesX.RwRev(),
							By(
								subringX,
								subfieldL,
								kInX,
								valueInX,
								valueNonzero,
								algebra_point_bounds.AlgebraPointsAwayInField.Read(M).At(X, k, l, value))),
						"X has finitely many points exactly when each part has",
						"and counts its parts")
					finiteParts, countsParts := away[0], away[1]
					killed := c.Have(
						"at most deg u · m points of X kill u(t), at most m over each root of u",
						"finite(«killed»(X, l, «value»(u))) ∧ card(«killed»(X, l, «value»(u))) ≤ polynomial_degree(u) * m",
						By(
							subringX,
							subfieldL,
							kInX,
							tInX,
							uOverK,
							uNonzero,
							fibresX,
							algebra_point_bounds.KilledPointsBound.Read(M).At(X, k, l, t, u, m)))
					c.Show(
						"the killing points being finite",
						By(finiteParts, countsParts, killed))
				}))
			chartFibres := arg.Have(
				"at most deg F points of the first chart lie over each value of t",
				"∀y:A. "+
					"    finite({e:A → A | e ∈ «points»(«chart»(z), l) ∧ e(t) = y}) ∧ "+
					"    card({e:A → A | e ∈ «points»(«chart»(z), l) ∧ e(t) = y}) ≤ polynomial_degree(F)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					b.Show(
						"z is a root of the monic equation",
						By(
							subfieldK,
							model,
							subfieldL,
							plane_model.PlaneChartFibreBound.Read(M).At(K, k, l, t, z, F, weight, y)))
				}))
			invariantFibres := arg.Have(
				"at most |G| points of the invariants lie over each value of t",
				"∀y:A. "+
					"    finite({e:A → A | e ∈ «points»(invariant_chart(C, H), l) ∧ e(t) = y}) ∧ "+
					"    card({e:A → A | e ∈ «points»(invariant_chart(C, H), l) ∧ e(t) = y}) ≤ card(«G»)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					b.Show(
						"they are restrictions of the fibre of C",
						By(
							M,
							subfieldK,
							good,
							subgroupH,
							fixedIs,
							subfieldL,
							finiteL,
							InvariantPointsOverBase.Read(M).At(K, k, L, t, C, a, H, l, y)))
				}))
			localizedIs := arg.Have(
				"the common localization is the first chart with u(t) inverted",
				"ring_away(field_ring(M), «chart»(z), «value»(u)) = «localized»(z, u)",
				Refl())
			chartSide := arg.Conjuncts(
				GroupPremises(
					subringChart, chartHolds, tInChart, localizedIs, chartFibres, offU.At(chartSet, degree)),
				"the first chart has finitely many points exactly when the localization has",
				"it counts the localization and the points killing u(t)",
				"at most deg u · deg F points kill u(t)")
			chartFinitely, chartCounts, chartKilled := chartSide[0], chartSide[1], chartSide[2]
			invariantSide := arg.Conjuncts(
				GroupPremises(
					chart.subring,
					chart.holdsK,
					chart.holdsT,
					invariantHolds,
					invariantsAgree,
					invariantFibres,
					offU.At(invariants, order)),
				"the invariants have finitely many points exactly when the localization has",
				"they count the localization and the points killing u(t)",
				"at most deg u · |G| points kill u(t)")
			invariantFinitely, invariantCounts, invariantKilled :=
				invariantSide[0], invariantSide[1], invariantSide[2]
			finiteLocalized := arg.Have(
				"so the common localization has finitely many points",
				"finite(«points»(«localized»(z, u), l))",
				By(finiteChart, chartFinitely))
			finiteInvariant := arg.Have(
				"and so have the invariants",
				"finite(«points»(invariant_chart(C, H), l))",
				By(finiteLocalized, invariantFinitely))
			chartCount := arg.Have(
				"the first chart counts the localization and the killing points",
				"card(«points»(«chart»(z), l)) = "+
					"card(«points»(«localized»(z, u), l)) + card(«killed»(«chart»(z), l, «value»(u)))",
				By(finiteChart, chartCounts))
			invariantCount := arg.Have(
				"as do the invariants",
				"card(«points»(invariant_chart(C, H), l)) = "+
					"card(«points»(«localized»(z, u), l)) + card(«killed»(invariant_chart(C, H), l, «value»(u)))",
				By(finiteInvariant, invariantCounts))
			arg.Do(
				Simp(Fwd(nat_monus.DistLessEqCases)),
				SplitConj(
					Case(
						"the count is at most the points of the invariants and the bound",
						ByArith(countBelowPlane, planeBelowChart, chartCount, invariantCount, chartKilled)),
					Case(
						"and those points at most the count and the bound",
						ByArith(planeBelowCount, chartBelowPlane, chartCount, invariantCount, invariantKilled))))
		}),
})}
