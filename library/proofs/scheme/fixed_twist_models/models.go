package fixed_twist_models

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/constant_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_fibres"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/scheme/twisted_count"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// TwistModelsRefineGoodOpen — a good open refines, by inverting one polynomial
// c(t), to a good open carrying a model of every fixed twist field, and the
// refinement changes each count of twisted points by at most card(G) · deg(c):
// the models come from TwistModelsOnRefinement, the bound, true of every nonzero
// c, from twisted_count.TwistedCountOffRefinement.
var TwistModelsRefineGoodOpen = twistModelsRefineGoodOpenThm{family.Add(registry.ProofEntry{
	Name: "TwistModelsRefineGoodOpen",
	Key:  "prop_3b13e183c3491af0",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
		},
		Conclusion: "∃c:(num → A). " +
			"∃z:(permutation(A) → A). " +
			"∃F:(permutation(A) → num → A). " +
			"∃b:(permutation(A) → num). " +
			"    polynomial_over(k, c) ∧ " +
			"    c ≠ vec_zero ∧ " +
			"    fixed_twist_models(M, " +
			"        k, " +
			"        L, " +
			"        t, " +
			"        ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
			"        polynomial_mul(a, c), " +
			"        z, " +
			"        F, " +
			"        b) ∧ " +
			"    (∀s:permutation(A). ∀m:num. " +
			"        s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L) ∧ 0 < m ⇒ " +
			"        twisted_evaluation_count(M, " +
			"            k, " +
			"            ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
			"            card(k) ^ m, " +
			"            s) ≤ " +
			"        twisted_evaluation_count(M, k, C, card(k) ^ m, s) ∧ " +
			"        twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ " +
			"        twisted_evaluation_count(M, " +
			"            k, " +
			"            ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
			"            card(k) ^ m, " +
			"            s) + " +
			"        card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) * polynomial_degree(c))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		closedField, good Fact,
	) {
		c, refined := arg.UnpackAs[Fun[Nat, A]](
			arg.Have(
				"inverting one polynomial c(t) refines the good open to carry the models",
				"∃c:(num → A). "+
					"    polynomial_over(k, c) ∧ "+
					"    c ≠ vec_zero ∧ "+
					"    (∃z:(permutation(A) → A). ∃F:(permutation(A) → num → A). ∃b:(permutation(A) → num). "+
					"        fixed_twist_models(M, "+
					"            k, "+
					"            L, "+
					"            t, "+
					"            ring_away(field_ring(M), C, polynomial_eval(c, t)), "+
					"            polynomial_mul(a, c), "+
					"            z, "+
					"            F, "+
					"            b))",
				By(closedField, good, TwistModelsOnRefinement.Read(M).At(k, L, C, t, a))),
			"c")
		parts := arg.Conjuncts(
			refined,
			"c is a polynomial over k",
			"c is nonzero",
			"the refinement carries the models")
		z, F, b, models := arg.Unpack3As[Fun[symmetric_group.Permutation[A], A], Fun2[symmetric_group.Permutation[A], Nat, A], Fun[symmetric_group.Permutation[A], Nat]](
			parts[2], "z", "F", "b")
		counts := arg.Have(
			"and it changes each twisted count by at most card(G) · deg(c)",
			Statement{
				Binders:    "∀s:permutation(A). ∀m:num.",
				Hypotheses: []string{"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L) ∧ 0 < m"},
				Conclusion: "twisted_evaluation_count(M, " +
					"    k, " +
					"    ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
					"    card(k) ^ m, " +
					"    s) ≤ " +
					"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ∧ " +
					"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ " +
					"twisted_evaluation_count(M, " +
					"    k, " +
					"    ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
					"    card(k) ^ m, " +
					"    s) + " +
					"card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) * polynomial_degree(c)",
			},
			Derive(func(d *Argument) {
				s := d.FixAs[symmetric_group.Permutation[A]]("s")
				m := d.FixAs[Nat]("m")
				given := d.Conjuncts(
					d.Assume(),
					"s lies in G",
					"m is positive")
				d.Show(
					"the count of C and of the refinement differ by the points killing c at t",
					By(
						closedField,
						good,
						parts[0],
						parts[1],
						given[0],
						given[1],
						twisted_count.TwistedCountOffRefinement.Read(M).At(k, L, C, t, a, c, m, s)))
			}))
		arg.Show(
			"c, with the models it carries, is the refinement",
			Witness(c),
			Witness(z),
			Witness(F),
			Witness(b),
			By(parts[0], parts[1], models, counts))
	}),
})}

// ChartModelFacts — the chart of a ring X between S and K, with fraction field
// K and finite over S, is a ring between S and the composite of K with l, with
// the composite for fraction field, and finite over S: finite over X, and X is
// finite over S.
var ChartModelFacts = chartModelFactsThm{family.Add(registry.ProofEntry{
	Name: "ChartModelFacts",
	Key:  "prop_f0d8816414ca27a",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "constant_chart(field_ring(M), l, X)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), S)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S X:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"subring(field_ring(M), X)",
			"S ⊆ X",
			"k ⊆ X",
			"X ⊆ K",
			"fraction_field_carrier(field_ring(restrict_field(M, K)), X)",
			"module_finitely_generated(«scalars», restrict_module(regular_module(field_ring(M)), X))",
		},
		Conclusion: "subring(field_ring(M), «chart») ∧ " +
			"S ⊆ «chart» ∧ " +
			"fraction_field_carrier(field_ring(restrict_field(M, constant_composite(M, K, l))), «chart») ∧ " +
			"module_finitely_generated(«scalars», restrict_module(regular_module(field_ring(M)), «chart»))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, l, S, X *Expr[Set[A]],
		regular, lSubfield, kInL, finiteExtension, subringS, subringX, SInX, kInX, XInK, fractions, finiteX Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		kScalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
		lVectors := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(M)), l)")
		chart := a.TermAs[Set[A]]("«chart»")
		chartRing := a.Conjuncts(
			GroupPremises(
				regular,
				lSubfield,
				kInL,
				finiteExtension,
				subringX,
				XInK,
				kInX,
				constant_field_extension.ConstantChartRing.Read(M).At(K, k, l, X)),
			"the chart is a subring",
			"it holds l",
			"it holds X",
			"it carries ideals to ideals")
		E, basisData := a.ObtainAs[Set[A]](
			"take a finite k-basis of l",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(M), k), "+
				"        restrict_module(regular_module(field_ring(M)), l), "+
				"        E)",
			By(
				finiteExtension,
				field_extension.FiniteExtensionDef.At(ops, k, l),
				module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
		finiteChart := a.Have(
			"The chart is finite over X",
			"module_finitely_generated(restrict_ring(field_ring(M), X), "+
				"    restrict_module(regular_module(field_ring(M)), «chart»))",
			By(
				regular,
				lSubfield,
				kInL,
				basisData,
				subringX,
				XInK,
				kInX,
				constant_field_extension.ConstantChartFinite.Read(M).At(K, k, l, E, X)))
		overX := a.Have(
			"The chart is a submodule over X",
			"submodule(restrict_ring(field_ring(M), X), regular_module(field_ring(M)), «chart»)",
			By(
				chartRing[0],
				chartRing[2],
				principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(X, chart)))
		tower := a.Have(
			"so the chart is finite over S",
			"module_finitely_generated(«scalars», restrict_module(regular_module(field_ring(M)), «chart»))",
			By(
				SInX,
				subringS,
				subringX,
				overX,
				finiteX,
				finiteChart,
				principal_ideal_domain.FiniteModuleTower.Read(M).At(S, X, chart)))
		SInChart := a.Have(
			"The chart holds S",
			"S ⊆ «chart»",
			BySets(SInX, chartRing[2]))
		compositeFractions := a.Have(
			"The composite is the fraction field of the chart",
			"fraction_field_carrier(field_ring(restrict_field(M, constant_composite(M, K, l))), «chart»)",
			By(
				regular,
				lSubfield,
				kInL,
				finiteExtension,
				subringX,
				XInK,
				kInX,
				fractions,
				constant_field_extension.ConstantChartFractions.Read(M).At(K, k, l, X)))
		a.Show(
			"the four facts",
			By(chartRing[0], SInChart, compositeFractions, tower))
	}),
})}

// CompositeSeparable — every member of the composite of L with the finite
// constants is separable over k(t). L is finitely generated over k by separable
// elements, and the constants are separable over k, Galois as they are; their
// minimal polynomials are separable over k(t) and split in the closed field M,
// so the field of their roots is Galois over k(t), and it holds the composite.
var CompositeSeparable = compositeSeparableThm{family.Add(registry.ProofEntry{
	Name: "CompositeSeparable",
	Key:  "prop_b6f6aa69d0869d30",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "minimal", Text: "λE:set(A). image(minimal_polynomial(M, «base»), E ∪ «constants»)"},
			{Name: "roots", Text: "λE:set(A). " +
				"    {x:A | x ∈ M.carrier ∧ (∃p:(num → A). p ∈ «minimal»(E) ∧ polynomial_eval(p, x) = M.zero)}"},
			{Name: "rootField", Text: "λE:set(A). field_adjoin(M, «base», «roots»(E))"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀r:num. ∀x:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"galois_over(M, «base», L)",
			"0 < r",
			"x ∈ «composite»",
		},
		Conclusion: "separable_over(M, «base», x)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		r *Expr[Nat],
		x *Expr[A],
		closed, regular, finiteK, tInL, galois, positive, inComposite Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		base := a.TermAs[Set[A]]("«base»")
		constants := a.TermAs[Set[A]]("«constants»")
		single := a.TermAs[Set[A]]("{t}")
		data := a.Conjuncts(
			GroupPremises(
				regular, finiteK, positive, constant_galois.ConstantCompositeData.Read(M).At(L, k, r)),
			"k is a subfield",
			"L is a subfield",
			"k lies in L",
			"the constants of L are k",
			"l is a subfield",
			"k lies in l",
			"l is finite",
			"l is finite over k",
			"the composite is a subfield",
			"it holds L",
			"it holds l")
		kSubfield, LSubfield, lSubfield, kInConstants := data[0], data[1], data[4], data[5]
		E, generated := a.ObtainAs[Set[A]](
			"take finitely many generators of L over k",
			"∃E:set(A). finite(E) ∧ E ⊆ L ∧ field_adjoin(M, k, E) = L",
			By(a.Unfolded(regular, function_field.RegularFunctionFieldDef)))
		generators := a.Conjuncts(
			generated,
			"E is finite",
			"E lies in L",
			"E generates L")
		LInField := a.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(LSubfield, field.SubfieldSubset.At(ops, L)))
		kInField := a.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(kSubfield, field.SubfieldSubset.At(ops, k)))
		lInField := a.Have(
			"l lies in M",
			"«constants» ⊆ M.carrier",
			By(lSubfield, field.SubfieldSubset.At(ops, constants)))
		singleInL := a.Have(
			"{t} lies in L",
			"{t} ⊆ L",
			By(tInL, set_order.SingSubset.At(L, t)))
		singleInField := a.Have(
			"{t} lies in M",
			"{t} ⊆ M.carrier",
			BySets(singleInL, LInField))
		baseData := a.Conjuncts(
			a.Have(
				"k(t) is a subfield holding k",
				"subfield(M, «base») ∧ k ⊆ «base» ∧ {t} ⊆ «base»",
				By(kInField, singleInField, algebraic_element.AdjoinSubfield.Read(M).At(k, single))),
			"k(t) is a subfield",
			"it holds k",
			"it holds t")
		baseSubfield, kInBase := baseData[0], baseData[1]
		baseInField := a.Have(
			"k(t) lies in M",
			"«base» ⊆ M.carrier",
			By(baseSubfield, field.SubfieldSubset.At(ops, base)))
		galoisConstants := a.Have(
			"l is Galois over k: as many automorphisms as its degree",
			"galois_over(M, k, «constants»)",
			By(
				kSubfield,
				lSubfield,
				kInConstants,
				data[7],
				closed,
				finiteK,
				positive,
				finite_field.FiniteConstantsAutomorphisms.At(ops, k, r),
				cardinality.HasSizeDef.At(
					a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, k, «constants»)"), r),
				galois_correspondence.GaloisIffCard.Read(M).At(k, constants)))
		generatorsData := a.Conjuncts(
			a.Have(
				"The members of L and of l are separable over their fields",
				"(∀x:A. x ∈ L ⇒ separable_over(M, «base», x)) ∧ (∀x:A. x ∈ «constants» ⇒ separable_over(M, k, x))",
				By(
					galois,
					galoisConstants,
					galois_correspondence.GaloisOverDef.At(ops, base, L),
					galois_correspondence.GaloisOverDef.At(ops, k, constants))),
			"members of L are separable over k(t)",
			"members of l are separable over k")
		union := a.TermAs[Set[A]]("E ∪ «constants»")
		separableAll := a.Have(
			"Each generator is separable over k(t)",
			"∀b:A. b ∈ E ∪ «constants» ⇒ b ∈ M.carrier ∧ separable_over(M, «base», b)",
			Derive(func(c *Argument) {
				point := c.FixAs[A]("b")
				inUnion := c.Assume()
				inM := c.Have(
					"b lies in M",
					"b ∈ M.carrier",
					BySets(inUnion, generators[1], LInField, lInField))
				pointM := c.MemberOf[on.M](point, inM)
				c.Cases(c.Term("b ∈ L"))
				c.When(
					"a member of L is separable over k(t)",
					func(d *Argument, inL Fact) {
						d.Show(
							"by L being Galois",
							By(inM, inL, generatorsData[0].At(point)))
					})
				c.Otherwise(
					"a constant climbs from k to k(t)",
					func(d *Argument, outside Fact) {
						inConstants := d.Have(
							"b lies in l",
							"b ∈ «constants»",
							BySets(inUnion, outside, generators[1]))
						d.Show(
							"separability climbs",
							By(
								inM,
								kSubfield,
								baseSubfield,
								kInBase,
								pointM,
								inConstants,
								generatorsData[1].At(point),
								galois_correspondence.SeparableTower.Read(M).At(k, base, pointM)))
					})
			}))
		minimalData := a.Have(
			"Each generator is a root of its minimal polynomial, over k(t) and separable",
			Statement{
				Binders:    "∀b:A.",
				Hypotheses: []string{"b ∈ E ∪ «constants»"},
				Conclusion: "polynomial_over(«base», minimal_polynomial(M, «base», b)) ∧ " +
					"polynomial_separable(restrict_ring(field_ring(M), «base»), minimal_polynomial(M, «base», b)) ∧ " +
					"polynomial_eval(minimal_polynomial(M, «base», b), b) = M.zero ∧ " +
					"b ∈ M.carrier",
			},
			Derive(func(c *Argument) {
				point := c.FixAs[A]("b")
				inUnion := c.Assume()
				parts := c.Conjuncts(
					c.Have(
						"b lies in M and is separable over k(t)",
						"b ∈ M.carrier ∧ separable_over(M, «base», b)",
						By(inUnion, separableAll.At(point))),
					"b lies in M",
					"b is separable over k(t)")
				pointM := c.MemberOf[on.M](point, parts[0])
				opened := c.Conjuncts(
					c.Unfolded(parts[1], galois_correspondence.SeparableOverDef),
					"b is algebraic over k(t)",
					"its minimal polynomial is separable")
				c.Show(
					"the minimal polynomial is over k(t) and vanishes at b",
					By(
						baseSubfield,
						pointM,
						opened[0],
						opened[1],
						algebraic_element.MinimalPolynomialSpec.Read(M).At(base, pointM)))
			}))
		minimalMap := a.TermAs[Fun[A, Fun[Nat, A]]]("minimal_polynomial(M, «base»)")
		minimal := a.TermAs[Set[Fun[Nat, A]]]("«minimal»(E)")
		inMinimal := a.Have(
			"A member of the set is over k(t), separable, and splits in M",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"p ∈ «minimal»(E)"},
				Conclusion: "polynomial_over(«base», p) ∧ " +
					"polynomial_separable(restrict_ring(field_ring(M), «base»), p) ∧ " +
					"polynomial_splits(field_ring(M), p)",
			},
			Derive(func(c *Argument) {
				p := c.FixAs[Fun[Nat, A]]("p")
				inP := c.Assume()
				point, chosen := c.ObtainAs[A](
					"p is the minimal polynomial of a generator",
					"∃b:A. p = minimal_polynomial(M, «base», b) ∧ b ∈ E ∪ «constants»",
					By(inP, set_basic.InImage.At(minimalMap, union, p)))
				parts := c.Conjuncts(
					chosen,
					"p is minimal at b",
					"b is a generator")
				c.Show(
					"its data, and M is closed",
					By(
						closed,
						parts[0],
						minimalData.At(point),
						parts[1],
						algebraic_closure.ClosedFieldSplits.Read(M).At(p)))
			}))
		finiteUnion := a.Have(
			"Finitely many generators",
			"finite(E ∪ «constants»)",
			By(generators[0], data[6], finite_set.FiniteUnion.At(E, constants)))
		galoisRoots := a.Have(
			"The roots generate a Galois extension of k(t)",
			"galois_over(M, «base», «rootField»(E))",
			By(
				baseSubfield,
				finiteUnion,
				finite_set.FiniteImage.At(minimalMap, union),
				inMinimal,
				galois_correspondence.SeparableRootFieldGalois.Read(M).At(base, minimal)))
		rootsSet := a.TermAs[Set[A]]("«roots»(E)")
		rootsInField := a.Have(
			"The roots lie in M",
			"«roots»(E) ⊆ M.carrier",
			BySets())
		rootData := a.Conjuncts(
			a.Have(
				"The root field is a subfield holding k(t) and the roots",
				"subfield(M, «rootField»(E)) ∧ «base» ⊆ «rootField»(E) ∧ «roots»(E) ⊆ «rootField»(E)",
				By(baseInField, rootsInField, algebraic_element.AdjoinSubfield.Read(M).At(base, rootsSet))),
			"the root field is a subfield",
			"it holds k(t)",
			"it holds the roots")
		rootField := a.TermAs[Set[A]]("«rootField»(E)")
		generatorsInRoots := a.Have(
			"Each generator is a root",
			"E ∪ «constants» ⊆ «rootField»(E)",
			Derive(func(c *Argument) {
				c.Do(Simp(Fwd(set_basic.SubsetDef)))
				point := c.FixAs[A]("b")
				inUnion := c.Assume()
				parts := c.Conjuncts(
					GroupPremises(inUnion, minimalData.At(point)),
					"its minimal polynomial is over k(t)",
					"and separable",
					"and vanishes at b",
					"b lies in M")
				inMinimalSet := c.Have(
					"its minimal polynomial lies in the set",
					"minimal_polynomial(M, «base», b) ∈ «minimal»(E)",
					By(
						inUnion,
						set_basic.InImage.At(minimalMap, union, c.TermAs[Fun[Nat, A]]("minimal_polynomial(M, «base», b)"))))
				inRoots := c.Have(
					"so b is a root",
					"b ∈ «roots»(E)",
					BySets(parts[2], parts[3], inMinimalSet))
				c.Show(
					"and the root field holds the roots",
					BySets(inRoots, rootData[2]))
			}))
		inUnionLeft := a.Have(
			"E lies in the union",
			"E ⊆ E ∪ «constants»",
			BySets())
		inUnionRight := a.Have(
			"l lies in the union",
			"«constants» ⊆ E ∪ «constants»",
			BySets())
		kInRoots := a.Have(
			"k lies in the root field",
			"k ⊆ «rootField»(E)",
			BySets(kInBase, rootData[1]))
		LInRoots := a.Have(
			"L lies in the root field, generated over k by E",
			"L ⊆ «rootField»(E)",
			Derive(func(c *Argument) {
				EInRoots := c.Have(
					"E lies in the root field",
					"E ⊆ «rootField»(E)",
					By(generatorsInRoots, inUnionLeft, set_order.SubsetTrans.At(E, union, rootField)))
				c.Show(
					"by leastness",
					generators[2].RwRev(),
					By(rootData[0], kInRoots, EInRoots, algebraic_element.AdjoinLeast.Read(M).At(k, E, rootField)))
			}))
		constantsInRoots := a.Have(
			"l lies in the root field",
			"«constants» ⊆ «rootField»(E)",
			By(generatorsInRoots, inUnionRight, set_order.SubsetTrans.At(constants, union, rootField)))
		compositeInRoots := a.Have(
			"so the composite lies in the root field",
			"«composite» ⊆ «rootField»(E)",
			Unfold(constant_composite.ConstantCompositeDef),
			By(
				rootData[0],
				LInRoots,
				constantsInRoots,
				algebraic_element.AdjoinLeast.Read(M).At(L, constants, rootField)))
		separableRoots := a.Have(
			"Members of the root field are separable over k(t)",
			"∀x:A. x ∈ «rootField»(E) ⇒ separable_over(M, «base», x)",
			By(galoisRoots, galois_correspondence.GaloisOverDef.At(ops, base, rootField)))
		inRoots := a.Have(
			"x lies in the root field",
			"x ∈ «rootField»(E)",
			BySets(inComposite, compositeInRoots))
		a.Show(
			"so x is separable",
			By(inRoots, separableRoots.At(x)))
	}),
})}

// TwistModelAgrees — for one automorphism s the twisted field has an integral
// plane model whose chart, extended by the constants, agrees with the extended
// chart of a good open after inverting a polynomial p at t, and so after
// inverting any nonzero multiple of p(t). Over k[t] with a(t) inverted both
// extended charts are finite rings with fraction field the composite, so
// FiniteModelsAgreeAfterLocalization gives a common denominator d there, and d
// and p(t) differ by a power of the unit a(t).
var TwistModelAgrees = twistModelAgreesThm{family.Add(registry.ProofEntry{
	Name: "TwistModelAgrees",
	Key:  "prop_ad3018e2af477d52",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "twisted", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), «constants», X)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "value", Text: "λf:(num → A). polynomial_eval(f, t)"},
			{Name: "plane", Text: "λz:A. plane_chart_zero(restrict_ring(field_ring(M), «twisted»), k, t, z)"},
			{Name: "scalars", Text: "ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A). ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"s ∈ field_automorphisms(M, «base», L)",
		},
		Conclusion: "∃z:A. ∃F:(num → A). ∃b:num. " +
			"    integral_plane_model(restrict_field(M, «twisted»), k, t, z, F, b) ∧ " +
			"    (∃p:(num → A). " +
			"        polynomial_over(k, p) ∧ " +
			"        p ≠ vec_zero ∧ " +
			"        (∀g:A. " +
			"            g ≠ M.zero ∧ (∃q:(num → A). polynomial_over(k, q) ∧ g = «value»(p) * «value»(q)) ⇒ " +
			"            «chart»(ring_away(field_ring(M), C, g)) = " +
			"            «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t) * g))))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		s *Expr[symmetric_group.Permutation[A]],
		closed, good, inG Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		powers := comm_ring.MulMonoidOn.Read(ring)
		base := arg.TermAs[Set[A]]("«base»")
		constants := arg.TermAs[Set[A]]("«constants»")
		composite := arg.TermAs[Set[A]]("«composite»")
		twisted := arg.TermAs[Set[A]]("«twisted»")
		polynomials := arg.TermAs[Set[A]]("«polynomials»")
		scalars := arg.TermAs[Set[A]]("«scalars»")
		denominator := arg.TermAs[A]("polynomial_eval(a, t)")
		order := arg.TermAs[Nat]("permutation_order(s)")
		regular := arg.Have(
			"L is regular over k",
			"regular_function_field(M, k, L)",
			By(galois_good_open.GoodOpenRegular.Read(good)))
		finiteK := arg.Have(
			"k is finite",
			"finite(k)",
			By(galois_good_open.GoodOpenConstantsFinite.Read(good)))
		tInL := arg.Have(
			"t lies in L",
			"t ∈ L",
			By(galois_good_open.GoodOpenParameterIn.Read(good)))
		transcendental := arg.Have(
			"t is transcendental over k",
			"¬algebraic_over(M, k, t)",
			By(galois_good_open.GoodOpenParameterTranscendental.Read(good)))
		galois := arg.Have(
			"L is Galois over k(t)",
			"galois_over(M, «base», L)",
			By(galois_good_open.GoodOpenGalois.Read(good)))
		subfieldK, subfieldL :=
			galois_good_open.GoodOpenConstantsSubfield.Read(good),
			galois_good_open.GoodOpenFieldSubfield.Read(good)
		kInBase, tInBase, baseInL :=
			galois_good_open.GoodOpenConstantsInRational.Read(good),
			galois_good_open.GoodOpenParameterInRational.Read(good),
			galois_good_open.GoodOpenRationalInField.Read(good)
		subringPolynomials := arg.Have(
			"k[t] is a subring",
			"subring(field_ring(M), «polynomials»)",
			By(good, galois_good_open.GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		denominatorInPolynomials := galois_good_open.GoodOpenDenominatorInPolynomials.Read(good)
		denominatorNonzero := galois_good_open.GoodOpenDenominatorValueNonzero.Read(good)
		CInL := galois_good_open.GoodOpenChartInField.Read(good)
		LInField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subfieldL, field.SubfieldSubset.At(ops, L)))
		tm := arg.MemberOf[on.M](t, arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tInL, LInField)))
		denominatorM := arg.MemberOf[on.M](denominator, arg.Have(
			"a(t) lies in M",
			"polynomial_eval(a, t) ∈ M.carrier",
			BySets(
				good,
				galois_good_open.GoodOpenDenominatorInRational.Read(M).At(k, L, C, t, a),
				baseInL,
				LInField)))
		positive := arg.Have(
			"The order of s is positive",
			"0 < permutation_order(s)",
			By(
				good,
				galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
				subfieldL,
				baseInL,
				galois_good_open.GoodOpenFiniteExtension.Read(good),
				inG,
				field_automorphism.AutomorphismOrderFacts.Read(M).At(base, L, s)))
		constantData := arg.Conjuncts(
			arg.Have(
				"The constants are a finite extension of k inside the composite",
				"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite_extension(M, k, «constants») ∧ "+
					"subfield(M, «composite») ∧ "+
					"L ⊆ «composite»",
				By(
					closed,
					regular,
					finiteK,
					positive,
					constant_galois.ConstantCompositeData.Read(M).At(L, k, order))),
			"the constants are a subfield",
			"they hold k",
			"they are finite over k",
			"the composite is a subfield",
			"it holds L")
		subfieldConstants, kInConstants, finiteConstants, subfieldComposite :=
			constantData[0], constantData[1], constantData[2], constantData[3]
		descent := arg.Conjuncts(
			GroupPremises(
				closed,
				regular,
				finiteK,
				tInL,
				transcendental,
				galois,
				inG,
				constant_twist.CyclicConstantTwistDescent.Read(M).At(k, L, t, s)),
			"the twist has the order of s",
			"the twisted field is regular over k",
			"it is finite over k(t)",
			"it has the degree of G",
			"its composite is the composite of L",
			"the Frobenius lift fixes t")
		twistedData := arg.Conjuncts(
			arg.Have(
				"The twisted field is a subfield between k(t) and the composite",
				"subfield(M, «twisted») ∧ «base» ⊆ «twisted» ∧ «twisted» ⊆ «composite»",
				By(
					closed,
					regular,
					finiteK,
					tInL,
					transcendental,
					galois,
					inG,
					constant_twist.ConstantTwistFieldData.Read(M).At(k, L, t, s))),
			"the twisted field is a subfield",
			"it holds k(t)",
			"it lies in the composite")
		subfieldTwisted := twistedData[0]
		tInTwisted := arg.Have(
			"t lies in the twisted field",
			"t ∈ «twisted»",
			BySets(tInBase, twistedData[1]))
		kInTwisted := arg.Have(
			"k lies in the twisted field",
			"k ⊆ «twisted»",
			BySets(kInBase, twistedData[1]))
		separableMembers := arg.Have(
			"Members of the twisted field are separable over k(t)",
			"∀x:A. x ∈ «twisted» ⇒ separable_over(M, «base», x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inTwisted := b.Assume()
				inComposite := b.Have(
					"x lies in the composite",
					"x ∈ «composite»",
					BySets(inTwisted, twistedData[2]))
				b.Show(
					"where every member is separable",
					By(
						closed,
						regular,
						finiteK,
						tInL,
						galois,
						positive,
						inComposite,
						CompositeSeparable.Read(M).At(k, L, t, order, x)))
			}))
		z, F, bound, model := arg.Unpack3As[A, Fun[Nat, A], Nat](
			GroupPremises(
				descent[1],
				tInTwisted,
				transcendental,
				descent[2],
				separableMembers,
				plane_model.IntegralPlaneModelExists.Read(M).At(twisted, k, t)),
			"z",
			"F",
			"b")
		curve := arg.Conjuncts(
			GroupPremises(
				twistedData[0],
				model,
				plane_model.PlaneEquationBiaffineCurve.Read(M).At(twisted, k, t, z, F, bound)),
			"the charts of the model are a curve",
			"the powers of z are a basis of the affine chart over k[t]")
		affine := arg.TermAs[Set[A]]("«plane»(z)")
		affineFractions := arg.Have(
			"The twisted field is the fraction field of the affine chart",
			"fraction_field_carrier(field_ring(restrict_field(M, «twisted»)), «plane»(z))",
			By(arg.Unfolded(curve[0], algebraic_curve.CurveOverLineDef)))
		E, basisData := arg.UnpackAs[Set[A]](curve[1], "E")
		basisParts := arg.Conjuncts(
			basisData,
			"E is finite",
			"E is the powers of z",
			"E is a basis")
		zInTwisted := arg.Have(
			"z lies in the twisted field",
			"z ∈ «twisted»",
			By(arg.Unfolded(model, plane_model.IntegralPlaneModelDef)))
		sameChart := arg.Have(
			"The affine chart is k[t][z] under the operations of M",
			"«plane»(z) = polynomial_image(field_ring(M), «polynomials», z)",
			Simp(Fwd(plane_model.PlaneChartZeroDef), Fwd(algebraic_element.PolynomialImageDef)),
			Basic())
		chartData := arg.Conjuncts(
			arg.Simplified(
				arg.Have(
					"k[t][z] is a subring holding k[t], and inverting a(t) stays in the twisted field",
					"subring(field_ring(M), polynomial_image(field_ring(M), «polynomials», z)) ∧ "+
						"«polynomials» ⊆ polynomial_image(field_ring(M), «polynomials», z) ∧ "+
						"subring(field_ring(M), "+
						"    ring_away(field_ring(M), "+
						"        polynomial_image(field_ring(M), «polynomials», z), "+
						"        polynomial_eval(a, t))) ∧ "+
						"polynomial_image(field_ring(M), «polynomials», z) ⊆ "+
						"ring_away(field_ring(M), "+
						"    polynomial_image(field_ring(M), «polynomials», z), "+
						"    polynomial_eval(a, t)) ∧ "+
						"ring_away(field_ring(M), "+
						"    polynomial_image(field_ring(M), «polynomials», z), "+
						"    polynomial_eval(a, t)) ⊆ "+
						"«twisted»",
					By(
						subfieldK,
						subfieldTwisted,
						kInTwisted,
						tInTwisted,
						zInTwisted,
						galois_good_open.GoodOpenDenominatorOver.Read(good),
						denominatorNonzero,
						galois_good_fibres.ChartFacts.Read(M).At(k, twisted, t, z, a))),
				Rev(sameChart)),
			"the affine chart is a subring",
			"it holds k[t]",
			"its localization is a subring",
			"the localization holds the chart",
			"the localization lies in the twisted field")
		subringAffine, polynomialsInAffine, subringT, affineInT, TInTwisted :=
			chartData[0], chartData[1], chartData[2], chartData[3], chartData[4]
		localized := arg.TermAs[Set[A]]("ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))")
		inverse := field.InvIn.Read(M).At(denominatorM)
		scalarData := arg.Conjuncts(
			arg.Have(
				"k[t] with a(t) inverted is a subring holding k[t] and the inverse of a(t)",
				"«polynomials» ⊆ «scalars» ∧ "+
					"subring(field_ring(M), «scalars») ∧ "+
					"M.inv(polynomial_eval(a, t)) ∈ «scalars»",
				By(
					ring,
					subringPolynomials,
					denominatorInPolynomials,
					denominatorNonzero,
					inverse,
					field.MulRightInverseOn.Read(M).At(denominatorM),
					ring_away.RingAwaySubring.At(fieldRing, polynomials, denominator))),
			"it holds k[t]",
			"it is a subring",
			"it holds the inverse of a(t)")
		polynomialsInScalars, subringScalars, inverseInScalars :=
			scalarData[0], scalarData[1], scalarData[2]
		scalarsInC := galois_good_open.GoodOpenChartHoldsBase.Read(good)
		scalarsInT := arg.Have(
			"k[t] with a(t) inverted lies in the localized chart",
			"«scalars» ⊆ ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))",
			BySets(
				polynomialsInAffine,
				ring_away.RingAwayDef.At(fieldRing, polynomials, denominator),
				ring_away.RingAwayDef.At(fieldRing, affine, denominator)))
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ C",
			By(good, galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a)))
		kInT := arg.Have(
			"k lies in the localized chart",
			"k ⊆ ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))",
			BySets(
				good,
				galois_good_open.GoodOpenConstantsInPolynomials.Read(M).At(k, L, C, t, a),
				polynomialsInAffine,
				affineInT))
		basisT := arg.Have(
			"The powers of z are a basis of the localized chart over k[t] with a(t) inverted",
			"module_basis(restrict_ring(field_ring(M), «scalars»), "+
				"    restrict_module(regular_module(field_ring(M)), "+
				"        ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), "+
				"    E)",
			By(
				subringPolynomials,
				subringAffine,
				polynomialsInAffine,
				denominatorInPolynomials,
				denominatorNonzero,
				basisParts[2],
				ring_away.BasisAway.Read(M).At(polynomials, affine, denominator, E)))
		onBasis := arg.Conjuncts(
			arg.Unfolded(basisT, linear_independence.ModuleBasisDef),
			"E is independent",
			"E spans the localized chart")
		finiteT := arg.Have(
			"so the localized chart is finite over k[t] with a(t) inverted",
			"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), "+
				"    restrict_module(regular_module(field_ring(M)), "+
				"        ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))))",
			Unfold(principal_ideal_domain.FinitelyGeneratedDef),
			Witness(E),
			By(basisParts[0], onBasis[1], linear_independence.IndependentInCarrier.Read(onBasis[0])))
		fractionsT := arg.Have(
			"so the twisted field is the fraction field of the localized "+
				"chart, which holds the chart and lies in the twisted field",
			"fraction_field_carrier(field_ring(restrict_field(M, «twisted»)), "+
				"    ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))",
			By(
				affineFractions,
				affineInT,
				TInTwisted,
				field.FractionFieldCarrierMono.At(
					arg.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, «twisted»))"),
					arg.TermAs[Set[A]]("«plane»(z)"),
					arg.TermAs[Set[A]]("ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))"))))
		fractionsC := arg.Have(
			"L is the fraction field of C",
			"fraction_field_carrier(field_ring(restrict_field(M, L)), C)",
			Simp(Rev(field.RestrictFieldRing)),
			By(galois_good_open.GoodOpenFractionField.Read(good)))
		chartC := arg.Conjuncts(
			arg.Have(
				"The extended chart of C is a finite ring over k[t] "+
					"with a(t) inverted, with fraction field the composite",
				"subring(field_ring(M), «chart»(C)) ∧ "+
					"«scalars» ⊆ «chart»(C) ∧ "+
					"fraction_field_carrier(field_ring(restrict_field(M, «composite»)), «chart»(C)) ∧ "+
					"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), "+
					"    restrict_module(regular_module(field_ring(M)), «chart»(C)))",
				By(
					regular,
					subfieldConstants,
					kInConstants,
					finiteConstants,
					subringScalars,
					subringC,
					scalarsInC,
					kInC,
					CInL,
					fractionsC,
					galois_good_open.GoodOpenChartFinite.Read(good),
					ChartModelFacts.Read(M).At(L, k, constants, scalars, C))),
			"the chart of C is a subring",
			"it holds the scalars",
			"its fraction field is the composite",
			"it is finite over the scalars")
		chartT := arg.Conjuncts(
			arg.Simplified(
				arg.Have(
					"The extended chart of the model is a finite ring too",
					"subring(field_ring(M), «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))) ∧ "+
						"«scalars» ⊆ «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))) ∧ "+
						"fraction_field_carrier( "+
						"    field_ring(restrict_field(M, constant_composite(M, «twisted», «constants»))), "+
						"    «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))) ∧ "+
						"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), "+
						"    restrict_module(regular_module(field_ring(M)), "+
						"        «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))))",
					By(
						descent[1],
						subfieldConstants,
						kInConstants,
						finiteConstants,
						subringScalars,
						subringT,
						scalarsInT,
						kInT,
						TInTwisted,
						fractionsT,
						finiteT,
						ChartModelFacts.Read(M).At(twisted, k, constants, scalars, localized))),
				Fwd(descent[4])),
			"the chart of the model is a subring",
			"it holds the scalars",
			"its fraction field is the composite",
			"it is finite over the scalars")
		chartOfC := arg.TermAs[Set[A]]("«chart»(C)")
		chartOfModel := arg.TermAs[Set[A]](
			"«chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))")
		fieldComposite := arg.Have(
			"The composite is a field",
			"field_on(restrict_field(M, «composite»))",
			By(subfieldComposite, field.SubfieldFieldOn.Read(M).At(composite)))
		chartCInComposite := arg.Have(
			"The chart of C lies in the composite",
			"«chart»(C) ⊆ «composite»",
			By(arg.Unfolded(chartC[2], field.FractionFieldCarrierDef)))
		chartTInComposite := arg.Have(
			"The chart of the model lies in the composite",
			"«chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))) ⊆ «composite»",
			By(arg.Unfolded(chartT[2], field.FractionFieldCarrierDef)))
		scalarsInComposite := arg.Have(
			"So do the scalars",
			"«scalars» ⊆ «composite»",
			BySets(chartC[1], chartCInComposite))
		readIn := arg.Have(
			"A subring of M inside the composite is a subring read in the composite",
			Statement{
				Binders:    "∀X:set(A).",
				Hypotheses: []string{"subring(field_ring(M), X)", "X ⊆ «composite»"},
				Conclusion: "subring(field_ring(restrict_field(M, «composite»)), X)",
			},
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				given := b.Conjuncts(
					b.Assume(),
					"X is a subring",
					"X lies in the composite")
				b.Show(
					"restriction keeps the operations",
					By(
						given[0],
						given[1],
						field.RestrictFieldRing.At(ops, composite),
						comm_ring.SubringRestrict.At(fieldRing, X, composite)))
			}))
		finiteIn := arg.Have(
			"Finiteness over the scalars reads the same in the composite",
			Statement{
				Binders: "∀X:set(A).",
				Hypotheses: []string{
					"module_finitely_generated(restrict_ring(field_ring(M), «scalars»), " +
						"    restrict_module(regular_module(field_ring(M)), X))",
				},
				Conclusion: "module_finitely_generated( " +
					"    restrict_ring(field_ring(restrict_field(M, «composite»)), «scalars»), " +
					"    restrict_module(regular_module(field_ring(restrict_field(M, «composite»))), X))",
			},
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				given := b.Assume()
				onScalars := b.Conjuncts(
					field.RestrictFieldRecords.At(ops, composite, scalars),
					"the scalars read the same",
					"the scalars as a module read the same")
				onX := b.Conjuncts(
					field.RestrictFieldRecords.At(ops, composite, X),
					"X as a ring reads the same",
					"X as a module reads the same")
				b.Show(
					"restriction keeps the operations",
					onScalars[0].Rw(),
					onX[1].Rw(),
					By(given))
			}))
		scalarsSubring := arg.Have(
			"The scalars are a subring read in the composite",
			"subring(field_ring(restrict_field(M, «composite»)), «scalars»)",
			By(subringScalars, scalarsInComposite, readIn.At(scalars)))
		chartCSubring := arg.Have(
			"The chart of C is a subring read in the composite",
			"subring(field_ring(restrict_field(M, «composite»)), «chart»(C))",
			By(chartC[0], chartCInComposite, readIn.At(chartOfC)))
		modelChartSubring := arg.Have(
			"The chart of the model is a subring read in the composite",
			"subring(field_ring(restrict_field(M, «composite»)), "+
				"    «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))))",
			By(chartT[0], chartTInComposite, readIn.At(chartOfModel)))
		chartCFinite := arg.Have(
			"The chart of C is finite in the composite",
			"module_finitely_generated(restrict_ring(field_ring(restrict_field(M, «composite»)), «scalars»), "+
				"    restrict_module(regular_module(field_ring(restrict_field(M, «composite»))), «chart»(C)))",
			By(chartC[3], finiteIn.At(chartOfC)))
		modelChartFinite := arg.Have(
			"The chart of the model is finite in the composite",
			"module_finitely_generated(restrict_ring(field_ring(restrict_field(M, «composite»)), «scalars»), "+
				"    restrict_module(regular_module(field_ring(restrict_field(M, «composite»))), "+
				"        «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))))",
			By(chartT[3], finiteIn.At(chartOfModel)))
		d, agreement := arg.UnpackAs[A](
			GroupPremises(
				scalarsSubring,
				chartCSubring,
				modelChartSubring,
				chartC[1],
				chartT[1],
				chartC[2],
				chartT[2],
				chartCFinite,
				modelChartFinite,
				good_localization.FiniteModelsAgreeAfterLocalization.Read(fieldComposite).At(
					scalars, chartOfC, chartOfModel)),
			"d")
		agreed := arg.Conjuncts(
			agreement,
			"d lies in the scalars",
			"d is nonzero",
			"the two charts agree with d inverted")
		dInComposite := arg.Have(
			"d lies in the composite",
			"d ∈ «composite»",
			BySets(agreed[0], scalarsInComposite))
		dInverse := arg.Have(
			"so does its inverse",
			"M.inv(d) ∈ «composite»",
			By(subfieldComposite, dInComposite, field.SubfieldInv.At(ops, composite, d)))
		dData := arg.Conjuncts(
			arg.Have(
				"d lies in M, and a power of a(t) brings it into k[t]",
				"d ∈ M.carrier ∧ (∃j:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), j) * d ∈ «polynomials»)",
				By(agreed[0], ring_away.RingAwayMember.At(fieldRing, polynomials, denominator, d))),
			"d lies in M",
			"a power of a(t) brings d into k[t]")
		dm := arg.MemberOf[on.M](d, dData[0])
		subringComposite := arg.Have(
			"The composite is a subring of M",
			"subring(field_ring(M), «composite»)",
			By(subfieldComposite, field.SubfieldSubring.Read(M).At(composite)))
		inM := arg.Have(
			"Inverting d inside the composite is inverting it in M",
			Statement{
				Binders:    "∀X:set(A).",
				Hypotheses: []string{"X ⊆ «composite»"},
				Conclusion: "ring_away(field_ring(restrict_field(M, «composite»)), X, d) = " +
					"ring_away(field_ring(M), X, d)",
			},
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				inside := b.Assume()
				b.Show(
					"the composite holds d and its inverse",
					Simp(Rev(field.RestrictFieldRing)),
					By(
						ring,
						subringComposite,
						dInComposite,
						inside,
						dInverse,
						agreed[1],
						dm,
						field.MulRightInverseOn.Read(M).At(dm),
						ring_away.RingAwayInSubring.At(fieldRing, composite, X, d, b.TermAs[A]("M.inv(d)"))))
			}))
		agreeInM := arg.Have(
			"So the charts agree with d inverted, in M",
			"ring_away(field_ring(M), «chart»(C), d) = "+
				"ring_away(field_ring(M), «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), d)",
			GroupPremises(chartCInComposite, inM.At(chartOfC)).RwRev(),
			GroupPremises(chartTInComposite, inM.At(chartOfModel)).RwRev(),
			By(agreed[2]))
		j, numeratorIn := arg.UnpackAs[Nat](dData[1], "j")
		u, uIs := arg.LetAs[A]("u", "monoid_pow(M.mul, M.one, polynomial_eval(a, t), j)")
		v, vIs := arg.LetAs[A]("v", "monoid_pow(M.mul, M.one, M.inv(polynomial_eval(a, t)), j)")
		ringOfScalars := arg.Have(
			"The scalars are a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), «scalars»))",
			By(subringScalars, comm_ring.SubringRingOn.Read(ring).At(scalars)))
		powersOfScalars := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringOfScalars)).AsFact()
		denominatorInScalars := arg.Have(
			"a(t) lies in the scalars",
			"polynomial_eval(a, t) ∈ «scalars»",
			BySets(denominatorInPolynomials, polynomialsInScalars))
		uInScalars := arg.Have(
			"u lies in the scalars",
			"u ∈ «scalars»",
			By(uIs, denominatorInScalars, powersOfScalars.At(denominator, j)))
		vInScalars := arg.Have(
			"v lies in the scalars",
			"v ∈ «scalars»",
			By(vIs, inverseInScalars, powersOfScalars.At(arg.TermAs[A]("M.inv(polynomial_eval(a, t))"), j)))
		scalarsInField := arg.Have(
			"The scalars lie in M",
			"«scalars» ⊆ M.carrier",
			By(comm_ring.SubringSubset.Read(subringScalars)))
		um := arg.MemberOf[on.M](u, arg.Have(
			"u lies in M",
			"u ∈ M.carrier",
			BySets(uInScalars, scalarsInField)))
		vm := arg.MemberOf[on.M](v, arg.Have(
			"v lies in M",
			"v ∈ M.carrier",
			BySets(vInScalars, scalarsInField)))
		cancels := arg.Have(
			"u and v are inverse",
			"u * v = M.one",
			By(
				uIs,
				vIs,
				denominatorNonzero,
				field.MulRightInverseOn.Read(M).At(denominatorM),
				comm_monoid.PowInverseOn.Read(powers).At(denominatorM, inverse, j)))
		uNonzero := arg.Have(
			"so u is nonzero",
			"u ≠ M.zero",
			Derive(func(b *Argument) {
				zeroU := b.SupposeNot()
				b.Show(
					"zero has no inverse",
					By(
						Normalized,
						zeroU,
						cancels,
						field.OneNotZeroOn.Read(M),
						comm_ring.MulLeftZeroOn.Read(ring).At(vm)))
			}))
		valuesOf := arg.Have(
			"A member of k[t] is the value at t of a polynomial over k",
			"∀w:A. w ∈ «polynomials» ⇒ ∃f:(num → A). polynomial_over(k, f) ∧ w = «value»(f)",
			BySets(algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
		numerator := arg.TermAs[A]("u * d")
		p, pData := arg.UnpackAs[Fun[Nat, A]](GroupPremises(numeratorIn, valuesOf.At(numerator)), "p")
		pParts := arg.Conjuncts(
			pData,
			"p is a polynomial over k",
			"u · d is p(t)")
		pValueNonzero := arg.Have(
			"p(t) is nonzero",
			"«value»(p) ≠ M.zero",
			Derive(func(b *Argument) {
				zeroValue := b.SupposeNot()
				b.Show(
					"a product of nonzero factors is nonzero",
					By(zeroValue, pParts[1], uNonzero, agreed[1], um, dm, field.MulEqZeroOn.Read(M).At(um, dm)))
			}))
		pNonzero := arg.Have(
			"so p is nonzero",
			"p ≠ vec_zero",
			Derive(func(b *Argument) {
				isZero := b.Have(
					"p is the zero vector",
					"p = vec_zero",
					By(Normalized, b.SupposeNot()))
				vanishes := b.Have(
					"so p vanishes at t",
					"«value»(p) = M.zero",
					isZero.Rw(),
					By(polynomial_evaluation.EvalVecZero.Read(ring).At(tm)))
				b.Show(
					"which it does not",
					By(vanishes, pValueNonzero))
			}))
		pValue := arg.TermAs[A]("«value»(p)")
		unitOff := arg.Have(
			"Inverting p(t) in a ring over the scalars is inverting d, u being a unit there",
			Statement{
				Binders:    "∀X:set(A).",
				Hypotheses: []string{"subring(field_ring(M), X)", "«scalars» ⊆ X"},
				Conclusion: "ring_away(field_ring(M), X, «value»(p)) = ring_away(field_ring(M), X, d)",
			},
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				given := b.Conjuncts(
					b.Assume(),
					"X is a subring",
					"X holds the scalars")
				uInX := b.Have(
					"u lies in X",
					"u ∈ X",
					BySets(uInScalars, given[1]))
				vInX := b.Have(
					"v lies in X",
					"v ∈ X",
					BySets(vInScalars, given[1]))
				dInX := b.Have(
					"d lies in X",
					"d ∈ X",
					BySets(agreed[0], given[1]))
				twice := b.Have(
					"Inverting u and then d is inverting their product",
					"ring_away(field_ring(M), ring_away(field_ring(M), X, u), d) = ring_away(field_ring(M), X, u * d)",
					By(given[0], uInX, dInX, ring_away.RingAwayTwice.Read(M).At(X, u, d)))
				unit := b.Have(
					"and inverting the unit u changes nothing",
					"ring_away(field_ring(M), X, u) = X",
					By(given[0], uInX, vInX, cancels, ring_away.AwayOfUnit.Read(M).At(X, u, v)))
				b.Show(
					"p(t) is u · d",
					pParts[1].RwRev(),
					twice.RwRev(),
					unit.Rw(),
					Basic())
			}))
		atP := arg.Have(
			"So the charts agree with p(t) inverted",
			"ring_away(field_ring(M), «chart»(C), «value»(p)) = "+
				"ring_away(field_ring(M), "+
				"    «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), "+
				"    «value»(p))",
			GroupPremises(chartC[0], chartC[1], unitOff.At(chartOfC)).Rw(),
			GroupPremises(chartT[0], chartT[1], unitOff.At(chartOfModel)).Rw(),
			By(agreeInM))
		multiples := arg.Have(
			"Each nonzero multiple of p(t) serves",
			Statement{
				Binders: "∀g:A.",
				Hypotheses: []string{
					"g ≠ M.zero",
					"∃q:(num → A). polynomial_over(k, q) ∧ g = «value»(p) * «value»(q)",
				},
				Conclusion: "«chart»(ring_away(field_ring(M), C, g)) = " +
					"«chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t) * g))",
			},
			Derive(func(b *Argument) {
				g := b.FixAs[A]("g")
				given := b.Conjuncts(
					b.Assume(),
					"g is nonzero",
					"g is a multiple of p(t)")
				_, qData := b.UnpackAs[Fun[Nat, A]](given[1], "q")
				qParts := b.Conjuncts(
					qData,
					"q is a polynomial over k",
					"g is p(t) · q(t)")
				qValue := b.TermAs[A]("«value»(q)")
				pInPolynomials := b.Have(
					"p(t) lies in k[t]",
					"«value»(p) ∈ «polynomials»",
					BySets(pParts[0], algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
				qInPolynomials := b.Have(
					"q(t) lies in k[t]",
					"«value»(q) ∈ «polynomials»",
					BySets(qParts[0], algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
				gInPolynomials := b.Have(
					"so g lies in k[t]",
					"g ∈ «polynomials»",
					By(
						Normalized,
						qParts[1],
						subringPolynomials,
						pInPolynomials,
						qInPolynomials,
						comm_ring.SubringMul.At(fieldRing, polynomials, pValue, qValue)))
				gInC := b.Have(
					"g lies in C",
					"g ∈ C",
					BySets(gInPolynomials, good, galois_good_open.GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
				gInAffine := b.Have(
					"g lies in the affine chart",
					"g ∈ «plane»(z)",
					BySets(gInPolynomials, polynomialsInAffine))
				gInT := b.Have(
					"g lies in the localized chart",
					"g ∈ ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))",
					BySets(gInAffine, affineInT))
				forC := b.Have(
					"Inverting g commutes with taking the chart: chart(C[1/g]) = chart(C)[1/g]",
					"«chart»(ring_away(field_ring(M), C, g)) = ring_away(field_ring(M), «chart»(C), g)",
					By(
						regular,
						subfieldConstants,
						kInConstants,
						finiteConstants,
						subringC,
						CInL,
						kInC,
						gInC,
						given[0],
						constant_field_extension.ConstantChartOfAway.Read(M).At(L, k, constants, C, g)))
				forT := b.Have(
					"as for the model",
					"«chart»( "+
						"    ring_away(field_ring(M), ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)), g)) = "+
						"ring_away(field_ring(M), «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), g)",
					By(
						descent[1],
						subfieldConstants,
						kInConstants,
						finiteConstants,
						subringT,
						TInTwisted,
						kInT,
						gInT,
						given[0],
						constant_field_extension.ConstantChartOfAway.Read(M).At(twisted, k, constants, localized, g)))
				denominatorInAffine := b.Have(
					"a(t) lies in the affine chart",
					"polynomial_eval(a, t) ∈ «plane»(z)",
					BySets(denominatorInPolynomials, polynomialsInAffine))
				affineTwice := b.Have(
					"Inverting a(t) and then g in the affine chart is inverting their product",
					"ring_away(field_ring(M), ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)), g) = "+
						"ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t) * g)",
					By(
						subringAffine,
						denominatorInAffine,
						gInAffine,
						ring_away.RingAwayTwice.Read(M).At(affine, denominator, g)))
				pInC := b.Have(
					"p(t) lies in the chart of C",
					"«value»(p) ∈ «chart»(C)",
					BySets(pInPolynomials, polynomialsInScalars, chartC[1]))
				qInC := b.Have(
					"q(t) lies in the chart of C",
					"«value»(q) ∈ «chart»(C)",
					BySets(qInPolynomials, polynomialsInScalars, chartC[1]))
				pInT := b.Have(
					"p(t) lies in the chart of the model",
					"«value»(p) ∈ «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))",
					BySets(pInPolynomials, polynomialsInScalars, chartT[1]))
				qInT := b.Have(
					"q(t) lies in the chart of the model",
					"«value»(q) ∈ «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t)))",
					BySets(qInPolynomials, polynomialsInScalars, chartT[1]))
				twiceC := b.Have(
					"Inverting p(t) and then q(t) in the chart of C is inverting their product",
					"ring_away(field_ring(M), ring_away(field_ring(M), «chart»(C), «value»(p)), «value»(q)) = "+
						"ring_away(field_ring(M), «chart»(C), «value»(p) * «value»(q))",
					By(chartC[0], pInC, qInC, ring_away.RingAwayTwice.Read(M).At(chartOfC, pValue, qValue)))
				twiceT := b.Have(
					"as in the chart of the model",
					"ring_away(field_ring(M), "+
						"    ring_away(field_ring(M), "+
						"        «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), "+
						"        «value»(p)), "+
						"    «value»(q)) = "+
						"ring_away(field_ring(M), "+
						"    «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t))), "+
						"    «value»(p) * «value»(q))",
					By(chartT[0], pInT, qInT, ring_away.RingAwayTwice.Read(M).At(chartOfModel, pValue, qValue)))
				b.Show(
					"both sides are the rings agreeing at p(t) with q(t) inverted",
					affineTwice.RwRev(),
					forC.Rw(),
					forT.Rw(),
					qParts[1].Rw(),
					twiceC.RwRev(),
					twiceT.RwRev(),
					atP.Rw(),
					Basic())
			}))
		hasP := arg.Have(
			"p serves",
			"∃p:(num → A). "+
				"    polynomial_over(k, p) ∧ "+
				"    p ≠ vec_zero ∧ "+
				"    (∀g:A. "+
				"        g ≠ M.zero ∧ (∃q:(num → A). polynomial_over(k, q) ∧ g = «value»(p) * «value»(q)) ⇒ "+
				"        «chart»(ring_away(field_ring(M), C, g)) = "+
				"        «chart»(ring_away(field_ring(M), «plane»(z), polynomial_eval(a, t) * g)))",
			Witness(p),
			By(pParts[0], pNonzero, multiples))
		arg.Take(z)
		arg.Take(F)
		arg.Take(bound)
		arg.Show(
			"the model and its polynomial",
			By(model, hasP))
	}),
})}

// TwistModelsOnRefinement — a good open refines, by inverting one polynomial
// c(t), to a good open carrying a model of every fixed twist field. Each
// automorphism gives a model and a polynomial, finitely many in all, and c is a
// nonzero common multiple of those polynomials.
var TwistModelsOnRefinement = twistModelsOnRefinementThm{family.Add(registry.ProofEntry{
	Name: "TwistModelsOnRefinement",
	Key:  "prop_e03b08edf3e3ddb3",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "value", Text: "λf:(num → A). polynomial_eval(f, t)"},
			{Name: "twisted", Text: "λs:permutation(A). constant_twist_field(M, k, L, s)"},
			{Name: "chart", Text: "λs:permutation(A). λX:set(A). " +
				"    constant_chart(field_ring(M), " +
				"        finite_constants(field_ring(M), card(k), permutation_order(s)), " +
				"        X)"},
			{Name: "plane", Text: "λs:permutation(A). λz:A. " +
				"    plane_chart_zero(restrict_ring(field_ring(M), «twisted»(s)), k, t, z)"},
			{Name: "agrees", Text: "λs:permutation(A). λz:A. λp:(num → A). ∀g:A. " +
				"    g ≠ M.zero ∧ (∃q:(num → A). polynomial_over(k, q) ∧ g = «value»(p) * «value»(q)) ⇒ " +
				"    «chart»(s, ring_away(field_ring(M), C, g)) = " +
				"    «chart»(s, ring_away(field_ring(M), «plane»(s, z), polynomial_eval(a, t) * g))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
		},
		Conclusion: "∃c:(num → A). " +
			"∃z:(permutation(A) → A). " +
			"∃F:(permutation(A) → num → A). " +
			"∃b:(permutation(A) → num). " +
			"    polynomial_over(k, c) ∧ " +
			"    c ≠ vec_zero ∧ " +
			"    fixed_twist_models(M, " +
			"        k, " +
			"        L, " +
			"        t, " +
			"        ring_away(field_ring(M), C, polynomial_eval(c, t)), " +
			"        polynomial_mul(a, c), " +
			"        z, " +
			"        F, " +
			"        b)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		closed, good Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		automorphisms := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		subfieldK := galois_good_open.GoodOpenConstantsSubfield.Read(good)
		LInField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(galois_good_open.GoodOpenFieldSubfield.Read(good), field.SubfieldSubset.At(ops, L)))
		tInField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(galois_good_open.GoodOpenParameterIn.Read(good), LInField))
		modelsExist := arg.Have(
			"Each automorphism has a model and a polynomial",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ «G»"},
				Conclusion: "∃z:A. ∃F:(num → A). ∃b:num. " +
					"    integral_plane_model(restrict_field(M, «twisted»(s)), k, t, z, F, b) ∧ " +
					"    (∃p:(num → A). polynomial_over(k, p) ∧ p ≠ vec_zero ∧ «agrees»(s, z, p))",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				inG := b.Assume()
				b.Show(
					"as TwistModelAgrees says",
					By(closed, good, inG, TwistModelAgrees.Read(M).At(k, L, C, t, a, s)))
			}))
		z, F, bound, chosen := arg.Unpack3As[Fun[symmetric_group.Permutation[A], A], Fun[symmetric_group.Permutation[A], Fun[Nat, A]], Fun[symmetric_group.Permutation[A], Nat]](
			GroupPremises(
				modelsExist,
				functions.ChooseThreeOn.At(
					arg.TermAs[Fun[symmetric_group.Permutation[A], Fun3[A, Fun[Nat, A], Nat, Bool]]](
						"λs:permutation(A). λz:A. λF:(num → A). λb:num. "+
							"    integral_plane_model(restrict_field(M, «twisted»(s)), k, t, z, F, b) ∧ "+
							"    (∃p:(num → A). polynomial_over(k, p) ∧ p ≠ vec_zero ∧ «agrees»(s, z, p))"),
					automorphisms)),
			"z",
			"F",
			"b")
		polynomialsExist := arg.Have(
			"Each chosen model has its polynomial",
			Statement{
				Binders: "∀s:permutation(A).",
				Hypotheses: []string{
					"s ∈ «G»",
				},
				Conclusion: "∃p:(num → A). polynomial_over(k, p) ∧ p ≠ vec_zero ∧ «agrees»(s, z(s), p)",
			},
			By(chosen))
		p, chosenPolynomials := arg.UnpackAs[Fun[symmetric_group.Permutation[A], Fun[Nat, A]]](
			GroupPremises(
				polynomialsExist,
				functions.ChooseOn.At(
					arg.TermAs[Fun2[symmetric_group.Permutation[A], Fun[Nat, A], Bool]](
						"λs:permutation(A). λp:(num → A). polynomial_over(k, p) ∧ p ≠ vec_zero ∧ «agrees»(s, z(s), p)"),
					automorphisms)),
			"p")
		polynomialsGood := arg.Have(
			"Each chosen polynomial is good",
			"∀s:permutation(A). s ∈ «G» ⇒ polynomial_over(k, p(s)) ∧ p(s) ≠ vec_zero",
			By(chosenPolynomials))
		c, multiple := arg.UnpackAs[Fun[Nat, A]](
			arg.Have(
				"The chosen polynomials have a nonzero common multiple",
				"∃c:(num → A). "+
					"    polynomial_over(k, c) ∧ "+
					"    c ≠ vec_zero ∧ "+
					"    (∀s:permutation(A). "+
					"        s ∈ «G» ⇒ ∃q:(num → A). polynomial_over(k, q) ∧ «value»(c) = «value»(p(s)) * «value»(q))",
				By(
					subfieldK,
					tInField,
					good,
					galois_good_open.GoodOpenGroupFinite.Read(M).At(k, L, C, t, a),
					polynomialsGood,
					galois_good_open.GoodOpenDenominatorOver.Read(good),
					galois_good_open.GoodOpenDenominatorNonzero.Read(good),
					polynomial_roots.PolynomialCommonMultiple.Read(M).AsFact().At(k, t, automorphisms, p, a))),
			"c")
		multipleData := arg.Conjuncts(
			multiple,
			"c is a polynomial over k",
			"c is nonzero",
			"c is a multiple of each")
		localized := arg.Have(
			"Inverting c(t) leaves a good open",
			"galois_good_open(M, k, L, t, ring_away(field_ring(M), C, «value»(c)), polynomial_mul(a, c))",
			By(
				good,
				multipleData[0],
				multipleData[1],
				galois_good_open.GaloisGoodOpenLocalize.Read(M).At(k, L, C, t, a, c)))
		valueNonzero := arg.Have(
			"c(t) is nonzero",
			"«value»(c) ≠ M.zero",
			By(
				galois_good_open.GoodOpenParameterTranscendental.Read(good),
				multipleData[0],
				multipleData[1],
				algebraic_element.AlgebraicOverDef.At(ops, k, t)))
		productValue := arg.Have(
			"a · c evaluates at t to the product of the values",
			"polynomial_eval(polynomial_mul(a, c), t) = polynomial_eval(a, t) * «value»(c)",
			By(
				tInField,
				subfieldK,
				galois_good_open.GoodOpenDenominatorOver.Read(good),
				multipleData[0],
				polynomial_evaluation.PolynomialProductData.Read(M).At(k, a, c)))
		models := arg.Have(
			"Each automorphism has its model on the refinement",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ «G»"},
				Conclusion: "integral_plane_model(restrict_field(M, constant_twist_field(M, k, L, s)), " +
					"    k, " +
					"    t, " +
					"    z(s), " +
					"    F(s), " +
					"    b(s)) ∧ " +
					"constant_chart(field_ring(M), " +
					"    finite_constants(field_ring(M), card(k), permutation_order(s)), " +
					"    ring_away(field_ring(M), C, «value»(c))) = " +
					"constant_chart(field_ring(M), " +
					"    finite_constants(field_ring(M), card(k), permutation_order(s)), " +
					"    ring_away(field_ring(M), " +
					"        plane_chart_zero(restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), " +
					"            k, " +
					"            t, " +
					"            z(s)), " +
					"        polynomial_eval(polynomial_mul(a, c), t)))",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				inG := b.Assume()
				modelAt := b.Have(
					"the model of s",
					"integral_plane_model(restrict_field(M, constant_twist_field(M, k, L, s)), k, t, z(s), F(s), b(s))",
					By(inG, chosen.At(s)))
				agreesAt := b.Have(
					"the charts agree at the multiples of the polynomial of s",
					"«agrees»(s, z(s), p(s))",
					By(inG, chosenPolynomials.At(s)))
				agree := b.Have(
					"c(t) is a nonzero multiple of p(s)(t)",
					"«chart»(s, ring_away(field_ring(M), C, «value»(c))) = "+
						"«chart»(s, ring_away(field_ring(M), «plane»(s, z(s)), polynomial_eval(a, t) * «value»(c)))",
					By(valueNonzero, inG, multipleData[2].At(s), agreesAt.At(b.TermAs[A]("«value»(c)"))))
				b.Show(
					"the model, and the two charts agree",
					productValue.Rw(),
					By(modelAt, agree))
			}))
		arg.Take(c)
		arg.Take(z)
		arg.Take(F)
		arg.Take(bound)
		arg.Show(
			"c, with the models chosen, is a refinement of the fixed twist models",
			By(
				multipleData[0],
				multipleData[1],
				localized,
				models,
				FixedTwistModelsDef.At(
					ops,
					k,
					L,
					arg.TermAs[Set[A]]("ring_away(field_ring(M), C, «value»(c))"),
					t,
					arg.TermAs[Fun[Nat, A]]("polynomial_mul(a, c)"),
					z,
					F,
					bound)))
	}),
})}

// FixedTwistModelsOnCommonGoodOpen — every fixed twist has a model over one
// common good open: take a good open by the torsor theorem and refine it.
var FixedTwistModelsOnCommonGoodOpen = fixedTwistModelsOnCommonGoodOpenThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistModelsOnCommonGoodOpen",
	Key:  "prop_fecc62d32dc521b1",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "∃C:set(A). " +
			"∃a:(num → A). " +
			"∃z:(permutation(A) → A). " +
			"∃F:(permutation(A) → num → A). " +
			"∃b:(permutation(A) → num). " +
			"    fixed_twist_models(M, k, L, t, C, a, z, F, b)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		closed, regular, finiteK, tInL, transcendental, galois Fact,
	) {
		C, a, torsors := arg.Unpack2As[Set[A], Fun[Nat, A]](
			GroupPremises(
				regular,
				finiteK,
				tInL,
				transcendental,
				galois,
				galois_good_fibres.GaloisGoodFibresAreTorsors.Read(M).At(k, L, t)),
			"C",
			"a")
		arg.Show(
			"a good open exists, and it refines to carry the models",
			By(Normalized, closed, torsors, TwistModelsOnRefinement.Read(M).At(k, L, C, t, a)))
	}),
})}
