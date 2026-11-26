// constant_extension.go — enlarging the constants of a regular function field.

package constant_composite

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantExtensionDegree — a finite extension l of a perfect field k keeps
// its degree over a field K in which k is algebraically closed. l is k(θ) for
// one θ, so K(l) is K(θ). The minimal polynomial h of θ over K divides the
// minimal polynomial g over k, so its coefficients are algebraic over k, and
// lying in K they lie in k: g and h each lie over the field where the other is
// least, and their degrees agree.
var ConstantExtensionDegree = constantExtensionDegreeThm{family.Add(registry.ProofEntry{
	Name: "ConstantExtensionDegree",
	Key:  "prop_7710da78c7eac47",
	Reading: "That k is algebraically closed in K is load-bearing: at K = l the " +
		"composite is K and its degree is one. Perfectness is read only to make l " +
		"simple over k; a simple algebraic extension keeps its degree without it.",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k K l:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"subfield(M, l)",
			"k ⊆ K",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"perfect_field(restrict_field(M, k))",
			"∀x:A. x ∈ K ∧ algebraic_over(M, k, x) ⇒ x ∈ k",
		},
		Conclusion: "finite_extension(M, K, field_adjoin(M, K, l)) ∧ " +
			"extension_degree(M, K, field_adjoin(M, K, l)) = extension_degree(M, k, l)",
		Abbrev: Abbrev{
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), l)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A finite extension of a perfect field is simple: a finite k has a finite
		// l, and over an infinite k perfectness makes every element separable.
		simple := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k l:set(A).",
			Hypotheses: []string{
				"subfield(M, k)",
				"subfield(M, l)",
				"k ⊆ l",
				"finite_extension(M, k, l)",
				"perfect_field(restrict_field(M, k))",
			},
			Conclusion: "∃θ:A. θ ∈ l ∧ field_adjoin(M, k, {θ}) = l",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			kField, lField, kInL, finite, perfect Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			F := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
			a.Cases(a.TermAs[Bool]("finite(k)"))
			a.When(
				"over a finite k the space l has finitely many "+
					"vectors, and a finite field is simple over a subfield",
				func(b *Argument, finiteK Fact) {
					space := b.Have(
						"l is a finite-dimensional space over the finite field k",
						"finite_field(restrict_field(M, k)) ∧ "+
							"module_on(field_ring(restrict_field(M, k)), «vectors») ∧ "+
							"finite_dimensional(field_ring(restrict_field(M, k)), «vectors»)",
						By(
							Normalized,
							finiteK,
							kField,
							lField,
							kInL,
							finite,
							field.SubfieldFieldOn.Read(M).At(k),
							finite_field.FiniteFieldDef.At(F),
							field_extension.ExtensionModuleOn.Read(M).At(k, l),
							field.RestrictFieldRing.At(m, k),
							field_extension.FiniteExtensionDef.At(m, k, l)))
					finiteL := b.Have(
						"so l has finitely many points",
						"finite(l)",
						By(
							space,
							finite_field.FiniteDimensionalSpaceSize.At(F, b.TermAs[module_record.ModuleOps[A, A]]("«vectors»")),
							cardinality.HasSizeDef))
					b.Show(
						"and it is generated over k by one of them",
						By(kField, lField, kInL, finiteL, finite_field.FiniteSubfieldSimple.Read(M).At(k, l)))
				})
			a.Otherwise(
				"over an infinite k the primitive element theorem applies",
				func(b *Argument, infiniteK Fact) {
					separable := b.Have(
						"perfectness makes every element of l separable over k",
						"∀x:A. x ∈ l ⇒ separable_over(M, k, x)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inL := c.Assume()
							point := c.Have(
								"x lies in M and, l being finite over k, is algebraic over k",
								"x ∈ M.carrier ∧ algebraic_over(M, k, x)",
								BySets(
									inL,
									kField,
									lField,
									kInL,
									finite,
									field.SubfieldSubset.At(m, l),
									algebraic_element.FiniteExtensionAlgebraic.Read(M).At(k, l, x)))
							pointParts := c.Conjuncts(
								point,
								"x lies in M",
								"x is algebraic over k")
							c.Show(
								"its minimal polynomial over k is irreducible, so separable over the perfect field k",
								By(
									perfect,
									kField,
									pointParts[1],
									galois_correspondence.SeparableOverDef.At(m, k, x),
									algebraic_element.MinimalPolynomialIrreducible.Read(M).At(k, c.MemberOf[on.M](x, pointParts[0])),
									field.RestrictFieldRing.At(m, k),
									perfect_field.PerfectFieldDef.At(F)))
						}))
					b.Show(
						"k is infinite and l is finite and separable over it",
						By(
							infiniteK,
							separable,
							kField,
							lField,
							kInL,
							finite,
							finite_set.InfiniteDef.At(k),
							algebraic_closure.PrimitiveElement.Read(M).At(k, l)))
				})
		})

		// When k is algebraically closed in K, θ has minimal polynomials of one
		// degree over the two. Over K the polynomial h divides g, the one over k,
		// and a monic factor of a polynomial over k has its coefficients algebraic
		// over k; lying in K they lie in k. So g and h are nonzero polynomials over
		// K and over k respectively, with root θ, and each bounds the other.
		sameDegree := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K:set(A). ∀θ:A.",
			Hypotheses: []string{
				"subfield(M, k)",
				"subfield(M, K)",
				"k ⊆ K",
				"θ ∈ M.carrier",
				"algebraic_over(M, k, θ)",
				"∀x:A. x ∈ K ∧ algebraic_over(M, k, x) ⇒ x ∈ k",
			},
			Conclusion: "polynomial_degree(minimal_polynomial(M, K, θ)) = " +
				"polynomial_degree(minimal_polynomial(M, k, θ))",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			θ *Expr[A],
			kField, KField, kInK, θIn, algebraic, closed Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			carrier := a.TermAs[Set[A]]("M.carrier")
			domain := integral_domain.FieldIntegralDomain.Read(M)
			θm := a.MemberOf[on.M](θ, θIn)
			g, gDef := a.LetAs[Fun[Nat, A]]("g", "minimal_polynomial(M, k, θ)")
			h, hDef := a.LetAs[Fun[Nat, A]]("h", "minimal_polynomial(M, K, θ)")
			gSpec := a.Have(
				"g is a monic polynomial over k with root θ",
				"polynomial_over(k, g) ∧ polynomial_monic(g) ∧ polynomial_eval(g, θ) = M.zero",
				By(
					Normalized,
					gDef,
					θIn,
					kField,
					algebraic,
					algebraic_element.MinimalPolynomialSpec.Read(M).At(k, θm)))
			hSpec := a.Have(
				"θ is algebraic over the larger field K, and h is a monic polynomial over K with root θ",
				"algebraic_over(M, K, θ) ∧ "+
					"polynomial_over(K, h) ∧ "+
					"polynomial_monic(h) ∧ "+
					"polynomial_eval(h, θ) = M.zero",
				By(
					Normalized,
					hDef,
					θIn,
					KField,
					kInK,
					algebraic,
					algebraic_element.AlgebraicOverMono.Read(M).At(k, K, θ),
					algebraic_element.MinimalPolynomialSpec.Read(M).At(K, θm)))
			gOverK := a.Have(
				"g is a polynomial over K, and being monic it is not zero",
				"polynomial_over(K, g) ∧ g ≠ vec_zero",
				By(
					kInK,
					gSpec,
					polynomial.PolynomialOverMono.At(zero, k, K, g),
					polynomial.MonicNonzero.Read(domain).At(g)))
			dividesOverK := a.Have(
				"g vanishes at θ, so h divides it over K",
				"polynomial_divides(restrict_ring(field_ring(M), K), h, g)",
				By(
					Normalized,
					hDef,
					θIn,
					KField,
					hSpec,
					gSpec,
					gOverK,
					algebraic_element.MinimalPolynomialDivides.Read(M).At(K, θm, g)))
			r, cofactor := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(dividesOverK, polynomial_division.PolynomialDividesDef), "r")
			dividesOverM := a.Have(
				"the cofactor r is a polynomial over M, so h divides g over M",
				"polynomial_divides(field_ring(M), h, g)",
				By(
					KField,
					cofactor,
					field.SubfieldSubset.At(m, K),
					polynomial.PolynomialOverMono.At(zero, K, carrier, r),
					polynomial_division.PolynomialDividesDef.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(M)"), h, g)))
			coefficients := a.Have(
				"every coefficient of h lies in k",
				"∀i:num. h(i) ∈ k",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"h(i) lies in K and, h being a monic factor over M of g, is algebraic over k",
						By(
							closed.At(b.TermAs[A]("h(i)")),
							KField,
							kField,
							hSpec,
							gSpec,
							gOverK,
							dividesOverM,
							field.SubfieldSubset.At(m, K),
							polynomial.PolynomialOverMono.At(zero, K, carrier, h),
							polynomial.PolynomialOverDef.At(zero, K, h),
							algebraic_closure.MonicFactorCoefficientsAlgebraic.Read(M).At(k, g, h, i)))
				}))
			hOverk := a.Have(
				"so h is a polynomial over k, and being monic it is not zero",
				"polynomial_over(k, h) ∧ h ≠ vec_zero",
				By(
					coefficients,
					hSpec,
					polynomial.PolynomialOverDef.At(zero, K, h),
					polynomial.PolynomialOverDef.At(zero, k, h),
					polynomial.MonicNonzero.Read(domain).At(h)))
			atMost := a.Have(
				"over K the polynomial h has the least degree, and g is a candidate",
				"polynomial_degree(h) ≤ polynomial_degree(g)",
				By(
					Normalized,
					hDef,
					θIn,
					KField,
					gSpec,
					gOverK,
					algebraic_element.MinimalPolynomialLeast.Read(M).At(K, θm, g)))
			atLeast := a.Have(
				"over k the polynomial g has the least degree, and h is a candidate",
				"polynomial_degree(g) ≤ polynomial_degree(h)",
				By(
					Normalized,
					gDef,
					θIn,
					kField,
					hSpec,
					hOverk,
					algebraic_element.MinimalPolynomialLeast.Read(M).At(k, θm, h)))
			a.Show(
				"so the two degrees are equal",
				ByArith(atMost, atLeast))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			kField, KField, lField, kInK, kInL, finite, perfect, closed Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			θ, primitive := a.ObtainAs[A](
				"k being perfect, l is k(θ) for one θ in l",
				"∃θ:A. θ ∈ l ∧ field_adjoin(M, k, {θ}) = l",
				By(kField, lField, kInL, finite, perfect, Read(simple, M).At(k, l)))
			generator := a.Conjuncts(
				primitive,
				"θ lies in l",
				"θ generates l over k")
			θIn, generates := generator[0], generator[1]
			point := a.Have(
				"θ lies in M and, l being finite over k, is algebraic over k",
				"θ ∈ M.carrier ∧ algebraic_over(M, k, θ)",
				BySets(
					θIn,
					kField,
					lField,
					kInL,
					finite,
					field.SubfieldSubset.At(m, l),
					algebraic_element.FiniteExtensionAlgebraic.Read(M).At(k, l, θ)))
			pointParts := a.Conjuncts(
				point,
				"θ lies in M",
				"θ is algebraic over k")
			θm := a.MemberOf[on.M](θ, pointParts[0])
			singleton := a.TermAs[Set[A]]("{θ}")
			E, EDef := a.LetAs[Set[A]]("E", "field_adjoin(M, K, {θ})")
			C, CDef := a.LetAs[Set[A]]("C", "field_adjoin(M, K, l)")
			EHoldsθ := a.Have(
				"E = K(θ) is a subfield over K holding θ",
				"subfield(M, E) ∧ K ⊆ E ∧ θ ∈ E",
				By(
					Normalized,
					EDef,
					KField,
					pointParts[0],
					algebraic_element.AdjoinElementSubfield.Read(M).At(K, θm)))
			CHoldsL := a.Have(
				"C = K(l) is a subfield over K holding l",
				"subfield(M, C) ∧ K ⊆ C ∧ l ⊆ C",
				By(
					Normalized,
					CDef,
					KField,
					lField,
					field.SubfieldSubset.At(m, K),
					field.SubfieldSubset.At(m, l),
					algebraic_element.AdjoinSubfield.Read(M).At(K, l)))
			lInE := a.Have(
				"E holds k and θ, so it holds l = k(θ)",
				"l ⊆ E",
				BySets(generates, kInK, EHoldsθ, algebraic_element.AdjoinLeast.Read(M).At(k, singleton, E)))
			same := a.Have(
				"K(l) = K(θ), each holding the generators of the other",
				"C = E",
				BySets(
					CDef,
					EDef,
					θIn,
					lInE,
					CHoldsL,
					EHoldsθ,
					algebraic_element.AdjoinLeast.Read(M).At(K, singleton, C),
					algebraic_element.AdjoinLeast.Read(M).At(K, l, E)))
			degreeOverK := a.Have(
				"θ is algebraic over K, so K(θ) is finite over K, of the degree of the minimal polynomial",
				"finite_extension(M, K, E) ∧ "+
					"extension_degree(M, K, E) = polynomial_degree(minimal_polynomial(M, K, θ))",
				By(
					Normalized,
					EDef,
					KField,
					kInK,
					point,
					algebraic_element.AlgebraicOverMono.Read(M).At(k, K, θ),
					algebraic_element.AdjoinDegree.Read(M).At(K, θm)))
			a.Show(
				"so K(l) is finite over K, of degree [l : k]",
				SplitConj(
					Case(
						"K(l) = K(θ) is finite over K",
						By(Normalized, same, degreeOverK)),
					Case(
						"the degrees agree along the two minimal polynomials",
						CalcEq(
							Leg(
								a.Term("extension_degree(M, K, E)"),
								"K(l) is K(θ)",
								By(Normalized, same)),
							Leg(
								a.Term("polynomial_degree(minimal_polynomial(M, K, θ))"),
								"the degree of K(θ) over K",
								By(degreeOverK)),
							Leg(
								a.Term("polynomial_degree(minimal_polynomial(M, k, θ))"),
								"the minimal polynomials over K and over k have one degree",
								By(kField, KField, kInK, point, closed, Read(sameDegree, M).At(k, K, θ))),
							FinalLeg(
								"over k that degree is [k(θ) : k] = [l : k]",
								By(Normalized, generates, kField, point, algebraic_element.AdjoinDegree.Read(M).At(k, θm)))))))
		})
	}),
})}

// RegularConstantExtension — a finite constant extension l of a regular function
// field K over k. The composite Kl is regular over l; multiplication is an
// l-linear isomorphism l ⊗ₖ K ≅ Kl; and a separating parameter t of K stays one
// of Kl, with the same degree. Everything rests on ConstantExtensionDegree, read
// three times: [Kl : K] = [l : k] gives the tensor clause, read at l(x) it leaves
// no room for an element of Kl algebraic over l outside l, and read at k(t) it
// gives [l(t) : k(t)] = [l : k], so the two towers from k(t) to Kl have
// [Kl : l(t)] = [K : k(t)].
var RegularConstantExtension = regularConstantExtensionThm{family.Add(registry.ProofEntry{
	Name: "RegularConstantExtension",
	Key:  "prop_f9866c2631d3dca9",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k K l:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "regular_function_field(M, l, constant_composite(M, K, l)) ∧ " +
			"(∃f:(set(prod(A, A) → A) → A). " +
			"    module_isomorphism(restrict_ring(field_ring(M), l), " +
			"        scalar_extension(restrict_ring(field_ring(M), k), " +
			"            restrict_ring(field_ring(M), l), " +
			"            restrict_module(regular_module(field_ring(M)), K)), " +
			"        restrict_module(regular_module(field_ring(M)), constant_composite(M, K, l)), " +
			"        f) ∧ " +
			"    (∀a x:A. " +
			"        a ∈ l ∧ x ∈ K ⇒ " +
			"        f(tensor(restrict_ring(field_ring(M), k), " +
			"                restrict_module(regular_module(field_ring(M)), l), " +
			"                restrict_module(regular_module(field_ring(M)), K), " +
			"                a, " +
			"                x)) = " +
			"        a * x) ∧ " +
			"    (∀t:A. " +
			"        t ∈ K ∧ " +
			"        ¬algebraic_over(M, k, t) ∧ " +
			"        finite_extension(M, field_adjoin(M, k, {t}), K) ∧ " +
			"        (∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {t}), x)) ⇒ " +
			"        finite_extension(M, field_adjoin(M, l, {t}), constant_composite(M, K, l)) ∧ " +
			"        (∀x:A. " +
			"            x ∈ constant_composite(M, K, l) ⇒ separable_over(M, field_adjoin(M, l, {t}), x)) ∧ " +
			"        extension_degree(M, field_adjoin(M, l, {t}), constant_composite(M, K, l)) = " +
			"        extension_degree(M, field_adjoin(M, k, {t}), K)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// The composite of two subfields is a subfield holding both.
		composite := ctx.Lemma(Statement{
			Binders:    "∀M:field_on(A). ∀K l:set(A).",
			Hypotheses: []string{"subfield(M, K)", "subfield(M, l)"},
			Conclusion: "subfield(M, field_adjoin(M, K, l)) ∧ " +
				"K ⊆ field_adjoin(M, K, l) ∧ " +
				"l ⊆ field_adjoin(M, K, l)",
		}, func(a *Argument, M field.FieldFact[on.M], K, l *Expr[Set[A]], subfields Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			a.Show(
				"both subfields lie in M",
				By(
					subfields,
					field.SubfieldSubset.At(m, K),
					field.SubfieldSubset.At(m, l),
					algebraic_element.AdjoinSubfield.Read(M).At(K, l)))
		})

		// A larger base keeps the inclusion when t is adjoined to both.
		rationalInside := ctx.Lemma(Statement{
			Binders:    "∀M:field_on(A). ∀k l:set(A). ∀t:A.",
			Hypotheses: []string{"subfield(M, l)", "k ⊆ l", "t ∈ M.carrier"},
			Conclusion: "field_adjoin(M, k, {t}) ⊆ field_adjoin(M, l, {t})",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			t *Expr[A],
			lField, kInL, tInM Fact,
		) {
			adjoined := a.Conjuncts(
				GroupPremises(lField, tInM, algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(l, t)),
				"l(t) is a subfield",
				"holding l",
				"and t")
			holds := a.Have(
				"so it holds k and t",
				"k ⊆ field_adjoin(M, l, {t}) ∧ {t} ⊆ field_adjoin(M, l, {t})",
				BySets(kInL, adjoined[1], adjoined[2]))
			a.Show(
				"so it holds k(t)",
				By(
					adjoined[0],
					holds,
					algebraic_element.AdjoinLeast.Read(M).At(
						k, a.TermAs[Set[A]]("{t}"), a.TermAs[Set[A]]("field_adjoin(M, l, {t})"))))
		})

		// l is exact in Kl: an element x of Kl algebraic over l has
		// [l(x) : k] = [K(l(x)) : K] = [Kl : K] = [l : k], so l(x), holding l, is l.
		exactConstants := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K l:set(A). ∀x:A.",
			Hypotheses: []string{
				"regular_function_field(M, k, K)",
				"subfield(M, l)",
				"k ⊆ l",
				"finite_extension(M, k, l)",
				"x ∈ field_adjoin(M, K, l)",
				"algebraic_over(M, l, x)",
			},
			Conclusion: "x ∈ l",
		}, func(a *Argument, M field.FieldFact[on.M], k, K, l *Expr[Set[A]], x *Expr[A], hypotheses Fact) {
			data := a.Unfolded(hypotheses, function_field.RegularFunctionFieldDef)
			m := a.TermAs[FieldOps[A]]("M")
			Kl := a.TermAs[Set[A]]("field_adjoin(M, K, l)")
			lx := a.TermAs[Set[A]]("field_adjoin(M, l, {x})")
			Klx := a.TermAs[Set[A]]("field_adjoin(M, K, field_adjoin(M, l, {x}))")
			composed := a.Conjuncts(
				GroupPremises(data, Read(composite, M).At(K, l)),
				"Kl is a subfield",
				"holding K",
				"and l")
			KlField, KInKl := composed[0], composed[1]
			between := a.Conjuncts(
				GroupPremises(
					composed[0], data, composed[2], algebraic_element.AdjoinElementBetween.Read(M).At(l, Kl, x)),
				"l(x) is a subfield",
				"holding l",
				"and x",
				"inside Kl")
			lxField, lInLx, xInLx, lxInKl := between[0], between[1], between[2], between[3]
			xInM := a.Have(
				"x lies in M",
				"x ∈ M.carrier",
				BySets(data, KlField, field.SubfieldSubset.At(m, Kl)))
			finiteLx := a.Have(
				"x is algebraic over l, so l(x) is finite over l",
				"finite_extension(M, l, field_adjoin(M, l, {x}))",
				By(data, algebraic_element.AlgebraicIffFinite.Read(M).At(l, a.MemberOf[on.M](x, xInM))))
			kInLx := a.Have(
				"k lies in l(x)",
				"k ⊆ field_adjoin(M, l, {x})",
				BySets(data, lInLx))
			finiteOverK := a.Have(
				"so l(x) is finite over k",
				"finite_extension(M, k, field_adjoin(M, l, {x}))",
				By(data, lxField, lInLx, finiteLx, field_extension.TowerLaw.Read(M).At(k, l, lx)))
			keptLx := a.Conjuncts(
				GroupPremises(data, between[0], finiteOverK, kInLx, ConstantExtensionDegree.Read(M).At(k, K, lx)),
				"K(l(x)) is finite over K",
				"of degree [l(x) : k]")
			keptL := a.Conjuncts(
				GroupPremises(data, ConstantExtensionDegree.Read(M).At(k, K, l)),
				"Kl is finite over K",
				"of degree [l : k]")
			sameComposite := a.Have(
				"x lying in Kl, K(l(x)) is Kl",
				"field_adjoin(M, K, field_adjoin(M, l, {x})) = field_adjoin(M, K, l)",
				Derive(func(b *Argument) {
					upper := b.Conjuncts(
						GroupPremises(data, between[0], Read(composite, M).At(K, lx)),
						"K(l(x)) is a subfield",
						"holding K",
						"and l(x)")
					lInKlx := b.Have(
						"so it holds l",
						"l ⊆ field_adjoin(M, K, field_adjoin(M, l, {x}))",
						BySets(lInLx, upper[2]))
					into := b.Have(
						"Kl holds K and l(x)",
						"field_adjoin(M, K, field_adjoin(M, l, {x})) ⊆ field_adjoin(M, K, l)",
						By(KlField, KInKl, lxInKl, algebraic_element.AdjoinLeast.Read(M).At(K, lx, Kl)))
					onto := b.Have(
						"K(l(x)) holds K and l",
						"field_adjoin(M, K, l) ⊆ field_adjoin(M, K, field_adjoin(M, l, {x}))",
						By(upper[0], upper[1], lInKlx, algebraic_element.AdjoinLeast.Read(M).At(K, l, Klx)))
					b.Show(
						"the two composites hold each other",
						By(into, onto, set_order.SubsetAntisym.At(Klx, Kl)))
				}))
			sameDegree := a.Have(
				"so l(x) has the degree of l over k",
				"extension_degree(M, k, field_adjoin(M, l, {x})) = extension_degree(M, k, l)",
				By(keptLx[1], keptL[1], sameComposite))
			a.Show(
				"so l(x), holding l with its degree over k, is l, and x lies in l",
				By(
					data,
					lxField,
					lInLx,
					finiteOverK,
					sameDegree,
					xInLx,
					field_extension.IntermediateDegree.Read(M).At(k, l, lx)))
		})

		// The composite is regular over l: perfect, generated over l by the
		// generators of K, algebraic over l(t) for the parameter t of K, which stays
		// transcendental, and exact.
		regularComposite := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K l:set(A).",
			Hypotheses: []string{
				"regular_function_field(M, k, K)",
				"subfield(M, l)",
				"k ⊆ l",
				"finite_extension(M, k, l)",
			},
			Conclusion: "regular_function_field(M, l, constant_composite(M, K, l))",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			regular, lField, kInL, finite Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			Kl := a.TermAs[Set[A]]("field_adjoin(M, K, l)")
			data := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"K holds k",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is exact in K")
			kField, KField, perfect := data[0], data[1], data[3]
			generated, parameter := data[4], data[5]
			E, generators := a.UnpackAs[Set[A]](generated, "E")
			t, transcendence := a.UnpackAs[A](parameter, "t")
			generatorParts := a.Conjuncts(
				generators,
				"E is finite",
				"E lies in K",
				"E generates K over k")
			finiteE, EInK, generatesK := generatorParts[0], generatorParts[1], generatorParts[2]
			parameterParts := a.Conjuncts(
				transcendence,
				"t lies in K",
				"t is transcendental over k",
				"K is algebraic over k(t)")
			tInK, transcendental, algebraic := parameterParts[0], parameterParts[1], parameterParts[2]
			composed := a.Conjuncts(
				GroupPremises(data[1], lField, Read(composite, M).At(K, l)),
				"Kl is a subfield",
				"holding K",
				"and l")
			KlField, KInKl, lInKl := composed[0], composed[1], composed[2]
			perfectL := a.Have(
				"l is perfect, being finite over the perfect k",
				"perfect_field(restrict_field(M, l))",
				By(kField, lField, kInL, finite, perfect, perfect_field.FiniteExtensionPerfect.Read(M).At(k, l)))
			EInKl := a.Have(
				"E lies in Kl",
				"E ⊆ field_adjoin(M, K, l)",
				BySets(EInK, KInKl))
			generatesKl := a.Have(
				"E generates Kl over l",
				"field_adjoin(M, l, E) = field_adjoin(M, K, l)",
				Derive(func(b *Argument) {
					lE := b.TermAs[Set[A]]("field_adjoin(M, l, E)")
					lAndEInM := b.Have(
						"l and E lie in M",
						"l ⊆ M.carrier ∧ E ⊆ M.carrier",
						BySets(lField, KField, EInK, field.SubfieldSubset.At(m, l), field.SubfieldSubset.At(m, K)))
					upper := b.Conjuncts(
						GroupPremises(lAndEInM, algebraic_element.AdjoinSubfield.Read(M).At(l, E)),
						"l(E) is a subfield",
						"holding l",
						"and E")
					kInLE := b.Have(
						"so it holds k",
						"k ⊆ field_adjoin(M, l, E)",
						BySets(kInL, upper[1]))
					KInLE := b.Have(
						"and K = k(E)",
						"K ⊆ field_adjoin(M, l, E)",
						By(
							Normalized,
							generatesK,
							upper[0],
							kInLE,
							upper[2],
							algebraic_element.AdjoinLeast.Read(M).At(k, E, lE)))
					into := b.Have(
						"l(E) holds K and l",
						"field_adjoin(M, K, l) ⊆ field_adjoin(M, l, E)",
						By(upper[0], KInLE, upper[1], algebraic_element.AdjoinLeast.Read(M).At(K, l, lE)))
					onto := b.Have(
						"Kl holds l and E",
						"field_adjoin(M, l, E) ⊆ field_adjoin(M, K, l)",
						By(KlField, lInKl, EInKl, algebraic_element.AdjoinLeast.Read(M).At(l, E, Kl)))
					b.Show(
						"the two fields hold each other",
						By(onto, into, set_order.SubsetAntisym.At(lE, Kl)))
				}))
			tInM := a.Have(
				"t lies in M",
				"t ∈ M.carrier",
				BySets(tInK, KField, field.SubfieldSubset.At(m, K)))
			lAlgebraic := a.Have(
				"l is algebraic over k, being finite over it",
				"∀y:A. y ∈ l ⇒ algebraic_over(M, k, y)",
				a.ForEach(func(y *Expr[A]) Action {
					return By(
						kField,
						lField,
						kInL,
						finite,
						algebraic_element.FiniteExtensionAlgebraic.Read(M).At(k, l, y))
				}))
			stillTranscendental := a.Have(
				"t stays transcendental over l, which is algebraic over k",
				"¬algebraic_over(M, l, t)",
				By(
					kField,
					transcendental,
					lField,
					lAlgebraic,
					tInM,
					field.SubfieldSubset.At(m, l),
					algebraic_element.AlgebraicOverTrans.Read(M).AsFact().At(k, l, t)))
			lt := a.TermAs[Set[A]]("field_adjoin(M, l, {t})")
			kt := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			ltParts := a.Conjuncts(
				GroupPremises(lField, tInM, algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(l, t)),
				"l(t) is a subfield",
				"holding l",
				"and t")
			ltField, lInLt := ltParts[0], ltParts[1]
			ktInLt := Read(rationalInside, M).At(k, l, t)
			algebraicOverLt := a.Have(
				"Kl is algebraic over l(t): those elements form a subfield holding K and l",
				"∀x:A. x ∈ field_adjoin(M, K, l) ⇒ algebraic_over(M, field_adjoin(M, l, {t}), x)",
				Derive(func(b *Argument) {
					closure := b.TermAs[Set[A]]("algebraic_elements(M, field_adjoin(M, l, {t}))")
					elements := algebraic_element.AlgebraicElementsDef.At(m, lt)
					algebraics := b.Have(
						"the elements algebraic over l(t) form a subfield holding it",
						"subfield(M, algebraic_elements(M, field_adjoin(M, l, {t}))) ∧ "+
							"field_adjoin(M, l, {t}) ⊆ algebraic_elements(M, field_adjoin(M, l, {t}))",
						By(ltField, algebraic_element.AlgebraicElementsSubfield.Read(M).At(lt)))
					overLt := b.Have(
						"K is algebraic over k(t), so over the larger l(t)",
						"∀y:A. y ∈ K ⇒ algebraic_over(M, field_adjoin(M, l, {t}), y)",
						b.ForEach(func(y *Expr[A]) Action {
							return By(
								algebraic,
								lField,
								kInL,
								tInM,
								ktInLt,
								algebraic_element.AlgebraicOverMono.Read(M).At(kt, lt, y))
						}))
					holdsK := b.Have(
						"so that subfield holds K",
						"K ⊆ algebraic_elements(M, field_adjoin(M, l, {t}))",
						BySets(KField, overLt, field.SubfieldSubset.At(m, K), elements))
					holdsL := b.Have(
						"and l, which lies in l(t)",
						"l ⊆ algebraic_elements(M, field_adjoin(M, l, {t}))",
						BySets(lInLt, algebraics))
					b.Show(
						"so it holds Kl",
						BySets(
							elements,
							algebraics,
							holdsK,
							holdsL,
							algebraic_element.AdjoinLeast.Read(M).At(K, l, closure)))
				}))
			tInKl := a.Have(
				"t lies in Kl",
				"t ∈ field_adjoin(M, K, l)",
				BySets(tInK, KInKl))
			generatorsKl := a.Have(
				"the generators of K generate Kl over l",
				"∃F:set(A). finite(F) ∧ F ⊆ field_adjoin(M, K, l) ∧ field_adjoin(M, l, F) = field_adjoin(M, K, l)",
				Witness(E),
				By(finiteE, EInKl, generatesKl))
			parameterKl := a.Have(
				"t is a parameter of Kl over l",
				"∃s:A. "+
					"    s ∈ field_adjoin(M, K, l) ∧ "+
					"    ¬algebraic_over(M, l, s) ∧ "+
					"    (∀x:A. x ∈ field_adjoin(M, K, l) ⇒ algebraic_over(M, field_adjoin(M, l, {s}), x))",
				Witness(t),
				By(tInKl, stillTranscendental, algebraicOverLt))
			exactL := a.Have(
				"l is exact in Kl",
				"∀x:A. x ∈ field_adjoin(M, K, l) ∧ algebraic_over(M, l, x) ⇒ x ∈ l",
				a.ForEach(func(x *Expr[A]) Action {
					return By(regular, lField, kInL, finite, Read(exactConstants, M).At(k, K, l, x))
				}))
			a.Show(
				"so Kl is regular over l",
				Simp(Fwd(ConstantCompositeDef), Fwd(function_field.RegularFunctionFieldDef)),
				By(lField, KlField, lInKl, perfectL, generatorsKl, parameterKl, exactL))
		})

		// A separating parameter t of K stays one of Kl. k is exact in k(t), so
		// [l(t) : k(t)] = [l : k], and the towers from k(t) up to Kl through K and
		// through l(t) give [Kl : l(t)] = [K : k(t)]. k(t) is infinite, so K = k(t)(z)
		// for a separable z, and Kl = l(t)(z) is separable over l(t).
		parameterExtension := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K l:set(A). ∀t:A.",
			Hypotheses: []string{
				"regular_function_field(M, k, K)",
				"subfield(M, l)",
				"k ⊆ l",
				"finite_extension(M, k, l)",
				"t ∈ K",
				"¬algebraic_over(M, k, t)",
				"finite_extension(M, field_adjoin(M, k, {t}), K)",
				"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {t}), x)",
			},
			Conclusion: "finite_extension(M, field_adjoin(M, l, {t}), constant_composite(M, K, l)) ∧ " +
				"(∀x:A. x ∈ constant_composite(M, K, l) ⇒ separable_over(M, field_adjoin(M, l, {t}), x)) ∧ " +
				"extension_degree(M, field_adjoin(M, l, {t}), constant_composite(M, K, l)) = " +
				"extension_degree(M, field_adjoin(M, k, {t}), K)",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			t *Expr[A],
			regular, lField, kInL, finite, tInK, transcendental, finiteK, separable Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			data := a.Unfolded(regular, function_field.RegularFunctionFieldDef)
			Kl := a.TermAs[Set[A]]("field_adjoin(M, K, l)")
			kt := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			lt := a.TermAs[Set[A]]("field_adjoin(M, l, {t})")
			singleton := a.TermAs[Set[A]]("{t}")
			ktl := a.TermAs[Set[A]]("field_adjoin(M, field_adjoin(M, k, {t}), l)")
			composed := a.Conjuncts(
				GroupPremises(data, lField, Read(composite, M).At(K, l)),
				"Kl is a subfield",
				"holding K",
				"and l")
			KlField, KInKl := composed[0], composed[1]
			tInExtension := a.Have(
				"t lies in Kl",
				"t ∈ field_adjoin(M, K, l)",
				BySets(tInK, KInKl))
			rational := a.Conjuncts(
				GroupPremises(data, tInK, algebraic_element.AdjoinElementBetween.Read(M).At(k, K, t)),
				"k(t) is a subfield",
				"holding k",
				"and t",
				"inside K")
			ktField, tInKt, ktInK := rational[0], rational[2], rational[3]
			extended := a.Conjuncts(
				GroupPremises(
					lField,
					composed[0],
					composed[2],
					tInExtension,
					algebraic_element.AdjoinElementBetween.Read(M).At(l, Kl, t)),
				"l(t) is a subfield",
				"holding l",
				"and t",
				"inside Kl")
			ltField, lInLt, ltInKl := extended[0], extended[1], extended[3]
			exactInKt := a.Have(
				"k is exact in k(t), which lies in K",
				"∀y:A. y ∈ field_adjoin(M, k, {t}) ∧ algebraic_over(M, k, y) ⇒ y ∈ k",
				BySets(data, ktInK))
			keptKt := a.Conjuncts(
				GroupPremises(
					data,
					rational[0],
					lField,
					rational[1],
					kInL,
					finite,
					exactInKt,
					ConstantExtensionDegree.Read(M).At(k, kt, l)),
				"k(t)(l) is finite over k(t)",
				"of degree [l : k]")
			keptK := a.Conjuncts(
				GroupPremises(data, lField, kInL, finite, ConstantExtensionDegree.Read(M).At(k, K, l)),
				"Kl is finite over K",
				"of degree [l : k]")
			tInM := a.Have(
				"t lies in M",
				"t ∈ M.carrier",
				BySets(tInK, data, field.SubfieldSubset.At(m, K)))
			ktInLt := a.Have(
				"k(t) lies in l(t)",
				"field_adjoin(M, k, {t}) ⊆ field_adjoin(M, l, {t})",
				By(lField, kInL, tInM, Read(rationalInside, M).At(k, l, t)))
			sameField := a.Have(
				"k(t)(l) is l(t)",
				"field_adjoin(M, field_adjoin(M, k, {t}), l) = field_adjoin(M, l, {t})",
				Derive(func(b *Argument) {
					into := b.Have(
						"l(t) holds k(t) and l",
						"field_adjoin(M, field_adjoin(M, k, {t}), l) ⊆ field_adjoin(M, l, {t})",
						By(ltField, ktInLt, lInLt, algebraic_element.AdjoinLeast.Read(M).At(kt, l, lt)))
					upper := b.Conjuncts(
						GroupPremises(rational[0], lField, Read(composite, M).At(kt, l)),
						"k(t)(l) is a subfield",
						"holding k(t)",
						"and l")
					singletonInside := b.Have(
						"so it holds t",
						"{t} ⊆ field_adjoin(M, field_adjoin(M, k, {t}), l)",
						BySets(tInKt, upper[1]))
					onto := b.Have(
						"k(t)(l) holds l and t",
						"field_adjoin(M, l, {t}) ⊆ field_adjoin(M, field_adjoin(M, k, {t}), l)",
						By(
							upper[0],
							upper[2],
							singletonInside,
							algebraic_element.AdjoinLeast.Read(M).At(l, singleton, ktl)))
					b.Show(
						"the two fields hold each other",
						By(into, onto, set_order.SubsetAntisym.At(ktl, lt)))
				}))
			inside := a.Conjuncts(
				a.Have(
					"l(t) is finite over k(t), of degree [l : k]",
					"finite_extension(M, field_adjoin(M, k, {t}), field_adjoin(M, l, {t})) ∧ "+
						"extension_degree(M, field_adjoin(M, k, {t}), field_adjoin(M, l, {t})) = extension_degree(M, k, l)",
					By(sameField, keptKt[0], keptKt[1])),
				"l(t) is finite over k(t)",
				"of degree [l : k]")
			throughK := a.Conjuncts(
				GroupPremises(
					rational[0],
					data,
					composed[0],
					rational[3],
					composed[1],
					finiteK,
					keptK[0],
					field_extension.TowerLaw.Read(M).At(kt, K, Kl)),
				"Kl is finite over k(t)",
				"of degree [K : k(t)] [Kl : K]")
			finiteAbove := a.Have(
				"so Kl is finite over l(t)",
				"finite_extension(M, field_adjoin(M, l, {t}), field_adjoin(M, K, l))",
				By(
					ktField,
					ltField,
					KlField,
					ktInLt,
					ltInKl,
					throughK[0],
					field_extension.TowerFinite.Read(M).At(kt, lt, Kl)))
			throughLt := a.Have(
				"the tower from k(t) to Kl through l(t)",
				"extension_degree(M, field_adjoin(M, k, {t}), field_adjoin(M, K, l)) = "+
					"extension_degree(M, field_adjoin(M, k, {t}), field_adjoin(M, l, {t})) * "+
					"extension_degree(M, field_adjoin(M, l, {t}), field_adjoin(M, K, l))",
				By(
					ktField,
					ltField,
					KlField,
					ktInLt,
					ltInKl,
					inside[0],
					finiteAbove,
					field_extension.TowerLaw.Read(M).At(kt, lt, Kl)))
			degree := a.Have(
				"[l : k] cancels from the two towers",
				"extension_degree(M, field_adjoin(M, l, {t}), field_adjoin(M, K, l)) = "+
					"extension_degree(M, field_adjoin(M, k, {t}), K)",
				ByArith(
					throughK[1],
					throughLt,
					keptK[1],
					inside[1],
					data,
					lField,
					kInL,
					finite,
					field_extension.ExtensionDegreePositive.Read(M).At(k, l),
					nat_arith.MulEqLCancel.At(
						a.TermAs[Nat]("extension_degree(M, k, l)"),
						a.TermAs[Nat]("extension_degree(M, field_adjoin(M, l, {t}), field_adjoin(M, K, l))"),
						a.TermAs[Nat]("extension_degree(M, field_adjoin(M, k, {t}), K)"))))
			infiniteKt := a.Have(
				"k(t) is infinite, holding the transcendental t",
				"infinite(field_adjoin(M, k, {t}))",
				By(
					data,
					ktField,
					tInKt,
					transcendental,
					algebraic_element.TranscendentalSubfieldInfinite.Read(M).At(k, kt, t)))
			z, primitive := a.ObtainAs[A](
				"so K, finite and separable over k(t), is generated over it by one z",
				"∃z:A. z ∈ K ∧ field_adjoin(M, field_adjoin(M, k, {t}), {z}) = K",
				By(
					ktField,
					data,
					ktInK,
					infiniteKt,
					finiteK,
					separable,
					algebraic_closure.PrimitiveElement.Read(M).At(kt, K)))
			zParts := a.Conjuncts(
				primitive,
				"z lies in K",
				"z generates K over k(t)")
			zInK, generatesK := zParts[0], zParts[1]
			zInM := a.Have(
				"z lies in M",
				"z ∈ M.carrier",
				BySets(zInK, data, field.SubfieldSubset.At(m, K)))
			zMember := a.MemberOf[on.M](z, zInM)
			zSeparable := a.Have(
				"z is separable over k(t), so over the larger l(t)",
				"separable_over(M, field_adjoin(M, l, {t}), z)",
				By(
					ktField,
					ltField,
					ktInLt,
					separable.At(z),
					zInK,
					galois_correspondence.SeparableTower.Read(M).At(kt, lt, zMember)))
			zInKl := a.Have(
				"z lies in Kl",
				"z ∈ field_adjoin(M, K, l)",
				BySets(zInK, KInKl))
			ltz := a.TermAs[Set[A]]("field_adjoin(M, field_adjoin(M, l, {t}), {z})")
			top := a.Conjuncts(
				GroupPremises(
					extended[0],
					composed[0],
					extended[3],
					zInKl,
					algebraic_element.AdjoinElementBetween.Read(M).At(lt, Kl, z)),
				"l(t, z) is a subfield",
				"holding l(t)",
				"and z",
				"inside Kl")
			ltzField, ltInLtz, zInLtz := top[0], top[1], top[2]
			KlInLtz := a.Have(
				"Kl lies in l(t, z): it holds K = k(t, z) and l",
				"field_adjoin(M, K, l) ⊆ field_adjoin(M, field_adjoin(M, l, {t}), {z})",
				Derive(func(b *Argument) {
					holds := b.Have(
						"l(t, z) holds k(t), z and l",
						"field_adjoin(M, k, {t}) ⊆ field_adjoin(M, field_adjoin(M, l, {t}), {z}) ∧ "+
							"{z} ⊆ field_adjoin(M, field_adjoin(M, l, {t}), {z}) ∧ "+
							"l ⊆ field_adjoin(M, field_adjoin(M, l, {t}), {z})",
						BySets(ktInLt, lInLt, ltInLtz, zInLtz))
					KInLtz := b.Have(
						"so it holds K",
						"K ⊆ field_adjoin(M, field_adjoin(M, l, {t}), {z})",
						By(
							ltzField,
							holds,
							generatesK,
							algebraic_element.AdjoinLeast.Read(M).At(kt, b.TermAs[Set[A]]("{z}"), ltz)))
					b.Show(
						"so it holds Kl",
						By(ltzField, holds, KInLtz, algebraic_element.AdjoinLeast.Read(M).At(K, l, ltz)))
				}))
			separableKl := a.Have(
				"every element of Kl is separable over l(t), lying in l(t, z)",
				"∀x:A. x ∈ field_adjoin(M, K, l) ⇒ separable_over(M, field_adjoin(M, l, {t}), x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					xInLtz := b.Have(
						"x lies in l(t, z)",
						"x ∈ field_adjoin(M, field_adjoin(M, l, {t}), {z})",
						BySets(xIn, KlInLtz))
					b.Show(
						"z being separable over l(t), so is x",
						By(
							ltField,
							zSeparable,
							xInLtz,
							algebraic_closure.SeparableAdjoinSeparable.Read(M).At(lt, zMember, x)))
				}))
			a.Show(
				"so t separates Kl over l, with the degree of K over k(t)",
				Simp(Fwd(ConstantCompositeDef)),
				By(finiteAbove, separableKl, degree))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K, l *Expr[Set[A]],
			regular, lField, kInL, finite Fact,
		) {
			data := a.Unfolded(regular, function_field.RegularFunctionFieldDef)
			degreeOverK := a.Have(
				"Kl has degree [l : k] over K",
				"finite_extension(M, K, constant_composite(M, K, l)) ∧ "+
					"extension_degree(M, K, constant_composite(M, K, l)) = extension_degree(M, k, l)",
				Simp(Fwd(ConstantCompositeDef)),
				By(data, lField, kInL, finite, ConstantExtensionDegree.Read(M).At(k, K, l)))
			f, multiplication := a.UnpackAs[Fun[_Tensor, A]](
				GroupPremises(data, lField, kInL, finite, degreeOverK, ConstantCompositeTensor.Read(M).At(k, K, l)),
				"f")
			a.Show(
				"Kl is regular over l, multiplication identifies l ⊗ₖ "+
					"K with Kl, and parameters of K stay parameters of Kl",
				SplitConj(
					Case(
						"Kl is regular over l",
						By(regular, lField, kInL, finite, Read(regularComposite, M).At(k, K, l))),
					Case(
						"multiplication is the isomorphism, and a separating parameter of K stays one of Kl",
						Witness(f),
						SplitConj(
							Case(
								"f is multiplication on pure tensors, an isomorphism",
								By(multiplication)),
							Case(
								"each parameter t of K separates Kl over l(t)",
								a.ForEach(func(t *Expr[A]) Action {
									return By(Normalized, regular, lField, kInL, finite, Read(parameterExtension, M).At(k, K, l, t))
								}))))))
		})
	}),
})}
