// models.go — integral plane models exist: a function field regular over k,
// finite and separable over k(t), has one read inside its own carrier, and so
// does the field k(t)(z) of a root z of an absolutely irreducible monic
// equation F over k[T] read at a transcendental t.

package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/rational_function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/separating_parameter"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegralPlaneModelExists — a function field regular over k, finite and
// separable over k(t), has an integral plane model read inside its own
// carrier: a primitive element with a monic separable minimal polynomial over
// k[t], and a weight above the degrees of its finitely many coefficients. The
// restriction keeps the operations, so the adjunctions, the algebraicity and
// the minimal polynomial are those of M.
var IntegralPlaneModelExists = integralPlaneModelExistsThm{family.Add(registry.ProofEntry{
	Name: "IntegralPlaneModelExists",
	Key:  "prop_a071f8531c1b072b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"t ∈ K",
			"¬algebraic_over(M, k, t)",
			"finite_extension(M, «pmRational», K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, «pmRational», x)",
		},
		Conclusion: "∃z:A. ∃F:(num → A). ∃b:num. integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t *Expr[A],
		regular, tInK, transcendental, finiteOverBase, separable Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		base := a.TermAs[Set[A]]("«pmRational»")
		single := a.TermAs[Set[A]]("{t}")
		ambient := a.Unfolded(regular, function_field.RegularFunctionFieldDef)
		subfields := a.Have(
			"k and K are subfields of M, k inside K",
			"subfield(M, k) ∧ subfield(M, K) ∧ k ⊆ K",
			By(ambient))
		z, primitive := a.UnpackAs[A](
			GroupPremises(
				subfields,
				tInK,
				transcendental,
				finiteOverBase,
				separable,
				separating_parameter.IntegralPrimitiveElement.Read(M).At(k, K, t)),
			"z")
		F, isMinimal := a.LetAs[Fun[Nat, A]]("F", "minimal_polynomial(M, «pmRational», z)")
		inImage := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. u ∈ «pmPolynomials» ⇔ ∃c:(num → A). polynomial_over(k, c) ∧ u = polynomial_eval(c, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		coefficient := a.Have(
			"Each coefficient of F is the value at t of a polynomial over k",
			"∀i:num. ∃c:(num → A). polynomial_over(k, c) ∧ polynomial_eval(c, t) = F(i)",
			Derive(func(c *Argument) {
				c.Fix()
				inImageRing := c.Have(
					"The coefficient lies in k[t]",
					"F(i) ∈ «pmPolynomials»",
					By(primitive, polynomial.PolynomialOverDef))
				c.Show(
					"which is the value at t of a polynomial over k",
					By(inImage.At(c.TermAs[A]("F(i)")), inImageRing))
			}))
		bounded := a.Have(
			"Finitely many coefficients have a common degree bound",
			"∀n:num. ∃B:num. ∀i:num. "+
				"    i < n ⇒ "+
				"    ∃g:(num → A). polynomial_over(k, g) ∧ polynomial_degree(g) ≤ B ∧ polynomial_eval(g, t) = F(i)",
			Derive(func(c *Argument) {
				c.Induct("n")
				c.Base(
					"no index lies below 0",
					func(d *Argument) {
						d.Take(d.TermAs[Nat]("0"))
						d.Show(
							"so any bound serves",
							ByArith())
					})
				c.Step(
					"one more coefficient adds its degree to the bound",
					func(d *Argument, ih Fact) {
						n := d.TermAs[Nat]("n")
						_, bound := d.UnpackAs[Nat](ih, "B")
						next, nextData := d.UnpackAs[Fun[Nat, A]](coefficient.At(n), "e")
						d.Take(d.TermAs[Nat]("B + polynomial_degree(e)"))
						i := d.FixAs[Nat]("i")
						below := d.Assume()
						d.Cases(d.Term("i = n"))
						d.When(
							"The new index takes the new polynomial",
							func(e *Argument, same Fact) {
								e.Take(next)
								degree := e.Have(
									"Its degree lies under the sum",
									"polynomial_degree(e) ≤ B + polynomial_degree(e)",
									ByArith())
								e.Show(
									"and its value at t is F(n)",
									By(nextData, same, degree))
							})
						d.Otherwise(
							"An older index keeps its polynomial, under a larger bound",
							func(e *Argument, other Fact) {
								older := e.Have(
									"The index lies below n",
									"i < n",
									ByArith(below, other))
								kept, keptData := e.UnpackAs[Fun[Nat, A]](GroupPremises(older, bound.At(i)), "h")
								degree := e.Have(
									"Its degree lies under the sum",
									"polynomial_degree(h) ≤ B + polynomial_degree(e)",
									ByArith(keptData))
								e.Take(kept)
								e.Show(
									"and its value at t is F(i)",
									By(keptData, degree, older))
							})
					})
			}))
		_, bound := a.UnpackAs[Nat](bounded.At(a.TermAs[Nat]("polynomial_degree(F)")), "B")
		baseInK := a.Have(
			"k(t) lies in K",
			"«pmRational» ⊆ K",
			By(
				subfields,
				tInK,
				set_order.SingSubset.At(K, t),
				algebraic_element.AdjoinLeast.Read(M).At(k, single, K)))
		sameBase := a.Have(
			"k(t) is one field read in K and in M",
			"«pmRationalInK» = «pmRational»",
			By(
				subfields,
				tInK,
				set_order.SingSubset.At(K, t),
				algebraic_element.AdjoinInSubfield.Read(M).At(K, k, single)))
		sameTop := a.Have(
			"K is k(t)(z) read in K as in M",
			"field_adjoin(restrict_field(M, K), «pmRational», {z}) = K",
			By(
				primitive,
				subfields,
				baseInK,
				set_order.SingSubset.At(K, z),
				algebraic_element.AdjoinInSubfield.Read(M).At(K, base, a.TermAs[Set[A]]("{z}"))))
		sameParameter := a.Have(
			"t stays transcendental read in K",
			"¬algebraic_over(restrict_field(M, K), k, t)",
			Unfold(algebraic_element.AlgebraicOverDef))
		sameMinimal := a.Have(
			"The minimal polynomial reads the operations alone, which the restriction keeps",
			"F = minimal_polynomial(restrict_field(M, K), «pmRational», z)",
			Unfold(algebraic_element.MinimalPolynomialDef))
		algebraic := a.Have(
			"z is algebraic over k(t)",
			"algebraic_over(M, «pmRational», z)",
			By(separable.At(z), primitive, galois_correspondence.SeparableOverDef))
		inCarrier := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfields, field.SubfieldSubset.At(ops, K)))
		zInM := a.MemberOf[on.M](z, a.Have(
			"z lies in M",
			"z ∈ M.carrier",
			By(primitive, inCarrier, set_basic.SubsetDef)))
		tInM := a.Have(
			"t lies in M",
			"{t} ⊆ M.carrier",
			By(tInK, inCarrier, set_order.SingSubset, set_basic.SubsetDef))
		baseSubfield := a.Have(
			"k(t) is a subfield of M",
			"subfield(M, «pmRational»)",
			By(
				subfields,
				tInM,
				field.SubfieldSubset.At(ops, k),
				algebraic_element.AdjoinSubfield.Read(M).At(k, single)))
		positive := a.Have(
			"The minimal polynomial has positive degree",
			"0 < polynomial_degree(F)",
			By(
				Normalized,
				algebraic,
				baseSubfield,
				isMinimal,
				zInM,
				algebraic_element.MinimalPolynomialPositive.Read(M).At(base, zInM)))
		weights := a.Have(
			"Each coefficient has its degree under its weight",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < polynomial_degree(F)"},
				Conclusion: "∃g:(num → A). " +
					"    polynomial_over(k, g) ∧ " +
					"    polynomial_degree(g) ≤ (B + 1) * (polynomial_degree(F) - i) ∧ " +
					"    polynomial_eval(g, t) = F(i)",
			},
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				below := c.Assume()
				g, gData := c.UnpackAs[Fun[Nat, A]](GroupPremises(below, bound.At(i)), "g")
				weight := c.Have(
					"The weight is at least B + 1, since i lies below the degree",
					"polynomial_degree(g) ≤ (B + 1) * (polynomial_degree(F) - i)",
					ByArith(
						below,
						gData,
						nat_order.LessEqMulNonzero.At(c.TermAs[Nat]("B + 1"), c.TermAs[Nat]("polynomial_degree(F) - i"))))
				c.Take(g)
				c.Show(
					"so the polynomial of the coefficient has the required degree",
					By(gData, weight))
			}))
		a.Take(z)
		a.Take(F)
		a.Take(a.TermAs[Nat]("B + 1"))
		restricted := a.Have(
			"K stays regular over k read in K",
			"regular_function_field(restrict_field(M, K), k, K)",
			By(subfields, regular, function_field.RegularFunctionFieldInRestriction.Read(M).At(k, K)))
		weightPositive := a.Have(
			"The weight is positive",
			"0 < B + 1",
			ByArith())
		sameRing := a.Have(
			"Restricted to k(t), the ring of K is the ring of M",
			"restrict_ring(field_ring(restrict_field(M, K)), «pmRational») = "+
				"restrict_ring(field_ring(M), «pmRational»)",
			Unfold(module_record.RestrictRingDef))
		a.Show(
			"Read in K, these are the conditions of an integral plane model",
			Simp(Fwd(IntegralPlaneModelDef)),
			By(
				restricted,
				tInK,
				sameParameter,
				primitive,
				sameBase,
				sameTop,
				sameMinimal,
				sameRing,
				positive,
				weightPositive,
				weights))
	}),
})}

// AbsoluteEquationGenericModel — let M be algebraically closed, k a perfect
// subfield, t an element of M transcendental over k, and F an absolutely
// irreducible monic plane equation over k[T]. Then f = F(t, Z) has a root z in
// M, f has the degree of F in Z, and f with the weight
// b = 1 + Σ_{j < deg f} deg F(j) is an integral plane model of k(t)(z). The
// rows of F read at t form the monic f over k[t]; Gauss's lemma makes f the
// minimal polynomial of z over k(t) and K = k(t)(z) regular over k; the
// derivative of F in Z, nonzero, reads as a nonzero derivative of f, so f is
// separable; and each coefficient of f below its degree is a row F(i) read at
// t, of degree at most b − 1, under the weight b(deg f − i).
var AbsoluteEquationGenericModel = absoluteEquationGenericModelThm{family.Add(registry.ProofEntry{
	Name: "AbsoluteEquationGenericModel",
	Key:  "prop_71dad91dccf9a833",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"perfect_field(restrict_field(M, k))",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"absolute_plane_equation(M, k, F)",
		},
		Conclusion: "∃z:A. ∃b:num. " +
			"    z ∈ M.carrier ∧ " +
			"    integral_plane_model(restrict_field(M, field_adjoin(M, «pmRational», {z})), " +
			"        k, " +
			"        t, " +
			"        z, " +
			"        «f», " +
			"        b) ∧ " +
			"    polynomial_degree(«f») = polynomial_degree(λi:num. M.zero, F)",
		Abbrev: Abbrev{
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			{Name: "Pk", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		t *Expr[A],
		closed, kField, perfect, tIn, transcendental, equation Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		polynomials := a.TermAs[Set[A]]("«pmPolynomials»")
		rational := a.TermAs[Set[A]]("«pmRational»")
		carrier := a.TermAs[Set[A]]("M.carrier")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		tm := a.MemberOf[on.M](t, tIn)
		plane := a.Conjuncts(
			a.Unfolded(equation, AbsolutePlaneEquationDef),
			"F is a polynomial over k[T]",
			"F is monic in Z",
			"of positive degree",
			"F is irreducible over k̄[T]",
			"and its derivative in Z is not zero")
		overP, monic, positiveF, irreducible, derivative := plane[0], plane[1], plane[2], plane[3], plane[4]
		rows := a.Conjuncts(
			GroupPremises(overP, monic, rational_function_field.MonicRowsAtPoint.Read(M).At(k, F, tm)),
			"the rows of F read at t form a polynomial f over k[t]",
			"f is monic",
			"f has the degree of F")
		fOver, fMonic, fDegree := rows[0], rows[1], rows[2]
		rings := a.Have(
			"k[t] is a subring inside the subfield k(t), which holds t",
			"subring(field_ring(M), «pmPolynomials») ∧ "+
				"«pmPolynomials» ⊆ «pmRational» ∧ "+
				"subfield(M, «pmRational») ∧ "+
				"k ⊆ «pmRational» ∧ "+
				"t ∈ «pmRational»",
			By(
				kField,
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm),
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		fInM := a.Have(
			"f is a polynomial over M of positive degree",
			"polynomial_over(M.carrier, «f») ∧ 0 < polynomial_degree(«f»)",
			By(
				rings,
				fOver,
				fDegree,
				positiveF,
				comm_ring.SubringSubset.At(fieldRing, polynomials),
				polynomial.PolynomialOverMono.At(zero, polynomials, carrier, f),
				polynomial.PolynomialRingDef))
		z, rooted := a.ObtainAs[A](
			"M being algebraically closed, f has a root z in M",
			"∃z:A. z ∈ M.carrier ∧ polynomial_eval(«f», z) = M.zero",
			By(closed, fInM, algebraic_closure.AlgebraicallyClosedDef),
			Named("z"))
		rootParts := a.Conjuncts(
			rooted,
			"z lies in M",
			"z is a root of f")
		zIn, root := rootParts[0], rootParts[1]
		zm := a.MemberOf[on.M](z, zIn)
		// absolute_plane_equation spells k̄ by the set-builder {x | x ∈ M.carrier ∧
		// algebraic_over(M, k, x)}: read it as algebraic_elements(M, k), the spelling
		// AbsolutelyIrreducibleRegular states.
		irreducibleBar := a.Simplified(irreducible, Rev(algebraic_element.AlgebraicElementsDef))
		model := a.Conjuncts(
			GroupPremises(
				kField,
				perfect,
				transcendental,
				overP,
				monic,
				irreducibleBar,
				root,
				rational_function_field.AbsolutelyIrreducibleRegular.Read(M).At(k, F, tm, zm)),
			"by Gauss's lemma f is the minimal polynomial of z over k(t)",
			"and K = k(t)(z) is a regular function field over k")
		minimal, regular := model[0], model[1]
		K := a.TermAs[Set[A]]("field_adjoin(M, «pmRational», {z})")
		algebraic := a.Have(
			"z is algebraic over k(t), a root of the nonzero f",
			"algebraic_over(M, «pmRational», z)",
			By(
				rings,
				fOver,
				root,
				fMonic,
				polynomial.PolynomialOverMono.At(zero, polynomials, rational, f),
				polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M)),
				algebraic_element.AlgebraicOverDef.At(ops, rational, z)))
		top := a.Have(
			"K is a subfield holding k(t) and z",
			"subfield(M, field_adjoin(M, «pmRational», {z})) ∧ "+
				"«pmRational» ⊆ field_adjoin(M, «pmRational», {z}) ∧ "+
				"z ∈ field_adjoin(M, «pmRational», {z})",
			By(rings, algebraic_element.AdjoinElementSubfield.Read(M).At(rational, zm)))
		rationalField := a.Have(
			"k(t) is a field under the operations of M",
			"field_on(restrict_field(M, «pmRational»))",
			By(rings, field.SubfieldFieldOn.Read(M).At(rational)))
		separable := a.Have(
			"f, irreducible over k(t) with a nonzero derivative, is separable over k(t)",
			"polynomial_separable(restrict_ring(field_ring(M), «pmRational»), «f»)",
			By(
				rings,
				zIn,
				algebraic,
				minimal,
				rationalField,
				algebraic_element.MinimalPolynomialIrreducible.Read(M).At(rational, zm),
				a.Have(
					"F has a nonzero derivative in Z, so f has a nonzero derivative",
					"polynomial_derivative(«f») ≠ vec_zero",
					By(
						M,
						kField,
						tIn,
						transcendental,
						overP,
						derivative,
						rational_function_field.RowsDerivativeNonzero.At(ops, k, F, t))),
				field.RestrictFieldRing.At(ops, rational),
				separable_polynomial.SeparableIffDerivative.Read(rationalField)))
		inK := a.Have(
			"K holds k, t and z",
			"k ⊆ field_adjoin(M, «pmRational», {z}) ∧ "+
				"{t} ⊆ field_adjoin(M, «pmRational», {z}) ∧ "+
				"{z} ⊆ field_adjoin(M, «pmRational», {z}) ∧ "+
				"t ∈ field_adjoin(M, «pmRational», {z})",
			BySets(rings, top))
		restricted := a.Have(
			"K stays regular over k read in K",
			"regular_function_field(restrict_field(M, field_adjoin(M, «pmRational», {z})), "+
				"    k, "+
				"    field_adjoin(M, «pmRational», {z}))",
			By(top, regular, function_field.RegularFunctionFieldInRestriction.Read(M).At(k, K)))
		sameBase := a.Have(
			"k(t) is one field read in K and in M",
			"field_adjoin(restrict_field(M, field_adjoin(M, «pmRational», {z})), k, {t}) = «pmRational»",
			By(top, inK, algebraic_element.AdjoinInSubfield.Read(M).At(K, k, a.TermAs[Set[A]]("{t}"))))
		sameTop := a.Have(
			"K is k(t)(z) read in K as in M",
			"field_adjoin(restrict_field(M, field_adjoin(M, «pmRational», {z})), «pmRational», {z}) = "+
				"field_adjoin(M, «pmRational», {z})",
			By(top, inK, algebraic_element.AdjoinInSubfield.Read(M).At(K, rational, a.TermAs[Set[A]]("{z}"))))
		sameParameter := a.Have(
			"t stays transcendental read in K",
			"¬algebraic_over(restrict_field(M, field_adjoin(M, «pmRational», {z})), k, t)",
			Unfold(algebraic_element.AlgebraicOverDef))
		sameMinimal := a.Have(
			"the minimal polynomial reads the operations alone, which the restriction keeps",
			"minimal_polynomial(restrict_field(M, field_adjoin(M, «pmRational», {z})), «pmRational», z) = «f»",
			Unfold(algebraic_element.MinimalPolynomialDef))
		sameRing := a.Have(
			"restricted to k(t), the ring of K is the ring of M",
			"restrict_ring(field_ring(restrict_field(M, field_adjoin(M, «pmRational», {z}))), "+
				"    «pmRational») = "+
				"restrict_ring(field_ring(M), «pmRational»)",
			Unfold(module_record.RestrictRingDef))
		rowsOverK := a.Have(
			"each row of F is a polynomial over k",
			"∀i:num. polynomial_over(k, F(i))",
			By(
				overP,
				polynomial.PolynomialOverDef.At(
					a.TermAs[Fun[Nat, A]]("«Pk».zero"), a.TermAs[Set[Fun[Nat, A]]]("«Pk».carrier"), F)))
		_, bDef := a.LetAs[Nat](
			"B", "nat_sum({j:num | j < polynomial_degree(«f»)}, λj:num. polynomial_degree(F(j)))")
		below := a.TermAs[Set[Nat]]("{j:num | j < polynomial_degree(«f»)}")
		rowDegrees := a.TermAs[Fun[Nat, Nat]]("λj:num. polynomial_degree(F(j))")
		weights := a.Have(
			"each coefficient of f below its degree is a row of "+
				"F read at t, of degree at most (B + 1)(deg f − i)",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < polynomial_degree(«f»)"},
				Conclusion: "∃a:(num → A). " +
					"    polynomial_over(k, a) ∧ " +
					"    polynomial_degree(a) ≤ (B + 1) * (polynomial_degree(«f») - i) ∧ " +
					"    polynomial_eval(a, t) = polynomial_eval(F(i), t)",
			},
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				isBelow := c.Assume()
				bounded := c.Have(
					"the degree of F(i) is one term of the sum B",
					"polynomial_degree(F(i)) ≤ B",
					By(
						bDef,
						isBelow,
						num_segment.FiniteBelowStrict.At(c.TermAs[Nat]("polynomial_degree(«f»)")),
						nat_sum.TermLeSum.At(rowDegrees, below, i)))
				c.Take(c.TermAs[Fun[Nat, A]]("F(i)"))
				c.Show(
					"F(i) itself, its degree under B + 1 ≤ (B + 1)(deg f − i), as i lies below deg f",
					ByArith(
						isBelow,
						bounded,
						rowsOverK.At(i),
						nat_order.LessEqMulNonzero.At(c.TermAs[Nat]("B + 1"), c.TermAs[Nat]("polynomial_degree(«f») - i"))))
			}))
		zeroRow := a.Have(
			"the zero of k[T], the zero vector, is the constant zero sequence",
			"polynomial_degree(vec_zero, F) = polynomial_degree(λi:num. M.zero, F)",
			By(
				Normalized,
				a.Have(
					"the zero vector is the constant zero sequence",
					"vec_zero = (λi:num. M.zero)",
					Funext(),
					By(vec_space.VecZeroDef))))
		weightPositive := a.Have(
			"the weight B + 1 is positive",
			"0 < B + 1",
			ByArith())
		a.Take(z)
		a.Take(a.TermAs[Nat]("B + 1"))
		a.Show(
			"read in K, these are the conditions of an integral plane model, and f has the degree of F",
			Simp(Fwd(IntegralPlaneModelDef)),
			By(
				zIn,
				restricted,
				inK,
				sameParameter,
				top,
				sameBase,
				sameTop,
				minimal,
				sameMinimal,
				separable,
				sameRing,
				fInM,
				weightPositive,
				weights,
				fDegree,
				zeroRow,
				set_order.SubsetRefl))
	}),
})}
