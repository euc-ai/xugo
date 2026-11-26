// absolutely_irreducible.go — the constants of a rational function field: an
// element of k(t), t transcendental over k, that is algebraic over k lies in
// k; and so the function field of an absolutely irreducible monic equation is
// regular over a perfect field of constants.

package rational_function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RationalFunctionConstants — k is algebraically closed in k(t) for t
// transcendental over k. Write x = a/b with a = p(t), b = q(t), p and q over
// k. Over the field of elements algebraic over k, t stays transcendental and
// x is a constant, so p(t) = x·q(t) makes p = x·q coefficientwise; at the
// degree of q this reads x = p(d)/q(d), a quotient of two elements of k.
var RationalFunctionConstants = rationalFunctionConstantsThm{family.Add(registry.ProofEntry{
	Name: "RationalFunctionConstants",
	Key:  "prop_84aa16d889fadf33",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t x:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"x ∈ field_adjoin(M, k, {t})",
			"algebraic_over(M, k, x)",
		},
		Conclusion: "x ∈ k",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			// Body-only: polynomial_degree(q) is the degree of q, the polynomial over k the body
			// obtains with b = q(t).
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t, x *Expr[A],
		kField, tIn, transcendental, xRational, algebraic Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		closure := a.TermAs[Set[A]]("algebraic_elements(M, k)")
		tm := a.MemberOf[on.M](t, tIn)
		ring := field.RingOn.Read(M)
		xm := a.MemberOf[on.M](x, a.Have(
			"x lies in M",
			"x ∈ M.carrier",
			By(
				tIn,
				xRational,
				kField,
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
				field.SubfieldSubset.At(ops, a.TermAs[Set[A]]("field_adjoin(M, k, {t})")),
				set_basic.SubsetDef)))
		closed := a.Have(
			"the elements algebraic over k form a subfield containing k",
			"subfield(M, algebraic_elements(M, k)) ∧ k ⊆ algebraic_elements(M, k)",
			By(kField, algebraic_element.AlgebraicElementsSubfield.Read(M).At(k)))
		closureMembers := a.Have(
			"they lie in M and are algebraic over k",
			"algebraic_elements(M, k) ⊆ M.carrier ∧ "+
				"(∀y:A. y ∈ algebraic_elements(M, k) ⇒ algebraic_over(M, k, y))",
			BySets(algebraic_element.AlgebraicElementsDef))
		stillTranscendental := a.Have(
			"t stays transcendental over them, algebraicity over k being transitive",
			"¬algebraic_over(M, algebraic_elements(M, k), t)",
			By(
				transcendental,
				tIn,
				kField,
				closureMembers,
				algebraic_element.AlgebraicOverTrans.Read(M).At(k, closure, tm)))
		xClosed := a.Have(
			"x is one of them",
			"x ∈ algebraic_elements(M, k)",
			BySets(xm, algebraic, algebraic_element.AlgebraicElementsDef))
		// k(t) is the fraction field of k[t].
		fractions := a.Unfolded(
			GroupPremises(kField, integral_element.RationalFunctionsFractionField.Read(M).At(k, tm)),
			field.FractionFieldCarrierDef)
		_, _, quotient := a.Obtain2As[A, A](
			"write x as a quotient a/b of two elements of k[t]",
			"∃a b:A. a ∈ «polynomials» ∧ b ∈ «polynomials» ∧ b ≠ M.zero ∧ x * b = a",
			By(xRational, fractions),
			Named("a", "b"))
		image := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. u ∈ «polynomials» ⇔ ∃c:(num → A). polynomial_over(k, c) ∧ u = polynomial_eval(c, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		p, q, values := a.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
			"write a = p(t) and b = q(t) with p and q over k",
			"∃p q:(num → A). "+
				"    polynomial_over(k, p) ∧ "+
				"    polynomial_over(k, q) ∧ "+
				"    a = polynomial_eval(p, t) ∧ "+
				"    b = polynomial_eval(q, t)",
			By(image, quotient),
			Named("p", "q"))
		scaled := a.TermAs[Fun[Nat, A]]("x • q")
		scaledOver := a.Have(
			"x·q is a polynomial over the elements algebraic over k",
			"polynomial_over(algebraic_elements(M, k), x • q)",
			By(
				xm,
				xClosed,
				closed,
				values,
				polynomial.PolynomialOverDef.At(zero, k, q),
				polynomial.PolynomialOverDef.At(zero, closure, scaled),
				vec_space.VecSmulOn.Read(ring),
				vec_space.VecScalarMulDef,
				field.SubfieldMul,
				set_basic.SubsetDef))
		coefficientwise := a.Have(
			"p(t) = x·q(t), and reading at t is one-to-one over the algebraic elements, so p = x·q",
			"p = x • q",
			By(
				stillTranscendental,
				tIn,
				xm,
				kField,
				closed,
				quotient,
				values,
				scaledOver,
				algebraic_element.EvalInjectiveTranscendental.Read(M).At(closure, tm, p, scaled),
				polynomial_evaluation.EvalScalar.Read(ring).At(xm, tm, q),
				polynomial.PolynomialOverMono.At(zero, k, closure, p),
				polynomial.PolynomialOverMono.At(zero, k, a.TermAs[Set[A]]("M.carrier"), q),
				field.SubfieldSubset.At(ops, k)))
		nonzero := a.Have(
			"b ≠ 0, so q is not the zero polynomial",
			"q ≠ vec_zero",
			By(Normalized, tIn, quotient, values, polynomial_evaluation.EvalVecZero.Read(ring).At(tm)))
		leading := a.Conjuncts(
			a.Have(
				"at the degree d of q, q(d) ≠ 0 and p(d) = x·q(d), both coefficients in k",
				"q(polynomial_degree(q)) ≠ M.zero ∧ "+
					"q(polynomial_degree(q)) ∈ k ∧ "+
					"p(polynomial_degree(q)) ∈ k ∧ "+
					"p(polynomial_degree(q)) = x * q(polynomial_degree(q))",
				By(
					nonzero,
					coefficientwise,
					values,
					polynomial.DegreeLeading.At(zero, k, q),
					polynomial.PolynomialOverDef.At(zero, k, q),
					polynomial.PolynomialOverDef.At(zero, k, p),
					vec_space.VecScalarMulDef)),
			"q(d) ≠ 0",
			"q(d) lies in k",
			"p(d) lies in k",
			"p(d) = x·q(d)")
		qNonzero, qIn, pIn, relation := leading[0], leading[1], leading[2], leading[3]
		inM := a.Have(
			"both coefficients lie in M",
			"q(polynomial_degree(q)) ∈ M.carrier ∧ p(polynomial_degree(q)) ∈ M.carrier",
			By(kField, qIn, pIn, field.SubfieldSubset.At(ops, k), set_basic.SubsetDef))
		qd := a.MemberOf[on.M](a.TermAs[A]("q(polynomial_degree(q))"), a.Have(
			"q(d) lies in M",
			"q(polynomial_degree(q)) ∈ M.carrier",
			By(Normalized, inM)))
		divided := a.Have(
			"so x = p(d)/q(d)",
			"x = p(polynomial_degree(q)) / q(polynomial_degree(q))",
			ByArith(
				M,
				xm,
				inM,
				qNonzero,
				Scaled(a.TermAs[A]("M.inv(q(polynomial_degree(q)))"), relation),
				Scaled(x, field.MulLeftInverseOn.Read(M).At(qd))))
		a.Show(
			"a quotient of two elements of k lies in k",
			By(
				Normalized,
				divided,
				kField,
				qIn,
				pIn,
				field.SubfieldDiv.Read(M).AsFact().At(
					k, a.TermAs[A]("p(polynomial_degree(q))"), a.TermAs[A]("q(polynomial_degree(q))"))))
	}),
})}

// AbsolutelyIrreducibleRegular — let F be monic over k[T] and irreducible over
// k̄[T], k̄ the elements algebraic over k, t transcendental over k and z a root
// of f, the rows of F read at t. Then f is the minimal polynomial of z over
// k(t), and K = k(t)(z) is a regular function field over k when k is perfect.
// By Gauss's lemma over k̄ (GaussMinimalPolynomial at k̄) f is the minimal
// polynomial of z over k̄(t), hence over every field between k(t) and k̄(t). An element x of K algebraic over k lies
// in k̄, so E = k(t)(x) is such a field: [K : E] = deg f = [K : k(t)] forces
// E = k(t), and x, in k(t) and algebraic over k, lies in k.
var AbsolutelyIrreducibleRegular = absolutelyIrreducibleRegularThm{family.Add(registry.ProofEntry{
	Name: "AbsolutelyIrreducibleRegular",
	Key:  "prop_df206b4912789a4f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A). ∀t z:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"perfect_field(restrict_field(M, k))",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"polynomial_over(«P».zero, «P».carrier, F)",
			"polynomial_monic(«P».zero, «P».one, F)",
			"polynomial_irreducible(polynomial_ring(restrict_ring(field_ring(M), algebraic_elements(M, k))), " +
				"    F)",
			"z ∈ M.carrier",
			"polynomial_eval(«f», z) = M.zero",
		},
		Conclusion: "minimal_polynomial(M, «rational», z) = «f» ∧ regular_function_field(M, k, «K»)",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			{Name: "rational", Text: "field_adjoin(M, k, {t})"},
			{Name: "rationalBar", Text: "field_adjoin(M, algebraic_elements(M, k), {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "K", Text: "field_adjoin(M, «rational», {z})"},
			// Body-only: «E» = k(t)(x) and «Ez» = E(z), x the element of K fixed
			// where k is shown algebraically closed in K.
			{Name: "E", Text: "field_adjoin(M, «rational», {x})"},
			{Name: "Ez", Text: "field_adjoin(M, «E», {z})"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		t, z *Expr[A],
		kField, perfect, tIn, transcendental, overP, monic, irreducible, zIn, root Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		closure := a.TermAs[Set[A]]("algebraic_elements(M, k)")
		rational := a.TermAs[Set[A]]("«rational»")
		rationalBar := a.TermAs[Set[A]]("«rationalBar»")
		polynomials := a.TermAs[Set[A]]("«polynomials»")
		K := a.TermAs[Set[A]]("«K»")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		single := a.TermAs[Set[A]]("{t}")
		tm, zm := a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](z, zIn)
		closed := a.Have(
			"the elements algebraic over k form a subfield k̄ containing k",
			"subfield(M, algebraic_elements(M, k)) ∧ k ⊆ algebraic_elements(M, k)",
			By(kField, algebraic_element.AlgebraicElementsSubfield.Read(M).At(k)))
		closureMembers := a.Have(
			"they lie in M and are algebraic over k",
			"algebraic_elements(M, k) ⊆ M.carrier ∧ "+
				"(∀y:A. y ∈ algebraic_elements(M, k) ⇒ algebraic_over(M, k, y))",
			BySets(algebraic_element.AlgebraicElementsDef))
		barTranscendental := a.Have(
			"t stays transcendental over k̄, algebraicity over k being transitive",
			"¬algebraic_over(M, algebraic_elements(M, k), t)",
			By(
				transcendental,
				tIn,
				kField,
				closureMembers,
				algebraic_element.AlgebraicOverTrans.Read(M).At(k, closure, tm)))
		rows := a.Conjuncts(
			GroupPremises(overP, monic, MonicRowsAtPoint.Read(M).At(k, F, tm)),
			"the rows of F read at t form a polynomial f over k[t]",
			"f is monic",
			"f has the degree of F")
		fOver, fMonic := rows[0], rows[1]
		// monic, stated over k[T], is Gauss's monic hypothesis over k̄[T]: the zero and
		// one of a polynomial ring over a subring do not depend on the subring.
		minimalBar := a.Have(
			"by Gauss's lemma, f is the minimal polynomial of z over k̄(t)",
			"minimal_polynomial(M, «rationalBar», z) = «f»",
			By(
				M,
				closed,
				tIn,
				barTranscendental,
				monic,
				irreducible,
				zIn,
				root,
				GaussMinimalPolynomial.At(ops, closure, F, t, z)))
		rings := a.Have(
			"k[t] is a subring inside the subfield k(t), which holds k and t",
			"subring(field_ring(M), «polynomials») ∧ "+
				"«polynomials» ⊆ «rational» ∧ "+
				"subfield(M, «rational») ∧ "+
				"k ⊆ «rational» ∧ "+
				"t ∈ «rational»",
			By(
				kField,
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm),
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		barField := a.Have(
			"k̄(t) is a subfield holding k̄ and t",
			"subfield(M, «rationalBar») ∧ algebraic_elements(M, k) ⊆ «rationalBar» ∧ t ∈ «rationalBar»",
			By(closed, algebraic_element.AdjoinElementSubfield.Read(M).At(closure, tm)))
		barHolds := a.Have(
			"k̄(t) holds k(t), holding k and t",
			"«rational» ⊆ «rationalBar»",
			By(
				barField,
				a.Have(
					"k̄(t) holds k and {t}",
					"k ⊆ «rationalBar» ∧ {t} ⊆ «rationalBar»",
					BySets(closed, barField)),
				algebraic_element.AdjoinLeast.Read(M).At(k, single, rationalBar)))
		fRational := a.Have(
			"f is a nonzero polynomial over k(t)",
			"polynomial_over(«rational», «f») ∧ «f» ≠ vec_zero",
			By(
				rings,
				fMonic,
				fOver,
				polynomial.PolynomialOverMono.At(zero, polynomials, rational, f),
				polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M))))
		between := a.Have(
			"f is the minimal polynomial of z over every field between k(t) and k̄(t)",
			Statement{
				Binders:    "∀E:set(A).",
				Hypotheses: []string{"subfield(M, E)", "«rational» ⊆ E", "E ⊆ «rationalBar»"},
				Conclusion: "minimal_polynomial(M, E, z) = «f»",
			},
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]("E")
				bounds := b.Conjuncts(
					b.Assume(),
					"E is a subfield",
					"E holds k(t)",
					"E lies in k̄(t)")
				eField, eHolds, eInBar := bounds[0], bounds[1], bounds[2]
				g := b.TermAs[Fun[Nat, A]]("minimal_polynomial(M, E, z)")
				fOverE := b.Have(
					"f is a nonzero polynomial over E",
					"polynomial_over(E, «f»)",
					By(fRational, eHolds, polynomial.PolynomialOverMono.At(zero, rational, E, f)))
				algebraicE := b.Have(
					"z is algebraic over E, a root of f",
					"algebraic_over(M, E, z)",
					By(fOverE, fRational, root, algebraic_element.AlgebraicOverDef.At(ops, E, z)))
				spec := b.Have(
					"the minimal polynomial g of z over E is monic over E and vanishes at z",
					"polynomial_over(E, minimal_polynomial(M, E, z)) ∧ "+
						"polynomial_monic(minimal_polynomial(M, E, z)) ∧ "+
						"polynomial_eval(minimal_polynomial(M, E, z), z) = M.zero",
					By(eField, zIn, algebraicE, algebraic_element.MinimalPolynomialSpec.Read(M).At(E, zm)))
				gBar := b.Have(
					"g is a nonzero polynomial over k̄(t)",
					"polynomial_over(«rationalBar», minimal_polynomial(M, E, z)) ∧ "+
						"minimal_polynomial(M, E, z) ≠ vec_zero",
					By(
						spec,
						eInBar,
						polynomial.PolynomialOverMono.At(zero, E, rationalBar, g),
						polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M))))
				upper := b.Have(
					"g has degree at most that of f",
					"polynomial_degree(minimal_polynomial(M, E, z)) ≤ polynomial_degree(«f»)",
					By(
						eField,
						zIn,
						fOverE,
						fRational,
						root,
						algebraic_element.MinimalPolynomialLeast.Read(M).At(E, zm, f)))
				lower := b.Have(
					"and at least that of f, the minimal polynomial over the larger k̄(t)",
					"polynomial_degree(«f») ≤ polynomial_degree(minimal_polynomial(M, E, z))",
					By(
						barField,
						zIn,
						minimalBar,
						gBar,
						spec,
						algebraic_element.MinimalPolynomialLeast.Read(M).At(rationalBar, zm, g)))
				b.Show(
					"f is monic over E, vanishes at z and has the degree of z over E",
					By(
						eField,
						zIn,
						fOverE,
						fMonic,
						root,
						upper,
						lower,
						algebraicE,
						nat_order.LessEqAntisym,
						algebraic_element.MinimalPolynomialOfDegree.Read(M).At(E, zm, f),
						algebraic_element.AdjoinDegree.Read(M).At(E, zm)))
			}))
		minimal := a.Have(
			"in particular f is the minimal polynomial of z over k(t)",
			"minimal_polynomial(M, «rational», z) = «f»",
			By(rings, barHolds, set_order.SubsetRefl.At(rational), between.At(rational)))
		algebraic := a.Have(
			"z is algebraic over k(t)",
			"algebraic_over(M, «rational», z)",
			By(fRational, root, algebraic_element.AlgebraicOverDef.At(ops, rational, z)))
		top := a.Have(
			"K is a subfield holding k(t) and z, of degree deg f over k(t)",
			"subfield(M, «K») ∧ "+
				"«rational» ⊆ «K» ∧ "+
				"z ∈ «K» ∧ "+
				"finite_extension(M, «rational», «K») ∧ "+
				"extension_degree(M, «rational», «K») = polynomial_degree(«f»)",
			By(
				rings,
				zIn,
				algebraic,
				minimal,
				algebraic_element.AdjoinElementSubfield.Read(M).At(rational, zm),
				algebraic_element.AdjoinDegree.Read(M).At(rational, zm)))
		positive := a.Have(
			"f has positive degree",
			"0 < polynomial_degree(«f»)",
			By(
				rings,
				zIn,
				algebraic,
				minimal,
				algebraic_element.MinimalPolynomialPositive.Read(M).At(rational, zm)))
		inK := a.Have(
			"K holds k and t, and lies in M",
			"k ⊆ «K» ∧ t ∈ «K» ∧ «K» ⊆ M.carrier",
			BySets(
				rings,
				top,
				a.Have(
					"K lies in M",
					"«K» ⊆ M.carrier",
					By(top, field.SubfieldSubset.At(ops, K)))))
		generated := a.Have(
			"K is generated over k by z and t",
			"∃E:set(A). finite(E) ∧ E ⊆ «K» ∧ field_adjoin(M, k, E) = «K»",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Set[A]]("{z, t}"))
				b.Show(
					"adjoining t and then z gives K",
					By(
						kField,
						tIn,
						zIn,
						top,
						inK,
						finite_set.FiniteInsert,
						finite_set.FiniteSing,
						set_order.InsertSubset,
						set_order.SingSubset,
						field.SubfieldSubset.At(ops, k),
						algebraic_element.AdjoinInsert.Read(M).At(k, single, zm)))
			}))
		parameter := a.Have(
			"t is transcendental over k, and K, finite over k(t), is algebraic over it",
			"∃s:A. "+
				"    s ∈ «K» ∧ "+
				"    ¬algebraic_over(M, k, s) ∧ "+
				"    (∀x:A. x ∈ «K» ⇒ algebraic_over(M, field_adjoin(M, k, {s}), x))",
			Derive(func(b *Argument) {
				b.Take(t)
				b.Show(
					"every element of a finite extension is algebraic",
					By(inK, transcendental, rings, top, algebraic_element.FiniteExtensionAlgebraic.Read(M)))
			}))
		exact := a.Have(
			"k is algebraically closed in K",
			"∀x:A. x ∈ «K» ∧ algebraic_over(M, k, x) ⇒ x ∈ k",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in K",
					"x is algebraic over k")
				xInK, xAlgebraic := given[0], given[1]
				xm := b.MemberOf[on.M](x, b.Have(
					"x lies in M",
					"x ∈ M.carrier",
					BySets(xInK, inK)))
				E := b.TermAs[Set[A]]("«E»")
				xBar := b.Have(
					"x lies in k̄",
					"x ∈ algebraic_elements(M, k)",
					BySets(xm, xAlgebraic, algebraic_element.AlgebraicElementsDef))
				eData := b.Have(
					"E = k(t)(x) lies between k(t) and K",
					"subfield(M, «E») ∧ «rational» ⊆ «E» ∧ x ∈ «E» ∧ «E» ⊆ «K»",
					By(rings, top, xInK, algebraic_element.AdjoinElementBetween.Read(M).At(rational, K, x)))
				eInBar := b.Have(
					"E lies in k̄(t), x lying in k̄",
					"«E» ⊆ «rationalBar»",
					By(
						barField,
						barHolds,
						b.Have(
							"k̄(t) holds x",
							"{x} ⊆ «rationalBar»",
							BySets(barField, xBar)),
						algebraic_element.AdjoinLeast.Read(M).At(rational, b.TermAs[Set[A]]("{x}"), rationalBar)))
				minimalE := b.Have(
					"so f is the minimal polynomial of z over E",
					"minimal_polynomial(M, «E», z) = «f»",
					By(eData, eInBar, between.At(E)))
				eZ := b.TermAs[Set[A]]("«Ez»")
				eZData := b.Have(
					"E(z) is a subfield holding E and z",
					"subfield(M, «Ez») ∧ «E» ⊆ «Ez» ∧ z ∈ «Ez»",
					By(eData, algebraic_element.AdjoinElementSubfield.Read(M).At(E, zm)))
				containments := b.Have(
					"E(z) holds k(t) and z, and K holds E and z",
					"«rational» ⊆ «Ez» ∧ {z} ⊆ «Ez» ∧ «E» ⊆ «K» ∧ {z} ⊆ «K»",
					BySets(eData, eZData, top))
				eTop := b.Have(
					"E(z) is K, each holding the generators of the other",
					"«Ez» = «K»",
					By(
						eZData,
						top,
						containments,
						set_order.SubsetAntisym.At(eZ, K),
						algebraic_element.AdjoinLeast.Read(M).At(E, b.TermAs[Set[A]]("{z}"), K),
						algebraic_element.AdjoinLeast.Read(M).At(rational, b.TermAs[Set[A]]("{z}"), eZ)))
				overE := b.Have(
					"K has degree deg f over E",
					"finite_extension(M, «E», «K») ∧ extension_degree(M, «E», «K») = polynomial_degree(«f»)",
					By(
						eData,
						zIn,
						algebraic,
						eTop,
						minimalE,
						algebraic_element.AlgebraicOverMono.Read(M).AsFact().At(rational, E, z),
						algebraic_element.AdjoinDegree.Read(M).At(E, zm)))
				lower := b.Have(
					"E is finite over k(t)",
					"finite_extension(M, «rational», «E»)",
					By(rings, eData, top, field_extension.TowerFinite.Read(M).At(rational, E, K)))
				e := b.TermAs[Nat]("extension_degree(M, «rational», «E»)")
				n := b.TermAs[Nat]("polynomial_degree(«f»)")
				tower := b.Have(
					"by the tower law, deg f = [E : k(t)]·deg f",
					"polynomial_degree(«f») = extension_degree(M, «rational», «E») * polynomial_degree(«f»)",
					By(rings, eData, top, lower, overE, field_extension.TowerLaw.Read(M).At(rational, E, K)))
				one := b.Have(
					"so [E : k(t)] = 1, f having positive degree",
					"extension_degree(M, «rational», «E») = 1",
					By(
						tower,
						positive,
						nat_arith.MulEqLCancel.At(n, e, b.TermAs[Nat]("1")),
						nat_arith.MulSym.At(e, n),
						nat_arith.MulOne.At(n),
						nat_order.LessThanIrrefl))
				same := b.Have(
					"so E is k(t), and x lies in k(t)",
					"x ∈ «rational»",
					By(rings, eData, lower, one, field_extension.DegreeOneIff.Read(M).At(rational, E)))
				b.Show(
					"an element of k(t) algebraic over k lies in k",
					By(M, kField, tIn, transcendental, same, xAlgebraic, RationalFunctionConstants.At(ops, k, t, x)))
			}))
		regular := a.Have(
			"so K is a regular function field over k",
			"regular_function_field(M, k, «K»)",
			By(kField, perfect, top, inK, generated, parameter, exact, function_field.RegularFunctionFieldDef))
		a.Show(
			"f is the minimal polynomial of z over k(t), and K is regular over k",
			By(minimal, regular))
	}),
})}
