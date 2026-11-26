// gauss.go — a polynomial F over k[T] in a second variable Z,
// F = Σ F(i)·Zⁱ, each row F(i) a polynomial in T over k, read at a
// transcendental t: the rows of a monic F read at t form a monic polynomial
// over k[t] (MonicRowsAtPoint); a polynomial over k[t] lifts back to k[T]
// (RowsLift); irreducibility over k[T] makes the read polynomial the minimal
// polynomial of each of its roots over k(t), Gauss's lemma
// (GaussMinimalPolynomial); and a nonzero derivative in Z reads as a nonzero
// derivative (RowsDerivativeNonzero).

package rational_function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MonicRowsAtPoint — a monic polynomial F over k[T], each row read at a point
// t, is a monic polynomial over k[t] of the degree of F: the leading row is the
// constant one, which reads as one, and the rows past it vanish.
var MonicRowsAtPoint = monicRowsAtPointThm{family.Add(registry.ProofEntry{
	Name: "MonicRowsAtPoint",
	Key:  "prop_41bf2010863e7def",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A). ∀t:A.",
		Hypotheses: []string{
			"t ∈ M.carrier",
			"polynomial_over(«P».zero, «P».carrier, F)",
			"polynomial_monic(«P».zero, «P».one, F)",
		},
		Conclusion: "polynomial_over(polynomial_image(field_ring(M), k, t), «f») ∧ " +
			"polynomial_monic(«f») ∧ " +
			"polynomial_degree(«f») = polynomial_degree(«P».zero, F)",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		t *Expr[A],
		tIn, rows, monic Fact,
	) {
		zero, one := a.TermAs[A]("M.zero"), a.TermAs[A]("M.one")
		rowZero, rowOne := a.TermAs[Fun[Nat, A]]("«P».zero"), a.TermAs[Fun[Nat, A]]("«P».one")
		rowRing := a.TermAs[Set[Fun[Nat, A]]]("«P».carrier")
		values := a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		n := a.TermAs[Nat]("polynomial_degree(«P».zero, F)")
		past := a.TermAs[Nat]("suc(polynomial_degree(«P».zero, F))")
		tm := a.MemberOf[on.M](t, tIn)
		ring := field.RingOn.Read(M)
		rowsOverK := a.Have(
			"each row of F is a polynomial over k",
			"∀i:num. polynomial_over(k, F(i))",
			By(rows, polynomial.PolynomialOverDef.At(rowZero, rowRing, F)))
		image := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. "+
				"    u ∈ polynomial_image(field_ring(M), k, t) ⇔ "+
				"    ∃c:(num → A). polynomial_over(k, c) ∧ u = polynomial_eval(c, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		inImage := a.Have(
			"so each row read at t lies in k[t]",
			"∀i:num. polynomial_eval(F(i), t) ∈ polynomial_image(field_ring(M), k, t)",
			By(image, rowsOverK))
		leading := a.Have(
			"the leading row is the constant one",
			"F(polynomial_degree(«P».zero, F)) = basis_vector(0)",
			By(monic, polynomial.PolynomialMonicDef.At(rowZero, rowOne, F)))
		rowsPast := a.Have(
			"and the rows past it vanish",
			"∀i:num. suc(polynomial_degree(«P».zero, F)) ≤ i ⇒ F(i) = vec_zero",
			By(
				rows,
				polynomial.DegreeVec.At(rowZero, rowRing, F),
				vec_space.VecDef.At(rowZero, a.VecAt[Fun[Nat, A]](past, "F"))))
		top := a.Have(
			"so the leading row reads as one at t",
			"polynomial_eval(F(polynomial_degree(«P».zero, F)), t) = M.one",
			By(
				leading,
				polynomial_evaluation.EvalBasisVector.Read(ring).At(a.TermAs[Nat]("0"), tm),
				comm_monoid.MonoidPowDef))
		valuesPast := a.Have(
			"and the rows past it read as zero",
			"∀i:num. suc(polynomial_degree(«P».zero, F)) ≤ i ⇒ polynomial_eval(F(i), t) = M.zero",
			By(rowsPast, polynomial_evaluation.EvalVecZero.Read(ring).At(tm)))
		bounded := a.Have(
			"so the coefficients of f vanish from suc(n) on",
			"vec⟨suc(polynomial_degree(«P».zero, F))⟩(«f»)",
			By(valuesPast, vec_space.VecDef.At(zero, a.VecAt[A](past, "«f»"))))
		over := a.Have(
			"f is a polynomial over k[t]",
			"polynomial_over(polynomial_image(field_ring(M), k, t), «f»)",
			By(inImage, bounded, polynomial.PolynomialOverDef.At(zero, values, f)))
		nonzero := a.Have(
			"so the coefficient of f at n is not zero",
			"polynomial_eval(F(polynomial_degree(«P».zero, F)), t) ≠ M.zero",
			By(top, field.OneNotZeroOn.Read(M)))
		degree := a.Have(
			"so f has the degree n of F",
			"polynomial_degree(«f») = polynomial_degree(«P».zero, F)",
			By(over, bounded, nonzero, polynomial.DegreeExact.At(zero, values, f, n)))
		a.Show(
			"with that coefficient one, f is monic",
			By(over, degree, top, polynomial.PolynomialMonicDef.At(zero, one, f)))
	}),
})}

// RowsLift — a polynomial p over k[t] is read at t from a polynomial Q over
// k[T] of the same degree: each coefficient p(i) is the value at t of a
// polynomial over k, chosen to be zero where p(i) is zero, so Q and p vanish
// from the same index on.
var RowsLift = rowsLiftThm{family.Add(registry.ProofEntry{
	Name: "RowsLift",
	Key:  "prop_e43129da5ea9f65d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"polynomial_over(polynomial_image(field_ring(M), k, t), p)",
		},
		Conclusion: "∃Q:(num → num → A). " +
			"    polynomial_over(«P».zero, «P».carrier, Q) ∧ " +
			"    (∀i:num. polynomial_eval(Q(i), t) = p(i)) ∧ " +
			"    polynomial_degree(«P».zero, Q) = polynomial_degree(p)",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t *Expr[A],
		p *Arrow[Nat, A],
		kField, tIn, pOver Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		noRow := a.TermAs[Fun[Nat, A]]("vec_zero")
		rowZero := a.TermAs[Fun[Nat, A]]("«P».zero")
		rowRing := a.TermAs[Set[Fun[Nat, A]]]("«P».carrier")
		values := a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)")
		tm := a.MemberOf[on.M](t, tIn)
		ring := field.RingOn.Read(M)
		image := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. "+
				"    u ∈ polynomial_image(field_ring(M), k, t) ⇔ "+
				"    ∃c:(num → A). polynomial_over(k, c) ∧ u = polynomial_eval(c, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		rows := a.Have(
			"each coefficient of p is the value at t of a "+
				"polynomial over k, the zero polynomial where it is zero",
			"∀i:num. ∃c:(num → A). "+
				"    polynomial_over(k, c) ∧ polynomial_eval(c, t) = p(i) ∧ (p(i) = M.zero ⇒ c = vec_zero)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Cases(b.TermAs[Bool]("p(i) = M.zero"))
				b.When(
					"a zero coefficient is the value of the zero polynomial",
					func(c *Argument, isZero Fact) {
						c.Take(noRow)
						c.Show(
							"which is over k and reads zero at t",
							By(
								isZero,
								kField,
								polynomial_evaluation.EvalVecZero.Read(ring).At(tm),
								polynomial.PolynomialOverDef.At(zero, k, noRow),
								vec_space.VecDef.At(zero, c.VecAt[A](c.TermAs[Nat]("0"), "vec_zero")),
								vec_space.VecZeroDef,
								field.SubfieldZero.At(ops, k)))
					})
				b.Otherwise(
					"any other coefficient lies in k[t]",
					func(c *Argument, nonzero Fact) {
						c.Show(
							"so it is the value at t of a polynomial over k",
							By(nonzero, image.At(p.Apply(i)), pOver, polynomial.PolynomialOverDef.At(zero, values, p)))
					})
			}))
		Q, lifted := a.ObtainAs[Fun[Nat, Fun[Nat, A]]](
			"choose such a polynomial at every index",
			"∃Q:(num → num → A). ∀i:num. "+
				"    polynomial_over(k, Q(i)) ∧ "+
				"    polynomial_eval(Q(i), t) = p(i) ∧ "+
				"    (p(i) = M.zero ⇒ Q(i) = vec_zero)",
			By(rows),
			Named("Q"))
		zeros := a.Have(
			"Q(i) is the zero polynomial exactly where p(i) is zero",
			"∀i:num. Q(i) = vec_zero ⇔ p(i) = M.zero",
			By(Normalized, lifted, polynomial_evaluation.EvalVecZero.Read(ring).At(tm)))
		support := a.Have(
			"so Q and p vanish from the same index on",
			"∀n:num. vec⟨n⟩(p) ⇔ vec⟨n⟩(«P».zero, Q)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"pointwise the two vanish together",
					Simp(Fwd(polynomial.PolynomialRingDef)),
					By(
						zeros,
						vec_space.VecDef.At(zero, b.VecAt[A](n, "p")),
						vec_space.VecDef.At(noRow, b.VecAt[Fun[Nat, A]](n, "Q"))))
			}))
		degreeP := a.TermAs[Nat]("suc(polynomial_degree(p))")
		over := a.Have(
			"Q is a polynomial over k[T]",
			"polynomial_over(«P».zero, «P».carrier, Q)",
			Simp(Fwd(polynomial.PolynomialRingDef)),
			By(
				support.At(degreeP),
				lifted,
				pOver,
				polynomial.DegreeVec.At(zero, values, p),
				polynomial.PolynomialOverDef.At(
					noRow, a.TermAs[Set[Fun[Nat, A]]]("{c:(num → A) | polynomial_over(k, c)}"), Q)))
		bounds := a.Have(
			"each degree bounds the other",
			"polynomial_degree(«P».zero, Q) ≤ polynomial_degree(p) ∧ "+
				"polynomial_degree(p) ≤ polynomial_degree(«P».zero, Q)",
			By(
				support.At(degreeP),
				support.At(a.TermAs[Nat]("suc(polynomial_degree(«P».zero, Q))")),
				pOver,
				over,
				polynomial.DegreeVec.At(zero, values, p),
				polynomial.DegreeVec.At(rowZero, rowRing, Q),
				polynomial.DegreeLeast.At(rowZero, Q, a.TermAs[Nat]("polynomial_degree(p)")),
				polynomial.DegreeLeast.At(zero, p, a.TermAs[Nat]("polynomial_degree(«P».zero, Q)"))))
		a.Take(Q)
		a.Show(
			"Q lifts p with the degree of p",
			By(lifted, bounds, over, nat_order.LessEqAntisym))
	}),
})}

// GaussMinimalPolynomial — Gauss's lemma, at the minimal polynomial: let F be
// monic over k[T] and irreducible there, t transcendental over k, and z a root
// of f, the rows of F read at t. Then f is the minimal polynomial g of z over
// k(t). A root of the monic f, z is integral over k[t], which is integrally
// closed in k(t), so g lies over k[t] and divides f there, f = g·h. Lifting g
// and h to k[T] factors F, since reading at t is a one-to-one ring map on
// k[T]; g has positive degree, so h is constant and f, of the degree of g, is g.
var GaussMinimalPolynomial = gaussMinimalPolynomialThm{family.Add(registry.ProofEntry{
	Name: "GaussMinimalPolynomial",
	Key:  "prop_16aa726acd28f16e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A). ∀t z:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"polynomial_monic(«P».zero, «P».one, F)",
			"polynomial_irreducible(«P», F)",
			"z ∈ M.carrier",
			"polynomial_eval(«f», z) = M.zero",
		},
		Conclusion: "minimal_polynomial(M, «rational», z) = «f»",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			{Name: "rational", Text: "field_adjoin(M, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "g", Text: "minimal_polynomial(M, «rational», z)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		t, z *Expr[A],
		kField, tIn, transcendental, monic, irreducible, zIn, root Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
		rowRing := a.TermAs[module_record.RingOps[Fun[Nat, A]]]("«P»")
		rowZero := a.TermAs[Fun[Nat, A]]("«P».zero")
		rowCarrier := a.TermAs[Set[Fun[Nat, A]]]("«P».carrier")
		noRow := a.TermAs[Fun[Nat, A]]("vec_zero")
		polynomialsOverK := a.TermAs[Set[Fun[Nat, A]]]("{c:(num → A) | polynomial_over(k, c)}")
		rational := a.TermAs[Set[A]]("«rational»")
		polynomials := a.TermAs[Set[A]]("«polynomials»")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		g := a.TermAs[Fun[Nat, A]]("«g»")
		reading := a.TermAs[Fun[Fun[Nat, A], A]]("λp:(num → A). polynomial_eval(p, t)")
		tm, zm := a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](z, zIn)
		irreducibility := a.Conjuncts(
			a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
			"F is a polynomial over k[T]",
			"of positive degree",
			"which factors only with a constant factor")
		overP, positiveF, noFactor := irreducibility[0], irreducibility[1], irreducibility[2]
		rows := a.Conjuncts(
			GroupPremises(overP, monic, MonicRowsAtPoint.Read(M).At(k, F, tm)),
			"the rows of F read at t form a polynomial f over k[t]",
			"f is monic",
			"f has the degree of F")
		fOver, fMonic, fDegree := rows[0], rows[1], rows[2]
		rings := a.Have(
			"k[t] is a subring inside the subfield k(t)",
			"subring(field_ring(M), «polynomials») ∧ «polynomials» ⊆ «rational» ∧ subfield(M, «rational»)",
			By(
				kField,
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm),
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		fRational := a.Have(
			"f is a nonzero polynomial over k(t)",
			"polynomial_over(«rational», «f») ∧ «f» ≠ vec_zero",
			By(
				rings,
				fMonic,
				fOver,
				polynomial.PolynomialOverMono.At(zero, polynomials, rational, f),
				polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M))))
		fPositive := a.Have(
			"f has positive degree",
			"0 < polynomial_degree(«f»)",
			By(positiveF, fDegree, polynomial.PolynomialRingDef))
		integral := a.Have(
			"z is algebraic over k(t), and integral over k[t] as a root of the monic f",
			"algebraic_over(M, «rational», z) ∧ integral_over(restrict_ring(field_ring(M), «polynomials»), z)",
			By(
				fPositive,
				root,
				fRational,
				fMonic,
				fOver,
				algebraic_element.AlgebraicOverDef.At(ops, rational, z),
				integral_element.IntegralOverDef.At(
					a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «polynomials»)"), z)))
		gOver := a.Have(
			"k[t] is integrally closed in k(t), so the minimal polynomial g of z over k(t) lies over k[t]",
			"polynomial_over(«polynomials», «g»)",
			By(
				tIn,
				zIn,
				kField,
				rings,
				integral,
				algebraic_closure.MinimalPolynomialOverClosed.Read(M).At(polynomials, rational, zm),
				principal_ideal_domain.PolynomialRingIntegrallyClosed.Read(M).At(k, tm)))
		h, division := a.ObtainAs[Fun[Nat, A]](
			"g divides f over k[t]",
			"∃h:(num → A). polynomial_over(«polynomials», h) ∧ «f» = polynomial_mul(«g», h)",
			By(
				root,
				zIn,
				rings,
				integral,
				gOver,
				fOver,
				algebraic_element.MinimalPolynomialDividesOver.Read(M).At(rational, polynomials, zm, f),
				polynomial_division.PolynomialDividesDef),
			Named("h"))
		quotient := a.Conjuncts(
			division,
			"the quotient h lies over k[t]",
			"f is g times h")
		hOver, factored := quotient[0], quotient[1]
		G, gLift := a.ObtainAs[Fun[Nat, Fun[Nat, A]]](
			"lift g to a polynomial G over k[T]",
			"∃G:(num → num → A). "+
				"    polynomial_over(«P».zero, «P».carrier, G) ∧ "+
				"    (∀i:num. polynomial_eval(G(i), t) = «g»(i)) ∧ "+
				"    polynomial_degree(«P».zero, G) = polynomial_degree(«g»)",
			By(M, kField, tIn, gOver, RowsLift.At(ops, k, t, g)),
			Named("G"))
		H, hLift := a.ObtainAs[Fun[Nat, Fun[Nat, A]]](
			"and h to a polynomial H over k[T]",
			"∃H:(num → num → A). "+
				"    polynomial_over(«P».zero, «P».carrier, H) ∧ "+
				"    (∀i:num. polynomial_eval(H(i), t) = h(i)) ∧ "+
				"    polynomial_degree(«P».zero, H) = polynomial_degree(h)",
			By(M, kField, tIn, hOver, RowsLift.At(ops, k, t, h)),
			Named("H"))
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(restrict_ring(field_ring(M), k), field_ring(M), λx:A. x)",
			By(
				kField,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
		evaluation := a.Have(
			"reading at t is a ring map from k[T] to M",
			"ring_homomorphism(«P», field_ring(M), λp:(num → A). polynomial_eval(p, t))",
			By(
				tIn,
				inclusion,
				polynomial_evaluation.TransportedEvaluationHomomorphism.At(
					scalars, fieldRing, a.TermAs[Fun[A, A]]("λx:A. x"), t)))
		scalarRing := a.Have(
			"k is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), k))",
			By(kField, field.SubfieldCommRing.Read(M).At(k)))
		rowsInP := a.Have(
			"the rows of G and H are polynomials over k",
			"∀n:num. G(n) ∈ «P».carrier ∧ H(n) ∈ «P».carrier",
			By(
				gLift,
				hLift,
				polynomial.PolynomialOverDef.At(rowZero, rowCarrier, G),
				polynomial.PolynomialOverDef.At(rowZero, rowCarrier, H)))
		transported := a.Have(
			"reading the product G·H at t multiplies the readings",
			"(λn:num. polynomial_eval(polynomial_mul(«P».add, «P».zero, «P».mul, G, H, n), t)) = "+
				"polynomial_mul(λi:num. polynomial_eval(G(i), t), λi:num. polynomial_eval(H(i), t))",
			By(
				rowsInP,
				evaluation,
				polynomial.PolynomialRingOn.Read(scalarRing),
				field.RingOn.Read(M),
				polynomial.ConvolutionRingMap.At(rowRing, fieldRing, reading, G, H)))
		readings := a.Have(
			"the readings of G and H are g and h",
			"(λi:num. polynomial_eval(G(i), t)) = «g» ∧ (λi:num. polynomial_eval(H(i), t)) = h",
			By(gLift, hLift))
		rowValues := a.Have(
			"so G·H and F read alike at t",
			"∀m:num. "+
				"    polynomial_eval(polynomial_mul(«P».add, «P».zero, «P».mul, G, H, m), t) = "+
				"    polynomial_eval(F(m), t)",
			By(transported, readings, factored))
		// The lifts with k[T]'s operations written out: rows over k, zero vec_zero(M.zero).
		gLiftOverK := a.Simplified(gLift, Fwd(polynomial.PolynomialRingDef))
		hLiftOverK := a.Simplified(hLift, Fwd(polynomial.PolynomialRingDef))
		product := a.Have(
			"reading at the transcendental t is one-to-one on k[T], so F is G times H",
			"F = polynomial_mul(vec_add, vec_zero, polynomial_mul, G, H)",
			Derive(func(b *Argument) {
				b.Do(Funext())
				m := b.FixAs[Nat]("m")
				rowProduct := b.TermAs[Fun[Nat, A]]("polynomial_mul(vec_add, vec_zero, polynomial_mul, G, H, m)")
				row := b.TermAs[Fun[Nat, A]]("F(m)")
				members := b.Have(
					"both rows are polynomials over k",
					"polynomial_mul(vec_add, vec_zero, polynomial_mul, G, H, m) ∈ "+
						"{c:(num → A) | polynomial_over(k, c)} ∧ "+
						"F(m) ∈ {c:(num → A) | polynomial_over(k, c)}",
					By(
						gLiftOverK,
						hLiftOverK,
						overP,
						polynomial.SeriesMulIn.Read(polynomial.PolynomialRingOn.Read(scalarRing)).AsFact().At(G, H, m),
						polynomial.PolynomialOverDef.At(noRow, polynomialsOverK, G),
						polynomial.PolynomialOverDef.At(noRow, polynomialsOverK, H),
						polynomial.PolynomialOverDef.At(noRow, polynomialsOverK, F)))
				b.Show(
					"they read alike at t",
					By(
						transcendental,
						tIn,
						kField,
						members,
						rowValues.At(m),
						polynomial.PolynomialRingDef,
						algebraic_element.EvalInjectiveTranscendental.Read(M).At(k, tm, rowProduct, row)))
			}))
		constantFactor := a.Have(
			"F being irreducible over k[T], G or H is constant",
			"polynomial_degree(vec_zero, G) = 0 ∨ polynomial_degree(vec_zero, H) = 0",
			By(noFactor.At(G, H), product, gLiftOverK, hLiftOverK))
		gPositive := a.Have(
			"g has positive degree",
			"0 < polynomial_degree(«g»)",
			By(zIn, rings, integral, algebraic_element.MinimalPolynomialPositive.Read(M).At(rational, zm)))
		hConstant := a.Have(
			"so G, of the degree of g, is not constant, and h, of the degree of H, is",
			"polynomial_degree(h) = 0",
			ByArith(gPositive, gLiftOverK, hLiftOverK, constantFactor))
		inM := a.Have(
			"g and h are polynomials over M",
			"polynomial_over(M.carrier, «g») ∧ polynomial_over(M.carrier, h)",
			By(
				rings,
				gOver,
				hOver,
				comm_ring.SubringSubset.At(fieldRing, polynomials),
				polynomial.PolynomialOverMono.At(zero, polynomials, a.TermAs[Set[A]]("M.carrier"), g),
				polynomial.PolynomialOverMono.At(zero, polynomials, a.TermAs[Set[A]]("M.carrier"), h)))
		sameDegree := a.Have(
			"f = g·h has degree at most that of g, and no less, g being minimal",
			"polynomial_degree(«f») = polynomial_degree(«g»)",
			ByArith(
				root,
				hConstant,
				zIn,
				rings,
				inM,
				fRational,
				factored,
				polynomial.DegreeMulLe.Read(field.RingOn.Read(M)).At(g, h),
				algebraic_element.MinimalPolynomialLeast.Read(M).At(rational, zm, f)))
		a.Show(
			"f is monic, vanishes at z and has the degree of z over k(t), so it is the minimal polynomial",
			By(
				root,
				sameDegree,
				zIn,
				rings,
				integral,
				fRational,
				fMonic,
				algebraic_element.MinimalPolynomialOfDegree.Read(M).At(rational, zm, f),
				algebraic_element.AdjoinDegree.Read(M).At(rational, zm)))
	}),
})}

// RowsDerivativeNonzero — a polynomial F over k[T] whose derivative in Z is
// not zero keeps a nonzero derivative read at a transcendental t: reading at t
// is a ring map on k[T], so it carries each coefficient (i+1)·F(i+1) of the
// derivative to (i+1)·f(i+1), and it is one-to-one there.
var RowsDerivativeNonzero = rowsDerivativeNonzeroThm{family.Add(registry.ProofEntry{
	Name: "RowsDerivativeNonzero",
	Key:  "prop_16216d97f42409fa",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"polynomial_over(«P».zero, «P».carrier, F)",
			"polynomial_derivative(«P».add, «P».zero, «P».mul, «P».one, F) ≠ (λi:num. «P».zero)",
		},
		Conclusion: "polynomial_derivative(«f») ≠ vec_zero",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			// «D» is the hypothesis's derivative of F in Z, k[T]'s operations written out.
			{Name: "D", Text: "polynomial_derivative(vec_add, vec_zero, polynomial_mul, basis_vector(0), F)"},
			{Name: "polynomials", Text: "{c:(num → A) | polynomial_over(k, c)}"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		t *Expr[A],
		kField, tIn, transcendental, rows, nonzero Fact,
	) {
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
		noRow := a.TermAs[Fun[Nat, A]]("vec_zero")
		polynomials := a.TermAs[Set[Fun[Nat, A]]]("«polynomials»")
		derivative := a.TermAs[Fun[Nat, Fun[Nat, A]]]("«D»")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		tm := a.MemberOf[on.M](t, tIn)
		ring := field.RingOn.Read(M)
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(restrict_ring(field_ring(M), k), field_ring(M), λx:A. x)",
			By(
				kField,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
		// Reading at t is a ring map from k[T] to M.
		evaluation := a.Simplified(
			GroupPremises(
				tIn,
				inclusion,
				polynomial_evaluation.TransportedEvaluationHomomorphism.At(scalars, fieldRing, identity, t)),
			Fwd(polynomial.PolynomialRingDef))
		scalarRing := a.Have(
			"k is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), k))",
			By(kField, field.SubfieldCommRing.Read(M).At(k)))
		rowRing := polynomial.PolynomialRingOn.Read(scalarRing)
		rowsOverK := a.Simplified(rows, Fwd(polynomial.PolynomialRingDef))
		derivativeOver := a.Have(
			"the derivative D of F is a polynomial over k[T]",
			"polynomial_over(vec_zero, «polynomials», «D»)",
			By(rows, polynomial.DerivativeOverCarrier.Read(rowRing), polynomial.PolynomialRingDef))
		transported := a.Have(
			"reading D at t gives the derivative of f",
			"(λj:num. polynomial_eval(«D»(j), t)) = polynomial_derivative(«f»)",
			Derive(func(b *Argument) {
				b.Do(Funext())
				b.FixAs[Nat]("j")
				next := b.TermAs[Nat]("suc(j)")
				one := b.TermAs[Fun[Nat, A]]("basis_vector(0)")
				numeral := b.TermAs[Fun[Nat, A]]("monoid_pow(vec_add, vec_zero, basis_vector(0), suc(j))")
				b.Show(
					"the ring map keeps the numeral suc(j) and the row F(suc(j))",
					Simp(Fwd(polynomial.PolynomialDerivativeDef)),
					By(
						Normalized,
						rowsOverK,
						evaluation,
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(numeral, b.TermAs[Fun[Nat, A]]("F(suc(j))")),
						ring_homomorphism.RingMapNumeral.Read(evaluation).At(next),
						comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(rowRing)).AsFact().At(one, next),
						comm_ring.OneIn.Read(rowRing),
						polynomial.PolynomialOverDef.At(noRow, polynomials, F)))
			}))
		derivativeNonzero := a.Simplified(nonzero, Fwd(polynomial.PolynomialRingDef))
		a.Show(
			"a zero derivative of f would read every coefficient of D as "+
				"zero, and reading at the transcendental t is one-to-one over k",
			Derive(func(b *Argument) {
				vanishing := b.SupposeNot()
				rowsVanish := b.Have(
					"every coefficient of D is then the zero polynomial",
					"∀j:num. «D»(j) = vec_zero",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("j")
						row := c.TermAs[Fun[Nat, A]]("«D»(j)")
						c.Show(
							"its reading at t is the coefficient of the derivative of f, zero",
							By(
								transcendental,
								tIn,
								kField,
								vanishing,
								transported,
								derivativeOver,
								polynomial.PolynomialOverDef.At(noRow, polynomials, derivative),
								polynomial.VecZeroOver.Read(scalarRing),
								polynomial_evaluation.EvalVecZero.Read(ring).At(tm),
								vec_space.VecZeroDef,
								algebraic_element.EvalInjectiveTranscendental.Read(M).At(k, tm, row, noRow)))
					}))
				b.Show(
					"so D would be zero",
					By(derivativeNonzero, rowsVanish))
			}))
	}),
})}
