// transcendence.go — a function field of transcendence degree one is algebraic over
// the rational functions of any of its transcendental elements.

package rational_function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraicExchange — the exchange property of algebraic dependence: when t
// is transcendental over k and algebraic over k(s), s is algebraic over k(t).
// A nonzero polynomial Q over k(s) vanishing at t can be taken over k[s],
// k(s) being the fraction field of k[s]. Q lifts to a polynomial q over k[T]
// of its degree (RowsLift): each coefficient Q(i) is the value at s of a row
// q(i) over k, the zero polynomial where Q has run out, and the
// coefficients q(i, j) make a polynomial in two variables that vanishes at
// (t, s). Evaluated in the other order it is the polynomial over k[t] whose
// j-th coefficient is the column Σᵢ q(i, j)·tⁱ, at s. That polynomial is not
// zero: a column vanishing at t is the zero polynomial, t being
// transcendental over k, and were every column zero so would be every q(i)
// and Q. So s is algebraic over k[t], and over k(t).
var AlgebraicExchange = algebraicExchangeThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicExchange",
	Key:  "prop_3e39040f354b0602",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀s t:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"s ∈ M.carrier",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"algebraic_over(M, field_adjoin(M, k, {s}), t)",
		},
		Conclusion: "algebraic_over(M, field_adjoin(M, k, {t}), s)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		s, t *Expr[A],
		subfieldK, sIn, tIn, transcendental, algebraic Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldOps := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		sm, tm := a.MemberOf[on.M](s, sIn), a.MemberOf[on.M](t, tIn)

		// A relation for t with coefficients in k[s].
		overPolynomials := a.Have(
			"t is algebraic over k[s], the ring whose fraction field is k(s)",
			"algebraic_over(M, polynomial_image(field_ring(M), k, s), t)",
			By(
				subfieldK,
				sIn,
				tIn,
				algebraic,
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, sm),
				algebraic_element.PolynomialImageRing.Read(M).At(k, sm),
				integral_element.RationalFunctionsFractionField.Read(M).At(k, sm),
				integral_element.AlgebraicOverFractionSubring.Read(M).At(
					a.TermAs[Set[A]]("field_adjoin(M, k, {s})"),
					a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, s)"),
					tm)))
		Q, relation := a.ObtainAs[Fun[Nat, A]](
			"a nonzero polynomial Q over k[s] vanishes at t",
			"∃Q:(num → A). "+
				"    polynomial_over(polynomial_image(field_ring(M), k, s), Q) ∧ "+
				"    Q ≠ vec_zero ∧ "+
				"    polynomial_eval(Q, t) = M.zero",
			By(overPolynomials, algebraic_element.AlgebraicOverDef),
			Named("Q"))
		QParts := a.Conjuncts(
			relation,
			"Q is a polynomial over k[s]",
			"Q is not zero",
			"Q vanishes at t")
		QOver, QNonzero, QRoot := QParts[0], QParts[1], QParts[2]

		// The coefficients of Q as polynomials q(i) over k evaluated at s.
		q, lift := a.UnpackAs[Fun2[Nat, Nat, A]](
			GroupPremises(subfieldK, QOver, RowsLift.Read(M).At(k, sm, Q)), "q")
		lifted := a.Conjuncts(
			lift,
			"Q lifts to a polynomial q over k[T]",
			"whose rows q(i) read Q(i) at s",
			"of the degree of Q")
		rowValues := lifted[1]
		noRow := a.TermAs[Fun[Nat, A]]("vec_zero")
		overK := a.TermAs[Set[Fun[Nat, A]]]("{c:(num → A) | polynomial_over(k, c)}")
		rows := a.Have(
			"each row q(i) is a polynomial over k",
			"∀i:num. polynomial_over(k, q(i))",
			By(lifted[0], polynomial.PolynomialOverDef.At(noRow, overK, q)))
		m, mDef := a.LetAs[Nat]("m", "suc(polynomial_degree(Q))")
		zeroRows := a.Have(
			"and q(i) is zero from m = deg Q + 1 on, q having the degree of Q",
			"∀i:num. m ≤ i ⇒ q(i) = vec_zero",
			By(mDef, lifted[0], lifted[2], polynomial.DegreeVec.At(noRow, overK, q), vec_space.VecDef))

		// The array q(i, j) vanishes outside i < m and j ≤ N.
		_, bounded := a.ObtainAs[Nat](
			"the finitely many degrees of q(i), i < m, are at most some N",
			"∃N:num. image(λi:num. polynomial_degree(q(i)), {i:num | i < m}) ⊆ 0 .. N",
			By(
				num_segment.FiniteIffBounded.At(
					a.TermAs[Set[Nat]]("image(λi:num. polynomial_degree(q(i)), {i:num | i < m})")),
				finite_set.FiniteImage.At(
					a.TermAs[Fun[Nat, Nat]]("λi:num. polynomial_degree(q(i))"), a.TermAs[Set[Nat]]("{i:num | i < m}")),
				num_segment.FiniteBelowStrict.At(m)),
			Named("N"))
		degreeBound := a.Have(
			"so every q(i) with i < m has degree at most N",
			"∀i:num. i < m ⇒ polynomial_degree(q(i)) ≤ N",
			BySets(bounded))
		pastColumn := a.Have(
			"every coefficient q(i, j) with j past N is zero",
			"∀i j:num. suc(N) ≤ j ⇒ q(i, j) = M.zero",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.FixAs[Nat]("j")
				past := b.Assume()
				b.Cases(b.TermAs[Bool]("i < m"))
				b.When(
					"below m, j lies past the degree of q(i), at most N",
					func(c *Argument, below Fact) {
						beyond := c.Have(
							"j lies past the degree of q(i)",
							"suc(polynomial_degree(q(i))) ≤ j",
							ByArith(degreeBound.At(i), below, past))
						c.Show(
							"where q(i) vanishes",
							By(
								beyond,
								rows.At(i),
								polynomial.DegreeVec.At(c.TermAs[A]("M.zero"), k, c.TermAs[Fun[Nat, A]]("q(i)")),
								vec_space.VecDef))
					})
				b.Otherwise(
					"from m on, q(i) is the zero polynomial",
					func(c *Argument, notBelow Fact) {
						c.Show(
							"so its coefficient at j is zero",
							By(notBelow, zeroRows.At(i), nat_order.NotLessThan.At(i, m), vec_space.VecZeroDef))
					})
			}))
		pastRow := a.Have(
			"and every coefficient q(i, j) with i from m on",
			"∀i j:num. m ≤ i ⇒ q(i, j) = M.zero",
			By(zeroRows, vec_space.VecZeroDef))
		inK := a.Have(
			"every coefficient q(i, j) lies in k",
			"∀i j:num. q(i, j) ∈ k",
			By(rows, polynomial.PolynomialOverDef))
		inM := a.Have(
			"and so in M",
			"∀i j:num. q(i, j) ∈ M.carrier",
			BySets(inK, subfieldK, field.SubfieldSubset.At(fieldOps, k)))

		// The two orders of evaluation at (t, s).
		exchanged := a.Have(
			"evaluating q at s and then at t is evaluating it at t and then at s",
			"polynomial_eval(λi:num. polynomial_eval(q(i), s), t) = "+
				"polynomial_eval(λj:num. polynomial_eval(λi:num. q(i, j), t), s)",
			By(
				inM,
				pastRow,
				pastColumn,
				polynomial_evaluation.EvalTwoVariables.Read(ring).At(m, a.TermAs[Nat]("suc(N)"), q, tm, sm)))
		vanishes := a.Have(
			"the first order gives Q at t, which is zero",
			"polynomial_eval(λj:num. polynomial_eval(λi:num. q(i, j), t), s) = M.zero",
			By(rowValues, QRoot, exchanged))

		// The columns of q evaluated at t: a polynomial over k[t].
		columnsVanish := a.Have(
			"each column of q vanishes from m on",
			"∀j:num. vec⟨m⟩(λi:num. q(i, j))",
			By(pastRow, vec_space.VecDef))
		columns := a.Have(
			"so each column is a polynomial over k",
			"∀j:num. polynomial_over(k, λi:num. q(i, j))",
			By(inK, columnsVanish, polynomial.PolynomialOverDef))
		columnValues := a.Have(
			"the value of each column at t lies in k[t]",
			"∀j:num. polynomial_eval(λi:num. q(i, j), t) ∈ polynomial_image(field_ring(M), k, t)",
			BySets(columns, algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
		zeroColumns := a.Have(
			"past N the columns are zero",
			"∀j:num. suc(N) ≤ j ⇒ (λi:num. q(i, j)) = vec_zero",
			By(pastColumn, vec_space.VecZeroDef))
		transposedVanishes := a.Have(
			"so the values of the columns vanish past N",
			"vec⟨suc(N)⟩(λj:num. polynomial_eval(λi:num. q(i, j), t))",
			Simp(Fwd(vec_space.VecDef)),
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				past := b.Assume()
				b.Show(
					"the zero polynomial vanishes at t",
					By(Normalized, zeroColumns.At(j), past, tIn, polynomial_evaluation.EvalVecZero.Read(ring)))
			}))
		transposed := a.Have(
			"and they are the coefficients of a polynomial over k[t]",
			"polynomial_over(polynomial_image(field_ring(M), k, t), "+
				"    λj:num. polynomial_eval(λi:num. q(i, j), t))",
			By(columnValues, transposedVanishes, polynomial.PolynomialOverDef))
		columnsTranscendental := a.Have(
			"a column vanishing at t is zero, t being transcendental over k",
			"∀j:num. polynomial_eval(λi:num. q(i, j), t) = M.zero ⇒ (λi:num. q(i, j)) = vec_zero",
			By(transcendental, columns, algebraic_element.AlgebraicOverDef))
		transposedNonzero := a.Have(
			"the values of the columns are not all zero",
			"(λj:num. polynomial_eval(λi:num. q(i, j), t)) ≠ vec_zero",
			Derive(func(b *Argument) {
				allVanish := b.SupposeNot()
				allZero := b.Have(
					"then every column, and every coefficient q(i, j), is zero",
					"∀i j:num. q(i, j) = M.zero",
					By(allVanish, columnsTranscendental, vec_space.VecZeroDef))
				zeroPolynomials := b.Have(
					"so every q(i) is the zero polynomial",
					"∀i:num. q(i) = vec_zero",
					By(allZero, vec_space.VecZeroDef))
				b.Show(
					"and every coefficient Q(i), the value of q(i) at s, is zero: but Q is not zero",
					By(
						QNonzero,
						rowValues,
						zeroPolynomials,
						sIn,
						vec_space.VecZeroDef,
						polynomial_evaluation.EvalVecZero.Read(ring)))
			}))
		overPolynomialsT := a.Have(
			"so s is algebraic over k[t]",
			"algebraic_over(M, polynomial_image(field_ring(M), k, t), s)",
			By(transposedNonzero, vanishes, transposed, algebraic_element.AlgebraicOverDef))
		a.Show(
			"and over k(t), which contains k[t]",
			By(
				overPolynomialsT,
				subfieldK,
				tIn,
				algebraic_element.AlgebraicOverMono.Read(M).At(
					a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)"),
					a.TermAs[Set[A]]("field_adjoin(M, k, {t})"),
					s),
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
	}),
})}

// AlgebraicOverAnyTranscendental — a regular function field K over k is
// algebraic over k(t) for every t in K transcendental over k, not only over
// the k(s) its definition provides. By the exchange of algebraic dependence s
// is algebraic over k(t), so k(t)(s) is finite over k(t) and all its elements
// are algebraic over k(t); an element x of K is algebraic over k(s), which lies
// in k(t)(s), and so over k(t).
var AlgebraicOverAnyTranscendental = algebraicOverAnyTranscendentalThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverAnyTranscendental",
	Key:  "prop_a295b1b194fa6cda",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀t x:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"t ∈ K",
			"¬algebraic_over(M, k, t)",
			"x ∈ K",
		},
		Conclusion: "algebraic_over(M, «rational», x)",
		Abbrev: Abbrev{
			{Name: "rational", Text: "field_adjoin(M, k, {t})"},
			{Name: "composite", Text: "field_adjoin(M, «rational», {s})"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K *Expr[Set[A]],
		t, x *Expr[A],
		regular, tInK, transcendental, xInK Fact,
	) {
		data := a.Conjuncts(
			a.Unfolded(regular, function_field.RegularFunctionFieldDef),
			"k is a subfield of M",
			"so is K",
			"k lies in K",
			"k is perfect",
			"K is finitely generated over k",
			"K is algebraic over k(s) for some s in K transcendental over k",
			"k is algebraically closed in K")
		subfieldk, subfieldK := data[0], data[1]
		s, parameter := a.UnpackAs[A](data[5], "s")
		sParts := a.Conjuncts(
			parameter,
			"s lies in K",
			"s is transcendental over k",
			"every element of K is algebraic over k(s)")
		sInK, overKs := sParts[0], sParts[2]
		KInM := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset))
		inM := a.Have(
			"t, s and x lie in M",
			"t ∈ M.carrier ∧ s ∈ M.carrier ∧ x ∈ M.carrier",
			BySets(tInK, sInK, xInK, KInM))
		points := a.Conjuncts(
			inM,
			"t lies in M",
			"s lies in M",
			"x lies in M")
		tm, sm := a.MemberOf[on.M](t, points[0]), a.MemberOf[on.M](s, points[1])
		sOverKt := a.Have(
			"t is algebraic over k(s), so s is algebraic over k(t)",
			"algebraic_over(M, «rational», s)",
			By(M, subfieldk, inM, transcendental, tInK, overKs.At(t), AlgebraicExchange.Read(M).At(k, sm, tm)))
		rationalT := a.Have(
			"k(t) is a subfield of M containing k",
			"subfield(M, «rational») ∧ k ⊆ «rational»",
			By(subfieldk, inM, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		rational := a.TermAs[Set[A]]("«rational»")
		composite := a.Have(
			"k(t)(s) is a subfield containing k(t) and s, finite over k(t) since s is algebraic over it",
			"subfield(M, «composite») ∧ "+
				"«rational» ⊆ «composite» ∧ "+
				"s ∈ «composite» ∧ "+
				"finite_extension(M, «rational», «composite»)",
			By(
				rationalT,
				inM,
				sOverKt,
				algebraic_element.AdjoinElementSubfield.Read(M).At(rational, sm),
				algebraic_element.AlgebraicIffFinite.Read(M).At(rational, sm)))
		inside := a.Have(
			"k(s) lies in k(t)(s), which contains k and s",
			"field_adjoin(M, k, {s}) ⊆ «composite»",
			BySets(
				rationalT,
				composite,
				algebraic_element.AdjoinLeast.Read(M).At(
					k,
					a.TermAs[Set[A]]("{s}"),
					a.TermAs[Set[A]]("«composite»"))))
		finiteAlgebraic := a.Have(
			"every element of the finite extension k(t)(s) of k(t) is algebraic over k(t)",
			"∀y:A. y ∈ «composite» ⇒ algebraic_over(M, «rational», y)",
			By(rationalT, composite, algebraic_element.FiniteExtensionAlgebraic.Read(M)))
		xOverComposite := a.Have(
			"x is algebraic over k(s), so over k(t)(s)",
			"algebraic_over(M, «composite», x)",
			By(overKs.At(x), xInK, inside, algebraic_element.AlgebraicOverMono.Read(M)))
		a.Show(
			"algebraic over the algebraic elements k(t)(s), x is algebraic over k(t)",
			By(
				rationalT,
				inM,
				composite,
				finiteAlgebraic,
				xOverComposite,
				algebraic_element.AlgebraicOverTrans.Read(M),
				field.SubfieldSubset))
	}),
})}
