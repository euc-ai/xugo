// algebraic_element.go — an element of the field L algebraic over a subfield
// K, its minimal polynomial, the subfield K(S) and the subring a set
// generates, the ring K[a] of polynomial values, evaluation at a as a ring
// homomorphism from the polynomials over K into K(a), those values as
// combinations of powers of a, and K(a) = K[a] with its power basis; at a
// transcendental element the one-to-one evaluation, the basis of K[a] by all
// the powers, the transcendence of its inverse and the infinitude of a
// subfield holding it; and the algebraic elements: those of a finite
// extension, the finite extension finitely many of them generate, the
// subfield they form, and the transitivity of algebraicity.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// AlgebraicOverDef — `algebraic_over(L, K, a)`: some nonzero polynomial
// over K vanishes at a.
var AlgebraicOverDef = algebraicOverDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraicOverDef",
	Key:   "prop_fa06f14c85259fe5",
	Const: "algebraic_over",
	Type:  "field_ops(A) → set(A) → A → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). ∀a:A. " +
			"    algebraic_over(L, K, a) ⇔ " +
			"    ∃p:(num → A). " +
			"        polynomial_over(K, p) ∧ ¬(p = vec_zero(L.zero)) ∧ polynomial_eval(p, a) = L.zero",
	},
})}

// AlgebraicElementsDef — `algebraic_elements(L, K)`: the points of L
// algebraic over K, the algebraic closure of K in L.
var AlgebraicElementsDef = algebraicElementsDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraicElementsDef",
	Key:   "prop_2cb5645ff460d75e",
	Const: "algebraic_elements",
	Type:  "field_ops(A) → set(A) → set(A)",
	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). " +
			"    algebraic_elements(L, K) = {x:A | x ∈ L.carrier ∧ algebraic_over(L, K, x)}",
	},
	Deps: []registry.EntryLike{AlgebraicOverDef},
})}

// MinimalPolynomialDef — `minimal_polynomial(L, K, a)`: a monic polynomial
// over K vanishing at a, of least degree among the nonzero polynomials
// over K vanishing at a, chosen. Where a is not algebraic over K it is a
// sequence nothing is said about.
var MinimalPolynomialDef = minimalPolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "MinimalPolynomialDef",
	Key:   "prop_8a89f6a4b1b4f5e8",
	Const: "minimal_polynomial",
	Type:  "field_ops(A) → set(A) → A → num → A",
	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). ∀a:A. " +
			"    minimal_polynomial(L, K, a) = " +
			"    εp:(num → A). " +
			"        polynomial_over(K, p) ∧ " +
			"        polynomial_monic(L.zero, L.one, p) ∧ " +
			"        polynomial_eval(p, a) = L.zero ∧ " +
			"        (∀q:(num → A). " +
			"            polynomial_over(K, q) ∧ ¬(q = vec_zero(L.zero)) ∧ polynomial_eval(q, a) = L.zero ⇒ " +
			"            polynomial_degree(L.zero, p) ≤ polynomial_degree(L.zero, q))",
	},
})}

// FieldAdjoinDef — `field_adjoin(L, K, S)`, written K(S) on paper: the
// meet of the subfields of the field L holding K and S, the least of
// them. The ambient field is an argument, as the subfield predicate's
// carrier is: K(S) depends on the field it is taken in.
var FieldAdjoinDef = fieldAdjoinDefThm{family.Define(registry.DefEntry{
	Name:  "FieldAdjoinDef",
	Key:   "prop_70df3ad155429eb3",
	Const: "field_adjoin",
	Type:  "field_ops(A) → set(A) → set(A) → set(A)",

	Equations: []string{
		"∀L:field_ops(A). ∀K S:set(A). " +
			"    field_adjoin(L, K, S) = ⋂{M:set(A) | subfield(L, M) ∧ K ⊆ M ∧ S ⊆ M}",
	},
})}

// GeneratedSubringDef — `generated_subring(R, S, E)`, written S[E] on paper:
// the meet of the subrings of R holding S and E, the least of them.
var GeneratedSubringDef = generatedSubringDefThm{family.Define(registry.DefEntry{
	Name:  "GeneratedSubringDef",
	Key:   "prop_22c8b63d2b2ec885",
	Const: "generated_subring",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S E:set(A). generated_subring(R, S, E) = ⋂{B:set(A) | subring(R, B) ∧ S ∪ E ⊆ B}",
	},
})}

// PolynomialImageDef — `polynomial_image(R, K, a)`, written K[a]: the values
// at a of the polynomials over K.
var PolynomialImageDef = polynomialImageDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialImageDef",
	Key:   "prop_cb5c87aae3986ebe",
	Const: "polynomial_image",
	Type:  "ring_ops(A) → set(A) → A → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀K:set(A). ∀a:A. " +
			"    polynomial_image(R, K, a) = {polynomial_eval(p, a) | p:(num → A) | polynomial_over(K, p)}",
	},
})}

// ---------------------------------------------------------------------------
// The minimal polynomial
// ---------------------------------------------------------------------------

// MinimalPolynomialSpec — the minimal polynomial of an element algebraic
// over a subfield K meets the specification it is chosen by. Among the
// nonzero polynomials over K vanishing at a, well-ordering gives one, p,
// of least degree. Scaled by the inverse of its leading coefficient c it
// is a monic polynomial m over the field K of p's degree, vanishing at a
// as m(a) = inv(c) * p(a), and so of least degree among them too. So m
// meets that specification, and the chosen one meets it too.
var MinimalPolynomialSpec = minimalPolynomialSpecThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialSpec",
	Key:  "prop_1d8c43b243b0eea1",
	Reading: "subfield(L, K) is load-bearing: in ℚ with K = ℤ and a = 1/2, the element is " +
		"a root of 2x - 1, but no monic polynomial with integer coefficients vanishes at 1/2.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "polynomial_over(K, minimal_polynomial(L, K, a)) ∧ " +
			"polynomial_monic(minimal_polynomial(L, K, a)) ∧ " +
			"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero ∧ " +
			"(∀q:(num → A). " +
			"    polynomial_over(K, q) ∧ ¬(q = vec_zero) ∧ polynomial_eval(q, a) = L.zero ⇒ " +
			"    polynomial_degree(minimal_polynomial(L, K, a)) ≤ polynomial_degree(q))",
		Abbrev: Abbrev{
			{Name: "leading", Text: "p(polynomial_degree(p))"},
			{Name: "monicMultiple", Text: "vec_scalar_mul(L.inv(«leading»), p)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]

			attained := arg.Have(
				"a nonzero polynomial over K vanishes at a, so some n is the degree of one",
				"∃n:num. ∃q:(num → A). "+
					"    polynomial_over(K, q) ∧ "+
					"    ¬(q = vec_zero) ∧ "+
					"    polynomial_eval(q, a) = L.zero ∧ "+
					"    polynomial_degree(q) = n",
				By(arg.Unfolded(algebraic, AlgebraicOverDef)))
			leastDegree := arg.Have(
				"by well-ordering some such n is least",
				"∃n:num. "+
					"    (∃q:(num → A). "+
					"        polynomial_over(K, q) ∧ "+
					"        ¬(q = vec_zero) ∧ "+
					"        polynomial_eval(q, a) = L.zero ∧ "+
					"        polynomial_degree(q) = n) ∧ "+
					"    (∀m:num. "+
					"        m < n ⇒ "+
					"        ¬∃q:(num → A). "+
					"            polynomial_over(K, q) ∧ "+
					"            ¬(q = vec_zero) ∧ "+
					"            polynomial_eval(q, a) = L.zero ∧ "+
					"            polynomial_degree(q) = m)",
				By(
					attained,
					nat_order.WellOrdering.At(arg.TermAs[Set[Nat]](
						"λn:num. ∃q:(num → A). "+
							"    polynomial_over(K, q) ∧ "+
							"    ¬(q = vec_zero) ∧ "+
							"    polynomial_eval(q, a) = L.zero ∧ "+
							"    polynomial_degree(q) = n"))))
			p, least := arg.ObtainAs[Fun[Nat, A]](
				"a nonzero polynomial p over K vanishing at a, of that least degree",
				"∃p:(num → A). "+
					"    polynomial_over(K, p) ∧ "+
					"    ¬(p = vec_zero) ∧ "+
					"    polynomial_eval(p, a) = L.zero ∧ "+
					"    (∀q:(num → A). "+
					"        polynomial_over(K, q) ∧ ¬(q = vec_zero) ∧ polynomial_eval(q, a) = L.zero ⇒ "+
					"        polynomial_degree(p) ≤ polynomial_degree(q))",
				By(leastDegree, nat_order.NotLessThan))
			pFacts := arg.Conjuncts(
				least,
				"p is a polynomial over K",
				"p is not zero",
				"p vanishes at a",
				"no nonzero polynomial over K vanishing at a has smaller degree")
			pOver, pNonzero, pRoot, pLeast := pFacts[0], pFacts[1], pFacts[2], pFacts[3]

			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			m := arg.TermAs[Fun[Nat, A]]("«monicMultiple»")
			multiple := arg.Conjuncts(
				arg.Have(
					"over the field K, m = inv(c) • p, c the leading "+
						"coefficient of p, is a monic polynomial over K of p's degree",
					"polynomial_over(K, «monicMultiple») ∧ "+
						"polynomial_monic(«monicMultiple») ∧ "+
						"polynomial_degree(«monicMultiple») = polynomial_degree(p)",
					By(pOver, pNonzero, polynomial.MonicMultiple.Read(fieldK).At(p))),
				"m is a polynomial over K",
				"m is monic",
				"m has p's degree")
			mOver, mMonic, mDegree := multiple[0], multiple[1], multiple[2]

			ring := field.RingOn.Read(L)
			pOverL := arg.Have(
				"K lying in L, p is a polynomial over L as well",
				"polynomial_over(L.carrier, p)",
				By(subK, field.SubfieldSubset, pOver, polynomial.PolynomialOverMono))
			c := arg.MemberOf[on.L](
				arg.TermAs[A]("«leading»"),
				polynomial.CoefficientIn.Read(pOverL).At(arg.TermAs[Nat]("polynomial_degree(p)")))
			cInverse := field.InvIn.Read(L).At(c)
			mRoot := arg.Have(
				"m vanishes at a: m(a) = inv(c) * p(a) = inv(c) * zero = zero",
				"polynomial_eval(«monicMultiple», a) = L.zero",
				By(
					pOverL,
					pRoot,
					polynomial_evaluation.EvalScalar.Read(ring).At(cInverse, arg.MemberOf[on.L](a, aInL), p),
					comm_ring.MulRightZeroOn.Read(ring).At(cInverse)))
			mLeast := arg.Have(
				"of p's degree, m too has the least degree among them",
				Statement{
					Binders: "∀q:(num → A).",
					Hypotheses: []string{
						"polynomial_over(K, q)",
						"¬(q = vec_zero)",
						"polynomial_eval(q, a) = L.zero",
					},
					Conclusion: "polynomial_degree(«monicMultiple») ≤ polynomial_degree(q)",
				},
				mDegree.Rw(),
				By(pLeast))

			specified := arg.Have(
				"some monic polynomial over K vanishing at a has the least degree among them: m",
				"∃μ:(num → A). "+
					"    polynomial_over(K, μ) ∧ "+
					"    polynomial_monic(μ) ∧ "+
					"    polynomial_eval(μ, a) = L.zero ∧ "+
					"    (∀q:(num → A). "+
					"        polynomial_over(K, q) ∧ ¬(q = vec_zero) ∧ polynomial_eval(q, a) = L.zero ⇒ "+
					"        polynomial_degree(μ) ≤ polynomial_degree(q))",
				Derive(func(b *Argument) {
					b.Take(m)
					b.Show(
						"m is such a polynomial",
						By(mOver, mMonic, mRoot, mLeast))
				}))
			arg.Show(
				"the minimal polynomial is the one that specification chooses, so it meets it",
				Simp(Fwd(MinimalPolynomialDef)),
				By(HilbertDenoted, specified))
		}),
})}

// MinimalPolynomialLeast — every nonzero polynomial over K vanishing at
// a has at least the minimal polynomial's degree: such a q makes a
// algebraic over K, so the minimal polynomial meets its specification,
// whose least-degree clause read at q is the statement.
var MinimalPolynomialLeast = minimalPolynomialLeastThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialLeast",
	Key:  "prop_ff23ee56e9667da2",
	Reading: "algebraic_over is not asked: q itself witnesses it. subfield(L, K) " +
		"is: in ℚ with K = ℤ, q = 2x - 1 vanishes at 1/2, but no monic polynomial over " +
		"ℤ does, so nothing bounds the degree of the sequence the definition chooses.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀q:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"polynomial_over(K, q)",
			"¬(q = vec_zero)",
			"polynomial_eval(q, a) = L.zero",
		},
		Conclusion: "polynomial_degree(minimal_polynomial(L, K, a)) ≤ polynomial_degree(q)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a *Expr[A],
			q *Expr[Fun[Nat, A]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"q is a polynomial over K",
				"q is not zero",
				"q vanishes at a")
			subK, aInL, qOver, qNonzero, qRoot := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]

			algebraic := arg.Have(
				"a nonzero polynomial over K vanishes at a, so a is algebraic over K",
				"algebraic_over(L, K, a)",
				Unfold(AlgebraicOverDef),
				Derive(func(b *Argument) {
					b.Take(q)
					b.Show(
						"q is such a polynomial",
						By(qOver, qNonzero, qRoot))
				}))
			arg.Show(
				"the minimal polynomial meets its specification, whose least-degree clause holds at q",
				By(
					subK,
					algebraic,
					qOver,
					qNonzero,
					qRoot,
					MinimalPolynomialSpec.Read(L).At(K, arg.MemberOf[on.L](a, aInL))))
		}),
})}

// MinimalPolynomialPositive — the minimal polynomial has positive
// degree: a monic polynomial of degree zero is the one polynomial, whose
// value is one everywhere, never zero.
var MinimalPolynomialPositive = minimalPolynomialPositiveThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialPositive",
	Key:  "prop_7c3e2fd025f4f331",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "0 < polynomial_degree(minimal_polynomial(L, K, a))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, algebraic := hyp[0], hyp[2]
			aM := arg.MemberOf[on.L](a, hyp[1])
			specified := arg.Have(
				"the minimal polynomial μ is a monic polynomial over K vanishing at a",
				"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ "+
					"polynomial_monic(minimal_polynomial(L, K, a)) ∧ "+
					"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
				By(subK, algebraic, MinimalPolynomialSpec.Read(L).At(K, aM)))
			spec := arg.Conjuncts(
				specified,
				"μ is a polynomial over K",
				"μ is monic",
				"μ vanishes at a")
			over, monic, root := spec[0], spec[1], spec[2]
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			μ := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")

			notPositive := arg.SupposeNot()
			isOne := arg.Have(
				"then μ, monic over K and of degree zero, is the one polynomial",
				"minimal_polynomial(L, K, a) = basis_vector(0)",
				By(
					over,
					monic,
					notPositive,
					nat_order.PosIffNonzero.At(arg.TermAs[Nat]("polynomial_degree(minimal_polynomial(L, K, a))")),
					polynomial.MonicDegreeZero.Read(field.RingOn.Read(fieldK)).At(μ)))
			valueOne := arg.Have(
				"so the value of μ at a is a ^ 0 = one",
				"polynomial_eval(minimal_polynomial(L, K, a), a) = L.one",
				isOne.Rw(),
				By(
					Normalized,
					polynomial_evaluation.EvalBasisVector.Read(field.RingOn.Read(L)).At(arg.TermAs[Nat]("0"), aM),
					comm_monoid.MonoidPowDef))
			arg.Show(
				"but μ vanishes at a, so one = zero, which in a field it is not",
				By(valueOne, root, field.OneNotZeroOn.Read(L)))
		}),
})}

// LeastMonicRelationDivides — a monic polynomial g over a subring S of a
// commutative ring R, vanishing at z with the least degree among the nonzero
// polynomials over S that vanish there, divides over S every polynomial over
// S vanishing at z. Dividing p by the monic g over S leaves p = g q + u with
// u vanishing from the degree of g on; at the root z of g, p takes the value
// of u (polynomial_evaluation.DivisionValueAtRoot), so u vanishes at z, and a
// nonzero u would have degree at least g's. So u is zero and p = g q.
var LeastMonicRelationDivides = leastMonicRelationDividesThm{family.Add(registry.ProofEntry{
	Name: "LeastMonicRelationDivides",
	Key:  "prop_f672ac96dc15fbcb",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀g:(num → A). ∀z:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"z ∈ R.carrier",
			"polynomial_over(S, g)",
			"polynomial_monic(g)",
			"polynomial_eval(g, z) = R.zero",
			"∀q:(num → A). " +
				"    polynomial_over(S, q) ∧ q ≠ vec_zero(R.zero) ∧ polynomial_eval(q, z) = R.zero ⇒ " +
				"    polynomial_degree(g) ≤ polynomial_degree(q)",
			"polynomial_over(S, p)",
			"polynomial_eval(p, z) = R.zero",
		},
		Conclusion: "polynomial_divides(restrict_ring(R, S), g, p)",
		Abbrev: Abbrev{
			{Name: "polynomialsOverS", Text: "{h:(num → A) | polynomial_over(S, h)}"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		g *Arrow[Nat, A],
		z *Expr[A],
		p *Arrow[Nat, A],
		sub, zIn, gOver, gMonic, gRoot, gLeast, pOver, pRoot Fact,
	) {
		scalarRing := a.Have(
			"S is a ring under the operations of R",
			"comm_ring_on(restrict_ring(R, S))",
			By(sub, comm_ring.SubringRingOn.Read(R).AsFact().At(S)))
		q, u, division := a.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
			"divide p by the monic g over S",
			"∃q u:(num → A). «division»(S, p, g, q, u)",
			By(
				scalarRing,
				gOver,
				gMonic,
				pOver,
				polynomial_division.MonicDivisionExists.At(a.TermAs[RingOps[A]]("restrict_ring(R, S)"), p, g)))
		parts := a.Conjuncts(
			division,
			"q is over S",
			"u is over S",
			"u vanishes from the degree of g on",
			"p is g q + u")
		qOver, uOver, short, divided := parts[0], parts[1], parts[2], parts[3]
		overR := a.Have(
			"g, q and u are polynomials over R as well, S lying in R",
			"polynomial_over(R.carrier, g) ∧ polynomial_over(R.carrier, q) ∧ polynomial_over(R.carrier, u)",
			By(
				sub,
				comm_ring.SubringSubset.At(a.TermAs[RingOps[A]]("R"), S),
				gOver,
				qOver,
				uOver,
				polynomial.PolynomialOverMono))
		uRoot := a.Have(
			"so u vanishes at z: at this root of g, p takes the value of u, and p vanishes there",
			"polynomial_eval(u, z) = R.zero",
			By(
				overR,
				divided,
				gRoot,
				pRoot,
				polynomial_evaluation.DivisionValueAtRoot.Read(R).At(p, g, q, u, a.MemberOf[on.R](z, zIn))))
		uZero := a.Have(
			"so u is zero, its degree being below that of g",
			"u = vec_zero",
			Derive(func(b *Argument) {
				nonzero := b.SupposeNot()
				least := b.Have(
					"g has degree at most that of u",
					"polynomial_degree(g) ≤ polynomial_degree(u)",
					By(uOver, nonzero, uRoot, gLeast.At(u)))
				b.Show(
					"but u lies below the degree of g",
					ByArith(
						least,
						short,
						nonzero,
						polynomial.DegreeBelow.At(b.TermAs[A]("R.zero"), proof.InhabitFrom(u, short))))
			}))
		members := a.Have(
			"p, g, q and u lie in the ring of polynomials over S, where its arithmetic reads them",
			"p ∈ «polynomialsOverS» ∧ g ∈ «polynomialsOverS» ∧ q ∈ «polynomialsOverS» ∧ u ∈ «polynomialsOverS»",
			BySets(pOver, gOver, qOver, uOver))
		multiple := a.Have(
			"so p is g times q in that ring",
			"p = polynomial_mul(g, q)",
			ByArith(polynomial.PolynomialRingOn.Read(scalarRing), members, divided, uZero))
		a.Show(
			"g divides p over S, the quotient q",
			Simp(Fwd(polynomial_division.PolynomialDividesDef)),
			Derive(func(b *Argument) {
				b.Take(q)
				b.Show(
					"q is a polynomial over S and p is g times q",
					By(qOver, multiple))
			}))
	}),
})}

// MinimalPolynomialDivides — the minimal polynomial divides, over K,
// every polynomial over K vanishing at a: K is a subring of L lying in
// itself and holds the coefficients of the minimal polynomial, so
// MinimalPolynomialDividesOver applies with K as both the field and the
// subring.
var MinimalPolynomialDivides = minimalPolynomialDividesThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialDivides",
	Key:  "prop_7b522c9b0c9e5240",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀q:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"polynomial_over(K, q)",
			"polynomial_eval(q, a) = L.zero",
		},
		Conclusion: "polynomial_divides(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a), q)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a *Expr[A],
			q *Expr[Fun[Nat, A]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K",
				"q is a polynomial over K",
				"q vanishes at a")
			subK, aInL, algebraic, qOver, qRoot := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			aM := arg.MemberOf[on.L](a, aInL)
			arg.Show(
				"K is a subring of L lying in itself that holds the coefficients of "+
					"the minimal polynomial, so the minimal polynomial divides q over K",
				By(
					subK,
					algebraic,
					qOver,
					qRoot,
					field.SubfieldSubring.Read(L).At(K),
					set_order.SubsetRefl.At(K),
					MinimalPolynomialSpec.Read(L).At(K, aM),
					MinimalPolynomialDividesOver.Read(L).At(K, K, aM, q)))
		}),
})}

// MinimalPolynomialDividesOver — the minimal polynomial of z over a field E, when its
// coefficients lie in a subring S of E, divides over S every polynomial over S vanishing
// at z: it is monic and vanishes at z, and no nonzero polynomial over S vanishing at z
// has smaller degree, such a polynomial being one over E (MinimalPolynomialLeast); so
// LeastMonicRelationDivides applies.
var MinimalPolynomialDividesOver = minimalPolynomialDividesOverThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialDividesOver",
	Key:  "prop_3438ccb6626bf857",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀E S:set(A). ∀z:A. ∀g:(num → A).",
		Hypotheses: []string{
			"subfield(L, E)",
			"subring(field_ring(L), S)",
			"S ⊆ E",
			"z ∈ L.carrier",
			"algebraic_over(L, E, z)",
			"polynomial_over(S, minimal_polynomial(L, E, z))",
			"polynomial_over(S, g)",
			"«atZ»(g) = L.zero",
		},
		Conclusion: "polynomial_divides(«sRing», minimal_polynomial(L, E, z), g)",
		Abbrev: Abbrev{
			{Name: "sRing", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "atZ", Text: "λp:(num → A). polynomial_eval(p, z)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		E, S *Expr[Set[A]],
		z *Expr[A],
		g *Arrow[Nat, A],
		fieldE, sub, inside, zIn, algebraic, minimalOver, gOver, root Fact,
	) {
		zL := a.MemberOf[on.L](z, zIn)
		spec := a.Conjuncts(
			a.Have(
				"the minimal polynomial is monic and vanishes at z",
				"polynomial_monic(minimal_polynomial(L, E, z)) ∧ «atZ»(minimal_polynomial(L, E, z)) = L.zero",
				By(fieldE, zIn, algebraic, MinimalPolynomialSpec.Read(L).At(E, zL))),
			"it is monic",
			"it vanishes at z")
		least := a.Have(
			"no nonzero polynomial over S vanishing at z has smaller degree, S lying in E",
			Statement{
				Binders:    "∀q:(num → A).",
				Hypotheses: []string{"polynomial_over(S, q)", "q ≠ vec_zero", "«atZ»(q) = L.zero"},
				Conclusion: "polynomial_degree(minimal_polynomial(L, E, z)) ≤ polynomial_degree(q)",
			},
			Derive(func(b *Argument) {
				q := b.FixAs[Fun[Nat, A]]("q")
				given := b.Assume()
				b.Show(
					"such a polynomial is one over E, where the minimal polynomial has the least degree",
					By(
						fieldE,
						inside,
						given,
						polynomial.PolynomialOverMono,
						MinimalPolynomialLeast.Read(L).At(E, zL, q)))
			}))
		a.Show(
			"a monic relation of least degree over S divides every "+
				"relation over S, so the minimal polynomial divides g over S",
			By(
				sub,
				minimalOver,
				spec[0],
				spec[1],
				least,
				gOver,
				root,
				LeastMonicRelationDivides.Read(field.RingOn.Read(L)).At(
					S, a.TermAs[Fun[Nat, A]]("minimal_polynomial(L, E, z)"), zL, g)))
	}),
})}

// MinimalPolynomialIrreducible — the minimal polynomial is irreducible
// over K. It is a polynomial over K of positive degree. Let μ = q r be a
// factorization over K; a zero factor has degree zero, so let both
// factors be nonzero. Over L, a domain, their degrees add to μ's, and
// q(a) r(a) = μ(a) = zero, so one of them vanishes at a. That factor has
// at least μ's degree, μ having the least degree among the nonzero
// polynomials over K vanishing at a, and the other is left degree zero.
var MinimalPolynomialIrreducible = minimalPolynomialIrreducibleThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialIrreducible",
	Key:  "prop_2b7d62575087f381",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "polynomial_irreducible(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]
			aM := arg.MemberOf[on.L](a, aInL)
			ring := field.RingOn.Read(L)
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))

			specification := MinimalPolynomialSpec.Read(L).At(K, aM)
			over := arg.Have(
				"μ is a polynomial over K",
				"polynomial_over(K, minimal_polynomial(L, K, a))",
				By(subK, algebraic, specification))
			root := arg.Have(
				"vanishing at a",
				"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
				By(subK, algebraic, specification))
			positive := arg.Have(
				"of positive degree",
				"0 < polynomial_degree(minimal_polynomial(L, K, a))",
				By(subK, algebraic, MinimalPolynomialPositive.Read(L).At(K, aM)))

			factorizations := arg.Have(
				"a factorization μ = q r over K has a factor of degree zero",
				Statement{
					Binders: "∀q r:(num → A).",
					Hypotheses: []string{
						"polynomial_over(K, q)",
						"polynomial_over(K, r)",
						"minimal_polynomial(L, K, a) = polynomial_mul(q, r)",
					},
					Conclusion: "polynomial_degree(q) = 0 ∨ polynomial_degree(r) = 0",
				},
				Derive(func(b *Argument) {
					q, r := b.FixAs[Fun[Nat, A]](), b.FixAs[Fun[Nat, A]]()
					factors := b.Conjuncts(
						b.Assume(),
						"q is a polynomial over K",
						"so is r",
						"and μ = q r")
					qOver, rOver, factorization := factors[0], factors[1], factors[2]
					qNonzero := b.Unless(
						b.Term("q = vec_zero"),
						"a zero factor q has degree zero",
						Given(func(c *Argument, qZero Fact) {
							c.Show(
								"deg q = deg vec_zero = 0",
								qZero.Rw(),
								Cite(polynomial.DegreeVecZero))
						}))
					rNonzero := b.Unless(
						b.Term("r = vec_zero"),
						"a zero factor r has degree zero",
						Given(func(c *Argument, rZero Fact) {
							c.Show(
								"deg r = deg vec_zero = 0",
								rZero.Rw(),
								Cite(polynomial.DegreeVecZero))
						}))

					qOverL := b.Have(
						"q is a polynomial over L",
						"polynomial_over(L.carrier, q)",
						By(kInL, qOver, polynomial.PolynomialOverMono))
					rOverL := b.Have(
						"so is r",
						"polynomial_over(L.carrier, r)",
						By(kInL, rOver, polynomial.PolynomialOverMono))
					degrees := b.Have(
						"over L, a domain, the degrees of the nonzero factors add to μ's",
						"polynomial_degree(minimal_polynomial(L, K, a)) = polynomial_degree(q) + polynomial_degree(r)",
						factorization.Rw(),
						By(
							qNonzero,
							rNonzero,
							qOverL,
							rOverL,
							polynomial.DegreeMul.Read(integral_domain.FieldIntegralDomain.Read(L)).At(q, r)))
					vanishes := b.Have(
						"q(a) r(a) = (q r)(a) = μ(a) = zero",
						"polynomial_eval(q, a) * polynomial_eval(r, a) = L.zero",
						CalcEq(
							Leg(
								b.Term("polynomial_eval(polynomial_mul(q, r), a)"),
								"evaluation at a multiplies",
								By(qOverL, rOverL, polynomial_evaluation.EvalMul.Read(ring).At(q, r, aM))),
							FinalLeg(
								"which is the value of μ = q r at a",
								factorization.RwRev(),
								By(root)),
						))
					oneVanishes := b.Have(
						"so q or r vanishes at a, L having no zero divisors",
						"polynomial_eval(q, a) = L.zero ∨ polynomial_eval(r, a) = L.zero",
						By(
							vanishes,
							aInL,
							qOverL,
							rOverL,
							field.MulEqZeroOn.Read(L),
							polynomial_evaluation.EvalIn.Read(ring)))

					b.Show(
						"the factor vanishing at a has at least μ's degree, which leaves the other degree zero",
						oneVanishes.SplitDisj(
							LeftHolds(
								"q vanishes at a",
								Given(func(c *Argument, qRoot Fact) {
									least := c.Have(
										"so deg μ ≤ deg q",
										"polynomial_degree(minimal_polynomial(L, K, a)) ≤ polynomial_degree(q)",
										By(subK, qOver, qNonzero, qRoot, MinimalPolynomialLeast.Read(L).At(K, aM, q)))
									c.Show(
										"and deg r = 0",
										ByArith(least, degrees))
								})),
							RightHolds(
								"r vanishes at a",
								Given(func(c *Argument, rRoot Fact) {
									least := c.Have(
										"so deg μ ≤ deg r",
										"polynomial_degree(minimal_polynomial(L, K, a)) ≤ polynomial_degree(r)",
										By(subK, rOver, rNonzero, rRoot, MinimalPolynomialLeast.Read(L).At(K, aM, r)))
									c.Show(
										"and deg q = 0",
										ByArith(least, degrees))
								})),
						))
				}))
			arg.Show(
				"over K, of positive degree, with a factor of degree zero in every factorization, μ is irreducible",
				By(over, positive, factorizations, polynomial_division.PolynomialIrreducibleDef))
		}),
})}

// MinimalPolynomialUnique — the minimal polynomial is the one monic
// irreducible polynomial over K vanishing at a: it divides any such p,
// whose irreducibility forces the quotient to have degree zero. Comparing
// leading coefficients makes that quotient monic, hence the constant one.
var MinimalPolynomialUnique = minimalPolynomialUniqueThm{family.Add(registry.ProofEntry{
	Name:    "MinimalPolynomialUnique",
	Key:     "prop_16a832b2e2b8af53",
	Reading: "Irreducibility is load-bearing: μ times x - b is monic, vanishes at a and is not μ.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"polynomial_irreducible(restrict_ring(field_ring(L), K), p)",
			"polynomial_monic(p)",
			"polynomial_eval(p, a) = L.zero",
		},
		Conclusion: "p = minimal_polynomial(L, K, a)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a *Expr[A],
			p *Expr[Fun[Nat, A]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"p is irreducible over K",
				"p is monic",
				"p vanishes at a")
			subK, aInL, irreducible, pMonic, pRoot := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			aM := arg.MemberOf[on.L](a, aInL)
			μ := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
			scalars := arg.TermAs[RingOps[A]]("«scalars»")
			zero, one := arg.TermAs[A]("L.zero"), arg.TermAs[A]("L.one")
			pOver := arg.Have(
				"irreducibility makes p a polynomial over K",
				"polynomial_over(K, p)",
				By(irreducible, polynomial_division.PolynomialIrreducibleDef.At(scalars, p)))
			pNonzero := arg.Have(
				"p is nonzero, being monic",
				"p ≠ vec_zero",
				By(pMonic, polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(L)).At(p)))
			algebraic := arg.Have(
				"the nonzero polynomial p vanishes at a, so a is algebraic over K",
				"algebraic_over(L, K, a)",
				Unfold(AlgebraicOverDef),
				Derive(func(b *Argument) {
					b.Take(p)
					b.Show(
						"p witnesses algebraicity",
						By(pOver, pNonzero, pRoot))
				}))
			minimal := arg.Have(
				"μ is a monic polynomial over K",
				"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ polynomial_monic(minimal_polynomial(L, K, a))",
				By(subK, algebraic, MinimalPolynomialSpec.Read(L).At(K, aM)))
			parts := arg.Conjuncts(
				minimal,
				"μ has coefficients in K",
				"μ is monic")
			μOver, μMonic := parts[0], parts[1]
			positive := arg.Have(
				"μ has positive degree",
				"0 < polynomial_degree(minimal_polynomial(L, K, a))",
				By(subK, algebraic, MinimalPolynomialPositive.Read(L).At(K, aM)))
			s, factored := arg.ObtainAs[Fun[Nat, A]](
				"μ divides p over K, with quotient s",
				"∃s:(num → A). polynomial_over(K, s) ∧ p = polynomial_mul(minimal_polynomial(L, K, a), s)",
				By(
					subK,
					algebraic,
					pOver,
					pRoot,
					MinimalPolynomialDivides.Read(L).At(K, aM, p),
					polynomial_division.PolynomialDividesDef.At(scalars, μ, p)),
				Named("s"))
			factors := arg.Conjuncts(
				factored,
				"s is a polynomial over K",
				"p = μ s")
			sOver, factorization := factors[0], factors[1]
			degreeAlternative := arg.Have(
				"irreducibility forces one factor to have degree zero",
				"polynomial_degree(minimal_polynomial(L, K, a)) = 0 ∨ polynomial_degree(s) = 0",
				By(
					irreducible,
					μOver,
					sOver,
					factorization,
					polynomial_division.PolynomialIrreducibleDef.At(scalars, p)))
			constant := arg.Have(
				"μ has positive degree, so s has degree zero",
				"polynomial_degree(s) = 0",
				ByArith(positive, degreeAlternative))

			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			ringK := field.RingOn.Read(fieldK)
			polynomialRing := polynomial.PolynomialRingOn.Read(ringK)
			sNonzero := arg.Have(
				"s is nonzero, since μ s = p is nonzero",
				"s ≠ vec_zero",
				By(
					Normalized,
					pNonzero,
					factorization,
					μOver,
					comm_ring.MulRightZeroOn.Read(polynomialRing).AsFact().At(μ)))
			degrees := arg.Have(
				"μ being monic and s nonzero, the degrees of the two factors add to that of p",
				"polynomial_degree(p) = polynomial_degree(minimal_polynomial(L, K, a)) + polynomial_degree(s)",
				By(
					μMonic,
					polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(L)).At(μ),
					sNonzero,
					μOver,
					sOver,
					factorization,
					polynomial.DegreeMul.Read(integral_domain.FieldIntegralDomain.Read(fieldK)).At(μ, s)))
			leading := arg.Have(
				"the leading coefficient of p is the product of the factors' leading coefficients",
				"p(polynomial_degree(minimal_polynomial(L, K, a)) + polynomial_degree(s)) = "+
					"L.mul(minimal_polynomial(L, K, a, polynomial_degree(minimal_polynomial(L, K, a))), "+
					"    s(polynomial_degree(s)))",
				By(μOver, sOver, factorization, polynomial.LeadingCoefficientMul.Read(ringK).At(μ, s)))
			sLead := arg.TermAs[A]("s(polynomial_degree(s))")
			sLeadMember := arg.MemberOf[on.Any](
				sLead, polynomial.CoefficientIn.Read(sOver).At(arg.TermAs[Nat]("polynomial_degree(s)")))
			sMonic := arg.Have(
				"p and μ are monic, so their leading coefficient equation makes s monic",
				"polynomial_monic(s)",
				By(
					leading,
					degrees,
					pMonic,
					μMonic,
					polynomial.PolynomialMonicDef.At(zero, one, p),
					polynomial.PolynomialMonicDef.At(zero, one, μ),
					polynomial.PolynomialMonicDef.At(zero, one, s),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ringK)).At(sLeadMember)))
			unit := arg.Have(
				"a monic polynomial of degree zero is the constant one",
				"s = basis_vector(0)",
				By(sOver, constant, sMonic, polynomial.MonicDegreeZero.Read(ringK).At(s)))
			arg.Show(
				"therefore p = μ times one = μ",
				By(
					Normalized,
					unit,
					factorization,
					μOver,
					comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(polynomialRing)).AsFact().At(μ)))
		}),
})}

// ---------------------------------------------------------------------------
// The subfield and the subring a set generates, and the values of polynomials
// ---------------------------------------------------------------------------

// AdjoinSubfield — K(S) is a subfield holding K and S: the subfields of
// L holding K and S include L itself, so they meet in a subfield, and
// their meet holds what each of them holds.
var AdjoinSubfield = adjoinSubfieldThm{family.Add(registry.ProofEntry{
	Name: "AdjoinSubfield",
	Key:  "prop_796679df25b72c92",
	Reading: "K ⊆ L.carrier and S ⊆ L.carrier are load-bearing: with S outside the " +
		"carrier no subfield holds S, and the meet of no sets is the whole type. With them " +
		"the family met is never empty: L.carrier is its own subfield and holds K and S.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A).",
		Hypotheses: []string{
			"K ⊆ L.carrier",
			"S ⊆ L.carrier",
		},
		Conclusion: "subfield(L, field_adjoin(L, K, S)) ∧ " +
			"K ⊆ field_adjoin(L, K, S) ∧ " +
			"S ⊆ field_adjoin(L, K, S)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, S *Expr[Set[A]], inside Fact) {
			F, inF := a.LetAs[Set[Set[A]]]("F", "{M:set(A) | subfield(L, M) ∧ K ⊆ M ∧ S ⊆ M}")

			carrier := a.Have(
				"L is a subfield of itself and holds K and S, so it is a member of F",
				"L.carrier ∈ F",
				BySets(inF, inside, field.CarrierSubfield.Read(L)))
			nonempty := a.Have(
				"so F is not empty",
				"¬(F = ∅)",
				By(Normalized, carrier, set_basic.MemberNotEmpty.At(F)))
			subfields := a.Have(
				"every member of F is a subfield",
				"∀k:set(A). k ∈ F ⇒ subfield(L, k)",
				BySets(inF))
			meet := a.Have(
				"K(S) is by definition the meet of F",
				"field_adjoin(L, K, S) = ⋂F",
				Unfold(FieldAdjoinDef),
				inF.Rw(),
				Basic())

			a.Show(
				"the meet of F is a subfield holding K and S",
				meet.Rw(),
				SplitConjAll(
					Case(
						"a nonempty family of subfields meets in a subfield",
						By(nonempty, subfields, field.SubfieldInters.At(a.TermAs[FieldOps[A]]("L"), F))),
					Case(
						"K lies in every member of F, so in their meet",
						BySets(inF)),
					Case(
						"S lies in every member of F, so in their meet",
						BySets(inF)),
				))
		}),
})}

// AdjoinLeast — K(S) lies in every subfield holding K and S: such a
// subfield is one of the sets K(S) is the meet of.
var AdjoinLeast = adjoinLeastThm{family.Add(registry.ProofEntry{
	Name: "AdjoinLeast",
	Key:  "prop_f4eb70e69caf6b9f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S M:set(A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"K ⊆ M",
			"S ⊆ M",
		},
		Conclusion: "field_adjoin(L, K, S) ⊆ M",
	},
		func(a *Argument, L field.FieldFact[on.L], K, S, M *Expr[Set[A]], holds Fact) {
			member := a.Have(
				"M is a member of the family K(S) is the meet of",
				"M ∈ {N:set(A) | subfield(L, N) ∧ K ⊆ N ∧ S ⊆ N}",
				BySets(holds))
			a.Show(
				"and a meet lies in each of its members",
				Unfold(FieldAdjoinDef),
				BySets(member))
		}),
})}

// AdjoinElementSubfield — K(a), for a subfield K and a member a of L, is
// a subfield of L holding K and a: K and {a} lie in L, so AdjoinSubfield
// at S = {a} applies, and holding {a}, K(a) holds a.
var AdjoinElementSubfield = adjoinElementSubfieldThm{family.Add(registry.ProofEntry{
	Name: "AdjoinElementSubfield",
	Key:  "prop_1913407b09313a5b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
		},
		Conclusion: "subfield(L, field_adjoin(L, K, {a})) ∧ " +
			"K ⊆ field_adjoin(L, K, {a}) ∧ " +
			"a ∈ field_adjoin(L, K, {a})",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L")
			subK, aInL := hyp[0], hyp[1]
			adjoined := arg.Have(
				"so K(a) is a subfield of L holding K and {a}",
				"subfield(L, field_adjoin(L, K, {a})) ∧ "+
					"K ⊆ field_adjoin(L, K, {a}) ∧ "+
					"{a} ⊆ field_adjoin(L, K, {a})",
				By(
					subK,
					field.SubfieldSubset,
					aInL,
					set_order.SingSubset,
					AdjoinSubfield.Read(L).At(K, arg.TermAs[Set[A]]("{a}"))))
			arg.Show(
				"holding {a}, it holds a",
				By(adjoined, set_order.SingSubset))
		}),
})}

// AdjoinElementBetween — adjoining to K a point a of a subfield E ⊇ K
// stays inside E: K(a) is a subfield holding K and a, the least one, so
// E is among those it lies in.
var AdjoinElementBetween = adjoinElementBetweenThm{family.Add(registry.ProofEntry{
	Name: "AdjoinElementBetween",
	Key:  "prop_f551629de93964ba",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀K E:set(A). ∀a:A.",
		Hypotheses: []string{"subfield(L, K)", "subfield(L, E)", "K ⊆ E", "a ∈ E"},
		Conclusion: "subfield(L, field_adjoin(L, K, {a})) ∧ " +
			"K ⊆ field_adjoin(L, K, {a}) ∧ " +
			"a ∈ field_adjoin(L, K, {a}) ∧ " +
			"field_adjoin(L, K, {a}) ⊆ E",
	}, func(arg *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], a *Expr[A], h Fact) {
		pointInL := arg.Have(
			"a lies in L",
			"a ∈ L.carrier",
			BySets(h, field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), E)))
		arg.Show(
			"K(a) is the least subfield holding K and a, and E is one",
			BySets(
				h,
				pointInL,
				AdjoinElementSubfield.Read(L).AsFact().At(K, a),
				AdjoinLeast.Read(L).At(K, arg.TermAs[Set[A]]("{a}"), E)))
	}),
})}

// GeneratedSubringStructure — the generated subring is a subring of the
// field holding its generators, and the least such: a point lies in it when
// it lies in every qualifying subring, and each closure condition, holding
// in every qualifying subring, holds in their intersection.
var GeneratedSubringStructure = generatedSubringStructureThm{family.Add(registry.ProofEntry{
	Name: "GeneratedSubringStructure",
	Key:  "prop_650a90505708f5e8",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S E:set(A).",
		Hypotheses: []string{"subring(field_ring(L), S)", "E ⊆ L.carrier"},
		Conclusion: "subring(field_ring(L), «G») ∧ S ∪ E ⊆ «G» ∧ (∀B:set(A). «qualifies»(B) ⇒ «G» ⊆ B)",
		Abbrev: Abbrev{
			{Name: "G", Text: "generated_subring(field_ring(L), S, E)"},
			{Name: "qualifies", Text: "λB:set(A). subring(field_ring(L), B) ∧ S ∪ E ⊆ B"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, E *Expr[Set[A]], h Fact) {
		ring := a.TermAs[RingOps[A]]("field_ring(L)")
		least := a.Have(
			"the defining intersection contains the generators and lies in every qualifying subring",
			"S ∪ E ⊆ «G» ∧ (∀B:set(A). «qualifies»(B) ⇒ «G» ⊆ B)",
			BySets(GeneratedSubringDef))
		inField := a.Have(
			"the field is itself a qualifying subring, holding S and E, so the generated subring lies in it",
			"«G» ⊆ L.carrier",
			BySets(comm_ring.CarrierSubring.Read(field.RingOn.Read(L)), least, comm_ring.SubringSubset, h))
		membership := a.Have(
			"membership means belonging to every qualifying subring",
			"∀z:A. z ∈ «G» ⇔ (∀B:set(A). «qualifies»(B) ⇒ z ∈ B)",
			BySets(At(GeneratedSubringDef, ring, S, E)))
		constants := a.Have(
			"the generated subring holds zero and one, which S holds",
			"L.zero ∈ «G» ∧ L.one ∈ «G»",
			BySets(least, h, At(comm_ring.SubringZero, ring, S), At(comm_ring.SubringOne, ring, S)))
		sums := a.Have(
			"the intersection is closed under sums",
			"∀x y:A. x ∈ «G» ∧ y ∈ «G» ⇒ x + y ∈ «G»",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				xy := b.Assume()
				everyRing := b.Have(
					"each qualifying subring contains the sum",
					"∀B:set(A). «qualifies»(B) ⇒ x + y ∈ B",
					Derive(func(c *Argument) {
						B := c.FixAs[Set[A]]("B")
						qualifies := c.Assume()
						points := c.Have(
							"both summands lie in this subring",
							"x ∈ B ∧ y ∈ B",
							BySets(xy, least, qualifies))
						c.Show(
							"a subring holds the sum of two of its members",
							By(points, qualifies, At(comm_ring.SubringAdd, ring, B)))
					}))
				b.Show(
					"the sum lies in the intersection",
					By(membership.At(b.TermAs[A]("x + y")), everyRing))
			}))
		negatives := a.Have(
			"the intersection is closed under negatives",
			"∀x:A. x ∈ «G» ⇒ -x ∈ «G»",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				xIn := b.Assume()
				everyRing := b.Have(
					"each qualifying subring contains the negative",
					"∀B:set(A). «qualifies»(B) ⇒ -x ∈ B",
					Derive(func(c *Argument) {
						B := c.FixAs[Set[A]]("B")
						qualifies := c.Assume()
						point := c.Have(
							"the element lies in this subring",
							"x ∈ B",
							BySets(xIn, least, qualifies))
						c.Show(
							"a subring holds the negation of a member",
							By(point, qualifies, At(comm_ring.SubringNeg, ring, B)))
					}))
				b.Show(
					"the negative lies in the intersection",
					By(membership.At(b.TermAs[A]("-x")), everyRing))
			}))
		products := a.Have(
			"the intersection is closed under products",
			"∀x y:A. x ∈ «G» ∧ y ∈ «G» ⇒ x * y ∈ «G»",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				xy := b.Assume()
				everyRing := b.Have(
					"each qualifying subring contains the product",
					"∀B:set(A). «qualifies»(B) ⇒ x * y ∈ B",
					Derive(func(c *Argument) {
						B := c.FixAs[Set[A]]("B")
						qualifies := c.Assume()
						points := c.Have(
							"both factors lie in this subring",
							"x ∈ B ∧ y ∈ B",
							BySets(xy, least, qualifies))
						c.Show(
							"a subring holds the product of two of its members",
							By(points, qualifies, At(comm_ring.SubringMul, ring, B)))
					}))
				b.Show(
					"the product lies in the intersection",
					By(membership.At(b.TermAs[A]("x * y")), everyRing))
			}))
		ringG := a.Have(
			"so the intersection is a subring of the field",
			"subring(field_ring(L), «G»)",
			Simp(Fwd(comm_ring.SubringDef)),
			By(inField, constants, sums, negatives, products))
		a.Show(
			"a subring holding the generators, inside every qualifying subring",
			By(ringG, least))
	}),
})}

// PolynomialImageSubring — polynomial values over a subring S of L form
// a subring of L holding S and x. Constant and variable polynomials
// supply S and x; evaluation preserves sums and products. L is itself a
// ring holding S and x, so S[x], the least such ring, lies in L; and
// multiplication by -one supplies negation, so S[x] meets the subring
// conditions.
var PolynomialImageSubring = polynomialImageSubringThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageSubring",
	Key:  "prop_4cef38d95f94ad91",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
		},
		Conclusion: "subring(field_ring(L), polynomial_image(field_ring(L), S, x)) ∧ " +
			"S ⊆ polynomial_image(field_ring(L), S, x) ∧ " +
			"x ∈ polynomial_image(field_ring(L), S, x)",
	},
		func(arg *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"S is a subring of L",
				"x lies in L")
			subringS, xInL := hyp[0], hyp[1]
			ring := field.RingOn.Read(L)
			sInL := arg.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringS)))
			ringS := arg.Have(
				"S is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			xM := arg.MemberOf[on.L](x, xInL)
			inImage := arg.Have(
				"S[x] is the set of the values at x of the polynomials over S",
				"∀u:A. "+
					"    u ∈ polynomial_image(field_ring(L), S, x) ⇔ "+
					"    ∃p:(num → A). polynomial_over(S, p) ∧ u = polynomial_eval(p, x)",
				Unfold(PolynomialImageDef),
				SetTac())

			// The polynomials over S at x: constants, the variable, sums and products.
			constants := arg.Have(
				"a member k of S is the value of the constant polynomial k • basis_vector(0) over S",
				Statement{
					Binders: "∀k:A.",
					Hypotheses: []string{
						"k ∈ S",
					},
					Conclusion: "polynomial_over(S, vec_scalar_mul(k, basis_vector(0))) ∧ " +
						"polynomial_eval(vec_scalar_mul(k, basis_vector(0)), x) = k",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[A]()
					kInS := b.Assume()
					km := b.MemberOf[on.L](k, b.Have(
						"k lies in L",
						"k ∈ L.carrier",
						BySets(sInL, kInS)))
					over := b.Have(
						"k • basis_vector(0) is a polynomial over S, the polynomials over S a module over S",
						"polynomial_over(S, vec_scalar_mul(k, basis_vector(0)))",
						BySets(
							kInS,
							polynomial.BasisVectorOver.Read(ringS),
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringS))))
					b.Show(
						"so k is the value of a constant polynomial over S, which takes the value k",
						By(over, polynomial_evaluation.EvalConstant.Read(ring).At(km, xM)))
				}))
			first := arg.TermAs[Nat]("1")
			variable := arg.Have(
				"x is the value of the variable basis_vector(1), a polynomial over S: x ^ 1 = x",
				"polynomial_over(S, basis_vector(1)) ∧ polynomial_eval(basis_vector(1), x) = x",
				By(
					polynomial.BasisVectorOver.Read(ringS).At(first),
					polynomial_evaluation.EvalBasisVector.Read(ring).At(first, xM),
					comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(xM)))
			sums := arg.Have(
				"the sum of two polynomials over S is a polynomial over S, and evaluation at x adds",
				Statement{
					Binders: "∀p q:(num → A).",
					Hypotheses: []string{
						"polynomial_over(S, p)",
						"polynomial_over(S, q)",
					},
					Conclusion: "polynomial_over(S, vec_add(p, q)) ∧ " +
						"polynomial_eval(vec_add(p, q), x) = polynomial_eval(p, x) + polynomial_eval(q, x)",
				},
				BySets(
					sInL,
					xInL,
					comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ringS)),
					polynomial_evaluation.EvalAdd.Read(ring),
					polynomial.PolynomialOverMono))
			products := arg.Have(
				"the product of two polynomials over S is a polynomial over S, and evaluation at x multiplies",
				Statement{
					Binders: "∀p q:(num → A).",
					Hypotheses: []string{
						"polynomial_over(S, p)",
						"polynomial_over(S, q)",
					},
					Conclusion: "polynomial_over(S, polynomial_mul(p, q)) ∧ " +
						"polynomial_eval(polynomial_mul(p, q), x) = polynomial_eval(p, x) * polynomial_eval(q, x)",
				},
				By(
					sInL,
					xInL,
					polynomial.PolynomialMulOver.Read(ringS),
					polynomial_evaluation.EvalMul.Read(ring),
					polynomial.PolynomialOverMono))

			// S[x] holds S and x and is closed under + and *.
			sInImage := arg.Have(
				"S lies in S[x], each member the value of a constant",
				"S ⊆ polynomial_image(field_ring(L), S, x)",
				BySets(inImage, constants))
			xInImage := arg.Have(
				"x lies in S[x], the value of the variable",
				"x ∈ polynomial_image(field_ring(L), S, x)",
				By(inImage, variable))
			closed := arg.Have(
				"S[x] is closed under + and *: for u = p(x) and v = q(x) "+
					"they are the values of p + q and polynomial_mul(p, q)",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ polynomial_image(field_ring(L), S, x)",
						"v ∈ polynomial_image(field_ring(L), S, x)",
					},
					Conclusion: "u + v ∈ polynomial_image(field_ring(L), S, x) ∧ " +
						"u * v ∈ polynomial_image(field_ring(L), S, x)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[A](), b.FixAs[A]()
					both := b.Assume()
					p, pValue := b.ObtainAs[Fun[Nat, A]](
						"u is the value at x of a polynomial p over S",
						"∃p:(num → A). polynomial_over(S, p) ∧ u = polynomial_eval(p, x)",
						By(inImage.At(u), both))
					q, qValue := b.ObtainAs[Fun[Nat, A]](
						"and v the value of a polynomial q over S",
						"∃q:(num → A). polynomial_over(S, q) ∧ v = polynomial_eval(q, x)",
						By(inImage.At(v), both))
					b.Show(
						"p + q and polynomial_mul(p, q) are polynomials over S with the values u + v and u * v",
						By(
							inImage.At(b.TermAs[A]("u + v")),
							inImage.At(b.TermAs[A]("u * v")),
							sums.At(p, q),
							products.At(p, q),
							pValue,
							qValue))
				}))

			// S[x] lies in L: L itself is a ring holding S and x, and S[x] is the least one.
			fullRing := arg.Have(
				"L's whole carrier is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), L.carrier))",
				By(
					Normalized,
					ring,
					module_record.RestrictRingCarrier.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"))))
			inL := arg.Have(
				"so S[x] lies in L",
				"polynomial_image(field_ring(L), S, x) ⊆ L.carrier",
				By(fullRing, sInL, xInL, PolynomialImageLeast.Read(L).At(S, arg.TermAs[Set[A]]("L.carrier"), x)))

			// S[x] is closed under negation and holds zero and one.
			negClosed := arg.Have(
				"S[x] is closed under negation: -u = -one * u, a product of two of its members",
				"∀u:A. u ∈ polynomial_image(field_ring(L), S, x) ⇒ -u ∈ polynomial_image(field_ring(L), S, x)",
				BySets(
					closed,
					comm_ring.OneIn.Read(ringS),
					comm_ring.NegIn.Read(ringS),
					sInImage,
					inL,
					comm_ring.NegOneMulOn.Read(ring)))
			zeroOne := arg.Have(
				"zero and one lie in S, so in S[x]",
				"L.zero ∈ polynomial_image(field_ring(L), S, x) ∧ L.one ∈ polynomial_image(field_ring(L), S, x)",
				By(
					arg.Unfolded(sInImage, set_basic.SubsetDef),
					comm_ring.ZeroIn.Read(ringS),
					comm_ring.OneIn.Read(ringS)))
			imageSubring := arg.Have(
				"a subset of L holding zero and one and closed under +, - and *, S[x] is a subring of L",
				"subring(field_ring(L), polynomial_image(field_ring(L), S, x))",
				Simp(Fwd(comm_ring.SubringDef)),
				By(inL, zeroOne, closed, negClosed))
			arg.Show(
				"S[x] is a subring of L holding S and x",
				By(imageSubring, sInImage, xInImage))
		}),
})}

// PolynomialImageRing — K[a] is a subring of L holding K and a, inside
// K(a). The subfield K is a subring of L, so PolynomialImageSubring
// applies. The field K(a) holds K and a, so PolynomialImageLeast puts
// every polynomial value in K(a).
var PolynomialImageRing = polynomialImageRingThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageRing",
	Key:  "prop_5a3a94383c731ae8",
	Reading: "subfield(L, K) is load-bearing: at K = {one} no sequence is a " +
		"polynomial over K, its trailing coefficients being zero, so K[a] is empty.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
		},
		Conclusion: "subring(field_ring(L), polynomial_image(field_ring(L), K, a)) ∧ " +
			"K ⊆ polynomial_image(field_ring(L), K, a) ∧ " +
			"a ∈ polynomial_image(field_ring(L), K, a) ∧ " +
			"polynomial_image(field_ring(L), K, a) ⊆ field_adjoin(L, K, {a})",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L")
			subK, aInL := hyp[0], hyp[1]
			aM := arg.MemberOf[on.L](a, aInL)
			fieldL := arg.TermAs[FieldOps[A]]("L")
			image := arg.Have(
				"K[a] is a subring of L holding K and a",
				"subring(field_ring(L), polynomial_image(field_ring(L), K, a)) ∧ "+
					"K ⊆ polynomial_image(field_ring(L), K, a) ∧ "+
					"a ∈ polynomial_image(field_ring(L), K, a)",
				By(subK, field.SubfieldSubring.Read(L).At(K), aInL, PolynomialImageSubring.Read(L).At(K, aM)))

			// K[a] lies in K(a), a subfield of L holding K and a.
			kOfA := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
			adjoined := arg.Conjuncts(
				arg.Have(
					"K(a) is a subfield of L holding K and a",
					"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
					By(subK, AdjoinElementSubfield.Read(L).At(K, aM))),
				"K(a) is a subfield of L",
				"holding K",
				"and a")
			subAdjoin, kInAdjoin, aInAdjoin := adjoined[0], adjoined[1], adjoined[2]
			adjoinedField := arg.Have(
				"and is a field in its own right",
				"field_on(restrict_field(L, field_adjoin(L, K, {a})))",
				By(subAdjoin, field.SubfieldFieldOn.Read(L).At(kOfA)))
			adjoinedRecord := arg.Simplified(field.RestrictFieldRing.At(fieldL, kOfA))
			adjoinedRing := arg.Have(
				"so K(a) is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), field_adjoin(L, K, {a})))",
				adjoinedRecord.Rw(),
				By(field.RingOn.Read(adjoinedField)))
			inAdjoin := arg.Have(
				"so K[a], the least ring holding K and a, lies in K(a)",
				"polynomial_image(field_ring(L), K, a) ⊆ field_adjoin(L, K, {a})",
				By(adjoinedRing, kInAdjoin, aInAdjoin, PolynomialImageLeast.Read(L).At(K, kOfA, a)))
			arg.Show(
				"K[a] is a subring of L holding K and a, inside K(a)",
				By(image, inAdjoin))
		}),
})}

// PolynomialImageLeast — K[a] is the least ring holding K and a: a ring
// Q under the field's operations holding both holds the value at a of
// every polynomial over K. A polynomial over K is one over Q, its
// coefficients lying in K ⊆ Q, and its value at a ∈ Q, computed in the
// ring on Q, lies in Q.
var PolynomialImageLeast = polynomialImageLeastThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageLeast",
	Key:  "prop_116b615aabe35525",
	Reading: "Q is any ring under the field's operations holding K and a, " +
		"whether or not it lies in L. If L.zero ∉ K then K[a] is empty, " +
		"polynomial_over asking every coefficient in K, and the claim holds vacuously.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K Q:set(A). ∀a:A.",
		Hypotheses: []string{
			"comm_ring_on(restrict_ring(field_ring(L), Q))",
			"K ⊆ Q",
			"a ∈ Q",
		},
		Conclusion: "polynomial_image(field_ring(L), K, a) ⊆ Q",
	},
		func(arg *Argument, L field.FieldFact[on.L], K, Q *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"Q is a ring under the field's operations",
				"K lies in Q",
				"and so does a")
			ringQ, kInQ, aInQ := hyp[0], hyp[1], hyp[2]
			values := arg.Have(
				"a polynomial over K is one over Q, and takes its value at a in Q, read in the ring on Q",
				"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_eval(p, a) ∈ Q",
				By(kInQ, aInQ, polynomial_evaluation.EvalIn.Read(ringQ), polynomial.PolynomialOverMono))
			arg.Show(
				"so K[a], the image of the polynomials over K under evaluation at a, lies in Q",
				Unfold(PolynomialImageDef),
				Simp(Fwd(set_image.SimpleImageGen), Fwd(set_image.ImageSubsetIff)),
				By(values))
		}),
})}

// AdjoinEvaluationHomomorphism — evaluation at a is a ring homomorphism
// from the polynomials over K into K(a). K(a) is a ring under the
// field's operations holding K and a, so evaluation at a is a ring
// homomorphism from the polynomials over K(a) into it. The polynomials
// over K lie among them and carry the same operations, so each clause
// of a ring homomorphism is read off that one, restricted to them.
var AdjoinEvaluationHomomorphism = adjoinEvaluationHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AdjoinEvaluationHomomorphism",
	Key:  "prop_4a21a7558958a6c0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
		},
		Conclusion: "ring_homomorphism(polynomial_ring(«scalars»), " +
			"    «adjoinRing», " +
			"    λp:(num → A). polynomial_eval(p, a))",
		Abbrev: Abbrev{
			{Name: "adjoinRing", Text: "restrict_ring(field_ring(L), field_adjoin(L, K, {a}))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], subK, aInL Fact) {
			kOfA := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
			scalars := arg.Have(
				"K is a ring under the field's operations",
				"comm_ring_on(«scalars»)",
				By(subK, field.SubfieldCommRing.Read(L).At(K)))
			adjoined := arg.Conjuncts(
				arg.Have(
					"K(a) is a subfield of L holding K and a",
					"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
					By(subK, AdjoinElementSubfield.Read(L).At(K, arg.MemberOf[on.L](a, aInL)))),
				"K(a) is a subfield of L",
				"holding K",
				"and a")
			subAdjoin, kInAdjoin, aInAdjoin := adjoined[0], adjoined[1], adjoined[2]
			adjoinRing := arg.Have(
				"so K(a) is a ring under the field's operations",
				"comm_ring_on(«adjoinRing»)",
				By(subAdjoin, field.SubfieldCommRing.Read(L).At(kOfA)))
			evaluation := arg.Have(
				"evaluation at a, a point of K(a), is a ring homomorphism from the polynomials over K(a) into K(a)",
				"ring_homomorphism(polynomial_ring(«adjoinRing»), "+
					"    «adjoinRing», "+
					"    λp:(num → A). polynomial_eval(p, a))",
				By(polynomial_evaluation.EvalHomomorphism.Read(adjoinRing).At(proof.MemberOf(a, aInAdjoin))))

			overAdjoin := arg.Have(
				"a polynomial over K is one over K(a), K lying in K(a)",
				"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_over(field_adjoin(L, K, {a}), p)",
				By(kInAdjoin, polynomial.PolynomialOverMono))
			values := arg.Have(
				"so its value at a lies in K(a)",
				"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_eval(p, a) ∈ field_adjoin(L, K, {a})",
				By(overAdjoin, ring_homomorphism.MapIn.Read(evaluation)))
			sums := arg.Have(
				"evaluation keeps the sum of two polynomials over K",
				Statement{
					Binders:    "∀p q:(num → A).",
					Hypotheses: []string{"polynomial_over(K, p)", "polynomial_over(K, q)"},
					Conclusion: "polynomial_eval(vec_add(p, q), a) = polynomial_eval(p, a) + polynomial_eval(q, a)",
				},
				By(overAdjoin, ring_homomorphism.MapAdd.Read(evaluation)))
			products := arg.Have(
				"and their product",
				Statement{
					Binders:    "∀p q:(num → A).",
					Hypotheses: []string{"polynomial_over(K, p)", "polynomial_over(K, q)"},
					Conclusion: "polynomial_eval(polynomial_mul(p, q), a) = " +
						"polynomial_eval(p, a) * polynomial_eval(q, a)",
				},
				By(overAdjoin, ring_homomorphism.MapMul.Read(evaluation)))
			arg.Show(
				"so on the ring of the polynomials over K evaluation "+
					"at a keeps the carrier, sums, products and one",
				By(
					polynomial.PolynomialRingOn.Read(scalars),
					adjoinRing,
					values,
					sums,
					products,
					ring_homomorphism.MapOne.Read(evaluation),
					ring_homomorphism.RingHomomorphism))
		}),
})}

// CombinationOfPowers — a combination of finitely many powers of a with
// coefficients in K, the powers drawn from exponents E on which
// i ↦ a ^ i is one-to-one, is the value at a of the polynomial over K
// carrying those coefficients at those exponents. The exponents in E of
// the members of T are finitely many, i ↦ a ^ i being one-to-one on them
// and sending them onto T, so they are bounded by some m. The polynomial
// p with coefficient κ(a ^ i) at each such exponent i and zero elsewhere
// vanishes past m and has its coefficients in K. Its value is the sum of
// its terms over its support, which widens to those exponents, p
// vanishing off them, and reindexes along i ↦ a ^ i onto T.
var CombinationOfPowers = combinationOfPowersThm{family.Add(registry.ProofEntry{
	Name: "CombinationOfPowers",
	Key:  "prop_335619f9e0ea9915",
	Reading: "Injectivity on E is load-bearing: at a = one and T = {one}, E = {0, 1} " +
		"gives q = κ(one) • (1 + x), whose value is twice the combination κ(one) * one, and E " +
		"= 𝕌 gives no polynomial at all. An empty T gives q = vec_zero and the empty sum, zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K T:set(A). ∀E:set(num). ∀a:A. ∀κ:(A → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"finite(T)",
			"T ⊆ image(«powerMap», E)",
			"∀x:A. x ∈ T ⇒ κ(x) ∈ K",
			"injective_on(E, «powerMap»)",
		},
		Conclusion: "∃q:(num → A). " +
			"    polynomial_over(K, q) ∧ " +
			"    polynomial_eval(q, a) = module_sum(L.add, L.zero, T, λx:A. κ(x) * x) ∧ " +
			"    (∀i:num. " +
			"        q(i) = " +
			"        COND(i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T, " +
			"            κ(monoid_pow(L.mul, L.one, a, i)), " +
			"            L.zero))",
		Abbrev: Abbrev{
			{Name: "exponentsOfT", Text: "preimage_on(E, «powerMap», T)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, T *Expr[Set[A]],
			E *Expr[Set[Nat]],
			a *Expr[A],
			κ *Arrow[A, A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"T is finite",
				"T consists of powers a ^ i with i in E",
				"the coefficients lie in K",
				"i ↦ a ^ i is one-to-one on E")
			subK, aInL, finiteT, inImage, coefficientsInK, injectiveE :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			ring := field.RingOn.Read(L)
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			powersInL := arg.Have(
				"every power of a lies in L",
				"∀i:num. monoid_pow(L.mul, L.one, a, i) ∈ L.carrier",
				By(aInL, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))

			// The exponents in E of the members of T: finitely many, so bounded.
			exponents := arg.TermAs[Set[Nat]]("«exponentsOfT»")
			power := arg.TermAs[Fun[Nat, A]]("«powerMap»")
			exponentOf := arg.Have(
				"i is such an exponent exactly when it lies in E and a ^ i in T",
				"∀i:num. i ∈ «exponentsOfT» ⇔ i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T",
				BySets())
			exponentsInE := arg.Have(
				"the exponents lie in E",
				"«exponentsOfT» ⊆ E",
				BySets())
			injectiveOnExponents := arg.Have(
				"so i ↦ a ^ i is one-to-one on them",
				"injective_on(«exponentsOfT», «powerMap»)",
				By(injectiveE, exponentsInE, functions.InjectiveOnSubset.At(power, exponents, E)))
			imageIsT := arg.Have(
				"and sends them onto T, each member of T being a ^ i for some i in E",
				"image(«powerMap», «exponentsOfT») = T",
				BySets(inImage))
			finiteExponents := arg.Have(
				"the exponents are finitely many, as their image T is",
				"finite(«exponentsOfT»)",
				By(finiteT, imageIsT, injectiveOnExponents, finite_set.FiniteImageInjEq.At(power, exponents)))
			m, bounded := arg.ObtainAs[Nat](
				"being finitely many, they are bounded by some m",
				"∃m:num. «exponentsOfT» ⊆ 0 .. m",
				By(finiteExponents, num_segment.FiniteIffBounded))
			atMostM := arg.Have(
				"so i lies in E with a ^ i in T only for i ≤ m",
				"∀i:num. i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T ⇒ i ≤ m",
				BySets(bounded))

			// The polynomial p: κ(a ^ i) at each exponent i, zero elsewhere.
			pDefined := arg.Let(
				"p",
				arg.Term(
					"λi:num. "+
						"    COND(i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T, κ(monoid_pow(L.mul, L.one, a, i)), L.zero)"))
			atExponents := arg.Have(
				"at an exponent i the coefficient of p is κ(a ^ i)",
				"∀i:num. i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T ⇒ p(i) = κ(monoid_pow(L.mul, L.one, a, i))",
				By(pDefined))
			elsewhere := arg.Have(
				"and elsewhere it is zero",
				"∀i:num. ¬(i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T) ⇒ p(i) = L.zero",
				By(pDefined))
			pastM := arg.Have(
				"so p vanishes past m: an index i ≥ suc(m) is no exponent",
				"vec⟨suc(m)⟩(p)",
				Unfold(vec_space.VecDef),
				arg.ForEach(func(i *Expr[Nat]) Action {
					return By(
						elsewhere.At(i),
						atMostM.At(i),
						nat_order.SucLessEqIffLessThan.At(m, i),
						nat_order.NotLessEq.At(i, m))
				}))
			pInK := arg.Have(
				"each coefficient of p lies in K",
				"∀i:num. p(i) ∈ K",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.Term("i ∈ E ∧ monoid_pow(L.mul, L.one, a, i) ∈ T"))
					b.When(
						"at an exponent it is a coefficient κ(a ^ i) of the combination",
						func(c *Argument, exponent Fact) {
							c.Show(
								"κ(a ^ i) lies in K, a ^ i lying in T",
								By(Normalized, exponent, atExponents.At(i), coefficientsInK))
						})
					b.Otherwise(
						"elsewhere it is zero, a member of the subfield K",
						func(c *Argument, notExponent Fact) {
							c.Show(
								"zero lies in K",
								By(notExponent, elsewhere.At(i), subK, field.SubfieldZero))
						})
				}))
			pOver := arg.Have(
				"so p, vanishing past m, is a polynomial over K",
				"polynomial_over(K, p)",
				By(Normalized, pastM, pInK, polynomial.PolynomialOverDef))

			// Its value at a is the combination.
			termsInL := arg.Have(
				"the terms p(i) * a ^ i lie in L, as K does",
				"∀i:num. p(i) * monoid_pow(L.mul, L.one, a, i) ∈ L.carrier",
				By(pInK, arg.Unfolded(kInL, set_basic.SubsetDef), powersInL, comm_ring.MulIn.Read(ring)))
			support := arg.TermAs[Set[Nat]]("fun_support(L.zero, p)")
			supportInExponents := arg.Have(
				"p is nonzero only at exponents",
				"fun_support(L.zero, p) ⊆ «exponentsOfT»",
				BySets(elsewhere))
			offSupport := arg.Have(
				"off its support a term of p is zero * a ^ i = zero",
				"∀i:num. i ∉ fun_support(L.zero, p) ⇒ p(i) * monoid_pow(L.mul, L.one, a, i) = L.zero",
				BySets(powersInL, comm_ring.MulLeftZeroOn.Read(ring)))
			coefficientsInL := arg.Have(
				"the coefficients κ(x) lie in K, so in L",
				"∀x:A. x ∈ T ⇒ κ(x) ∈ L.carrier",
				BySets(coefficientsInK, kInL))
			exponentTermsInL := arg.Have(
				"so the terms κ(a ^ i) * a ^ i at the exponents lie in L",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ∈ «exponentsOfT»",
					},
					Conclusion: "κ(monoid_pow(L.mul, L.one, a, i)) * monoid_pow(L.mul, L.one, a, i) ∈ L.carrier",
				},
				By(exponentOf, coefficientsInL, powersInL, comm_ring.MulIn.Read(ring)))

			regular := module.RegularModuleOn.Read(ring)
			termOfP := arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(L.mul, L.one, a, i)")
			combinationTerm := arg.TermAs[Fun[A, A]]("λx:A. κ(x) * x")
			value := arg.Have(
				"p(a) is the combination",
				"polynomial_eval(p, a) = module_sum(L.add, L.zero, T, λx:A. κ(x) * x)",
				CalcEq(
					Leg(
						arg.Term(
							"module_sum(L.add, L.zero, fun_support(L.zero, p), λi:num. p(i) * monoid_pow(L.mul, L.one, a, i))"),
						"p(a) is the sum of the terms of p over its support",
						By(polynomial_evaluation.PolynomialEvalDef)),
					Leg(
						arg.Term(
							"module_sum(L.add, L.zero, «exponentsOfT», λi:num. p(i) * monoid_pow(L.mul, L.one, a, i))"),
						"which, read in L as a module over itself, is the sum over the exponents, p vanishing off them",
						By(
							finiteExponents,
							supportInExponents,
							termsInL,
							offSupport,
							module.ModuleSumSupport.Read(regular).At(exponents, support, termOfP))),
					Leg(
						arg.Term(
							"module_sum(L.add, "+
								"    L.zero, "+
								"    «exponentsOfT», "+
								"    λi:num. κ(monoid_pow(L.mul, L.one, a, i)) * monoid_pow(L.mul, L.one, a, i))"),
						"where p(i) = κ(a ^ i)",
						By(exponentOf, atExponents, module.ModuleSumCongruence)),
					FinalLeg(
						"the exponents run once over T, i ↦ a ^ i being one-to-one on them",
						By(
							imageIsT,
							finiteExponents,
							injectiveOnExponents,
							exponentTermsInL,
							module.ModuleSumImage.Read(regular).At(exponents, power, combinationTerm))),
				))
			arg.Take(arg.TermAs[Fun[Nat, A]]("p"))
			arg.Show(
				"p is a polynomial over K with those coefficients, and its value at a is the combination",
				By(pOver, value, pDefined))
		}),
})}

// PolynomialValueInSpan — the value at a of a polynomial over K vanishing
// from n on lies in the span over K of the powers a ^ i with i below n,
// taken in any ring M under the field's operations holding K and a. M is
// a vector space over K, and the span of those powers, which lie in M, is
// a subspace of it holding each of them. The value of p is the sum of its
// terms p(i) * a ^ i below n; each is a multiple of a power by a member of
// K, so lies in the subspace, and so does their sum.
var PolynomialValueInSpan = polynomialValueInSpanThm{family.Add(registry.ProofEntry{
	Name: "PolynomialValueInSpan",
	Key:  "prop_54caf7dfea5f5b3f",
	Reading: "Of M only its ring under the field's operations is read: it need " +
		"not lie in L.carrier nor be a field, as K[a] at a transcendental a is not.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A. ∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"comm_ring_on(restrict_ring(field_ring(L), M))",
			"K ⊆ M",
			"a ∈ M",
			"polynomial_over(K, p)",
			"vec⟨n⟩(p)",
		},
		Conclusion: "polynomial_eval(p, a) ∈ «powersBelowSpan»",
		Abbrev: Abbrev{
			{Name: "ringVectors", Text: "restrict_module(regular_module(field_ring(L)), M)"},
			{Name: "powersBelowSpan", Text: "module_span(«scalars», " +
				"    «ringVectors», " +
				"    {monoid_pow(L.mul, L.one, a, i) | i:num | i < n})"},
			{Name: "spanOfS", Text: "module_span(«scalars», «ringVectors», S)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			a *Expr[A],
			n *Expr[Nat],
			p *Expr[Fun[Nat, A]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"M is a ring under the field's operations",
				"holding K",
				"and a",
				"p is a polynomial over K",
				"vanishing from n on")
			subK, ringM, kInM, aInM, pOver, pPast := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]

			// The span of the set S of the powers below n is a subspace of M over K holding each of them.
			belowSet, belowDefined := arg.LetAs[Set[A]]("S", "{monoid_pow(L.mul, L.one, a, i) | i:num | i < n}")
			space := arg.Have(
				"M is a vector space over K",
				"module_on(«scalars», «ringVectors»)",
				By(subK, ringM, kInM, field_extension.RingExtensionModuleOn.Read(L).At(K, M)))
			powersInM := arg.Have(
				"M holds a and is closed under the product, so it holds every power of a",
				"∀i:num. monoid_pow(L.mul, L.one, a, i) ∈ M",
				By(aInM, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringM))))
			belowInM := arg.Have(
				"in particular S lies in M",
				"S ⊆ M",
				BySets(belowDefined, powersInM))
			scalarRing := arg.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«ringVectors»")
			spanTerm := arg.TermAs[Set[A]]("«spanOfS»")
			spanSubspace := arg.Have(
				"the span of S is a subspace of M",
				"submodule(«scalars», «ringVectors», «spanOfS»)",
				By(belowInM, submodule.SpanSubmodule.Read(space).At(belowSet)))
			spanRecord := arg.Have(
				"restricting L to the span is restricting M to it, M's operations being L's",
				"restrict_module(regular_module(field_ring(L)), «spanOfS») = "+
					"restrict_module(«ringVectors», «spanOfS»)",
				Simp(Fwd(module_record.RestrictModuleDef), Fwd(module_record.RegularModuleDef)),
				Refl())
			spanModule := arg.Have(
				"a vector space over K in its own right",
				"module_on(«scalars», restrict_module(regular_module(field_ring(L)), «spanOfS»))",
				spanRecord.Rw(),
				By(spanSubspace, submodule.SubmoduleModuleOn.Read(space).At(spanTerm)))
			powersInSpan := arg.Have(
				"holding each power below n",
				"∀i:num. i < n ⇒ monoid_pow(L.mul, L.one, a, i) ∈ «spanOfS»",
				BySets(belowDefined, submodule.SubsetSpan.At(scalarRing, vectors, belowSet)))

			// The value of p is a sum of multiples of those powers by members of K.
			pOverM := arg.Have(
				"p is a polynomial over M as well",
				"polynomial_over(M, p)",
				By(kInM, pOver, polynomial.PolynomialOverMono))
			value := arg.Have(
				"its value is the sum of its terms below n",
				"polynomial_eval(p, a) = "+
					"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. p(i) * monoid_pow(L.mul, L.one, a, i))",
				By(
					pOverM,
					polynomial_evaluation.EvalBelow.Read(ringM).At(
						proof.InhabitFrom(p, pPast), proof.MemberOf(a, aInM))))
			terms := arg.Have(
				"each term p(i) * a ^ i lies in the span, closed under scaling by K",
				"∀i:num. i ∈ {i:num | i < n} ⇒ p(i) * monoid_pow(L.mul, L.one, a, i) ∈ «spanOfS»",
				By(polynomial.CoefficientIn.Read(pOver), powersInSpan, submodule.SubmoduleSmul.Read(spanSubspace)))
			below := arg.TermAs[Set[Nat]]("{i:num | i < n}")
			term := arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(L.mul, L.one, a, i)")
			arg.Show(
				"and so does their sum",
				By(
					value,
					terms,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumIn.Read(spanModule).At(below, term)))
		}),
})}

// ---------------------------------------------------------------------------
// K(a) = K[a], and its power basis
// ---------------------------------------------------------------------------

// AdjoinEqImage — for an algebraic a, K(a) = K[a]: the values of
// polynomials already form a field. K[a] is a ring inside K(a) holding K
// and a; what it lacks of a subfield is the inverses. A multiple of the
// minimal polynomial μ vanishes at a, so μ does not divide a polynomial p
// over K with p(a) ≠ zero; μ being irreducible over the field K, then
// u μ + v p is the one polynomial for some u and v over K, and evaluating
// at a gives v(a) * p(a) = one: inv(p(a)) is the value v(a). So K[a] is a
// subfield holding K and a, and K(a), the least one, lies in it.
var AdjoinEqImage = adjoinEqImageThm{family.Add(registry.ProofEntry{
	Name: "AdjoinEqImage",
	Key:  "prop_ec2bdb019ae739a6",
	Reading: "Algebraicity is load-bearing: for a transcendental a, K[a] " +
		"is a ring that is no field, and K(a) holds the quotients of its values.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "field_adjoin(L, K, {a}) = polynomial_image(field_ring(L), K, a)",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]
			ring := field.RingOn.Read(L)
			aM := arg.MemberOf[on.L](a, aInL)
			inImage := arg.Have(
				"K[a] is the set of the values at a of the polynomials over K",
				"∀x:A. "+
					"    x ∈ polynomial_image(field_ring(L), K, a) ⇔ "+
					"    ∃p:(num → A). polynomial_over(K, p) ∧ x = polynomial_eval(p, a)",
				Unfold(PolynomialImageDef),
				SetTac())
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))

			image := arg.TermAs[Set[A]]("polynomial_image(field_ring(L), K, a)")
			imageFacts := arg.Conjuncts(
				GroupPremises(hyp[0], PolynomialImageRing.Read(L).At(K, aM)),
				"K[a] is a subring of L",
				"holding K",
				"and a",
				"inside K(a)")
			imageSubring, kInImage, aInImage, imageInAdjoin :=
				imageFacts[0], imageFacts[1], imageFacts[2], imageFacts[3]
			imageInL := arg.Have(
				"K[a] lies in L",
				"polynomial_image(field_ring(L), K, a) ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(imageSubring)))

			// The minimal polynomial μ.
			μ := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
			μFacts := arg.Conjuncts(
				arg.Have(
					"μ is a polynomial over K vanishing at a, and irreducible over K",
					"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ "+
						"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero ∧ "+
						"polynomial_irreducible(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
					By(
						subK,
						aInL,
						algebraic,
						MinimalPolynomialSpec.Read(L).At(K, aM),
						MinimalPolynomialIrreducible.Read(L).At(K, aM))),
				"μ is a polynomial over K",
				"vanishing at a",
				"and irreducible over K")
			μOver, μRoot, μIrreducible := μFacts[0], μFacts[1], μFacts[2]
			μOverL := arg.Have(
				"μ is a polynomial over L as well",
				"polynomial_over(L.carrier, minimal_polynomial(L, K, a))",
				By(kInL, μOver, polynomial.PolynomialOverMono))

			// A nonzero value p(a) has an inverse among the values.
			inverse := arg.Have(
				"a nonzero value p(a) has an inverse v(a), v a polynomial over K",
				Statement{
					Binders: "∀p:(num → A).",
					Hypotheses: []string{
						"polynomial_over(K, p)",
						"¬(polynomial_eval(p, a) = L.zero)",
					},
					Conclusion: "∃v:(num → A). " +
						"    polynomial_over(K, v) ∧ polynomial_eval(v, a) * polynomial_eval(p, a) = L.one",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					pFacts := b.Conjuncts(
						b.Assume(),
						"p is a polynomial over K",
						"whose value at a is not zero")
					pOver, pNonzero := pFacts[0], pFacts[1]
					scalarRecord := b.Have(
						"restriction commutes with taking the underlying ring",
						"field_ring(restrict_field(L, K)) = restrict_ring(field_ring(L), K)",
						Simp(Fwd(field.FieldRingDef), Fwd(field.RestrictFieldDef), Fwd(module_record.RestrictRingDef)),
						Refl())
					μIrreducibleK := b.Have(
						"so μ is irreducible over the field K",
						"polynomial_irreducible(field_ring(restrict_field(L, K)), minimal_polynomial(L, K, a))",
						scalarRecord.Rw(),
						By(μIrreducible))
					notDivides := b.Have(
						"μ does not divide p: p = μ r would vanish at a",
						"¬polynomial_divides(field_ring(restrict_field(L, K)), minimal_polynomial(L, K, a), p)",
						Derive(func(c *Argument) {
							divides := c.SupposeNot()
							r, factored := c.ObtainAs[Fun[Nat, A]](
								"were it to divide p, p = μ r for a polynomial r over K",
								"∃r:(num → A). polynomial_over(K, r) ∧ p = polynomial_mul(minimal_polynomial(L, K, a), r)",
								By(c.Unfolded(divides, polynomial_division.PolynomialDividesDef)))
							factors := c.Conjuncts(
								factored,
								"r is a polynomial over K",
								"with p = μ r")
							rOver, pMultiple := factors[0], factors[1]
							rOverL := c.Have(
								"r is a polynomial over L as well",
								"polynomial_over(L.carrier, r)",
								By(kInL, rOver, polynomial.PolynomialOverMono))
							pZero := c.Have(
								"then p(a), the value of a multiple of μ, is zero",
								"polynomial_eval(p, a) = L.zero",
								pMultiple.Rw(),
								By(μOverL, rOverL, μRoot, polynomial_evaluation.EvalMulRoot.Read(ring).At(μ, r, aM)))
							c.Show(
								"contradicting p(a) ≠ zero",
								By(pNonzero, pZero))
						}))
					u, v, bezout := b.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
						"μ, irreducible over the field K, does not divide p, so "+
							"u μ + v p is the one polynomial for some u and v over K",
						"∃u v:(num → A). "+
							"    polynomial_over(K, u) ∧ "+
							"    polynomial_over(K, v) ∧ "+
							"    vec_add(polynomial_mul(u, minimal_polynomial(L, K, a)), polynomial_mul(v, p)) = "+
							"    basis_vector(0)",
						By(μIrreducibleK, pOver, notDivides, polynomial_division.IrreducibleCoprime.Read(fieldK).At(μ, p)))
					bezoutFacts := b.Conjuncts(
						bezout,
						"u is a polynomial over K",
						"so is v",
						"and u μ + v p is the one polynomial")
					uOver, vOver, identity := bezoutFacts[0], bezoutFacts[1], bezoutFacts[2]

					overL := b.Conjuncts(
						b.Have(
							"u, v and p are polynomials over L",
							"polynomial_over(L.carrier, u) ∧ polynomial_over(L.carrier, v) ∧ polynomial_over(L.carrier, p)",
							By(kInL, uOver, vOver, pOver, polynomial.PolynomialOverMono)),
						"u is a polynomial over L",
						"so is v",
						"and so is p")
					uOverL, vOverL, pOverL := overL[0], overL[1], overL[2]
					vValue := b.MemberOf[on.L](b.TermAs[A]("polynomial_eval(v, a)"),
						b.Have(
							"v(a) lies in L",
							"polynomial_eval(v, a) ∈ L.carrier",
							By(vOverL, polynomial_evaluation.EvalIn.Read(ring).At(v, aM))))
					pValue := b.MemberOf[on.L](b.TermAs[A]("polynomial_eval(p, a)"),
						b.Have(
							"p(a) lies in L",
							"polynomial_eval(p, a) ∈ L.carrier",
							By(pOverL, polynomial_evaluation.EvalIn.Read(ring).At(p, aM))))
					zeroth := b.TermAs[Nat]("0")
					uμ := b.TermAs[Fun[Nat, A]]("polynomial_mul(u, minimal_polynomial(L, K, a))")
					vp := b.TermAs[Fun[Nat, A]]("polynomial_mul(v, p)")
					value := b.Have(
						"evaluated at a, the one polynomial u μ + v p gives "+
							"v(a) * p(a) = one, the multiple u μ of μ vanishing there",
						"polynomial_eval(v, a) * polynomial_eval(p, a) = L.one",
						CalcEq(
							Leg(
								b.Term("L.zero + polynomial_eval(v, a) * polynomial_eval(p, a)"),
								"zero is the identity of the sum",
								ByArith(ring, vValue, pValue)),
							Leg(
								b.Term(
									"polynomial_eval(polynomial_mul(u, minimal_polynomial(L, K, a)), a) + "+
										"polynomial_eval(polynomial_mul(v, p), a)"),
								"u μ, a multiple of μ, vanishes at a, and evaluation multiplies",
								By(
									uOverL,
									μOverL,
									μRoot,
									polynomial_evaluation.EvalMulRoot.Read(ring).At(μ, u, aM),
									vOverL,
									pOverL,
									polynomial_evaluation.EvalMul.Read(ring).At(v, p, aM))),
							Leg(
								b.Term(
									"polynomial_eval(vec_add(polynomial_mul(u, minimal_polynomial(L, K, a)), polynomial_mul(v, p)), "+
										"    a)"),
								"evaluation adds",
								By(
									uOverL,
									μOverL,
									vOverL,
									pOverL,
									polynomial.PolynomialMulOver.Read(ring),
									polynomial_evaluation.EvalAdd.Read(ring).At(uμ, vp, aM))),
							Leg(
								b.Term("polynomial_eval(basis_vector(0), a)"),
								"u μ + v p is the one polynomial",
								identity.Rw(),
								Basic()),
							FinalLeg(
								"which takes the value a ^ 0 = one",
								By(
									Normalized,
									polynomial_evaluation.EvalBasisVector.Read(ring).At(zeroth, aM),
									comm_monoid.MonoidPowDef)),
						))
					b.Take(v)
					b.Show(
						"v is a polynomial over K with v(a) * p(a) = one",
						By(vOver, value))
				}))

			// K[a] is closed under inverses, so a subfield, and K(a) lies in it.
			invClosed := arg.Have(
				"K[a] is closed under inverses: inv(zero) = zero, and a nonzero x = p(a) has the inverse v(a)",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ polynomial_image(field_ring(L), K, a)",
					},
					Conclusion: "L.inv(x) ∈ polynomial_image(field_ring(L), K, a)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					p, pValue := b.ObtainAs[Fun[Nat, A]](
						"x is the value at a of a polynomial p over K",
						"∃p:(num → A). polynomial_over(K, p) ∧ x = polynomial_eval(p, a)",
						By(inImage.At(x), xIn))
					xM := b.MemberOf[on.L](x, b.Have(
						"x lies in L",
						"x ∈ L.carrier",
						BySets(imageInL, xIn)))
					b.Cases(b.Term("x = L.zero"))
					b.When(
						"inv(zero) = zero lies in the ring K[a]",
						func(c *Argument, isZero Fact) {
							c.Show(
								"inv(x) is inv(zero) = zero",
								isZero.Rw(),
								Simp(Fwd(field.InvZeroOn.Read(L))),
								Cite(comm_ring.SubringZero.Read(imageSubring)))
						})
					b.Otherwise(
						"a nonzero x = p(a) has the inverse v(a), a value at a",
						func(c *Argument, nonzero Fact) {
							v, vFacts := c.ObtainAs[Fun[Nat, A]](
								"some v over K has v(a) * x = L.one",
								"∃v:(num → A). polynomial_over(K, v) ∧ polynomial_eval(v, a) * x = L.one",
								By(Normalized, pValue, nonzero, inverse.At(p)))
							parts := c.Conjuncts(
								vFacts,
								"v is a polynomial over K",
								"with v(a) * x = one")
							vOver, inverts := parts[0], parts[1]
							vA := c.TermAs[A]("polynomial_eval(v, a)")
							valueOfV := c.Have(
								"v(a) is the value at a of a polynomial over K, v itself",
								"∃q:(num → A). polynomial_over(K, q) ∧ polynomial_eval(v, a) = polynomial_eval(q, a)",
								Derive(func(d *Argument) {
									d.Take(v)
									d.Show(
										"v is a polynomial over K",
										By(vOver))
								}))
							vIn := c.Have(
								"so v(a) lies in K[a]",
								"polynomial_eval(v, a) ∈ polynomial_image(field_ring(L), K, a)",
								By(valueOfV, inImage.At(vA)))
							vM := c.MemberOf[on.L](vA, c.Have(
								"and in L",
								"polynomial_eval(v, a) ∈ L.carrier",
								BySets(imageInL, vIn)))
							c.Show(
								"inv(x) = v(a), an inverse being unique",
								By(inverts, vIn, field.InvLeftUniqueOn.Read(L).At(vM, xM)))
						})
				}))
			subImage := arg.Have(
				"a ring inside L closed under inverses, K[a] is a subfield of L",
				"subfield(L, polynomial_image(field_ring(L), K, a))",
				Unfold(field.SubfieldDef),
				By(
					imageInL,
					invClosed,
					comm_ring.SubringZero.Read(imageSubring),
					comm_ring.SubringOne.Read(imageSubring),
					comm_ring.SubringAdd.Read(imageSubring),
					comm_ring.SubringNeg.Read(imageSubring),
					comm_ring.SubringMul.Read(imageSubring)))
			adjoinInImage := arg.Have(
				"so K(a), the least subfield holding K and a, lies in K[a]",
				"field_adjoin(L, K, {a}) ⊆ polynomial_image(field_ring(L), K, a)",
				By(
					subImage,
					kInImage,
					aInImage,
					set_order.SingSubset,
					AdjoinLeast.Read(L).At(K, arg.TermAs[Set[A]]("{a}"), image)))
			arg.Show(
				"K(a) and K[a] lie in each other",
				By(
					adjoinInImage,
					imageInAdjoin,
					set_order.SubsetAntisym.At(arg.TermAs[Set[A]]("field_adjoin(L, K, {a})"), image)))
		}),
})}

// AdjoinPowerBasis — for an algebraic a, the powers of a below the degree
// d of its minimal polynomial μ are d in number and a basis of K(a) over
// K. A polynomial over K vanishing from d on and at a is zero, μ having
// the least degree among the nonzero ones. So two equal powers
// a ^ i = a ^ j below d have i = j: x ^ i - x ^ j would be such a
// polynomial, with coefficient one at i. i ↦ a ^ i is then one-to-one below d, which
// counts d powers, and a vanishing combination of them is the value at a
// of a polynomial over K vanishing from d on (CombinationOfPowers), so
// its coefficients are zero. A member of K(a) = K[a] is the value of a
// polynomial over K, which is the value of its remainder by μ, and that
// lies in the span of the powers below d (PolynomialValueInSpan).
var AdjoinPowerBasis = adjoinPowerBasisThm{family.Add(registry.ProofEntry{
	Name: "AdjoinPowerBasis",
	Key:  "prop_bc8f6086896bde45",
	Reading: "The basis is a set of powers, not a family indexed by the " +
		"exponents: has_size says the d exponents below d give d distinct powers.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "module_basis(«scalars», «adjoinVectors», «powersBelowDegree») ∧ " +
			"has_size(«powersBelowDegree», polynomial_degree(minimal_polynomial(L, K, a)))",
		Abbrev: Abbrev{
			{Name: "spanOfB", Text: "module_span(«scalars», «adjoinVectors», B)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]
			ring := field.RingOn.Read(L)
			aM := arg.MemberOf[on.L](a, aInL)
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			ringK := field.RingOn.Read(fieldK)
			zero := arg.TermAs[A]("L.zero")

			// The minimal polynomial μ, its degree d, and the set B of the powers of a below d.
			d, dDef := arg.LetAs[Nat]("d", "polynomial_degree(minimal_polynomial(L, K, a))")
			basisSet, basisDefined := arg.LetAs[Set[A]]("B", "{monoid_pow(L.mul, L.one, a, i) | i:num | i < d}")
			spec := arg.Conjuncts(
				arg.Have(
					"μ is a monic polynomial over K vanishing at a, of least degree d among the nonzero ones",
					"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ "+
						"polynomial_monic(minimal_polynomial(L, K, a)) ∧ "+
						"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero ∧ "+
						"(∀q:(num → A). "+
						"    polynomial_over(K, q) ∧ ¬(q = vec_zero) ∧ polynomial_eval(q, a) = L.zero ⇒ "+
						"    d ≤ polynomial_degree(q))",
					By(Normalized, dDef, subK, algebraic, MinimalPolynomialSpec.Read(L).At(K, aM))),
				"μ is a polynomial over K",
				"μ is monic",
				"μ vanishes at a",
				"no nonzero polynomial over K vanishing at a has degree below d")
			μOver, μMonic, μRoot, μLeast := spec[0], spec[1], spec[2], spec[3]
			μ := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")

			// A polynomial over K vanishing from d on and at a is zero.
			lowDegree := arg.Have(
				"a polynomial over K vanishing from d on and at a is zero: a "+
					"nonzero one would have degree below d, the least such degree",
				"∀q:(num → A). polynomial_over(K, q) ∧ vec⟨d⟩(q) ∧ polynomial_eval(q, a) = L.zero ⇒ q = vec_zero",
				Derive(func(b *Argument) {
					q := b.FixAs[Fun[Nat, A]]("q")
					parts := b.Conjuncts(
						b.Assume(),
						"q is a polynomial over K",
						"q vanishes from d on",
						"q vanishes at a")
					qOver, qVec, qRoot := parts[0], parts[1], parts[2]
					nonzero := b.SupposeNot()
					small := b.Have(
						"nonzero and vanishing from d on, q has degree below d",
						"polynomial_degree(q) < d",
						By(nonzero, polynomial.DegreeBelow.At(zero, proof.InhabitFrom(q, qVec))))
					large := b.Have(
						"yet no nonzero polynomial over K vanishing at a has degree below d",
						"d ≤ polynomial_degree(q)",
						By(qOver, nonzero, qRoot, μLeast.At(q)))
					b.Show(
						"the two bounds contradict each other",
						By(small, large, nat_order.NotLessEq.At(d, b.TermAs[Nat]("polynomial_degree(q)"))))
				}))

			// The powers below d are distinct.
			below := arg.TermAs[Set[Nat]]("{i:num | i < d}")
			power := arg.TermAs[Fun[Nat, A]]("«powerMap»")
			negOneInK := arg.Have(
				"-one lies in K, a subfield",
				"-L.one ∈ K",
				By(subK, field.SubfieldOne, field.SubfieldNeg))
			negOne := arg.MemberOf[on.L](arg.TermAs[A]("-L.one"), arg.Have(
				"and so in L",
				"-L.one ∈ L.carrier",
				BySets(kInL, negOneInK)))
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			injective := arg.Have(
				"i ↦ a ^ i is one-to-one below d",
				"injective_on({i:num | i < d}, «powerMap»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					parts := b.Conjuncts(
						b.Assume(),
						"i lies below d",
						"j lies below d",
						"a ^ i = a ^ j")
					iBelow, jBelow, equal := parts[0], parts[1], parts[2]
					distinct := b.SupposeNot()
					xi, xj := b.TermAs[Fun[Nat, A]]("basis_vector(i)"), b.TermAs[Fun[Nat, A]]("basis_vector(j)")
					scaled := b.TermAs[Fun[Nat, A]]("vec_scalar_mul(-L.one, basis_vector(j))")
					scaledOver := b.Have(
						"-x ^ j is a polynomial over K, the polynomials over K a module over K",
						"polynomial_over(K, vec_scalar_mul(-L.one, basis_vector(j)))",
						BySets(
							negOneInK,
							polynomial.BasisVectorOver.Read(ringK),
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringK))))
					over := b.Have(
						"and so is x ^ i - x ^ j",
						"polynomial_over(K, vec_add(basis_vector(i), vec_scalar_mul(-L.one, basis_vector(j))))",
						BySets(
							scaledOver,
							polynomial.BasisVectorOver.Read(ringK).At(i),
							comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ringK))))
					powersPast := b.Have(
						"x ^ i and x ^ j vanish from d on, i and j lying below d",
						"vec⟨d⟩(basis_vector(i)) ∧ vec⟨d⟩(basis_vector(j))",
						By(iBelow, jBelow, vec_space.VecBasisVector))
					past := b.Have(
						"and so does x ^ i - x ^ j",
						"vec⟨d⟩(vec_add(basis_vector(i), vec_scalar_mul(-L.one, basis_vector(j))))",
						By(powersPast, negOne, vec_space.VecSmulOn.Read(ring), vec_space.VecAddOn.Read(ring)))
					scaledOverL := b.Have(
						"-x ^ j is a polynomial over L as well",
						"polynomial_over(L.carrier, vec_scalar_mul(-L.one, basis_vector(j)))",
						By(kInL, scaledOver, polynomial.PolynomialOverMono))
					root := b.Have(
						"its value at a is a ^ i - a ^ j = zero",
						"polynomial_eval(vec_add(basis_vector(i), vec_scalar_mul(-L.one, basis_vector(j))), a) = L.zero",
						CalcEq(
							Leg(
								b.Term(
									"polynomial_eval(basis_vector(i), a) + "+
										"polynomial_eval(vec_scalar_mul(-L.one, basis_vector(j)), a)"),
								"evaluation at a adds",
								By(
									scaledOverL,
									polynomial.BasisVectorOver.Read(ring).At(i),
									polynomial_evaluation.EvalAdd.Read(ring).At(xi, scaled, aM))),
							Leg(
								b.Term("monoid_pow(L.mul, L.one, a, i) + -L.one * monoid_pow(L.mul, L.one, a, j)"),
								"x ^ k takes the value a ^ k, and the scalar -one comes out",
								By(
									polynomial_evaluation.EvalBasisVector.Read(ring).At(i, aM),
									polynomial.BasisVectorOver.Read(ring).At(j),
									polynomial_evaluation.EvalScalar.Read(ring).At(negOne, aM, xj),
									polynomial_evaluation.EvalBasisVector.Read(ring).At(j, aM))),
							FinalLeg(
								"which is zero, a ^ i and a ^ j being one",
								ByArith(
									ring,
									comm_monoid.PowIn.Read(mulMonoid).At(aM, i),
									comm_monoid.PowIn.Read(mulMonoid).At(aM, j),
									equal)),
						))
					vanishing := b.Have(
						"so x ^ i - x ^ j is the zero polynomial",
						"vec_add(basis_vector(i), vec_scalar_mul(-L.one, basis_vector(j))) = vec_zero",
						By(over, past, root, lowDegree))
					coefficient := b.Have(
						"yet its coefficient at i is one + -one * zero = one, i and j being distinct",
						"(vec_add(basis_vector(i), vec_scalar_mul(-L.one, basis_vector(j))))(i) = L.one",
						Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
						ByArith(ring, distinct))
					b.Show(
						"and one is not zero",
						By(vanishing, coefficient, vec_space.VecZeroDef, field.OneNotZeroOn.Read(L)))
				}))

			// K(a) is a vector space over K holding the powers below d.
			adjoin := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
			adjoined := arg.Conjuncts(
				arg.Have(
					"K(a) is a subfield of L holding K and a",
					"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
					By(subK, AdjoinElementSubfield.Read(L).At(K, aM))),
				"K(a) is a subfield of L",
				"holding K",
				"and a")
			subAdjoin, kInAdjoin, aInAdjoin := adjoined[0], adjoined[1], adjoined[2]
			space := arg.Have(
				"K(a) is a vector space over K",
				"module_on(«scalars», «adjoinVectors»)",
				By(subK, subAdjoin, kInAdjoin, field_extension.ExtensionModuleOn.Read(L).At(K, adjoin)))
			adjoinField := arg.Have(
				"K(a) is a field in its own right",
				"field_on(restrict_field(L, field_adjoin(L, K, {a})))",
				By(subAdjoin, field.SubfieldFieldOn.Read(L).At(adjoin)))
			adjoinRing := field.RingOn.Read(adjoinField)
			powersInAdjoin := arg.Have(
				"K(a) holds a and is closed under the product, so it holds every power of a",
				"∀i:num. monoid_pow(L.mul, L.one, a, i) ∈ field_adjoin(L, K, {a})",
				By(aInAdjoin, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(adjoinRing))))
			basisImage := arg.Have(
				"B is the image of the numbers below d under i ↦ a ^ i",
				"B = image(«powerMap», {i:num | i < d})",
				BySets(basisDefined))
			basisInAdjoin := arg.Have(
				"so B lies in K(a)",
				"B ⊆ field_adjoin(L, K, {a})",
				BySets(basisDefined, powersInAdjoin))

			// The powers below d are independent over K.
			vanishing := arg.Have(
				"a vanishing combination of the powers below d with coefficients in K has every coefficient zero",
				Statement{
					Binders: "∀T:set(A). ∀c:(A → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ B",
						"∀x:A. x ∈ T ⇒ c(x) ∈ K",
						"module_sum(L.add, L.zero, T, λx:A. c(x) * x) = L.zero",
					},
					Conclusion: "∀x:A. x ∈ T ⇒ c(x) = L.zero",
				},
				Derive(func(b *Argument) {
					T, c := b.FixAs[Set[A]]("T"), b.FixAs[Fun[A, A]]("c")
					parts := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T consists of powers below d",
						"the coefficients lie in K",
						"the combination vanishes")
					finiteT, inBasis, coefficientsInK, vanishes := parts[0], parts[1], parts[2], parts[3]
					tInImage := b.Have(
						"T consists of powers a ^ i with i below d",
						"T ⊆ image(«powerMap», {i:num | i < d})",
						BySets(inBasis, basisImage))
					_, combination := b.ObtainAs[Fun[Nat, A]](
						"the combination is the value at a of the polynomial q over "+
							"K with coefficient c(a ^ i) at each exponent i < d of T",
						"∃q:(num → A). "+
							"    polynomial_over(K, q) ∧ "+
							"    polynomial_eval(q, a) = module_sum(L.add, L.zero, T, λx:A. c(x) * x) ∧ "+
							"    (∀i:num. "+
							"        q(i) = "+
							"        COND(i < d ∧ monoid_pow(L.mul, L.one, a, i) ∈ T, "+
							"            c(monoid_pow(L.mul, L.one, a, i)), "+
							"            L.zero))",
						By(
							subK,
							finiteT,
							tInImage,
							coefficientsInK,
							injective,
							CombinationOfPowers.Read(L).At(K, T, below, aM, c)))
					qFacts := b.Conjuncts(
						combination,
						"q is a polynomial over K",
						"whose value at a is the combination",
						"with coefficient c(a ^ i) at each exponent i < d of T")
					qOver, qValue, qCoefficients := qFacts[0], qFacts[1], qFacts[2]
					qPast := b.Have(
						"q vanishes from d on, its exponents lying below d",
						"vec⟨d⟩(q)",
						Unfold(vec_space.VecDef),
						b.ForEach(func(i *Expr[Nat]) Action {
							return By(qCoefficients.At(i), nat_order.NotLessThan.At(i, d))
						}))
					qZero := b.Have(
						"so q, vanishing at a, is the zero polynomial",
						"q = vec_zero",
						By(Normalized, qOver, qPast, qValue, vanishes, lowDegree))

					b.FixAs[A]("x")
					xIn := b.Assume()
					i, isPower := b.ObtainAs[Nat](
						"x is a power a ^ i with i below d",
						"∃i:num. i < d ∧ x = monoid_pow(L.mul, L.one, a, i)",
						BySets(xIn, inBasis, basisDefined))
					b.Show(
						"c(x) = c(a ^ i) is the coefficient q(i) of the zero polynomial",
						By(xIn, isPower, qCoefficients.At(i), qZero, vec_space.VecZeroDef))
				}))
			independent := arg.Have(
				"the powers below d are independent over K in K(a)",
				"module_independent(«scalars», «adjoinVectors», B)",
				By(basisInAdjoin, vanishing, linear_independence.ModuleIndependentDef))

			// The powers below d span K(a).
			spanTerm := arg.TermAs[Set[A]]("«spanOfB»")
			spanSubspace := arg.Have(
				"the span of the powers below d is a subspace of K(a)",
				"submodule(«scalars», «adjoinVectors», «spanOfB»)",
				By(basisInAdjoin, submodule.SpanSubmodule.Read(space).At(basisSet)))
			adjoinRingRecord := arg.Have(
				"restriction commutes with taking the underlying ring",
				"restrict_ring(field_ring(L), field_adjoin(L, K, {a})) = "+
					"field_ring(restrict_field(L, field_adjoin(L, K, {a})))",
				Simp(Fwd(field.FieldRingDef), Fwd(field.RestrictFieldDef), Fwd(module_record.RestrictRingDef)),
				Refl())
			adjoinRingFact := arg.Have(
				"K(a) is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), field_adjoin(L, K, {a})))",
				adjoinRingRecord.Rw(),
				By(adjoinRing))
			valuesInSpan := arg.Have(
				"the value at a of a polynomial over K is the value of its remainder by μ, so lies in the span",
				"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_eval(p, a) ∈ «spanOfB»",
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					pOver := b.Assume()
					s, r, division := b.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
						"divide p by μ over K: p = μ s + r, with r vanishing from d on",
						"∃s r:(num → A). "+
							"    polynomial_over(K, s) ∧ "+
							"    polynomial_over(K, r) ∧ "+
							"    vec⟨d⟩(r) ∧ "+
							"    p = vec_add(polynomial_mul(minimal_polynomial(L, K, a), s), r)",
						By(
							dDef,
							pOver,
							μOver,
							μMonic,
							polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(L)).At(μ),
							polynomial_division.DivisionExists.Read(fieldK).At(p, μ)))
					parts := b.Conjuncts(
						division,
						"s is a polynomial over K",
						"so is r",
						"r vanishes from d on",
						"p = μ s + r")
					sOver, rOver, rPast, pIs := parts[0], parts[1], parts[2], parts[3]
					overL := b.Have(
						"μ, s and r are polynomials over L",
						"polynomial_over(L.carrier, minimal_polynomial(L, K, a)) ∧ "+
							"polynomial_over(L.carrier, s) ∧ "+
							"polynomial_over(L.carrier, r)",
						By(kInL, μOver, sOver, rOver, polynomial.PolynomialOverMono))
					remainder := b.Have(
						"the value of p is the value of r, a being a root of μ",
						"polynomial_eval(p, a) = polynomial_eval(r, a)",
						By(overL, pIs, μRoot, polynomial_evaluation.DivisionValueAtRoot.Read(ring).At(p, μ, s, r, aM)))
					inSpan := b.Have(
						"r(a) lies in the span of the powers below d, r vanishing from d on",
						"polynomial_eval(r, a) ∈ «spanOfB»",
						By(
							subK,
							adjoinRingFact,
							kInAdjoin,
							aInAdjoin,
							rOver,
							basisDefined,
							PolynomialValueInSpan.Read(L).At(K, adjoin, a, proof.InhabitFrom(r, rPast))))
					b.Show(
						"so p(a) = r(a) lies in the span",
						remainder.Rw(),
						By(inSpan))
				}))
			imageInSpan := arg.Have(
				"K[a] lies in the span",
				"polynomial_image(field_ring(L), K, a) ⊆ «spanOfB»",
				Unfold(PolynomialImageDef),
				BySets(valuesInSpan))
			spanned := arg.Have(
				"K(a) = K[a], so the powers below d span K(a)",
				"«spanOfB» = field_adjoin(L, K, {a})",
				By(
					subK,
					aInL,
					algebraic,
					imageInSpan,
					AdjoinEqImage.Read(L).At(K, aM),
					submodule.SubmoduleSubset.Read(spanSubspace),
					set_order.SubsetAntisym.At(spanTerm, adjoin)))

			// There are d of them.
			sized := arg.Have(
				"there are d powers below d, i ↦ a ^ i being one-to-one there",
				"has_size(B, d)",
				By(
					basisImage,
					injective,
					num_segment.HasSizeBelowStrict.At(d),
					cardinality.HasSizeImageInj.At(power, below, d)))
			arg.Show(
				"independent and spanning K(a), the d powers below d are a basis of it",
				By(independent, spanned, sized, linear_independence.ModuleBasisDef))
		}),
})}

// AdjoinDegree — for an algebraic a, K(a) is a finite extension of K
// whose degree is the degree of the minimal polynomial. The powers of a
// below that degree are a basis of K(a) over K, as many as the degree,
// and a finite basis counts the degree of the extension it spans.
var AdjoinDegree = adjoinDegreeThm{family.Add(registry.ProofEntry{
	Name: "AdjoinDegree",
	Key:  "prop_4b5edb6029491110",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "finite_extension(L, K, field_adjoin(L, K, {a})) ∧ " +
			"extension_degree(L, K, field_adjoin(L, K, {a})) = polynomial_degree(minimal_polynomial(L, K, a))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]
			aM := arg.MemberOf[on.L](a, aInL)

			kOfA := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
			adjoined := arg.Conjuncts(
				arg.Have(
					"K(a) is a subfield of L holding K and a",
					"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
					By(subK, AdjoinElementSubfield.Read(L).At(K, aM))),
				"K(a) is a subfield of L",
				"holding K",
				"and a")
			subAdjoin, kInAdjoin := adjoined[0], adjoined[1]

			basisSet := arg.TermAs[Set[A]]("«powersBelowDegree»")
			basis := arg.Have(
				"the powers of a below the degree of μ are a basis of K(a) over K, as many as that degree",
				"module_basis(«scalars», «adjoinVectors», «powersBelowDegree») ∧ "+
					"has_size(«powersBelowDegree», polynomial_degree(minimal_polynomial(L, K, a)))",
				By(subK, algebraic, AdjoinPowerBasis.Read(L).At(K, aM)))
			counted := arg.Have(
				"so they are finitely many, and their number is the degree of μ",
				"finite(«powersBelowDegree») ∧ "+
					"card(«powersBelowDegree») = polynomial_degree(minimal_polynomial(L, K, a))",
				By(
					basis,
					cardinality.HasSizeDef.At(
						basisSet, arg.TermAs[Nat]("polynomial_degree(minimal_polynomial(L, K, a))"))))

			degree := arg.Have(
				"with that finite basis K(a) is finite over K, its degree the number of the powers",
				"finite_extension(L, K, field_adjoin(L, K, {a})) ∧ "+
					"extension_degree(L, K, field_adjoin(L, K, {a})) = card(«powersBelowDegree»)",
				By(
					subK,
					subAdjoin,
					kInAdjoin,
					counted,
					basis,
					field_extension.BasisDegree.Read(L).At(K, kOfA, basisSet)))
			arg.Show(
				"so K(a) is finite over K, of degree the degree of μ",
				By(degree, counted))
		}),
})}

// ---------------------------------------------------------------------------
// A transcendental element
// ---------------------------------------------------------------------------

// EvalInjectiveTranscendental — at an element transcendental over K,
// two polynomials over K with the same value are equal. The
// difference vec_add(L.add, vec_neg(L.neg, p), q) is a polynomial over K, the polynomials over the field
// K forming a ring; it is written vec_add(L.add, vec_neg(L.neg, p), q), inverse first, because that is
// the form the additive group's laws read (EqIffInKernel, InvMulEqOneOn).
// Evaluation at a is a ring homomorphism from the polynomials over L to
// L, so vec_add(L.add, vec_neg(L.neg, p), q), between two polynomials with the same value, lies in its
// kernel and vanishes at a. A nonzero polynomial over K vanishing at a
// would make a algebraic over K, so vec_add(L.add, vec_neg(L.neg, p), q) is the zero polynomial, and in
// the additive group of the polynomials over L that says p = q.
var EvalInjectiveTranscendental = evalInjectiveTranscendentalThm{family.Add(registry.ProofEntry{
	Name: "EvalInjectiveTranscendental",
	Key:  "prop_9e2f1289f3a7a01d",
	Reading: "Equality of polynomials is equality of coefficient sequences, both zero from some " +
		"index on. Transcendence is load-bearing: for an algebraic a the minimal polynomial and vec_zero " +
		"have the value zero. subfield(L, K) makes the difference of two polynomials over K one over K.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀p q:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"¬algebraic_over(L, K, a)",
			"polynomial_over(K, p)",
			"polynomial_over(K, q)",
			"polynomial_eval(p, a) = polynomial_eval(q, a)",
		},
		Conclusion: "p = q",
		Abbrev: Abbrev{
			{Name: "polynomialsOverL", Text: "{f:(num → A) | polynomial_over(L.carrier, f)}"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a *Expr[A],
			p, q *Expr[Fun[Nat, A]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is transcendental over K",
				"p is a polynomial over K",
				"so is q",
				"and the two take the same value at a")
			subK, aInL, transcendental, pOver, qOver, sameValue :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			ring := field.RingOn.Read(L)
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			polynomialsK, polynomialsL :=
				polynomial.PolynomialRingOn.Read(field.RingOn.Read(fieldK)), polynomial.PolynomialRingOn.Read(ring)

			// The difference vec_add(L.add, vec_neg(L.neg, p), q) is a polynomial over K vanishing at a.
			difference := arg.TermAs[Fun[Nat, A]]("vec_add(vec_neg(p), q)")
			differenceOver := arg.Have(
				"the difference -p + q is a polynomial over K, the polynomials over K forming a ring",
				"polynomial_over(K, vec_add(vec_neg(p), q))",
				By(pOver, qOver, comm_ring.AddIn.Read(polynomialsK), comm_ring.NegIn.Read(polynomialsK)))
			pm := proof.MemberOf(p, arg.Have(
				"p is a polynomial over L as well, a member of the ring of the polynomials over L",
				"p ∈ «polynomialsOverL»",
				By(kInL, pOver, polynomial.PolynomialOverMono)))
			qm := proof.MemberOf(q, arg.Have(
				"and so is q",
				"q ∈ «polynomialsOverL»",
				By(kInL, qOver, polynomial.PolynomialOverMono)))
			evaluation := arg.Have(
				"evaluation at a is a ring homomorphism from the polynomials over L to L",
				"ring_homomorphism(polynomial_ring(field_ring(L)), "+
					"    field_ring(L), "+
					"    λf:(num → A). polynomial_eval(f, a))",
				By(polynomial_evaluation.EvalHomomorphism.Read(ring).At(arg.MemberOf[on.L](a, aInL))))
			root := arg.Have(
				"p and q having the same value, -p + q lies in the kernel of the evaluation: it vanishes at a",
				"polynomial_eval(vec_add(vec_neg(p), q), a) = L.zero",
				By(
					sameValue,
					group_homomorphism.EqIffInKernel.Read(ring_homomorphism.AdditiveHomomorphism.Read(evaluation)).At(
						pm, qm),
					group_homomorphism.InKernel.At(
						arg.TermAs[A]("L.zero"),
						arg.TermAs[Set[Fun[Nat, A]]]("«polynomialsOverL»"),
						arg.TermAs[Fun[Fun[Nat, A], A]]("λf:(num → A). polynomial_eval(f, a)"),
						difference)))

			onlyZero := arg.Have(
				"a being transcendental over K, the only polynomial over K vanishing at a is the zero polynomial",
				"∀r:(num → A). polynomial_over(K, r) ∧ polynomial_eval(r, a) = L.zero ⇒ r = vec_zero",
				By(transcendental, AlgebraicOverDef))
			zeroDifference := arg.Have(
				"so -p + q is the zero polynomial",
				"vec_add(vec_neg(p), q) = vec_zero",
				By(onlyZero.At(difference), differenceOver, root))
			arg.Show(
				"-p + q is the zero of the additive group of the polynomials over L, which says p = q",
				By(
					zeroDifference,
					group.InvMulEqOneOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(polynomialsL))).At(
						pm, qm)))
		}),
})}

// TranscendentalPowersIndependent — the powers of an element transcendental
// over K are pairwise distinct and independent over K in L. Two powers
// a ^ i = a ^ j are the values at a of basis_vector(i) and
// basis_vector(j), polynomials over K, which are therefore equal, so
// i = j. So i ↦ a ^ i is one-to-one, and a vanishing combination of
// finitely many powers with coefficients c(x) in K is the value at a of
// the polynomial over K with coefficient c(a ^ i) at each exponent i
// (CombinationOfPowers), which is then the zero polynomial, a being
// transcendental: every c(x) is zero.
var TranscendentalPowersIndependent = transcendentalPowersIndependentThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalPowersIndependent",
	Key:  "prop_84a1dc6be0a29127",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"¬algebraic_over(L, K, a)",
		},
		Conclusion: "(∀i j:num. " +
			"    monoid_pow(L.mul, L.one, a, i) = monoid_pow(L.mul, L.one, a, j) ⇒ i = j) ∧ " +
			"module_independent(restrict_ring(field_ring(L), K), " +
			"    regular_module(field_ring(L)), " +
			"    monoid_powers(L.mul, L.one, a))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is transcendental over K")
			subK, aInL, transcendental := hyp[0], hyp[1], hyp[2]
			ring := field.RingOn.Read(L)
			aM := arg.MemberOf[on.L](a, aInL)
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			ringK := field.RingOn.Read(fieldK)

			// The powers are distinct.
			distinct := arg.Have(
				"a ^ i = a ^ j only for i = j",
				"∀i j:num. monoid_pow(L.mul, L.one, a, i) = monoid_pow(L.mul, L.one, a, j) ⇒ i = j",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					equal := b.Assume()
					xi, xj := b.TermAs[Fun[Nat, A]]("basis_vector(i)"), b.TermAs[Fun[Nat, A]]("basis_vector(j)")
					same := b.Have(
						"basis_vector(i) and basis_vector(j), polynomials over K, agree at a, so they are equal",
						"basis_vector(i) = basis_vector(j)",
						By(
							subK,
							transcendental,
							equal,
							polynomial.BasisVectorOver.Read(ringK).At(i),
							polynomial.BasisVectorOver.Read(ringK).At(j),
							polynomial_evaluation.EvalBasisVector.Read(ring).At(i, aM),
							polynomial_evaluation.EvalBasisVector.Read(ring).At(j, aM),
							EvalInjectiveTranscendental.Read(L).At(K, aM, xi, xj)))
					b.Show(
						"at i the first has coefficient one, the second zero unless i = j, and one ≠ zero",
						By(same, vec_space.BasisVectorDef, field.OneNotZeroOn.Read(L)))
				}))

			// The powers are independent: a vanishing combination is the value
			// at a of a polynomial over K, the zero polynomial.
			everyNumber := arg.TermAs[Set[Nat]]("𝕌")
			injective := arg.Have(
				"so i ↦ a ^ i is one-to-one",
				"injective_on(𝕌, «powerMap»)",
				By(distinct, functions.InjectiveOnDef))
			powersImage := arg.Have(
				"and the powers are its image",
				"monoid_powers(L.mul, L.one, a) = image(«powerMap», 𝕌)",
				BySets(comm_monoid.MonoidPowersDef))
			powersInL := arg.Have(
				"L holds a and is closed under the product, so it holds every power of a",
				"monoid_powers(L.mul, L.one, a) ⊆ L.carrier",
				Unfold(comm_monoid.MonoidPowersDef),
				BySets(aInL, At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), a)))
			vanishing := arg.Have(
				"a combination of finitely many powers of a with coefficients "+
					"in K vanishes only when every coefficient is zero",
				"∀T:set(A). ∀c:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ monoid_powers(L.mul, L.one, a) ∧ "+
					"    (∀x:A. x ∈ T ⇒ c(x) ∈ K) ∧ "+
					"    module_sum(L.add, L.zero, T, λx:A. c(x) * x) = L.zero ⇒ "+
					"    ∀x:A. x ∈ T ⇒ c(x) = L.zero",
				Derive(func(b *Argument) {
					T, c := b.FixAs[Set[A]]("T"), b.FixAs[Fun[A, A]]("c")
					parts := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T consists of powers of a",
						"the coefficients lie in K",
						"the combination vanishes")
					finiteT, inPowers, coefficientsInK, vanishes := parts[0], parts[1], parts[2], parts[3]
					tInImage := b.Have(
						"T lies in the image of i ↦ a ^ i",
						"T ⊆ image(«powerMap», 𝕌)",
						BySets(inPowers, powersImage))
					_, combination := b.ObtainAs[Fun[Nat, A]](
						"the combination is the value at a of the polynomial q "+
							"over K with coefficient c(a ^ i) at each exponent i of T",
						"∃q:(num → A). "+
							"    polynomial_over(K, q) ∧ "+
							"    polynomial_eval(q, a) = module_sum(L.add, L.zero, T, λx:A. c(x) * x) ∧ "+
							"    (∀i:num. "+
							"        q(i) = "+
							"        COND(i ∈ 𝕌 ∧ monoid_pow(L.mul, L.one, a, i) ∈ T, "+
							"            c(monoid_pow(L.mul, L.one, a, i)), "+
							"            L.zero))",
						By(
							subK,
							finiteT,
							tInImage,
							coefficientsInK,
							injective,
							CombinationOfPowers.Read(L).At(K, T, everyNumber, aM, c)))
					qFacts := b.Conjuncts(
						combination,
						"q is a polynomial over K",
						"whose value at a is the combination",
						"with coefficient c(a ^ i) at each exponent i of T")
					qOver, qValue, qCoefficients := qFacts[0], qFacts[1], qFacts[2]
					qZero := b.Have(
						"the combination vanishing, q is the zero polynomial, a being transcendental over K",
						"q = vec_zero",
						By(transcendental, qOver, qValue, vanishes, AlgebraicOverDef))

					b.FixAs[A]("x")
					xIn := b.Assume()
					i, isPower := b.ObtainAs[Nat](
						"x is a power a ^ i",
						"∃i:num. x = monoid_pow(L.mul, L.one, a, i)",
						BySets(xIn, inPowers, comm_monoid.MonoidPowersDef))
					b.Show(
						"c(x) = c(a ^ i) is the coefficient q(i) of the zero polynomial",
						By(xIn, isPower, qCoefficients.At(i), set_basic.InUniv.At(i), qZero, vec_space.VecZeroDef))
				}))
			arg.Show(
				"distinct, the powers are independent over K",
				By(distinct, powersInL, vanishing, linear_independence.ModuleIndependentDef))
		}),
})}

// EvalImageFreeOverK — at an element transcendental over K, the powers
// of a are distinct and a basis of K[a] over K. They are distinct and
// independent over K in L, and K[a], which holds them, shares the
// operations of L, so they are independent in K[a] too. K[a] is a ring
// holding K and a, so a vector space over K, and the value at a of a
// polynomial over K vanishing from n on lies in the span there of the
// powers below n (PolynomialValueInSpan), so in the span of all of them,
// which therefore holds K[a].
var EvalImageFreeOverK = evalImageFreeOverKThm{family.Add(registry.ProofEntry{
	Name: "EvalImageFreeOverK",
	Key:  "prop_7dce26ebe132898e",
	Reading: "K[a] is the module over K under the field's own operations, as " +
		"field_extension reads a subfield above K; it is no subfield here, K[a] being no field " +
		"for a transcendental a. The basis is the set of the powers, not a family indexed by " +
		"the exponents: the distinctness conjunct says each exponent gives its own member.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"¬algebraic_over(L, K, a)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), K), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), K, a)), " +
			"    monoid_powers(L.mul, L.one, a)) ∧ " +
			"(∀i j:num. monoid_pow(L.mul, L.one, a, i) = monoid_pow(L.mul, L.one, a, j) ⇒ i = j)",
		Abbrev: Abbrev{
			{Name: "imageVectors", Text: "restrict_module(regular_module(field_ring(L)), " +
				"    polynomial_image(field_ring(L), K, a))"},
			{Name: "imageSpan", Text: "module_span(«scalars», «imageVectors», monoid_powers(L.mul, L.one, a))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is transcendental over K")
			subK, aInL := hyp[0], hyp[1]
			aM := arg.MemberOf[on.L](a, aInL)
			inImage := arg.Have(
				"K[a] is the set of the values at a of the polynomials over K",
				"∀x:A. "+
					"    x ∈ polynomial_image(field_ring(L), K, a) ⇔ "+
					"    ∃p:(num → A). polynomial_over(K, p) ∧ x = polynomial_eval(p, a)",
				Unfold(PolynomialImageDef),
				SetTac())
			image := arg.TermAs[Set[A]]("polynomial_image(field_ring(L), K, a)")
			powerSet := arg.TermAs[Set[A]]("monoid_powers(L.mul, L.one, a)")
			imageFacts := arg.Conjuncts(
				GroupPremises(hyp[0], PolynomialImageRing.Read(L).At(K, aM)),
				"K[a] is a subring of L",
				"holding K",
				"and a",
				"inside K(a)")
			imageSubring, kInImage, aInImage := imageFacts[0], imageFacts[1], imageFacts[2]
			imageRing := arg.Have(
				"K[a] is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), polynomial_image(field_ring(L), K, a)))",
				By(imageSubring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(image)))
			free := arg.Conjuncts(
				GroupPremises(hyp[0], hyp[2], TranscendentalPowersIndependent.Read(L).At(K, aM)),
				"the powers of a are distinct",
				"and independent over K in L")
			distinct, independentInL := free[0], free[1]

			// K[a] is a vector space over K holding the powers, independent there as in L.
			vectorSpace := arg.Have(
				"K[a], a ring holding K, is a vector space over K",
				"module_on(«scalars», «imageVectors»)",
				By(subK, imageRing, kInImage, field_extension.RingExtensionModuleOn.Read(L).At(K, image)))
			powersInImage := arg.Have(
				"K[a] holds a and is closed under the product, so it holds every power of a",
				"monoid_powers(L.mul, L.one, a) ⊆ polynomial_image(field_ring(L), K, a)",
				Unfold(comm_monoid.MonoidPowersDef),
				BySets(aInImage, At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(imageRing)), a)))
			independent := arg.Have(
				"independence reads only the operations, which K[a] "+
					"shares with L: the powers are independent over K in K[a]",
				"module_independent(«scalars», «imageVectors», monoid_powers(L.mul, L.one, a))",
				By(
					arg.Unfolded(independentInL, linear_independence.ModuleIndependentDef),
					powersInImage,
					linear_independence.ModuleIndependentDef))

			// The powers span K[a]: the value of each polynomial lies in the span of finitely many of them.
			scalarRing := arg.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«imageVectors»")
			values := arg.Have(
				"the value at a of a polynomial over K lies in the span of the powers in K[a]",
				"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_eval(p, a) ∈ «imageSpan»",
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					pOver := b.Assume()
					parts := b.Conjuncts(
						b.Unfolded(pOver, polynomial.PolynomialOverDef),
						"p vanishes from some index on",
						"every coefficient of p lies in K")
					_, past := b.UnpackAs[Nat](parts[0], "n")
					belowSet, belowDefined := b.LetAs[Set[A]]("S", "{monoid_pow(L.mul, L.one, a, i) | i:num | i < n}")
					inBelowSpan := b.Have(
						"p vanishing from n on, p(a) lies in the span in K[a] of the set S of the powers below n",
						"polynomial_eval(p, a) ∈ module_span(«scalars», «imageVectors», S)",
						By(
							subK,
							imageRing,
							kInImage,
							aInImage,
							pOver,
							belowDefined,
							PolynomialValueInSpan.Read(L).At(K, image, a, proof.InhabitFrom(p, past))))
					belowInPowers := b.Have(
						"S consists of powers of a",
						"S ⊆ monoid_powers(L.mul, L.one, a)",
						BySets(belowDefined, comm_monoid.MonoidPowersDef))
					b.Show(
						"and the span of fewer vectors lies in the span of more",
						BySets(inBelowSpan, belowInPowers, submodule.SpanMono.At(scalarRing, vectors, belowSet, powerSet)))
				}))
			imageInSpan := arg.Have(
				"so K[a] lies in the span of the powers",
				"polynomial_image(field_ring(L), K, a) ⊆ «imageSpan»",
				BySets(inImage, values))
			spanSubspace := arg.Have(
				"the span of the powers in K[a] is a subspace of K[a]",
				"submodule(«scalars», «imageVectors», «imageSpan»)",
				By(powersInImage, submodule.SpanSubmodule.Read(vectorSpace)))
			spanned := arg.Have(
				"so the powers span K[a]",
				"«imageSpan» = polynomial_image(field_ring(L), K, a)",
				By(
					imageInSpan,
					submodule.SubmoduleSubset.Read(spanSubspace),
					set_order.SubsetAntisym.At(arg.TermAs[Set[A]]("«imageSpan»"), image)))
			arg.Show(
				"independent and spanning K[a], the powers are a basis of it, and they are distinct",
				By(independent, spanned, distinct, linear_independence.ModuleBasisDef))
		}),
})}

// TranscendentalInverse — the inverse of a transcendental element is
// transcendental, and the element is not zero. Every member of K is
// algebraic over K, zero among them, so a transcendental t is not zero.
// Were inv(t) algebraic over K, the subfield K(inv(t)) would be a finite
// extension of K; closed under inverses, it holds inv(inv(t)) = t, and t,
// lying in a finite extension of K, would be algebraic over K.
var TranscendentalInverse = transcendentalInverseThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalInverse",
	Key:  "prop_63c5d9e315e71eb3",
	Reading: "inv is total, with inv(zero) = zero, so the conjunct t ≠ zero is what makes inv(t) " +
		"the inverse of t. The argument reads only inv(inv(t)) = t, which holds at zero as well.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, K, t)",
		},
		Conclusion: "¬(t = L.zero) ∧ L.inv(t) ∈ L.carrier ∧ ¬algebraic_over(L, K, L.inv(t))",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := a.Conjuncts(
				h,
				"K is a subfield of L",
				"t lies in L",
				"t is transcendental over K")
			subK, tInL, transcendental := hyp[0], hyp[1], hyp[2]
			tm := a.MemberOf[on.L](t, tInL)
			inverse := field.InvIn.Read(L).At(tm)

			// t is not zero: zero, a member of K, is algebraic over K.
			zeroAlgebraic := a.Have(
				"zero lies in K, a subfield, so it is algebraic over K, as every member of K is",
				"algebraic_over(L, K, L.zero)",
				By(subK, field.SubfieldZero, MemberAlgebraic.Read(L).At(K, a.TermAs[A]("L.zero"))))
			nonzero := a.Have(
				"and t, transcendental, is not zero",
				"t ≠ L.zero",
				By(Normalized, transcendental, zeroAlgebraic))

			// K(inv(t)) is a subfield holding inv(t), so t = inv(inv(t)) as well.
			adjoin := a.TermAs[Set[A]]("field_adjoin(L, K, {L.inv(t)})")
			adjoined := a.Conjuncts(
				a.Have(
					"K(inv(t)) is a subfield of L holding K and inv(t)",
					"subfield(L, field_adjoin(L, K, {L.inv(t)})) ∧ "+
						"K ⊆ field_adjoin(L, K, {L.inv(t)}) ∧ "+
						"L.inv(t) ∈ field_adjoin(L, K, {L.inv(t)})",
					By(subK, AdjoinElementSubfield.Read(L).At(K, inverse))),
				"K(inv(t)) is a subfield of L",
				"holding K",
				"and inv(t)")
			subAdjoin, kInAdjoin, inverseIn := adjoined[0], adjoined[1], adjoined[2]
			inverseInverse := a.Have(
				"closed under inverses, K(inv(t)) holds inv(inv(t))",
				"L.inv(L.inv(t)) ∈ field_adjoin(L, K, {L.inv(t)})",
				By(subAdjoin, inverseIn, field.SubfieldInv))
			tIn := a.Have(
				"which is t",
				"t ∈ field_adjoin(L, K, {L.inv(t)})",
				By(inverseInverse, field.InvInvOn.Read(L).At(tm)))

			fromInverse := a.Have(
				"were inv(t) algebraic over K, K(inv(t)) would be finite over K, and t in it algebraic",
				"algebraic_over(L, K, L.inv(t)) ⇒ algebraic_over(L, K, t)",
				Derive(func(b *Argument) {
					algebraic := b.Assume()
					finite := b.Have(
						"inv(t) being algebraic, K(inv(t)) is a finite extension of K",
						"finite_extension(L, K, field_adjoin(L, K, {L.inv(t)}))",
						By(subK, algebraic, AdjoinDegree.Read(L).At(K, inverse)))
					b.Show(
						"t, lying in a finite extension of K, is algebraic over K",
						By(subK, subAdjoin, kInAdjoin, finite, tIn, FiniteExtensionAlgebraic.Read(L).At(K, adjoin, t)))
				}))
			a.Show(
				"t is not zero, inv(t) lies in L by the field's closure, and inv(t) is transcendental as t is",
				By(nonzero, inverse, fromInverse, transcendental))
		}),
})}

// TranscendentalSubfieldInfinite — a subfield E holding an element a
// transcendental over a subfield K is infinite: the powers of a are
// pairwise distinct (TranscendentalPowersIndependent), and E, closed under
// the product, holds every one of them.
var TranscendentalSubfieldInfinite = transcendentalSubfieldInfiniteThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalSubfieldInfinite",
	Key:  "prop_4956b0930643933a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"a ∈ E",
			"¬algebraic_over(L, K, a)",
		},
		Conclusion: "infinite(E)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, E *Expr[Set[A]],
		a *Expr[A],
		KField, EField, aInE, transcendental Fact,
	) {
		l := arg.TermAs[FieldOps[A]]("L")
		everyNumber := arg.TermAs[Set[Nat]]("𝕌")
		powerMap := arg.TermAs[Fun[Nat, A]]("«powerMap»")
		aInL := arg.Have(
			"a lies in L",
			"a ∈ L.carrier",
			BySets(EField, aInE, field.SubfieldSubset.At(l, E)))
		ring := arg.Have(
			"E is a commutative ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), E))",
			By(EField, field.SubfieldCommRing.Read(L).At(E)))
		injective := arg.Have(
			"the powers of a are pairwise distinct",
			"injective_on(𝕌, «powerMap»)",
			By(
				KField,
				transcendental,
				TranscendentalPowersIndependent.Read(L).At(K, arg.MemberOf[on.L](a, aInL)),
				functions.InjectiveOnDef))
		powersInE := arg.Have(
			"every power of a lies in E",
			"∀i:num. monoid_pow(L.mul, L.one, a, i) ∈ E",
			arg.ForEach(func(i *Expr[Nat]) Action {
				return By(aInE, At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), a, i))
			}))
		arg.Show(
			"so E holds an injective image of the naturals, which is infinite",
			By(
				injective,
				powersInE,
				set_image.ImageSubsetIff.At(powerMap, everyNumber, E),
				num_segment.Infinite,
				finite_set.InfiniteImage.At(powerMap, everyNumber),
				finite_set.InfiniteSuperset.At(arg.TermAs[Set[A]]("image(«powerMap», 𝕌)"), E)))
	}),
})}

// ---------------------------------------------------------------------------
// The algebraic elements: finite extensions, and the subfield they form
// ---------------------------------------------------------------------------

// FiniteExtensionAlgebraic — every element of a finite extension is
// algebraic: its powers cannot all be independent. Were a transcendental
// over K, its powers would be pairwise distinct and independent over K in
// L, so independent inside M, which holds them; an independent set in the
// finite-dimensional M is finite, while the powers, one for each number,
// are infinitely many.
var FiniteExtensionAlgebraic = finiteExtensionAlgebraicThm{family.Add(registry.ProofEntry{
	Name: "FiniteExtensionAlgebraic",
	Key:  "prop_c6de1a579dbe1fa5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
			"a ∈ M",
		},
		Conclusion: "algebraic_over(L, K, a)",
		Abbrev: Abbrev{
			{Name: "fieldVectors", Text: "regular_module(field_ring(L))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"M is a subfield of L",
				"K lies in M",
				"M is finite over K",
				"a lies in M")
			subK, subM, kInM, finiteM, aInM := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			transcendental := arg.SupposeNot()

			mInL := arg.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subM, field.SubfieldSubset))
			aInL := arg.Have(
				"so a lies in L",
				"a ∈ L.carrier",
				BySets(mInL, aInM))
			free := arg.Conjuncts(
				arg.Have(
					"the powers of the transcendental a are distinct and independent over K in L",
					"(∀i j:num. monoid_pow(L.mul, L.one, a, i) = monoid_pow(L.mul, L.one, a, j) ⇒ i = j) ∧ "+
						"module_independent(«scalars», «fieldVectors», monoid_powers(L.mul, L.one, a))",
					By(
						subK,
						transcendental,
						TranscendentalPowersIndependent.Read(L).At(K, arg.MemberOf[on.L](a, aInL)))),
				"the powers are pairwise distinct",
				"and independent over K in L")
			distinct, independentInL := free[0], free[1]

			fieldM := arg.Have(
				"M is a field in its own right",
				"field_on(restrict_field(L, M))",
				By(subM, field.SubfieldFieldOn.Read(L).At(M)))
			powersInM := arg.Have(
				"M is closed under the product and holds a, so it holds every power of a",
				"monoid_powers(L.mul, L.one, a) ⊆ M",
				Unfold(comm_monoid.MonoidPowersDef),
				BySets(aInM, At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(fieldM))), a)))
			powerSet := arg.TermAs[Set[A]]("monoid_powers(L.mul, L.one, a)")
			independentM := arg.Have(
				"independence reads only the operations, which M "+
					"shares with L: the powers are independent inside M",
				"module_independent(«scalars», "+
					"    restrict_module(regular_module(field_ring(L)), M), "+
					"    monoid_powers(L.mul, L.one, a))",
				By(
					independentInL,
					powersInM,
					mInL,
					linear_independence.IndependentRestrict.At(
						arg.TermAs[module_record.RingOps[A]]("«scalars»"),
						arg.TermAs[module_record.ModuleOps[A, A]]("«fieldVectors»"),
						M,
						powerSet)))

			space := arg.Have(
				"M is a vector space over K",
				"module_on(«scalars», restrict_module(regular_module(field_ring(L)), M))",
				By(subK, subM, kInM, field_extension.ExtensionModuleOn.Read(L).At(K, M)))
			inv := arg.TermAs[Fun[A, A]]("L.inv")
			finiteSpace := arg.Simplified(finiteM, Fwd(field_extension.FiniteExtensionDef))
			finitelyMany := arg.Have(
				"an independent set in the finite-dimensional M is finite",
				"finite(monoid_powers(L.mul, L.one, a))",
				By(
					subK,
					field.SubfieldRingSubfield.Read(L).At(K, K),
					finiteSpace,
					independentM,
					module_dimension.IndependentBound.Read(space).At(inv, powerSet)))

			image := arg.Have(
				"the powers are the image of the numbers under i ↦ a ^ i",
				"monoid_powers(L.mul, L.one, a) = image(«powerMap», 𝕌)",
				BySets(comm_monoid.MonoidPowersDef))
			injective := arg.Have(
				"the powers being pairwise distinct, i ↦ a ^ i is one-to-one",
				"injective_on(𝕌, «powerMap»)",
				By(distinct, functions.InjectiveOnDef))
			infinitelyMany := arg.Have(
				"so there are infinitely many of them, as there are numbers",
				"infinite(monoid_powers(L.mul, L.one, a))",
				By(
					injective,
					image,
					num_segment.Infinite,
					finite_set.InfiniteImage.At(arg.TermAs[Fun[Nat, A]]("«powerMap»"), arg.TermAs[Set[Nat]]("𝕌"))))
			arg.Show(
				"the powers cannot be finitely and infinitely many at once",
				By(finitelyMany, infinitelyMany, finite_set.InfiniteDef.At(powerSet)))
		}),
})}

// AlgebraicIffFinite — an element is algebraic over K exactly when K(a)
// is a finite extension of K: AdjoinDegree gives finiteness, and every
// member of a finite extension is algebraic.
var AlgebraicIffFinite = algebraicIffFiniteThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicIffFinite",
	Key:  "prop_b95cb1273d75585a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
		},
		Conclusion: "algebraic_over(L, K, a) ⇔ finite_extension(L, K, field_adjoin(L, K, {a}))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], subK Fact, a *Member[A, on.L]) {
			arg.Iff()
			arg.Forward(
				"an algebraic element generates a finite extension",
				func(b *Argument, algebraic Fact) {
					b.Show(
						"K(a) is finite over K",
						By(subK, algebraic, AdjoinDegree.Read(L).At(K, a)))
				})
			arg.Backward(
				"a member of the finite extension K(a) is algebraic",
				func(b *Argument, finite Fact) {
					adjoin := b.Have(
						"K(a) is a subfield of L containing K and a",
						"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
						By(subK, AdjoinElementSubfield.Read(L).At(K, a)))
					b.Show(
						"a is algebraic over K, since it lies in the finite extension K(a)",
						By(
							subK,
							adjoin,
							finite,
							FiniteExtensionAlgebraic.Read(L).At(K, b.TermAs[Set[A]]("field_adjoin(L, K, {a})"), a)))
				})
		}),
})}

// MemberAlgebraic — every member of K is algebraic over K: k is a root of
// x - k. That polynomial is the variable plus the constant -k, both over K;
// its coefficient at 1 is one, so it is not zero, and its value at k is
// k ^ 1 + -k = k + -k = zero.
var MemberAlgebraic = memberAlgebraicThm{family.Add(registry.ProofEntry{
	Name: "MemberAlgebraic",
	Key:  "prop_3050f0b1b4d9ac4d",
	Reading: "subfield(L, K) puts -k and one in K, so x - k is a polynomial " +
		"over K; the field's one ≠ zero keeps it from being the zero polynomial.",

	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀k:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"k ∈ K",
		},
		Conclusion: "algebraic_over(L, K, k)",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], k *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"k lies in K")
			subK, kInK := hyp[0], hyp[1]
			ring := field.RingOn.Read(L)
			fieldK := arg.Have(
				"K is a field in its own right",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			ringK := field.RingOn.Read(fieldK)
			kInL := arg.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			kMember := arg.MemberOf[on.L](k, arg.Have(
				"so k lies in L",
				"k ∈ L.carrier",
				BySets(kInL, kInK)))
			negMember := comm_ring.NegIn.Read(ring).At(kMember)
			first := arg.TermAs[Nat]("1")
			variable, constant :=
				arg.TermAs[Fun[Nat, A]]("basis_vector(1)"),
				arg.TermAs[Fun[Nat, A]]("vec_scalar_mul(-k, basis_vector(0))")

			// x - k is a nonzero polynomial over K.
			negInK := arg.Have(
				"-k lies in K, a subfield",
				"-k ∈ K",
				By(subK, kInK, field.SubfieldNeg))
			constantOver := arg.Have(
				"the constant -k is a polynomial over K, the polynomials over K a module over K",
				"polynomial_over(K, vec_scalar_mul(-k, basis_vector(0)))",
				BySets(
					negInK,
					polynomial.BasisVectorOver.Read(ringK),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringK))))
			over := arg.Have(
				"and so is its sum with the variable x",
				"polynomial_over(K, vec_add(basis_vector(1), vec_scalar_mul(-k, basis_vector(0))))",
				BySets(
					constantOver,
					polynomial.BasisVectorOver.Read(ringK).At(first),
					comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ringK))))
			coefficient := arg.Have(
				"its coefficient at 1 is one + -k * zero = one",
				"(vec_add(basis_vector(1), vec_scalar_mul(-k, basis_vector(0))))(1) = L.one",
				Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
				ByArith(ring, kMember))
			nonzero := arg.Have(
				"so x - k is not zero, one ≠ zero",
				"¬(vec_add(basis_vector(1), vec_scalar_mul(-k, basis_vector(0))) = vec_zero)",
				By(field.OneNotZeroOn.Read(L), coefficient, vec_space.VecZeroDef))

			// x - k vanishes at k.
			constantOverL := arg.Have(
				"the constant -k is a polynomial over L as well",
				"polynomial_over(L.carrier, vec_scalar_mul(-k, basis_vector(0)))",
				By(kInL, constantOver, polynomial.PolynomialOverMono))
			root := arg.Have(
				"x - k vanishes at k",
				"polynomial_eval(vec_add(basis_vector(1), vec_scalar_mul(-k, basis_vector(0))), k) = L.zero",
				CalcEq(
					Leg(
						arg.Term(
							"polynomial_eval(basis_vector(1), k) + polynomial_eval(vec_scalar_mul(-k, basis_vector(0)), k)"),
						"evaluation at k adds",
						By(
							constantOverL,
							polynomial.BasisVectorOver.Read(ring).At(first),
							polynomial_evaluation.EvalAdd.Read(ring).At(variable, constant, kMember))),
					Leg(
						arg.Term("monoid_pow(L.mul, L.one, k, 1) + -k"),
						"x takes the value k ^ 1 and the constant -k the value -k",
						By(
							polynomial_evaluation.EvalBasisVector.Read(ring).At(first, kMember),
							polynomial_evaluation.EvalConstant.Read(ring).At(negMember, kMember))),
					FinalLeg(
						"which is k + -k = zero",
						ByArith(ring, kMember)),
				))
			arg.Show(
				"k is algebraic over K, a root of x - k",
				Simp(Fwd(AlgebraicOverDef)),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Nat, A]]("vec_add(basis_vector(1), vec_scalar_mul(-k, basis_vector(0)))"))
					b.Show(
						"x - k is a nonzero polynomial over K vanishing at k",
						By(over, nonzero, root))
				}))
		}),
})}

// AlgebraicOverMono — an element algebraic over K is algebraic over any
// larger set: the same nonzero polynomial still vanishes at it.
var AlgebraicOverMono = algebraicOverMonoThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverMono",
	Key:  "prop_c961ce6d737e350",
	Reading: "K ⊆ M is all that is asked of the two sets: polynomial_over " +
		"is monotone in its coefficient set, so neither need be a subfield.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A.",
		Hypotheses: []string{
			"K ⊆ M",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "algebraic_over(L, M, a)",
	},
		func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K lies in M",
				"a is algebraic over K")
			inclusion, algebraic := hyp[0], hyp[1]
			p, vanishing := arg.UnpackAs[Fun[Nat, A]](arg.Unfolded(algebraic, AlgebraicOverDef), "p")
			overM := arg.Have(
				"the same polynomial has its coefficients in M",
				"polynomial_over(M, p)",
				By(inclusion, vanishing, polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), K, M, p)))
			arg.Show(
				"the same nonzero polynomial witnesses algebraicity over M",
				Simp(Fwd(AlgebraicOverDef)),
				Derive(func(b *Argument) {
					b.Take(p)
					b.Show(
						"p is nonzero and vanishes at a",
						By(vanishing, overM))
				}))
		}),
})}

// AdjoinOfSubset — adjoining to a subfield points it already holds changes
// nothing: the subfield is one of the subfields met, and it lies in each.
var AdjoinOfSubset = adjoinOfSubsetThm{family.Add(registry.ProofEntry{
	Name: "AdjoinOfSubset",
	Key:  "prop_a69c3174750a1ea1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"S ⊆ K",
		},
		Conclusion: "field_adjoin(L, K, S) = K",
	}, func(a *Argument, L field.FieldFact[on.L], K, S *Expr[Set[A]], subK, sInK Fact) {
		a.Show(
			"K is among the subfields met, so the meet lies in K, and the meet holds K",
			BySets(
				subK,
				sInK,
				field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K),
				AdjoinSubfield.Read(L).At(K, S),
				AdjoinLeast.Read(L).At(K, S, K)))
	}),
})}

// AdjoinInsert — adjoining one more point a to S adjoins S first and a
// after it: K(S)(a) holds K and all of insert(a, S), and K(insert(a, S))
// holds K(S) and a, so leastness gives each inclusion.
var AdjoinInsert = adjoinInsertThm{family.Add(registry.ProofEntry{
	Name: "AdjoinInsert",
	Key:  "prop_d6fbd2e2f4b9148d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A). ∀a:A.",
		Hypotheses: []string{
			"K ⊆ L.carrier",
			"S ⊆ L.carrier",
			"a ∈ L.carrier",
		},
		Conclusion: "field_adjoin(L, K, insert(a, S)) = field_adjoin(L, field_adjoin(L, K, S), {a})",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, S *Expr[Set[A]],
		a *Member[A, on.L],
		kInL, sInL Fact,
	) {
		C, CDef := arg.LetAs[Set[A]]("C", "field_adjoin(L, K, S)")
		D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, K, insert(a, S))")
		E, EDef := arg.LetAs[Set[A]]("E", "field_adjoin(L, C, {a})")
		adjoinS := arg.Have(
			"C = K(S) is a subfield holding K and S",
			"subfield(L, C) ∧ K ⊆ C ∧ S ⊆ C",
			By(Normalized, kInL, sInL, CDef, AdjoinSubfield.Read(L).At(K, S)))
		adjoinInserted := arg.Have(
			"D = K(insert(a, S)) is a subfield holding K and every point of insert(a, S)",
			"subfield(L, D) ∧ K ⊆ D ∧ insert(a, S) ⊆ D",
			BySets(kInL, sInL, a, DDef, AdjoinSubfield.Read(L).At(K, arg.TermAs[Set[A]]("insert(a, S)"))))
		adjoinA := arg.Have(
			"E = C(a) is a subfield holding C and a",
			"subfield(L, E) ∧ C ⊆ E ∧ a ∈ E",
			By(Normalized, EDef, adjoinS, AdjoinElementSubfield.Read(L).At(C, a)))
		arg.Show(
			"leastness of each adjunction gives both inclusions",
			BySets(
				CDef,
				DDef,
				EDef,
				adjoinS,
				adjoinInserted,
				adjoinA,
				AdjoinLeast.Read(L).At(K, S, D),
				AdjoinLeast.Read(L).At(C, arg.TermAs[Set[A]]("{a}"), D),
				AdjoinLeast.Read(L).At(K, arg.TermAs[Set[A]]("insert(a, S)"), E)))
	}),
})}

// FiniteAdjoinStep — a finite extension C of K stays a finite extension of K
// when a point algebraic over C is adjoined: that point makes C(x) finite
// over C, and the tower law composes the two extensions.
var FiniteAdjoinStep = finiteAdjoinStepThm{family.Add(registry.ProofEntry{
	Name: "FiniteAdjoinStep",
	Key:  "prop_545bb7ddf7389b74",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K C:set(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, C)",
			"K ⊆ C",
			"finite_extension(L, K, C)",
			"x ∈ L.carrier",
			"algebraic_over(L, C, x)",
		},
		Conclusion: "subfield(L, field_adjoin(L, C, {x})) ∧ " +
			"C ⊆ field_adjoin(L, C, {x}) ∧ " +
			"finite_extension(L, K, field_adjoin(L, C, {x}))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, C *Expr[Set[A]],
		x *Member[A, on.L],
		subK, subC, kInC, finiteC, algebraicX Fact,
	) {
		D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, C, {x})")
		adjoinX := arg.Have(
			"D = C(x) is a subfield of L holding C",
			"subfield(L, D) ∧ C ⊆ D",
			By(Normalized, DDef, subC, AdjoinElementSubfield.Read(L).At(C, x)))
		finiteX := arg.Have(
			"x is algebraic over C, so D is finite over C",
			"finite_extension(L, C, D)",
			By(Normalized, DDef, subC, algebraicX, AdjoinDegree.Read(L).At(C, x)))
		arg.Show(
			"the tower law makes D finite over K",
			By(DDef, subK, subC, kInC, finiteC, adjoinX, finiteX, field_extension.TowerLaw.Read(L).At(K, C, D)))
	}),
})}

// AdjoinTwoFinite — adjoining two algebraic elements one after the other
// gives a finite extension of K: K(a) is finite over K, b stays algebraic
// over it, and adjoining b keeps the extension finite.
var AdjoinTwoFinite = adjoinTwoFiniteThm{family.Add(registry.ProofEntry{
	Name: "AdjoinTwoFinite",
	Key:  "prop_e469a7894b205494",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a b:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"b ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"algebraic_over(L, K, b)",
		},
		Conclusion: "finite_extension(L, K, field_adjoin(L, field_adjoin(L, K, {a}), {b}))",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a, b *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"b lies in L",
				"a is algebraic over K",
				"b is algebraic over K")
			subK, aInL, bInL, algebraicA, algebraicB := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			aMember, bMember := arg.MemberOf[on.L](a, aInL), arg.MemberOf[on.L](b, bInL)
			E := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
			adjoinA := arg.Have(
				"K(a) is a subfield of L containing K",
				"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a})",
				By(subK, AdjoinElementSubfield.Read(L).At(K, aMember)))
			finiteA := arg.Have(
				"K(a) is finite over K, since a is algebraic",
				"finite_extension(L, K, field_adjoin(L, K, {a}))",
				By(subK, algebraicA, AdjoinDegree.Read(L).At(K, aMember)))
			algebraicOverE := arg.Have(
				"b is algebraic over the larger coefficient field K(a)",
				"algebraic_over(L, field_adjoin(L, K, {a}), b)",
				By(adjoinA, algebraicB, AlgebraicOverMono.Read(L).At(K, E, b)))
			arg.Show(
				"so adjoining b keeps K(a)(b) a finite extension of K",
				By(subK, adjoinA, finiteA, algebraicOverE, FiniteAdjoinStep.Read(L).At(K, E, bMember)))
		}),
})}

// FiniteAlgebraicAdjoin — finitely many algebraic elements generate a
// finite extension: adjoining one point at a time gives a tower of finite
// simple extensions.
var FiniteAlgebraicAdjoin = finiteAlgebraicAdjoinThm{family.Add(registry.ProofEntry{
	Name: "FiniteAlgebraicAdjoin",
	Key:  "prop_76b8015bd7040eb4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite(S)",
			"S ⊆ L.carrier",
			"∀x:A. x ∈ S ⇒ algebraic_over(L, K, x)",
		},
		Conclusion: "finite_extension(L, K, field_adjoin(L, K, S))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K, S *Expr[Set[A]],
		subK, finiteS, sInL, algebraic Fact,
	) {
		a.Show(
			"by induction, every finite set of points of L algebraic "+
				"over K generates a finite extension of K, and S is one",
			ByInduction(
				finite_set.FiniteInduct,
				finiteS,
				Generalizing(sInL, algebraic),
				Case(
					"no point adjoined: K(∅) = K, and K is finite over itself",
					BySets(
						subK,
						AdjoinOfSubset.Read(L).At(K, a.TermAs[Set[A]]("∅")),
						field_extension.ExtensionOverItself.Read(L).At(K))),
				Case(
					"one more algebraic point x adjoined to the smaller set s",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						s := b.FixAs[Set[A]]("s")
						inductive := b.Assume()
						enlarged := b.Assume()
						C, CDef := b.LetAs[Set[A]]("C", "field_adjoin(L, K, s)")
						_, DDef := b.LetAs[Set[A]]("D", "field_adjoin(L, C, {x})")
						smallerAndPoint := b.Have(
							"the smaller set s and the new point lie in L and are algebraic over K",
							"s ⊆ L.carrier ∧ x ∈ L.carrier ∧ algebraic_over(L, K, x) ∧ (∀y:A. y ∈ s ⇒ algebraic_over(L, K, y))",
							BySets(enlarged))
						finiteC := b.Have(
							"the smaller set s generates a finite extension C of K",
							"K ⊆ L.carrier ∧ subfield(L, C) ∧ K ⊆ C ∧ finite_extension(L, K, C)",
							By(
								CDef,
								inductive,
								subK,
								smallerAndPoint,
								field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), K),
								AdjoinSubfield.Read(L).At(K, s)))
						algebraicOverC := b.Have(
							"the new point is algebraic over C",
							"algebraic_over(L, C, x)",
							By(finiteC, smallerAndPoint, AlgebraicOverMono.Read(L).At(K, C, x)))
						finiteD := b.Have(
							"adjoining the new point keeps the extension finite over K",
							"finite_extension(L, K, D)",
							By(
								Normalized,
								DDef,
								subK,
								finiteC,
								smallerAndPoint,
								algebraicOverC,
								FiniteAdjoinStep.Read(L).AsFact().At(K, C, x)))
						insertIsSuccessive := b.Have(
							"adjoining the enlarged set is the successive simple adjunction",
							"field_adjoin(L, K, insert(x, s)) = D",
							By(Normalized, CDef, DDef, finiteC, smallerAndPoint, AdjoinInsert.Read(L).AsFact().At(K, s, x)))
						b.Show(
							"adjoining the enlarged set is that finite extension of K",
							By(Normalized, insertIsSuccessive, finiteD))
					}))))
	}),
})}

// AdjoinAlgebraicOver — an element of K(S) is algebraic over a subfield B
// holding K when S is a finite set of elements algebraic over B: K(S) lies
// in B(S), which is a finite extension of B.
var AdjoinAlgebraicOver = adjoinAlgebraicOverThm{family.Add(registry.ProofEntry{
	Name: "AdjoinAlgebraicOver",
	Key:  "prop_9531278ff84dfb85",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K B S:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, B)",
			"K ⊆ B",
			"finite(S)",
			"S ⊆ L.carrier",
			"∀s:A. s ∈ S ⇒ algebraic_over(L, B, s)",
			"z ∈ field_adjoin(L, K, S)",
		},
		Conclusion: "algebraic_over(L, B, z)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, B, S *Expr[Set[A]], z *Expr[A],
			bSubfield, kInB, finite, inside, algebraic, zIn Fact) {
			generated := a.TermAs[Set[A]]("field_adjoin(L, B, S)")
			adjoined := a.Have(
				"B(S) is a subfield holding B and S",
				"subfield(L, field_adjoin(L, B, S)) ∧ B ⊆ field_adjoin(L, B, S) ∧ S ⊆ field_adjoin(L, B, S)",
				By(bSubfield, inside, field.SubfieldSubset, AdjoinSubfield.Read(L).At(B, S)))
			finiteOver := a.Have(
				"K(S) lies in B(S), a subfield holding K and S, so z does; and B(S) is a finite extension of B",
				"z ∈ field_adjoin(L, B, S) ∧ finite_extension(L, B, field_adjoin(L, B, S))",
				BySets(
					finite,
					algebraic,
					zIn,
					bSubfield,
					inside,
					kInB,
					adjoined,
					AdjoinLeast.Read(L).At(K, S, generated),
					FiniteAlgebraicAdjoin.Read(L).At(B, S)))
			a.Show(
				"an element of a finite extension of B is algebraic over B",
				By(bSubfield, finiteOver, adjoined, FiniteExtensionAlgebraic.Read(L).At(B, generated, z)))
		}),
})}

// AlgebraicElementsSubfield — the elements algebraic over K form a
// subfield holding K: any two of them, a and b, lie in their common finite
// extension K(a)(b) of K, a subfield whose members are all algebraic, and it
// holds a + b, a * b, -a and inv(a).
var AlgebraicElementsSubfield = algebraicElementsSubfieldThm{family.Add(registry.ProofEntry{
	Name:    "AlgebraicElementsSubfield",
	Key:     "prop_4076d103ef69273b",
	Reading: "inv(zero) = zero makes the inverse closure at zero automatic.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
		},
		Conclusion: "subfield(L, algebraic_elements(L, K)) ∧ K ⊆ algebraic_elements(L, K)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteMembers := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite_extension(L, K, M)",
			},
			Conclusion: "M ⊆ algebraic_elements(L, K)",
		}, func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], h Fact) {
			record := arg.TermAs[FieldOps[A]]("L")
			arg.Show(
				"every member of the finite extension M lies in L and is algebraic over K",
				BySets(
					L,
					h,
					field.SubfieldSubset.At(record, M),
					At(FiniteExtensionAlgebraic, record, K, M),
					AlgebraicElementsDef.At(record, K)))
		})
		return ctx.Theorem(headline,
			func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], subK Fact) {
				record := arg.TermAs[FieldOps[A]]("L")
				C, cDef := arg.LetAs[Set[A]]("C", "algebraic_elements(L, K)")
				elements := AlgebraicElementsDef.At(record, K)
				inL := arg.Have(
					"the algebraic elements under consideration lie in L",
					"C ⊆ L.carrier",
					BySets(cDef, elements))
				containsK := arg.Have(
					"every element of K is algebraic over K",
					"K ⊆ C",
					BySets(L, cDef, elements, subK, field.SubfieldSubset.At(record, K), At(MemberAlgebraic, record, K)))
				identities := arg.Have(
					"zero and one lie in K and hence in C",
					"L.zero ∈ C ∧ L.one ∈ C",
					BySets(subK, containsK, field.SubfieldZero.At(record, K), field.SubfieldOne.At(record, K)))
				closed := arg.Have(
					"any a, b in C lie in a subfield H ⊆ C, their common finite "+
						"extension K(a)(b), so the operations on them stay in C",
					"∀a b:A. a ∈ C ∧ b ∈ C ⇒ a + b ∈ C ∧ a * b ∈ C ∧ -a ∈ C ∧ L.inv(a) ∈ C",
					Derive(func(c *Argument) {
						a, b := c.FixAs[A]("a"), c.FixAs[A]("b")
						members := c.Assume()
						algebraic := c.Have(
							"a and b are algebraic over K",
							"algebraic_over(L, K, a) ∧ algebraic_over(L, K, b)",
							BySets(cDef, elements, members))
						am := c.MemberOf[on.L](a, c.Have(
							"a lies in L",
							"a ∈ L.carrier",
							BySets(inL, members)))
						bm := c.MemberOf[on.L](b, c.Have(
							"b lies in L",
							"b ∈ L.carrier",
							BySets(inL, members)))
						E, eDef := c.LetAs[Set[A]]("E", "field_adjoin(L, K, {a})")
						H, hDef := c.LetAs[Set[A]]("H", "field_adjoin(L, E, {b})")
						adjoinA := c.Have(
							"K(a) is a subfield containing K and a",
							"subfield(L, E) ∧ K ⊆ E ∧ a ∈ E",
							By(Normalized, eDef, subK, AdjoinElementSubfield.Read(L).At(K, am)))
						adjoinB := c.Have(
							"K(a)(b) is a subfield containing K(a) and b",
							"subfield(L, H) ∧ E ⊆ H ∧ b ∈ H",
							By(Normalized, hDef, adjoinA, AdjoinElementSubfield.Read(L).At(E, bm)))
						finite := c.Have(
							"adjoining the two algebraic elements gives a finite extension of K",
							"finite_extension(L, K, H)",
							By(Normalized, eDef, hDef, subK, algebraic, AdjoinTwoFinite.Read(L).At(K, am, bm)))
						contains := c.Have(
							"the common finite extension contains K and a",
							"K ⊆ H ∧ a ∈ H",
							BySets(adjoinA, adjoinB))
						algebraicField := c.Have(
							"every member of the common finite extension is algebraic over K",
							"H ⊆ C",
							By(Normalized, L, cDef, subK, contains, adjoinB, finite, At(finiteMembers, record, K, H)))
						operations := c.Have(
							"the subfield H holds the sum, the product, the negative and the inverse",
							"a + b ∈ H ∧ a * b ∈ H ∧ -a ∈ H ∧ L.inv(a) ∈ H",
							By(
								contains,
								adjoinB,
								field.SubfieldAdd.At(record, H, a, b),
								field.SubfieldMul.At(record, H, a, b),
								field.SubfieldNeg.At(record, H, a),
								field.SubfieldInv.At(record, H, a)))
						c.Show(
							"and H lies in C",
							BySets(algebraicField, operations))
					}))
				arg.Show(
					"these closure properties make C a subfield containing K",
					By(cDef, closed, inL, containsK, identities, field.SubfieldDef.At(record, C)))
			})
	}),
})}

// AlgebraicOverTrans — a point algebraic over algebraic points is
// algebraic over the base field: the finitely many nonzero coefficients
// of one annihilating polynomial generate a finite extension H of K, and
// the same polynomial makes x algebraic over H, so H(x) is finite over K.
var AlgebraicOverTrans = algebraicOverTransThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverTrans",
	Key:  "prop_e9692cd2a6a8fc26",
	Reading: "E need not hold K nor be a subfield: only the finitely many " +
		"coefficients of one polynomial over E are read, each algebraic over K. " +
		"With E empty no polynomial is over E, and the hypothesis on x is false.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E:set(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"E ⊆ L.carrier",
			"∀y:A. y ∈ E ⇒ algebraic_over(L, K, y)",
			"x ∈ L.carrier",
			"algebraic_over(L, E, x)",
		},
		Conclusion: "algebraic_over(L, K, x)",
	}, func(arg *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], x *Expr[A], h Fact) {
		parts := arg.Conjuncts(
			h,
			"K is a subfield of L",
			"E lies in L",
			"every point of E is algebraic over K",
			"x lies in L",
			"x is algebraic over E")
		subK, eInL, algebraicE, xInL, overE := parts[0], parts[1], parts[2], parts[3], parts[4]
		record, zero := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[A]("L.zero")
		xm := arg.MemberOf[on.L](x, xInL)
		q, vanishing := arg.ObtainAs[Fun[Nat, A]](
			"choose a nonzero polynomial over E vanishing at x",
			"∃q:(num → A). polynomial_over(E, q) ∧ q ≠ vec_zero ∧ polynomial_eval(q, x) = L.zero",
			By(overE, AlgebraicOverDef.At(record, E, x)))
		U, uDef := arg.LetAs[Set[Nat]]("U", "fun_support(L.zero, q)")
		S, sDef := arg.LetAs[Set[A]]("S", "image(q, U)")
		support := arg.Have(
			"q has finite nonzero support and every coefficient lies in E",
			"finite(U) ∧ (∀i:num. q(i) ∈ E)",
			By(Normalized, uDef, vanishing, polynomial.PolynomialFiniteSupport.At(zero, E, q)))
		finiteS := arg.Have(
			"the nonzero coefficients form a finite set",
			"finite(S)",
			By(Normalized, sDef, support, finite_set.FiniteImage.At(q, U)))
		coefficientsInE := arg.Have(
			"the coefficient set lies in E",
			"S ⊆ E",
			BySets(sDef, support))
		algebraicCoefficients := arg.Have(
			"these finitely many coefficients lie in L and are algebraic over K",
			"S ⊆ L.carrier ∧ (∀y:A. y ∈ S ⇒ algebraic_over(L, K, y))",
			BySets(algebraicE, eInL, coefficientsInE))
		H, hDef := arg.LetAs[Set[A]]("H", "field_adjoin(L, K, S)")
		finiteH := arg.Have(
			"adjoining the finite set of algebraic coefficients gives a finite extension of K",
			"finite_extension(L, K, H)",
			By(
				Normalized,
				L,
				finiteS,
				hDef,
				subK,
				algebraicCoefficients,
				At(FiniteAlgebraicAdjoin, record, K, S)))
		adjoinH := arg.Have(
			"the coefficient field H contains K and every nonzero coefficient",
			"subfield(L, H) ∧ K ⊆ H ∧ S ⊆ H",
			By(
				Normalized,
				hDef,
				subK,
				algebraicCoefficients,
				field.SubfieldSubset.At(record, K),
				AdjoinSubfield.Read(L).At(K, S)))
		coefficientsInH := arg.Have(
			"every coefficient of q lies in H, including zero coefficients",
			"∀i:num. q(i) ∈ H",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				nonzero := c.Unless(
					c.Term("q(i) = L.zero"),
					"a zero coefficient lies in the subfield H",
					Given(func(d *Argument, equalZero Fact) {
						d.Show(
							"H contains zero",
							By(Normalized, equalZero, adjoinH, field.SubfieldZero.At(record, H)))
					}))
				inSupport := c.Have(
					"a nonzero coefficient has its index in the support",
					"i ∈ U",
					BySets(nonzero, uDef))
				inCoefficients := c.Have(
					"its value therefore belongs to the coefficient set",
					"q(i) ∈ S",
					By(Normalized, sDef, inSupport, set_image.FunInImage.At(q, U, i)))
				c.Show(
					"and the coefficient set lies in H",
					BySets(inCoefficients, adjoinH))
			}))
		polynomialH := arg.Have(
			"q has the same finite support and all its coefficients now lie in H",
			"polynomial_over(H, q)",
			By(Normalized, coefficientsInH, uDef, support, polynomial.PolynomialFiniteSupport.At(zero, H, q)))
		algebraicH := arg.Have(
			"the same nonzero polynomial q witnesses algebraicity over H",
			"algebraic_over(L, H, x)",
			Derive(func(c *Argument) {
				c.Do(Simp(Fwd(AlgebraicOverDef)))
				c.Take(q)
				c.Show(
					"q is over H, is nonzero, and vanishes at x",
					By(vanishing, polynomialH))
			}))
		J, jDef := arg.LetAs[Set[A]]("J", "field_adjoin(L, H, {x})")
		finiteJ := arg.Have(
			"x is algebraic over H, so H(x) is a subfield holding H and finite over K",
			"subfield(L, J) ∧ H ⊆ J ∧ finite_extension(L, K, J)",
			By(Normalized, jDef, subK, adjoinH, finiteH, algebraicH, FiniteAdjoinStep.Read(L).At(K, H, xm)))
		xInJ := arg.Have(
			"H(x) holds x",
			"x ∈ J",
			By(Normalized, jDef, adjoinH, AdjoinElementSubfield.Read(L).At(H, xm)))
		kInJ := arg.Have(
			"the tower contains K",
			"K ⊆ J",
			BySets(adjoinH, finiteJ))
		arg.Show(
			"x belongs to a finite extension of K, hence is algebraic over K",
			By(subK, kInJ, xInJ, finiteJ, FiniteExtensionAlgebraic.Read(L).At(K, J, x)))
	}),
})}

// PolynomialsOverRestriction — polynomials evaluate by the operations alone, so
// the polynomial image is the same in a restricted field.
var PolynomialsOverRestriction = polynomialsOverRestrictionThm{family.Add(registry.ProofEntry{
	Name: "PolynomialsOverRestriction",
	Key:  "prop_4fdf8284b649d446",
	Build: family.Theorem("∀M:field_ops(A). ∀K k:set(A). ∀x:A. "+
		"    polynomial_image(field_ring(restrict_field(M, K)), k, x) = "+
		"    polynomial_image(field_ring(M), k, x)",
		func(a *Argument, M *Expr[FieldOps[A]], K, k *Expr[Set[A]], x *Expr[A]) {
			a.Show(
				"the image reads the sum, zero, product and one of the ring, which restriction keeps",
				Simp(Rev(field.RestrictFieldRing)),
				Simp(Fwd(PolynomialImageDef), Fwd(module_record.RestrictRingDef)),
				Basic())
		}),
})}

// AdjoinInverse — k(1/t) is k(t): each field holds the other's generator, the
// inverse of its own, so leastness gives both inclusions.
var AdjoinInverse = adjoinInverseThm{family.Add(registry.ProofEntry{
	Name: "AdjoinInverse",
	Key:  "prop_16a581af7465952e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "«inverseField» = «forwardField»",
		Abbrev: Abbrev{
			{Name: "forwardField", Text: "field_adjoin(L, k, {t})"},
			{Name: "inverseField", Text: "field_adjoin(L, k, {L.inv(t)})"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], constants, tIn Fact) {
			record := a.TermAs[FieldOps[A]]("L")
			forward, inverse := a.TermAs[Set[A]]("«forwardField»"), a.TermAs[Set[A]]("«inverseField»")
			tm := a.MemberOf[on.L](t, tIn)
			kInL := a.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(constants, field.SubfieldSubset.At(record, k)))
			generators := a.Have(
				"t and its inverse lie in L",
				"{t} ⊆ L.carrier ∧ {L.inv(t)} ⊆ L.carrier",
				BySets(tIn, field.InvIn.Read(L).At(tm)))
			forwardField := a.Have(
				"k(t) is a subfield holding k and t",
				"subfield(L, «forwardField») ∧ k ⊆ «forwardField» ∧ {t} ⊆ «forwardField»",
				By(kInL, generators, AdjoinSubfield.Read(L).At(k, a.TermAs[Set[A]]("{t}"))))
			inverseField := a.Have(
				"k(1/t) is a subfield holding k and 1/t",
				"subfield(L, «inverseField») ∧ k ⊆ «inverseField» ∧ {L.inv(t)} ⊆ «inverseField»",
				By(kInL, generators, AdjoinSubfield.Read(L).At(k, a.TermAs[Set[A]]("{L.inv(t)}"))))
			inForward := a.Have(
				"t lies in k(t)",
				"t ∈ «forwardField»",
				BySets(forwardField))
			inInverse := a.Have(
				"1/t lies in k(1/t)",
				"L.inv(t) ∈ «inverseField»",
				BySets(inverseField))
			inverseInForward := a.Have(
				"1/t lies in k(t)",
				"L.inv(t) ∈ «forwardField»",
				By(forwardField, inForward, field.SubfieldInv.At(record, forward, t)))
			back := a.Have(
				"t, the inverse of 1/t, lies in k(1/t)",
				"t ∈ «inverseField»",
				By(
					inverseField,
					inInverse,
					field.SubfieldInv.At(record, inverse, a.TermAs[A]("L.inv(t)")),
					field.InvInvOn.Read(L).At(tm)))
			singletons := a.Have(
				"each field holds the other's generator",
				"{t} ⊆ «inverseField» ∧ {L.inv(t)} ⊆ «forwardField»",
				BySets(back, inverseInForward))
			first := a.Have(
				"leastness of k(1/t) gives one inclusion",
				"«inverseField» ⊆ «forwardField»",
				By(forwardField, singletons, AdjoinLeast.Read(L).At(k, a.TermAs[Set[A]]("{L.inv(t)}"), forward)))
			second := a.Have(
				"and leastness of k(t) the other",
				"«forwardField» ⊆ «inverseField»",
				By(inverseField, singletons, AdjoinLeast.Read(L).At(k, a.TermAs[Set[A]]("{t}"), inverse)))
			a.Show(
				"so the two fields are equal",
				By(first, second, set_order.SubsetAntisym))
		}),
})}

// AdjoinInSubfield — adjoining to k inside a subfield K of M, or inside M,
// gives one field, when k and S lie in K: the subfields of M between k ∪ S
// and K are the subfields of K holding them, and each adjunction is the least
// of them.
var AdjoinInSubfield = adjoinInSubfieldThm{family.Add(registry.ProofEntry{
	Name: "AdjoinInSubfield",
	Key:  "prop_6425f614822aa31d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k S:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"k ⊆ K",
			"S ⊆ K",
		},
		Conclusion: "field_adjoin(restrict_field(M, K), k, S) = field_adjoin(M, k, S)",
		Abbrev: Abbrev{
			{Name: "inside", Text: "field_adjoin(restrict_field(M, K), k, S)"},
		},
	},
		func(a *Argument, M field.FieldFact[on.M], K, k, S *Expr[Set[A]], subfieldK, kInK, sInK Fact) {
			ambient, L := a.TermAs[FieldOps[A]]("M"), a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			inside, outside := a.TermAs[Set[A]]("«inside»"), a.TermAs[Set[A]]("field_adjoin(M, k, S)")
			functionField := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			carrier := a.Have(
				"whose carrier is K",
				"restrict_field(M, K).carrier = K",
				Simp(Fwd(field.RestrictFieldDef)),
				Basic())
			inM := a.Have(
				"k and S lie in M",
				"k ⊆ M.carrier ∧ S ⊆ M.carrier",
				BySets(subfieldK, kInK, sInK, field.SubfieldSubset.At(ambient, K)))
			adjoinedOutside := a.Conjuncts(
				a.Have(
					"the adjunction in M is a subfield of M, holding k and S",
					"subfield(M, field_adjoin(M, k, S)) ∧ k ⊆ field_adjoin(M, k, S) ∧ S ⊆ field_adjoin(M, k, S)",
					By(inM, AdjoinSubfield.Read(M).At(k, S))),
				"the adjunction in M is a subfield of M",
				"holding k",
				"and S")
			inK := a.Have(
				"it lies in K",
				"field_adjoin(M, k, S) ⊆ K",
				By(subfieldK, kInK, sInK, AdjoinLeast.Read(M).At(k, S, K)))
			outsideInL := a.Have(
				"so it is a subfield of K",
				"subfield(restrict_field(M, K), field_adjoin(M, k, S))",
				By(adjoinedOutside[0], inK, field.SubfieldRestrict.At(ambient, K, outside)))
			adjoinedInside := a.Conjuncts(
				a.Have(
					"the adjunction in K is a subfield of K, holding k and S",
					"subfield(restrict_field(M, K), «inside») ∧ k ⊆ «inside» ∧ S ⊆ «inside»",
					By(functionField, carrier, kInK, sInK, AdjoinSubfield.At(L, k, S))),
				"the adjunction in K is a subfield of K",
				"holding k",
				"and S")
			insideInM := a.Have(
				"so it is a subfield of M",
				"subfield(M, «inside»)",
				By(subfieldK, adjoinedInside[0], field.SubfieldTrans.At(ambient, K, inside)))
			a.Show(
				"each adjunction lies in the other, being least",
				By(
					AdjoinLeast.At(L, k, S, outside),
					AdjoinLeast.Read(M).At(k, S, inside),
					functionField,
					outsideInL,
					adjoinedOutside[1],
					adjoinedOutside[2],
					insideInM,
					adjoinedInside[1],
					adjoinedInside[2],
					set_order.SubsetAntisym.At(inside, outside)))
		}),
})}

// ConstantTranscendental — an element transcendental over k stays
// transcendental over a finite extension l: l is algebraic over k, and
// algebraicity is transitive.
var ConstantTranscendental = constantTranscendentalThm{family.Add(registry.ProofEntry{
	Name: "ConstantTranscendental",
	Key:  "prop_2ab2299b3e60302f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
		},
		Conclusion: "¬algebraic_over(M, l, t)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			t *Expr[A],
			kSubfield, lSubfield, kInL, finiteExtension, tInField, transcendental Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			algebraic := a.Have(
				"each member of l is algebraic over k",
				"∀y:A. y ∈ l ⇒ algebraic_over(M, k, y)",
				a.ForEach(func(y *Expr[A]) Action {
					return By(
						kSubfield,
						lSubfield,
						kInL,
						finiteExtension,
						FiniteExtensionAlgebraic.Read(M).AsFact().At(k, l, y))
				}))
			a.Show(
				"so t algebraic over l would be algebraic over k",
				By(
					kSubfield,
					tInField,
					transcendental,
					algebraic,
					field.SubfieldSubset.At(ops, l),
					lSubfield,
					AlgebraicOverTrans.Read(M).AsFact().At(k, l, t)))
		}),
})}

// RestrictFieldReadings — polynomials over X evaluated at y, and algebraicity
// over X, read the operations alone, so a restricted field reads them as the
// field does.
var RestrictFieldReadings = restrictFieldReadingsThm{family.Add(registry.ProofEntry{
	Name: "RestrictFieldReadings",
	Key:  "prop_4ea9256c3fc4a845",
	Build: family.Theorem(
		"∀M:field_ops(A). ∀K X:set(A). ∀y:A. "+
			"    polynomial_image(field_ring(restrict_field(M, K)), X, y) = "+
			"    polynomial_image(field_ring(M), X, y) ∧ "+
			"    (algebraic_over(restrict_field(M, K), X, y) ⇔ algebraic_over(M, X, y))",
		func(a *Argument, M *Expr[FieldOps[A]], K, X *Expr[Set[A]], y *Expr[A]) {
			a.Show(
				"the restriction keeps the operations",
				Simp(Fwd(PolynomialImageDef), Fwd(AlgebraicOverDef)),
				Basic())
		}),
})}
