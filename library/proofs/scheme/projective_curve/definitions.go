// definitions.go — the chapter's definitions, each followed by the laws that
// state its parts, which a proof cites in place of the unfolded definition.
// The parts of a curve are the conjuncts of a predicate, stated through the
// definition's Conjunct door; the points are a set, which that door does not
// read, so the parts of a point are theorems proved by unfolding the
// membership, and so is the reading of the points of a listed family of
// equations as its normalized common zeros.

package projective_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

var ProjectiveEquationPointsDef = projectiveEquationPointsDefThm{family.Define(registry.DefEntry{
	Name:  "ProjectiveEquationPointsDef",
	Key:   "prop_500cb6abcb33bddc",
	Deps:  []registry.EntryLike{},
	Const: "projective_equation_points",
	Type:  "ring_ops(A) → set(A) → set(A) → num → set(((num → num) → A)) → set(num → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀k l:set(A). ∀n:num. ∀E:set(((num → num) → A)). " +
			"    projective_equation_points(R, k, l, n, E) = " +
			"    {x:(num → A) | " +
			"        (∀i:num. i ≤ n ⇒ x(i) ∈ l) ∧ " +
			"        (∀i:num. n < i ⇒ x(i) = R.zero) ∧ " +
			"        (∃j:num. j ≤ n ∧ x(j) = R.one ∧ (∀i:num. i < j ⇒ x(i) = R.zero)) ∧ " +
			"        (∀P:((num → num) → A). " +
			"            P ∈ E ⇒ polynomial_algebra_eval(restrict_ring(R, k), R, (λa:A. a), x, P) = R.zero)}",
	},
})}

// PointCoordinatesIn — the coordinates up to n of a point of the curve over l lie in l.
var PointCoordinatesIn = pointCoordinatesInThm{family.Add(registry.ProofEntry{
	Name: "PointCoordinatesIn",
	Key:  "prop_a0606ea7fa0da660",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k l:set(A). ∀n:num. ∀E:set((num → num) → A). ∀x:(num → A). ∀i:num.",
		Hypotheses: []string{
			"x ∈ projective_equation_points(R, k, l, n, E)",
			"i ≤ n",
		},
		Conclusion: "x(i) ∈ l",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, l *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			i *Expr[Nat],
			point, inRange Fact,
		) {
			a.Show(
				"a point's coordinates up to n lie in l",
				By(a.Unfolded(point, ProjectiveEquationPointsDef), inRange))
		}),
})}

// PointZeroPastN — the coordinates past n of a point of the curve are zero.
var PointZeroPastN = pointZeroPastNThm{family.Add(registry.ProofEntry{
	Name: "PointZeroPastN",
	Key:  "prop_1f3451253c61ec6b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k l:set(A). ∀n:num. ∀E:set((num → num) → A). ∀x:(num → A). ∀i:num.",
		Hypotheses: []string{
			"x ∈ projective_equation_points(R, k, l, n, E)",
			"n < i",
		},
		Conclusion: "x(i) = R.zero",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, l *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			i *Expr[Nat],
			point, pastN Fact,
		) {
			a.Show(
				"a point's coordinates past n are zero",
				By(a.Unfolded(point, ProjectiveEquationPointsDef), pastN))
		}),
})}

// PointLeadingOne — the first nonzero coordinate of a point of the curve is one, at an index up to n.
var PointLeadingOne = pointLeadingOneThm{family.Add(registry.ProofEntry{
	Name: "PointLeadingOne",
	Key:  "prop_f0830262e70f2984",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k l:set(A). ∀n:num. ∀E:set((num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"x ∈ projective_equation_points(R, k, l, n, E)",
		},
		Conclusion: "∃j:num. j ≤ n ∧ x(j) = R.one ∧ (∀i:num. i < j ⇒ x(i) = R.zero)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, l *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			point Fact,
		) {
			a.Show(
				"a point's first nonzero coordinate is one",
				By(a.Unfolded(point, ProjectiveEquationPointsDef)))
		}),
})}

// PointEquationsVanish — every equation in E vanishes at a point of the curve.
var PointEquationsVanish = pointEquationsVanishThm{family.Add(registry.ProofEntry{
	Name: "PointEquationsVanish",
	Key:  "prop_f19c2f0b6e688172",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀k l:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀P:((num → num) → A).",
		Hypotheses: []string{
			"x ∈ projective_equation_points(R, k, l, n, E)",
			"P ∈ E",
		},
		Conclusion: "polynomial_algebra_eval(restrict_ring(R, k), R, (λa:A. a), x, P) = R.zero",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, l *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			P *Arrow[Fun[Nat, Nat], A],
			point, inE Fact,
		) {
			a.Show(
				"the equations vanish at a point",
				By(a.Unfolded(point, ProjectiveEquationPointsDef), inE))
		}),
})}

// PointsAsNormalizedZeros — the projective points over F of the curve cut out
// by a listed family of equations P(0), …, P(r − 1) are the normalized
// (n + 1)-tuples of F at which every P(j) vanishes. Both sides are four
// conditions on x. A tuple of length n + 1 has its coordinates below n + 1,
// that is up to n, in F and the rest zero; the leading one sits at an index
// below n + 1; and an equation over the constants k takes at x the value it
// takes over F, the one sum over the one support. Neither k nor any law of F is
// used.
var PointsAsNormalizedZeros = pointsAsNormalizedZerosThm{family.Add(registry.ProofEntry{
	Name: "PointsAsNormalizedZeros",
	Key:  "prop_10d6ed4c4ba79943",
	Build: family.Theorem("∀F:field_ops(A). "+
		"∀k:set(A). "+
		"∀n r:num. "+
		"∀P:(num → (num → num) → A). "+
		"∀x:(num → A). "+
		"    x ∈ projective_equation_points(field_ring(F), k, F.carrier, n, image(P, {j:num | j < r})) ⇔ "+
		"    ring_tuple(field_ring(F), n + 1, x) ∧ "+
		"    (∃j:num. j < n + 1 ∧ x(j) = F.one ∧ (∀i:num. i < j ⇒ x(i) = F.zero)) ∧ "+
		"    (∀j:num. j < r ⇒ polynomial_value(field_ring(F), P(j), x) = F.zero)",
		func(
			a *Argument,
			F *Expr[FieldOps[A]],
			k *Expr[Set[A]],
			n, r *Expr[Nat],
			P *Arrow2[Nat, Fun[Nat, Nat], A],
			x *Arrow[Nat, A],
		) {
			// Unfold both sides to their conditions on x, then read i < n + 1
			// as i ≤ n and n + 1 ≤ i as n < i.
			a.Do(
				Simp(
					Fwd(ProjectiveEquationPointsDef),
					Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients),
					Fwd(polynomial_encoding.PolynomialValueDef),
					Fwd(polynomial_encoding.RingTupleDef),
					Fwd(vec_space.VecDef),
					Fwd(set_image.ForallInImage)),
				Simp(Rev(nat_arith.Add1), Fwd(nat_order.LessThanSucIffLessEq), Rev(nat_order.SucLessEqIffLessThan)))
			a.Iff()
			a.Forward(
				"a point of the curve is a normalized zero of P",
				func(b *Argument, point Fact) {
					b.Show(
						"its four conditions are the zero's, in another order",
						By(point))
				})
			a.Backward(
				"a normalized zero of P is a point of the curve",
				func(b *Argument, zero Fact) {
					b.Show(
						"its four conditions are the point's, in another order",
						By(zero))
				})
		}),
})}

var ProjectiveHilbertFunctionDef = projectiveHilbertFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "ProjectiveHilbertFunctionDef",
	Key:   "prop_508851b3aedb0369",
	Deps:  []registry.EntryLike{},
	Const: "projective_hilbert_function",
	Type:  "ring_ops(A) → set(A) → num → set(((num → num) → A)) → num → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀n d:num. ∀E:set(((num → num) → A)). " +
			"    projective_hilbert_function(R, k, n, E, d) = " +
			"    module_dim(restrict_ring(R, k), " +
			"        quotient_module(mk_module( " +
			"                polynomial_algebra_ring(restrict_ring(R, k), {i:num | i ≤ n}).add, " +
			"                polynomial_algebra_ring(restrict_ring(R, k), {i:num | i ≤ n}).zero, " +
			"                polynomial_algebra_ring(restrict_ring(R, k), {i:num | i ≤ n}).neg, " +
			"                (λa:A. λP:((num → num) → A). λm:(num → num). R.mul(a, P(m))), " +
			"                {P:((num → num) → A) | homogeneous_polynomial(restrict_ring(R, k), n, d, P)}), " +
			"            {P:((num → num) → A) | homogeneous_polynomial(restrict_ring(R, k), n, d, P)} ∩ " +
			"            ideal_span(polynomial_algebra_ring(restrict_ring(R, k), {i:num | i ≤ n}), E)))",
	},
})}

var ProjectiveGenusDef = projectiveGenusDefThm{family.Define(registry.DefEntry{
	Name:  "ProjectiveGenusDef",
	Key:   "prop_f1ad139e7567de42",
	Deps:  []registry.EntryLike{ProjectiveHilbertFunctionDef},
	Const: "projective_equation_genus",
	Type:  "ring_ops(A) → set(A) → num → set(((num → num) → A)) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀n:num. ∀E:set(((num → num) → A)). " +
			"    projective_equation_genus(R, k, n, E) = " +
			"    εg:num. ∃e N:num. " +
			"        0 < e ∧ (∀d:num. N ≤ d ⇒ projective_hilbert_function(R, k, n, E, d) + g = e * d + 1)",
	},
})}

// GenusAlongMultiples — the Hilbert genus is read along the multiples of a
// positive degree r: when the Hilbert function is eventually linear and
// h(r·j) + g = c·j + 1 from some j on, the genus is g. The genus is a g' with
// h(d) + g' = e·d + 1 from some d on; at two consecutive j past both bounds
// the lines in j agree, so c = e·r and then g' = g.
var GenusAlongMultiples = genusAlongMultiplesThm{family.Add(registry.ProofEntry{
	Name: "GenusAlongMultiples",
	Key:  "prop_7c116f4cb879211b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A). ∀r g:num.",
		Hypotheses: []string{
			"0 < r",
			"∃g' e N':num. " +
				"    0 < e ∧ (∀d:num. N' ≤ d ⇒ projective_hilbert_function(R, k, n, E, d) + g' = e * d + 1)",
			"∃c N:num. ∀j:num. N ≤ j ⇒ projective_hilbert_function(R, k, n, E, r * j) + g = c * j + 1",
		},
		Conclusion: "projective_equation_genus(R, k, n, E) = g",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			r, g *Expr[Nat],
			positive, eventuallyLinear, alongMultiples Fact,
		) {
			_, _, along := a.Unpack2As[Nat, Nat](alongMultiples, "c", "N")
			_, chosen := a.ObtainChosen(
				"take g' as projective_equation_genus takes it, the ε-choice of a constant "+
					"with which the Hilbert function is eventually linear, one existing",
				"∃g':num. ∃e N':num. "+
					"    0 < e ∧ (∀d:num. N' ≤ d ⇒ projective_hilbert_function(R, k, n, E, d) + g' = e * d + 1)",
				eventuallyLinear)
			_, _, line := a.Unpack2As[Nat, Nat](chosen, "e", "N₁")
			lineParts := a.Conjuncts(
				line,
				"the slope e is positive",
				"from N₁ on, h(d) + g' = e·d + 1")
			j := a.TermAs[Nat]("N + N₁")
			next := a.TermAs[Nat]("N + N₁ + 1")
			past := a.Have(
				"j = N + N₁ and j + 1 are past N, and r·j and r·(j + 1) past N₁",
				"N ≤ N + N₁ ∧ N ≤ N + N₁ + 1 ∧ N₁ ≤ r * (N + N₁) ∧ N₁ ≤ r * (N + N₁ + 1)",
				ByArith(positive, nat_order.LessEqMulNonzero.At(j, r), nat_order.LessEqMulNonzero.At(next, r)))
			degreeJ, degreeNext := a.TermAs[Nat]("r * (N + N₁)"), a.TermAs[Nat]("r * (N + N₁ + 1)")
			slope := a.Have(
				"the two lines rise by the same amount from j to j + 1: c = e·r",
				"c = e * r",
				ByArith(past, along.At(j), along.At(next), lineParts[1].At(degreeJ), lineParts[1].At(degreeNext)))
			a.Show(
				"so at j their constant terms agree, and the genus, g', is g",
				ByArith(
					past,
					along.At(j),
					lineParts[1].At(degreeJ),
					Scaled(j, slope),
					ProjectiveGenusDef.At(R, k, n, E)))
		}),
})}

var SmoothProjectiveEquationCurveDef = smoothProjectiveEquationCurveDefThm{family.Define(registry.DefEntry{
	Name: "SmoothProjectiveEquationCurveDef",
	Key:  "prop_266b751983a3de72",
	Reading: "The input is a finite homogeneous closed embedding with " +
		"geometrically prime ideal, linear Hilbert polynomial, and the Jacobian rank " +
		"of a smooth projective curve. It is independent of any two-chart presentation.",
	Deps:  []registry.EntryLike{ProjectiveEquationPointsDef, ProjectiveHilbertFunctionDef},
	Const: "smooth_projective_equation_curve",
	Type:  "field_ops(A) → set(A) → num → (set(((num → num) → A))) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀n:num. ∀E:set(((num → num) → A)). " +
			"    smooth_projective_equation_curve(R, k, n, E) ⇔ " +
			"    subfield(R, k) ∧ " +
			"    finite(k) ∧ " +
			"    0 < n ∧ " +
			"    finite(E) ∧ " +
			"    (∀P:((num → num) → A). " +
			"        P ∈ E ⇒ ∃d:num. homogeneous_polynomial(restrict_ring(field_ring(R), k), n, d, P)) ∧ " +
			"    prime_ideal(polynomial_algebra_ring(field_ring(R), {i:num | i ≤ n}), " +
			"        ideal_span(polynomial_algebra_ring(field_ring(R), {i:num | i ≤ n}), E)) ∧ " +
			"    (∃x:(num → A). x ∈ projective_equation_points(field_ring(R), k, R.carrier, n, E)) ∧ " +
			"    (∃g e N:num. " +
			"        0 < e ∧ " +
			"        (∀d:num. " +
			"            N ≤ d ⇒ projective_hilbert_function(field_ring(R), k, n, E, d) + g = e * d + 1)) ∧ " +
			"    (∀x:(num → A). " +
			"        x ∈ projective_equation_points(field_ring(R), k, R.carrier, n, E) ⇒ " +
			"        module_dim(field_ring(R), " +
			"            restrict_module(free_module_record(field_ring(R), {i:num | i ≤ n}), " +
			"                module_span(field_ring(R), " +
			"                    free_module_record(field_ring(R), {i:num | i ≤ n}), " +
			"                    {(λi:num. " +
			"                            COND(i ≤ n, " +
			"                                polynomial_algebra_eval(restrict_ring(field_ring(R), k), " +
			"                                    field_ring(R), " +
			"                                    (λa:A. a), " +
			"                                    x, " +
			"                                    polynomial_algebra_partial(restrict_ring(field_ring(R), k), " +
			"                                        i, " +
			"                                        P)), " +
			"                                R.zero)) | " +
			"                        P:((num → num) → A) | " +
			"                        P ∈ E}))) + " +
			"        1 = " +
			"        n)",
	},
})}

// CurveConstantsSubfield — the constants k of a smooth projective equation curve are a subfield of the field.
var CurveConstantsSubfield = curveConstantsSubfieldThm{family.Add(registry.ProofEntry{
	Name:  "CurveConstantsSubfield",
	Key:   "prop_b58f9a4f02525afb",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct("subfield(R, k)"),
})}

// CurveConstantsFinite — the constants k of a smooth projective equation curve are finitely many.
var CurveConstantsFinite = curveConstantsFiniteThm{family.Add(registry.ProofEntry{
	Name:  "CurveConstantsFinite",
	Key:   "prop_359f753a42c002f6",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct("finite(k)"),
})}

// CurveEquationsForms — each equation of a smooth projective equation curve is a form over its constants.
var CurveEquationsForms = curveEquationsFormsThm{family.Add(registry.ProofEntry{
	Name: "CurveEquationsForms",
	Key:  "prop_9e6ba94ae11e178d",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct(Statement{
		Binders: "∀P:((num → num) → A).",
		Hypotheses: []string{
			"P ∈ E",
		},
		Conclusion: "∃d:num. homogeneous_polynomial(restrict_ring(field_ring(R), k), n, d, P)",
	}),
})}

// CurveIdealGeometricallyPrime — the equations of a smooth projective equation curve span a prime ideal of the polynomials over the whole field.
var CurveIdealGeometricallyPrime = curveIdealGeometricallyPrimeThm{family.Add(registry.ProofEntry{
	Name: "CurveIdealGeometricallyPrime",
	Key:  "prop_edbdca6a2b2f1522",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct(
		"prime_ideal(polynomial_algebra_ring(field_ring(R), {i:num | i ≤ n}), " +
			"    ideal_span(polynomial_algebra_ring(field_ring(R), {i:num | i ≤ n}), E))"),
})}

// CurveHasPoint — a smooth projective equation curve has a point with coordinates in the field.
var CurveHasPoint = curveHasPointThm{family.Add(registry.ProofEntry{
	Name: "CurveHasPoint",
	Key:  "prop_ba5a7507eb0dfe41",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct(
		"∃x:(num → A). x ∈ projective_equation_points(field_ring(R), k, R.carrier, n, E)"),
})}

// CurveHilbertEventuallyLinear — the Hilbert function of a smooth projective equation curve is eventually e·d + 1 − g, with e positive.
var CurveHilbertEventuallyLinear = curveHilbertEventuallyLinearThm{family.Add(registry.ProofEntry{
	Name: "CurveHilbertEventuallyLinear",
	Key:  "prop_4e8557fc4ca9cf24",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct(
		"∃g e N:num. " +
			"    0 < e ∧ " +
			"    (∀d:num. N ≤ d ⇒ projective_hilbert_function(field_ring(R), k, n, E, d) + g = e * d + 1)"),
})}

// CurveJacobianRank — at every point of a smooth projective equation curve, the gradients of its equations span a space of dimension n − 1.
var CurveJacobianRank = curveJacobianRankThm{family.Add(registry.ProofEntry{
	Name: "CurveJacobianRank",
	Key:  "prop_53965237082d063a",
	Build: SmoothProjectiveEquationCurveDef.Entry().Conjunct(Statement{
		Binders: "∀x:(num → A).",
		Hypotheses: []string{
			"x ∈ projective_equation_points(field_ring(R), k, R.carrier, n, E)",
		},
		Conclusion: "module_dim(field_ring(R), " +
			"    restrict_module(free_module_record(field_ring(R), {i:num | i ≤ n}), " +
			"        module_span(field_ring(R), " +
			"            free_module_record(field_ring(R), {i:num | i ≤ n}), " +
			"            {λi:num. " +
			"                COND(i ≤ n, " +
			"                    polynomial_algebra_eval(restrict_ring(field_ring(R), k), " +
			"                        field_ring(R), " +
			"                        λa:A. a, " +
			"                        x, " +
			"                        polynomial_algebra_partial(restrict_ring(field_ring(R), k), i, P)), " +
			"                    R.zero) | " +
			"            P:(num → num) → A | " +
			"            P ∈ E}))) + " +
			"1 = " +
			"n",
	}),
})}

var ProjectiveGenericFieldDef = projectiveGenericFieldDefThm{family.Define(registry.DefEntry{
	Name:  "ProjectiveGenericFieldDef",
	Key:   "prop_20e40ab035ecb37e",
	Deps:  []registry.EntryLike{ProjectiveEquationPointsDef},
	Const: "projective_generic_field",
	Type:  "field_ops(A) → set(A) → num → (set(((num → num) → A))) → set(A) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀K:set(A). ∀n:num. ∀E:set(((num → num) → A)). " +
			"    projective_generic_field(R, k, n, E, K) ⇔ " +
			"    ∃x:(num → A). " +
			"        x ∈ projective_equation_points(field_ring(R), k, K, n, E) ∧ " +
			"        field_adjoin(R, k, {x(i) | i:num | i ≤ n}) = K ∧ " +
			"        (∀P:((num → num) → A).( " +
			"                ∃d:num. homogeneous_polynomial(restrict_ring(field_ring(R), k), n, d, P)) ⇒ " +
			"            (polynomial_algebra_eval(restrict_ring(field_ring(R), k), " +
			"                    field_ring(R), " +
			"                    (λa:A. a), " +
			"                    x, " +
			"                    P) = " +
			"                R.zero ⇔ " +
			"                P ∈ " +
			"                ideal_span( " +
			"                    polynomial_algebra_ring(restrict_ring(field_ring(R), k), {i:num | i ≤ n}), " +
			"                    E)))",
	},
})}
