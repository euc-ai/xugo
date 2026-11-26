package polynomial_optimization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial_geometry"
	"github.com/euc-ai/xugo/library/registry"

	// real_closed_field_transfer states SentenceTransfer, and real_closed_instance the reals' instance,
	// which ByElementarity reads by name and by statement: the imports keep this chapter above them in
	// Go's import graph.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_closed_instance"
)

// LexicographicMinimum — over a real closed field, an objective f and a secondary objective q in n
// variables whose feasible set, cut out by s weak polynomial inequalities and t polynomial
// equations, is nonempty and lies in the box of a bound have a lexicographic minimizer: the
// 2 + s + t polynomials have a common degree bound d, and lexicographic_minimum_property at d, a
// closed sentence true over the reals (real_polynomial_geometry.LexicographicSource), holds in
// every real closed field by real_closed_field_transfer.SentenceTransfer and is read at f, q, g, h
// and M, the order of its ∀ binders.
var LexicographicMinimum = lexicographicMinimumThm{family.Add(registry.ProofEntry{
	Name: "LexicographicMinimum",
	Key:  "prop_b43bd5afd21af0d4",
	Reading: "Weak inequalities and boundedness are load-bearing. Strict constraints can " +
		"yield a bounded nonempty real set without a minimum. Empty constraint lists are " +
		"permitted; their positive-dimensional feasible set cannot meet the box-bound premise.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀n s t:num. " +
			"∀f q:((num → num) → A). " +
			"∀g h:(num → (num → num) → A). " +
			"∀M:A.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"f ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"q ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"∀j:num. j < s ⇒ g(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"∀j:num. j < t ⇒ h(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"polynomial_constraint_set(F, lt, n, s, t, g, h) ≠ ∅",
			"polynomial_box_bound(F, lt, n, polynomial_constraint_set(F, lt, n, s, t, g, h), M)",
		},
		Conclusion: "∃x:(num → A). " +
			"    polynomial_lex_minimizer(F, lt, polynomial_constraint_set(F, lt, n, s, t, g, h), f, q, x)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		n, s, t *Expr[Nat],
		f, q *Arrow[Fun[Nat, Nat], A],
		g, h *Arrow2[Nat, Fun[Nat, Nat], A],
		M *Expr[A],
		closedF real_closed_field.RealClosedFieldFact[on.F],
		fIn, qIn, gIn, hIn, feasible, bounded Fact,
	) {
		a.Show(
			"the lexicographic minimum over the reals, transferred at "+
				"a common degree bound of f, q, g and h and read at the data",
			ByElementarity(
				real_polynomial_geometry.LexicographicSource,
				closedF,
				fIn,
				qIn,
				gIn,
				hIn,
				feasible,
				bounded).At(f, q, g, h, M))
	}),
})}

// ClosedIntervalMinimum — over a real closed field, a polynomial in one variable attains its
// minimum on a nonempty closed interval ⟦a, b⟧: p is a tuple of some n coefficients
// (polynomial_encoding.TupleOfPolynomial), and interval_minimum_property at n, a closed sentence
// true over the reals, where a continuous function takes a least value on ⟦a, b⟧
// (real_polynomial_geometry.IntervalMinimumSource), holds in F by
// real_closed_field_transfer.SentenceTransfer and is read at p, a and b, its ∀ binders.
var ClosedIntervalMinimum = closedIntervalMinimumThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalMinimum",
	Key:  "prop_19f3a6986f2c56e",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"ordered_le(lt, a, b)",
		},
		Conclusion: "∃u:A. " +
			"    u ∈ F.carrier ∧ " +
			"    ordered_le(lt, a, u) ∧ " +
			"    ordered_le(lt, u, b) ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ " +
			"        ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)))",
	}, func(
		arg *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		p *Arrow[Nat, A],
		a, b *Expr[A],
		closedF, over, aIn, bIn, endpoints Fact,
	) {
		arg.Show(
			"the minimum on a closed interval over the reals, transferred "+
				"at the number of p's coefficients and read at p, a and b",
			ByElementarity(
				real_polynomial_geometry.IntervalMinimumSource,
				closedF,
				over,
				aIn,
				bIn,
				endpoints).At(p, a, b))
	}),
})}

// ClosedIntervalExtrema — over a real closed field, a polynomial in one variable attains its
// minimum and its maximum on a nonempty closed interval: the minimum is ClosedIntervalMinimum's,
// and the maximum is where the negated polynomial is least, evaluation at a point being a ring
// homomorphism that carries the negation to the negated value.
var ClosedIntervalExtrema = closedIntervalExtremaThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalExtrema",
	Key:  "prop_d210b455493bbd3c",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"ordered_le(lt, a, b)",
		},
		Conclusion: "∃u v:A. " +
			"    u ∈ F.carrier ∧ " +
			"    v ∈ F.carrier ∧ " +
			"    ordered_le(lt, a, u) ∧ " +
			"    ordered_le(lt, u, b) ∧ " +
			"    ordered_le(lt, a, v) ∧ " +
			"    ordered_le(lt, v, b) ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ " +
			"        ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)) ∧ " +
			"        ordered_le(lt, polynomial_eval(p, x), polynomial_eval(p, v)))",
		Abbrev: Abbrev{
			{Name: "negated", Text: "polynomial_ring(field_ring(F)).neg(p)"},
		},
	}, func(
		arg *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		p *Arrow[Nat, A],
		a, b *Expr[A],
		closedF real_closed_field.RealClosedFieldFact[on.F],
		over, aIn, bIn, endpoints Fact,
	) {
		orderedF := real_closed_field.OrderedFieldOn.Read(closedF)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(orderedF))
		polynomials := arg.Have(
			"the polynomials over the field form a commutative ring",
			"comm_ring_on(polynomial_ring(field_ring(F)))",
			By(polynomial.PolynomialRingOn.Read(ring)))
		inRing := arg.Have(
			"p is one of them",
			"p ∈ polynomial_ring(field_ring(F)).carrier",
			By(over, polynomial.PolynomialRingDef))
		negatedOver := arg.Have(
			"so is its negation",
			"polynomial_over(F.carrier, «negated»)",
			By(inRing, polynomial.PolynomialRingDef, comm_ring.NegIn.Read(polynomials).AsFact().At(p)))
		values := arg.Have(
			"at a carrier value x the negation takes the negated value, and p a carrier value",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
				},
				Conclusion: "polynomial_eval(«negated», x) = F.neg(polynomial_eval(p, x)) ∧ " +
					"polynomial_eval(p, x) ∈ F.carrier",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xIn := c.Assume()
				evaluation := c.Have(
					"evaluation at x is a ring homomorphism from the polynomials to the field",
					"ring_homomorphism(polynomial_ring(field_ring(F)), "+
						"    field_ring(F), "+
						"    λq:(num → A). polynomial_eval(q, x))",
					By(polynomial_evaluation.EvalHomomorphism.Read(ring).At(c.MemberOf[on.F](x, xIn))))
				c.Show(
					"a ring homomorphism keeps negatives and the carrier",
					By(
						inRing,
						evaluation,
						ring_homomorphism.MapNeg.Read(evaluation).AsFact().At(p),
						ring_homomorphism.MapIn.Read(evaluation).AsFact().At(p)))
			}))
		u, least := arg.UnpackAs[A](
			GroupPremises(closedF, over, aIn, bIn, endpoints, ClosedIntervalMinimum.At(F, lt, p, a, b)),
			"u")
		v, most := arg.UnpackAs[A](
			GroupPremises(
				closedF,
				negatedOver,
				aIn,
				bIn,
				endpoints,
				ClosedIntervalMinimum.At(F, lt, arg.TermAs[Fun[Nat, A]]("«negated»"), a, b)),
			"v")
		lowest := arg.Conjuncts(
			least,
			"u is a carrier value",
			"a ≤ u",
			"u ≤ b",
			"p is least at u")
		highest := arg.Conjuncts(
			most,
			"v is a carrier value",
			"a ≤ v",
			"v ≤ b",
			"the negation of p is least at v")
		arg.Take(u)
		arg.Take(v)
		maximum := arg.Have(
			"p is greatest at v on ⟦a, b⟧",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"ordered_le(lt, a, x)",
					"ordered_le(lt, x, b)",
				},
				Conclusion: "ordered_le(lt, polynomial_eval(p, x), polynomial_eval(p, v))",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				given := c.Assume()
				inF := c.Conjuncts(
					given,
					"x is a carrier value",
					"a ≤ x",
					"x ≤ b")
				atX := c.Conjuncts(
					GroupPremises(inF[0], values.At(x)),
					"the negation of p at x is −p(x)",
					"p(x) is a carrier value")
				atV := c.Conjuncts(
					GroupPremises(highest[0], values.At(v)),
					"the negation of p at v is −p(v)",
					"p(v) is a carrier value")
				px := c.TermAs[A]("polynomial_eval(p, x)")
				pv := c.TermAs[A]("polynomial_eval(p, v)")
				pxM := c.MemberOf[on.F](px, atX[1])
				pvM := c.MemberOf[on.F](pv, atV[1])
				cancel := c.Have(
					"−p(v) + (p(x) + p(v)) = p(x) and −p(x) + (p(x) + p(v)) = p(v)",
					"F.add(F.neg(polynomial_eval(p, v)), F.add(polynomial_eval(p, x), polynomial_eval(p, v))) = "+
						"polynomial_eval(p, x) ∧ "+
						"F.add(F.neg(polynomial_eval(p, x)), F.add(polynomial_eval(p, x), polynomial_eval(p, v))) = "+
						"polynomial_eval(p, v)",
					ByArith(ring, pxM, pvM))
				c.Show(
					"−p(v) ≤ −p(x), and adding p(x) + p(v) to both sides",
					By(
						given,
						highest[3].At(x),
						atX[0],
						atV[0],
						cancel,
						ordered_field.WeakOrderTranslation.Read(orderedF).At(
							comm_ring.NegIn.Read(ring).At(pvM),
							comm_ring.NegIn.Read(ring).At(pxM),
							comm_ring.AddIn.Read(ring).At(pxM, pvM))))
			}))
		arg.Show(
			"u and v lie in ⟦a, b⟧, p is least at u and greatest at v",
			By(lowest[0], lowest[1], lowest[2], lowest[3], highest[0], highest[1], highest[2], maximum))
	}),
})}

// CubePositiveLowerBound — over a real closed field, a polynomial positive on the carrier cube has
// a positive lower bound there: cube_positive_bound_property at p's degree bound, a closed sentence
// true over the reals, where a positive polynomial attains its least value on the compact cube
// (real_polynomial_geometry.CubePositiveSource), holds in F by
// real_closed_field_transfer.SentenceTransfer and is read at p, its one ∀ binder. It is also a
// corollary of LexicographicMinimum, the cube cut out by its 2n weak inequalities in the box of
// bound 1 and the minimizer's value the bound.
var CubePositiveLowerBound = cubePositiveLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "CubePositiveLowerBound",
	Key:  "prop_e9935e9e01c554dd",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"p ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"∀x:(num → A). x ∈ carrier_cube(F, lt, n) ⇒ lt(F.zero, polynomial_value(field_ring(F), p, x))",
		},
		Conclusion: "∃e:A. " +
			"    e ∈ F.carrier ∧ " +
			"    lt(F.zero, e) ∧ " +
			"    (∀x:(num → A). " +
			"        x ∈ carrier_cube(F, lt, n) ⇒ ordered_le(lt, e, polynomial_value(field_ring(F), p, x)))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		n *Expr[Nat],
		p *Arrow[Fun[Nat, Nat], A],
		closedF, member, positive Fact,
	) {
		a.Show(
			"positivity on the cube over the reals, transferred at p's degree bound and read at p",
			ByElementarity(real_polynomial_geometry.CubePositiveSource, closedF, member, positive).At(p))
	}),
})}
