package real_closed_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RealClosedField — An ordered field in which every polynomial crossing from negative to positive has a root between the endpoints.
var RealClosedField = realClosedFieldThm{family.DefineStructure(registry.DefEntry{
	Name: "RealClosedField", Const: "real_closed_field", Type: "field_ops(A) → (A → A → bool) → bool",
	Key: "prop_20264462f5e5ad3",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). " +
			"    real_closed_field(F, lt) ⇔ " +
			"    ordered_field_on(F, lt) ∧ " +
			"    (∀p:(num → A). ∀a b:A. " +
			"        polynomial_over(F.zero, F.carrier, p) ∧ " +
			"        a ∈ F.carrier ∧ " +
			"        b ∈ F.carrier ∧ " +
			"        lt(a, b) ∧ " +
			"        lt(polynomial_eval(F.add, F.zero, F.mul, F.one, p, a), F.zero) ∧ " +
			"        lt(F.zero, polynomial_eval(F.add, F.zero, F.mul, F.one, p, b)) ⇒ " +
			"        ∃x:A. " +
			"            x ∈ F.carrier ∧ " +
			"            lt(a, x) ∧ " +
			"            lt(x, b) ∧ " +
			"            polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = F.zero)",
	},
})}

// OrderedFieldOn — A real closed field is an ordered field.
var OrderedFieldOn = orderedFieldOnThm{family.Add(registry.ProofEntry{
	Name:  "OrderedFieldOn",
	Key:   "prop_1143cf734648845b",
	Build: RealClosedField.Axiom("ordered_field_on(F, lt)"),
})}

// IntermediateValue — A polynomial negative at a and positive at a later point b has a root
// strictly between them.
var IntermediateValue = intermediateValueThm{family.Add(registry.ProofEntry{
	Name: "IntermediateValue",
	Key:  "prop_c89d419c620e917f",
	Build: RealClosedField.Axiom(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"lt(polynomial_eval(p, a), F.zero)",
			"lt(F.zero, polynomial_eval(p, b))",
		},
		Conclusion: "∃x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(p, x) = F.zero",
	}),
})}

// DownwardIntermediateValue — A polynomial positive at a and negative at b has a root strictly
// between them: its negative rises through zero there, so the axiom IntermediateValue gives the
// negative a root, and a root of −p is a root of p.
var DownwardIntermediateValue = downwardIntermediateValueThm{family.Add(registry.ProofEntry{
	Name: "DownwardIntermediateValue",
	Key:  "prop_e2d4f221728554ab",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"lt(F.zero, polynomial_eval(p, a))",
			"lt(polynomial_eval(p, b), F.zero)",
		},
		Conclusion: "∃x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(p, x) = F.zero",
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, positive, negative Fact) {
		ordered := OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		reverse := ordered_field.NegationReversesSign.Read(ordered).AsFact()
		negP := arg.TermAs[Fun[Nat, A]]("-p")
		negValues := arg.Have(
			"negating the coefficients negates every value",
			"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(-p, x) = -polynomial_eval(p, x)",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xIn := c.Assume()
				evaluation := c.Have(
					"evaluation at x is a ring homomorphism from the polynomials over F to F",
					"ring_homomorphism(polynomial_ring(field_ring(F)), "+
						"    field_ring(F), "+
						"    λq:(num → A). polynomial_eval(q, x))",
					By(polynomial_evaluation.EvalHomomorphism.Read(ring).At(c.MemberOf[on.F](x, xIn))))
				c.Show(
					"and a ring homomorphism takes the negative of p to the negative of its value",
					By(ring_homomorphism.MapNeg.Read(evaluation), poly))
			}))
		values := arg.Have(
			"the values of p at a and b lie in F",
			"polynomial_eval(p, a) ∈ F.carrier ∧ polynomial_eval(p, b) ∈ F.carrier",
			By(polynomial_evaluation.EvalIn.Read(ring), poly, a, b))
		pa := arg.TermAs[A]("polynomial_eval(p, a)")
		pb := arg.TermAs[A]("polynomial_eval(p, b)")
		below := arg.Have(
			"so −p is negative at a",
			"lt(polynomial_eval(-p, a), F.zero)",
			By(negValues.At(a), reverse.At(pa), positive, values, a))
		above := arg.Have(
			"and positive at b",
			"lt(F.zero, polynomial_eval(-p, b))",
			By(negValues.At(b), reverse.At(pb), negative, values, b))
		y, root := arg.ObtainAs[A](
			"the axiom IntermediateValue gives −p a root strictly between a and b",
			"∃y:A. y ∈ F.carrier ∧ lt(a, y) ∧ lt(y, b) ∧ polynomial_eval(-p, y) = F.zero",
			By(
				IntermediateValue.Read(closed).At(negP, a, b),
				comm_ring.NegIn.Read(polynomial.PolynomialRingOn.Read(ring)),
				poly,
				ab,
				below,
				above))
		arg.Take(y)
		arg.Show(
			"and a root of −p is a root of p",
			ByArith(ring, root, negValues.At(y), polynomial_evaluation.EvalIn.Read(ring), poly))
	}),
})}

// OppositeSignsRoot — A polynomial that vanishes at neither of two points a < b
// and has different signs there has a root strictly between them: nonzero values
// of different signs lie on opposite sides of zero, so p rises through zero from a
// to b, where the axiom IntermediateValue gives the root, or falls through it, where
// DownwardIntermediateValue does.
var OppositeSignsRoot = oppositeSignsRootThm{family.Add(registry.ProofEntry{
	Name: "OppositeSignsRoot",
	Key:  "prop_509cef29dcdfae9c",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"polynomial_eval(p, a) ≠ F.zero",
			"polynomial_eval(p, b) ≠ F.zero",
			"ordered_sign(F, lt, polynomial_eval(p, a)) ≠ ordered_sign(F, lt, polynomial_eval(p, b))",
		},
		Conclusion: "∃x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(p, x) = F.zero",
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, aNonzero, bNonzero, differ Fact) {
		F := arg.TermAs[FieldOps[A]]("F")
		lt := arg.TermAs[Fun2[A, A, Bool]]("lt")
		ordered := OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		comparable := ordered_field.Trichotomy.Read(ordered).AsFact()
		zero := arg.TermAs[A]("F.zero")
		pa := arg.TermAs[A]("polynomial_eval(p, a)")
		pb := arg.TermAs[A]("polynomial_eval(p, b)")
		inCarrier := arg.Have(
			"zero and the values of p at a and b lie in F",
			"F.zero ∈ F.carrier ∧ polynomial_eval(p, a) ∈ F.carrier ∧ polynomial_eval(p, b) ∈ F.carrier",
			By(comm_ring.ZeroIn.Read(ring), polynomial_evaluation.EvalIn.Read(ring), poly, a, b))
		crossing := arg.Have(
			"nonzero values of different signs lie on opposite sides of zero",
			"(lt(polynomial_eval(p, a), F.zero) ∧ lt(F.zero, polynomial_eval(p, b))) ∨ "+
				"(lt(F.zero, polynomial_eval(p, a)) ∧ lt(polynomial_eval(p, b), F.zero))",
			By(
				differ,
				aNonzero,
				bNonzero,
				inCarrier,
				comparable.At(pa, zero),
				comparable.At(pb, zero),
				ordered_field.OrderedSignDef.At(F, lt, pa),
				ordered_field.OrderedSignDef.At(F, lt, pb)))
		arg.Do(crossing.SplitDisj(
			LeftHolds(
				"p rises from negative at a to positive at b",
				Given(func(c *Argument, rising Fact) {
					c.Show(
						"the axiom IntermediateValue puts a root strictly between a and b",
						By(IntermediateValue.Read(closed).At(p, a, b), rising, poly, ab))
				})),
			RightHolds(
				"p falls from positive at a to negative at b",
				Given(func(c *Argument, falling Fact) {
					c.Show(
						"intermediate values for a falling polynomial put a root strictly between a and b",
						By(DownwardIntermediateValue.Read(closed).At(p, a, b), falling, poly, ab))
				})),
		))
	}),
})}

// RootFreeIntervalSign — A polynomial without roots on a closed interval has equal endpoint signs:
// neither endpoint is a root, so signs that differed would give p a root strictly between a and
// b by opposite signs.
var RootFreeIntervalSign = rootFreeIntervalSignThm{family.Add(registry.ProofEntry{
	Name: "RootFreeIntervalSign",
	Key:  "prop_e31fa02bdd42443c",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"∀x:A. " +
				"    x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
		},
		Conclusion: "ordered_sign(F, lt, polynomial_eval(p, a)) = " +
			"ordered_sign(F, lt, polynomial_eval(p, b))",
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, rootFree Fact) {
		between := arg.Unfolded(rootFree, ordered_field.OrderedLeDef)
		endpoints := arg.Have(
			"neither endpoint is a root",
			"polynomial_eval(p, a) ≠ F.zero ∧ polynomial_eval(p, b) ≠ F.zero",
			By(between.At(a), between.At(b), ab, a, b))
		differ := arg.SupposeNot()
		y, root := arg.ObtainAs[A](
			"p would then have a root strictly between a and b, its signs there differing",
			"∃y:A. y ∈ F.carrier ∧ lt(a, y) ∧ lt(y, b) ∧ polynomial_eval(p, y) = F.zero",
			By(OppositeSignsRoot.Read(closed).At(p, a, b), poly, ab, endpoints, differ))
		arg.Show(
			"which the hypothesis rules out",
			By(root, between.At(y)))
	}),
})}

// InjectivePolynomialMonotone — over a real closed field, a polynomial in one variable injective
// on the carrier is strictly increasing or strictly decreasing there: between two points x < y it
// takes every value v strictly between p(x) and p(y), since p − v changes sign from x to y and the
// axiom of a real closed field gives it a root strictly between them (IntermediateValue where it
// rises, DownwardIntermediateValue where it falls); so p is an instance, on the whole carrier, of
// ordered_field.IntermediateValueInjectiveMonotone.
var InjectivePolynomialMonotone = injectivePolynomialMonotoneThm{family.Add(registry.ProofEntry{
	Name: "InjectivePolynomialMonotone",
	Key:  "prop_4778fdadb4113056",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"injective_on(F.carrier, λx:A. polynomial_eval(p, x))",
		},
		Conclusion: "(∀x y:A. " +
			"    x ∈ F.carrier ∧ y ∈ F.carrier ∧ lt(x, y) ⇒ " +
			"    lt(polynomial_eval(p, x), polynomial_eval(p, y))) ∨ " +
			"(∀x y:A. " +
			"    x ∈ F.carrier ∧ y ∈ F.carrier ∧ lt(x, y) ⇒ lt(polynomial_eval(p, y), polynomial_eval(p, x)))",
	}, func(arg *Argument, closedF RealClosedFieldFact[on.F], p *Arrow[Nat, A], over, injective Fact) {
		orderedF := OrderedFieldOn.Read(closedF)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(orderedF))
		intermediate := arg.Have(
			"p takes, strictly between two points, every value strictly between its values there",
			Statement{
				Binders: "∀x y v:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"y ∈ F.carrier",
					"lt(x, y)",
					"v ∈ F.carrier",
					"lt(polynomial_eval(p, x), v) ∧ lt(v, polynomial_eval(p, y)) ∨ " +
						"lt(polynomial_eval(p, y), v) ∧ lt(v, polynomial_eval(p, x))",
				},
				Conclusion: "∃z:A. z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ∧ polynomial_eval(p, z) = v",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				v := b.FixAs[A]("v")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in F",
					"y lies in F",
					"x lies below y",
					"v lies in F",
					"v lies strictly between p(x) and p(y)")
				xm, ym, vm :=
					b.MemberOf[on.F](x, given[0]), b.MemberOf[on.F](y, given[1]), b.MemberOf[on.F](v, given[3])
				px := b.MemberOf[on.F](
					b.TermAs[A]("polynomial_eval(p, x)"),
					GroupPremises(over, polynomial_evaluation.EvalIn.Read(ring).At(p, xm)))
				py := b.MemberOf[on.F](
					b.TermAs[A]("polynomial_eval(p, y)"),
					GroupPremises(over, polynomial_evaluation.EvalIn.Read(ring).At(p, ym)))
				constant, constantDef := b.LetAs[Fun[Nat, A]]("c", "v • basis_vector(0)")
				q, qDef := b.LetAs[Fun[Nat, A]]("q", "p - c")
				qOver := b.Have(
					"q = p − c, with c the constant polynomial v, is a polynomial over F",
					"polynomial_over(F.carrier, q)",
					BySets(
						qDef,
						constantDef,
						over,
						vm,
						polynomial.BasisVectorOver.Read(ring),
						module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
						comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring))))
				qValue := b.Have(
					"q takes the value p(w) − v at every point w of F",
					"∀w:A. w ∈ F.carrier ⇒ polynomial_eval(q, w) = polynomial_eval(p, w) - v",
					Derive(func(c *Argument) {
						w := c.FixAs[A]("w")
						wm := c.MemberOf[on.F](w, c.Assume())
						c.Show(
							"evaluation at w subtracts the value v of the constant from the value of p",
							qDef.Rw(),
							ByArith(
								ring,
								wm,
								vm,
								over,
								constantDef,
								polynomial_evaluation.EvalSub.Read(ring).At(p, constant, wm),
								polynomial_evaluation.EvalConstant.Read(ring).At(vm, wm),
								polynomial_evaluation.EvalIn.Read(ring).At(p, wm),
								polynomial.BasisVectorOver.Read(ring),
								module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
					}))
				signs := b.Have(
					"so q rises through zero from x to y, or falls through it",
					"lt(polynomial_eval(q, x), F.zero) ∧ lt(F.zero, polynomial_eval(q, y)) ∨ "+
						"lt(F.zero, polynomial_eval(q, x)) ∧ lt(polynomial_eval(q, y), F.zero)",
					By(
						given[4],
						qValue.At(x),
						qValue.At(y),
						xm,
						ym,
						ordered_field.SubNegative.Read(orderedF).At(px, vm),
						ordered_field.SubPositive.Read(orderedF).At(vm, py),
						ordered_field.SubPositive.Read(orderedF).At(vm, px),
						ordered_field.SubNegative.Read(orderedF).At(py, vm)))
				z, root := b.ObtainAs[A](
					"the axiom of a real closed field gives q a root z strictly between x and y",
					"∃z:A. z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ∧ polynomial_eval(q, z) = F.zero",
					By(
						signs,
						qOver,
						given[2],
						IntermediateValue.Read(closedF).At(q, xm, ym),
						DownwardIntermediateValue.Read(closedF).At(q, xm, ym)))
				parts := b.Conjuncts(
					root,
					"z lies in F",
					"z lies above x",
					"z lies below y",
					"q vanishes at z")
				zm := b.MemberOf[on.F](z, parts[0])
				taken := b.Have(
					"so p takes the value v at z",
					"polynomial_eval(p, z) = v",
					ByArith(ring, parts[3], qValue.At(z), zm, vm, over, qOver, polynomial_evaluation.EvalIn.Read(ring)))
				b.Take(z)
				b.Show(
					"z lies strictly between x and y, and p takes v there",
					By(parts[0], parts[1], parts[2], taken))
			}))
		arg.Show(
			"p is injective on F and has the intermediate value property there, so it is strictly monotone",
			By(
				ordered_field.IntermediateValueInjectiveMonotone.Read(orderedF).At(
					arg.TermAs[Fun[A, A]]("λx:A. polynomial_eval(p, x)"),
					arg.TermAs[Set[A]]("F.carrier")),
				set_order.SubsetRefl,
				over,
				polynomial_evaluation.EvalIn.Read(ring),
				injective,
				intermediate))
	}),
})}

// EuclideanField — A real closed field is a Euclidean field: it is ordered,
// and a positive a is a square, the polynomial p = x² − a being negative at 0,
// where it is −a, and positive at 1 + a, where it is (1 + a)·a + 1, so that the
// axiom IntermediateValue gives it a root between them, whose square is a.
var EuclideanField = euclideanFieldThm{family.Add(registry.ProofEntry{
	Name: "EuclideanField",
	Key:  "prop_f4f719d7129c0491",
	Build: RealClosedField.Law("euclidean_field(F, lt)", func(
		arg *Argument,
		closed RealClosedFieldFact[on.F],
	) {
		arg.Do(ordered_field.EuclideanField.Intro(
			Case(
				"a real closed field is ordered",
				By(OrderedFieldOn.Read(closed))),
			Case(
				"every positive element is a square",
				Derive(func(d *Argument) {
					point := d.FixAs[A]("a")
					given := d.Conjuncts(
						d.Assume(),
						"a lies in F",
						"a is positive")
					a := d.MemberOf[on.F](point, given[0])
					positive := given[1]
					ordered := OrderedFieldOn.Read(closed)
					ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
					zero := d.MemberOf[on.F](d.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
					one := d.MemberOf[on.F](d.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
					onePlusA := comm_ring.AddIn.Read(ring).At(one, a)
					square := d.TermAs[Fun[Nat, A]]("basis_vector(2)")
					constant := d.TermAs[Fun[Nat, A]]("a • basis_vector(0)")
					p, pDef := d.LetAs[Fun[Nat, A]]("p", "basis_vector(2) - a • basis_vector(0)")
					over := d.Have(
						"p = x² − a is a polynomial over F",
						"polynomial_over(F.carrier, p)",
						BySets(
							pDef,
							a,
							polynomial.BasisVectorOver.Read(ring),
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
							comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring))))
					value := d.Have(
						"p takes the value x·x − a at every point x of F",
						"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) = x * x - a",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.MemberOf[on.F](x, c.Assume())
							c.Show(
								"evaluation at x subtracts the value a of the constant from the value x² of the square",
								pDef.Rw(),
								ByArith(
									ring,
									a,
									xIn,
									polynomial_evaluation.EvalSub.Read(ring).At(square, constant, xIn),
									polynomial_evaluation.EvalBasisVector.Read(ring).At(c.TermAs[Nat]("2"), xIn),
									polynomial_evaluation.EvalConstant.Read(ring).At(a, xIn),
									polynomial.BasisVectorOver.Read(ring),
									module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
						}))
					positiveSum := ordered_field.AddPositive.Read(ordered)
					onePositive := ordered_field.OnePositive.Read(ordered)
					rightEnd := d.Have(
						"one and a are positive, so 1 + a is",
						"lt(F.zero, F.one + a)",
						By(positiveSum.At(one, a), onePositive, positive))
					ends := d.Have(
						"so p takes the value −a at zero and (1 + a)·a + 1 at 1 + a",
						"polynomial_eval(p, F.zero) = -a ∧ polynomial_eval(p, F.one + a) = (F.one + a) * a + F.one",
						ByArith(
							ring,
							value.At(zero),
							value.At(onePlusA),
							a,
							zero,
							onePlusA,
							over,
							polynomial_evaluation.EvalIn.Read(ring)))
					below := d.Have(
						"negation reverses the order against zero, so p is negative at zero, where it is −a",
						"lt(polynomial_eval(p, F.zero), F.zero)",
						By(ends, positive, ordered_field.NegationReversesSign.Read(ordered).At(a)))
					above := d.Have(
						"(1 + a)·a and one are positive, so p is positive at 1 + a",
						"lt(F.zero, polynomial_eval(p, F.one + a))",
						By(
							ends,
							positiveSum.At(comm_ring.MulIn.Read(ring).At(onePlusA, a), one),
							ordered_field.MulPositive.Read(ordered).At(onePlusA, a),
							rightEnd,
							positive,
							onePositive))
					b, root := d.ObtainAs[A](
						"the axiom IntermediateValue gives p a root b strictly between 0 and 1 + a",
						"∃b:A. b ∈ F.carrier ∧ lt(F.zero, b) ∧ lt(b, F.one + a) ∧ polynomial_eval(p, b) = F.zero",
						By(IntermediateValue.Read(closed).At(p, zero, onePlusA), over, rightEnd, below, above))
					d.Take(b)
					d.Show(
						"b·b − a = 0 says b·b = a",
						ByArith(ring, a, root, value.At(b)))
				}))))
	}),
})}

// PositiveSquareRoot — Every positive element of a real closed field has a
// positive square root, a real closed field being Euclidean.
var PositiveSquareRoot = positiveSquareRootThm{family.Add(registry.ProofEntry{
	Name: "PositiveSquareRoot",
	Key:  "prop_97e846efc3cd596e",
	Build: RealClosedField.Law(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ F.carrier",
			"lt(F.zero, a)",
		},
		Conclusion: "∃b:A. b ∈ F.carrier ∧ lt(F.zero, b) ∧ b * b = a",
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], a *Member[A, on.F], positive Fact) {
		arg.Show(
			"the positive square root of a Euclidean field",
			By(positive, ordered_field.PositiveSquareRoot.Read(EuclideanField.Read(closed)).At(a)))
	}),
})}

// HomomorphismOrderEmbedding — a ring homomorphism from a real closed field
// to an ordered field is an order embedding. It is one-to-one, as every
// homomorphism of fields is. A positive u is the square of some s other than
// zero, so i(u) is the nonzero square i(s)·i(s), which is positive; hence i
// sends y - x > 0 to i(y) - i(x) > 0, and it reflects the order as well, the
// order of F being total.
var HomomorphismOrderEmbedding = homomorphismOrderEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "HomomorphismOrderEmbedding",
	Key:  "prop_40cad6892bcaac7a",
	Build: RealClosedField.Law(Statement{
		Binders: "∀G:field_ops(B). ∀ls:(B → B → bool). ∀i:(A → B).",
		Hypotheses: []string{
			"ordered_field_on(G, ls)",
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
		},
		Conclusion: "ordered_field_embedding(F, lt, G, ls, i)",
	}, func(
		a *Argument,
		closedF RealClosedFieldFact[on.F],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		i *Arrow[A, B],
		orderedG ordered_field.OrderedFieldFact[on.G],
		hom Fact,
	) {
		F := a.TermAs[FieldOps[A]]("F")
		lt := a.TermAs[Fun2[A, A, Bool]]("lt")
		orderedF := OrderedFieldOn.Read(closedF)
		fieldF := ordered_field.FieldOn.Read(orderedF)
		fieldG := ordered_field.FieldOn.Read(orderedG)
		ringF := field.RingOn.Read(fieldF)
		ringG := field.RingOn.Read(fieldG)
		injective := a.Have(
			"a homomorphism of fields is one-to-one",
			"injective_on(F.carrier, i)",
			By(fieldF, fieldG, hom, ring_homomorphism.FieldHomomorphismInjective.At(F, G, i)))
		positive := a.Have(
			"i sends a positive element of F to a positive element of G",
			"∀u:A. u ∈ F.carrier ∧ lt(F.zero, u) ⇒ ls(G.zero, i(u))",
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				given := b.Conjuncts(
					b.Assume(),
					"u lies in F",
					"u is positive")
				s, root := b.UnpackAs[A](
					GroupPremises(given[1], PositiveSquareRoot.Read(closedF).At(b.MemberOf[on.F](u, given[0]))),
					"s")
				square := b.Conjuncts(
					root,
					"s lies in F",
					"s is positive",
					"s squares to u")
				image := b.Have(
					"i(s) lies in G",
					"i(s) ∈ G.carrier",
					By(square[0], ring_homomorphism.MapIn.Read(hom)))
				squares := b.Have(
					"i(u) is the square of i(s)",
					"i(u) = G.mul(i(s), i(s))",
					By(Normalized, square[0], square[2], ring_homomorphism.MapMul.Read(hom)))
				nonzero := b.Have(
					"i(s) is not zero: s is not, being positive, and i is one-to-one",
					"i(s) ≠ G.zero",
					By(
						square[0],
						square[1],
						injective,
						functions.InjectiveOnDef,
						ring_homomorphism.MapZero.Read(hom),
						comm_ring.ZeroIn.Read(ringF),
						ordered_field.Irreflexive.Read(orderedF)))
				b.Show(
					"a nonzero square is positive",
					By(
						Normalized,
						image,
						squares,
						nonzero,
						ordered_field.SquarePositive.Read(orderedG).AsFact().At(i.Apply(s))))
			}))
		preserves := a.Have(
			"i preserves the order",
			"∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ∧ lt(x, y) ⇒ ls(i(x), i(y))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in F",
					"y lies in F",
					"x lies below y")
				imageGap := b.Have(
					"y - x is positive, x lying below y, and so is its image, i(y) - i(x)",
					"ls(G.zero, G.sub(i(y), i(x)))",
					By(
						Normalized,
						given[0],
						given[1],
						given[2],
						ordered_field.SubPositive.Read(orderedF).AsFact().At(x, y),
						comm_ring.SubIn.Read(ringF).AsFact().At(y, x),
						positive.At(b.TermAs[A]("y - x")),
						ring_homomorphism.MapSub.Read(hom).AsFact().At(y, x)))
				images := b.Have(
					"i(x) and i(y) lie in G",
					"i(x) ∈ G.carrier ∧ i(y) ∈ G.carrier",
					By(given[0], given[1], ring_homomorphism.MapIn.Read(hom)))
				back := b.Have(
					"adding i(x) sends zero to i(x) and i(y) - i(x) to i(y)",
					"G.add(G.zero, i(x)) = i(x) ∧ G.add(G.sub(i(y), i(x)), i(x)) = i(y)",
					ByArith(ringG, images))
				b.Show(
					"add i(x) to both sides of 0 < i(y) - i(x)",
					By(
						imageGap,
						back,
						images,
						comm_ring.SubIn.Read(ringG).AsFact().At(i.Apply(y), i.Apply(x)),
						comm_ring.ZeroIn.Read(ringG),
						ordered_field.AddOrderIff.Read(orderedG).AsFact().At(
							b.TermAs[B]("G.zero"),
							b.TermAs[B]("G.sub(i(y), i(x))"),
							i.Apply(x))))
			}))
		compares := a.Have(
			"i preserves and reflects the order, the order of F being total",
			"∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ (lt(x, y) ⇔ ls(i(x), i(y)))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				points := b.Assume()
				b.Show(
					"i keeps the linear order of F, so it reflects it",
					By(
						points,
						preserves,
						ring_homomorphism.MapIn.Read(hom),
						ordered_field.Trichotomy.Read(orderedF),
						ordered_field.IncreasingMapReflectsOrder.Read(orderedG).At(
							i, a.TermAs[Set[A]]("F.carrier"), lt, x, y)))
			}))
		a.Show(
			"i is an order embedding",
			By(orderedF, orderedG, hom, injective, compares, ordered_field.OrderedEmbeddingDef))
	}),
})}

// OddDegreeRoot — Every polynomial of odd degree over a real closed field has a root in the field
// (polynomial_evaluation.OddDegreeRootsDef):
// its leading coefficient c is not zero, and far enough out p takes the sign of c at x and, the
// degree being odd, the sign of −c at −x; a polynomial with no root would keep one sign from −x
// to x, and c and −c have opposite signs.
var OddDegreeRoot = oddDegreeRootThm{family.Add(registry.ProofEntry{
	Name: "OddDegreeRoot",
	Key:  "prop_bf3d96eb6831c9e",
	Build: RealClosedField.Law("odd_degree_roots(F)", func(
		arg *Argument,
		closed RealClosedFieldFact[on.F],
	) {
		arg.Do(Unfold(polynomial_evaluation.OddDegreeRootsDef))
		p := arg.FixAs[Fun[Nat, A]]("p")
		given := arg.Conjuncts(
			arg.Assume(),
			"p is a polynomial over F",
			"of odd degree")
		poly, odd := given[0], given[1]
		ordered := OrderedFieldOn.Read(closed)
		transitive := ordered_field.Transitive.Read(ordered)
		comparable := ordered_field.Trichotomy.Read(ordered)
		reverse := ordered_field.NegationReversesSign.Read(ordered)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		powers := comm_ring.MulMonoidOn.Read(ring)
		zero := arg.MemberOf[on.F](arg.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := comm_ring.NegIn.Read(ring).At(one)
		k, degree := arg.UnpackAs[Nat](odd, "k")
		positiveDegree := arg.Have(
			"an odd degree is positive",
			"0 < polynomial_degree(p)",
			ByArith(degree))
		nonzeroVector := arg.Have(
			"so p is not the zero polynomial, whose degree is zero",
			"p ≠ vec_zero",
			By(positiveDegree, polynomial.DegreeVecZero.At(zero), nat_order.LessThanIrrefl))
		leading := arg.Conjuncts(
			GroupPremises(
				poly,
				nonzeroVector,
				polynomial.LeadingCoefficientNonzero.At(zero, arg.TermAs[Set[A]]("F.carrier"), p)),
			"the leading coefficient c of p lies in F",
			"c is not zero")
		lead := arg.MemberOf[on.F](arg.TermAs[A]("p(polynomial_degree(p))"), leading[0])
		minusLead := comm_ring.NegIn.Read(ring).At(lead)
		b, far := arg.UnpackAs[A](
			GroupPremises(poly, nonzeroVector, ordered_field_polynomial.SignsAtInfinity.Read(ordered).At(p)))
		bounds := arg.Conjuncts(
			far,
			"b lies in F",
			"b is positive",
			"past b, p has the sign of c at x and the sign of c·(−1)^deg at −x")
		bPositive, beyond := bounds[1], bounds[2]
		bm := arg.MemberOf[on.F](b, bounds[0])
		square := arg.Have(
			"(−1)² = (−1)·(−1) = 1·1 = 1",
			"monoid_pow(F.mul, F.one, -F.one, 2) = F.one",
			ByArith(
				ring,
				comm_monoid.PowTwoOn.Read(powers).At(minusOne),
				comm_ring.MulNegNegOn.Read(ring).At(one, one)))
		oddPower := arg.Have(
			"so (−1)^(2k + 1) = ((−1)²)^k·(−1) = 1^k·(−1) = −1",
			"monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p)) = -F.one",
			By(
				degree,
				square,
				comm_monoid.PowAddOn.Read(powers).At(minusOne, arg.TermAs[Nat]("2 * k"), arg.TermAs[Nat]("1")),
				comm_monoid.PowPowOn.Read(powers).At(minusOne, arg.TermAs[Nat]("2"), k),
				comm_monoid.IdentityPowOn.Read(powers).At(k),
				comm_monoid.PowOneOn.Read(powers).At(minusOne),
				comm_monoid.LeftIdentityOn.Read(powers).At(minusOne)))
		flip := arg.Have(
			"and c·(−1)^deg = −c",
			"p(polynomial_degree(p)) * monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p)) = "+
				"-p(polynomial_degree(p))",
			ByArith(ring, oddPower, leading[0]))
		signs := ordered_field.SignValues.Read(ordered)
		x := comm_ring.AddIn.Read(ring).At(one, bm)
		minusX := comm_ring.NegIn.Read(ring).At(x)
		pastB := arg.Have(
			"one is positive, so x = 1 + b lies past b",
			"lt(b, F.one + b)",
			By(
				ordered_field.OnePositive.Read(ordered),
				ordered_field.LessThanSelfAddLeft.Read(ordered).At(one, bm)))
		symmetric := arg.Have(
			"x lies above b, which is positive, so −x < 0 < x",
			"lt(-(F.one + b), F.one + b)",
			By(pastB, bPositive, reverse.At(x), transitive.At(zero, bm, x), transitive.At(minusX, zero, x)))
		ends := arg.Have(
			"so p has the sign of c at x and the sign of −c at −x",
			"ordered_sign(F, lt, polynomial_eval(p, F.one + b)) = "+
				"ordered_sign(F, lt, p(polynomial_degree(p))) ∧ "+
				"ordered_sign(F, lt, polynomial_eval(p, -(F.one + b))) = "+
				"ordered_sign(F, lt, -p(polynomial_degree(p)))",
			By(beyond.At(x), flip, pastB, x))
		distinct := arg.Have(
			"the signs −1 and 1 differ",
			"-1 ≠ int_of_num(1)",
			ByArith())
		noRoot := arg.SupposeNot()
		oneSign := arg.Have(
			"a polynomial with no root keeps one sign from −x to x",
			"ordered_sign(F, lt, polynomial_eval(p, -(F.one + b))) = "+
				"ordered_sign(F, lt, polynomial_eval(p, F.one + b))",
			By(RootFreeIntervalSign.Read(closed).At(p, minusX, x), noRoot, poly, symmetric))
		arg.Show(
			"so c and −c would share a sign, but c ≠ 0 puts one of them below zero and the other above",
			By(
				distinct,
				oneSign,
				ends,
				leading[1],
				signs.At(lead),
				signs.At(minusLead),
				comparable.At(lead, zero),
				reverse.At(lead)))
	}),
})}

// ConsecutiveRootsRolle — Between two roots a < b of a polynomial over a real closed field with
// no root strictly between them, the derivative has a root. Split x − a and then x − b off to
// their full multiplicities, p = (x − a)^(m+1)·(x − b)^(n+1)·s with s not vanishing at a or b; then
// s has no root on ⟦a, b⟧, so s(a) and s(b) share a sign. The derivative is (x − a)^m·(x − b)^n·h
// with h = M(x − b)s + (x − a)(Ns + (x − b)s'), M and N the positive numerals m + 1 and n + 1.
// The sign of a product being the product of the signs, h(a) = −M(b − a)s(a) has the sign opposite
// to that of s(a) and h(b) = (b − a)Ns(b) the sign of s(b), so h takes nonzero values of different
// signs at a and b, which gives h, and with it the derivative, a root strictly between them.
var ConsecutiveRootsRolle = consecutiveRootsRolleThm{family.Add(registry.ProofEntry{
	Name: "ConsecutiveRootsRolle",
	Key:  "prop_241acac646a2ddb7",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"polynomial_eval(p, a) = F.zero",
			"polynomial_eval(p, b) = F.zero",
			"∀x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(polynomial_derivative(p), x) = F.zero",
		Abbrev: Abbrev{
			{Name: "numeral", Text: "λk:num. monoid_pow(F.add, F.zero, F.one, k)"},
		},
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, aRoot, bRoot, between Fact) {
		ordered := OrderedFieldOn.Read(closed)
		irreflexive := ordered_field.Irreflexive.Read(ordered).AsFact()
		reverse := ordered_field.NegationReversesSign.Read(ordered)
		fieldF := ordered_field.FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		domain := integral_domain.FieldIntegralDomain.Read(fieldF)
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		z, middle := arg.UnpackAs[A](
			GroupPremises(ab, ordered_field.DenseOrder.Read(ordered).At(a, b)), "z")
		nonzero := arg.Have(
			"p is not the zero polynomial: it does not vanish at a point z strictly between a and b",
			"p ≠ vec_zero",
			By(Normalized, middle, between.At(z), polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(z)))
		m, g, first := arg.Unpack2As[Nat, Fun[Nat, A]](
			GroupPremises(poly, nonzero, aRoot, polynomial_roots.RootMultiplicity.Read(domain).At(p, a)),
			"m",
			"g")
		cofactorAtA := arg.Conjuncts(
			first,
			"g is a polynomial over F",
			"g does not vanish at a",
			"p is (x − a)^(m+1) times g",
			"the roots of p are a and the roots of g")
		gOver, gAtA, pFactored, pRoots := cofactorAtA[0], cofactorAtA[1], cofactorAtA[2], cofactorAtA[3]
		gAtB := arg.Have(
			"b is a root of p other than a, so a root of g",
			"polynomial_eval(g, b) = F.zero",
			BySets(pRoots, bRoot, b, ab, irreflexive.At(b), polynomial_roots.PolynomialRootsDef))
		gNonzero := arg.Have(
			"g is not the zero polynomial, not vanishing at a",
			"g ≠ vec_zero",
			By(Normalized, gAtA, polynomial_evaluation.EvalVecZero.Read(ring).At(a)))
		n, s, second := arg.Unpack2As[Nat, Fun[Nat, A]](
			GroupPremises(gOver, gNonzero, gAtB, polynomial_roots.RootMultiplicity.Read(domain).At(g, b)),
			"n",
			"s")
		cofactorAtB := arg.Conjuncts(
			second,
			"s is a polynomial over F",
			"s does not vanish at b",
			"g is (x − b)^(n+1) times s",
			"the roots of g are b and the roots of s")
		sOver, sAtB, gFactored, gRoots := cofactorAtB[0], cofactorAtB[1], cofactorAtB[2], cofactorAtB[3]
		sAtA := arg.Have(
			"s does not vanish at a either, since g does not",
			"polynomial_eval(s, a) ≠ F.zero",
			BySets(gRoots, gAtA, a, polynomial_roots.PolynomialRootsDef))
		rootsOfS := arg.Have(
			"a root of s is a root of g, and so of p",
			"∀x:A. x ∈ F.carrier ∧ polynomial_eval(s, x) = F.zero ⇒ polynomial_eval(p, x) = F.zero",
			BySets(pRoots, gRoots, polynomial_roots.PolynomialRootsDef))
		rootFree := arg.Have(
			"so s has no root on ⟦a, b⟧: one there would be a root of p at a, at b or strictly between",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"ordered_le(lt, a, x)",
					"ordered_le(lt, x, b)",
				},
				Conclusion: "polynomial_eval(s, x) ≠ F.zero",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				within := c.Unfolded(c.Assume(), ordered_field.OrderedLeDef)
				c.Show(
					"s does not vanish at a or at b, and p does not vanish strictly between them",
					By(within, rootsOfS.At(x), between.At(x), sAtA, sAtB))
			}))
		oneSign := arg.Have(
			"s has no root on ⟦a, b⟧, so it takes one sign at a and at b",
			"ordered_sign(F, lt, polynomial_eval(s, a)) = ordered_sign(F, lt, polynomial_eval(s, b))",
			By(RootFreeIntervalSign.Read(closed).At(s, a, b), sOver, ab, rootFree))
		h, hDef := arg.LetAs[Fun[Nat, A]](
			"h",
			"«numeral»(suc(m)) • polynomial_mul(«linear»(b), s) + "+
				"polynomial_mul(«linear»(a), "+
				"    «numeral»(suc(n)) • s + polynomial_mul(«linear»(b), polynomial_derivative(s)))")
		factored := arg.Have(
			"so p = (x − a)^(m+1)·(x − b)^(n+1)·s, whose derivative "+
				"keeps (x − a)^m·(x − b)^n with the cofactor h",
			"polynomial_derivative(p) = "+
				"polynomial_mul(polynomial_pow(«linear»(a), m), polynomial_mul(polynomial_pow(«linear»(b), n), h))",
			By(
				Normalized,
				pFactored,
				gFactored,
				hDef,
				sOver,
				polynomial_roots.LinearPowersDerivative.Read(ring).At(m, n, a, b, s)))
		numerals := comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))
		mIn := numerals.At(one, arg.TermAs[Nat]("suc(m)"))
		nIn := numerals.At(one, arg.TermAs[Nat]("suc(n)"))
		polynomials := polynomial.PolynomialRingOn.Read(ring)
		hOver := arg.Have(
			"h is a polynomial over F",
			"polynomial_over(F.carrier, h)",
			BySets(
				hDef,
				sOver,
				mIn,
				nIn,
				polynomial_roots.LinearFactor.Read(ring).At(a),
				polynomial_roots.LinearFactor.Read(ring).At(b),
				polynomial.DerivativeOverCarrier.Read(ring).At(s),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
				comm_ring.AddIn.Read(polynomials),
				comm_ring.MulIn.Read(polynomials)))
		hValue := arg.Have(
			"h takes the value (m + 1)(x − b)s(x) + (x − a)((n + 1)s(x) + (x − b)s'(x)) at every point x of F",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ F.carrier"},
				Conclusion: "polynomial_eval(h, x) = " +
					"«numeral»(suc(m)) * ((x - b) * polynomial_eval(s, x)) + " +
					"(x - a) * " +
					"(«numeral»(suc(n)) * polynomial_eval(s, x) + " +
					"    (x - b) * polynomial_eval(polynomial_derivative(s), x))",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xm := c.MemberOf[on.F](x, c.Assume())
				linearA := c.TermAs[Fun[Nat, A]]("«linear»(a)")
				linearB := c.TermAs[Fun[Nat, A]]("«linear»(b)")
				derivative := c.TermAs[Fun[Nat, A]]("polynomial_derivative(s)")
				multipleOfS := c.TermAs[Fun[Nat, A]]("«numeral»(suc(n)) • s")
				shiftedS := c.TermAs[Fun[Nat, A]]("polynomial_mul(«linear»(b), s)")
				shiftedDerivative := c.TermAs[Fun[Nat, A]]("polynomial_mul(«linear»(b), polynomial_derivative(s))")
				inner := c.TermAs[Fun[Nat, A]](
					"«numeral»(suc(n)) • s + polynomial_mul(«linear»(b), polynomial_derivative(s))")
				firstSummand := c.TermAs[Fun[Nat, A]]("«numeral»(suc(m)) • polynomial_mul(«linear»(b), s)")
				secondSummand := c.TermAs[Fun[Nat, A]](
					"polynomial_mul(«linear»(a), " +
						"    «numeral»(suc(n)) • s + polynomial_mul(«linear»(b), polynomial_derivative(s)))")
				c.Show(
					"evaluation at x is additive and multiplicative and takes a multiple to the multiple of the value",
					hDef.Rw(),
					ByArith(
						ring,
						xm,
						a,
						b,
						sOver,
						mIn,
						nIn,
						polynomial_evaluation.EvalAdd.Read(ring).At(firstSummand, secondSummand, xm),
						polynomial_evaluation.EvalScalar.Read(ring).At(mIn, xm, shiftedS),
						polynomial_evaluation.EvalMul.Read(ring).At(linearB, s, xm),
						polynomial_evaluation.EvalMul.Read(ring).At(linearA, inner, xm),
						polynomial_evaluation.EvalAdd.Read(ring).At(multipleOfS, shiftedDerivative, xm),
						polynomial_evaluation.EvalScalar.Read(ring).At(nIn, xm, s),
						polynomial_evaluation.EvalMul.Read(ring).At(linearB, derivative, xm),
						polynomial_roots.LinearFactor.Read(ring).At(a),
						polynomial_roots.LinearFactor.Read(ring).At(b),
						polynomial.DerivativeOverCarrier.Read(ring).At(s),
						polynomial.PolynomialMulOver.Read(ring),
						polynomial_evaluation.EvalIn.Read(ring),
						module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
						comm_ring.AddIn.Read(polynomials)))
			}))
		ends := arg.Have(
			"so h is −(m + 1)(b − a)s(a) at a and (b − a)(n + 1)s(b) at b",
			"polynomial_eval(h, a) = -«numeral»(suc(m)) * ((b - a) * polynomial_eval(s, a)) ∧ "+
				"polynomial_eval(h, b) = (b - a) * («numeral»(suc(n)) * polynomial_eval(s, b))",
			ByArith(
				ring,
				hValue.At(a),
				hValue.At(b),
				a,
				b,
				sOver,
				hOver,
				mIn,
				nIn,
				polynomial.DerivativeOverCarrier.Read(ring).At(s),
				polynomial_evaluation.EvalIn.Read(ring)))
		sign := ordered_field.SignValues.Read(ordered)
		multiplicative := ordered_field.SignMul.Read(ordered)
		mulIn, evaluation := comm_ring.MulIn.Read(ring), polynomial_evaluation.EvalIn.Read(ring)
		gap := comm_ring.SubIn.Read(ring).At(b, a)
		minusM := comm_ring.NegIn.Read(ring).At(mIn)
		saM := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(s, a)"), GroupPremises(sOver, evaluation.At(s, a)))
		sbM := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(s, b)"), GroupPremises(sOver, evaluation.At(s, b)))
		haM := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(h, a)"), GroupPremises(hOver, evaluation.At(h, a)))
		hbM := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(h, b)"), GroupPremises(hOver, evaluation.At(h, b)))
		numeralsPositive := arg.Have(
			"the numerals m + 1 and n + 1 are positive",
			"lt(F.zero, «numeral»(suc(m))) ∧ lt(F.zero, «numeral»(suc(n)))",
			By(
				nat_order.ZeroLessThanSuc.At(m),
				nat_order.ZeroLessThanSuc.At(n),
				ordered_field.MultipleOfOnePositive.Read(ordered).At(arg.TermAs[Nat]("suc(m)")),
				ordered_field.MultipleOfOnePositive.Read(ordered).At(arg.TermAs[Nat]("suc(n)"))))
		factorSigns := arg.Have(
			"−(m + 1) is negative, while b − a and n + 1 are positive",
			"ordered_sign(F, lt, -«numeral»(suc(m))) = -1 ∧ "+
				"ordered_sign(F, lt, b - a) = 1 ∧ "+
				"ordered_sign(F, lt, «numeral»(suc(n))) = 1",
			By(
				numeralsPositive,
				ab,
				ordered_field.SubPositive.Read(ordered).At(a, b),
				reverse.At(mIn),
				sign.At(minusM),
				sign.At(gap),
				sign.At(nIn)))
		signs := arg.Have(
			"the sign of a product is the product of the signs, so h has "+
				"the sign opposite to that of s at a, and the sign of s at b",
			"ordered_sign(F, lt, polynomial_eval(h, a)) = -ordered_sign(F, lt, polynomial_eval(s, a)) ∧ "+
				"ordered_sign(F, lt, polynomial_eval(h, b)) = ordered_sign(F, lt, polynomial_eval(s, b))",
			ByArith(
				ends,
				factorSigns,
				multiplicative.At(minusM, mulIn.At(gap, saM)),
				multiplicative.At(gap, saM),
				multiplicative.At(gap, mulIn.At(nIn, sbM)),
				multiplicative.At(nIn, sbM)))
		differ := arg.Have(
			"s does not vanish at a and takes one sign at a "+
				"and b, so the signs of h there are not 0 and differ",
			"ordered_sign(F, lt, polynomial_eval(h, a)) ≠ 0 ∧ "+
				"ordered_sign(F, lt, polynomial_eval(h, b)) ≠ 0 ∧ "+
				"ordered_sign(F, lt, polynomial_eval(h, a)) ≠ ordered_sign(F, lt, polynomial_eval(h, b))",
			ByArith(signs, oneSign, sAtA, sign.At(saM)))
		hNonzero := arg.Have(
			"so h vanishes at neither a nor b",
			"polynomial_eval(h, a) ≠ F.zero ∧ polynomial_eval(h, b) ≠ F.zero",
			By(differ, sign.At(haM), sign.At(hbM)))
		x, root := arg.ObtainAs[A](
			"h takes nonzero values of different signs at a and b, so it has a root x strictly between them",
			"∃x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(h, x) = F.zero",
			By(OppositeSignsRoot.Read(closed).At(h, a, b), hOver, ab, hNonzero, differ))
		powerA := arg.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(a), m)")
		powerB := arg.TermAs[Fun[Nat, A]]("polynomial_pow(«linear»(b), n)")
		arg.Take(x)
		arg.Show(
			"a root of h is a root of (x − b)^n·h and of (x − a)^m·(x − b)^n·h, the derivative of p",
			By(
				root,
				factored,
				hOver,
				a,
				b,
				polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(h, powerB, x),
				polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(
					arg.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_pow(«linear»(b), n), h)"), powerA, x),
				polynomial.PolynomialMulOver.Read(ring),
				polynomial.PolynomialPowOver.Read(ring),
				polynomial_roots.LinearFactor.Read(ring).At(a),
				polynomial_roots.LinearFactor.Read(ring).At(b)))
	}),
})}

// RolleBetweenRoots — Between two roots a < b of a polynomial over a real closed field lies a root
// of its derivative. The zero polynomial's derivative vanishes everywhere, and a point strictly
// between a and b serves. A nonzero polynomial has finitely many roots, so among its roots in
// ⟦a, b⟭ there is a greatest one, r; no root lies strictly between r and b, and Rolle between the
// consecutive roots r and b gives the root.
var RolleBetweenRoots = rolleBetweenRootsThm{family.Add(registry.ProofEntry{
	Name: "RolleBetweenRoots",
	Key:  "prop_979467a0ebc63de6",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"polynomial_eval(p, a) = F.zero",
			"polynomial_eval(p, b) = F.zero",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(polynomial_derivative(p), x) = F.zero",
		Abbrev: Abbrev{
			{Name: "roots", Text: "{y:A | " +
				"    y ∈ polynomial_roots(F.carrier, p) ∧ ordered_le(lt, a, y) ∧ lt(y, b)}"},
		},
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, aRoot, bRoot Fact) {
		lt := arg.TermAs[Fun2[A, A, Bool]]("lt")
		ordered := OrderedFieldOn.Read(closed)
		irreflexive := ordered_field.Irreflexive.Read(ordered).AsFact()
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		fieldF := ordered_field.FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		nonzero := arg.Unless(
			arg.TermAs[Bool]("p = vec_zero"),
			"set the zero polynomial aside",
			Given(func(c *Argument, zeroPolynomial Fact) {
				z, middle := c.UnpackAs[A](GroupPremises(ab, ordered_field.DenseOrder.Read(ordered).At(a, b)), "z")
				c.Take(z)
				c.Show(
					"its derivative is zero, which vanishes at a point z strictly between a and b",
					By(
						Normalized,
						middle,
						zeroPolynomial,
						polynomial.DerivativeVecZero.Read(ring),
						polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(z)))
			}))
		rootsSet := arg.TermAs[Set[A]]("«roots»")
		allRoots := arg.TermAs[Set[A]]("polynomial_roots(F.carrier, p)")
		finiteRoots := arg.Have(
			"a nonzero polynomial over a field has finitely many roots",
			"finite(polynomial_roots(F.carrier, p))",
			By(
				poly,
				nonzero,
				polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(fieldF)).At(p)))
		aIsRoot := arg.Have(
			"a is a root of p",
			"a ∈ polynomial_roots(F.carrier, p)",
			Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
			BySets(a, aRoot))
		aInRoots := arg.Have(
			"a is a root of p in ⟦a, b⟭",
			"a ∈ «roots»",
			BySets(aIsRoot, ab, ordered_field.OrderedLeDef.At(lt, a, a)))
		bounded := arg.Have(
			"the roots of p in ⟦a, b⟭ are finitely many points of F, a among them",
			"finite(«roots») ∧ «roots» ⊆ F.carrier ∧ «roots» ≠ ∅",
			BySets(
				finiteRoots,
				aInRoots,
				finite_set.FiniteSubset.At(rootsSet, allRoots),
				polynomial_roots.PolynomialRootsDef))
		r, greatest := arg.UnpackAs[A](
			GroupPremises(bounded, ordered_field.FiniteGreatest.Read(ordered).At(rootsSet)), "r")
		top := arg.Conjuncts(
			greatest,
			"r is a root of p in ⟦a, b⟭",
			"every root of p in ⟦a, b⟭ is at or below r")
		rFacts := arg.Conjuncts(
			top[0],
			"r is a root of p",
			"a ≤ r",
			"r < b")
		rRoot := arg.Conjuncts(
			arg.Unfolded(rFacts[0], polynomial_roots.PolynomialRootsDef),
			"r lies in F",
			"p vanishes at r")
		rIn := rRoot[0]
		consecutive := arg.Have(
			"no root of p lies strictly between r and b: it would be a root in ⟦a, b⟭ above r",
			"∀x:A. x ∈ F.carrier ∧ lt(r, x) ∧ lt(x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				above := c.Assume()
				fromA := c.Have(
					"a ≤ r < x puts x above a",
					"ordered_le(lt, a, x)",
					By(
						above,
						rFacts[1],
						rIn,
						a,
						transitive.At(a, r, x),
						ordered_field.OrderedLeDef.At(lt, a, r),
						ordered_field.OrderedLeDef.At(lt, a, x)))
				candidate := c.Have(
					"a root at x would be a root of p in ⟦a, b⟭",
					"polynomial_eval(p, x) = F.zero ⇒ x ∈ «roots»",
					BySets(above, fromA, polynomial_roots.PolynomialRootsDef))
				c.Show(
					"and so would be r or lie below r, against r < x",
					By(
						candidate,
						top[1].At(x),
						ordered_field.OrderedLeDef.At(lt, x, r),
						above,
						rIn,
						transitive.At(x, r, x),
						irreflexive.At(x)))
			}))
		y, derivativeRoot := arg.UnpackAs[A](
			GroupPremises(
				poly,
				rFacts[2],
				rRoot[1],
				bRoot,
				consecutive,
				ConsecutiveRootsRolle.Read(closed).At(p, arg.MemberOf[on.F](r, rIn), b)),
			"y")
		arg.Take(y)
		arg.Show(
			"y serves, lying above a since a ≤ r < y",
			By(
				Normalized,
				derivativeRoot,
				rFacts[1],
				rIn,
				a,
				transitive.At(a, r, y),
				ordered_field.OrderedLeDef.At(lt, a, r)))
	}),
})}

// PolynomialRolle — Equal values of a polynomial over a real closed field at a < b give a root of
// its derivative strictly between them: subtracting the constant c = p(a) leaves q = p − c, which
// vanishes at a and at b and has the derivative of p, and Rolle between the roots a and b of q
// gives the root.
var PolynomialRolle = polynomialRolleThm{family.Add(registry.ProofEntry{
	Name: "PolynomialRolle",
	Key:  "prop_3f0b338f1ae3481a",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
			"polynomial_eval(p, a) = polynomial_eval(p, b)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ∧ polynomial_eval(polynomial_derivative(p), x) = F.zero",
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab, equal Fact) {
		ordered := OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		value := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(p, a)"),
			GroupPremises(poly, polynomial_evaluation.EvalIn.Read(ring).At(p, a)))
		constant := arg.TermAs[Fun[Nat, A]]("polynomial_eval(p, a) • basis_vector(0)")
		q, qDef := arg.LetAs[Fun[Nat, A]]("q", "p - polynomial_eval(p, a) • basis_vector(0)")
		qOver := arg.Have(
			"q = p − p(a) is a polynomial over F",
			"polynomial_over(F.carrier, q)",
			BySets(
				qDef,
				poly,
				value,
				polynomial.BasisVectorOver.Read(ring),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
				comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring))))
		qValue := arg.Have(
			"q takes the value p(x) − p(a) at every point x of F",
			"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(q, x) = polynomial_eval(p, x) - polynomial_eval(p, a)",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xm := c.MemberOf[on.F](x, c.Assume())
				c.Show(
					"evaluation at x subtracts the value p(a) of the constant from the value of p",
					qDef.Rw(),
					ByArith(
						ring,
						xm,
						value,
						poly,
						polynomial_evaluation.EvalSub.Read(ring).At(p, constant, xm),
						polynomial_evaluation.EvalConstant.Read(ring).At(value, xm),
						polynomial_evaluation.EvalIn.Read(ring).At(p, xm),
						polynomial.BasisVectorOver.Read(ring),
						module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
			}))
		roots := arg.Have(
			"so q vanishes at a, and at b, where p takes the same value",
			"polynomial_eval(q, a) = F.zero ∧ polynomial_eval(q, b) = F.zero",
			ByArith(
				ring,
				qValue.At(a),
				qValue.At(b),
				a,
				b,
				equal,
				poly,
				qOver,
				polynomial_evaluation.EvalIn.Read(ring)))
		sameDerivative := arg.Have(
			"q and p differ only in the constant coefficient, which the derivative does not read",
			"polynomial_derivative(q) = polynomial_derivative(p)",
			Derive(func(c *Argument) {
				c.Do(qDef.Rw(), Funext())
				c.FixAs[Nat]("i")
				c.Do(Simp(
					Fwd(polynomial.PolynomialDerivativeDef),
					Fwd(vec_space.VecSubDef),
					Fwd(vec_space.VecScalarMulDef),
					Fwd(vec_space.BasisVectorDef)))
				coefficient := c.Have(
					"the coefficient of p past i lies in F",
					"p(suc(i)) ∈ F.carrier",
					By(poly, polynomial.PolynomialOverDef))
				c.Show(
					"past the constant term the coefficients of q are those of p",
					ByArith(
						ring,
						coefficient,
						value,
						comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).At(
							c.MemberOf[on.F](c.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring)), c.TermAs[Nat]("suc(i)"))))
			}))
		arg.Show(
			"Rolle between the roots a and b of q gives a root of its derivative, which is that of p",
			By(RolleBetweenRoots.Read(closed).At(q, a, b), qOver, ab, roots, sameDerivative))
	}),
})}

// PolynomialMeanValue — A polynomial over a real closed field takes, at some point strictly between
// a < b, a derivative value equal to its secant slope: p'(x)·(b − a) = p(b) − p(a). The polynomial
// q = (b − a)·p + (p(a) − p(b))·(x − a), which is (b − a) times p less the line through its
// endpoint values, takes the value (b − a)·p(a) at a and at b; by linearity of the derivative, x − a
// having derivative one, q' = (b − a)·p' + (p(a) − p(b)); and Rolle for q gives a root of q', where
// (b − a)·p'(x) = p(b) − p(a).
var PolynomialMeanValue = polynomialMeanValueThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMeanValue",
	Key:  "prop_b75e4af0c6dc085b",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"lt(a, b)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ F.carrier ∧ " +
			"    lt(a, x) ∧ " +
			"    lt(x, b) ∧ " +
			"    polynomial_eval(polynomial_derivative(p), x) * (b - a) = " +
			"    polynomial_eval(p, b) - polynomial_eval(p, a)",
		Abbrev: Abbrev{
			{Name: "drop", Text: "polynomial_eval(p, a) - polynomial_eval(p, b)"},
		},
	}, func(arg *Argument, closed RealClosedFieldFact[on.F], p *Arrow[Nat, A], a, b *Member[A, on.F],
		poly, ab Fact) {
		ordered := OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		pa := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(p, a)"),
			GroupPremises(poly, polynomial_evaluation.EvalIn.Read(ring).At(p, a)))
		pb := arg.MemberOf[on.F](
			arg.TermAs[A]("polynomial_eval(p, b)"),
			GroupPremises(poly, polynomial_evaluation.EvalIn.Read(ring).At(p, b)))
		width, drop := comm_ring.SubIn.Read(ring).At(b, a), comm_ring.SubIn.Read(ring).At(pa, pb)
		line := arg.TermAs[Fun[Nat, A]]("«linear»(a)")
		scaledP := arg.TermAs[Fun[Nat, A]]("(b - a) • p")
		scaledLine := arg.TermAs[Fun[Nat, A]]("«drop» • «linear»(a)")
		derivativeP := arg.TermAs[Fun[Nat, A]]("polynomial_derivative(p)")
		q, qDef := arg.LetAs[Fun[Nat, A]]("q", "(b - a) • p + «drop» • «linear»(a)")
		summands := arg.Have(
			"x − a, (b − a)·p and (p(a) − p(b))·(x − a) are polynomials over F",
			"polynomial_over(F.carrier, «linear»(a)) ∧ "+
				"polynomial_over(F.carrier, (b - a) • p) ∧ "+
				"polynomial_over(F.carrier, «drop» • «linear»(a))",
			By(
				width,
				drop,
				poly,
				polynomial_roots.LinearFactor.Read(ring).At(a),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
		qOver := arg.Have(
			"so their sum q is a polynomial over F",
			"polynomial_over(F.carrier, q)",
			qDef.Rw(),
			By(summands, comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ring))))
		qValue := arg.Have(
			"q takes the value (b − a)·p(x) + (p(a) − p(b))·(x − a) at every point x of F",
			"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(q, x) = (b - a) * polynomial_eval(p, x) + «drop» * (x - a)",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xm := c.MemberOf[on.F](x, c.Assume())
				c.Show(
					"evaluation at x is additive, lets the scalars out and takes x − a to x − a",
					qDef.Rw(),
					ByArith(
						ring,
						xm,
						width,
						drop,
						poly,
						summands,
						polynomial_roots.LinearFactor.Read(ring).At(a),
						polynomial_evaluation.EvalAdd.Read(ring).At(scaledP, scaledLine, xm),
						polynomial_evaluation.EvalScalar.Read(ring).At(width, xm, p),
						polynomial_evaluation.EvalScalar.Read(ring).At(drop, xm, line)))
			}))
		endpoints := arg.Have(
			"q takes the value (b − a)·p(a) at a and at b",
			"polynomial_eval(q, a) = polynomial_eval(q, b)",
			ByArith(
				ring,
				qValue.At(a),
				qValue.At(b),
				pa,
				pb,
				a,
				b,
				qOver,
				polynomial_evaluation.EvalIn.Read(ring).At(q, a),
				polynomial_evaluation.EvalIn.Read(ring).At(q, b)))
		coefficients := arg.Have(
			"the coefficients of p, of x − a and of the two summands of q lie in F",
			"(∀i:num. p(i) ∈ F.carrier) ∧ "+
				"(∀i:num. «linear»(a)(i) ∈ F.carrier) ∧ "+
				"(∀i:num. ((b - a) • p)(i) ∈ F.carrier ∧ («drop» • «linear»(a))(i) ∈ F.carrier)",
			By(poly, summands, polynomial.PolynomialOverDef))
		derivative := arg.Have(
			"the derivative is linear and x − a has derivative one, so q' = (b − a)·p' + (p(a) − p(b))",
			"polynomial_derivative(q) = (b - a) • polynomial_derivative(p) + «drop» • basis_vector(0)",
			qDef.Rw(),
			By(
				width,
				drop,
				coefficients,
				polynomial.DerivativeAdd.Read(ring).At(scaledP, scaledLine),
				polynomial.DerivativeScalar.Read(ring).At(width, p),
				polynomial.DerivativeScalar.Read(ring).At(drop, line),
				polynomial_roots.LinearFactorDerivative.Read(ring).At(a)))
		y, root := arg.UnpackAs[A](
			GroupPremises(qOver, ab, endpoints, PolynomialRolle.Read(closed).At(q, a, b)), "y")
		rolle := arg.Conjuncts(
			root,
			"y lies in F",
			"a < y",
			"y < b",
			"the derivative of q vanishes at y")
		ym := arg.MemberOf[on.F](y, rolle[0])
		derivativeValue := arg.Have(
			"so q'(y) = (b − a)·p'(y) + (p(a) − p(b))",
			"polynomial_eval(polynomial_derivative(q), y) = "+
				"(b - a) * polynomial_eval(polynomial_derivative(p), y) + «drop»",
			derivative.Rw(),
			ByArith(
				ring,
				ym,
				width,
				drop,
				poly,
				polynomial.DerivativeOverCarrier.Read(ring).At(p),
				polynomial.BasisVectorOver.Read(ring),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
				polynomial_evaluation.EvalAdd.Read(ring).At(
					arg.TermAs[Fun[Nat, A]]("(b - a) • polynomial_derivative(p)"),
					arg.TermAs[Fun[Nat, A]]("«drop» • basis_vector(0)"),
					ym),
				polynomial_evaluation.EvalScalar.Read(ring).At(width, ym, derivativeP),
				polynomial_evaluation.EvalConstant.Read(ring).At(drop, ym),
				polynomial_evaluation.EvalIn.Read(ring).At(derivativeP, ym)))
		arg.Take(y)
		arg.Show(
			"y serves: q'(y) = 0 says (b − a)·p'(y) = p(b) − p(a)",
			ByArith(
				ring,
				ym,
				rolle[1],
				rolle[2],
				rolle[3],
				derivativeValue,
				a,
				b,
				pa,
				pb,
				poly,
				polynomial.DerivativeOverCarrier.Read(ring).At(p),
				polynomial_evaluation.EvalIn.Read(ring).At(derivativeP, ym)))
	}),
})}

// DerivativeSignMonotone — a polynomial whose derivative has the sign σ at
// every point strictly between x < y changes by the sign σ from x to y: the
// mean value theorem writes p(y) − p(x) as p′(c)·(y − x) for some c between
// them, the sign of a product is the product of the signs, and y − x is
// positive.
var DerivativeSignMonotone = derivativeSignMonotoneThm{family.Add(registry.ProofEntry{
	Name: "DerivativeSignMonotone",
	Key:  "prop_65302f67896297a2",
	Build: RealClosedField.Law(Statement{
		Binders: "∀p:(num → A). ∀x y:A. ∀σ:int.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"lt(x, y)",
			"∀z:A. " +
				"    z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ⇒ " +
				"    ordered_sign(F, lt, polynomial_eval(polynomial_derivative(p), z)) = σ",
		},
		Conclusion: "ordered_sign(F, lt, polynomial_eval(p, y) - polynomial_eval(p, x)) = σ",
	}, func(
		arg *Argument,
		closed RealClosedFieldFact[on.F],
		p *Arrow[Nat, A],
		x, y *Member[A, on.F],
		σ *Expr[Int],
		poly, xy, slope Fact,
	) {
		ordered := OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		c, mean := arg.UnpackAs[A](
			GroupPremises(poly, xy, PolynomialMeanValue.Read(closed).At(p, x, y)), "c")
		at := arg.Conjuncts(
			mean,
			"c lies in F",
			"x < c",
			"c < y",
			"p′(c)·(y − x) = p(y) − p(x)")
		cm := arg.MemberOf[on.F](c, at[0])
		width := comm_ring.SubIn.Read(ring).At(y, x)
		positive := arg.Have(
			"y − x is positive",
			"ordered_sign(F, lt, y - x) = &1",
			By(
				xy,
				width,
				ordered_field.SubPositive.Read(ordered).At(x, y),
				ordered_field.SignValues.Read(ordered).AsFact().At(arg.TermAs[A]("y - x"))))
		unit := arg.Have(
			"σ · 1 = σ",
			"σ * &1 = σ",
			ByArith())
		arg.Show(
			"p(y) − p(x) = p′(c)·(y − x) has the sign σ · 1",
			By(
				at[3],
				positive,
				unit,
				slope.At(c),
				at[0],
				at[1],
				at[2],
				width,
				polynomial_evaluation.EvalIn.Read(ring).At(arg.TermAs[Fun[Nat, A]]("polynomial_derivative(p)"), cm),
				poly,
				polynomial.DerivativeOverCarrier.Read(ring).At(p),
				ordered_field.SignMul.Read(ordered).AsFact().At(
					arg.TermAs[A]("polynomial_eval(polynomial_derivative(p), c)"), arg.TermAs[A]("y - x"))))
	}),
})}
