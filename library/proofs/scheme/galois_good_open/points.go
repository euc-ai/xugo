package galois_good_open

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// PointAtPolynomialValue — a point ψ of D with values in U, a ring map fixing
// k, carries the value at t of a polynomial c over k to the value of c at ψ(t):
// a ring map carries a value of c to the value of the image of c at the image
// of t, and ψ fixes the coefficients.
var PointAtPolynomialValue = pointAtPolynomialValueThm{family.Add(registry.ProofEntry{
	Name: "PointAtPolynomialValue",
	Key:  "prop_1935736152e02624",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k D U:set(A). ∀t:A. ∀c:(num → A). ∀ψ:(A → A).",
		Hypotheses: []string{
			"k ⊆ D",
			"t ∈ D",
			"polynomial_over(k, c)",
			"ψ ∈ algebra_points(restrict_ring(field_ring(M), D), restrict_ring(field_ring(M), U), k, λy:A. y)",
		},
		Conclusion: "ψ(polynomial_eval(c, t)) = polynomial_eval(c, ψ(t))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, D, U *Expr[Set[A]],
		t *Expr[A],
		c *Arrow[Nat, A],
		ψ *Arrow[A, A],
		kInD, tInD, overK, point Fact,
	) {
		onD := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), D)")
		target := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), U)")
		zero := a.TermAs[A]("M.zero")
		data := a.Conjuncts(
			a.Simplified(point, Fwd(algebra_points.AlgebraPointsMember)),
			"ψ is a ring map",
			"ψ fixes k",
			"ψ vanishes off D")
		along := a.Have(
			"a ring map carries the value of c to the value of its image",
			"ψ(polynomial_eval(c, t)) = polynomial_eval(λi:num. ψ(c(i)), ψ(t))",
			By(
				data[0],
				tInD,
				overK,
				kInD,
				polynomial.PolynomialOverMono.At(zero, k, D, c),
				polynomial_evaluation.EvalAlongHomomorphism.At(onD, target, ψ, c, t)))
		coefficientsFixed := a.Have(
			"ψ fixes the coefficients of c",
			"(λi:num. ψ(c(i))) = c",
			Funext(),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inK := b.Have(
					"c(i) lies in k",
					"c(i) ∈ k",
					By(overK, polynomial.PolynomialOverDef))
				b.Show(
					"and ψ fixes k",
					By(inK, data[1].At(c.Apply(i))))
			}))
		a.Show(
			"so ψ(c(t)) is c(ψ(t))",
			By(along, coefficientsFixed))
	}),
})}

// GeometricPointMember — a point of C with values in the algebraic elements: a ring map
// from C to them, fixing k and vanishing off C.
var GeometricPointMember = geometricPointMemberThm{family.Add(registry.ProofEntry{
	Name: "GeometricPointMember",
	Key:  "prop_14ebdadd2cad6923",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_ops(A). ∀k C:set(A). ∀ev:(A → A).",
		Conclusion: "ev ∈ geometric_evaluation_points(M, k, C) ⇔ " +
			"ring_homomorphism(restrict_ring(field_ring(M), C), «target», ev) ∧ " +
			"(∀x:A. x ∈ k ⇒ ev(x) = x) ∧ " +
			"(∀x:A. x ∉ C ⇒ ev(x) = M.zero)",
		Abbrev: Abbrev{
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(a *Argument, M *Expr[FieldOps[A]], k, C *Expr[Set[A]], ev *Arrow[A, A]) {
		a.Do(
			Simp(Fwd(GeometricEvaluationPointsDef), Fwd(algebra_points.AlgebraPointsMember)),
			Basic())
	}),
})}

// EvaluationActionIdentity — the identity leaves a map vanishing off D where it is.
var EvaluationActionIdentity = evaluationActionIdentityThm{family.Add(registry.ProofEntry{
	Name: "EvaluationActionIdentity",
	Key:  "prop_d08e3f2a1a0c4601",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀D:set(A). ∀ev:(A → A).",
		Hypotheses: []string{"∀x:A. x ∉ D ⇒ ev(x) = R.zero"},
		Conclusion: "evaluation_action(R, D, permutation_identity, ev) = ev",
	}, func(a *Argument, R *Expr[RingOps[A]], D *Expr[Set[A]], ev *Arrow[A, A], vanishes Fact) {
		a.Do(Funext())
		x := a.FixAs[A]("x")
		identity := a.TermAs[symmetric_group.Permutation[A]]("permutation_identity")
		a.Show(
			"the inverse of the identity fixes x, and off D the map vanishes",
			By(
				Normalized,
				vanishes,
				EvaluationActionDef.At(R, D, identity, ev, x),
				symmetric_group.MapInverseRight.At(identity, x),
				symmetric_group.MapIdentity))
	}),
})}

// EvaluationActionCompose — when the inverse of g keeps D the action on maps is
// multiplicative at g: on D both sides read the map at h⁻¹(g⁻¹(x)), the point the
// product g h carries to x, and off D both vanish.
var EvaluationActionCompose = evaluationActionComposeThm{family.Add(registry.ProofEntry{
	Name: "EvaluationActionCompose",
	Key:  "prop_40276e68550c228e",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀D:set(A). ∀g h:permutation(A). ∀ev:(A → A).",
		Hypotheses: []string{"∀y:A. y ∈ D ⇒ permutation_map(permutation_inverse(g), y) ∈ D"},
		Conclusion: "evaluation_action(R, D, permutation_compose(g, h), ev) = " +
			"evaluation_action(R, D, g, evaluation_action(R, D, h, ev))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		D *Expr[Set[A]],
		g, h *Expr[symmetric_group.Permutation[A]],
		ev *Arrow[A, A],
		keeps Fact,
	) {
		a.Do(Funext())
		x := a.FixAs[A]("x")
		product := a.TermAs[symmetric_group.Permutation[A]]("permutation_compose(g, h)")
		first := a.TermAs[A]("permutation_map(permutation_inverse(g), x)")
		preimage := a.TermAs[A](
			"permutation_map(permutation_inverse(h), permutation_map(permutation_inverse(g), x))")
		carried := a.Have(
			"g h carries h⁻¹(g⁻¹(x)) to x",
			"permutation_map(permutation_compose(g, h), "+
				"    permutation_map(permutation_inverse(h), permutation_map(permutation_inverse(g), x))) = "+
				"x",
			By(
				symmetric_group.MapCompose.At(g, h, preimage),
				symmetric_group.MapInverseRight.At(h, first),
				symmetric_group.MapInverseRight.At(g, x)))
		undone := a.Have(
			"so the inverse of the product reads x there",
			"permutation_map(permutation_inverse(permutation_compose(g, h)), x) = "+
				"permutation_map(permutation_inverse(h), permutation_map(permutation_inverse(g), x))",
			By(Normalized, carried, symmetric_group.MapInverse.At(product, preimage)))
		a.Show(
			"the two sides agree on D and vanish off it",
			Simp(Fwd(EvaluationActionDef)),
			undone.Rw(),
			By(keeps.At(x)))
	}),
})}

// FibreAway — inverting c(t) in a ring D over k changes no fibre over a point
// x with c(x) ≠ 0: restriction to D is a bijection of the fibre of D[1/c(t)]
// over x onto the fibre of D. A point of D over x sends c(t) to c(x), which is
// a unit, so it extends over the inverse (AlgebraPointsAway), uniquely.
var FibreAway = fibreAwayThm{family.Add(registry.ProofEntry{
	Name: "FibreAway",
	Key:  "prop_edb5903291028333",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "points", Text: "λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), " +
				"        restrict_ring(field_ring(M), algebraic_elements(M, k)), " +
				"        k, " +
				"        λy:A. y)"},
			{Name: "fibre", Text: "λX:set(A). geometric_fibre(M, k, X, t, x)"},
			{Name: "away", Text: "ring_away(field_ring(M), D, polynomial_eval(c, t))"},
			{Name: "inverted", Text: "restrict_ring(field_ring(M), «away»)"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ D, ev(y), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀k D:set(A). ∀t x:A. ∀c:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(M), D)",
			"k ⊆ D",
			"t ∈ D",
			"polynomial_over(k, c)",
			"polynomial_eval(c, t) ≠ M.zero",
			"x ∈ algebraic_elements(M, k)",
			"subfield(M, k)",
			"polynomial_eval(c, x) ≠ M.zero",
		},
		Conclusion: "injective_on(«fibre»(«away»), «restriction») ∧ " +
			"image(«restriction», «fibre»(«away»)) = «fibre»(D)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, D *Expr[Set[A]],
		t, x *Expr[A],
		c *Arrow[Nat, A],
		subringD, kInD, tInD, overK, valueNonzero, xInClosure, subfieldK, rootFree Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		target := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), algebraic_elements(M, k))")
		identity := a.TermAs[Fun[A, A]]("λy:A. y")
		value := a.TermAs[A]("polynomial_eval(c, t)")
		away := a.TermAs[Set[A]]("«away»")
		inverted := a.TermAs[RingOps[A]]("«inverted»")
		restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		fibreAway := a.TermAs[Set[Fun[A, A]]]("«fibre»(«away»)")
		pointsAway := a.TermAs[Set[Fun[A, A]]]("«points»(«away»)")
		zero := a.TermAs[A]("M.zero")
		onDRing := a.Have(
			"D is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), D))",
			By(subringD, comm_ring.SubringRingOn.Read(ring).At(D)))
		coefficients := a.Have(
			"c has its coefficients in D",
			"polynomial_over(D, c)",
			By(overK, kInD, polynomial.PolynomialOverMono.At(zero, k, D, c)))
		valueInD := a.Have(
			"c(t) lies in D",
			"polynomial_eval(c, t) ∈ D",
			By(tInD, coefficients, polynomial_evaluation.EvalIn.Read(onDRing).AsFact().At(c, t)))
		DInField := a.Have(
			"D lies in M",
			"D ⊆ M.carrier",
			By(comm_ring.SubringSubset.Read(subringD)))
		vm := a.MemberOf[on.M](value, a.Have(
			"c(t) lies in M",
			"polynomial_eval(c, t) ∈ M.carrier",
			BySets(valueInD, DInField)))
		inverseValue := field.InvIn.Read(M).At(vm)
		twice := module_record.RestrictRingTwice.At(fieldRing, away, D)
		localization := a.Have(
			"D with c(t) inverted is the localization of D at the powers of c(t)",
			"is_localization_on(restrict_ring(«inverted», D), "+
				"    monoid_powers(«inverted».mul, «inverted».one, polynomial_eval(c, t)), "+
				"    «inverted», "+
				"    λx:A. x)",
			By(
				ring,
				valueInD,
				subringD,
				inverseValue,
				valueNonzero,
				field.MulRightInverseOn.Read(M).At(vm),
				ring_away.RingAwayIsLocalization.At(fieldRing, D, value, inverseValue),
				twice,
				module_record.RingMulDef,
				module_record.RingOneDef,
				module_record.RestrictRingDef))
		bijection := a.Conjuncts(
			a.Have(
				"so restriction to D is a bijection from its points onto the points of D making c(t) a unit",
				"injective_on(«points»(«away»), «restriction») ∧ "+
					"image(«restriction», «points»(«away»)) = "+
					"{ψ:A → A | "+
					"    ψ ∈ «points»(D) ∧ "+
					"    ring_unit(restrict_ring(field_ring(M), algebraic_elements(M, k)), ψ(polynomial_eval(c, t)))}",
				By(
					valueInD,
					kInD,
					localization,
					algebra_point_bounds.AlgebraPointsAway.At(inverted, target, D, k, identity, value),
					twice)),
			"restriction is injective on the points of the localization",
			"its image is the points of D making c(t) a unit")
		fibreMember := a.Have(
			"A map lies in the fibre of a chart X over x when it is a point of X sending t to x",
			"∀X:set(A). ∀ev:(A → A). ev ∈ «fibre»(X) ⇔ ev ∈ «points»(X) ∧ ev(t) = x",
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				b.FixAs[Fun[A, A]]("ev")
				b.Show(
					"the geometric points of X are its points over the algebraic elements",
					BySets(GeometricFibreDef.At(ops, k, X, t, x), GeometricEvaluationPointsDef.At(ops, k, X)))
			}))
		inside := a.Have(
			"The fibre lies among the points",
			"«fibre»(«away») ⊆ «points»(«away»)",
			BySets(fibreMember.At(away)))
		injective := a.Have(
			"Restriction is injective on the fibre",
			"injective_on(«fibre»(«away»), «restriction»)",
			By(bijection[0], inside, functions.InjectiveOnSubset.At(restriction, fibreAway, pointsAway)))
		closureData := a.Conjuncts(
			a.Have(
				"The algebraic elements are a subfield holding k",
				"subfield(M, algebraic_elements(M, k)) ∧ k ⊆ algebraic_elements(M, k)",
				By(subfieldK, algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k))),
			"the algebraic elements are a subfield",
			"they hold k")
		closureSubfield := closureData[0]
		closureSet := a.TermAs[Set[A]]("algebraic_elements(M, k)")
		closureRing := a.Have(
			"The algebraic elements are a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), algebraic_elements(M, k)))",
			By(closureSubfield, field.SubfieldCommRing.Read(M).At(closureSet)))
		rootValue, rootIs := a.LetAs[A]("w", "polynomial_eval(c, x)")
		rootInClosure := a.Have(
			"c(x) is algebraic",
			"w ∈ algebraic_elements(M, k)",
			By(
				Normalized,
				rootIs,
				xInClosure,
				overK,
				closureData[1],
				polynomial.PolynomialOverMono.At(zero, k, closureSet, c),
				polynomial_evaluation.EvalIn.Read(closureRing).AsFact().At(c, x)))
		rootInverse := a.Have(
			"so is its inverse",
			"M.inv(w) ∈ algebraic_elements(M, k)",
			By(closureSubfield, rootInClosure, field.SubfieldInv.At(ops, closureSet, rootValue)))
		rootm := a.MemberOf[on.M](rootValue, a.Have(
			"c(x) lies in M",
			"w ∈ M.carrier",
			BySets(rootInClosure, algebraic_element.AlgebraicElementsDef.At(ops, k))))
		rootUnit := a.Have(
			"c(x) is a unit among the algebraic elements",
			"ring_unit(restrict_ring(field_ring(M), algebraic_elements(M, k)), w)",
			Unfold(ring_ideal.RingUnitDef),
			By(rootInClosure, rootInverse, rootFree, rootIs, field.MulRightInverseOn.Read(M).At(rootm)))
		valueAt := a.Have(
			"A point of D over x sends c(t) to c(x)",
			"∀ψ:(A → A). ψ ∈ «fibre»(D) ⇒ ψ(polynomial_eval(c, t)) = w",
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				inFibre := b.Assume()
				parts := b.Conjuncts(
					b.Have(
						"ψ is a point of D with ψ(t) = x",
						"ψ ∈ «points»(D) ∧ ψ(t) = x",
						By(inFibre, fibreMember.At(D, ψ))),
					"ψ is a point of D",
					"ψ(t) = x")
				b.Show(
					"ψ carries c(t) to c(ψ(t)), and ψ(t) is x",
					By(
						kInD,
						tInD,
						overK,
						parts[0],
						parts[1],
						rootIs,
						PointAtPolynomialValue.Read(M).At(k, D, closureSet, t, c, ψ)))
			}))
		imageIsFibre := a.Have(
			"A map is the restriction of a point of the fibre exactly when it lies in the fibre of D",
			"image(«restriction», «fibre»(«away»)) = «fibre»(D)",
			Simp(Fwd(set_basic.Extension)),
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				b.Iff()
				b.Forward(
					"the restriction of a point over x is a point over x",
					func(c *Argument, inImage Fact) {
						e, chosen := c.ObtainAs[Fun[A, A]](
							"ψ restricts a point of the fibre",
							"∃e:(A → A). ψ = «restriction»(e) ∧ e ∈ «fibre»(«away»)",
							By(inImage, set_basic.InImage.At(restriction, fibreAway, ψ)))
						parts := c.Conjuncts(
							chosen,
							"ψ restricts e",
							"e lies in the fibre")
						data := c.Conjuncts(
							c.Have(
								"e is a point with e(t) = x",
								"e ∈ «points»(«away») ∧ e(t) = x",
								By(parts[1], fibreMember.At(away, e))),
							"e is a point",
							"e(t) = x")
						restricts := c.Have(
							"ψ restricts a point",
							"∃g:(A → A). ψ = «restriction»(g) ∧ g ∈ «points»(«away»)",
							Witness(e),
							By(parts[0], data[0]))
						amongPoints := c.Have(
							"so ψ lies in the image on the points",
							"ψ ∈ image(«restriction», «points»(«away»))",
							By(restricts, set_basic.InImage.At(restriction, pointsAway, ψ)))
						point := c.Have(
							"so ψ is a point of D",
							"ψ ∈ «points»(D)",
							BySets(amongPoints, bijection[1]))
						atT := c.Have(
							"and ψ(t) is e(t), t lying in D",
							"ψ(t) = x",
							By(parts[0], data[1], tInD))
						c.Show(
							"so ψ lies in the fibre of D",
							By(point, atT, fibreMember.At(D, ψ)))
					})
				b.Backward(
					"a point of D over x extends over the inverse",
					func(c *Argument, inFibre Fact) {
						parts := c.Conjuncts(
							c.Have(
								"ψ is a point of D with ψ(t) = x",
								"ψ ∈ «points»(D) ∧ ψ(t) = x",
								By(inFibre, fibreMember.At(D, ψ))),
							"ψ is a point of D",
							"ψ(t) = x")
						unitAt := c.Have(
							"ψ sends c(t) to the unit c(x)",
							"ring_unit(restrict_ring(field_ring(M), algebraic_elements(M, k)), ψ(polynomial_eval(c, t)))",
							By(rootUnit, inFibre, valueAt.At(ψ)))
						amongPoints := c.Have(
							"so ψ lies in the image on the points",
							"ψ ∈ image(«restriction», «points»(«away»))",
							BySets(parts[0], unitAt, bijection[1]))
						e, chosen := c.ObtainAs[Fun[A, A]](
							"ψ restricts a point of the localization",
							"∃e:(A → A). ψ = «restriction»(e) ∧ e ∈ «points»(«away»)",
							By(amongPoints, set_basic.InImage.At(restriction, pointsAway, ψ)))
						restricted := c.Conjuncts(
							chosen,
							"ψ restricts e",
							"e is a point")
						atT := c.Have(
							"e(t) is ψ(t), t lying in D",
							"e(t) = x",
							By(restricted[0], parts[1], tInD))
						inLocalFibre := c.Have(
							"so e lies in the fibre",
							"e ∈ «fibre»(«away»)",
							By(restricted[1], atT, fibreMember.At(away, e)))
						restricts := c.Have(
							"ψ restricts a point of the fibre",
							"∃g:(A → A). ψ = «restriction»(g) ∧ g ∈ «fibre»(«away»)",
							Witness(e),
							By(restricted[0], inLocalFibre))
						c.Show(
							"so ψ lies in the image on the fibre",
							By(restricts, set_basic.InImage.At(restriction, fibreAway, ψ)))
					})
			}))
		a.Show(
			"Restriction is injective on the fibre, and its image is the fibre of D",
			By(injective, imageIsFibre))
	}),
})}

// EvaluationActionPoint — an automorphism of L whose inverse keeps a subring D
// moves points of D to points of D: the action is the point composed with the
// inverse on D, and the inverse fixes k.
var EvaluationActionPoint = evaluationActionPointThm{family.Add(registry.ProofEntry{
	Name: "EvaluationActionPoint",
	Key:  "prop_f9cc0725d771e45c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "undo", Text: "permutation_map(permutation_inverse(s))"},
			{Name: "closure", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "onD", Text: "restrict_ring(field_ring(M), D)"},
		},
		Binders: "∀M:field_on(A). ∀k K L D:set(A). ∀s:permutation(A). ∀ev:(A → A).",
		Hypotheses: []string{
			"subfield(M, L)",
			"k ⊆ K",
			"subring(field_ring(M), D)",
			"D ⊆ L",
			"k ⊆ D",
			"permutation_inverse(s) ∈ field_automorphisms(M, K, L)",
			"∀y:A. y ∈ D ⇒ «undo»(y) ∈ D",
			"ev ∈ geometric_evaluation_points(M, k, D)",
		},
		Conclusion: "evaluation_action(field_ring(M), D, s, ev) ∈ geometric_evaluation_points(M, k, D)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K, L, D *Expr[Set[A]],
		s *Expr[symmetric_group.Permutation[A]],
		ev *Arrow[A, A],
		subfieldL, kInK, subringD, DInL, kInD, inverseIn, keepsD, point Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		onD := a.TermAs[RingOps[A]]("«onD»")
		closure := a.TermAs[RingOps[A]]("«closure»")
		undo := a.TermAs[Fun[A, A]]("«undo»")
		action := a.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), D, s, ev)")
		composed := a.TermAs[Fun[A, A]]("λy:A. ev(«undo»(y))")
		onL := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, L))")
		inPoints := a.Have(
			"ev is a point of D",
			"ev ∈ algebra_points(«onD», «closure», k, λx:A. x)",
			By(point, GeometricEvaluationPointsDef.At(ops, k, D)))
		pointData := a.Conjuncts(
			a.Simplified(inPoints, Fwd(algebra_points.AlgebraPointsMember)),
			"ev is a ring map",
			"ev fixes k",
			"ev vanishes off D")
		fixes := a.Have(
			"The inverse of s fixes K",
			"∀x:A. x ∈ K ⇒ «undo»(x) = x",
			BySets(inverseIn, field_automorphism.FieldAutomorphismsDef.At(ops, K, L)))
		subringInL := a.Have(
			"D is a subring read in L",
			"subring(field_ring(restrict_field(M, L)), D)",
			By(
				Normalized,
				subringD,
				DInL,
				field.RestrictFieldRing.At(ops, L),
				comm_ring.SubringRestrict.At(fieldRing, D, L)))
		onLMap := a.Have(
			"The inverse of s is a ring map on L",
			"ring_homomorphism(field_ring(restrict_field(M, L)), field_ring(restrict_field(M, L)), «undo»)",
			By(
				subfieldL,
				inverseIn,
				field_automorphism.AutomorphismRingHomomorphism.Read(M).AsFact().At(
					K, L, a.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)"))))
		sameRing := a.Have(
			"D read in L is D read in M",
			"restrict_ring(field_ring(restrict_field(M, L)), D) = «onD»",
			By(field.RestrictFieldRecords.At(ops, L, D)))
		onDMap := a.Have(
			"so it is a ring map on D, into D",
			"ring_homomorphism(«onD», «onD», «undo»)",
			By(
				Normalized,
				sameRing,
				onLMap,
				subringInL,
				keepsD,
				ring_homomorphism.RingHomRestrictSource.At(onL, onL, undo, D),
				ring_homomorphism.RingHomCorestrict.At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(restrict_field(M, L)), D)"), onL, undo, D)))
		composedMap := a.Have(
			"The point composed with it is a ring map on D",
			"ring_homomorphism(«onD», «closure», λy:A. ev(«undo»(y)))",
			By(onDMap, pointData[0], ring_homomorphism.RingHomCompose.At(onD, onD, closure, undo, ev)))
		onValues := a.Have(
			"On D the action is that composition",
			"∀x:A. x ∈ D ⇒ evaluation_action(field_ring(M), D, s, ev, x) = ev(«undo»(x))",
			Simp(Fwd(EvaluationActionDef)),
			BySets())
		actionMap := a.Have(
			"so the action is a ring map on D",
			"ring_homomorphism(«onD», «closure», evaluation_action(field_ring(M), D, s, ev))",
			By(composedMap, onValues, ring_homomorphism.RingHomCongruence.At(onD, closure, composed, action)))
		prescribed := a.Have(
			"It fixes k, which the inverse of s and the point both fix",
			"∀x:A. x ∈ k ⇒ evaluation_action(field_ring(M), D, s, ev, x) = x",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inK := b.Assume()
				inD := b.Have(
					"x lies in D",
					"x ∈ D",
					BySets(inK, kInD))
				fixed := b.Have(
					"x lies in K",
					"x ∈ K",
					BySets(inK, kInK))
				b.Show(
					"the inverse of s fixes x and ev fixes x",
					By(Normalized, inK, inD, fixed, onValues.At(x), fixes.At(x), pointData[1].At(x)))
			}))
		vanishes := a.Have(
			"and it vanishes off D",
			"∀x:A. x ∉ D ⇒ evaluation_action(field_ring(M), D, s, ev, x) = «closure».zero",
			Simp(Fwd(EvaluationActionDef)),
			BySets())
		a.Show(
			"so the action is a point of D",
			Simp(Fwd(GeometricEvaluationPointsDef), Fwd(algebra_points.AlgebraPointsMember)),
			By(actionMap, prescribed, vanishes))
	}),
})}

// EvaluationActionKeepsFibre — an automorphism whose inverse keeps a subring C moves a
// point of C to a point of C with the same value at t, for t in the fixed field K.
var EvaluationActionKeepsFibre = evaluationActionKeepsFibreThm{family.Add(registry.ProofEntry{
	Name: "EvaluationActionKeepsFibre",
	Key:  "prop_97ced8d6adc57b93",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K L C:set(A). ∀t:A. ∀s:permutation(A). ∀ev:(A → A).",
		Hypotheses: []string{
			"subfield(M, L)",
			"k ⊆ K",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"k ⊆ C",
			"t ∈ K",
			"t ∈ C",
			"permutation_inverse(s) ∈ field_automorphisms(M, K, L)",
			"∀y:A. y ∈ C ⇒ permutation_map(permutation_inverse(s), y) ∈ C",
			"ev ∈ geometric_evaluation_points(M, k, C)",
		},
		Conclusion: "evaluation_action(field_ring(M), C, s, ev) ∈ geometric_evaluation_points(M, k, C) ∧ " +
			"evaluation_action(field_ring(M), C, s, ev, t) = ev(t)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, K, L, C *Expr[Set[A]],
		t *Expr[A],
		s *Expr[symmetric_group.Permutation[A]],
		ev *Arrow[A, A],
		subL, kInK, subC, cInL, kInC, tInK, tInC, inverseIn, keeps, evIn Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		fixes := arg.Have(
			"the inverse of s fixes K",
			"∀x:A. x ∈ K ⇒ permutation_map(permutation_inverse(s), x) = x",
			BySets(inverseIn, field_automorphism.FieldAutomorphismsDef.At(fieldM, K, L)))
		value := arg.Have(
			"so it fixes t, a point of C",
			"evaluation_action(field_ring(M), C, s, ev, t) = ev(t)",
			Simp(Fwd(EvaluationActionDef)),
			GroupPremises(tInK, fixes.At(t)).Rw(),
			By(tInC))
		arg.Show(
			"and the action keeps the points of C",
			By(
				M,
				subL,
				kInK,
				subC,
				cInL,
				kInC,
				inverseIn,
				keeps,
				evIn,
				value,
				EvaluationActionPoint.Read(M).At(k, K, L, C, s, ev)))
	}),
})}

// InvariantChartFacts — the invariants in a subring C of L of a group H of
// automorphisms over K are a subring of C holding what lies in both C and K:
// they are the meet of C with the fixed field of H.
var InvariantChartFacts = invariantChartFactsThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartFacts",
	Key:  "prop_aa124f83db882d3a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K L C:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(M, L)",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"H ⊆ field_automorphisms(M, K, L)",
		},
		Conclusion: "subring(field_ring(M), invariant_chart(C, H)) ∧ " +
			"invariant_chart(C, H) ⊆ C ∧ " +
			"(∀y:A. y ∈ C ∧ y ∈ K ⇒ y ∈ invariant_chart(C, H))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		subfieldL, subringC, CInL, HInAutomorphisms Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		empty := a.TermAs[Set[A]]("∅")
		overNothing := a.Have(
			"H consists of automorphisms over nothing",
			"H ⊆ field_automorphisms(M, ∅, L)",
			BySets(HInAutomorphisms, field_automorphism.AutomorphismsAntitone.Read(M).AsFact().At(empty, K, L)))
		fixed := a.TermAs[Set[A]]("fixed_field(L, H)")
		subfieldFixed := a.Have(
			"The fixed field of H is a subfield",
			"subfield(M, fixed_field(L, H))",
			By(subfieldL, overNothing, field_automorphism.FixedFieldSubfield.Read(M).AsFact().At(L, H)))
		subringFixed := a.Have(
			"so it is a subring",
			"subring(field_ring(M), fixed_field(L, H))",
			By(subfieldFixed, field.SubfieldSubring.Read(M).At(fixed)))
		member := a.Have(
			"The invariants of C are the members of C that the fixed field holds",
			"∀y:A. y ∈ invariant_chart(C, H) ⇔ y ∈ C ∧ y ∈ fixed_field(L, H)",
			Derive(func(b *Argument) {
				b.FixAs[A]("y")
				b.Show(
					"both read: y lies in C and H fixes it",
					BySets(CInL, InvariantChartDef.At(C, H), field_automorphism.FixedFieldDef.At(L, H)))
			}))
		subringMeet := a.Have(
			"The invariants are a subring, as a meet of two subrings",
			"subring(field_ring(M), invariant_chart(C, H))",
			Simp(Fwd(comm_ring.SubringDef)),
			BySets(
				a.Unfolded(subringC, comm_ring.SubringDef),
				a.Unfolded(subringFixed, comm_ring.SubringDef),
				member))
		kFixed := a.Have(
			"H fixes K",
			"∀y:A. y ∈ C ∧ y ∈ K ⇒ y ∈ invariant_chart(C, H)",
			BySets(
				CInL,
				HInAutomorphisms,
				InvariantChartDef.At(C, H),
				field_automorphism.FieldAutomorphismsDef.At(ops, K, L)))
		inside := a.Have(
			"The invariants lie in C",
			"invariant_chart(C, H) ⊆ C",
			BySets(member))
		a.Show(
			"the three facts",
			By(subringMeet, inside, kFixed))
	}),
})}

// AutomorphismOnStableRing — an automorphism of L keeping a subring D is a ring map of
// D to itself.
var AutomorphismOnStableRing = automorphismOnStableRingThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismOnStableRing",
	Key:  "prop_5705c80f024bf4e2",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K L D:set(A). ∀s:permutation(A).",
		Hypotheses: []string{
			"subfield(M, L)",
			"subring(field_ring(M), D)",
			"D ⊆ L",
			"s ∈ field_automorphisms(M, K, L)",
			"∀y:A. y ∈ D ⇒ permutation_map(s, y) ∈ D",
		},
		Conclusion: "ring_homomorphism(«onD», «onD», permutation_map(s))",
		Abbrev: Abbrev{
			{Name: "onD", Text: "restrict_ring(field_ring(M), D)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L, D *Expr[Set[A]],
		s *Expr[symmetric_group.Permutation[A]],
		subL, subD, dInL, sIn, keeps Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		onL := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, L))")
		onD := a.TermAs[RingOps[A]]("restrict_ring(field_ring(restrict_field(M, L)), D)")
		e := a.TermAs[Fun[A, A]]("permutation_map(s)")
		readInL := a.Have(
			"D is a subring read in L",
			"subring(field_ring(restrict_field(M, L)), D)",
			By(
				Normalized,
				subD,
				dInL,
				field.RestrictFieldRing.At(ops, L),
				comm_ring.SubringRestrict.At(fieldRing, D, L)))
		onLMap := a.Have(
			"s is a ring map on L",
			"ring_homomorphism(field_ring(restrict_field(M, L)), "+
				"    field_ring(restrict_field(M, L)), "+
				"    permutation_map(s))",
			By(subL, sIn, field_automorphism.AutomorphismRingHomomorphism.Read(M).AsFact().At(K, L, s)))
		a.Show(
			"so on D, into D",
			By(
				Normalized,
				field.RestrictFieldRecords.At(ops, L, D),
				onLMap,
				readInL,
				keeps,
				ring_homomorphism.RingHomRestrictSource.At(onL, onL, e, D),
				ring_homomorphism.RingHomCorestrict.At(onD, onL, e, D)))
	}),
})}

// PointRestricts — a point of a ring restricts to a point of any subring
// holding the set the points are prescribed on: its restriction is a ring map
// on the subring, equal to the point there and zero off it.
var PointRestricts = pointRestrictsThm{family.Add(registry.ProofEntry{
	Name: "PointRestricts",
	Key:  "prop_789c4abe6fc6beb5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀S k:set(A). ∀i φ:(A → B).",
		Hypotheses: []string{
			"subring(R, S)",
			"k ⊆ S",
			"φ ∈ algebra_points(R, T, k, i)",
		},
		Conclusion: "(λx:A. COND(x ∈ S, φ(x), T.zero)) ∈ algebra_points(restrict_ring(R, S), T, k, i)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		S, k *Expr[Set[A]],
		i, φ *Arrow[A, B],
		subringS, kInS, point Fact,
	) {
		onS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
		restricted := a.TermAs[Fun[A, B]]("λx:A. COND(x ∈ S, φ(x), T.zero)")
		data := a.Conjuncts(
			a.Have(
				"φ is a ring map fixing what i prescribes on k",
				"ring_homomorphism(R, T, φ) ∧ (∀x:A. x ∈ k ⇒ φ(x) = i(x)) ∧ (∀x:A. x ∉ R.carrier ⇒ φ(x) = T.zero)",
				By(point, algebra_points.AlgebraPointsMember.At(R, T, k, i, φ))),
			"φ is a ring map",
			"φ is prescribed on k",
			"φ vanishes off R")
		onSubring := a.Have(
			"φ is a ring map on S",
			"ring_homomorphism(restrict_ring(R, S), T, φ)",
			By(data[0], subringS, ring_homomorphism.RingHomRestrictSource.At(R, T, φ, S)))
		restrictedMap := a.Have(
			"so is its restriction, equal to it on S",
			"ring_homomorphism(restrict_ring(R, S), T, λx:A. COND(x ∈ S, φ(x), T.zero))",
			By(onSubring, ring_homomorphism.RingHomCongruence.At(onS, T, φ, restricted)))
		a.Show(
			"it is prescribed on k, which lies in S, and vanishes off S",
			BySets(data[1], kInS, restrictedMap, algebra_points.AlgebraPointsDef.At(onS, T, k, i)))
	}),
})}
