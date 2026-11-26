// embedding_adjoin.go — extending a ring map out of a subring S to S[z]
// along an adjoined element z: at a root of every moved relation of z, at
// any point for a transcendental z, and at a root of the moved monic
// relation of least degree; and so a field embedding across one algebraic
// element, with the divisibility its transported minimal polynomial keeps.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialImageLift — a ring map out of S extends to S[z], sending z to y, as soon as
// y is a root of every polynomial over S that vanishes at z, moved along ε: the values at
// y of the moved polynomials then factor through their values at z.
var PolynomialImageLift = polynomialImageLiftThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageLift",
	Key:  "prop_b9ee1b7886cc0511",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀T:ring_ops(B). ∀S:set(A). ∀ε:(A → B). ∀z:A. ∀y:B.",
		Hypotheses: []string{
			"subring(R, S)",
			"z ∈ R.carrier",
			"ring_homomorphism(restrict_ring(R, S), T, ε)",
			"y ∈ T.carrier",
			"∀g:(num → A). polynomial_over(S, g) ∧ «atZ»(g) = R.zero ⇒ «atY»(g) = T.zero",
		},
		Conclusion: "∃φ:(A → B). " +
			"    ring_homomorphism(restrict_ring(R, polynomial_image(R, S, z)), T, φ) ∧ " +
			"    (∀x:A. x ∈ S ⇒ φ(x) = ε(x)) ∧ " +
			"    φ(z) = y",
		Abbrev: Abbrev{
			{Name: "P", Text: "polynomial_ring(restrict_ring(R, S))"},
			{Name: "atZ", Text: "λp:(num → A). polynomial_eval(p, z)"},
			{Name: "atY", Text: "λp:(num → A). polynomial_eval(λi:num. ε(p(i)), y)"},
			{Name: "constant", Text: "λc:A. vec_scalar_mul(c, basis_vector(R.zero, R.one, 0))"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		T *Expr[RingOps[B]],
		S *Expr[Set[A]],
		ε *Arrow[A, B],
		z *Expr[A],
		y *Expr[B],
		sub, zIn, hom, yIn, kills Fact,
	) {
		ring := a.TermAs[RingOps[A]]("R")
		scalars := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
		polynomials := a.TermAs[RingOps[Fun[Nat, A]]]("«P»")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		scalarRing := a.Have(
			"S is a ring under the operations of R",
			"comm_ring_on(restrict_ring(R, S))",
			By(sub, comm_ring.SubringRingOn.Read(R).AsFact().At(S)))
		inclusion := a.Have(
			"S includes into R",
			"ring_homomorphism(restrict_ring(R, S), R, λx:A. x)",
			By(sub, ring_homomorphism.SubringInclusionHom.Read(R).At(S)))
		atZ := a.Conjuncts(
			a.Have(
				"evaluation at z is the case of the inclusion",
				"ring_homomorphism(«P», R, «atZ») ∧ "+
					"(∀c:A. c ∈ S ⇒ «atZ»(«constant»(c)) = c) ∧ "+
					"«atZ»(basis_vector(R.zero, R.one, 1)) = z",
				By(
					inclusion,
					zIn,
					polynomial_evaluation.MappedEvaluationHomomorphism.At(scalars, ring, identity, z))),
			"evaluation at z is a ring map",
			"a constant has itself as value",
			"the variable has the value z")
		atZMap, atZConstant, atZVariable := atZ[0], atZ[1], atZ[2]
		atY := a.Conjuncts(
			a.Have(
				"moved evaluation at y is the case of ε",
				"ring_homomorphism(«P», T, «atY») ∧ "+
					"(∀c:A. c ∈ S ⇒ «atY»(«constant»(c)) = ε(c)) ∧ "+
					"«atY»(basis_vector(R.zero, R.one, 1)) = y",
				By(hom, yIn, polynomial_evaluation.MappedEvaluationHomomorphism.At(scalars, T, ε, y))),
			"moved evaluation at y is a ring map",
			"a constant has the value ε(c)",
			"the variable has the value y")
		atYMap, atYConstant, atYVariable := atY[0], atY[1], atY[2]
		carrier := a.Have(
			"the polynomial ring of S is the polynomials over S",
			"∀p:(num → A). p ∈ «P».carrier ⇔ polynomial_over(S, p)",
			Simp(Fwd(polynomial.PolynomialRingDef), Fwd(module_record.RestrictRingDef)),
			BySets())
		evaluationAtZ, evaluationAtY :=
			a.TermAs[Fun[Fun[Nat, A], A]]("«atZ»"), a.TermAs[Fun[Fun[Nat, A], B]]("«atY»")
		kernels := a.Have(
			"what evaluation at z kills, moved evaluation at y kills",
			"∀p:(num → A). p ∈ «P».carrier ∧ «atZ»(p) = R.zero ⇒ «atY»(p) = T.zero",
			By(kills, carrier))
		φ, factored := a.ObtainAs[Fun[A, B]](
			"moved evaluation at y factors through evaluation at z",
			"∃φ:(A → B). "+
				"    ring_homomorphism(restrict_ring(R, image(«atZ», «P».carrier)), T, φ) ∧ "+
				"    (∀p:(num → A). p ∈ «P».carrier ⇒ φ(«atZ»(p)) = «atY»(p))",
			By(
				atZMap,
				atYMap,
				kernels,
				ring_homomorphism.KernelFactorization.At(polynomials, ring, T, evaluationAtZ, evaluationAtY)))
		parts := a.Conjuncts(
			factored,
			"φ is a ring map on the image",
			"φ reads the moved values off the values at z")
		φMap, φValues := parts[0], parts[1]
		image := a.Have(
			"the values at z of the polynomials over S are S[z]",
			"image(«atZ», «P».carrier) = polynomial_image(R, S, z)",
			BySets(carrier, PolynomialImageDef.At(ring, S, z)))
		constantMap := a.Have(
			"constants embed S in its polynomial ring",
			"ring_homomorphism(restrict_ring(R, S), "+
				"    «P», "+
				"    λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)))",
			By(polynomial.ConstantPolynomialHomomorphism.Read(scalarRing)))
		a.Take(φ)
		a.Do(SplitConjAll(
			Case(
				"φ is a ring map on S[z]",
				By(φMap, image)),
			Case(
				"φ extends ε, read at the constants",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					b.Show(
						"the constant x has the value x at z and ε(x) at y",
						By(xIn, ring_homomorphism.MapIn.Read(constantMap), atZConstant.At(x), atYConstant.At(x), φValues))
				})),
			Case(
				"φ sends z to y, read at the variable",
				By(
					Normalized,
					carrier,
					polynomial.BasisVectorOver.Read(scalarRing).AsFact().At(a.TermAs[Nat]("1")),
					atZVariable,
					atYVariable,
					φValues))))
	}),
})}

// TranscendentalLift — a ring map out of k extends to k[t], for t transcendental over
// k, sending t to any chosen point: only the zero polynomial vanishes at t, and every
// point is a root of the zero polynomial.
var TranscendentalLift = transcendentalLiftThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalLift",
	Key:  "prop_fbc23e2842666dd3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:ring_ops(B). ∀k:set(A). ∀ε:(A → B). ∀t:A. ∀x:B.",
		Hypotheses: []string{
			"subring(field_ring(L), k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"ring_homomorphism(restrict_ring(field_ring(L), k), T, ε)",
			"x ∈ T.carrier",
		},
		Conclusion: "∃φ:(A → B). " +
			"    ring_homomorphism(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
			"        T, " +
			"        φ) ∧ " +
			"    (∀c:A. c ∈ k ⇒ φ(c) = ε(c)) ∧ " +
			"    φ(t) = x",
		Abbrev: Abbrev{
			{Name: "atT", Text: "λp:(num → A). polynomial_eval(p, t)"},
			{Name: "atX", Text: "λp:(num → A). polynomial_eval(λi:num. ε(p(i)), x)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		T *Expr[RingOps[B]],
		k *Expr[Set[A]],
		ε *Arrow[A, B],
		t *Expr[A],
		x *Expr[B],
		sub, tIn, transcendental, hom, xIn Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("L")
		ring := a.TermAs[RingOps[A]]("field_ring(L)")
		kills := a.Have(
			"only the zero polynomial vanishes at t, and every point is its root",
			"∀g:(num → A). polynomial_over(k, g) ∧ «atT»(g) = L.zero ⇒ «atX»(g) = T.zero",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("g")
				vanishes := b.Assume()
				zero := b.Have(
					"g is zero, or it would make t algebraic",
					"g = vec_zero(L.zero)",
					Derive(func(c *Argument) {
						nonzero := c.SupposeNot()
						c.Show(
							"g witnesses that t is algebraic over k",
							By(vanishes, nonzero, transcendental, AlgebraicOverDef.At(ops, k, t)))
					}))
				moved := b.Have(
					"along ε it stays zero",
					"(λi:num. ε(g(i))) = vec_zero(T.zero)",
					Derive(func(c *Argument) {
						c.Do(Funext())
						c.FixAs[Nat]("i")
						c.Show(
							"ε keeps zero",
							zero.Rw(),
							Simp(Fwd(vec_space.VecZeroDef)),
							By(ring_homomorphism.MapZero.Read(hom)))
					}))
				b.Show(
					"the zero polynomial vanishes at x",
					By(
						Normalized,
						moved,
						xIn,
						polynomial_evaluation.EvalVecZero.Read(ring_homomorphism.Target.Read(hom))))
			}))
		a.Show(
			"k[t] maps to T by the lift",
			By(field.RingOn.Read(L), sub, tIn, hom, xIn, kills, PolynomialImageLift.At(ring, T, k, ε, t, x)))
	}),
})}

// TranscendentalLiftInjective — a ring map φ on k[t] that agrees on k with a
// one-to-one ring map ε and sends t to a point x transcendental over ε(k) is
// one-to-one: φ takes the value at t of a polynomial over k to the value at x
// of the polynomial moved along ε, two polynomials over ε(k) with one value at
// x are one polynomial, and ε moves only equal polynomials over k to equal ones.
var TranscendentalLiftInjective = transcendentalLiftInjectiveThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalLiftInjective",
	Key:  "prop_db78784939dbfba4",
	Reading: "ε one-to-one and x transcendental over ε(k) are load-bearing: φ " +
		"identifies any two constants ε identifies, and if x is a root of ε(g) for " +
		"a nonzero g over k, φ sends g(t) to zero, which is not zero when t is " +
		"transcendental over k. t transcendental over k is not asked: φ is given.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:field_on(B). ∀k:set(A). ∀ε φ:(A → B). ∀t:A. ∀x:B.",
		Hypotheses: []string{
			"subring(field_ring(L), k)",
			"t ∈ L.carrier",
			"ring_homomorphism(restrict_ring(field_ring(L), k), field_ring(T), ε)",
			"injective_on(k, ε)",
			"x ∈ T.carrier",
			"¬algebraic_over(T, image(ε, k), x)",
			"ring_homomorphism(restrict_ring(field_ring(L), «polynomials»), field_ring(T), φ)",
			"∀c:A. c ∈ k ⇒ φ(c) = ε(c)",
			"φ(t) = x",
		},
		Conclusion: "injective_on(«polynomials», φ)",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "polynomialsOverT", Text: "{f:(num → B) | polynomial_over(T.carrier, f)}"},
			{Name: "atX", Text: "λf:(num → B). polynomial_eval(f, x)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		T field.FieldFact[on.T],
		k *Expr[Set[A]],
		ε, φ *Arrow[A, B],
		t *Expr[A],
		x *Expr[B],
		sub, tIn, hom, injective, xIn, transcendental, φHom, φOnK, φAtT Fact,
	) {
		fieldT := a.TermAs[FieldOps[B]]("T")
		ringT := field.RingOn.Read(T)
		zero := a.TermAs[A]("L.zero")
		polynomials := a.TermAs[Set[A]]("«polynomials»")
		image := a.TermAs[Set[B]]("image(ε, k)")
		holds := a.Have(
			"k[t] holds k and t",
			"k ⊆ «polynomials» ∧ t ∈ «polynomials»",
			By(sub, tIn, PolynomialImageSubring.Read(L).AsFact().At(k, t)))
		values := a.Have(
			"φ takes the value at t of a polynomial p over k to the value at x of p moved along ε",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"polynomial_over(k, p)"},
				Conclusion: "φ(polynomial_eval(p, t)) = polynomial_eval(λi:num. ε(p(i)), x)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				over := b.Assume()
				along := b.Have(
					"φ carries the value of p at t to the value of p moved along φ at φ(t)",
					"φ(polynomial_eval(p, t)) = polynomial_eval(λi:num. φ(p(i)), φ(t))",
					By(
						holds,
						over,
						φHom,
						polynomial.PolynomialOverMono.At(zero, k, polynomials, p),
						polynomial_evaluation.EvalAlongHomomorphism.At(
							b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «polynomials»)"),
							b.TermAs[RingOps[B]]("field_ring(T)"),
							φ,
							p,
							t)))
				coefficients := b.Have(
					"on the coefficients of p, which lie in k, φ is ε",
					"(λi:num. φ(p(i))) = (λi:num. ε(p(i)))",
					Derive(func(c *Argument) {
						c.Do(Funext())
						c.FixAs[Nat]("i")
						c.Show(
							"p(i) lies in k",
							By(φOnK.At(c.TermAs[A]("p(i)")), over, polynomial.PolynomialOverDef.At(zero, k, p)))
					}))
				b.Show(
					"and φ(t) is x",
					By(φAtT, along, coefficients))
			}))
		imageSubring := a.Have(
			"ε(k) is a subring of T",
			"subring(field_ring(T), image(ε, k))",
			By(
				hom,
				ring_homomorphism.ImageSubring.At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), k)"),
					a.TermAs[RingOps[B]]("field_ring(T)"),
					ε)))
		oneValue := a.Have(
			"x is transcendental over ε(k): two polynomials over ε(k) with one value at x are one polynomial",
			Statement{
				Binders: "∀p q:(num → B).",
				Hypotheses: []string{
					"polynomial_over(image(ε, k), p)",
					"polynomial_over(image(ε, k), q)",
					"polynomial_eval(p, x) = polynomial_eval(q, x)",
				},
				Conclusion: "p = q",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, B]]("p")
				q := b.FixAs[Fun[Nat, B]]("q")
				given := b.Assume()
				overImage := polynomial.PolynomialRingOn.Read(b.Have(
					"ε(k) is a ring under the operations of T",
					"comm_ring_on(restrict_ring(field_ring(T), image(ε, k)))",
					By(imageSubring, comm_ring.SubringRingOn.Read(ringT).At(image))))
				difference := b.Have(
					"the difference -p + q is a polynomial over ε(k), the polynomials over ε(k) forming a ring",
					"polynomial_over(image(ε, k), vec_add(vec_neg(p), q))",
					By(given, comm_ring.AddIn.Read(overImage), comm_ring.NegIn.Read(overImage)))
				overT := b.Have(
					"p and q are polynomials over T as well, members of the ring of the polynomials over T",
					"p ∈ «polynomialsOverT» ∧ q ∈ «polynomialsOverT»",
					BySets(
						given,
						imageSubring,
						comm_ring.SubringSubset.At(b.TermAs[RingOps[B]]("field_ring(T)"), image),
						polynomial.PolynomialOverMono))
				evaluation := b.Have(
					"evaluation at x is a ring homomorphism from the polynomials over T to T",
					"ring_homomorphism(polynomial_ring(field_ring(T)), field_ring(T), «atX»)",
					By(polynomial_evaluation.EvalHomomorphism.Read(ringT).At(b.MemberOf[on.T](x, xIn))))
				root := b.Have(
					"p and q having one value, -p + q lies in the kernel of the evaluation: it vanishes at x",
					"polynomial_eval(vec_add(vec_neg(p), q), x) = T.zero",
					By(
						given,
						overT,
						group_homomorphism.EqIffInKernel.Read(
							ring_homomorphism.AdditiveHomomorphism.Read(evaluation)).AsFact().At(
							p, q),
						group_homomorphism.InKernel.At(
							b.TermAs[B]("T.zero"),
							b.TermAs[Set[Fun[Nat, B]]]("«polynomialsOverT»"),
							b.TermAs[Fun[Fun[Nat, B], B]]("«atX»"),
							b.TermAs[Fun[Nat, B]]("vec_add(vec_neg(p), q)"))))
				vanishing := b.Have(
					"x being transcendental over ε(k), -p + q is the zero polynomial",
					"vec_add(vec_neg(p), q) = vec_zero(T.zero)",
					By(transcendental, root, difference, AlgebraicOverDef.At(fieldT, image, x)))
				b.Show(
					"-p + q is the zero of the additive group of the polynomials over T, which says p = q",
					By(
						vanishing,
						overT,
						group.InvMulEqOneOn.Read(abelian_group.GroupOn.Read(
							comm_ring.AddGroupOn.Read(polynomial.PolynomialRingOn.Read(ringT)))).AsFact().At(
							p, q)))
			}))
		a.Show(
			"φ is one-to-one: x satisfies no relation over ε(k), and ε is one-to-one",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				b.FixAs[A]("y")
				b.FixAs[A]("z")
				given := b.Assume()
				p, q, written := b.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
					"y and z are the values at t of polynomials p and q over k",
					"∃p q:(num → A). "+
						"    polynomial_over(k, p) ∧ "+
						"    polynomial_over(k, q) ∧ "+
						"    y = polynomial_eval(p, t) ∧ "+
						"    z = polynomial_eval(q, t)",
					BySets(given, PolynomialImageDef.At(b.TermAs[RingOps[A]]("field_ring(L)"), k, t)))
				movedP := b.TermAs[Fun[Nat, B]]("λi:num. ε(p(i))")
				movedQ := b.TermAs[Fun[Nat, B]]("λi:num. ε(q(i))")
				moved := b.Have(
					"ε carries p and q to polynomials over ε(k)",
					"polynomial_over(image(ε, k), λi:num. ε(p(i))) ∧ polynomial_over(image(ε, k), λi:num. ε(q(i)))",
					By(
						written,
						ring_homomorphism.MapZero.Read(hom),
						At(set_image.FunInImage, ε, k),
						polynomial.PolynomialOverMap.At(ε, zero, b.TermAs[B]("T.zero"), k, image, p),
						polynomial.PolynomialOverMap.At(ε, zero, b.TermAs[B]("T.zero"), k, image, q)))
				samePolynomial := b.Have(
					"the two moved polynomials take one value at x, so they are one polynomial",
					"(λi:num. ε(p(i))) = (λi:num. ε(q(i)))",
					By(moved, given, written, values.At(p), values.At(q), oneValue.At(movedP, movedQ)))
				equal := b.Have(
					"ε is one-to-one on k, where the coefficients lie, so p = q",
					"p = q",
					Derive(func(c *Argument) {
						c.Do(Funext())
						c.FixAs[Nat]("i")
						c.Show(
							"ε(p(i)) = ε(q(i)) with p(i) and q(i) in k",
							By(
								samePolynomial,
								injective,
								written,
								functions.InjectiveOnDef.At(k, ε),
								polynomial.PolynomialOverDef.At(zero, k, p),
								polynomial.PolynomialOverDef.At(zero, k, q)))
					}))
				b.Show(
					"so y = z",
					By(equal, written))
			}))
	}),
})}

// HomomorphismExtendsAtRoot — let z in a commutative ring have a monic polynomial g over
// the subring S as a relation of least degree. A homomorphism e of S into a ring T
// extends to S[z] at any root w of the image of g: every relation p of z over S
// is a multiple of g (LeastMonicRelationDivides), so its image vanishes at w
// (PolynomialImageLift).
var HomomorphismExtendsAtRoot = homomorphismExtendsAtRootThm{family.Add(registry.ProofEntry{
	Name: "HomomorphismExtendsAtRoot",
	Key:  "prop_b4e32dbbaed88566",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀T:ring_ops(B). ∀S:set(A). ∀e:(A → B). ∀g:(num → A). ∀z:A. ∀w:B.",
		Hypotheses: []string{
			"subring(R, S)",
			"z ∈ R.carrier",
			"polynomial_over(S, g)",
			"polynomial_monic(g)",
			"polynomial_eval(g, z) = R.zero",
			"∀q:(num → A). " +
				"    polynomial_over(S, q) ∧ q ≠ vec_zero(R.zero) ∧ polynomial_eval(q, z) = R.zero ⇒ " +
				"    polynomial_degree(g) ≤ polynomial_degree(q)",
			"ring_homomorphism(restrict_ring(R, S), T, e)",
			"w ∈ T.carrier",
			"polynomial_eval(λi:num. e(g(i)), w) = T.zero",
		},
		Conclusion: "∃h:(A → B). " +
			"    ring_homomorphism(restrict_ring(R, polynomial_image(R, S, z)), T, h) ∧ " +
			"    (∀x:A. x ∈ S ⇒ h(x) = e(x)) ∧ " +
			"    h(z) = w",
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		T *Expr[RingOps[B]],
		S *Expr[Set[A]],
		e *Arrow[A, B],
		g *Arrow[Nat, A],
		z *Expr[A],
		w *Expr[B],
		sub, zIn, gOver, gMonic, gRoot, gLeast, hom, wIn, gImageRoot Fact,
	) {
		target := ring_homomorphism.Target.Read(hom)
		_, VDef := arg.LetAs[Fun[Fun[Nat, A], B]]("V", "λp:(num → A). polynomial_eval(λi:num. e(p(i)), w)")
		moved := arg.Have(
			"moving coefficients and evaluating at w is a homomorphism",
			"ring_homomorphism(polynomial_ring(restrict_ring(R, S)), T, V)",
			By(
				VDef,
				hom,
				wIn,
				polynomial_evaluation.TransportedEvaluationHomomorphism.At(
					arg.TermAs[RingOps[A]]("restrict_ring(R, S)"), T, e, w)))
		relations := arg.Have(
			"it kills every relation of z",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"polynomial_over(S, p)", "polynomial_eval(p, z) = R.zero"},
				Conclusion: "polynomial_eval(λi:num. e(p(i)), w) = T.zero",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				given := b.Assume()
				divides := b.Have(
					"g divides p over S, a monic relation of least degree dividing every relation",
					"polynomial_divides(restrict_ring(R, S), g, p)",
					By(
						sub,
						gOver,
						gMonic,
						gRoot,
						gLeast,
						given,
						LeastMonicRelationDivides.Read(R).At(S, g, b.MemberOf[on.R](z, zIn), p)))
				q, product := b.UnpackAs[Fun[Nat, A]](
					b.Unfolded(divides, polynomial_division.PolynomialDividesDef), "q")
				parts := b.Conjuncts(
					product,
					"the quotient q is over S",
					"p is g q")
				qOver, pIs := parts[0], parts[1]
				inP := b.Have(
					"g and q lie in the polynomial ring",
					"g ∈ polynomial_ring(restrict_ring(R, S)).carrier ∧ "+
						"q ∈ polynomial_ring(restrict_ring(R, S)).carrier",
					By(gOver, qOver))
				value := b.Have(
					"V kills p = g q",
					"V(p) = T.zero",
					Derive(func(c *Argument) {
						splits := c.Have(
							"V is multiplicative",
							"V(polynomial_mul(g, q)) = T.mul(V(g), V(q))",
							By(inP, ring_homomorphism.MapMul.Read(moved).AsFact().At(g, q)))
						c.Show(
							"and it kills g",
							pIs.Rw(),
							splits.Rw(),
							gImageRoot.Rw(),
							By(inP, ring_homomorphism.MapIn.Read(moved).AsFact().At(q), comm_ring.MulLeftZeroOn.Read(target)))
					}))
				b.Show(
					"which is the claim",
					By(Normalized, VDef, value))
			}))
		arg.Show(
			"the homomorphism extends",
			By(
				sub,
				hom,
				wIn,
				relations,
				PolynomialImageLift.Read(R).At(T, S, e, arg.MemberOf[on.R](z, zIn), w)))
	}),
})}

// AdjoinEmbeddingAtRoot — a homomorphism f of a subfield K of L into a field
// T extends to the simple algebraic extension K(a), sending a to any root b
// in T of its transported minimal polynomial: the minimal polynomial of a
// is a monic relation of a over K of least degree, so f extends to K[a]
// sending a to b (HomomorphismExtendsAtRoot), and K[a] is K(a) since a is
// algebraic.
var AdjoinEmbeddingAtRoot = adjoinEmbeddingAtRootThm{family.Add(registry.ProofEntry{
	Name: "AdjoinEmbeddingAtRoot",
	Key:  "prop_c2409e02454c1611",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:field_on(B). ∀K:set(A). ∀f:(A → B). ∀a:A. ∀b:B.",
		Hypotheses: []string{
			"subfield(L, K)",
			"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(T), f)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"b ∈ T.carrier",
			"polynomial_eval(λi:num. f(minimal_polynomial(L, K, a, i)), b) = T.zero",
		},
		Conclusion: "∃g:(A → B). " +
			"    ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"        field_ring(T), " +
			"        g) ∧ " +
			"    (∀x:A. x ∈ K ⇒ g(x) = f(x)) ∧ " +
			"    g(a) = b",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		T field.FieldFact[on.T],
		K *Expr[Set[A]],
		f *Arrow[A, B],
		a *Member[A, on.L],
		b *Member[B, on.T],
		kField, hom, algebraic, root Fact,
	) {
		lifted := arg.Have(
			"f extends to K[a], sending a to b",
			"∃g:(A → B). "+
				"    ring_homomorphism(restrict_ring(field_ring(L), polynomial_image(field_ring(L), K, a)), "+
				"        field_ring(T), "+
				"        g) ∧ "+
				"    (∀x:A. x ∈ K ⇒ g(x) = f(x)) ∧ "+
				"    g(a) = b",
			By(
				L,
				kField,
				algebraic,
				hom,
				b,
				root,
				field.SubfieldSubring.Read(L).At(K),
				MinimalPolynomialSpec.Read(L).At(K, a),
				HomomorphismExtendsAtRoot.Read(field.RingOn.Read(L)).At(
					arg.TermAs[RingOps[B]]("field_ring(T)"),
					K,
					f,
					arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)"),
					a,
					b)))
		arg.Show(
			"K[a] is K(a)",
			By(kField, algebraic, lifted, AdjoinEqImage.Read(L).At(K, a)))
	}),
})}

// TransportedMinimalPolynomial — an embedding f of M into L that fixes K
// carries the minimal polynomial q of a over M to a polynomial over L of
// the degree of q dividing, in L's polynomial ring, every polynomial p over
// K that vanishes at a: q divides p over M, and moving the factorization
// p = q r along f leaves p unchanged and gives p = f(q) f(r).
var TransportedMinimalPolynomial = transportedMinimalPolynomialThm{family.Add(registry.ProofEntry{
	Name: "TransportedMinimalPolynomial",
	Key:  "prop_37e086d58d421f48",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀f:(A → A). ∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"K ⊆ M",
			"ring_homomorphism(restrict_ring(field_ring(L), M), field_ring(L), f)",
			"∀x:A. x ∈ K ⇒ f(x) = x",
			"a ∈ L.carrier",
			"algebraic_over(L, M, a)",
			"polynomial_over(K, p)",
			"polynomial_eval(p, a) = L.zero",
		},
		Conclusion: "polynomial_over(L.carrier, «image») ∧ " +
			"polynomial_degree(«image») = polynomial_degree(minimal_polynomial(L, M, a)) ∧ " +
			"polynomial_divides(field_ring(L), «image», p)",
		Abbrev: Abbrev{
			{Name: "image", Text: "λi:num. f(minimal_polynomial(L, M, a, i))"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, M *Expr[Set[A]],
		f *Arrow[A, A],
		a *Member[A, on.L],
		p *Arrow[Nat, A],
		mField, nested, hom, fixesK, algebraic, pOver, aRoot Fact,
	) {
		l, zero := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[A]("L.zero")
		carrier := arg.TermAs[Set[A]]("L.carrier")
		q, qDef := arg.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, M, a)")
		Q, QDef := arg.LetAs[Fun[Nat, A]]("Q", "λi:num. f(q(i))")
		divisor := arg.Have(
			"q divides p over M",
			"polynomial_over(M, q) ∧ "+
				"polynomial_over(M, p) ∧ "+
				"polynomial_divides(restrict_ring(field_ring(L), M), q, p)",
			By(
				qDef,
				a,
				mField,
				nested,
				algebraic,
				pOver,
				aRoot,
				MinimalPolynomialSpec.Read(L).At(M, a),
				polynomial.PolynomialOverMono.At(zero, K, M, p),
				MinimalPolynomialDivides.Read(L).At(M, a, p)))
		fieldM := arg.Have(
			"the restricted operations make M a field",
			"field_on(restrict_field(L, M))",
			By(mField, field.SubfieldFieldOn.Read(L).At(M)))
		homM := arg.Have(
			"f is a homomorphism of the field M into L",
			"ring_homomorphism(field_ring(restrict_field(L, M)), field_ring(L), f)",
			By(hom, field.RestrictFieldRing))
		transport := arg.Conjuncts(
			arg.Have(
				"the embedding of the field M keeps the degree of q and carries each product with q",
				"polynomial_degree(λi:num. f(q(i))) = polynomial_degree(q) ∧ "+
					"(∀r:(num → A). "+
					"    polynomial_over(M, r) ⇒ "+
					"    (λi:num. f(polynomial_mul(q, r, i))) = polynomial_mul(λi:num. f(q(i)), λi:num. f(r(i))))",
				By(
					L,
					fieldM,
					homM,
					field.CarrierSubfield.Read(fieldM),
					divisor,
					FieldEmbeddingPolynomials.Read(fieldM).At(l, f, M, q))),
			"the image has the degree of q",
			"transport carries products with q to products with its image")
		mapsInto := arg.Have(
			"f preserves zero and maps M into L",
			"f(L.zero) = L.zero ∧ (∀x:A. x ∈ M ⇒ f(x) ∈ L.carrier)",
			By(ring_homomorphism.MapZero.Read(hom), ring_homomorphism.MapIn.Read(hom)))
		imagePolynomial := arg.Have(
			"Q is a polynomial over L of the degree of q",
			"polynomial_over(L.carrier, Q) ∧ polynomial_degree(Q) = polynomial_degree(q)",
			By(
				Normalized,
				QDef,
				divisor,
				mapsInto,
				transport[0],
				polynomial.PolynomialOverMap.At(f, zero, zero, M, carrier, q)))
		fixedPolynomial := arg.Have(
			"f fixes the coefficients of p, which lie in K",
			"(λi:num. f(p(i))) = p",
			Derive(func(b *Argument) {
				b.Do(Funext())
				b.FixAs[Nat]("i")
				b.Show(
					"each coefficient lies in K",
					By(pOver, fixesK, polynomial.PolynomialOverDef.At(zero, K, p)))
			}))
		r, factorization := arg.ObtainAs[Fun[Nat, A]](
			"write p as q times a polynomial over M",
			"∃r:(num → A). polynomial_over(M, r) ∧ p = polynomial_mul(q, r)",
			By(
				divisor,
				polynomial_division.PolynomialDividesDef.At(
					arg.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), M)"), q, p)))
		transported := arg.Have(
			"moving the factorization along f gives p = Q f(r), with f(r) over L",
			"polynomial_over(L.carrier, λi:num. f(r(i))) ∧ p = polynomial_mul(Q, λi:num. f(r(i)))",
			By(
				Normalized,
				QDef,
				fixedPolynomial,
				factorization,
				mapsInto,
				transport[1].At(r),
				polynomial.PolynomialOverMap.At(f, zero, zero, M, carrier, r)))
		arg.Show(
			"Q is a polynomial over L of the degree of q, and p = Q f(r) in L's polynomial ring",
			By(
				Normalized,
				imagePolynomial,
				transported,
				polynomial_division.PolynomialDividesDef.At(
					arg.TermAs[comm_ring.RingOps[A]]("field_ring(L)"), Q, p)))
	}),
})}
