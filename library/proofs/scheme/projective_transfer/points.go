// points.go — the points of a projective equation curve along a ring
// homomorphism ι of fields. ι carries them one to one onto the carried curve's
// points, keeping their count over each finite field of constants; and, the
// points read as the normalized zeros of the listed equations, the curve has a
// point over an algebraically closed M exactly when the carried curve has one
// over an algebraically closed N, by elementarity.

package projective_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"

	// algebraically_closed_field_transfer states EmbeddingElementary, which
	// ByElementarity's embedding mode reads by name: the import keeps this
	// chapter above it in Go's import graph.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_field_transfer"
)

// CarriedEvaluation — a polynomial P over k, carried along ι, takes at the
// carried point the image under ι of P's value at x. ι after evaluation is
// evaluation along ι at the carried point; and evaluation along ι is
// evaluation of «carried»(P) along the identity, the two sums running over
// one support with the same terms, since ι is one to one on M and sends zero
// to zero.
var CarriedEvaluation = carriedEvaluationThm{family.Add(registry.ProofEntry{
	Name: "CarriedEvaluation",
	Key:  "prop_eadf230f1dfa7305",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀x:(num → A). " +
			"∀P:((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			"P ∈ «polynomials».carrier",
		},
		Conclusion: "polynomial_algebra_eval(restrict_ring(field_ring(N), image(ι, k)), " +
			"    field_ring(N), " +
			"    (λb:B. b), " +
			"    «carriedPoint»(x), " +
			"    «carried»(P)) = " +
			"ι(«valueAt»(x, P))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			N field.FieldFact[on.N],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			n *Expr[Nat],
			x *Arrow[Nat, A],
			P *Arrow[Fun[Nat, Nat], A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"ι is a ring homomorphism of M into N",
				"k is a subfield of M",
				"x has its coordinates up to n in M",
				"P is a polynomial over k")
			hom, subK, xInM, polynomial := parts[0], parts[1], parts[2], parts[3]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
			kRing := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			inclusion := a.TermAs[Fun[A, A]]("λa:A. a")
			natural := a.Have(
				"evaluation is natural: ι of P's value at x, k included in M, "+
					"is P's value at the carried point, its coefficients sent along ι",
				"ι(«valueAt»(x, P)) = "+
					"polynomial_algebra_eval(«hilbertCoefficients», field_ring(N), ι, λi:num. ι(x(i)), P)",
				By(
					hom,
					subK,
					xInM,
					polynomial,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k),
					ring_homomorphism.RingHomRestrictSource.At(ringM, ringN, ι, k),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural.At(
						kRing, ringM, ringN, inclusion, ι, ι, variables, x, P)))
			coefficients := a.Have(
				"the coefficients of P lie in k",
				"∀m:(num → num). P(m) ∈ k",
				By(polynomial, polynomial_algebra.PolynomialAlgebraMember.At(kRing, variables, P)))
			oneToOne := a.Have(
				"ι is one to one on M",
				"injective_on(M.carrier, ι)",
				By(N, hom, ring_homomorphism.FieldHomomorphismInjective.Read(M).At(fieldN, ι)))
			vanishing := a.Have(
				"a coefficient of «carried»(P) vanishes exactly where P's "+
					"does: it lies in k, inside M, where ι sends only zero to zero",
				"∀m:(num → num). ι(P(m)) = N.zero ⇔ P(m) = M.zero",
				a.ForEach(func(m *Expr[Fun[Nat, Nat]]) Action {
					return By(
						oneToOne,
						subK,
						coefficients.At(m),
						field.SubfieldSubset.At(fieldM, k),
						set_basic.SubsetDef,
						ring_homomorphism.ZeroIffImageZero.Read(hom).AsFact().At(P.Apply(m)))
				}))
			support := a.Have(
				"so «carried»(P) and P have one support",
				"fun_support(N.zero, «carried»(P)) = fun_support(M.zero, P)",
				BySets(vanishing))
			a.Show(
				"both values are the sum over that support of the same terms",
				natural.Rw(),
				Simp(Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef)),
				support.Rw(),
				Basic())
		}),
})}

// CarriedPoints — a ring homomorphism ι of M into N carries the projective
// points of the curve E over l one to one onto the points of the carried
// curve over ι(l), ι applied coordinatewise. Two points with one image agree
// past n, where both vanish, and up to n, where their coordinates lie in l,
// inside M, where ι is one to one. The carried point of a point is a point
// by CarriedEvaluation. A point y of the carried curve has a preimage in l of
// each coordinate up to n; with zero past n they make a point x with ι∘x = y,
// normalized because ι is one to one, and on the curve because ι of each
// equation's value at x is the carried equation's value at y, zero.
var CarriedPoints = carriedPointsThm{family.Add(registry.ProofEntry{
	Name: "CarriedPoints",
	Key:  "prop_7136b60162202200",
	Reading: "l ⊆ M.carrier and E over k are load-bearing: off M's carrier ι " +
		"is unconstrained, so two coordinates outside it could share an image, " +
		"and a coefficient outside M could vanish under ι without being zero.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k l:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"l ⊆ M.carrier",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "«carriedPoints» = image(«carriedPoint», «points») ∧ " +
			"injective_on(«points», «carriedPoint»)",
		Abbrev: Abbrev{
			{Name: "points", Text: "projective_equation_points(field_ring(M), k, l, n, E)"},
			{Name: "carriedPoints", Text: "projective_equation_points(field_ring(N), " +
				"    image(ι, k), " +
				"    image(ι, l), " +
				"    n, " +
				"    image(«carried», E))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			N field.FieldFact[on.N],
			ι *Arrow[A, B],
			k, l *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"ι is a ring homomorphism of M into N",
				"k is a subfield of M",
				"l lies in M",
				"the equations are polynomials over k")
			hom, subK, lInM, equationsOverK := parts[0], parts[1], parts[2], parts[3]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
			carriedK := a.TermAs[Set[B]]("image(ι, k)")
			carriedL := a.TermAs[Set[B]]("image(ι, l)")
			carriedE := a.TermAs[Set[Fun[Fun[Nat, Nat], B]]]("image(«carried», E)")
			carried := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], Fun[Fun[Nat, Nat], B]]]("«carried»")
			carriedPoint := a.TermAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("«carriedPoint»")
			points := a.TermAs[Set[Fun[Nat, A]]]("«points»")
			zero := ring_homomorphism.MapZero.Read(hom)
			oneToOne := a.Have(
				"ι is one to one on M",
				"injective_on(M.carrier, ι)",
				By(N, hom, ring_homomorphism.FieldHomomorphismInjective.Read(M).At(fieldN, ι)))
			kernel := a.Have(
				"so ι sends to zero only the zero of M",
				"∀u:A. u ∈ M.carrier ∧ ι(u) = N.zero ⇒ u = M.zero",
				By(oneToOne, ring_homomorphism.ZeroIffImageZero.Read(hom)))

			injective := a.Have(
				"two points with one carried point agree: past n both "+
					"vanish, and up to n their coordinates lie in l, inside M",
				"injective_on(«points», «carriedPoint»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, A]]("x")
					y := b.FixAs[Fun[Nat, A]]("y")
					pair := b.Conjuncts(
						b.Assume(),
						"x is a point",
						"y is a point",
						"x and y have one carried point")
					xPoint, yPoint, same := pair[0], pair[1], pair[2]
					agree := b.Have(
						"x and y agree at every coordinate",
						"∀i:num. x(i) = y(i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							c.Cases(c.Term("i ≤ n"))
							c.When(
								"up to n both coordinates lie in l, inside M, and have one image under ι",
								func(d *Argument, upToN Fact) {
									d.Show(
										"ι is one to one on M",
										By(
											upToN,
											xPoint,
											yPoint,
											same,
											oneToOne,
											lInM,
											projective_curve.PointCoordinatesIn.At(ringM, k, l, n, E, x, i),
											projective_curve.PointCoordinatesIn.At(ringM, k, l, n, E, y, i),
											functions.InjectiveOnDef.At(a.TermAs[Set[A]]("M.carrier"), ι),
											set_basic.SubsetDef))
								})
							c.Otherwise(
								"past n both coordinates are zero",
								func(d *Argument, pastN Fact) {
									d.Show(
										"both vanish",
										By(
											Normalized,
											pastN,
											xPoint,
											yPoint,
											nat_order.NotLessEq.At(i, n),
											projective_curve.PointZeroPastN.At(ringM, k, l, n, E, x, i),
											projective_curve.PointZeroPastN.At(ringM, k, l, n, E, y, i)))
								})
						}))
					b.Show(
						"so x = y",
						By(Normalized, agree))
				}))

			carriedIn := a.Have(
				"the carried point of a point is a point of the carried curve",
				"image(«carriedPoint», «points») ⊆ «carriedPoints»",
				Simp(Fwd(set_image.ImageSubsetIff)),
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, A]]("x")
					point := b.Assume()
					inL := b.Have(
						"its coordinates up to n lie in ι(l)",
						"∀i:num. i ≤ n ⇒ ι(x(i)) ∈ image(ι, l)",
						By(point, projective_curve.PointCoordinatesIn, set_image.FunInImage))
					inM := b.Have(
						"so x has its coordinates up to n in M",
						"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
						By(point, lInM, projective_curve.PointCoordinatesIn, set_basic.SubsetDef))
					pastN := b.Have(
						"past n they are ι(M.zero) = N.zero",
						"∀i:num. n < i ⇒ ι(x(i)) = N.zero",
						b.ForEach(func(i *Expr[Nat]) Action {
							return By(point, zero, projective_curve.PointZeroPastN.At(ringM, k, l, n, E, x, i))
						}))
					leading := b.Have(
						"the leading coordinate is ι(M.one) = N.one, the earlier ones zero",
						"∃j:num. j ≤ n ∧ ι(x(j)) = N.one ∧ (∀i:num. i < j ⇒ ι(x(i)) = N.zero)",
						By(
							point,
							zero,
							ring_homomorphism.MapOne.Read(hom),
							projective_curve.PointLeadingOne.At(ringM, k, l, n, E, x)))
					equations := b.Have(
						"each carried equation takes at the carried point ι of the equation's value at x, zero",
						Statement{
							Binders: "∀P:((num → num) → A).",
							Hypotheses: []string{
								"P ∈ E",
							},
							Conclusion: "polynomial_algebra_eval(restrict_ring(field_ring(N), image(ι, k)), " +
								"    field_ring(N), " +
								"    λb:B. b, " +
								"    «carriedPoint»(x), " +
								"    «carried»(P)) = " +
								"N.zero",
						},
						Derive(func(c *Argument) {
							P := c.FixAs[Fun[Fun[Nat, Nat], A]]("P")
							inE := c.Assume()
							polynomial := c.Have(
								"P is a polynomial over k",
								"P ∈ «polynomials».carrier",
								By(inE, equationsOverK, set_basic.SubsetDef))
							c.Show(
								"by CarriedEvaluation, as P vanishes at x",
								By(
									M,
									N,
									hom,
									subK,
									point,
									inM,
									polynomial,
									inE,
									zero,
									CarriedEvaluation.At(fieldM, fieldN, ι, k, n, x, P),
									projective_curve.PointEquationsVanish.At(ringM, k, l, n, E, x, P)))
						}))
					b.Show(
						"so the carried point has the four properties of a point",
						Simp(Fwd(projective_curve.ProjectiveEquationPointsDef), Fwd(set_image.ForallInImage)),
						By(inL, pastN, leading, equations))
				}))

			carriedOnto := a.Have(
				"every point of the carried curve is a carried point",
				"«carriedPoints» ⊆ image(«carriedPoint», «points»)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					y := b.FixAs[Fun[Nat, B]]("y")
					point := b.Assume()
					preimages := b.Have(
						"each coordinate of y has a preimage in M, in l up to n",
						"∀i:num. ∃a:A. a ∈ M.carrier ∧ ι(a) = y(i) ∧ (i ≤ n ⇒ a ∈ l)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							c.Cases(c.Term("i ≤ n"))
							c.When(
								"up to n, y(i) lies in ι(l), and l lies in M",
								func(d *Argument, upToN Fact) {
									d.Show(
										"a preimage of y(i) in l",
										By(
											upToN,
											point,
											lInM,
											projective_curve.PointCoordinatesIn.At(ringN, carriedK, carriedL, n, carriedE, y, i),
											set_basic.InImage.At(ι, l, d.TermAs[B]("y(i)")),
											set_basic.SubsetDef))
								})
							c.Otherwise(
								"past n, y(i) is zero, the image of M.zero",
								func(d *Argument, pastN Fact) {
									d.Take(d.TermAs[A]("M.zero"))
									d.Show(
										"M.zero lies in M and ι(M.zero) = N.zero = y(i)",
										By(
											Normalized,
											pastN,
											point,
											zero,
											comm_ring.ZeroIn.Read(field.RingOn.Read(M)),
											nat_order.NotLessEq.At(i, n),
											projective_curve.PointZeroPastN.At(ringN, carriedK, carriedL, n, carriedE, y, i)))
								})
						}))
					x, preimage := b.ObtainAs[Fun[Nat, A]](
						"choose such a preimage at every coordinate",
						"∃x:(num → A). ∀i:num. x(i) ∈ M.carrier ∧ ι(x(i)) = y(i) ∧ (i ≤ n ⇒ x(i) ∈ l)",
						By(preimages))
					inM := b.Have(
						"x has its coordinates up to n in M",
						"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
						By(preimage))
					pastN := b.Have(
						"past n, ι(x(i)) = y(i) = N.zero, so x(i) is zero",
						"∀i:num. n < i ⇒ x(i) = M.zero",
						By(kernel, preimage, point, projective_curve.PointZeroPastN))
					j, normalized := b.UnpackAs[Nat](
						GroupPremises(
							point, projective_curve.PointLeadingOne.At(ringN, carriedK, carriedL, n, carriedE, y)),
						"j")
					leading := b.Have(
						"x leads with one at the index j where y does, the earlier coordinates zero",
						"∃j:num. j ≤ n ∧ x(j) = M.one ∧ (∀i:num. i < j ⇒ x(i) = M.zero)",
						Derive(func(c *Argument) {
							c.Take(j)
							c.Show(
								"ι(x(j)) = y(j) = N.one = ι(M.one), and ι is one to one on M",
								By(
									normalized,
									kernel,
									preimage,
									oneToOne,
									comm_ring.OneIn.Read(field.RingOn.Read(M)),
									ring_homomorphism.MapOne.Read(hom),
									functions.InjectiveOnDef.At(a.TermAs[Set[A]]("M.carrier"), ι)))
						}))
					carries := b.Have(
						"ι carries x to y",
						"y = «carriedPoint»(x)",
						By(Normalized, preimage))
					evaluation := b.Have(
						"evaluation at x is a ring homomorphism from the polynomials over k into M",
						"ring_homomorphism(«polynomials», "+
							"    field_ring(M), "+
							"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), x))",
						By(subK, inM, homogeneous_polynomial.EvaluationRingHom.Read(M).At(k, n, x)))
					equations := b.Have(
						"every equation vanishes at x: ι of its value is the carried equation's value at y, zero",
						"∀P:((num → num) → A). P ∈ E ⇒ «valueAt»(x, P) = M.zero",
						Derive(func(c *Argument) {
							P := c.FixAs[Fun[Fun[Nat, Nat], A]]("P")
							inE := c.Assume()
							polynomial := c.Have(
								"P is a polynomial over k",
								"P ∈ «polynomials».carrier",
								By(inE, equationsOverK, set_basic.SubsetDef))
							carriedValue := c.Have(
								"ι of the value of P at x is the value of «carried»(P) at y, zero",
								"ι(«valueAt»(x, P)) = N.zero",
								By(
									M,
									N,
									hom,
									subK,
									inM,
									polynomial,
									inE,
									carries,
									point,
									CarriedEvaluation.At(fieldM, fieldN, ι, k, n, x, P),
									set_image.FunInImage.At(carried, E, P),
									projective_curve.PointEquationsVanish.At(
										ringN, carriedK, carriedL, n, carriedE, y, c.TermAs[Fun[Fun[Nat, Nat], B]]("«carried»(P)"))))
							c.Show(
								"the value lies in M, where only zero goes to zero",
								By(kernel, carriedValue, polynomial, ring_homomorphism.MapIn.Read(evaluation)))
						}))
					inPoints := b.Have(
						"so x is a point of the curve over l",
						"x ∈ «points»",
						Simp(Fwd(projective_curve.ProjectiveEquationPointsDef)),
						By(preimage, pastN, leading, equations))
					b.Show(
						"and y is its carried point",
						carries.Rw(),
						By(inPoints, set_image.FunInImage.At(carriedPoint, points, x)))
				}))

			a.Show(
				"the two inclusions are the equation, and ι carries the points one to one",
				By(carriedIn, carriedOnto, injective, set_order.SubsetAntisym))
		}),
})}

// CarriedPointCount — carried along ι, the curve keeps the size of its field
// of constants and its number of points over every finite extension of it in
// M. ι is one to one on M, so on k. Over the field l of q^m elements of M,
// q = card(k) and m > 0, the points are finitely many, maps with their
// coordinates up to n in the finite l and zero past n; CarriedPoints carries
// them one to one onto the carried curve's points over ι(l), and ι(l) is the
// field of q^m elements of N (FiniteConstantsImage).
var CarriedPointCount = carriedPointCountThm{family.Add(registry.ProofEntry{
	Name: "CarriedPointCount",
	Key:  "prop_1a24614f2ca50c9f",
	Reading: "M algebraically closed is load-bearing: it gives the field of q^m elements " +
		"of M its size, so that ι carries it onto the whole of N's; N need not be closed.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"finite(k)",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "card(image(ι, k)) = card(k) ∧ " +
			"(∀m:num. 0 < m ⇒ card(«carriedPoints»(m)) = card(«points»(m)))",
		Abbrev: Abbrev{
			{Name: "points", Text: "λm:num. " +
				"    projective_equation_points(field_ring(M), " +
				"        k, " +
				"        finite_constants(field_ring(M), card(k), m), " +
				"        n, " +
				"        E)"},
			{Name: "carriedPoints", Text: "λm:num. " +
				"    projective_equation_points(field_ring(N), " +
				"        image(ι, k), " +
				"        finite_constants(field_ring(N), card(k), m), " +
				"        n, " +
				"        image(«carried», E))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			N field.FieldFact[on.N],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is algebraically closed",
				"ι is a ring homomorphism of M into N",
				"k is a subfield of M",
				"k is finite",
				"the equations are polynomials over k")
			closed, hom, subK, finiteK, equationsOverK := parts[0], parts[1], parts[2], parts[3], parts[4]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			carriedPoint := a.TermAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("«carriedPoint»")
			constants := a.Have(
				"ι is one to one on M, so on k, and keeps its size",
				"card(image(ι, k)) = card(k)",
				By(
					N,
					hom,
					subK,
					finiteK,
					ring_homomorphism.FieldHomomorphismInjective.Read(M).At(fieldN, ι),
					field.SubfieldSubset.At(fieldM, k),
					functions.InjectiveOnSubset.At(ι, k, a.TermAs[Set[A]]("M.carrier")),
					cardinality.CardImageInj.At(ι, k)))
			counts := a.Have(
				"over the field of q^m elements, m > 0, the carried curve has as many points as the curve",
				"∀m:num. 0 < m ⇒ card(«carriedPoints»(m)) = card(«points»(m))",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					positive := b.Assume()
					l := b.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), m)")
					extension := b.Conjuncts(
						GroupPremises(
							M, closed, subK, finiteK, positive, finite_field.FiniteConstantsSubfield.At(fieldM, k, m)),
						"the points of M the q^m-th power fixes form a subfield",
						"it holds k",
						"it has q^m elements")
					maps := b.Have(
						"a point over the field of q^m elements is a map "+
							"with its coordinates up to n there and zero past n",
						"«points»(m) ⊆ "+
							"{h:(num → A) | "+
							"    (∀i:num. i ∈ {j:num | j ≤ n} ⇒ h(i) ∈ finite_constants(field_ring(M), card(k), m)) ∧ "+
							"    (∀i:num. i ∉ {j:num | j ≤ n} ⇒ h(i) = M.zero)}",
						BySets(projective_curve.PointCoordinatesIn, projective_curve.PointZeroPastN, nat_order.NotLessEq))
					finitely := b.Have(
						"so the points are finitely many, the coordinates up to n ranging over a finite field",
						"finite(«points»(m))",
						By(
							maps,
							extension[2],
							cardinality.HasSizeDef.At(l, b.TermAs[Nat]("card(k) ^ m")),
							num_segment.FiniteBelow.At(n),
							cardinality.FiniteFunspace.At(b.TermAs[Set[Nat]]("{j:num | j ≤ n}"), l, b.TermAs[A]("M.zero")),
							finite_set.FiniteSubset))
					carriedField := b.Have(
						"ι carries the field of q^m elements of M onto N's",
						"image(ι, finite_constants(field_ring(M), card(k), m)) = "+
							"finite_constants(field_ring(N), card(k), m)",
						By(
							M,
							N,
							closed,
							hom,
							subK,
							finiteK,
							positive,
							finite_field.FiniteConstantsImage.At(fieldM, fieldN, ι, k, m)))
					b.Show(
						"so the carried curve's points over N's field are "+
							"the curve's over M's, carried one to one, and as many",
						carriedField.RwRev(),
						By(
							M,
							N,
							hom,
							subK,
							equationsOverK,
							finitely,
							extension[0],
							field.SubfieldSubset.At(fieldM, l),
							CarriedPoints.At(fieldM, fieldN, ι, k, l, n, E),
							cardinality.CardImageInj.At(carriedPoint, b.TermAs[Set[Fun[Nat, A]]]("«points»(m)"))))
				}))
			a.Show(
				"the two counts",
				By(constants, counts))
		}),
})}

// CarriedPointExists — along a ring homomorphism ι of an algebraically closed
// field M into another, N, a curve given by finitely many polynomials E over
// M, with constants k, has a projective point over M exactly when the carried
// curve has one over N, with constants ι(k). The finite set E is listed as
// P(0), …, P(r − 1), r = card(E), and the carried equations then as
// «carried»(P(j)). Listed, the points of either curve are the normalized
// (n + 1)-tuples at which its family vanishes
// (projective_curve.PointsAsNormalizedZeros), over M for P and over N for the
// carried family; that such a tuple exists is a first-order sentence in the
// coefficients of the family, polynomials over M in n + 1 variables, and ι,
// an embedding of one algebraically closed field into another, is elementary
// (ByElementarity, the embedding mode).
var CarriedPointExists = carriedPointExistsThm{family.Add(registry.ProofEntry{
	Name: "CarriedPointExists",
	Key:  "prop_32b91adf8f05441b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"algebraically_closed_field(N)",
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"finite(E)",
			"E ⊆ polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n}).carrier",
		},
		Conclusion: "(∃y:(num → B). " +
			"    y ∈ " +
			"    projective_equation_points(field_ring(N), " +
			"        image(ι, k), " +
			"        N.carrier, " +
			"        n, " +
			"        image(«carried», E))) ⇔ " +
			"(∃x:(num → A). x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			N field.FieldFact[on.N],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is algebraically closed",
				"N is algebraically closed",
				"ι is a ring homomorphism of M into N",
				"E is finite",
				"the equations are polynomials over M")
			closedM, closedN, hom, finite, equationsOverM := parts[0], parts[1], parts[2], parts[3], parts[4]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			polynomialsOverM := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
				"polynomial_algebra(field_ring(M), {i:num | i ≤ n})")
			_, P, listing := a.Obtain2As[Nat, Fun[Nat, Fun[Fun[Nat, Nat], A]]](
				"E is finite, so it is the image of the numbers below its size",
				"∃r:num. ∃P:(num → (num → num) → A). E = image(P, {j:num | j < r})",
				Derive(func(b *Argument) {
					count := b.TermAs[Nat]("card(E)")
					below := b.TermAs[Set[Nat]]("{j:num | j < card(E)}")
					size := b.Have(
						"the numbers below card(E) are card(E) many",
						"finite({j:num | j < card(E)}) ∧ card({j:num | j < card(E)}) = card(E)",
						By(num_segment.HasSizeBelowStrict.At(count), cardinality.HasSizeDef.At(below, count)))
					P, enumeration := b.UnpackAs[Fun[Nat, Fun[Fun[Nat, Nat], A]]](
						GroupPremises(finite, size, cardinality.CardEqBijection.At(below, E)),
						"P")
					b.Take(count)
					b.Take(P)
					b.Show(
						"P maps the numbers below card(E) onto E",
						BySets(enumeration))
				}))
			bound := a.Have(
				"so each P(j), j < r, is a polynomial over M in the variables below n + 1",
				"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(M), {i:num | i < n + 1})",
				Simp(Rev(nat_arith.Add1), Fwd(nat_order.LessThanSucIffLessEq)),
				By(
					listing,
					equationsOverM,
					set_image.ImageSubsetIff.At(P, a.TermAs[Set[Nat]]("{j:num | j < r}"), polynomialsOverM)))
			closedFieldM := a.Have(
				"M is an algebraically closed field",
				"algebraically_closed_field_on(M)",
				By(M, closedM, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldM)))
			closedFieldN := a.Have(
				"N is an algebraically closed field",
				"algebraically_closed_field_on(N)",
				By(N, closedN, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldN)))
			transfer := a.Have(
				"P has a normalized zero over M exactly when its carried "+
					"family λj. λm. ι(P(j, m)) has one over N: ι is elementary",
				"(∃x:(num → A). "+
					"    ring_tuple(field_ring(M), n + 1, x) ∧ "+
					"    (∃j:num. j < n + 1 ∧ x(j) = M.one ∧ (∀i:num. i < j ⇒ x(i) = M.zero)) ∧ "+
					"    (∀j:num. j < r ⇒ polynomial_value(field_ring(M), P(j), x) = M.zero)) ⇔ "+
					"(∃y:(num → B). "+
					"    ring_tuple(field_ring(N), n + 1, y) ∧ "+
					"    (∃j:num. j < n + 1 ∧ y(j) = N.one ∧ (∀i:num. i < j ⇒ y(i) = N.zero)) ∧ "+
					"    (∀j:num. "+
					"        j < r ⇒ "+
					"        polynomial_value(field_ring(N), (λj:num. λm:(num → num). ι(P(j, m)))(j), y) = N.zero))",
				ByElementarity(nil, closedFieldM, closedFieldN, hom, bound))
			a.Show(
				"listed, either curve has a point exactly when its family has a normalized zero",
				listing.Rw(),
				Simp(
					Rev(set_image.ImageCompose),
					Fwd(functions.ComposeApply),
					Fwd(projective_curve.PointsAsNormalizedZeros)),
				By(transfer))
		}),
})}
