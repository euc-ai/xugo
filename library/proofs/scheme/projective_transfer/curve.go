// curve.go — the smooth projective equation curve carried along an embedding
// of algebraically closed fields.

package projective_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_system_descent"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CarriedSmoothCurve — along a ring homomorphism ι of an algebraically closed
// field M into another, N, a set E of forms over a subfield k of M cuts out a
// smooth projective equation curve over M exactly when the carried forms cut
// one out over N, with constants ι(k). The definition asks nine things of
// each side, and they match one by one. ι is one to one on k, whose image is
// a subfield of N (SubfieldHomomorphismEmbedding), so ι(k) is finite exactly
// when k is; «carried» is one to one on the polynomials over k
// (CarriedPolynomials), so the carried forms are finitely many exactly when E
// is, and each is a form over ι(k). With E infinite neither side holds. With
// E finite, listed as P(0), …, P(r − 1), forms over M as well: the carried
// forms span a prime ideal over N exactly when E spans one over M
// (FormIdealPrimeDescent); either curve has a point exactly when the other
// does (CarriedPointExists); the two Hilbert functions agree
// (CarriedHilbertFunction), so one genus, degree and bound serve both; and
// either meets the Jacobian condition exactly when the other does
// (CarriedSmoothness).
var CarriedSmoothCurve = carriedSmoothCurveThm{family.Add(registry.ProofEntry{
	Name: "CarriedSmoothCurve",
	Key:  "prop_6f6e560113c4129e",
	Reading: "Both fields being algebraically closed is load-bearing: primality, the point " +
		"and the Jacobian condition are carried by elementarity, which needs an embedding of " +
		"one closed field into another. E being forms over k is what the Hilbert function and " +
		"primality read; over M it is the forms condition itself, and over N it follows. k " +
		"need not be assumed finite: both sides ask it, and ι(k) is finite exactly when k is.",
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
			"subfield(M, k)",
			"∀P:((num → num) → A). P ∈ E ⇒ ∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
		},
		Conclusion: "smooth_projective_equation_curve(N, image(ι, k), n, image(«carried», E)) ⇔ " +
			"smooth_projective_equation_curve(M, k, n, E)",
		Abbrev: Abbrev{
			{Name: "polynomialsM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "polynomialsN", Text: "polynomial_algebra_ring(field_ring(N), {i:num | i ≤ n})"},
			{Name: "space", Text: "free_module_record(field_ring(M), {i:num | i ≤ n})"},
			{Name: "carriedSpace", Text: "free_module_record(field_ring(N), {i:num | i ≤ n})"},
			{Name: "gradients", Text: "λx:(num → A). λS:set((num → num) → A). " +
				"    {λi:num. " +
				"        COND(i ≤ n, polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x, polynomial_algebra_partial(«hilbertCoefficients», i, G)), M.zero):num → " +
				"        A | " +
				"    G:(num → num) → A | " +
				"    G ∈ S}"},
			{Name: "carriedGradients", Text: "λx:(num → B). λS:set((num → num) → B). " +
				"    {λi:num. " +
				"        COND(i ≤ n, polynomial_algebra_eval(«carriedCoefficients», field_ring(N), λa:B. a, x, polynomial_algebra_partial(«carriedCoefficients», i, G)), N.zero):num → " +
				"        B | " +
				"    G:(num → num) → B | " +
				"    G ∈ S}"},
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
			type polynomial = Fun[Fun[Nat, Nat], A]
			type carriedPolynomial = Fun[Fun[Nat, Nat], B]
			parts := a.Conjuncts(
				given,
				"M is algebraically closed",
				"N is algebraically closed",
				"ι is a ring homomorphism of M into N",
				"k is a subfield of M",
				"the equations are forms over k")
			closedM, closedN, hom, subK, formsE := parts[0], parts[1], parts[2], parts[3], parts[4]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
			kRing := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			carriedKRing := a.TermAs[module_record.RingOps[B]]("«carriedCoefficients»")
			carried := a.TermAs[Fun[polynomial, carriedPolynomial]]("«carried»")
			polynomialsOverK := a.TermAs[Set[polynomial]](
				"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})")

			onK := a.Have(
				"ι is a ring homomorphism on k",
				"ring_homomorphism(«hilbertCoefficients», field_ring(N), ι)",
				By(
					hom,
					subK,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.RingHomRestrictSource.At(ringM, ringN, ι, k)))
			embedding := a.Conjuncts(
				GroupPremises(
					N, subK, onK, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(fieldN, k, ι)),
				"ι(k) is a subfield of N",
				"ι is one to one on k")
			finiteK := a.Have(
				"so ι(k) is finite exactly when k is",
				"finite(image(ι, k)) ⇔ finite(k)",
				By(embedding[1], finite_set.FiniteImageInjEq.At(ι, k)))
			equationsOverK := a.Have(
				"the equations are polynomials over k",
				"E ⊆ «polynomials».carrier",
				BySets(formsE, homogeneous_polynomial.FormPolynomial))
			transfer := a.Conjuncts(
				GroupPremises(M, N, hom, subK, CarriedPolynomials.At(fieldM, fieldN, ι, k, n)),
				"ι is an isomorphism of k onto ι(k)",
				"«carried» is an isomorphism of the polynomials over k onto those over ι(k)",
				"taking the forms of each degree onto the forms of that degree")
			carriedIso := a.Conjuncts(
				a.Unfolded(transfer[1], ring_homomorphism.RingIsomorphismDef),
				"«carried» is a ring homomorphism",
				"one to one on the polynomials over k",
				"onto the polynomials over ι(k)")
			finiteE := a.Have(
				"so the carried equations are finitely many exactly when E is",
				"finite(image(«carried», E)) ⇔ finite(E)",
				By(
					carriedIso[1],
					equationsOverK,
					functions.InjectiveOnSubset.At(carried, E, polynomialsOverK),
					finite_set.FiniteImageInjEq.At(carried, E)))

			finite := a.Assuming(
				a.TermAs[Bool]("finite(E)"),
				"with E infinite so are the carried equations, and neither curve is one",
				Given(func(b *Argument, infinite Fact) {
					b.Do(Unfold(projective_curve.SmoothProjectiveEquationCurveDef))
					b.Show(
						"the equations of neither side are finitely many",
						By(infinite, finiteE))
				}))

			formsN := a.Have(
				"each carried equation is a form over ι(k), carried "+
					"from a form over k along ι, a ring homomorphism on k",
				Statement{
					Binders: "∀Q:((num → num) → B).",
					Hypotheses: []string{
						"Q ∈ image(«carried», E)",
					},
					Conclusion: "∃d:num. homogeneous_polynomial(«carriedCoefficients», n, d, Q)",
				},
				Simp(Fwd(set_image.ForallInImage)),
				By(
					formsE,
					transfer[0],
					ring_homomorphism.RingIsomorphismDef.At(kRing, carriedKRing, ι),
					homogeneous_polynomial.CarriedForm))
			r, P, listing := a.Obtain2As[Nat, Fun[Nat, polynomial]](
				"E is finite, so it is the image of the numbers below its size",
				"∃r:num. ∃P:(num → (num → num) → A). E = image(P, {j:num | j < r})",
				Derive(func(b *Argument) {
					count := b.TermAs[Nat]("card(E)")
					below := b.TermAs[Set[Nat]]("{j:num | j < card(E)}")
					size := b.Have(
						"the numbers below card(E) are card(E) many",
						"finite({j:num | j < card(E)}) ∧ card({j:num | j < card(E)}) = card(E)",
						By(num_segment.HasSizeBelowStrict.At(count), cardinality.HasSizeDef.At(below, count)))
					P, enumeration := b.UnpackAs[Fun[Nat, polynomial]](
						GroupPremises(finite, size, cardinality.CardEqBijection.At(below, E)),
						"P")
					b.Take(count)
					b.Take(P)
					b.Show(
						"P maps the numbers below card(E) onto E",
						BySets(enumeration))
				}))
			indices := a.TermAs[Set[Nat]]("{j:num | j < r}")
			formsOverM := a.Have(
				"each P(j), j < r, is one of the equations, a form "+
					"over k, so a form over M through the inclusion of k",
				"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(field_ring(M), n, e, P(j))",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(
						formsE,
						listing,
						subK,
						set_image.FunInImage.At(P, indices, j),
						field.SubfieldSubring.Read(M).At(k),
						ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k),
						homogeneous_polynomial.CarriedForm)
				}))
			prime := a.Have(
				"so the carried forms span a prime ideal over N exactly when E spans one over M",
				"prime_ideal(«polynomialsN», ideal_span(«polynomialsN», image(«carried», E))) ⇔ "+
					"prime_ideal(«polynomialsM», ideal_span(«polynomialsM», E))",
				listing.Rw(),
				Simp(Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
				By(
					M,
					N,
					closedM,
					closedN,
					hom,
					formsOverM,
					polynomial_system_descent.FormIdealPrimeDescent.At(fieldM, fieldN, ι, n, r, P)))
			hilbert := a.Have(
				"the carried equations have the Hilbert function of E",
				"∀d:num. "+
					"    projective_hilbert_function(field_ring(N), image(ι, k), n, image(«carried», E), d) = "+
					"    projective_hilbert_function(field_ring(M), k, n, E, d)",
				By(M, N, hom, subK, equationsOverK, CarriedHilbertFunction.At(fieldM, fieldN, ι, k, n, E)))
			linearGrowth := a.Have(
				"so one genus, degree and bound serve both Hilbert functions",
				"(∃g e b:num. "+
					"    0 < e ∧ "+
					"    (∀d:num. "+
					"        b ≤ d ⇒ "+
					"        projective_hilbert_function(field_ring(N), image(ι, k), n, image(«carried», E), d) + "+
					"        g = "+
					"        e * d + 1)) ⇔ "+
					"(∃g e b:num. "+
					"    0 < e ∧ "+
					"    (∀d:num. b ≤ d ⇒ projective_hilbert_function(field_ring(M), k, n, E, d) + g = e * d + 1))",
				Simp(Fwd(hilbert)),
				Refl())
			equationsOverM := a.Have(
				"the equations are polynomials over M, k lying in M",
				"E ⊆ «polynomialsM».carrier",
				By(
					subK,
					equationsOverK,
					field.SubfieldSubset.At(fieldM, k),
					polynomial_algebra.PolynomialAlgebraOverMono.At(ringM, k, a.TermAs[Set[Nat]]("{i:num | i ≤ n}")),
					set_order.SubsetTrans.At(
						E,
						polynomialsOverK,
						a.TermAs[Set[polynomial]]("polynomial_algebra(field_ring(M), {i:num | i ≤ n})"))))
			point := a.Have(
				"either curve has a point exactly when the other does",
				"(∃y:(num → B). "+
					"    y ∈ "+
					"    projective_equation_points(field_ring(N), "+
					"        image(ι, k), "+
					"        N.carrier, "+
					"        n, "+
					"        image(«carried», E))) ⇔ "+
					"(∃x:(num → A). x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E))",
				By(
					M,
					N,
					closedM,
					closedN,
					hom,
					finite,
					equationsOverM,
					CarriedPointExists.At(fieldM, fieldN, ι, k, n, E)))
			jacobian := a.Have(
				"and either meets the Jacobian condition exactly when the other does",
				"(∀x:(num → B). "+
					"    x ∈ "+
					"    projective_equation_points(field_ring(N), image(ι, k), N.carrier, n, image(«carried», E)) ⇒ "+
					"    module_dim(field_ring(N), "+
					"        restrict_module(«carriedSpace», "+
					"            module_span(field_ring(N), "+
					"                «carriedSpace», "+
					"                «carriedGradients»(x, image(«carried», E))))) + "+
					"    1 = "+
					"    n) ⇔ "+
					"(∀x:(num → A). "+
					"    x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E) ⇒ "+
					"    module_dim(field_ring(M), "+
					"        restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x, E)))) + "+
					"    1 = "+
					"    n)",
				By(
					M,
					N,
					closedM,
					closedN,
					hom,
					subK,
					finite,
					equationsOverK,
					CarriedSmoothness.At(fieldM, fieldN, ι, k, n, E)))
			a.Show(
				"unfolded, the nine conditions of the two curves match one by one",
				Unfold(projective_curve.SmoothProjectiveEquationCurveDef),
				By(
					embedding[0],
					subK,
					finiteK,
					finite,
					finiteE,
					formsN,
					formsE,
					prime,
					point,
					linearGrowth,
					jacobian))
		}),
})}
