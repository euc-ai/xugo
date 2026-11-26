// homomorphism_at_root.go — the homomorphisms out of a subring S[z] of a field:
// two homomorphisms agreeing on S and at z agree on S[z]; a homomorphism keeps
// simple roots apart; and one into a domain, one to one on deg p roots of a
// monic p, reaches every root of the image of p.

package integral_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialImageAgreement — two homomorphisms on a subring Q of a field that agree
// on S and at a point z of Q agree on S[z]: a value of a polynomial over S at z goes
// to the value at the image of z of the moved polynomial, and the two moved
// polynomials are one.
var PolynomialImageAgreement = polynomialImageAgreementThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageAgreement",
	Key:  "prop_302bbd637fde4239",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:ring_ops(B). ∀Q S:set(A). ∀f g:(A → B). ∀z y:A.",
		Hypotheses: []string{
			"ring_homomorphism(restrict_ring(field_ring(L), Q), T, f)",
			"ring_homomorphism(restrict_ring(field_ring(L), Q), T, g)",
			"S ⊆ Q",
			"z ∈ Q",
			"∀c:A. c ∈ S ⇒ f(c) = g(c)",
			"f(z) = g(z)",
			"y ∈ polynomial_image(field_ring(L), S, z)",
		},
		Conclusion: "f(y) = g(y)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		T *Expr[RingOps[B]],
		Q, S *Expr[Set[A]],
		f, g *Arrow[A, B],
		z, y *Expr[A],
		fHom, gHom, sInQ, zIn, agree, zAgree, yIn Fact,
	) {
		zero := arg.TermAs[A]("L.zero")
		R := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), Q)")
		p, value := arg.ObtainAs[Fun[Nat, A]](
			"y is the value at z of a polynomial over S",
			"∃p:(num → A). polynomial_over(S, p) ∧ y = polynomial_eval(p, z)",
			BySets(yIn, algebraic_element.PolynomialImageDef.At(arg.TermAs[RingOps[A]]("field_ring(L)"), S, z)))
		parts := arg.Conjuncts(
			value,
			"p is over S",
			"y is its value at z")
		over := arg.Have(
			"p is over Q",
			"polynomial_over(Q, p)",
			By(sInQ, parts[0], polynomial.PolynomialOverMono.At(zero, S, Q, p)))
		alongF := arg.Have(
			"f carries the value of p to the value of the polynomial moved along f",
			"f(polynomial_eval(p, z)) = polynomial_eval(λi:num. f(p(i)), f(z))",
			By(fHom, over, zIn, polynomial_evaluation.EvalAlongHomomorphism.At(R, T, f, p, z)))
		alongG := arg.Have(
			"so does g",
			"g(polynomial_eval(p, z)) = polynomial_eval(λi:num. g(p(i)), g(z))",
			By(gHom, over, zIn, polynomial_evaluation.EvalAlongHomomorphism.At(R, T, g, p, z)))
		same := arg.Have(
			"the two moved polynomials are one",
			"(λi:num. f(p(i))) = (λi:num. g(p(i)))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				b.FixAs[Nat]("i")
				b.Show(
					"each coefficient of p lies in S",
					By(agree.At(b.TermAs[A]("p(i)")), parts[0], polynomial.PolynomialOverDef.At(zero, S, p)))
			}))
		arg.Show(
			"so f and g agree at y",
			parts[1].Rw(),
			alongF.Rw(),
			alongG.Rw(),
			same.Rw(),
			zAgree.Rw(),
			Basic())
	}),
})}

// HomomorphismSeparatesSimpleRoots — let r and s be distinct roots in a subring C
// of a field of a nonzero polynomial F over C whose derivative at r is a unit of C.
// Then r - s divides that unit, so it is itself a unit of C, and no homomorphism of
// C into a nonzero ring identifies r with s.
var HomomorphismSeparatesSimpleRoots = homomorphismSeparatesSimpleRootsThm{family.Add(registry.ProofEntry{
	Name: "HomomorphismSeparatesSimpleRoots",
	Key:  "prop_dddb5686319c79a2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:ring_ops(B). ∀C:set(A). ∀e:(A → B). ∀F:(num → A). ∀r s v:A.",
		Hypotheses: []string{
			"subring(field_ring(L), C)",
			"ring_homomorphism(«chart», T, e)",
			"T.one ≠ T.zero",
			"polynomial_over(C, F)",
			"F ≠ vec_zero(L.zero)",
			"r ∈ C",
			"s ∈ C",
			"r ≠ s",
			"polynomial_eval(F, r) = L.zero",
			"polynomial_eval(F, s) = L.zero",
			"v ∈ C",
			"polynomial_eval(polynomial_derivative(F), r) * v = L.one",
		},
		Conclusion: "e(r) ≠ e(s)",
		Abbrev: Abbrev{
			{Name: "chart", Text: "restrict_ring(field_ring(L), C)"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		T *Expr[RingOps[B]],
		C *Expr[Set[A]],
		e *Arrow[A, B],
		F *Arrow[Nat, A],
		r, s, v *Expr[A],
		sub, hom, nontrivial, over, nonzero, rIn, sIn, distinct, rRoot, sRoot, vIn, unit Fact,
	) {
		chart := arg.TermAs[RingOps[A]]("«chart»")
		ring := ring_homomorphism.Source.Read(hom)
		target := ring_homomorphism.Target.Read(hom)
		domainC := arg.Have(
			"C, a subring of the field L, is a domain",
			"integral_domain_on(«chart»)",
			By(sub, integral_domain.SubringOfFieldDomain.Read(L).At(C)))
		c, factored := arg.UnpackAs[A](
			GroupPremises(
				domainC,
				over,
				nonzero,
				rIn,
				sIn,
				distinct,
				rRoot,
				sRoot,
				separable_polynomial.DerivativeAtRootFactors.At(chart, F, r, s)),
			"c")
		parts := arg.Conjuncts(
			factored,
			"c lies in C",
			"the derivative at r is (r - s) c")
		same := arg.Have(
			"suppose e(r) = e(s)",
			"e(r) = e(s)",
			By(arg.SupposeNot()))
		image := arg.Have(
			"e(r - s) vanishes",
			"e(r - s) = T.zero",
			GroupPremises(rIn, sIn, ring_homomorphism.MapSub.Read(hom).AsFact().At(r, s)).Rw(),
			same.Rw(),
			ByArith(target, ring_homomorphism.MapIn.Read(hom).AsFact().At(s), sIn))
		w := arg.TermAs[A]("c * v")
		wIn := arg.Have(
			"c v lies in C",
			"c * v ∈ C",
			By(parts[0], vIn, comm_ring.MulIn.Read(ring).AsFact().At(c, v)))
		differenceInC := arg.Have(
			"r - s lies in C",
			"r - s ∈ C",
			By(rIn, sIn, comm_ring.SubIn.Read(ring).AsFact().At(r, s)))
		product := arg.Have(
			"(r - s) c v is one",
			"(r - s) * (c * v) = L.one",
			ByArith(ring, parts[1], unit, parts[0], rIn, sIn, vIn))
		mapped := arg.Have(
			"so e(r - s) e(c v) is one",
			"T.mul(e(r - s), e(c * v)) = T.one",
			GroupPremises(
				differenceInC,
				wIn,
				ring_homomorphism.MapMul.Read(hom).AsFact().At(arg.TermAs[A]("r - s"), w)).RwRev(),
			product.Rw(),
			By(ring_homomorphism.MapOne.Read(hom)))
		arg.Show(
			"but e(r - s) vanishes, and one is not zero",
			ByArith(target, mapped, image, nontrivial, ring_homomorphism.MapIn.Read(hom).AsFact().At(w), wIn))
	}),
})}

// RootsOfImagePolynomial — let p be monic over a ring R, of degree the size of a finite
// set Y on which it vanishes, and let e be a homomorphism into a domain T, injective on
// Y. Every root of the image of p in T is the image of a point of Y: the images of the
// points of Y are card(Y) roots, as many as the image of p, of degree at most card(Y),
// can have.
var RootsOfImagePolynomial = rootsOfImagePolynomialThm{family.Add(registry.ProofEntry{
	Name: "RootsOfImagePolynomial",
	Key:  "prop_31d303b6674b73f0",
	Build: family.Theorem(Statement{
		Binders: "∀T:integral_domain_on(B). ∀R:ring_ops(A). ∀Y:set(A). ∀e:(A → B). ∀p:(num → A). ∀w:B.",
		Hypotheses: []string{
			"ring_homomorphism(R, T, e)",
			"polynomial_over(R.carrier, p)",
			"polynomial_monic(p)",
			"finite(Y)",
			"Y ⊆ R.carrier",
			"polynomial_degree(p) = card(Y)",
			"∀r:A. r ∈ Y ⇒ polynomial_eval(p, r) = R.zero",
			"injective_on(Y, e)",
			"w ∈ T.carrier",
			"polynomial_eval(«image», w) = T.zero",
		},
		Conclusion: "∃r:A. r ∈ Y ∧ e(r) = w",
		Abbrev: Abbrev{
			{Name: "image", Text: "λi:num. e(p(i))"},
			{Name: "roots", Text: "polynomial_roots(T.carrier, «image»)"},
		},
	}, func(
		arg *Argument,
		T integral_domain.IntegralDomainFact[on.T],
		R *Expr[RingOps[A]],
		Y *Expr[Set[A]],
		e *Arrow[A, B],
		p *Arrow[Nat, A],
		w *Expr[B],
		hom, over, monic, finiteY, inside, degree, vanishes, injective, wIn, wRoot Fact,
	) {
		zero, zeroT := arg.TermAs[A]("R.zero"), arg.TermAs[B]("T.zero")
		carrier, carrierT := arg.TermAs[Set[A]]("R.carrier"), arg.TermAs[Set[B]]("T.carrier")
		ringT := arg.TermAs[RingOps[B]]("T")
		image := arg.TermAs[Fun[Nat, B]]("«image»")
		roots := arg.TermAs[Set[B]]("«roots»")
		onImage := arg.TermAs[Set[B]]("image(e, Y)")
		keepsZero := ring_homomorphism.MapZero.Read(hom)
		imageOverT := arg.Have(
			"the image of p is a polynomial over T",
			"polynomial_over(T.carrier, «image»)",
			By(
				over,
				keepsZero,
				ring_homomorphism.MapIn.Read(hom),
				polynomial.PolynomialOverMap.At(e, zero, zeroT, carrier, carrierT, p)))
		leading := arg.Have(
			"its coefficient at the degree of p is one",
			"e(p(polynomial_degree(p))) = T.one",
			arg.Unfolded(monic, polynomial.PolynomialMonicDef).Rw(),
			By(ring_homomorphism.MapOne.Read(hom)))
		imageNonzero := arg.Have(
			"so it is not zero",
			"«image» ≠ vec_zero(T.zero)",
			Derive(func(b *Argument) {
				vanishing := b.SupposeNot()
				b.Show(
					"one is not zero in T",
					By(vanishing, leading, integral_domain.OneNotZero.Read(T), vec_space.VecZeroDef))
			}))
		bounded := arg.Conjuncts(
			GroupPremises(imageOverT, imageNonzero, polynomial_roots.RootBound.Read(T).At(image)),
			"the image of p has finitely many roots",
			"at most its degree")
		below := arg.Have(
			"the image of p has degree at most that of p",
			"polynomial_degree(«image») ≤ polynomial_degree(p)",
			By(
				over,
				keepsZero,
				polynomial.DegreeVec.At(zero, carrier, p),
				At(polynomial.VecMap, e, zero, zeroT, arg.TermAs[Nat]("suc(polynomial_degree(p))"), p),
				polynomial.DegreeLeast.At(zeroT, image, arg.TermAs[Nat]("polynomial_degree(p)"))))
		imagesAreRoots := arg.Have(
			"the images of the points of Y are roots",
			"image(e, Y) ⊆ «roots»",
			Derive(func(b *Argument) {
				pointwise := b.Have(
					"a point of Y goes to a root",
					"∀r:A. r ∈ Y ⇒ e(r) ∈ «roots»",
					Derive(func(c *Argument) {
						r := c.FixAs[A]("r")
						rIn := c.Assume()
						rCarrier := c.Have(
							"r lies in R",
							"r ∈ R.carrier",
							BySets(rIn, inside))
						along := c.Have(
							"e moves the value of p at r to the value of its image at e(r)",
							"e(polynomial_eval(p, r)) = polynomial_eval(«image», e(r))",
							By(hom, over, rCarrier, polynomial_evaluation.EvalAlongHomomorphism.At(R, ringT, e, p, r)))
						c.Show(
							"and p vanishes at r",
							Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
							By(
								rIn,
								rCarrier,
								along,
								keepsZero,
								vanishes.At(r),
								ring_homomorphism.MapIn.Read(hom).AsFact().At(r)))
					}))
				b.Show(
					"so the image of Y lies among the roots",
					BySets(pointwise))
			}))
		size := arg.Have(
			"e is injective on Y, so the image of Y has card(Y) points",
			"card(image(e, Y)) = card(Y)",
			By(injective, finiteY, cardinality.CardImageInj.At(e, Y)))
		equal := arg.Have(
			"so the image of Y is all the roots",
			"image(e, Y) = «roots»",
			By(
				bounded[0],
				imagesAreRoots,
				arg.Have(
					"there are at most card(Y) roots",
					"card(«roots») ≤ card(image(e, Y))",
					ByArith(bounded[1], below, degree, size)),
				cardinality.CardSubsetLe.At(onImage, roots)))
		isRoot := arg.Have(
			"w is a root",
			"w ∈ «roots»",
			Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
			BySets(wIn, wRoot))
		arg.Show(
			"so it is the image of a point of Y",
			BySets(
				arg.Have(
					"w lies in the image of Y",
					"w ∈ image(e, Y)",
					equal.Rw(),
					By(isRoot))))
	}),
})}
