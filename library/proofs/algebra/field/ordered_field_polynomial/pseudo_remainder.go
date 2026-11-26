// pseudo_remainder.go — the sign a pseudo-remainder keeps: taken with an even
// power of the divisor's leading coefficient, it has the dividend's sign at
// every root of the divisor's image in an ordered field.

package ordered_field_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PseudoRemainderSigns — the ordered twin of
// polynomial_roots.PseudoRemainderRoots: over a commutative ring R, the
// polynomial f has a pseudo-remainder r by g, vanishing from the degree of g
// on, that takes the sign of the image of f at every root of the image of g,
// under every homomorphism σ into an ordered field that keeps the leading
// coefficient c of g nonzero. Pseudo-division gives cᵉ f = g·s + r₀ with r₀
// vanishing from the degree of g on, and r is cᵉ r₀, which vanishes there
// too. At a root x of σg, σcᵉ·σf(x) = σr₀(x) with σcᵉ nonzero
// (polynomial_roots.PseudoDivisionValueAtRoot), so σr(x) is σcᵉ·σcᵉ·σf(x),
// and the square of the nonzero σcᵉ is positive.
var PseudoRemainderSigns = pseudoRemainderSignsThm{family.Add(registry.ProofEntry{
	Name: "PseudoRemainderSigns",
	Key:  "prop_4ab1f405a9449d5d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀f g:(num → B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "∃r:(num → B). " +
			"    polynomial_over(R.carrier, r) ∧ " +
			"    vec⟨polynomial_degree(g)⟩(r) ∧ " +
			"    (∀F:field_ops(A). ∀lt:(A → A → bool). ∀σ:(B → A). ∀x:A. " +
			"        ordered_field_on(F, lt) ∧ " +
			"        ring_homomorphism(R, field_ring(F), σ) ∧ " +
			"        σ(g(polynomial_degree(g))) ≠ F.zero ∧ " +
			"        x ∈ F.carrier ∧ " +
			"        polynomial_eval(λi:num. σ(g(i)), x) = F.zero ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(λi:num. σ(r(i)), x)) = " +
			"        ordered_sign(F, lt, polynomial_eval(λi:num. σ(f(i)), x)))",
		Abbrev: Abbrev{
			{Name: "exponent", Text: "suc(polynomial_degree(f)) - polynomial_degree(g)"},
			{Name: "power", Text: "monoid_pow(R.mul, R.one, g(polynomial_degree(g)), «exponent»)"},
			{Name: "scale", Text: "monoid_pow(F.mul, F.one, σ(g(polynomial_degree(g))), «exponent»)"},
		},
	}, func(
		a *Argument,
		R *Expr[module_record.RingOps[B]],
		ring comm_ring.CommRingFact[on.R],
		f, g *Arrow[Nat, B],
		fOver, gOver Fact,
	) {
		lead := a.TermAs[B]("g(polynomial_degree(g))")
		exponent := a.TermAs[Nat]("«exponent»")
		power := a.TermAs[B]("«power»")
		leadIn := polynomial.CoefficientIn.Read(gOver).At(a.TermAs[Nat]("polynomial_degree(g)"))
		s, r0, division := a.Unpack2As[Fun[Nat, B], Fun[Nat, B]](
			GroupPremises(fOver, gOver, polynomial_division.PseudoDivision.Read(ring).At(f, g)),
			"s", "r₀")
		parts := a.Conjuncts(
			division,
			"s is a polynomial over R",
			"so is r₀",
			"r₀ vanishes from the degree of g on",
			"cᵉ f is g·s + r₀, c the leading coefficient of g")
		powerIn := a.Have(
			"cᵉ lies in R",
			"«power» ∈ R.carrier",
			By(leadIn, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(lead, exponent)))
		a.Take(a.TermAs[Fun[Nat, B]]("vec_scalar_mul(«power», r₀)"))
		a.Show(
			"cᵉ r₀ is a polynomial over R vanishing from the degree of g on, and "+
				"its images have the sign of those of f at the roots of the image of g",
			SplitConjAll(
				Case(
					"cᵉ r₀ is a polynomial over R",
					BySets(module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)), powerIn, parts[1])),
				Case(
					"cᵉ r₀ vanishes from the degree of g on, as r₀ does",
					By(
						powerIn,
						parts[2],
						vec_space.VecSmulOn.Read(ring).AsFact().At(a.TermAs[Nat]("polynomial_degree(g)"), power, r0))),
				Case(
					"at a root of the image of g, the image of cᵉ r₀ has the sign of the image of f",
					Derive(func(b *Argument) {
						b.FixAs[FieldOps[A]]("F")
						b.FixAs[Fun2[A, A, Bool]]("lt")
						σ := b.FixAs[Fun[B, A]]("σ")
						x := b.FixAs[A]("x")
						given := b.Conjuncts(
							b.Assume(),
							"F with lt is an ordered field",
							"σ is a ring homomorphism from R into F",
							"σ keeps the leading coefficient of g nonzero",
							"x lies in F",
							"x is a root of the image of g")
						ordered, hom, kept, xIn, root := given[0], given[1], given[2], given[3], given[4]
						fieldOn := ordered_field.FieldOn.Read(ordered)
						fieldRing := field.RingOn.Read(fieldOn)
						atRoot := b.Conjuncts(
							GroupPremises(
								hom,
								kept,
								root,
								fOver,
								gOver,
								division,
								polynomial_roots.PseudoDivisionValueAtRoot.Read(fieldOn).At(
									R, σ, f, g, s, r0, b.MemberOf[on.Any](x, xIn))),
							"σcᵉ lies in F",
							"σcᵉ is not zero",
							"σcᵉ·σf(x) = σr₀(x)")
						scalarIn, nonzero, values := atRoot[0], atRoot[1], atRoot[2]
						imageF := b.TermAs[Fun[Nat, A]]("λi:num. σ(f(i))")
						imageR := b.TermAs[Fun[Nat, A]]("λi:num. σ(r₀(i))")
						scalar := b.TermAs[A]("«scale»")
						value := b.TermAs[A]("polynomial_eval(λi:num. σ(f(i)), x)")
						powerImage := b.Have(
							"σ carries cᵉ to σcᵉ",
							"σ(«power») = «scale»",
							By(leadIn, ring_homomorphism.RingMapPower.Read(hom).AsFact().At(exponent, lead)))
						scaledR := b.Have(
							"so σ carries cᵉ r₀ coefficient by coefficient to σcᵉ σr₀",
							"(λi:num. σ(vec_scalar_mul(«power», r₀, i))) = vec_scalar_mul(«scale», λi:num. σ(r₀(i)))",
							By(
								parts[1],
								powerIn,
								powerImage,
								polynomial_evaluation.CoefficientMapScalar.Read(hom).AsFact().At(power, r0)))
						images := b.Have(
							"the images of f and r₀ are polynomials over F",
							"polynomial_over(F.carrier, λi:num. σ(f(i))) ∧ polynomial_over(F.carrier, λi:num. σ(r₀(i)))",
							By(
								fOver,
								parts[1],
								polynomial.PolynomialOverMap,
								ring_homomorphism.MapZero.Read(hom),
								ring_homomorphism.MapIn.Read(hom)))
						valueIn := b.Have(
							"σf(x) lies in F",
							"polynomial_eval(λi:num. σ(f(i)), x) ∈ F.carrier",
							By(images, xIn, polynomial_evaluation.EvalIn.Read(fieldRing).AsFact().At(imageF, x)))
						remainderValue := b.Have(
							"so σ(cᵉ r₀)(x) is σcᵉ·σcᵉ·σf(x)",
							"polynomial_eval(λi:num. σ(vec_scalar_mul(«power», r₀, i)), x) = "+
								"«scale» * «scale» * polynomial_eval(λi:num. σ(f(i)), x)",
							By(
								scaledR,
								values,
								images,
								xIn,
								scalarIn,
								valueIn,
								polynomial_evaluation.EvalScalar.Read(fieldRing).AsFact().At(scalar, x, imageR),
								comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(fieldRing)).AsFact().At(scalar, scalar, value)))
						square := b.TermAs[A]("«scale» * «scale»")
						squareIn := b.Have(
							"σcᵉ·σcᵉ lies in F",
							"«scale» * «scale» ∈ F.carrier",
							By(scalarIn, comm_ring.MulIn.Read(fieldRing).AsFact().At(scalar, scalar)))
						squareSign := b.Have(
							"the square of the nonzero σcᵉ is positive, so its sign is one",
							"ordered_sign(F, lt, «scale» * «scale») = &1",
							By(
								nonzero,
								scalarIn,
								squareIn,
								ordered_field.SquarePositive.Read(ordered).AsFact().At(scalar),
								ordered_field.SignValues.Read(ordered).AsFact().At(square)))
						productSign := b.Have(
							"the sign of σcᵉ·σcᵉ·σf(x) is one times the sign of σf(x)",
							"ordered_sign(F, lt, «scale» * «scale» * polynomial_eval(λi:num. σ(f(i)), x)) = "+
								"ordered_sign(F, lt, polynomial_eval(λi:num. σ(f(i)), x))",
							ByArith(
								ordered_field.SignMul.Read(ordered).At(
									b.MemberOf[on.Any](square, squareIn), b.MemberOf[on.Any](value, valueIn)),
								squareSign))
						b.Show(
							"so σ(cᵉ r₀)(x) has the sign of σf(x)",
							By(remainderValue, productSign))
					}))))
	}),
})}
