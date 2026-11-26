// pseudo_remainder.go — a pseudo-division of f by g read at a root of the
// image of g under a ring homomorphism into a field that keeps the leading
// coefficient of g: there the remainder's value is a nonzero multiple of the
// dividend's, so the pseudo-remainder vanishes exactly where the dividend
// does.

package polynomial_roots

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// PseudoDivisionValueAtRoot — a pseudo-division cᵉ f = g·s + r over R, c
// the leading coefficient of g, read at a root x of the image of g under a
// ring homomorphism σ from R into a field keeping c nonzero, R being a
// commutative ring as the source of σ (ring_homomorphism.Source): σcᵉ is a
// nonzero element of the field, and σcᵉ·σf(x) = σr(x). σ carries the
// identity coefficientwise (polynomial_evaluation.CoefficientMapDivision), σ(cᵉ)
// being σcᵉ, and at the root x the image of g·s vanishes
// (polynomial_evaluation.DivisionValueAtRoot); a power of the nonzero σc is
// not zero, a field having no zero divisors.
var PseudoDivisionValueAtRoot = pseudoDivisionValueAtRootThm{family.Add(registry.ProofEntry{
	Name: "PseudoDivisionValueAtRoot",
	Key:  "prop_3c4b1dfc5b650e30",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀R:ring_ops(B). ∀σ:(B → A). ∀f g s r:(num → B). ∀x:A.",
		Hypotheses: []string{
			"field_on(F)",
			"ring_homomorphism(R, field_ring(F), σ)",
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, s)",
			"polynomial_over(R.carrier, r)",
			"monoid_pow(R.mul, R.one, g(polynomial_degree(g)), «exponent») • f = polynomial_mul(g, s) + r",
			"σ(g(polynomial_degree(g))) ≠ F.zero",
			"x ∈ F.carrier",
			"polynomial_eval(λi:num. σ(g(i)), x) = F.zero",
		},
		Conclusion: "«scale» ∈ F.carrier ∧ " +
			"«scale» ≠ F.zero ∧ " +
			"«scale» * polynomial_eval(λi:num. σ(f(i)), x) = polynomial_eval(λi:num. σ(r(i)), x)",
		Abbrev: Abbrev{
			{Name: "exponent", Text: "suc(polynomial_degree(f)) - polynomial_degree(g)"},
			{Name: "scale", Text: "monoid_pow(F.mul, F.one, σ(g(polynomial_degree(g))), «exponent»)"},
		},
	}, func(
		a *Argument,
		_ *Expr[FieldOps[A]],
		fieldOn field.FieldFact[on.F],
		_ *Expr[module_record.RingOps[B]],
		_ *Arrow[B, A],
		hom Fact,
		f, g, s, r *Arrow[Nat, B],
		fOver, gOver, sOver, rOver, divided, kept Fact,
		x *Member[A, on.F],
		root Fact,
	) {
		ring := ring_homomorphism.Source.Read(hom)
		lead := a.TermAs[B]("g(polynomial_degree(g))")
		imageLead := a.TermAs[A]("σ(g(polynomial_degree(g)))")
		exponent := a.TermAs[Nat]("«exponent»")
		scale := a.TermAs[A]("«scale»")
		fieldRing := field.RingOn.Read(fieldOn)
		leadIn := polynomial.CoefficientIn.Read(gOver).At(a.TermAs[Nat]("polynomial_degree(g)"))
		imageLeadIn := ring_homomorphism.MapIn.Read(hom).AsFact().At(lead)
		identity := a.Have(
			"σ carries the pseudo-division coefficientwise, σ(cᵉ) being σcᵉ",
			"«scale» • (λi:num. σ(f(i))) = "+
				"polynomial_mul(λi:num. σ(g(i)), λi:num. σ(s(i))) + (λi:num. σ(r(i)))",
			By(
				fOver,
				gOver,
				sOver,
				rOver,
				divided,
				leadIn,
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(lead, exponent),
				polynomial_evaluation.CoefficientMapDivision.Read(hom).AsFact().At(
					a.TermAs[B]("monoid_pow(R.mul, R.one, g(polynomial_degree(g)), «exponent»)"), f, g, s, r),
				ring_homomorphism.RingMapPower.Read(hom).AsFact().At(exponent, lead)))
		images := a.Have(
			"the images of f, g, s and r are polynomials over F",
			"polynomial_over(F.carrier, λi:num. σ(f(i))) ∧ "+
				"polynomial_over(F.carrier, λi:num. σ(g(i))) ∧ "+
				"polynomial_over(F.carrier, λi:num. σ(s(i))) ∧ "+
				"polynomial_over(F.carrier, λi:num. σ(r(i)))",
			By(
				fOver,
				gOver,
				sOver,
				rOver,
				polynomial.PolynomialOverMap,
				ring_homomorphism.MapZero.Read(hom),
				ring_homomorphism.MapIn.Read(hom)))
		scaleIn := a.Have(
			"σcᵉ lies in F",
			"«scale» ∈ F.carrier",
			By(
				leadIn,
				imageLeadIn,
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(fieldRing)).AsFact().At(imageLead, exponent)))
		a.Show(
			"σcᵉ is a nonzero element of F, and at the root x of σg the identity reads σcᵉ·σf(x) = σr(x)",
			SplitConjAll(
				Case(
					"σcᵉ lies in F",
					By(scaleIn)),
				Case(
					"a power of the nonzero σc is not zero",
					By(kept, leadIn, imageLeadIn, field.PowEqZeroOn.Read(fieldOn).AsFact().At(imageLead, exponent))),
				Case(
					"at the root x of σg the image of g·s vanishes, so σcᵉ·σf(x) = σr(x)",
					By(
						identity,
						root,
						images,
						x,
						scaleIn,
						polynomial_evaluation.EvalScalar.Read(fieldRing).AsFact().At(
							scale, x, a.TermAs[Fun[Nat, A]]("λi:num. σ(f(i))")),
						polynomial_evaluation.DivisionValueAtRoot.Read(fieldRing).AsFact().At(
							a.TermAs[Fun[Nat, A]]("«scale» • (λi:num. σ(f(i)))"),
							a.TermAs[Fun[Nat, A]]("λi:num. σ(g(i))"),
							a.TermAs[Fun[Nat, A]]("λi:num. σ(s(i))"),
							a.TermAs[Fun[Nat, A]]("λi:num. σ(r(i))"),
							x)))))
	}),
})}

// PseudoRemainderRoots — over a commutative ring R, the pseudo-remainder r
// of f by g, with no coefficient from deg g on, vanishes at a root of the
// image of g exactly where the image of f does, under every homomorphism σ
// into a field keeping the leading coefficient c of g: at a root x of σg
// the pseudo-division cᵉ f = g·s + r reads σcᵉ·σf(x) = σr(x), σcᵉ a
// nonzero element of the field (PseudoDivisionValueAtRoot), and a field has
// no zero divisors.
var PseudoRemainderRoots = pseudoRemainderRootsThm{family.Add(registry.ProofEntry{
	Name: "PseudoRemainderRoots",
	Key:  "prop_d7d3f1085c8ce440",
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
			"    (∀F:field_ops(A). ∀σ:(B → A). ∀x:A. " +
			"        field_on(F) ∧ " +
			"        ring_homomorphism(R, field_ring(F), σ) ∧ " +
			"        σ(g(polynomial_degree(g))) ≠ F.zero ∧ " +
			"        x ∈ F.carrier ∧ " +
			"        polynomial_eval(λi:num. σ(g(i)), x) = F.zero ⇒ " +
			"        (polynomial_eval(λi:num. σ(f(i)), x) = F.zero ⇔ " +
			"            polynomial_eval(λi:num. σ(r(i)), x) = F.zero))",
		Abbrev: Abbrev{
			{Name: "exponent", Text: "suc(polynomial_degree(f)) - polynomial_degree(g)"},
		},
	}, func(
		a *Argument,
		R *Expr[module_record.RingOps[B]],
		ring comm_ring.CommRingFact[on.R],
		f, g *Arrow[Nat, B],
		fOver, gOver Fact,
	) {
		s, r, division := a.Unpack2As[Fun[Nat, B], Fun[Nat, B]](
			GroupPremises(fOver, gOver, polynomial_division.PseudoDivision.Read(ring).At(f, g)),
			"s", "r")
		parts := a.Conjuncts(
			division,
			"s is a polynomial over R",
			"so is r",
			"r vanishes from the degree of g on",
			"cᵉ f is g·s + r, c the leading coefficient of g")
		a.Take(r)
		a.Show(
			"r is a polynomial over R vanishing from the degree of g on, and "+
				"its images vanish with those of f at the roots of the image of g",
			SplitConjAll(
				Case(
					"r is a polynomial over R",
					By(parts[1])),
				Case(
					"r vanishes from the degree of g on",
					By(parts[2])),
				Case(
					"at a root of the image of g, the image of r vanishes exactly where the image of f does",
					Derive(func(b *Argument) {
						b.FixAs[FieldOps[A]]("F")
						σ := b.FixAs[Fun[B, A]]("σ")
						x := b.FixAs[A]("x")
						given := b.Conjuncts(
							b.Assume(),
							"F is a field",
							"σ is a ring homomorphism from R into F",
							"σ keeps the leading coefficient of g nonzero",
							"x lies in F",
							"x is a root of the image of g")
						fieldOn, hom, kept, xIn, root := given[0], given[1], given[2], given[3], given[4]
						atRoot := b.Conjuncts(
							GroupPremises(
								hom,
								kept,
								root,
								fOver,
								gOver,
								division,
								PseudoDivisionValueAtRoot.Read(fieldOn).At(R, σ, f, g, s, r, b.MemberOf[on.Any](x, xIn))),
							"σcᵉ lies in F",
							"σcᵉ is not zero",
							"σcᵉ·σf(x) = σr(x)")
						imageF := b.TermAs[Fun[Nat, A]]("λi:num. σ(f(i))")
						value := b.TermAs[A]("polynomial_eval(λi:num. σ(f(i)), x)")
						valueIn := b.Have(
							"σf(x) lies in F, the image of f being a polynomial over F",
							"polynomial_eval(λi:num. σ(f(i)), x) ∈ F.carrier",
							By(
								fOver,
								xIn,
								polynomial.PolynomialOverMap,
								ring_homomorphism.MapZero.Read(hom),
								ring_homomorphism.MapIn.Read(hom),
								polynomial_evaluation.EvalIn.Read(field.RingOn.Read(fieldOn)).AsFact().At(imageF, x)))
						b.Show(
							"σcᵉ is not zero, so σf(x) and σr(x) vanish together",
							By(
								atRoot[0],
								atRoot[1],
								atRoot[2],
								valueIn,
								field.MulEqZeroOn.Read(fieldOn).AsFact().At(
									b.TermAs[A]("monoid_pow(F.mul, F.one, σ(g(polynomial_degree(g))), «exponent»)"),
									value)))
					}))))
	}),
})}
