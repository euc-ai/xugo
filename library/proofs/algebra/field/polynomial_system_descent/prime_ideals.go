// prime_ideals.go — the primality of the ideal finitely many forms generate,
// carried along an embedding of algebraically closed fields. An algebraically
// closed field is infinite, so over either field the ideal's primality reads as
// first-order conditions on the coefficients of the forms
// (homogeneous_polynomial.FormIdealPrimeCriterion), and the embedding, being
// elementary, carries each condition both ways.

package polynomial_system_descent

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/registry"
)

// FormIdealPrimeDescent — along a ring homomorphism ι of an algebraically
// closed field M into another, N, the ideal the forms P(0), …, P(r − 1) over M
// generate is prime exactly when the ideal their carried forms generate over N
// is. Both fields are infinite (finite_field.ClosedFieldInfinite) and, being
// fields, integral domains (integral_domain.FieldIntegralDomain), and a carried
// form is a form of the same degree (homogeneous_polynomial.CarriedForm), so on
// either side homogeneous_polynomial.FormIdealPrimeCriterion reads primality as
// conditions on the coefficients of the forms: 1 is no combination of them
// with constant cofactors, and at each degree bound D a product of polynomials
// of degree at most D that is a combination with cofactors of degree at most
// 2D has a factor that is a combination with cofactors of degree at most D,
// every combination an identity of values at the points. Each condition is a
// first-order sentence in the coefficients, the forms being polynomials of
// bounded degree, and ι, an embedding of one algebraically closed field into
// another, is elementary (ByElementarity, the embedding mode): it holds over M
// exactly when its carried sentence holds over N.
var FormIdealPrimeDescent = formIdealPrimeDescentThm{family.Add(registry.ProofEntry{
	Name: "FormIdealPrimeDescent",
	Key:  "prop_cfd9de6b734181f3",
	Reading: "Both fields being algebraically closed is load-bearing twice: the criterion reads " +
		"membership through values at points, which needs infinite fields, and the transfer needs ι " +
		"to be an elementary embedding, which an embedding of closed fields is. Homogeneity of the " +
		"P(j) is what bounds the cofactors' degrees in the criterion. With no forms (r = 0) both " +
		"ideals are zero, prime on both sides, the polynomial rings over fields being domains.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀N:field_on(B). ∀ι:(A → B). ∀n r:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"algebraically_closed_field(N)",
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(field_ring(M), n, e, P(j))",
		},
		Conclusion: "prime_ideal(«polynomialsN», " +
			"    ideal_span(«polynomialsN», image(«carriedFamily», {j:num | j < r}))) ⇔ " +
			"prime_ideal(«polynomialsM», ideal_span(«polynomialsM», image(P, {j:num | j < r})))",
		Abbrev: Abbrev{
			{Name: "polynomialsM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "polynomialsN", Text: "polynomial_algebra_ring(field_ring(N), {i:num | i ≤ n})"},
			{Name: "carriedFamily", Text: "λj:num. λm:(num → num). ι(P(j, m))"},
			{Name: "combinationM", Text: "λb:num. λv:((num → A) → A). ∃H:(num → (num → num) → A). " +
				"    (∀j:num. j < r ⇒ polynomial_bound(field_ring(M), n + 1, b, H(j))) ∧ " +
				"    (∀x:(num → A). " +
				"        ring_tuple(field_ring(M), n + 1, x) ⇒ " +
				"        v(x) = " +
				"        module_sum(M.add, " +
				"            M.zero, " +
				"            {j:num | j < r}, " +
				"            λj:num. " +
				"                M.mul(polynomial_value(field_ring(M), P(j), x), " +
				"                    polynomial_value(field_ring(M), H(j), x))))"},
			{Name: "combinationN", Text: "λb:num. λv:((num → B) → B). ∃H:(num → (num → num) → B). " +
				"    (∀j:num. j < r ⇒ polynomial_bound(field_ring(N), n + 1, b, H(j))) ∧ " +
				"    (∀y:(num → B). " +
				"        ring_tuple(field_ring(N), n + 1, y) ⇒ " +
				"        v(y) = " +
				"        module_sum(N.add, " +
				"            N.zero, " +
				"            {j:num | j < r}, " +
				"            λj:num. " +
				"                N.mul(polynomial_value(field_ring(N), " +
				"                        (λj:num. λm:(num → num). ι(P(j, m)))(j), " +
				"                        y), " +
				"                    polynomial_value(field_ring(N), H(j), y))))"},
			{Name: "factorM", Text: "λD:num. ∀f g:((num → num) → A). " +
				"    polynomial_bound(field_ring(M), n + 1, D, f) ∧ " +
				"    polynomial_bound(field_ring(M), n + 1, D, g) ∧ " +
				"    «combinationM»(2 * D, " +
				"        λx:(num → A). " +
				"            M.mul(polynomial_value(field_ring(M), f, x), " +
				"                polynomial_value(field_ring(M), g, x))) ⇒ " +
				"    «combinationM»(D, λx:(num → A). polynomial_value(field_ring(M), f, x)) ∨ " +
				"    «combinationM»(D, λx:(num → A). polynomial_value(field_ring(M), g, x))"},
			{Name: "factorN", Text: "λD:num. ∀f g:((num → num) → B). " +
				"    polynomial_bound(field_ring(N), n + 1, D, f) ∧ " +
				"    polynomial_bound(field_ring(N), n + 1, D, g) ∧ " +
				"    «combinationN»(2 * D, " +
				"        λy:(num → B). " +
				"            N.mul(polynomial_value(field_ring(N), f, y), " +
				"                polynomial_value(field_ring(N), g, y))) ⇒ " +
				"    «combinationN»(D, λy:(num → B). polynomial_value(field_ring(N), f, y)) ∨ " +
				"    «combinationN»(D, λy:(num → B). polynomial_value(field_ring(N), g, y))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			N field.FieldFact[on.N],
			ι *Arrow[A, B],
			n, r *Expr[Nat],
			P *Arrow2[Nat, Fun[Nat, Nat], A],
			closedM, closedN, hom, forms Fact,
		) {
			type polynomial = Fun[Fun[Nat, Nat], A]
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldN := a.TermAs[FieldOps[B]]("N")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			ringN := a.TermAs[RingOps[B]]("field_ring(N)")
			carried := a.TermAs[Fun[Nat, Fun[Fun[Nat, Nat], B]]]("«carriedFamily»")
			infiniteM := a.Have(
				"M is infinite, being algebraically closed",
				"infinite(M.carrier)",
				By(closedM, finite_field.ClosedFieldInfinite.Read(M)))
			infiniteN := a.Have(
				"and so is N",
				"infinite(N.carrier)",
				By(closedN, finite_field.ClosedFieldInfinite.Read(N)))
			carriedForms := a.Have(
				"ι carries each form P(j) to a form of the same degree",
				"∀j:num. j < r ⇒ ∃e:num. homogeneous_polynomial(field_ring(N), n, e, «carriedFamily»(j))",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					below := b.Assume()
					e, form := b.UnpackAs[Nat](GroupPremises(below, forms.At(j)), "e")
					b.Take(e)
					b.Show(
						"a form of degree e carried along ι is a form of degree e",
						By(
							form,
							hom,
							homogeneous_polynomial.CarriedForm.At(ringM, ringN, ι, n, e, b.TermAs[polynomial]("P(j)"))))
				}))
			bound := a.Have(
				"the forms are polynomials over M in the variables below n + 1",
				"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(M), {i:num | i < n + 1})",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					below := b.Assume()
					e, form := b.UnpackAs[Nat](GroupPremises(below, forms.At(j)), "e")
					Pj := b.TermAs[polynomial]("P(j)")
					b.Show(
						"a form of degree e is a polynomial of degree at most e",
						By(
							form,
							homogeneous_polynomial.FormBound.At(ringM, n, e, Pj),
							polynomial_encoding.PolynomialBoundDef.At(ringM, b.TermAs[Nat]("n + 1"), e, Pj)))
				}))
			closedFieldM := a.Have(
				"M is an algebraically closed field",
				"algebraically_closed_field_on(M)",
				By(M, closedM, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldM)))
			closedFieldN := a.Have(
				"and so is N",
				"algebraically_closed_field_on(N)",
				By(N, closedN, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldN)))
			unit := a.Have(
				"1 is a combination of the forms with constant cofactors over M "+
					"exactly when it is one of the carried forms over N: ι is elementary",
				"«combinationM»(0, λx:(num → A). M.one) ⇔ «combinationN»(0, λy:(num → B). N.one)",
				ByElementarity(nil, closedFieldM, closedFieldN, hom, bound))
			factors := a.Have(
				"and at each degree bound D, a product in the ideal has a factor in it over M exactly when over N",
				"∀D:num. «factorM»(D) ⇔ «factorN»(D)",
				a.ForEach(func(D *Expr[Nat]) Action {
					return ByElementarity(nil, closedFieldM, closedFieldN, hom, bound)
				}))
			a.Show(
				"either ideal is prime exactly when its conditions hold, and the conditions agree",
				GroupPremises(
					infiniteN,
					carriedForms,
					homogeneous_polynomial.FormIdealPrimeCriterion.Read(integral_domain.FieldIntegralDomain.Read(N)).At(
						n, r, carried)).Rw(),
				GroupPremises(
					infiniteM,
					forms,
					homogeneous_polynomial.FormIdealPrimeCriterion.Read(integral_domain.FieldIntegralDomain.Read(M)).At(
						n, r, P)).Rw(),
				unit.Rw(),
				Simp(Fwd(factors)),
				Basic())
		}),
})}
