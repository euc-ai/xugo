// orders.go — the order, evaluation and pole filtration at a regular
// rational point, gathered from their three members.

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// RegularPointOrderAndFiltration — at a regular point P of a curve over the
// line, the order is a valuation whose exponent of a nonzero function is the
// one integer power of the maximal ideal it generates, evaluation at P is a
// ring map from the local ring onto the constants k fixing k with kernel the
// maximal ideal, and the pole spaces L(nP) grow by at most one dimension a
// step, are cut out of each other by the order at P and are regular at every
// other regular point: the order, the evaluation and the pole filtration at
// P, the evaluation read at the rational half of the regular point.
var RegularPointOrderAndFiltration = regularPointOrderAndFiltrationThm{family.Add(registry.ProofEntry{
	Name: "RegularPointOrderAndFiltration",
	Key:  "prop_e1489dcf0583839c",
	Reading: "The filtration clause is relative: it cuts L(nP) out of a known L(mP) by " +
		"the order at P, since orders at regular points alone cannot detect regularity at " +
		"a singular point of the model. The statement is local to the point: neither " +
		"finiteness of k nor regularity of the function field enters, so a Weierstrass " +
		"model instantiates it at its origin without any statement about its constant field.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "valuation_order(field_ring(L), «order») ∧ " +
			"(∀f:A. " +
			"    f ∈ L.carrier ∧ f ≠ L.zero ⇒ " +
			"    ∃!n:int. " +
			"        image(L.mul(f), «local») = signed_ideal_power(field_ring(L), «local», «maximal», n)) ∧ " +
			"(∀f:A. f ∈ «local» ⇒ «evaluation»(f) ∈ k ∧ f - «evaluation»(f) ∈ «maximal») ∧ " +
			"ring_homomorphism(restrict_ring(field_ring(L), «local»), " +
			"    restrict_ring(field_ring(L), k), " +
			"    «evaluation») ∧ " +
			"(∀a:A. a ∈ k ⇒ «evaluation»(a) = a) ∧ " +
			"{a:A | a ∈ «local» ∧ «evaluation»(a) = L.zero} = «maximal» ∧ " +
			"(∀n:num. " +
			"    module_dim(restrict_ring(field_ring(L), k), «poles»(n + 1)) ≤ " +
			"    module_dim(restrict_ring(field_ring(L), k), «poles»(n)) + 1) ∧ " +
			"(∀f:A. ∀n:num. f ∈ «poles»(n).carrier ∧ f ≠ L.zero ⇒ -n ≤ «order»(f)) ∧ " +
			"(∀f:A. ∀m n:num. " +
			"    f ∈ «poles»(m).carrier ∧ n ≤ m ⇒ (f ∈ «poles»(n).carrier ⇔ f = L.zero ∨ -n ≤ «order»(f))) ∧ " +
			"(∀f:A. ∀n:num. ∀Q:prod(set(A), set(A)). " +
			"    f ∈ «poles»(n).carrier ∧ biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, Q) ∧ Q ≠ P ⇒ " +
			"    f ∈ point_local_ring(field_ring(L), A₀, A₁, Q))",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "order", Text: "regular_point_order(field_ring(L), A₀, A₁, P)"},
			{Name: "evaluation", Text: "regular_point_evaluation(field_ring(L), k, A₀, A₁, P)"},
			{Name: "poles", Text: "λn:num. single_point_pole_space(field_ring(L), A₀, A₁, P, n)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point Fact,
		) {
			rational := a.Conjuncts(
				a.Unfolded(point, lattice_pair_twist.BiaffineRegularPointDef),
				"P is a rational point of the overlap",
				"and its ideal pair is invertible")[0]
			a.Show(
				"the order at P, the evaluation at P and the pole filtration at P",
				By(
					curve,
					point,
					rational,
					OrderAtRegularPoint.Read(L).At(k, A0, A1, A01, t, P),
					EvaluationAtRationalPoint.Read(L).At(k, A0, A1, A01, t, P),
					PoleFiltrationAtRegularPoint.Read(L).At(k, A0, A1, A01, t, P)))
		}),
})}
