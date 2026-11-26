package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothCurveConstantBaseChange — extending the constants to the field with
// q^r elements. The extended charts are a smooth curve of the same genus; a
// closed point of degree d splits into gcd(d, r) points of degree
// d / gcd(d, r); the point count over the field with q^m elements is the sum
// of the degrees dividing m, and the extended curve counts at m what the
// curve counts at r·m; and an invertible pair keeps the dimensions of H⁰ and
// H¹. Each clause is a member of its own.
var SmoothCurveConstantBaseChange = smoothCurveConstantBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveConstantBaseChange",
	Key:  "prop_7523d338faabc36c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "extended", Text: "restrict_ring(field_ring(M), «composite»)"},
			{Name: "extendedVectors", Text: "restrict_module(regular_module(field_ring(M)), «composite»)"},
			{Name: "chart₀", Text: "constant_chart(field_ring(M), «constants», A₀)"},
			{Name: "chart₁", Text: "constant_chart(field_ring(M), «constants», A₁)"},
			{Name: "chart₀₁", Text: "constant_chart(field_ring(M), «constants», A₀₁)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«ambientCurve»",
			"0 < r",
			"0 < m",
		},
		Conclusion: "smooth_finite_curve(restrict_field(M, «composite»), " +
			"    «constants», " +
			"    t, " +
			"    «chart₀», " +
			"    «chart₁», " +
			"    «chart₀₁») ∧ " +
			"curve_genus(«extended», «constants», «chart₀», «chart₁», «chart₀₁») = " +
			"curve_genus(«ambientRing», k, A₀, A₁, A₀₁) ∧ " +
			"(∀P:prod(set(A), set(A)). " +
			"    curve_closed_point(«ambientRing», A₀, A₁, A₀₁, P) ⇒ " +
			"    card({Q:prod(set(A), set(A)) | " +
			"            curve_closed_point(«extended», «chart₀», «chart₁», «chart₀₁», Q) ∧ " +
			"            (A₀ ∩ fst(Q), A₁ ∩ snd(Q)) = P}) = " +
			"    nat_gcd(curve_closed_degree(«ambientRing», k, A₀, A₁, P), r) ∧ " +
			"    (∀Q:prod(set(A), set(A)). " +
			"        curve_closed_point(«extended», «chart₀», «chart₁», «chart₀₁», Q) ∧ " +
			"        (A₀ ∩ fst(Q), A₁ ∩ snd(Q)) = P ⇒ " +
			"        curve_closed_degree(«extended», «constants», «chart₀», «chart₁», Q) * " +
			"        nat_gcd(curve_closed_degree(«ambientRing», k, A₀, A₁, P), r) = " +
			"        curve_closed_degree(«ambientRing», k, A₀, A₁, P))) ∧ " +
			"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m) = " +
			"nat_sum({P:prod(set(A), set(A)) | " +
			"        curve_closed_point(«ambientRing», A₀, A₁, A₀₁, P) ∧ " +
			"        curve_closed_degree(«ambientRing», k, A₀, A₁, P) ∣ m}, " +
			"    curve_closed_degree(«ambientRing», k, A₀, A₁)) ∧ " +
			"curve_extension_count(field_ring(M), «constants», «chart₀», «chart₁», «chart₀₁», m) = " +
			"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, r * m) ∧ " +
			"(∀X:prod(set(A), set(A)). " +
			"    invertible_lattice_pair(«ambientRing», A₀, A₁, A₀₁, X) ⇒ " +
			"    module_dim(restrict_ring(field_ring(M), «constants»), " +
			"        lattice_pair_h0(«extendedVectors», " +
			"            (constant_chart(field_ring(M), «constants», fst(X)), " +
			"                constant_chart(field_ring(M), «constants», snd(X))))) = " +
			"    module_dim(restrict_ring(field_ring(M), k), " +
			"        lattice_pair_h0(restrict_module(regular_module(field_ring(M)), K), X)) ∧ " +
			"    lattice_pair_h1_dim(restrict_ring(field_ring(M), «chart₀₁»), " +
			"        «constants», " +
			"        «extendedVectors», " +
			"        (constant_chart(field_ring(M), «constants», fst(X)), " +
			"            constant_chart(field_ring(M), «constants», snd(X)))) = " +
			"    lattice_pair_h1_dim(restrict_ring(field_ring(M), A₀₁), " +
			"        k, " +
			"        restrict_module(regular_module(field_ring(M)), K), " +
			"        X))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			r, m *Expr[Nat],
			closed, inField, curve, positiveR, positiveM Fact,
		) {
			constants := a.TermAs[Set[A]]("«constants»")
			smooth := a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)
			data := a.Have(
				"K is regular over k in M, and the constants of "+
					"degree r are a subfield of M of finite degree over k",
				"regular_function_field(M, k, K) ∧ "+
					"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite_extension(M, k, «constants»)",
				By(
					closed,
					inField,
					curve,
					positiveR,
					smooth,
					SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t),
					constant_galois.ConstantCompositeData.Read(M).At(K, k, r)))
			a.Show(
				"the clauses are the members",
				By(
					closed,
					inField,
					curve,
					positiveR,
					positiveM,
					smooth,
					data,
					SmoothCurveConstantExtension.Read(M).At(K, k, A0, A1, A01, t, r),
					ConstantChartGenus.Read(M).At(K, k, constants, A0, A1, A01, t),
					At(Read(ClosedPointSplitting, M), K, k, A0, A1, A01, t, r),
					ExtensionCountClosedPoints.Read(M).At(K, k, A0, A1, A01, t, m),
					ExtensionCountBaseChange.Read(M).At(K, k, A0, A1, A01, t, r, m),
					At(Read(ConstantChartLatticeDimensions, M), K, k, constants, A0, A1, A01, t)))
		}),
})}
