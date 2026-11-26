// closed_points.go — the Hasse–Weil bound read at the closed points: for a
// smooth curve over a finite field, held by its two charts inside its
// function field K within a closed field M, the closed points of degree
// dividing m, weighted by their degrees, number q^m + 1 up to 2g·√(q^m).

package weil_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// HasseWeilClosedPoints — for a smooth curve over a finite field of q
// elements, its function field K inside a closed field M, the weighted
// count of closed points of degree dividing m is within 2g·√(q^m) of q^m + 1
// for every m > 0. At m > 0 the weighted multiples are by definition
// Σ_{deg P ∣ m} deg P, which ExtensionCountClosedPoints names the m-th
// extension count, so the bound is HasseWeilAllExtensions's.
var HasseWeilClosedPoints = hasseWeilClosedPointsThm{family.Add(registry.ProofEntry{
	Name: "HasseWeilClosedPoints",
	Key:  "prop_d636f4622dac54ff",
	Reading: "The curve is read as HasseWeilAllExtensions reads it: K is its function " +
		"field, a subfield of M, and the closed points, their degrees and the genus are read " +
		"at M's ring restricted to K. That M is algebraically closed is what " +
		"HasseWeilAllExtensions and ExtensionCountClosedPoints ask; the weighted closed-point " +
		"count reads nothing of M beyond that ring. The count at m is weighted_multiples at " +
		"the closed points weighted by degree, zero at m = 0, which the hypothesis 0 < m " +
		"excludes. The bound is stated over the reals; card(k) ^ m + 1 is a numeral cast.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"0 < m",
		},
		Conclusion: "|real_of_num(weighted_multiples(«closedPoints», «pointDegree», m)) - " +
			"real_of_num(card(k) ^ m + 1)| ≤ " +
			"real_of_num(2 * «genus») * real_sqrt(real_of_num(card(k) ^ m))",
		Abbrev: Abbrev{
			{Name: "closedPoints", Text: "curve_closed_point(«functionRing», A₀, A₁, A₀₁)"},
			{Name: "pointDegree", Text: "curve_closed_degree(«functionRing», k, A₀, A₁)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		m *Expr[Nat],
		closed, subK, curve, positive Fact,
	) {
		count := a.Have(
			"m being positive, the degrees of the closed points "+
				"of degree dividing m sum to the m-th extension count",
			"weighted_multiples(«closedPoints», «pointDegree», m) = «count»(m)",
			Simp(Fwd(weighted_divisors.WeightedMultiplesDef), Fwd(set_basic.SetMemberDef)),
			By(
				closed,
				subK,
				curve,
				positive,
				nat_order.PosIffNonzero.At(m),
				curve_point_count.ExtensionCountClosedPoints.Read(M).At(K, k, A0, A1, A01, t, m)))
		a.Show(
			"so the Hasse-Weil bound on the extension count is the bound on the closed points",
			By(
				closed,
				subK,
				curve,
				positive,
				count,
				HasseWeilAllExtensions.Read(M).At(K, k, A0, A1, A01, t, m)))
	}),
})}
