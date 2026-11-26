// theorems.go — the trace of Frobenius, and the elliptic Riemann hypothesis
// as the genus-one case of Hasse–Weil, in the reals and in the integers, and
// Hasse's theorem at m = 1.

package elliptic_hasse_weil

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/weil_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// FrobeniusTraceDef — the trace of Frobenius, q + 1 − N: q = card(k), N the rational point count.
var FrobeniusTraceDef = frobeniusTraceDefThm{family.Define(registry.DefEntry{
	Name:  "FrobeniusTraceDef",
	Key:   "prop_d275d50d899fe9f5",
	Const: "elliptic_frobenius_trace",
	Type:  "field_ops(A) → set(A) → A → A → int",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    elliptic_frobenius_trace(R, k, x, y) = card(k) + &1 - elliptic_point_count(R, k, x, y)",
	},
})}

// RiemannHypothesisEllipticReal — for an elliptic curve over a finite field
// with q elements, its function field inside a closed field, the Frobenius
// count N_m lies within 2√(q^m) of q^m + 1 for every m ≥ 1: the Hasse–Weil
// bound read at the datum, up to the sign inside the absolute value.
var RiemannHypothesisEllipticReal = riemannHypothesisEllipticRealThm{family.Add(registry.ProofEntry{
	Name: "RiemannHypothesisEllipticReal",
	Key:  "prop_fb2f02457bc20ad9",
	Reading: "The curve is read as weil_curve.HasseWeilClosedPoints reads it, inside " +
		"an algebraically closed field M holding its function field K. The smooth datum is " +
		"stated in that function field, M restricted to K, where closed_point reads it; " +
		"the field keeps M's operations, so its 2 ≠ 0 and 4a³ + 27b² ≠ 0 are M's. Only m≥1 " +
		"is asserted because the geometric Frobenius count is defined specially at zero.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀x y a b:A. ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_weierstrass(restrict_field(M, K), k, x, y, a, b)",
			"finite(k)",
			"1 ≤ m",
		},
		Conclusion: "|real_of_num(card(k) ^ m) + " +
			"real_of_num(1) - " +
			"real_of_num(elliptic_frobenius_count(restrict_field(M, K), k, x, y, m))| ≤ " +
			"real_of_num(2) * real_sqrt(real_of_num(card(k) ^ m))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			m *Expr[Nat],
			closed, sub, smooth, finite, positive Fact,
		) {
			functionFieldOn := arg.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(sub, field.SubfieldFieldOn.Read(M).At(K)))
			// The datum's charts are read in M, where HasseWeilClosedPoints reads
			// the curve.
			curve := arg.Simplified(
				GroupPremises(
					smooth, finite, closed_point.WeierstrassSmoothFiniteCurve.Read(functionFieldOn).At(k, x, y, a, b)),
				curve_point_count.InAmbient)
			genus := arg.Simplified(
				GroupPremises(
					elliptic_curve.SmoothWeierstrassDatum.Read(smooth),
					elliptic_curve.GenusOne.Read(functionFieldOn).At(k, x, y, a, b)),
				curve_point_count.InAmbient)
			count := arg.Simplified(
				GroupPremises(
					smooth,
					finite,
					closed_point.FrobeniusCountIsWeightedMultiples.Read(functionFieldOn).At(k, x, y, a, b, m)),
				curve_point_count.InAmbient)
			bound := arg.Have(
				"Hasse–Weil at the datum, a smooth curve of genus g = 1 whose closed "+
					"points of degree dividing m > 0, weighted by degree, number N_m",
				"|real_of_num(elliptic_frobenius_count(restrict_field(M, K), k, x, y, m)) - "+
					"real_of_num(card(k) ^ m + 1)| ≤ "+
					"real_of_num(2) * real_sqrt(real_of_num(card(k) ^ m))",
				By(
					closed,
					sub,
					positive,
					curve,
					genus,
					count,
					weil_curve.HasseWeilClosedPoints.Read(M),
					nat_order.OneLessEqIffPos.At(m),
					nat_arith.MulOne.At(arg.TermAs[Nat]("2"))))
			arg.Show(
				"the same deviation with its sign flipped, q^m + 1 read in ℝ as real_of_num(q^m) + real_of_num(1)",
				ByArith(bound, real_construction.OfNumAdd.At(arg.TermAs[Nat]("card(k) ^ m"), arg.TermAs[Nat]("1"))))
		}),
})}

// RiemannHypothesisElliptic — for an elliptic curve over a finite field
// with q elements and every m ≥ 1, the deviation q^m + 1 − N_m of the
// Frobenius count from q^m + 1 has square at most 4q^m, in the integers:
// the real bound |d| ≤ 2√(q^m) squared is d² ≤ 4·(√(q^m))² = 4q^m, and
// the embedding of ℤ in ℝ carries the integer statement to that one.
var RiemannHypothesisElliptic = riemannHypothesisEllipticThm{family.Add(registry.ProofEntry{
	Name: "RiemannHypothesisElliptic",
	Key:  "prop_ab5037e5def892af",
	Reading: "The curve is read inside a closed field M holding its function field K, as " +
		"RiemannHypothesisEllipticReal reads it. Only m≥1 is asserted because the geometric Frobenius " +
		"count is defined specially at zero. The conclusion uses integer subtraction throughout.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀x y a b:A. ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_weierstrass(restrict_field(M, K), k, x, y, a, b)",
			"finite(k)",
			"1 ≤ m",
		},
		Conclusion: "int_pow(card(k) ^ m + " +
			"    int_of_num(1) - " +
			"    int_of_num(elliptic_frobenius_count(restrict_field(M, K), k, x, y, m)), " +
			"    2) ≤ " +
			"int_of_num(4 * card(k) ^ m)",
		Abbrev: Abbrev{
			{Name: "d", Text: "real_of_num(card(k) ^ m) + " +
				"real_of_num(1) - " +
				"real_of_num(elliptic_frobenius_count(restrict_field(M, K), k, x, y, m))"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			m *Expr[Nat],
			datum Fact,
		) {
			// The closer squares a two-sided bound on one atom, so the deviation is
			// named d.
			d := arg.TermAs[Real]("«d»")
			square := arg.Have(
				"squaring the real bound |d| ≤ 2√(q^m) gives d² ≤ 4·√(q^m)², which is 4q^m",
				"«d» ^ 2 ≤ real_of_num(4) * real_of_num(card(k) ^ m)",
				ByArith(
					DenotedAs("d", d),
					datum,
					RiemannHypothesisEllipticReal.Read(M).At(K, k, x, y, a, b, m),
					real_sgn_abs.AbsBounds.At(
						d, arg.TermAs[Real]("real_of_num(2) * real_sqrt(real_of_num(card(k) ^ m))")),
					real_sqrt.SqrtPowTwo.At(arg.TermAs[Real]("real_of_num(card(k) ^ m)"))))
			arg.Show(
				"read in ℝ through the embedding, the integer bound is the real one",
				Simp(int_construction.InReals, Fwd(int_pow.PowBridge)),
				By(square, real_construction.OfNumMul.At(arg.TermAs[Nat]("4"), arg.TermAs[Nat]("card(k) ^ m"))))
		}),
})}

// HasseTheoremReal — for an elliptic curve over a finite field with q
// elements, its rational point count N lies within 2√q of q + 1: the
// Riemann hypothesis at m = 1, where q¹ = q and the Frobenius count N₁ is N,
// and the deviation q + 1 − N has the absolute value of N − q − 1.
var HasseTheoremReal = hasseTheoremRealThm{family.Add(registry.ProofEntry{
	Name:    "HasseTheoremReal",
	Key:     "prop_e0cd9f671f62c121",
	Reading: "The point count is read at the function field K.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_weierstrass(restrict_field(M, K), k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "|real_of_num(elliptic_point_count(restrict_field(M, K), k, x, y)) - " +
			"real_of_num(card(k)) - " +
			"real_of_num(1)| ≤ " +
			"real_of_num(2) * real_sqrt(real_of_num(card(k)))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			closed, sub, smooth, finite Fact,
		) {
			functionFieldOn := arg.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(sub, field.SubfieldFieldOn.Read(M).At(K)))
			rational := arg.Have(
				"the Frobenius count at m = 1 is the rational point count",
				"elliptic_frobenius_count(restrict_field(M, K), k, x, y, 1) = "+
					"elliptic_point_count(restrict_field(M, K), k, x, y)",
				By(smooth, finite, closed_point.FrobeniusCountOne.Read(functionFieldOn).At(k, x, y, a, b)))
			one := arg.TermAs[Nat]("1")
			arg.Show(
				"the Riemann hypothesis at m = 1, its deviation q¹ + "+
					"1 − N₁ read as q + 1 − N, the negative of N − q − 1",
				ByArith(
					GroupPremises(
						closed,
						sub,
						smooth,
						finite,
						nat_order.LessEqRefl.At(one),
						RiemannHypothesisEllipticReal.Read(M).At(K, k, x, y, a, b, one)),
					rational,
					nat_arith.PowOne.At(arg.TermAs[Nat]("card(k)"))))
		}),
})}

// HasseTheorem — for an elliptic curve over a finite field with q elements,
// the trace of Frobenius q + 1 − N, N its rational point count, has square
// at most 4q: the Riemann hypothesis at m = 1, where q¹ = q and the Frobenius
// count N₁ is N, so its deviation q¹ + 1 − N₁ is the trace.
var HasseTheorem = hasseTheoremThm{family.Add(registry.ProofEntry{
	Name: "HasseTheorem",
	Key:  "prop_7dbcb88fc0f206f5",
	Reading: "The curve is read inside a closed field M holding its function field K, " +
		"as RiemannHypothesisElliptic reads it; the trace is read at that function field.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_weierstrass(restrict_field(M, K), k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "int_pow(elliptic_frobenius_trace(restrict_field(M, K), k, x, y), 2) ≤ 4 * card(k)",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			closed, sub, smooth, finite Fact,
		) {
			functionFieldOn := arg.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(sub, field.SubfieldFieldOn.Read(M).At(K)))
			rational := arg.Have(
				"the Frobenius count at m = 1 is the rational point count",
				"elliptic_frobenius_count(restrict_field(M, K), k, x, y, 1) = "+
					"elliptic_point_count(restrict_field(M, K), k, x, y)",
				By(smooth, finite, closed_point.FrobeniusCountOne.Read(functionFieldOn).At(k, x, y, a, b)))
			one := arg.TermAs[Nat]("1")
			arg.Show(
				"the Riemann hypothesis at m = 1, its deviation q¹ + 1 − N₁ read as q + 1 − N, the trace",
				By(
					GroupPremises(
						closed,
						sub,
						smooth,
						finite,
						nat_order.LessEqRefl.At(one),
						RiemannHypothesisElliptic.Read(M).At(K, k, x, y, a, b, one)),
					rational,
					nat_arith.PowOne.At(arg.TermAs[Nat]("card(k)")),
					FrobeniusTraceDef.At(arg.TermAs[FieldOps[A]]("restrict_field(M, K)"), k, x, y)))
		}),
})}
