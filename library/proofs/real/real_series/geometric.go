// geometric.go — the geometric series: its partial sums in closed form,
// and its sum; and the powers of t at the squares, whose partial sums
// reach every bound as t → 1⁻.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/registry"
)

// GeometricPartialSum — (1 − x)·(1 + x + … + xⁿ) = 1 − xⁿ⁺¹.
var GeometricPartialSum = geometricPartialSumThm{family.Add(registry.ProofEntry{
	Name: "GeometricPartialSum",
	Key:  "prop_560eab84970e88ff",
	Build: family.Theorem("∀x:real. ∀n:num. "+
		"    (&1 - x) * Σ_{k∈0 .. n} real_pow(x, k) = &1 - real_pow(x, n + 1)",
		func(arg *Argument, x *Expr[Real], n *Expr[Nat]) {
			power := arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(x, k)")
			scaled := arg.TermAs[Fun[Nat, Real]]("λk:num. (&1 - x) * real_pow(x, k)")
			difference := arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(x, k) - real_pow(x, k + 1)")
			zero := arg.TermAs[Nat]("0")
			step := arg.Have(
				"each term times 1 − x is the difference of two consecutive powers "+
					"— stated for 0 ≤ k ≤ n, the guard the congruence of sums reads",
				"∀k:num. 0 ≤ k ∧ k ≤ n ⇒ (&1 - x) * real_pow(x, k) = real_pow(x, k) - real_pow(x, k + 1)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					d.Assume()
					d.Show(
						"xᵏ⁺¹ = xᵏ·x",
						ByArith(real_pow.PowAdd.At(x, k, d.TermAs[Nat]("1")), real_pow.PowOne.At(x)))
				}))
			arg.Do(CalcEq(
				Leg(
					arg.TermAs[Real]("Σ_{k∈0 .. n} (&1 - x) * real_pow(x, k)"),
					"the factor enters the sum",
					By(real_sum.ScalarLeft.At(arg.TermAs[Real]("&1 - x"), power, arg.TermAs[Set[Nat]]("0 .. n")))),
				Leg(
					arg.TermAs[Real]("Σ_{k∈0 .. n} (real_pow(x, k) - real_pow(x, k + 1))"),
					"term by term it is a difference of consecutive powers",
					By(step, real_sum.IntervalCongruence.At(zero, n, scaled, difference))),
				Leg(
					arg.TermAs[Real]("COND(0 ≤ n, real_pow(x, 0) - real_pow(x, n + 1), &0)"),
					"which telescopes",
					By(real_sum.TelescopeDown.At(zero, n, power))),
				FinalLeg(
					"the lower bound 0 is below n, and x⁰ = 1",
					By(Normalized, nat_order.ZeroLessEq.At(n), real_pow.PowExpZeroClause.At(x))),
			))
		}),
})}

// Geometric — the sum of the geometric series. With |x| < 1, 1 − x is
// positive, so the closed form of the partial sums, divided by it,
// gives each as (1 − x)⁻¹·(1 − xⁿ⁺¹). The powers tend to 0, hence so do
// the powers from the second on, and the partial sums tend to
// (1 − x)⁻¹·(1 − 0).
var Geometric = geometricThm{family.Add(registry.ProofEntry{
	Name: "Geometric",
	Key:  "prop_c06052de74033e0f",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"|x| < &1",
		},
		Conclusion: "real_sums(λn:num. real_pow(x, n), real_inv(&1 - x))",
	},
		func(arg *Argument, x *Expr[Real], small Fact) {
			one := arg.TermAs[Real]("&1")
			zero := arg.TermAs[Real]("&0")
			inverse := arg.TermAs[Real]("real_inv(&1 - x)")
			powers := arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x, n)")
			laterPowers := arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x, n + 1)")
			constantOne := arg.TermAs[Fun[Nat, Real]]("λn:num. &1")
			shortfall := arg.TermAs[Fun[Nat, Real]]("λn:num. &1 - real_pow(x, n + 1)")

			positive := arg.Have(
				"|x| < 1 puts x below 1",
				"&0 < &1 - x",
				ByArith(small))
			solved := arg.Have(
				"read 1 − xⁿ⁺¹ back as (1 − x)·Σ xᵏ, and (1 − x)⁻¹·(1 − x) = 1",
				"∀n:num. Σ_{k∈0 .. n} real_pow(x, k) = real_inv(&1 - x) * (&1 - real_pow(x, n + 1))",
				Simp(Rev(GeometricPartialSum)),
				ByArith(positive))
			later := arg.Have(
				"the powers tend to 0, and so do the powers from the second on",
				"(λn:num. real_pow(x, n + 1)) ⟶ &0",
				By(small, real_sequences.PowerTendsToZero.At(x), real_sequences.LimitShift.At(powers, zero)))
			toOne := arg.Have(
				"so 1 − xⁿ⁺¹ tends to 1 − 0 = 1",
				"(λn:num. &1 - real_pow(x, n + 1)) ⟶ &1",
				By(
					later,
					real_sequences.LimitSub.At(constantOne, laterPowers, one, zero),
					real_sequences.LimitConst.At(one),
					real_ring.SubRightZero.At(one)))
			toInverse := arg.Have(
				"and (1 − x)⁻¹ times it tends to (1 − x)⁻¹·1 = (1 − x)⁻¹",
				"(λn:num. real_inv(&1 - x) * (&1 - real_pow(x, n + 1))) ⟶ real_inv(&1 - x)",
				By(toOne, real_sequences.LimitScale.At(shortfall, one, inverse), real_ring.MulRightId.At(inverse)))
			arg.Show(
				"that sequence is the partial sums, so the series sums to (1 − x)⁻¹",
				By(toInverse, solved, RealSumsDef))
		}),
})}

// SquarePowersUnbounded — the sums of t^(m²) over 1 ≤ m ≤ M reach every
// bound for some t in [0, 1) and some M. With M one more than a whole number
// n ≥ B and t = 1 − 1/M³, Bernoulli's inequality makes t^(M²) at least
// 1 − 1/M, and so every term, t being at most 1: the M terms sum to at least
// M − 1 = n.
var SquarePowersUnbounded = squarePowersUnboundedThm{family.Add(registry.ProofEntry{
	Name: "SquarePowersUnbounded",
	Key:  "prop_d278247c418342e5",
	Reading: "The series Σ_{m≥1} t^(m²) is unbounded as t → 1⁻; the " +
		"statement says so through its partial sums, with no limit in t taken.",
	Build: family.Theorem("∀B:real. ∃t:real. ∃M:num. &0 ≤ t ∧ t < &1 ∧ B ≤ Σ_{m∈1 .. M} t ^ (m * m)",
		func(a *Argument, B *Expr[Real]) {
			_, above := a.UnpackAs[Nat](real_archimedean.ExistsNumAbove.At(B), "n")
			M, mDef := a.LetAs[Nat]("M", "n + 1")
			_, deltaDef := a.LetAs[Real]("δ", "&1 / (&M * &M * &M)")
			t, tDef := a.LetAs[Real]("t", "&1 - δ")
			a.Take(t)
			a.Take(M)
			small := a.Have(
				"M is at least 1, so δ = 1/M³ lies in (0, 1]",
				"&0 < δ ∧ δ ≤ &1",
				ByArith(mDef, deltaDef))
			inUnit := a.Have(
				"so t = 1 − δ lies in [0, 1)",
				"&0 ≤ t ∧ t < &1",
				ByArith(tDef, small))
			nearOne := a.Have(
				"Bernoulli's inequality at −δ and the exponent M², with t written as 1 + (−δ) and M²·δ = 1/M",
				"&1 - &1 / &M ≤ t ^ (M * M)",
				Simp(Fwd(tDef), Fwd(real_ring.RealSubDef)),
				ByArith(mDef, deltaDef, small, real_pow.Bernoulli.At(a.TermAs[Real]("-δ"), a.TermAs[Nat]("M * M"))))
			termwise := a.Have(
				"every term up to M is at least 1 − 1/M too",
				"∀m:num. 1 ≤ m ∧ m ≤ M ⇒ &1 - &1 / &M ≤ t ^ (m * m)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					inRange := b.Assume()
					b.Show(
						"t^(m²) is at least t^(M²), the base lying in [0, 1] and m² being at most M²",
						ByArith(
							inUnit,
							nearOne,
							inRange,
							real_pow.PowMonoExpBelowOne.At(t, b.TermAs[Nat]("m * m"), b.TermAs[Nat]("M * M"))))
				}))
			bound := a.CalcLeibniz(real_order_ring.OrderCalc(a.Ctx()), a.TermAs[Real]("&n"),
				EqLeg(
					a.TermAs[Real]("Σ_{m∈1 .. M} (&1 - &1 / &M)"),
					"M terms equal to 1 − 1/M sum to M − 1, which is n",
					ByArith(mDef, real_sum.IntervalConst.At(a.TermAs[Real]("&1 - &1 / &M"), M, a.TermAs[Nat]("1")))),
				LeLeg(
					a.TermAs[Real]("Σ_{m∈1 .. M} t ^ (m * m)"),
					"the sums compare term by term",
					By(termwise, real_sum.IntervalMonotone)))
			a.Show(
				"t and M are the witnesses: B is at most n, and n at most the sum",
				ByArith(inUnit, above, bound))
		}),
})}
