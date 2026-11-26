// estimates.go — the bounds on the pieces of Newman's integrand: the
// kernel 1/z + z/R² on the circle |z| = R; the tail of a Dirichlet series
// with coefficients bounded by B to the right of w and its partial sum to
// the left; and from them the integrals over the right and the left
// half-circle, where the kernel tames the two series bounds, and over the
// three sides of the rectangle, where N^z is small.

package tauberian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// KernelOnCircle — on the circle |z| = R, Newman's factor 1/z + z/R² has
// modulus 2|Re z|/R².
var KernelOnCircle = kernelOnCircleThm{family.Add(registry.ProofEntry{
	Name: "KernelOnCircle",
	Key:  "prop_988f9f480b0e78b5",
	Build: family.Theorem(Statement{
		Binders: "∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"&0 < R",
			"|z| = R",
		},
		Conclusion: "|«kernel»(R, z)| = &2 * |re(z)| / (R * R)",
	}, func(a *Argument, R *Expr[Real], z *Expr[Complex], onCircle Fact) {
		square := a.TermAs[Real]("R * R")
		denominator := a.TermAs[Complex]("complex_of_real(R * R)")
		circleProduct := a.Have(
			"z times its conjugate is the square of the radius",
			"z * conj(z) = complex_of_real(R * R)",
			By(onCircle, complex_abs.AbsSquare.At(z), complex_field.MulConj.At(z)))
		nonzero := a.Have(
			"the radius has nonzero square",
			"complex_of_real(R * R) ≠ complex_of_real(&0)",
			ByArith(onCircle, complex_field.OfRealInjective.At(square, a.TermAs[Real]("&0"))))
		inverseProduct := a.Have(
			"z times the conjugate divided by the radius squared is 1",
			"z * (conj(z) / complex_of_real(R * R)) = complex_of_real(&1)",
			Simp(Fwd(complex_field.ComplexDivDef), Fwd(comm_monoid.Assoc.Read(complex_field.MulMonoid))),
			circleProduct.Rw(),
			By(nonzero, field.MulRightInverse.Read(complex_field.Field).At(denominator)))
		inverse := a.Have(
			"uniqueness of the inverse gives conjugate divided by the radius squared",
			"complex_inv(z) = conj(z) / complex_of_real(R * R)",
			By(
				inverseProduct,
				field.InvRightUnique.Read(complex_field.Field).At(
					z, a.TermAs[Complex]("conj(z) / complex_of_real(R * R)"))))
		kernel := a.Have(
			"both terms of the kernel have the same denominator",
			"«kernel»(R, z) = (conj(z) + z) / complex_of_real(R * R)",
			Simp(Fwd(complex_field.ComplexDivDef)),
			ByArith(a.Simplified(inverse, Fwd(complex_field.ComplexDivDef))))
		realNumerator := a.Have(
			"adding the conjugate doubles the real part",
			"conj(z) + z = complex_of_real(&2 * re(z))",
			Simp(
				Fwd(complex_field.ComplexEq),
				Fwd(complex_field.PartsAdd),
				Fwd(complex_field.PartsConj),
				Fwd(complex_field.PartsOfReal)),
			ByArith())
		doubled := a.TermAs[Real]("&2 * re(z)")
		moduli := a.Have(
			"take the absolute values of the embedded numerator and denominator",
			"|complex_of_real(&2 * re(z))| = &2 * |re(z)| ∧ |complex_of_real(R * R)| = R * R",
			ByArith(
				onCircle,
				complex_abs.AbsOfReal.At(doubled),
				complex_abs.AbsOfReal.At(square),
				real_sgn_abs.AbsMul.At(a.TermAs[Real]("&2"), a.TermAs[Real]("re(z)"))))
		a.Show(
			"the modulus of the quotient is the quotient of the moduli",
			By(
				realNumerator,
				kernel,
				moduli,
				complex_abs.AbsDiv.At(
					a.TermAs[Complex]("complex_of_real(&2 * re(z))"), denominator)))
	}),
	Reading: "The factor vanishes at ±iR, the two points where the half-circle " +
		"meets the line Re z = 0 and the bounds on the series degenerate.",
})}

// KernelContinuousAt states the continuity of Newman's factor away from zero.
var KernelContinuousAt = kernelContinuousAtThm{family.Add(registry.ProofEntry{
	Name: "KernelContinuousAt",
	Key:  "prop_49fdc7d786c0c486",
	Build: family.Theorem(Statement{
		Binders:    "∀R:real. ∀z:complex.",
		Hypotheses: []string{"z ≠ &0"},
		Conclusion: "complex_continuous_at(λu:complex. «kernel»(R, u), z)",
	}, func(a *Argument, R *Expr[Real], z *Expr[Complex], nonzero Fact) {
		id := a.TermAs[Fun[Complex, Complex]]("λu:complex. u")
		inverse := a.TermAs[Fun[Complex, Complex]]("λu:complex. complex_inv(u)")
		scale := a.TermAs[Complex]("complex_inv(&(R * R))")
		scalar := a.TermAs[Fun[Complex, Complex]]("λu:complex. complex_inv(&(R * R))")
		linear := a.TermAs[Fun[Complex, Complex]]("λu:complex. u * complex_inv(&(R * R))")
		a.Show(
			"add the reciprocal to a linear function",
			Simp(Fwd(complex_field.ComplexDivDef)),
			By(
				nonzero,
				complex_topology.ContinuousAtId.At(z),
				complex_topology.ContinuousAtInv.At(id, z),
				complex_topology.ContinuousAtConst.At(z, scale),
				complex_topology.ContinuousAtMul.At(id, scalar, z),
				complex_topology.ContinuousAtAdd.At(inverse, linear, z)))
	}),
})}

// ShiftedTermBound — shifting by w with Re w ≥ 1 gives at least one
// additional inverse power in the bound on a Dirichlet term.
var ShiftedTermBound = shiftedTermBoundThm{family.Add(registry.ProofEntry{
	Name: "ShiftedTermBound",
	Key:  "prop_b0a2f7ad85e13c5b",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → complex). ∀B:real. ∀z w:complex. ∀n:num.",
		Hypotheses: []string{"|a(n)| ≤ B", "&1 ≤ re(w)", "0 < n"},
		Conclusion: "|a(n) * complex_cpow(&n, -(z + w))| ≤ B * real_rpow(&n, -re(z) - &1)",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		B *Expr[Real],
		z, w *Expr[Complex],
		n *Expr[Nat],
		bounded, shift, positive Fact,
	) {
		x := arg.TermAs[Real]("&n")
		base := arg.Have(
			"the positive integer base is at least one",
			"&0 < real_of_num(n) ∧ &1 ≤ real_of_num(n)",
			ByArith(
				positive,
				real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), n),
				real_construction.OfNumLessEq.At(arg.TermAs[Nat]("1"), n)))
		power := arg.TermAs[Complex]("complex_cpow(&n, -(z + w))")
		exponent := arg.Have(
			"the bound's exponent is −(re z + 1)",
			"-re(z) - &1 = -(re(z) + &1)",
			ByArith())
		size := arg.Have(
			"the real part of w lowers the exponent by at least one, so at "+
				"the base n ≥ 1 the power is at most n^(−re z − 1) in modulus",
			"|complex_cpow(&n, -(z + w))| ≤ real_rpow(&n, -re(z) - &1)",
			exponent.Rw(),
			ByArith(
				shift,
				base,
				complex_field.PartsAdd.At(z, w),
				complex_cpow.AbsCpowNegLessEq.At(x, arg.TermAs[Real]("re(z) + &1"), arg.TermAs[Complex]("z + w"))))
		arg.Show(
			"combine the coefficient bound and the bound on the power",
			ByArith(
				bounded,
				size,
				complex_abs.AbsMul.At(a.Apply(n), power),
				complex_abs.AbsNonneg.At(a.Apply(n))))
	}),
})}

// TailBoundRight — to the right of w, with Re w ≥ 1, a Dirichlet series
// with coefficients bounded by B is within B·N^(−Re z)/Re z of its N-th
// partial sum at z + w.
var TailBoundRight = tailBoundRightThm{family.Add(registry.ProofEntry{
	Name: "TailBoundRight",
	Key:  "prop_187a1fec748e7e84",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀z w v:complex. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 ≤ re(w)",
			"&0 < re(z)",
			"0 < N",
			"dirichlet_sums(a, z + w, v)",
		},
		Conclusion: "|v - «partial»(a, N, z + w)| ≤ B * real_rpow(&N, -re(z)) / re(z)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			B *Expr[Real],
			z, w, v *Expr[Complex],
			N *Expr[Nat],
			given Fact,
		) {
			zero := arg.TermAs[Nat]("0")
			one := arg.TermAs[Nat]("1")
			previous := arg.TermAs[Nat]("N - 1")
			shift := arg.TermAs[Nat]("N + 1")
			x := arg.TermAs[Real]("re(z)")
			sigma := arg.TermAs[Real]("re(z) + &1")
			cap := arg.TermAs[Real]("real_rpow(&N, -re(z)) / re(z)")

			terms := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * complex_cpow(&n, -(z + w))")
			series := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 1) * complex_cpow(&(n + 1), -(z + w))")
			tail := arg.TermAs[Fun[Nat, Complex]](
				"λn:num. a(n + (N - 1) + 1 + 1) * complex_cpow(&(n + (N - 1) + 1 + 1), -(z + w))")
			remainder := arg.TermAs[Complex]("v - «partial»(a, N, z + w)")
			sums := arg.Have(
				"the Dirichlet series is indexed from one",
				"complex_sums(λn:num. a(n + 1) * complex_cpow(&(n + 1), -(z + w)), v)",
				By(given, dirichlet_series.DirichletSumsDef.At(a, arg.TermAs[Complex]("z + w"), v)))
			head := arg.Have(
				"the first N terms are the stated partial sum",
				"Σ_{k∈0 .. N - 1} a(k + 1) * complex_cpow(&(k + 1), -(z + w)) = «partial»(a, N, z + w)",
				ByArith(
					given,
					monoidal.Shift.Read(comm_ring.MonoidalAdd.Read(complex_field.CommRing)).At(
						zero, previous, one, terms)))
			tailSums := arg.Have(
				"removing the head gives the complex remainder",
				"complex_sums(λn:num. a(n + (N - 1) + 1 + 1) * complex_cpow(&(n + (N - 1) + 1 + 1), -(z + w)), "+
					"    v - «partial»(a, N, z + w))",
				By(head, sums, complex_series.SumsOffset.At(series, v, previous)))

			exponents := arg.Have(
				"the two spellings of the exponent agree",
				"-(re(z) + &1) = -re(z) - &1",
				ByArith())
			aboveOne := arg.Have(
				"the majorant's exponent exceeds one",
				"&1 < re(z) + &1",
				ByArith(given))
			L, rpowSeries := arg.ObtainAs[Real](
				"the real power majorant has a convergent series",
				"∃L:real. real_sums(λn:num. real_rpow(&(n + 1), -(re(z) + &1)), L)",
				By(aboveOne, real_rpow.RpowSeriesConverges.At(sigma)),
				Named("L"))
			powerTail := arg.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1)")
			powerRemainder := arg.TermAs[Real]("L - Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1)")
			powers := arg.Have(
				"remove the real power terms through N",
				"real_sums(λn:num. real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1), "+
					"    L - Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1))",
				exponents.RwRev(),
				By(
					rpowSeries,
					real_series.SumsOffset.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + 1), -(re(z) + &1))"), L, previous)))
			indices := arg.Have(
				"the first remaining index is N plus one",
				"(λn:num. real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1)) = "+
					"(λn:num. real_rpow(&(n + (N + 1)), -re(z) - &1))",
				Funext(),
				StripQuant(),
				ByArith(given))
			partials := arg.TermAs[Fun[Nat, Real]](
				"λM:num. Σ_{k∈0 .. M} real_rpow(&(k + (N - 1) + 1 + 1), -re(z) - &1)")
			finiteBounds := arg.Have(
				"every partial sum of the majorant satisfies the real power tail estimate",
				"∀M:num. "+
					"    Σ_{k∈0 .. M} real_rpow(&(k + (N - 1) + 1 + 1), -re(z) - &1) ≤ real_rpow(&N, -re(z)) / re(z)",
				Derive(func(b *Argument) {
					M := b.FixAs[Nat]("M")
					b.Show(
						"shift the sum to start at N plus one",
						indices.Rw(),
						ByArith(
							given,
							real_sum.Shift.At(zero, M, shift, b.TermAs[Fun[Nat, Real]]("λk:num. real_rpow(&k, -re(z) - &1)")),
							real_rpow.RpowTailSumBound.At(x, N, b.TermAs[Nat]("M + (N + 1)"))))
				}))
			limitBound := arg.Have(
				"the same bound holds at the real series limit",
				"L - (Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1)) ≤ real_rpow(&N, -re(z)) / re(z)",
				By(
					finiteBounds,
					powers,
					real_series.RealSumsDef.At(powerTail, powerRemainder),
					real_sequences.LimitLessEqBound.At(partials, powerRemainder, cap)))
			pointwise := arg.Have(
				"the shifted coefficient bound holds at each tail index",
				"∀n:num. "+
					"    |a(n + (N - 1) + 1 + 1) * complex_cpow(&(n + (N - 1) + 1 + 1), -(z + w))| ≤ "+
					"    B * real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"each tail index is positive",
						ByArith(given, ShiftedTermBound.At(a, B, z, w, b.TermAs[Nat]("n + (N - 1) + 1 + 1"))))
				}))
			scaled := arg.Have(
				"scale the real series by the coefficient bound",
				"real_sums(λn:num. B * real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1), "+
					"    B * (L - Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1)))",
				By(powers, real_series.SumsScale.At(powerTail, powerRemainder, B)))
			compared := arg.Have(
				"comparison bounds the modulus of the complex remainder",
				"|v - «partial»(a, N, z + w)| ≤ B * (L - Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1))",
				By(
					pointwise,
					tailSums,
					scaled,
					complex_series.ComparisonBound.At(
						tail, arg.TermAs[Fun[Nat, Real]]("λn:num. B * real_rpow(&(n + (N - 1) + 1 + 1), -re(z) - &1)"),
						remainder, arg.TermAs[Real]("B * (L - Σ_{k∈0 .. N - 1} real_rpow(&(k + 1), -re(z) - &1))"))))
			nonnegative := arg.Have(
				"the coefficient bound is nonnegative",
				"&0 ≤ B",
				ByArith(given, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("a(0)"))))
			arg.Show(
				"use the real tail estimate at the limit",
				ByArith(compared, nonnegative, limitBound))
		}),
})}

// HeadBoundLeft — to the left of w, with Re w ≥ 1, the N-th partial sum
// at z + w is at most B·N^(−Re z)·(1/N + 1/|Re z|).
var HeadBoundLeft = headBoundLeftThm{family.Add(registry.ProofEntry{
	Name: "HeadBoundLeft",
	Key:  "prop_69177f1fce5f7adf",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀z w:complex. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 ≤ re(w)",
			"re(z) < &0",
			"0 < N",
		},
		Conclusion: "|«partial»(a, N, z + w)| ≤ B * real_rpow(&N, -re(z)) * (&1 / &N + &1 / (-re(z)))",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], B *Expr[Real],
			z, w *Expr[Complex], N *Expr[Nat], given Fact) {
			one := arg.TermAs[Nat]("1")
			segment := arg.TermAs[Set[Nat]]("1 .. N")
			terms := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * complex_cpow(&n, -(z + w))")
			moduli := arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n) * complex_cpow(&n, -(z + w))|")
			powers := arg.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&n, -re(z) - &1)")
			majorant := arg.TermAs[Fun[Nat, Real]]("λn:num. B * real_rpow(&n, -re(z) - &1)")
			pointwise := arg.Have(
				"each positive index has the shifted Dirichlet term bound",
				"∀n:num. n ∈ 1 .. N ⇒ |a(n) * complex_cpow(&n, -(z + w))| ≤ B * real_rpow(&n, -re(z) - &1)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					inSegment := b.Assume()
					b.Show(
						"an index in the head is positive",
						ByArith(inSegment, given, ShiftedTermBound.At(a, B, z, w, n), num_segment.Membership.At(n, one, N)))
				}))
			dominated := arg.Have(
				"the finite sum of moduli is bounded by the sum of the majorant",
				"|«partial»(a, N, z + w)| ≤ B * Σ_{n∈1 .. N} real_rpow(&n, -re(z) - &1)",
				ByArith(
					pointwise,
					complex_series.AbsSumLessEq.Inst[Nat]().At(segment, terms),
					num_segment.Finite.At(one, N),
					real_sum.Monotone.Inst[Nat]().At(segment, moduli, majorant),
					real_sum.ScalarLeft.Inst[Nat]().At(B, powers, segment)))
			nonnegative := arg.Have(
				"the coefficient bound is nonnegative",
				"&0 ≤ B",
				ByArith(given, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("a(0)"))))
			arg.Show(
				"scale the real power sum estimate by the coefficient bound",
				ByArith(
					dominated,
					nonnegative,
					given,
					real_rpow.RpowHeadSumBound.At(arg.TermAs[Real]("-re(z)"), N)))
		}),
})}

// WeightedKernelArcBound — on an arc of the circle |z| = R, the integral of
// G(z)·N^z·(1/z + z/R²) is at most 2K(β − α)/R when G is continuous on the
// arc and |G(z)| ≤ K·N^(−Re z)/|Re z| off the imaginary axis: on the circle
// the kernel has modulus 2|Re z|/R², which cancels |Re z| against the bound
// and vanishes on the axis, where the bound says nothing; N^z has modulus
// N^(Re z), and the arc has length R(β − α).
var WeightedKernelArcBound = weightedKernelArcBoundThm{family.Add(registry.ProofEntry{
	Name: "WeightedKernelArcBound",
	Key:  "prop_da0797fc2a3cb104",
	Build: family.Theorem(Statement{
		Binders: "∀G:(complex → complex). ∀R K α β:real. ∀N:num.",
		Hypotheses: []string{
			"&0 < R",
			"&0 ≤ K",
			"0 < N",
			"α ≤ β",
			"∀t:real. " +
				"    α ≤ t ∧ t ≤ β ⇒ " +
				"    complex_continuous_at(G, circle_path(&0, R, t)) ∧ " +
				"    (re(circle_path(&0, R, t)) ≠ &0 ⇒ " +
				"        |G(circle_path(&0, R, t))| ≤ " +
				"        K * real_rpow(&N, -re(circle_path(&0, R, t))) / |re(circle_path(&0, R, t))|)",
		},
		Conclusion: "|«arcInt»(«weightedKernel»(G, R, N), R, α, β)| ≤ &2 * K * (β - α) / R",
	}, func(
		arg *Argument,
		G *Arrow[Complex, Complex],
		R, K, α, β *Expr[Real],
		N *Expr[Nat],
		positiveR, nonnegativeK, positiveN, ordered, onArc Fact,
	) {
		base := arg.TermAs[Real]("&N")
		U := arg.TermAs[Set[Complex]]("𝕌")
		scale := arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&N, z)")
		factor := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «kernel»(R, z)")
		weighted := arg.TermAs[Fun[Complex, Complex]]("λz:complex. G(z) * complex_cpow(&N, z)")
		integrand := arg.TermAs[Fun[Complex, Complex]]("«weightedKernel»(G, R, N)")
		bound := arg.TermAs[Real]("&2 * K / (R * R)")
		basePos := arg.Have(
			"the positive integer gives a positive base",
			"&0 < real_of_num(N)",
			By(positiveN, real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), N)))
		holScale := arg.Have(
			"the power is entire in the exponent",
			"holomorphic_on(𝕌, λz:complex. complex_cpow(&N, z))",
			By(basePos, complex_cpow.CpowHolomorphicExponent.At(base)))
		arc := arg.Have(
			"the integrand is continuous on the closed arc and bounded there by 2K/R²",
			Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"α ≤ t",
					"t ≤ β",
				},
				Conclusion: "complex_continuous_at(«weightedKernel»(G, R, N), circle_path(&0, R, t)) ∧ " +
					"|«weightedKernel»(G, R, N, circle_path(&0, R, t))| ≤ &2 * K / (R * R)",
			},
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				within := b.Assume()
				z, circle := b.LetAs[Complex]("z", "circle_path(&0, R, t)")
				local := b.Have(
					"G is continuous at the arc point z and obeys its bound off the imaginary axis",
					"complex_continuous_at(G, z) ∧ (re(z) ≠ &0 ⇒ |G(z)| ≤ K * real_rpow(&N, -re(z)) / |re(z)|)",
					circle.Rw(),
					By(within, onArc.At(t)))
				radius := b.Have(
					"z lies on the circle of radius R",
					"|z| = R",
					circle.Rw(),
					By(positiveR, path_integral.CirclePathModulus.At(R, t)))
				nonzero := b.Have(
					"the positive radius keeps z away from zero",
					"z ≠ &0",
					ByArith(radius, positiveR, complex_abs.AbsEqZero.At(z)))
				continuousAt := b.Have(
					"G, the power and the kernel are continuous at z",
					"complex_continuous_at(«weightedKernel»(G, R, N), z)",
					By(
						local,
						nonzero,
						holScale,
						set_basic.InUniv.At(z),
						KernelContinuousAt.At(R, z),
						complex_derivative.HolomorphicOnContinuousAt.At(U, scale, z),
						complex_topology.ContinuousAtMul.At(G, scale, z),
						complex_topology.ContinuousAtMul.At(weighted, factor, z)))
				power := b.TermAs[Complex]("complex_cpow(&N, z)")
				modulus := b.Have(
					"the modulus is the product of the moduli, the kernel's being 2|re z|/R² on the circle",
					"|«weightedKernel»(G, R, N, z)| = |G(z)| * real_rpow(&N, re(z)) * (&2 * |re(z)| / (R * R))",
					By(
						positiveR,
						basePos,
						radius,
						KernelOnCircle.At(R, z),
						complex_cpow.AbsCpow.At(base, z),
						complex_abs.AbsMul.At(G.Apply(z), power),
						complex_abs.AbsMul.At(
							b.TermAs[Complex]("G(z) * complex_cpow(&N, z)"), b.TermAs[Complex]("«kernel»(R, z)"))))
				bounded := b.Have(
					"the integrand is at most 2K/R² at z",
					"|«weightedKernel»(G, R, N, z)| ≤ &2 * K / (R * R)",
					Derive(func(c *Argument) {
						offAxis := c.Unless(
							c.TermAs[Bool]("re(z) = &0"),
							"on the imaginary axis the kernel vanishes",
							Given(func(d *Argument, onAxis Fact) {
								d.Show(
									"so does the integrand",
									modulus.Rw(),
									onAxis.Rw(),
									ByArith(positiveR, nonnegativeK, real_sgn_abs.AbsOfZero))
							}))
						y := c.TermAs[Real]("re(z)")
						size := c.Have(
							"off the axis |re z| is positive",
							"&0 < |re(z)|",
							By(offAxis, real_sgn_abs.AbsPosIffNonzero.At(y)))
						zeroExponent := c.Have(
							"the opposite exponents add to zero",
							"-re(z) + re(z) = &0",
							ByArith())
						productLaw := c.Simplified(
							GroupPremises(basePos, real_rpow.RpowAdd.At(base, c.TermAs[Real]("-re(z)"), y)),
							Fwd(zeroExponent))
						powers := c.Have(
							"the two real powers are reciprocal",
							"real_rpow(&N, -re(z)) * real_rpow(&N, re(z)) = &1",
							By(basePos, productLaw, real_rpow.RpowZeroExponent.At(base)))
						multiplied := c.Have(
							"multiply the bound on G by the nonnegative power N^(re z)",
							"|G(z)| * real_rpow(&N, re(z)) ≤ (K * real_rpow(&N, -re(z)) / |re(z)|) * real_rpow(&N, re(z))",
							By(
								local,
								offAxis,
								real_rpow.RpowNonneg.At(base, y),
								real_order_ring.LessEqMulRight.At(
									c.TermAs[Real]("|G(z)|"),
									c.TermAs[Real]("K * real_rpow(&N, -re(z)) / |re(z)|"),
									c.TermAs[Real]("real_rpow(&N, re(z))"))))
						regroup := c.Have(
							"group the two powers together",
							"(K * real_rpow(&N, -re(z)) / |re(z)|) * real_rpow(&N, re(z)) = "+
								"(K / |re(z)|) * (real_rpow(&N, -re(z)) * real_rpow(&N, re(z)))",
							ByArith())
						weightedBound := c.Have(
							"the two powers cancel",
							"|G(z)| * real_rpow(&N, re(z)) ≤ K / |re(z)|",
							ByArith(c.Simplified(multiplied, Fwd(regroup), Fwd(powers))))
						kernelFactor := c.TermAs[Real]("&2 * |re(z)| / (R * R)")
						kernelNonneg := c.Have(
							"the modulus of the kernel is nonnegative",
							"&0 ≤ &2 * |re(z)| / (R * R)",
							ByArith(size, positiveR))
						c.Show(
							"|re z| cancels between the bound and the kernel",
							modulus.Rw(),
							real_order_ring.OrderCalc(c.Ctx()).CalcLeibniz(
								c.TermAs[Real]("|G(z)| * real_rpow(&N, re(z)) * (&2 * |re(z)| / (R * R))"),
								LeLeg(
									c.TermAs[Real]("(K / |re(z)|) * (&2 * |re(z)| / (R * R))"),
									"the bound on |G(z)|·N^(re z) times the kernel's modulus",
									By(
										weightedBound,
										kernelNonneg,
										real_order_ring.LessEqMulRight.At(
											c.TermAs[Real]("|G(z)| * real_rpow(&N, re(z))"),
											c.TermAs[Real]("K / |re(z)|"),
											kernelFactor))),
								EqLeg(
									bound,
									"|re z| cancels",
									ByArith(size, positiveR))))
					}))
				b.Show(
					"the arc point is continuous and bounded",
					By(continuousAt, bounded))
			}))
		estimate := arg.Have(
			"multiply the uniform bound by the length R(β − α) of the arc",
			"|«arcInt»(«weightedKernel»(G, R, N), R, α, β)| ≤ (&2 * K / (R * R)) * (R * (β - α))",
			By(arc, positiveR, ordered, path_integral.ArcIntegralBound.At(integrand, R, α, β, bound)))
		arg.Show(
			"one factor R cancels",
			ByArith(estimate, positiveR))
	}),
})}

// RightArcInBox — a point of the right half of the circle |z| = R lies in
// the box 0 ≤ Re z ≤ R, |Im z| ≤ R, and is not 0.
var RightArcInBox = rightArcInBoxThm{family.Add(registry.ProofEntry{
	Name: "RightArcInBox",
	Key:  "prop_cd82fb5f428f97e3",
	Build: family.Theorem(Statement{
		Binders:    "∀R t:real.",
		Hypotheses: []string{"&0 < R", "-(pi / &2) ≤ t", "t ≤ pi / &2"},
		Conclusion: "&0 ≤ re(circle_path(&0, R, t)) ∧ " +
			"re(circle_path(&0, R, t)) ≤ R ∧ " +
			"|im(circle_path(&0, R, t))| ≤ R ∧ " +
			"circle_path(&0, R, t) ≠ &0",
	}, func(arg *Argument, R, t *Expr[Real], positive, lower, upper Fact) {
		z, pointDef := arg.LetAs[Complex]("z", "circle_path(&0, R, t)")
		realPart := arg.Have(
			"the circle's real part is R times cosine",
			"re(z) = R * cos(t)",
			Simp(
				Fwd(pointDef),
				Fwd(path_integral.CirclePathDef),
				Fwd(complex_exp.EulerOfReal),
				Fwd(complex_field.PartsAdd),
				Fwd(complex_field.PartsMul),
				Fwd(complex_field.PartsOfReal),
				Fwd(complex_field.PartsI)),
			ByArith())
		size := arg.Have(
			"the point has modulus R",
			"|z| = R",
			Simp(Fwd(pointDef)),
			By(positive, path_integral.CirclePathModulus.At(R, t)))
		cosNonnegative := arg.Have(
			"cosine is nonnegative on the right half-circle",
			"&0 ≤ cos(t)",
			By(lower, upper, real_trigonometry.CosNonnegHalfPi.At(t)))
		arg.Show(
			"the positive modulus bounds the parts and excludes zero",
			ByArith(
				positive,
				realPart,
				size,
				cosNonnegative,
				complex_abs.ReLessEqAbs.At(z),
				complex_abs.ImLessEqAbs.At(z),
				complex_abs.AbsEqZero.At(z)))
	}),
})}

// RightArcBound — over the right half-circle, the integral of
// (F − partial sum)·N^z·kernel is at most 2πB/R: the tail of the series
// to the right of w is at most B·N^(−Re z)/Re z, and WeightedKernelArcBound
// turns that into 2B·π/R.
var RightArcBound = rightArcBoundThm{family.Add(registry.ProofEntry{
	Name: "RightArcBound",
	Key:  "prop_defda5741d13eb7a",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B R:real. ∀F:(complex → complex). ∀w:complex. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 ≤ re(w)",
			"&0 < R",
			"0 < N",
			"∀z:complex. |z| = R ∧ &0 < re(z) ⇒ dirichlet_sums(a, z + w, F(z + w))",
			"∀z:complex. |z| = R ∧ &0 ≤ re(z) ⇒ complex_continuous_at(F, z + w)",
		},
		Conclusion: "|«arcInt»(«weightedKernel»(λz:complex. F(z + w) - «partial»(a, N, z + w), R, N), R, -(pi / &2), pi / &2)| ≤ " +
			"&2 * pi * B / R",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			B, R *Expr[Real],
			F *Arrow[Complex, Complex],
			w *Expr[Complex],
			N *Expr[Nat],
			coefficientBound, shift, positiveR, positiveN, sums, continuity Fact,
		) {
			α := arg.TermAs[Real]("-(pi / &2)")
			β := arg.TermAs[Real]("pi / &2")
			U := arg.TermAs[Set[Complex]]("𝕌")
			id := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z")
			translate := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z + w")
			partial := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «partial»(a, N, z)")
			difference := arg.TermAs[Fun[Complex, Complex]]("λz:complex. F(z + w) - «partial»(a, N, z + w)")
			nonnegative := arg.Have(
				"the bound on the coefficients is nonnegative",
				"&0 ≤ B",
				ByArith(
					coefficientBound.At(arg.TermAs[Nat]("0")),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("a(0)"))))
			continuousTranslate := arg.Have(
				"translation is continuous everywhere",
				"∀z:complex. complex_continuous_at(λx:complex. x + w, z)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					b.Show(
						"add a constant to the identity",
						By(
							complex_topology.ContinuousAtId.At(z),
							complex_topology.ContinuousAtConst.At(z, w),
							complex_topology.ContinuousAtAdd.At(id, b.TermAs[Fun[Complex, Complex]]("λx:complex. w"), z)))
				}))
			arc := arg.Have(
				"on the closed right arc the difference is continuous "+
					"and, off the imaginary axis, at most B·N^(−re z)/|re z|",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"-(pi / &2) ≤ t",
						"t ≤ pi / &2",
					},
					Conclusion: "complex_continuous_at(λx:complex. F(x + w) - «partial»(a, N, x + w), " +
						"    circle_path(&0, R, t)) ∧ " +
						"(re(circle_path(&0, R, t)) ≠ &0 ⇒ " +
						"    |F(circle_path(&0, R, t) + w) - «partial»(a, N, circle_path(&0, R, t) + w)| ≤ " +
						"    B * real_rpow(&N, -re(circle_path(&0, R, t))) / |re(circle_path(&0, R, t))|)",
				},
				Derive(func(b *Argument) {
					t := b.FixAs[Real]("t")
					inInterval := b.Assume()
					z, circle := b.LetAs[Complex]("z", "circle_path(&0, R, t)")
					box := b.Have(
						"z lies on the circle, to the right of the imaginary axis",
						"|z| = R ∧ &0 ≤ re(z)",
						circle.Rw(),
						By(positiveR, inInterval, path_integral.CirclePathModulus.At(R, t), RightArcInBox.At(R, t)))
					shifted := b.TermAs[Complex]("z + w")
					fContin := b.Have(
						"the translated F is continuous at z",
						"complex_continuous_at(F ∘ (λx:complex. x + w), z)",
						By(
							box,
							continuity.At(z),
							continuousTranslate.At(z),
							complex_topology.ContinuousAtCompose.At(F, translate, z)))
					pContin := b.Have(
						"the translated partial sum, an entire function, is continuous at z",
						"complex_continuous_at((λx:complex. «partial»(a, N, x)) ∘ (λx:complex. x + w), z)",
						By(
							dirichlet_series.PartialSumHolomorphic.At(a, N),
							set_basic.InUniv.At(shifted),
							complex_derivative.HolomorphicOnContinuousAt.At(U, partial, shifted),
							continuousTranslate.At(z),
							complex_topology.ContinuousAtCompose.At(partial, translate, z)))
					differenceContinuous := b.Have(
						"so is their difference",
						"complex_continuous_at(λx:complex. F(x + w) - «partial»(a, N, x + w), z)",
						By(
							b.Simplified(fContin, Fwd(functions.ComposeApply)),
							b.Simplified(pContin, Fwd(functions.ComposeApply)),
							complex_topology.ContinuousAtSub.At(
								b.TermAs[Fun[Complex, Complex]]("λx:complex. F(x + w)"),
								b.TermAs[Fun[Complex, Complex]]("λx:complex. «partial»(a, N, x + w)"), z)))
					tail := b.Have(
						"off the imaginary axis z lies strictly to the right, where "+
							"the tail of the series at z + w is at most B·N^(−re z)/re z",
						"re(z) ≠ &0 ⇒ |F(z + w) - «partial»(a, N, z + w)| ≤ B * real_rpow(&N, -re(z)) / |re(z)|",
						Derive(func(c *Argument) {
							offAxis := c.Assume()
							strict := c.Have(
								"z lies strictly to the right of the imaginary axis",
								"&0 < re(z)",
								ByArith(box, offAxis))
							absPart := c.Have(
								"so |re z| is re z",
								"|re(z)| = re(z)",
								ByArith(strict, real_sgn_abs.AbsFixedIffNonneg.At(c.TermAs[Real]("re(z)"))))
							c.Show(
								"the tail of the series to the right of w",
								Simp(Fwd(absPart)),
								By(
									box,
									strict,
									coefficientBound,
									shift,
									positiveN,
									sums.At(z),
									TailBoundRight.At(a, B, z, w, c.TermAs[Complex]("F(z + w)"), N)))
						}))
					b.Show(
						"the arc point is a continuity point with the bound",
						By(differenceContinuous, tail))
				}))
			ordered := arg.Have(
				"the parameters of the right arc are ordered",
				"-(pi / &2) ≤ pi / &2",
				ByArith(real_trigonometry.PiBounds))
			estimate := arg.Have(
				"the weighted kernel estimate on the arc at K = B",
				"|«arcInt»(«weightedKernel»(λz:complex. F(z + w) - «partial»(a, N, z + w), R, N), R, -(pi / &2), pi / &2)| ≤ "+
					"&2 * B * (pi / &2 - -(pi / &2)) / R",
				By(
					positiveR,
					nonnegative,
					positiveN,
					ordered,
					arc,
					WeightedKernelArcBound.At(difference, R, B, α, β, N)))
			arg.Show(
				"the arc spans π",
				ByArith(estimate))
		}),
	Reading: "The continuity hypothesis makes the integrand integrable along " +
		"the arc, its ends on the line Re s = Re w included; the theorem supplies " +
		"it from F holomorphic on an open set containing the closed half-plane.",
})}

// LeftArcBound — over the left half-circle, the integral of
// partial sum·N^z·kernel is at most 2πB·(1/N + 1/R): the head of the series
// to the left of w is at most B·N^(−Re z)·(1/N + 1/|Re z|), which −Re z ≤ R
// makes at most B(R/N + 1)·N^(−Re z)/|Re z|, and WeightedKernelArcBound turns
// that into 2B(R/N + 1)·π/R.
var LeftArcBound = leftArcBoundThm{family.Add(registry.ProofEntry{
	Name: "LeftArcBound",
	Key:  "prop_93e6ea6bedd8e110",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B R:real. ∀w:complex. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 ≤ re(w)",
			"&0 < R",
			"0 < N",
		},
		Conclusion: "|«arcInt»(«weightedKernel»(λz:complex. «partial»(a, N, z + w), R, N), R, pi / &2, &3 * pi / &2)| ≤ " +
			"&2 * pi * B * (&1 / &N + &1 / R)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			B, R *Expr[Real],
			w *Expr[Complex],
			N *Expr[Nat],
			coefficientBound, shift, positiveR, positiveN Fact,
		) {
			α := arg.TermAs[Real]("pi / &2")
			β := arg.TermAs[Real]("&3 * pi / &2")
			base := arg.TermAs[Real]("&N")
			K := arg.TermAs[Real]("B * (R / &N + &1)")
			U := arg.TermAs[Set[Complex]]("𝕌")
			id := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z")
			translate := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z + w")
			partial := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «partial»(a, N, z)")
			head := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «partial»(a, N, z + w)")
			basePos := arg.Have(
				"the positive integer gives a positive base",
				"&0 < real_of_num(N)",
				By(positiveN, real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), N)))
			nonnegative := arg.Have(
				"the bound on the coefficients is nonnegative",
				"&0 ≤ B",
				ByArith(
					coefficientBound.At(arg.TermAs[Nat]("0")),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("a(0)"))))
			arc := arg.Have(
				"on the closed left arc the partial sum is continuous and, "+
					"off the imaginary axis, at most B(R/N + 1)·N^(−re z)/|re z|",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"pi / &2 ≤ t",
						"t ≤ &3 * pi / &2",
					},
					Conclusion: "complex_continuous_at(λx:complex. «partial»(a, N, x + w), circle_path(&0, R, t)) ∧ " +
						"(re(circle_path(&0, R, t)) ≠ &0 ⇒ " +
						"    |«partial»(a, N, circle_path(&0, R, t) + w)| ≤ " +
						"    B * (R / &N + &1) * real_rpow(&N, -re(circle_path(&0, R, t))) / |re(circle_path(&0, R, t))|)",
				},
				Derive(func(b *Argument) {
					t := b.FixAs[Real]("t")
					inInterval := b.Assume()
					z, circle := b.LetAs[Complex]("z", "circle_path(&0, R, t)")
					radius := b.Have(
						"z lies on the circle of radius R",
						"|z| = R",
						circle.Rw(),
						By(positiveR, path_integral.CirclePathModulus.At(R, t)))
					realPart := b.Have(
						"the real part is the radius times the cosine",
						"re(z) = R * cos(t)",
						circle.Rw(),
						Simp(
							Fwd(path_integral.CirclePathDef),
							Fwd(complex_exp.EulerOfReal),
							Fwd(complex_field.PartsAdd),
							Fwd(complex_field.PartsMul),
							Fwd(complex_field.PartsOfReal),
							Fwd(complex_field.PartsI)),
						ByArith())
					theta := b.TermAs[Real]("t - pi")
					turn := b.Have(
						"adding a half turn to t minus pi recovers t",
						"(t - pi) + pi = t",
						ByArith())
					halfTurn := b.Have(
						"subtracting a half turn puts the cosine on the right arc",
						"cos(t) = -cos(t - pi) ∧ -(pi / &2) ≤ t - pi ∧ t - pi ≤ pi / &2",
						ByArith(inInterval, b.Simplified(real_trigonometry.CosAddPi.At(theta), Fwd(turn))))
					leftPart := b.Have(
						"the real part is nonpositive on the closed left arc",
						"re(z) ≤ &0",
						ByArith(halfTurn, realPart, positiveR, real_trigonometry.CosNonnegHalfPi.At(theta)))
					partBound := b.Have(
						"the radius bounds the magnitude of the negative real part",
						"-re(z) ≤ R",
						ByArith(
							radius,
							complex_abs.ReLessEqAbs.At(b.TermAs[Complex]("-z")),
							complex_abs.AbsNeg.At(z),
							complex_field.PartsNeg.At(z)))
					shifted := b.TermAs[Complex]("z + w")
					shiftContin := b.Have(
						"translation is continuous at z",
						"complex_continuous_at(λx:complex. x + w, z)",
						By(
							complex_topology.ContinuousAtId.At(z),
							complex_topology.ContinuousAtConst.At(z, w),
							complex_topology.ContinuousAtAdd.At(id, b.TermAs[Fun[Complex, Complex]]("λx:complex. w"), z)))
					pContin := b.Have(
						"the translated partial sum, an entire function, is continuous at z",
						"complex_continuous_at((λx:complex. «partial»(a, N, x)) ∘ (λx:complex. x + w), z)",
						By(
							dirichlet_series.PartialSumHolomorphic.At(a, N),
							set_basic.InUniv.At(shifted),
							complex_derivative.HolomorphicOnContinuousAt.At(U, partial, shifted),
							shiftContin,
							complex_topology.ContinuousAtCompose.At(partial, translate, z)))
					y := b.TermAs[Real]("re(z)")
					headBound := b.Have(
						"off the imaginary axis z lies strictly to the left, where the "+
							"head of the series at z + w is at most B(R/N + 1)·N^(−re z)/|re z|",
						"re(z) ≠ &0 ⇒ |«partial»(a, N, z + w)| ≤ B * (R / &N + &1) * real_rpow(&N, -re(z)) / |re(z)|",
						Derive(func(c *Argument) {
							offAxis := c.Assume()
							strict := c.Have(
								"z lies strictly to the left of the imaginary axis",
								"re(z) < &0",
								ByArith(offAxis, leftPart))
							absPart := c.Have(
								"so |re z| is −re z",
								"|re(z)| = -re(z)",
								By(leftPart, real_sgn_abs.AbsNegatedIffNonpos.At(y)))
							ratios := c.Have(
								"dividing −re z ≤ R by the positive index preserves it",
								"(-re(z)) / &N + &1 ≤ R / &N + &1",
								ByArith(partBound, basePos, real_order_field.DivPos.At(c.TermAs[Real]("&1"), base)))
							weight := c.Have(
								"the common factor is nonnegative",
								"&0 ≤ B * real_rpow(&N, -re(z)) / (-re(z))",
								ByArith(nonnegative, strict, real_rpow.RpowNonneg.At(base, c.TermAs[Real]("-re(z)"))))
							c.Show(
								"the head of the series to the left of w, with −re z at most R",
								Simp(Fwd(absPart)),
								real_order_ring.OrderCalc(c.Ctx()).CalcLeibniz(
									c.TermAs[Real]("|«partial»(a, N, z + w)|"),
									LeLeg(
										c.TermAs[Real]("B * real_rpow(&N, -re(z)) * (&1 / &N + &1 / (-re(z)))"),
										"the head of the series to the left of w",
										By(strict, coefficientBound, shift, positiveN, HeadBoundLeft.At(a, B, z, w, N))),
									EqLeg(
										c.TermAs[Real]("(B * real_rpow(&N, -re(z)) / (-re(z))) * ((-re(z)) / &N + &1)"),
										"take −re z out of the bracket",
										ByArith(strict)),
									LeLeg(
										c.TermAs[Real]("(B * real_rpow(&N, -re(z)) / (-re(z))) * (R / &N + &1)"),
										"−re z is at most R",
										By(
											ratios,
											weight,
											real_order_ring.LessEqMulLeft.At(
												c.TermAs[Real]("B * real_rpow(&N, -re(z)) / (-re(z))"),
												c.TermAs[Real]("(-re(z)) / &N + &1"),
												c.TermAs[Real]("R / &N + &1")))),
									EqLeg(
										c.TermAs[Real]("B * (R / &N + &1) * real_rpow(&N, -re(z)) / (-re(z))"),
										"regroup",
										ByArith(strict))))
						}))
					b.Show(
						"the arc point is a continuity point with the bound",
						By(b.Simplified(pContin, Fwd(functions.ComposeApply)), headBound))
				}))
			ordered := arg.Have(
				"the parameters of the left arc are ordered",
				"pi / &2 ≤ &3 * pi / &2",
				ByArith(real_trigonometry.PiBounds))
			factor := arg.Have(
				"the bound B(R/N + 1) is nonnegative",
				"&0 ≤ B * (R / &N + &1)",
				ByArith(nonnegative, positiveR, basePos, real_order_field.DivPos.At(R, base)))
			estimate := arg.Have(
				"the weighted kernel estimate on the arc at K = B(R/N + 1)",
				"|«arcInt»(«weightedKernel»(λz:complex. «partial»(a, N, z + w), R, N), R, pi / &2, &3 * pi / &2)| ≤ "+
					"&2 * (B * (R / &N + &1)) * (&3 * pi / &2 - pi / &2) / R",
				By(positiveR, factor, positiveN, ordered, arc, WeightedKernelArcBound.At(head, R, K, α, β, N)))
			arg.Show(
				"the arc spans π",
				ByArith(estimate, positiveR, basePos))
		}),
	Reading: "The partial sum is entire, so its left side of the contour " +
		"can be the half-circle, where the kernel is small; F's left side " +
		"has to stay inside the region where F is known, the thin rectangle.",
})}

// LeftSidesBound — over the three sides of the rectangle, the integral of
// G·N^z is at most M·(2/log N + 2R·N^(−δ)) for G bounded by M there.
var LeftSidesBound = leftSidesBoundThm{family.Add(registry.ProofEntry{
	Name: "LeftSidesBound",
	Key:  "prop_1ffa1f4cb0fcafb",
	Build: family.Theorem(Statement{
		Binders: "∀G:(complex → complex). ∀M R δ:real. ∀N:num.",
		Hypotheses: []string{
			"&0 < R",
			"&0 < δ",
			"2 ≤ N",
			"∀z:complex. z ∈ «sides»(R, δ) ⇒ complex_continuous_at(G, z) ∧ |G(z)| ≤ M",
		},
		Conclusion: "|«sidesInt»(λz:complex. G(z) * complex_cpow(complex_of_real(&N), z), R, δ)| ≤ " +
			"M * (&2 / log(&N) + &2 * R * real_rpow(&N, -δ))",
	},
		func(
			arg *Argument,
			G *Arrow[Complex, Complex],
			M, R, δ *Expr[Real],
			N *Expr[Nat],
			positiveR, positiveδ, atLeastTwo, onSides Fact,
		) {
			U := arg.TermAs[Set[Complex]]("𝕌")
			base := arg.TermAs[Real]("&N")
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			power := arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&N, z)")
			weighted := arg.TermAs[Fun[Complex, Complex]]("λz:complex. G(z) * complex_cpow(&N, z)")
			upperLeft := arg.TermAs[Complex]("-&δ + complex_i * &R")
			lowerLeft := arg.TermAs[Complex]("-&δ - complex_i * &R")
			majorant := arg.TermAs[Fun[Real, Real]]("λt:real. M * δ * real_rpow(&N, -δ * t)")
			area := arg.TermAs[Real]("M * (&1 - real_rpow(&N, -δ)) / log(&N)")
			baseAboveOne := arg.Have(
				"the real base is greater than one",
				"&1 < real_of_num(N)",
				ByArith(atLeastTwo))
			logPos := arg.Have(
				"the logarithm of the base is positive",
				"&0 < log(real_of_num(N))",
				ByArith(baseAboveOne, real_exp_log.LogOne, real_exp_log.LogLessIff.At(one, base)))
			holPower := arg.Have(
				"the weight is entire in its exponent",
				"holomorphic_on(𝕌, λz:complex. complex_cpow(&N, z))",
				ByArith(baseAboveOne, complex_cpow.CpowHolomorphicExponent.At(base)))
			sides := arg.Have(
				"the weighted integrand is continuous along the sides with the stated pointwise bound",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ «sides»(R, δ)",
					},
					Conclusion: "complex_continuous_at(λu:complex. G(u) * complex_cpow(&N, u), z) ∧ " +
						"|G(z) * complex_cpow(&N, z)| ≤ M * real_rpow(&N, re(z))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					onSide := b.Assume()
					gOnSide := b.Have(
						"G is continuous at the side point and bounded there by M",
						"complex_continuous_at(G, z) ∧ |G(z)| ≤ M",
						By(onSide, onSides.At(z)))
					scale := b.Have(
						"the modulus of the weight is the real power at the real part",
						"|complex_cpow(&N, z)| = real_rpow(&N, re(z))",
						ByArith(baseAboveOne, complex_cpow.AbsCpow.At(base, z)))
					b.Show(
						"multiply the continuous factors and their moduli",
						ByArith(
							gOnSide,
							holPower,
							set_basic.InUniv.At(z),
							scale,
							complex_derivative.HolomorphicOnContinuousAt.At(U, power, z),
							complex_topology.ContinuousAtMul.At(G, power, z),
							complex_abs.AbsMul.At(b.TermAs[Complex]("G(z)"), b.TermAs[Complex]("complex_cpow(&N, z)")),
							complex_abs.AbsNonneg.At(b.TermAs[Complex]("complex_cpow(&N, z)"))))
				}))
			atUpper := arg.Have(
				"the upper left corner is a side point",
				"re(-&δ + complex_i * &R) = -δ ∧ im(-&δ + complex_i * &R) = R",
				Simp(
					Fwd(complex_field.PartsAdd),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsNeg),
					Fwd(complex_field.PartsI),
					Fwd(complex_field.PartsOfReal)),
				ByArith())
			nonnegative := arg.Have(
				"the side bound is nonnegative from its value at the upper corner",
				"&0 ≤ M",
				ByArith(
					atUpper,
					positiveR,
					onSides.At(upperLeft),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("G(-&δ + complex_i * &R)"))))
			majorantIntegral := arg.Have(
				"the horizontal real majorant integrates explicitly",
				"real_has_integral(λt:real. M * δ * real_rpow(&N, -δ * t), "+
					"    &0, "+
					"    &1, "+
					"    M * (&1 - real_rpow(&N, -δ)) / log(&N))",
				By(baseAboveOne, real_rpow.RpowExponentIntegral.At(base, δ, M)))
			areaBound := arg.Have(
				"the positive endpoint power can be dropped from the integral bound",
				"M * (&1 - real_rpow(&N, -δ)) / log(&N) ≤ M / log(&N)",
				ByArith(logPos, nonnegative, real_rpow.RpowNonneg.At(base, arg.TermAs[Real]("-δ"))))
			horizontal := arg.Have(
				"either orientation of a horizontal side has the same modulus bound",
				Statement{
					Binders: "∀y:real.",
					Hypotheses: []string{
						"|y| = R",
					},
					Conclusion: "|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &y, -&δ + complex_i * &y)| ≤ " +
						"M / log(&N) ∧ " +
						"|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ + complex_i * &y, complex_i * &y)| ≤ " +
						"M / log(&N)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					height := b.Assume()
					p := b.TermAs[Complex]("complex_i * &y")
					q := b.TermAs[Complex]("-&δ + complex_i * &y")
					path := b.TermAs[Fun[Real, Complex]]("segment_path(complex_i * &y, -&δ + complex_i * &y)")
					velocity := b.TermAs[Fun[Real, Complex]]("λt:real. (-&δ + complex_i * &y) - complex_i * &y")
					pullback := b.TermAs[Fun[Real, Complex]](
						"λt:real. " +
							"    G(segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * " +
							"    complex_cpow(&N, segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * " +
							"    (-&δ + complex_i * &y - complex_i * &y)")
					horizontalDirection := b.Have(
						"the horizontal displacement is minus δ",
						"(-&δ + complex_i * &y) - complex_i * &y = &(-δ)",
						ByArith(complex_field.OfRealNeg.At(δ)))
					speed := b.Have(
						"the horizontal velocity has modulus δ",
						"|(-&δ + complex_i * &y) - complex_i * &y| = δ",
						horizontalDirection.Rw(),
						ByArith(positiveδ))
					pointwise := b.Have(
						"the pulled back integrand is continuous along the path and bounded by the majorant",
						Statement{
							Binders: "∀t:real.",
							Hypotheses: []string{
								"&0 ≤ t",
								"t ≤ &1",
							},
							Conclusion: "complex_continuous_at(λz:complex. G(z) * complex_cpow(&N, z), " +
								"    segment_path(complex_i * &y, -&δ + complex_i * &y, t)) ∧ " +
								"|(λz:complex. G(z) * complex_cpow(&N, z))( " +
								"    segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * " +
								"(-&δ + complex_i * &y - complex_i * &y)| ≤ " +
								"M * δ * real_rpow(&N, -δ * t)",
						},
						Derive(func(c *Argument) {
							c.FixAs[Real]("t")
							unit := c.Assume()
							z := c.TermAs[Complex]("segment_path(complex_i * &y, -&δ + complex_i * &y, t)")
							parts := c.Have(
								"the height is fixed and the real part decreases linearly",
								"re(segment_path(complex_i * &y, -&δ + complex_i * &y, t)) = -δ * t ∧ "+
									"im(segment_path(complex_i * &y, -&δ + complex_i * &y, t)) = y",
								Simp(
									Fwd(path_integral.SegmentPathDef),
									Fwd(complex_field.PartsAdd),
									Fwd(complex_field.PartsSub),
									Fwd(complex_field.PartsMul),
									Fwd(complex_field.PartsNeg),
									Fwd(complex_field.PartsOfReal),
									Fwd(complex_field.PartsI)),
								ByArith())
							c.Show(
								"the bound along the side acquires the speed factor δ",
								ByArith(
									unit,
									height,
									positiveδ,
									parts,
									speed,
									sides.At(z),
									complex_abs.AbsMul.At(
										c.TermAs[Complex](
											"(λz:complex. G(z) * complex_cpow(&N, z))(segment_path(complex_i * &y, -&δ + complex_i * &y, t))"),
										c.TermAs[Complex]("(-&δ + complex_i * &y) - complex_i * &y"))))
						}))
					weightedContinuous := b.Have(
						"the weighted function is continuous at all the segment points",
						Statement{
							Binders: "∀t:real.",
							Hypotheses: []string{
								"&0 ≤ t",
								"t ≤ &1",
							},
							Conclusion: "complex_continuous_at(λz:complex. G(z) * complex_cpow(&N, z), " +
								"    segment_path(complex_i * &y, -&δ + complex_i * &y, t))",
						},
						b.ForEach(func(t *Expr[Real]) Action { return By(pointwise.At(t)) }))
					dominated := b.Have(
						"the scalar majorant dominates the pulled back integrand",
						Statement{
							Binders: "∀t:real.",
							Hypotheses: []string{
								"&0 ≤ t",
								"t ≤ &1",
							},
							Conclusion: "|(λz:complex. G(z) * complex_cpow(&N, z))( " +
								"    segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * " +
								"(-&δ + complex_i * &y - complex_i * &y)| ≤ " +
								"M * δ * real_rpow(&N, -δ * t)",
						},
						b.ForEach(func(t *Expr[Real]) Action { return By(pointwise.At(t)) }))
					I, integral := b.ObtainAs[Complex](
						"the continuous integrand has an integral along the segment",
						"∃I:complex. "+
							"    complex_has_integral(λt:real. "+
							"            G(segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * "+
							"            complex_cpow(&N, segment_path(complex_i * &y, -&δ + complex_i * &y, t)) * "+
							"            (-&δ + complex_i * &y - complex_i * &y), "+
							"        &0, "+
							"        &1, "+
							"        I)",
						By(
							weightedContinuous,
							path_integral.SegmentPiecewiseSmooth.At(p, q),
							path_integral.PathIntegrable.At(weighted, path, velocity, zero, one)),
						Named("I"))
					forward := b.Have(
						"the forward integral is bounded by the majorant integral",
						"|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &y, -&δ + complex_i * &y)| ≤ "+
							"M / log(&N)",
						Simp(Fwd(path_integral.PathIntegralDef)),
						ByArith(
							dominated,
							integral,
							majorantIntegral,
							areaBound,
							path_integral.ComplexHasIntegralDominated.At(pullback, majorant, zero, one, area, I),
							path_integral.ComplexHasIntegralValue.At(pullback, zero, one, I)))
					b.Show(
						"reversing the path changes the sign of the integral",
						By(
							forward,
							weightedContinuous,
							path_integral.SegmentReverse.At(weighted, p, q),
							complex_abs.AbsNeg.At(b.TermAs[Complex](
								"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &y, -&δ + complex_i * &y)"))))
				}))
			verticalPath := arg.TermAs[Fun[Real, Complex]](
				"segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R)")
			verticalVelocity := arg.TermAs[Fun[Real, Complex]](
				"λt:real. (-&δ - complex_i * &R) - (-&δ + complex_i * &R)")
			verticalBound := arg.TermAs[Real]("M * real_rpow(&N, -δ)")
			verticalPoints := arg.Have(
				"the vertical segment stays at real part minus δ",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &1",
					},
					Conclusion: "complex_continuous_at(λz:complex. G(z) * complex_cpow(&N, z), " +
						"    segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) ∧ " +
						"|G(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) * " +
						"complex_cpow(&N, segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t))| ≤ " +
						"M * real_rpow(&N, -δ)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]("t")
					unit := b.Assume()
					z := b.TermAs[Complex]("segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)")
					parts := b.Have(
						"the imaginary part interpolates between the two heights",
						"re(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) = -δ ∧ "+
							"im(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) = R - &2 * R * t",
						Simp(
							Fwd(path_integral.SegmentPathDef),
							Fwd(complex_field.PartsAdd),
							Fwd(complex_field.PartsSub),
							Fwd(complex_field.PartsMul),
							Fwd(complex_field.PartsNeg),
							Fwd(complex_field.PartsOfReal),
							Fwd(complex_field.PartsI)),
						ByArith())
					b.Show(
						"the height stays within R, so the fixed exponent is minus δ",
						ByArith(
							unit,
							positiveR,
							parts,
							sides.At(z),
							real_sgn_abs.AbsBounds.At(
								b.TermAs[Real]("im(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t))"), R)))
				}))
			verticalDirection := arg.Have(
				"the vertical displacement is minus twice the upper height vector",
				"(-&δ - complex_i * &R) - (-&δ + complex_i * &R) = -(complex_of_real(&2) * (complex_i * &R))",
				ByArith())
			verticalSpeed := arg.Have(
				"the speed on the vertical segment is twice the height",
				"|(-&δ - complex_i * &R) - (-&δ + complex_i * &R)| = &2 * R",
				verticalDirection.Rw(),
				ByArith(positiveR))
			length := arg.Have(
				"the vertical segment has length twice R",
				"real_integral(λt:real. |(-&δ - complex_i * &R) - (-&δ + complex_i * &R)|, &0, &1) = &2 * R",
				Simp(Fwd(verticalSpeed)),
				ByArith(
					real_integral.HasIntegralConst.At(zero, one, arg.TermAs[Real]("&2 * R")),
					real_integral.HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. &2 * R"), zero, one, arg.TermAs[Real]("&2 * R"))))
			vertical := arg.Have(
				"the vertical contribution is at most its length times the fixed power bound",
				"|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ + complex_i * &R, -&δ - complex_i * &R)| ≤ "+
					"&2 * R * M * real_rpow(&N, -δ)",
				ByArith(
					verticalPoints,
					length,
					path_integral.SegmentPiecewiseSmooth.At(upperLeft, lowerLeft),
					path_integral.PathIntegralBound.At(
						weighted, verticalPath, verticalVelocity, zero, one, verticalBound)))
			lowerEndpoints := arg.Have(
				"the negative height gives the two lower corners",
				"complex_i * &(-R) = -(complex_i * &R) ∧ -&δ + complex_i * &(-R) = -&δ - complex_i * &R",
				Simp(Fwd(complex_field.OfRealNeg)),
				ByArith())
			lowerCorners := arg.Conjuncts(
				lowerEndpoints,
				"the lower right corner uses negative height",
				"the lower left corner uses negative height")
			height := arg.Have(
				"both signed heights have modulus R",
				"|R| = R ∧ |-R| = R",
				ByArith(positiveR, real_sgn_abs.AbsFixedIffNonneg.At(R), real_sgn_abs.AbsEven.At(R)))
			top := arg.Have(
				"the upper horizontal integral has the logarithmic bound",
				"|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &R, -&δ + complex_i * &R)| ≤ "+
					"M / log(&N)",
				By(height, horizontal.At(R)))
			bottom := arg.Have(
				"the lower horizontal integral has the logarithmic bound",
				"|«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ - complex_i * &R, -(complex_i * &R))| ≤ "+
					"M / log(&N)",
				Simp(Rev(lowerCorners[0]), Rev(lowerCorners[1])),
				By(height, horizontal.At(arg.TermAs[Real]("-R"))))
			topIntegral := arg.TermAs[Complex](
				"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &R, -&δ + complex_i * &R)")
			leftIntegral := arg.TermAs[Complex](
				"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ + complex_i * &R, -&δ - complex_i * &R)")
			bottomIntegral := arg.TermAs[Complex](
				"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ - complex_i * &R, -(complex_i * &R))")
			arg.Show(
				"add the three modulus bounds around the rectangle",
				ByArith(
					top,
					vertical,
					bottom,
					complex_abs.AbsTriangle.At(topIntegral, leftIntegral),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex](
							"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), complex_i * &R, -&δ + complex_i * &R) + "+
								"«segInt»(λz:complex. G(z) * complex_cpow(&N, z), -&δ + complex_i * &R, -&δ - complex_i * &R)"),
						bottomIntegral)))
		}),
	Reading: "The bound and the continuity are asked on the three sides only, not on the " +
		"rectangle they border: Newman's integrand has a pole at 0, inside the rectangle. Both " +
		"terms tend to 0 as N grows with R, δ and M fixed: this is the piece of the contour " +
		"that carries no bound uniform in R, and needs none. N ≥ 2 makes log N positive.",
})}
