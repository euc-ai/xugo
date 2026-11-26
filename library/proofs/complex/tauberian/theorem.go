// theorem.go — Newman's Tauberian theorem. At a fixed radius R the
// contour formula for F(z + w) and the circle formula for the partial sum
// at z + w, each weighted by N^z·(1/z + z/R²), differ by 2πi·(F(w) − S_N(w)),
// and the estimates put the partial sums at w eventually within 3B/R of
// F(w); R is then taken as large as the tolerance asks.

package tauberian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// NewmanSidesBounded gives a common bound for a function continuous on
// the three closed segments of the left side of Newman's contour.
var NewmanSidesBounded = newmanSidesBoundedThm{family.Add(registry.ProofEntry{
	Name: "NewmanSidesBounded",
	Key:  "prop_b1827feb6c227dc1",
	Build: family.Theorem(Statement{
		Binders: "∀G:(complex → complex). ∀R δ:real.",
		Hypotheses: []string{
			"&0 < R", "&0 < δ",
			"∀z:complex. z ∈ «sides»(R, δ) ⇒ complex_continuous_at(G, z)",
		},
		Conclusion: "∃M:real. ∀z:complex. z ∈ «sides»(R, δ) ⇒ |G(z)| ≤ M",
		Abbrev: Abbrev{
			{Name: "realBand", Text: "λa:real. λb:real. preimage_on(𝕌, λz:complex. re(z), ⟦a, b⟧)"},
			{Name: "imaginaryBand", Text: "λa:real. λb:real. preimage_on(𝕌, λz:complex. im(z), ⟦a, b⟧)"},
			{Name: "left", Text: "«realBand»(-δ, -δ) ∩ «imaginaryBand»(-R, R)"},
			{Name: "top", Text: "«realBand»(-δ, &0) ∩ «imaginaryBand»(R, R)"},
			{Name: "bottom", Text: "«realBand»(-δ, &0) ∩ «imaginaryBand»(-R, -R)"},
		},
	}, func(a *Argument, G *Arrow[Complex, Complex], R, δ *Expr[Real], given Fact) {
		complexSpace := a.TermAs[Set[Set[Complex]]]("complex_topology")
		realSpace := a.TermAs[Set[Set[Real]]]("real_topology")
		sides := a.TermAs[Set[Complex]]("«sides»(R, δ)")
		left := a.TermAs[Set[Complex]]("«left»")
		top := a.TermAs[Set[Complex]]("«top»")
		bottom := a.TermAs[Set[Complex]]("«bottom»")
		leftTop := a.TermAs[Set[Complex]]("«left» ∪ «top»")
		realPart := a.TermAs[Fun[Complex, Real]]("λz:complex. re(z)")
		imaginaryPart := a.TermAs[Fun[Complex, Real]]("λz:complex. im(z)")
		parts := a.Have(
			"each coordinate preimage of a closed interval is closed",
			"∀l u:real. "+
				"    closed_in(complex_topology, «realBand»(l, u)) ∧ "+
				"    closed_in(complex_topology, «imaginaryBand»(l, u))",
			Derive(func(b *Argument) {
				l := b.FixAs[Real]("l")
				u := b.FixAs[Real]("u")
				b.Show(
					"both coordinate projections are continuous",
					By(
						complex_topology.PartsContinuous,
						real_topology.ClosedIntervalClosed.At(l, u),
						continuous.ClosedPreimage.At(complexSpace, realSpace, realPart),
						continuous.ClosedPreimage.At(complexSpace, realSpace, imaginaryPart),
						complex_topology.ComplexTopologySpace))
			}))
		minusδ, minusR := a.TermAs[Real]("-δ"), a.TermAs[Real]("-R")
		inter := topological_space.InterClosed.Read(complex_topology.ComplexTopology)
		leftClosed := a.Have(
			"the left side is closed, where the closed line re z = −δ meets the closed band −R ≤ im z ≤ R",
			"closed_in(complex_topology, «left»)",
			By(
				parts.At(minusδ, minusδ),
				parts.At(minusR, R),
				inter.At(
					a.TermAs[Set[Complex]]("«realBand»(-δ, -δ)"), a.TermAs[Set[Complex]]("«imaginaryBand»(-R, R)"))))
		topClosed := a.Have(
			"the top side is closed, where the closed band −δ ≤ re z ≤ 0 meets the closed line im z = R",
			"closed_in(complex_topology, «top»)",
			By(
				parts.At(minusδ, a.TermAs[Real]("&0")),
				parts.At(R, R),
				inter.At(
					a.TermAs[Set[Complex]]("«realBand»(-δ, &0)"), a.TermAs[Set[Complex]]("«imaginaryBand»(R, R)"))))
		bottomClosed := a.Have(
			"the bottom side is closed, where that band meets the closed line im z = −R",
			"closed_in(complex_topology, «bottom»)",
			By(
				parts.At(minusδ, a.TermAs[Real]("&0")),
				parts.At(minusR, minusR),
				inter.At(
					a.TermAs[Set[Complex]]("«realBand»(-δ, &0)"), a.TermAs[Set[Complex]]("«imaginaryBand»(-R, -R)"))))
		union := topological_space.UnionClosed.Read(complex_topology.ComplexTopology)
		closedUnion := a.Have(
			"the union of the three closed segments is closed",
			"closed_in(complex_topology, «left» ∪ «top» ∪ «bottom»)",
			By(leftClosed, topClosed, bottomClosed, union.At(left, top), union.At(leftTop, bottom)))
		shape := a.Have(
			"the side inequalities describe the same three segments",
			"«sides»(R, δ) = «left» ∪ «top» ∪ «bottom»",
			Simp(
				Fwd(set_basic.Extension.Inst[Complex]()),
				Fwd(set_basic.InUnion.Inst[Complex]()),
				Fwd(set_basic.InInter.Inst[Complex]()),
				Fwd(functions.PreimageOnDef),
				Fwd(set_basic.InUniv.Inst[Complex]()),
				Fwd(real_topology.ClosedIntervalMembership)),
			Derive(func(b *Argument) {
				b.FixAs[Complex]("z")
				y := b.TermAs[Real]("im(z)")
				b.Show(
					"the extreme heights are precisely the points with imaginary modulus R",
					ByArith(
						given,
						real_sgn_abs.AbsBounds.At(y, R),
						real_sgn_abs.AbsFixedIffNonneg.At(y),
						real_sgn_abs.AbsNegatedIffNonpos.At(y)))
			}))
		bounded := a.Have(
			"the moduli on the three sides are bounded by the sum of width and height",
			"∃A:real. ∀z:complex. z ∈ «sides»(R, δ) ⇒ |z| ≤ A",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Real]("δ + R"))
				z := b.FixAs[Complex]("z")
				member := b.Assume()
				location := b.Have(
					"read the side membership as coordinate bounds",
					"(re(z) = -δ ∧ |im(z)| ≤ R) ∨ (-δ ≤ re(z) ∧ re(z) ≤ &0 ∧ |im(z)| = R)",
					BySets(member))
				b.Show(
					"use the sum of the moduli of both coordinates",
					ByArith(
						location,
						given,
						complex_abs.AbsLeParts.At(z),
						real_sgn_abs.AbsNegatedIffNonpos.At(b.TermAs[Real]("re(z)"))))
			}))
		compact := a.Have(
			"closed and bounded side segments form a compact set",
			"compact_in(complex_topology, «sides»(R, δ))",
			By(shape, bounded, closedUnion, complex_topology.ComplexCompactIff.At(sides)))
		continuousOn := a.Have(
			"pointwise continuity gives continuity on that set",
			"complex_continuous_on(«sides»(R, δ), G)",
			By(given, complex_topology.ContinuousAtOn.At(sides, G)))
		a.Show(
			"a continuous function is bounded on the compact set",
			By(compact, continuousOn, complex_topology.ContinuousOnCompactBounded.At(sides, G)))
	}),
})}

// NewmanEventualError bounds the terms that vanish as the partial sum
// index grows, with the contour and its uniform side bound held fixed.
var NewmanEventualError = newmanEventualErrorThm{family.Add(registry.ProofEntry{
	Name: "NewmanEventualError",
	Key:  "prop_9331315bfb122412",
	Build: family.Theorem(Statement{
		Binders:    "∀B M R δ:real.",
		Hypotheses: []string{"&0 < B", "&0 < R", "&0 < δ"},
		Conclusion: "∃K:num. ∀N:num. " +
			"    K ≤ N ⇒ " +
			"    2 ≤ N ∧ B * (&1 / &N) + (M / pi) * (&1 / log(&N)) + (M * R / pi) * real_rpow(&N, -δ) ≤ B / R",
		Abbrev: Abbrev{
			{Name: "recip", Text: "λn:num. &1 / &(n + 1)"},
			{Name: "recipLog", Text: "λn:num. &1 / log(&(n + 1))"},
			{Name: "power", Text: "λn:num. real_rpow(&(n + 1), -δ)"},
			{Name: "first", Text: "λn:num. B * «recip»(n)"},
			{Name: "second", Text: "λn:num. (M / pi) * «recipLog»(n)"},
			{Name: "third", Text: "λn:num. (M * R / pi) * «power»(n)"},
			{Name: "pair", Text: "λn:num. «first»(n) + «second»(n)"},
			{Name: "error", Text: "λn:num. «pair»(n) + «third»(n)"},
		},
	}, func(a *Argument, B, M, R, δ *Expr[Real], given Fact) {
		zero := a.TermAs[Real]("&0")
		one := a.TermAs[Real]("&1")
		recip := a.TermAs[Fun[Nat, Real]]("«recip»")
		recipLog := a.TermAs[Fun[Nat, Real]]("«recipLog»")
		power := a.TermAs[Fun[Nat, Real]]("«power»")
		first := a.TermAs[Fun[Nat, Real]]("«first»")
		second := a.TermAs[Fun[Nat, Real]]("«second»")
		third := a.TermAs[Fun[Nat, Real]]("«third»")
		pair := a.TermAs[Fun[Nat, Real]]("«pair»")
		total := a.TermAs[Fun[Nat, Real]]("«error»")
		inversePower := a.Have(
			"the reciprocal is the power with exponent minus one",
			"(λn:num. real_rpow(&(n + 1), -&1)) = «recip»",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				x := b.TermAs[Real]("&(n + 1)")
				b.Show(
					"use the power laws at a positive base",
					ByArith(real_rpow.RpowNeg.At(x, one), real_rpow.RpowOneExponent.At(x)))
			}))
		inverseLimit := a.Have(
			"the reciprocal of the index tends to zero",
			"«recip» ⟶ &0",
			inversePower.RwRev(),
			By(real_rpow.RpowNegTendsToZero.At(one)))
		powerLimit := a.Have(
			"the fixed negative power tends to zero",
			"«power» ⟶ &0",
			By(given, real_rpow.RpowNegTendsToZero.At(δ)))
		firstLimit := a.Have(
			"scaling preserves the reciprocal limit",
			"«first» ⟶ &0",
			ByArith(inverseLimit, real_sequences.LimitScale.At(recip, zero, B)))
		secondLimit := a.Have(
			"scaling preserves the logarithmic limit",
			"«second» ⟶ &0",
			ByArith(
				real_exp_log.ReciprocalLogTendsToZero,
				real_sequences.LimitScale.At(recipLog, zero, a.TermAs[Real]("M / pi"))))
		thirdLimit := a.Have(
			"scaling preserves the power limit",
			"«third» ⟶ &0",
			ByArith(powerLimit, real_sequences.LimitScale.At(power, zero, a.TermAs[Real]("M * R / pi"))))
		pairLimit := a.Have(
			"both reciprocal terms together tend to zero",
			"«pair» ⟶ &0",
			By(firstLimit, secondLimit, real_sequences.LimitAdd.At(first, second, zero, zero)))
		totalLimit := a.Have(
			"the total error tends to zero",
			"«error» ⟶ &0",
			By(pairLimit, thirdLimit, real_sequences.LimitAdd.At(pair, third, zero, zero)))
		_, eventually := a.ObtainAs[Nat](
			"the error eventually lies within B divided by R of zero",
			"∃J:num. ∀n:num. J ≤ n ⇒ |«error»(n) - &0| < B / R",
			ByArith(given, totalLimit, real_sequences.RealConvergesToDef.At(total, zero)),
			Named("J"))
		a.Take(a.TermAs[Nat]("J + 2"))
		a.FixAs[Nat]("N")
		large := a.Assume()
		enough := a.Have(
			"subtracting one leaves an index past J",
			"2 ≤ N ∧ J ≤ N - 1 ∧ N - 1 + 1 = N",
			ByArith(large))
		tolerance := a.Have(
			"the error at N is smaller than the tolerance",
			"|«error»(N - 1) - &0| < B / R",
			By(enough, eventually.At(a.TermAs[Nat]("N - 1"))))
		small := a.Simplified(tolerance, Fwd(enough))
		a.Show(
			"the error itself is bounded by its modulus",
			ByArith(
				enough,
				small,
				real_sgn_abs.AbsDominates.At(
					a.TermAs[Real]("B * (&1 / &N) + (M / pi) * (&1 / log(&N)) + (M * R / pi) * real_rpow(&N, -δ)"))))
	}),
})}

// NewmanWeightedNumerator multiplies by the entire factors used before
// applying Cauchy's formula. Both factors have value one at the origin.
var NewmanWeightedNumerator = newmanWeightedNumeratorThm{family.Add(registry.ProofEntry{
	Name: "NewmanWeightedNumerator",
	Key:  "prop_77686941b2b630d6",
	Build: family.Theorem(Statement{
		Binders:    "∀G:(complex → complex). ∀V:set(complex). ∀R:real. ∀N:num.",
		Hypotheses: []string{"holomorphic_on(V, G)", "0 < N"},
		Conclusion: "holomorphic_on(V, «numerator»(G, R, N)) ∧ " +
			"«numerator»(G, R, N, complex_of_real(&0)) = G(complex_of_real(&0))",
	}, func(
		a *Argument,
		G *Arrow[Complex, Complex],
		V *Expr[Set[Complex]],
		R *Expr[Real],
		N *Expr[Nat],
		given Fact,
	) {
		id := a.TermAs[Fun[Complex, Complex]]("λz:complex. z")
		square := a.TermAs[Fun[Complex, Complex]]("λz:complex. z * z")
		one := a.TermAs[Complex]("&1")
		unit := a.TermAs[Fun[Complex, Complex]]("λz:complex. &1")
		scalar := a.TermAs[Complex]("complex_inv(&(R * R))")
		constant := a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(&(R * R))")
		scaled := a.TermAs[Fun[Complex, Complex]]("λz:complex. (z * z) * complex_inv(&(R * R))")
		polynomial := a.TermAs[Fun[Complex, Complex]]("λz:complex. &1 + (z * z) / &(R * R)")
		U := a.TermAs[Set[Complex]]("𝕌")
		base := a.TermAs[Real]("&N")
		power := a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&N, z)")
		holPolynomial := a.Have(
			"the quadratic factor is holomorphic",
			"holomorphic_on(V, λz:complex. &1 + (z * z) / &(R * R))",
			Simp(Fwd(complex_field.ComplexDivDef)),
			By(
				complex_derivative.HolomorphicOnId.At(V),
				complex_derivative.HolomorphicOnConst.At(V, one),
				complex_derivative.HolomorphicOnConst.At(V, scalar),
				complex_derivative.HolomorphicOnMul.At(V, id, id),
				complex_derivative.HolomorphicOnMul.At(V, square, constant),
				complex_derivative.HolomorphicOnAdd.At(V, unit, scaled)))
		basePos := a.Have(
			"the index provides a positive base",
			"&0 < real_of_num(N)",
			ByArith(given))
		holPower := a.Have(
			"the power is entire and hence holomorphic here",
			"holomorphic_on(V, λz:complex. complex_cpow(&N, z))",
			By(
				basePos,
				complex_cpow.CpowHolomorphicExponent.At(base),
				set_order.SubsetUniv.At(V),
				complex_derivative.HolomorphicOnSubset.At(U, V, power)))
		hol := a.Have(
			"the three factors give a holomorphic numerator",
			"holomorphic_on(V, «numerator»(G, R, N))",
			By(
				given,
				holPower,
				holPolynomial,
				complex_derivative.HolomorphicOnMul.At(V, G, power),
				complex_derivative.HolomorphicOnMul.At(
					V, a.TermAs[Fun[Complex, Complex]]("λz:complex. G(z) * complex_cpow(&N, z)"), polynomial)))
		atZero := a.Have(
			"both weighting factors are one at zero",
			"«numerator»(G, R, N, complex_of_real(&0)) = G(complex_of_real(&0))",
			Simp(Fwd(complex_field.ComplexDivDef), Fwd(complex_cpow.CpowZeroExponent)),
			ByArith())
		a.Show(
			"combine holomorphy and the value at zero",
			By(hol, atZero))
	}),
})}

// NewmanPathWeight rewrites the quotient in Cauchy's formula to the
// weighted kernel integrand along a path avoiding zero.
var NewmanPathWeight = newmanPathWeightThm{family.Add(registry.ProofEntry{
	Name: "NewmanPathWeight",
	Key:  "prop_759b098526456277",
	Build: family.Theorem(Statement{
		Binders:    "∀G:(complex → complex). ∀R:real. ∀N:num. ∀γ v:(real → complex). ∀l u:real.",
		Hypotheses: []string{"l ≤ u", "∀t:real. l ≤ t ∧ t ≤ u ⇒ γ(t) ≠ &0"},
		Conclusion: "path_integral(λz:complex. «numerator»(G, R, N, z) / z, γ, v, l, u) = " +
			"path_integral(«weightedKernel»(G, R, N), γ, v, l, u)",
	}, func(a *Argument, G *Arrow[Complex, Complex], R *Expr[Real], N *Expr[Nat],
		γ, v *Arrow[Real, Complex], l, u *Expr[Real], given Fact) {
		quotient := a.TermAs[Fun[Complex, Complex]]("λz:complex. «numerator»(G, R, N, z) / z")
		kernel := a.TermAs[Fun[Complex, Complex]]("«weightedKernel»(G, R, N)")
		form := a.Have(
			"away from zero the quotient is the weighted kernel",
			"∀z:complex. z ≠ &0 ⇒ «numerator»(G, R, N, z) / z = «weightedKernel»(G, R, N, z)",
			Simp(Fwd(complex_field.ComplexDivDef)),
			Derive(func(b *Argument) {
				b.FixAs[Complex]("z")
				nz := b.Assume()
				b.Show(
					"cancel the nonzero denominator in the quadratic term",
					ByArith(nz))
			}))
		agree := a.Have(
			"the two integrands agree on the path",
			Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"min(l, u) ≤ t",
					"t ≤ max(l, u)",
				},
				Conclusion: "«numerator»(G, R, N, γ(t)) / γ(t) = «weightedKernel»(G, R, N, γ(t))",
			},
			Simp(Fwd(real_sup_inf.RealMinDef), Fwd(real_sup_inf.RealMaxDef)),
			CondRewrite(),
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				inside := b.Assume()
				b.Show(
					"at each parameter the point is nonzero",
					By(given, inside, form.At(γ.Apply(t))))
			}))
		a.Show(
			"the path integral depends only on those values",
			By(agree, path_integral.PathIntegralCongruence.At(quotient, kernel, γ, v, l, u)))
	}),
})}

// NewmanApproximation — under the hypotheses of Newman's theorem, with a
// positive bound B on the coefficients, for every R > 0 the partial sums
// at w are eventually within 3B/R of F(w). With R fixed, F(z + w) and the
// partial sum at z + w, each times N^z·(1/z + z/R²), are integrated: F's
// over the right half-circle and the three sides of a thin rectangle on the
// left, where F(· + w) is still holomorphic (ContourFormula), the entire
// partial sum's over the whole circle (CircleFormula). The two formulas
// differ by 2πi·(F(w) − S_N(w)), and the pieces of the difference are
// bounded by RightArcBound, LeftSidesBound and LeftArcBound.
var NewmanApproximation = newmanApproximationThm{family.Add(registry.ProofEntry{
	Name: "NewmanApproximation",
	Key:  "prop_194e7f9ae9e3fc16",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B R:real. ∀U:set(complex). ∀F:(complex → complex). ∀w:complex.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&0 < B",
			"U ∈ complex_topology",
			"∀s:complex. &1 ≤ re(s) ⇒ s ∈ U",
			"holomorphic_on(U, F)",
			"∀s:complex. &1 < re(s) ⇒ dirichlet_sums(a, s, F(s))",
			"&1 ≤ re(w)",
			"&0 < R",
		},
		Conclusion: "∃K:num. ∀N:num. K ≤ N ⇒ |F(w) - «partial»(a, N, w)| ≤ &3 * B / R",
		Abbrev: Abbrev{
			{Name: "rectangle", Text: "λD:real. " +
				"    {z:complex | -D < re(z) ∧ re(z) < R + &1 ∧ -(R + &1) < im(z) ∧ im(z) < R + &1}"},
			{Name: "shiftedF", Text: "λz:complex. F(z + w)"},
			{Name: "shiftedPartial", Text: "λN:num. λz:complex. «partial»(a, N, z + w)"},
			{Name: "sideF", Text: "λz:complex. F(z + w) * «kernel»(R, z)"},
		},
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		B, R *Expr[Real],
		U *Expr[Set[Complex]],
		F *Arrow[Complex, Complex],
		w *Expr[Complex],
		bounded, positiveB, open, halfPlane, holomorphic, sums, shift, radiusPos Fact,
	) {
		zero := arg.TermAs[Complex]("&0")
		rzero, rone := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
		universe := arg.TermAs[Set[Complex]]("𝕌")
		rho := arg.TermAs[Real]("R + &1")
		_, width := arg.ObtainAs[Real](
			"there is a positive width available at the shifted contour height",
			"∃D:real. &0 < D ∧ ∀s:complex. &1 - D < re(s) ∧ |im(s)| ≤ R + &1 + |im(w)| ⇒ s ∈ U",
			By(open, halfPlane, complex_topology.StripInsideOpen.At(U, arg.TermAs[Real]("R + &1 + |im(w)|"))),
			Named("D"))
		// The rectangle's left side Re z = −δ is closed and must lie inside the
		// open strip 1 − D < Re s, so δ is taken strictly below D.
		δ, widthHalf := arg.LetAs[Real]("δ", "D / &2")
		deltaPos := arg.Have(
			"the chosen half-width is positive",
			"&0 < δ ∧ δ < D",
			ByArith(width, widthHalf))
		V := arg.TermAs[Set[Complex]]("«rectangle»(D)")
		translation := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z + w")
		shiftedF := arg.TermAs[Fun[Complex, Complex]]("«shiftedF»")
		sideF := arg.TermAs[Fun[Complex, Complex]]("«sideF»")
		rectangle := arg.Have(
			"the contour neighbourhood is open and convex",
			"«rectangle»(D) ∈ complex_topology ∧ «convex»(«rectangle»(D))",
			Simp(Fwd(path_integral.SegmentPathDef)),
			By(complex_topology.RectangleOpenConvex.At(
				arg.TermAs[Real]("-D"), rho, arg.TermAs[Real]("-(R + &1)"), rho)))
		inside := arg.Have(
			"the entire contour box lies in the open rectangle",
			"∀z:complex. z ∈ «box»(R, δ) ⇒ z ∈ «rectangle»(D)",
			Derive(func(b *Argument) {
				b.FixAs[Complex]("z")
				box := b.Assume()
				bounds := b.Have(
					"there is strictly positive margin on all four sides",
					"-D < re(z) ∧ re(z) < R + &1 ∧ -(R + &1) < im(z) ∧ im(z) < R + &1",
					ByArith(box, deltaPos, real_sgn_abs.AbsBounds.At(b.TermAs[Real]("im(z)"), R)))
				b.Show(
					"the strict bounds give rectangle membership",
					BySets(bounds))
			}))
		translated := arg.Have(
			"translation sends the rectangle into U",
			"∀z:complex. z ∈ «rectangle»(D) ⇒ z + w ∈ U",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				member := b.Assume()
				bounds := b.Have(
					"the rectangle bounds both coordinates",
					"-D < re(z) ∧ re(z) < R + &1 ∧ -(R + &1) < im(z) ∧ im(z) < R + &1",
					BySets(member))
				strip := b.Have(
					"the translated point satisfies both bounds for inclusion in U",
					"&1 - D < re(z + w) ∧ |im(z + w)| ≤ R + &1 + |im(w)|",
					ByArith(
						bounds,
						shift,
						complex_field.PartsAdd.At(z, w),
						real_sgn_abs.AbsBounds.At(b.TermAs[Real]("im(z)"), rho),
						real_sgn_abs.AbsTriangle.At(b.TermAs[Real]("im(z)"), b.TermAs[Real]("im(w)"))))
				widthParts := b.Conjuncts(
					width,
					"D is positive",
					"the translated strip lies in U")
				b.Show(
					"apply the strip inclusion at the translated point",
					By(strip, widthParts[1].At(b.TermAs[Complex]("z + w"))))
			}))
		entireTranslation := arg.Have(
			"translation is entire",
			"holomorphic_on(𝕌, λz:complex. z + w)",
			By(
				complex_derivative.HolomorphicOnId.At(universe),
				complex_derivative.HolomorphicOnConst.At(universe, w),
				complex_derivative.HolomorphicOnAdd.At(universe, arg.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
					arg.TermAs[Fun[Complex, Complex]]("λz:complex. w"))))
		localTranslation := arg.Have(
			"translation is holomorphic on the rectangle",
			"holomorphic_on(«rectangle»(D), λz:complex. z + w)",
			By(
				entireTranslation,
				set_order.SubsetUniv.At(V),
				complex_derivative.HolomorphicOnSubset.At(universe, V, translation)))
		fComposed := arg.Have(
			"compose F with the holomorphic translation",
			"holomorphic_on(«rectangle»(D), F ∘ (λz:complex. z + w))",
			By(
				holomorphic,
				localTranslation,
				translated,
				complex_derivative.HolomorphicOnCompose.At(V, U, F, translation)))
		fHol := arg.Simplified(fComposed, Fwd(functions.ComposeApply))
		sideContin := arg.Have(
			"the shifted function times the kernel is continuous on every side point",
			"∀z:complex. z ∈ «sides»(R, δ) ⇒ complex_continuous_at(«sideF», z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				member := b.Assume()
				box := b.Have(
					"the side point lies in the box and is away from zero",
					"-δ ≤ re(z) ∧ re(z) ≤ R ∧ |im(z)| ≤ R ∧ z ≠ &0",
					Derive(func(c *Argument) {
						location := c.Have(
							"the side point lies on a horizontal or vertical segment",
							"(re(z) = -δ ∧ |im(z)| ≤ R) ∨ (-δ ≤ re(z) ∧ re(z) ≤ &0 ∧ |im(z)| = R)",
							BySets(member))
						c.Show(
							"its real or imaginary part keeps the point away from zero",
							ByArith(location, radiusPos, deltaPos, complex_field.PartsOfReal.At(rzero)))
					}))
				b.Show(
					"multiply the continuous shifted function and kernel",
					By(
						box,
						inside.At(z),
						fHol,
						complex_derivative.HolomorphicOnContinuousAt.At(V, shiftedF, z),
						KernelContinuousAt.At(R, z),
						complex_topology.ContinuousAtMul.At(shiftedF,
							b.TermAs[Fun[Complex, Complex]]("λx:complex. «kernel»(R, x)"), z)))
			}))
		M, sideSize := arg.ObtainAs[Real](
			"there is a uniform bound on the three compact sides",
			"∃M:real. ∀z:complex. z ∈ «sides»(R, δ) ⇒ |«sideF»(z)| ≤ M",
			By(radiusPos, deltaPos, sideContin, NewmanSidesBounded.At(sideF, R, δ)),
			Named("M"))
		K, tolerance := arg.ObtainAs[Nat](
			"the decaying terms jointly fit within B divided by R past K",
			"∃K:num. ∀N:num. "+
				"    K ≤ N ⇒ "+
				"    2 ≤ N ∧ B * (&1 / &N) + (M / pi) * (&1 / log(&N)) + (M * R / pi) * real_rpow(&N, -δ) ≤ B / R",
			By(positiveB, radiusPos, deltaPos, NewmanEventualError.At(B, M, R, δ)),
			Named("K"))
		arg.Take(K)
		N := arg.FixAs[Nat]("N")
		large := arg.Assume()
		Nbig := arg.Have(
			"the index is at least two",
			"2 ≤ N",
			By(large, tolerance.At(N)))
		Npositive := arg.Have(
			"the index is positive",
			"0 < N",
			ByArith(Nbig))
		basePartial := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «partial»(a, N, z)")
		shiftedPartial := arg.TermAs[Fun[Complex, Complex]]("«shiftedPartial»(N)")
		toUniverse := arg.Have(
			"translation always lands in the complex plane",
			"∀z:complex. z ∈ 𝕌 ⇒ z + w ∈ 𝕌",
			Derive(func(b *Argument) {
				b.FixAs[Complex]("z")
				b.Assume()
				b.Show(
					"the translated point is complex",
					By(set_basic.InUniv.At(b.TermAs[Complex]("z + w"))))
			}))
		composed := arg.Have(
			"translate the entire partial sum",
			"holomorphic_on(𝕌, (λz:complex. «partial»(a, N, z)) ∘ (λz:complex. z + w))",
			By(
				entireTranslation,
				toUniverse,
				dirichlet_series.PartialSumHolomorphic.At(a, N),
				complex_derivative.HolomorphicOnCompose.At(universe, universe, basePartial, translation)))
		pHol := arg.Simplified(composed, Fwd(functions.ComposeApply))
		qF := arg.TermAs[Fun[Complex, Complex]]("«numerator»(«shiftedF», R, N)")
		qP := arg.TermAs[Fun[Complex, Complex]]("«numerator»(«shiftedPartial»(N), R, N)")
		fWeight := arg.TermAs[Fun[Complex, Complex]]("«weightedKernel»(«shiftedF», R, N)")
		pWeight := arg.TermAs[Fun[Complex, Complex]]("«weightedKernel»(«shiftedPartial»(N), R, N)")
		arc := arg.TermAs[Fun[Real, Complex]]("circle_path(&0, R)")
		velocity := arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &R * exp(complex_i * &t)")
		α := arg.TermAs[Real]("-(pi / &2)")
		β := arg.TermAs[Real]("pi / &2")
		χ := arg.TermAs[Real]("&3 * pi / &2")
		fNumerator := arg.Have(
			"the weighted numerator from F is holomorphic and has value F(w) at zero",
			"holomorphic_on(«rectangle»(D), «numerator»(«shiftedF», R, N)) ∧ "+
				"«numerator»(«shiftedF», R, N, complex_of_real(&0)) = F(w)",
			ByArith(fHol, Npositive, NewmanWeightedNumerator.At(shiftedF, V, R, N)))
		disc := arg.TermAs[Set[Complex]]("«disc»(complex_of_real(&0), R + &1)")
		pNumerator := arg.Have(
			"the weighted numerator from the partial sum is holomorphic on the disc",
			"holomorphic_on(«disc»(complex_of_real(&0), R + &1), «numerator»(«shiftedPartial»(N), R, N)) ∧ "+
				"«numerator»(«shiftedPartial»(N), R, N, complex_of_real(&0)) = «partial»(a, N, w)",
			ByArith(
				pHol,
				Npositive,
				NewmanWeightedNumerator.At(shiftedPartial, universe, R, N),
				set_order.SubsetUniv.At(disc),
				complex_derivative.HolomorphicOnSubset.At(universe, disc, qP)))
		noZero := arg.Have(
			"the circle of radius R misses zero",
			"∀t:real. circle_path(&0, R, t) ≠ &0",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Show(
					"its distance from zero is R",
					ByArith(
						radiusPos,
						path_integral.CirclePathModulus.At(R, t),
						complex_abs.AbsEqZero.At(b.TermAs[Complex]("circle_path(&0, R, t)"))))
			}))
		ordered := arg.Have(
			"both arc parameter intervals are ordered",
			"-(pi / &2) ≤ pi / &2 ∧ pi / &2 ≤ &3 * pi / &2 ∧ &0 ≤ &1",
			ByArith(real_trigonometry.PiBounds))
		rightWeighted := arg.Have(
			"replace the right arc quotient by the F kernel integrand",
			"«arcInt»(λz:complex. «numerator»(«shiftedF», R, N, z) / z, R, -(pi / &2), pi / &2) = "+
				"«arcInt»(«weightedKernel»(«shiftedF», R, N), R, -(pi / &2), pi / &2)",
			By(ordered, noZero, NewmanPathWeight.At(shiftedF, R, N, arc, velocity, α, β)))
		pRightWeighted := arg.Have(
			"replace the right arc quotient by the partial sum kernel integrand",
			"«arcInt»(λz:complex. «numerator»(«shiftedPartial»(N), R, N, z) / z, R, -(pi / &2), pi / &2) = "+
				"«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, -(pi / &2), pi / &2)",
			By(ordered, noZero, NewmanPathWeight.At(shiftedPartial, R, N, arc, velocity, α, β)))
		pLeftWeighted := arg.Have(
			"replace the left arc quotient by the partial sum kernel integrand",
			"«arcInt»(λz:complex. «numerator»(«shiftedPartial»(N), R, N, z) / z, R, pi / &2, &3 * pi / &2) = "+
				"«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, pi / &2, &3 * pi / &2)",
			By(ordered, noZero, NewmanPathWeight.At(shiftedPartial, R, N, arc, velocity, β, χ)))
		topWeighted := arg.Have(
			"the same quotient identity holds on the top side",
			"«segInt»(λz:complex. «numerator»(«shiftedF», R, N, z) / z, "+
				"    complex_i * &R, "+
				"    -&δ + complex_i * &R) = "+
				"«segInt»(«weightedKernel»(«shiftedF», R, N), complex_i * &R, -&δ + complex_i * &R)",
			By(
				ordered,
				radiusPos,
				deltaPos,
				LeftSidesInBox,
				NewmanPathWeight.At(
					shiftedF, R, N,
					arg.TermAs[Fun[Real, Complex]]("segment_path(complex_i * &R, -&δ + complex_i * &R)"),
					arg.TermAs[Fun[Real, Complex]]("λt:real. (-&δ + complex_i * &R) - complex_i * &R"),
					rzero, rone)))
		leftSideWeighted := arg.Have(
			"the same quotient identity holds on the left side",
			"«segInt»(λz:complex. «numerator»(«shiftedF», R, N, z) / z, "+
				"    -&δ + complex_i * &R, "+
				"    -&δ - complex_i * &R) = "+
				"«segInt»(«weightedKernel»(«shiftedF», R, N), -&δ + complex_i * &R, -&δ - complex_i * &R)",
			By(
				ordered,
				radiusPos,
				deltaPos,
				LeftSidesInBox,
				NewmanPathWeight.At(
					shiftedF, R, N,
					arg.TermAs[Fun[Real, Complex]]("segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R)"),
					arg.TermAs[Fun[Real, Complex]]("λt:real. (-&δ - complex_i * &R) - (-&δ + complex_i * &R)"),
					rzero, rone)))
		bottomWeighted := arg.Have(
			"the same quotient identity holds on the bottom side",
			"«segInt»(λz:complex. «numerator»(«shiftedF», R, N, z) / z, "+
				"    -&δ - complex_i * &R, "+
				"    -(complex_i * &R)) = "+
				"«segInt»(«weightedKernel»(«shiftedF», R, N), -&δ - complex_i * &R, -(complex_i * &R))",
			By(
				ordered,
				radiusPos,
				deltaPos,
				LeftSidesInBox,
				NewmanPathWeight.At(
					shiftedF, R, N,
					arg.TermAs[Fun[Real, Complex]]("segment_path(-&δ - complex_i * &R, -(complex_i * &R))"),
					arg.TermAs[Fun[Real, Complex]]("λt:real. -(complex_i * &R) - (-&δ - complex_i * &R)"),
					rzero, rone)))
		fFormula := arg.Have(
			"Cauchy's formula on the rectangular-left contour gives F(w)",
			"«arcInt»(«weightedKernel»(«shiftedF», R, N), R, -(pi / &2), pi / &2) + "+
				"«sidesInt»(«weightedKernel»(«shiftedF», R, N), R, δ) = "+
				"&(&2 * pi) * complex_i * F(w)",
			Simp(Rev(rightWeighted), Rev(topWeighted), Rev(leftSideWeighted), Rev(bottomWeighted)),
			By(radiusPos, deltaPos, inside, rectangle, fNumerator, ContourFormula.At(qF, V, R, δ)))
		pFormula := arg.Have(
			"Cauchy's formula on the circle gives the partial sum",
			"«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, -(pi / &2), pi / &2) + "+
				"«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, pi / &2, &3 * pi / &2) = "+
				"&(&2 * pi) * complex_i * «partial»(a, N, w)",
			Simp(Rev(pRightWeighted), Rev(pLeftWeighted)),
			ByArith(radiusPos, pNumerator, CircleFormula.At(qP, R, rho)))
		weight := arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&N, z)")
		kernel := arg.TermAs[Fun[Complex, Complex]]("λz:complex. «kernel»(R, z)")
		weightHol := arg.Have(
			"the weight is entire",
			"holomorphic_on(𝕌, λz:complex. complex_cpow(&N, z))",
			ByArith(Npositive, complex_cpow.CpowHolomorphicExponent.At(arg.TermAs[Real]("&N"))))
		factors := arg.Have(
			"the weight N^z and the kernel are continuous at every point of the circle",
			"∀t:real. "+
				"    complex_continuous_at(λx:complex. complex_cpow(&N, x), circle_path(&0, R, t)) ∧ "+
				"    complex_continuous_at(λx:complex. «kernel»(R, x), circle_path(&0, R, t))",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				z := b.TermAs[Complex]("circle_path(&0, R, t)")
				b.Show(
					"the weight is entire and the kernel is continuous away from zero",
					By(
						noZero.At(t),
						weightHol,
						set_basic.InUniv.At(z),
						complex_derivative.HolomorphicOnContinuousAt.At(universe, weight, z),
						KernelContinuousAt.At(R, z)))
			}))
		fArcCont := arg.Have(
			"the F integrand is continuous at the points of the right arc, which lie in the rectangle",
			Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"-(pi / &2) ≤ t",
					"t ≤ pi / &2",
				},
				Conclusion: "complex_continuous_at(«weightedKernel»(«shiftedF», R, N), circle_path(&0, R, t))",
			},
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				interval := b.Assume()
				z := b.TermAs[Complex]("circle_path(&0, R, t)")
				inV := b.Have(
					"the right arc point lies in the rectangle",
					"circle_path(&0, R, t) ∈ «rectangle»(D)",
					ByArith(interval, radiusPos, deltaPos, RightArcInBox.At(R, t), inside.At(z)))
				b.Show(
					"F translated, the weight and the kernel are continuous there",
					By(
						inV,
						fHol,
						complex_derivative.HolomorphicOnContinuousAt.At(V, shiftedF, z),
						factors.At(t),
						complex_topology.ContinuousAtMul.At(shiftedF, weight, z),
						complex_topology.ContinuousAtMul.At(
							b.TermAs[Fun[Complex, Complex]]("λx:complex. «shiftedF»(x) * complex_cpow(&N, x)"), kernel, z)))
			}))
		pArcCont := arg.Have(
			"the partial sum integrand is continuous at the points of the right arc",
			Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"-(pi / &2) ≤ t",
					"t ≤ pi / &2",
				},
				Conclusion: "complex_continuous_at(«weightedKernel»(«shiftedPartial»(N), R, N), " +
					"    circle_path(&0, R, t))",
			},
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Assume()
				z := b.TermAs[Complex]("circle_path(&0, R, t)")
				b.Show(
					"the translated partial sum is entire, and the weight and the kernel are continuous there",
					By(
						pHol,
						set_basic.InUniv.At(z),
						complex_derivative.HolomorphicOnContinuousAt.At(universe, shiftedPartial, z),
						factors.At(t),
						complex_topology.ContinuousAtMul.At(shiftedPartial, weight, z),
						complex_topology.ContinuousAtMul.At(
							b.TermAs[Fun[Complex, Complex]]("λx:complex. «shiftedPartial»(N, x) * complex_cpow(&N, x)"),
							kernel,
							z)))
			}))
		diffForm := arg.Have(
			"the difference of the weighted integrands factors",
			"(λz:complex. "+
				"    «weightedKernel»(«shiftedF», R, N, z) - «weightedKernel»(«shiftedPartial»(N), R, N, z)) = "+
				"(λz:complex. («shiftedF»(z) - «shiftedPartial»(N, z)) * complex_cpow(&N, z) * «kernel»(R, z))",
			Funext(),
			StripQuant(),
			ByArith())
		arcDifference := arg.Have(
			"the difference of the right arc integrals is the integral of the difference",
			"«arcInt»(«weightedKernel»(«shiftedF», R, N), R, -(pi / &2), pi / &2) - "+
				"«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, -(pi / &2), pi / &2) = "+
				"«arcInt»(λz:complex. "+
				"        («shiftedF»(z) - «shiftedPartial»(N, z)) * complex_cpow(&N, z) * «kernel»(R, z), "+
				"    R, "+
				"    -(pi / &2), "+
				"    pi / &2)",
			diffForm.RwRev(),
			By(
				ordered,
				fArcCont,
				pArcCont,
				path_integral.CircleArcPiecewiseSmooth.At(zero, R, α, β),
				path_integral.PathIntegralSub.At(fWeight, pWeight, arc, velocity, α, β)))
		rightSums := arg.Have(
			"F agrees with the shifted series at the shifted points of the open right arc",
			"∀z:complex. |z| = R ∧ &0 < re(z) ⇒ dirichlet_sums(a, z + w, F(z + w))",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				onArc := b.Assume()
				b.Show(
					"the shift lies strictly to the right of one",
					ByArith(onArc, shift, complex_field.PartsAdd.At(z, w), sums.At(b.TermAs[Complex]("z + w"))))
			}))
		rightFCont := arg.Have(
			"F is continuous at every shifted point on the right arc",
			"∀z:complex. |z| = R ∧ &0 ≤ re(z) ⇒ complex_continuous_at(F, z + w)",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				onArc := b.Assume()
				s := b.TermAs[Complex]("z + w")
				inU := b.Have(
					"the shifted point is in the closed half-plane",
					"z + w ∈ U",
					ByArith(onArc, shift, complex_field.PartsAdd.At(z, w), halfPlane.At(s)))
				b.Show(
					"holomorphy gives continuity at that point",
					By(inU, holomorphic, complex_derivative.HolomorphicOnContinuousAt.At(U, F, s)))
			}))
		sideForm := arg.Have(
			"the order of the weight and the kernel on the sides can be interchanged",
			"(λz:complex. «sideF»(z) * complex_cpow(&N, z)) = «weightedKernel»(«shiftedF», R, N)",
			Funext(),
			StripQuant(),
			ByArith())
		_, rightDef := arg.LetAs[Complex](
			"rightArc",
			"«arcInt»(λz:complex. "+
				"        («shiftedF»(z) - «shiftedPartial»(N, z)) * complex_cpow(&N, z) * «kernel»(R, z), "+
				"    R, "+
				"    -(pi / &2), "+
				"    pi / &2)")
		_, sideDef := arg.LetAs[Complex]("sides", "«sidesInt»(«weightedKernel»(«shiftedF», R, N), R, δ)")
		_, leftDef := arg.LetAs[Complex](
			"leftArc", "«arcInt»(«weightedKernel»(«shiftedPartial»(N), R, N), R, pi / &2, &3 * pi / &2)")
		rightBound := arg.Have(
			"the right arc contributes at most twice pi B over R",
			"|rightArc| ≤ &2 * pi * B / R",
			rightDef.Rw(),
			By(rightSums, rightFCont, bounded, shift, radiusPos, Npositive, RightArcBound.At(a, B, R, F, w, N)))
		leftBound := arg.Have(
			"the left arc has the bound for the finite partial sum",
			"|leftArc| ≤ &2 * pi * B * (&1 / &N + &1 / R)",
			leftDef.Rw(),
			By(bounded, shift, radiusPos, Npositive, LeftArcBound.At(a, B, R, w, N)))
		sideBound := arg.Have(
			"the contributions of the three sides have the decaying bound",
			"|sides| ≤ M * (&2 / log(&N) + &2 * R * real_rpow(&N, -δ))",
			sideDef.Rw(),
			sideForm.RwRev(),
			By(radiusPos, deltaPos, Nbig, sideContin, sideSize, LeftSidesBound.At(sideF, M, R, δ, N)))
		contour := arg.Have(
			"subtract the circle formula from the contour formula",
			"&(&2 * pi) * complex_i * (F(w) - «partial»(a, N, w)) = rightArc + sides + -leftArc",
			ByArith(fFormula, pFormula, arcDifference))
		multiplier := arg.Have(
			"the complex multiplier has modulus twice pi",
			"|&(&2 * pi) * complex_i| = &2 * pi",
			ByArith(
				real_trigonometry.PiBounds,
				complex_abs.AbsI,
				complex_abs.AbsOfReal.At(arg.TermAs[Real]("&2 * pi")),
				complex_abs.AbsMul.At(arg.TermAs[Complex]("&(&2 * pi)"), arg.TermAs[Complex]("complex_i"))))
		estimate := arg.Have(
			"the triangle inequality and the three estimates bound 2π times the error",
			"&2 * pi * |F(w) - «partial»(a, N, w)| ≤ "+
				"&2 * "+
				"pi * "+
				"(&2 * B / R + (B * (&1 / &N) + (M / pi) * (&1 / log(&N)) + (M * R / pi) * real_rpow(&N, -δ)))",
			real_order_ring.OrderCalc(arg.Ctx()).CalcLeibniz(
				arg.TermAs[Real]("&2 * pi * |F(w) - «partial»(a, N, w)|"),
				EqLeg(
					arg.TermAs[Real]("|&(&2 * pi) * complex_i * (F(w) - «partial»(a, N, w))|"),
					"2π is the modulus of the multiplier 2πi",
					By(
						multiplier,
						complex_abs.AbsMul.At(
							arg.TermAs[Complex]("&(&2 * pi) * complex_i"), arg.TermAs[Complex]("F(w) - «partial»(a, N, w)")))),
				EqLeg(
					arg.TermAs[Real]("|rightArc + sides + -leftArc|"),
					"the difference of the two formulas",
					By(contour)),
				LeLeg(
					arg.TermAs[Real]("|rightArc| + |sides| + |leftArc|"),
					"the triangle inequality",
					ByArith(
						complex_abs.AbsTriangle.At(
							arg.TermAs[Complex]("rightArc + sides"), arg.TermAs[Complex]("-leftArc")),
						complex_abs.AbsTriangle.At(arg.TermAs[Complex]("rightArc"), arg.TermAs[Complex]("sides")),
						complex_abs.AbsNeg.At(arg.TermAs[Complex]("leftArc")))),
				LeLeg(
					arg.TermAs[Real]("&2 * pi * B / R + "+
						"M * (&2 / log(&N) + &2 * R * real_rpow(&N, -δ)) + "+
						"&2 * pi * B * (&1 / &N + &1 / R)"),
					"the estimates on the right arc, the sides and the left arc",
					ByArith(rightBound, sideBound, leftBound)),
				EqLeg(
					arg.TermAs[Real]("&2 * "+
						"pi * "+
						"(&2 * B / R + (B * (&1 / &N) + (M / pi) * (&1 / log(&N)) + (M * R / pi) * real_rpow(&N, -δ)))"),
					"take out the factor 2π",
					ByArith(real_trigonometry.PiBounds))))
		arg.Show(
			"divided by 2π, the error is at most 2B/R plus the decaying terms, which fit within B/R past K",
			ByArith(estimate, real_trigonometry.PiBounds, large, tolerance.At(N)))
	}),
	Reading: "R is fixed first and N then taken large: the bound on the " +
		"sides depends on R through M and δ, the bounds on the arcs do not.",
})}

// NewmanTauberian — a Dirichlet series with bounded coefficients whose sum
// on Re s > 1 continues holomorphically to an open set containing
// Re s ≥ 1 converges at every point of that closed half-plane, to the
// continuation.
var NewmanTauberian = newmanTauberianThm{family.Add(registry.ProofEntry{
	Name: "NewmanTauberian",
	Key:  "prop_2540737efab12cf4",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀U:set(complex). ∀F:(complex → complex). ∀w:complex.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"U ∈ complex_topology",
			"∀s:complex. &1 ≤ re(s) ⇒ s ∈ U",
			"holomorphic_on(U, F)",
			"∀s:complex. &1 < re(s) ⇒ dirichlet_sums(a, s, F(s))",
			"&1 ≤ re(w)",
		},
		Conclusion: "dirichlet_sums(a, w, F(w))",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			B *Expr[Real],
			U *Expr[Set[Complex]],
			F *Arrow[Complex, Complex],
			w *Expr[Complex],
			bounded, open, halfPlane, holomorphic, sums, shift Fact,
		) {
			C, raised := arg.LetAs[Real]("C", "B + &1")
			looser := arg.Have(
				"C = B + 1 bounds the coefficients as well",
				"∀n:num. |a(n)| ≤ C",
				arg.ForEach(func(n *Expr[Nat]) Action { return ByArith(raised, bounded.At(n)) }))
			positiveBound := arg.Have(
				"and C is positive, B bounding |a(0)|",
				"&0 < C",
				ByArith(
					raised,
					bounded.At(arg.TermAs[Nat]("0")),
					complex_abs.AbsNonneg.At(a.Apply(arg.TermAs[Nat]("0")))))
			limit := arg.Have(
				"the partial sums tend to the continuation's value at w",
				"(λN:num. Σ_{k∈0 .. N} a(k + 1) * complex_cpow(&(k + 1), -w)) ⟶ F(w)",
				Simp(Fwd(complex_topology.ComplexConvergesToDef)),
				Derive(func(b *Argument) {
					b.FixAs[Real]("ε")
					positive := b.Assume()
					R := b.TermAs[Real]("&1 + &3 * C / ε")
					radius := b.Have(
						"the chosen radius is positive and makes the error smaller than ε",
						"&0 < &1 + &3 * C / ε ∧ &3 * C / (&1 + &3 * C / ε) < ε",
						ByArith(positiveBound, positive))
					K, estimates := b.Obtain(
						"Newman's estimate at the bound C controls every partial sum from K onward",
						"∃K:num. ∀N:num. K ≤ N ⇒ |F(w) - «partial»(a, N, w)| ≤ &3 * C / (&1 + &3 * C / ε)",
						By(
							looser,
							positiveBound,
							open,
							halfPlane,
							holomorphic,
							sums,
							shift,
							radius,
							NewmanApproximation.At(a, C, R, U, F, w)))
					b.Take(K)
					n := b.FixAs[Nat]("n")
					late := b.Assume()
					next := b.TermAs[Nat]("n + 1")
					addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
					shifted := b.Have(
						"the sum over 0..n of shifted terms is the sum over 1..n+1",
						"Σ_{k∈0 .. n} a(k + 1) * complex_cpow(&(k + 1), -w) = «partial»(a, n + 1, w)",
						By(monoidal.Shift.Read(addition).At(
							b.TermAs[Nat]("0"), n, b.TermAs[Nat]("1"),
							b.TermAs[Fun[Nat, Complex]]("λk:num. a(k) * complex_cpow(&k, -w)"))))
					nextLate := b.Have(
						"n + 1 is also past the cutoff",
						"K ≤ n + 1",
						ByArith(late))
					b.Show(
						"the estimate puts this partial sum strictly within ε of F(w)",
						ByArith(
							nextLate,
							estimates.At(next),
							shifted,
							radius,
							complex_abs.AbsSubComm.At(
								b.TermAs[Complex]("«partial»(a, n + 1, w)"), F.Apply(w))))
				}))
			arg.Show(
				"the Dirichlet series sums to the limit of its partial sums",
				Unfold(dirichlet_series.DirichletSumsDef),
				By(
					limit,
					complex_series.SumsIffPartialSums.At(
						arg.TermAs[Fun[Nat, Complex]]("λk:num. a(k + 1) * complex_cpow(&(k + 1), -w)"), F.Apply(w))))
		}),
	Reading: "The coefficients are bounded, not merely of bounded average, and the continuation " +
		"is to an open set containing the closed half-plane, of no prescribed shape. The conclusion " +
		"on the line Re s = 1 is the new information; for Re s > 1 it is a hypothesis.",
})}
