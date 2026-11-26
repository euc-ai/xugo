// circle.go — t ↦ (cos t, sin t) as a map of the line onto the unit
// circle: both are continuous, as maps of the line and so on every set,
// the sine is positive on ⟬0, π⟭, every integer multiple of 2π is a
// period, the subtraction formulas, the two take the same values at s
// and t exactly when s − t is an integer multiple of 2π, so at no two
// angles of ⟬−π, π⟧, and every point of the circle is reached from
// ⟦0, 2π⟭.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// CosContinuous — the cosine is a continuous map of the line to itself:
// having a derivative at every point, it is continuous at every point.
var CosContinuous = cosContinuousThm{family.Add(registry.ProofEntry{
	Name: "CosContinuous",
	Key:  "prop_dbb7470e96042fd7",
	Build: family.Theorem("continuous_map(real_topology, real_topology, real_cos)",
		func(arg *Argument) {
			cos := arg.TermAs[Fun[Real, Real]]("real_cos")
			pointwise := arg.Have(
				"the cosine is continuous at every point, having a derivative there",
				"∀c:real. real_continuous_at(real_cos, c)",
				arg.ForEach(func(c *Expr[Real]) Action {
					return By(CosDerivative.At(c), real_derivative.DerivativeContinuous)
				}))
			arg.Show(
				"a function continuous at every point is a continuous map of the line",
				By(pointwise, real_continuous.ContinuousMapIffPointwise.At(cos)))
		}),
})}

// SinContinuous — the sine is a continuous map of the line to itself,
// as the cosine is.
var SinContinuous = sinContinuousThm{family.Add(registry.ProofEntry{
	Name: "SinContinuous",
	Key:  "prop_7e9c728de2c12578",
	Build: family.Theorem("continuous_map(real_topology, real_topology, real_sin)",
		func(arg *Argument) {
			sin := arg.TermAs[Fun[Real, Real]]("real_sin")
			pointwise := arg.Have(
				"the sine is continuous at every point, having a derivative there",
				"∀c:real. real_continuous_at(real_sin, c)",
				arg.ForEach(func(c *Expr[Real]) Action {
					return By(SinDerivative.At(c), real_derivative.DerivativeContinuous)
				}))
			arg.Show(
				"a function continuous at every point is a continuous map of the line",
				By(pointwise, real_continuous.ContinuousMapIffPointwise.At(sin)))
		}),
})}

// SinContinuousOn — the sine is continuous on every set of reals: a
// continuous map of the line, it is continuous at every point.
var SinContinuousOn = sinContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "SinContinuousOn",
	Key:  "prop_f5ba71fd74d362d5",
	Build: family.Theorem("∀s:set(real). real_continuous_on(s, real_sin)",
		func(arg *Argument, s *Expr[Set[Real]]) {
			sin := arg.TermAs[Fun[Real, Real]]("real_sin")
			arg.Show(
				"a continuous map of the line is continuous at every point, so on every set",
				By(
					SinContinuous,
					real_continuous.ContinuousMapIffPointwise.At(sin),
					real_continuous.ContinuousAtOn.At(sin, s)))
		}),
})}

// CosContinuousOn — the cosine is continuous on every set of reals: a
// continuous map of the line, it is continuous at every point.
var CosContinuousOn = cosContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "CosContinuousOn",
	Key:  "prop_50e1abc0ae67baca",
	Build: family.Theorem("∀s:set(real). real_continuous_on(s, real_cos)",
		func(arg *Argument, s *Expr[Set[Real]]) {
			cos := arg.TermAs[Fun[Real, Real]]("real_cos")
			arg.Show(
				"a continuous map of the line is continuous at every point, so on every set",
				By(
					CosContinuous,
					real_continuous.ContinuousMapIffPointwise.At(cos),
					real_continuous.ContinuousAtOn.At(cos, s)))
		}),
})}

// SinPositivePi — the sine is positive on ⟬0, π⟭. Below 2 it is, by the
// Taylor bound; from 2 on, the sine is symmetric about π/2,
// sin x = sin(π − x), and π − x lies in ⟬0, π − 2⟧, inside ⟬0, 2⟭ as
// π < 4.
var SinPositivePi = sinPositivePiThm{family.Add(registry.ProofEntry{
	Name: "SinPositivePi",
	Key:  "prop_40843c385e51d5e3",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
			"x < pi",
		},
		Conclusion: "&0 < sin(x)",
	},
		func(arg *Argument, x *Expr[Real], within Fact) {
			fromTwo := arg.Unless(
				arg.Term("x < &2"),
				"below 2 the sine is positive",
				Given(func(b *Argument, below Fact) {
					b.Show(
						"x lies in ⟬0, 2⟭",
						By(below, within, SinPositive.At(x)))
				}))
			reflect := arg.Have(
				"π − x is −x + π",
				"pi - x = -x + pi",
				ByArith())
			mirror := arg.Have(
				"so sin(π − x) = sin(−x + π) = −sin(−x) = sin x",
				"sin(pi - x) = sin(x)",
				ByArith(reflect, SinAddPi.At(arg.TermAs[Real]("-x")), SinNeg.At(x)))
			arg.Show(
				"π − x lies in ⟬0, π − 2⟧, inside ⟬0, 2⟭ as π < 4, where the sine is positive",
				ByArith(fromTwo, within, mirror, PiBounds, SinPositive.At(arg.TermAs[Real]("pi - x"))))
		}),
})}

// CosPeriodicInteger — every integer multiple of 2π is a period of the cosine.
// A natural multiple is, by induction, one period more at each step; and
// x is x + 2πk moved on by 2π·(−k), a natural multiple when k is negative.
var CosPeriodicInteger = cosPeriodicIntegerThm{family.Add(registry.ProofEntry{
	Name: "CosPeriodicInteger",
	Key:  "prop_d0142d26fc64c57c",
	Build: family.Theorem(Statement{
		Binders: "∀x k:real.",
		Hypotheses: []string{
			"integer(k)",
		},
		Conclusion: "cos(x + &2 * pi * k) = cos(x)",
	},
		func(arg *Argument, x, k *Expr[Real], isInteger Fact) {
			natural := arg.Have(
				"every natural multiple of 2π is a period, one period more at each step",
				"∀y:real. ∀n:num. cos(y + &2 * pi * &n) = cos(y)",
				Derive(func(d *Argument) {
					d.FixAs[Real]("y")
					d.Induct("n")
					d.Base(
						"no period at all moves nothing",
						ByArith())
					d.Step(
						"one period more: cos(y + 2π(n + 1)) = cos(y + 2πn) = cos y",
						func(b *Argument, ih Fact) {
							n := b.TermAs[Nat]("n")
							more := b.Have(
								"y + 2π(n + 1) is (y + 2πn) + 2π",
								"y + &2 * pi * &suc(n) = y + &2 * pi * &n + &2 * pi",
								ByArith(Scaled(b.TermAs[Real]("pi"), real_ring.OfNumSuc.At(n))))
							b.Show(
								"a period more moves nothing",
								ByArith(ih, more, CosPeriodic.At(b.TermAs[Real]("y + &2 * pi * &n"))))
						})
				}))
			n, sign := arg.Obtain(
				"k is a natural number n or its negative",
				"∃n:num. k = &n ∨ k = -&n",
				By(isInteger, int_construction.IntegerIffPlusMinusNat.At(k)))
			arg.Do(sign.SplitDisj(
				LeftHolds(
					"k = n: 2πk is a natural multiple of 2π",
					Given(func(b *Argument, nonnegative Fact) {
						b.Show(
							"a natural multiple is a period",
							By(Normalized, nonnegative, natural.At(x, n)))
					})),
				RightHolds(
					"k = −n: x is x + 2πk moved on by the natural multiple 2πn",
					Given(func(b *Argument, negative Fact) {
						back := b.Have(
							"x + 2πk + 2πn is x",
							"x + &2 * pi * k + &2 * pi * &n = x",
							ByArith(Scaled(b.TermAs[Real]("pi"), negative)))
						b.Show(
							"cos x = cos((x + 2πk) + 2πn) = cos(x + 2πk)",
							By(Normalized, back, natural.At(b.TermAs[Real]("x + &2 * pi * k"), n)))
					}))))
		}),
})}

// SinPeriodicInteger — every integer multiple of 2π is a period of the sine.
// A natural multiple is, by induction, one period more at each step; and
// x is x + 2πk moved on by 2π·(−k), a natural multiple when k is negative.
var SinPeriodicInteger = sinPeriodicIntegerThm{family.Add(registry.ProofEntry{
	Name: "SinPeriodicInteger",
	Key:  "prop_9c84773f00a671ab",
	Build: family.Theorem(Statement{
		Binders: "∀x k:real.",
		Hypotheses: []string{
			"integer(k)",
		},
		Conclusion: "sin(x + &2 * pi * k) = sin(x)",
	},
		func(arg *Argument, x, k *Expr[Real], isInteger Fact) {
			natural := arg.Have(
				"every natural multiple of 2π is a period, one period more at each step",
				"∀y:real. ∀n:num. sin(y + &2 * pi * &n) = sin(y)",
				Derive(func(d *Argument) {
					d.FixAs[Real]("y")
					d.Induct("n")
					d.Base(
						"no period at all moves nothing",
						ByArith())
					d.Step(
						"one period more: sin(y + 2π(n + 1)) = sin(y + 2πn) = sin y",
						func(b *Argument, ih Fact) {
							n := b.TermAs[Nat]("n")
							more := b.Have(
								"y + 2π(n + 1) is (y + 2πn) + 2π",
								"y + &2 * pi * &suc(n) = y + &2 * pi * &n + &2 * pi",
								ByArith(Scaled(b.TermAs[Real]("pi"), real_ring.OfNumSuc.At(n))))
							b.Show(
								"a period more moves nothing",
								ByArith(ih, more, SinPeriodic.At(b.TermAs[Real]("y + &2 * pi * &n"))))
						})
				}))
			n, sign := arg.Obtain(
				"k is a natural number n or its negative",
				"∃n:num. k = &n ∨ k = -&n",
				By(isInteger, int_construction.IntegerIffPlusMinusNat.At(k)))
			arg.Do(sign.SplitDisj(
				LeftHolds(
					"k = n: 2πk is a natural multiple of 2π",
					Given(func(b *Argument, nonnegative Fact) {
						b.Show(
							"a natural multiple is a period",
							By(Normalized, nonnegative, natural.At(x, n)))
					})),
				RightHolds(
					"k = −n: x is x + 2πk moved on by the natural multiple 2πn",
					Given(func(b *Argument, negative Fact) {
						back := b.Have(
							"x + 2πk + 2πn is x",
							"x + &2 * pi * k + &2 * pi * &n = x",
							ByArith(Scaled(b.TermAs[Real]("pi"), negative)))
						b.Show(
							"sin x = sin((x + 2πk) + 2πn) = sin(x + 2πk)",
							By(Normalized, back, natural.At(b.TermAs[Real]("x + &2 * pi * k"), n)))
					}))))
		}),
})}

// CosOneSinZeroIff — the cosine is 1 and the sine 0 exactly at the
// integer multiples of 2π. At 2πk, a period, they are cos 0 and sin 0.
// Conversely, with m the integer part of x/(2π), write x = 2h + 2πm with
// 0 ≤ h < π: then 1 = cos x = cos 2h = 1 − 2·sin²h, and sin h > 0 were
// h > 0, so h = 0 and x/(2π) is the integer m.
var CosOneSinZeroIff = cosOneSinZeroIffThm{family.Add(registry.ProofEntry{
	Name: "CosOneSinZeroIff",
	Key:  "prop_d1a16ea655af982a",
	Build: family.Theorem("∀x:real. cos(x) = &1 ∧ sin(x) = &0 ⇔ integer(x / (&2 * pi))",
		func(arg *Argument, x *Expr[Real]) {
			k := arg.TermAs[Real]("x / (&2 * pi)")
			multiple := arg.Have(
				"x is 2π times x/(2π)",
				"&2 * pi * (x / (&2 * pi)) = x",
				ByArith(PiBounds))
			arg.Iff()
			arg.Backward(
				"at an integer multiple of 2π the cosine and the sine take their values at 0",
				func(b *Argument, isInteger Fact) {
					zero := b.TermAs[Real]("&0")
					b.Show(
						"cos x = cos(0 + 2π·x/(2π)) = cos 0 = 1, and sin x = sin 0 = 0 likewise",
						ByArith(
							isInteger,
							multiple,
							At(CosPeriodicInteger, zero, k),
							At(SinPeriodicInteger, zero, k),
							CosZero,
							SinZero))
				})
			arg.Forward(
				"where the cosine is 1, x is 2πm with m the integer part of x/(2π)",
				func(b *Argument, atOne Fact) {
					m, part := b.UnpackAs[Real](rational.IntegerPart.At(k))
					parts := b.Conjuncts(
						part,
						"m is an integer",
						"m ≤ x/(2π)",
						"x/(2π) < m + 1")
					isInteger, below, above := parts[0], parts[1], parts[2]
					h, hDef := b.LetAs[Real]("h", "x / &2 - pi * m")
					bounds := b.Have(
						"0 ≤ h < π, as 2πm ≤ x < 2πm + 2π",
						"&0 ≤ h ∧ h < pi",
						ByArith(hDef, multiple, below, above, PiBounds))
					split := b.Have(
						"x is 2h + 2πm",
						"h + h + &2 * pi * m = x",
						ByArith(hDef))
					double := b.Have(
						"cos 2h = cos x = 1, 2πm being a period",
						"cos(h + h) = &1",
						By(Normalized, isInteger, split, atOne, At(CosPeriodicInteger, b.TermAs[Real]("h + h"), m)))
					notPositive := b.Unless(
						b.Term("&0 < h"),
						"h > 0 is excluded: sin h > 0 on ⟬0, π⟭, so cos 2h = 1 − 2·sin²h < 1",
						Given(func(c *Argument, positive Fact) {
							c.Show(
								"cos 2h = cos²h − sin²h = 1 − 2·sin²h, and sin h > 0",
								ByArith(
									double,
									positive,
									bounds,
									CosAdd.At(h, h),
									SinSquareAddCosSquare.At(h),
									At(SinPositivePi, h)))
						}))
					atM := b.Have(
						"so h = 0, x = 2πm and x/(2π) = m",
						"x / (&2 * pi) = m",
						ByArith(notPositive, split, bounds, PiBounds))
					b.Show(
						"which is an integer",
						By(Normalized, isInteger, atM))
				})
		}),
})}

// CosSub — the subtraction formula for the cosine: the addition formula
// at x and −y, where the cosine is even and the sine odd.
var CosSub = cosSubThm{family.Add(registry.ProofEntry{
	Name: "CosSub",
	Key:  "prop_d7b2faf72c36973b",
	Build: family.Theorem("∀x y:real. cos(x - y) = cos(x) * cos(y) + sin(x) * sin(y)",
		func(arg *Argument, x, y *Expr[Real]) {
			arg.Show(
				"cos(x + (−y)) = cos x·cos(−y) − sin x·sin(−y) = cos x·cos y + sin x·sin y",
				Simp(Fwd(real_ring.RealSubDef)),
				ByArith(
					CosAdd.At(x, arg.TermAs[Real]("-y")),
					Scaled(arg.TermAs[Real]("cos(x)"), CosNeg.At(y)),
					Scaled(arg.TermAs[Real]("sin(x)"), SinNeg.At(y))))
		}),
})}

// SinSub — the subtraction formula for the sine, from the addition
// formula at x and −y in the same way.
var SinSub = sinSubThm{family.Add(registry.ProofEntry{
	Name: "SinSub",
	Key:  "prop_326b24aec589cc58",
	Build: family.Theorem("∀x y:real. sin(x - y) = sin(x) * cos(y) - cos(x) * sin(y)",
		func(arg *Argument, x, y *Expr[Real]) {
			arg.Show(
				"sin(x + (−y)) = sin x·cos(−y) + cos x·sin(−y) = sin x·cos y − cos x·sin y",
				Simp(Fwd(real_ring.RealSubDef)),
				ByArith(
					SinAdd.At(x, arg.TermAs[Real]("-y")),
					Scaled(arg.TermAs[Real]("sin(x)"), CosNeg.At(y)),
					Scaled(arg.TermAs[Real]("cos(x)"), SinNeg.At(y))))
		}),
})}

// CosSinEqIff — two reals have the same cosine and the same sine exactly
// when they differ by an integer multiple of 2π. Such a difference is a
// period of both; conversely, equal values make cos(s − t) = cos²t + sin²t = 1
// and sin(s − t) = sin t·cos t − cos t·sin t = 0 by the subtraction
// formulas, so (s − t)/(2π) is an integer.
var CosSinEqIff = cosSinEqIffThm{family.Add(registry.ProofEntry{
	Name: "CosSinEqIff",
	Key:  "prop_ce3126cd34a9cd68",
	Build: family.Theorem("∀s t:real. cos(s) = cos(t) ∧ sin(s) = sin(t) ⇔ integer((s - t) / (&2 * pi))",
		func(arg *Argument, s, t *Expr[Real]) {
			arg.Iff()
			arg.Backward(
				"s is t moved on by an integer multiple of 2π, which is a period of both",
				func(b *Argument, isInteger Fact) {
					k := b.TermAs[Real]("(s - t) / (&2 * pi)")
					shift := b.Have(
						"s is t + 2π·(s − t)/(2π)",
						"t + &2 * pi * ((s - t) / (&2 * pi)) = s",
						ByArith(PiBounds))
					b.Show(
						"cos s = cos t and sin s = sin t",
						By(Normalized, isInteger, shift, At(CosPeriodicInteger, t, k), At(SinPeriodicInteger, t, k)))
				})
			arg.Forward(
				"equal values put s − t where the cosine is 1 and the sine 0",
				func(b *Argument, equal Fact) {
					parts := b.Conjuncts(
						equal,
						"cos s = cos t",
						"sin s = sin t")
					cosEq, sinEq := parts[0], parts[1]
					cosT, sinT := b.TermAs[Real]("cos(t)"), b.TermAs[Real]("sin(t)")
					one := b.Have(
						"cos(s − t) = cos s·cos t + sin s·sin t = cos²t + sin²t = 1",
						"cos(s - t) = &1",
						ByArith(At(CosSub, s, t), Scaled(cosT, cosEq), Scaled(sinT, sinEq), SinSquareAddCosSquare.At(t)))
					zero := b.Have(
						"sin(s − t) = sin s·cos t − cos s·sin t = sin t·cos t − cos t·sin t = 0",
						"sin(s - t) = &0",
						ByArith(At(SinSub, s, t), Scaled(cosT, sinEq), Scaled(sinT, cosEq)))
					b.Show(
						"so (s − t)/(2π) is an integer",
						By(one, zero, At(CosOneSinZeroIff, b.TermAs[Real]("s - t"))))
				})
		}),
})}

// CosSinInjective — two angles of ⟬−π, π⟧ with the same cosine and sine are
// equal: their difference is 2πk for an integer k, and it lies strictly
// between −2π and 2π, so |k| < 1 and k = 0.
var CosSinInjective = cosSinInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CosSinInjective",
	Key:  "prop_ed4c08b12c9a75ae",
	Build: family.Theorem(Statement{
		Binders: "∀s t:real.",
		Hypotheses: []string{
			"-pi < s",
			"s ≤ pi",
			"-pi < t",
			"t ≤ pi",
			"cos(s) = cos(t)",
			"sin(s) = sin(t)",
		},
		Conclusion: "s = t",
	}, func(a *Argument, s, t *Expr[Real], sAbove, sBelow, tAbove, tBelow, cosEq, sinEq Fact) {
		k, kDef := a.LetAs[Real]("k", "(s - t) / (&2 * pi)")
		multiple := a.Have(
			"k is (s − t)/(2π), so 2πk = s − t",
			"&2 * pi * k = s - t",
			kDef.Rw(),
			ByArith(PiBounds))
		interval := a.Have(
			"s − t lies strictly between −2π and 2π, so k strictly between −1 and 1",
			"-&1 < k ∧ k < &1",
			ByArith(multiple, sAbove, sBelow, tAbove, tBelow, PiBounds))
		small := a.Have(
			"so k is below 1 in size",
			"|k| < &1",
			ByArith(interval))
		zero := a.Have(
			"equal cosines and sines make k an integer, so k = 0",
			"k = &0",
			By(
				Normalized,
				cosEq,
				sinEq,
				kDef,
				small,
				CosSinEqIff.At(s, t),
				int_construction.IntegerAbsLessOne.At(k)))
		a.Show(
			"so s − t = 2π·0 = 0",
			ByArith(multiple, Scaled(a.TermAs[Real]("pi"), zero)))
	}),
})}

// CircleParametrization — every point (a, b) of the unit circle is
// (cos t, sin t) for some t in ⟦0, 2π⟭. The cosine falls from 1 to −1 on
// ⟦0, π⟧ and a lies between, so it takes the value a at some t there;
// then sin²t = 1 − a² = b², and sin t is b or −b. If it is b, t is the
// point; if not, t is not 0, where the sine is 0, and 2π − t, which has
// the cosine of t and the opposite sine, is the point.
var CircleParametrization = circleParametrizationThm{family.Add(registry.ProofEntry{
	Name: "CircleParametrization",
	Key:  "prop_33403c93949676ec",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real.",
		Hypotheses: []string{
			"a * a + b * b = &1",
		},
		Conclusion: "∃t:real. &0 ≤ t ∧ t < &2 * pi ∧ cos(t) = a ∧ sin(t) = b",
	},
		func(arg *Argument, a, b *Expr[Real], unit Fact) {
			square := arg.Have(
				"a² ≤ 1, b² being nonnegative",
				"a * a ≤ &1",
				ByArith(unit))
			ends := arg.Have(
				"so a lies between cos π = −1 and cos 0 = 1",
				"&0 ≤ pi ∧ cos(pi) ≤ a ∧ a ≤ cos(&0)",
				ByArith(square, PiBounds, CosPi, CosZero))
			cosine := arg.TermAs[Fun[Real, Real]]("real_cos")
			t, found := arg.ObtainAs[Real](
				"so the cosine, continuous on ⟦0, π⟧, takes the value "+
					"a at some t there, by the intermediate value theorem",
				"∃t:real. &0 ≤ t ∧ t ≤ pi ∧ cos(t) = a",
				By(
					CosContinuousOn.At(arg.TermAs[Set[Real]]("⟦&0, pi⟧")),
					ends,
					real_continuous.IntermediateValueDecreasing.At(
						cosine, arg.TermAs[Real]("&0"), arg.TermAs[Real]("pi"), a)))
			parts := arg.Conjuncts(
				found,
				"0 ≤ t",
				"t ≤ π",
				"cos t = a")
			lower, upper, atA := parts[0], parts[1], parts[2]
			sineSquare := arg.Have(
				"sin²t = 1 − cos²t = 1 − a² = b²",
				"sin(t) * sin(t) = b * b",
				ByArith(unit, Scaled(arg.TermAs[Real]("cos(t) + a"), atA), SinSquareAddCosSquare.At(t)))
			arg.Cases(arg.Term("sin(t) = b"))
			arg.When(
				"sin t = b: t itself is the point",
				func(c *Argument, atB Fact) {
					c.Take(t)
					c.Show(
						"0 ≤ t ≤ π < 2π",
						ByArith(atA, atB, lower, upper, PiBounds))
				})
			arg.Otherwise(
				"sin t ≠ b: then sin t = −b, and 2π − t is the point",
				func(c *Argument, notB Fact) {
					product := c.Have(
						"(sin t − b)·(sin t + b) = sin²t − b² = 0",
						"(sin(t) - b) * (sin(t) + b) = &0",
						ByArith(sineSquare))
					atMinusB := c.Have(
						"so sin t = −b, the first factor not vanishing",
						"sin(t) = -b",
						ByArith(
							notB,
							product,
							real_ring.MulEqZero.At(c.TermAs[Real]("sin(t) - b"), c.TermAs[Real]("sin(t) + b"))))
					positive := c.Have(
						"t > 0: at 0 the sine is 0, which would make b = −sin t = 0 = sin t",
						"&0 < t",
						Derive(func(d *Argument) {
							notZero := d.Unless(
								d.Term("t = &0"),
								"t = 0 is excluded",
								Given(func(e *Argument, atZero Fact) {
									e.Show(
										"sin 0 = 0 would be both −b and, then, b",
										ByArith(atZero, notB, atMinusB, SinZero))
								}))
							d.Show(
								"t ≥ 0 and t ≠ 0",
								ByArith(notZero, lower))
						}))
					reflect := c.Have(
						"2π − t is −t + 2π",
						"&2 * pi - t = -t + &2 * pi",
						ByArith())
					minusT := c.TermAs[Real]("-t")
					c.Take(c.TermAs[Real]("&2 * pi - t"))
					c.Show(
						"0 ≤ 2π − t < 2π, cos(2π − t) = cos(−t) = cos t = a and sin(2π − t) = sin(−t) = −sin t = b",
						ByArith(
							atA,
							atMinusB,
							reflect,
							upper,
							positive,
							PiBounds,
							CosPeriodic.At(minusT),
							SinPeriodic.At(minusT),
							CosNeg.At(t),
							SinNeg.At(t)))
				})
		}),
})}
