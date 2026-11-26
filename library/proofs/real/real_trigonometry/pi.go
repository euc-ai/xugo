// pi.go — π: the cosine falls on ⟦0, 2⟧, from 1 at 0 to a negative
// value at 2, so it has exactly one zero there, and π is twice it; the
// values of the sine and the cosine at π/2 and π, and their periods.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// CosStrictlyDecreasing — the cosine falls strictly on ⟦0, 2⟧: it is
// continuous there, and its derivative −sin is negative on ⟬0, 2⟭, where
// the sine is positive.
var CosStrictlyDecreasing = cosStrictlyDecreasingThm{family.Add(registry.ProofEntry{
	Name: "CosStrictlyDecreasing",
	Key:  "prop_8ac676606421e105",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"x < y",
			"y ≤ &2",
		},
		Conclusion: "cos(y) < cos(x)",
	},
		func(arg *Argument, x, y *Expr[Real], order Fact) {
			slope := arg.Have(
				"the cosine's derivative at t is −sin t, as at every point",
				"∀t:real. &0 < t ∧ t < &2 ⇒ real_derivative_at(real_cos, t, -sin(t))",
				arg.ForEach(func(t *Expr[Real]) Action { return By(CosDerivative.At(t)) }))
			negative := arg.Have(
				"which is negative on ⟬0, 2⟭, where the sine is positive",
				"∀t:real. &0 < t ∧ t < &2 ⇒ -sin(t) < &0",
				arg.ForEach(func(t *Expr[Real]) Action { return ByArith(SinPositive.At(t)) }))
			arg.Show(
				"continuous on ⟦0, 2⟧ with a negative derivative inside, the cosine falls strictly there",
				By(
					order,
					CosContinuousOn.At(arg.TermAs[Set[Real]]("⟦&0, &2⟧")),
					slope,
					negative,
					real_derivative.DerivativeNegativeStrictlyDecreasing.At(
						arg.TermAs[Fun[Real, Real]]("real_cos"), arg.TermAs[Fun[Real, Real]]("λt:real. -sin(t)"),
						arg.TermAs[Real]("&0"), arg.TermAs[Real]("&2"), x, y)))
		}),
})}

// PiHalfZero — π/2 is a zero of the cosine between 0 and 2. The
// cosine is continuous and passes from cos 0 = 1 to cos 2 < 0, so it has
// a zero in ⟦0, 2⟧ by the intermediate value theorem; π/2 is the chosen
// one.
var PiHalfZero = piHalfZeroThm{family.Add(registry.ProofEntry{
	Name: "PiHalfZero",
	Key:  "prop_2243669b9efab99b",
	Build: family.Theorem("&0 ≤ pi / &2 ∧ pi / &2 ≤ &2 ∧ cos(pi / &2) = &0",
		func(arg *Argument) {
			ends := arg.Have(
				"0 lies between cos 2 < 0 and cos 0 = 1",
				"&0 ≤ &2 ∧ cos(&2) ≤ &0 ∧ &0 ≤ cos(&0)",
				ByArith(CosZero, CosTwoNegative))
			zero, two := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&2")
			exists := arg.Have(
				"so the cosine, continuous on ⟦0, 2⟧, has a zero there, by the intermediate value theorem",
				"∃x:real. &0 ≤ x ∧ x ≤ &2 ∧ cos(x) = &0",
				By(
					CosContinuousOn.At(arg.TermAs[Set[Real]]("⟦&0, &2⟧")),
					ends,
					real_continuous.IntermediateValueDecreasing.At(
						arg.TermAs[Fun[Real, Real]]("real_cos"), zero, two, zero)))
			half := arg.Have(
				"π/2 is the chosen zero",
				"pi / &2 = (εx:real. &0 ≤ x ∧ x ≤ &2 ∧ cos(x) = &0)",
				Unfold(PiDef),
				ByArith())
			arg.Show(
				"and a chosen zero is a zero, one existing",
				half.Rw(),
				By(exists))
		}),
})}

// CosEqZeroIff — π/2 is the only zero of the cosine in ⟦0, 2⟧: it is
// one, and a zero x on either side of it is excluded because the cosine
// falls strictly between x and π/2, so the two cannot both be 0.
var CosEqZeroIff = cosEqZeroIffThm{family.Add(registry.ProofEntry{
	Name: "CosEqZeroIff",
	Key:  "prop_6c3a077a2e290a2a",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"x ≤ &2",
		},
		Conclusion: "cos(x) = &0 ⇔ x = pi / &2",
	},
		func(arg *Argument, x *Expr[Real], within Fact) {
			half := arg.TermAs[Real]("pi / &2")
			arg.Iff()
			arg.Forward(
				"a zero of the cosine in ⟦0, 2⟧ is π/2",
				func(d *Argument, zero Fact) {
					notBelow := d.Unless(
						d.Term("x < pi / &2"),
						"below π/2 the cosine would fall from x to π/2: 0 = cos(π/2) < cos x = 0",
						Given(func(e *Argument, below Fact) {
							e.Show(
								"the two zeros would differ",
								ByArith(zero, below, within, PiHalfZero, CosStrictlyDecreasing.At(x, half)))
						}))
					notAbove := d.Unless(
						d.Term("pi / &2 < x"),
						"above π/2 it would fall from π/2 to x: 0 = cos x < cos(π/2) = 0",
						Given(func(e *Argument, above Fact) {
							e.Show(
								"the two zeros would differ",
								ByArith(zero, above, within, PiHalfZero, CosStrictlyDecreasing.At(half, x)))
						}))
					d.Show(
						"neither below π/2 nor above it, x is π/2",
						ByArith(notBelow, notAbove))
				})
			arg.Backward(
				"at π/2 the cosine is 0",
				func(d *Argument, atHalf Fact) {
					d.Show(
						"as π/2 is a zero",
						By(atHalf, PiHalfZero))
				})
		}),
})}

// PiBounds — π lies between 0 and 4. π/2 is a zero of the cosine in
// ⟦0, 2⟧, and it is neither end: the cosine is 1 at 0 and negative at 2.
var PiBounds = piBoundsThm{family.Add(registry.ProofEntry{
	Name: "PiBounds",
	Key:  "prop_75e489d10b361a98",
	Build: family.Theorem("&0 < pi ∧ pi < &4",
		func(arg *Argument) {
			lower := arg.Unless(
				arg.Term("pi / &2 ≤ &0"),
				"were π/2 ≤ 0 it would be 0, where the cosine is 1, not 0",
				Given(func(d *Argument, atMostZero Fact) {
					atZero := d.Have(
						"π/2 would be 0, being at least 0",
						"pi / &2 = &0",
						ByArith(atMostZero, PiHalfZero))
					d.Show(
						"so cos(π/2) would be cos 0 = 1, against cos(π/2) = 0",
						ByArith(atZero, CosZero, PiHalfZero))
				}))
			upper := arg.Unless(
				arg.Term("&2 ≤ pi / &2"),
				"were π/2 ≥ 2 it would be 2, where the cosine is negative, not 0",
				Given(func(d *Argument, atLeastTwo Fact) {
					atTwo := d.Have(
						"π/2 would be 2, being at most 2",
						"pi / &2 = &2",
						ByArith(atLeastTwo, PiHalfZero))
					d.Show(
						"so cos(π/2) would be cos 2 < 0, against cos(π/2) = 0",
						By(atTwo, PiHalfZero, CosTwoNegative))
				}))
			arg.Show(
				"so 0 < π/2 < 2, and 0 < π < 4",
				ByArith(lower, upper))
		}),
})}

// SinPiHalf — the sine is 1 at π/2: there its square is
// 1 − cos²(π/2) = 1, so its size is 1, and it is positive, π/2 lying in
// ⟬0, 2⟭.
var SinPiHalf = sinPiHalfThm{family.Add(registry.ProofEntry{
	Name: "SinPiHalf",
	Key:  "prop_b6c71e5ab8b17205",
	Build: family.Theorem("sin(pi / &2) = &1",
		func(arg *Argument) {
			half, one := arg.TermAs[Real]("pi / &2"), arg.TermAs[Real]("&1")
			sine := arg.TermAs[Real]("sin(pi / &2)")
			square := arg.Have(
				"sin²(π/2) = 1 − cos²(π/2) = 1 − 0² = 1",
				"real_pow(sin(pi / &2), 2) = &1",
				ByArith(SinSquareAddCosSquare.At(half), PiHalfZero))
			size := arg.Have(
				"so its size is 1: sizes compare as their squares do, and 1² = 1 = |1|",
				"|sin(pi / &2)| = &1",
				ByArith(
					square,
					real_pow.AbsLessEqIffPowTwoLessEq.At(sine, one),
					real_pow.AbsLessEqIffPowTwoLessEq.At(one, sine),
					real_sgn_abs.AbsOfOne,
					real_pow.OnePow.At(arg.TermAs[Nat]("2"))))
			positive := arg.Have(
				"and it is positive, π/2 lying in ⟬0, 2⟭, where the sine is",
				"&0 < sin(pi / &2)",
				ByArith(PiBounds, SinPositive.At(half)))
			arg.Show(
				"a positive number is its own size",
				ByArith(size, positive))
		}),
})}

// CosPi — the cosine is −1 at π: by the addition formula at π/2 and π/2,
// cos π = cos²(π/2) − sin²(π/2) = 0 − 1.
var CosPi = cosPiThm{family.Add(registry.ProofEntry{
	Name: "CosPi",
	Key:  "prop_b8f3df12164121a4",
	Build: family.Theorem("cos(pi) = -&1",
		func(arg *Argument) {
			sum := arg.Have(
				"π is π/2 + π/2",
				"pi / &2 + pi / &2 = pi",
				ByArith())
			value := arg.Have(
				"so cos π is cos(π/2 + π/2)",
				"cos(pi) = cos(pi / &2 + pi / &2)",
				By(sum))
			cosHalf := arg.Have(
				"the cosine is 0 at π/2",
				"cos(pi / &2) = &0",
				By(PiHalfZero))
			arg.Show(
				"= cos(π/2)·cos(π/2) − sin(π/2)·sin(π/2) = 0·0 − 1·1",
				value.Rw(),
				Simp(Fwd(CosAdd), Fwd(SinPiHalf)),
				cosHalf.Rw(),
				ByArith())
		}),
})}

// SinPi — the sine is 0 at π: by the addition formula at π/2 and π/2,
// sin π = sin(π/2)·cos(π/2) + cos(π/2)·sin(π/2) = 1·0 + 0·1.
var SinPi = sinPiThm{family.Add(registry.ProofEntry{
	Name: "SinPi",
	Key:  "prop_545c927d3708b2c9",
	Build: family.Theorem("sin(pi) = &0",
		func(arg *Argument) {
			sum := arg.Have(
				"π is π/2 + π/2",
				"pi / &2 + pi / &2 = pi",
				ByArith())
			value := arg.Have(
				"so sin π is sin(π/2 + π/2)",
				"sin(pi) = sin(pi / &2 + pi / &2)",
				By(sum))
			cosHalf := arg.Have(
				"the cosine is 0 at π/2",
				"cos(pi / &2) = &0",
				By(PiHalfZero))
			arg.Show(
				"= sin(π/2)·cos(π/2) + cos(π/2)·sin(π/2) = 1·0 + 0·1",
				value.Rw(),
				Simp(Fwd(SinAdd), Fwd(SinPiHalf)),
				cosHalf.Rw(),
				ByArith())
		}),
})}

// SinAddPi — moving by π changes the sign of the sine:
// sin(x + π) = sin x·cos π + cos x·sin π = −sin x.
var SinAddPi = sinAddPiThm{family.Add(registry.ProofEntry{
	Name: "SinAddPi",
	Key:  "prop_6e6a18b94d5b95e2",
	Build: family.Theorem("∀x:real. sin(x + pi) = -sin(x)",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"sin(x + π) = sin x·cos π + cos x·sin π = sin x·(−1) + cos x·0",
				Simp(Fwd(SinAdd), Fwd(CosPi), Fwd(SinPi)),
				ByArith())
		}),
})}

// CosAddPi — and of the cosine: cos(x + π) = cos x·cos π − sin x·sin π
// = −cos x.
var CosAddPi = cosAddPiThm{family.Add(registry.ProofEntry{
	Name: "CosAddPi",
	Key:  "prop_c11cae0659484a08",
	Build: family.Theorem("∀x:real. cos(x + pi) = -cos(x)",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"cos(x + π) = cos x·cos π − sin x·sin π = cos x·(−1) − sin x·0",
				Simp(Fwd(CosAdd), Fwd(CosPi), Fwd(SinPi)),
				ByArith())
		}),
})}

// SinPeriodic — the sine has period 2π: moving by π twice changes its
// sign twice.
var SinPeriodic = sinPeriodicThm{family.Add(registry.ProofEntry{
	Name: "SinPeriodic",
	Key:  "prop_551276acc5641b77",
	Build: family.Theorem("∀x:real. sin(x + &2 * pi) = sin(x)",
		func(arg *Argument, x *Expr[Real]) {
			twice := arg.Have(
				"x + 2π is (x + π) + π",
				"x + &2 * pi = x + pi + pi",
				ByArith())
			value := arg.Have(
				"so sin(x + 2π) is sin((x + π) + π)",
				"sin(x + &2 * pi) = sin(x + pi + pi)",
				By(twice))
			arg.Show(
				"= −sin(x + π) = −(−sin x)",
				value.Rw(),
				Simp(Fwd(SinAddPi)),
				ByArith())
		}),
})}

// CosPeriodic — the cosine has period 2π, as the sine does.
var CosPeriodic = cosPeriodicThm{family.Add(registry.ProofEntry{
	Name: "CosPeriodic",
	Key:  "prop_232e3054d76c7e79",
	Build: family.Theorem("∀x:real. cos(x + &2 * pi) = cos(x)",
		func(arg *Argument, x *Expr[Real]) {
			twice := arg.Have(
				"x + 2π is (x + π) + π",
				"x + &2 * pi = x + pi + pi",
				ByArith())
			value := arg.Have(
				"so cos(x + 2π) is cos((x + π) + π)",
				"cos(x + &2 * pi) = cos(x + pi + pi)",
				By(twice))
			arg.Show(
				"= −cos(x + π) = −(−cos x)",
				value.Rw(),
				Simp(Fwd(CosAddPi)),
				ByArith())
		}),
})}
