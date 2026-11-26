// unit_circle.go — the polar form of a unit complex number, its n-th roots
// and the direction that turns a coefficient onto the negative real axis.

package complex_polynomial

import (
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"

	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"

	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"

	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"

	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitPolar — every point of the unit circle has an angle:
// cosine supplies the real part, and the circle equation fixes the sine up to sign.
var UnitPolar = unitPolarThm{family.Add(registry.ProofEntry{
	Name: "UnitPolar",
	Key:  "prop_e8feab6db70ea90c",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"|z| = &1"},
		Conclusion: "∃t:real. z = complex(cos(t), sin(t))",
	}, func(a *Argument, z *Expr[Complex], unit Fact) {
		circle := a.Have(
			"the parts lie on the unit circle",
			"re(z) * re(z) + im(z) * im(z) = &1",
			ByArith(unit, complex_abs.AbsSquare.At(z)))
		continuous := a.Have(
			"cosine is continuous on the half circle",
			"real_continuous_on(⟦&0, π⟧, cos)",
			By(
				Where(real_derivative.DerivativeContinuousOn, "f'", a.TermAs[Fun[Real, Real]]("λx:real. -sin(x)")),
				real_trigonometry.CosDerivative))
		endpoints := a.Have(
			"the real part lies between the endpoint cosine values",
			"cos(π) ≤ re(z) ∧ re(z) ≤ cos(&0)",
			ByArith(
				unit,
				complex_abs.ReLessEqAbs.At(z),
				real_sgn_abs.AbsBounds.At(a.TermAs[Real]("re(z)"), a.TermAs[Real]("&1")),
				real_trigonometry.CosPi,
				real_trigonometry.CosZero))
		t, angle := a.ObtainAs[Real](
			"choose an angle with the prescribed cosine",
			"∃t:real. &0 ≤ t ∧ t ≤ π ∧ cos(t) = re(z)",
			ByArith(
				continuous,
				endpoints,
				real_continuous.IntermediateValueDecreasing.At(a.TermAs[Fun[Real, Real]]("cos"),
					a.TermAs[Real]("&0"), a.TermAs[Real]("π"), a.TermAs[Real]("re(z)")),
				real_trigonometry.PiBounds),
			Named("t"))
		signs := a.Have(
			"the imaginary part is the sine or its negative",
			"im(z) = sin(t) ∨ im(z) = -sin(t)",
			Derive(func(b *Argument) {
				parts := b.Conjuncts(
					angle,
					"the angle is nonnegative",
					"the angle is at most pi",
					"the cosine is the real part")
				product := b.Have(
					"the difference of the two squares factors to zero",
					"(im(z) - sin(t)) * (im(z) + sin(t)) = &0",
					ByArith(
						Scaled(b.TermAs[Real]("cos(t) + re(z)"), parts[2]),
						circle,
						real_trigonometry.SinSquareAddCosSquare.At(t)))
				b.Show(
					"one of the two factors vanishes",
					ByArith(
						product,
						real_ring.MulEqZero.At(b.TermAs[Real]("im(z) - sin(t)"), b.TermAs[Real]("im(z) + sin(t)"))))
			}))
		a.Do(signs.SplitDisj(
			LeftHolds(
				"the angle has the required sine",
				Given(func(b *Argument, sine Fact) {
					b.Take(t)
					b.Show(
						"the two parts determine the complex number",
						By(sine, angle, complex_field.ComplexEq, complex_field.ComplexReDef, complex_field.ComplexImDef))
				})),
			RightHolds(
				"negating the angle gives the required sine",
				Given(func(b *Argument, sine Fact) {
					b.Take(b.TermAs[Real]("-t"))
					b.Show(
						"cosine is even and sine is odd",
						By(
							sine,
							angle,
							complex_field.ComplexEq,
							complex_field.ComplexReDef,
							complex_field.ComplexImDef,
							real_trigonometry.CosNeg.At(t),
							real_trigonometry.SinNeg.At(t)))
				}))))
	}),
})}

// DeMoivre — taking a natural power multiplies the angle:
// the successor step is the sine and cosine addition formula.
var DeMoivre = deMoivreThm{family.Add(registry.ProofEntry{
	Name: "DeMoivre",
	Key:  "prop_71454518cc31e32c",
	Build: family.Theorem("∀n:num. ∀t:real. "+
		"    complex(cos(t), sin(t)) ^ n = complex(cos(&n * t), sin(&n * t))",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"the zeroth power has angle zero",
				Simp(
					Fwd(comm_monoid.MonoidPowDef),
					Fwd(real_ring.MulLeftZero),
					Fwd(real_trigonometry.CosZero),
					Fwd(real_trigonometry.SinZero),
					Fwd(complex_field.ComplexOfRealDef)),
				Basic())
			a.Step(
				"one further factor adds the angle once more",
				func(b *Argument, ih Fact) {
					b.FixAs[Real]("t")
					b.Do(Simp(Fwd(comm_monoid.MonoidPowDef)))
					angle := b.Have(
						"the successor multiple adds one angle",
						"&suc(n) * t = t + &n * t",
						Simp(Fwd(nat_arith.Add1), Fwd(real_construction.OfNumAdd)),
						ByArith())
					b.Show(
						"the two component formulas agree",
						Simp(
							complex_field.Parts,
							Fwd(ih),
							Fwd(angle),
							Fwd(complex_field.ComplexMulDef),
							Fwd(real_trigonometry.CosAdd),
							Fwd(real_trigonometry.SinAdd)),
						ByArith())
				})
		}),
})}

// UnitPowerRoot — every unit complex number has a unit root of
// every positive natural order: divide a polar angle by that order.
var UnitPowerRoot = unitPowerRootThm{family.Add(registry.ProofEntry{
	Name: "UnitPowerRoot",
	Key:  "prop_332e236b27efbcfd",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀z:complex.",
		Hypotheses: []string{"0 < n", "|z| = &1"},
		Conclusion: "∃w:complex. |w| = &1 ∧ w ^ n = z",
		Abbrev:     Abbrev{{Name: "rootAngle", Text: "λu:real. u / &n"}},
	}, func(a *Argument, n *Expr[Nat], z *Expr[Complex], h Fact) {
		_, polar := a.ObtainAs[Real](
			"choose a polar angle",
			"∃t:real. z = complex(cos(t), sin(t))",
			By(h, UnitPolar.At(z)),
			Named("t"))
		a.Take(a.TermAs[Complex]("complex(cos(«rootAngle»(t)), sin(«rootAngle»(t)))"))
		a.Show(
			"the divided angle gives a unit root",
			SplitConj(
				Case(
					"the divided angle is still a point on the unit circle",
					By(
						complex_exp.AbsExpIOfReal.At(a.TermAs[Real]("«rootAngle»(t)")),
						complex_exp.EulerOfReal.At(a.TermAs[Real]("«rootAngle»(t)")),
						complex_field.StandardForm.At(
							a.TermAs[Real]("cos(«rootAngle»(t))"), a.TermAs[Real]("sin(«rootAngle»(t))")))),
				Case(
					"taking the power restores the original angle",
					Derive(func(b *Argument) {
						restored := b.Have(
							"the positive order cancels its divisor",
							"&n * «rootAngle»(t) = t",
							ByArith(h))
						b.Show(
							"De Moivre restores the original point",
							By(polar, restored, DeMoivre.At(n, b.TermAs[Real]("«rootAngle»(t)"))))
					}))))
	}),
})}

// DescendingDirection — a unit kth root aligns a nonzero coefficient
// with the negative real axis.
var DescendingDirection = descendingDirectionThm{family.Add(registry.ProofEntry{
	Name: "DescendingDirection",
	Key:  "prop_5a2054ea44db8318",
	Build: family.Theorem(Statement{
		Binders:    "∀k:num. ∀d:complex.",
		Hypotheses: []string{"0 < k", "d ≠ &0"},
		Conclusion: "∃u:complex. |u| = &1 ∧ d * u ^ k = -complex_of_real(|d|)",
	}, func(a *Argument, k *Expr[Nat], d *Expr[Complex], h Fact) {
		positive := a.Have(
			"the nonzero coefficient has positive modulus",
			"&0 < |d|",
			By(h, complex_abs.AbsPosIffNonzero.At(d)))
		unit := a.Have(
			"normalize the desired negative-real direction",
			"|-complex_of_real(|d|) / d| = &1",
			Simp(Fwd(complex_abs.AbsDiv), Fwd(complex_abs.AbsNeg), Fwd(complex_abs.AbsOfReal)),
			ByArith(positive))
		u, alignment := a.ObtainAs[Complex](
			"take a unit kth root of that direction",
			"∃u:complex. |u| = &1 ∧ u ^ k = -complex_of_real(|d|) / d",
			By(unit, h, UnitPowerRoot.At(k, a.TermAs[Complex]("-complex_of_real(|d|) / d"))),
			Named("u"))
		a.Take(u)
		a.Show(
			"multiply the normalized root by the coefficient",
			By(
				h,
				alignment,
				field.DivLeftMul.Read(complex_field.Field).At(a.TermAs[Complex]("-complex_of_real(|d|)"), d)))
	}),
})}
