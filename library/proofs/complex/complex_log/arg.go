// arg.go — the principal argument: every complex number is |z|·exp(it)
// for an angle t of ⟬−π, π⟧, and complex_arg(z) is the chosen one; the
// slit plane, where it is continuous.

package complex_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_inverse_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// PolarFormExists — every complex number is |z|·exp(it) for an angle t of
// ⟬−π, π⟧. At 0 any angle serves. Otherwise w = z/|z| lies on the unit
// circle, and so does its reflection (−re w, im w), which is (cos s, sin s)
// for an s of ⟦0, 2π⟭; the angle π − s then has cosine re w and sine im w,
// and lies in ⟬−π, π⟧.
var PolarFormExists = polarFormExistsThm{family.Add(registry.ProofEntry{
	Name: "PolarFormExists",
	Key:  "prop_1a45f7c0e9045d35",
	Build: family.Theorem("∀z:complex. ∃t:real. -pi < t ∧ t ≤ pi ∧ z = &(|z|) * exp(complex_i * &t)",
		func(a *Argument, z *Expr[Complex]) {
			a.Cases(a.Term("z = &0"))
			a.When(
				"at 0 the modulus is 0, so the angle 0 serves",
				func(b *Argument, zero Fact) {
					b.Take(b.TermAs[Real]("&0"))
					b.Show(
						"0 lies in ⟬−π, π⟧, and 0 = 0·exp(0)",
						ByArith(zero, real_trigonometry.PiBounds, complex_abs.AbsEqZero.At(z)))
				})
			a.Otherwise(
				"off 0, z/|z| is a point of the unit circle",
				func(b *Argument, nonzero Fact) {
					positive := b.Have(
						"a nonzero number has positive modulus",
						"&0 < |z|",
						By(nonzero, complex_abs.AbsPosIffNonzero.At(z)))
					w, wDef := b.LetAs[Complex]("w", "z / &(|z|)")
					unit := b.Have(
						"w has modulus |z|/|z| = 1",
						"|w| = &1",
						Derive(func(c *Argument) {
							own := c.Have(
								"the modulus is its own absolute value",
								"||z|| = |z|",
								ByArith(positive))
							c.Do(wDef.Rw(), Simp(Fwd(complex_abs.AbsDiv), Fwd(complex_abs.AbsOfReal)))
							c.Show(
								"|z|/|z| = 1",
								ByArith(own, positive))
						}))
					circle := b.Have(
						"so the reflected point (−re w, im w) lies on the unit circle too",
						"-re(w) * -re(w) + im(w) * im(w) = &1",
						ByArith(unit, complex_abs.AbsSquare.At(w)))
					_, angle := b.ObtainAs[Real](
						"the reflected point is (cos s, sin s) for an angle s of ⟦0, 2π⟭",
						"∃s:real. &0 ≤ s ∧ s < &2 * pi ∧ cos(s) = -re(w) ∧ sin(s) = im(w)",
						By(
							circle,
							real_trigonometry.CircleParametrization.At(b.TermAs[Real]("-re(w)"), b.TermAs[Real]("im(w)"))),
						Named("s"))
					polar := b.Have(
						"exp(i(π − s)) = cos(π − s) + i·sin(π − s) = −cos s + i·sin s = w",
						"exp(complex_i * &(pi - s)) = w",
						Simp(
							Fwd(complex_exp.EulerOfReal),
							Fwd(real_trigonometry.CosSub),
							Fwd(real_trigonometry.SinSub),
							Fwd(real_trigonometry.CosPi),
							Fwd(real_trigonometry.SinPi),
							complex_field.Parts,
							Fwd(complex_field.ComplexAddDef),
							Fwd(complex_field.ComplexMulDef),
							Fwd(complex_field.ComplexOfRealDef),
							Fwd(complex_field.ComplexIDef)),
						ByArith(angle))
					b.Take(b.TermAs[Real]("pi - s"))
					b.Show(
						"π − s lies in ⟬−π, π⟧, and |z|·w = z, |z| being nonzero",
						ByArith(
							wDef,
							polar,
							positive,
							angle,
							field.DivLeftMul.Read(complex_field.Field).At(z, b.TermAs[Complex]("&(|z|)")),
							complex_field.OfRealInjective.At(b.TermAs[Real]("|z|"), b.TermAs[Real]("&0"))))
				})
		}),
})}

// ArgSpec — the argument of z is an angle of ⟬−π, π⟧ with
// z = |z|·exp(i·arg z): it is chosen among such angles, and z has one.
var ArgSpec = argSpecThm{family.Add(registry.ProofEntry{
	Name: "ArgSpec",
	Key:  "prop_15368c544b5f7bdb",
	Build: family.Theorem(
		"∀z:complex. "+
			"    -pi < complex_arg(z) ∧ complex_arg(z) ≤ pi ∧ z = &(|z|) * exp(complex_i * &(complex_arg(z)))",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"z has a polar angle in ⟬−π, π⟧, and arg z is chosen among those angles",
				Cite(PolarFormExists, z),
				Unfold(ComplexArgDef))
		}),
})}

// ArgBounds — the argument lies in ⟬−π, π⟧, by its specification.
var ArgBounds = argBoundsThm{family.Add(registry.ProofEntry{
	Name: "ArgBounds",
	Key:  "prop_c76c1b0288b96198",
	Build: family.Theorem("∀z:complex. -pi < complex_arg(z) ∧ complex_arg(z) ≤ pi",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"arg z is an angle of ⟬−π, π⟧",
				By(ArgSpec.At(z)))
		}),
})}

// ArgPolar — every complex number is its modulus times exp(i·arg z), by the
// argument's specification; at 0 both sides are 0.
var ArgPolar = argPolarThm{family.Add(registry.ProofEntry{
	Name: "ArgPolar",
	Key:  "prop_ad3ab68ed728727",
	Build: family.Theorem("∀z:complex. z = &(|z|) * exp(complex_i * &(complex_arg(z)))",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"arg z is a polar angle of z",
				By(ArgSpec.At(z)))
		}),
})}

// PolarParts — z = r·exp(it) exactly when the parts of z are r·cos t and
// r·sin t: exp(it) is cos t + i·sin t, and a number is its parts.
var PolarParts = polarPartsThm{family.Add(registry.ProofEntry{
	Name: "PolarParts",
	Key:  "prop_ad4dadb8741020fe",
	Build: family.Theorem("∀z:complex. ∀r t:real. "+
		"    z = &r * exp(complex_i * &t) ⇔ re(z) = r * cos(t) ∧ im(z) = r * sin(t)",
		func(a *Argument, z *Expr[Complex], r, t *Expr[Real]) {
			a.Show(
				"exp(it) = cos t + i·sin t, and r·(cos t + i·sin t) has parts r·cos t and r·sin t",
				Simp(
					Fwd(complex_exp.EulerOfReal),
					complex_field.Parts,
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexIDef)),
				ByArith())
		}),
})}

// ArgUnique — the argument of a nonzero z is its only polar angle in
// ⟬−π, π⟧: an angle t of ⟬−π, π⟧ with z = |z|·exp(it) gives z the parts
// |z|·cos t and |z|·sin t, as arg z does, and |z| > 0, so t has the cosine
// and the sine of arg z.
var ArgUnique = argUniqueThm{family.Add(registry.ProofEntry{
	Name: "ArgUnique",
	Key:  "prop_31099a5ad0f80bdd",
	Build: family.Theorem(Statement{
		Binders: "∀z:complex. ∀t:real.",
		Hypotheses: []string{
			"z ≠ &0",
			"-pi < t",
			"t ≤ pi",
			"z = &(|z|) * exp(complex_i * &t)",
		},
		Conclusion: "complex_arg(z) = t",
	}, func(a *Argument, z *Expr[Complex], t *Expr[Real], nonzero, above, below, polar Fact) {
		angle, size := a.TermAs[Real]("complex_arg(z)"), a.TermAs[Real]("|z|")
		same := a.Have(
			"both angles give z the parts |z|·cos and |z|·sin, and |z| > 0, so their cosines and sines agree",
			"cos(complex_arg(z)) = cos(t) ∧ sin(complex_arg(z)) = sin(t)",
			ByArith(
				nonzero,
				polar,
				complex_abs.AbsPosIffNonzero.At(z),
				ArgSpec.At(z),
				PolarParts.At(z, size, angle),
				PolarParts.At(z, size, t)))
		a.Show(
			"two angles of ⟬−π, π⟧ with the same cosine and sine are equal",
			By(same, above, below, ArgBounds.At(z), real_trigonometry.CosSinInjective.At(angle, t)))
	}),
})}

// ArgPositiveReal — a positive real has argument 0: x = |x|·exp(i·0), its
// parts being |x|·cos 0 = x and |x|·sin 0 = 0, and 0 lies in ⟬−π, π⟧.
var ArgPositiveReal = argPositiveRealThm{family.Add(registry.ProofEntry{
	Name: "ArgPositiveReal",
	Key:  "prop_f77291e0b2d9de7d",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_arg(&x) = &0",
	}, func(a *Argument, x *Expr[Real], positive Fact) {
		z, zero := a.TermAs[Complex]("&x"), a.TermAs[Real]("&0")
		parts := a.Have(
			"x has the parts |x|·cos 0 = x and |x|·sin 0 = 0",
			"re(&x) = |&x| * cos(&0) ∧ im(&x) = |&x| * sin(&0)",
			Simp(
				Fwd(complex_abs.AbsOfReal),
				Fwd(complex_field.ComplexOfRealDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef),
				Fwd(real_trigonometry.CosZero),
				Fwd(real_trigonometry.SinZero)),
			ByArith(positive))
		a.Show(
			"so x = |x|·exp(i·0), x is not 0, and 0 lies in ⟬−π, π⟧",
			ByArith(
				positive,
				parts,
				real_trigonometry.PiBounds,
				complex_field.OfRealInjective.At(x, zero),
				PolarParts.At(z, a.TermAs[Real]("|&x|"), zero),
				ArgUnique.At(z, zero)))
	}),
})}

// ArgNegativeReal — a negative real has argument π: x = |x|·exp(iπ), its
// parts being |x|·cos π = −|x| = x and |x|·sin π = 0, and π lies in
// ⟬−π, π⟧.
var ArgNegativeReal = argNegativeRealThm{family.Add(registry.ProofEntry{
	Name: "ArgNegativeReal",
	Key:  "prop_3dc0c033118b05f1",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"x < &0"},
		Conclusion: "complex_arg(&x) = pi",
	}, func(a *Argument, x *Expr[Real], negative Fact) {
		z, straight := a.TermAs[Complex]("&x"), a.TermAs[Real]("pi")
		parts := a.Have(
			"x has the parts |x|·cos π = −|x| = x and |x|·sin π = 0",
			"re(&x) = |&x| * cos(pi) ∧ im(&x) = |&x| * sin(pi)",
			Simp(
				Fwd(complex_abs.AbsOfReal),
				Fwd(complex_field.ComplexOfRealDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef),
				Fwd(real_trigonometry.CosPi),
				Fwd(real_trigonometry.SinPi)),
			ByArith(negative))
		a.Show(
			"so x = |x|·exp(iπ), x is not 0, and π lies in ⟬−π, π⟧",
			ByArith(
				negative,
				parts,
				real_trigonometry.PiBounds,
				complex_field.OfRealInjective.At(x, a.TermAs[Real]("&0")),
				PolarParts.At(z, a.TermAs[Real]("|&x|"), straight),
				ArgUnique.At(z, straight)))
	}),
})}

// SlitPlaneIff — z lies in the slit plane, off the closed negative
// half-line, exactly when |z| + re z > 0: re z ≥ −|z| always, and
// re z = −|z| exactly when im z = 0 and re z ≤ 0, |z|² being re² + im².
var SlitPlaneIff = slitPlaneIffThm{family.Add(registry.ProofEntry{
	Name: "SlitPlaneIff",
	Key:  "prop_900e76d8781f9042",
	Build: family.Theorem("∀z:complex. z ∈ slit_plane ⇔ &0 < |z| + re(z)",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"|re z| ≤ |z|, and re z = −|z| exactly on the half-line, |z|² being re² + im²",
				Unfold(SlitPlaneDef),
				ByArith(complex_abs.AbsSquare.At(z), complex_abs.AbsNonneg.At(z), complex_abs.ReLessEqAbs.At(z)))
		}),
})}

// SlitPlaneAbsPos — 0 is off the slit plane: a point of it has positive
// modulus, as |z| + re z > 0 there and re z ≤ |z|.
var SlitPlaneAbsPos = slitPlaneAbsPosThm{family.Add(registry.ProofEntry{
	Name: "SlitPlaneAbsPos",
	Key:  "prop_ed743c8c2a5d62e2",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ slit_plane"},
		Conclusion: "&0 < |z|",
	}, func(a *Argument, z *Expr[Complex], inSlit Fact) {
		a.Show(
			"|z| + re z > 0 and re z ≤ |z|, so |z| > 0",
			ByArith(inSlit, SlitPlaneIff.At(z), complex_abs.ReLessEqAbs.At(z)))
	}),
})}

// SlitPlaneNearOne — the disc of radius 1 about 1 lies in the slit plane:
// within 1 of 1, re w > 1 − |w − 1| > 0, so |w| + re w > 0.
var SlitPlaneNearOne = slitPlaneNearOneThm{family.Add(registry.ProofEntry{
	Name: "SlitPlaneNearOne",
	Key:  "prop_7b462476c02639b",
	Build: family.Theorem(Statement{
		Binders: "∀w:complex.",
		Hypotheses: []string{
			"|w - &1| < &1",
		},
		Conclusion: "w ∈ slit_plane",
	}, func(a *Argument, w *Expr[Complex], near Fact) {
		a.Show(
			"re(w − 1) ≥ −|w − 1| > −1, so re w > 0 and |w| + re w > 0",
			ByArith(
				near,
				complex_abs.PartsNonexpanding.At(w, a.TermAs[Complex]("&1")),
				complex_field.PartsOfReal.At(a.TermAs[Real]("&1")),
				complex_abs.AbsNonneg.At(w),
				SlitPlaneIff.At(w)))
	}),
})}

// ArgHalfAngle — in the slit plane the argument is 2·arctan(im z/(|z| + re z)).
// With h half the argument, z = |z|·exp(2ih) gives |z| + re z = 2|z|·cos²h
// and im z = 2|z|·sin h·cos h, so the quotient is tan h; and h lies in
// ⟬−π/2, π/2⟭, where the arctangent undoes the tangent, h = π/2 being
// excluded by cos h ≠ 0.
var ArgHalfAngle = argHalfAngleThm{family.Add(registry.ProofEntry{
	Name: "ArgHalfAngle",
	Key:  "prop_e3958973f5160312",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ slit_plane"},
		Conclusion: "complex_arg(z) = &2 * arctan(im(z) / (|z| + re(z)))",
	}, func(a *Argument, z *Expr[Complex], inSlit Fact) {
		size := a.TermAs[Real]("|z|")
		positive := a.Have(
			"in the slit plane |z| + re z is positive",
			"&0 < |z| + re(z)",
			By(inSlit, SlitPlaneIff.At(z)))
		h, hDef := a.LetAs[Real]("h", "complex_arg(z) / &2")
		twice := a.Have(
			"h is half the argument",
			"complex_arg(z) = h + h",
			ByArith(hDef))
		parts := a.Have(
			"z = |z|·exp(i(h + h)) has the parts |z|·cos(h + h) and |z|·sin(h + h)",
			"re(z) = |z| * cos(h + h) ∧ im(z) = |z| * sin(h + h)",
			By(twice, ArgSpec.At(z), PolarParts.At(z, size, a.TermAs[Real]("h + h"))))
		sum := a.Have(
			"so |z| + re z = |z|·(1 + cos²h − sin²h) = 2|z|·cos²h",
			"|z| + re(z) = &2 * |z| * (cos(h) * cos(h))",
			ByArith(
				parts,
				Scaled(size, real_trigonometry.CosAdd.At(h, h)),
				Scaled(size, real_trigonometry.SinSquareAddCosSquare.At(h))))
		imaginary := a.Have(
			"and im z = |z|·sin(h + h) = 2|z|·sin h·cos h",
			"im(z) = &2 * |z| * (sin(h) * cos(h))",
			ByArith(parts, Scaled(size, real_trigonometry.SinAdd.At(h, h))))
		cosNonzero := a.Have(
			"2|z|·cos²h = |z| + re z is positive, so cos h ≠ 0",
			"cos(h) ≠ &0",
			ByArith(positive, sum, complex_abs.AbsNonneg.At(z)))
		notTop := a.Have(
			"so h ≠ π/2, where the cosine vanishes",
			"h ≠ pi / &2",
			By(cosNonzero, real_trigonometry.PiHalfZero))
		inside := a.Have(
			"h lies strictly inside ⟬−π/2, π/2⟭, arg z lying in ⟬−π, π⟧",
			"-(pi / &2) < h ∧ h < pi / &2",
			ByArith(notTop, twice, ArgBounds.At(z)))
		quotient := a.Have(
			"im z/(|z| + re z) = 2|z|·sin h·cos h/(2|z|·cos²h) = sin h/cos h = tan h",
			"im(z) / (|z| + re(z)) = tan(h)",
			ByArith(
				positive,
				cosNonzero,
				imaginary,
				Scaled(a.TermAs[Real]("tan(h)"), sum),
				Scaled(a.TermAs[Real]("&2 * |z| * (cos(h) * cos(h))"), real_inverse_trigonometry.RealTanDef.At(h))))
		a.Show(
			"so 2·arctan(im z/(|z| + re z)) = 2·arctan(tan h) = 2h = arg z",
			ByArith(quotient, twice, inside, real_inverse_trigonometry.ArctanTan.At(h)))
	}),
})}

// ArgContinuous — the argument is continuous on the slit plane. About a
// point z of it, it is 2·arctan(im w/(|w| + re w)) on a whole disc about
// z, |w| + re w staying positive within (|z| + re z)/2 of z; and that
// function is continuous at z: the half-angle tangent im w/(|w| + re w) is
// built from the parts and the modulus by a sum, an inverse at a nonzero
// value and a product, and s ↦ 2·arctan s has a derivative.
var ArgContinuous = argContinuousThm{family.Add(registry.ProofEntry{
	Name: "ArgContinuous",
	Key:  "prop_1c53a560b2d1ecde",
	Build: family.Sections(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ slit_plane"},
		Conclusion: "complex_continuous_at(λw:complex. &(complex_arg(w)), z)",
		Abbrev:     Abbrev{{Name: "halfAngleTangent", Text: "λw:complex. im(w) / (|w| + re(w))"}},
	}, func(ctx *Script, headline string) *GoalStackNode {
		halfAngle := ctx.Lemma(Statement{
			Binders:    "∀z:complex.",
			Hypotheses: []string{"&0 < |z| + re(z)"},
			Conclusion: "complex_continuous_at(λw:complex. &(&2 * arctan(«halfAngleTangent»(w))), z)",
		}, func(a *Argument, z *Expr[Complex], positive Fact) {
			modulus := a.TermAs[Fun[Complex, Complex]]("λw:complex. &(|w|)")
			realPart := a.TermAs[Fun[Complex, Complex]]("λw:complex. &(re(w))")
			denominator := a.TermAs[Fun[Complex, Complex]]("λw:complex. &(|w|) + &(re(w))")
			nonzero := a.Have(
				"|z| + re z, seen in ℂ, is not 0",
				"&(|z|) + &(re(z)) ≠ &0",
				ByArith(
					positive,
					complex_field.OfRealAdd.At(a.TermAs[Real]("|z|"), a.TermAs[Real]("re(z)")),
					complex_field.OfRealInjective.At(a.TermAs[Real]("|z| + re(z)"), a.TermAs[Real]("&0"))))
			product := a.Have(
				"im w·(|w| + re w)⁻¹ is continuous at z: a product of a part and an inverse of a sum, nonzero at z",
				"complex_continuous_at(λw:complex. &(im(w)) * complex_inv(&(|w|) + &(re(w))), z)",
				By(
					nonzero,
					complex_topology.ContinuousAtParts.At(z),
					complex_topology.ContinuousAtAdd.At(modulus, realPart, z),
					complex_topology.ContinuousAtInv.At(denominator, z),
					complex_topology.ContinuousAtMul.At(
						a.TermAs[Fun[Complex, Complex]]("λw:complex. &(im(w))"),
						a.TermAs[Fun[Complex, Complex]]("λw:complex. complex_inv(&(|w|) + &(re(w)))"),
						z)))
			pointwise := a.Have(
				"which is the half-angle tangent im w/(|w| + re w) seen in ℂ",
				"∀w:complex. &(«halfAngleTangent»(w)) = &(im(w)) * complex_inv(&(|w|) + &(re(w)))",
				Simp(Fwd(complex_field.OfRealDiv), Fwd(complex_field.OfRealAdd), Fwd(complex_field.ComplexDivDef)),
				Basic())
			tangent := a.Have(
				"so the half-angle tangent is continuous at z",
				"complex_continuous_at(λw:complex. &(«halfAngleTangent»(w)), z)",
				By(pointwise, product))
			value := a.TermAs[Real]("«halfAngleTangent»(z)")
			outer := a.Have(
				"s ↦ 2·arctan s is continuous at the half-angle "+
					"tangent's value, having the derivative 2/(1 + s²) there",
				"real_continuous_at(λs:real. &2 * arctan(s), «halfAngleTangent»(z))",
				By(
					real_derivative.DerivativeContinuous.At(
						a.TermAs[Fun[Real, Real]]("λs:real. &2 * arctan(s)"),
						value,
						a.TermAs[Real]("&2 * real_inv(&1 + real_pow(«halfAngleTangent»(z), 2))")),
					real_derivative.DerivativeScale.At(
						a.TermAs[Fun[Real, Real]]("real_arctan"),
						value,
						a.TermAs[Real]("real_inv(&1 + real_pow(«halfAngleTangent»(z), 2))"),
						a.TermAs[Real]("&2")),
					real_inverse_trigonometry.ArctanDerivative.At(value)))
			a.Show(
				"so is 2·arctan of the half-angle tangent",
				By(
					tangent,
					outer,
					complex_topology.ContinuousAtRealCompose.At(
						a.TermAs[Fun[Real, Real]]("λs:real. &2 * arctan(s)"),
						a.TermAs[Fun[Complex, Real]]("«halfAngleTangent»"),
						z)))
		})
		return ctx.Theorem(headline, func(a *Argument, z *Expr[Complex], inSlit Fact) {
			positive := a.Have(
				"in the slit plane |z| + re z is positive",
				"&0 < |z| + re(z)",
				By(inSlit, SlitPlaneIff.At(z)))
			agree := a.Have(
				"within (|z| + re z)/2 of z the argument is 2·arctan(im w/(|w| + re w))",
				Statement{
					Binders:    "∀w:complex.",
					Hypotheses: []string{"|w - z| < (|z| + re(z)) / &2"},
					Conclusion: "&(complex_arg(w)) = &(&2 * arctan(«halfAngleTangent»(w)))",
				},
				Derive(func(b *Argument) {
					w := b.FixAs[Complex]("w")
					near := b.Assume()
					stays := b.Have(
						"|w| + re w ≥ |z| + re z − 2|w − z| > 0",
						"&0 < |w| + re(w)",
						ByArith(
							near,
							positive,
							complex_abs.AbsTriangleReverse.At(w, z),
							complex_abs.PartsNonexpanding.At(w, z)))
					b.Show(
						"so w lies in the slit plane, where the half-angle formula holds",
						By(stays, SlitPlaneIff.At(w), ArgHalfAngle.At(w)))
				}))
			a.Show(
				"so the argument agrees near z with a function continuous at z",
				ByArith(
					agree,
					positive,
					At(halfAngle, z),
					complex_topology.ContinuousAtLocal.At(
						a.TermAs[Fun[Complex, Complex]]("λw:complex. &(complex_arg(w))"),
						a.TermAs[Fun[Complex, Complex]]("λw:complex. &(&2 * arctan(«halfAngleTangent»(w)))"),
						z,
						a.TermAs[Real]("(|z| + re(z)) / &2"))))
		})
	}),
})}
