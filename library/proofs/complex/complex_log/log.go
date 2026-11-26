// log.go — the principal logarithm log z = log|z| + i·arg z: its parts, its
// value on the positive reals, its inverse relation with exp, and its
// continuity and derivative on the slit plane.

package complex_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/registry"
)

// LogParts — the real part of log z is log|z| and its imaginary part is
// arg z, read off the definition.
var LogParts = logPartsThm{family.Add(registry.ProofEntry{
	Name: "LogParts",
	Key:  "prop_6d9467e743c23b41",
	Build: family.Theorem("∀z:complex. re(log(z)) = log(|z|) ∧ im(log(z)) = complex_arg(z)",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"log z = log|z| + i·arg z, whose parts are log|z| and arg z",
				Simp(
					Fwd(ComplexLogDef),
					complex_field.Parts,
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexIDef)),
				ByArith())
		}),
})}

// LogPositiveReal — on the positive reals the principal logarithm is the
// real one: |x| = x and arg x = 0, so log x = log|x| + i·0.
var LogPositiveReal = logPositiveRealThm{family.Add(registry.ProofEntry{
	Name: "LogPositiveReal",
	Key:  "prop_b46a29c1e2f8544a",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "log(&x) = &(log(x))",
	}, func(a *Argument, x *Expr[Real], positive Fact) {
		size := a.Have(
			"|x| = x, x being positive",
			"|x| = x",
			ByArith(positive))
		a.Show(
			"log x = log|x| + i·arg x = log x + i·0",
			Simp(Fwd(ComplexLogDef), Fwd(complex_abs.AbsOfReal)),
			ByArith(positive, size, ArgPositiveReal.At(x)))
	}),
})}

// ExpLog — exp undoes the principal logarithm away from 0: exp(log z) is
// exp(log|z|)·exp(i·arg z), and exp(log|z|) is the real exp(log|z|) = |z|,
// |z| being positive; so exp(log z) is |z|·exp(i·arg z), which is z.
var ExpLog = expLogThm{family.Add(registry.ProofEntry{
	Name: "ExpLog",
	Key:  "prop_4cdffa55a20697b7",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ≠ &0"},
		Conclusion: "exp(log(z)) = z",
	}, func(a *Argument, z *Expr[Complex], nonzero Fact) {
		positive := a.Have(
			"z is not 0, so |z| is positive",
			"&0 < |z|",
			By(nonzero, complex_abs.AbsPosIffNonzero.At(z)))
		radial := a.Have(
			"exp(log|z|) is the real exp(log|z|), which is |z| as |z| > 0",
			"exp(&(log(|z|))) = &(|z|)",
			By(
				Normalized,
				positive,
				real_exp_log.ExpLog.At(a.TermAs[Real]("|z|")),
				complex_exp.ExpOfReal.At(a.TermAs[Real]("log(|z|)"))))
		a.Show(
			"exp(log z) = exp(log|z| + i·arg z) = exp(log|z|)·exp(i·arg z) = |z|·exp(i·arg z) = z",
			Unfold(ComplexLogDef),
			By(
				radial,
				At(
					complex_power_series.ExpAdd,
					a.TermAs[Complex]("&(log(|z|))"),
					a.TermAs[Complex]("complex_i * &(complex_arg(z))")),
				ArgPolar.At(z)))
	}),
})}

// LogExp — the principal logarithm undoes exp on the strip −π < im z ≤ π.
// Written z = re z + i·im z, exp(z) is exp(re z)·exp(i·im z), a positive
// real times a point of the unit circle, and |exp(z)| = exp(re z)
// (complex_power_series.AbsExp): so im z, an angle of ⟬−π, π⟧, is the
// argument of exp(z) ≠ 0. Hence
// log(exp z) = log(exp(re z)) + i·im z = re z + i·im z = z.
var LogExp = logExpThm{family.Add(registry.ProofEntry{
	Name: "LogExp",
	Key:  "prop_cd5e8db5f681f0a1",
	Build: family.Theorem(Statement{
		Binders: "∀z:complex.",
		Hypotheses: []string{
			"-pi < im(z)",
			"im(z) ≤ pi",
		},
		Conclusion: "log(exp(z)) = z",
	}, func(a *Argument, z *Expr[Complex], strip Fact) {
		x, y := a.TermAs[Real]("re(z)"), a.TermAs[Real]("im(z)")
		decomposed := a.Have(
			"z is its real part plus i times its imaginary part",
			"z = &(re(z)) + complex_i * &(im(z))",
			Simp(
				complex_field.Parts,
				Fwd(complex_field.ComplexAddDef),
				Fwd(complex_field.ComplexMulDef),
				Fwd(complex_field.ComplexOfRealDef),
				Fwd(complex_field.ComplexIDef)),
			ByArith())
		polar := a.Have(
			"so exp(z) = exp(re z)·exp(i·im z), the positive real exp(re z) times a point of the unit circle",
			"exp(z) = &(exp(re(z))) * exp(complex_i * &(im(z)))",
			By(
				Normalized,
				decomposed,
				complex_power_series.ExpAdd.At(
					a.TermAs[Complex]("&(re(z))"), a.TermAs[Complex]("complex_i * &(im(z))")),
				complex_exp.ExpOfReal.At(x)))
		size := complex_power_series.AbsExp.At(z)
		angle := a.Have(
			"exp(z) is not 0 and is |exp(z)|·exp(i·im z) with im z in ⟬−π, π⟧, so its argument is im z",
			"complex_arg(exp(z)) = im(z)",
			ByArith(
				polar,
				size,
				strip,
				complex_power_series.ExpNonzero.At(z),
				ArgUnique.At(a.TermAs[Complex]("exp(z)"), y)))
		a.Show(
			"log(exp z) = log|exp z| + i·arg(exp z) = log(exp(re z)) + i·im z = re z + i·im z = z",
			Unfold(ComplexLogDef),
			By(decomposed, size, angle, real_exp_log.LogExp.At(x)))
	}),
})}

// LogContinuous — the principal logarithm is continuous on the slit plane:
// log|w| is the continuous real logarithm of the continuous modulus, |z|
// being positive there, and arg is continuous there, so log|w| + i·arg w
// is.
var LogContinuous = logContinuousThm{family.Add(registry.ProofEntry{
	Name: "LogContinuous",
	Key:  "prop_fdb26dc5ac50e903",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ slit_plane"},
		Conclusion: "complex_continuous_at(complex_log, z)",
	}, func(a *Argument, z *Expr[Complex], inSlit Fact) {
		size := a.TermAs[Real]("|z|")
		logModulus := a.TermAs[Fun[Complex, Complex]]("λw:complex. &(log(|w|))")
		rotation := a.TermAs[Fun[Complex, Complex]]("λw:complex. complex_i * &(complex_arg(w))")
		logModulusContinuous := a.Have(
			"log|w| is continuous at z: the real logarithm is continuous at "+
				"|z|, positive on the slit plane, and the modulus is continuous at z",
			"complex_continuous_at(λw:complex. &(log(|w|)), z)",
			By(
				complex_topology.ContinuousAtParts.At(z),
				real_exp_log.LogContinuous.At(size),
				SlitPlaneAbsPos.At(z),
				inSlit,
				complex_topology.ContinuousAtRealCompose.At(
					a.TermAs[Fun[Real, Real]]("real_log"),
					a.TermAs[Fun[Complex, Real]]("λw:complex. |w|"),
					z)))
		rotationContinuous := a.Have(
			"i·arg w is continuous at z, a constant times the continuous argument",
			"complex_continuous_at(λw:complex. complex_i * &(complex_arg(w)), z)",
			By(
				ArgContinuous.At(z),
				inSlit,
				complex_topology.ContinuousAtConst.At(z, a.TermAs[Complex]("complex_i")),
				complex_topology.ContinuousAtMul.At(
					a.TermAs[Fun[Complex, Complex]]("λw:complex. complex_i"),
					a.TermAs[Fun[Complex, Complex]]("λw:complex. &(complex_arg(w))"),
					z)))
		a.Show(
			"so is their sum log|w| + i·arg w, which is log w",
			By(
				logModulusContinuous,
				rotationContinuous,
				ComplexLogDef,
				complex_topology.ContinuousAtAdd.At(logModulus, rotation, z)))
	}),
})}

// LogDerivative — the derivative of the principal logarithm on the slit
// plane is 1/z: log is the inverse of exp there. It is continuous at z, exp
// undoes it on the disc of radius |z| about z, which misses 0, and exp has
// at log z the derivative exp(log z) = z ≠ 0, so the derivative of the
// inverse function is 1/z.
var LogDerivative = logDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LogDerivative",
	Key:  "prop_f38b1f12d6612747",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ slit_plane"},
		Conclusion: "complex_derivative_at(complex_log, z, complex_inv(z))",
	}, func(a *Argument, z *Expr[Complex], inSlit Fact) {
		positive := SlitPlaneAbsPos.At(z)
		nonzero := a.Have(
			"so z is not 0",
			"z ≠ &0",
			By(inSlit, positive, complex_abs.AbsPosIffNonzero.At(z)))
		undone := a.Have(
			"exp undoes log on the disc of radius |z| about z",
			"∀w:complex. |w - z| < |z| ⇒ exp(log(w)) = w",
			Derive(func(b *Argument) {
				w := b.FixAs[Complex]("w")
				near := b.Assume()
				apart := b.Have(
					"w is not 0: |z| − |w| ≤ |w − z| < |z|",
					"w ≠ &0",
					ByArith(near, complex_abs.AbsTriangleReverse.At(w, z), complex_abs.AbsPosIffNonzero.At(w)))
				b.Show(
					"and away from 0 exp undoes log",
					By(apart, ExpLog.At(w)))
			}))
		slope := a.Have(
			"exp has at log z the derivative exp(log z) = z",
			"complex_derivative_at(complex_exp, log(z), z)",
			By(
				Normalized,
				nonzero,
				complex_power_series.ExpDerivative.At(a.TermAs[Complex]("log(z)")),
				ExpLog.At(z)))
		a.Show(
			"log is continuous at z and undone by exp near z, where exp "+
				"has the nonzero derivative z: the inverse has derivative 1/z",
			By(
				inSlit,
				positive,
				nonzero,
				undone,
				slope,
				LogContinuous.At(z),
				At(
					complex_derivative.DerivativeInverse,
					a.TermAs[Fun[Complex, Complex]]("complex_exp"),
					a.TermAs[Fun[Complex, Complex]]("complex_log"),
					z,
					z,
					a.TermAs[Real]("|z|"))))
	}),
})}
