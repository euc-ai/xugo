// parity.go — the cosine is even and the sine odd, read off the series
// through the ring's laws for the powers of a negation; and with Euler's
// formula at z and at −z, the cosine and the sine through the
// exponential.

package complex_exp

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/registry"
)

// CosNeg — the cosine is even: an even power forgets the sign (the
// ring's law at ℂ), so the series at −z is the series at z, which sums
// to cos(−z) and to cos(z), and a series has one sum.
var CosNeg = cosNegThm{family.Add(registry.ProofEntry{
	Name: "CosNeg",
	Key:  "prop_875323f8d6fee84d",
	Build: family.Theorem("∀z:complex. cos(-z) = cos(z)",
		func(arg *Argument, z *Expr[Complex]) {
			even := arg.Have(
				"an even power forgets the sign, the ring's law at ℂ",
				"∀n:num. (-z) ^ (2 * n) = z ^ (2 * n)",
				By(comm_ring.NegPowEven.Read(complex_field.CommRing)))
			same := arg.Have(
				"so the series at −z is the series at z, term by term",
				"(λn:num. "+
					"    complex_of_real(real_pow(-&1, n)) * (-z) ^ (2 * n) / complex_of_real(&factorial(2 * n))) = "+
					"λn:num. complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n))",
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action { return By(even.At(n)) }))
			atNeg := arg.Have(
				"so the series at z sums to cos(−z)",
				"complex_sums(λn:num. "+
					"        complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)), "+
					"    cos(-z))",
				same.RwRev(),
				By(CosSums.At(arg.TermAs[Complex]("-z"))))
			arg.Show(
				"it sums to cos z as well, and a series has one sum",
				By(atNeg, CosSums.At(z), complex_series.SumsUnique))
		}),
})}

// SinNeg — the sine is odd: an odd power keeps the sign (the ring's law
// at ℂ), so the series at −z is −1 times the series at z, which sums to
// −1·sin z; it sums to sin(−z) as well.
var SinNeg = sinNegThm{family.Add(registry.ProofEntry{
	Name: "SinNeg",
	Key:  "prop_f870f5cbf753f340",
	Build: family.Theorem("∀z:complex. sin(-z) = -sin(z)",
		func(arg *Argument, z *Expr[Complex]) {
			// No single law of the ring says this; it is stated over
			// variables, where comparing parts touches no power.
			negatedFactor := arg.Have(
				"a negated factor turns a quotient into −1 times it",
				"∀c y u:complex. c * -y / u = -complex_of_real(&1) * (c * y / u)",
				Derive(func(d *Argument) {
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.Show(
						"both sides have the same parts",
						Simp(
							complex_field.Parts,
							Fwd(complex_field.ComplexDivDef),
							Fwd(complex_field.ComplexMulDef),
							Fwd(complex_field.ComplexNegDef),
							Fwd(complex_field.ComplexOfRealDef)),
						ByArith())
				}))
			odd := arg.Have(
				"an odd power keeps the sign, the ring's law at ℂ",
				"∀n:num. (-z) ^ (2 * n + 1) = -(z ^ (2 * n + 1))",
				By(comm_ring.NegPowOdd.Read(complex_field.CommRing)))
			scaled := arg.Have(
				"so the series at −z is −1 times the series at z, term by term",
				"(λn:num. "+
					"    complex_of_real(real_pow(-&1, n)) * "+
					"    (-z) ^ (2 * n + 1) / "+
					"    complex_of_real(&factorial(2 * n + 1))) = "+
					"λn:num. "+
					"    -complex_of_real(&1) * "+
					"    (complex_of_real(real_pow(-&1, n)) * "+
					"        z ^ (2 * n + 1) / "+
					"        complex_of_real(&factorial(2 * n + 1)))",
				Funext(),
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					power := d.Have(
						"the n-th term's odd power of −z",
						"(-z) ^ (2 * n + 1) = -(z ^ (2 * n + 1))",
						By(odd))
					d.Show(
						"so the n-th term at −z is −1 times the one at z",
						power.Rw(),
						By(negatedFactor))
				}))
			atNeg := arg.Have(
				"so −1 times the series at z sums to sin(−z)",
				"complex_sums(λn:num. "+
					"        -complex_of_real(&1) * "+
					"        (complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1))), "+
					"    sin(-z))",
				scaled.RwRev(),
				By(SinSums.At(arg.TermAs[Complex]("-z"))))
			atZ := arg.Have(
				"and to −1 times sin z",
				"complex_sums(λn:num. "+
					"        -complex_of_real(&1) * "+
					"        (complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1))), "+
					"    -complex_of_real(&1) * sin(z))",
				By(SinSums.At(z), complex_series.SumsScale))
			unique := arg.Have(
				"a series has one sum",
				"sin(-z) = -complex_of_real(&1) * sin(z)",
				By(atNeg, atZ, complex_series.SumsUnique))
			arg.Show(
				"and −1·sin z is −sin z, the ring's law at ℂ",
				unique.Rw(),
				By(comm_ring.NegOneMul.Read(complex_field.CommRing)))
		}),
})}

// CosExp — the cosine through the exponential: Euler's formula at z and
// at −z gives exp(i·z) = cos z + i·sin z and, the cosine being even and
// the sine odd, exp(−i·z) = cos z − i·sin z; their mean is cos z.
var CosExp = cosExpThm{family.Add(registry.ProofEntry{
	Name: "CosExp",
	Key:  "prop_c92a278416259abe",
	Build: family.Theorem("∀z:complex. "+
		"    cos(z) = (exp(complex_i * z) + exp(-(complex_i * z))) / complex_of_real(&2)",
		func(arg *Argument, z *Expr[Complex]) {
			flip := arg.Have(
				"−(i·z) is i·(−z), the ring's law at ℂ",
				"-(complex_i * z) = complex_i * -z",
				By(comm_ring.MulRightNeg.Read(complex_field.CommRing)))
			half := arg.Have(
				"the inverse of 2 is the embedded inverse of 2",
				"complex_inv(complex_of_real(&2)) = complex_of_real(real_inv(&2))",
				By(complex_field.OfRealInv))
			mean := arg.Have(
				"the mean of c + i·s and c + i·(−s) is c",
				"∀c s:complex. c = (c + complex_i * s + (c + complex_i * -s)) / complex_of_real(&2)",
				Derive(func(d *Argument) {
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.Show(
						"dividing by 2 is multiplying by the embedded 1/2, and then both sides have the same parts",
						Simp(Fwd(complex_field.ComplexDivDef)),
						half.Rw(),
						Simp(
							complex_field.Parts,
							Fwd(complex_field.ComplexAddDef),
							Fwd(complex_field.ComplexMulDef),
							Fwd(complex_field.ComplexNegDef),
							Fwd(complex_field.ComplexOfRealDef),
							Fwd(complex_field.ComplexIDef)),
						ByArith())
				}))
			arg.Show(
				"Euler's formula at z and at −z, the cosine even and the sine odd",
				flip.Rw(),
				Simp(Fwd(Euler)),
				Simp(Fwd(CosNeg), Fwd(SinNeg)),
				By(mean))
		}),
})}

// SinExp — the sine through the exponential: the difference of the same
// two values is 2i·sin z.
var SinExp = sinExpThm{family.Add(registry.ProofEntry{
	Name: "SinExp",
	Key:  "prop_8f62dbc72d2281bb",
	Build: family.Theorem("∀z:complex. "+
		"    sin(z) = (exp(complex_i * z) - exp(-(complex_i * z))) / (complex_of_real(&2) * complex_i)",
		func(arg *Argument, z *Expr[Complex]) {
			flip := arg.Have(
				"−(i·z) is i·(−z), the ring's law at ℂ",
				"-(complex_i * z) = complex_i * -z",
				By(comm_ring.MulRightNeg.Read(complex_field.CommRing)))
			inverse := arg.Have(
				"the inverse of 2i is the embedded 1/2 times the inverse of i, which is −i",
				"complex_inv(complex_of_real(&2) * complex_i) = complex_of_real(real_inv(&2)) * -complex_i",
				Simp(
					Fwd(field.InvMul.Read(complex_field.Field)),
					Rev(complex_field.OfRealInv),
					Fwd(complex_field.InvI)),
				Basic())
			difference := arg.Have(
				"the difference of c + i·s and c + i·(−s) is 2i·s",
				"∀c s:complex. s = (c + complex_i * s - (c + complex_i * -s)) / (complex_of_real(&2) * complex_i)",
				Derive(func(d *Argument) {
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.Show(
						"dividing by 2i is multiplying by −i/2, and then both sides have the same parts",
						Simp(Fwd(complex_field.ComplexDivDef)),
						inverse.Rw(),
						Simp(
							complex_field.Parts,
							Fwd(complex_field.ComplexSubDef),
							Fwd(complex_field.ComplexAddDef),
							Fwd(complex_field.ComplexMulDef),
							Fwd(complex_field.ComplexNegDef),
							Fwd(complex_field.ComplexOfRealDef),
							Fwd(complex_field.ComplexIDef)),
						ByArith())
				}))
			arg.Show(
				"Euler's formula at z and at −z, the cosine even and the sine odd",
				flip.Rw(),
				Simp(Fwd(Euler)),
				Simp(Fwd(CosNeg), Fwd(SinNeg)),
				By(difference))
		}),
})}
