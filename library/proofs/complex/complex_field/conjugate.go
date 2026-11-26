// conjugate.go — conjugation, the reflection that fixes the reals and
// sends i to −i, is an automorphism of the field; a number times its
// conjugate is the square sum of its parts, which is multiplicative.

package complex_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ConjConj — conjugating twice is the identity.
var ConjConj = conjConjThm{family.Add(registry.ProofEntry{
	Name: "ConjConj",
	Key:  "prop_efe2c53cf13f5943",
	Build: family.Theorem("∀z:complex. conj(conj(z)) = z",
		Chain(Simp(Parts, Fwd(ComplexConjDef)), ByArith())),
})}

// ConjAdd — the conjugate of a sum is the sum of the conjugates.
var ConjAdd = conjAddThm{family.Add(registry.ProofEntry{
	Name: "ConjAdd",
	Key:  "prop_399089fbe33c702c",
	Build: family.Theorem("∀z w:complex. conj(z + w) = conj(z) + conj(w)",
		Chain(Simp(Parts, Fwd(ComplexConjDef), Fwd(ComplexAddDef)), ByArith())),
})}

// ConjMul — the conjugate of a product is the product of the
// conjugates: negating both imaginary parts leaves the real part of the
// product alone and negates its imaginary part.
var ConjMul = conjMulThm{family.Add(registry.ProofEntry{
	Name: "ConjMul",
	Key:  "prop_d46daaae25676746",
	Build: family.Theorem("∀z w:complex. conj(z * w) = conj(z) * conj(w)",
		Chain(Simp(Parts, Fwd(ComplexConjDef), Fwd(ComplexMulDef)), ByArith())),
})}

// ConjOfReal — conjugation fixes the reals.
var ConjOfReal = conjOfRealThm{family.Add(registry.ProofEntry{
	Name: "ConjOfReal",
	Key:  "prop_659caa97765ef7fd",
	Build: family.Theorem("∀x:real. conj(complex_of_real(x)) = complex_of_real(x)",
		Chain(Simp(Parts, Fwd(ComplexConjDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// ConjI — and sends i to −i.
var ConjI = conjIThm{family.Add(registry.ProofEntry{
	Name: "ConjI",
	Key:  "prop_cbec1b3dd7fd9aa3",
	Build: family.Theorem("conj(complex_i) = -complex_i",
		Chain(Simp(Parts, Fwd(ComplexConjDef), Fwd(ComplexIDef), Fwd(ComplexNegDef)), ByArith())),
})}

// MulConj — a number times its conjugate is the real number
// re(z)² + im(z)²: the cross terms of the imaginary part cancel.
var MulConj = mulConjThm{family.Add(registry.ProofEntry{
	Name: "MulConj",
	Key:  "prop_c96bae9b67524464",
	Build: family.Theorem("∀z:complex. z * conj(z) = complex_of_real(re(z) * re(z) + im(z) * im(z))",
		Chain(Simp(Parts, Fwd(ComplexConjDef), Fwd(ComplexMulDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// SquareSumMul — the square sum of the parts of a product of two complex
// numbers is the product of their square sums: the parts of the product
// are differences and sums of products of the parts, and what is left is
// the identity of two squares, arithmetic in ℝ.
var SquareSumMul = squareSumMulThm{family.Add(registry.ProofEntry{
	Name: "SquareSumMul",
	Key:  "prop_2340eee979315771",
	Build: family.Theorem(
		Statement{
			Binders:    "∀z w:complex.",
			Conclusion: "«SquareSum»(z * w) = «SquareSum»(z) * «SquareSum»(w)",
			Abbrev:     Abbrev{{Name: "SquareSum", Text: "λz:complex. re(z) * re(z) + im(z) * im(z)"}},
		},
		func(a *Argument, z, w *Expr[Complex]) {
			a.Show(
				"compute the parts of the product; the two-squares identity is arithmetic",
				Simp(Fwd(ComplexMulDef)),
				ByArith())
		}),
})}

// ConjInv — the conjugate of an inverse is the inverse of the conjugate.
// Conjugation fixes the reals, zero and one among them, and respects
// products, so it carries inverses to inverses (field.MapInv).
var ConjInv = conjInvThm{family.Add(registry.ProofEntry{
	Name: "ConjInv",
	Key:  "prop_cbeb3bf815de8f60",
	Build: family.Theorem("∀z:complex. conj(complex_inv(z)) = complex_inv(conj(z))",
		func(a *Argument, z *Expr[Complex]) {
			complexes := a.TermAs[field.FieldOps[Complex]]("restrict_field(complex_field_ops, 𝕌)")
			whole := a.Have(
				"ℂ is a field on the whole of ℂ",
				"field_on(restrict_field(complex_field_ops, 𝕌))",
				By(Field, field.FieldOnUniverse))
			a.Show(
				"conjugation respects zero, one and products, so it carries inverses to inverses",
				By(
					field.MapInv.At(complexes, complexes, a.TermAs[Fun[Complex, Complex]]("complex_conj"), z),
					whole,
					ConjMul,
					ConjOfReal,
					set_basic.InUniv))
		}),
})}
