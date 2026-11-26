// parts.go — the parts of each operation: the real and the imaginary
// part of a sum, a negative, a difference, a product, an inverse, a
// conjugate, a real number and i, each read off the operation's
// definition. A proof that wants the parts of `z * w` cites the law, at
// the one place it wants them.

package complex_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// PartsAdd — a sum is taken part by part.
var PartsAdd = partsAddThm{family.Add(registry.ProofEntry{
	Name: "PartsAdd",
	Key:  "prop_8015824fdca32030",
	Build: family.Theorem("∀z w:complex. re(z + w) = re(z) + re(w) ∧ im(z + w) = im(z) + im(w)",
		Chain(Simp(Fwd(ComplexAddDef)), ByArith())),
})}

// PartsNeg — and so is a negative.
var PartsNeg = partsNegThm{family.Add(registry.ProofEntry{
	Name: "PartsNeg",
	Key:  "prop_2ee40f0fa85a1254",
	Build: family.Theorem("∀z:complex. re(-z) = -re(z) ∧ im(-z) = -im(z)",
		Chain(Simp(Fwd(ComplexNegDef)), ByArith())),
})}

// PartsSub — and a difference, a sum with a negative.
var PartsSub = partsSubThm{family.Add(registry.ProofEntry{
	Name: "PartsSub",
	Key:  "prop_3b454a3ef86e3d41",
	Build: family.Theorem("∀z w:complex. re(z - w) = re(z) - re(w) ∧ im(z - w) = im(z) - im(w)",
		Chain(Simp(Fwd(ComplexSubDef), Fwd(ComplexAddDef), Fwd(ComplexNegDef)), ByArith())),
})}

// PartsMul — the parts of a product: the real part is the product of
// the real parts less that of the imaginary parts, the imaginary part
// the sum of the two cross products.
var PartsMul = partsMulThm{family.Add(registry.ProofEntry{
	Name: "PartsMul",
	Key:  "prop_cc06e410c2525a8d",
	Build: family.Theorem(
		"∀z w:complex. "+
			"    re(z * w) = re(z) * re(w) - im(z) * im(w) ∧ im(z * w) = re(z) * im(w) + im(z) * re(w)",
		Chain(Simp(Fwd(ComplexMulDef)), ByArith())),
})}

// PartsInv — the parts of an inverse: those of the conjugate, each over
// the square sum of the parts.
var PartsInv = partsInvThm{family.Add(registry.ProofEntry{
	Name: "PartsInv",
	Key:  "prop_bd9a18089cd9c880",
	Build: family.Theorem(
		"∀z:complex. "+
			"    re(complex_inv(z)) = re(z) / (re(z) * re(z) + im(z) * im(z)) ∧ "+
			"    im(complex_inv(z)) = -im(z) / (re(z) * re(z) + im(z) * im(z))",
		Chain(Simp(Fwd(ComplexInvDef)), ByArith())),
})}

// PartsConj — conjugation keeps the real part and negates the
// imaginary part.
var PartsConj = partsConjThm{family.Add(registry.ProofEntry{
	Name: "PartsConj",
	Key:  "prop_793c1aba403661e6",
	Build: family.Theorem("∀z:complex. re(conj(z)) = re(z) ∧ im(conj(z)) = -im(z)",
		Chain(Simp(Fwd(ComplexConjDef)), ByArith())),
})}

// PartsOfReal — a real number seen in ℂ has itself as its real part
// and no imaginary part.
var PartsOfReal = partsOfRealThm{family.Add(registry.ProofEntry{
	Name: "PartsOfReal",
	Key:  "prop_488c226e59406c27",
	Build: family.Theorem("∀x:real. re(complex_of_real(x)) = x ∧ im(complex_of_real(x)) = &0",
		Chain(Simp(Fwd(ComplexOfRealDef)), ByArith())),
})}

// PartsI — i has no real part, and imaginary part 1.
var PartsI = partsIThm{family.Add(registry.ProofEntry{
	Name: "PartsI",
	Key:  "prop_4d43550d59a84a6",
	Build: family.Theorem("re(complex_i) = &0 ∧ im(complex_i) = &1",
		Chain(Simp(Fwd(ComplexIDef)), ByArith())),
})}
