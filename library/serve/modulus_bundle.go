package serve

import (
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// installModulus binds omega's reading of a modulus to ℂ's, as
// complex_abs states it: the sign, the laws that carry the modulus
// across ℂ's product, inverse, quotient, power, negation and
// conjugation, across the embedding of ℝ and to the imaginary unit, and
// the two of the zero test. The arith closer reads them where a proof's
// scope admits arith:modulus: a modulus of a compound term is rewritten
// toward the leaves, `&0 ≤ |z|` stands beside a decision's hypotheses,
// and a modulus and its argument are known zero, or not zero, together.
//
// The laws are their own capability. Its foundation is what they rest
// on, complex_abs's own members among them, and a proof there may not
// read the modulus through them.
func installModulus() {
	laws := &omega.ModulusLaws{
		Nonneg: fromEntryAsStated(complex_abs.AbsNonneg),
		Mul:    fromEntryAsStated(complex_abs.AbsMul),
		Inv:    fromEntryAsStated(complex_abs.AbsInv),
		Div:    fromEntryAsStated(complex_abs.AbsDiv),
		Pow:    fromEntryAsStated(complex_abs.AbsPow),
		Neg:    fromEntryAsStated(complex_abs.AbsNeg),
		Conj:   fromEntryAsStated(complex_abs.AbsConj),
		OfReal: fromEntryAsStated(complex_abs.AbsOfReal),
		Unit:   fromEntryAsStated(complex_abs.AbsI),

		EqZero:        fromEntryAsStated(complex_abs.AbsEqZero),
		PosIffNonzero: fromEntryAsStated(complex_abs.AbsPosIffNonzero),
	}
	omega.SetModulusLaws(laws)
	roots, foundation := computeBundleCapability(laws)
	omega.SetModulusFoundation(foundation)
	installCapability(proof.CapabilityArithModulus, roots, foundation)
}
