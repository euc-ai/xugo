// dot.go — what the form does at ℤ: the two order facts read through
// the embedding, and definiteness by the generic argument.
//
// The order theory of the form is ℝ's — an
// inequality at ℤ is the inequality of the representatives, and the
// representative of the form is the real form of the image — so
// positivity, and that a null vector is orthogonal to everything, are
// the real theorems read at the images. Definiteness is not an order
// fact: with null-implies-orthogonal in hand, the equality of two
// integer vectors is non-degeneracy's, a law of the generic chapter,
// and nothing passes through ℝ.

package lattice

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// DotPosLe — the form at ℤ is positive semidefinite. The inequality at ℤ
// is the inequality of the representatives; the representative of the
// integer zero is the real zero and that of the form is the real form of
// the image, which is positive semidefinite.
var DotPosLe = dotPosLeThm{family.Add(registry.ProofEntry{
	Name: "DotPosLe",
	Key:  "prop_7c0757fb372c5719",
	Build: family.Theorem("∀n:num. ∀u:(num → int). &0 ≤ ⟪u, u⟫_n",
		func(a *Argument, n *Expr[Nat], u *Vec[Int, DimN]) {
			a.Do(Simp(int_construction.InReals, Fwd(DotBridge)))
			image := a.VecAs[Real, DimN]("vec_of_int(u)")
			a.Show(
				"the real form of the image is positive semidefinite",
				By(euclidean.DotPosLe.At(image)))
		}),
})}

// NullVectorOrthogonal — an integer vector null for the form is
// orthogonal to every integer vector. Both equations are equations of
// the representatives, the representative of the integer zero is the
// real zero and that of the form is the real form of the images: read
// through the embedding, the statement is the real theorem at the images.
var NullVectorOrthogonal = nullVectorOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "NullVectorOrthogonal",
	Key:  "prop_b0190f918b2bc37c",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u v:(num → int).",
		Hypotheses: []string{
			"⟪u, u⟫_n = &0",
		},
		Conclusion: "⟪u, v⟫_n = &0",
	},
		func(a *Argument, n *Expr[Nat], u, v *Vec[Int, DimN]) {
			a.Do(Simp(int_construction.InReals, Fwd(DotBridge)))
			imageU := a.VecAs[Real, DimN]("vec_of_int(u)")
			imageV := a.VecAs[Real, DimN]("vec_of_int(v)")
			a.Show(
				"at the images this is the real theorem",
				By(euclidean.NullVectorOrthogonal.At(imageU, imageV)))
		}),
})}

// DotEqZero — on a dimension the form at ℤ is DEFINITE: the zero
// vector is the only null n-vector. Definiteness's one order-dependent
// input is that a null vector be orthogonal to everything, which the
// chapter already holds at ℤ; the generic law does the rest, and
// nothing passes through ℝ.
var DotEqZero = dotEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DotEqZero",
	Key:  "prop_d51fca14ec8652de",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u:(num → int).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "⟪u, u⟫_n = &0 ⇔ u = vec_zero",
	},
		func(a *Argument, n *Expr[Nat], u *Vec[Int, DimN], member Fact) {
			nullOrthogonal := a.Have(
				"a null vector is orthogonal to everything — the one thing definiteness asks of ℤ",
				"∀v w:(num → int). ⟪v, v⟫_n = &0 ⇒ ⟪v, w⟫_n = &0",
				By(NullVectorOrthogonal))
			a.Show(
				"and the generic law does the rest",
				By(nullOrthogonal, dot.Definite.Read(int_real_lift.CommRing).At(proof.Inhabit(u, member))))
		}),
})}
