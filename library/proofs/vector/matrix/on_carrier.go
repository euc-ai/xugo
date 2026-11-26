// on_carrier.go — the matrix product read inside a ring's carrier: its
// definition, which starts each entry's sum at the ring's zero, and the
// theorem that on a commutative ring whose carrier is the whole type it
// is the form-based product matrix_mul.

package matrix

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/registry"
)

var MatrixProductDef = matrixProductDefThm{family.Define(registry.DefEntry{
	Name: "MatrixProductDef",
	Key:  "prop_efdd8835ed40c6a2",
	Reading: "The carrier-ring product starts its finite sum at the specified ring " +
		"zero. The dot-based matrix_mul uses the identity of addition on the whole host type.",
	Deps:  []registry.EntryLike{},
	Const: "matrix_product",
	Type:  "ring_ops(A) → num → (num → num → A) → (num → num → A) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P Q:(num → num → A). ∀i j:num. " +
			"    matrix_product(R, n, P, Q, i, j) = " +
			"    module_sum(R.add, R.zero, {k:num | k < n}, λk:num. R.mul(P(i, k), Q(k, j)))",
	},
})}

// MatrixProductAgrees — on a commutative ring whose carrier is the whole
// type, the carrier-ring product of two matrices is the product read off
// the form: entry by entry, both are the finite sum over k < n of
// P(i, k) * Q(k, j). The carrier product folds that sum from the ring's
// zero, the form iterates the addition, and the two folds agree because
// the addition and the zero are a commutative monoid on the whole type.
var MatrixProductAgrees = matrixProductAgreesThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductAgrees",
	Key:  "prop_b3eb7bf938ae8cc6",
	Reading: "The universe premise includes dimension zero: an operation " +
		"may have a different global identity outside a proper ring carrier.",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{
			"c.carrier = 𝕌",
		},
		Conclusion: "matrix_product(c, n, P, Q) = matrix_mul(n, P, Q)",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P, Q *Arrow2[Nat, Nat, A],
			universe Fact,
		) {
			monoid := a.Have(
				"with the whole type for carrier, the ring's addition and zero form a commutative monoid",
				"comm_monoid(c.add, c.zero)",
				By(comm_ring.AddMonoidOn.Read(c), universe, comm_monoid.CommMonoidOnUniverse))
			a.Do(Funext())
			a.FixAs[Nat]("i")
			a.FixAs[Nat]("j")
			a.Show(
				"at entry (i, j) both products sum P(i, k) * Q(k, j) over k < n, "+
					"and on that finite range the fold from c.zero is the iterated sum",
				Unfold(MatrixProductDef),
				Unfold(MatrixMulDef),
				Unfold(dot.DotDef),
				Unfold(TransposeDef),
				By(module.ModuleSumIteratedOp.Read(monoid), num_segment.FiniteBelowStrict.At(n)))
		}),
})}
