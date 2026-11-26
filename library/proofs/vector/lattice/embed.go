// embed.go — the two bridges: the form to Σ over ℤ, and ℤⁿ into ℝⁿ.
//
// `⟪u, v⟫_n` is `Σ_{i<n} u(i) * v(i)` by the two definitions, and the
// first bridge states it once. `vec_of_int` carries an integer sequence
// to the real sequence with the same entries, and the second bridge
// carries the form along: the two sums the form unfolds to are one fold
// read on either side of the representation map. Everything the chapter
// borrows from ℝ — the order theory of the form — enters through that
// identity. A real vector in a statement
// here spells its operations with their components, `dot⟨n⟩(real_add,
// real_mul, …)`: the chapter's binding is the integer ring's, and the
// parser reads that prefix as ℝ's by the arguments' types (the README
// says how).

package lattice

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"

	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/registry"
)

// DotIsSum — the form at ℤ is the Σ of the pointwise products: the two
// definitions name the same fold.
var DotIsSum = dotIsSumThm{family.Add(registry.ProofEntry{
	Name: "DotIsSum",
	Key:  "prop_b3c952edad188bb",
	Build: family.Theorem("∀n:num. ∀u v:(num → int). ⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)",
		func(a *Argument, n *Expr[Nat], u, v *Vec[Int, DimN]) {
			a.Do(Unfold(dot.DotDef), Unfold(int_sum.IntSumDef))
		}),
})}

// DotBridge — the form of two integer vectors, seen in ℝ, is the real
// form of their images. Both forms read as sums over the active range;
// the integer sum crosses into ℝ term by term, and each product crosses
// factor by factor.
var DotBridge = dotBridgeThm{family.Add(registry.ProofEntry{
	Name: "DotBridge",
	Key:  "prop_3864765dfb0be95e",
	Build: family.Theorem("∀n:num. ∀u v:(num → int). "+
		"    real_of_int(⟪u, v⟫_n) = dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))",
		func(a *Argument, n *Expr[Nat], u, v *Vec[Int, DimN]) {
			// Both forms read as sums over the active range, and an image's
			// entries are the entries seen in ℝ — the shape the two bridges
			// below match.
			a.Do(Simp(Fwd(DotIsSum), Fwd(euclidean.DotIsSum)), Unfold(VecOfIntDef))
			a.Show(
				"the integer sum crosses into ℝ over the finite range — the "+
					"transfer law at the index type ℕ — and each product factor by factor",
				Simp(
					Fwd(int_sum.IntSumBridge.Inst[Nat]()),
					Fwd(num_segment.FiniteBelowStrict),
					Fwd(int_construction.MulBridge)),
				Basic())
		}),
})}
