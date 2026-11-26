// Integer sums inherit recursion and transport from the fold mechanism.

package int_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// IntSumClauses — the recursion at ℤ's addition.
var IntSumClauses = intSumClausesThm{family.Add(registry.ProofEntry{
	Name: "IntSumClauses",
	Key:  "prop_ad74b3b551176fad",
	Build: family.Theorem(
		"(∀f:(A → int). sum(∅, f) = &0) ∧ "+
			"(∀g:(C → int). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ sum(insert(x, s), g) = COND(x ∈ s, sum(s, g), g(x) + sum(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(IntSumDef), By(monoidal.Clauses, int_real_lift.MonoidalAdd, int_real_lift.NeutralAdd))
		}),
})}

// IntSumBridge — the transfer law `monoidal.Homomorphic` at
// `real_of_int`, from ℤ's addition to ℝ's.
//
// That the embedding fixes the neutral element is a claim about
// `neutral_elem(int_add)` and `neutral_elem(real_add)`, which are what the law
// speaks of; the two carriers say those are their zeros, and the
// numeral bridge at 0 identifies the zeros across the embedding.
var IntSumBridge = intSumBridgeThm{family.Add(registry.ProofEntry{
	Name: "IntSumBridge",
	Key:  "prop_954a5d29447d28df",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → int).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "real_of_int(sum(s, f)) = sum(s, λi:A. real_of_int(f(i)))",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Int], finite Fact) {
			// Each sum is the fold at its carrier's addition.
			a.Do(Unfold(IntSumDef), Unfold(real_sum.RealSumDef))

			fixesNeutral := a.Have(
				"the embedding fixes the neutral element",
				"real_of_int(neutral_elem(int_add)) = neutral_elem(real_add)",
				Simp(Fwd(int_real_lift.NeutralAdd), Fwd(real_ring.NeutralAdd)),
				Cite(int_construction.OfNumBridge, a.Ctx().Nat(0)))

			a.Show(
				"so the transfer law carries the fold across the embedding",
				By(
					finite,
					fixesNeutral,
					monoidal.Homomorphic,
					int_real_lift.MonoidalAdd,
					real_ring.MonoidalAdd,
					int_construction.AddBridge))
		}),
})}
