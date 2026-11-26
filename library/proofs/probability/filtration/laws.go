// laws.go — a filtration is increasing in time: its successive inclusions
// compose to every later time.

package filtration

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/registry"
)

// FiltrationMono — a filtration is increasing in time: its successive inclusions compose.
var FiltrationMono = filtrationMonoThm{family.Add(registry.ProofEntry{
	Name: "FiltrationMono",
	Key:  "prop_71179b713868c320",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀m n:num.",
		Hypotheses: []string{"filtration_on(Ω, S, F)", "m ≤ n"},
		Conclusion: "F(m) ⊆ F(n)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		F *Arrow[Nat, Set[Set[A]]],
		m, n *Expr[Nat],
		h Fact,
	) {
		a.Show(
			"the successive inclusions compose from m to n",
			By(h, FiltrationDef.At(Ω, S, F), order.IncreasingFromSteps.At(F, m, n)))
	}),
})}
