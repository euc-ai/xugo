package engine

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// A partially grounded local law uses the same derived instance clause
// as its typed Go cite, including when several type letters coalesce.
func TestBy_LocalPrefixInstanceUsesDerivedClause(t *testing.T) {
	const law = "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀u:(A → B). ∀v:(A → C). ∀x y:A. ring_homomorphism(R, S, u) ∧ ring_homomorphism(R, T, v) ∧ ring_kernel(ring_zero(S), ring_carrier(R), u) ⊆ ring_kernel(ring_zero(T), ring_carrier(R), v) ∧ x ∈ ring_carrier(R) ∧ y ∈ ring_carrier(R) ∧ u(x) = u(y) ⇒ v(x) = v(y)"
	const goal = "∀R:ring_ops(num → A). ∀S T:ring_ops(A). ∀u v:((num → A) → A). ∀x y:(num → A). ring_homomorphism(R, S, u) ∧ ring_homomorphism(R, T, v) ∧ ring_kernel(ring_zero(S), ring_carrier(R), u) ⊆ ring_kernel(ring_zero(T), ring_carrier(R), v) ∧ x ∈ ring_carrier(R) ∧ y ∈ ring_carrier(R) ∧ u(x) = u(y) ⇒ v(x) = v(y)"
	for _, pin := range []bool{false, true} {
		t.Run(map[bool]string{false: "inferred", true: "explicit"}[pin], func(t *testing.T) {
			e, s := boundSession(t, "algebra/ring/ring_homomorphism")
			addTextGoal(t, s, law)
			source := s.sections[0].root
			require.True(t, proof.ApplyCiteKnown(source, core.TestThm(source.Goal.Conclusion())))
			addTextGoal(t, s, goal)
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
			premise := LemmaWithSpec{Text: law, TermSpecialize: map[string]string{"R": "R₀", "S": "S₀", "T": "T₀", "u": "u₀", "v": "v₀"}}
			if pin {
				premise.TypeSpecialize = map[string]string{"A": "num → A", "B": "A", "C": "A"}
			}
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByShape: &ByShapeReq{Normalized: true}, ByHyps: []ByHypSpec{hyp(0)}, WithLemmas: []LemmaWithSpec{premise}})
			require.True(t, s.sections[1].root.Proved())
		})
	}
}
