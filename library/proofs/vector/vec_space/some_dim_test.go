package vec_space

// The dimension-refined surface at a dimension no letter spells: a
// vector anchored at a term (a.VecAt) or at the dimension its membership
// fact spells (proof.InhabitFrom) carries SomeDim, and the generated
// typed cite takes it like any other phantom, writing the dimension off
// the vector. Exercised against VecDef's own wrapper, the way a
// polynomial chapter reads `vec⟨suc(polynomial_degree(p))⟩(zero, p)`.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
)

// someDimEnv is a replay env with VecDef trusted: the member itself is
// replayed by the corpus harness, and this test exercises the typed
// seam around it (cartesian/carrier/vectors_test.go does the same with
// ConcatClosed).
func someDimEnv(t *testing.T, name string) *proof.ProverEnv {
	env := testenv.MakeT(t)
	env.Scope = proof.NewProofScope(core.PropKey(name))
	def := VecDef.Entry().Statement().Prop
	hyps := make([]core.Term, def.NumHyps())
	for i := range hyps {
		hyps[i] = def.Hyp(i)
	}
	env.LibraryThms[VecDef.DepName()] = core.TestThm(def.Conclusion(), hyps...)
	return env
}

func proveSomeDim(t *testing.T, env *proof.ProverEnv, statement string, body any) {
	t.Helper()
	top, graph := family.Theorem(statement, body).Fn(env)
	for i, section := range graph.SectionThms() {
		if cert, _ := core.ForceWithBoundary(
			context.Background(), section, func(core.Prop) bool { return false }); cert.IsZero() {
			t.Fatalf("section %d yielded no certificate", i)
		}
	}
	if cert, _ := core.ForceWithBoundary(
		context.Background(), top, func(core.Prop) bool { return false }); cert.IsZero() {
		t.Fatal("the theorem yielded no certificate")
	}
}

func TestSomeDimCite(t *testing.T) {
	const vanishes = "∀zero:A. ∀p:(num → A). ∀k:num. " +
		"vec⟨suc(k)⟩(zero, p) ⇒ (∀i:num. suc(k) ≤ i ⇒ p(i) = zero)"
	t.Run("anchored at the term", func(t *testing.T) {
		proveSomeDim(t, someDimEnv(t, "some_dim_at_term"), vanishes,
			func(a *Argument, zero *Expr[A], p *Arrow[Nat, A], k *Expr[Nat], member Fact) {
				v := proof.Inhabit(a.VecAt[A](a.TermAs[Nat]("suc(k)"), "p"), member)
				a.Show(
					"p vanishes from suc(k) on",
					By(VecDef.At(zero, v.Vec), v.Evidence()))
			})
	})
	t.Run("anchored by the membership", func(t *testing.T) {
		proveSomeDim(t, someDimEnv(t, "some_dim_from_fact"), vanishes,
			func(a *Argument, zero *Expr[A], p *Arrow[Nat, A], k *Expr[Nat], member Fact) {
				v := proof.InhabitFrom(p, member)
				a.Show(
					"p vanishes from suc(k) on",
					By(VecDef.At(zero, v.Vec), v.Evidence()))
			})
	})
	t.Run("at a literal", func(t *testing.T) {
		proveSomeDim(t, someDimEnv(
			t, "some_dim_literal"), "∀zero:A. ∀p:(num → A). vec⟨0⟩(zero, p) ⇒ (∀i:num. 0 ≤ i ⇒ p(i) = zero)",
			func(a *Argument, zero *Expr[A], p *Arrow[Nat, A], member Fact) {
				v := proof.InhabitFrom(p, member)
				a.Show(
					"p vanishes everywhere",
					By(VecDef.At(zero, v.Vec), v.Evidence()))
			})
	})
}
