package module_test

// typed_reading_test.go — a closure law's typed At on a reading of a
// projection (prover/proof's ReadMember at a reading's content): the
// member form and the bare reading as a premise name the same fact.

import (
	"testing"

	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/prover/proof"
)

// A closure law's typed At on the reading of a projection names its
// member from the reading's statement: SmulIn read at HomSource read at
// the homomorphism's fact, grounded at the scalar and the vector, is the
// membership of the scaled vector — the fact the bare reading cited
// beside the two points proves.
func TestTypedReading_ClosureAtAReadingOfAProjection(t *testing.T) {
	statement := "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀c:A. " +
		"∀u:B. module_homomorphism(R, M, N, f) ∧ c ∈ R.carrier ∧ u ∈ M.carrier ⇒ M.smul(c, u) ∈ M.carrier"
	type closure = func(
		a *Argument,
		R *Expr[module_record.RingOps[A]],
		M *Expr[module_record.ModuleOps[A, B]],
		N *Expr[module_record.ModuleOps[A, C]],
		f *Arrow[B, C],
		c *Expr[A],
		u *Expr[B],
		given Fact,
	)
	body := func(spell func(
		b *Argument,
		hom Fact,
		cm *Member[A, on.Any],
		um *Member[B, on.Any],
	) Action) closure {
		return func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			M *Expr[module_record.ModuleOps[A, B]],
			N *Expr[module_record.ModuleOps[A, C]],
			f *Arrow[B, C],
			c *Expr[A],
			u *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism",
				"c is a scalar",
				"u is a vector of M")
			cm, um := proof.MemberOf(c, parts[1]), proof.MemberOf(u, parts[2])
			a.Show(
				"M is closed under scaling",
				spell(a, parts[0], cm, um))
		}
	}
	t.Run("the member form", func(t *testing.T) {
		runLaw(t, bundles.Theorem(statement, body(func(
			b *Argument,
			hom Fact,
			cm *Member[A, on.Any],
			um *Member[B, on.Any],
		) Action {
			return By(module.SmulIn.Read(module_homomorphism.HomSource.Read(hom)).At(cm, um))
		})), module.SmulIn, module_homomorphism.HomSource)
	})
	t.Run("the bare reading beside the points", func(t *testing.T) {
		runLaw(t, bundles.Theorem(statement, body(func(
			b *Argument,
			hom Fact,
			cm *Member[A, on.Any],
			um *Member[B, on.Any],
		) Action {
			return By(module.SmulIn.Read(module_homomorphism.HomSource.Read(hom)), cm, um)
		})), module.SmulIn, module_homomorphism.HomSource)
	})
}
