package functional_dual

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// FunctionalDualDef — The ring elements whose products with a test set take values of the functional in a prescribed set.
var FunctionalDualDef = functionalDualDefThm{family.Define(registry.DefEntry{
	Name:  "FunctionalDualDef",
	Key:   "prop_616fbeb2251a47e8",
	Deps:  []registry.EntryLike{},
	Const: "functional_dual",
	Type:  "ring_ops(A) → (A → A) → set(A) → set(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀l:(A → A). ∀B N:set(A). " +
			"    functional_dual(R, l, B, N) = {z:A | z ∈ R.carrier ∧ (∀b:A. b ∈ B ⇒ l(R.mul(z, b)) ∈ N)}",
	},
})}

// FunctionalDualMember — z lies in the dual exactly when it lies in the
// ring and every test against B lands in N: the definition's set-builder
// read at z.
var FunctionalDualMember = functionalDualMemberThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualMember",
	Key:  "prop_4e38410152fe39f4",
	Build: family.Theorem("∀R:ring_ops(A). ∀l:(A → A). ∀B N:set(A). ∀z:A. "+
		"    z ∈ functional_dual(R, l, B, N) ⇔ z ∈ R.carrier ∧ (∀b:A. b ∈ B ⇒ l(R.mul(z, b)) ∈ N)",
		func(a *Argument, R *Expr[RingOps[A]], l *Arrow[A, A], B, N *Expr[Set[A]], z *Expr[A]) {
			a.Show(
				"the set-builder read at z",
				Unfold(FunctionalDualDef),
				SetTacMembership())
		}),
})}
