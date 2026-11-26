package trace_dual

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/registry"
)

// TraceDualDef — the field elements whose trace products with a test set lie
// in a prescribed set.
var TraceDualDef = traceDualDefThm{family.Define(registry.DefEntry{
	Name:  "TraceDualDef",
	Key:   "prop_683998ad138a3de0",
	Const: "trace_dual",
	Type:  "field_ops(A) → set(A) → set(A) → set(A) → set(A)",

	Equations: []string{
		"∀L:field_ops(A). ∀K B N:set(A). " +
			"    trace_dual(L, K, B, N) = " +
			"    {z:A | z ∈ L.carrier ∧ (∀b:A. b ∈ B ⇒ field_trace(L, K, L.mul(z, b)) ∈ N)}",
	},
})}

// TraceDualIsFunctionalDual — the trace dual is the functional dual at the
// field trace: the two definitions unfold to one set.
var TraceDualIsFunctionalDual = traceDualIsFunctionalDualThm{family.Add(registry.ProofEntry{
	Name: "TraceDualIsFunctionalDual",
	Key:  "prop_a9776adcf2af00c0",
	Build: family.Theorem("∀L:field_ops(A). ∀K B N:set(A). "+
		"    trace_dual(L, K, B, N) = functional_dual(field_ring(L), field_trace(L, K), B, N)",
		func(a *Argument, L *Expr[FieldOps[A]], K, B, N *Expr[Set[A]]) {
			a.Show(
				"both definitions unfold to the elements of L whose trace tests against B lie in N",
				Simp(Fwd(TraceDualDef), Fwd(functional_dual.FunctionalDualDef), Fwd(field.FieldRingDef)),
				Refl())
		}),
})}
