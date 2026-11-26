package trace_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// TraceDualSubmodule — the trace dual of an S-submodule of K, tested against a
// subring B, is a B-submodule of L.
var TraceDualSubmodule = traceDualSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "TraceDualSubmodule",
	Key:  "prop_545b07668e619d08",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S B N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"subring(field_ring(L), B)",
			"submodule(«ScalarS», «VectorsK», N)",
		},
		Conclusion: "submodule(«ScalarB», «Regular», trace_dual(L, K, B, N))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K, S, B, N *Expr[Set[A]],
		subK, finite, subringB, subN Fact,
	) {
		a.Show(
			"the trace dual is the functional dual of the K-linear trace",
			Simp(Fwd(TraceDualIsFunctionalDual)),
			By(
				subK,
				finite,
				subringB,
				subN,
				field_trace.FieldTraceLinear.Read(L).At(K),
				functional_dual.FunctionalDualSubmodule.Read(L).At(
					K, a.TermAs[Fun[A, A]]("field_trace(L, K)"), S, B, N)))
	}),
})}

var TraceDualMonotone = traceDualMonotoneThm{family.Add(registry.ProofEntry{
	Name: "TraceDualMonotone",
	Key:  "prop_e8f3de8c9e1c8de0",
	Deps: []registry.EntryLike{TraceDualDef},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K X Y N P:set(A).",
		Hypotheses: []string{
			"X ⊆ Y",
			"N ⊆ P",
		},
		Conclusion: "trace_dual(L, K, Y, N) ⊆ trace_dual(L, K, X, P)",
	},
		"A smaller test set imposes fewer conditions, and a larger target permits "+
			"more trace values. This uses the defining membership condition only."),
})}

var TraceDualHomIso = traceDualHomIsoThm{family.Add(registry.ProofEntry{
	Name: "TraceDualHomIso",
	Key:  "prop_8f2ef00d8ddb5bf1",
	Reading: "The function is zero off B. The codomain uses the B precomposition " +
		"action rather than pointwise B multiplication on the target N.",
	Deps: []registry.EntryLike{
		TraceDualSubmodule,
		linear_pairing.NondegeneratePairingDualityIso,
		hom_module.CoextendScalarsDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B E N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"finite(E)",
			"module_basis(«ScalarS», restrict_module(«Regular», B), E)",
			"module_basis(«ScalarK», «Regular», E)",
			"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
			"submodule(«ScalarS», «VectorsK», N)",
		},
		Conclusion: "module_isomorphism(«ScalarB», " +
			"    restrict_module(«Regular», trace_dual(L, K, B, N)), " +
			"    coextend_scalars(«ScalarS», «ScalarB», λa:A. a, restrict_module(«Regular», N)), " +
			"    λz:A. λb:A. COND(b ∈ B, field_trace(L, K, z * b), L.zero))",
	},
		"Extend a map on the common S-basis to a K-linear functional on L. "+
			"Nondegenerate pairing duality represents it uniquely by trace "+
			"multiplication; the B-action is precomposition, as in coextend_scalars."),
})}

var TraceDualValueInvertible = traceDualValueInvertibleThm{family.Add(registry.ProofEntry{
	Name: "TraceDualValueInvertible",
	Key:  "prop_61aa69e52314c60c",
	Deps: []registry.EntryLike{
		TraceDualSubmodule,
		invertible_fractional_ideal.InvertiblePartitionOfUnity,
		field_trace.FieldTraceLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"invertible_fractional(«ScalarK», S, N)",
		},
		Conclusion: "trace_dual(L, K, B, N) = fractional_mul(field_ring(L), B, N, trace_dual(L, K, B, S))",
	},
		"One containment follows by trace linearity. For the other, expand one by the partition "+
			"of unity for N and its inverse and move each inverse base-field factor through the trace."),
})}

var TraceDualTestIdealInvertible = traceDualTestIdealInvertibleThm{family.Add(registry.ProofEntry{
	Name: "TraceDualTestIdealInvertible",
	Key:  "prop_26a736405ade477f",
	Deps: []registry.EntryLike{
		TraceDualSubmodule,
		invertible_fractional_ideal.InvertiblePartitionOfUnity,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B I N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"submodule(«ScalarS», «VectorsK», N)",
			"invertible_fractional(field_ring(L), B, I)",
		},
		Conclusion: "trace_dual(L, K, I, N) = " +
			"fractional_mul(field_ring(L), B, fractional_inverse(field_ring(L), B, I), trace_dual(L, K, B, N))",
	},
		"Products from I⁻¹D(B,N) satisfy all I-tests. Conversely use the partition "+
			"of unity of I and I⁻¹ to express a tested element as a sum in that product."),
})}
