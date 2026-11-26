package sequence_hilbert

import "github.com/euc-ai/xugo/library/registry"

var UnorderedSumRelationDef = unorderedSumRelationDefThm{family.Define(registry.DefEntry{
	Name:  "UnorderedSumRelationDef",
	Key:   "prop_296ea8d1a974d86e",
	Const: "unordered_complex_sums",
	Type:  "set(I) → (I → complex) → complex → bool",
	Equations: []string{
		"∀J:set(I). ∀a:(I → complex). ∀z:complex. " +
			"    unordered_complex_sums(J, a, z) ⇔ " +
			"    ∀ε:real. " +
			"        &0 < ε ⇒ " +
			"        ∃F:set(I). " +
			"            finite(F) ∧ " +
			"            F ⊆ J ∧ " +
			"            ∀G:set(I). " +
			"                finite(G) ∧ F ⊆ G ∧ G ⊆ J ⇒ " +
			"                |module_sum(complex_add, complex_of_real(&0), G, a) - z| < ε",
	},
})}

var UnorderedSumDef = unorderedSumDefThm{family.Define(registry.DefEntry{
	Name:  "UnorderedSumDef",
	Key:   "prop_e49c68fed30b3fe4",
	Const: "unordered_complex_sum",
	Type:  "set(I) → (I → complex) → complex",
	Deps:  []registry.EntryLike{UnorderedSumRelationDef},
	Reading: "The chosen value has its summation meaning only when the finite-subset " +
		"net converges. The empty set has sum zero, once existence and uniqueness are applied.",
	Equations: []string{
		"∀J:set(I). ∀a:(I → complex). " +
			"    unordered_complex_sum(J, a) = εz:complex. unordered_complex_sums(J, a, z)",
	},
})}

var WeightedSquareSummableDef = weightedSquareSummableDefThm{family.Define(registry.DefEntry{
	Name:  "WeightedSquareSummableDef",
	Key:   "prop_9dbf59122c95d4a7",
	Const: "weighted_square_summable",
	Type:  "set(I) → (I → real) → (I → complex) → bool",
	Equations: []string{
		"∀J:set(I). ∀w:(I → real). ∀u:(I → complex). " +
			"    weighted_square_summable(J, w, u) ⇔ " +
			"    (∀i:I. i ∉ J ⇒ u(i) = complex_of_real(&0)) ∧ " +
			"    ∃C:real. ∀F:set(I). finite(F) ∧ F ⊆ J ⇒ real_sum(F, λi:I. w(i) * real_pow(|u(i)|, 2)) ≤ C",
	},
})}

var SequenceModuleDef = sequenceModuleDefThm{family.Define(registry.DefEntry{
	Name:  "SequenceModuleDef",
	Key:   "prop_f1834a35123150b9",
	Const: "weighted_sequence_module",
	Type:  "set(I) → (I → real) → module_ops(complex, I → complex)",
	Deps:  []registry.EntryLike{WeightedSquareSummableDef},
	Equations: []string{
		"∀J:set(I). ∀w:(I → real). " +
			"    weighted_sequence_module(J, w) = " +
			"    mk_module(λu:(I → complex). λv:(I → complex). λi:I. u(i) + v(i), " +
			"        λi:I. complex_of_real(&0), " +
			"        λu:(I → complex). λi:I. -u(i), " +
			"        λc:complex. λu:(I → complex). λi:I. c * u(i), " +
			"        {u:(I → complex) | weighted_square_summable(J, w, u)})",
	},
})}

var SequenceInnerDef = sequenceInnerDefThm{family.Define(registry.DefEntry{
	Name:  "SequenceInnerDef",
	Key:   "prop_37049d204ffd9f17",
	Const: "weighted_sequence_inner",
	Type:  "set(I) → (I → real) → (I → complex) → (I → complex) → complex",
	Deps:  []registry.EntryLike{UnorderedSumDef},
	Equations: []string{
		"∀J:set(I). ∀w:(I → real). ∀u v:(I → complex). " +
			"    weighted_sequence_inner(J, w, u, v) = " +
			"    unordered_complex_sum(J, λi:I. complex_of_real(w(i)) * u(i) * complex_conj(v(i)))",
	},
})}

var SequenceTruncateDef = sequenceTruncateDefThm{family.Define(registry.DefEntry{
	Name:  "SequenceTruncateDef",
	Key:   "prop_bad6b464b5c3b3b0",
	Const: "sequence_truncate",
	Type:  "set(I) → (I → complex) → I → complex",
	Equations: []string{
		"∀F:set(I). ∀u:(I → complex). ∀i:I. " +
			"    sequence_truncate(F, u, i) = COND(i ∈ F, u(i), complex_of_real(&0))",
	},
})}
