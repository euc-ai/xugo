package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var leastExtensionSectionDef = leastExtensionSectionDefThm{family.Define(registry.DefEntry{
	Name:  "leastExtensionSectionDef",
	Key:   "prop_7daa343c368fd902",
	Const: "least_extension_section",
	Type:  "ring_ops(B) → square_zero_ops(A, B, num, D) → B → num",
	Equations: []string{
		"∀S:ring_ops(B). ∀E:square_zero_ops(A, B, num, D). ∀y:B. " +
			"    least_extension_section(S, E, y) = " +
			"    COND(y = S.zero, " +
			"        E.ring.zero, " +
			"        εk:num. " +
			"            k ∈ E.ring.carrier ∧ " +
			"            E.projection(k) = y ∧ " +
			"            (∀j:num. j ∈ E.ring.carrier ∧ E.projection(j) = y ⇒ k ≤ j))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The least preimage on natural-number ring " +
		"codes, overridden at zero to preserve the fixed marking."})}

var countableExtensionTopologyDef = countableExtensionTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "countableExtensionTopologyDef",
	Key:   "prop_42d82aa3a05edb8",
	Const: "countable_extension_topology",
	Type:  "set(set(square_zero_ops(A, B, num, D)))",
	Equations: []string{
		"countable_extension_topology = " +
			"topology_generated_on(𝕌, " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i j k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.add(i, j) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i j k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.mul(i, j) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i j k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.sub(i, j) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.neg(i) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.zero = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃k:num. v = {E:square_zero_ops(A, B, num, D) | E.ring.one = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i:num. " +
			"            v = {E:square_zero_ops(A, B, num, D) | i ∈ E.ring.carrier} ∨ " +
			"            v = {E:square_zero_ops(A, B, num, D) | i ∉ E.ring.carrier}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃r:A. ∃k:num. v = {E:square_zero_ops(A, B, num, D) | E.structure(r) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃n:D. ∃k:num. v = {E:square_zero_ops(A, B, num, D) | E.inclusion(n) = k}} ∪ " +
			"    {v:set(square_zero_ops(A, B, num, D)) | " +
			"        ∃i:num. ∃y:B. v = {E:square_zero_ops(A, B, num, D) | E.projection(i) = y}})",
	},
	Deps: []registry.EntryLike{},
	Reading: "The pointwise discrete topology on the carrier predicate, " +
		"ring operation tables and marking tables of extensions on num."})}

var CountableRingCodeExtraction = countableRingCodeExtractionThm{family.Add(registry.ProofEntry{
	Name: "CountableRingCodeExtraction",
	Key:  "prop_9dd4cc526c4a8562",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "continuous_map(subtopology(countable_extension_topology, " +
				"        {E:square_zero_ops(A, B, num, D) | square_zero_extension(R, S, f, N, E)}), " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    λE:square_zero_ops(A, B, num, D). " +
				"        factor_set_extract(R, S, N, E, least_extension_section(S, E)))",
		},
		"Near a fixed valid code each least preimage is certified by finitely many "+
			"tests below its value. The inverse inclusion value used by extraction is "+
			"certified by the single inclusion coordinate at that value. Ring operations "+
			"and markings are pointwise continuous; override the zero section explicitly."),
	Deps: []registry.EntryLike{
		leastExtensionSectionDef,
		countableExtensionTopologyDef,
		FactorSetRealization,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Near a fixed valid code each least preimage is certified by finitely " +
		"many tests below its value. The inverse inclusion value used by extraction is " +
		"certified by the single inclusion coordinate at that value. Ring operations " +
		"and markings are pointwise continuous; override the zero section explicitly.",
})}

var CountableRingCodeClassification = countableRingCodeClassificationThm{family.Add(registry.ProofEntry{
	Name: "CountableRingCodeClassification",
	Key:  "prop_577b400595596c21",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀E F:square_zero_ops(A, B, num, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"square_zero_extension(R, S, f, N, E)",
				"square_zero_extension(R, S, f, N, F)",
			},
			Conclusion: "(∃p:(num → num). square_zero_isomorphism(R, N, E, F, p)) ⇔ " +
				"factor_set_ambient(R, S, N).mul(factor_set_extract(R, S, N, E, least_extension_section(S, E)), " +
				"    factor_set_ambient(R, S, N).inv( " +
				"        factor_set_extract(R, S, N, F, least_extension_section(S, F)))) ∈ " +
				"factor_set_boundaries(R, S, f, N)",
		},
		"Both extracted codes realize their marked extensions; "+
			"FactorSetIsoIffBoundary gives the equivalence."),
	Deps: []registry.EntryLike{
		CountableRingCodeExtraction,
		FactorSetRealization,
		FactorSetIsoIffBoundary,
	},
	Reading: "Both extracted codes realize their marked " +
		"extensions; FactorSetIsoIffBoundary gives the equivalence.",
})}
