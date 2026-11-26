// Closed supports control restriction, zero extension and composition.

package function_support

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

var SupportClosed = supportClosedThm{family.Add(registry.ProofEntry{
	Name: "SupportClosed",
	Key:  "prop_4d0c54d13e5a0854",
	Deps: []registry.EntryLike{SupportDef, topological_space.ClosureClosed},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f:(A → B).",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "closed_in(T, function_support(T, z, f))",
	},
		"The nonzero locus is contained in the space carrier by definition. "+
			"ClosureClosed therefore makes its closure a closed subset of that carrier."),
})}

var SupportEmpty = supportEmptyThm{family.Add(registry.ProofEntry{
	Name: "SupportEmpty",
	Key:  "prop_301b486c6aa49a64",
	Deps: []registry.EntryLike{
		SupportDef,
		topological_space.SubsetClosure,
		topological_space.ClosureEmpty,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f:(A → B).",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "function_support(T, z, f) = ∅ ⇔ (∀x:A. x ∈ ⋃T ⇒ f(x) = z)",
	},
		"If the support is empty, the nonzero locus contained in it is empty. Conversely a "+
			"function equal to z on the carrier has empty nonzero locus, whose closure is empty."),
})}

var SupportCongruence = supportCongruenceThm{family.Add(registry.ProofEntry{
	Name: "SupportCongruence",
	Key:  "prop_457bef7030d4bb6c",
	Deps: []registry.EntryLike{SupportDef},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f g:(A → B).",
		Hypotheses: []string{"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)"},
		Conclusion: "function_support(T, z, f) = function_support(T, z, g)",
	},
		"Agreement on the carrier identifies the two guarded nonzero loci before "+
			"taking closure. No topology axiom or agreement outside the carrier is needed."),
})}

var SupportOutside = supportOutsideThm{family.Add(registry.ProofEntry{
	Name: "SupportOutside",
	Key:  "prop_a78c805c8f2d9833",
	Reading: "No topology axiom is needed: the intersection defining " +
		"closure contains the original nonzero locus for every family T.",
	Deps: []registry.EntryLike{SupportDef, topological_space.SubsetClosure},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{"x ∈ ⋃T", "x ∉ function_support(T, z, f)"},
		Conclusion: "f(x) = z",
	},
		"A carrier point with value different from z lies in the nonzero locus and hence "+
			"in its closure. The contrapositive gives the claimed value outside support."),
})}

var SupportClosedBound = supportClosedBoundThm{family.Add(registry.ProofEntry{
	Name: "SupportClosedBound",
	Key:  "prop_c27e372907cb82a5",
	Reading: "No topology axiom is needed: the supplied closed bound " +
		"is one of the sets intersected in the definition of closure.",
	Deps: []registry.EntryLike{SupportDef, topological_space.ClosureMinimal},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f:(A → B). ∀K:set(A).",
		Hypotheses: []string{"closed_in(T, K)", "∀x:A. x ∈ ⋃T ∧ x ∉ K ⇒ f(x) = z"},
		Conclusion: "function_support(T, z, f) ⊆ K",
	},
		"The vanishing hypothesis places the nonzero locus in K. "+
			"Minimality of closure inside a closed set gives the support bound."),
})}

var SupportRestrictOpen = supportRestrictOpenThm{family.Add(registry.ProofEntry{
	Name: "SupportRestrictOpen",
	Key:  "prop_661feb03a0f44fa2",
	Reading: "Openness of U is essential: a restriction to a closed " +
		"singleton can erase all nonzero values approaching that point.",
	Deps: []registry.EntryLike{
		SupportDef,
		topological_space.ClosureSubtopology,
		topological_space.OpenInterClosure,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀f:(A → B). ∀U:set(A).",
		Hypotheses: []string{"is_topology(T)", "U ∈ T"},
		Conclusion: "function_support(subtopology(T, U), z, f) = U ∩ function_support(T, z, f)",
	},
		"The restricted nonzero locus is the original one intersected with U. ClosureSubtopology and "+
			"OpenInterClosure identify its subspace closure with U intersected with the original support."),
})}

var SupportExtendZero = supportExtendZeroThm{family.Add(registry.ProofEntry{
	Name: "SupportExtendZero",
	Key:  "prop_803e436040c4a5b6",
	Reading: "Being closed only in U does not suffice. Ambient closedness of " +
		"the subspace support keeps all extension-boundary points outside it; " +
		"compact support in U supplies this condition in a Hausdorff ambient space.",
	Deps: []registry.EntryLike{
		SupportDef,
		SupportClosedBound,
		topological_space.ClosureSubtopology,
		topological_space.ClosureIdempotent,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀z:B. ∀f:(A → B). ∀U:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"U ∈ T",
			"closed_in(T, function_support(subtopology(T, U), z, f))",
		},
		Conclusion: "function_support(T, z, normalize_on(U, z, f)) = " +
			"function_support(subtopology(T, U), z, f)",
	},
		"The extended function has exactly the nonzero locus of the restriction. Its subspace closure "+
			"is already closed in the ambient space, so taking the ambient closure adds no boundary points."),
})}

var SupportProduct = supportProductThm{family.Add(registry.ProofEntry{
	Name: "SupportProduct",
	Key:  "prop_20a5ae41969221d6",
	Deps: []registry.EntryLike{
		SupportOutside,
		SupportClosed,
		SupportClosedBound,
		topological_space.InterClosed,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀z:B. ∀w:C. ∀v:D. ∀f:(A → B). ∀g:(A → C). ∀h:(B → C → D).",
		Hypotheses: []string{"is_topology(T)", "∀b:B. h(b, w) = v", "∀c:C. h(z, c) = v"},
		Conclusion: "function_support(T, v, λx:A. h(f(x), g(x))) ⊆ " +
			"function_support(T, z, f) ∩ function_support(T, w, g)",
	},
		"Either input taking its distinguished value forces the output to v. Thus the "+
			"combined function vanishes outside the closed intersection of the supports."),
})}

var SupportPullback = supportPullbackThm{family.Add(registry.ProofEntry{
	Name: "SupportPullback",
	Key:  "prop_ef0dd28b10489c4",
	Deps: []registry.EntryLike{
		SupportOutside,
		SupportClosed,
		SupportClosedBound,
		continuous.ClosedPreimage,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀S:set(set(B)). ∀z:C. ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{"is_topology(T)", "is_topology(S)", "continuous_map(T, S, f)"},
		Conclusion: "function_support(T, z, g ∘ f) ⊆ preimage_on(⋃T, f, function_support(S, z, g))",
	},
		"Continuity makes the carrier-relative preimage of the closed target support closed. Carrier "+
			"preservation and SupportOutside make the composite equal to z outside this preimage."),
})}

var SupportHomeomorphism = supportHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "SupportHomeomorphism",
	Key:  "prop_4f5074e2eabc2402",
	Deps: []registry.EntryLike{
		SupportPullback,
		SupportCongruence,
		continuous.HomeomorphismInverse,
		continuous.HomeomorphismContinuous,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀S:set(set(B)). ∀z:C. ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{"is_topology(T)", "is_topology(S)", "homeomorphic_map(T, S, f)"},
		Conclusion: "function_support(T, z, g ∘ f) = preimage_on(⋃T, f, function_support(S, z, g))",
	},
		"Apply SupportPullback to the homeomorphism and its inverse. Their inverse equations on "+
			"the carriers identify the twice-composed function with g and give the reverse inclusion."),
})}
