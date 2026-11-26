package cech_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CechIndicesCountable — The zero-tail tuples are the image of finite sequences of natural numbers of length n+1.
var CechIndicesCountable = cechIndicesCountableThm{family.Add(registry.ProofEntry{
	Name: "CechIndicesCountable",
	Key:  "prop_74aa946c34a5aca1",
	Deps: []registry.EntryLike{
		cardinal.CountableFiniteSubsets,
		cardinal.NumPairCountable,
		cardinal.CardLeCountable,
		num_segment.FiniteBelow,
		finite_set.FiniteImage,
	},
	Build: family.Card(
		"∀n:num. countable(cech_indices(n))",
		"The zero-tail tuples are the image of finite sequences of natural numbers of length n+1. "+
			"A tuple is fixed by its graph below n + 1, a finite set of pairs of naturals "+
			"(FiniteBelow, FiniteImage), and that map is injective; the finite subsets of the "+
			"countable ℕ × ℕ are countable (NumPairCountable, CountableFiniteSubsets, CardLeCountable)."),
})}

// CountableCoverCechPolishModel — Finite deletion support gives the continuity of the countable-cover Cech differential.
var CountableCoverCechPolishModel = countableCoverCechPolishModelThm{family.Add(registry.ProofEntry{
	Name: "CountableCoverCechPolishModel",
	Key:  "prop_7ce0c585c5afb9a1",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)).",
		Hypotheses: []string{
			"cech_datum(R, T, F, res, U)",
		},
		Conclusion: "polish_cochain_complex(R, cech_complex(R, F, res, U), cech_topologies(F, U))",
	},
		"Presheaf restriction composition gives the alternating cochain-complex laws. Each "+
			"degree term is the normalized product of the countable section groups of its tuples "+
			"with pointwise operations, a Polish abelian group by DiscreteProductGroupPolish; for "+
			"each active output tuple the differential reads only its finitely many deletion tuples, "+
			"so FiniteCoordinateContinuous supplies continuity after verifying carrier preservation."),
	Deps: []registry.EntryLike{
		CechIndicesCountable,
		polish_group.DiscreteProductGroupPolish,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Section carriers may vary with the tuple. For an output tuple of " +
		"degree n+1 the finite input support is the set of its n+2 deletion tuples. " +
		"Inactive coordinates keep the same coordinate-dependent zero in every degree; " +
		"algebraic cancellation proving d squared zero remains a separate obligation.",
})}

// CechRefinementContinuous — Refinement uses one old coordinate followed by a section restriction.
var CechRefinementContinuous = cechRefinementContinuousThm{family.Add(registry.ProofEntry{
	Name: "CechRefinementContinuous",
	Key:  "prop_a7f62fb06973328a",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U V:(num → set(A)). " +
			"∀r:(num → num).",
		Hypotheses: []string{
			"cech_datum(R, T, F, res, U)",
			"cech_datum(R, T, F, res, V)",
			"∀i:num. V(i) ⊆ U(r(i))",
		},
		Conclusion: "polish_cochain_map(R, " +
			"    cech_complex(R, F, res, U), " +
			"    cech_topologies(F, U), " +
			"    cech_complex(R, F, res, V), " +
			"    cech_topologies(F, V), " +
			"    cech_refinement_map(F, res, U, V, r))",
	},
		"Refinement commutes with the alternating restriction differential and carries normalized "+
			"cochains into the refined carrier. Each active output tuple reads only its refined old "+
			"tuple before restriction, so FiniteCoordinateContinuous supplies degreewise continuity."),
	Deps: []registry.EntryLike{
		CountableCoverCechPolishModel,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "The coordinate carriers are the section modules of possibly different " +
		"intersections. Singleton-coordinate dependence supplies continuity, while " +
		"presheaf restriction and the refinement containment supply carrier preservation.",
})}

// CechRefinementHomotopy — Tuple deletion is used in positive degree at valid positions. Refinement choices need only yield algebraic homotopies to induce identical maps on cohomology.
var CechRefinementHomotopy = cechRefinementHomotopyThm{family.Add(registry.ProofEntry{
	Name: "CechRefinementHomotopy",
	Key:  "prop_1db65e763e4b9fdd",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U V:(num → set(A)). " +
			"∀r s:(num → num).",
		Hypotheses: []string{
			"cech_datum(R, T, F, res, U)",
			"cech_datum(R, T, F, res, V)",
			"∀i:num. V(i) ⊆ U(r(i)) ∧ V(i) ⊆ U(s(i))",
		},
		Conclusion: "∃h:(num → (prod(num, num → num) → C) → prod(num, num → num) → C). " +
			"    cochain_homotopy(R, " +
			"        cech_complex(R, F, res, U), " +
			"        cech_complex(R, F, res, V), " +
			"        cech_refinement_map(F, res, U, V, r), " +
			"        cech_refinement_map(F, res, U, V, s), " +
			"        h)",
	},
		"Use the prism sum mixing the r-prefix and s-suffix of each tuple, restricting "+
			"every term to the refined intersection. Adjacent terms cancel in d h + h d."),
	Deps: []registry.EntryLike{CechRefinementContinuous},
	Reading: "Tuple deletion is used in positive degree at valid positions. Refinement " +
		"choices need only yield algebraic homotopies to induce identical maps on cohomology.",
})}

// CechRefinementDefinableIso — A refinement alone does not force equality of cover cohomology, and an unrelated abstract group isomorphism is not the required hypothesis.
var CechRefinementDefinableIso = cechRefinementDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "CechRefinementDefinableIso",
	Key:  "prop_3e732ae58d4aeb00",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U V:(num → set(A)). " +
			"∀r:(num → num). " +
			"∀n:num.",
		Hypotheses: []string{
			"cech_datum(R, T, F, res, U)",
			"cech_datum(R, T, F, res, V)",
			"∀i:num. V(i) ⊆ U(r(i))",
			"module_isomorphism(R, " +
				"    cohomology_module(cech_complex(R, F, res, U), n), " +
				"    cohomology_module(cech_complex(R, F, res, V), n), " +
				"    cohomology_map(cech_complex(R, F, res, V), cech_refinement_map(F, res, U, V, r), n))",
		},
		Conclusion: "cohomology_borel_iso(cech_complex(R, F, res, U), " +
			"    cech_topologies(F, U), " +
			"    n, " +
			"    cech_complex(R, F, res, V), " +
			"    cech_topologies(F, V), " +
			"    n, " +
			"    cohomology_map(cech_complex(R, F, res, V), cech_refinement_map(F, res, U, V, r), n))",
	},
		"Apply ContinuousQuasiIsoDefinableIso in degree n to the actual refinement map. The ordinary "+
			"isomorphism hypothesis is essential and can be supplied by an acyclic-cover comparison."),
	Deps: []registry.EntryLike{
		CechRefinementContinuous,
		polish_cohomology.ContinuousQuasiIsoDefinableIso,
	},
	Reading: "A refinement alone does not force equality of cover cohomology, " +
		"and an unrelated abstract group isomorphism is not the required hypothesis.",
})}

// CechCountableOrContinuum — Countable-cover Čech cohomology with countable sections is countable or has at least continuum many classes.
var CechCountableOrContinuum = cechCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "CechCountableOrContinuum",
	Key:  "prop_9080a1abec956111",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)). " +
			"∀n:num.",
		Hypotheses: []string{
			"cech_datum(R, T, F, res, U)",
		},
		Conclusion: "countable(cohomology(cech_complex(R, F, res, U), n)) ∨ " +
			"card_le(𝕌⟨A:set(num)⟩, cohomology(cech_complex(R, F, res, U), n))",
	}, "CohomologyCountableOrContinuum at the Polish model of CountableCoverCechPolishModel."),
	Deps: []registry.EntryLike{
		CountableCoverCechPolishModel,
		polish_cohomology.CohomologyCountableOrContinuum,
	},
	Reading: "This is the cohomology of the one cover, not of the space.",
})}
