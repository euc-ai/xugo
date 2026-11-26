package id_derivation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/do_derivation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/latent_projection"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	"github.com/euc-ai/xugo/library/registry"
)

var TopologicalListExists = topologicalListExistsThm{family.Add(registry.ProofEntry{
	Name: "TopologicalListExists",
	Key:  "prop_f3d3e87409bd1e0f",
	Reading: "O ⊆ V makes O finite; the edges of a DAG are " +
		"well founded, so a sink of what is left is removed last.",
	Deps: []registry.EntryLike{dag.DagSinkExists},
	Build: family.Card(Statement{
		Binders:    "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I).",
		Hypotheses: []string{"dag_on(V, E)", "O ⊆ V"},
		Conclusion: "∃l:list(I). dag_topological_list(E, O, l)",
	},
		"The observed nodes of a DAG have a topological list: by induction on the finite set O, "+
			"a nonempty O has a node that is an ancestor of no other node of O (DagSinkExists on the "+
			"reversed relation's transitive closure), which is listed last after a list of the rest."),
})}

var DerivableAncestralTransfer = derivableAncestralTransferThm{family.Add(registry.ProofEntry{
	Name: "DerivableAncestralTransfer",
	Key:  "prop_d50f3177736a3e24",
	Reading: "The parent-closure of P is load-bearing: it makes every separation the rules ask among " +
		"nodes of P the same in the restricted and the full graph, edge deletions keeping P parent-closed.",
	Deps: []registry.EntryLike{
		do_derivation.DoDerivableInduct,
		d_separation.DSeparatedAncestralRestrict,
	},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀P O:set(I). ∀e₁ e₂:do_expr(I).",
		Hypotheses: []string{
			"dag_ancestral(E, P)",
			"do_derivable(relation_on(P, E), O ∩ P, e₁, e₂)",
		},
		Conclusion: "do_derivable(E, O, e₁, e₂)",
	},
		"A derivation in the restriction of the graph to a parent-closed set P, with the observed "+
			"nodes in P, is a derivation in the graph. By rule induction: each rule's sets lie in O ∩ "+
			"P, so in O; the causal rules' graphs are the restrictions to P of the same deletions of "+
			"the full graph, in which P stays parent-closed, so their separations hold there "+
			"(DSeparatedAncestralRestrict), and the ancestors Rule 3 reads are the same in both."),
})}

var DerivableInterveneTransfer = derivableInterveneTransferThm{family.Add(registry.ProofEntry{
	Name: "DerivableInterveneTransfer",
	Key:  "prop_5d96588f8b9556c1",
	Reading: "D ⊆ O is load-bearing: the intervened atoms must stay well formed. The " +
		"subproblem's sums bind nodes of O ∖ D and the intervened atoms read D freely, " +
		"so no value is captured. The rules whose right side is the constant 1 transfer " +
		"through the empty event, the intervened constant being do_prob(∅, D, ∅).",
	Deps: []registry.EntryLike{
		do_derivation.DoDerivableInduct,
		do_derivation.DoDerivableRules,
		d_separation.DSeparatedRemoveIntervene,
	},
	Build: family.Card(Statement{
		Binders:    "∀E:(I → I → bool). ∀O D:set(I). ∀e₁ e₂:do_expr(I).",
		Hypotheses: []string{"D ⊆ O", "do_derivable(relation_on(𝕌 ∖ D, E), O ∖ D, e₁, e₂)"},
		Conclusion: "do_derivable(E, O, do_expr_intervene(D, e₁), do_expr_intervene(D, e₂))",
	},
		"A derivation in the graph with the observed nodes D removed transfers to the graph with D "+
			"intervened on in every atom. By rule induction: a causal rule's separation in G[V ∖ D], with "+
			"its own deletions, is separation given D ∪ X ∪ W in G with the edges into X ∪ D deleted "+
			"(DSeparatedRemoveIntervene), which is the rule at the intervention group X ∪ D; Rule 3's "+
			"ancestors outside D agree, Z missing D. The probability and algebraic rules transfer "+
			"unchanged, the constant 1 becoming do_prob(∅, D, ∅), which the empty event derives back to 1."),
})}

var DistrictDerivable = districtDerivableThm{family.Add(registry.ProofEntry{
	Name: "DistrictDerivable",
	Key:  "prop_1e2cdcbef43d89d7",
	Reading: "S must be a district of the projection on all of O; a " +
		"district of a subset is not identified this way. The conditioning " +
		"set of each factor is every observed predecessor, inside S or not.",
	Deps: []registry.EntryLike{
		do_derivation.DoDerivableRules,
		latent_projection.DistrictPredecessorSeparation,
		d_separation.DSeparatedIsolatedRoots,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O S:set(I). ∀l:list(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"S ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O)",
			"dag_topological_list(E, O, l)",
		},
		Conclusion: "do_derivable(E, O, do_prob(S, O ∖ S, ∅), do_chain(S, list_reverse(l)))",
	},
		"Tian's identification of a district: Q[S] = P_{O ∖ S}(S) = Π_{v_i ∈ S} P(v_i | v_π^{(i−1)}). "+
			"Expand P_{O ∖ S}(S) by conditioning along the list into Π_{v ∈ S} P_{O ∖ S}(v | P_v ∩ S), P_v "+
			"the nodes before v. Rule 3 drops the intervention on the nodes after v, none an ancestor of v "+
			"or of P_v, their edges in deleted (DSeparatedIsolatedRoots); Rule 2 turns the intervention on "+
			"P_v ∖ S into observation (DistrictPredecessorSeparation). Each factor becomes P(v | P_v)."),
})}

var DistrictFactorization = districtFactorizationThm{family.Add(registry.ProofEntry{
	Name: "DistrictFactorization",
	Key:  "prop_bc01f7b35c3c2c22",
	Reading: "The list L enumerates the districts once each; any order serves, derivability " +
		"being closed under commuting and reassociating products. With O empty both sides are 1.",
	Deps: []registry.EntryLike{
		DistrictDerivable,
		TopologicalListExists,
		mixed_graph.DistrictsPartition,
		do_derivation.DoDerivableRules,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀L:list(set(I)).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"list_distinct(L)",
			"∀C:set(I). list_member(C, L) ⇔ C ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O)",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(O, ∅, ∅), " +
			"    do_prod(list_map(λC:set(I). do_prob(C, O ∖ C, ∅), L)))",
	},
		"Tian's factorization: the joint law is the product over the districts S of Q[S] = P_{O ∖ "+
			"S}(S). Take a topological list (TopologicalListExists); conditioning along it gives P(O) = "+
			"Π_{v ∈ O} P(v | v_π^{(i−1)}), the districts partition O (DistrictsPartition), so the product "+
			"regroups as Π_S do_chain(S, ·), and each group derives back to Q[S] (DistrictDerivable)."),
})}

var DistrictAtomDerivable = districtAtomDerivableThm{family.Add(registry.ProofEntry{
	Name: "DistrictAtomDerivable",
	Key:  "prop_d9a3c1981656d2da",
	Reading: "A and C must lie in S and be disjoint; the intervention group is " +
		"exactly O ∖ S. The outer sums run over nodes of S only, so the chain's " +
		"free nodes outside S keep the environment's values, the intervened ones.",
	Deps: []registry.EntryLike{DistrictDerivable, do_derivation.DoDerivableRules},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O S A C:set(I). ∀l:list(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"S ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O)",
			"dag_topological_list(E, O, l)",
			"A ⊆ S",
			"C ⊆ S",
			"A ∩ C = ∅",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(A, O ∖ S, C), " +
			"    do_div(do_sum(S ∖ (A ∪ C), do_chain(S, list_reverse(l))), " +
			"        do_sum(S ∖ C, do_chain(S, list_reverse(l)))))",
	},
		"Every conditional of Q[S] is observational: P_{O ∖ S}(A | C) is the quotient of the "+
			"marginals of P_{O ∖ S}(S) on A ∪ C and on C, by conditioning and marginalisation, and P_{O "+
			"∖ S}(S) is the chain (DistrictDerivable) under the sum congruence. This is how the seventh "+
			"line's output, the subproblem's expression with O ∖ S′ intervened, becomes observational."),
})}

var IdLineOne = idLineOneThm{family.Add(registry.ProofEntry{
	Name:    "IdLineOne",
	Key:     "prop_5d705bb16f74f666",
	Reading: "No graph hypothesis: it is marginalisation read backwards.",
	Deps:    []registry.EntryLike{do_derivation.DoDerivableRules},
	Build: family.Card(Statement{
		Binders:    "∀E:(I → I → bool). ∀O Y:set(I).",
		Hypotheses: []string{"Y ⊆ O"},
		Conclusion: "do_derivable(E, O, do_prob(Y, ∅, ∅), do_sum(O ∖ Y, do_prob(O, ∅, ∅)))",
	},
		"ID's first line: with no intervention the query is the marginal of the "+
			"joint law, marginalisation over O ∖ Y with Y ∪ (O ∖ Y) = O, and symmetry."),
})}

var IdLineAncestors = idLineAncestorsThm{family.Add(registry.ProofEntry{
	Name: "IdLineAncestors",
	Key:  "prop_36438f5493a4b732",
	Reading: "The subproblem is the restriction to the ancestors of Y in the full " +
		"DAG, latent ones included, its observed nodes those of O there; its projection " +
		"is the projection's restriction (latent_projection.LatentProjectionAncestral). " +
		"The intervention on X outside those ancestors is dropped first.",
	Deps: []registry.EntryLike{
		DerivableAncestralTransfer,
		do_derivation.DoDerivableRules,
		d_separation.DSeparatedIsolatedRoots,
		dag.AncestorsClosed,
	},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y:set(I). ∀e:do_expr(I).",
		Hypotheses: []string{
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"do_derivable(relation_on(dag_ancestors(E, Y), E), " +
				"    O ∩ dag_ancestors(E, Y), " +
				"    do_prob(Y, X ∩ dag_ancestors(E, Y), ∅), " +
				"    e)",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, ∅), e)",
	},
		"ID's second line: only the ancestors of Y matter. Rule 3 deletes the intervention on X outside "+
			"the ancestors of Y: with the edges into X deleted those nodes are roots that are ancestors of "+
			"neither Y nor the rest of X (DSeparatedIsolatedRoots). The ancestors of Y are parent-closed "+
			"(AncestorsClosed), so the subproblem's derivation transfers (DerivableAncestralTransfer)."),
})}

var IdLineIntervene = idLineInterveneThm{family.Add(registry.ProofEntry{
	Name: "IdLineIntervene",
	Key:  "prop_5fd59af046414a01",
	Reading: "W is computed in the graph with X's in-edges deleted: an observed node outside " +
		"X that is no ancestor of Y once X is fixed. Intervening on it changes nothing Y sees.",
	Deps: []registry.EntryLike{do_derivation.DoDerivableRules, d_separation.DSeparatedIsolatedRoots},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y:set(I). ∀e:do_expr(I).",
		Hypotheses: []string{
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"do_derivable(E, O, do_prob(Y, X ∪ «Wnon», ∅), e)",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, ∅), e)",
		Abbrev: Abbrev{
			{Name: "Wnon", Text: "(O ∖ X) ∖ dag_ancestors(dag_delete_in(E, X), Y)"},
		},
	},
		"ID's third line: add the intervention on W = (O ∖ X) ∖ An(Y) computed with X's in-edges "+
			"deleted. Rule 3 at the groups (X, Y, W, ∅): with the edges into X and W deleted, W is a "+
			"set of roots that are ancestors of neither Y nor X (DSeparatedIsolatedRoots), so "+
			"do_prob(Y, X ∪ W, ∅) derives to do_prob(Y, X, ∅); symmetry and transitivity give the line."),
})}

var IdLineDistricts = idLineDistrictsThm{family.Add(registry.ProofEntry{
	Name: "IdLineDistricts",
	Key:  "prop_5c2194e77526ca4e",
	Reading: "The districts are those of the projection restricted to " +
		"O ∖ X, the observed nodes left once X is fixed; L pairs each with " +
		"an expression its query derives to, listing each district once.",
	Deps: []registry.EntryLike{
		DistrictFactorization,
		DerivableInterveneTransfer,
		latent_projection.LatentProjectionRemove,
		do_derivation.DoDerivableRules,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O X Y:set(I). ∀L:list(prod(set(I), do_expr(I))).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"list_distinct(list_map(fst, L))",
			"∀C:set(I). " +
				"    list_member(C, list_map(fst, L)) ⇔ " +
				"    C ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O ∖ X)",
			"∀p:prod(set(I), do_expr(I)). " +
				"    list_member(p, L) ⇒ do_derivable(E, O, do_prob(fst(p), O ∖ fst(p), ∅), snd(p))",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, ∅), do_sum(O ∖ (X ∪ Y), do_prod(list_map(snd, L))))",
	},
		"ID's fourth line, the factorization over the districts of G ∖ X: P_x(y) = Σ_{O ∖ (X ∪ "+
			"Y)} Π_S P_{O ∖ S}(S). DistrictFactorization in the graph with X removed, whose "+
			"projection is the projection restricted to O ∖ X (LatentProjectionRemove), transfers to "+
			"the graph with X intervened (DerivableInterveneTransfer): each factor's intervention "+
			"group becomes X ∪ ((O ∖ X) ∖ S) = O ∖ S, and the intervened constant 1 derives back to "+
			"1. Marginalisation and the product congruence with the given derivations finish."),
})}

var IdLineDistrict = idLineDistrictThm{family.Add(registry.ProofEntry{
	Name: "IdLineDistrict",
	Key:  "prop_76b7ce78f29a2e0b",
	Reading: "The precondition is ID's sixth: O ∖ X is a single district, and a " +
		"district of the whole projection. Without the second, line seven applies instead.",
	Deps: []registry.EntryLike{DistrictDerivable, do_derivation.DoDerivableRules},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O X Y:set(I). ∀l:list(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"O ∖ X ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O)",
			"dag_topological_list(E, O, l)",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(Y, X, ∅), " +
			"    do_sum((O ∖ X) ∖ Y, do_chain(O ∖ X, list_reverse(l))))",
	},
		"ID's sixth line: when the nodes left after X form a district of the whole graph, "+
			"P_x(y) = Σ_{S ∖ Y} Π_{v_i ∈ S} P(v_i | v_π^{(i−1)}) with S = O ∖ X. Marginalise "+
			"P_x(y) from P_x(S), whose intervention group X is O ∖ S, and apply DistrictDerivable."),
})}

var IdLineSubDistrict = idLineSubDistrictThm{family.Add(registry.ProofEntry{
	Name: "IdLineSubDistrict",
	Key:  "prop_60c5cb2e1bf50912",
	Reading: "Line seven's district S′ ⊇ O ∖ X enters through the subproblem, whose graph removes O " +
		"∖ S′ and keeps the latent nodes; the output's atoms read O ∖ S′ intervened, each a conditional " +
		"of Q[S′] that DistrictAtomDerivable makes observational. X ⊇ O ∖ S′, so X ∩ S′ with O ∖ S′ is X.",
	Deps: []registry.EntryLike{DerivableInterveneTransfer, DistrictAtomDerivable},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y S:set(I). ∀e:do_expr(I).",
		Hypotheses: []string{
			"S ⊆ O",
			"X ⊆ O",
			"O ∖ X ⊆ S",
			"do_derivable(relation_on(𝕌 ∖ (O ∖ S), E), S, do_prob(Y, X ∩ S, ∅), e)",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, ∅), do_expr_intervene(O ∖ S, e))",
	},
		"ID's seventh line: recurse into a district S′ of the whole graph containing O ∖ "+
			"X, on the graph with O ∖ S′ removed and the observed nodes S′. The subproblem's "+
			"derivation transfers with O ∖ S′ intervened (DerivableInterveneTransfer), and "+
			"the intervened query is do_prob(Y, (X ∩ S′) ∪ (O ∖ S′), ∅) = do_prob(Y, X, ∅)."),
})}

var IdcLineExchange = idcLineExchangeThm{family.Add(registry.ProofEntry{
	Name:    "IdcLineExchange",
	Key:     "prop_995c187aaf8b33a8",
	Reading: "The separation is Rule 2's at the single node z, the rest of W kept as observation.",
	Deps:    []registry.EntryLike{do_derivation.DoDerivableRules},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y W:set(I). ∀z:I. ∀e:do_expr(I).",
		Hypotheses: []string{
			"X ⊆ O",
			"Y ⊆ O",
			"W ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ W = ∅",
			"Y ∩ W = ∅",
			"z ∈ W",
			"d_separated(dag_delete_out(dag_delete_in(E, X), {z}), Y, {z}, X ∪ (W ∖ {z}))",
			"do_derivable(E, O, do_prob(Y, X ∪ {z}, W ∖ {z}), e)",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, W), e)",
	},
		"IDC's first line: an observed z ∈ W with no back door to Y given the rest becomes "+
			"an intervention. Rule 2 at the groups (X, Y, {z}, W ∖ {z}) derives do_prob(Y, X ∪ "+
			"{z}, W ∖ {z}) to do_prob(Y, X, W); symmetry and transitivity give the line."),
})}

var IdcLineCondition = idcLineConditionThm{family.Add(registry.ProofEntry{
	Name:    "IdcLineCondition",
	Key:     "prop_41aaff49bf3114fc",
	Reading: "The denominator is the numerator summed over Y: one derivation serves both.",
	Deps:    []registry.EntryLike{do_derivation.DoDerivableRules},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y W:set(I). ∀e:do_expr(I).",
		Hypotheses: []string{
			"X ⊆ O",
			"Y ⊆ O",
			"W ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ W = ∅",
			"Y ∩ W = ∅",
			"do_derivable(E, O, do_prob(Y ∪ W, X, ∅), e)",
		},
		Conclusion: "do_derivable(E, O, do_prob(Y, X, W), do_div(e, do_sum(Y, e)))",
	},
		"IDC's second line: P_x(y | w) = P_x(y, w) / Σ_y P_x(y, w). Conditioning splits do_prob(Y, X, "+
			"W) into the quotient of do_prob(Y ∪ W, X, ∅) by do_prob(W, X, ∅); the latter is the sum over "+
			"Y of the former by marginalisation, Y and W disjoint; the congruences put e in both places."),
})}

var NoHedgeDerivable = noHedgeDerivableThm{family.Add(registry.ProofEntry{
	Name: "NoHedgeDerivable",
	Key:  "prop_c22614b2e311ddfb",
	Reading: "The hypothesis is no hedge for X itself and Y: a hedge for a proper subset of " +
		"X need not block identification (with l → a, l → c, a → c → y, the effect of {a, c} on " +
		"y is P(y | c), though {a, c} hold a hedge for the effect of a). It is the hypothesis " +
		"that passes down ID's recursion: a hedge in a subproblem is one for the original X and Y.",
	Deps: []registry.EntryLike{
		IdLineOne,
		IdLineAncestors,
		IdLineIntervene,
		IdLineDistricts,
		IdLineDistrict,
		IdLineSubDistrict,
		DistrictAtomDerivable,
		latent_projection.LatentProjectionAncestral,
		latent_projection.LatentProjectionRemove,
		mixed_graph.DistrictsPartition,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O X Y:set(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"∀F F':set(I). " +
				"    ¬mixed_graph_hedge(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, F, F')",
		},
		Conclusion: "∃e:do_expr(I). do_expr_observational(e) ∧ do_derivable(E, O, do_prob(Y, X, ∅), e)",
	},
		"Without a hedge for X and Y the effect derives to an observational expression (Shpitser "+
			"and Pearl, 2006). By well-founded induction on the number of observed nodes and then of "+
			"nodes outside X, following ID: each case is the line lemma of its line, on the "+
			"restricted or reduced graphs, whose projections are the restrictions "+
			"(LatentProjectionAncestral, LatentProjectionRemove); the seventh line's atoms are made "+
			"observational by DistrictAtomDerivable. The hypothesis passes to every recursive call, a "+
			"hedge there being one for X and Y: lines 2 and 7 only restrict the graph; after line 3, "+
			"a hedge for X ∪ W missing X would put a node of W, which reaches the roots inside F, "+
			"among the ancestors of Y with X's in-edges deleted; after line 4, a hedge for O ∖ S_i "+
			"missing X would be a bidirected-connected set inside one district S_i meeting O ∖ S_i, "+
			"and its roots lie in S_i, among the ancestors of Y. Line 5, where ID fails, is excluded: "+
			"the whole graph and the district O ∖ X, with the roots Y, form a hedge for X and Y."),
})}
