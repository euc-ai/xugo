package do_derivation

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// derivationRules holds the rules of do_derivable(E, O) read out once, and
// derives, the chain kit that folds a run of derivations through the
// transitivity rule.
type derivationRules struct {
	reflexive, symmetric, transitive                   Fact
	sumCongruence, productCongruence                   Fact
	exchange, deletion, conditioning, marginalisation  Fact
	commute, associate, unit, selfDivision, reciprocal Fact
	derives                                            CalcRel
}

func readDerivationRules(a *Argument, E *Arrow2[I, I, Bool], O *Expr[Set[I]]) derivationRules {
	derivable := a.TermAs[Fun2[DoExpr[I], DoExpr[I], Bool]]("do_derivable(E, O)")
	rules := a.Conjuncts(
		DoDerivableRules.At(E, O),
		"reflexivity",
		"symmetry",
		"transitivity",
		"sum congruence",
		"product congruence",
		"quotient congruence",
		"observation",
		"exchange",
		"deletion",
		"conditioning",
		"marginalisation",
		"empty event",
		"product commutativity",
		"product associativity",
		"product unit",
		"self-division",
		"division by reciprocal",
		"factor out of a sum",
		"nested sums",
		"empty sum")
	return derivationRules{
		reflexive:         rules[0],
		symmetric:         rules[1],
		transitive:        rules[2],
		sumCongruence:     rules[3],
		productCongruence: rules[4],
		exchange:          rules[7],
		deletion:          rules[8],
		conditioning:      rules[9],
		marginalisation:   rules[10],
		commute:           rules[12],
		associate:         rules[13],
		unit:              rules[14],
		selfDivision:      rules[15],
		reciprocal:        rules[16],
		derives: CalcRel{
			Rel:   func(s, t Term) Prop { return MakeProp(ext.Apply(derivable.Core(), s, t)) },
			Trans: rules[2],
		},
	}
}

// TotalProbabilityDerivable derives the law of total probability under
// intervention: the effect of X on Y is the sum over Z of the effect on Y
// given Z times the effect on Z. Reverse marginalisation puts the joint of
// Y and Z under the sum, and conditioning factors the joint, a reciprocal
// of the marginal cancelling the marginal.
var TotalProbabilityDerivable = totalProbabilityDerivableThm{family.Add(registry.ProofEntry{
	Name: "TotalProbabilityDerivable",
	Key:  "prop_7584980722e51f37",
	Build: family.Theorem(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y Z:set(I).",
		Hypotheses: []string{
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(Y, X, ∅), " +
			"    do_sum(Z, do_mul(do_prob(Y, X, Z), do_prob(Z, X, ∅))))",
		Abbrev: Abbrev{
			{Name: "Joint", Text: "do_prob(Y ∪ Z, X, ∅)"},
			{Name: "Reciprocal", Text: "do_div(do_prob(∅, ∅, ∅), do_prob(Z, X, ∅))"},
		},
	}, func(a *Argument, E *Arrow2[I, I, Bool], O, X, Y, Z *Expr[Set[I]], groups Fact) {
		r := readDerivationRules(a, E, O)
		empty := a.TermAs[Set[I]]("∅")
		effect := a.TermAs[DoExpr[I]]("do_prob(Y, X, ∅)")
		summedJoint := a.TermAs[DoExpr[I]]("do_sum(Z, «Joint»)")
		summedProduct := a.TermAs[DoExpr[I]]("do_sum(Z, do_mul(do_prob(Y, X, Z), do_prob(Z, X, ∅)))")
		conditional := a.TermAs[DoExpr[I]]("do_prob(Y, X, Z)")
		joint := a.TermAs[DoExpr[I]]("«Joint»")
		marginal := a.TermAs[DoExpr[I]]("do_prob(Z, X, ∅)")
		unit := a.TermAs[DoExpr[I]]("do_prob(∅, ∅, ∅)")
		reciprocal := a.TermAs[DoExpr[I]]("«Reciprocal»")
		quotient := a.TermAs[DoExpr[I]]("do_div(«Joint», do_prob(Z, X, ∅))")
		marginalQuotient := a.TermAs[DoExpr[I]]("do_div(do_prob(Z, X, ∅), do_prob(Z, X, ∅))")
		marginalTimesReciprocal := a.TermAs[DoExpr[I]]("do_mul(do_prob(Z, X, ∅), «Reciprocal»)")
		reciprocalTimesMarginal := a.TermAs[DoExpr[I]]("do_mul(«Reciprocal», do_prob(Z, X, ∅))")
		jointTimesReciprocal := a.TermAs[DoExpr[I]]("do_mul(«Joint», «Reciprocal»)")
		conditionalTimesMarginal := a.TermAs[DoExpr[I]]("do_mul(do_prob(Y, X, Z), do_prob(Z, X, ∅))")

		byConditioning := a.Have(
			"conditioning expresses the conditional as a quotient",
			"do_derivable(E, O, do_prob(Y, X, Z), do_div(«Joint», do_prob(Z, X, ∅)))",
			By(groups, r.conditioning.At(X, Y, Z)))
		factors := a.Have(
			"the quotient has a well-formed numerator and denominator",
			"do_expr_wf(O, «Joint») ∧ do_expr_wf(O, do_prob(Z, X, ∅))",
			By(byConditioning, DerivableWellFormed.At(E, O, conditional, quotient), WellFormedDef))
		unitFormed := UnitWellFormed.At(O)
		reciprocalFormed := a.Have(
			"the reciprocal has well-formed operands",
			"do_expr_wf(O, «Reciprocal»)",
			By(factors, unitFormed, WellFormedDef))

		cancelMarginal := a.Calc(r.derives, reciprocalTimesMarginal,
			Leg(
				marginalTimesReciprocal,
				"move the marginal before its reciprocal",
				By(factors, reciprocalFormed, r.commute)),
			Leg(
				marginalQuotient,
				"convert the marginal times its reciprocal to self-division",
				By(factors, r.reciprocal.At(marginal, marginal), r.symmetric)),
			Leg(
				unit,
				"the marginal divided by itself yields the unit",
				By(factors, r.selfDivision)))

		conditionalAsProduct := a.Have(
			"replace the quotient by a product with its reciprocal",
			"do_derivable(E, O, do_prob(Y, X, Z), do_mul(«Joint», «Reciprocal»))",
			By(
				factors,
				byConditioning,
				r.reciprocal.At(joint, marginal),
				r.transitive.At(conditional, quotient, jointTimesReciprocal)))
		appendedMarginal := a.TermAs[DoExpr[I]]("do_mul(do_mul(«Joint», «Reciprocal»), do_prob(Z, X, ∅))")
		reassociated := a.TermAs[DoExpr[I]]("do_mul(«Joint», do_mul(«Reciprocal», do_prob(Z, X, ∅)))")
		jointTimesUnit := a.TermAs[DoExpr[I]]("do_mul(«Joint», do_prob(∅, ∅, ∅))")
		unitTimesJoint := a.TermAs[DoExpr[I]]("do_mul(do_prob(∅, ∅, ∅), «Joint»)")
		recoverJoint := a.Calc(r.derives, conditionalTimesMarginal,
			Leg(
				appendedMarginal,
				"multiply the conditional and its replacement by the marginal",
				By(factors, conditionalAsProduct, r.reflexive.At(marginal), r.productCongruence)),
			Leg(
				reassociated,
				"associate the reciprocal with the marginal",
				By(factors, reciprocalFormed, r.associate.At(joint, reciprocal, marginal), r.symmetric)),
			Leg(
				jointTimesUnit,
				"cancel the two marginal factors inside the product",
				By(factors, cancelMarginal, r.reflexive.At(joint), r.productCongruence)),
			Leg(
				unitTimesJoint,
				"commute the unit to the front",
				By(factors, unitFormed, r.commute)),
			Leg(
				joint,
				"the unit law recovers the joint",
				By(factors, r.unit)))

		a.Show(
			"reverse marginalisation, then factor the joint inside the sum",
			r.derives.Calc(effect,
				Leg(
					summedJoint,
					"reverse marginalisation puts the joint under a sum over Z",
					BySets(groups, r.marginalisation.At(X, Y, Z, empty), r.symmetric)),
				Leg(
					summedProduct,
					"factor the joint inside the sum",
					By(groups, recoverJoint, r.symmetric.At(conditionalTimesMarginal, joint), r.sumCongruence))))
	}),
})}

// BackdoorDerivable derives adjustment over an observed back-door set.
var BackdoorDerivable = backdoorDerivableThm{family.Add(registry.ProofEntry{
	Name: "BackdoorDerivable",
	Key:  "prop_2272395eb22ccb70",
	Build: family.Theorem(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y Z:set(I).",
		Hypotheses: []string{
			"backdoor_criterion(E, X, Y, Z)",
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(Y, X, ∅), " +
			"    do_sum(Z, do_mul(do_prob(Y, ∅, X ∪ Z), do_prob(Z, ∅, ∅))))",
		Abbrev: Abbrev{
			{Name: "OriginalProduct", Text: "do_mul(do_prob(Y, X, Z), do_prob(Z, X, ∅))"},
			{Name: "AdjustedProduct", Text: "do_mul(do_prob(Y, ∅, X ∪ Z), do_prob(Z, ∅, ∅))"},
		},
	}, func(a *Argument, E *Arrow2[I, I, Bool], O, X, Y, Z *Expr[Set[I]], guards Fact) {
		r := readDerivationRules(a, E, O)
		empty := a.TermAs[Set[I]]("∅")
		target := a.TermAs[DoExpr[I]]("do_prob(Y, X, ∅)")
		conditional := a.TermAs[DoExpr[I]]("do_prob(Y, X, Z)")
		marginal := a.TermAs[DoExpr[I]]("do_prob(Z, X, ∅)")
		observedConditional := a.TermAs[DoExpr[I]]("do_prob(Y, ∅, X ∪ Z)")
		observedMarginal := a.TermAs[DoExpr[I]]("do_prob(Z, ∅, ∅)")
		summedProduct := a.TermAs[DoExpr[I]]("do_sum(Z, «OriginalProduct»)")
		adjustment := a.TermAs[DoExpr[I]]("do_sum(Z, «AdjustedProduct»)")

		emptyDeletion := a.Have(
			"deleting the edges into the empty set preserves the graph",
			"dag_delete_in(E, ∅) = E",
			Funext(),
			Simp(Fwd(dag.DeleteInDef), Fwd(set_basic.NotInEmpty)),
			BySets())
		emptyAncestors := a.Have(
			"the empty set has no ancestors",
			"dag_ancestors(E, ∅) = ∅",
			Simp(Fwd(dag.AncestorsDef)),
			BySets())
		criterion := d_separation.BackdoorCriterionDef.At(E, X, Y, Z)
		exchangeSeparation := a.Have(
			"the back-door separation permits action and observation exchange",
			"d_separated(dag_delete_out(E, X), Y, X, Z)",
			By(guards, criterion))
		exchanged := a.Have(
			"exchange X into the conditioning group of the first factor",
			"do_derivable(E, O, do_prob(Y, X, Z), do_prob(Y, ∅, X ∪ Z))",
			BySets(
				guards,
				exchangeSeparation,
				a.Simplified(r.exchange.At(empty, Y, X, Z), Fwd(emptyDeletion), Fwd(set_algebra.UnionEmpty))))

		deletionSeparation := a.Have(
			"after deleting the edges into X, X is separated from Z",
			"d_separated(dag_delete_in(E, X), Z, X, ∅)",
			By(guards, criterion, d_separation.DeleteInSeparatesNonDescendants.At(E, X, Z)))
		deleted := a.Have(
			"delete the action on X from the marginal",
			"do_derivable(E, O, do_prob(Z, X, ∅), do_prob(Z, ∅, ∅))",
			BySets(
				guards,
				deletionSeparation,
				a.Simplified(
					r.deletion.At(empty, Z, X, empty),
					Fwd(emptyDeletion),
					Fwd(emptyAncestors),
					Fwd(set_algebra.DiffEmpty),
					Fwd(set_algebra.UnionEmpty))))
		replacedFactors := a.Have(
			"combine the exchanged conditional and the observational marginal",
			"do_derivable(E, O, «OriginalProduct», «AdjustedProduct»)",
			By(
				exchanged,
				deleted,
				r.productCongruence.At(conditional, observedConditional, marginal, observedMarginal)))
		a.Show(
			"total probability over Z, then the two causal rules in the summand",
			r.derives.Calc(target,
				Leg(
					summedProduct,
					"total probability over Z",
					By(guards, TotalProbabilityDerivable.At(E, O, X, Y, Z))),
				Leg(
					adjustment,
					"replace the summand by the observational product",
					By(guards, replacedFactors, r.sumCongruence))))
	}),
})}

// FrontdoorDerivable derives the nested observational adjustment through the mediator Z.
var FrontdoorDerivable = frontdoorDerivableThm{family.Add(registry.ProofEntry{
	Name: "FrontdoorDerivable",
	Key:  "prop_93e38d26b3518e56",
	Build: family.Sections(Statement{
		Binders: "∀E:(I → I → bool). ∀O X Y Z:set(I).",
		Hypotheses: []string{
			"frontdoor_criterion(E, X, Y, Z)",
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
		},
		Conclusion: "do_derivable(E, " +
			"    O, " +
			"    do_prob(Y, X, ∅), " +
			"    do_sum(Z, " +
			"        do_mul(do_prob(Z, ∅, X), do_sum(X, do_mul(do_prob(Y, ∅, Z ∪ X), do_prob(X, ∅, ∅))))))",
		Abbrev: Abbrev{
			{Name: "OriginalProduct", Text: "do_mul(do_prob(Y, X, Z), do_prob(Z, X, ∅))"},
			{Name: "ExchangeGraph", Text: "dag_delete_out(dag_delete_in(E, X), Z)"},
			{Name: "DeletionGraph", Text: "dag_delete_in(dag_delete_in(E, Z), X)"},
			{Name: "InnerAdjustment", Text: "do_sum(X, do_mul(do_prob(Y, ∅, Z ∪ X), do_prob(X, ∅, ∅)))"},
			{Name: "FrontdoorProduct", Text: "do_mul(do_prob(Z, ∅, X), «InnerAdjustment»)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		moveIntoCondition := ctx.Lemma(Statement{
			Binders:    "∀E:(I → I → bool). ∀X Y Z:set(I).",
			Hypotheses: []string{"d_separated(E, X ∪ Z, Y, ∅)"},
			Conclusion: "d_separated(E, X, Y, Z)",
			Abbrev: Abbrev{
				{Name: "Scope", Text: "dag_ancestors(E, X ∪ Y ∪ Z)"},
				{Name: "Moral", Text: "dag_moral(E, «Scope»)"},
				{Name: "Restricted", Text: "relation_on(«Scope» ∖ Z, «Moral»)"},
				{Name: "Unrestricted", Text: "relation_on(«Scope», «Moral»)"},
			},
		}, func(a *Argument, E *Arrow2[I, I, Bool], X, Y, Z *Expr[Set[I]], separated Fact) {
			sameScope := a.Have(
				"both moral graphs have the same ancestral scope",
				"(X ∪ Z) ∪ Y ∪ ∅ = X ∪ Y ∪ Z",
				BySets())
			noWalk := a.Simplified(
				separated,
				Fwd(d_separation.DSeparatedDef),
				Fwd(sameScope),
				Fwd(set_algebra.DiffEmpty))
			subgraph := a.Have(
				"the conditioning set removes moral edges",
				"∀u v:I. «Restricted»(u, v) ⇒ «Unrestricted»(u, v)",
				Simp(Fwd(equivalence.RelationOnDef)),
				BySets())
			a.Do(Simp(Fwd(d_separation.DSeparatedDef)))
			u := a.FixAs[I]("u")
			v := a.FixAs[I]("v")
			endpoints := a.Assume()
			inExtendedSet := a.Have(
				"the first endpoint is in the original separated set",
				"u ∈ X ∪ Z ∧ v ∈ Y",
				BySets(endpoints))
			restricted := a.TermAs[Fun2[I, I, Bool]]("«Restricted»")
			unrestricted := a.TermAs[Fun2[I, I, Bool]]("«Unrestricted»")
			a.Show(
				"a restricted moral walk would also connect the original sets",
				By(inExtendedSet, noWalk, subgraph, closure.Monotone.At(restricted, unrestricted, u, v)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			E *Arrow2[I, I, Bool],
			O, X, Y, Z *Expr[Set[I]],
			guards Fact,
		) {
			r := readDerivationRules(a, E, O)
			empty := a.TermAs[Set[I]]("∅")
			effect := a.TermAs[DoExpr[I]]("do_prob(Y, X, ∅)")
			originalProduct := a.TermAs[DoExpr[I]]("«OriginalProduct»")
			summedOriginal := a.TermAs[DoExpr[I]]("do_sum(Z, «OriginalProduct»)")

			criterion := d_separation.FrontdoorCriterionDef.At(E, X, Y, Z)
			outcomeAncestry := a.Have(
				"cutting the edges into Z leaves no ancestor of Y in X",
				"dag_ancestors(dag_delete_in(E, Z), Y) ∩ X = ∅",
				By(guards, criterion))
			mediatorSeparation := a.Have(
				"cutting the edges out of X separates Z from X",
				"d_separated(dag_delete_out(E, X), Z, X, ∅)",
				By(guards, criterion))
			outcomeSeparation := a.Have(
				"cutting the edges out of Z separates Y from Z given X",
				"d_separated(dag_delete_out(E, Z), Y, Z, X)",
				By(guards, criterion))

			emptyDeletion := a.Have(
				"deleting edges into the empty set preserves the graph",
				"dag_delete_in(E, ∅) = E",
				Funext(),
				Simp(Fwd(dag.DeleteInDef), Fwd(set_basic.NotInEmpty)),
				BySets())
			exchangedMarginal := a.Have(
				"exchange action on X for observation in the marginal",
				"do_derivable(E, O, do_prob(Z, X, ∅), do_prob(Z, ∅, X))",
				BySets(
					guards,
					mediatorSeparation,
					a.Simplified(r.exchange.At(empty, Z, X, empty), Fwd(emptyDeletion), Fwd(set_algebra.UnionEmpty))))

			restricted := a.TermAs[Fun2[I, I, Bool]]("«ExchangeGraph»")
			withoutZOut := a.TermAs[Fun2[I, I, Bool]]("dag_delete_out(E, Z)")
			fewerEdges := a.Have(
				"deleting the edges into X further restricts the exchange graph",
				"∀u v:I. «ExchangeGraph»(u, v) ⇒ dag_delete_out(E, Z, u, v)",
				Simp(Fwd(dag.DeleteOutDef), Fwd(dag.DeleteInDef)),
				BySets())
			conditionalExchangeSeparation := a.Have(
				"the third criterion survives the additional edge deletion",
				"d_separated(«ExchangeGraph», Y, Z, X)",
				By(
					fewerEdges,
					outcomeSeparation,
					d_separation.DSeparatedEdgeMonotone.At(withoutZOut, restricted, Y, Z, X)))
			exchangedConditional := a.Have(
				"exchange at Z between the joint action and the conditioned outcome",
				"do_derivable(E, O, do_prob(Y, X ∪ Z, ∅), do_prob(Y, X, Z))",
				BySets(
					guards,
					conditionalExchangeSeparation,
					a.Simplified(r.exchange.At(X, Y, Z, empty), Fwd(set_algebra.UnionEmpty))))

			withoutZIn := a.TermAs[Fun2[I, I, Bool]]("dag_delete_in(E, Z)")
			deletionGraph := a.TermAs[Fun2[I, I, Bool]]("«DeletionGraph»")
			outcomeWithMediator := a.TermAs[Set[I]]("Y ∪ Z")
			mediatorRoots := a.Have(
				"deleting the incoming edges makes Z a set of roots",
				"∀u z:I. z ∈ Z ⇒ ¬dag_delete_in(E, Z, u, z)",
				Simp(Fwd(dag.DeleteInDef)),
				BySets())
			combinedAncestors := a.Have(
				"adding the roots Z adds only Z to the outcome ancestors",
				"dag_ancestors(dag_delete_in(E, Z), Y ∪ Z) = Z ∪ dag_ancestors(dag_delete_in(E, Z), Y)",
				By(
					Normalized,
					mediatorRoots,
					set_algebra.UnionComm.At(Y, Z),
					dag.AncestorsRootUnion.At(withoutZIn, Z, Y)))
			disjointAncestors := a.Have(
				"neither the roots Z nor the outcome ancestors meet X",
				"dag_ancestors(dag_delete_in(E, Z), Y ∪ Z) ∩ X = ∅",
				Simp(Fwd(combinedAncestors)),
				BySets(outcomeAncestry, guards))
			separatedUnion := a.Have(
				"deleting edges into X separates it from the outcome and mediator together",
				"d_separated(«DeletionGraph», Y ∪ Z, X, ∅)",
				By(
					disjointAncestors,
					d_separation.DeleteInSeparatesNonDescendants.At(withoutZIn, X, outcomeWithMediator)))
			emptyAncAfterZ := a.Have(
				"the empty set has no ancestors after intervention on Z",
				"dag_ancestors(dag_delete_in(E, Z), ∅) = ∅",
				Simp(Fwd(dag.AncestorsDef)),
				BySets())
			deletionSeparation := a.Have(
				"move Z into the conditioning set for the deletion rule",
				"d_separated(«DeletionGraph», Y, X, Z)",
				By(separatedUnion, At(moveIntoCondition, deletionGraph, Y, X, Z)))

			withoutXOut := a.TermAs[Fun2[I, I, Bool]]("dag_delete_out(E, X)")
			sameAncestors := a.Have(
				"deleting the outgoing edges of X preserves its ancestors",
				"dag_ancestors(dag_delete_out(E, X), X) = dag_ancestors(E, X)",
				By(set_order.SubsetRefl.At(X), dag.AncestorsDeleteOut.At(E, X, X)))
			noMediatorAncestor := a.Have(
				"no ancestor of X lies in Z, for it would be an ancestor of the empty conditioning set",
				"dag_ancestors(E, X) ∩ Z = ∅",
				BySets(
					guards,
					mediatorSeparation,
					sameAncestors,
					d_separation.DSeparatedAncestorsReachConditioningSet.At(withoutXOut, Z, X, empty)))
			innerCriterion := a.Have(
				"X meets the back-door criterion for the effect of Z on Y",
				"backdoor_criterion(E, Z, Y, X)",
				By(noMediatorAncestor, outcomeSeparation, d_separation.BackdoorCriterionDef.At(E, Z, Y, X)))

			conditional := a.TermAs[DoExpr[I]]("do_prob(Y, X, Z)")
			marginal := a.TermAs[DoExpr[I]]("do_prob(Z, X, ∅)")
			bothActions := a.TermAs[DoExpr[I]]("do_prob(Y, Z ∪ X, ∅)")
			mediatorAction := a.TermAs[DoExpr[I]]("do_prob(Y, Z, ∅)")
			inner := a.TermAs[DoExpr[I]]("«InnerAdjustment»")
			observedMarginal := a.TermAs[DoExpr[I]]("do_prob(Z, ∅, X)")
			adjustedConditional := a.Calc(r.derives, conditional,
				Leg(
					bothActions,
					"read the exchange at Z backwards to act on Z and X together",
					By(exchangedConditional, set_algebra.UnionComm.At(X, Z), r.symmetric)),
				Leg(
					mediatorAction,
					"delete the action on X while keeping the intervention on Z",
					BySets(
						guards,
						deletionSeparation,
						a.Simplified(
							r.deletion.At(Z, Y, X, empty),
							Fwd(emptyAncAfterZ),
							Fwd(set_algebra.DiffEmpty),
							Fwd(set_algebra.UnionEmpty)))),
				Leg(
					inner,
					"apply back-door adjustment to the outcome with intervention on Z",
					BySets(guards, innerCriterion, BackdoorDerivable.At(E, O, Z, Y, X))))
			wellFormed := a.Have(
				"the two new factors are well formed",
				"do_expr_wf(O, «InnerAdjustment») ∧ do_expr_wf(O, do_prob(Z, ∅, X))",
				By(
					adjustedConditional,
					exchangedMarginal,
					DerivableWellFormed.At(E, O, conditional, inner),
					DerivableWellFormed.At(E, O, marginal, observedMarginal)))
			reversedProduct := a.TermAs[DoExpr[I]]("do_mul(«InnerAdjustment», do_prob(Z, ∅, X))")
			frontdoorProduct := a.TermAs[DoExpr[I]]("«FrontdoorProduct»")
			reorderProduct := a.Calc(r.derives, originalProduct,
				Leg(
					reversedProduct,
					"replace the two factors by the adjusted outcome and observed marginal",
					By(adjustedConditional, exchangedMarginal, r.productCongruence)),
				Leg(
					frontdoorProduct,
					"put the observed marginal before the inner adjustment",
					By(wellFormed, r.commute)))
			target := a.TermAs[DoExpr[I]]("do_sum(Z, «FrontdoorProduct»)")
			a.Show(
				"total probability over Z, then the front-door summand",
				r.derives.Calc(effect,
					Leg(
						summedOriginal,
						"total probability over Z",
						By(guards, TotalProbabilityDerivable.At(E, O, X, Y, Z))),
					Leg(
						target,
						"replace the summand by the front-door product",
						By(guards, reorderProduct, r.sumCongruence))))
		})
	}),
})}
