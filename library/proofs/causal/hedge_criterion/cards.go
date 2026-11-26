package hedge_criterion

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/do_semantics"
	"github.com/euc-ai/xugo/library/proofs/causal/id_derivation"
	"github.com/euc-ai/xugo/library/proofs/causal/identifiability"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/latent_projection"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var HedgeNotIdentifiable = hedgeNotIdentifiableThm{family.Add(registry.ProofEntry{
	Name: "HedgeNotIdentifiable",
	Key:  "prop_1efc1e5e506d24ff",
	Reading: "The hedge is for X itself, not a subset: with l → a, l → c, a → c → y, the " +
		"effect of {a, c} on y is P(y | c), though {a, c} hold a hedge for the effect of a — the " +
		"published corollary over subsets X′ ⊆ X fails in this direction. A hedge for a part of Y " +
		"is one for Y. The richness hypotheses are load-bearing. The construction needs " +
		"independent coins of dyadic weight, held by a uniform probability on 2^k points of the " +
		"sample type; latent nodes that carry several bits at once, held by an infinite state " +
		"type; and two values at each observed node. With one-point carriers every effect is " +
		"identifiable. The value v is existential: at some configurations the two models may agree.",
	Deps: []registry.EntryLike{
		identifiability.IdentifiableDef,
		identifiability.PositiveScmDef,
		SpinProgramRealized,
		HedgeSpinProgramsExist,
		intervention.DoEmpty,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y F F':set(I).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"∀i:I. i ∈ O ⇒ finite(D(i)) ∧ (∃a b:B. a ∈ D(i) ∧ b ∈ D(i) ∧ a ≠ b)",
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"mixed_graph_hedge(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, F, F')",
		},
		Conclusion: "∃v:(I → B). " +
			"    (∀i:I. i ∈ O ⇒ v(i) ∈ D(i)) ∧ " +
			"    ¬scm_identifiable(«positiveClass», " +
			"        O, " +
			"        λM:scm_model(A, B, I). " +
			"            extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y, v))))",
	},
		"A hedge makes the effect not identifiable on the positive class (Shpitser and Pearl, JMLR 2008, "+
			"Theorem 17). Pick a point a(i) in each observed carrier. HedgeSpinProgramsExist gives two sign "+
			"programs on the projection whose class laws agree with nothing held and whose marginals on Y "+
			"differ at some class configuration with X held at a; SpinProgramRealized realizes both over the "+
			"same weights as models on the graph. Both are in the positive class, every conditional "+
			"probability lying in [1/4, 3/4] and every weight being positive; they agree on every observed "+
			"configuration, legal or not, an intervention on no node being the model (DoEmpty); and at v "+
			"equal to a on X and in the differing classes on Y the effect differs. The hedge is for X "+
			"itself: for a proper subset of X the statement fails. The bow graph is the smallest case."),
})}

var HedgeCriterion = hedgeCriterionThm{family.Add(registry.ProofEntry{
	Name: "HedgeCriterion",
	Key:  "prop_b0bbedb3844b82e5",
	Reading: "⇐ needs none of the richness hypotheses: it is a derivation and its soundness. " +
		"⇒ is completeness and needs them all. The hedge is for X itself: ranging over subsets " +
		"X′ ⊆ X, as Shpitser and Pearl's corollary does, makes ⇒ false. Identifiability is asked " +
		"at every v legal on X; off the carrier on Y the effect is 0 in every model.",
	Deps: []registry.EntryLike{
		HedgeNotIdentifiable,
		id_derivation.NoHedgeDerivable,
		do_semantics.DerivationIdentifies,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y:set(I).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"∀i:I. i ∈ O ⇒ finite(D(i)) ∧ (∃a b:B. a ∈ D(i) ∧ b ∈ D(i) ∧ a ≠ b)",
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
		},
		Conclusion: "(∀v:(I → B). " +
			"    (∀i:I. i ∈ X ⇒ v(i) ∈ D(i)) ⇒ " +
			"    scm_identifiable(«positiveClass», " +
			"        O, " +
			"        λM:scm_model(A, B, I). " +
			"            extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y, v))))) ⇔ " +
			"(∀F F':set(I). " +
			"    ¬mixed_graph_hedge(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, F, F'))",
	},
		"The hedge criterion: the effect of X on Y is identifiable on the positive class exactly when "+
			"the latent projection has no hedge for the effect of X on Y. ⇐: without a hedge the effect "+
			"derives to an observational expression (NoHedgeDerivable), and a derived effect is identifiable "+
			"(DerivationIdentifies). ⇒: a hedge gives a configuration where it is not (HedgeNotIdentifiable)."),
})}

var DoDerivationComplete = doDerivationCompleteThm{family.Add(registry.ProofEntry{
	Name: "DoDerivationComplete",
	Key:  "prop_5d5e39e3afaf7ce5",
	Reading: "This is the completeness of the derivation relation for effects: " +
		"it holds for the rule table as laid, the line lemmas being derivations in " +
		"it. The richness hypotheses are those of HedgeNotIdentifiable.",
	Deps: []registry.EntryLike{HedgeCriterion, id_derivation.NoHedgeDerivable},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y:set(I).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"∀i:I. i ∈ O ⇒ finite(D(i)) ∧ (∃a b:B. a ∈ D(i) ∧ b ∈ D(i) ∧ a ≠ b)",
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"(∀v:(I → B). " +
				"    (∀i:I. i ∈ X ⇒ v(i) ∈ D(i)) ⇒ " +
				"    scm_identifiable(«positiveClass», " +
				"        O, " +
				"        λM:scm_model(A, B, I). " +
				"            extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y, v)))))",
		},
		Conclusion: "∃e:do_expr(I). do_expr_observational(e) ∧ do_derivable(E, O, do_prob(Y, X, ∅), e)",
	},
		"The do-calculus is complete for effects: an effect identifiable on the positive "+
			"class derives to an observational expression. Identifiability excludes a hedge for "+
			"X and Y (HedgeCriterion), and without one the derivation exists (NoHedgeDerivable)."),
})}

var IdcReduction = idcReductionThm{family.Add(registry.ProofEntry{
	Name: "IdcReduction",
	Key:  "prop_ec8aad4e31979246",
	Reading: "The hypothesis is that IDC's first line applies to no node of W. ⇐ " +
		"is a ratio of finite sums of identified joint probabilities over the fixed " +
		"observed carriers; ⇒ is the hard direction and needs the richness hypotheses.",
	Deps: []registry.EntryLike{
		id_derivation.IdcLineCondition,
		id_derivation.NoHedgeDerivable,
		do_semantics.DerivationIdentifies,
		HedgeNotIdentifiable,
		identifiability.ObservedMarginal,
		identifiability.PositiveInterventional,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y:set(I). ∀W:set(I).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"∀i:I. i ∈ O ⇒ finite(D(i)) ∧ (∃a b:B. a ∈ D(i) ∧ b ∈ D(i) ∧ a ≠ b)",
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"X ∩ Y = ∅",
			"W ⊆ O",
			"X ∩ W = ∅",
			"Y ∩ W = ∅",
			"∀z:I. z ∈ W ⇒ ¬d_separated(dag_delete_out(dag_delete_in(E, X), {z}), Y, {z}, X ∪ (W ∖ {z}))",
		},
		Conclusion: "(∀v:(I → B). " +
			"    (∀i:I. i ∈ X ⇒ v(i) ∈ D(i)) ⇒ " +
			"    scm_identifiable(«positiveClass», " +
			"        O, " +
			"        λM:scm_model(A, B, I). " +
			"            cond_prob(scm_distribution(scm_do(M, X, v)), agree_on(Y, v), agree_on(W, v)))) ⇔ " +
			"(∀v:(I → B). " +
			"    (∀i:I. i ∈ X ⇒ v(i) ∈ D(i)) ⇒ " +
			"    scm_identifiable(«positiveClass», " +
			"        O, " +
			"        λM:scm_model(A, B, I). " +
			"            extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y ∪ W, v)))))",
	},
		"A conditional effect to which no exchange applies is identifiable exactly when the joint "+
			"effect is (Shpitser and Pearl, UAI 2006, and JMLR 2008, Lemma 21). ⇐: the conditional is the "+
			"joint divided by its sum over the configurations of Y, finitely many in the class, each "+
			"identifiable, the denominator positive (PositiveInterventional). ⇒: if the joint effect is not "+
			"identifiable, the projection has a hedge for X and Y ∪ W (NoHedgeDerivable and "+
			"DerivationIdentifies, read contrapositively); with every node of W holding a back door to Y "+
			"given the rest, the hedge's two models extend along those back doors to two positive models "+
			"that agree on observations and differ on the conditional (HedgeNotIdentifiable's construction)."),
})}

var DyadicNetworkRealized = dyadicNetworkRealizedThm{family.Add(registry.ProofEntry{
	Name: "DyadicNetworkRealized",
	Key:  "prop_ca8fbd7ead365fa4",
	Reading: "κ(i, p, b)/2^m is the probability that node i takes the value b at the " +
		"configuration p; it sums to 1 over the carrier, which is therefore nonempty. Its locality " +
		"is load-bearing: a mechanism sees the configuration at the parents only. The formula is the " +
		"truncated factorization: under do(X = x) the factors of X are dropped and the configuration " +
		"is held to x there. X ⊆ V is load-bearing: held at a non-node off its default, the formula " +
		"gives 0 for the whole space. Q is any set of configurations, the law being carried by the " +
		"legal ones. The sample type must be infinite to hold the coins; the state type is free.",
	Deps: []registry.EntryLike{
		structural_model.CoinModelLegal,
		structural_model.ScmSolution,
		independence.CoinBlocksProbability,
		intervention.DoDef,
		cardinality.ChooseSubsetStrong,
		cardinality.CardEqBijection,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀S:(I → set(B)). " +
			"∀d:(I → B). " +
			"∀m:num. " +
			"∀κ:(I → (I → B) → B → num).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"dag_on(V, E)",
			"∀i:I. i ∈ V ⇒ finite(S(i))",
			"∀i:I. ∀p q:(I → B). ∀b:B. i ∈ V ∧ (∀j:I. E(j, i) ⇒ p(j) = q(j)) ⇒ κ(i, p, b) = κ(i, q, b)",
			"∀i:I. ∀p:(I → B). i ∈ V ⇒ Σ_{b∈S(i)} κ(i, p, b) = 2 ^ m",
		},
		Conclusion: "∃M:scm_model(A, B, I). " +
			"    scm_on(M) ∧ " +
			"    scm_noise_independent(M) ∧ " +
			"    M.nodes = V ∧ " +
			"    M.edges = E ∧ " +
			"    M.default = d ∧ " +
			"    (∀i:I. i ∈ V ⇒ M.states(i) = S(i) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ S(i)}) ∧ " +
			"    (∀X:set(I). ∀x:(I → B). ∀Q:set(I → B). " +
			"        X ⊆ V ∧ (∀i:I. i ∈ X ⇒ x(i) ∈ S(i)) ⇒ " +
			"        scm_distribution(scm_do(M, X, x), Q) = " +
			"        extended_of_real( " +
			"            Σ_{w∈{w:I → B | w ∈ indexed_functions(V, d, S) ∧ w ∈ Q ∧ w ∈ agree_on(X, x)}} (Π_{i∈V ∖ X} &(κ(i, w, w(i)))) / " +
			"            &(2 ^ (m * card(V ∖ X)))))",
	},
		"Every finite network of dyadic conditional probabilities is the law of a model with "+
			"independent noise, and its interventional laws are the truncated factorization. Each node "+
			"owns m fair coins, on a sample set that is an injective copy of the sets of coins: an "+
			"infinite type holds one of any finite size (ChooseSubsetStrong, whose bound is asked of "+
			"finite sets only, and CardEqBijection). For each parent configuration split the 2^m sets of "+
			"the node's coins into parts of sizes κ(i, p, b), b in the carrier, and let the mechanism "+
			"return the b whose part holds the node's coins. CoinModelLegal makes the model legal with "+
			"independent noise; an intervention is a model of the same kind, constant on X (DoDef). By "+
			"ScmSolution a sample solves to w exactly when each node's coins fall in the part of w(i) at "+
			"w, an event of the node's own noise: the intersection has the product of the probabilities, "+
			"each κ/2^m (CoinBlocksProbability). A set Q is the finite union of its legal configurations."),
})}

var ProjectionKernelsRealized = projectionKernelsRealizedThm{family.Add(registry.ProofEntry{
	Name: "ProjectionKernelsRealized",
	Key:  "prop_559377679b12f01d",
	Reading: "A specification on the latent projection: observed node v takes the value b with " +
		"probability K(v, t, σ, b)/2^m, reading the configuration t only at its parents in the " +
		"projection and, of the set σ of labels whose fair bit is set, only the labels attached to it. A " +
		"label e is read by the nodes of N(e), which must share a latent ancestor reaching each of them " +
		"through latent nodes; a bidirected edge is the label of its two ends. The shared ancestor is " +
		"load-bearing: two observed nodes with no common cause cannot read one bit. The formula gives " +
		"every marginal on observed nodes under every intervention on observed nodes at legal values; t " +
		"ranges over the observed configurations, written as w off O. Both types must be infinite: the " +
		"sample type for the coins, the state type for a latent node to carry what passes through it — " +
		"with two states a latent node with three children cannot carry a bit for each pair of them.",
	Deps: []registry.EntryLike{
		DyadicNetworkRealized,
		latent_projection.LatentReachDef,
		latent_projection.LatentDirectedDef,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀Λ:set(C). " +
			"∀N:(C → set(I)). " +
			"∀m:num. " +
			"∀K:(I → (I → B) → set(C) → B → num).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"dag_on(V, E)",
			"O ⊆ V",
			"∀i:I. i ∈ O ⇒ finite(D(i))",
			"finite(Λ)",
			"∀e:C. e ∈ Λ ⇒ (∃l:I. l ∉ O ∧ (∀v:I. v ∈ N(e) ⇒ latent_reach(E, O, l, v)))",
			"∀v:I. ∀t t':(I → B). ∀σ:set(C). ∀b:B. " +
				"    v ∈ O ∧ (∀u:I. latent_proj_directed(E, O, u, v) ⇒ t(u) = t'(u)) ⇒ " +
				"    K(v, t, σ, b) = K(v, t', σ, b)",
			"∀v:I. ∀t:(I → B). ∀σ σ':set(C). ∀b:B. " +
				"    v ∈ O ∧ (∀e:C. e ∈ Λ ∧ v ∈ N(e) ⇒ (e ∈ σ ⇔ e ∈ σ')) ⇒ K(v, t, σ, b) = K(v, t, σ', b)",
			"∀v:I. ∀t:(I → B). ∀σ:set(C). v ∈ O ⇒ Σ_{b∈D(v)} K(v, t, σ, b) = 2 ^ m",
		},
		Conclusion: "∃M:scm_model(A, B, I). " +
			"    scm_on(M) ∧ " +
			"    scm_noise_independent(M) ∧ " +
			"    M.nodes = V ∧ " +
			"    M.edges = E ∧ " +
			"    (∀i:I. i ∈ O ⇒ M.states(i) = D(i) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ D(i)}) ∧ " +
			"    (∀X S:set(I). ∀x w:(I → B). " +
			"        X ⊆ O ∧ S ⊆ O ∧ (∀i:I. i ∈ X ⇒ x(i) ∈ D(i)) ⇒ " +
			"        scm_distribution(scm_do(M, X, x), agree_on(S, w)) = " +
			"        extended_of_real( " +
			"            Σ_{t∈{t:I → B | t ∈ indexed_functions(O, w, D) ∧ t ∈ agree_on(S, w) ∧ t ∈ agree_on(X, x)}} (Σ_{σ∈{σ:set(C) | σ ⊆ Λ}} Π_{v∈O ∖ X} &(K(v, t, σ, t(v)))) / " +
			"            &(2 ^ (card(Λ) + m * card(O ∖ X)))))",
	},
		"A dyadic specification on the latent projection, with fair bits shared along latent paths, is "+
			"the observed law of a model on the graph under every intervention on observed nodes. Realize it "+
			"by a network on the whole graph (DyadicNetworkRealized), at one exponent large enough for every "+
			"node: a latent source owns a bit for each of its labels, and the observed kernels are scaled up "+
			"to it. A latent node's state is a finite record, injected into the infinite state type: one bit "+
			"for each label and one value for each observed node, drawn fresh at the label's source, read at "+
			"an observed parent, copied from a latent parent that carries it, and a fixed default otherwise. "+
			"By induction along the graph a latent node reached from a label's source through latent nodes "+
			"carries the source's bit, and one reached from an observed node through latent nodes carries "+
			"its value, intervened or not. An observed node reads its projection parents and its labels off "+
			"its own parents and draws by K. A label no node reads may have no source among the nodes: no "+
			"node draws it, K does not read it, and its two values double the sum over the bits against its "+
			"factor 2 in the denominator. Summing the network's factorization over the latent records leaves "+
			"the average over the bits of the product of the observed factors."),
})}

var SpinProgramRealized = spinProgramRealizedThm{family.Add(registry.ProofEntry{
	Name: "SpinProgramRealized",
	Key:  "prop_7a1beba66a1e62d2",
	Reading: "Each observed carrier is split into the point a(i) and the rest, and the class " +
		"set z holds the nodes that are off a(i). The weights ν split the class off a(i) among its " +
		"points and do not depend on the program, so two programs over one label type, realized " +
		"over them, are compared through their class laws alone. X ∩ S = ∅ is load-bearing: a node " +
		"held at a point off a(i) and also observed there has probability 1, not its weight. So is " +
		"the second point of each carrier: the mass off a(i) needs a value to land on.",
	Deps: []registry.EntryLike{signProgramDef, signLawDef, ProjectionKernelsRealized},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀a:(I → B).",
		Hypotheses: []string{
			"infinite(𝕌⟨A:A⟩)",
			"infinite(𝕌⟨A:B⟩)",
			"dag_on(V, E)",
			"O ⊆ V",
			"∀i:I. i ∈ O ⇒ finite(D(i)) ∧ a(i) ∈ D(i) ∧ (∃b:B. b ∈ D(i) ∧ b ≠ a(i))",
		},
		Conclusion: "∃ν:(I → B → real). " +
			"    (∀i:I. ∀b:B. i ∈ O ∧ b ∈ D(i) ⇒ &0 < ν(i, b)) ∧ " +
			"    (∀Λ:set(C). ∀N:(C → set(I)). ∀g:(I → set(I) → set(C) → real). " +
			"        latent_sign_program(E, O, Λ, N, g) ⇒ " +
			"        (∃M:scm_model(A, B, I). " +
			"            scm_on(M) ∧ " +
			"            scm_noise_independent(M) ∧ " +
			"            M.nodes = V ∧ " +
			"            M.edges = E ∧ " +
			"            (∀i:I. i ∈ O ⇒ M.states(i) = D(i) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ D(i)}) ∧ " +
			"            (∀X S:set(I). ∀x w:(I → B). " +
			"                X ⊆ O ∧ S ⊆ O ∧ X ∩ S = ∅ ∧ (∀i:I. i ∈ X ⇒ x(i) ∈ D(i)) ⇒ " +
			"                scm_distribution(scm_do(M, X, x), agree_on(S, w)) = " +
			"                extended_of_real(COND(∀i:I. i ∈ S ⇒ w(i) ∈ D(i), " +
			"                        (Π_{i∈S} ν(i, w(i))) * " +
			"                        Σ_{z∈{z:set(I) | z ⊆ O ∧ (∀i:I. i ∈ X ⇒ (i ∈ z ⇔ x(i) ≠ a(i))) ∧ (∀i:I. i ∈ S ⇒ (i ∈ z ⇔ w(i) ≠ a(i)))}} latent_sign_law(O, Λ, g, X, z), " +
			"                        &0)))))",
	},
		"A sign program on the latent projection is realized on carriers of any finite size "+
			"with two points or more. Fix positive dyadic weights on each D(i) ∖ {a(i)} summing "+
			"to 1, and ν(i, a(i)) = 1. The program's kernel sends node v to a(v) with probability "+
			"(1 + g)/2 and to another point b with probability (1 − g)/2 · ν(v, b): dyadic with "+
			"one exponent, local as the program is, and normalized. ProjectionKernelsRealized "+
			"gives the model. In its formula the product over O ∖ X splits into the weights and "+
			"the class factors (1 ± g)/2; summing the configurations of one class configuration "+
			"sums each free node's weights to 1 and leaves the weights of S and the class laws."),
})}

var StepSignTelescope = stepSignTelescopeThm{family.Add(registry.ProofEntry{
	Name: "StepSignTelescope",
	Key:  "prop_6862e2fc5f8f591d",
	Reading: "τ is a next step, read only on F ∖ R, and no acyclicity is asked of " +
		"it. Each vertex off R and off A appears twice on the left, once for itself and " +
		"once at its successor, and squares to 1: a vertex stepping to itself with z = 2 " +
		"gives 4. The vertices of R and of A appear once, and z is any real there. That " +
		"τ keeps F ∖ R inside F is load-bearing: a vertex stepping out of F appears once.",
	Build: family.Card(Statement{
		Binders: "∀F R A:set(I). ∀τ:(I → I). ∀z:(I → real).",
		Hypotheses: []string{
			"finite(F)",
			"R ⊆ F",
			"A ⊆ F ∖ R",
			"∀w:I. w ∈ F ∧ w ∉ R ⇒ τ(w) ∈ F",
			"∀w:I. w ∈ F ∧ w ∉ R ∧ w ∉ A ⇒ z(w) * z(w) = &1",
		},
		Conclusion: "Π_{v∈F} (z(v) * Π_{w∈«stepsTo»(A, v)} z(w)) = (Π_{r∈R} z(r)) * Π_{u∈A} z(u)",
	},
		"Along a step map the product of each vertex's sign with the signs stepping to it "+
			"telescopes to the signs of the roots and of the vertices left out. Split the "+
			"product over F pointwise. The product over v of the product over the vertices "+
			"stepping to v is the product over the vertices of F off R and off A, regrouped by "+
			"their successors, which lie in F; the product over F is that of R, of A and of the "+
			"same vertices. The two products over the vertices off R and off A multiply to 1."),
})}

var ForestSignProgram = forestSignProgramThm{family.Add(registry.ProofEntry{
	Name: "ForestSignProgram",
	Key:  "prop_1df0eab468436edc",
	Reading: "The hypotheses make the forest mean a sign program on the projection. " +
		"Every label of Λ lies on a bidirected edge, whose two ends share a latent ancestor; " +
		"τ steps along directed edges of the projection, so a vertex reads the classes of " +
		"its parents only; W and κ are local and dyadic with exponent m; the bounds 1/4 on W " +
		"and on α·2^card(U) keep the mean within 1/2. The labels of the mean's own spins " +
		"must be among Λ, or it would read a bit outside its labels; that makes Ed finite.",
	Deps: []registry.EntryLike{
		forestSignMeanDef,
		signProgramDef,
		latent_projection.LatentBidirectedDef,
	},
	Build: family.Card(Statement{
		Binders: "∀E:(I → I → bool). " +
			"∀O F R U:set(I). " +
			"∀Ed:set(prod(I, I)). " +
			"∀Λ:set(prod(prod(I, I), set(I))). " +
			"∀τ:(I → I). " +
			"∀W κ:(I → set(I) → real). " +
			"∀α:(I → real). " +
			"∀m:num.",
		Hypotheses: []string{
			"finite(O)",
			"F ⊆ O",
			"R ⊆ F",
			"U ⊆ F",
			"finite(Λ)",
			"set_cross(Ed, {A:set(I) | A ⊆ U}) ⊆ Λ",
			"∀p:prod(prod(I, I), set(I)). p ∈ Λ ⇒ latent_proj_bidirected(E, O, fst(fst(p)), snd(fst(p)))",
			"∀w:I. w ∈ F ∧ w ∉ R ⇒ latent_proj_directed(E, O, w, τ(w))",
			"∀v:I. ∀z z':set(I). " +
				"    v ∈ O ∧ (∀u:I. latent_proj_directed(E, O, u, v) ⇒ (u ∈ z ⇔ u ∈ z')) ⇒ " +
				"    W(v, z) = W(v, z') ∧ κ(v, z) = κ(v, z')",
			"∀v:I. ∀z:set(I). " +
				"    v ∈ O ⇒ " +
				"    (∃n:num. W(v, z) = &n / &(2 ^ m) ∨ W(v, z) = -(&n / &(2 ^ m))) ∧ " +
				"    (∃n:num. κ(v, z) = &n / &(2 ^ m) ∨ κ(v, z) = -(&n / &(2 ^ m)))",
			"∀v:I. v ∈ F ⇒ (∃n:num. α(v) = &n / &(2 ^ m)) ∧ α(v) * &(2 ^ card(U)) ≤ &1 / &4",
			"∀v:I. ∀z:set(I). v ∈ O ⇒ -(&1 / &4) ≤ W(v, z) ∧ W(v, z) ≤ &1 / &4 ∧ -&1 ≤ κ(v, z) ∧ κ(v, z) ≤ &1",
		},
		Conclusion: "latent_sign_program(E, " +
			"    O, " +
			"    Λ, " +
			"    λp:prod(prod(I, I), set(I)). {fst(fst(p)), snd(fst(p))}, " +
			"    «mean») ∧ " +
			"(∀v:I. ∀z:set(I). ∀σ:set(prod(prod(I, I), set(I))). " +
			"    v ∈ O ⇒ -(&1 / &2) ≤ «mean»(v, z, σ) ∧ «mean»(v, z, σ) ≤ &1 / &2)",
	},
		"A forest mean with local, dyadic, bounded data is a sign program bounded by 1/2. Unfold "+
			"the mean. It reads the class set through W and κ, local by hypothesis, and through the "+
			"signs of the vertices τ sends to v, parents of v in the projection; it reads the bits at "+
			"the labels (e, A) with e an edge of Ed at v (forestSignMeanLocal), which are in Λ and "+
			"have v among their two readers. A product of signs is ±1, so the mean is a sum of 1 + "+
			"2^card(U) terms, each dyadic with exponent 2m, and (1 + mean)/2 is dyadic with exponent "+
			"2m + 1; it lies in [0, 1] by the bound. The bound: W is at most 1/4 in size, and each of "+
			"the 2^card(U) terms of the sum is at most α(v), its factors being signs and W, κ or 1."),
})}

var HedgeForestData = hedgeForestDataThm{family.Add(registry.ProofEntry{
	Name: "HedgeForestData",
	Key:  "prop_791bc23b9354c2c0",
	Reading: "Everything the construction takes from the graph. F lies among the observed " +
		"nodes because it has two vertices or more — one in X, and one of the smaller forest, " +
		"which misses X — and each is then an end of a bidirected edge of the projection. τ " +
		"is a step inside F from each vertex off the smaller forest. ρ is a step towards Y " +
		"along edges not entering X, and H the vertices met from the smaller forest along it, " +
		"stopping at Y. Acyclicity is not claimed here: the routes' is the projection's.",
	Deps: []registry.EntryLike{
		mixed_graph.HedgeRootsWhole,
		latent_projection.LatentDirectedDef,
		latent_projection.LatentBidirectedDef,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O X Y F F':set(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"mixed_graph_hedge(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, F, F')",
		},
		Conclusion: "F ⊆ O ∧ " +
			"F' ⊆ F ∧ " +
			"F' ≠ ∅ ∧ " +
			"F ∩ X ≠ ∅ ∧ " +
			"F' ∩ X = ∅ ∧ " +
			"«edgeFacts»(F) ∧ " +
			"«edgeFacts»(F') ∧ " +
			"(∃τ:(I → I). ∀w:I. w ∈ F ∧ w ∉ F' ⇒ τ(w) ∈ F ∧ latent_proj_directed(E, O, w, τ(w))) ∧ " +
			"(∃ρ:(I → I). ∃H:set(I). " +
			"    F' ⊆ H ∧ " +
			"    H ⊆ O ∧ " +
			"    H ∩ X = ∅ ∧ " +
			"    (∀u:I. u ∈ H ∧ u ∉ Y ⇒ ρ(u) ∈ H ∧ latent_proj_directed(E, O, u, ρ(u))) ∧ " +
			"    (∀v:I. v ∈ H ∧ v ∉ F' ⇒ (∃w:I. w ∈ H ∧ w ∉ Y ∧ ρ(w) = v)))",
		Abbrev: Abbrev{
			{Name: "edgeFacts", Text: "λS:set(I). " +
				"    finite({e:prod(I, I) | " +
				"            fst(e) ∈ S ∧ snd(e) ∈ S ∧ latent_proj_bidirected(E, O, fst(e), snd(e))}) ∧ " +
				"    (∀u v:I. " +
				"        u ∈ S ∧ v ∈ S ⇒ " +
				"        reflexive_transitive_closure(λa:I. λb:I. " +
				"                (a, b) ∈ " +
				"                {e:prod(I, I) | " +
				"                    fst(e) ∈ S ∧ snd(e) ∈ S ∧ latent_proj_bidirected(E, O, fst(e), snd(e))} ∨ " +
				"                (b, a) ∈ " +
				"                {e:prod(I, I) | " +
				"                    fst(e) ∈ S ∧ snd(e) ∈ S ∧ latent_proj_bidirected(E, O, fst(e), snd(e))}, " +
				"            u, " +
				"            v))"},
		},
	},
		"The graph side of the hedge construction. HedgeRootsWhole makes F′ the root set: F′ ⊆ "+
			"F, each connected by its own bidirected edges, each vertex of F reaching F′ inside F, "+
			"and F′ among the ancestors of Y with the edges into X deleted. F′ is nonempty, a vertex "+
			"of F reaching it. F has a vertex of X and one of F′, two vertices, so each vertex of F "+
			"starts a bidirected step and is observed, and the edges inside F are finitely many "+
			"pairs. A vertex of F off F′ reaches F′ inside F by a chain of at least one edge, whose "+
			"first step is τ. For ρ choose at each ancestor of Y off Y the first step of a chain to "+
			"Y; H is what F′ reaches along ρ, stopping at Y. H misses X, a vertex of H off F′ being "+
			"entered along an edge not into X; and it is entered from a vertex of H off Y."),
})}

var ClassMarginalsParity = classMarginalsParityThm{family.Add(registry.ProofEntry{
	Name: "ClassMarginalsParity",
	Key:  "prop_dd8446b089f4762c",
	Reading: "T ⊆ Y is load-bearing: the parity must be read off the classes on Y. T " +
		"may be infinite, the product being a function of the classes on T either way. " +
		"Read backwards: two laws whose parities of T differ have different marginals on Y.",
	Deps: []registry.EntryLike{monoidal.Regroup},
	Build: family.Card(Statement{
		Binders: "∀O X Y T:set(I). ∀L M:(set(I) → real).",
		Hypotheses: []string{
			"finite(O)",
			"T ⊆ Y",
			"∀z:set(I). " +
				"    Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅ ∧ y ∩ Y = z ∩ Y}} L(y) = " +
				"    Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅ ∧ y ∩ Y = z ∩ Y}} M(y)",
		},
		Conclusion: "Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅}} (Π_{t∈T} «sgn»(t ∈ y)) * L(y) = " +
			"Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅}} (Π_{t∈T} «sgn»(t ∈ y)) * M(y)",
	},
		"Two functions on the class sets off X with the same marginals on Y have the same sum against "+
			"the parity of T. Regroup each sum by the classes on Y (monoidal's Regroup, along y ↦ y ∩ Y): "+
			"the parity of T is constant on a fibre, T lying in Y, and the fibre sums are the marginals."),
})}
