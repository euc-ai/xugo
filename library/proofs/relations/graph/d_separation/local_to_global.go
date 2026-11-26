package d_separation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

type independenceRelation = Expr[Fun3[Set[A], Set[A], Set[A], Bool]]

type semigraphoidLaws struct {
	trivial, symmetric, decompose, weakUnion, contract Fact
}

func readSemigraphoid(a *Argument, semigraphoid Fact) semigraphoidLaws {
	laws := a.Conjuncts(
		a.Unfolded(semigraphoid, SemigraphoidOn),
		"X is independent of the empty set",
		"independence is symmetric",
		"independence of Y ∪ W gives independence of Y",
		"independence of Y ∪ W moves W into the condition",
		"independence of Y given Z ∪ W and of W given Z join by contraction")
	return semigraphoidLaws{laws[0], laws[1], laws[2], laws[3], laws[4]}
}

// LocalToGlobalMarkov — on a DAG, a semigraphoid with the local Markov
// property at every vertex holds at every d-separation: when Z separates
// disjoint X and Y, X is independent of Y given Z. The proof removes sinks
// from the ancestral set; the sink and its parents miss one side of the
// moral cut, which allows contraction on the other.
var LocalToGlobalMarkov = localToGlobalMarkovThm{family.Add(registry.ProofEntry{
	Name: "LocalToGlobalMarkov",
	Key:  "prop_b4175d4daaa60135",
	Build: family.Sections(Statement{
		Binders: "∀V:set(A). ∀E:(A → A → bool). ∀R:(set(A) → set(A) → set(A) → bool). ∀X Y Z:set(A).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"semigraphoid_on(V, R)",
			"∀i:A. i ∈ V ⇒ R({i}, V ∖ dag_descendants(E, {i}) ∖ dag_parents(E, i), dag_parents(E, i))",
			"X ⊆ V",
			"Y ⊆ V",
			"Z ⊆ V",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"d_separated(E, X, Y, Z)",
		},
		Conclusion: "R(X, Y, Z)",
		Abbrev: Abbrev{
			{Name: "Anc", Text: "dag_ancestors(E, X ∪ Y ∪ Z)"},
		},
	}, buildLocalToGlobalMarkov),
})}

func decomposeRight(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀V:set(A). ∀R:(set(A) → set(A) → set(A) → bool). ∀X Y Z W:set(A).",
		Hypotheses: []string{
			"semigraphoid_on(V, R)", "X ⊆ V", "Y ⊆ V", "Z ⊆ V",
			"X ∩ Y = ∅", "X ∩ Z = ∅", "Y ∩ Z = ∅", "W ⊆ Y", "R(X, Y, Z)",
		},
		Conclusion: "R(X, W, Z)",
	}, func(a *Argument, V *Expr[Set[A]], R *independenceRelation, X, Y, Z, W *Expr[Set[A]],
		semigraphoid, inX, inY, inZ, apartXY, apartXZ, apartYZ, subset, independent Fact) {
		decompose := readSemigraphoid(a, semigraphoid).decompose
		split := a.Have(
			"split Y into W and its complement in Y",
			"W ∪ (Y ∖ W) = Y",
			BySets(subset))
		moved := a.Have(
			"read Y as W with its complement",
			"R(X, W ∪ (Y ∖ W), Z)",
			By(Normalized, independent, split))
		rest := a.TermAs[Set[A]]("Y ∖ W")
		a.Show(
			"decompose to W",
			BySets(decompose.At(X, W, rest, Z), moved, inX, inY, inZ, apartXY, apartXZ, apartYZ, subset))
	})
}

func pruneParentClosed(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀E:(A → A → bool). ∀U:set(A). ∀s:A.",
		Hypotheses: []string{"dag_ancestral(E, U)", "∀t:A. t ∈ U ⇒ ¬E(s, t)"},
		Conclusion: "dag_ancestral(E, U ∖ {s})",
	}, func(a *Argument, E *Arrow2[A, A, Bool], U *Expr[Set[A]], s *Expr[A], ancestral, sink Fact) {
		parents := a.Unfolded(ancestral, dag.AncestralDef)
		a.Show(
			"removing a sink keeps U ancestral",
			Unfold(dag.AncestralDef),
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				b.Show(
					"a parent could not be the sink",
					BySets(parents.At(u, v), sink.At(v), edge))
			}))
	})
}

func restrictSinkLocal(ctx *Script, prune, decompose *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀V U:set(A). ∀E:(A → A → bool). ∀R:(set(A) → set(A) → set(A) → bool). ∀s:A.",
		Hypotheses: []string{
			"semigraphoid_on(V, R)", "U ⊆ V", "s ∈ U",
			"dag_ancestral(E, U)",
			"∀t:A. t ∈ U ⇒ ¬E(s, t)", "R({s}, «NonDescendants», dag_parents(E, s))",
		},
		Conclusion: "R({s}, «PrunedNonparents», dag_parents(E, s))",
		Abbrev: Abbrev{
			{Name: "NonDescendants", Text: "V ∖ dag_descendants(E, {s}) ∖ dag_parents(E, s)"},
			{Name: "PrunedNonparents", Text: "U ∖ {s} ∖ dag_parents(E, s)"},
		},
	}, func(a *Argument, V, U *Expr[Set[A]], E *Arrow2[A, A, Bool], R *independenceRelation, s *Expr[A],
		semigraphoid, subV, inU, ancestral, sink, local Fact) {
		singleton := a.TermAs[Set[A]]("{s}")
		pruned := a.TermAs[Set[A]]("U ∖ {s}")
		parents := a.TermAs[Set[A]]("dag_parents(E, s)")
		prunedClosed := a.Have(
			"sink deletion keeps the set ancestral",
			"dag_ancestral(E, U ∖ {s})",
			By(At(prune, E, U, s), ancestral, sink))
		prunedAncestors := a.Have(
			"the pruned set contains its ancestors",
			"dag_ancestors(E, U ∖ {s}) ⊆ U ∖ {s}",
			By(dag.AncestorsUpperBound.At(E, pruned, pruned), set_order.SubsetRefl.At(pruned), prunedClosed))
		avoidsSink := a.Have(
			"the pruned ancestors miss the sink",
			"dag_ancestors(E, U ∖ {s}) ∩ {s} = ∅",
			BySets(prunedAncestors))
		avoidsDescendants := a.Have(
			"the pruned set misses descendants of the sink",
			"dag_descendants(E, {s}) ∩ (U ∖ {s}) = ∅",
			By(dag.DescendantsAncestorsDual.At(E, singleton, pruned), avoidsSink))
		smaller := a.Have(
			"the remaining nonparents lie in the original set the sink is independent of",
			"«PrunedNonparents» ⊆ «NonDescendants»",
			BySets(avoidsDescendants, subV))
		parentsOfU := a.Unfolded(ancestral, dag.AncestralDef)
		parentsInU := a.Have(
			"the parents belong to U, which is ancestral",
			"dag_parents(E, s) ⊆ U",
			Simp(Fwd(set_basic.SubsetDef), Fwd(dag.ParentsDef)),
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				parent := b.Assume()
				b.Show(
					"the parent edge reaches a vertex of U",
					BySets(parentsOfU.At(x, s), inU, parent))
			}))
		inSingleton := a.Have(
			"the singleton contains the sink",
			"s ∈ {s}",
			BySets())
		zeroSteps := a.Have(
			"the sink reaches itself in zero steps",
			"reflexive_transitive_closure(E, s, s)",
			By(closure.ReflexiveTransitiveClosureDef.At(E, s, s)))
		witness := a.Have(
			"the sink itself witnesses reachability from its singleton",
			"∃x:A. x ∈ {s} ∧ reflexive_transitive_closure(E, x, s)",
			Witness(s),
			By(inSingleton, zeroSteps))
		selfDescendant := a.Have(
			"the sink belongs to its descendants",
			"s ∈ dag_descendants(E, {s})",
			Simp(Fwd(dag.DescendantsDef)),
			BySets(witness))
		noSelfParent := a.Have(
			"the sink has no self-edge",
			"s ∉ dag_parents(E, s)",
			Simp(Fwd(dag.ParentsDef)),
			BySets(sink.At(s), inU))
		original := a.TermAs[Set[A]]("«NonDescendants»")
		remaining := a.TermAs[Set[A]]("«PrunedNonparents»")
		a.Show(
			"restrict the local statement to the remaining vertices",
			BySets(
				At(decompose, V, R, singleton, original, parents, remaining),
				semigraphoid,
				smaller,
				local,
				inU,
				subV,
				parentsInU,
				selfDescendant,
				noSelfParent))
	})
}

func reattachIndependence(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀V:set(A). ∀R:(set(A) → set(A) → set(A) → bool). ∀X Y Z S P:set(A).",
		Hypotheses: []string{
			"semigraphoid_on(V, R)", "X ∪ Y ∪ Z ⊆ V", "X ∩ Y = ∅", "X ∩ Z = ∅", "Y ∩ Z = ∅",
			"S ⊆ X ∪ Z", "P ⊆ (X ∪ Z) ∖ S", "R(S, «Remainder», P)", "R(X ∖ S, Y, Z ∖ S)",
		},
		Conclusion: "R(X, Y, Z)",
		Abbrev: Abbrev{
			{Name: "Remainder", Text: "(X ∪ Y ∪ Z) ∖ S ∖ P"},
			{Name: "Nonparents", Text: "((Z ∖ S) ∪ (X ∖ S)) ∖ P"},
		},
	}, func(a *Argument, V *Expr[Set[A]], R *independenceRelation, X, Y, Z, S, P *Expr[Set[A]],
		semigraphoid, carrier, apartXY, apartXZ, apartYZ, reattached, parents, local, smaller Fact) {
		laws := readSemigraphoid(a, semigraphoid)
		left := a.TermAs[Set[A]]("X ∖ S")
		condition := a.TermAs[Set[A]]("Z ∖ S")
		nonparents := a.TermAs[Set[A]]("«Nonparents»")
		moved := a.TermAs[Set[A]]("(Z ∖ S) ∪ (X ∖ S)")
		onRight := a.Have(
			"Y and the other nonparents make up the remainder",
			"Y ∪ «Nonparents» = «Remainder»",
			BySets(apartXY, apartYZ, reattached, parents))
		conditioning := a.Have(
			"the parents and the other nonparents cover the pruned X and Z",
			"P ∪ «Nonparents» = (Z ∖ S) ∪ (X ∖ S)",
			BySets(parents))
		localSplit := a.Have(
			"read the remainder as Y with the other nonparents",
			"R(S, Y ∪ «Nonparents», P)",
			By(local, onRight))
		weakened := a.Have(
			"weak union moves the other nonparents into the condition",
			"R(S, Y, P ∪ «Nonparents»)",
			BySets(
				laws.weakUnion.At(S, Y, nonparents, P),
				localSplit,
				carrier,
				apartXY,
				apartYZ,
				reattached,
				parents))
		fromS := a.Have(
			"the condition is the pruned X and Z",
			"R(S, Y, (Z ∖ S) ∪ (X ∖ S))",
			By(weakened, conditioning))
		toS := a.Have(
			"read the local statement from Y",
			"R(Y, S, (Z ∖ S) ∪ (X ∖ S))",
			BySets(laws.symmetric.At(S, Y, moved), fromS, carrier, apartXY, apartYZ, reattached))
		toPruned := a.Have(
			"read the pruned independence from Y",
			"R(Y, X ∖ S, Z ∖ S)",
			BySets(laws.symmetric.At(left, Y, condition), smaller, carrier, apartXY, apartXZ, apartYZ))
		joined := a.Have(
			"contract to reattach S",
			"R(Y, S ∪ (X ∖ S), Z ∖ S)",
			BySets(
				laws.contract.At(Y, S, left, condition),
				toS,
				toPruned,
				carrier,
				apartXY,
				apartXZ,
				apartYZ,
				reattached))
		split := a.Have(
			"the reattached vertices belong to X or to the restored part of Z",
			"X ∪ (Z ∩ S) = S ∪ (X ∖ S)",
			BySets(apartXZ, reattached))
		restoreZ := a.Have(
			"restore the conditioning set Z",
			"(Z ∖ S) ∪ (Z ∩ S) = Z",
			BySets())
		movedToZ := a.TermAs[Set[A]]("Z ∩ S")
		regrouped := a.Have(
			"read the reattached vertices as X with the restored part of Z",
			"R(Y, X ∪ (Z ∩ S), Z ∖ S)",
			By(Normalized, joined, split))
		conditioned := a.Have(
			"weak union puts the restored part of Z back into the condition",
			"R(Y, X, (Z ∖ S) ∪ (Z ∩ S))",
			BySets(laws.weakUnion.At(Y, X, movedToZ, condition), regrouped, carrier, apartXY, apartXZ, apartYZ))
		restored := a.Have(
			"the condition is Z again",
			"R(Y, X, Z)",
			By(Normalized, conditioned, restoreZ))
		a.Show(
			"read the restored independence from X",
			BySets(laws.symmetric.At(Y, X, Z), restored, carrier, apartXY, apartXZ, apartYZ))
	})
}

func moralFamilyMissesOneSide(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀U X Y:set(A). ∀E:(A → A → bool). ∀s:A.",
		Hypotheses: []string{
			"s ∈ U", "X ∩ Y = ∅",
			"∀u v:A. u ∈ X ∧ v ∈ Y ⇒ ¬dag_moral(E, U, u, v)",
		},
		Conclusion: "«Family» ∩ Y = ∅ ∨ «Family» ∩ X = ∅",
		Abbrev: Abbrev{
			{Name: "Family", Text: "{s} ∪ dag_parents(E, s)"},
		},
	}, func(
		a *Argument,
		U, X, Y *Expr[Set[A]],
		E *Arrow2[A, A, Bool],
		s *Expr[A],
		child, apart, cut Fact,
	) {
		noPair := a.Have(
			"vertices in the family on both sides would be morally adjacent",
			"∀u v:A. u ∈ X ∩ «Family» ∧ v ∈ Y ∩ «Family» ⇒ ⊥",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				familyPair := b.Assume()
				onSides := b.Have(
					"the disjoint sides give distinct vertices",
					"u ∈ X ∧ v ∈ Y ∧ u ≠ v",
					BySets(familyPair, apart))
				incident := b.Have(
					"the two vertices are joined directly or through their child s",
					"E(u, v) ∨ E(v, u) ∨ (E(u, s) ∧ E(v, s))",
					BySets(familyPair, onSides))
				b.Show(
					"moral adjacency contradicts the cut",
					By(cut.At(u, v), onSides, child, incident, MoralDef.At(E, U, u, v)))
			}))
		a.Show(
			"at least one side misses the family",
			BySets(noPair))
	})
}

// markovOnMoralCut: on a finite parent-closed U inside V and M, X is
// independent of Y given Z for every partition X, Y, Z of U with no edge
// of the moral graph on M between X and Y. M is kept apart from U and
// fixed throughout the induction on U, so the smaller partition inherits
// the same cut: a child in M still witnesses a moral edge after pruning.
func markovOnMoralCut(
	ctx *Script,
	prune, sinkLocal, reattach, familyMissesSide *GoalStackNode,
) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀V M U:set(A). ∀E:(A → A → bool). ∀R:(set(A) → set(A) → set(A) → bool).",
		Hypotheses: []string{
			"finite(U)", "dag_on(V, E)", "semigraphoid_on(V, R)",
			"∀i:A. i ∈ V ⇒ R({i}, V ∖ dag_descendants(E, {i}) ∖ dag_parents(E, i), dag_parents(E, i))",
		},
		Conclusion: "U ⊆ V ∧ U ⊆ M ∧ dag_ancestral(E, U) ⇒ " +
			"∀X Y Z:set(A). " +
			"    X ∪ Y ∪ Z = U ∧ " +
			"    X ∩ Y = ∅ ∧ " +
			"    X ∩ Z = ∅ ∧ " +
			"    Y ∩ Z = ∅ ∧ " +
			"    (∀u v:A. u ∈ X ∧ v ∈ Y ⇒ ¬dag_moral(E, M, u, v)) ⇒ " +
			"    R(X, Y, Z)",
	}, func(a *Argument, V, M, U *Expr[Set[A]], E *Arrow2[A, A, Bool], R *independenceRelation) {
		fixed := a.Conjuncts(
			a.Assume(),
			"the carrier of induction is finite",
			"the original graph is a DAG",
			"R is a semigraphoid",
			"R satisfies the local Markov condition")
		finite, dagOn, semigraphoid, local := fixed[0], fixed[1], fixed[2], fixed[3]
		a.Do(ByInduction(finite_set.FiniteInductProperSubset, finite,
			Case(
				"prove a cut by induction on proper subsets of its carrier",
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]("T")
					rank := b.Assume()
					scope := b.Assume()
					X := b.FixAs[Set[A]]()
					Y := b.FixAs[Set[A]]()
					Z := b.FixAs[Set[A]]()
					partition := b.Assume()
					ih := b.Conjuncts(
						rank,
						"the carrier is finite",
						"every proper subset satisfies the induction property")[1]
					region := b.Conjuncts(
						scope,
						"the cut lies in V",
						"the cut lies in M",
						"the carrier is ancestral")
					subV, subM, ancestral := region[0], region[1], region[2]
					parts := b.Conjuncts(
						partition,
						"X, Y and Z cover the carrier",
						"X misses Y",
						"X misses Z",
						"Y misses Z",
						"moral adjacency cannot cross between X and Y")
					cover, apartXY, apartXZ, apartYZ, cut := parts[0], parts[1], parts[2], parts[3], parts[4]
					laws := readSemigraphoid(b, semigraphoid)
					b.Cases(b.Term("T = ∅"))
					b.When(
						"triviality on the empty carrier",
						func(c *Argument, empty Fact) {
							guard := c.Have(
								"X and Z lie in V and Y is empty",
								"X ⊆ V ∧ Z ⊆ V ∧ Y = ∅",
								BySets(cover, empty))
							c.Show(
								"X is independent of the empty Y",
								By(Normalized, laws.trivial.At(X, Z), guard, apartXZ))
						})
					b.Otherwise(
						"delete a sink and reattach it along the cut",
						func(c *Argument, nonempty Fact) {
							s, sink := c.ObtainAs[A](
								"take a sink of T",
								"∃s:A. s ∈ T ∧ (∀t:A. t ∈ T ⇒ ¬E(s, t))",
								By(dag.DagSinkExists.At(V, T, E), dagOn, nonempty))
							sinkParts := c.Conjuncts(
								sink,
								"the sink belongs to T",
								"no edge leaves the sink for T")
							inT, noOutgoing := sinkParts[0], sinkParts[1]
							pruned := c.TermAs[Set[A]]("T ∖ {s}")
							prunedX := c.TermAs[Set[A]]("X ∖ {s}")
							prunedY := c.TermAs[Set[A]]("Y ∖ {s}")
							prunedZ := c.TermAs[Set[A]]("Z ∖ {s}")
							singleton := c.TermAs[Set[A]]("{s}")
							parents := c.TermAs[Set[A]]("dag_parents(E, s)")
							below := c.Have(
								"deleting the sink gives a proper subset within V and M",
								"T ∖ {s} ⊊ T ∧ T ∖ {s} ⊆ V ∧ T ∖ {s} ⊆ M",
								Simp(Fwd(set_basic.ProperSubsetDef)),
								BySets(inT, subV, subM))
							prunedClosed := c.Have(
								"the pruned carrier is ancestral",
								"dag_ancestral(E, T ∖ {s})",
								By(At(prune, E, T, s), ancestral, noOutgoing))
							prunedPartition := c.Have(
								"remove the sink from all three parts",
								"(X ∖ {s}) ∪ (Y ∖ {s}) ∪ (Z ∖ {s}) = T ∖ {s} ∧ "+
									"(X ∖ {s}) ∩ (Y ∖ {s}) = ∅ ∧ "+
									"(X ∖ {s}) ∩ (Z ∖ {s}) = ∅ ∧ "+
									"(Y ∖ {s}) ∩ (Z ∖ {s}) = ∅",
								BySets(cover, apartXY, apartXZ, apartYZ))
							prunedCut := c.Have(
								"the moral cut still holds between the pruned sides",
								"∀u v:A. u ∈ X ∖ {s} ∧ v ∈ Y ∖ {s} ⇒ ¬dag_moral(E, M, u, v)",
								Derive(func(d *Argument) {
									u := d.FixAs[A]()
									v := d.FixAs[A]()
									endpoints := d.Assume()
									d.Show(
										"each pruned endpoint belongs to its original side",
										BySets(cut.At(u, v), endpoints))
								}))
							smaller := c.Have(
								"apply induction to the pruned partition",
								"R(X ∖ {s}, Y ∖ {s}, Z ∖ {s})",
								By(ih.At(pruned, prunedX, prunedY, prunedZ), below, prunedClosed, prunedPartition, prunedCut))
							parentsOfT := c.Unfolded(ancestral, dag.AncestralDef)
							parentsInPruned := c.Have(
								"every parent of the sink lies in the pruned carrier",
								"dag_parents(E, s) ⊆ T ∖ {s}",
								Simp(Fwd(set_basic.SubsetDef), Fwd(dag.ParentsDef)),
								Derive(func(d *Argument) {
									x := d.FixAs[A]()
									edge := d.Assume()
									d.Show(
										"the parent of s lies in T, which is ancestral, and the sink has no self-edge",
										BySets(parentsOfT.At(x, s), noOutgoing.At(s), inT, edge))
								}))
							sinkScope := c.Have(
								"the sink lies in V and in the ambient moral carrier",
								"s ∈ V ∧ s ∈ M",
								BySets(inT, subV, subM))
							atSink := c.Have(
								"read the vertexwise Markov statement at the sink",
								"R({s}, V ∖ dag_descendants(E, {s}) ∖ dag_parents(E, s), dag_parents(E, s))",
								By(local.At(s), sinkScope))
							onPruned := c.Have(
								"restrict the sink's local statement to T",
								"R({s}, T ∖ {s} ∖ dag_parents(E, s), dag_parents(E, s))",
								By(At(sinkLocal, V, T, E, R, s), semigraphoid, subV, inT, ancestral, noOutgoing, atSink))
							oneSide := c.Have(
								"the sink and its parents miss one side of the moral cut",
								"({s} ∪ dag_parents(E, s)) ∩ Y = ∅ ∨ ({s} ∪ dag_parents(E, s)) ∩ X = ∅",
								By(At(familyMissesSide, M, X, Y, E, s), sinkScope, apartXY, cut))

							c.Do(oneSide.SplitDisj(
								LeftHolds(
									"reattach the sink opposite Y",
									Given(func(d *Argument, missesY Fact) {
										ready := d.Have(
											"the sink and its parents belong on the X side of the cut or in Z",
											"X ∪ Y ∪ Z ⊆ V ∧ {s} ⊆ X ∪ Z ∧ dag_parents(E, s) ⊆ (X ∪ Z) ∖ {s} ∧ Y ∖ {s} = Y",
											BySets(cover, subV, inT, parentsInPruned, missesY))
										d.Show(
											"reattach while keeping Y fixed",
											By(
												At(reattach, V, R, X, Y, Z, singleton, parents),
												ready,
												cover,
												apartXY,
												apartXZ,
												apartYZ,
												semigraphoid,
												onPruned,
												smaller))
									})),
								RightHolds(
									"reattach the sink opposite X",
									Given(func(d *Argument, missesX Fact) {
										reversed := d.Have(
											"read the pruned independence from Y",
											"R(Y ∖ {s}, X ∖ {s}, Z ∖ {s})",
											BySets(laws.symmetric.At(prunedX, prunedY, prunedZ), smaller, prunedPartition, cover, subV))
										ready := d.Have(
											"the reversed cut lets the sink rejoin Y or Z",
											"Y ∪ X ∪ Z ⊆ V ∧ Y ∪ X ∪ Z = T ∧ {s} ⊆ Y ∪ Z ∧ dag_parents(E, s) ⊆ (Y ∪ Z) ∖ {s} ∧ X ∖ {s} = X",
											BySets(cover, subV, inT, parentsInPruned, missesX))
										apartYX := d.Have(
											"Y misses X",
											"Y ∩ X = ∅",
											BySets(apartXY))
										restored := d.Have(
											"reattach the sink while keeping X fixed",
											"R(Y, X, Z)",
											By(
												At(reattach, V, R, Y, X, Z, singleton, parents),
												ready,
												apartYX,
												apartYZ,
												apartXZ,
												semigraphoid,
												onPruned,
												reversed))
										d.Show(
											"read the restored independence from X",
											BySets(laws.symmetric.At(Y, X, Z), restored, cover, subV, apartXY, apartXZ, apartYZ))
									})),
							))
						})
				})),
		))
	})
}

func completeMoralPartition(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀U S Z:set(A).",
		Hypotheses: []string{"S ⊆ U ∖ Z", "Z ⊆ U"},
		Conclusion: "S ∪ «ComplementPart» ∪ Z = U ∧ " +
			"S ∩ «ComplementPart» = ∅ ∧ " +
			"S ∩ Z = ∅ ∧ " +
			"«ComplementPart» ∩ Z = ∅",
		Abbrev: Abbrev{{Name: "ComplementPart", Text: "U ∖ (S ∪ Z)"}},
	}, func(a *Argument, U, S, Z *Expr[Set[A]], inside, condition Fact) {
		a.Show(
			"split U into the left side, the condition and their complement",
			BySets(inside, condition))
	})
}

func decomposeBothSides(ctx *Script, decompose *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀V:set(A). ∀R:(set(A) → set(A) → set(A) → bool). ∀L B X Y Z:set(A).",
		Hypotheses: []string{
			"semigraphoid_on(V, R)", "L ∪ B ∪ Z ⊆ V", "L ∩ B = ∅", "L ∩ Z = ∅", "B ∩ Z = ∅",
			"X ⊆ L", "Y ⊆ B", "R(L, B, Z)",
		},
		Conclusion: "R(X, Y, Z)",
	}, func(a *Argument, V *Expr[Set[A]], R *independenceRelation, L, B, X, Y, Z *Expr[Set[A]],
		semigraphoid, scope, apartLB, apartLZ, apartBZ, left, right, independent Fact) {
		symmetric := readSemigraphoid(a, semigraphoid).symmetric
		toY := a.Have(
			"decompose B to Y",
			"R(L, Y, Z)",
			BySets(
				At(decompose, V, R, L, B, Z, Y),
				semigraphoid,
				independent,
				scope,
				apartLB,
				apartLZ,
				apartBZ,
				right))
		fromY := a.Have(
			"read the independence from Y",
			"R(Y, L, Z)",
			BySets(symmetric.At(L, Y, Z), toY, scope, apartLB, apartLZ, apartBZ, right))
		toX := a.Have(
			"decompose L to X",
			"R(Y, X, Z)",
			BySets(
				At(decompose, V, R, Y, L, Z, X),
				semigraphoid,
				fromY,
				scope,
				apartLB,
				apartLZ,
				apartBZ,
				left,
				right))
		a.Show(
			"read the restricted independence from X",
			BySets(symmetric.At(Y, X, Z), toX, scope, apartLB, apartLZ, apartBZ, left, right))
	})
}

func buildLocalToGlobalMarkov(ctx *Script, headline string) *GoalStackNode {
	decompose := decomposeRight(ctx)
	prune := pruneParentClosed(ctx)
	sinkLocal := restrictSinkLocal(ctx, prune, decompose)
	reattach := reattachIndependence(ctx)
	familyMissesSide := moralFamilyMissesOneSide(ctx)
	markovCut := markovOnMoralCut(ctx, prune, sinkLocal, reattach, familyMissesSide)
	partition := completeMoralPartition(ctx)
	shrinkSides := decomposeBothSides(ctx, decompose)

	return ctx.Theorem(headline, func(a *Argument, V *Expr[Set[A]], E *Arrow2[A, A, Bool],
		R *independenceRelation, X, Y, Z *Expr[Set[A]],
		dagOn, semigraphoid, local, subX, subY, subZ, apartXY, apartXZ, apartYZ, separated Fact) {
		dagFacts := a.Conjuncts(
			a.Unfolded(dagOn, dag.DagOn),
			"the DAG carrier is finite",
			"every edge has both endpoints in V",
			"the graph has no directed cycles")
		finiteV, edgesInV := dagFacts[0], dagFacts[1]
		ancestralV := a.Have(
			"the graph carrier is ancestral",
			"dag_ancestral(E, V)",
			Unfold(dag.AncestralDef),
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				incoming := b.Assume()
				b.Show(
					"the source of an edge belongs to V",
					By(edgesInV.At(u, v), incoming))
			}))
		union := a.TermAs[Set[A]]("X ∪ Y ∪ Z")
		ancestors := a.TermAs[Set[A]]("«Anc»")
		unionInV := a.Have(
			"the three given sets lie in V",
			"X ∪ Y ∪ Z ⊆ V",
			BySets(subX, subY, subZ))
		ancestorScope := a.Have(
			"the ancestral set contains X, Y and Z and is ancestral",
			"X ∪ Y ∪ Z ⊆ «Anc» ∧ dag_ancestral(E, «Anc»)",
			By(dag.AncestorsClosed.At(E, union)))
		ancestorsInV := a.Have(
			"all ancestors lie in V",
			"«Anc» ⊆ V",
			By(dag.AncestorsUpperBound.At(E, union, V), unionInV, ancestralV))
		finiteAncestors := a.Have(
			"the ancestral set is finite",
			"finite(«Anc»)",
			By(finite_set.FiniteSubset.At(ancestors, V), ancestorsInV, finiteV))
		containsX := a.Have(
			"the ancestral set contains X",
			"X ⊆ «Anc»",
			BySets(ancestorScope))
		left, certificate := a.UnpackAs[Set[A]](
			GroupPremises(
				apartXY,
				apartXZ,
				containsX,
				set_order.SubsetRefl.At(ancestors),
				separated,
				SeparationGivesCertificate.At(E, X, Y, Z, ancestors)),
			"L")
		leftPart := a.Conjuncts(
			certificate,
			"L contains X",
			"L lies in the ancestral set outside Z",
			"L misses Y",
			"a moral step outside Z stays in L")
		right, rightDef := a.LetAs[Set[A]]("B", "«Anc» ∖ (L ∪ Z)")
		rightContainsY := a.Have(
			"Y lies in the other part of the ancestral set outside Z",
			"Y ⊆ B",
			BySets(leftPart[2], apartYZ, ancestorScope, rightDef))
		cut := a.Have(
			"no moral edge crosses the partition",
			"∀u v:A. u ∈ L ∧ v ∈ B ⇒ ¬dag_moral(E, «Anc», u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				sides := b.Assume()
				b.Show(
					"a crossing moral edge would put v in L",
					BySets(sides, leftPart[3].At(u, v), rightDef))
			}))
		parts := a.Have(
			"the two sides and Z partition the ancestral set",
			"L ∪ B ∪ Z = «Anc» ∧ L ∩ B = ∅ ∧ L ∩ Z = ∅ ∧ B ∩ Z = ∅",
			Derive(func(b *Argument) {
				conditionInUnion := b.Have(
					"Z is part of the given union",
					"Z ⊆ X ∪ Y ∪ Z",
					BySets())
				conditionInAncestors := b.Have(
					"Z is in the ancestral set",
					"Z ⊆ «Anc»",
					By(conditionInUnion, ancestorScope, set_order.SubsetTrans.At(Z, union, ancestors)))
				b.Show(
					"the right part is the complement of the left part and Z",
					By(Normalized, At(partition, ancestors, left, Z), leftPart[1], conditionInAncestors, rightDef))
			}))
		independent := a.Have(
			"apply the moral cut theorem to the ancestral partition",
			"R(L, B, Z)",
			By(
				At(markovCut, V, ancestors, ancestors, E, R, left, right, Z),
				finiteAncestors,
				dagOn,
				semigraphoid,
				local,
				ancestorsInV,
				set_order.SubsetRefl.At(ancestors),
				ancestorScope,
				parts,
				cut))
		a.Show(
			"decompose from the two sides to X and Y",
			By(
				Normalized,
				At(shrinkSides, V, R, left, right, X, Y, Z),
				semigraphoid,
				leftPart[0],
				rightContainsY,
				ancestorsInV,
				parts,
				independent))
	})
}
