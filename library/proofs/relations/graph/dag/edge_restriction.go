package dag

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// DagSubrelation says that removing edges preserves the DAG on V.
var DagSubrelation = dagSubrelationThm{family.Add(registry.ProofEntry{
	Name: "DagSubrelation",
	Key:  "prop_34c5190b8831f815",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀E F:(A → A → bool).",
		Hypotheses: []string{"dag_on(V, E)", "∀x y:A. F(x, y) ⇒ E(x, y)"},
		Conclusion: "dag_on(V, F)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		E, F *Arrow2[A, A, Bool],
		graph DagFact[on.V],
		fewerEdges Fact,
	) {
		dagFacts := a.Conjuncts(
			a.Unfolded(graph, DagOn),
			"V is finite",
			"the endpoints of E lie in V",
			"E has no cycle")
		a.Do(Unfold(DagOn))
		endpoints := a.Have(
			"every F edge has both endpoints in V",
			"∀x y:A. F(x, y) ⇒ x ∈ V ∧ y ∈ V",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				y := b.FixAs[A]()
				edge := b.Assume()
				b.Show(
					"an F edge is an E edge",
					By(edge, fewerEdges.At(x, y), dagFacts[1].At(x, y)))
			}))
		acyclic := a.Have(
			"F has no cycle",
			"∀x:A. ¬transitive_closure(F, x, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				b.Show(
					"a cycle in F would also be a cycle in E",
					By(fewerEdges, dagFacts[2].At(x), closure.Monotone.At(F, E, x, x)))
			}))
		a.Show(
			"finiteness, endpoint containment, and acyclicity give the DAG on V",
			By(dagFacts[0], endpoints, acyclic))
	}),
})}

// AncestorsDeleteOut preserves the ancestors of X when the tails of
// all deleted edges already belong to X.
var AncestorsDeleteOut = ancestorsDeleteOutThm{family.Add(registry.ProofEntry{
	Name: "AncestorsDeleteOut",
	Key:  "prop_1459154ae9b39a44",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X Z:set(A).",
		Hypotheses: []string{"Z ⊆ X"},
		Conclusion: "dag_ancestors(dag_delete_out(E, Z), X) = dag_ancestors(E, X)",
		Abbrev: Abbrev{
			{Name: "U", Text: "dag_ancestors(dag_delete_out(E, Z), X)"},
		},
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Z *Expr[Set[A]], tailsInX Fact) {
		deleted := a.TermAs[Fun2[A, A, Bool]]("dag_delete_out(E, Z)")
		restrictedAncestors := a.TermAs[Set[A]]("«U»")
		inOriginal := a.Have(
			"every ancestor in the restricted graph is an ancestor in the original graph",
			"«U» ⊆ dag_ancestors(E, X)",
			Derive(func(b *Argument) {
				retained := b.Have(
					"every retained edge belongs to E",
					"∀u v:A. dag_delete_out(E, Z, u, v) ⇒ E(u, v)",
					By(DeleteOutDef))
				b.Show(
					"every walk in the restricted graph is an original walk",
					By(retained, set_order.SubsetRefl.At(X), AncestorsMonotone.At(deleted, E, X, X)))
			}))
		inRestricted := a.Have(
			"every original ancestor belongs to the restricted ancestor set",
			"dag_ancestors(E, X) ⊆ «U»",
			Derive(func(b *Argument) {
				ancestorFacts := b.Conjuncts(
					AncestorsClosed.At(deleted, X),
					"the restricted ancestors contain X",
					"the restricted ancestors are ancestral for the retained edges")
				retainedParents := b.Unfolded(ancestorFacts[1], AncestralDef)
				deletedTails := b.Have(
					"the tails of deleted edges are in the restricted ancestor set",
					"Z ⊆ «U»",
					By(tailsInX, ancestorFacts[0], set_order.SubsetTrans.At(Z, X, restrictedAncestors)))
				tailInU := b.Unfolded(deletedTails, set_basic.SubsetDef)
				ancestral := b.Have(
					"the restricted ancestors are ancestral for E",
					"dag_ancestral(E, «U»)",
					Unfold(AncestralDef),
					Derive(func(c *Argument) {
						u := c.FixAs[A]()
						v := c.FixAs[A]()
						edge := c.Assume()
						c.Show(
							"a deleted tail is in U and a retained parent of a point in U is in U",
							By(edge, tailInU.At(u), retainedParents.At(u, v), DeleteOutDef.At(E, Z, u, v)))
					}))
				b.Show(
					"the restricted ancestor set contains X and is ancestral for E",
					By(ancestorFacts[0], ancestral, AncestorsUpperBound.At(E, X, restrictedAncestors)))
			}))
		a.Show(
			"the two inclusions give equality",
			By(inOriginal, inRestricted, set_order.SubsetAntisym))
	}),
})}

// AncestorsDeleteIn preserves the ancestors of X when the heads of all
// deleted edges lie outside the original ancestor set of X.
var AncestorsDeleteIn = ancestorsDeleteInThm{family.Add(registry.ProofEntry{
	Name: "AncestorsDeleteIn",
	Key:  "prop_e91bd65e7c2a81b9",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X Z:set(A).",
		Hypotheses: []string{"dag_ancestors(E, X) ∩ Z = ∅"},
		Conclusion: "dag_ancestors(dag_delete_in(E, Z), X) = dag_ancestors(E, X)",
		Abbrev: Abbrev{
			{Name: "U", Text: "dag_ancestors(dag_delete_in(E, Z), X)"},
		},
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Z *Expr[Set[A]], avoidsZ Fact) {
		deleted := a.TermAs[Fun2[A, A, Bool]]("dag_delete_in(E, Z)")
		restrictedAncestors := a.TermAs[Set[A]]("«U»")
		inOriginal := a.Have(
			"every ancestor in the restricted graph is an ancestor in the original graph",
			"«U» ⊆ dag_ancestors(E, X)",
			Derive(func(b *Argument) {
				retained := b.Have(
					"every retained edge belongs to E",
					"∀u v:A. dag_delete_in(E, Z, u, v) ⇒ E(u, v)",
					By(DeleteInDef))
				b.Show(
					"every walk in the restricted graph is an original walk",
					By(retained, set_order.SubsetRefl.At(X), AncestorsMonotone.At(deleted, E, X, X)))
			}))
		inRestricted := a.Have(
			"every original ancestor belongs to the restricted ancestor set",
			"dag_ancestors(E, X) ⊆ «U»",
			Derive(func(b *Argument) {
				ancestorFacts := b.Conjuncts(
					AncestorsClosed.At(deleted, X),
					"the restricted ancestors contain X",
					"the restricted ancestors are ancestral for the retained edges")
				retainedParents := b.Unfolded(ancestorFacts[1], AncestralDef)
				retainedHeads := b.Have(
					"the restricted ancestor set also avoids Z",
					"∀v:A. v ∈ «U» ⇒ v ∉ Z",
					BySets(inOriginal, avoidsZ))
				ancestral := b.Have(
					"the restricted ancestors are ancestral for E",
					"dag_ancestral(E, «U»)",
					Unfold(AncestralDef),
					Derive(func(c *Argument) {
						u := c.FixAs[A]()
						v := c.FixAs[A]()
						edge := c.Assume()
						c.Show(
							"every edge into U survives deletion and its source belongs to U",
							By(edge, retainedHeads.At(v), retainedParents.At(u, v), DeleteInDef.At(E, Z, u, v)))
					}))
				b.Show(
					"the restricted ancestor set contains X and is ancestral for E",
					By(ancestorFacts[0], ancestral, AncestorsUpperBound.At(E, X, restrictedAncestors)))
			}))
		a.Show(
			"the two inclusions give equality",
			By(inOriginal, inRestricted, set_order.SubsetAntisym))
	}),
})}
