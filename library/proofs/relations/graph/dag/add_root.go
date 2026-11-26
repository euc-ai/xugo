package dag

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AddRootDag: adjoining a new root with an edge to each vertex of Z ⊆ V
// keeps a DAG on V and the root.
var AddRootDag = addRootDagThm{family.Add(registry.ProofEntry{
	Name: "AddRootDag",
	Reading: "Z ⊆ V puts the targets of the edges from " +
		"none inside the new vertex set; none has no parent.",
	Key: "prop_694cc879ebae73af",
	Build: family.Sections(Statement{
		Binders:    "∀V Z:set(A). ∀E:(A → A → bool).",
		Hypotheses: []string{"dag_on(V, E)", "Z ⊆ V"},
		Conclusion: "dag_on({none} ∪ image(some, V), dag_add_root(E, Z))",
		Abbrev: Abbrev{
			{Name: "U", Text: "{none} ∪ image(some, V)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		projectedWalk := ctx.Lemma(Statement{
			Binders:    "∀E:(A → A → bool). ∀Z:set(A). ∀p q:option(A).",
			Hypotheses: []string{"transitive_closure(dag_add_root(E, Z), p, q)"},
			Conclusion: "∃v:A. q = some(v) ∧ (∀u:A. p = some(u) ⇒ transitive_closure(E, u, v))",
		}, func(a *Argument, E *Arrow2[A, A, Bool], Z *Expr[Set[A]], p, q *Expr[Option[A]], walk Fact) {
			rules := closure.TransitiveClosureRules.At(E)
			a.Do(ByInduction(
				closure.TransitiveClosureInduct, walk,
				Case(
					"a single augmented edge ends at an original vertex",
					Derive(func(b *Argument) {
						b.FixAs[Option[A]]()
						b.FixAs[Option[A]]()
						edge := b.Unfolded(b.Assume(), AddRootDef)
						b.Do(edge.SplitDisj(
							LeftHolds(
								"an edge between original vertices projects to its original edge",
								Given(func(c *Argument, original Fact) {
									_, v, endpoints := c.Unpack2As[A, A](original)
									c.Take(v)
									c.Show(
										"the original edge is a walk and some is injective",
										By(endpoints, option.SomeInjective.Inst[A](), rules))
								})),
							RightHolds(
								"an edge from the new root still ends at an original vertex",
								Given(func(c *Argument, fromRoot Fact) {
									z, endpoints := c.UnpackAs[A](fromRoot)
									c.Take(z)
									c.Show(
										"the new root is distinct from every embedded vertex",
										By(endpoints, option.NoneNotSome.Inst[A]()))
								})),
						))
					})),
				Case(
					"two augmented stretches project through the original vertex at their join",
					Derive(func(b *Argument) {
						b.FixAs[Option[A]]()
						b.FixAs[Option[A]]()
						b.FixAs[Option[A]]()
						stretches := b.Conjuncts(
							b.Assume(),
							"the first stretch",
							"the second stretch")
						m, first := b.UnpackAs[A](stretches[0], "m")
						v, second := b.UnpackAs[A](stretches[1])
						firstParts := b.Conjuncts(
							first,
							"the join is some(m)",
							"the first projection")
						secondParts := b.Conjuncts(
							second,
							"the target is some(v)",
							"the second projection")
						afterJoin := b.Have(
							"the original join reaches the original target",
							"transitive_closure(E, m, v)",
							By(firstParts[0], secondParts[1].At(m)))
						b.Take(v)
						b.Show(
							"the same target witnesses the composition of the projected walks",
							By(secondParts[0], firstParts[1], afterJoin, rules))
					})),
			))
		})

		return ctx.Theorem(headline,
			func(a *Argument, V, Z *Expr[Set[A]], E *Arrow2[A, A, Bool], graph DagFact[on.V], targetsInV Fact) {
				dagFacts := a.Conjuncts(
					a.Unfolded(graph, DagOn),
					"V is finite",
					"every original edge has endpoints in V",
					"the original graph has no cycle")
				some := a.TermAs[Fun[A, Option[A]]]("some")
				none := a.TermAs[Option[A]]("none")
				root := a.TermAs[Set[Option[A]]]("{none}")
				image := a.TermAs[Set[Option[A]]]("image(some, V)")
				augmentedFinite := a.Have(
					"adding the root to the finite image leaves a finite vertex set",
					"finite(«U»)",
					Derive(func(b *Argument) {
						finiteImage := b.Have(
							"the embedded original vertices form a finite set",
							"finite(image(some, V))",
							By(dagFacts[0], finite_set.FiniteImage.At(some, V)))
						b.Show(
							"the union of the image and the singleton root is finite",
							By(finiteImage, finite_set.FiniteSing.At(none), finite_set.FiniteUnionImp.At(root, image)))
					}))
				endpoints := a.Have(
					"every augmented edge has both ends in the augmented vertex set",
					"∀p q:option(A). dag_add_root(E, Z, p, q) ⇒ p ∈ «U» ∧ q ∈ «U»",
					Derive(func(b *Argument) {
						lifted := b.Have(
							"each original vertex embeds into U",
							"∀a:A. a ∈ V ⇒ some(a) ∈ «U»",
							BySets())
						rootInU := b.Have(
							"U contains the new root",
							"none ∈ «U»",
							BySets())
						targets := b.Unfolded(targetsInV, set_basic.SubsetDef)
						b.FixAs[Option[A]]()
						b.FixAs[Option[A]]()
						edge := b.Unfolded(b.Assume(), AddRootDef)
						b.Do(edge.SplitDisj(
							LeftHolds(
								"an original edge embeds both vertices into U",
								Given(func(c *Argument, original Fact) {
									u, v, ends := c.Unpack2As[A, A](original)
									c.Show(
										"both ends belong to the image of V",
										By(Normalized, ends, dagFacts[1].At(u, v), lifted.At(u), lifted.At(v)))
								})),
							RightHolds(
								"an edge out of the new root targets an embedded point of Z",
								Given(func(c *Argument, fromRoot Fact) {
									z, ends := c.UnpackAs[A](fromRoot)
									c.Show(
										"the root belongs to U and the target embeds from Z ⊆ V",
										By(Normalized, ends, rootInU, targets.At(z), lifted.At(z)))
								})),
						))
					}))
				acyclic := a.Have(
					"the graph with the new root has no cycle",
					"∀p:option(A). ¬transitive_closure(dag_add_root(E, Z), p, p)",
					Derive(func(b *Argument) {
						p := b.FixAs[Option[A]]()
						b.Show(
							"a cycle would be based at some(v) and project to a cycle at v",
							By(dagFacts[2], At(projectedWalk, E, Z, p, p)))
					}))
				a.Show(
					"the augmented vertex set is finite and its edges define an acyclic graph",
					Unfold(DagOn),
					By(augmentedFinite, endpoints, acyclic))
			})
	}),
})}
