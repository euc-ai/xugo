package dag

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DagWellfounded proves well-foundedness of the edges and of reachability
// by nonempty walks in a finite acyclic graph.
var DagWellfounded = dagWellfoundedThm{family.Add(registry.ProofEntry{
	Name: "DagWellfounded",
	Reading: "The first edge of a nonempty walk puts " +
		"its source in V, which bounds every predecessor set.",
	Key: "prop_1cfce25511b74476",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀E:(A → A → bool).",
		Hypotheses: []string{"dag_on(V, E)"},
		Conclusion: "wellfounded(E) ∧ wellfounded(transitive_closure(E))",
	}, func(a *Argument, V *Expr[Set[A]], E *Arrow2[A, A, Bool], graph DagFact[on.V]) {
		reachability := a.TermAs[Fun2[A, A, Bool]]("transitive_closure(E)")
		dagFacts := a.Conjuncts(
			a.Unfolded(graph, DagOn),
			"V is finite",
			"every edge has both ends in V",
			"the transitive closure has no cycle")
		rules := a.Conjuncts(
			closure.TransitiveClosureRules.At(E),
			"every edge is a walk",
			"two walks with a common endpoint compose")
		predecessorsFinite := a.Have(
			"each vertex has finitely many predecessors in the transitive closure",
			"∀v:A. finite({u:A | transitive_closure(E, u, v)})",
			Derive(func(b *Argument) {
				v := b.FixAs[A]()
				inV := b.Have(
					"every predecessor of v is in V",
					"{u:A | transitive_closure(E, u, v)} ⊆ V",
					Unfold(set_basic.SubsetDef),
					Derive(func(c *Argument) {
						u := c.FixAs[A]("u")
						reaches := c.Assume()
						c.Show(
							"the first edge of the walk starts in V",
							By(Normalized, reaches, dagFacts[1], closure.CasesRight.At(E, u, v)))
					}))
				predecessors := b.TermAs[Set[A]]("{u:A | transitive_closure(E, u, v)}")
				b.Show(
					"a subset of the finite vertex set is finite",
					By(dagFacts[0], inV, finite_set.FiniteSubset.At(predecessors, V)))
			}))
		wellFounded := a.Have(
			"acyclic reachability is transitive with finite predecessor sets",
			"wellfounded(transitive_closure(E))",
			By(dagFacts[2], rules[1], predecessorsFinite, well_founded.FinitePredecessors.At(reachability)))
		a.Show(
			"the edges inherit well-foundedness from the walks",
			By(rules[0], wellFounded, well_founded.Subrelation.At(E, reachability)))
	}),
})}

// DagSinkExists finds a point of a nonempty set with no outgoing edge
// into that set.
var DagSinkExists = dagSinkExistsThm{family.Add(registry.ProofEntry{
	Name: "DagSinkExists",
	Key:  "prop_bc814dc60da32fbb",
	Build: family.Theorem(Statement{
		Binders:    "∀V U:set(A). ∀E:(A → A → bool).",
		Hypotheses: []string{"dag_on(V, E)", "U ≠ ∅"},
		Conclusion: "∃s:A. s ∈ U ∧ (∀t:A. t ∈ U ⇒ ¬E(s, t))",
		Abbrev: Abbrev{
			{Name: "R", Text: "λu:A. λv:A. transitive_closure(E, v, u)"},
		},
	}, func(
		a *Argument,
		V, U *Expr[Set[A]],
		E *Arrow2[A, A, Bool],
		graph DagFact[on.V],
		nonempty Fact,
	) {
		reversed := a.TermAs[Fun2[A, A, Bool]]("«R»")
		rules := closure.TransitiveClosureRules.At(E)
		wellFounded := a.Have(
			"reverse reachability is well-founded",
			"wellfounded(«R»)",
			Derive(func(b *Argument) {
				dagFacts := b.Conjuncts(
					b.Unfolded(graph, DagOn),
					"V is finite",
					"every edge has both ends in V",
					"the transitive closure has no cycle")
				composition := b.Have(
					"composing the two walks in reverse order makes reverse reachability transitive",
					"∀u v w:A. transitive_closure(E, v, u) ∧ transitive_closure(E, w, v) ⇒ transitive_closure(E, w, u)",
					By(rules))
				successorsFinite := b.Have(
					"each vertex has finitely many successors in the transitive closure",
					"∀v:A. finite({u:A | transitive_closure(E, v, u)})",
					Derive(func(c *Argument) {
						v := c.FixAs[A]()
						inV := c.Have(
							"every successor of v is in V",
							"{u:A | transitive_closure(E, v, u)} ⊆ V",
							Unfold(set_basic.SubsetDef),
							Derive(func(d *Argument) {
								u := d.FixAs[A]("u")
								reaches := d.Assume()
								d.Show(
									"the last edge of the walk ends in V",
									By(reaches, dagFacts[1], closure.CasesLeft.At(E, v, u)))
							}))
						successors := c.TermAs[Set[A]]("{u:A | transitive_closure(E, v, u)}")
						c.Show(
							"a subset of the finite vertex set is finite",
							By(dagFacts[0], inV, finite_set.FiniteSubset.At(successors, V)))
					}))
				b.Show(
					"the acyclic reverse closure is transitive with finite predecessor sets",
					By(dagFacts[2], composition, successorsFinite, well_founded.FinitePredecessors.At(reversed)))
			}))
		inhabited := a.Have(
			"U has a point",
			"∃u:A. u ∈ U",
			BySets(nonempty))
		minimalPoints := a.Unfolded(wellFounded, well_founded.WellfoundedDef)
		inU := a.TermAs[Set[A]]("λp:A. p ∈ U")
		s, minimal := a.ObtainAs[A](
			"choose a minimal point of U in the reverse closure",
			"∃s:A. s ∈ U ∧ (∀t:A. transitive_closure(E, s, t) ⇒ t ∉ U)",
			By(inhabited, minimalPoints.At(inU)))
		a.Take(s)
		a.Show(
			"an outgoing edge to U would contradict minimality",
			By(minimal, rules))
	}),
})}
