package d_separation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AddRootSeparationCertificate — a trap for moral walks lifts to the graph
// with a root none added above Z, the original vertices embedded by some:
// a set S in a parent-closed U that contains Y, misses Z, has no edge into
// U ∩ Z and keeps every moral step into U ∖ W shows that W separates Y
// from the root.
var AddRootSeparationCertificate = addRootSeparationCertificateThm{family.Add(registry.ProofEntry{
	Name: "AddRootSeparationCertificate",
	Key:  "prop_761d340ed47cd84e",
	Build: family.Sections(Statement{
		Binders: "∀E:(A → A → bool). ∀U S Y Z W:set(A).",
		Hypotheses: []string{
			"Y ∪ W ⊆ U",
			"dag_ancestral(E, U)",
			"Y ⊆ S",
			"S ∩ Z = ∅",
			"∀u v:A. u ∈ S ∧ v ∈ U ∩ Z ⇒ ¬E(u, v)",
			"∀u v:A. u ∈ S ∧ v ∈ U ∖ W ∧ dag_moral(E, U, u, v) ⇒ v ∈ S",
		},
		Conclusion: "d_separated(dag_add_root(E, Z), image(some, Y), {none}, image(some, W))",
		Abbrev: Abbrev{
			{Name: "AugmentedScope", Text: "{none} ∪ image(some, U)"},
			{Name: "Allowed", Text: "«AugmentedScope» ∖ image(some, W)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		embeddedArrow := ctx.Lemma(
			"∀E:(A → A → bool). ∀Z:set(A). ∀u v:A. dag_add_root(E, Z, some(u), some(v)) ⇔ E(u, v)",
			Chain(Simp(Fwd(dag.AddRootDef), Fwd(option.NoneNotSome), Fwd(option.SomeInjective)), BySets()))
		rootArrow := ctx.Lemma(
			"∀E:(A → A → bool). ∀Z:set(A). ∀v:A. dag_add_root(E, Z, none, some(v)) ⇔ v ∈ Z",
			Chain(Simp(Fwd(dag.AddRootDef), Fwd(option.NoneNotSome), Fwd(option.SomeInjective)), BySets()))
		noArrowIntoRoot := ctx.Lemma(
			"∀E:(A → A → bool). ∀Z:set(A). ∀p:option(A). ¬dag_add_root(E, Z, p, none)",
			Chain(Simp(Fwd(dag.AddRootDef), Fwd(option.NoneNotSome)), BySets()))
		embeddedMembership := ctx.Lemma(
			"∀U:set(A). ∀u:A. some(u) ∈ image(some, U) ⇔ u ∈ U",
			Chain(Simp(Fwd(set_basic.InImage), Fwd(option.SomeInjective)), BySets()))
		rootOutsideImage := ctx.Lemma(
			"∀U:set(A). none ∉ image(some, U)",
			Chain(Simp(Fwd(set_basic.InImage), Fwd(option.NoneNotSome)), BySets()))
		inAugmentedScope := ctx.Lemma(
			"∀U:set(A). ∀p:option(A). p ∈ {none} ∪ image(some, U) ⇔ p = none ∨ (∃u:A. p = some(u) ∧ u ∈ U)",
			BySets())

		childInScope := ctx.Lemma(Statement{
			Binders:    "∀E:(A → A → bool). ∀U Z:set(A). ∀u:A. ∀p:option(A).",
			Hypotheses: []string{"p ∈ «AugmentedScope»", "dag_add_root(E, Z, some(u), p)"},
			Conclusion: "∃w:A. p = some(w) ∧ w ∈ U ∧ E(u, w)",
		}, func(
			a *Argument,
			E *Arrow2[A, A, Bool],
			U, Z *Expr[Set[A]],
			u *Expr[A],
			p *Expr[option.Option[A]],
			inScope, edge Fact,
		) {
			source := a.TermAs[option.Option[A]]("some(u)")
			child := a.Have(
				"a child in the augmented scope is the root or an embedded vertex",
				"p = none ∨ (∃w:A. p = some(w) ∧ w ∈ U)",
				By(inScope, At(inAugmentedScope, U, p)))
			a.Do(child.SplitDisj(
				LeftHolds(
					"the root has no incoming edge",
					Given(func(b *Argument, atRoot Fact) {
						b.Show(
							"the edge cannot end at the root",
							By(edge, atRoot, At(noArrowIntoRoot, E, Z, source)))
					})),
				RightHolds(
					"the embedded child yields an original edge",
					Given(func(b *Argument, embedded Fact) {
						w, point := b.UnpackAs[A](embedded)
						b.Take(w)
						b.Show(
							"the original arrow has the child in U",
							By(Normalized, edge, point, At(embeddedArrow, E, Z, u, w)))
					}))))
		})

		embeddedMoral := ctx.Lemma(Statement{
			Binders:    "∀E:(A → A → bool). ∀U Z:set(A). ∀u v:A.",
			Hypotheses: []string{"dag_moral(dag_add_root(E, Z), «AugmentedScope», some(u), some(v))"},
			Conclusion: "dag_moral(E, U, u, v)",
		}, func(a *Argument, E *Arrow2[A, A, Bool], U, Z *Expr[Set[A]], u, v *Expr[A], adjacency Fact) {
			augmented := a.TermAs[Fun2[option.Option[A], option.Option[A], Bool]]("dag_add_root(E, Z)")
			scope := a.TermAs[Set[option.Option[A]]]("«AugmentedScope»")
			source := a.TermAs[option.Option[A]]("some(u)")
			target := a.TermAs[option.Option[A]]("some(v)")
			read := MoralDef.At(augmented, scope, source, target)
			old := MoralDef.At(E, U, u, v)
			distinct := a.Have(
				"the original endpoints are distinct",
				"u ≠ v",
				By(adjacency, read, option.SomeInjective.At(u, v)))
			options := a.Have(
				"an edge or a common child witnesses the moral adjacency",
				"(dag_add_root(E, Z, some(u), some(v)) ∨ dag_add_root(E, Z, some(v), some(u))) ∨ "+
					"(∃r:option(A). "+
					"    r ∈ «AugmentedScope» ∧ dag_add_root(E, Z, some(u), r) ∧ dag_add_root(E, Z, some(v), r))",
				By(adjacency, read))
			a.Do(options.SplitDisj(
				LeftHolds(
					"a directed edge between embedded vertices is an original edge",
					Given(func(b *Argument, direct Fact) {
						b.Show(
							"the original arrow witnesses moral adjacency",
							By(direct, distinct, At(embeddedArrow, E, Z, u, v), At(embeddedArrow, E, Z, v, u), old))
					})),
				RightHolds(
					"the common child is an embedded vertex",
					Given(func(b *Argument, common Fact) {
						r, child := b.UnpackAs[option.Option[A]](common)
						w, projected := b.ObtainAs[A](
							"project the common child to U",
							"∃w:A. r = some(w) ∧ w ∈ U ∧ E(u, w)",
							By(child, At(childInScope, E, U, Z, u, r)))
						oldChild := b.Have(
							"the original vertices share that child",
							"∃w:A. w ∈ U ∧ E(u, w) ∧ E(v, w)",
							Derive(func(c *Argument) {
								c.Take(w)
								c.Show(
									"project the other arrow to the same child",
									By(Normalized, child, projected, At(embeddedArrow, E, Z, v, w)))
							}))
						b.Show(
							"the original child witnesses moral adjacency",
							By(distinct, oldChild, old))
					}))))
		})

		rootMoral := ctx.Lemma(Statement{
			Binders:    "∀E:(A → A → bool). ∀U Z:set(A). ∀u:A.",
			Hypotheses: []string{"dag_moral(dag_add_root(E, Z), «AugmentedScope», some(u), none)"},
			Conclusion: "u ∈ Z ∨ (∃w:A. w ∈ U ∩ Z ∧ E(u, w))",
		}, func(a *Argument, E *Arrow2[A, A, Bool], U, Z *Expr[Set[A]], u *Expr[A], adjacency Fact) {
			augmented := a.TermAs[Fun2[option.Option[A], option.Option[A], Bool]]("dag_add_root(E, Z)")
			scope := a.TermAs[Set[option.Option[A]]]("«AugmentedScope»")
			source := a.TermAs[option.Option[A]]("some(u)")
			root := a.TermAs[option.Option[A]]("none")
			options := a.Have(
				"a direct edge or a shared child witnesses adjacency to the root",
				"(dag_add_root(E, Z, some(u), none) ∨ dag_add_root(E, Z, none, some(u))) ∨ "+
					"(∃r:option(A). "+
					"    r ∈ «AugmentedScope» ∧ dag_add_root(E, Z, some(u), r) ∧ dag_add_root(E, Z, none, r))",
				By(adjacency, MoralDef.At(augmented, scope, source, root)))
			a.Do(options.SplitDisj(
				LeftHolds(
					"a direct edge can only go from the root to a member of Z",
					Given(func(b *Argument, direct Fact) {
						b.Show(
							"the vertex belongs to Z",
							By(direct, At(noArrowIntoRoot, E, Z, source), At(rootArrow, E, Z, u)))
					})),
				RightHolds(
					"the shared child lies in U and Z",
					Given(func(b *Argument, common Fact) {
						r, child := b.UnpackAs[option.Option[A]](common)
						w, projected := b.ObtainAs[A](
							"project the shared child to U",
							"∃w:A. r = some(w) ∧ w ∈ U ∧ E(u, w)",
							By(child, At(childInScope, E, U, Z, u, r)))
						inZ := b.Have(
							"the arrow from the root puts the child in Z",
							"w ∈ Z",
							By(Normalized, child, projected, At(rootArrow, E, Z, w)))
						shared := b.Have(
							"the original arrow targets U ∩ Z",
							"∃w:A. w ∈ U ∩ Z ∧ E(u, w)",
							Derive(func(c *Argument) {
								c.Take(w)
								c.Show(
									"the child belongs to both sets",
									BySets(projected, inZ))
							}))
						b.Show(
							"the arrow to U ∩ Z witnesses the second alternative",
							By(shared))
					}))))
		})

		return ctx.Theorem(headline, func(
			a *Argument, E *Arrow2[A, A, Bool], U, S, Y, Z, W *Expr[Set[A]],
			groupsInU, ancestral, starts, avoidsZ, noArrowToZ, closed Fact,
		) {
			augmented := a.TermAs[Fun2[option.Option[A], option.Option[A], Bool]]("dag_add_root(E, Z)")
			scope := a.TermAs[Set[option.Option[A]]]("«AugmentedScope»")
			embeddedY := a.TermAs[Set[option.Option[A]]]("image(some, Y)")
			embeddedW := a.TermAs[Set[option.Option[A]]]("image(some, W)")
			embeddedS := a.TermAs[Set[option.Option[A]]]("image(some, S)")
			root := a.TermAs[Set[option.Option[A]]]("{none}")
			embedding := a.TermAs[Fun[A, option.Option[A]]]("some")
			containsSeeds := a.Have(
				"the augmented scope contains the endpoints and conditioning vertices",
				"image(some, Y) ∪ {none} ∪ image(some, W) ⊆ «AugmentedScope»",
				BySets(groupsInU))
			containsStarts := a.Have(
				"the embedded trap contains the embedded start set",
				"image(some, Y) ⊆ image(some, S)",
				BySets(starts))
			avoidsRoot := a.Have(
				"the embedded trap excludes the root",
				"image(some, S) ∩ {none} = ∅",
				BySets(At(rootOutsideImage, S)))
			parents := a.Unfolded(ancestral, dag.AncestralDef)
			augmentedAncestral := a.Have(
				"the augmented scope is ancestral in the augmented graph",
				"dag_ancestral(dag_add_root(E, Z), «AugmentedScope»)",
				Unfold(dag.AncestralDef),
				Derive(func(b *Argument) {
					p := b.FixAs[option.Option[A]]("p")
					q := b.FixAs[option.Option[A]]("q")
					edge := b.Assume()
					source := b.Have(
						"the parent is the root or an embedded vertex",
						"p = none ∨ (∃u:A. p = some(u))",
						By(Normalized, option.Cases))
					b.Do(source.SplitDisj(
						LeftHolds(
							"the new root belongs to the augmented scope",
							Given(func(c *Argument, atRoot Fact) {
								c.Show(
									"the root is included",
									By(atRoot, At(inAugmentedScope, U, p)))
							})),
						RightHolds(
							"an embedded parent projects to a parent in U",
							Given(func(c *Argument, embedded Fact) {
								u, parent := c.UnpackAs[A](embedded)
								w, child := c.ObtainAs[A](
									"project the child and the edge to U",
									"∃w:A. q = some(w) ∧ w ∈ U ∧ E(u, w)",
									By(edge, parent, At(childInScope, E, U, Z, u, q)))
								inU := c.Have(
									"U contains the parent of the child",
									"u ∈ U",
									By(child, parents.At(u, w)))
								c.Show(
									"the embedded parent belongs to the scope",
									By(parent, inU, At(inAugmentedScope, U, p)))
							}))))
				}))
			moralClosed := a.Have(
				"moral steps outside the conditioning image stay in the embedded trap",
				Statement{
					Binders: "∀p q:option(A).",
					Hypotheses: []string{
						"p ∈ image(some, S)",
						"q ∈ «Allowed»",
						"dag_moral(dag_add_root(E, Z), «AugmentedScope», p, q)",
					},
					Conclusion: "q ∈ image(some, S)",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[option.Option[A]]()
					q := b.FixAs[option.Option[A]]()
					step := b.Assume()
					u, source := b.ObtainAs[A](
						"the source embeds from S",
						"∃u:A. p = some(u) ∧ u ∈ S",
						By(step, set_basic.InImage.At(embedding, S, p)))
					target := b.Have(
						"the target is the root or an embedded vertex in U",
						"q = none ∨ (∃v:A. q = some(v) ∧ v ∈ U)",
						BySets(step, At(inAugmentedScope, U, q)))
					b.Do(target.SplitDisj(
						LeftHolds(
							"the trap cannot have the root as a moral neighbor",
							Given(func(c *Argument, atRoot Fact) {
								witness := c.Have(
									"adjacency to the root requires a target in Z",
									"u ∈ Z ∨ (∃w:A. w ∈ U ∩ Z ∧ E(u, w))",
									By(step, source, atRoot, At(rootMoral, E, U, Z, u)))
								c.Do(witness.SplitDisj(
									LeftHolds(
										"the source in S avoids Z",
										Given(func(d *Argument, inZ Fact) {
											d.Show(
												"membership in S and Z contradicts disjointness",
												BySets(source, inZ, avoidsZ))
										})),
									RightHolds(
										"the source has no arrow to U ∩ Z",
										Given(func(d *Argument, shared Fact) {
											w, child := d.UnpackAs[A](shared)
											d.Show(
												"the claimed arrow is forbidden",
												By(source, child, noArrowToZ.At(u, w)))
										}))))
							})),
						RightHolds(
							"an embedded neighbor stays in S by the original closure",
							Given(func(c *Argument, embedded Fact) {
								v, target := c.UnpackAs[A](embedded)
								allowed := c.Have(
									"the projected target is in U outside W",
									"v ∈ U ∖ W",
									BySets(step, target, At(embeddedMembership, W, v)))
								projected := c.Have(
									"the moral adjacency projects to U",
									"dag_moral(E, U, u, v)",
									By(Normalized, step, source, target, At(embeddedMoral, E, U, Z, u, v)))
								inS := c.Have(
									"the projected target therefore lies in S",
									"v ∈ S",
									By(source, allowed, projected, closed.At(u, v)))
								c.Show(
									"the target is in the embedded trap",
									By(Normalized, target, inS, At(embeddedMembership, S, v)))
							}))))
				}))
			a.Show(
				"the embedded trap certifies separation from the root",
				By(
					containsSeeds,
					augmentedAncestral,
					containsStarts,
					avoidsRoot,
					moralClosed,
					SeparationCertificate.At(augmented, embeddedY, root, embeddedW, scope, embeddedS)))
		})
	}),
})}

// RegimeSeparationExchange — Rule 2's condition as separation from the root:
// when W separates Y from Z once the edges out of Z are deleted, Z ∪ W
// separates Y from the root added above Z.
var RegimeSeparationExchange = regimeSeparationExchangeThm{family.Add(registry.ProofEntry{
	Name: "RegimeSeparationExchange",
	Key:  "prop_73c10260a8a32345",
	Build: family.Theorem(Statement{
		Binders: "∀E:(A → A → bool). ∀Y Z W:set(A).",
		Hypotheses: []string{
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"d_separated(dag_delete_out(E, Z), Y, Z, W)",
		},
		Conclusion: "d_separated(dag_add_root(E, Z), image(some, Y), {none}, image(some, Z ∪ W))",
		Abbrev: Abbrev{
			{Name: "U", Text: "dag_ancestors(dag_delete_out(E, Z), Y ∪ Z ∪ W)"},
		},
	}, func(
		a *Argument,
		E *Arrow2[A, A, Bool],
		Y, Z, W *Expr[Set[A]],
		avoidsYZ, avoidsYW, avoidsZW, separated Fact,
	) {
		reduced := a.TermAs[Fun2[A, A, Bool]]("dag_delete_out(E, Z)")
		scope := a.TermAs[Set[A]]("«U»")
		seeds := a.TermAs[Set[A]]("Y ∪ Z ∪ W")
		condition := a.TermAs[Set[A]]("Z ∪ W")

		targetsInSeeds := a.Have(
			"the seed set contains Z",
			"Z ⊆ Y ∪ Z ∪ W",
			BySets())
		sameAncestors := a.Have(
			"deleting the outgoing edges of Z preserves the ancestral scope",
			"«U» = dag_ancestors(E, Y ∪ Z ∪ W)",
			By(targetsInSeeds, dag.AncestorsDeleteOut.At(E, seeds, Z)))
		containsY := a.Have(
			"the reduced ancestral scope contains Y",
			"Y ⊆ «U»",
			BySets(dag.AncestorsClosed.At(reduced, seeds)))
		containsSeeds := a.Have(
			"the reduced ancestral scope contains Y and the conditioning set Z ∪ W",
			"Y ∪ (Z ∪ W) ⊆ «U»",
			BySets(dag.AncestorsClosed.At(reduced, seeds)))
		ancestral := a.Have(
			"the scope is the original ancestral set, so it is ancestral in the original graph",
			"dag_ancestral(E, «U»)",
			Simp(Fwd(sameAncestors)),
			By(dag.AncestorsClosed.At(E, seeds)))

		S, certificate := a.UnpackAs[Set[A]](
			GroupPremises(
				avoidsYZ,
				avoidsYW,
				containsY,
				set_order.SubsetRefl.At(scope),
				separated,
				SeparationGivesCertificate.At(reduced, Y, Z, W, scope)),
			"S")
		trap := a.Conjuncts(
			certificate,
			"S contains Y",
			"S lies in U outside W",
			"S misses Z",
			"a moral step of the reduced graph into U outside W stays in S")
		transfer := a.Have(
			"moral edges whose endpoints avoid Z survive deletion of the outgoing edges of Z",
			"∀u v:A. u ∉ Z ∧ v ∉ Z ∧ dag_moral(E, «U», u, v) ⇒ dag_moral(dag_delete_out(E, Z), «U», u, v)",
			Simp(Fwd(MoralDef), Fwd(dag.DeleteOutDef)),
			BySets())

		noArrowToZ := a.Have(
			"S has no arrow to a point of Z in the ancestral scope",
			"∀u v:A. u ∈ S ∧ v ∈ «U» ∩ Z ⇒ ¬E(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				endpoints := b.Assume()
				allowed := b.Have(
					"as Z misses W, the target lies in U ∖ W, which moral steps from S "+
						"may enter, and outside S; the source avoids Z and is not the target",
					"u ∉ Z ∧ u ≠ v ∧ v ∈ «U» ∖ W ∧ v ∉ S",
					BySets(endpoints, trap[2], avoidsZW))
				b.Show(
					"the arrow would survive in the reduced graph and its moral step would enter S at Z",
					By(
						endpoints,
						allowed,
						dag.DeleteOutDef.At(E, Z, u, v),
						MoralDef.At(reduced, scope, u, v),
						trap[3].At(u, v)))
			}))
		closed := a.Have(
			"a moral step to a vertex outside Z and W stays in S",
			"∀u v:A. u ∈ S ∧ v ∈ «U» ∖ (Z ∪ W) ∧ dag_moral(E, «U», u, v) ⇒ v ∈ S",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				allowed := b.Have(
					"both endpoints avoid Z and the target lies in U outside W",
					"u ∉ Z ∧ v ∉ Z ∧ v ∈ «U» ∖ W",
					BySets(edge, trap[2]))
				b.Show(
					"the moral edge survives in the reduced graph, whose moral steps stay in S",
					By(edge, allowed, transfer.At(u, v), trap[3].At(u, v)))
			}))
		a.Show(
			"S certifies separation from the regime root",
			By(
				containsSeeds,
				ancestral,
				trap[0],
				trap[2],
				noArrowToZ,
				closed,
				AddRootSeparationCertificate.At(E, scope, S, Y, Z, condition)))
	}),
})}

// RegimeSeparationDelete — Rule 3's condition as separation from the root:
// when W separates Y from Z once the edges into the points of Z that are
// no ancestors of W are deleted, W separates Y from the root added above
// Z. The certificate is taken inside the ancestors of Y ∪ W after the
// deletion, which miss the points whose incoming edges were deleted, so
// the two graphs agree on every edge into them; the walks of the
// separation run in the ancestral set of all three groups.
var RegimeSeparationDelete = regimeSeparationDeleteThm{family.Add(registry.ProofEntry{
	Name: "RegimeSeparationDelete",
	Key:  "prop_85f160fb393b5ec8",
	Build: family.Sections(Statement{
		Binders: "∀E:(A → A → bool). ∀Y Z W:set(A).",
		Hypotheses: []string{
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"d_separated(dag_delete_in(E, Z ∖ dag_ancestors(E, W)), Y, Z, W)",
		},
		Conclusion: "d_separated(dag_add_root(E, Z), image(some, Y), {none}, image(some, W))",
		Abbrev: Abbrev{
			{Name: "Targets", Text: "Z ∖ dag_ancestors(E, W)"},
			{Name: "AfterDelete", Text: "dag_delete_in(E, «Targets»)"},
			{Name: "Carrier", Text: "dag_ancestors(«AfterDelete», Y ∪ W)"},
			{Name: "AllAncestors", Text: "dag_ancestors(«AfterDelete», Y ∪ Z ∪ W)"},
		},
	}, buildRegimeSeparationDelete),
})}

func regimeDeleteAncestorsOfUnion(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀G:(A → A → bool). ∀Y W:set(A).",
		Conclusion: "dag_ancestors(G, Y ∪ W) ⊆ «AncestorsOfParts»",
		Abbrev: Abbrev{
			{Name: "AncestorsOfParts", Text: "dag_ancestors(G, Y) ∪ dag_ancestors(G, W)"},
		},
	}, func(a *Argument, G *Arrow2[A, A, Bool], Y, W *Expr[Set[A]]) {
		ancestorsY := a.Conjuncts(
			dag.AncestorsClosed.At(G, Y),
			"Y is in its ancestors",
			"the ancestors of Y are ancestral")
		ancestorsW := a.Conjuncts(
			dag.AncestorsClosed.At(G, W),
			"W is in its ancestors",
			"the ancestors of W are ancestral")
		parentsOfY := a.Unfolded(ancestorsY[1], dag.AncestralDef)
		parentsOfW := a.Unfolded(ancestorsW[1], dag.AncestralDef)
		contains := a.Have(
			"the union of the ancestral sets contains Y and W",
			"Y ∪ W ⊆ «AncestorsOfParts»",
			BySets(ancestorsY[0], ancestorsW[0]))
		ancestral := a.Have(
			"the union of two ancestral sets is ancestral",
			"dag_ancestral(G, «AncestorsOfParts»)",
			Unfold(dag.AncestralDef),
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				incoming := b.Assume()
				b.Show(
					"the part that contains v contains its parent",
					BySets(parentsOfY.At(u, v), parentsOfW.At(u, v), incoming))
			}))
		union := a.TermAs[Set[A]]("Y ∪ W")
		bound := a.TermAs[Set[A]]("«AncestorsOfParts»")
		a.Show(
			"bound the ancestors by the ancestral union",
			By(dag.AncestorsUpperBound.At(G, union, bound), contains, ancestral))
	})
}

func regimeDeleteAvoidTargets(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀U L B C Z:set(A).",
		Hypotheses: []string{"U ⊆ L ∪ B", "L ∩ Z ⊆ B", "B ⊆ C"},
		Conclusion: "U ∩ (Z ∖ C) = ∅",
	}, func(a *Argument, U, L, B, C, Z *Expr[Set[A]], bounds Fact) {
		a.Show(
			"every point of Z in U is already in C",
			BySets(bounds))
	})
}

func regimeDeleteCarrier(ctx *Script, unionBound, avoidTargets *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀E:(A → A → bool). ∀Y Z W:set(A).",
		Hypotheses: []string{"Y ∩ Z = ∅", "d_separated(«AfterDelete», Y, Z, W)"},
		Conclusion: "Y ∪ W ⊆ «Carrier» ∧ " +
			"(∀u v:A. E(u, v) ∧ v ∈ «Carrier» ⇒ «AfterDelete»(u, v) ∧ u ∈ «Carrier»)",
	}, func(a *Argument, E *Arrow2[A, A, Bool], Y, Z, W *Expr[Set[A]], apart, separated Fact) {
		deleted := a.TermAs[Fun2[A, A, Bool]]("«AfterDelete»")
		targets := a.TermAs[Set[A]]("«Targets»")
		carrier := a.TermAs[Set[A]]("«Carrier»")
		deletedWA := a.TermAs[Set[A]]("dag_ancestors(«AfterDelete», W)")
		deletedYA := a.TermAs[Set[A]]("dag_ancestors(«AfterDelete», Y)")
		originalWA := a.TermAs[Set[A]]("dag_ancestors(E, W)")
		deletionOnly := a.Have(
			"edge deletion only removes edges",
			"∀u v:A. «AfterDelete»(u, v) ⇒ E(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				b.Show(
					"a surviving edge was in E",
					By(edge, dag.DeleteInDef.At(E, targets, u, v)))
			}))
		insideOriginal := a.Have(
			"the remaining ancestors of W are original ancestors of W",
			"dag_ancestors(«AfterDelete», W) ⊆ dag_ancestors(E, W)",
			By(dag.AncestorsMonotone.At(deleted, E, W, W), deletionOnly, set_order.SubsetRefl.At(W)))
		apartZY := a.Have(
			"Z and Y are disjoint",
			"Z ∩ Y = ∅",
			BySets(apart))
		swapped := a.Have(
			"read separation from Z toward Y",
			"d_separated(«AfterDelete», Z, Y, W)",
			By(separated, DSeparatedSymmetric.At(deleted, Y, Z, W)))
		conditioned := a.Have(
			"an ancestor of Y in Z also reaches W",
			"dag_ancestors(«AfterDelete», Y) ∩ Z ⊆ dag_ancestors(«AfterDelete», W)",
			By(apartZY, swapped, DSeparatedAncestorsReachConditioningSet.At(deleted, Z, Y, W)))
		withinParts := a.Have(
			"the carrier lies in the ancestral sets of Y and W",
			"«Carrier» ⊆ dag_ancestors(«AfterDelete», Y) ∪ dag_ancestors(«AfterDelete», W)",
			By(At(unionBound, deleted, Y, W)))
		misses := a.Have(
			"the carrier misses the vertices whose incoming edges were removed",
			"«Carrier» ∩ «Targets» = ∅",
			By(
				At(avoidTargets, carrier, deletedYA, deletedWA, originalWA, Z),
				withinParts,
				conditioned,
				insideOriginal))
		union := a.TermAs[Set[A]]("Y ∪ W")
		ancestors := a.Conjuncts(
			dag.AncestorsClosed.At(deleted, union),
			"the carrier contains Y and W",
			"the carrier is ancestral for the retained edges")
		retainedParents := a.Unfolded(ancestors[1], dag.AncestralDef)
		intoCarrier := a.Have(
			"each original edge into the carrier survives and has its source there",
			"∀u v:A. E(u, v) ∧ v ∈ «Carrier» ⇒ «AfterDelete»(u, v) ∧ u ∈ «Carrier»",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				incoming := b.Assume()
				outside := b.Have(
					"the head is outside the deletion targets",
					"v ∉ «Targets»",
					BySets(incoming, misses))
				b.Show(
					"retain the edge and use parent closure",
					By(incoming, outside, dag.DeleteInDef.At(E, targets, u, v), retainedParents.At(u, v)))
			}))
		a.Show(
			"use the retained ancestral set as the carrier",
			By(ancestors[0], intoCarrier))
	})
}

func regimeDeleteRetainsMoralAdjacency(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀E F:(A → A → bool). ∀U:set(A). ∀u v:A.",
		Hypotheses: []string{
			"∀a b:A. E(a, b) ∧ b ∈ U ⇒ F(a, b)",
			"u ∈ U", "v ∈ U", "dag_moral(E, U, u, v)",
		},
		Conclusion: "dag_moral(F, U, u, v)",
	}, func(a *Argument, E, F *Arrow2[A, A, Bool], U *Expr[Set[A]], u, v *Expr[A],
		survives, source, target, adjacent Fact) {
		direct := a.Have(
			"each direct edge between the endpoints survives",
			"E(u, v) ∨ E(v, u) ⇒ F(u, v) ∨ F(v, u)",
			By(survives.At(u, v), survives.At(v, u), source, target))
		child := a.Have(
			"every common child in U remains a common child",
			"∀w:A. w ∈ U ∧ E(u, w) ∧ E(v, w) ⇒ F(u, w) ∧ F(v, w)",
			Derive(func(b *Argument) {
				w := b.FixAs[A]()
				witness := b.Assume()
				b.Show(
					"retain both incoming edges to the child",
					By(survives.At(u, w), survives.At(v, w), witness))
			}))
		a.Show(
			"read moral adjacency in the graph after deletion",
			By(adjacent, direct, child, MoralDef.At(E, U, u, v), MoralDef.At(F, U, u, v)))
	})
}

func regimeDeleteUnreachableHead(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀S U Z W:set(A). ∀u v:A.",
		Hypotheses: []string{"S ∩ Z = ∅", "Z ∩ W = ∅", "u ∈ S", "v ∈ U ∩ Z"},
		Conclusion: "v ∈ U ∖ W ∧ u ≠ v ∧ v ∉ S",
	}, func(a *Argument, S, U, Z, W *Expr[Set[A]], u, v *Expr[A], guards Fact) {
		a.Show(
			"the proposed edge would reach a distinct vertex outside S and W",
			BySets(guards))
	})
}

func buildRegimeSeparationDelete(ctx *Script, headline string) *GoalStackNode {
	unionBound := regimeDeleteAncestorsOfUnion(ctx)
	avoidTargets := regimeDeleteAvoidTargets(ctx)
	carrierKeepsEdges := regimeDeleteCarrier(ctx, unionBound, avoidTargets)
	retainsMoral := regimeDeleteRetainsMoralAdjacency(ctx)
	headOutside := regimeDeleteUnreachableHead(ctx)

	return ctx.Theorem(headline, func(
		a *Argument,
		E *Arrow2[A, A, Bool],
		Y, Z, W *Expr[Set[A]],
		apartYZ, apartYW, apartZW, separated Fact,
	) {
		deleted := a.TermAs[Fun2[A, A, Bool]]("«AfterDelete»")
		U := a.TermAs[Set[A]]("«Carrier»")
		carrierFacts := a.Conjuncts(
			a.Have(
				"the carrier contains Y and W and keeps every original edge into it",
				"Y ∪ W ⊆ «Carrier» ∧ (∀u v:A. E(u, v) ∧ v ∈ «Carrier» ⇒ «AfterDelete»(u, v) ∧ u ∈ «Carrier»)",
				By(At(carrierKeepsEdges, E, Y, Z, W), apartYZ, separated)),
			"the carrier contains the union of Y and W",
			"every original incoming edge survives with its source in the carrier")
		contains := a.Have(
			"the carrier contains Y",
			"Y ⊆ «Carrier»",
			BySets(carrierFacts[0]))
		seeds := a.TermAs[Set[A]]("Y ∪ W")
		allSeeds := a.TermAs[Set[A]]("Y ∪ Z ∪ W")
		seedsSubset := a.Have(
			"adding Z enlarges the ancestor seed set",
			"Y ∪ W ⊆ Y ∪ Z ∪ W",
			BySets())
		inFull := a.Have(
			"the carrier lies in the ancestral set of the three groups",
			"«Carrier» ⊆ «AllAncestors»",
			By(dag.AncestorsMonotone.At(deleted, deleted, seeds, allSeeds), seedsSubset))
		S, certificate := a.UnpackAs[Set[A]](
			GroupPremises(
				apartYZ, apartYW, contains, inFull, separated, SeparationGivesCertificate.At(deleted, Y, Z, W, U)),
			"S")
		trap := a.Conjuncts(
			certificate,
			"S contains Y",
			"S lies in the carrier outside W",
			"S misses Z",
			"a retained moral step into the carrier outside W stays in S")
		ancestral := a.Have(
			"the carrier is ancestral in the original graph",
			"dag_ancestral(E, «Carrier»)",
			Unfold(dag.AncestralDef),
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				incoming := b.Assume()
				b.Show(
					"the source belongs to the carrier",
					By(carrierFacts[1].At(u, v), incoming))
			}))
		survives := a.Have(
			"all original incoming edges to the carrier survive deletion",
			"∀u v:A. E(u, v) ∧ v ∈ «Carrier» ⇒ «AfterDelete»(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				incoming := b.Assume()
				b.Show(
					"the same edge occurs after deletion",
					By(carrierFacts[1].At(u, v), incoming))
			}))
		closed := a.Have(
			"original moral edges outside W also stay in S",
			"∀u v:A. u ∈ S ∧ v ∈ «Carrier» ∖ W ∧ dag_moral(E, «Carrier», u, v) ⇒ v ∈ S",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				endpoints := b.Have(
					"the edge has both endpoints in the carrier",
					"u ∈ «Carrier» ∧ v ∈ «Carrier»",
					BySets(edge, trap[1]))
				moved := b.Have(
					"the moral edge survives deletion",
					"dag_moral(«AfterDelete», «Carrier», u, v)",
					By(At(retainsMoral, E, deleted, U, u, v), survives, endpoints, edge))
				b.Show(
					"a retained moral step stays in S",
					By(trap[3].At(u, v), edge, moved))
			}))
		noEdge := a.Have(
			"no original edge from S enters Z within the carrier",
			"∀u v:A. u ∈ S ∧ v ∈ «Carrier» ∩ Z ⇒ ¬E(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				endpoints := b.Assume()
				head := b.Have(
					"the head is distinct, in the carrier outside W, and outside S",
					"v ∈ «Carrier» ∖ W ∧ u ≠ v ∧ v ∉ S",
					By(At(headOutside, S, U, Z, W, u, v), endpoints, trap[2], apartZW))
				b.Show(
					"a surviving edge would give a moral step into S at the head",
					BySets(survives.At(u, v), trap[3].At(u, v), endpoints, head, MoralDef.At(deleted, U, u, v)))
			}))
		a.Show(
			"lift the separation certificate to the added root",
			By(
				AddRootSeparationCertificate.At(E, U, S, Y, Z, W),
				carrierFacts[0],
				ancestral,
				trap[0],
				trap[2],
				noEdge,
				closed))
	})
}
