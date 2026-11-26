// base.go — bases, and the topology a family of sets generates. A base of
// a topology is a family of open sets among which every point of an open
// set finds one inside that open set; the open sets are then exactly the
// unions of members of the base. Any family of sets generates a topology,
// the smallest containing it, whose open sets are the unions of the
// finite intersections of its members; a family in which two members
// meeting at a point hold a third around the point inside both is a base
// of the topology it generates.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Bases
// ---------------------------------------------------------------------------

// BaseOpenIff — the open sets are exactly the unions of members of a
// base: an open set u is the union of the members of the base inside
// it, each point of u lying in one of them, and a union of members of
// the base is a union of open sets.
var BaseOpenIff = baseOpenIffThm{family.Add(registry.ProofEntry{
	Name: "BaseOpenIff",
	Key:  "prop_28f63229785dac44",
	Build: IsTopology.Law(Statement{
		Binders: "∀b:set(set(A)). ∀u:set(A).",
		Hypotheses: []string{
			"topology_base(b)",
		},
		Conclusion: "u ∈ T ⇔ ∃c:set(set(A)). c ⊆ b ∧ u = ⋃c",
	},
		func(a *Argument, topology IsTopologyFact[on.T], b *Expr[Set[Set[A]]], u *Expr[Set[A]], base Fact) {
			parts := a.Conjuncts(
				a.Unfolded(base, TopologyBaseDef),
				"the members of b are open",
				"each point of an open set lies in a member of b inside it")
			membersOpen, around := parts[0], parts[1]
			a.Iff()

			a.Forward(
				"an open set is the union of the members of b inside it",
				func(c *Argument, uOpen Fact) {
					c.Take(c.TermAs[Set[Set[A]]]("{v:set(A) | v ∈ b ∧ v ⊆ u}"))
					c.Show(
						"those members lie in b, and each point of u lies in one of them",
						BySets(around.At(u), uOpen))
				})

			a.Backward(
				"a union of members of b is a union of open sets",
				func(c *Argument, union Fact) {
					_, subfamily := c.Unpack(union)
					cParts := c.Conjuncts(
						subfamily,
						"c lies in b",
						"u is the union of c")
					c.Show(
						"c lies in b, whose members are open, so its union is open",
						cParts[1].Rw(),
						By(topology, membersOpen, cParts[0], UnionsOpen, set_order.SubsetTrans))
				})
		}),
})}

// SubtopologyBase — the traces of a base on a subset form a base of the
// subspace. The trace of a member of the base is the trace of an open
// set; a point x of a subspace-open set t = u ∩ s lies in a member v of
// the base inside u, and the trace v ∩ s holds x inside t.
var SubtopologyBase = subtopologyBaseThm{family.Add(registry.ProofEntry{
	Name: "SubtopologyBase",
	Key:  "prop_5c2e4fb4e7e83076",
	Build: family.Theorem(Statement{
		Binders: "∀T b:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"topology_base(T, b)",
		},
		Conclusion: "topology_base(subtopology(T, s), image(λv:set(A). v ∩ s, b))",
	},
		func(a *Argument, T, b *Expr[Set[Set[A]]], s *Expr[Set[A]], base Fact) {
			parts := a.Conjuncts(
				a.Unfolded(base, TopologyBaseDef),
				"the members of b are open",
				"each point of an open set lies in a member of b inside it")
			membersOpen, around := parts[0], parts[1]
			a.Show(
				"the traces of b are open in the subspace, and a "+
					"point of a subspace-open set lies in one inside it",
				Unfold(TopologyBaseDef),
				SplitConj(
					Case(
						"the traces of members of b are among the traces of open sets",
						Unfold(SubtopologyDef),
						By(membersOpen, set_image.ImageSubset)),
					Case(
						"a point of a subspace-open set lies in the trace of a member of b inside it",
						Derive(func(c *Argument) {
							c.Fix("t")
							x := c.FixAs[A]("x")
							given := c.Conjuncts(
								c.Assume(),
								"t is open in the subspace",
								"x lies in t")
							u, trace := c.ObtainAs[Set[A]](
								"t is the trace of an open set u",
								"∃u:set(A). t = u ∩ s ∧ u ∈ T",
								By(given[0], OpenInSubtopology))
							traceParts := c.Conjuncts(
								trace,
								"t is u ∩ s",
								"u is open")
							_, member := c.Obtain(
								"x lies in u, so in a member v of b inside u",
								"∃v:set(A). v ∈ b ∧ x ∈ v ∧ v ⊆ u",
								BySets(around.At(u, x), traceParts[0], given[1], traceParts[1]))
							c.Take(c.TermAs[Set[A]]("v ∩ s"))
							c.Show(
								"v ∩ s is the trace of a member of b, holds x and lies inside u ∩ s, which is t",
								BySets(member, traceParts[0], given[1]))
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The topology a family generates
// ---------------------------------------------------------------------------

// GeneratedTopology — the family a set of sets generates is a topology.
var GeneratedTopology = generatedTopologyThm{family.Add(registry.ProofEntry{
	Name: "GeneratedTopology",
	Key:  "prop_d065a4c84656d3b8",
	Build: family.Theorem("∀b:set(set(A)). is_topology(topology_generated(b))",
		func(a *Argument, b *Expr[Set[Set[A]]]) {
			a.Show(
				"the topologies containing b meet in a topology",
				Unfold(TopologyGeneratedDef),
				By(IntersTopologies))
		}),
})}

// GeneratedContains — the generating family lies in the topology it
// generates.
var GeneratedContains = generatedContainsThm{family.Add(registry.ProofEntry{
	Name: "GeneratedContains",
	Key:  "prop_a83ee716eaf6072c",
	Build: family.Theorem("∀b:set(set(A)). b ⊆ topology_generated(b)",
		func(a *Argument, b *Expr[Set[Set[A]]]) {
			a.Show(
				"a member of b lies in every topology containing b",
				Unfold(TopologyGeneratedDef),
				BySets())
		}),
})}

// GeneratedMinimal — the generated topology lies in every topology
// containing the family.
var GeneratedMinimal = generatedMinimalThm{family.Add(registry.ProofEntry{
	Name: "GeneratedMinimal",
	Key:  "prop_e3b7a7b750be7cde",
	Build: IsTopology.Law(Statement{
		Binders: "∀b:set(set(A)).",
		Hypotheses: []string{
			"b ⊆ T",
		},
		Conclusion: "topology_generated(b) ⊆ T",
	},
		func(a *Argument, topology IsTopologyFact[on.T], b *Expr[Set[Set[A]]], contains Fact) {
			a.Show(
				"T is one of the topologies containing b, so their intersection lies in T",
				Unfold(TopologyGeneratedDef),
				BySets(topology, contains))
		}),
})}

// GeneratedSpace — the points of the generated topology are the points
// of the family.
var GeneratedSpace = generatedSpaceThm{family.Add(registry.ProofEntry{
	Name: "GeneratedSpace",
	Key:  "prop_6ef99be705922fed",
	Build: family.Theorem("∀b:set(set(A)). ⋃topology_generated(b) = ⋃b",
		func(a *Argument, b *Expr[Set[Set[A]]]) {
			points := a.TermAs[Set[A]]("⋃b")
			among := a.Have(
				"each member of b is a subset of ⋃b",
				"b ⊆ {t:set(A) | t ⊆ ⋃b}",
				BySets())
			within := a.Have(
				"the subsets of ⋃b form a topology containing b, so the generated topology lies among them",
				"topology_generated(b) ⊆ {t:set(A) | t ⊆ ⋃b}",
				By(GeneratedMinimal, Discrete.At(points), among))
			a.Show(
				"b lies in the generated topology and every generated open set lies in ⋃b, so the unions agree",
				BySets(GeneratedContains.At(b), within))
		}),
})}

// LocalMeetsTopology — a family in which two members meeting at a point
// hold a third around the point inside both defines a topology: the sets
// each of whose points lies in a member of the family inside the set.
// Around a point of the meet of two such sets lie a member inside the
// one and a member inside the other, and a third member around the point
// inside both lies inside the meet; a point of a union of such sets lies
// in one of them, and the member around it inside that set lies inside
// the union.
var LocalMeetsTopology = localMeetsTopologyThm{family.Add(registry.ProofEntry{
	Name: "LocalMeetsTopology",
	Key:  "prop_3ed6ef7d50fb1de4",
	Build: family.Theorem(Statement{
		Binders: "∀b:set(set(A)).",
		Hypotheses: []string{
			"∀u v:set(A). ∀x:A. u ∈ b ∧ v ∈ b ∧ x ∈ u ∧ x ∈ v ⇒ ∃w:set(A). w ∈ b ∧ x ∈ w ∧ w ⊆ u ∩ v",
		},
		Conclusion: "is_topology({u:set(A) | ∀x:A. x ∈ u ⇒ ∃w:set(A). w ∈ b ∧ x ∈ w ∧ w ⊆ u})",
	},
		func(a *Argument, b *Expr[Set[Set[A]]], meets Fact) {
			a.Show(
				"the sets each of whose points lies in a member of b inside them are closed under meets and unions",
				Simp(Fwd(IsTopology)),
				SplitConj(
					Case(
						"two such sets meet in one",
						Derive(func(c *Argument) {
							c.Fix("u")
							c.Fix("v")
							given := c.Conjuncts(
								c.Assume(),
								"each point of u lies in a member of b inside u",
								"each point of v lies in a member of b inside v")
							pointwise := c.Have(
								"each point of u ∩ v lies in a member of b inside u ∩ v",
								"∀x:A. x ∈ u ∩ v ⇒ ∃w:set(A). w ∈ b ∧ x ∈ w ∧ w ⊆ u ∩ v",
								Derive(func(d *Argument) {
									x := d.FixAs[A]("x")
									xIn := d.Assume()
									w1, insideU := d.ObtainAs[Set[A]](
										"x lies in u, so in a member w₁ of b inside u",
										"∃w₁:set(A). w₁ ∈ b ∧ x ∈ w₁ ∧ w₁ ⊆ u",
										BySets(xIn, given[0]))
									w2, insideV := d.ObtainAs[Set[A]](
										"x lies in v, so in a member w₂ of b inside v",
										"∃w₂:set(A). w₂ ∈ b ∧ x ∈ w₂ ∧ w₂ ⊆ v",
										BySets(xIn, given[1]))
									d.Show(
										"a member of b around x inside w₁ ∩ w₂ lies inside u ∩ v",
										BySets(meets.At(w1, w2, x), insideU, insideV))
								}))
							c.Show(
								"so u ∩ v is one of the sets",
								By(pointwise))
						})),
					Case(
						"a union of such sets is one: the member around a "+
							"point inside one of the sets lies inside the union",
						BySets()),
				))
		}),
})}

// GeneratedOpenIff — the open sets of the topology a family generates
// are the unions of intersections of finite non-empty subfamilies.
// Those intersections m meet two at a time in a third, the intersection
// of the union of the two subfamilies, so the sets each of whose points
// lies in a member of m inside the set form a topology g
// (LocalMeetsTopology). It contains the family, a member v being the
// intersection of {v}, and so the generated topology: an open set u is
// the union of the members of m inside it. Conversely each member of m
// is open in the generated topology (IntersOpen), and so is a union of
// them (UnionsOpen).
var GeneratedOpenIff = generatedOpenIffThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOpenIff",
	Key:  "prop_af2d73af16d0ba6c",
	Build: family.Theorem("∀b:set(set(A)). ∀u:set(A). "+
		"    u ∈ topology_generated(b) ⇔ "+
		"    ∃c:set(set(A)). "+
		"        u = ⋃c ∧ ∀w:set(A). w ∈ c ⇒ ∃f:set(set(A)). finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∧ w = ⋂f",
		func(a *Argument, b *Expr[Set[Set[A]]], u *Expr[Set[A]]) {
			_, meetsDef := a.LetAs[Set[Set[A]]](
				"m",
				"{w:set(A) | ∃f:set(set(A)). finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∧ w = ⋂f}")
			inMeets := a.Have(
				"m holds the intersections of the finite non-empty subfamilies of b",
				"∀w:set(A). w ∈ m ⇔ ∃f:set(set(A)). finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∧ w = ⋂f",
				BySets(meetsDef))
			localMeets := a.Have(
				"two members of m meet in a member of m, the intersection of the union of their subfamilies",
				"∀v₁ v₂:set(A). ∀x:A. v₁ ∈ m ∧ v₂ ∈ m ∧ x ∈ v₁ ∧ x ∈ v₂ ⇒ ∃w:set(A). w ∈ m ∧ x ∈ w ∧ w ⊆ v₁ ∩ v₂",
				Derive(func(c *Argument) {
					v1, v2 := c.FixAs[Set[A]]("v₁"), c.FixAs[Set[A]]("v₂")
					c.Fix("x")
					given := c.Conjuncts(
						c.Assume(),
						"v₁ lies in m",
						"v₂ lies in m",
						"x lies in v₁",
						"x lies in v₂")
					f1, family1 := c.ObtainAs[Set[Set[A]]](
						"v₁ is the intersection of a finite non-empty subfamily f₁ of b",
						"∃f₁:set(set(A)). finite(f₁) ∧ ¬(f₁ = ∅) ∧ f₁ ⊆ b ∧ v₁ = ⋂f₁",
						By(given[0], inMeets.At(v1)))
					f2, family2 := c.ObtainAs[Set[Set[A]]](
						"v₂ is the intersection of a finite non-empty subfamily f₂ of b",
						"∃f₂:set(set(A)). finite(f₂) ∧ ¬(f₂ = ∅) ∧ f₂ ⊆ b ∧ v₂ = ⋂f₂",
						By(given[1], inMeets.At(v2)))
					joined := c.Have(
						"v₁ ∩ v₂ is the intersection of f₁ ∪ f₂",
						"∃f:set(set(A)). finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∧ v₁ ∩ v₂ = ⋂f",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[Set[Set[A]]]("f₁ ∪ f₂"))
							d.Show(
								"f₁ ∪ f₂ is a finite non-empty subfamily of b whose intersection is v₁ ∩ v₂",
								SplitConj(
									Case(
										"f₁ ∪ f₂ is finite, non-empty and inside b",
										BySets(family1, family2, finite_set.FiniteUnion.At(f1, f2))),
									Case(
										"its intersection is the intersection of the two intersections",
										By(Normalized, family1, family2, set_algebra.IntersUnion.At(f1, f2))),
								))
						}))
					meet := c.TermAs[Set[A]]("v₁ ∩ v₂")
					c.Take(meet)
					c.Show(
						"v₁ ∩ v₂ lies in m, holds x and lies inside itself",
						BySets(joined, inMeets.At(meet), given[2], given[3]))
				}))
			_, gDef := a.LetAs[Set[Set[A]]](
				"g",
				"{v:set(A) | ∀x:A. x ∈ v ⇒ ∃w:set(A). w ∈ m ∧ x ∈ w ∧ w ⊆ v}")
			topology := a.Have(
				"g, the sets each of whose points lies in a member of m inside them, is a topology",
				"is_topology(g)",
				gDef.Rw(),
				By(localMeets, LocalMeetsTopology))
			generators := a.Have(
				"a member v of b lies in m, the intersection of {v}",
				"∀v:set(A). v ∈ b ⇒ v ∈ m",
				Derive(func(c *Argument) {
					v := c.FixAs[Set[A]]("v")
					vIn := c.Assume()
					c.Do(inMeets.At(v).Rw())
					c.Take(c.TermAs[Set[Set[A]]]("{v}"))
					c.Show(
						"{v} is finite, non-empty and inside b, and its intersection is v",
						By(
							Normalized,
							vIn,
							finite_set.FiniteSing.At(v),
							set_algebra.IntersSing.At(v),
							set_order.SingSubset.At(b, v),
							set_algebra.InsertNotEmpty.At(c.TermAs[Set[Set[A]]]("∅"), v)))
				}))
			contains := a.Have(
				"g contains b: a member of b lies in m around each of its points, inside itself",
				"b ⊆ g",
				BySets(gDef, generators))
			within := a.Have(
				"so the generated topology lies in g",
				"topology_generated(b) ⊆ g",
				By(topology, contains, GeneratedMinimal))
			a.Iff()

			a.Forward(
				"an open set of the generated topology is the union of the members of m inside it",
				func(c *Argument, uOpen Fact) {
					pointwise := c.Have(
						"u lies in g: each point of u lies in a member of m inside u",
						"∀x:A. x ∈ u ⇒ ∃w:set(A). w ∈ m ∧ x ∈ w ∧ w ⊆ u",
						BySets(uOpen, within, gDef))
					c.Take(c.TermAs[Set[Set[A]]]("{w:set(A) | w ∈ m ∧ w ⊆ u}"))
					c.Show(
						"u is the union of the members of m inside it, and each member of m is an intersection",
						SplitConj(
							Case(
								"u is the union of the members of m inside it",
								BySets(pointwise)),
							Case(
								"a member of m is the intersection of a finite non-empty subfamily of b",
								BySets(inMeets)),
						))
				})

			a.Backward(
				"a union of intersections of finite non-empty subfamilies of b is open in the generated topology",
				func(c *Argument, union Fact) {
					_, subfamily := c.Unpack(union)
					parts := c.Conjuncts(
						subfamily,
						"u is the union of c",
						"each member of c is the intersection of a finite non-empty subfamily of b")
					open := c.Have(
						"each member of c is open in the generated topology",
						"∀w:set(A). w ∈ c ⇒ w ∈ topology_generated(b)",
						Derive(func(d *Argument) {
							w := d.FixAs[Set[A]]("w")
							wIn := d.Assume()
							_, meetOf := d.Unpack(GroupPremises(wIn, parts[1].At(w)), "f")
							fParts := d.Conjuncts(
								meetOf,
								"f is finite",
								"f is non-empty",
								"f lies in b",
								"w is the intersection of f")
							d.Show(
								"the generated topology contains b, so it holds the intersection of f",
								fParts[3].Rw(),
								By(
									fParts[0],
									fParts[1],
									fParts[2],
									IntersOpen,
									GeneratedTopology.At(b),
									GeneratedContains.At(b),
									set_order.SubsetTrans))
						}))
					c.Show(
						"so u, the union of the members of c, is open there",
						parts[0].Rw(),
						By(open, UnionsOpen, GeneratedTopology.At(b), set_basic.SubsetDef))
				})
		}),
})}

// BaseOfGenerated — a family in which two members meeting at a point
// hold a third around it inside both is a base of the topology it
// generates. The sets each of whose points lies in a member of the
// family inside the set form a topology g (LocalMeetsTopology), which
// contains the family and so the generated topology: each point of a
// generated open set lies in a member of the family inside it. The
// family lies in the topology it generates (GeneratedContains).
var BaseOfGenerated = baseOfGeneratedThm{family.Add(registry.ProofEntry{
	Name: "BaseOfGenerated",
	Key:  "prop_32eb68f177a26ba0",
	Build: family.Theorem(Statement{
		Binders: "∀b:set(set(A)).",
		Hypotheses: []string{
			"∀u v:set(A). ∀x:A. u ∈ b ∧ v ∈ b ∧ x ∈ u ∧ x ∈ v ⇒ ∃w:set(A). w ∈ b ∧ x ∈ w ∧ w ⊆ u ∩ v",
		},
		Conclusion: "topology_base(topology_generated(b), b)",
	},
		func(a *Argument, b *Expr[Set[Set[A]]], meets Fact) {
			_, gDef := a.LetAs[Set[Set[A]]](
				"g",
				"{v:set(A) | ∀x:A. x ∈ v ⇒ ∃w:set(A). w ∈ b ∧ x ∈ w ∧ w ⊆ v}")
			topology := a.Have(
				"g, the sets each of whose points lies in a member of b inside them, is a topology",
				"is_topology(g)",
				gDef.Rw(),
				By(meets, LocalMeetsTopology))
			contains := a.Have(
				"g contains b: a member of b lies around each of its points inside itself",
				"b ⊆ g",
				BySets(gDef))
			within := a.Have(
				"so the generated topology lies in g",
				"topology_generated(b) ⊆ g",
				By(topology, contains, GeneratedMinimal))
			a.Show(
				"b lies in the topology it generates, and is a base of it",
				Unfold(TopologyBaseDef),
				SplitConj(
					Case(
						"b lies in the topology it generates",
						Cite(GeneratedContains)),
					Case(
						"a generated open set lies in g: each of its points lies in a member of b inside it",
						BySets(gDef, within)),
				))
		}),
})}

// BaseGenerates — a topology is generated by any base of it. The
// generated topology lies in T, a topology containing the base; and an
// open set of T is a union of members of the base, which the generated
// topology holds, being a topology that contains the base.
var BaseGenerates = baseGeneratesThm{family.Add(registry.ProofEntry{
	Name: "BaseGenerates",
	Key:  "prop_c81b80eed83e6182",
	Build: IsTopology.Law(Statement{
		Binders: "∀b:set(set(A)).",
		Hypotheses: []string{
			"topology_base(b)",
		},
		Conclusion: "topology_generated(b) = T",
	},
		func(a *Argument, topology IsTopologyFact[on.T], b *Expr[Set[Set[A]]], base Fact) {
			within := a.Have(
				"T is a topology containing b, so it holds the topology b generates",
				"topology_generated(b) ⊆ T",
				By(GeneratedMinimal, topology, base, TopologyBaseDef))
			contains := a.Have(
				"an open set of T is a union of members of b, open in the topology b generates",
				"∀u:set(A). u ∈ T ⇒ u ∈ topology_generated(b)",
				Derive(func(c *Argument) {
					c.Fix("u")
					uOpen := c.Assume()
					_, union := c.Obtain(
						"u is the union of a subfamily c of b",
						"∃c:set(set(A)). c ⊆ b ∧ u = ⋃c",
						By(uOpen, base, BaseOpenIff.Read(topology)))
					parts := c.Conjuncts(
						union,
						"c lies in b",
						"u is the union of c")
					c.Show(
						"c lies in b, which lies in the generated topology, so its union is open there",
						parts[1].Rw(),
						By(parts[0], UnionsOpen, GeneratedTopology.At(b), GeneratedContains.At(b), set_order.SubsetTrans))
				}))
			a.Show(
				"each topology holds the other's open sets",
				By(within, contains, set_order.SubsetAntisym, set_basic.SubsetDef))
		}),
})}
