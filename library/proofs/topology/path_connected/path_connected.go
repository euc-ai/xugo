// path_connected.go — paths and path-connected sets: the values of a
// path form a connected set, so a path-connected set is connected; paths
// with a common end join into one, so two path-connected sets sharing a
// point unite to one; continuous maps carry path-connected sets to
// path-connected sets; and every interval of the line is path-connected,
// by the straight path.

package path_connected

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The unit interval
// ---------------------------------------------------------------------------

// UnitIntervalPoints — the points of the unit interval, read as a
// subspace of the line, are the reals between 0 and 1: the subspace's
// points are the line's, all the reals, cut to ⟦0, 1⟧.
var UnitIntervalPoints = unitIntervalPointsThm{family.Add(registry.ProofEntry{
	Name: "UnitIntervalPoints",
	Key:  "prop_813b32fa6a1adaa6",
	Build: family.Theorem("∀x:real. x ∈ ⋃subtopology(real_topology, ⟦&0, &1⟧) ⇔ &0 ≤ x ∧ x ≤ &1",
		func(a *Argument, x *Expr[Real]) {
			a.Show(
				"the subspace's points are the reals cut to ⟦0, 1⟧",
				Simp(Fwd(topological_space.SubtopologySpace), Fwd(real_topology.RealSpace)),
				BySets())
		}),
})}

// ---------------------------------------------------------------------------
// Path-connected sets are connected
// ---------------------------------------------------------------------------

// PathImageConnected — the values of a path on ⟦0, 1⟧ form a connected
// set: ⟦0, 1⟧ is an interval, so connected in the line and in its own
// subspace, and a continuous map carries a connected set to a connected
// set.
var PathImageConnected = pathImageConnectedThm{family.Add(registry.ProofEntry{
	Name: "PathImageConnected",
	Key:  "prop_af46fce1960cbb2f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "connected_in(T, image(g, ⟦&0, &1⟧))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], g *Arrow[Real, A], path Fact) {
			interval := a.Have(
				"⟦0, 1⟧ is an interval: a real between two of its points lies between 0 and 1",
				"real_interval(⟦&0, &1⟧)",
				Unfold(real_topology.RealIntervalDef),
				ByArith())
			connectedInSubspace := a.Have(
				"so ⟦0, 1⟧ is connected in the line, and so in its own subspace",
				"connected_in(subtopology(real_topology, ⟦&0, &1⟧), ⟦&0, &1⟧)",
				By(
					interval,
					real_topology.IntervalConnected,
					connected.ConnectedInSubtopology,
					set_order.SubsetRefl))
			a.Show(
				"the path, continuous on that subspace, carries it to a connected set",
				By(continuous.ImageConnected.Read(a.Unfolded(path, PathInDef)), connectedInSubspace))
		}),
})}

// PathConnectedConnected — a path-connected set is connected: the empty
// set is, and a set holding a point a is the union of the value sets of
// the paths in it from a, connected sets that all hold a.
var PathConnectedConnected = pathConnectedConnectedThm{family.Add(registry.ProofEntry{
	Name: "PathConnectedConnected",
	Key:  "prop_8f6c24bad452554a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"path_connected_in(T, s)",
		},
		Conclusion: "connected_in(T, s)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], pathConnected Fact) {
			nonempty := a.Unless(
				a.Term("s = ∅"),
				"an empty s is connected",
				Given(func(b *Argument, empty Fact) {
					b.Show(
						"s is the empty set, connected in any space",
						empty.Rw(),
						Cite(connected.EmptyConnected))
				}))
			parts := a.Conjuncts(
				a.Unfolded(pathConnected, PathConnectedInDef),
				"s lies in the space",
				"a path in s joins any two points of s")
			joins := parts[1]
			pt, aIn := a.ObtainAs[A](
				"s holds a point a",
				"∃a:A. a ∈ s",
				By(nonempty, set_basic.MemberNotEmpty))
			_, fDef := a.LetAs[Set[Set[A]]](
				"F",
				"{image(g, ⟦&0, &1⟧) | g:(real → A) | path_in(T, g) ∧ image(g, ⟦&0, &1⟧) ⊆ s ∧ g(&0) = a}")
			members := a.Have(
				"each set in F, the value set of a path in s from a, is connected, holds a and lies in s",
				"∀u:set(A). u ∈ F ⇒ connected_in(T, u) ∧ a ∈ u ∧ u ⊆ s",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("u")
					uIn := b.Assume()
					g, valueSet := b.UnpackAs[Fun[Real, A]](b.Simplified(uIn, Fwd(fDef)), "g")
					path := b.Conjuncts(
						valueSet,
						"g is a path",
						"its values lie in s",
						"it starts at a",
						"u is its value set")
					start := b.Have(
						"g starts at one of its values",
						"g(&0) ∈ image(g, ⟦&0, &1⟧)",
						By(set_image.FunInImage))
					b.Show(
						"so u is connected, holds a = g(0), and lies in s",
						path[3].Rw(),
						By(PathImageConnected.At(T, g), path[0], path[1], path[2], start))
				}))
			covers := a.Have(
				"a point y of s is the end of a path in s from a, so lies in that path's value set",
				"∀y:A. y ∈ s ⇒ y ∈ ⋃F",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					_, joined := b.UnpackAs[Fun[Real, A]](GroupPremises(aIn, yIn, joins.At(pt, y)), "g")
					path := b.Conjuncts(
						joined,
						"g is a path",
						"its values lie in s",
						"it starts at a",
						"it ends at y")
					end := b.Have(
						"g ends at one of its values",
						"g(&1) ∈ image(g, ⟦&0, &1⟧)",
						By(set_image.FunInImage))
					inF := b.Have(
						"the value set of g is in F",
						"image(g, ⟦&0, &1⟧) ∈ F",
						Simp(Fwd(fDef)),
						By(path[0], path[1], path[2]))
					b.Show(
						"so y = g(1) lies in the union of F",
						BySets(path[3], end, inF))
				}))
			spanned := a.Have(
				"so the sets in F make up s",
				"⋃F = s",
				BySets(covers, members))
			meet := a.Have(
				"and they share the point a",
				"¬(⋂F = ∅)",
				BySets(members))
			a.Show(
				"s, a union of connected sets with a point in common, is connected",
				spanned.RwRev(),
				By(meet, members, connected.ConnectedUnions))
		}),
})}

// ---------------------------------------------------------------------------
// Joining paths
// ---------------------------------------------------------------------------

// PathReparametrise — a path run after a continuous map of the line that
// sends a set s of reals into ⟦0, 1⟧ is continuous on s: the map is
// continuous from s into the unit interval, and the path is continuous on
// the unit interval.
var PathReparametrise = pathReparametriseThm{family.Add(registry.ProofEntry{
	Name: "PathReparametrise",
	Key:  "prop_559ee82344ba4bab",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A). ∀p:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"path_in(T, g)",
			"continuous_map(real_topology, real_topology, p)",
			"∀t:real. t ∈ s ⇒ &0 ≤ p(t) ∧ p(t) ≤ &1",
		},
		Conclusion: "continuous_map(subtopology(real_topology, s), T, λt:real. g(p(t)))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			g *Arrow[Real, A],
			p *Arrow[Real, Real],
			s *Expr[Set[Real]],
			path, pContinuous, bounded Fact,
		) {
			intoUnit := a.Have(
				"p carries the points of s, as a subspace of the line, into ⟦0, 1⟧",
				"∀x:real. x ∈ ⋃subtopology(real_topology, s) ⇒ p(x) ∈ ⟦&0, &1⟧",
				BySets(bounded, topological_space.SubtopologySpace))
			reparametrised := a.Have(
				"so p is continuous from s into the unit interval",
				"continuous_map(subtopology(real_topology, s), subtopology(real_topology, ⟦&0, &1⟧), p)",
				By(continuous.FromSubtopology.Read(pContinuous), intoUnit, continuous.IntoSubtopology))
			composite := a.Have(
				"and g after p is continuous from s into the space, by composition",
				"continuous_map(subtopology(real_topology, s), T, g ∘ p)",
				By(path, PathInDef, continuous.Compose.Read(reparametrised)))
			a.Show(
				"g after p is t ↦ g(p(t))",
				By(composite, functions.ComposeApply))
		}),
})}

// PathJoin — a path ending where a second begins joins it into one path,
// the first run at double speed on ⟦0, 1/2⟧, the second on ⟦1/2, 1⟧: each
// half is closed in the unit interval, on each the joined map is a path
// run after an affine map, and the pasting lemma glues the two, which
// agree at 1/2 because g(1) = h(0).
var PathJoin = pathJoinThm{family.Add(registry.ProofEntry{
	Name: "PathJoin",
	Key:  "prop_f32de16cccc0bd10",
	Reading: "No axiom of T: only the unit interval, the source, has to be a topology. For " +
		"t in ⟦0, 1⟧ the joined map reads g and h on ⟦0, 1⟧ only, and at t = 1/2 both halves " +
		"give g(1) = h(0), which is what makes the preimage of an open set relatively open there.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
			"path_in(T, h)",
			"g(&1) = h(&0)",
		},
		Conclusion: "path_in(T, λt:real. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1)))",
		Abbrev: Abbrev{
			{Name: "lower", Text: "⟦&0, &1 / &2⟧"},
			{Name: "upper", Text: "⟦&1 / &2, &1⟧"},
			{Name: "joined", Text: "λt:real. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], g, h *Arrow[Real, A], gPath, hPath, meet Fact) {
			lowerInside := a.Have(
				"⟦0, 1/2⟧ lies in ⟦0, 1⟧",
				"«lower» ⊆ ⟦&0, &1⟧",
				Simp(Fwd(set_basic.SubsetDef)),
				ByArith())
			upperInside := a.Have(
				"⟦1/2, 1⟧ lies in ⟦0, 1⟧",
				"«upper» ⊆ ⟦&0, &1⟧",
				Simp(Fwd(set_basic.SubsetDef)),
				ByArith())
			lowerClosed := a.Have(
				"so ⟦0, 1/2⟧, closed in the line, is closed in the unit interval",
				"closed_in(subtopology(real_topology, ⟦&0, &1⟧), «lower»)",
				By(
					lowerInside,
					topological_space.ClosedInClosedSubtopology.Read(real_topology.RealTopology),
					real_topology.ClosedIntervalClosed))
			upperClosed := a.Have(
				"and so is ⟦1/2, 1⟧",
				"closed_in(subtopology(real_topology, ⟦&0, &1⟧), «upper»)",
				By(
					upperInside,
					topological_space.ClosedInClosedSubtopology.Read(real_topology.RealTopology),
					real_topology.ClosedIntervalClosed))
			covered := a.Have(
				"the two halves cover the unit interval",
				"⋃subtopology(real_topology, ⟦&0, &1⟧) ⊆ «lower» ∪ «upper»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					xIn := b.Assume()
					b.Show(
						"a point of ⟦0, 1⟧ lies at or below 1/2, or at or above it",
						Simp(Fwd(set_basic.InUnion)),
						ByArith(xIn, UnitIntervalPoints.At(x)))
				}))

			doubling := a.Have(
				"t ↦ 2t is a polynomial, so continuous on the line",
				"continuous_map(real_topology, real_topology, λt:real. &2 * t)",
				By(
					real_continuous.PolynomialFunctionContinuous.At(a.TermAs[Fun[Real, Real]]("λt:real. &2 * t")),
					real_polynomial.ScalarLeft.At(a.TermAs[Fun[Real, Real]]("λt:real. t"), a.TermAs[Real]("&2")),
					real_polynomial.Id))
			doublingBounded := a.Have(
				"for x in ⟦0, 1/2⟧, 2x lies in ⟦0, 1⟧",
				"∀x:real. x ∈ ⟦&0, &1⟧ ∩ «lower» ⇒ &0 ≤ &2 * x ∧ &2 * x ≤ &1",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					xIn := b.Assume()
					b.Show(
						"x lies in both, so between 0 and 1/2",
						ByArith(b.Simplified(xIn, Fwd(set_basic.InInter))))
				}))
			gFast := a.Have(
				"g at twice the time is continuous on ⟦0, 1/2⟧",
				"continuous_map(subtopology(real_topology, ⟦&0, &1⟧ ∩ «lower»), T, λt:real. g(&2 * t))",
				By(PathReparametrise, gPath, doubling, doublingBounded))
			gAgrees := a.Have(
				"on ⟦0, 1/2⟧ the joined map is g at twice the time",
				"∀x:real. x ∈ ⋃subtopology(real_topology, ⟦&0, &1⟧ ∩ «lower») ⇒ g(&2 * x) = «joined»(x)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					xIn := b.Assume()
					b.Show(
						"x ≤ 1/2, so the joined map takes its first branch",
						By(
							b.Simplified(
								xIn,
								Fwd(topological_space.SubtopologySpace),
								Fwd(real_topology.RealSpace),
								Fwd(set_basic.InInter))))
				}))
			lowerHalf := a.Have(
				"so the joined map is continuous on ⟦0, 1/2⟧, a subspace of the unit interval",
				"continuous_map(subtopology(subtopology(real_topology, ⟦&0, &1⟧), «lower»), T, «joined»)",
				Simp(Fwd(topological_space.SubtopologySubtopology)),
				By(gAgrees, continuous.Eq.Read(gFast)))

			shifted := a.Have(
				"t ↦ 2t − 1 is a polynomial, so continuous on the line",
				"continuous_map(real_topology, real_topology, λt:real. &2 * t - &1)",
				By(
					real_continuous.PolynomialFunctionContinuous.At(a.TermAs[Fun[Real, Real]]("λt:real. &2 * t - &1")),
					real_polynomial.Sub.At(
						a.TermAs[Fun[Real, Real]]("λt:real. &2 * t"),
						a.TermAs[Fun[Real, Real]]("λt:real. &1")),
					real_polynomial.ScalarLeft.At(a.TermAs[Fun[Real, Real]]("λt:real. t"), a.TermAs[Real]("&2")),
					real_polynomial.Id,
					real_polynomial.Const))
			shiftedBounded := a.Have(
				"for x in ⟦1/2, 1⟧, 2x − 1 lies in ⟦0, 1⟧",
				"∀x:real. x ∈ ⟦&0, &1⟧ ∩ «upper» ⇒ &0 ≤ &2 * x - &1 ∧ &2 * x - &1 ≤ &1",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					xIn := b.Assume()
					b.Show(
						"x lies in both, so between 1/2 and 1",
						ByArith(b.Simplified(xIn, Fwd(set_basic.InInter))))
				}))
			hFast := a.Have(
				"h at twice the time less one is continuous on ⟦1/2, 1⟧",
				"continuous_map(subtopology(real_topology, ⟦&0, &1⟧ ∩ «upper»), T, λt:real. h(&2 * t - &1))",
				By(PathReparametrise, hPath, shifted, shiftedBounded))
			hAgrees := a.Have(
				"on ⟦1/2, 1⟧ the joined map is h at twice the time less one",
				"∀x:real. x ∈ ⋃subtopology(real_topology, ⟦&0, &1⟧ ∩ «upper») ⇒ h(&2 * x - &1) = «joined»(x)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					xIn := b.Simplified(
						b.Assume(),
						Fwd(topological_space.SubtopologySpace),
						Fwd(real_topology.RealSpace),
						Fwd(set_basic.InInter))
					b.Cases(b.Term("x ≤ &1 / &2"))
					b.When(
						"at x = 1/2 the first branch is g(1), which is h(0)",
						func(c *Argument, atHalf Fact) {
							middle := c.Have(
								"x is 1/2, so 2x = 1 and 2x − 1 = 0",
								"&2 * x = &1 ∧ &2 * x - &1 = &0",
								ByArith(atHalf, xIn))
							c.Show(
								"both branches give the point where g ends and h begins",
								By(meet, atHalf, middle))
						})
					b.Otherwise(
						"past 1/2 the joined map takes its second branch",
						func(c *Argument, past Fact) {
							c.Show(
								"so it is h at twice the time less one",
								By(past))
						})
				}))
			upperHalf := a.Have(
				"so the joined map is continuous on ⟦1/2, 1⟧, a subspace of the unit interval",
				"continuous_map(subtopology(subtopology(real_topology, ⟦&0, &1⟧), «upper»), T, «joined»)",
				Simp(Fwd(topological_space.SubtopologySubtopology)),
				By(hAgrees, continuous.Eq.Read(hFast)))

			a.Do(Unfold(PathInDef))
			a.Show(
				"the halves are closed, cover the unit interval, and "+
					"carry the joined map continuously: pasting glues them",
				By(
					continuous.ClosedPasting,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology),
					lowerClosed,
					upperClosed,
					covered,
					lowerHalf,
					upperHalf))
		}),
})}

// PathJoinEnds — the joined path starts where the first path does and
// ends where the second does: at 0 it reads g at 0, and at 1 it reads h at
// 2 · 1 − 1 = 1.
var PathJoinEnds = pathJoinEndsThm{family.Add(registry.ProofEntry{
	Name: "PathJoinEnds",
	Key:  "prop_b1506c03cd77f34a",
	Build: family.Theorem(Statement{
		Binders: "∀g h j:(real → A).",
		Hypotheses: []string{
			"∀t:real. j(t) = COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))",
		},
		Conclusion: "j(&0) = g(&0) ∧ j(&1) = h(&1)",
	},
		func(a *Argument, g, h, j *Arrow[Real, A], joined Fact) {
			lands := a.Have(
				"at time 1 the second path is read at 2 · 1 − 1 = 1",
				"h(&2 * &1 - &1) = h(&1)",
				Congr(),
				ByArith())
			a.Show(
				"at 0 the joined path takes its first branch, at 1 its second",
				ByArith(joined.At(a.TermAs[Real]("&0")), joined.At(a.TermAs[Real]("&1")), lands))
		}),
})}

// PathJoinImage — the values of the joined path on ⟦0, 1⟧ are values of
// the two paths: up to 1/2 it reads g at 2t, past it h at 2t − 1, both
// times in ⟦0, 1⟧.
var PathJoinImage = pathJoinImageThm{family.Add(registry.ProofEntry{
	Name: "PathJoinImage",
	Key:  "prop_af8de84bdbeb3223",
	Build: family.Theorem("∀g h:(real → A). "+
		"    image(λt:real. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1)), ⟦&0, &1⟧) ⊆ "+
		"    image(g, ⟦&0, &1⟧) ∪ image(h, ⟦&0, &1⟧)",
		func(a *Argument, g, h *Arrow[Real, A]) {
			unit := a.TermAs[Set[Real]]("⟦&0, &1⟧")
			a.Do(Simp(Fwd(set_image.ImageSubsetIff)))
			a.FixAs[Real]("t")
			inUnit := a.Assume()
			a.Cases(a.Term("t ≤ &1 / &2"))
			a.When(
				"up to 1/2 the joined path is g at 2t, a time in ⟦0, 1⟧",
				func(b *Argument, early Fact) {
					b.Show(
						"so a value of g",
						ByArith(
							early,
							inUnit,
							set_image.FunInImage.At(g, unit, b.TermAs[Real]("&2 * t")),
							set_basic.InUnion))
				})
			a.Otherwise(
				"past 1/2 it is h at 2t − 1, a time in ⟦0, 1⟧",
				func(b *Argument, late Fact) {
					b.Show(
						"so a value of h",
						ByArith(
							late,
							inUnit,
							set_image.FunInImage.At(h, unit, b.TermAs[Real]("&2 * t - &1")),
							set_basic.InUnion))
				})
		}),
})}

// PathConnectedUnion — two path-connected sets sharing a point unite to a
// path-connected set: through a common point z, each point of the union
// is joined to z and z to each point inside one of the sets, and two
// points are joined by the path to z followed by the path from z.
var PathConnectedUnion = pathConnectedUnionThm{family.Add(registry.ProofEntry{
	Name: "PathConnectedUnion",
	Key:  "prop_bd3af67f561c6513",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"path_connected_in(T, s)",
			"path_connected_in(T, t)",
			"¬(s ∩ t = ∅)",
		},
		Conclusion: "path_connected_in(T, s ∪ t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], sConnected, tConnected, meet Fact) {
			sParts := a.Conjuncts(
				a.Unfolded(sConnected, PathConnectedInDef),
				"s lies in the space",
				"a path in s joins any two points of s")
			tParts := a.Conjuncts(
				a.Unfolded(tConnected, PathConnectedInDef),
				"t lies in the space",
				"a path in t joins any two points of t")
			_, zIn := a.ObtainAs[A](
				"s and t share a point z",
				"∃z:A. z ∈ s ∧ z ∈ t",
				By(meet, set_basic.MemberNotEmpty, set_basic.InInter))
			toZ := a.Have(
				"a point of s ∪ t is joined to z by a path in s or a path in t, so in s ∪ t",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ s ∪ t",
					},
					Conclusion: "∃g:(real → A). path_in(T, g) ∧ image(g, ⟦&0, &1⟧) ⊆ s ∪ t ∧ g(&0) = x ∧ g(&1) = z",
				},
				BySets(sParts[1], tParts[1], zIn))
			fromZ := a.Have(
				"and z is joined to each point of s ∪ t in the same way",
				Statement{
					Binders: "∀y:A.",
					Hypotheses: []string{
						"y ∈ s ∪ t",
					},
					Conclusion: "∃h:(real → A). path_in(T, h) ∧ image(h, ⟦&0, &1⟧) ⊆ s ∪ t ∧ h(&0) = z ∧ h(&1) = y",
				},
				BySets(sParts[1], tParts[1], zIn))
			a.Do(
				Simp(Fwd(PathConnectedInDef)),
				SplitConj(
					Case(
						"s ∪ t lies in the space, as s and t do",
						By(sParts[0], tParts[0], set_order.UnionSubset)),
					Case(
						"two points x, y of s ∪ t are joined through z",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							ends := b.Conjuncts(
								b.Assume(),
								"x lies in s ∪ t",
								"y lies in s ∪ t")
							g, first := b.UnpackAs[Fun[Real, A]](GroupPremises(ends[0], toZ.At(x)), "g")
							gParts := b.Conjuncts(
								first,
								"g is a path",
								"its values lie in s ∪ t",
								"it starts at x",
								"it ends at z")
							h, second := b.UnpackAs[Fun[Real, A]](GroupPremises(ends[1], fromZ.At(y)), "h")
							hParts := b.Conjuncts(
								second,
								"h is a path",
								"its values lie in s ∪ t",
								"it starts at z",
								"it ends at y")
							joined := b.TermAs[Fun[Real, A]]("λr:real. COND(r ≤ &1 / &2, g(&2 * r), h(&2 * r - &1))")
							b.Take(joined)
							b.Show(
								"g followed by h is a path from x to y inside s ∪ t",
								SplitConjAll(
									Case(
										"it is a path, g ending at z where h begins",
										By(PathJoin.At(T, g, h), gParts[0], hParts[0], gParts[3], hParts[2])),
									Case(
										"its values are values of g or of h, which lie in s ∪ t",
										By(PathJoinImage.At(g, h), gParts[1], hParts[1], set_order.UnionSubset, set_order.SubsetTrans)),
									Case(
										"it starts at g(0) = x",
										By(PathJoinEnds.At(g, h, joined), gParts[2])),
									Case(
										"it ends at h(1) = y",
										By(PathJoinEnds.At(g, h, joined), hParts[3]))))
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Images and the line
// ---------------------------------------------------------------------------

// ImagePathConnected — a continuous map carries a path-connected set to a
// path-connected set: f after a path in s from x to y is a path in the
// image from f(x) to f(y), and the image lies in the second space by the
// mapping clause of continuity.
var ImagePathConnected = imagePathConnectedThm{family.Add(registry.ProofEntry{
	Name: "ImagePathConnected",
	Key:  "prop_31d12d09753fa036",
	Build: continuous.ContinuousMap.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"path_connected_in(T, s)",
		},
		Conclusion: "path_connected_in(S, image(f, s))",
	},
		func(
			a *Argument,
			fContinuous continuous.ContinuousMapFact[on.T, on.S],
			s *Expr[Set[A]],
			pathConnected Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(pathConnected, PathConnectedInDef),
				"s lies in the space",
				"a path in s joins any two points of s")
			a.Do(
				Simp(Fwd(PathConnectedInDef)),
				SplitConj(
					Case(
						"the image lies in the second space: f carries each point of s, a point of the space, into it",
						By(parts[0], continuous.MapsInto.Read(fContinuous), set_image.ImageSubsetIff, set_basic.SubsetDef)),
					Case(
						"two values f(x), f(y) with x, y in s are joined by f after a path in s from x to y",
						Simp(Fwd(set_image.ForallInImagePair)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							ends := b.Assume()
							_, joined := b.UnpackAs[Fun[Real, A]](GroupPremises(ends, parts[1].At(x, y)), "g")
							path := b.Conjuncts(
								joined,
								"g is a path",
								"its values lie in s",
								"it starts at x",
								"it ends at y")
							gContinuous := b.Unfolded(path[0], PathInDef)
							b.Take(b.Term("f ∘ g"))
							b.Show(
								"f ∘ g is a path in the image from f(x) to f(y)",
								SplitConjAll(
									Case(
										"f ∘ g is continuous on the unit interval, by composition",
										By(fContinuous, PathInDef, continuous.Compose.Read(gContinuous))),
									Case(
										"its values are f's values on g's values, which lie in s",
										Simp(Fwd(set_image.ImageCompose)),
										By(path[1], set_image.ImageSubset)),
									Case(
										"it starts at f(g(0)) = f(x)",
										By(path[2], functions.ComposeApply)),
									Case(
										"it ends at f(g(1)) = f(y)",
										By(path[3], functions.ComposeApply))))
						})),
				))
		}),
})}

// IntervalPathConnected — every interval of the line is path-connected:
// two of its points x and y are joined by the straight path
// t ↦ x + t · (y − x), a polynomial, whose values on ⟦0, 1⟧ lie between x
// and y, so in the interval. An instance theorem of the line; it lives
// here because real_topology, below this chapter, cannot spell
// path_connected_in.
var IntervalPathConnected = intervalPathConnectedThm{family.Add(registry.ProofEntry{
	Name: "IntervalPathConnected",
	Key:  "prop_d0e072b5298d8b08",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"real_interval(s)",
		},
		Conclusion: "path_connected_in(real_topology, s)",
		Abbrev: Abbrev{
			{Name: "straight", Text: "λt:real. x + t * (y - x)"},
		},
	},
		func(a *Argument, s *Expr[Set[Real]], interval Fact) {
			between := a.Unfolded(interval, real_topology.RealIntervalDef)
			a.Do(
				Simp(Fwd(PathConnectedInDef)),
				SplitConj(
					Case(
						"s lies in the line, whose points are all the reals",
						By(real_topology.RealSpace, set_order.SubsetUniv)),
					Case(
						"two points x, y of s are joined by the straight path from x to y",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]("x")
							y := b.FixAs[Real]("y")
							ends := b.Assume()
							straight := b.TermAs[Fun[Real, Real]]("«straight»")
							onLine := b.Have(
								"the straight path, x plus a multiple of the identity, is a polynomial, so continuous on the line",
								"continuous_map(real_topology, real_topology, «straight»)",
								By(
									real_continuous.PolynomialFunctionContinuous.At(straight),
									real_polynomial.Add.At(
										b.TermAs[Fun[Real, Real]]("λt:real. x"),
										b.TermAs[Fun[Real, Real]]("λt:real. t * (y - x)")),
									real_polynomial.Const,
									real_polynomial.ScalarRight.At(
										b.TermAs[Fun[Real, Real]]("λt:real. t"),
										b.TermAs[Real]("y - x")),
									real_polynomial.Id))
							b.Take(straight)
							b.Show(
								"it is a path from x to y whose values lie in s",
								SplitConjAll(
									Case(
										"it is continuous on the unit interval, a subspace of the line",
										By(PathInDef, continuous.FromSubtopology.Read(onLine))),
									Case(
										"its value at a time t in ⟦0, 1⟧ lies between x and y, so in s",
										Simp(Fwd(set_image.ImageSubsetIff)),
										Derive(func(c *Argument) {
											c.FixAs[Real]("t")
											inUnit := c.Assume()
											point := c.Term("«straight»(t)")
											c.Cases(c.Term("x ≤ y"))
											c.When(
												"where x ≤ y, the point lies between x and y",
												func(d *Argument, ordered Fact) {
													order := d.Have(
														"t and 1 − t are not negative, nor is y − x",
														"x ≤ «straight»(t) ∧ «straight»(t) ≤ y",
														ByArith(ordered, inUnit))
													d.Show(
														"so it lies in s",
														By(between.At(x, point, y), ends, order))
												})
											c.Otherwise(
												"where y < x, the point lies between y and x",
												func(d *Argument, reversed Fact) {
													yx := d.Have(
														"x ≤ y fails, so y ≤ x",
														"y ≤ x",
														ByArith(reversed))
													order := d.Have(
														"t and 1 − t are not negative, nor is x − y",
														"y ≤ «straight»(t) ∧ «straight»(t) ≤ x",
														ByArith(yx, inUnit))
													d.Show(
														"so it lies in s",
														By(between.At(y, point, x), ends, order))
												})
										})),
									Case(
										"it starts at x",
										ByArith()),
									Case(
										"it ends at y",
										ByArith())))
						})),
				))
		}),
})}
