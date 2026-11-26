// completely_regular.go — completely regular spaces: a point and a closed
// set not holding it are separated by a continuous function into ⟦0, 1⟧.
// Such a space is regular; a normal space whose points are closed is one,
// by Urysohn's lemma, so the topology of a distance is; and a subspace
// inherits the property.

package real_valued

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Completely regular spaces
// ---------------------------------------------------------------------------

// CompletelyRegularImpRegular — a completely regular space is regular. For
// a closed set c and a point x of the space outside it, a continuous f
// into ⟦0, 1⟧ is 0 at x and 1 on c; the points of the space where f lies
// below 1/2 and those where it lies above 1/2 are the preimages of two
// open rays, disjoint open sets about x and around c. No axiom enters.
var CompletelyRegularImpRegular = completelyRegularImpRegularThm{family.Add(registry.ProofEntry{
	Name: "CompletelyRegularImpRegular",
	Key:  "prop_86b91feacce9075a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"completely_regular_space(T)",
		},
		Conclusion: "regular_space(T)",
	}, func(a *Argument, T *Expr[Set[Set[A]]], completelyRegular Fact) {
		separating := a.Unfolded(completelyRegular, CompletelyRegularSpaceDef)
		a.Do(Simp(Fwd(separation.RegularSpaceDef)))
		c := a.FixAs[Set[A]]("c")
		x := a.FixAs[A]("x")
		given := a.Conjuncts(
			a.Assume(),
			"c is closed",
			"x is a point of the space",
			"outside c")
		_, properties := a.UnpackAs[Fun[A, Real]](
			GroupPremises(given[0], given[1], given[2], separating.At(c, x)),
			"f")
		parts := a.Conjuncts(
			properties,
			"f is continuous into the line",
			"with values in ⟦0, 1⟧",
			"0 at x",
			"and 1 on c")
		continuousF, zeroAtX, oneOnC := parts[0], parts[2], parts[3]
		half := a.TermAs[Real]("&1 / &2")
		below := a.Have(
			"f(x) = 0 lies below 1/2",
			"f(x) < &1 / &2",
			ByArith(zeroAtX))
		above := a.Have(
			"on c, f = 1 lies above 1/2",
			"∀y:A. y ∈ c ⇒ &1 / &2 < f(y)",
			ByArith(oneOnC))
		cInSpace := a.Have(
			"c, being closed, lies in the space",
			"c ⊆ ⋃T",
			By(given[0], topological_space.ClosedInDef))
		apart := a.Have(
			"no value of f lies both below and above 1/2",
			"∀y:A. ¬(f(y) < &1 / &2 ∧ &1 / &2 < f(y))",
			a.ForEach(func(y *Expr[A]) Action { return ByArith() }))
		a.Take(a.TermAs[Set[A]]("preimage_on(⋃T, f, {r:real | r < &1 / &2})"))
		a.Take(a.TermAs[Set[A]]("preimage_on(⋃T, f, {r:real | &1 / &2 < r})"))
		a.Do(SplitConjAll(
			Case(
				"the points where f lies below 1/2 form an open set, the preimage of an open ray",
				By(continuous.PreimageOpen.Read(continuousF), real_topology.RayBelowOpen.At(half))),
			Case(
				"so do the points where f lies above 1/2",
				By(continuous.PreimageOpen.Read(continuousF), real_topology.RayAboveOpen.At(half))),
			Case(
				"x is among the first",
				BySets(given[1], below)),
			Case(
				"c lies among the second",
				BySets(above, cInSpace)),
			Case(
				"and the two share no point",
				BySets(apart))))
	}),
})}

// NormalT1ImpCompletelyRegular — a normal space whose points are closed is
// completely regular: for a closed set c and a point x of the space outside
// it, {x} is closed and misses c, and Urysohn's function for {x} and c is
// 0 at x and 1 on c.
var NormalT1ImpCompletelyRegular = normalT1ImpCompletelyRegularThm{family.Add(registry.ProofEntry{
	Name: "NormalT1ImpCompletelyRegular",
	Key:  "prop_6d60fa205c660d7d",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"t1_space(T)",
		},
		Conclusion: "completely_regular_space(T)",
	}, func(a *Argument, T *Expr[Set[Set[A]]], topology, normal, t1 Fact) {
		a.Do(Unfold(CompletelyRegularSpaceDef))
		c := a.FixAs[Set[A]]("c")
		a.FixAs[A]("x")
		given := a.Conjuncts(
			a.Assume(),
			"c is closed",
			"x is a point of the space",
			"outside c")
		point := a.Have(
			"{x} is closed, the points of a T1 space being closed",
			"closed_in(T, {x})",
			By(t1, given[1], separation.T1IffSingletonsClosed.Read(topology)))
		apart := a.Have(
			"and misses c",
			"{x} ∩ c = ∅",
			BySets(given[2]))
		f, urysohn := a.UnpackAs[Fun[A, Real]](
			GroupPremises(topology, normal, point, given[0], apart, Urysohn.At(T, a.TermAs[Set[A]]("{x}"), c)),
			"f")
		a.Take(f)
		a.Show(
			"Urysohn's function for {x} and c is 0 at x and 1 on c",
			BySets(urysohn))
	}),
})}

// CompletelyRegularSubtopology — a subspace of a completely regular space
// is completely regular. A closed set c of the subspace is the trace d ∩ s
// of a closed set d of the space, and a point x of the subspace outside c
// lies in s, so outside d. The function separating x from d in the space
// is continuous on the subspace, keeps its values there in ⟦0, 1⟧, is 0 at
// x and is 1 on c, which lies in d. No axiom enters.
var CompletelyRegularSubtopology = completelyRegularSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "CompletelyRegularSubtopology",
	Key:  "prop_500a38f78df05101",
	Reading: "No axiom: the complement ⋃T ∖ u of an open u is closed in T by closed_in itself, " +
		"which is all the subspace's closed sets need. s may leave ⋃T — the subspace's points are ⋃T ∩ s.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"completely_regular_space(T)",
		},
		Conclusion: "completely_regular_space(subtopology(T, s))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], completelyRegular Fact) {
		separating := a.Unfolded(completelyRegular, CompletelyRegularSpaceDef)
		a.Do(Simp(Fwd(CompletelyRegularSpaceDef)))
		a.FixAs[Set[A]]("c")
		x := a.FixAs[A]("x")
		given := a.Conjuncts(
			a.Assume(),
			"c is closed in the subspace",
			"x is a point of the subspace",
			"outside c")
		d, trace := a.ObtainAs[Set[A]](
			"c is the trace on s of a closed set d of the space",
			"∃d:set(A). closed_in(T, d) ∧ c = d ∩ s",
			By(given[0], topological_space.ClosedInSubtopology))
		traceParts := a.Conjuncts(
			trace,
			"d is closed",
			"and c = d ∩ s")
		dClosed, cTrace := traceParts[0], traceParts[1]
		subspacePoints := topological_space.SubtopologySpace.At(T, s)
		point := a.Have(
			"x is a point of the space lying in s",
			"x ∈ ⋃T ∧ x ∈ s",
			BySets(given[1], subspacePoints))
		outsideD := a.Have(
			"so x, outside c = d ∩ s, lies outside d",
			"x ∉ d",
			BySets(given[2], cTrace, point))
		f, properties := a.UnpackAs[Fun[A, Real]](
			GroupPremises(dClosed, point, outsideD, separating.At(d, x)),
			"f")
		parts := a.Conjuncts(
			properties,
			"f is continuous on the space",
			"with values in ⟦0, 1⟧ there",
			"0 at x",
			"and 1 on d")
		a.Take(f)
		a.Do(cTrace.Rw())
		a.Do(SplitConjAll(
			Case(
				"f is continuous on the subspace",
				By(continuous.FromSubtopology.Read(parts[0]))),
			Case(
				"its values at the subspace's points, which are points of the space, are at least 0",
				BySets(parts[1], subspacePoints)),
			Case(
				"and at most 1",
				BySets(parts[1], subspacePoints)),
			Case(
				"it is 0 at x",
				By(parts[2])),
			Case(
				"and 1 on c = d ∩ s, which lies in d",
				BySets(parts[3]))))
	}),
})}

// MetricCompletelyRegular — the topology of a distance is completely
// regular: it is a topology, it is normal, and it is Hausdorff, so its
// points are closed; a normal space whose points are closed is completely
// regular.
var MetricCompletelyRegular = metricCompletelyRegularThm{family.Add(registry.ProofEntry{
	Name: "MetricCompletelyRegular",
	Key:  "prop_a74475bb97f78166",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "completely_regular_space(metric_topology(M, d))",
	}, func(
		a *Argument,
		M *Expr[Set[A]],
		d *Arrow2[A, A, Real],
		metric metric_space.MetricSpaceFact[on.M],
	) {
		space := a.TermAs[Set[Set[A]]]("metric_topology(M, d)")
		a.Show(
			"a normal topology whose points are closed, as a Hausdorff space's are, is completely regular",
			By(
				metric,
				metric_space.MetricTopology.At(M, d),
				MetricNormal.At(M, d),
				metric_space.MetricHausdorff.Read(metric),
				separation.HausdorffImpT1.At(space),
				NormalT1ImpCompletelyRegular.At(space)))
	}),
})}
