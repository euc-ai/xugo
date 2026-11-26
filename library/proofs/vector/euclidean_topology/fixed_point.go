// fixed_point.go — Brouwer's fixed point theorem on the unit cube, by
// Kuhn's lemma. A self-map of the cube labels each point and coordinate
// by the direction the map moves it; Kuhn's lemma on the grid of width
// 1/p finds a cell in which every coordinate is moved both up and down;
// the cells shrink to a point as p grows, and by continuity the map moves
// that point in no coordinate.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/kuhn"
	"github.com/euc-ai/xugo/library/proofs/cartesian/kuhn_labelling"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// KuhnLabelling — a map of the cube into itself labels the cube as Kuhn's
// lemma asks: ⊥ where a coordinate is 0, ⊤ where it is 1, and the map
// moves a coordinate labelled ⊥ up or not at all and one labelled ⊤ down
// or not at all. Label x at i ⊤ when x(i) is 1 or f moves it down. Then
// ⊤ where x(i) is 1, and the direction where ⊥, are immediate; f(x) lies
// in the cube, its coordinates in ⟦0, 1⟧, so f moves no coordinate 0 down,
// giving ⊥ there, and no coordinate 1 up. No continuity enters.
var KuhnLabelling = kuhnLabellingThm{family.Add(registry.ProofEntry{
	Name: "KuhnLabelling",
	Key:  "prop_8d135c86e3a35058",
	Reading: "The self-map hypothesis is load-bearing at both faces: for f ≡ −1 the label at x(i) = " +
		"0 must be ⊥, and then 0 ≤ −1 is asked. Nothing is read of f off the cube, nor of its continuity.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"∀x:(num → real). x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)",
		},
		Conclusion: "∃l:((num → real) → num → bool). " +
			"    (∀x:(num → real). ∀i:num. «cubeCoordinate»(x, i) ∧ x(i) = &0 ⇒ ¬l(x, i)) ∧ " +
			"    (∀x:(num → real). ∀i:num. «cubeCoordinate»(x, i) ∧ x(i) = &1 ⇒ l(x, i)) ∧ " +
			"    (∀x:(num → real). ∀i:num. «cubeCoordinate»(x, i) ∧ ¬l(x, i) ⇒ x(i) ≤ f(x)(i)) ∧ " +
			"    (∀x:(num → real). ∀i:num. «cubeCoordinate»(x, i) ∧ l(x, i) ⇒ f(x)(i) ≤ x(i))",
		Abbrev: Abbrev{
			{Name: "cubeCoordinate", Text: "λx:(num → real). λi:num. x ∈ unit_cube(n) ∧ i < n"},
		},
	},
		func(a *Argument, n *Expr[Nat], f *Arrow2[Fun[Nat, Real], Nat, Real], selfMap Fact) {
			a.Take(a.TermAs[Fun2[Fun[Nat, Real], Nat, Bool]](
				"λx:(num → real). λi:num. x(i) = &1 ∨ f(x)(i) < x(i)"))
			// The cube read by its coordinates, here and where f maps it.
			a.Do(Unfold(UnitCubeDef))
			a.Do(SplitConjAll(
				Case(
					"at a coordinate 0 the label is ⊥: f(x) lies in the cube, so f(x)(i) is not below 0",
					ByArith(selfMap)),
				Case(
					"at a coordinate 1 the label is ⊤",
					ByArith()),
				Case(
					"where the label is ⊥, f(x)(i) is not below x(i)",
					ByArith()),
				Case(
					"where the label is ⊤, x(i) is 1, at least f(x)(i) "+
						"as f(x) lies in the cube, or f(x)(i) lies below it",
					ByArith(selfMap)),
			))
		}),
})}

// AlmostFixedCell — for every width 1/p the cube has a cell of that width
// in which each coordinate is moved up at one point and down at another:
// the grid {0, …, p}ⁿ scaled by 1/p lies in the cube, the labelling of the
// cube read through the scaling is ⊥ and ⊤ on the grid's faces as Kuhn's
// lemma asks, and the lemma's cell, scaled, is the cell, its two points at
// each coordinate ordered by their labels.
var AlmostFixedCell = almostFixedCellThm{family.Add(registry.ProofEntry{
	Name: "AlmostFixedCell",
	Key:  "prop_67fbdab1861c2841",
	Reading: "True of every self-map of the cube, continuous or not. 0 < p is " +
		"load-bearing: at p = 0 the cell has width &0 and the statement would ask a " +
		"fixed point of a map that need have none, a step map of ⟦0, 1⟧ across 1/2.",
	Build: family.Theorem(Statement{
		Binders: "∀n p:num. ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"0 < p",
			"∀x:(num → real). x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)",
		},
		Conclusion: "∃q:(num → real). " +
			"    q ∈ unit_cube(n) ∧ " +
			"    ∀i:num. " +
			"        i < n ⇒ " +
			"        ∃r s:(num → real). " +
			"            r ∈ unit_cube(n) ∧ " +
			"            s ∈ unit_cube(n) ∧ " +
			"            «inCell»(q, &1 / &p, r, s) ∧ " +
			"            r(i) ≤ f(r)(i) ∧ " +
			"            f(s)(i) ≤ s(i)",
	},
		func(a *Argument, n, p *Expr[Nat], f *Arrow2[Fun[Nat, Real], Nat, Real], positive, selfMap Fact) {
			_, labelled := a.Unpack(GroupPremises(selfMap, KuhnLabelling.At(n, f)), "l")
			labels := a.Conjuncts(
				labelled,
				"l is ⊥ where a coordinate is 0",
				"l is ⊤ where a coordinate is 1",
				"f moves a coordinate labelled ⊥ up or not at all",
				"f moves a coordinate labelled ⊤ down or not at all")
			atZero, atOne, up, down := labels[0], labels[1], labels[2], labels[3]
			// The scaling carries a grid point into the cube coordinate by
			// coordinate and is zero from the dimension on, as an n-vector is.
			_, scaleDef := a.LetAs[Fun2[Fun[Nat, Nat], Nat, Real]](
				"scale", "λx:(num → num). λi:num. COND(i < n, &(x(i)) / &p, &0)")
			intoCube := a.Have(
				"the scaling carries the grid into the cube",
				"∀x:(num → num). x ∈ kuhn_grid(p, n) ⇒ scale(x) ∈ unit_cube(n)",
				scaleDef.Rw(),
				Simp(Fwd(UnitCubeDef), Fwd(kuhn.KuhnGridDef), Fwd(vec_space.VecDef)),
				ByArith(positive))
			faces := a.Have(
				"the scaling carries a grid coordinate 0 to 0 and p to 1",
				"∀x:(num → num). ∀i:num. i < n ⇒ (x(i) = 0 ⇒ scale(x)(i) = &0) ∧ (x(i) = p ⇒ scale(x)(i) = &1)",
				scaleDef.Rw(),
				ByArith(positive))
			width := a.Have(
				"the scaling carries a rise of at most one in a grid coordinate to a rise of at most 1/p",
				Statement{
					Binders:    "∀x y:(num → num). ∀j:num.",
					Hypotheses: []string{"j < n", "x(j) ≤ y(j)", "y(j) ≤ x(j) + 1"},
					Conclusion: "scale(x)(j) ≤ scale(y)(j) ∧ scale(y)(j) ≤ scale(x)(j) + &1 / &p",
				},
				scaleDef.Rw(),
				ByArith(positive))
			gridLower := a.Have(
				"l read through the scaling is ⊥ where a grid coordinate is 0",
				"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = 0 ⇒ ¬l(scale(x), i)",
				By(faces, intoCube, atZero))
			gridUpper := a.Have(
				"l read through the scaling is ⊤ where a grid coordinate is p",
				"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = p ⇒ l(scale(x), i)",
				By(faces, intoCube, atOne))
			_, cell := a.ObtainAs[Fun[Nat, Nat]](
				"by Kuhn's lemma some grid point c has a cell holding, at "+
					"each coordinate, two grid points labelled differently there",
				"∃c:(num → num). "+
					"    c ∈ kuhn_grid(p, n) ∧ "+
					"    ∀i:num. "+
					"        i < n ⇒ "+
					"        ∃u v:(num → num). "+
					"            u ∈ kuhn_grid(p, n) ∧ "+
					"            v ∈ kuhn_grid(p, n) ∧ "+
					"            (∀j:num. j < n ⇒ c(j) ≤ u(j) ∧ u(j) ≤ c(j) + 1 ∧ c(j) ≤ v(j) ∧ v(j) ≤ c(j) + 1) ∧ "+
					"            ¬(l(scale(u), i) ⇔ l(scale(v), i))",
				By(
					gridLower,
					gridUpper,
					kuhn_labelling.KuhnLemma.At(
						p, n, a.TermAs[Fun2[Fun[Nat, Nat], Nat, Bool]]("λx:(num → num). λi:num. l(scale(x), i)"))))
			cellParts := a.Conjuncts(
				cell,
				"c is a point of the grid",
				"at each coordinate the cell of c holds two points labelled differently there")
			cIn, corners := cellParts[0], cellParts[1]
			a.Take(a.TermAs[Fun[Nat, Real]]("scale(c)"))
			a.Do(SplitConj(
				Case(
					"scale(c) lies in the cube, as c lies in the grid",
					By(intoCube, cIn)),
				Case(
					"at each coordinate i, the scaling carries the two "+
						"points of the cell to one moved up and one moved down",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						below := b.Assume()
						u, v, pair := b.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
							GroupPremises(below, corners.At(i)), "u", "v")
						pairParts := b.Conjuncts(
							pair,
							"u is a point of the grid",
							"v is a point of the grid",
							"u and v lie in the cell of c",
							"the labels of scale(u) and scale(v) at i differ")
						uIn, vIn, inCell, differ := pairParts[0], pairParts[1], pairParts[2], pairParts[3]
						scaled := b.Have(
							"scale(u) and scale(v) lie in the cube, within 1/p above scale(c) in every coordinate",
							"scale(u) ∈ unit_cube(n) ∧ "+
								"scale(v) ∈ unit_cube(n) ∧ "+
								"«inCell»(scale(c), &1 / &p, scale(u), scale(v))",
							By(intoCube.At(u), intoCube.At(v), width, uIn, vIn, inCell))
						su := b.TermAs[Fun[Nat, Real]]("scale(u)")
						sv := b.TermAs[Fun[Nat, Real]]("scale(v)")
						b.Cases(b.Term("l(scale(u), i)"))
						b.When(
							"scale(u) is labelled ⊤ at i and so scale(v) ⊥: r "+
								"is scale(v), moved up, and s is scale(u), moved down",
							func(c *Argument, top Fact) {
								c.Take(sv)
								c.Take(su)
								c.Show(
									"f moves coordinate i of scale(v) up and that of scale(u) down",
									By(differ, top, scaled, up.At(sv, i), down.At(su, i), below))
							})
						b.Otherwise(
							"scale(u) is labelled ⊥ at i and so scale(v) ⊤: r "+
								"is scale(u), moved up, and s is scale(v), moved down",
							func(c *Argument, bottom Fact) {
								c.Take(su)
								c.Take(sv)
								c.Show(
									"f moves coordinate i of scale(u) up and that of scale(v) down",
									By(differ, bottom, scaled, up.At(su, i), down.At(sv, i), below))
							})
					})),
			))
		}),
})}

// BrouwerCube — Brouwer's fixed point theorem on the cube: a continuous
// map of the unit cube into itself fixes a point. Kuhn's lemma gives, at
// every width 1/(k + 1), a cell q(k) of the cube in which each coordinate
// i is moved up at one point r(k, i) and down at another s(k, i); the
// cells have a subsequence converging to a point x, the points r and s
// of the subsequence converge to x with them, and by continuity their
// images converge to f(x), so the two inequalities pass to the limit and
// pin each coordinate of f(x) to that of x.
var BrouwerCube = brouwerCubeThm{family.Add(registry.ProofEntry{
	Name: "BrouwerCube",
	Key:  "prop_6b9bedbf92e98a21",
	Reading: "Continuity is load-bearing, as the step map of ⟦0, 1⟧ across 1/2 shows, and it " +
		"does not imply the self-map hypothesis, giving only f(x) ∈ ℝⁿ. f(x) = x is equality of " +
		"total functions, which holds because both are zero from n on; at n = 0 the cube is one point.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"∀x:(num → real). x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)",
			"continuous_map(subtopology(euclidean_topology(n), unit_cube(n)), euclidean_topology(n), f)",
		},
		Conclusion: "∃x:(num → real). x ∈ unit_cube(n) ∧ f(x) = x",
	}, func(a *Argument, n *Expr[Nat], f *Arrow2[Fun[Nat, Real], Nat, Real], selfMap, continuity Fact) {
		type point = Fun[Nat, Real]
		type sequence = Fun2[Nat, Nat, Real]
		cube := a.TermAs[Set[point]]("unit_cube(n)")
		space := a.TermAs[Set[point]]("{u:(num → real) | vec⟨n⟩(u)}")
		dist := a.TermAs[Fun2[point, point, Real]]("vec_dist⟨n⟩")

		inSpace := a.Have(
			"the cube lies in ℝⁿ",
			"unit_cube(n) ⊆ {u:(num → real) | vec⟨n⟩(u)}",
			BySets(UnitCubeDef.At(n)))
		coordinatewise := a.Have(
			"a sequence of the cube converges in ℝⁿ to a point of "+
				"the cube exactly when its coordinates below n converge",
			Statement{
				Binders: "∀y:(num → num → real). ∀l:(num → real).",
				Hypotheses: []string{
					"∀k:num. y(k) ∈ unit_cube(n)",
					"l ∈ unit_cube(n)",
				},
				Conclusion: "metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, y, l) ⇔ " +
					"∀i:num. i < n ⇒ (λk:num. y(k)(i)) ⟶ l(i)",
			},
			Derive(func(b *Argument) {
				b.FixAs[sequence]("y")
				b.FixAs[point]("l")
				inCube := b.Assume()
				vectors := b.Have(
					"its terms and its limit are n-vectors",
					"(∀k:num. vec⟨n⟩(y(k))) ∧ vec⟨n⟩(l)",
					BySets(inSpace, inCube))
				b.Show(
					"and a sequence of n-vectors converges to an n-vector as its coordinates do",
					By(vectors, ConvergesIffCoordinates))
			}))
		onCube := a.Have(
			"for the distance of ℝⁿ f is continuous on the cube, whose "+
				"subspace topology is the metric topology of the distance there",
			"continuous_map(metric_topology(unit_cube(n), vec_dist⟨n⟩), "+
				"    metric_topology({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩), "+
				"    f)",
			By(
				continuity,
				inSpace,
				euclidean.EuclideanMetric.At(n),
				metric_space.MetricTopologySubspace.At(space, dist, cube),
				EuclideanTopologyDef.At(n)))
		sequential := a.Have(
			"so f carries a sequence of the cube converging to a "+
				"point of the cube to a sequence converging to its image",
			Statement{
				Binders: "∀y:(num → num → real). ∀l:(num → real).",
				Hypotheses: []string{
					"∀k:num. y(k) ∈ unit_cube(n)",
					"l ∈ unit_cube(n)",
					"metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, y, l)",
				},
				Conclusion: "metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, f ∘ y, f(l))",
			},
			Derive(func(b *Argument) {
				y := b.FixAs[sequence]("y")
				l := b.FixAs[point]("l")
				given := b.Assume()
				withinCube := b.Have(
					"the sequence converges to l in the cube as well, its terms and l lying there",
					"metric_converges_to(unit_cube(n), vec_dist⟨n⟩, y, l)",
					By(
						given,
						complete_metric.MetricConvergesToDef.At(cube, dist, y, l),
						complete_metric.MetricConvergesToDef.At(space, dist, y, l)))
				b.Show(
					"and a continuous map between metric spaces keeps the limits of sequences",
					By(
						withinCube,
						onCube,
						inSpace,
						euclidean.EuclideanMetric.At(n),
						metric_space.SubMetricSpace.At(space, dist, cube),
						complete_metric.ContinuousIffSequential.At(cube, dist, space, dist, f)))
			}))

		cellsAt := a.Have(
			"at each width 1/(k + 1) some cell of the cube has, for "+
				"every coordinate, a point moved up and a point moved down",
			"∀k:num. ∃q:(num → real). "+
				"    q ∈ unit_cube(n) ∧ "+
				"    ∀i:num. "+
				"        i < n ⇒ "+
				"        ∃r s:(num → real). "+
				"            r ∈ unit_cube(n) ∧ "+
				"            s ∈ unit_cube(n) ∧ "+
				"            «inCell»(q, &1 / &(k + 1), r, s) ∧ "+
				"            r(i) ≤ f(r)(i) ∧ "+
				"            f(s)(i) ≤ s(i)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				positive := b.Have(
					"k + 1 is positive",
					"0 < k + 1",
					ByArith())
				b.Show(
					"Kuhn's lemma on the grid of width 1/(k + 1)",
					By(selfMap, positive, AlmostFixedCell.At(n, b.TermAs[Nat]("k + 1"), f)))
			}))
		q, _, _, cells := a.Obtain3As[sequence, Fun3[Nat, Nat, Nat, Real], Fun3[Nat, Nat, Nat, Real]](
			"choose the cell q(k) and its points r(k, i) and s(k, i) at every width at once",
			"∃q:(num → num → real). ∃r s:(num → num → num → real). ∀k:num. "+
				"    q(k) ∈ unit_cube(n) ∧ "+
				"    ∀i:num. "+
				"        i < n ⇒ "+
				"        r(k, i) ∈ unit_cube(n) ∧ "+
				"        s(k, i) ∈ unit_cube(n) ∧ "+
				"        «inCell»(q(k), &1 / &(k + 1), r(k, i), s(k, i)) ∧ "+
				"        r(k, i)(i) ≤ f(r(k, i))(i) ∧ "+
				"        f(s(k, i))(i) ≤ s(k, i)(i)",
			By(cellsAt))

		σ, x, limit := a.Obtain2As[Fun[Nat, Nat], point](
			"the cells have a subsequence q(σ(k)) converging to a point x of the cube",
			"∃σ:(num → num). ∃x:(num → real). "+
				"    (∀j:num. σ(j) < σ(j + 1)) ∧ "+
				"    x ∈ unit_cube(n) ∧ "+
				"    metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, λk:num. q(σ(k)), x)",
			By(cells, CubeSubsequence.At(n, q), functions.ComposeApply))
		sub := a.Conjuncts(
			limit,
			"σ is strictly increasing",
			"x lies in the cube",
			"q(σ(k)) converges to x")
		increasing, xIn, converges := sub[0], sub[1], sub[2]
		cellsConverge := a.Have(
			"so each coordinate of q(σ(k)) converges to that of x",
			"∀j:num. j < n ⇒ (λk:num. q(σ(k))(j)) ⟶ x(j)",
			By(coordinatewise.At(a.TermAs[sequence]("λk:num. q(σ(k))"), x), cells, xIn, converges))
		widths := a.Have(
			"the widths 1/(σ(k) + 1) of these cells shrink to nothing, σ(k) being at least k",
			"(λk:num. &1 / &(σ(k) + 1)) ⟶ &0",
			Derive(func(b *Argument) {
				b.Do(Unfold(real_sequences.RealConvergesToDef))
				eps := b.FixAs[Real]("ε")
				positive := b.Assume()
				N, small := b.ObtainAs[Nat](
					"some 1/(N + 1) lies below ε",
					"∃N:num. real_inv(&N + &1) < ε",
					By(positive, real_archimedean.ExistsReciprocalBelow.At(eps)))
				b.Take(N)
				k := b.FixAs[Nat]("k")
				past := b.Assume()
				later := b.Have(
					"past N, σ(k) + 1 is at least N + 1",
					"&0 < &N + &1 ∧ &N + &1 ≤ &(σ(k) + 1)",
					ByArith(past, increasing, nat_order.LessEqStrictlyIncreasing.At(σ, k)))
				width := b.TermAs[Real]("&(σ(k) + 1)")
				bounded := b.Have(
					"so 1/(σ(k) + 1) is positive and at most 1/(N + 1)",
					"&0 < &1 / &(σ(k) + 1) ∧ &1 / &(σ(k) + 1) ≤ real_inv(&N + &1)",
					ByArith(
						later,
						real_order_field.InvAntitoneWeak.At(b.TermAs[Real]("&N + &1"), width),
						real_order_field.InvPos.At(width),
						real_field.RealDivDef.At(b.TermAs[Real]("&1"), width)))
				b.Show(
					"and 1/(N + 1) lies below ε",
					ByArith(bounded, small))
			}))

		trapped := a.Have(
			"a sequence of the cube kept in the cells q(σ(k)) converges "+
				"to x coordinate by coordinate, and its image to f(x)",
			Statement{
				Binders: "∀y:(num → num → real).",
				Hypotheses: []string{
					"∀k:num. y(k) ∈ unit_cube(n)",
					"∀k j:num. j < n ⇒ q(σ(k))(j) ≤ y(k)(j) ∧ y(k)(j) ≤ q(σ(k))(j) + &1 / &(σ(k) + 1)",
				},
				Conclusion: "∀i:num. i < n ⇒ (λk:num. y(k)(i)) ⟶ x(i) ∧ (λk:num. f(y(k))(i)) ⟶ f(x)(i)",
			},
			Derive(func(b *Argument) {
				y := b.FixAs[sequence]("y")
				given := b.Conjuncts(
					b.Assume(),
					"the terms of y lie in the cube",
					"each lies in its cell")
				inCube, within := given[0], given[1]
				coordinates := b.Have(
					"each coordinate of y(k) is squeezed onto that of x",
					"∀j:num. j < n ⇒ (λk:num. y(k)(j)) ⟶ x(j)",
					Derive(func(c *Argument) {
						j := c.FixAs[Nat]("j")
						below := c.Assume()
						gap := c.Have(
							"y(k)(j) lies within the width of the cell of q(σ(k))(j)",
							"∀k:num. |y(k)(j) - q(σ(k))(j)| ≤ &1 / &(σ(k) + 1)",
							c.ForEach(func(k *Expr[Nat]) Action {
								return ByArith(within.At(k, j), below)
							}))
						c.Show(
							"the widths tend to 0 while q(σ(k))(j) tends to x(j)",
							By(
								gap,
								widths,
								cellsConverge.At(j),
								below,
								real_sequences.LimitSqueezeDistance.At(
									c.TermAs[Fun[Nat, Real]]("λk:num. y(k)(j)"),
									c.TermAs[Fun[Nat, Real]]("λk:num. q(σ(k))(j)"),
									c.TermAs[Fun[Nat, Real]]("λk:num. &1 / &(σ(k) + 1)"),
									c.TermAs[Real]("x(j)"))))
					}))
				toX := b.Have(
					"so y converges to x in ℝⁿ",
					"metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, y, x)",
					By(coordinatewise.At(y, x), inCube, xIn, coordinates))
				image := b.Have(
					"and by continuity f(y(k)) converges to f(x)",
					"metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, λk:num. f(y(k)), f(x))",
					By(sequential.At(y, x), inCube, xIn, toX, functions.ComposeApply))
				imageCoordinates := b.Have(
					"coordinate by coordinate, f(y(k)) and f(x) lying in the cube",
					"∀i:num. i < n ⇒ (λk:num. f(y(k))(i)) ⟶ f(x)(i)",
					By(
						coordinatewise.At(b.TermAs[sequence]("λk:num. f(y(k))"), b.TermAs[point]("f(x)")),
						selfMap,
						inCube,
						xIn,
						image))
				b.Show(
					"both limits hold in every coordinate below n",
					By(coordinates, imageCoordinates))
			}))

		fixed := a.Have(
			"f fixes every coordinate of x below n",
			"∀i:num. i < n ⇒ f(x)(i) = x(i)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				up := b.Have(
					"f moves coordinate i of each r(σ(k), i) up, so in the limit x(i) ≤ f(x)(i)",
					"x(i) ≤ f(x)(i)",
					By(
						trapped.At(b.TermAs[sequence]("λk:num. r(σ(k), i)"), i),
						cells,
						below,
						real_sequences.LimitLessEq.At(
							b.TermAs[Fun[Nat, Real]]("λk:num. r(σ(k), i)(i)"),
							b.TermAs[Fun[Nat, Real]]("λk:num. f(r(σ(k), i))(i)"),
							b.TermAs[Real]("x(i)"),
							b.TermAs[Real]("f(x)(i)"),
							b.TermAs[Nat]("0"))))
				down := b.Have(
					"f moves coordinate i of each s(σ(k), i) down, so in the limit f(x)(i) ≤ x(i)",
					"f(x)(i) ≤ x(i)",
					By(
						trapped.At(b.TermAs[sequence]("λk:num. s(σ(k), i)"), i),
						cells,
						below,
						real_sequences.LimitLessEq.At(
							b.TermAs[Fun[Nat, Real]]("λk:num. f(s(σ(k), i))(i)"),
							b.TermAs[Fun[Nat, Real]]("λk:num. s(σ(k), i)(i)"),
							b.TermAs[Real]("f(x)(i)"),
							b.TermAs[Real]("x(i)"),
							b.TermAs[Nat]("0"))))
				b.Show(
					"so f(x) and x agree in coordinate i",
					ByArith(up, down))
			}))
		a.Take(x)
		vectors := a.Conjuncts(
			a.Have(
				"f(x) and x are n-vectors, both lying in the cube",
				"vec⟨n⟩(f(x)) ∧ vec⟨n⟩(x)",
				BySets(selfMap.At(x), inSpace, xIn)),
			"f(x) is an n-vector",
			"x is an n-vector")
		fx := a.TermAs[point]("f(x)")
		a.Show(
			"x is a point of the cube, and two n-vectors agreeing below n are equal",
			By(
				fixed,
				xIn,
				vec_space.Extensionality.At(
					a.TermAs[Real]("&0"),
					proof.InhabitFrom(fx, vectors[0]),
					proof.InhabitFrom(x, vectors[1]))))
	}),
})}
