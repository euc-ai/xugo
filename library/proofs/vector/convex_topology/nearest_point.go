// nearest_point.go — the topology of a convex set of ℝⁿ: an open box is
// one; a nonempty one contracts along straight lines; a nonempty closed
// set holds a point nearest to any vector, which in a convex set is
// characterized by an obtuse angle and moves no farther than the vector
// does; so a nonempty closed convex set is a retract of the whole space.

package convex_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OpenBoxConvex — a coordinatewise open box of ℝⁿ is convex.
var OpenBoxConvex = openBoxConvexThm{family.Add(registry.ProofEntry{
	Name: "OpenBoxConvex",
	Key:  "prop_7082ad075829a8ca",
	Deps: []registry.EntryLike{euclidean_topology.OpenBoxDef, convex.ConvexDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀a b:(num → real).",
		Hypotheses: []string{},
		Conclusion: "convex(euclidean_open_box⟨n⟩(a, b))",
	},
		"For two points of the box, each coordinate of a convex combination remains strictly between "+
			"its two bounds: the nonnegative weights sum to one, so at least one is positive. Vector "+
			"closure supplies the zero tail. An empty box satisfies the same convexity predicate vacuously."),
})}

// ConvexContractible — a nonempty convex set of ℝⁿ is contractible: for a
// point c of the set, the straight line (x, t) ↦ (1 − t) • x + t • c is a
// continuous map of the set times the unit interval into the set, each of
// its coordinates a sum of products of continuous functions and each of
// its values a convex combination of two points of the set; it is the
// identity at time 0 and the constant map at c at time 1.
var ConvexContractible = convexContractibleThm{family.Add(registry.ProofEntry{
	Name: "ConvexContractible",
	Key:  "prop_395ec86910c222a",
	Reading: "k ≠ ∅ is load-bearing, the empty space not being contractible; " +
		"k ⊆ ℝⁿ makes the subspace's points exactly k. At n = 0, k = {0}.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀k:set(num → real).",
		Hypotheses: []string{
			"convex(k)",
			"k ≠ ∅",
			"k ⊆ {u:(num → real) | vec⟨n⟩(u)}",
		},
		Conclusion: "contractible_space(«K»)",
		Abbrev: Abbrev{
			{Name: "K", Text: "subtopology(euclidean_topology(n), k)"},
			{Name: "I", Text: "subtopology(real_topology, ⟦&0, &1⟧)"},
			{Name: "line", Text: "λc:(num → real). λp:prod(num → real, real). " +
				"    (&1 - snd(p)) • fst(p) + snd(p) • c"},
		},
	}, func(
		a *Argument,
		n *Expr[Nat],
		k *Expr[Set[Fun[Nat, Real]]],
		convexK, nonempty, vectors Fact,
	) {
		c, cIn := a.ObtainAs[Fun[Nat, Real]](
			"k has a point c",
			"∃c:(num → real). c ∈ k",
			By(nonempty, set_basic.MemberNotEmpty))
		ambient := a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)")
		subspace := a.TermAs[Set[Set[Fun[Nat, Real]]]]("«K»")
		unit := a.TermAs[Set[Set[Real]]]("«I»")
		cylinder := a.TermAs[Set[Set[Prod[Fun[Nat, Real], Real]]]]("product_topology(«K», «I»)")
		reals := a.TermAs[Set[Set[Real]]]("real_topology")
		first := a.TermAs[Fun[Prod[Fun[Nat, Real], Real], Fun[Nat, Real]]]("fst")
		second := a.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("snd")
		straightLine := a.TermAs[Fun[Prod[Fun[Nat, Real], Real], Fun[Nat, Real]]]("«line»(c)")

		space := a.Have(
			"k lying in ℝⁿ, the points of the subspace are the points of k",
			"⋃«K» = k",
			BySets(
				vectors,
				topological_space.SubtopologySpace.At(ambient, k),
				euclidean_topology.EuclideanSpace.At(n)))
		straight := a.Have(
			"the straight line to c is a continuous map of the "+
				"subspace times the unit interval into the subspace",
			"continuous_map(product_topology(«K», «I»), «K», «line»(c))",
			Derive(func(b *Argument) {
				topology := b.Have(
					"the subspace times the unit interval is a topology",
					"is_topology(product_topology(«K», «I»))",
					By(
						product_topology.ProductTopology,
						topological_space.SubtopologyTopology.Read(real_topology.RealTopology),
						topological_space.SubtopologyTopology.At(ambient, k),
						euclidean_topology.EuclideanTopology.At(n)))
				along := b.Have(
					"each coordinate of the first projection is a continuous function on it",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i < n",
						},
						Conclusion: "continuous_map(product_topology(«K», «I»), " +
							"    real_topology, " +
							"    λp:prod(num → real, real). fst(p)(i))",
					},
					Derive(func(e *Argument) {
						i := e.FixAs[Nat]("i")
						below := e.Assume()
						coordinate := e.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). x(i)")
						e.Show(
							"it is the coordinate map of ℝⁿ after the first projection, which is continuous into ℝⁿ",
							By(
								below,
								product_topology.FstContinuous.At(subspace, unit),
								continuous.IntoSubtopology.At(cylinder, ambient, first, k),
								euclidean_topology.CoordinateContinuous.At(n, i),
								continuous.Compose.At(cylinder, ambient, first, reals, coordinate),
								functions.ComposeApply.At(coordinate, first)))
					}))
				time := b.Have(
					"so is the second projection, the time",
					"continuous_map(product_topology(«K», «I»), real_topology, snd)",
					By(
						product_topology.SndContinuous.At(subspace, unit),
						continuous.IntoSubtopology.At(cylinder, reals, second, b.TermAs[Set[Real]]("⟦&0, &1⟧"))))
				weight := b.Have(
					"and so is the weight 1 − t, a constant less the time",
					"continuous_map(product_topology(«K», «I»), real_topology, λp:prod(num → real, real). &1 - snd(p))",
					By(
						topology,
						time,
						real_valued.ContinuousRealSub.At(
							cylinder, b.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("λp:prod(num → real, real). &1"), second),
						continuous.Constant.At(cylinder, reals, b.TermAs[Real]("&1")),
						real_topology.RealSpace,
						set_basic.InUniv))
				coordinates := b.Have(
					"each coordinate of the straight line, (1 − t)·x(i) + t·c(i), is a sum of products of these",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i < n",
						},
						Conclusion: "continuous_map(product_topology(«K», «I»), " +
							"    real_topology, " +
							"    λp:prod(num → real, real). ((&1 - snd(p)) • fst(p) + snd(p) • c)(i))",
					},
					Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef)),
					Derive(func(e *Argument) {
						i := e.FixAs[Nat]("i")
						below := e.Assume()
						e.Show(
							"the products of the weight with the coordinate and of the time with the constant c(i) add up",
							By(
								topology,
								along.At(i),
								below,
								time,
								weight,
								real_valued.ContinuousRealAdd.At(
									cylinder,
									e.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]](
										"λp:prod(num → real, real). (&1 - snd(p)) * fst(p)(i)"),
									e.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("λp:prod(num → real, real). snd(p) * c(i)")),
								real_valued.ContinuousRealMul.At(
									cylinder,
									e.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("λp:prod(num → real, real). &1 - snd(p)"),
									e.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("λp:prod(num → real, real). fst(p)(i)")),
								real_valued.ContinuousRealMul.At(
									cylinder,
									second,
									e.TermAs[Fun[Prod[Fun[Nat, Real], Real], Real]]("λp:prod(num → real, real). c(i)")),
								continuous.Constant.At(cylinder, reals, e.TermAs[Real]("c(i)")),
								real_topology.RealSpace,
								set_basic.InUniv))
					}))
				inside := b.Have(
					"its values lie in k, each a convex combination of a point of k and c",
					Statement{
						Binders: "∀p:prod(num → real, real).",
						Hypotheses: []string{
							"p ∈ ⋃product_topology(«K», «I»)",
						},
						Conclusion: "(&1 - snd(p)) • fst(p) + snd(p) • c ∈ k",
					},
					Derive(func(e *Argument) {
						p := e.FixAs[Prod[Fun[Nat, Real], Real]]("p")
						pIn := e.Assume()
						where := e.Have(
							"p is a point of k at a time in ⟦0, 1⟧",
							"fst(p) ∈ k ∧ &0 ≤ snd(p) ∧ snd(p) ≤ &1",
							By(
								pIn,
								space,
								product_topology.ProductSpace.At(subspace, unit),
								set_product.InCrossProjections.At(
									e.TermAs[Set[Fun[Nat, Real]]]("⋃«K»"), e.TermAs[Set[Real]]("⋃«I»"), p),
								path_connected.UnitIntervalPoints.At(e.TermAs[Real]("snd(p)"))))
						e.Show(
							"so convexity keeps (1 − t) • x + t • c in k",
							By(convexK, where, cIn, convex.Segment.At(k)))
					}))
				values := b.Have(
					"so its values are n-vectors",
					Statement{
						Binders: "∀p:prod(num → real, real).",
						Hypotheses: []string{
							"p ∈ ⋃product_topology(«K», «I»)",
						},
						Conclusion: "vec⟨n⟩((&1 - snd(p)) • fst(p) + snd(p) • c)",
					},
					BySets(inside, vectors))
				intoSpace := b.Have(
					"a map into ℝⁿ whose n coordinates are continuous is continuous",
					"continuous_map(product_topology(«K», «I»), euclidean_topology(n), «line»(c))",
					By(
						topology,
						coordinates,
						values,
						euclidean_topology.ContinuousIffCoordinates.At(n, cylinder, straightLine)))
				b.Show(
					"continuous into ℝⁿ with its values in k, it is continuous into the subspace",
					By(intoSpace, inside, continuous.IntoSubtopology))
			}))
		contraction := a.Have(
			"so the straight line is a homotopy from the identity of the subspace to the constant map at c",
			"homotopic_rel(«K», «K», ∅, λx:(num → real). x, λx:(num → real). c)",
			Unfold(homotopy.HomotopicRelDef),
			Derive(func(b *Argument) {
				b.Take(straightLine)
				ends := b.Have(
					"coordinatewise, at time 0 the straight line is the identity, at time 1 the constant map at c",
					"∀x:(num → real). «line»(c)((x, &0)) = x ∧ «line»(c)((x, &1)) = c",
					Funext(),
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef)),
					ByArith())
				b.Show(
					"continuous, starting at the identity and ending at c, it holds the empty set fixed",
					By(straight, ends, set_basic.NotInEmpty))
			}))
		a.Do(Unfold(homotopy.ContractibleSpaceDef))
		a.Take(c)
		a.Show(
			"so the subspace contracts to its point c",
			By(Normalized, cIn, space, contraction))
	}),
})}

// NearestPointExists — a nonempty closed set of ℝⁿ holds a point nearest
// to any n-vector x: for a point w of the set, its points within
// dist(x, w) of x form a closed bounded set, compact by Heine–Borel, on
// which the continuous distance to x attains its least value, and its
// points farther out are farther than w.
var NearestPointExists = nearestPointExistsThm{family.Add(registry.ProofEntry{
	Name: "NearestPointExists",
	Key:  "prop_4b72c508c77cbb71",
	Reading: "Closedness is load-bearing: an open disc has no point nearest to a " +
		"point of its rim. k ≠ ∅ supplies a first candidate. At n = 0, k = {0} = {x}.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀k:set(num → real). ∀x:(num → real).",
		Hypotheses: []string{
			"closed_in(euclidean_topology(n), k)",
			"k ≠ ∅",
			"vec⟨n⟩(x)",
		},
		Conclusion: "∃y:(num → real). y ∈ k ∧ ∀z:(num → real). z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)",
		Abbrev: Abbrev{
			{Name: "space", Text: "{u:(num → real) | vec⟨n⟩(u)}"},
			{Name: "closedBall", Text: "λr:real. closed_ball(«space», vec_dist⟨n⟩, x, r)"},
		},
	}, func(
		a *Argument,
		n *Expr[Nat],
		k *Expr[Set[Fun[Nat, Real]]],
		x *Vec[Real, DimN],
		closed, nonempty, xVector Fact,
	) {
		_, wIn := a.Obtain(
			"k has a point w",
			"∃w:(num → real). w ∈ k",
			By(nonempty, set_basic.MemberNotEmpty))
		space := a.TermAs[Set[Fun[Nat, Real]]]("«space»")
		distance := a.TermAs[Fun2[Fun[Nat, Real], Fun[Nat, Real], Real]]("vec_dist⟨n⟩")
		radius := a.TermAs[Real]("dist⟨n⟩(x, w)")
		vectors := a.Have(
			"a closed set of ℝⁿ consists of n-vectors",
			"k ⊆ «space»",
			By(closed, topological_space.ClosedInDef, euclidean_topology.EuclideanSpace))
		_, KDef := a.LetAs[Set[Fun[Nat, Real]]](
			"K", "{z:(num → real) | z ∈ k ∧ dist⟨n⟩(x, z) ≤ dist⟨n⟩(x, w)}")

		ballClosed := a.Have(
			"the closed ball about x through w is closed in ℝⁿ",
			"closed_in(euclidean_topology(n), «closedBall»(dist⟨n⟩(x, w)))",
			By(
				xVector,
				metric_space.ClosedBallClosed.At(space, distance, x, radius),
				euclidean.EuclideanMetric.At(n),
				euclidean_topology.EuclideanTopologyDef.At(n)))
		meet := a.Have(
			"K is the part of k in that ball",
			"K = k ∩ «closedBall»(dist⟨n⟩(x, w))",
			Unfold(metric_space.ClosedBallDef),
			BySets(KDef, vectors))
		closedK := a.Have(
			"so K, the meet of two closed sets, is closed",
			"closed_in(euclidean_topology(n), K)",
			By(
				meet,
				closed,
				ballClosed,
				topological_space.InterClosed.At(
					a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)"),
					k,
					a.TermAs[Set[Fun[Nat, Real]]]("«closedBall»(dist⟨n⟩(x, w))")),
				euclidean_topology.EuclideanTopology.At(n)))
		bounded := a.Have(
			"K lies within ‖x‖ + dist(x, w) of the origin",
			"∀z:(num → real). z ∈ K ⇒ ‖z‖_n ≤ ‖x‖_n + dist⟨n⟩(x, w)",
			Derive(func(b *Argument) {
				z := b.VecFixAs[Real, DimN]()
				inK := b.Assume()
				near := b.Have(
					"z is within dist(x, w) of x",
					"dist⟨n⟩(x, z) ≤ dist⟨n⟩(x, w)",
					BySets(KDef, inK))
				triangle := b.Have(
					"the triangle inequality for z = x + (z − x)",
					"‖z‖_n ≤ ‖x‖_n + dist⟨n⟩(x, z)",
					By(
						Normalized,
						euclidean.NormTriangle.At(x, b.VecAs[Real, DimN]("z - x")),
						vec_space.AddSubCancel.Read(real_ring.CommRing).At(x, z),
						euclidean.VecDistDef.At(z, x),
						euclidean.DistSym.At(x, z)))
				b.Show(
					"so ‖z‖ ≤ ‖x‖ + dist(x, w)",
					ByArith(triangle, near))
			}))
		compact := a.Have(
			"closed and bounded, K is compact",
			"compact_in(euclidean_topology(n), K)",
			By(closedK, bounded, euclidean_topology.HeineBorel))
		inhabited := a.Have(
			"K holds w",
			"K ≠ ∅",
			BySets(KDef, wIn, real_order_ring.LessEqRefl.At(radius)))
		distanceContinuous := a.Have(
			"the distance from x is continuous on ℝⁿ",
			"continuous_map(euclidean_topology(n), real_topology, λz:(num → real). dist⟨n⟩(x, z))",
			By(
				xVector,
				real_valued.MetricDistanceContinuous.At(space, distance, x),
				euclidean.EuclideanMetric.At(n),
				euclidean_topology.EuclideanTopologyDef.At(n)))

		y, least := a.Obtain(
			"on the compact K the distance from x attains its least value, at some y",
			"∃y:(num → real). y ∈ K ∧ ∀v:(num → real). v ∈ K ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, v)",
			By(inhabited, compact, distanceContinuous, real_valued.ContinuousCompactMinimum))
		parts := a.Conjuncts(
			least,
			"y lies in K",
			"no point of K is nearer to x than y")
		yParts := a.Have(
			"y is a point of k within dist(x, w) of x",
			"y ∈ k ∧ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, w)",
			BySets(KDef, parts[0]))
		nearest := a.Have(
			"no point of k is nearer to x than y",
			"∀z:(num → real). z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)",
			Derive(func(b *Argument) {
				z := b.VecFixAs[Real, DimN]()
				inside := b.Assume()
				b.Cases(b.Term("dist⟨n⟩(x, z) ≤ dist⟨n⟩(x, w)"))
				b.When(
					"z, within dist(x, w) of x, lies in K, on which y is nearest",
					func(c *Argument, within Fact) {
						c.Show(
							"so y is no farther from x than z",
							BySets(parts[1].At(z), KDef, within, inside))
					})
				b.Otherwise(
					"z, farther from x than w, is farther than y, which is within dist(x, w)",
					func(c *Argument, farther Fact) {
						c.Show(
							"so y is nearer to x than z",
							ByArith(farther, yParts))
					})
			}))
		a.Take(y)
		a.Show(
			"y is a point of k nearest to x",
			By(yParts, nearest))
	}),
})}

// NearestPointVariational — in a convex set, a point is nearest to x
// exactly when every point of the set makes an angle of at least a right
// angle with x at it. Along the segment from y to a point z of the set,
// the squared distance to x is a quadratic in the step t that falls by
// 2t⟪x − y, z − y⟫ and rises by t²‖z − y‖². At t = 1 it is the squared
// distance to z, which an obtuse angle keeps at least ‖x − y‖²; were the
// angle acute, the step t = ⟪x − y, z − y⟫ / (⟪x − y, z − y⟫ + ‖z − y‖²)
// would lie in (0, 1] and reach a point of the set nearer to x than y.
var NearestPointVariational = nearestPointVariationalThm{family.Add(registry.ProofEntry{
	Name: "NearestPointVariational",
	Key:  "prop_fb9d39ded791a129",
	Reading: "The backward direction holds for any set, ‖x − z‖² being ‖x − y‖² − 2⟪x − y, z − " +
		"y⟫ + ‖z − y‖²; convexity carries the forward one. Without it: k = {−1, 1} in ℝ, x = 0, y " +
		"= 1 is nearest, yet ⟪x − y, −1 − y⟫ = 2 > 0. No dimension is asked of k or x: dist⟨n⟩ and " +
		"⟪·, ·⟫_n read the first n coordinates only, and convexity is the same in every dimension.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀k:set(num → real). ∀x y:(num → real).",
		Hypotheses: []string{
			"convex(k)",
			"y ∈ k",
		},
		Conclusion: "(∀z:(num → real). z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)) ⇔ " +
			"∀z:(num → real). z ∈ k ⇒ ⟪x - y, z - y⟫_n ≤ &0",
	}, func(
		a *Argument,
		n *Expr[Nat],
		k *Expr[Set[Fun[Nat, Real]]],
		x, y *Vec[Real, DimN],
		convexK, yIn Fact,
	) {
		expansion := a.Have(
			"along the segment from y to z the squared distance "+
				"to x falls by 2t⟪x − y, z − y⟫ and rises by t²‖z − y‖²",
			"∀z:(num → real). ∀t:real. "+
				"    dist⟨n⟩(x, (&1 - t) • y + t • z) ^ 2 = "+
				"    dist⟨n⟩(x, y) ^ 2 - &2 * t * ⟪x - y, z - y⟫_n + t ^ 2 * ‖z - y‖_n ^ 2",
			Derive(func(b *Argument) {
				z := b.VecFixAs[Real, DimN]()
				t := b.FixAs[Real]()
				b.Show(
					"both sides open by bilinearity into forms of x, y and z, and symmetry "+
						"pairs each cross term with its mirror image under the factor t",
					Simp(
						Fwd(euclidean.VecDistDef),
						Fwd(euclidean.NormPow2),
						Fwd(dot.SubLeft.Read(real_ring.CommRing)),
						Fwd(dot.SubRight.Read(real_ring.CommRing)),
						Fwd(dot.AddLeft.Read(real_ring.CommRing)),
						Fwd(dot.AddRight.Read(real_ring.CommRing)),
						Fwd(dot.SmulLeft.Read(real_ring.CommRing)),
						Fwd(dot.SmulRight.Read(real_ring.CommRing))),
					ByArith(
						Scaled(t, dot.Sym.Read(real_ring.CommRing).At(x, y)),
						Scaled(t, dot.Sym.Read(real_ring.CommRing).At(y, z)),
						Scaled(t, dot.Sym.Read(real_ring.CommRing).At(x, z))))
			}))
		a.Iff()
		a.Forward(
			"were the angle at y acute towards a point z of k, "+
				"a short step from y towards z would come nearer to x",
			func(b *Argument, nearest Fact) {
				z := b.VecFixAs[Real, DimN]()
				zIn := b.Assume()
				acute := b.SupposeNot()
				t, tDef := b.LetAs[Real]("t", "⟪x - y, z - y⟫_n / (⟪x - y, z - y⟫_n + ‖z - y‖_n ^ 2)")
				step := b.Have(
					"the angle being acute and ‖z − y‖² not negative, t is a step in (0, 1]",
					"&0 < t ∧ t ≤ &1",
					ByArith(tDef, acute))
				point := b.Have(
					"so the convex k holds the point at step t from y towards z",
					"(&1 - t) • y + t • z ∈ k",
					By(
						convexK,
						yIn,
						zIn,
						step,
						real_order_ring.LessEqOfLessThan.At(b.TermAs[Real]("&0"), t),
						convex.Segment.At(k)))
				gain := b.Have(
					"y being nearest, that point is no nearer to x: squared and "+
						"set against the expansion at t, the fall is at most the rise",
					"&2 * t * ⟪x - y, z - y⟫_n ≤ t ^ 2 * ‖z - y‖_n ^ 2",
					ByArith(
						nearest.At(b.VecAs[Real, DimN]("(&1 - t) • y + t • z")),
						point,
						expansion.At(z, t),
						euclidean.NormNonneg.At(b.VecAs[Real, DimN]("x - y")),
						euclidean.VecDistDef.At(x, y),
						real_pow.PowMonoBase.At(
							b.TermAs[Real]("dist⟨n⟩(x, y)"),
							b.TermAs[Real]("dist⟨n⟩(x, (&1 - t) • y + t • z)"),
							b.TermAs[Nat]("2"))))
				b.Show(
					"cancelling t leaves 2⟪x − y, z − y⟫ ≤ t‖z − y‖², "+
						"which the choice of t makes less than ⟪x − y, z − y⟫",
					ByArith(gain, step, tDef, acute))
			})
		a.Backward(
			"an obtuse angle at y keeps every point z of k at least as far from x as y",
			func(b *Argument, obtuse Fact) {
				z := b.VecFixAs[Real, DimN]()
				zIn := b.Assume()
				end := b.Have(
					"the segment from y to z ends at z",
					"(&1 - &1) • y + &1 • z = z",
					Funext(),
					Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef)),
					ByArith())
				farther := b.Have(
					"read at t = 1, the expansion and the obtuse angle put "+
						"the squared distance to z above ‖x − y‖² + ‖z − y‖²",
					"dist⟨n⟩(x, y) ^ 2 + ‖z - y‖_n ^ 2 ≤ dist⟨n⟩(x, z) ^ 2",
					ByArith(expansion.At(z, b.TermAs[Real]("&1")), end, obtuse.At(z), zIn))
				b.Show(
					"were z nearer than y, squaring its nonnegative distance would put it below ‖x − y‖²",
					ByArith(
						farther,
						euclidean.NormNonneg.At(b.VecAs[Real, DimN]("x - z")),
						euclidean.VecDistDef.At(x, z),
						real_pow.PowMonoBaseStrict.At(
							b.TermAs[Real]("dist⟨n⟩(x, z)"),
							b.TermAs[Real]("dist⟨n⟩(x, y)"),
							b.TermAs[Nat]("2"))))
			})
	}),
})}

// NearestPointNonexpansive — in a convex set, nearest points are no farther
// apart than the vectors they are nearest to.
var NearestPointNonexpansive = nearestPointNonexpansiveThm{family.Add(registry.ProofEntry{
	Name: "NearestPointNonexpansive",
	Key:  "prop_3a298c64ab2c7055",
	Reading: "Convexity is load-bearing, through NearestPointVariational. Without " +
		"it: k = {−1, 1} in ℝ, x = −ε, x' = ε, y = −1, y' = 1 gives dist(y, y') = 2 > 2ε.",
	Deps: []registry.EntryLike{NearestPointVariational, euclidean.CauchySchwarz, euclidean.NormPow2},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀k:set(num → real). ∀x x' y y':(num → real).",
		Hypotheses: []string{
			"convex(k)",
			"k ⊆ {u:(num → real) | vec⟨n⟩(u)}",
			"vec⟨n⟩(x)",
			"vec⟨n⟩(x')",
			"y ∈ k",
			"y' ∈ k",
			"∀z:(num → real). z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)",
			"∀z:(num → real). z ∈ k ⇒ dist⟨n⟩(x', y') ≤ dist⟨n⟩(x', z)",
		},
		Conclusion: "dist⟨n⟩(y, y') ≤ dist⟨n⟩(x, x')",
	},
		"NearestPointVariational at y with z = y' and at y' with z = y gives ⟪x − y, y' − y⟫ ≤ 0 and "+
			"⟪x' − y', y − y'⟫ ≤ 0; adding, ‖y − y'‖² ≤ ⟪x − x', y − y'⟫ ≤ ‖x − x'‖ ‖y − y'‖ (CauchySchwarz)"),
})}

// ClosedConvexRetract — a nonempty closed convex set of ℝⁿ is a retract of
// ℝⁿ.
var ClosedConvexRetract = closedConvexRetractThm{family.Add(registry.ProofEntry{
	Name: "ClosedConvexRetract",
	Key:  "prop_644016cbbb846a31",
	Reading: "Convexity makes the nearest point unique and continuous — the " +
		"circle is no retract of ℝ²; closedness is needed, a retract of a Hausdorff " +
		"space being closed; k ≠ ∅ is needed, ℝⁿ being nonempty even at n = 0.",
	Deps: []registry.EntryLike{
		NearestPointExists,
		NearestPointNonexpansive,
		continuous.RetractOfDef,
		euclidean_topology.OpenIff,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀k:set(num → real).",
		Hypotheses: []string{
			"closed_in(euclidean_topology(n), k)",
			"convex(k)",
			"k ≠ ∅",
		},
		Conclusion: "retract_of(euclidean_topology(n), k)",
	},
		"the retraction sends each n-vector to its nearest point in k (NearestPointExists), "+
			"which is unique and moves no farther than its argument (NearestPointNonexpansive at "+
			"x' = x and in general), so it is continuous; a point of k is its own nearest point"),
})}
