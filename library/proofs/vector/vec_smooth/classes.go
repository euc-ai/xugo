// classes.go — the classes Cᵏ: they decrease with k, pass to subsets, see
// a function only on an open set, and are closed under sums, finite sums,
// products and composition. Each closure is an induction on k for all
// functions at once, the partial derivatives of the result being built
// from those of the parts one class lower.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ContinuouslyDifferentiableMono — a function of class Cᵏ is of every
// lower class.
var ContinuouslyDifferentiableMono = continuouslyDifferentiableMonoThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableMono",
	Key:  "prop_6d11ef561a35900d",
	Deps: []registry.EntryLike{ContinuouslyDifferentiableOnDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀j k:num. ∀g:((num → real) → real).",
		Hypotheses: []string{
			"j ≤ k",
			"vec_continuously_differentiable_on⟨n⟩(U, k, g)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, j, g)",
	},
		"class k + 1 gives class k, by induction on k for all g at once: at k = 0 continuity "+
			"is the first clause of class 1, and at k + 1 the partial derivatives drop from "+
			"class k + 1 to class k by the induction hypothesis; then induction on k − j"),
})}

// ContinuouslyDifferentiableLocallyLipschitz — a C¹ map is Lipschitz on
// a sufficiently small open neighbourhood of each point of its open domain.
var ContinuouslyDifferentiableLocallyLipschitz = continuouslyDifferentiableLocallyLipschitzThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableLocallyLipschitz",
	Key:  "prop_337cc4eb32ab093b",
	Deps: []registry.EntryLike{
		JacobianDerivative,
		vec_derivative.MeanValueInequality,
		euclidean_topology.OpenIff,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀U:set(num → real). ∀f:((num → real) → (num → real)). ∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀y:(num → real). y ∈ U ⇒ vec⟨m⟩(f(y))",
			"∀i:num. i < m ⇒ vec_continuously_differentiable_on⟨n⟩(U, 1, λy:(num → real). f(y)(i))",
			"x ∈ U",
		},
		Conclusion: "∃V:set(num → real). " +
			"    V ∈ euclidean_topology(n) ∧ " +
			"    x ∈ V ∧ " +
			"    V ⊆ U ∧ " +
			"    lipschitz_map(V, vec_dist⟨n⟩, {y:num → real | vec⟨m⟩(y)}, vec_dist⟨m⟩, f)",
	},
		"Choose a ball inside U (euclidean_topology.OpenIff). Continuity of the finitely "+
			"many first partials bounds every Jacobian entry on a smaller ball, hence bounds "+
			"its operator norm there; JacobianDerivative and vec_derivative.MeanValueInequality "+
			"along segments in this convex ball give the Lipschitz bound. For n = 0 the domain "+
			"has at most one point, and for m = 0 the carrier-valued map is constant."),
})}

// ContinuouslyDifferentiableSubset — a function of class Cᵏ on U is of
// class Cᵏ on every subset of U.
var ContinuouslyDifferentiableSubset = continuouslyDifferentiableSubsetThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableSubset",
	Key:  "prop_bbc9f1b0c489e824",
	Reading: "No openness is asked: every clause of the definition " +
		"is asked point by point on the set, of functions on all of ℝⁿ.",
	Deps: []registry.EntryLike{ContinuouslyDifferentiableOnDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V:((num → real) → bool). ∀k:num. ∀g:((num → real) → real).",
		Hypotheses: []string{
			"V ⊆ U",
			"vec_continuously_differentiable_on⟨n⟩(U, k, g)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(V, k, g)",
	},
		"induction on k for all g at once, each clause of "+
			"the definition being asked at the points of the set"),
})}

// ContinuouslyDifferentiableCongruence — on an open set the class of a
// function is read off its values there: U holds a ball about each of its
// points, so two functions agreeing on U are continuous at the same points
// of U and have the same partial derivatives there, and an induction on the
// class for all pairs of functions at once carries it from one to the
// other, their partial derivatives agreeing on U in turn.
var ContinuouslyDifferentiableCongruence = continuouslyDifferentiableCongruenceThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableCongruence",
	Key:  "prop_5e0f3823211215b6",
	Reading: "U open is load-bearing: on U = {x | vec⟨1⟩(x) ∧ x(0) ≤ 0}, g = 0 and h(x) " +
		"= max(x(0), 0) agree, g is of class 1 there, and h has no partial derivative at 0.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀k:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀x:(num → real). x ∈ U ⇒ g(x) = h(x)",
			"vec_continuously_differentiable_on⟨n⟩(U, k, g)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, k, h)",
	},
		func(a *Argument, n *Expr[Nat], U *Expr[Set[Fun[Nat, Real]]], isOpen Fact) {
			continuity := a.Have(
				"continuity at a point of U reads the function on U alone: an open set "+
					"about x that g carries into v, cut down to U, is one h carries into v",
				Statement{
					Binders: "∀g h:((num → real) → real). ∀x:(num → real).",
					Hypotheses: []string{
						"∀y:(num → real). y ∈ U ⇒ g(y) = h(y)",
						"x ∈ U",
						"continuous_map_at(euclidean_topology(n), real_topology, g, x)",
					},
					Conclusion: "continuous_map_at(euclidean_topology(n), real_topology, h, x)",
				},
				Derive(func(b *Argument) {
					b.Fix("g")
					b.Fix("h")
					x := b.FixAs[Fun[Nat, Real]]("x")
					given := b.Conjuncts(
						b.Assume(),
						"g and h agree on U",
						"x is a point of U",
						"g is continuous at x")
					agree, inU := given[0], given[1]
					atX := b.Conjuncts(
						b.Unfolded(given[2], continuous.ContinuousMapAtDef),
						"x is a point of ℝⁿ",
						"g(x) is a point of ℝ",
						"every open set about g(x) receives an open set about x")
					receives := b.Have(
						"every open set v about h(x) receives the open set about x that g carries into v, cut down to U",
						Statement{
							Binders:    "∀v:set(real).",
							Hypotheses: []string{"v ∈ real_topology", "h(x) ∈ v"},
							Conclusion: "∃u:set(num → real). " +
								"    u ∈ euclidean_topology(n) ∧ x ∈ u ∧ ∀y:(num → real). y ∈ u ⇒ h(y) ∈ v",
						},
						Derive(func(c *Argument) {
							v := c.FixAs[Set[Real]]("v")
							around := c.Assume()
							u, carried := c.ObtainAs[Set[Fun[Nat, Real]]](
								"v holds g(x) = h(x), so some open u about x is carried by g into v",
								"∃u:set(num → real). u ∈ euclidean_topology(n) ∧ x ∈ u ∧ ∀y:(num → real). y ∈ u ⇒ g(y) ∈ v",
								By(agree.At(x), inU, around, atX[2].At(v)))
							c.Take(c.TermAs[Set[Fun[Nat, Real]]]("u ∩ U"))
							c.Show(
								"u ∩ U is open, holds x, and on it h(y) = g(y) lies in v",
								By(
									agree,
									isOpen,
									inU,
									around,
									carried,
									euclidean_topology.EuclideanTopology.At(n),
									topological_space.InterOpen.At(c.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)"), u, U),
									set_basic.InInter))
						}))
					b.Show(
						"so h, which takes g's value at x, is continuous at x",
						Simp(Fwd(continuous.ContinuousMapAtDef)),
						By(atX[0], atX[1], agree.At(x), inU, receives))
				}))
			partials := a.Have(
				"so do the partial derivatives: a ball about x inside U is one on which g and h agree",
				Statement{
					Binders:    "∀g h:((num → real) → real). ∀j:num. ∀x:(num → real).",
					Hypotheses: []string{"∀y:(num → real). y ∈ U ⇒ g(y) = h(y)", "j < n", "x ∈ U"},
					Conclusion: "(∀d:real. partial_derivative_at(g, j, x, d) ⇔ partial_derivative_at(h, j, x, d)) ∧ " +
						"partial_derivative(g, j, x) = partial_derivative(h, j, x)",
				},
				Derive(func(b *Argument) {
					g := b.FixAs[Fun[Fun[Nat, Real], Real]]("g")
					h := b.FixAs[Fun[Fun[Nat, Real], Real]]("h")
					j := b.FixAs[Nat]("j")
					x := b.VecFixAs[Real, DimN]("x")
					given := b.Conjuncts(
						b.Assume(),
						"g and h agree on U",
						"j is below n",
						"x is a point of U")
					agree, below, inU := given[0], given[1], given[2]
					xVec := b.Have(
						"x is an n-vector, as every point of the open set U",
						"vec⟨n⟩(x)",
						By(isOpen, inU, euclidean_topology.OpenIff))
					r, ball := b.ObtainAs[Real](
						"and some ball about x lies in U",
						"∃r:real. &0 < r ∧ ∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∈ U",
						By(isOpen, inU, euclidean_topology.OpenIff))
					radius := b.Conjuncts(
						ball,
						"the radius is positive",
						"the ball lies in U")
					near := b.Have(
						"g and h agree on that ball",
						"∀y:(num → real). vec⟨n⟩(y) ∧ ‖y - x‖_n < r ⇒ g(y) = h(y)",
						Derive(func(c *Argument) {
							y := c.VecFixAs[Real, DimN]("y")
							within := c.Assume()
							c.Show(
								"‖y − x‖ is the distance from x to y, so y lies in the ball, hence in U",
								By(within, euclidean.VecDistDef.At(y, x), euclidean.DistSym.At(x, y), radius[1].At(y), agree.At(y)))
						}))
					b.Show(
						"two functions agreeing on a ball about x have the same partial derivatives at x",
						By(below, radius[0], near, PartialDerivativeLocal.At(g, h, j, proof.Inhabit(x, xVec), r)))
				}))
			a.Induct("k")
			a.Base(
				"class 0 is continuity at the points of U, which h has where g has it",
				Simp(Fwd(ContinuouslyDifferentiableOnDef)),
				By(continuity))
			a.Step(
				"at class k + 1, h has g's continuity and partial derivatives on "+
					"U, and each ∂ⱼh, agreeing with ∂ⱼg on U, is of class k by induction",
				func(b *Argument, ih Fact) {
					g := b.FixAs[Fun[Fun[Nat, Real], Real]]("g")
					h := b.FixAs[Fun[Fun[Nat, Real], Real]]("h")
					given := b.Conjuncts(
						b.Assume(),
						"g and h agree on U",
						"g is of class k + 1 on U")
					agree := given[0]
					classG := b.Conjuncts(
						b.Simplified(given[1], Fwd(ContinuouslyDifferentiableOnDef)),
						"g is continuous at every point of U",
						"g has its partial derivatives at every point of U",
						"and each ∂ⱼg is of class k on U")
					hContinuous := b.Have(
						"so h is continuous at every point of U",
						"∀x:(num → real). x ∈ U ⇒ continuous_map_at(euclidean_topology(n), real_topology, h, x)",
						By(continuity, agree, classG[0]))
					hPartials := b.Have(
						"and has g's partial derivatives there",
						"∀j:num. j < n ⇒ ∀x:(num → real). x ∈ U ⇒ ∃d:real. partial_derivative_at(h, j, x, d)",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							x := c.FixAs[Fun[Nat, Real]]("x")
							inU := c.Assume()
							c.Show(
								"a partial derivative of g at x along j is one of h",
								By(partials.At(g, h, j, x), agree, below, inU, classG[1].At(j, x)))
						}))
					hPartialClass := b.Have(
						"each ∂ⱼh is of class k on U, agreeing there with ∂ⱼg",
						"∀j:num. j < n ⇒ vec_continuously_differentiable_on⟨n⟩(U, k, partial_derivative(h, j))",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							c.Show(
								"the induction hypothesis at ∂ⱼg and ∂ⱼh, the two agreeing on U",
								By(
									ih.At(
										c.TermAs[Fun[Fun[Nat, Real], Real]]("partial_derivative(g, j)"),
										c.TermAs[Fun[Fun[Nat, Real], Real]]("partial_derivative(h, j)")),
									partials,
									agree,
									below,
									classG[2].At(j)))
						}))
					b.Show(
						"so h is of class k + 1 on U",
						Simp(Fwd(ContinuouslyDifferentiableOnDef)),
						By(hContinuous, hPartials, hPartialClass))
				})
		}),
})}

// ContinuouslyDifferentiableAdd — a sum of functions of class Cᵏ is of
// class Cᵏ.
var ContinuouslyDifferentiableAdd = continuouslyDifferentiableAddThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableAdd",
	Key:  "prop_2af945b3a2baff15",
	Deps: []registry.EntryLike{
		ContinuouslyDifferentiableOnDef,
		PartialDerivativeAdd,
		PartialDerivativeValue,
		ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀k:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_continuously_differentiable_on⟨n⟩(U, k, g)",
			"vec_continuously_differentiable_on⟨n⟩(U, k, h)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, k, λx:(num → real). g(x) + h(x))",
	},
		"induction on k for all g, h at once: a sum of functions continuous at x is; at k + 1, ∂ⱼ(g + "+
			"h) = ∂ⱼg + ∂ⱼh on U (PartialDerivativeAdd, PartialDerivativeValue), of class k by the "+
			"induction hypothesis, and ContinuouslyDifferentiableCongruence carries the class to ∂ⱼ(g + h)"),
})}

// ContinuouslyDifferentiableSum — a finite sum of functions of class Cᵏ
// is of class Cᵏ.
var ContinuouslyDifferentiableSum = continuouslyDifferentiableSumThm{family.Add(registry.ProofEntry{
	Name:    "ContinuouslyDifferentiableSum",
	Key:     "prop_edd7847dc2ba22c",
	Reading: "At N = 0 the sum is the zero function, of every class on an open set.",
	Deps:    []registry.EntryLike{ContinuouslyDifferentiableAdd, ContinuouslyDifferentiableCongruence},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀k N:num. ∀h:(num → (num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀i:num. i < N ⇒ vec_continuously_differentiable_on⟨n⟩(U, k, h(i))",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, k, λx:(num → real). Σ_{i<N} h(i)(x))",
	},
		"induction on N: the empty sum is the constant 0, whose partial derivatives are 0 again "+
			"(induction on k), and the sum to N + 1 is the sum to N plus h(N) (ContinuouslyDifferentiableAdd)"),
})}

// ContinuouslyDifferentiableMul — a product of functions of class Cᵏ is
// of class Cᵏ.
var ContinuouslyDifferentiableMul = continuouslyDifferentiableMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuouslyDifferentiableMul",
	Key:  "prop_ad1a26a60b603f8d",
	Deps: []registry.EntryLike{
		ContinuouslyDifferentiableOnDef,
		PartialDerivativeMul,
		PartialDerivativeValue,
		ContinuouslyDifferentiableMono,
		ContinuouslyDifferentiableAdd,
		ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀k:num. ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_continuously_differentiable_on⟨n⟩(U, k, g)",
			"vec_continuously_differentiable_on⟨n⟩(U, k, h)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, k, λx:(num → real). g(x) * h(x))",
	},
		"induction on k for all g, h at once: at k + 1, ∂ⱼ(gh) = ∂ⱼg·h + g·∂ⱼh "+
			"on U (PartialDerivativeMul, PartialDerivativeValue); g and h drop to "+
			"class k (ContinuouslyDifferentiableMono), each product is of class k by "+
			"the induction hypothesis, their sum by ContinuouslyDifferentiableAdd, "+
			"and ContinuouslyDifferentiableCongruence carries the class to ∂ⱼ(gh)"),
})}

// ContinuouslyDifferentiableCompose — a function of class Cᵏ of functions
// of class Cᵏ is of class Cᵏ.
var ContinuouslyDifferentiableCompose = continuouslyDifferentiableComposeThm{family.Add(registry.ProofEntry{
	Name:    "ContinuouslyDifferentiableCompose",
	Key:     "prop_a72a9ddf967ca59f",
	Reading: "V open in ℝᵐ makes each f(x) an m-vector, where g is read.",
	Deps: []registry.EntryLike{
		ContinuouslyDifferentiableOnDef,
		PartialDerivativeChain,
		PartialDerivativeValue,
		ContinuouslyDifferentiableMono,
		ContinuouslyDifferentiableMul,
		ContinuouslyDifferentiableSum,
		ContinuouslyDifferentiableCongruence,
		euclidean_topology.ContinuousIffCoordinates,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U V:((num → real) → bool). " +
			"∀k:num. " +
			"∀f:((num → real) → num → real). " +
			"∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(m)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"∀i:num. i < m ⇒ vec_continuously_differentiable_on⟨n⟩(U, k, λx:(num → real). f(x)(i))",
			"vec_continuously_differentiable_on⟨m⟩(V, k, g)",
		},
		Conclusion: "vec_continuously_differentiable_on⟨n⟩(U, k, λx:(num → real). g(f(x)))",
	},
		"induction on k for all g at once. At k = 0, f is continuous at each point of U as a map into "+
			"ℝᵐ, its coordinates being so (euclidean_topology.ContinuousIffCoordinates read at a point), "+
			"and g at its value. At k + 1, PartialDerivativeChain writes ∂ⱼ(g ∘ f) = Σ_{i<m} (∂ᵢg ∘ "+
			"f)·∂ⱼfᵢ on U; ∂ᵢg ∘ f is of class k by the induction hypothesis at ∂ᵢg, with f's coordinates "+
			"dropped to class k (ContinuouslyDifferentiableMono), and Mul, Sum and Congruence finish"),
})}
