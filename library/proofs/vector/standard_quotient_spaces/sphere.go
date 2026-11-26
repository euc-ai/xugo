// sphere.go — the sphere S^(n + 1) as the ball D^(n + 1) with its boundary
// sphere Sⁿ collapsed to a point. The collapse map sends a point x of norm r
// to (2√(1 − r²)·x, 2r² − 1): it carries the ball onto the sphere, the
// boundary to the north pole and the open ball one-to-one onto the rest.

package standard_quotient_spaces

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CollapseOnSphere — the collapse map carries the ball D^(n + 1) into the
// sphere S^(n + 1). At a point x of norm r ≤ 1 its coordinates below n + 1
// are those of x scaled by 2√(1 − r²), its coordinate n + 1 is 2r² − 1, and
// past that it is 0; so the form at the image is 4(1 − r²)·r² + (2r² − 1)²,
// which is 1.
var CollapseOnSphere = collapseOnSphereThm{family.Add(registry.ProofEntry{
	Name: "CollapseOnSphere",
	Key:  "prop_3abb2b89e540b950",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x:(num → real).",
		Hypotheses: []string{
			"x ∈ euclidean_ball(n + 1)",
		},
		Conclusion: "«collapse»(x) ∈ euclidean_sphere(n + 1)",
		Abbrev: Abbrev{
			{Name: "collapse", Text: "λx:(num → real). λi:num. " +
				"    COND(i = n + 1, &2 * ‖x‖_(n + 1) ^ 2 - &1, &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i))"},
		},
	}, func(a *Argument, n *Expr[Nat], x *Expr[Fun[Nat, Real]], inBall Fact) {
		ball := a.Conjuncts(
			a.Unfolded(inBall, euclidean_topology.EuclideanBallDef),
			"x is a vector of ℝ^(n + 1)",
			"of norm at most 1")
		point := a.VecAt[Real](a.TermAs[Nat]("n + 1"), "x")
		image := a.VecAt[Real](a.TermAs[Nat]("n + 1 + 1"), "«collapse»(x)")
		radius := a.TermAs[Real]("‖x‖_(n + 1) ^ 2")
		inside := a.Have(
			"1 − r² is not negative, the norm r of x lying in ⟦0, 1⟧",
			"&0 ≤ &1 - ‖x‖_(n + 1) ^ 2",
			ByArith(ball[1], euclidean.NormNonneg.At(point)))
		root := a.Have(
			"so √(1 − r²) squares to 1 − r²",
			"real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) ^ 2 = &1 - ‖x‖_(n + 1) ^ 2",
			By(inside, real_sqrt.SqrtPowTwo))
		identity := a.Have(
			"(2√(1 − r²))²·r² + (2r² − 1)² = 4(1 − r²)r² + (2r² − 1)² = 1",
			"&2 * "+
				"real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * "+
				"(&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)) * "+
				"‖x‖_(n + 1) ^ 2 + "+
				"(&2 * ‖x‖_(n + 1) ^ 2 - &1) * (&2 * ‖x‖_(n + 1) ^ 2 - &1) = "+
				"&1",
			ByArith(Scaled(radius, root)))
		below := a.Have(
			"below n + 1 the squared coordinates of the image are those of x times (2√(1 − r²))²",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < n + 1",
				},
				Conclusion: "«collapse»(x)(i) * «collapse»(x)(i) = " +
					"&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * (&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)) * (x(i) * x(i))",
			},
			ByArith())
		belowRange := a.TermAs[Set[Nat]]("{i:num | i < n + 1}")
		scale := a.TermAs[Real](
			"&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * (&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2))")
		sumBelow := a.Have(
			"so their sum is (2√(1 − r²))² times the form at x",
			"Σ_{i<n + 1} «collapse»(x)(i) * «collapse»(x)(i) = "+
				"&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * (&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)) * ⟪x, x⟫_(n + 1)",
			ByArith(
				below,
				real_sum.Congruence.At(
					belowRange,
					a.TermAs[Fun[Nat, Real]]("λi:num. «collapse»(x)(i) * «collapse»(x)(i)"),
					a.TermAs[Fun[Nat, Real]](
						"λi:num. "+
							"    &2 * "+
							"    real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * "+
							"    (&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)) * "+
							"    (x(i) * x(i))")),
				real_sum.ScalarLeft.At(scale, a.TermAs[Fun[Nat, Real]]("λi:num. x(i) * x(i)"), belowRange),
				euclidean.DotIsSum.At(point, point)))
		steps := a.Conjuncts(
			real_sum.BelowClauses.At(a.TermAs[Fun[Nat, Real]]("λi:num. «collapse»(x)(i) * «collapse»(x)(i)")),
			"the sum over no index is 0",
			"one index more adds its term")
		successor := a.Have(
			"n + 1 + 1 is the successor of n + 1",
			"suc(n + 1) = n + 1 + 1",
			ByArith())
		square := a.Have(
			"so the form at the image is (2√(1 − r²))²·r² + (2r² − 1)², which is 1",
			"⟪«collapse»(x), «collapse»(x)⟫_(n + 1 + 1) = &1",
			ByArith(
				steps[1].At(a.TermAs[Nat]("n + 1")),
				successor,
				sumBelow,
				identity,
				euclidean.DotIsSum.At(image, image),
				euclidean.NormPow2.At(point)))
		one := a.TermAs[Real]("&1")
		norm := a.Have(
			"so the image has norm 1",
			"‖«collapse»(x)‖_(n + 1 + 1) = &1",
			ByArith(square, euclidean.VecNormDef.At(image), real_sqrt.SqrtUnique.At(one, one)))
		vanish := a.Unfolded(ball[0], vec_space.VecDef)
		vector := a.Have(
			"the image is a vector of ℝ^(n + 2): past n + 1 its "+
				"coordinates are multiples of those of x, which are 0",
			"vec⟨n + 1 + 1⟩(«collapse»(x))",
			Unfold(vec_space.VecDef),
			a.ForEach(func(i *Expr[Nat]) Action { return ByArith(vanish.At(i)) }))
		a.Show(
			"so the image lies on the unit sphere S^(n + 1)",
			Simp(Fwd(euclidean_topology.EuclideanSphereDef)),
			By(norm, vector))
	}),
})}

// CollapseFibres — two points of the ball D^(n + 1) have the same image
// under the collapse map exactly when both lie on its boundary sphere Sⁿ or
// they are equal. Equal images have equal last coordinates 2r² − 1, so the
// two points have one norm r; on the boundary both lie on Sⁿ, and inside it
// the factor 2√(1 − r²) is positive and scales the other coordinates of the
// two points alike. Conversely every point of Sⁿ goes to the north pole.
var CollapseFibres = collapseFibresThm{family.Add(registry.ProofEntry{
	Name: "CollapseFibres",
	Key:  "prop_d4da099858f77b81",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x y:(num → real).",
		Hypotheses: []string{
			"x ∈ euclidean_ball(n + 1)",
			"y ∈ euclidean_ball(n + 1)",
		},
		Conclusion: "«collapse»(x) = «collapse»(y) ⇔ " +
			"x ∈ euclidean_sphere(n) ∧ y ∈ euclidean_sphere(n) ∨ x = y",
		Abbrev: Abbrev{
			{Name: "collapse", Text: "λx:(num → real). λi:num. " +
				"    COND(i = n + 1, &2 * ‖x‖_(n + 1) ^ 2 - &1, &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i))"},
		},
	}, func(a *Argument, n *Expr[Nat], x, y *Expr[Fun[Nat, Real]], xIn, yIn Fact) {
		xBall := a.Conjuncts(
			a.Unfolded(xIn, euclidean_topology.EuclideanBallDef),
			"x is a vector of ℝ^(n + 1)",
			"of norm at most 1")
		yBall := a.Conjuncts(
			a.Unfolded(yIn, euclidean_topology.EuclideanBallDef),
			"y is a vector of ℝ^(n + 1)",
			"of norm at most 1")
		dimension := a.TermAs[Nat]("n + 1")
		xPoint := a.VecAt[Real](dimension, "x")
		yPoint := a.VecAt[Real](dimension, "y")
		boundary := a.Have(
			"a vector of ℝ^(n + 1) lies on Sⁿ exactly when its norm is 1",
			"(x ∈ euclidean_sphere(n) ⇔ ‖x‖_(n + 1) = &1) ∧ (y ∈ euclidean_sphere(n) ⇔ ‖y‖_(n + 1) = &1)",
			Simp(Fwd(euclidean_topology.EuclideanSphereDef)),
			By(xBall[0], yBall[0]))
		a.Iff()
		a.Backward(
			"two points of Sⁿ both go to the north pole, and a point goes where it goes",
			func(b *Argument, either Fact) {
				b.Do(either.SplitDisj(
					LeftHolds(
						"both on Sⁿ: at norm 1 the image is (0, …, 0, 1)",
						Given(func(c *Argument, both Fact) {
							norms := c.Have(
								"both have norm 1",
								"‖x‖_(n + 1) = &1 ∧ ‖y‖_(n + 1) = &1",
								By(boundary, both))
							c.Show(
								"so both images are (0, …, 0, 1), √0 being 0",
								ByArith(norms, real_sqrt.SqrtUnique.At(c.TermAs[Real]("&1 - &1 ^ 2"), c.TermAs[Real]("&0"))))
						})),
					RightHolds(
						"x = y: the same point has the same image",
						Given(func(c *Argument, same Fact) {
							c.Show(
								"rewrite y as x",
								By(Normalized, same))
						}))))
			})
		a.Forward(
			"equal images have equal last coordinates, so x and y have one norm",
			func(b *Argument, equal Fact) {
				last := b.Have(
					"the last coordinates agree, 2‖x‖² − 1 = 2‖y‖² − 1",
					"&2 * ‖x‖_(n + 1) ^ 2 - &1 = &2 * ‖y‖_(n + 1) ^ 2 - &1",
					By(equal))
				forms := b.Have(
					"so the forms at x and y agree",
					"⟪x, x⟫_(n + 1) = ⟪y, y⟫_(n + 1)",
					ByArith(last, euclidean.NormPow2.At(xPoint), euclidean.NormPow2.At(yPoint)))
				norms := b.Have(
					"and so do the norms, their roots",
					"‖x‖_(n + 1) = ‖y‖_(n + 1)",
					By(forms, euclidean.VecNormDef.At(xPoint), euclidean.VecNormDef.At(yPoint)))
				inside := b.Unless(
					b.Term("‖x‖_(n + 1) = &1"),
					"on the boundary both have norm 1, so both lie on Sⁿ",
					Given(func(c *Argument, onBoundary Fact) {
						c.Show(
							"both lie on Sⁿ",
							By(onBoundary, norms, boundary))
					}))
				positive := b.Have(
					"inside the boundary the factor √(1 − ‖x‖²) is positive",
					"&0 < real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)",
					ByArith(
						inside,
						xBall[1],
						euclidean.NormNonneg.At(xPoint),
						real_sqrt.SqrtPos.At(b.TermAs[Real]("&1 - ‖x‖_(n + 1) ^ 2"))))
				xVanish := b.Unfolded(xBall[0], vec_space.VecDef)
				yVanish := b.Unfolded(yBall[0], vec_space.VecDef)
				same := b.Have(
					"so x = y, coordinate by coordinate",
					"x = y",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						notLast := c.Unless(
							c.Term("i = n + 1"),
							"at n + 1 both coordinates are 0",
							Given(func(d *Argument, atLast Fact) {
								last := d.TermAs[Nat]("n + 1")
								d.Show(
									"x and y are vectors of ℝ^(n + 1)",
									atLast.Rw(),
									ByArith(xVanish.At(last), yVanish.At(last)))
							}))
						scaled := c.Have(
							"elsewhere the images are x(i) and y(i) scaled by the one factor 2√(1 − ‖x‖²)",
							"&2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i) = &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * y(i)",
							By(notLast, equal, norms))
						c.Show(
							"so x(i) = y(i), the factor being positive",
							ByArith(scaled, positive))
					}))
				b.Show(
					"x = y",
					By(Normalized, same))
			})
	}),
})}

// CollapseOnto — the collapse map carries the ball D^(n + 1) onto the
// sphere S^(n + 1). Its values lie on the sphere (CollapseOnSphere). A point
// u of the sphere with last coordinate s has ⟪u, u⟫ = 1 − s² below n + 1.
// At the north pole, s = 1, the other coordinates of u vanish and u is the
// image of a boundary point, the first basis vector. Elsewhere s < 1, and u
// is the image of w, its first n + 1 coordinates divided by c = √(2 − 2s):
// then 2‖w‖² = 1 + s, so the last coordinate of the image is s, and its
// factor 2√(1 − ‖w‖²) is c again, which scales w back to u.
var CollapseOnto = collapseOntoThm{family.Add(registry.ProofEntry{
	Name: "CollapseOnto",
	Key:  "prop_d68e2b754d3092b6",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "image(«collapse», euclidean_ball(n + 1)) = euclidean_sphere(n + 1)",
		Abbrev: Abbrev{
			{Name: "collapse", Text: "λx:(num → real). λi:num. " +
				"    COND(i = n + 1, &2 * ‖x‖_(n + 1) ^ 2 - &1, &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i))"},
		},
	}, func(a *Argument, n *Expr[Nat]) {
		type point = Fun[Nat, Real]
		collapse := a.TermAs[Fun[point, point]]("«collapse»")
		ball := a.TermAs[Set[point]]("euclidean_ball(n + 1)")
		low := a.TermAs[Nat]("n + 1")
		high := a.TermAs[Nat]("n + 1 + 1")
		one := a.TermAs[Real]("&1")
		zero := a.TermAs[Real]("&0")
		into := a.Have(
			"the collapse map carries the ball into the sphere",
			"image(«collapse», euclidean_ball(n + 1)) ⊆ euclidean_sphere(n + 1)",
			By(CollapseOnSphere, set_image.ImageSubsetIff))
		onto := a.Have(
			"every point u of the sphere is the image of a point of the ball",
			"∀u:(num → real). u ∈ euclidean_sphere(n + 1) ⇒ u ∈ image(«collapse», euclidean_ball(n + 1))",
			Derive(func(b *Argument) {
				b.FixAs[point]("u")
				onSphere := b.Assume()
				sphere := b.Conjuncts(
					b.Unfolded(onSphere, euclidean_topology.EuclideanSphereDef),
					"u is a vector of ℝ^(n + 2)",
					"of norm 1")
				whole := b.VecAt[Real](high, "u")
				head := b.VecAt[Real](low, "u")
				steps := b.Conjuncts(
					real_sum.BelowClauses.At(b.TermAs[point]("λi:num. u(i) * u(i)")),
					"the sum over no index is 0",
					"one index more adds its term")
				successor := b.Have(
					"n + 1 + 1 is the successor of n + 1",
					"suc(n + 1) = n + 1 + 1",
					ByArith())
				split := b.Have(
					"the form at u is its form below n + 1 plus the square of its last coordinate s, and it is 1",
					"⟪u, u⟫_(n + 1) + u(n + 1) * u(n + 1) = &1",
					ByArith(
						steps[1].At(low),
						successor,
						sphere[1],
						euclidean.DotIsSum.At(whole, whole),
						euclidean.DotIsSum.At(head, head),
						euclidean.NormPow2.At(whole)))
				vanish := b.Unfolded(sphere[0], vec_space.VecDef)
				b.Cases(b.Term("u(n + 1) = &1"))
				b.When(
					"at the north pole u is the image of the first basis vector, a point of the boundary",
					func(c *Argument, north Fact) {
						flat := c.Have(
							"the form at u below n + 1 is 0, so u has norm 0 there",
							"‖u‖_(n + 1) = &0",
							ByArith(
								north,
								split,
								euclidean.VecNormDef.At(head),
								real_sqrt.SqrtUnique.At(c.TermAs[Real]("⟪u, u⟫_(n + 1)"), zero)))
						basis := c.VecAt[Real](low, "basis_vector(0)")
						basisNorm := c.Have(
							"the first basis vector, 0 being below n + 1, has norm 1",
							"‖basis_vector(0)‖_(n + 1) = &1",
							ByArith(euclidean.NormBasisVector.At(low, c.TermAs[Nat]("0"))))
						basisVector := c.Have(
							"it is a vector of ℝ^(n + 1), its coordinates past 0 being 0",
							"vec⟨n + 1⟩(basis_vector(0))",
							Unfold(vec_space.VecDef),
							c.ForEach(func(i *Expr[Nat]) Action {
								return ByArith(vec_space.BasisVectorDef.At(zero, one, c.TermAs[Nat]("0"), i))
							}))
						inBall := c.Have(
							"so it lies in the ball",
							"basis_vector(0) ∈ euclidean_ball(n + 1)",
							Simp(Fwd(euclidean_topology.EuclideanBallDef)),
							ByArith(basisNorm, basisVector))
						rootZero := real_sqrt.SqrtUnique.At(c.TermAs[Real]("&1 - &1 ^ 2"), zero)
						pole := c.Have(
							"its image is u, the north pole",
							"«collapse»(basis_vector(0)) = u",
							Funext(),
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								notLast := d.Unless(
									d.Term("i = n + 1"),
									"the last coordinate is 2·1 − 1 = 1, that of u",
									Given(func(e *Argument, last Fact) {
										e.Show(
											"the basis vector has norm 1",
											ByArith(last, north, basisNorm))
									}))
								lower := d.Unless(
									d.Term("i < n + 1"),
									"below n + 1 both are 0: √(1 − 1) = 0, and each coordinate of u there is at most its norm 0",
									Given(func(e *Argument, below Fact) {
										e.Show(
											"both coordinates vanish",
											ByArith(notLast, below, flat, basisNorm, rootZero, euclidean.ComponentLeNorm.At(i, head)))
									}))
								far := d.Have(
									"otherwise i is past n + 1",
									"n + 1 + 1 ≤ i",
									ByArith(notLast, lower))
								d.Show(
									"past n + 1 both are 0, u being a vector of ℝ^(n + 2)",
									ByArith(notLast, far, basisNorm, rootZero, vanish.At(i)))
							}))
						c.Show(
							"so u is a value of the collapse map on the ball",
							By(pole, inBall, set_image.FunInImage.At(collapse, ball, basis)))
					})
				b.Otherwise(
					"away from the north pole u is the image of its first coordinates divided by √(2 − 2s)",
					func(c *Argument, notNorth Fact) {
						gap := c.TermAs[Real]("&2 - &2 * u(n + 1)")
						below := c.Have(
							"s < 1: |s| is at most the norm 1 of u, and s ≠ 1",
							"&0 < &2 - &2 * u(n + 1)",
							ByArith(notNorth, sphere[1], euclidean.ComponentLeNorm.At(low, whole)))
						positive := c.Have(
							"so c = √(2 − 2s) is positive",
							"&0 < real_sqrt(&2 - &2 * u(n + 1))",
							ByArith(below, real_sqrt.SqrtPos.At(gap)))
						square := c.Have(
							"and squares to 2 − 2s",
							"real_sqrt(&2 - &2 * u(n + 1)) ^ 2 = &2 - &2 * u(n + 1)",
							ByArith(below, real_sqrt.SqrtPowTwo.At(gap)))
						w, wDef := c.LetAs[point]("w", "λi:num. COND(i = n + 1, &0, u(i) / real_sqrt(&2 - &2 * u(n + 1)))")
						preimage := c.VecAt[Real](low, "w")
						scaled := c.Have(
							"away from n + 1, c·w(i) = u(i)",
							"∀i:num. ¬(i = n + 1) ⇒ real_sqrt(&2 - &2 * u(n + 1)) * w(i) = u(i)",
							Derive(func(d *Argument) {
								d.FixAs[Nat]("i")
								notLast := d.Assume()
								d.Show(
									"c cancels against the division by c",
									wDef.Rw(),
									ByArith(notLast, positive))
							}))
						squares := c.Have(
							"so below n + 1, u(i)² = (2 − 2s)·w(i)²",
							"∀i:num. i < n + 1 ⇒ u(i) * u(i) = (&2 - &2 * u(n + 1)) * (w(i) * w(i))",
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								lower := d.Assume()
								at := d.Have(
									"there c·w(i) = u(i)",
									"real_sqrt(&2 - &2 * u(n + 1)) * w(i) = u(i)",
									ByArith(lower, scaled.At(i)))
								d.Show(
									"square both sides, c² being 2 − 2s",
									ByArith(
										Scaled(d.TermAs[Real]("u(i) + real_sqrt(&2 - &2 * u(n + 1)) * w(i)"), at),
										Scaled(d.TermAs[Real]("w(i) * w(i)"), square)))
							}))
						belowRange := c.TermAs[Set[Nat]]("{i:num | i < n + 1}")
						forms := c.Have(
							"summing, the form at u below n + 1 is (2 − 2s) times the form at w",
							"⟪u, u⟫_(n + 1) = (&2 - &2 * u(n + 1)) * ⟪w, w⟫_(n + 1)",
							ByArith(
								squares,
								real_sum.Congruence.At(
									belowRange,
									c.TermAs[point]("λi:num. u(i) * u(i)"),
									c.TermAs[point]("λi:num. (&2 - &2 * u(n + 1)) * (w(i) * w(i))")),
								real_sum.ScalarLeft.At(gap, c.TermAs[point]("λi:num. w(i) * w(i)"), belowRange),
								euclidean.DotIsSum.At(head, head),
								euclidean.DotIsSum.At(preimage, preimage)))
						doubled := c.Have(
							"so 2⟪w, w⟫ = 1 + s, dividing 1 − s² by 2 − 2s",
							"&2 * ⟪w, w⟫_(n + 1) = &1 + u(n + 1)",
							ByArith(split, forms, below))
						rest := c.TermAs[Real]("&1 - ‖w‖_(n + 1) ^ 2")
						factor := c.Have(
							"then the factor 2√(1 − ‖w‖²) is c: both are not negative and square to 4(1 − ‖w‖²) = 2 − 2s",
							"&2 * real_sqrt(&1 - ‖w‖_(n + 1) ^ 2) = real_sqrt(&2 - &2 * u(n + 1))",
							ByArith(
								doubled,
								below,
								euclidean.NormPow2.At(preimage),
								real_sqrt.SqrtPowTwo.At(rest),
								real_sqrt.SqrtNonneg.At(rest),
								real_sqrt.SqrtUnique.At(gap, c.TermAs[Real]("&2 * real_sqrt(&1 - ‖w‖_(n + 1) ^ 2)"))))
						short := c.Have(
							"‖w‖ ≤ 1, as ‖w‖² = (1 + s)/2 < 1",
							"‖w‖_(n + 1) ≤ &1",
							ByArith(doubled, below, euclidean.NormPow2.At(preimage), euclidean.NormNonneg.At(preimage)))
						wVector := c.Have(
							"w is a vector of ℝ^(n + 1): its coordinate n + 1 is 0, and past it those of u are",
							"vec⟨n + 1⟩(w)",
							wDef.Rw(),
							Unfold(vec_space.VecDef),
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								beyond := d.Assume()
								notLast := d.Unless(
									d.Term("i = n + 1"),
									"the coordinate n + 1 of w is 0",
									Given(func(e *Argument, last Fact) {
										e.Show(
											"by its definition",
											ByArith(last))
									}))
								far := d.Have(
									"otherwise i is past n + 1",
									"n + 1 + 1 ≤ i",
									ByArith(notLast, beyond))
								d.Show(
									"where u vanishes",
									ByArith(notLast, far, vanish.At(i)))
							}))
						inBall := c.Have(
							"so w lies in the ball",
							"w ∈ euclidean_ball(n + 1)",
							Simp(Fwd(euclidean_topology.EuclideanBallDef)),
							By(short, wVector))
						image := c.Have(
							"and its image is u",
							"«collapse»(w) = u",
							Funext(),
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								notLast := d.Unless(
									d.Term("i = n + 1"),
									"the last coordinate is 2‖w‖² − 1 = s",
									Given(func(e *Argument, last Fact) {
										e.Show(
											"‖w‖² is (1 + s)/2",
											ByArith(last, doubled, euclidean.NormPow2.At(preimage)))
									}))
								d.Show(
									"elsewhere it is c·w(i) = u(i)",
									ByArith(notLast, factor, scaled.At(i)))
							}))
						c.Show(
							"so u is a value of the collapse map on the ball",
							By(image, inBall, set_image.FunInImage.At(collapse, ball, w)))
					})
			}))
		a.Show(
			"so the image is the sphere",
			By(into, onto, set_order.SubsetAntisym, set_basic.SubsetDef))
	}),
})}

// CollapseContinuous — the collapse map is continuous from the ball D^(n + 1)
// to the sphere S^(n + 1). A map into ℝ^(n + 2) is continuous as its
// coordinates are. The last is 2‖x‖² − 1, a polynomial after the norm. The
// others are 2√(1 − ‖x‖²)·x(i), a coordinate times the square root of
// 1 − ‖x‖², which takes its values in ⟦0, ∞⟭ on the ball; and the square
// root is continuous there, square roots of reals within ε² of each other
// being within ε. Its values lie on the sphere (CollapseOnSphere).
var CollapseContinuous = collapseContinuousThm{family.Add(registry.ProofEntry{
	Name: "CollapseContinuous",
	Key:  "prop_91169c5644f7a63e",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "continuous_map(«disc», euclidean_sphere_topology(n + 1), «collapse»)",
		Abbrev: Abbrev{
			{Name: "collapse", Text: "λx:(num → real). λi:num. " +
				"    COND(i = n + 1, &2 * ‖x‖_(n + 1) ^ 2 - &1, &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i))"},
			{Name: "disc", Text: "subtopology(euclidean_topology(n + 1), euclidean_ball(n + 1))"},
		},
	}, func(a *Argument, n *Expr[Nat]) {
		type point = Fun[Nat, Real]
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		halfLine := a.TermAs[Set[Real]]("{t:real | &0 ≤ t}")
		disc := a.TermAs[Set[Set[point]]]("«disc»")
		ball := a.TermAs[Set[point]]("euclidean_ball(n + 1)")
		low := a.TermAs[Nat]("n + 1")
		collapse := a.TermAs[Fun[point, point]]("«collapse»")
		space := a.Have(
			"the ball is a space, a subspace of ℝ^(n + 1)",
			"is_topology(«disc»)",
			By(topological_space.SubtopologyTopology, euclidean_topology.EuclideanTopology.At(low)))
		points := a.Have(
			"its points are those of the ball",
			"⋃«disc» = euclidean_ball(n + 1)",
			BySets(
				topological_space.SubtopologySpace.At(a.TermAs[Set[Set[point]]]("euclidean_topology(n + 1)"), ball),
				euclidean_topology.EuclideanSpace.At(low),
				euclidean_topology.EuclideanBallDef.At(low)))
		norm := a.Have(
			"the norm is continuous on the ball",
			"continuous_map(«disc», real_topology, λx:(num → real). ‖x‖_(n + 1))",
			By(euclidean_topology.NormContinuous.At(low), continuous.FromSubtopology))
		lastPolynomial := a.Have(
			"t ↦ 2t² − 1 is continuous, a polynomial",
			"continuous_map(real_topology, real_topology, λt:real. &2 * t ^ 2 - &1)",
			By(
				real_continuous.PolynomialFunctionContinuous,
				real_polynomial.Sub.At(
					a.TermAs[Fun[Real, Real]]("λt:real. &2 * t ^ 2"), a.TermAs[Fun[Real, Real]]("λt:real. &1")),
				real_polynomial.ScalarLeft.At(a.TermAs[Fun[Real, Real]]("λt:real. t ^ 2"), a.TermAs[Real]("&2")),
				real_polynomial.Pow.At(a.TermAs[Fun[Real, Real]]("λt:real. t"), a.TermAs[Nat]("2")),
				real_polynomial.Id,
				real_polynomial.Const.At(a.TermAs[Real]("&1"))))
		lastCoordinate := a.Have(
			"so x ↦ 2‖x‖² − 1 is continuous on the ball",
			"continuous_map(«disc», real_topology, λx:(num → real). &2 * ‖x‖_(n + 1) ^ 2 - &1)",
			By(
				continuous.Compose.Read(norm).At(line, a.TermAs[Fun[Real, Real]]("λt:real. &2 * t ^ 2 - &1")),
				lastPolynomial,
				functions.ComposeApply))
		innerPolynomial := a.Have(
			"t ↦ 1 − t² is continuous, a polynomial",
			"continuous_map(real_topology, real_topology, λt:real. &1 - t ^ 2)",
			By(
				real_continuous.PolynomialFunctionContinuous,
				real_polynomial.Sub.At(
					a.TermAs[Fun[Real, Real]]("λt:real. &1"), a.TermAs[Fun[Real, Real]]("λt:real. t ^ 2")),
				real_polynomial.Pow.At(a.TermAs[Fun[Real, Real]]("λt:real. t"), a.TermAs[Nat]("2")),
				real_polynomial.Id,
				real_polynomial.Const.At(a.TermAs[Real]("&1"))))
		inner := a.TermAs[Fun[point, Real]]("λx:(num → real). &1 - ‖x‖_(n + 1) ^ 2")
		innerMap := a.Have(
			"so x ↦ 1 − ‖x‖² is continuous on the ball",
			"continuous_map(«disc», real_topology, λx:(num → real). &1 - ‖x‖_(n + 1) ^ 2)",
			By(
				continuous.Compose.Read(norm).At(line, a.TermAs[Fun[Real, Real]]("λt:real. &1 - t ^ 2")),
				innerPolynomial,
				functions.ComposeApply))
		innerValues := a.Have(
			"on the ball 1 − ‖x‖² is not negative",
			"∀x:(num → real). x ∈ ⋃«disc» ⇒ &0 ≤ &1 - ‖x‖_(n + 1) ^ 2",
			Derive(func(b *Argument) {
				b.FixAs[point]("x")
				inDisc := b.Assume()
				inBall := b.Have(
					"x lies in the ball",
					"x ∈ euclidean_ball(n + 1)",
					By(inDisc, points))
				parts := b.Conjuncts(
					b.Unfolded(inBall, euclidean_topology.EuclideanBallDef),
					"x is a vector of ℝ^(n + 1)",
					"of norm at most 1")
				b.Show(
					"its norm lies in ⟦0, 1⟧",
					ByArith(parts[1], euclidean.NormNonneg.At(b.VecAt[Real](low, "x"))))
			}))
		innerInto := a.Have(
			"so it is continuous into the half-line ⟦0, ∞⟭",
			"continuous_map(«disc», "+
				"    subtopology(real_topology, {t:real | &0 ≤ t}), "+
				"    λx:(num → real). &1 - ‖x‖_(n + 1) ^ 2)",
			By(innerMap, innerValues, continuous.IntoSubtopology.At(disc, line, inner, halfLine)))
		estimate := a.Have(
			"square roots of non-negative reals within ε² of each other "+
				"are within ε: |√x − √c|² ≤ |√x − √c|·(√x + √c) = |x − c|",
			"∀x c ε:real. &0 ≤ x ∧ &0 ≤ c ∧ &0 < ε ∧ |x - c| < ε * ε ⇒ |real_sqrt(x) - real_sqrt(c)| < ε",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				c := b.FixAs[Real]("c")
				eps := b.FixAs[Real]("ε")
				given := b.Assume()
				near := real_sgn_abs.AbsBetween.At(c, x, b.TermAs[Real]("ε * ε"))
				upper := b.Have(
					"√x − √c < ε",
					"real_sqrt(x) - real_sqrt(c) < ε",
					ByArith(
						given,
						near,
						real_sqrt.SqrtNonneg.At(x),
						real_sqrt.SqrtNonneg.At(c),
						real_sqrt.SqrtPowTwo.At(x),
						real_sqrt.SqrtPowTwo.At(c)))
				lower := b.Have(
					"√c − √x < ε",
					"real_sqrt(c) - real_sqrt(x) < ε",
					ByArith(
						given,
						near,
						real_sqrt.SqrtNonneg.At(x),
						real_sqrt.SqrtNonneg.At(c),
						real_sqrt.SqrtPowTwo.At(x),
						real_sqrt.SqrtPowTwo.At(c)))
				b.Show(
					"so |√x − √c| < ε",
					ByArith(
						given,
						upper,
						lower,
						real_sgn_abs.AbsBetween.At(b.TermAs[Real]("real_sqrt(c)"), b.TermAs[Real]("real_sqrt(x)"), eps)))
			}))
		rootOn := a.Have(
			"so the square root is continuous on ⟦0, ∞⟭, δ = ε² serving at every point",
			"real_continuous_on({t:real | &0 ≤ t}, real_sqrt)",
			Unfold(real_continuous.RealContinuousOnDef),
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				atC := b.Assume()
				b.FixAs[Real]("ε")
				positive := b.Assume()
				b.Take(b.TermAs[Real]("ε * ε"))
				b.Show(
					"δ = ε² serves",
					ByArith(atC, positive, estimate))
			}))
		root := a.TermAs[Fun[Real, Real]]("real_sqrt")
		rootMap := a.Have(
			"so x ↦ √(1 − ‖x‖²) is continuous on the ball",
			"continuous_map(«disc», real_topology, λx:(num → real). real_sqrt(&1 - ‖x‖_(n + 1) ^ 2))",
			By(
				continuous.Compose.Read(innerInto).At(line, root),
				rootOn,
				real_continuous.ContinuousOnIffMap.At(root, halfLine),
				functions.ComposeApply))
		factor := a.Have(
			"and so is x ↦ 2√(1 − ‖x‖²)",
			"continuous_map(«disc», real_topology, λx:(num → real). &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2))",
			By(
				space,
				rootMap,
				real_topology.RealSpace,
				set_basic.InUniv,
				continuous.Constant.At(disc, line, a.TermAs[Real]("&2")),
				real_valued.ContinuousRealMul.At(
					disc,
					a.TermAs[Fun[point, Real]]("λx:(num → real). &2"),
					a.TermAs[Fun[point, Real]]("λx:(num → real). real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)"))))
		coordinates := a.Have(
			"each coordinate of the collapse map below n + 2 is continuous on the ball",
			"∀i:num. i < n + 2 ⇒ continuous_map(«disc», real_topology, λx:(num → real). «collapse»(x)(i))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				notLast := b.Unless(
					b.Term("i = n + 1"),
					"the coordinate n + 1 is 2‖x‖² − 1",
					Given(func(c *Argument, last Fact) {
						c.Show(
							"which is continuous",
							By(last, lastCoordinate))
					}))
				lower := b.Have(
					"otherwise i is below n + 1",
					"i < n + 1",
					ByArith(below, notLast))
				coordinate := b.Have(
					"where the coordinate i is continuous on the ball",
					"continuous_map(«disc», real_topology, λx:(num → real). x(i))",
					By(lower, euclidean_topology.CoordinateContinuous.At(low, i), continuous.FromSubtopology))
				b.Show(
					"the coordinate i is 2√(1 − ‖x‖²)·x(i), a product of continuous functions",
					By(
						notLast,
						space,
						factor,
						coordinate,
						real_valued.ContinuousRealMul.At(
							disc,
							b.TermAs[Fun[point, Real]]("λx:(num → real). &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2)"),
							b.TermAs[Fun[point, Real]]("λx:(num → real). x(i)"))))
			}))
		onSphere := a.Have(
			"the collapse map carries the ball into the sphere",
			"∀x:(num → real). x ∈ ⋃«disc» ⇒ «collapse»(x) ∈ euclidean_sphere(n + 1)",
			Simp(Fwd(points)),
			By(CollapseOnSphere))
		twoMore := a.Have(
			"n + 1 + 1 is n + 2",
			"n + 1 + 1 = n + 2",
			ByArith())
		values := a.Have(
			"so its values are vectors of ℝ^(n + 2)",
			"∀x:(num → real). x ∈ ⋃«disc» ⇒ vec⟨n + 2⟩(«collapse»(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[point]("x")
				inDisc := b.Assume()
				parts := b.Conjuncts(
					b.Unfolded(GroupPremises(inDisc, onSphere.At(x)), euclidean_topology.EuclideanSphereDef),
					"the image is a vector of ℝ^(n + 1 + 1)",
					"of norm 1")
				b.Show(
					"ℝ^(n + 1 + 1) is ℝ^(n + 2)",
					Simp(Rev(twoMore)),
					By(parts[0]))
			}))
		plane := a.Have(
			"so the collapse map is continuous into ℝ^(n + 2), coordinate by coordinate",
			"continuous_map(«disc», euclidean_topology(n + 2), «collapse»)",
			By(
				space,
				values,
				coordinates,
				euclidean_topology.ContinuousIffCoordinates.At(a.TermAs[Nat]("n + 2"), disc, collapse)))
		sphereTopologyDef := a.Have(
			"the sphere S^(n + 1) as a space is the subspace of ℝ^(n + 2) on it",
			"euclidean_sphere_topology(n + 1) = "+
				"subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1))",
			By(euclidean_topology.EuclideanSphereTopologyDef.At(a.TermAs[Nat]("n + 1")), twoMore))
		a.Show(
			"its values lying on the sphere, it is continuous into the sphere",
			sphereTopologyDef.Rw(),
			By(
				plane,
				onSphere,
				continuous.IntoSubtopology.At(
					disc,
					a.TermAs[Set[Set[point]]]("euclidean_topology(n + 2)"),
					collapse,
					a.TermAs[Set[point]]("euclidean_sphere(n + 1)"))))
	}),
})}

// QuotientTopologyCongruence — two class maps that agree on the points of a
// space give it the same quotient topology. The quotient topology reads its
// map only through the image of the space and the preimages in the space,
// and on the space the two maps are one.
var QuotientTopologyCongruence = quotientTopologyCongruenceThm{family.Add(registry.ProofEntry{
	Name: "QuotientTopologyCongruence",
	Key:  "prop_c06481bf46745dd3",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → B).",
		Hypotheses: []string{
			"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
		},
		Conclusion: "quotient_topology(T, f) = quotient_topology(T, g)",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, B], agree Fact) {
		sameImage := a.Have(
			"f and g carry the space onto the same set",
			"image(f, ⋃T) = image(g, ⋃T)",
			By(agree, set_image.ImageCongruence.At(f, g, a.TermAs[Set[A]]("⋃T"))))
		samePreimages := a.Have(
			"and have the same preimages in it",
			"∀v:set(B). preimage_on(⋃T, f, v) = preimage_on(⋃T, g, v)",
			BySets(agree))
		a.Show(
			"the quotient topology reads its map only through these",
			Simp(Fwd(continuous.QuotientTopologyDef), Fwd(sameImage), Fwd(samePreimages)),
			Basic())
	}),
})}

// SphereQuotient — the ball D^(n + 1) with its boundary sphere Sⁿ collapsed
// to a point is the sphere S^(n + 1). The collapse map is continuous from
// the ball onto the sphere (CollapseContinuous, CollapseOnto), a Hausdorff
// space, and the ball is compact. On the ball its fibre through a point x of
// Sⁿ is Sⁿ, and through any other point x is {x} (CollapseFibres); so on the
// ball the fibres are the classes of the collapse, the two class maps give
// the ball one quotient topology (QuotientTopologyCongruence), and the
// quotient by the fibres is the sphere (continuous.FibreQuotientHomeomorphic).
var SphereQuotient = sphereQuotientThm{family.Add(registry.ProofEntry{
	Name: "SphereQuotient",
	Key:  "prop_bd334c6ef576d8d4",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Conclusion: "homeomorphic(quotient_topology(«disc», " +
			"        λx:(num → real). COND(x ∈ euclidean_sphere(n), euclidean_sphere(n), {x})), " +
			"    euclidean_sphere_topology(n + 1))",
		Abbrev: Abbrev{
			{Name: "collapse", Text: "λx:(num → real). λi:num. " +
				"    COND(i = n + 1, &2 * ‖x‖_(n + 1) ^ 2 - &1, &2 * real_sqrt(&1 - ‖x‖_(n + 1) ^ 2) * x(i))"},
			{Name: "disc", Text: "subtopology(euclidean_topology(n + 1), euclidean_ball(n + 1))"},
		},
	}, func(a *Argument, n *Expr[Nat]) {
		type point = Fun[Nat, Real]
		low := a.TermAs[Nat]("n + 1")
		high := a.TermAs[Nat]("n + 2")
		plane := a.TermAs[Set[Set[point]]]("euclidean_topology(n + 1)")
		target := a.TermAs[Set[Set[point]]]("euclidean_topology(n + 2)")
		ball := a.TermAs[Set[point]]("euclidean_ball(n + 1)")
		sphere := a.TermAs[Set[point]]("euclidean_sphere(n + 1)")
		discSpace := a.Have(
			"the ball is a space, a subspace of ℝ^(n + 1)",
			"is_topology(«disc»)",
			By(topological_space.SubtopologyTopology, euclidean_topology.EuclideanTopology.At(low)))
		sphereSpace := a.Have(
			"the sphere S^(n + 1) is a space, a subspace of ℝ^(n + 2)",
			"is_topology(subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1)))",
			By(topological_space.SubtopologyTopology, euclidean_topology.EuclideanTopology.At(high)))
		separated := a.Have(
			"and a Hausdorff one, as ℝ^(n + 2) is",
			"hausdorff(subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1)))",
			By(
				topological_space.HausdorffSubtopology.At(target, sphere),
				euclidean_topology.EuclideanHausdorff.At(high)))
		twoMore := a.Have(
			"n + 1 + 1 is n + 2",
			"n + 1 + 1 = n + 2",
			ByArith())
		sphereTopologyDef := a.Have(
			"the sphere S^(n + 1) as a space is the subspace of ℝ^(n + 2) on it",
			"euclidean_sphere_topology(n + 1) = "+
				"subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1))",
			By(euclidean_topology.EuclideanSphereTopologyDef.At(a.TermAs[Nat]("n + 1")), twoMore))
		spherePoints := a.Have(
			"the points of the sphere's subspace are those of the sphere, which lie in ℝ^(n + 2)",
			"⋃subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1)) = euclidean_sphere(n + 1)",
			Simp(
				Fwd(topological_space.SubtopologySpace),
				Fwd(euclidean_topology.EuclideanSpace),
				Fwd(euclidean_topology.EuclideanSphereDef),
				Fwd(twoMore)),
			BySets())
		onto := a.Have(
			"the collapse map carries the ball onto the sphere",
			"image(«collapse», euclidean_ball(n + 1)) = "+
				"⋃subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1))",
			By(spherePoints, At(CollapseOnto, n)))
		discPoints := a.Have(
			"the points of the ball's subspace are those of the ball",
			"⋃«disc» = euclidean_ball(n + 1)",
			BySets(
				topological_space.SubtopologySpace.At(plane, ball),
				euclidean_topology.EuclideanSpace.At(low),
				euclidean_topology.EuclideanBallDef.At(low)))
		classes := a.Have(
			"on the ball the fibre of the collapse map through x is Sⁿ when x lies on Sⁿ, and {x} otherwise",
			Statement{
				Binders: "∀x:(num → real).",
				Hypotheses: []string{
					"x ∈ ⋃«disc»",
				},
				Conclusion: "{y:(num → real) | y ∈ ⋃«disc» ∧ «collapse»(y) = «collapse»(x)} = " +
					"COND(x ∈ euclidean_sphere(n), euclidean_sphere(n), {x})",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[point]("x")
				inBall := b.Have(
					"x lies in the ball",
					"x ∈ euclidean_ball(n + 1)",
					By(b.Assume(), discPoints))
				b.Do(discPoints.Rw())
				b.Cases(b.Term("x ∈ euclidean_sphere(n)"))
				b.When(
					"x on Sⁿ: a point of the ball goes where x goes exactly when it lies on Sⁿ too",
					func(c *Argument, onBoundary Fact) {
						fibre := c.Have(
							"the points of the ball with x's image are those of Sⁿ, which lies in the ball",
							"∀y:(num → real). "+
								"    y ∈ euclidean_ball(n + 1) ∧ «collapse»(y) = «collapse»(x) ⇔ y ∈ euclidean_sphere(n)",
							c.ForEach(func(y *Expr[point]) Action {
								return By(
									inBall,
									onBoundary,
									At(CollapseFibres, n, y, x),
									euclidean_topology.SphereSubsetBall.At(n),
									set_basic.SubsetDef)
							}))
						c.Show(
							"so the fibre of x is Sⁿ",
							Simp(Fwd(set_basic.Extension)),
							By(fibre))
					})
				b.Otherwise(
					"x inside the ball: only x goes where x goes",
					func(c *Argument, inside Fact) {
						fibre := c.Have(
							"a point of the ball has x's image exactly when it is x",
							"∀y:(num → real). y ∈ euclidean_ball(n + 1) ∧ «collapse»(y) = «collapse»(x) ⇔ y = x",
							c.ForEach(func(y *Expr[point]) Action {
								return By(inside, inBall, At(CollapseFibres, n, y, x))
							}))
						c.Show(
							"so the fibre of x is {x}",
							Simp(Fwd(set_basic.Extension)),
							BySets(fibre))
					})
			}))
		fibres := a.TermAs[Fun[point, Set[point]]](
			"λx:(num → real). {y:(num → real) | y ∈ ⋃«disc» ∧ «collapse»(y) = «collapse»(x)}")
		collapsed := a.TermAs[Fun[point, Set[point]]](
			"λx:(num → real). COND(x ∈ euclidean_sphere(n), euclidean_sphere(n), {x})")
		disc := a.TermAs[Set[Set[point]]]("«disc»")
		same := a.Have(
			"so the quotient of the ball by the fibres is its quotient by the collapse",
			"quotient_topology(«disc», "+
				"    λx:(num → real). {y:(num → real) | y ∈ ⋃«disc» ∧ «collapse»(y) = «collapse»(x)}) = "+
				"quotient_topology(«disc», "+
				"    λx:(num → real). COND(x ∈ euclidean_sphere(n), euclidean_sphere(n), {x}))",
			By(classes, At(QuotientTopologyCongruence, disc, fibres, collapsed)))
		collapseInto := a.Have(
			"the collapse map is continuous into the sphere, the subspace of ℝ^(n + 2)",
			"continuous_map(«disc», "+
				"    subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1)), "+
				"    «collapse»)",
			sphereTopologyDef.RwRev(),
			By(At(CollapseContinuous, n)))
		a.Show(
			"which is the sphere S^(n + 1)",
			sphereTopologyDef.Rw(),
			same.RwRev(),
			By(
				discSpace,
				sphereSpace,
				separated,
				euclidean_topology.BallCompact.At(low),
				compact.CompactInOwnSubtopology.At(plane, ball),
				onto,
				collapseInto,
				continuous.FibreQuotientHomeomorphic.At(
					disc,
					a.TermAs[Set[Set[point]]]("subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1))"),
					a.TermAs[Fun[point, point]]("«collapse»"),
					ball)))
	}),
})}
