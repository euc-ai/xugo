// triangle.go — integrals along a segment, and the closed triangle: it holds
// its vertices, is convex, holds every triangle whose vertices it holds, is
// at most its perimeter across, and is closed. Round a triangle a linear
// function has integral zero, the integral is at most the function's bound
// times the perimeter, and the integral is the sum of those round the four
// quarters the midpoints cut it into.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

// SegmentIntegralPrimitive — the fundamental theorem along a segment: where
// F is a primitive of f at the points of the segment from z to w, and f is
// continuous there, the integral of f along the segment is F(w) − F(z). The
// segment is a piecewise smooth path, so the integral is the change of F
// between its ends, which it reaches at times 0 and 1.
var SegmentIntegralPrimitive = segmentIntegralPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "SegmentIntegralPrimitive",
	Key:  "prop_4fe310d7d5b52c03",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(complex → complex). ∀z w:complex.",
		Hypotheses: []string{
			"∀t:real. " +
				"    &0 ≤ t ∧ t ≤ &1 ⇒ complex_derivative_at(F, segment_path(z, w, t), f(segment_path(z, w, t)))",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
		},
		Conclusion: "«segInt»(f, z, w) = F(w) - F(z)",
	},
		func(
			arg *Argument,
			F, f *Arrow[Complex, Complex],
			z, w *Expr[Complex],
			primitive, continuous Fact,
		) {
			ends := arg.Have(
				"the segment starts at z and ends at w",
				"segment_path(z, w, &0) = z ∧ segment_path(z, w, &1) = w",
				Simp(Fwd(path_integral.SegmentPathDef)),
				ByArith())
			arg.Show(
				"the segment is a piecewise smooth path, so the integral is the change of F between its ends",
				By(
					primitive,
					continuous,
					ends,
					path_integral.SegmentPiecewiseSmooth.At(z, w),
					path_integral.PathIntegralPrimitive.At(
						F,
						f,
						arg.TermAs[Fun[Real, Complex]]("segment_path(z, w)"),
						arg.TermAs[Fun[Real, Complex]]("λt:real. w - z"),
						arg.TermAs[Real]("&0"),
						arg.TermAs[Real]("&1"))))
		}),
})}

// SegmentIntegralBound — the ML estimate along a segment: if f is
// continuous at the points of the segment from z to w and bounded there by
// M, its integral along the segment has modulus at most M·|w − z|. The
// segment is a piecewise smooth path whose speed is the constant |w − z|,
// and a constant integrates over ⟦0, 1⟧ to itself.
var SegmentIntegralBound = segmentIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "SegmentIntegralBound",
	Key:  "prop_a64c9c833c19775f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w:complex. ∀M:real.",
		Hypotheses: []string{
			"∀t:real. " +
				"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
				"    complex_continuous_at(f, segment_path(z, w, t)) ∧ |f(segment_path(z, w, t))| ≤ M",
		},
		Conclusion: "|«segInt»(f, z, w)| ≤ M * |w - z|",
	},
		func(arg *Argument, f *Arrow[Complex, Complex], z, w *Expr[Complex], M *Expr[Real], bounded Fact) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			arg.Show(
				"by the ML estimate along the segment, whose speed is the "+
					"constant |w − z|, with integral |w − z|·(1 − 0) over ⟦0, 1⟧",
				ByArith(
					bounded,
					path_integral.SegmentPiecewiseSmooth.At(z, w),
					path_integral.PathIntegralBound.At(
						f,
						arg.TermAs[Fun[Real, Complex]]("segment_path(z, w)"),
						arg.TermAs[Fun[Real, Complex]]("λt:real. w - z"),
						zero,
						one,
						M),
					real_integral.HasIntegralConst.At(zero, one, arg.TermAs[Real]("|w - z|")),
					real_integral.HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. |w - z|"),
						zero,
						one,
						arg.TermAs[Real]("|w - z| * (&1 - &0)"))))
		}),
})}

// TriangleVertices — a triangle holds its vertices: a, b and c are its
// points with coordinates (0, 0), (1, 0) and (0, 1) along the sides from a.
var TriangleVertices = triangleVerticesThm{family.Add(registry.ProofEntry{
	Name: "TriangleVertices",
	Key:  "prop_c7d49ccb2ffa2da",
	Build: family.Theorem(
		"∀a b c:complex. a ∈ «triangle»(a, b, c) ∧ b ∈ «triangle»(a, b, c) ∧ c ∈ «triangle»(a, b, c)",
		func(arg *Argument, a, b, c *Expr[Complex]) {
			points := arg.Have(
				"a, b and c are a + s·(b − a) + t·(c − a) at (s, t) = (0, 0), (1, 0) and (0, 1)",
				"a = a + &0 * (b - a) + &0 * (c - a) ∧ "+
					"b = a + &1 * (b - a) + &0 * (c - a) ∧ "+
					"c = a + &0 * (b - a) + &1 * (c - a)",
				ByArith())
			coordinates := arg.Have(
				"those coordinates are nonnegative with sum at most 1",
				"&0 ≤ &0 ∧ &0 ≤ &1 ∧ &0 + &0 ≤ &1 ∧ &1 + &0 ≤ &1 ∧ &0 + &1 ≤ &1",
				ByArith())
			arg.Show(
				"so each vertex lies in the triangle",
				By(points, coordinates))
		}),
})}

// TriangleConvex — a triangle is convex: the segment between two of its
// points lies in it. With x and y at coordinates (s₁, t₁) and (s₂, t₂) along
// the sides from a, the point of the segment at time θ is at
// (s₁ + θ·(s₂ − s₁), t₁ + θ·(t₂ − t₁)), and for θ in ⟦0, 1⟧ these are
// again nonnegative with sum at most 1, being one convex combination of the
// two pairs.
var TriangleConvex = triangleConvexThm{family.Add(registry.ProofEntry{
	Name: "TriangleConvex",
	Key:  "prop_892228f12d308a5f",
	Build: family.Theorem("∀a b c:complex. «convex»(«triangle»(a, b, c))",
		func(arg *Argument, a, b, c, x, y *Expr[Complex], θ *Expr[Real], xIn, yIn, low, high Fact) {
			_, _, xAt := arg.Unpack2As[Real, Real](xIn, "s₁", "t₁")
			_, _, yAt := arg.Unpack2As[Real, Real](yIn, "s₂", "t₂")
			coordinates := arg.Have(
				"the coordinates s₁ + θ·(s₂ − s₁) and t₁ + θ·(t₂ − t₁) are nonnegative with sum at most 1",
				"&0 ≤ s₁ + θ * (s₂ - s₁) ∧ "+
					"&0 ≤ t₁ + θ * (t₂ - t₁) ∧ "+
					"s₁ + θ * (s₂ - s₁) + (t₁ + θ * (t₂ - t₁)) ≤ &1",
				ByArith(low, high, xAt, yAt))
			xParts := arg.Conjuncts(
				xAt,
				"s₁ is at least 0",
				"t₁ is at least 0",
				"s₁ + t₁ is at most 1",
				"x is the point at (s₁, t₁)")
			yParts := arg.Conjuncts(
				yAt,
				"s₂ is at least 0",
				"t₂ is at least 0",
				"s₂ + t₂ is at most 1",
				"y is the point at (s₂, t₂)")
			point := arg.Have(
				"the segment from x to y is at time θ the point at those coordinates",
				"segment_path(x, y, θ) = a + &(s₁ + θ * (s₂ - s₁)) * (b - a) + &(t₁ + θ * (t₂ - t₁)) * (c - a)",
				xParts[3].Rw(),
				yParts[3].Rw(),
				Simp(
					Fwd(path_integral.SegmentPathDef),
					Fwd(complex_field.OfRealSub),
					Fwd(complex_field.OfRealAdd),
					Fwd(complex_field.OfRealMul)),
				ByArith())
			arg.Show(
				"so it lies in the triangle",
				By(point, coordinates))
		}),
})}

// ContinuousAlongSegment — a function continuous at every point of a convex
// set is continuous along every segment of the set: the segment between two
// of its points lies in it.
var ContinuousAlongSegment = continuousAlongSegmentThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAlongSegment",
	Key:  "prop_459236fba627c785",
	Build: family.Theorem(Statement{
		Binders: "∀K:set(complex). ∀f:(complex → complex). ∀p q:complex. ∀t:real.",
		Hypotheses: []string{
			"«convex»(K)",
			"∀z:complex. z ∈ K ⇒ complex_continuous_at(f, z)",
			"p ∈ K",
			"q ∈ K",
			"&0 ≤ t",
			"t ≤ &1",
		},
		Conclusion: "complex_continuous_at(f, segment_path(p, q, t))",
	},
		func(
			arg *Argument,
			K *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			p, q *Expr[Complex],
			t *Expr[Real],
			convex, continuous, pIn, qIn, low, high Fact,
		) {
			arg.Show(
				"the point at time t lies in K, where f is continuous",
				By(continuous, convex.At(p, q, t), pIn, qIn, low, high))
		}),
})}

// TriangleDiameter — two points of a triangle are at most its perimeter
// apart. With p and q at coordinates (s₁, t₁) and (s₂, t₂) along the sides
// from a, p − q is (s₁ − s₂)·(b − a) + (t₂ − t₁)·(a − c), and the coordinate
// differences are at most 1 in size, so |p − q| ≤ |b − a| + |a − c|.
var TriangleDiameter = triangleDiameterThm{family.Add(registry.ProofEntry{
	Name: "TriangleDiameter",
	Key:  "prop_e57135343922f90b",
	Build: family.Theorem(Statement{
		Binders: "∀a b c p q:complex.",
		Hypotheses: []string{
			"p ∈ «triangle»(a, b, c)",
			"q ∈ «triangle»(a, b, c)",
		},
		Conclusion: "|p - q| ≤ «perimeter»(a, b, c)",
	},
		func(arg *Argument, a, b, c, p, q *Expr[Complex], pIn, qIn Fact) {
			_, _, pAt := arg.Unpack2As[Real, Real](pIn, "s₁", "t₁")
			_, _, qAt := arg.Unpack2As[Real, Real](qIn, "s₂", "t₂")
			pParts := arg.Conjuncts(
				pAt,
				"s₁ is at least 0",
				"t₁ is at least 0",
				"s₁ + t₁ is at most 1",
				"p is the point at (s₁, t₁)")
			qParts := arg.Conjuncts(
				qAt,
				"s₂ is at least 0",
				"t₂ is at least 0",
				"s₂ + t₂ is at most 1",
				"q is the point at (s₂, t₂)")
			difference := arg.Have(
				"p − q is (s₁ − s₂)·(b − a) + (t₂ − t₁)·(a − c)",
				"p - q = &(s₁ - s₂) * (b - a) + &(t₂ - t₁) * (a - c)",
				Simp(Fwd(complex_field.OfRealSub)),
				ByArith(pParts[3], qParts[3]))
			close := arg.Have(
				"the coordinates differ by at most 1, all of them lying in ⟦0, 1⟧",
				"|s₁ - s₂| ≤ &1 ∧ |t₂ - t₁| ≤ &1",
				ByArith(pParts[0], pParts[1], pParts[2], qParts[0], qParts[1], qParts[2]))
			alongAB := arg.Have(
				"so (s₁ − s₂)·(b − a) is at most |b − a| in size",
				"|&(s₁ - s₂) * (b - a)| ≤ |b - a|",
				ByArith(
					close,
					complex_abs.AbsMul.At(arg.TermAs[Complex]("&(s₁ - s₂)"), arg.TermAs[Complex]("b - a")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("s₁ - s₂")),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("b - a"))))
			alongCA := arg.Have(
				"and (t₂ − t₁)·(a − c) at most |a − c|",
				"|&(t₂ - t₁) * (a - c)| ≤ |a - c|",
				ByArith(
					close,
					complex_abs.AbsMul.At(arg.TermAs[Complex]("&(t₂ - t₁)"), arg.TermAs[Complex]("a - c")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("t₂ - t₁")),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("a - c"))))
			arg.Show(
				"so by the triangle inequality |p − q| ≤ |b − a| + |a − c|",
				difference.Rw(),
				ByArith(
					alongAB,
					alongCA,
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex]("&(s₁ - s₂) * (b - a)"), arg.TermAs[Complex]("&(t₂ - t₁) * (a - c)")),
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("c - b"))))
		}),
})}

// TriangleSubset — a triangle whose vertices lie in a triangle lies in it.
// With p, q and r at coordinates (s₁, t₁), (s₂, t₂) and (s₃, t₃) along the
// sides from a, the point of the triangle pqr at coordinates (σ, τ) along
// its sides from p is at (s₁ + σ·(s₂ − s₁) + τ·(s₃ − s₁), t₁ + σ·(t₂ − t₁) +
// τ·(t₃ − t₁)), the combination of the three pairs with weights 1 − σ − τ,
// σ and τ, so again nonnegative with sum at most 1.
var TriangleSubset = triangleSubsetThm{family.Add(registry.ProofEntry{
	Name: "TriangleSubset",
	Key:  "prop_f55e6d37fe7f0220",
	Build: family.Theorem(Statement{
		Binders: "∀a b c p q r:complex.",
		Hypotheses: []string{
			"p ∈ «triangle»(a, b, c)",
			"q ∈ «triangle»(a, b, c)",
			"r ∈ «triangle»(a, b, c)",
		},
		Conclusion: "«triangle»(p, q, r) ⊆ «triangle»(a, b, c)",
	},
		func(arg *Argument, a, b, c, p, q, r *Expr[Complex], pIn, qIn, rIn Fact) {
			arg.Show(
				"every point of the triangle pqr lies in the triangle abc",
				Unfold(set_basic.SubsetDef),
				Derive(func(d *Argument) {
					_, _, pAt := d.Unpack2As[Real, Real](pIn, "s₁", "t₁")
					_, _, qAt := d.Unpack2As[Real, Real](qIn, "s₂", "t₂")
					_, _, rAt := d.Unpack2As[Real, Real](rIn, "s₃", "t₃")
					d.FixAs[Complex]("x")
					xIn := d.Assume()
					_, _, xAt := d.Unpack2As[Real, Real](xIn, "σ", "τ")
					coordinates := d.Have(
						"the coordinates of x along the sides from a are nonnegative with sum at most 1",
						"&0 ≤ s₁ + σ * (s₂ - s₁) + τ * (s₃ - s₁) ∧ "+
							"&0 ≤ t₁ + σ * (t₂ - t₁) + τ * (t₃ - t₁) ∧ "+
							"s₁ + σ * (s₂ - s₁) + τ * (s₃ - s₁) + (t₁ + σ * (t₂ - t₁) + τ * (t₃ - t₁)) ≤ &1",
						ByArith(pAt, qAt, rAt, xAt))
					pParts := d.Conjuncts(
						pAt,
						"s₁ is at least 0",
						"t₁ is at least 0",
						"s₁ + t₁ is at most 1",
						"p is the point at (s₁, t₁)")
					qParts := d.Conjuncts(
						qAt,
						"s₂ is at least 0",
						"t₂ is at least 0",
						"s₂ + t₂ is at most 1",
						"q is the point at (s₂, t₂)")
					rParts := d.Conjuncts(
						rAt,
						"s₃ is at least 0",
						"t₃ is at least 0",
						"s₃ + t₃ is at most 1",
						"r is the point at (s₃, t₃)")
					xParts := d.Conjuncts(
						xAt,
						"σ is at least 0",
						"τ is at least 0",
						"σ + τ is at most 1",
						"x is the point at (σ, τ) along the sides from p")
					point := d.Have(
						"x is the point at those coordinates along the sides from a",
						"x = "+
							"a + "+
							"&(s₁ + σ * (s₂ - s₁) + τ * (s₃ - s₁)) * (b - a) + "+
							"&(t₁ + σ * (t₂ - t₁) + τ * (t₃ - t₁)) * (c - a)",
						xParts[3].Rw(),
						pParts[3].Rw(),
						qParts[3].Rw(),
						rParts[3].Rw(),
						Simp(Fwd(complex_field.OfRealSub), Fwd(complex_field.OfRealAdd), Fwd(complex_field.OfRealMul)),
						ByArith())
					d.Show(
						"so x lies in the triangle abc",
						By(point, coordinates))
				}))
		}),
})}

// TriangleClosed — a triangle is closed: it holds the limit p of every
// convergent sequence x of its points. Each x(n) has coordinates
// (σ(n), τ(n)) in the closed simplex, so the points complex(σ(n), τ(n)) are
// bounded, and by Bolzano–Weierstrass a subsequence of them tends to some l,
// whose parts stay in the simplex, limits keeping ≤. Along that subsequence x
// is the image of complex(σ, τ) under the continuous map
// w ↦ a + re(w)·(b − a) + im(w)·(c − a), so it tends to the image of l; being a
// subsequence of x it also tends to p, so p is that image, a point of the
// triangle.
var TriangleClosed = triangleClosedThm{family.Add(registry.ProofEntry{
	Name: "TriangleClosed",
	Key:  "prop_e7f37a47ae806063",
	Build: family.Theorem(
		"∀a b c:complex. closed_in(complex_topology, «triangle»(a, b, c))",
		func(arg *Argument, a, b, c *Expr[Complex]) {
			triangle := arg.TermAs[Set[Complex]]("«triangle»(a, b, c)")
			universe := arg.TermAs[Set[Complex]]("𝕌")
			distance := arg.TermAs[Fun2[Complex, Complex, Real]]("complex_dist")
			limits := arg.Have(
				"the triangle holds the limit of every convergent sequence of its points",
				Statement{
					Binders: "∀x:(num → complex). ∀p:complex.",
					Hypotheses: []string{
						"∀n:num. x(n) ∈ «triangle»(a, b, c)",
						"x ⟶ p",
					},
					Conclusion: "p ∈ «triangle»(a, b, c)",
				},
				Derive(func(d *Argument) {
					x := d.FixAs[Fun[Nat, Complex]]("x")
					p := d.FixAs[Complex]("p")
					given := d.Conjuncts(
						d.Assume(),
						"every x(n) lies in the triangle",
						"x tends to p")
					pointwise := d.Have(
						"each x(n) has coordinates along the sides from a",
						"∀n:num. ∃s t:real. &0 ≤ s ∧ &0 ≤ t ∧ s + t ≤ &1 ∧ x(n) = a + &s * (b - a) + &t * (c - a)",
						By(given[0]))
					_, _, coordinates := d.Obtain2As[Fun[Nat, Real], Fun[Nat, Real]](
						"choose them as two sequences σ and τ",
						"∃σ τ:(num → real). ∀n:num. "+
							"    &0 ≤ σ(n) ∧ &0 ≤ τ(n) ∧ σ(n) + τ(n) ≤ &1 ∧ x(n) = a + &(σ(n)) * (b - a) + &(τ(n)) * (c - a)",
						By(pointwise))
					bounded := d.Have(
						"the points complex(σ(n), τ(n)) have modulus at most 2",
						"∀n:num. |complex(σ(n), τ(n))| ≤ &2",
						Derive(func(e *Argument) {
							n := e.FixAs[Nat]("n")
							e.Show(
								"a modulus is at most the sum of the sizes of the parts, here each at most 1",
								ByArith(coordinates.At(n), complex_abs.AbsLeParts.At(e.TermAs[Complex]("complex(σ(n), τ(n))"))))
						}))
					_, l, subsequence := d.Obtain2As[Fun[Nat, Nat], Complex](
						"by Bolzano–Weierstrass a subsequence of them tends to some l",
						"∃φ:(num → num). ∃l:complex. (∀j:num. φ(j) < φ(j + 1)) ∧ (λn:num. complex(σ(n), τ(n))) ∘ φ ⟶ l",
						By(
							bounded,
							complex_topology.BolzanoWeierstrass.At(
								d.TermAs[Fun[Nat, Complex]]("λn:num. complex(σ(n), τ(n))"),
								d.TermAs[Real]("&2"))))
					thinned := d.Conjuncts(
						subsequence,
						"φ increases",
						"the subsequence tends to l")
					alongL := d.Unfolded(thinned[1], functions.ComposeApply)
					parts := d.Have(
						"so the coordinates along it tend to the parts of l",
						"(λj:num. σ(φ(j))) ⟶ re(l) ∧ (λj:num. τ(φ(j))) ⟶ im(l)",
						By(
							alongL,
							complex_topology.ConvergesIffParts.At(
								d.TermAs[Fun[Nat, Complex]]("λj:num. complex(σ(φ(j)), τ(φ(j)))"),
								l)))
					sigma := d.TermAs[Fun[Nat, Real]]("λj:num. σ(φ(j))")
					tau := d.TermAs[Fun[Nat, Real]]("λj:num. τ(φ(j))")
					zero, one := d.TermAs[Real]("&0"), d.TermAs[Real]("&1")
					reL, imL := d.TermAs[Real]("re(l)"), d.TermAs[Real]("im(l)")
					simplex := d.Have(
						"and the parts of l lie in the closed simplex, limits keeping ≤",
						"&0 ≤ re(l) ∧ &0 ≤ im(l) ∧ re(l) + im(l) ≤ &1",
						By(
							parts,
							coordinates,
							real_sequences.LimitAdd.At(sigma, tau, reL, imL),
							real_sequences.BoundLessEqLimit.At(sigma, reL, zero),
							real_sequences.BoundLessEqLimit.At(tau, imL, zero),
							real_sequences.LimitLessEqBound.At(
								d.TermAs[Fun[Nat, Real]]("λj:num. σ(φ(j)) + τ(φ(j))"),
								d.TermAs[Real]("re(l) + im(l)"),
								one)))
					image := d.TermAs[Fun[Complex, Complex]]("λw:complex. a + &(re(w)) * (b - a) + &(im(w)) * (c - a)")
					continuous := d.Have(
						"the map w ↦ a + re(w)·(b − a) + im(w)·(c − a) is continuous at l",
						"complex_continuous_at(λw:complex. a + &(re(w)) * (b - a) + &(im(w)) * (c - a), l)",
						By(
							complex_topology.ContinuousAtParts.At(l),
							complex_topology.ContinuousAtConst.At(l, a),
							complex_topology.ContinuousAtConst.At(l, d.TermAs[Complex]("b - a")),
							complex_topology.ContinuousAtConst.At(l, d.TermAs[Complex]("c - a")),
							complex_topology.ContinuousAtMul.At(
								d.TermAs[Fun[Complex, Complex]]("λw:complex. &(re(w))"),
								d.TermAs[Fun[Complex, Complex]]("λw:complex. b - a"),
								l),
							complex_topology.ContinuousAtMul.At(
								d.TermAs[Fun[Complex, Complex]]("λw:complex. &(im(w))"),
								d.TermAs[Fun[Complex, Complex]]("λw:complex. c - a"),
								l),
							complex_topology.ContinuousAtAdd.At(
								d.TermAs[Fun[Complex, Complex]]("λw:complex. a"),
								d.TermAs[Fun[Complex, Complex]]("λw:complex. &(re(w)) * (b - a)"),
								l),
							complex_topology.ContinuousAtAdd.At(
								d.TermAs[Fun[Complex, Complex]]("λw:complex. a + &(re(w)) * (b - a)"),
								d.TermAs[Fun[Complex, Complex]]("λw:complex. &(im(w)) * (c - a)"),
								l)))
					imageLimit := d.Have(
						"so along the subsequence x, the image of complex(σ, τ), tends to the image of l",
						"(λj:num. x(φ(j))) ⟶ a + &(re(l)) * (b - a) + &(im(l)) * (c - a)",
						By(
							coordinates,
							continuous,
							alongL,
							complex_topology.ContinuousAtSequential.At(
								image,
								l,
								d.TermAs[Fun[Nat, Complex]]("λj:num. complex(σ(φ(j)), τ(φ(j)))"))))
					φ := d.TermAs[Fun[Nat, Nat]]("φ")
					limitP := d.Have(
						"and, a subsequence of x, it tends to p",
						"(λj:num. x(φ(j))) ⟶ p",
						By(
							Normalized,
							thinned[0],
							given[1],
							complex_topology.ConvergesIffMetric.At(x, p),
							complete_metric.LimitSubsequence.At(universe, distance, x, φ, p),
							complex_topology.ConvergesIffMetric.At(d.TermAs[Fun[Nat, Complex]]("x ∘ φ"), p),
							functions.ComposeApply.At(x, φ)))
					d.Show(
						"so p is the image of l, a point of the triangle",
						By(
							limitP,
							imageLimit,
							simplex,
							complex_topology.LimitUnique.At(
								d.TermAs[Fun[Nat, Complex]]("λj:num. x(φ(j))"),
								p,
								d.TermAs[Complex]("a + &(re(l)) * (b - a) + &(im(l)) * (c - a)"))))
				}))
			arg.Show(
				"so the triangle is closed, a set of a metric space that holds its limits being closed",
				Unfold(complex_topology.ComplexTopologyDef),
				By(
					limits,
					complex_topology.ComplexMetric,
					complete_metric.ClosedIffSequential.At(universe, distance, triangle),
					complex_topology.ConvergesIffMetric,
					set_order.SubsetUniv.At(triangle)))
		}),
})}

// TriangleBoundaryLinear — a linear function α + βz has integral zero round
// the boundary of every triangle. It has the primitive F(z) = αz + βz²/2 in
// the whole plane, so the integral along each side is the change of F from
// the side's start to its end, and the three changes cancel round the
// closed triangle.
var TriangleBoundaryLinear = triangleBoundaryLinearThm{family.Add(registry.ProofEntry{
	Name: "TriangleBoundaryLinear",
	Key:  "prop_f6af3186ce847bb7",
	Build: family.Theorem(
		"∀α β a b c:complex. «boundaryInt»(λz:complex. α + β * z, a, b, c) = &0",
		func(arg *Argument, α, β, a, b, c *Expr[Complex]) {
			primitive := arg.Have(
				"F(z) = αz + βz²/2 has derivative α + βu at every point u",
				"∀u:complex. complex_derivative_at(λz:complex. α * z + β / &2 * (z * z), u, α + β * u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					one := d.TermAs[Complex]("complex_of_real(&1)")
					identity := d.TermAs[Fun[Complex, Complex]]("λz:complex. z")
					value := d.Have(
						"α·1 + β/2·(1·u + u·1) is α + βu, since β/2 times 2 is β",
						"α * &1 + β / &2 * (&1 * u + u * &1) = α + β * u",
						ByArith())
					d.Show(
						"by the rules for derivatives αz + β/2·z² has derivative α·1 + β/2·(1·u + u·1), which is α + βu",
						By(
							value,
							complex_derivative.DerivativeId.At(u),
							complex_derivative.DerivativeMul.At(identity, identity, u, one, one),
							complex_derivative.DerivativeScale.At(identity, u, one, α),
							complex_derivative.DerivativeScale.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. z * z"),
								u,
								d.TermAs[Complex]("&1 * u + u * &1"),
								d.TermAs[Complex]("β / &2")),
							complex_derivative.DerivativeAdd.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. α * z"),
								d.TermAs[Fun[Complex, Complex]]("λz:complex. β / &2 * (z * z)"),
								u,
								d.TermAs[Complex]("α * &1"),
								d.TermAs[Complex]("β / &2 * (&1 * u + u * &1)"))))
				}))
			continuous := arg.Have(
				"α + βz is continuous at every point, a sum of a constant and a constant times z",
				"∀u:complex. complex_continuous_at(λz:complex. α + β * z, u)",
				arg.ForEach(func(u *Expr[Complex]) Action {
					return By(
						complex_topology.ContinuousAtConst.At(u, α),
						complex_topology.ContinuousAtConst.At(u, β),
						complex_topology.ContinuousAtId.At(u),
						complex_topology.ContinuousAtMul.At(
							arg.TermAs[Fun[Complex, Complex]]("λz:complex. β"),
							arg.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
							u),
						complex_topology.ContinuousAtAdd.At(
							arg.TermAs[Fun[Complex, Complex]]("λz:complex. α"),
							arg.TermAs[Fun[Complex, Complex]]("λz:complex. β * z"),
							u))
				}))
			F := arg.TermAs[Fun[Complex, Complex]]("λz:complex. α * z + β / &2 * (z * z)")
			f := arg.TermAs[Fun[Complex, Complex]]("λz:complex. α + β * z")
			arg.Show(
				"each side's integral is the change of F along it, and the three changes cancel round the triangle",
				ByArith(
					primitive,
					continuous,
					SegmentIntegralPrimitive.At(F, f, a, b),
					SegmentIntegralPrimitive.At(F, f, b, c),
					SegmentIntegralPrimitive.At(F, f, c, a)))
		}),
})}

// TriangleBoundaryBound — the estimate round a triangle: if f is continuous
// on the closed triangle and bounded there by M, its integral round the
// boundary has modulus at most M times the perimeter. The triangle is
// convex and holds its vertices, so each side lies in it, and on each side
// the ML estimate bounds the integral by M times the side's length; the
// triangle inequality adds the three.
var TriangleBoundaryBound = triangleBoundaryBoundThm{family.Add(registry.ProofEntry{
	Name: "TriangleBoundaryBound",
	Key:  "prop_dfbea2644fd7fb9c",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex. ∀M:real.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z) ∧ |f(z)| ≤ M",
		},
		Conclusion: "|«boundaryInt»(f, a, b, c)| ≤ M * «perimeter»(a, b, c)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			a, b, c *Expr[Complex],
			M *Expr[Real],
			bounded Fact,
		) {
			along := arg.Have(
				"along a segment between two points of the triangle, "+
					"which lies in the triangle, f is continuous and at most M",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ «triangle»(a, b, c)",
						"w ∈ «triangle»(a, b, c)",
					},
					Conclusion: "∀t:real. " +
						"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
						"    complex_continuous_at(f, segment_path(z, w, t)) ∧ |f(segment_path(z, w, t))| ≤ M",
				},
				By(bounded, At(TriangleConvex, a, b, c)))
			vertices := arg.Conjuncts(
				TriangleVertices.At(a, b, c),
				"a lies in the triangle",
				"so does b",
				"and so does c")
			arg.Show(
				"on each side the integral is at most M times the side's "+
					"length, and the triangle inequality adds the three",
				ByArith(
					vertices[0],
					vertices[1],
					vertices[2],
					along.At(a, b),
					along.At(b, c),
					along.At(c, a),
					SegmentIntegralBound.At(f, a, b, M),
					SegmentIntegralBound.At(f, b, c, M),
					SegmentIntegralBound.At(f, c, a, M),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex]("«segInt»(f, a, b) + «segInt»(f, b, c)"),
						arg.TermAs[Complex]("«segInt»(f, c, a)")),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex]("«segInt»(f, a, b)"),
						arg.TermAs[Complex]("«segInt»(f, b, c)"))))
		}),
})}

// TriangleQuadrisection — the boundary integral of a triangle is the sum of
// those of the four triangles its midpoints cut it into, each run with the
// orientation of the whole: the corner triangles at a, b and c and the
// middle one. Each side of the large triangle splits at its midpoint into
// two sides of corner triangles, and each side of the middle triangle is
// also a side of a corner triangle, run the other way, so its two integrals
// cancel. Every segment involved joins two points of the triangle and lies
// in it, so f is continuous along it.
var TriangleQuadrisection = triangleQuadrisectionThm{family.Add(registry.ProofEntry{
	Name: "TriangleQuadrisection",
	Key:  "prop_8c39179c2b67dc76",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
		},
		Conclusion: "«boundaryInt»(f, a, b, c) = " +
			"«boundaryInt»(f, a, «m_ab», «m_ca») + " +
			"«boundaryInt»(f, «m_ab», b, «m_bc») + " +
			"«boundaryInt»(f, «m_ca», «m_bc», c) + " +
			"«boundaryInt»(f, «m_bc», «m_ca», «m_ab»)",
		Abbrev: Abbrev{
			{Name: "m_ab", Text: "segment_path(a, b, &1 / &2)"},
			{Name: "m_bc", Text: "segment_path(b, c, &1 / &2)"},
			{Name: "m_ca", Text: "segment_path(a, c, &1 / &2)"},
		},
	},
		func(arg *Argument, f *Arrow[Complex, Complex], a, b, c *Expr[Complex], continuous Fact) {
			half := arg.TermAs[Real]("&1 / &2")
			mAB, mBC, mCA :=
				arg.TermAs[Complex]("«m_ab»"), arg.TermAs[Complex]("«m_bc»"), arg.TermAs[Complex]("«m_ca»")
			along := arg.Have(
				"f is continuous along a segment between two points of the triangle, the triangle being convex",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ «triangle»(a, b, c)",
						"w ∈ «triangle»(a, b, c)",
					},
					Conclusion: "∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
				},
				By(
					continuous,
					At(TriangleConvex, a, b, c),
					At(ContinuousAlongSegment, arg.TermAs[Set[Complex]]("«triangle»(a, b, c)"), f)))
			vertices := arg.Conjuncts(
				TriangleVertices.At(a, b, c),
				"a lies in the triangle",
				"so does b",
				"and so does c")
			midpoints := arg.Have(
				"so do the midpoints of the sides, the triangle being convex",
				"«m_ab» ∈ «triangle»(a, b, c) ∧ «m_bc» ∈ «triangle»(a, b, c) ∧ «m_ca» ∈ «triangle»(a, b, c)",
				By(
					vertices[0],
					vertices[1],
					vertices[2],
					TriangleConvex.At(a, b, c, a, b, half),
					TriangleConvex.At(a, b, c, b, c, half),
					TriangleConvex.At(a, b, c, a, c, half)))
			backwards := arg.Have(
				"run backwards, the segment from c to a is at time "+
					"s where the segment from a to c is at time 1 − s",
				"∀s:real. segment_path(c, a, s) = segment_path(a, c, &1 - s)",
				Simp(Fwd(path_integral.SegmentPathDef), Fwd(complex_field.OfRealSub)),
				ByArith())
			halfway := arg.Have(
				"1 − 1/2 is 1/2",
				"&1 - &1 / &2 = &1 / &2",
				ByArith())
			splitAB := arg.Have(
				"the side from a to b splits at its midpoint",
				"«segInt»(f, a, b) = «segInt»(f, a, «m_ab») + «segInt»(f, «m_ab», b)",
				By(vertices[0], vertices[1], along.At(a, b), path_integral.SegmentSplit.At(f, a, b, half)))
			splitBC := arg.Have(
				"so does the side from b to c",
				"«segInt»(f, b, c) = «segInt»(f, b, «m_bc») + «segInt»(f, «m_bc», c)",
				By(vertices[1], vertices[2], along.At(b, c), path_integral.SegmentSplit.At(f, b, c, half)))
			splitCA := arg.Have(
				"and the side from c to a, whose midpoint is «m_ca»",
				"«segInt»(f, c, a) = «segInt»(f, c, «m_ca») + «segInt»(f, «m_ca», a)",
				By(
					vertices[2],
					vertices[0],
					backwards.At(half),
					halfway,
					along.At(c, a),
					path_integral.SegmentSplit.At(f, c, a, half)))
			inner := arg.Have(
				"each side of the middle triangle is run once each way, and its two integrals cancel",
				"«segInt»(f, «m_ca», «m_ab») = -«segInt»(f, «m_ab», «m_ca») ∧ "+
					"«segInt»(f, «m_ab», «m_bc») = -«segInt»(f, «m_bc», «m_ab») ∧ "+
					"«segInt»(f, «m_bc», «m_ca») = -«segInt»(f, «m_ca», «m_bc»)",
				By(
					midpoints,
					along.At(mAB, mCA),
					along.At(mBC, mAB),
					along.At(mCA, mBC),
					path_integral.SegmentReverse.At(f, mAB, mCA),
					path_integral.SegmentReverse.At(f, mBC, mAB),
					path_integral.SegmentReverse.At(f, mCA, mBC)))
			arg.Show(
				"the four small boundaries add up to the large one",
				ByArith(splitAB, splitBC, splitCA, inner))
		}),
})}
