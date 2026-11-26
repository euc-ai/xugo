// exceptional.go — Goursat's theorem with one exceptional point, where the
// function is only continuous. Two numbers u and v with im(conj(u)·v) = 0 are
// parallel, and otherwise independent over ℝ; a triangle whose sides are
// parallel has boundary integral zero, one vertex lying on the side joining
// the other two. A triangle splits at any of its points into three with that
// point as a vertex; cutting off the corner at that vertex leaves two pieces
// that miss it, so the boundary integral is that of the corner triangle,
// which shrinks to the vertex.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ParallelRealMultiple — a number v parallel to a nonzero u, in that
// im(conj(u)·v) is 0, is a real multiple of u. With N = re(u)² + im(u)²,
// positive as u is not 0, and d = re(u)·re(v) + im(u)·im(v), the parts of
// N·v and d·u differ by im(u) and re(u) times re(u)·im(v) − im(u)·re(v),
// which is im(conj(u)·v) = 0; so v is k·u for k = d/N.
var ParallelRealMultiple = parallelRealMultipleThm{family.Add(registry.ProofEntry{
	Name: "ParallelRealMultiple",
	Key:  "prop_196a5fa5c4f30d91",
	Build: family.Theorem(Statement{
		Binders: "∀u v:complex.",
		Hypotheses: []string{
			"u ≠ &0",
			"im(conj(u) * v) = &0",
		},
		Conclusion: "∃k:real. v = &k * u",
	},
		func(arg *Argument, u, v *Expr[Complex], nonzero, parallel Fact) {
			reU, imU := arg.TermAs[Real]("re(u)"), arg.TermAs[Real]("im(u)")
			reV, imV := arg.TermAs[Real]("re(v)"), arg.TermAs[Real]("im(v)")
			modulusU := arg.TermAs[Real]("|u|")
			norm := arg.TermAs[Real]("re(u) * re(u) + im(u) * im(u)")
			cross := arg.Have(
				"the imaginary part of conj(u)·v is re(u)·im(v) − im(u)·re(v)",
				"im(conj(u) * v) = re(u) * im(v) - im(u) * re(v)",
				Simp(complex_field.Parts, Fwd(complex_field.ComplexMulDef), Fwd(complex_field.ComplexConjDef)),
				ByArith())
			modulus := arg.Have(
				"u, not being 0, has positive modulus",
				"&0 < |u|",
				ByArith(nonzero, complex_abs.AbsPosIffNonzero.At(u)))
			squares := arg.Have(
				"so N = re(u)² + im(u)², which is |u|², is positive",
				"&0 < re(u) * re(u) + im(u) * im(u)",
				ByArith(modulus, complex_abs.AbsSquare.At(u), real_order_ring.MulPos.At(modulusU, modulusU)))
			parts := arg.Have(
				"N·v and d·u have the same parts, for d = re(u)·re(v) + im(u)·im(v)",
				"(re(u) * re(u) + im(u) * im(u)) * re(v) = (re(u) * re(v) + im(u) * im(v)) * re(u) ∧ "+
					"(re(u) * re(u) + im(u) * im(u)) * im(v) = (re(u) * re(v) + im(u) * im(v)) * im(u)",
				ByArith(Scaled(imU, parallel), Scaled(imU, cross), Scaled(reU, parallel), Scaled(reU, cross)))
			k, kDef := arg.LetAs[Real]("k", "(re(u) * re(v) + im(u) * im(v)) / (re(u) * re(u) + im(u) * im(u))")
			ratio := arg.Have(
				"k·N = d",
				"k * (re(u) * re(u) + im(u) * im(u)) = re(u) * re(v) + im(u) * im(v)",
				ByArith(Scaled(norm, kDef), squares))
			arg.Take(k)
			arg.Show(
				"so N·v = N·(k·u) part by part, and N is not 0",
				Simp(complex_field.Parts, Fwd(complex_field.ComplexMulDef), Fwd(complex_field.ComplexOfRealDef)),
				ByArith(
					parts,
					squares,
					Scaled(reU, ratio),
					Scaled(imU, ratio),
					real_ring.MulLeftCancel.At(norm, reV, arg.TermAs[Real]("k * re(u)")),
					real_ring.MulLeftCancel.At(norm, imV, arg.TermAs[Real]("k * im(u)"))))
		}),
})}

// SkewIndependent — two numbers u and v with im(conj(u)·v) not 0 are
// independent over ℝ: if x·u + y·v = 0 for reals x and y, both are 0. Part by
// part x·re(u) + y·re(v) = 0 and x·im(u) + y·im(v) = 0; combining the two
// with the parts of v, and of u, as coefficients, x and y times
// D = re(u)·im(v) − im(u)·re(v) are 0, and D is im(conj(u)·v), not 0.
var SkewIndependent = skewIndependentThm{family.Add(registry.ProofEntry{
	Name: "SkewIndependent",
	Key:  "prop_25c04fbae5524969",
	Build: family.Theorem(Statement{
		Binders: "∀u v:complex. ∀x y:real.",
		Hypotheses: []string{
			"im(conj(u) * v) ≠ &0",
			"&x * u + &y * v = &0",
		},
		Conclusion: "x = &0 ∧ y = &0",
	},
		func(arg *Argument, u, v *Expr[Complex], x, y *Expr[Real], skew, combination Fact) {
			reU, imU := arg.TermAs[Real]("re(u)"), arg.TermAs[Real]("im(u)")
			reV, imV := arg.TermAs[Real]("re(v)"), arg.TermAs[Real]("im(v)")
			zero := arg.TermAs[Real]("&0")
			determinant := arg.TermAs[Real]("re(u) * im(v) - im(u) * re(v)")
			cross := arg.Have(
				"the imaginary part of conj(u)·v is re(u)·im(v) − im(u)·re(v)",
				"im(conj(u) * v) = re(u) * im(v) - im(u) * re(v)",
				Simp(complex_field.Parts, Fwd(complex_field.ComplexMulDef), Fwd(complex_field.ComplexConjDef)),
				ByArith())
			nonzero := arg.Have(
				"so D = re(u)·im(v) − im(u)·re(v) is not 0",
				"re(u) * im(v) - im(u) * re(v) ≠ &0",
				ByArith(skew, cross))
			partsOf := arg.Have(
				"the parts of x·u + y·v are x·re(u) + y·re(v) and x·im(u) + y·im(v)",
				"re(&x * u + &y * v) = x * re(u) + y * re(v) ∧ im(&x * u + &y * v) = x * im(u) + y * im(v)",
				Simp(
					complex_field.Parts,
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexOfRealDef)),
				ByArith())
			vanish := arg.Have(
				"both vanish, x·u + y·v being 0",
				"x * re(u) + y * re(v) = &0 ∧ x * im(u) + y * im(v) = &0",
				ByArith(
					combination,
					partsOf,
					complex_field.ComplexEq.At(arg.TermAs[Complex]("&x * u + &y * v"), arg.TermAs[Complex]("&0")),
					complex_field.PartsOfReal.At(zero)))
			parts := arg.Conjuncts(
				vanish,
				"x·re(u) + y·re(v) is 0",
				"x·im(u) + y·im(v) is 0")
			products := arg.Have(
				"so x·D and y·D are 0",
				"x * (re(u) * im(v) - im(u) * re(v)) = &0 ∧ y * (re(u) * im(v) - im(u) * re(v)) = &0",
				ByArith(Scaled(imV, parts[0]), Scaled(reV, parts[1]), Scaled(reU, parts[1]), Scaled(imU, parts[0])))
			arg.Show(
				"and D is not 0",
				By(
					nonzero,
					products,
					real_ring.MulEqZero.At(x, determinant),
					real_ring.MulEqZero.At(y, determinant)))
		}),
})}

// TriangleSplitAt — a triangle splits at any of its points p into the three
// triangles with p as a vertex and a side of the triangle as the opposite
// side, each run with the orientation of the whole: the three edges from p
// are each run once each way, so their integrals cancel. Each lies in the
// triangle, so f is continuous along it.
var TriangleSplitAt = triangleSplitAtThm{family.Add(registry.ProofEntry{
	Name: "TriangleSplitAt",
	Key:  "prop_ec6e132d35020429",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c p:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
			"p ∈ «triangle»(a, b, c)",
		},
		Conclusion: "«boundaryInt»(f, a, b, c) = " +
			"«boundaryInt»(f, a, b, p) + «boundaryInt»(f, b, c, p) + «boundaryInt»(f, c, a, p)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			a, b, c, p *Expr[Complex],
			continuous, inside Fact,
		) {
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
			arg.Show(
				"the edges from p to the vertices are each run once each way, and their integrals cancel",
				ByArith(
					vertices[0],
					vertices[1],
					vertices[2],
					inside,
					along.At(b, p),
					along.At(c, p),
					along.At(a, p),
					path_integral.SegmentReverse.At(f, b, p),
					path_integral.SegmentReverse.At(f, c, p),
					path_integral.SegmentReverse.At(f, a, p)))
		}),
})}

// TriangleFlat — a flat triangle, im(conj(b − a)·(c − a)) being 0, has
// boundary integral zero for f continuous on it: one vertex lies on the side
// joining the other two, so that side splits there into the two other sides
// run the other way. If b is a it lies on the side from a to c, at its start.
// Otherwise c − a is a real multiple k·(b − a): for k in ⟦0, 1⟧ c lies on the
// side from a to b, at time k; for k > 1, b lies on the side from a to c, at
// time 1/k; and for k < 0, c − b being (1 − k)·(a − b), a lies on the side
// from b to c, at time 1/(1 − k).
var TriangleFlat = triangleFlatThm{family.Add(registry.ProofEntry{
	Name: "TriangleFlat",
	Key:  "prop_7d70f286f1e5bd63",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
			"im(conj(b - a) * (c - a)) = &0",
		},
		Conclusion: "«boundaryInt»(f, a, b, c) = &0",
	},
		func(arg *Argument, f *Arrow[Complex, Complex], a, b, c *Expr[Complex], continuous, flat Fact) {
			zero := arg.TermAs[Real]("&0")
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
			arg.Cases(arg.Term("b = a"))
			arg.When(
				"if b is a, it is the start of the side from a to c",
				func(d *Argument, same Fact) {
					start := d.Have(
						"b is the point of the side from a to c at time 0",
						"&0 ≤ &0 ∧ &0 ≤ &1 ∧ b = segment_path(a, c, &0)",
						ByArith(same, path_integral.SegmentPathDef.At(a, c, zero)))
					d.Show(
						"so that side splits at b into the sides from a to b and from b to c",
						ByArith(
							start,
							vertices[0],
							vertices[2],
							along.At(a, c),
							path_integral.SegmentSplit.At(f, a, c, zero),
							path_integral.SegmentReverse.At(f, a, c)))
				})
			arg.Otherwise(
				"otherwise c − a is a real multiple of b − a",
				func(d *Argument, apart Fact) {
					nonzero := d.Have(
						"b − a is not 0",
						"b - a ≠ &0",
						ByArith(apart))
					k, multiple := d.ObtainAs[Real](
						"c − a is k·(b − a) for a real k",
						"∃k:real. c - a = &k * (b - a)",
						By(nonzero, flat, ParallelRealMultiple.At(d.TermAs[Complex]("b - a"), d.TermAs[Complex]("c - a"))))
					d.Cases(d.Term("k < &0"))
					d.When(
						"for k < 0, a lies between b and c",
						func(e *Argument, negative Fact) {
							time := e.TermAs[Real]("&1 / (&1 - k)")
							reciprocal := e.Have(
								"1/(1 − k) lies in ⟦0, 1⟧ and is the inverse of 1 − k",
								"&0 ≤ &1 / (&1 - k) ∧ &1 / (&1 - k) ≤ &1 ∧ &1 / (&1 - k) * (&1 - k) = &1",
								ByArith(negative))
							fromB := e.Have(
								"c − b is (1 − k)·(a − b)",
								"c - b = &(&1 - k) * (a - b)",
								Simp(Fwd(complex_field.OfRealSub)),
								ByArith(multiple))
							inverse := e.Have(
								"so 1/(1 − k) times 1 − k is 1 in ℂ too",
								"&(&1 / (&1 - k)) * &(&1 - k) = &1",
								By(reciprocal, complex_field.OfRealMul.At(time, e.TermAs[Real]("&1 - k"))))
							onSide := e.Have(
								"a is the point of the side from b to c at time 1/(1 − k)",
								"a = segment_path(b, c, &1 / (&1 - k))",
								ByArith(
									Scaled(e.TermAs[Complex]("&(&1 / (&1 - k))"), fromB),
									Scaled(e.TermAs[Complex]("a - b"), inverse),
									path_integral.SegmentPathDef.At(b, c, time)))
							e.Show(
								"so the side from b to c splits at a into the sides from b to a and from a to c",
								ByArith(
									reciprocal,
									onSide,
									vertices[0],
									vertices[1],
									vertices[2],
									along.At(b, c),
									along.At(a, b),
									along.At(a, c),
									path_integral.SegmentSplit.At(f, b, c, time),
									path_integral.SegmentReverse.At(f, a, b),
									path_integral.SegmentReverse.At(f, a, c)))
						})
					d.Otherwise(
						"for k ≥ 0, c lies on the side from a to b or b on the side from a to c",
						func(e *Argument, nonnegative Fact) {
							e.Cases(e.Term("k ≤ &1"))
							e.When(
								"for k in ⟦0, 1⟧, c lies on the side from a to b",
								func(g *Argument, atMost Fact) {
									inUnit := g.Have(
										"k lies in ⟦0, 1⟧",
										"&0 ≤ k ∧ k ≤ &1",
										ByArith(nonnegative, atMost))
									onSide := g.Have(
										"c is the point of the side from a to b at time k",
										"c = segment_path(a, b, k)",
										ByArith(multiple, path_integral.SegmentPathDef.At(a, b, k)))
									g.Show(
										"so the side from a to b splits at c into the sides from a to c and from c to b",
										ByArith(
											inUnit,
											onSide,
											vertices[0],
											vertices[1],
											vertices[2],
											along.At(a, b),
											along.At(b, c),
											along.At(a, c),
											path_integral.SegmentSplit.At(f, a, b, k),
											path_integral.SegmentReverse.At(f, b, c),
											path_integral.SegmentReverse.At(f, a, c)))
								})
							e.Otherwise(
								"for k > 1, b lies on the side from a to c",
								func(g *Argument, beyond Fact) {
									time := g.TermAs[Real]("&1 / k")
									reciprocal := g.Have(
										"1/k lies in ⟦0, 1⟧ and is the inverse of k",
										"&0 ≤ &1 / k ∧ &1 / k ≤ &1 ∧ &1 / k * k = &1",
										ByArith(beyond))
									inverse := g.Have(
										"so 1/k times k is 1 in ℂ too",
										"&(&1 / k) * &k = &1",
										By(reciprocal, complex_field.OfRealMul.At(time, k)))
									onSide := g.Have(
										"b is the point of the side from a to c at time 1/k",
										"b = segment_path(a, c, &1 / k)",
										ByArith(
											Scaled(g.TermAs[Complex]("&(&1 / k)"), multiple),
											Scaled(g.TermAs[Complex]("b - a"), inverse),
											path_integral.SegmentPathDef.At(a, c, time)))
									g.Show(
										"so the side from a to c splits at b into the sides from a to b and from b to c",
										ByArith(
											reciprocal,
											onSide,
											vertices[0],
											vertices[2],
											along.At(a, c),
											path_integral.SegmentSplit.At(f, a, c, time),
											path_integral.SegmentReverse.At(f, a, c)))
								})
						})
				})
		}),
})}

// TriangleCutCorner — cutting off the corner at p of a triangle along the
// segment from b_τ to c_τ, the points at time τ of its sides from p, the
// boundary integral is the sum of those round the corner triangle p b_τ c_τ
// and the two triangles b_τ b c and b_τ c c_τ covering the rest. The sides
// from p to b and from c to p split at b_τ and c_τ, and the edges from b_τ to
// c_τ and from b_τ to c are each run once each way, so their integrals
// cancel.
var TriangleCutCorner = triangleCutCornerThm{family.Add(registry.ProofEntry{
	Name: "TriangleCutCorner",
	Key:  "prop_8ff0a8873d66ff9e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p b c:complex. ∀τ:real.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)",
			"&0 ≤ τ",
			"τ ≤ &1",
		},
		Conclusion: "«boundaryInt»(f, p, b, c) = " +
			"«boundaryInt»(f, p, segment_path(p, b, τ), segment_path(p, c, τ)) + " +
			"«boundaryInt»(f, segment_path(p, b, τ), b, c) + " +
			"«boundaryInt»(f, segment_path(p, b, τ), c, segment_path(p, c, τ))",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			p, b, c *Expr[Complex],
			τ *Expr[Real],
			continuous, low, high Fact,
		) {
			bt, ct := arg.TermAs[Complex]("segment_path(p, b, τ)"), arg.TermAs[Complex]("segment_path(p, c, τ)")
			along := arg.Have(
				"f is continuous along a segment between two points of the triangle, the triangle being convex",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ «triangle»(p, b, c)",
						"w ∈ «triangle»(p, b, c)",
					},
					Conclusion: "∀s:real. &0 ≤ s ∧ s ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, s))",
				},
				By(
					continuous,
					At(TriangleConvex, p, b, c),
					At(ContinuousAlongSegment, arg.TermAs[Set[Complex]]("«triangle»(p, b, c)"), f)))
			vertices := arg.Conjuncts(
				TriangleVertices.At(p, b, c),
				"p lies in the triangle",
				"so does b",
				"and so does c")
			cuts := arg.Have(
				"b_τ and c_τ lie in the triangle, on its sides from p",
				"segment_path(p, b, τ) ∈ «triangle»(p, b, c) ∧ segment_path(p, c, τ) ∈ «triangle»(p, b, c)",
				By(
					vertices[0],
					vertices[1],
					vertices[2],
					low,
					high,
					TriangleConvex.At(p, b, c, p, b, τ),
					TriangleConvex.At(p, b, c, p, c, τ)))
			rest := arg.Have(
				"1 − τ lies in ⟦0, 1⟧",
				"&0 ≤ &1 - τ ∧ &1 - τ ≤ &1",
				ByArith(low, high))
			backwards := arg.Have(
				"run from c, the side to p reaches c_τ at time 1 − τ",
				"segment_path(c, p, &1 - τ) = segment_path(p, c, τ)",
				Simp(Fwd(path_integral.SegmentPathDef), Fwd(complex_field.OfRealSub)),
				ByArith())
			splitPB := arg.Have(
				"the side from p to b splits at b_τ",
				"«segInt»(f, p, b) = «segInt»(f, p, segment_path(p, b, τ)) + «segInt»(f, segment_path(p, b, τ), b)",
				By(low, high, vertices[0], vertices[1], along.At(p, b), path_integral.SegmentSplit.At(f, p, b, τ)))
			splitCP := arg.Have(
				"the side from c to p splits at c_τ",
				"«segInt»(f, c, p) = «segInt»(f, c, segment_path(p, c, τ)) + «segInt»(f, segment_path(p, c, τ), p)",
				backwards.RwRev(),
				By(
					rest,
					vertices[2],
					vertices[0],
					along.At(c, p),
					path_integral.SegmentSplit.At(f, c, p, arg.TermAs[Real]("&1 - τ"))))
			inner := arg.Have(
				"the edges from b_τ to c_τ and from b_τ to c are "+
					"each run once each way, and their integrals cancel",
				"«segInt»(f, segment_path(p, c, τ), segment_path(p, b, τ)) = "+
					"-«segInt»(f, segment_path(p, b, τ), segment_path(p, c, τ)) ∧ "+
					"«segInt»(f, c, segment_path(p, b, τ)) = -«segInt»(f, segment_path(p, b, τ), c)",
				By(
					cuts,
					vertices[2],
					along.At(bt, ct),
					along.At(bt, c),
					path_integral.SegmentReverse.At(f, bt, ct),
					path_integral.SegmentReverse.At(f, bt, c)))
			arg.Show(
				"the three boundaries add up to the large one",
				ByArith(splitPB, splitCP, inner))
		}),
})}

// TriangleCornerApart — when the triangle p b c is not flat, the two pieces
// left by cutting off its corner at p, the triangles b_τ b c and b_τ c c_τ for
// b_τ and c_τ the points at time τ of its sides from p, 0 < τ ≤ 1, miss p. A
// point of either is p plus a real combination of b − p and c − p whose
// coefficients add up to τ + (s + r)·(1 − τ), or to τ + s·(1 − τ), for its
// coordinates s and r in the piece; positive sums, so by independence the
// point is not p.
var TriangleCornerApart = triangleCornerApartThm{family.Add(registry.ProofEntry{
	Name: "TriangleCornerApart",
	Key:  "prop_21f62666aebf646a",
	Build: family.Theorem(Statement{
		Binders: "∀p b c:complex. ∀τ:real.",
		Hypotheses: []string{
			"im(conj(b - p) * (c - p)) ≠ &0",
			"&0 < τ",
			"τ ≤ &1",
		},
		Conclusion: "p ∉ «triangle»(segment_path(p, b, τ), b, c) ∧ " +
			"p ∉ «triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ))",
	},
		func(arg *Argument, p, b, c *Expr[Complex], τ *Expr[Real], skew, positive, atMost Fact) {
			u, v := arg.TermAs[Complex]("b - p"), arg.TermAs[Complex]("c - p")
			one := arg.TermAs[Real]("&1")
			first := arg.Have(
				"every point of the triangle b_τ b c differs from p",
				"∀z:complex. z ∈ «triangle»(segment_path(p, b, τ), b, c) ⇒ z ≠ p",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("z")
					inside := d.Assume()
					same := d.Have(
						"suppose z is p",
						"z = p",
						By(d.SupposeNot()))
					s, r, at := d.Unpack2As[Real, Real](d.Unfolded(inside, path_integral.SegmentPathDef), "s", "r")
					coordinates := d.Conjuncts(
						at,
						"s is at least 0",
						"r is at least 0",
						"s + r is at most 1",
						"z is the point at (s, r) along the sides from b_τ")
					combination := d.Have(
						"so (τ + s − s·τ − r·τ)·(b − p) + r·(c − p) is 0",
						"&(τ + s - s * τ - r * τ) * (b - p) + &r * (c - p) = &0",
						Simp(Fwd(complex_field.OfRealSub), Fwd(complex_field.OfRealAdd), Fwd(complex_field.OfRealMul)),
						ByArith(same, coordinates[3]))
					sum := d.Have(
						"its two coefficients add up to τ + (s + r)·(1 − τ), which is positive",
						"&0 < τ + s - s * τ - r * τ + r",
						ByArith(
							coordinates[0],
							coordinates[1],
							positive,
							atMost,
							real_order_ring.LessEqMulLeft.At(s, τ, one),
							real_order_ring.LessEqMulLeft.At(r, τ, one)))
					d.Show(
						"while by independence both would be 0",
						ByArith(
							skew,
							combination,
							sum,
							SkewIndependent.At(u, v, d.TermAs[Real]("τ + s - s * τ - r * τ"), r)))
				}))
			second := arg.Have(
				"every point of the triangle b_τ c c_τ differs from p",
				"∀z:complex. z ∈ «triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ)) ⇒ z ≠ p",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("z")
					inside := d.Assume()
					same := d.Have(
						"suppose z is p",
						"z = p",
						By(d.SupposeNot()))
					s, _, at := d.Unpack2As[Real, Real](d.Unfolded(inside, path_integral.SegmentPathDef), "s", "r")
					coordinates := d.Conjuncts(
						at,
						"s is at least 0",
						"r is at least 0",
						"s + r is at most 1",
						"z is the point at (s, r) along the sides from b_τ")
					combination := d.Have(
						"so (τ − s·τ − r·τ)·(b − p) + (s + r·τ)·(c − p) is 0",
						"&(τ - s * τ - r * τ) * (b - p) + &(s + r * τ) * (c - p) = &0",
						Simp(Fwd(complex_field.OfRealSub), Fwd(complex_field.OfRealAdd), Fwd(complex_field.OfRealMul)),
						ByArith(same, coordinates[3]))
					sum := d.Have(
						"its two coefficients add up to τ + s·(1 − τ), which is positive",
						"&0 < τ - s * τ - r * τ + (s + r * τ)",
						ByArith(coordinates[0], positive, atMost, real_order_ring.LessEqMulLeft.At(s, τ, one)))
					d.Show(
						"while by independence both would be 0",
						ByArith(
							skew,
							combination,
							sum,
							SkewIndependent.At(u, v, d.TermAs[Real]("τ - s * τ - r * τ"), d.TermAs[Real]("s + r * τ"))))
				}))
			arg.Show(
				"so neither piece holds p",
				By(first.At(p), second.At(p)))
		}),
})}

// TriangleShrinkToCorner — for f continuous on a triangle that is not flat
// and holomorphic there except at the vertex p, the boundary integral is that
// of every corner triangle p b_τ c_τ, b_τ and c_τ the points at time τ of the
// sides from p, 0 < τ ≤ 1. Cut off that corner: the two pieces left lie in
// the triangle and miss p, so f is holomorphic on them and by Goursat their
// boundary integrals are 0.
var TriangleShrinkToCorner = triangleShrinkToCornerThm{family.Add(registry.ProofEntry{
	Name: "TriangleShrinkToCorner",
	Key:  "prop_b05605f5cc5597d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p b c:complex. ∀τ:real.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)",
			"holomorphic_on(«triangle»(p, b, c) ∖ {p}, f)",
			"im(conj(b - p) * (c - p)) ≠ &0",
			"&0 < τ",
			"τ ≤ &1",
		},
		Conclusion: "«boundaryInt»(f, p, b, c) = " +
			"«boundaryInt»(f, p, segment_path(p, b, τ), segment_path(p, c, τ))",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			p, b, c *Expr[Complex],
			τ *Expr[Real],
			continuous, holomorphic, skew, positive, atMost Fact,
		) {
			bt, ct := arg.TermAs[Complex]("segment_path(p, b, τ)"), arg.TermAs[Complex]("segment_path(p, c, τ)")
			punctured := arg.TermAs[Set[Complex]]("«triangle»(p, b, c) ∖ {p}")
			vertices := arg.Conjuncts(
				TriangleVertices.At(p, b, c),
				"p lies in the triangle",
				"so does b",
				"and so does c")
			low := arg.Have(
				"τ is at least 0",
				"&0 ≤ τ",
				ByArith(positive))
			cuts := arg.Have(
				"b_τ and c_τ lie in the triangle, on its sides from p",
				"segment_path(p, b, τ) ∈ «triangle»(p, b, c) ∧ segment_path(p, c, τ) ∈ «triangle»(p, b, c)",
				By(
					vertices[0],
					vertices[1],
					vertices[2],
					low,
					atMost,
					TriangleConvex.At(p, b, c, p, b, τ),
					TriangleConvex.At(p, b, c, p, c, τ)))
			apart := arg.Conjuncts(
				GroupPremises(skew, positive, atMost, TriangleCornerApart.At(p, b, c, τ)),
				"p is off the piece b_τ b c",
				"and off the piece b_τ c c_τ")
			firstInside := arg.Have(
				"the piece b_τ b c lies in the triangle",
				"«triangle»(segment_path(p, b, τ), b, c) ⊆ «triangle»(p, b, c)",
				By(cuts, vertices[1], vertices[2], TriangleSubset.At(p, b, c, bt, b, c)))
			secondInside := arg.Have(
				"so does the piece b_τ c c_τ",
				"«triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ)) ⊆ «triangle»(p, b, c)",
				By(cuts, vertices[2], TriangleSubset.At(p, b, c, bt, c, ct)))
			firstOff := arg.Have(
				"so the piece b_τ b c lies in the triangle without p",
				"«triangle»(segment_path(p, b, τ), b, c) ⊆ «triangle»(p, b, c) ∖ {p}",
				BySets(firstInside, apart[0]))
			secondOff := arg.Have(
				"and so does the piece b_τ c c_τ",
				"«triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ)) ⊆ «triangle»(p, b, c) ∖ {p}",
				BySets(secondInside, apart[1]))
			firstPiece := arg.TermAs[Set[Complex]]("«triangle»(segment_path(p, b, τ), b, c)")
			secondPiece := arg.TermAs[Set[Complex]](
				"«triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ))")
			firstHolomorphic := arg.Have(
				"f is holomorphic on the piece b_τ b c",
				"holomorphic_on(«triangle»(segment_path(p, b, τ), b, c), f)",
				By(holomorphic, firstOff, complex_derivative.HolomorphicOnSubset.At(punctured, firstPiece, f)))
			secondHolomorphic := arg.Have(
				"and on the piece b_τ c c_τ",
				"holomorphic_on(«triangle»(segment_path(p, b, τ), c, segment_path(p, c, τ)), f)",
				By(holomorphic, secondOff, complex_derivative.HolomorphicOnSubset.At(punctured, secondPiece, f)))
			firstZero := arg.Have(
				"so by Goursat the boundary integral round the piece b_τ b c is 0",
				"«boundaryInt»(f, segment_path(p, b, τ), b, c) = &0",
				By(firstHolomorphic, Goursat.At(f, bt, b, c)))
			secondZero := arg.Have(
				"and so is that round the piece b_τ c c_τ",
				"«boundaryInt»(f, segment_path(p, b, τ), c, segment_path(p, c, τ)) = &0",
				By(secondHolomorphic, Goursat.At(f, bt, c, ct)))
			arg.Show(
				"so cutting off the corner leaves the boundary integral of the corner triangle",
				ByArith(continuous, low, atMost, TriangleCutCorner.At(f, p, b, c, τ), firstZero, secondZero))
		}),
})}

// GoursatAtVertex — a function continuous on a triangle and holomorphic there
// except at the vertex p has integral zero round its boundary. A flat
// triangle has. Otherwise the boundary integral is that of every corner
// triangle at p with sides τ times the triangle's, 0 < τ ≤ 1. Near p, f is
// within 1 of f(p), so on a corner triangle within that distance f is at
// most |f(p)| + 1, and its boundary integral at most (|f(p)| + 1)·P·τ, P the
// perimeter, for every small enough τ > 0; so its size is at most 0.
var GoursatAtVertex = goursatAtVertexThm{family.Add(registry.ProofEntry{
	Name: "GoursatAtVertex",
	Key:  "prop_5ca62046cb66be0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)",
			"holomorphic_on(«triangle»(p, b, c) ∖ {p}, f)",
		},
		Conclusion: "«boundaryInt»(f, p, b, c) = &0",
		Abbrev: Abbrev{
			{Name: "P", Text: "«perimeter»(p, b, c)"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			p, b, c *Expr[Complex],
			continuous, holomorphic Fact,
		) {
			vertices := arg.Conjuncts(
				TriangleVertices.At(p, b, c),
				"p lies in the triangle",
				"so does b",
				"and so does c")
			arg.Cases(arg.Term("im(conj(b - p) * (c - p)) = &0"))
			arg.When(
				"a flat triangle has boundary integral 0",
				func(d *Argument, flat Fact) {
					d.Show(
						"its sides being parallel",
						By(continuous, flat, TriangleFlat.At(f, p, b, c)))
				})
			arg.Otherwise(
				"otherwise the corner triangles at p shrink to p",
				func(d *Argument, skew Fact) {
					one := d.TermAs[Real]("&1")
					fp := d.TermAs[Complex]("f(p)")
					atP := d.Have(
						"f is continuous at p",
						"complex_continuous_at(f, p)",
						By(vertices[0], continuous))
					δ, near := d.ObtainAs[Real](
						"near p, f is within 1 of f(p)",
						"∃δ:real. &0 < δ ∧ ∀z:complex. |z - p| < δ ⇒ |f(z) - f(p)| < &1",
						By(d.Unfolded(atP, complex_topology.ComplexContinuousAtDef).At(one)))
					within := d.Conjuncts(
						near,
						"δ is positive",
						"within δ of p, f is within 1 of f(p)")
					sides := d.Have(
						"P + 1 is positive",
						"&0 < «P» + &1",
						ByArith(
							complex_abs.AbsNonneg.At(d.TermAs[Complex]("b - p")),
							complex_abs.AbsNonneg.At(d.TermAs[Complex]("c - b")),
							complex_abs.AbsNonneg.At(d.TermAs[Complex]("p - c"))))
					perimeterPlus := d.TermAs[Real]("«P» + &1")
					reach := d.TermAs[Real]("δ / («P» + &1)")
					shrink := d.Have(
						"for 0 < τ ≤ min(1, δ/(P + 1)) the boundary integral is at most (|f(p)| + 1)·P·τ",
						Statement{
							Binders: "∀τ:real.",
							Hypotheses: []string{
								"&0 < τ",
								"τ ≤ min(&1, δ / («P» + &1))",
							},
							Conclusion: "|«boundaryInt»(f, p, b, c)| ≤ (|f(p)| + &1) * «P» * τ",
						},
						Derive(func(e *Argument) {
							τ := e.FixAs[Real]("τ")
							given := e.Assume()
							bounds := e.Conjuncts(
								given,
								"τ is positive",
								"τ is at most min(1, δ/(P + 1))")
							small := e.Conjuncts(
								e.Have(
									"so τ is at most 1, and τ·(P + 1) at most δ",
									"τ ≤ &1 ∧ τ * («P» + &1) ≤ δ",
									By(
										bounds[1],
										sides,
										real_sup_inf.LessEqMin.At(one, reach, τ),
										real_order_field.LessEqDivMulLeft.At(τ, δ, perimeterPlus))),
								"τ is at most 1",
								"τ·(P + 1) is at most δ")
							bt := e.TermAs[Complex]("segment_path(p, b, τ)")
							ct := e.TermAs[Complex]("segment_path(p, c, τ)")
							low := e.Have(
								"τ is at least 0",
								"&0 ≤ τ",
								ByArith(bounds[0]))
							cuts := e.Have(
								"the points at time τ of the sides from p lie in the triangle",
								"segment_path(p, b, τ) ∈ «triangle»(p, b, c) ∧ segment_path(p, c, τ) ∈ «triangle»(p, b, c)",
								By(
									vertices[0],
									vertices[1],
									vertices[2],
									low,
									small[0],
									TriangleConvex.At(p, b, c, p, b, τ),
									TriangleConvex.At(p, b, c, p, c, τ)))
							corner := e.Have(
								"so the corner triangle they cut off lies in the triangle",
								"«triangle»(p, segment_path(p, b, τ), segment_path(p, c, τ)) ⊆ «triangle»(p, b, c)",
								By(vertices[0], cuts, TriangleSubset.At(p, b, c, p, bt, ct)))
							sides := e.Conjuncts(
								e.Have(
									"its sides are τ times the triangle's",
									"segment_path(p, b, τ) - p = &τ * (b - p) ∧ "+
										"segment_path(p, c, τ) - segment_path(p, b, τ) = &τ * (c - b) ∧ "+
										"p - segment_path(p, c, τ) = &τ * (p - c)",
									Simp(Fwd(path_integral.SegmentPathDef)),
									ByArith()),
								"the side from p to b_τ is τ·(b − p)",
								"the side from b_τ to c_τ is τ·(c − b)",
								"the side from c_τ to p is τ·(p − c)")
							size := e.Have(
								"|τ| is τ",
								"|&τ| = τ",
								By(low, complex_abs.AbsOfNonnegReal.At(τ)))
							perimeter := e.Have(
								"so its perimeter is τ·P",
								"«perimeter»(p, segment_path(p, b, τ), segment_path(p, c, τ)) = τ * «P»",
								sides[0].Rw(),
								sides[1].Rw(),
								sides[2].Rw(),
								ByArith(
									complex_abs.AbsMul.At(e.TermAs[Complex]("&τ"), e.TermAs[Complex]("b - p")),
									complex_abs.AbsMul.At(e.TermAs[Complex]("&τ"), e.TermAs[Complex]("c - b")),
									complex_abs.AbsMul.At(e.TermAs[Complex]("&τ"), e.TermAs[Complex]("p - c")),
									Scaled(e.TermAs[Real]("|b - p|"), size),
									Scaled(e.TermAs[Real]("|c - b|"), size),
									Scaled(e.TermAs[Real]("|p - c|"), size)))
							bound := e.Have(
								"on the corner triangle f is continuous and at most |f(p)| + 1",
								Statement{
									Binders: "∀z:complex.",
									Hypotheses: []string{
										"z ∈ «triangle»(p, segment_path(p, b, τ), segment_path(p, c, τ))",
									},
									Conclusion: "complex_continuous_at(f, z) ∧ |f(z)| ≤ |f(p)| + &1",
								},
								Derive(func(g *Argument) {
									z := g.FixAs[Complex]("z")
									inside := g.Assume()
									apex := g.Conjuncts(
										TriangleVertices.At(p, bt, ct),
										"p lies in the corner triangle",
										"so does b_τ",
										"and so does c_τ")
									distance := g.Have(
										"z is at most τ·P from p, so within δ of it",
										"|z - p| < δ",
										ByArith(inside, apex[0], perimeter, bounds[0], small[1], TriangleDiameter.At(p, bt, ct, z, p)))
									there := g.Have(
										"f is continuous at z, a point of the triangle",
										"complex_continuous_at(f, z)",
										By(inside, g.Unfolded(corner, set_basic.SubsetDef).At(z), continuous.At(z)))
									size := g.Have(
										"f(z) is within 1 of f(p), so at most |f(p)| + 1",
										"|f(z)| ≤ |f(p)| + &1",
										ByArith(
											distance,
											within[1].At(z),
											complex_abs.AbsTriangleReverse.At(g.TermAs[Complex]("f(z)"), fp)))
									g.Show(
										"both hold at z",
										By(there, size))
								}))
							equal := e.Have(
								"the boundary integral is that of the corner triangle",
								"«boundaryInt»(f, p, b, c) = «boundaryInt»(f, p, segment_path(p, b, τ), segment_path(p, c, τ))",
								By(continuous, holomorphic, skew, bounds[0], small[0], TriangleShrinkToCorner.At(f, p, b, c, τ)))
							e.Show(
								"which is at most (|f(p)| + 1) times its perimeter τ·P",
								equal.Rw(),
								ByArith(
									bound,
									TriangleBoundaryBound.At(f, p, bt, ct, e.TermAs[Real]("|f(p)| + &1")),
									Scaled(e.TermAs[Real]("|f(p)| + &1"), perimeter)))
						}))
					positive := d.Have(
						"min(1, δ/(P + 1)) is positive, 1 and δ/(P + 1) being so",
						"&0 < min(&1, δ / («P» + &1))",
						By(
							sides,
							within[0],
							real_order_field.DivPos.At(δ, perimeterPlus),
							real_sup_inf.LessThanMin.At(one, reach, d.TermAs[Real]("&0"))))
					integral := d.TermAs[Complex]("«boundaryInt»(f, p, b, c)")
					nonpositive := d.Have(
						"a size at most (|f(p)| + 1)·P·τ for every small enough τ > 0 is at most 0",
						"|«boundaryInt»(f, p, b, c)| ≤ &0",
						By(
							positive,
							shrink,
							real_order_field.NonposOfSmallMultiples.At(
								d.TermAs[Real]("|«boundaryInt»(f, p, b, c)|"),
								d.TermAs[Real]("(|f(p)| + &1) * «P»"),
								d.TermAs[Real]("min(&1, δ / («P» + &1))"))))
					d.Show(
						"so the boundary integral is 0",
						ByArith(nonpositive, complex_abs.AbsNonneg.At(integral), complex_abs.AbsEqZero.At(integral)))
				})
		}),
})}

// GoursatExceptPoint — a function continuous on a closed triangle and
// holomorphic there except at one point p has integral zero round its
// boundary. If p lies off the triangle, f is holomorphic on it and this is
// Goursat. Otherwise the triangle splits at p into three triangles with p as
// a vertex, each inside the triangle, and round each the integral is zero.
var GoursatExceptPoint = goursatExceptPointThm{family.Add(registry.ProofEntry{
	Name: "GoursatExceptPoint",
	Key:  "prop_924585389c3fcfee",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c p:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
			"holomorphic_on(«triangle»(a, b, c) ∖ {p}, f)",
		},
		Conclusion: "«boundaryInt»(f, a, b, c) = &0",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			a, b, c, p *Expr[Complex],
			continuous, holomorphic Fact,
		) {
			whole := arg.TermAs[Set[Complex]]("«triangle»(a, b, c)")
			punctured := arg.TermAs[Set[Complex]]("«triangle»(a, b, c) ∖ {p}")
			arg.Cases(arg.Term("p ∈ «triangle»(a, b, c)"))
			arg.When(
				"if p lies in the triangle, split the triangle at p",
				func(d *Argument, inside Fact) {
					vertices := d.Conjuncts(
						TriangleVertices.At(a, b, c),
						"a lies in the triangle",
						"so does b",
						"and so does c")
					corner := d.Have(
						"round a triangle with vertex p and its other vertices in the triangle the integral is 0",
						"∀u v:complex. u ∈ «triangle»(a, b, c) ∧ v ∈ «triangle»(a, b, c) ⇒ «boundaryInt»(f, p, u, v) = &0",
						Derive(func(e *Argument) {
							u := e.FixAs[Complex]("u")
							v := e.FixAs[Complex]("v")
							given := e.Assume()
							within := e.Conjuncts(
								given,
								"u lies in the triangle",
								"and so does v")
							small := e.TermAs[Set[Complex]]("«triangle»(p, u, v) ∖ {p}")
							inner := e.Have(
								"the triangle p u v lies in the triangle",
								"«triangle»(p, u, v) ⊆ «triangle»(a, b, c)",
								By(inside, within[0], within[1], TriangleSubset.At(a, b, c, p, u, v)))
							off := e.Have(
								"so without p it lies in the triangle without p",
								"«triangle»(p, u, v) ∖ {p} ⊆ «triangle»(a, b, c) ∖ {p}",
								BySets(inner))
							continuousThere := e.Have(
								"f is continuous on the triangle p u v",
								"∀z:complex. z ∈ «triangle»(p, u, v) ⇒ complex_continuous_at(f, z)",
								By(e.Unfolded(inner, set_basic.SubsetDef), continuous))
							holomorphicThere := e.Have(
								"and holomorphic there except at p",
								"holomorphic_on(«triangle»(p, u, v) ∖ {p}, f)",
								By(holomorphic, off, complex_derivative.HolomorphicOnSubset.At(punctured, small, f)))
							e.Show(
								"so round it the integral is 0, p being a vertex",
								By(continuousThere, holomorphicThere, GoursatAtVertex.At(f, p, u, v)))
						}))
					d.Show(
						"so each of the three integrals is 0, and so is their sum",
						ByArith(
							continuous,
							inside,
							TriangleSplitAt.At(f, a, b, c, p),
							vertices[0],
							vertices[1],
							vertices[2],
							corner.At(a, b),
							corner.At(b, c),
							corner.At(c, a)))
				})
			arg.Otherwise(
				"otherwise f is holomorphic on the whole triangle",
				func(d *Argument, outside Fact) {
					missing := d.Have(
						"the triangle misses p, so lies in the triangle without p",
						"«triangle»(a, b, c) ⊆ «triangle»(a, b, c) ∖ {p}",
						BySets(outside))
					everywhere := d.Have(
						"so f is holomorphic on the triangle",
						"holomorphic_on(«triangle»(a, b, c), f)",
						By(holomorphic, missing, complex_derivative.HolomorphicOnSubset.At(punctured, whole, f)))
					d.Show(
						"and Goursat applies",
						By(everywhere, Goursat.At(f, a, b, c)))
				})
		}),
})}
