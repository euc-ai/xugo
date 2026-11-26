// lines.go — the complex derivative read along a real line t ↦ z + t·w.

package complex_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousAlongLine — a complex function continuous at a point z + t₀·w
// of a line is continuous along the line: its real and imaginary parts at
// z + t·w are continuous functions of the real t at t₀.
//
// On the real axis first. The reals sit in ℂ with their own distance,
// |&t − &c| = |t − c|, and each part of a difference is at most its
// modulus, so the radius that keeps h(ζ) within ε of h(&c) keeps each part
// of h(&t) within ε of that part of h(&c) for t within it of c. The line
// is the real axis carried by s ↦ z + s·w, a continuous map of ℂ, and g
// read through that map is continuous at &t₀; at a real s = &t it is g at
// the point z + t·w of the line.
var ContinuousAlongLine = continuousAlongLineThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAlongLine",
	Key:  "prop_666f42eba463e327",
	Build: family.Sections(Statement{
		Binders: "∀g:(complex → complex). ∀z w:complex. ∀t₀:real.",
		Hypotheses: []string{
			"complex_continuous_at(g, z + &t₀ * w)",
		},
		Conclusion: "real_continuous_at(λt:real. re(g(z + &t * w)), t₀) ∧ " +
			"real_continuous_at(λt:real. im(g(z + &t * w)), t₀)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// On the real axis: a function continuous at a real point c is
			// continuous at c along the reals, part by part.
			alongReals := ctx.Lemma(Statement{
				Binders: "∀h:(complex → complex). ∀c:real.",
				Hypotheses: []string{
					"complex_continuous_at(h, &c)",
				},
				Conclusion: "real_continuous_at(λt:real. re(h(&t)), c) ∧ real_continuous_at(λt:real. im(h(&t)), c)",
			},
				func(a *Argument, h *Arrow[Complex, Complex], c *Expr[Real], continuous Fact) {
					near := a.Unfolded(continuous, complex_topology.ComplexContinuousAtDef)
					radius := a.Have(
						"one radius serves both parts: the radius that keeps "+
							"h(ζ) within ε of h(&c) keeps each part of h(&t) within ε",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃δ:real. " +
								"    &0 < δ ∧ ∀t:real. |t - c| < δ ⇒ |re(h(&t)) - re(h(&c))| < ε ∧ |im(h(&t)) - im(h(&c))| < ε",
						},
						Derive(func(b *Argument) {
							ε := b.FixAs[Real]()
							pos := b.Assume()
							δ, ball := b.ObtainAs[Real](
								"continuity of h at &c hands over a radius δ inside which h(ζ) is within ε of h(&c)",
								"∃δ:real. &0 < δ ∧ ∀ζ:complex. |ζ - &c| < δ ⇒ |h(ζ) - h(&c)| < ε",
								By(near.At(ε), pos),
								Named("δ"))
							disc := b.Conjuncts(
								ball,
								"δ is positive",
								"and on the disc of radius δ about &c, h(ζ) is within ε of h(&c)")
							b.Take(δ)
							b.Do(SplitConj(
								Case(
									"the radius δ is positive, as it was obtained",
									By(disc[0])),
								Case(
									"a real t within δ of c is a point &t within δ of &c, where each part of h moves by less than ε",
									Derive(func(d *Argument) {
										t := d.FixAs[Real]()
										nearC := d.Assume()
										onAxis := d.TermAs[Complex]("&t")
										d.Show(
											"|&t − &c| = |t − c| < δ, so |h(&t) − h(&c)| < ε, and a part moves by at most that",
											ByArith(
												disc[1].At(onAxis),
												complex_abs.AbsOfRealSub.At(t, c),
												complex_abs.PartsNonexpanding.At(h.Apply(onAxis), h.Apply(d.TermAs[Complex]("&c"))),
												nearC))
									})),
							))
						}))
					a.Do(SplitConj(
						Case(
							"the real part of h(&t) is continuous at c, by the shared radius",
							Unfold(real_continuous.RealContinuousAtDef),
							By(radius)),
						Case(
							"and so is the imaginary part",
							Unfold(real_continuous.RealContinuousAtDef),
							By(radius)),
					))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					g *Arrow[Complex, Complex],
					z, w *Expr[Complex],
					t0 *Expr[Real],
					continuous Fact,
				) {
					start := a.TermAs[Complex]("&t₀")
					line := a.Have(
						"the line s ↦ z + s·w is continuous at &t₀: a constant plus the identity times a constant",
						"complex_continuous_at(λs:complex. z + s * w, &t₀)",
						By(
							complex_topology.ContinuousAtAdd,
							complex_topology.ContinuousAtMul,
							complex_topology.ContinuousAtConst.At(start, z),
							complex_topology.ContinuousAtId.At(start),
							complex_topology.ContinuousAtConst.At(start, w)))
					composite := a.Have(
						"g is continuous at the line's point z + t₀·w, so g read through the line is continuous at &t₀",
						"complex_continuous_at(g ∘ (λs:complex. z + s * w), &t₀)",
						By(complex_topology.ContinuousAtCompose, line, continuous))
					alongLine := a.Unfolded(composite, functions.ComposeApply)
					a.Show(
						"on the real axis that function has continuous parts, and at s = &t it is g(z + t·w)",
						By(alongLine, At(alongReals, a.TermAs[Fun[Complex, Complex]]("λs:complex. g(z + s * w)"), t0)))
				})
		}),
})}

// DerivativeAlongLine — a function with complex derivative l at a point
// z + t₀·w of a line, read along the line, has velocity l·w at t₀: its real
// and imaginary parts have real derivatives re(l·w) and im(l·w) there.
//
// By Carathéodory, f(ζ) − f(ζ₀) = φ(ζ)·(ζ − ζ₀) at ζ₀ = z + t₀·w, with φ
// continuous at ζ₀ and φ(ζ₀) = l. Along the line ζ(t) − ζ₀ = (t − t₀)·w,
// so the increment f(ζ(t)) − f(ζ₀) is φ(ζ(t))·w·(t − t₀), and t − t₀ being
// real, each part of the increment is the same part of φ(ζ(t))·w times
// t − t₀. That part of φ(ζ(t))·w is continuous at t₀, φ·w being continuous
// at ζ₀ (ContinuousAlongLine), and is the part of l·w there, so by
// Carathéodory's form on the line it is the derivative of that part of
// f(ζ(t)). The factorization holds at w = 0 too, so that case needs no
// argument of its own.
var DerivativeAlongLine = derivativeAlongLineThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAlongLine",
	Key:  "prop_2a473bc51c12c3b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w l:complex. ∀t₀:real.",
		Hypotheses: []string{
			"complex_derivative_at(f, z + &t₀ * w, l)",
		},
		Conclusion: "path_derivative_at(λt:real. f(z + &t * w), t₀, l * w)",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			z, w, l *Expr[Complex],
			t0 *Expr[Real],
			derivative Fact,
		) {
			start := a.TermAs[Complex]("z + &t₀ * w")
			_, factored := a.ObtainAs[Fun[Complex, Complex]](
				"by Carathéodory, f's increment from ζ₀ = z + t₀·w "+
					"factors through a slope φ continuous at ζ₀, with φ(ζ₀) = l",
				"∃φ:(complex → complex). "+
					"    (∀ζ:complex. f(ζ) - f(z + &t₀ * w) = φ(ζ) * (ζ - (z + &t₀ * w))) ∧ "+
					"    complex_continuous_at(φ, z + &t₀ * w) ∧ "+
					"    φ(z + &t₀ * w) = l",
				By(derivative, DerivativeCaratheodory.At(f, start, l)))
			slope := a.Conjuncts(
				factored,
				"f(ζ) − f(ζ₀) = φ(ζ)·(ζ − ζ₀) at every ζ",
				"φ is continuous at ζ₀",
				"φ(ζ₀) = l")
			increment := a.Have(
				"along the line ζ(t) − ζ₀ = (t − t₀)·w, so the increment of f from ζ₀ is φ(ζ(t))·w·(t − t₀)",
				"∀t:real. f(z + &t * w) - f(z + &t₀ * w) = φ(z + &t * w) * w * (&t - &t₀)",
				Derive(func(b *Argument) {
					b.FixAs[Real]()
					b.Show(
						"the factorization at z + t·w, where (z + t·w) − "+
							"(z + t₀·w) regroups as (t − t₀)·w in the ring of ℂ",
						ByArith(slope[0].At(b.TermAs[Complex]("z + &t * w"))))
				}))
			realMultiple := a.Have(
				"an equation u − v = p·(s − r) between complex numbers, with s and r real, holds part by part",
				Statement{
					Binders: "∀u v p:complex. ∀s r:real.",
					Hypotheses: []string{
						"u - v = p * (&s - &r)",
					},
					Conclusion: "re(u) - re(v) = re(p) * (s - r) ∧ im(u) - im(v) = im(p) * (s - r)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Complex]()
					b.FixAs[Complex]()
					b.FixAs[Complex]()
					b.FixAs[Real]()
					b.FixAs[Real]()
					equation := b.Assume()
					parts := b.Simplified(
						equation,
						complex_field.Parts,
						Fwd(complex_field.ComplexSubDef),
						Fwd(complex_field.ComplexAddDef),
						Fwd(complex_field.ComplexNegDef),
						Fwd(complex_field.ComplexMulDef),
						Fwd(complex_field.ComplexOfRealDef))
					b.Show(
						"the two sides computed part by part, the real numbers s and r having imaginary part 0",
						ByArith(parts))
				}))
			parts := a.Have(
				"so each part of the increment is the same part of φ(ζ(t))·w times t − t₀",
				"∀t:real. "+
					"    re(f(z + &t * w)) - re(f(z + &t₀ * w)) = re(φ(z + &t * w) * w) * (t - t₀) ∧ "+
					"    im(f(z + &t * w)) - im(f(z + &t₀ * w)) = im(φ(z + &t * w) * w) * (t - t₀)",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					b.Show(
						"the increment at t, read part by part",
						By(
							realMultiple.At(
								f.Apply(b.TermAs[Complex]("z + &t * w")),
								f.Apply(start),
								b.TermAs[Complex]("φ(z + &t * w) * w"),
								t,
								t0),
							increment.At(t)))
				}))
			slopeAlong := a.Conjuncts(
				a.Have(
					"the parts of φ(ζ(t))·w are continuous at t₀, φ·w being continuous at ζ₀",
					"real_continuous_at(λt:real. re(φ(z + &t * w) * w), t₀) ∧ "+
						"real_continuous_at(λt:real. im(φ(z + &t * w) * w), t₀)",
					By(
						ContinuousAlongLine.At(a.TermAs[Fun[Complex, Complex]]("λζ:complex. φ(ζ) * w"), z, w, t0),
						complex_topology.ContinuousAtMul,
						slope[1],
						complex_topology.ContinuousAtConst.At(start, w))),
				"the real part of φ(ζ(t))·w is continuous at t₀",
				"and so is its imaginary part")

			a.Do(Unfold(PathDerivativeAtDef), SplitConj(
				Case(
					"the real part: re(φ(ζ(t))·w) is a slope for re f(ζ(t)) at t₀, continuous there with value re(l·w)",
					Derive(func(b *Argument) {
						realSlope := b.Have(
							"t ↦ re(φ(ζ(t))·w) factors the increment of re f along "+
								"the line, is continuous at t₀ and is re(l·w) there",
							"∃ψ:(real → real). "+
								"    (∀t:real. re(f(z + &t * w)) - re(f(z + &t₀ * w)) = ψ(t) * (t - t₀)) ∧ "+
								"    real_continuous_at(ψ, t₀) ∧ "+
								"    ψ(t₀) = re(l * w)",
							Derive(func(c *Argument) {
								c.Take(c.TermAs[Fun[Real, Real]]("λt:real. re(φ(z + &t * w) * w)"))
								c.Do(slope[2].Rw())
								c.Show(
									"the real parts of the increment, and the continuity of the slope's real part",
									By(parts, slopeAlong[0]))
							}))
						b.Show(
							"so by Carathéodory's form on the line, re f(ζ(t)) has derivative re(l·w) at t₀",
							By(
								realSlope,
								real_derivative.DerivativeCaratheodory.At(
									b.TermAs[Fun[Real, Real]]("λt:real. re(f(z + &t * w))"),
									t0,
									b.TermAs[Real]("re(l * w)"))))
					})),
				Case(
					"the imaginary part: im(φ(ζ(t))·w) is a slope for im "+
						"f(ζ(t)) at t₀, continuous there with value im(l·w)",
					Derive(func(b *Argument) {
						imaginarySlope := b.Have(
							"t ↦ im(φ(ζ(t))·w) factors the increment of im f along "+
								"the line, is continuous at t₀ and is im(l·w) there",
							"∃ψ:(real → real). "+
								"    (∀t:real. im(f(z + &t * w)) - im(f(z + &t₀ * w)) = ψ(t) * (t - t₀)) ∧ "+
								"    real_continuous_at(ψ, t₀) ∧ "+
								"    ψ(t₀) = im(l * w)",
							Derive(func(c *Argument) {
								c.Take(c.TermAs[Fun[Real, Real]]("λt:real. im(φ(z + &t * w) * w)"))
								c.Do(slope[2].Rw())
								c.Show(
									"the imaginary parts of the increment, and the continuity of the slope's imaginary part",
									By(parts, slopeAlong[1]))
							}))
						b.Show(
							"so by Carathéodory's form on the line, im f(ζ(t)) has derivative im(l·w) at t₀",
							By(
								imaginarySlope,
								real_derivative.DerivativeCaratheodory.At(
									b.TermAs[Fun[Real, Real]]("λt:real. im(f(z + &t * w))"),
									t0,
									b.TermAs[Real]("im(l * w)"))))
					})),
			))
		}),
})}

// CauchyRiemann — the Cauchy–Riemann equations: where f has complex
// derivative l at c, f has velocity l along the horizontal line c + t and
// velocity i·l along the vertical line c + i·t, at t = 0; that is,
// ∂f/∂y = i·∂f/∂x. Read part by part, with u = re f and v = im f, they
// say ∂u/∂x = re l = ∂v/∂y and ∂v/∂x = im l = −∂u/∂y, the parts of i·l
// being −im l and re l.
//
// The partial derivatives in x and in y are the velocities at t = 0 along
// the two lines, and c is the point t = 0 of each. Along a line of
// direction w, f has velocity l·w (DerivativeAlongLine): at w = 1 this is
// l, and at w = i, where t·i is i·t, it is l·i = i·l.
var CauchyRiemann = cauchyRiemannThm{family.Add(registry.ProofEntry{
	Name: "CauchyRiemann",
	Key:  "prop_f25de357f8aaa2af",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
		},
		Conclusion: "path_derivative_at(λt:real. f(c + &t), &0, l) ∧ " +
			"path_derivative_at(λt:real. f(c + complex_i * &t), &0, complex_i * l)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], derivative Fact) {
			start := a.Have(
				"c is the point t = 0 of every line through it, so f has derivative l there",
				"∀w:complex. complex_derivative_at(f, c + &0 * w, l)",
				Derive(func(b *Argument) {
					b.FixAs[Complex]()
					origin := b.Have(
						"c + 0·w is c",
						"c + &0 * w = c",
						ByArith())
					b.Do(origin.Rw())
					b.Show(
						"f has derivative l at c",
						By(derivative))
				}))
			zero := a.TermAs[Real]("&0")
			one := a.TermAs[Complex]("&1")
			i := a.TermAs[Complex]("complex_i")
			alongOne := a.Have(
				"along the horizontal line c + t·1, f has velocity l·1 at 0",
				"path_derivative_at(λt:real. f(c + &t * &1), &0, l * &1)",
				By(start.At(one), DerivativeAlongLine.At(f, c, one, l, zero)))
			horizontal := a.Simplified(alongOne, Fwd(comm_monoid.RightIdentity.Read(complex_field.MulMonoid)))
			commute := a.Have(
				"a real number commutes with i",
				"∀t:real. &t * complex_i = complex_i * &t",
				a.ForEach(func(t *Expr[Real]) Action { return ByArith() }))
			turned := a.Have(
				"and so does l",
				"l * complex_i = complex_i * l",
				ByArith())
			alongI := a.Have(
				"along the vertical line c + t·i, f has velocity l·i at 0",
				"path_derivative_at(λt:real. f(c + &t * complex_i), &0, l * complex_i)",
				By(start.At(i), DerivativeAlongLine.At(f, c, i, l, zero)))
			vertical := a.Simplified(alongI, Fwd(commute))
			a.Show(
				"along 1 f has velocity l, and along i velocity l·i = i·l",
				turned.RwRev(),
				By(horizontal, vertical))
		}),
})}

// DerivativeZeroConstantOnConvex — a function with derivative 0 at every
// point of a convex set takes one value on it: f(z) = f(w) for any two
// points z and w of the set.
//
// The segment w + t·(z − w), 0 ≤ t ≤ 1, lies in the set, which is convex.
// Along it the real and imaginary parts of f have derivative
// re(0·(z − w)) = im(0·(z − w)) = 0 at every t (DerivativeAlongLine), so
// each part, a real function with derivative 0 on ⟦0, 1⟧, takes the same
// value at t = 1, where the segment is at z, as at t = 0, where it is at
// w. Two complex numbers with the same parts are equal.
var DerivativeZeroConstantOnConvex = derivativeZeroConstantOnConvexThm{family.Add(registry.ProofEntry{
	Name: "DerivativeZeroConstantOnConvex",
	Key:  "prop_c34708cb2ce00c1a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀U:set(complex). ∀z w:complex.",
		Hypotheses: []string{
			"∀u v:complex. ∀t:real. u ∈ U ∧ v ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ u + &t * (v - u) ∈ U",
			"∀u:complex. u ∈ U ⇒ complex_derivative_at(f, u, &0)",
			"z ∈ U",
			"w ∈ U",
		},
		Conclusion: "f(z) = f(w)",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			U *Expr[Set[Complex]],
			convex, derivatives Fact,
			z, w *Expr[Complex],
			zIn, wIn Fact,
		) {
			flat := a.Have(
				"a real function with derivative 0 at every point of ⟦0, 1⟧ takes the same value at its two ends",
				"∀g:(real → real). (∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ real_derivative_at(g, t, &0)) ⇒ g(&1) = g(&0)",
				Derive(func(b *Argument) {
					g := b.FixAs[Fun[Real, Real]]()
					onInterval := b.Assume()
					zero := b.TermAs[Real]("&0")
					one := b.TermAs[Real]("&1")
					continuous := b.Have(
						"g has a derivative at every point of ⟦0, 1⟧, so it is continuous there",
						"real_continuous_on(⟦&0, &1⟧, g)",
						By(
							onInterval,
							real_derivative.DerivativeContinuousOn.At(
								g,
								b.TermAs[Fun[Real, Real]]("λt:real. &0"),
								b.TermAs[Set[Real]]("⟦&0, &1⟧"))))
					interior := b.Have(
						"in particular g has derivative 0 inside ⟬0, 1⟭",
						"∀t:real. &0 < t ∧ t < &1 ⇒ real_derivative_at(g, t, &0)",
						ByArith(onInterval))
					b.Show(
						"continuous on ⟦0, 1⟧ with derivative 0 inside, g is constant there, so g(1) = g(0)",
						By(continuous, interior, real_derivative.DerivativeZeroConstant.At(g, zero, one, one)))
				}))
			direction := a.TermAs[Complex]("z - w")
			vanishing := a.Have(
				"0·(z − w) has both parts 0",
				"re(&0 * (z - w)) = &0 ∧ im(&0 * (z - w)) = &0",
				Simp(
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexReDef),
					Fwd(complex_field.ComplexImDef)),
				ByArith())
			slopes := a.Have(
				"so at every point of the segment from w to z both parts of f along it have derivative 0",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &1",
					},
					Conclusion: "real_derivative_at(λs:real. re(f(w + &s * (z - w))), t, &0) ∧ " +
						"real_derivative_at(λs:real. im(f(w + &s * (z - w))), t, &0)",
				},
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					within := b.Assume()
					atPoint := b.Have(
						"the point at t lies in U, U being convex, so f has derivative 0 there",
						"complex_derivative_at(f, w + &t * (z - w), &0)",
						By(derivatives.At(b.TermAs[Complex]("w + &t * (z - w)")), convex.At(w, z, t), wIn, zIn, within))
					along := b.Unfolded(
						b.Have(
							"so along the segment f has velocity 0·(z − w) at t",
							"path_derivative_at(λs:real. f(w + &s * (z - w)), t, &0 * (z - w))",
							By(atPoint, DerivativeAlongLine.At(f, w, direction, b.TermAs[Complex]("&0"), t))),
						PathDerivativeAtDef)
					b.Show(
						"and both parts of 0·(z − w) are 0",
						By(b.Simplified(along, Fwd(vanishing))))
				}))
			ends := a.Have(
				"so each part of f takes the same value at the two ends of the segment",
				"re(f(w + &1 * (z - w))) = re(f(w + &0 * (z - w))) ∧ "+
					"im(f(w + &1 * (z - w))) = im(f(w + &0 * (z - w)))",
				By(
					flat.At(a.TermAs[Fun[Real, Real]]("λs:real. re(f(w + &s * (z - w)))")),
					flat.At(a.TermAs[Fun[Real, Real]]("λs:real. im(f(w + &s * (z - w)))")),
					slopes))
			endpoints := a.Have(
				"the segment runs from w, at t = 0, to z, at t = 1",
				"w + &1 * (z - w) = z ∧ w + &0 * (z - w) = w",
				ByArith())
			a.Show(
				"f(z) and f(w) have the same parts, so they are equal",
				By(endpoints, ends, complex_field.ComplexEq))
		}),
})}

// DerivativeZeroConstant — a function with derivative 0 at every point of
// an open disc is constant on the disc: f(z) = f(c) for every z in the disc
// about c.
//
// The disc is convex. The point at t of the segment from u to v, less c,
// is (1 − t)·(u − c) + t·(v − c), at most (1 − t)·|u − c| + t·|v − c|
// from c, and a mean of two distances below r with weights 1 − t and t is
// below r: it is at most the larger of the two. The disc holds z and its
// centre, so f takes one value on it (DerivativeZeroConstantOnConvex).
var DerivativeZeroConstant = derivativeZeroConstantThm{family.Add(registry.ProofEntry{
	Name: "DerivativeZeroConstant",
	Key:  "prop_5108efb93c0d69c",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀r:real. ∀z:complex.",
		Hypotheses: []string{
			"∀w:complex. |w - c| < r ⇒ complex_derivative_at(f, w, &0)",
			"|z - c| < r",
		},
		Conclusion: "f(z) = f(c)",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			derivatives Fact,
			z *Expr[Complex],
			inDisc Fact,
		) {
			convex := a.Have(
				"the disc is convex",
				"∀u v:complex. ∀t:real. |u - c| < r ∧ |v - c| < r ∧ &0 ≤ t ∧ t ≤ &1 ⇒ |u + &t * (v - u) - c| < r",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("u")
					b.FixAs[Complex]("v")
					t := b.FixAs[Real]("t")
					within := b.Assume()
					fromU, fromV := b.TermAs[Real]("|u - c|"), b.TermAs[Real]("|v - c|")
					split := b.Have(
						"the point at t, less c, is (1 − t)·(u − c) + t·(v − c)",
						"u + &t * (v - u) - c = (&1 - &t) * (u - c) + &t * (v - c)",
						ByArith())
					b.Do(split.Rw())
					b.Show(
						"so it is at most (1 − t)·|u − c| + t·|v − c| from c, which "+
							"is at most the larger of the two distances, both below r",
						ByArith(
							within,
							complex_abs.AbsTriangle.At(
								b.TermAs[Complex]("(&1 - &t) * (u - c)"), b.TermAs[Complex]("&t * (v - c)")),
							complex_abs.AbsOfRealSub.At(b.TermAs[Real]("&1"), t),
							real_order_ring.LessEqMulLeft.At(b.TermAs[Real]("&1 - t"), fromU, fromV),
							real_order_ring.LessEqMulLeft.At(t, fromV, fromU)))
				}))
			centre := a.Have(
				"the disc holds its centre, as it holds z",
				"|c - c| < r",
				ByArith(inDisc))
			a.Show(
				"f has derivative 0 on the disc, which is convex and holds z and c, so f(z) = f(c)",
				By(
					convex,
					derivatives,
					inDisc,
					centre,
					DerivativeZeroConstantOnConvex.At(f, a.TermAs[Set[Complex]]("{u:complex | |u - c| < r}"), z, c)))
		}),
})}

// CauchyRiemannConverse — the converse of the Cauchy–Riemann equations:
// where the parts u = re f and v = im f have partial derivatives ux, uy, vx,
// vy on a disc about c, continuous at c and satisfying ux(c) = vy(c) and
// uy(c) = −vx(c) there, f has the complex derivative l = ux(c) + i·vx(c) at
// c.
//
// Given ε, put η = ε/8 and shrink a radius in four steps, one partial at a
// time, until on the disc of radius δ₄ all four partials exist and lie
// within η of their values at c; the four partials are four functions, not
// one family indexed by a number, which is what
// real_order_ring.CommonRadius would take at once. For z ≠ c within δ₄/2
// of c write z − c as x + i·y and walk from c to c + x along the
// horizontal line, then on to z along the vertical one. On each step a part
// of f moves by its partial at c times the step, to within η times the
// step: the mean value inequality against that slope, the partial along
// the step being within η of it, and the derivative at a point of the step
// being the partial there, read on the line, in the direction 1 or i,
// translated to that point. With the equations at c the real and
// the imaginary part of f(z) − f(c) − l·(z − c) are then each at most
// η(|x| + |y|), so its modulus is at most 4η|z − c| = (ε/2)·|z − c|, below
// ε|z − c| as z ≠ c, which is the increment form of the derivative.
var CauchyRiemannConverse = cauchyRiemannConverseThm{family.Add(registry.ProofEntry{
	Name: "CauchyRiemannConverse",
	Key:  "prop_63d83cb635b66e9d",
	Build: family.Sections(Statement{
		Binders: "∀f:(complex → complex). ∀ux uy vx vy:(complex → real). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀z:complex. |z - c| < r ⇒ real_derivative_at(λt:real. re(f(z + &t)), &0, ux(z))",
			"∀z:complex. |z - c| < r ⇒ real_derivative_at(λt:real. re(f(z + complex_i * &t)), &0, uy(z))",
			"∀z:complex. |z - c| < r ⇒ real_derivative_at(λt:real. im(f(z + &t)), &0, vx(z))",
			"∀z:complex. |z - c| < r ⇒ real_derivative_at(λt:real. im(f(z + complex_i * &t)), &0, vy(z))",
			"complex_continuous_at(λz:complex. &(ux(z)), c)",
			"complex_continuous_at(λz:complex. &(uy(z)), c)",
			"complex_continuous_at(λz:complex. &(vx(z)), c)",
			"complex_continuous_at(λz:complex. &(vy(z)), c)",
			"ux(c) = vy(c)",
			"uy(c) = -vx(c)",
		},
		Conclusion: "complex_derivative_at(f, c, «l»)",
		Abbrev: Abbrev{
			{Name: "l", Text: "&(ux(c)) + complex_i * &(vx(c))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The mean value inequality on an interval about 0, read where
			// the derivative at each point t is given as the derivative at 0
			// of the function translated by t.
			meanValue := ctx.Lemma(Statement{
				Binders: "∀g D:(real → real). ∀ρ d K s:real.",
				Hypotheses: []string{
					"∀t:real. -ρ < t ∧ t < ρ ⇒ real_derivative_at(λu:real. g(t + u), &0, D(t))",
					"∀t:real. -ρ < t ∧ t < ρ ⇒ |D(t) - d| ≤ K",
					"-ρ < s",
					"s < ρ",
				},
				Conclusion: "|g(s) - g(&0) - d * s| ≤ K * |s|",
			},
				func(
					a *Argument,
					g, D *Arrow[Real, Real],
					ρ, d, K, s *Expr[Real],
					translated, near, above, below Fact,
				) {
					zero := a.TermAs[Real]("&0")
					one := a.TermAs[Real]("&1")
					slopes := a.Have(
						"g has derivative D(t) at every t of ⟬−ρ, ρ⟭: translating back by t is a step of slope 1",
						"∀t:real. -ρ < t ∧ t < ρ ⇒ real_derivative_at(g, t, D(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							inside := b.Assume()
							shifted := b.TermAs[Fun[Real, Real]]("λu:real. g(t + u)")
							back := b.TermAs[Fun[Real, Real]]("λy:real. y - t")
							atZero := b.Have(
								"the translate by t has derivative D(t) at t − t = 0",
								"real_derivative_at(λu:real. g(t + u), t - t, D(t))",
								By(Normalized, translated.At(t), inside, real_ring.SubRefl.At(t)))
							translation := b.Have(
								"y ↦ y − t has derivative 1 at t",
								"real_derivative_at(λy:real. y - t, t, &1)",
								By(
									Normalized,
									real_derivative.DerivativeSub.At(
										b.TermAs[Fun[Real, Real]]("λy:real. y"),
										b.TermAs[Fun[Real, Real]]("λy:real. t"),
										t,
										one,
										zero),
									real_derivative.DerivativeId,
									real_derivative.DerivativeConst,
									real_ring.SubRightZero.At(one)))
							composite := b.Have(
								"so by the chain rule the translate after y ↦ y − t has derivative D(t)·1 at t",
								"real_derivative_at((λu:real. g(t + u)) ∘ (λy:real. y - t), t, D(t) * &1)",
								By(atZero, translation, real_derivative.DerivativeChain.At(shifted, back, t, D.Apply(t), one)))
							returns := b.Have(
								"translating back by t returns each point",
								"∀y:real. t + (y - t) = y",
								b.ForEach(func(y *Expr[Real]) Action { return ByArith() }))
							b.Show(
								"and that composite is g",
								By(b.Simplified(
									b.Unfolded(composite, functions.ComposeApply),
									Fwd(returns),
									Fwd(real_ring.MulRightId))))
						}))
					inner := a.Have(
						"0 lies in ⟬−ρ, ρ⟭, as s does",
						"-ρ < &0 ∧ &0 < ρ",
						ByArith(above, below))
					mean := a.Have(
						"so by the mean value inequality against the slope d, g moves from 0 to s by d·s to within K|s|",
						"|g(s) - g(&0) - d * (s - &0)| ≤ K * |s - &0|",
						By(
							slopes,
							near,
							above,
							below,
							inner,
							real_derivative.MeanValueNearSlope.At(g, D, a.TermAs[Real]("-ρ"), ρ, d, K, zero, s)))
					a.Show(
						"which is the claim, s − 0 being s",
						By(a.Simplified(mean, Fwd(real_ring.SubRightZero))))
				})

			// The same along the line through p in the direction w, where the
			// derivative at p + w·t is the partial along w there.
			alongLine := ctx.Lemma(Statement{
				Binders: "∀G D:(complex → real). ∀p w:complex. ∀ρ d K s:real.",
				Hypotheses: []string{
					"∀t:real. -ρ < t ∧ t < ρ ⇒ real_derivative_at(λu:real. G(p + w * &t + w * &u), &0, D(p + w * &t))",
					"∀t:real. -ρ < t ∧ t < ρ ⇒ |D(p + w * &t) - d| ≤ K",
					"-ρ < s",
					"s < ρ",
				},
				Conclusion: "|G(p + w * &s) - G(p) - d * s| ≤ K * |s|",
			},
				func(
					a *Argument,
					G, D *Arrow[Complex, Real],
					p, w *Expr[Complex],
					ρ, d, K, s *Expr[Real],
					derivatives, near, above, below Fact,
				) {
					adds := a.Have(
						"the line adds its parameters: p + w·(t + u) is p + w·t + w·u",
						"∀t u:real. p + w * &(t + u) = p + w * &t + w * &u",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							u := b.FixAs[Real]()
							b.Show(
								"the embedding of ℝ in ℂ keeps sums, and w distributes over them",
								ByArith(Scaled(w, complex_field.OfRealAdd.At(t, u))))
						}))
					starts := a.Have(
						"and at 0 it is at p",
						"p + w * &0 = p",
						ByArith())
					a.Show(
						"the mean value inequality for t ↦ G(p + w·t), whose translates are the line read from p + w·t",
						By(
							a.Simplified(
								At(meanValue,
									a.TermAs[Fun[Real, Real]]("λs:real. G(p + w * &s)"),
									a.TermAs[Fun[Real, Real]]("λt:real. D(p + w * &t)"),
									ρ,
									d,
									K,
									s),
								Fwd(adds),
								Fwd(starts)),
							derivatives,
							near,
							above,
							below))
				})

			// A real function g whose embedding in ℂ is continuous at c stays
			// within η of g(c) on some disc about c, of radius at most ρ.
			radius := ctx.Lemma(Statement{
				Binders: "∀g:(complex → real). ∀c:complex. ∀η ρ:real.",
				Hypotheses: []string{
					"complex_continuous_at(λz:complex. &(g(z)), c)",
					"&0 < η",
					"&0 < ρ",
				},
				Conclusion: "∃δ:real. &0 < δ ∧ δ ≤ ρ ∧ ∀z:complex. |z - c| < δ ⇒ |g(z) - g(c)| ≤ η",
			},
				func(
					a *Argument,
					g *Arrow[Complex, Real],
					c *Expr[Complex],
					η, ρ *Expr[Real],
					continuous, ηPos, ρPos Fact,
				) {
					zero := a.TermAs[Real]("&0")
					near := a.Unfolded(continuous, complex_topology.ComplexContinuousAtDef)
					δ, ball := a.ObtainAs[Real](
						"continuity at c hands over a radius δ on which &g(z) is within η of &g(c)",
						"∃δ:real. &0 < δ ∧ ∀z:complex. |z - c| < δ ⇒ |&(g(z)) - &(g(c))| < η",
						By(near.At(η), ηPos),
						Named("δ"))
					disc := a.Conjuncts(
						ball,
						"δ is positive",
						"and within δ of c, &g(z) is within η of &g(c)")
					a.Take(a.TermAs[Real]("min(δ, ρ)"))
					a.Do(SplitConjAll(
						Case(
							"the smaller of δ and ρ is positive",
							By(disc[0], ρPos, real_sup_inf.LessThanMin.At(δ, ρ, zero))),
						Case(
							"and at most ρ",
							By(real_sup_inf.MinLowerBound.At(δ, ρ))),
						Case(
							"within it of c, z is within δ of c, where g(z) is within η of g(c)",
							Derive(func(b *Argument) {
								z := b.FixAs[Complex]()
								inside := b.Assume()
								b.Show(
									"|g(z) − g(c)| = |&g(z) − &g(c)| < η",
									ByArith(
										disc[1].At(z),
										complex_abs.AbsOfRealSub.At(g.Apply(z), g.Apply(c)),
										inside,
										real_sup_inf.LessThanMin.At(δ, ρ, b.TermAs[Real]("|z - c|"))))
							})),
					))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					f *Arrow[Complex, Complex],
					ux, uy, vx, vy *Arrow[Complex, Real],
					c *Expr[Complex],
					r *Expr[Real],
					rPos, uxAlong, uyAlong, vxAlong, vyAlong, uxContinuous, uyContinuous, vxContinuous, vyContinuous, equalX, equalY Fact,
				) {
					increment := a.Have(
						"for every ε > 0 a punctured disc about c keeps f(z) − f(c) within ε|z − c| of l·(z − c)",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃δ:real. " +
								"    &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c) - «l» * (z - c)| < ε * |z - c|",
						},
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							εPos := b.Assume()
							η, ηDef := b.LetAs[Real]("η", "ε / &8")
							ηPos := b.Have(
								"η is positive",
								"&0 < η",
								ByArith(ηDef, εPos))
							δ1, uxDisc := b.ObtainAs[Real](
								"ux stays within η of ux(c) on a disc of radius δ₁ ≤ r",
								"∃δ₁:real. &0 < δ₁ ∧ δ₁ ≤ r ∧ ∀ζ:complex. |ζ - c| < δ₁ ⇒ |ux(ζ) - ux(c)| ≤ η",
								By(uxContinuous, ηPos, rPos, At(radius, ux, c, η, r)))
							uxNear := b.Conjuncts(
								uxDisc,
								"δ₁ is positive",
								"δ₁ ≤ r",
								"on its disc ux is within η of ux(c)")
							δ2, uyDisc := b.ObtainAs[Real](
								"uy stays within η of uy(c) on a disc of radius δ₂ ≤ δ₁",
								"∃δ₂:real. &0 < δ₂ ∧ δ₂ ≤ δ₁ ∧ ∀ζ:complex. |ζ - c| < δ₂ ⇒ |uy(ζ) - uy(c)| ≤ η",
								By(uyContinuous, ηPos, uxNear[0], At(radius, uy, c, η, δ1)))
							uyNear := b.Conjuncts(
								uyDisc,
								"δ₂ is positive",
								"δ₂ ≤ δ₁",
								"on its disc uy is within η of uy(c)")
							δ3, vxDisc := b.ObtainAs[Real](
								"vx stays within η of vx(c) on a disc of radius δ₃ ≤ δ₂",
								"∃δ₃:real. &0 < δ₃ ∧ δ₃ ≤ δ₂ ∧ ∀ζ:complex. |ζ - c| < δ₃ ⇒ |vx(ζ) - vx(c)| ≤ η",
								By(vxContinuous, ηPos, uyNear[0], At(radius, vx, c, η, δ2)))
							vxNear := b.Conjuncts(
								vxDisc,
								"δ₃ is positive",
								"δ₃ ≤ δ₂",
								"on its disc vx is within η of vx(c)")
							_, vyDisc := b.ObtainAs[Real](
								"vy stays within η of vy(c) on a disc of radius δ₄ ≤ δ₃",
								"∃δ₄:real. &0 < δ₄ ∧ δ₄ ≤ δ₃ ∧ ∀ζ:complex. |ζ - c| < δ₄ ⇒ |vy(ζ) - vy(c)| ≤ η",
								By(vyContinuous, ηPos, vxNear[0], At(radius, vy, c, η, δ3)))
							vyNear := b.Conjuncts(
								vyDisc,
								"δ₄ is positive",
								"δ₄ ≤ δ₃",
								"on its disc vy is within η of vy(c)")
							near := b.Have(
								"within δ₄ of c the four partials exist, each within η of its value at c",
								Statement{
									Binders: "∀ζ:complex.",
									Hypotheses: []string{
										"|ζ - c| < δ₄",
									},
									Conclusion: "real_derivative_at(λt:real. re(f(ζ + &t)), &0, ux(ζ)) ∧ " +
										"real_derivative_at(λt:real. im(f(ζ + &t)), &0, vx(ζ)) ∧ " +
										"real_derivative_at(λt:real. re(f(ζ + complex_i * &t)), &0, uy(ζ)) ∧ " +
										"real_derivative_at(λt:real. im(f(ζ + complex_i * &t)), &0, vy(ζ)) ∧ " +
										"|ux(ζ) - ux(c)| ≤ η ∧ " +
										"|vx(ζ) - vx(c)| ≤ η ∧ " +
										"|uy(ζ) - uy(c)| ≤ η ∧ " +
										"|vy(ζ) - vy(c)| ≤ η",
								},
								Derive(func(d *Argument) {
									ζ := d.FixAs[Complex]()
									inside := d.Assume()
									radii := d.Have(
										"the radii shrink, so ζ is within r, δ₁, δ₂ and δ₃ of c too",
										"|ζ - c| < r ∧ |ζ - c| < δ₁ ∧ |ζ - c| < δ₂ ∧ |ζ - c| < δ₃",
										ByArith(inside, uxNear[1], uyNear[1], vxNear[1], vyNear[1]))
									d.Show(
										"the partials exist within r of c, and each radius keeps its partial within η",
										By(
											radii,
											inside,
											uxAlong.At(ζ),
											vxAlong.At(ζ),
											uyAlong.At(ζ),
											vyAlong.At(ζ),
											uxNear[2].At(ζ),
											vxNear[2].At(ζ),
											uyNear[2].At(ζ),
											vyNear[2].At(ζ)))
								}))
							half := b.TermAs[Real]("δ₄ / &2")
							b.Take(half)
							b.Do(SplitConj(
								Case(
									"half of δ₄ is positive",
									ByArith(vyNear[0])),
								Case(
									"for z ≠ c within δ₄/2 of c, walk from c to z along the horizontal line and then the vertical one",
									Derive(func(d *Argument) {
										z := d.FixAs[Complex]()
										closeToC := d.Assume()
										x, xDef := d.LetAs[Real]("x", "re(z) - re(c)")
										y, yDef := d.LetAs[Real]("y", "im(z) - im(c)")
										sizes := d.Have(
											"the parts x and y of z − c are at most |z − c| in size",
											"|x| ≤ |z - c| ∧ |y| ≤ |z - c|",
											ByArith(xDef, yDef, complex_abs.PartsNonexpanding.At(z, c)))
										steps := d.Have(
											"so both steps lie in ⟬−δ₄/2, δ₄/2⟭",
											"-(δ₄ / &2) < x ∧ x < δ₄ / &2 ∧ -(δ₄ / &2) < y ∧ y < δ₄ / &2",
											ByArith(sizes, closeToC))
										across := d.Have(
											"the horizontal line through c stays within δ₄ of c, so "+
												"the partials along 1 exist on it near their values at c",
											Statement{
												Binders: "∀t:real.",
												Hypotheses: []string{
													"-(δ₄ / &2) < t",
													"t < δ₄ / &2",
												},
												Conclusion: "real_derivative_at(λu:real. re(f(c + &t + &u)), &0, ux(c + &t)) ∧ " +
													"real_derivative_at(λu:real. im(f(c + &t + &u)), &0, vx(c + &t)) ∧ " +
													"|ux(c + &t) - ux(c)| ≤ η ∧ " +
													"|vx(c + &t) - vx(c)| ≤ η",
											},
											Derive(func(e *Argument) {
												e.FixAs[Real]()
												between := e.Assume()
												parts := e.Have(
													"c + t − c has parts t and 0",
													"re(c + &t - c) = t ∧ im(c + &t - c) = &0",
													Simp(
														Fwd(complex_field.ComplexSubDef),
														Fwd(complex_field.ComplexAddDef),
														Fwd(complex_field.ComplexNegDef),
														Fwd(complex_field.ComplexOfRealDef),
														Fwd(complex_field.ComplexReDef),
														Fwd(complex_field.ComplexImDef)),
													ByArith())
												point := e.Have(
													"so c + t lies within |t| < δ₄ of c",
													"|c + &t - c| < δ₄",
													ByArith(parts, between, vyNear[0], complex_abs.AbsLeParts.At(e.TermAs[Complex]("c + &t - c"))))
												e.Show(
													"where the partials exist and are within η of their values at c",
													By(near.At(e.TermAs[Complex]("c + &t")), point))
											}))
										up := d.Have(
											"the vertical line through c + x stays within δ₄ of c, so "+
												"the partials along i exist on it near their values at c",
											Statement{
												Binders: "∀t:real.",
												Hypotheses: []string{
													"-(δ₄ / &2) < t",
													"t < δ₄ / &2",
												},
												Conclusion: "real_derivative_at(λu:real. re(f(c + &x + complex_i * &t + complex_i * &u)), " +
													"    &0, " +
													"    uy(c + &x + complex_i * &t)) ∧ " +
													"real_derivative_at(λu:real. im(f(c + &x + complex_i * &t + complex_i * &u)), " +
													"    &0, " +
													"    vy(c + &x + complex_i * &t)) ∧ " +
													"|uy(c + &x + complex_i * &t) - uy(c)| ≤ η ∧ " +
													"|vy(c + &x + complex_i * &t) - vy(c)| ≤ η",
											},
											Derive(func(e *Argument) {
												e.FixAs[Real]()
												between := e.Assume()
												parts := e.Have(
													"c + x + i·t − c has parts x and t",
													"re(c + &x + complex_i * &t - c) = x ∧ im(c + &x + complex_i * &t - c) = t",
													Simp(
														Fwd(complex_field.ComplexSubDef),
														Fwd(complex_field.ComplexAddDef),
														Fwd(complex_field.ComplexNegDef),
														Fwd(complex_field.ComplexMulDef),
														Fwd(complex_field.ComplexIDef),
														Fwd(complex_field.ComplexOfRealDef),
														Fwd(complex_field.ComplexReDef),
														Fwd(complex_field.ComplexImDef)),
													ByArith())
												point := e.Have(
													"so c + x + i·t lies within |x| + |t| < δ₄ of c",
													"|c + &x + complex_i * &t - c| < δ₄",
													ByArith(
														parts,
														between,
														sizes,
														closeToC,
														complex_abs.AbsLeParts.At(e.TermAs[Complex]("c + &x + complex_i * &t - c"))))
												e.Show(
													"where the partials exist and are within η of their values at c",
													By(near.At(e.TermAs[Complex]("c + &x + complex_i * &t")), point))
											}))
										start := d.TermAs[Complex]("c + &x")
										one := d.TermAs[Complex]("&1")
										i := d.TermAs[Complex]("complex_i")
										u := d.TermAs[Fun[Complex, Real]]("λζ:complex. re(f(ζ))")
										v := d.TermAs[Fun[Complex, Real]]("λζ:complex. im(f(ζ))")
										// the horizontal line is the line in the direction 1, its 1·t read as t
										identity := Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid))
										reAcross := d.Have(
											"along the horizontal step re f moves by ux(c)·x, to within η|x|",
											"|re(f(c + &x)) - re(f(c)) - ux(c) * x| ≤ η * |x|",
											By(across, steps, d.Simplified(At(alongLine, u, ux, c, one, half, ux.Apply(c), η, x), identity)))
										imAcross := d.Have(
											"and im f by vx(c)·x, to within η|x|",
											"|im(f(c + &x)) - im(f(c)) - vx(c) * x| ≤ η * |x|",
											By(across, steps, d.Simplified(At(alongLine, v, vx, c, one, half, vx.Apply(c), η, x), identity)))
										reUp := d.Have(
											"along the vertical step, the line in the direction i, re f moves by uy(c)·y, to within η|y|",
											"|re(f(c + &x + complex_i * &y)) - re(f(c + &x)) - uy(c) * y| ≤ η * |y|",
											By(up, steps, At(alongLine, u, uy, start, i, half, uy.Apply(c), η, y)))
										imUp := d.Have(
											"and im f by vy(c)·y, to within η|y|",
											"|im(f(c + &x + complex_i * &y)) - im(f(c + &x)) - vy(c) * y| ≤ η * |y|",
											By(up, steps, At(alongLine, v, vy, start, i, half, vy.Apply(c), η, y)))
										end := d.Have(
											"the walk ends at z",
											"c + &x + complex_i * &y = z",
											Simp(
												complex_field.Parts,
												Fwd(complex_field.ComplexAddDef),
												Fwd(complex_field.ComplexMulDef),
												Fwd(complex_field.ComplexIDef),
												Fwd(complex_field.ComplexOfRealDef)),
											ByArith(xDef, yDef))
										uxc, vxc := ux.Apply(c), vx.Apply(c)
										errorParts := d.Have(
											"the parts of the error: l·(z − c) has parts ux(c)·x − vx(c)·y and ux(c)·y + vx(c)·x",
											"re(f(z) - f(c) - «l» * (z - c)) = re(f(z)) - re(f(c)) - (ux(c) * x - vx(c) * y) ∧ "+
												"im(f(z) - f(c) - «l» * (z - c)) = im(f(z)) - im(f(c)) - (ux(c) * y + vx(c) * x)",
											Simp(
												Fwd(complex_field.ComplexSubDef),
												Fwd(complex_field.ComplexAddDef),
												Fwd(complex_field.ComplexNegDef),
												Fwd(complex_field.ComplexMulDef),
												Fwd(complex_field.ComplexIDef),
												Fwd(complex_field.ComplexOfRealDef),
												Fwd(complex_field.ComplexReDef),
												Fwd(complex_field.ComplexImDef)),
											ByArith(Scaled(uxc, xDef), Scaled(vxc, yDef), Scaled(vxc, xDef), Scaled(uxc, yDef)))
										reBound := d.Have(
											"with uy(c) = −vx(c), the real part of the error is "+
												"the two real-part errors added: at most η(|x| + |y|)",
											"|re(f(z) - f(c) - «l» * (z - c))| ≤ η * |x| + η * |y|",
											ByArith(errorParts, reAcross, d.Simplified(reUp, Fwd(end)), Scaled(y, equalY)))
										imBound := d.Have(
											"with vy(c) = ux(c), so is the imaginary part",
											"|im(f(z) - f(c) - «l» * (z - c))| ≤ η * |x| + η * |y|",
											ByArith(errorParts, imAcross, d.Simplified(imUp, Fwd(end)), Scaled(y, equalX)))
										byParts := d.Have(
											"the modulus of the error is at most the sum of its parts' sizes",
											"|f(z) - f(c) - «l» * (z - c)| ≤ "+
												"|re(f(z) - f(c) - «l» * (z - c))| + |im(f(z) - f(c) - «l» * (z - c))|",
											Cite(complex_abs.AbsLeParts))
										scale := d.Have(
											"η|x| + η|y| is at most 2η|z − c|",
											"η * |x| + η * |y| ≤ &2 * η * |z - c|",
											ByArith(sizes, ηPos))
										d.Show(
											"so the error is at most 4η|z − c| = (ε/2)·|z − c|, below ε|z − c| as |z − c| > 0",
											ByArith(byParts, reBound, imBound, scale, closeToC, εPos, Scaled(d.TermAs[Real]("|z - c|"), ηDef)))
									})),
							))
						}))
					a.Show(
						"which is the increment form of the derivative l at c",
						By(increment, DerivativeIncrement.At(f, c, a.TermAs[Complex]("«l»"))))
				})
		}),
})}
