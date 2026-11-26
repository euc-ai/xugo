// paths.go — the calculus of a path: its velocity, a function read along
// it and the chain rule; the integral along a piecewise smooth path, its
// existence, the fundamental theorem, the ML estimate and linearity; and
// the segment, reversed and split.

package path_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// PathDerivativeContinuousOn — a path with a velocity at every point of a
// set has continuous parts there: each part has the matching part of the
// velocity as its derivative at every point of the set, and a real function
// with a derivative at every point of a set is continuous on it.
var PathDerivativeContinuousOn = pathDerivativeContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "PathDerivativeContinuousOn",
	Key:  "prop_a56e4f62c133f92",
	Build: family.Theorem(Statement{
		Binders: "∀γ γ':(real → complex). ∀s:set(real).",
		Hypotheses: []string{
			"∀t:real. t ∈ s ⇒ path_derivative_at(γ, t, γ'(t))",
		},
		Conclusion: "real_continuous_on(s, λt:real. re(γ(t))) ∧ real_continuous_on(s, λt:real. im(γ(t)))",
	},
		func(a *Argument, γ, γPrime *Arrow[Real, Complex], s *Expr[Set[Real]], velocity Fact) {
			rates := a.Unfolded(velocity, complex_derivative.PathDerivativeAtDef)
			a.Show(
				"each part of γ has a derivative at every point of s",
				SplitConj(
					Case(
						"so the real part is continuous on s",
						By(
							rates,
							real_derivative.DerivativeContinuousOn.At(
								a.TermAs[Fun[Real, Real]]("λt:real. re(γ(t))"),
								a.TermAs[Fun[Real, Real]]("λt:real. re(γ'(t))"),
								s))),
					Case(
						"and so is the imaginary part",
						By(
							rates,
							real_derivative.DerivativeContinuousOn.At(
								a.TermAs[Fun[Real, Real]]("λt:real. im(γ(t))"),
								a.TermAs[Fun[Real, Real]]("λt:real. im(γ'(t))"),
								s)))))
		}),
})}

// ContinuousAtPartwise — a complex function continuous at w is continuous
// there part by part: for every positive ε some positive η keeps both parts
// of f(z) within ε of those of f(w) once both parts of z are within η of
// those of w. Continuity at w gives a radius δ inside which f moves by less
// than ε; with both parts of z − w below δ/2, z lies within δ of w, a
// complex number being no longer than the sum of its parts, and each part
// of f(z) − f(w) is at most its modulus.
var ContinuousAtPartwise = continuousAtPartwiseThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtPartwise",
	Key:  "prop_cf4dff7b5fb6d646",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀w:complex. ∀ε:real.",
		Hypotheses: []string{
			"complex_continuous_at(f, w)",
			"&0 < ε",
		},
		Conclusion: "∃η:real. " +
			"    &0 < η ∧ " +
			"    ∀z:complex. " +
			"        |re(z) - re(w)| < η ∧ |im(z) - im(w)| < η ⇒ " +
			"        |re(f(z)) - re(f(w))| < ε ∧ |im(f(z)) - im(f(w))| < ε",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			w *Expr[Complex],
			ε *Expr[Real],
			continuous, positive Fact,
		) {
			_, ball := a.ObtainAs[Real](
				"f is continuous at w: inside some radius δ about w it moves by less than ε",
				"∃δ:real. &0 < δ ∧ ∀z:complex. |z - w| < δ ⇒ |f(z) - f(w)| < ε",
				By(continuous, positive, complex_topology.ComplexContinuousAtDef.At(f, w)),
				Named("δ"))
			disc := a.Conjuncts(
				ball,
				"δ is positive",
				"and inside δ about w, f is within ε of f(w)")
			a.Take(a.TermAs[Real]("δ / &2"))
			a.Do(SplitConj(
				Case(
					"half of δ is positive",
					ByArith(disc[0])),
				Case(
					"and once both parts of z are within δ/2 of those of "+
						"w, both parts of f(z) are within ε of those of f(w)",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						near := b.Assume()
						close := b.Have(
							"z lies within δ of w, a complex number being no longer than the sum of its parts",
							"|z - w| < δ",
							ByArith(
								complex_abs.AbsLeParts.At(b.TermAs[Complex]("z - w")),
								complex_field.PartsSub.At(z, w),
								near))
						moved := b.Have(
							"so f(z) lies within ε of f(w)",
							"|f(z) - f(w)| < ε",
							By(disc[1].At(z), close))
						b.Show(
							"and each part of a difference, the difference of the parts, is at most its modulus",
							ByArith(moved, complex_abs.PartsNonexpanding.At(f.Apply(z), f.Apply(w))))
					}))))
		}),
})}

// ContinuousAlongPath — a complex function continuous at the points of a
// path whose parts are continuous on s is, read along the path, continuous
// on s part by part.
//
// At a point c of s, f read part by part at γ(c) answers ε with an η, and
// each part of γ, given η, answers with a radius inside which it moves by
// less than η at the points of s. Inside the smaller of the two radii both
// parts of γ(x) are within η of those of γ(c), so both parts of f(γ(x)) are
// within ε of those of f(γ(c)).
var ContinuousAlongPath = continuousAlongPathThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAlongPath",
	Key:  "prop_3f8e35f687d55001",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀γ:(real → complex). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, λt:real. re(γ(t)))",
			"real_continuous_on(s, λt:real. im(γ(t)))",
			"∀t:real. t ∈ s ⇒ complex_continuous_at(f, γ(t))",
		},
		Conclusion: "real_continuous_on(s, λt:real. re(f(γ(t)))) ∧ " +
			"real_continuous_on(s, λt:real. im(f(γ(t))))",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			γ *Arrow[Real, Complex],
			s *Expr[Set[Real]],
			reContinuous, imContinuous, fContinuous Fact,
		) {
			nearRe := a.Unfolded(reContinuous, real_continuous.RealContinuousOnDef)
			nearIm := a.Unfolded(imContinuous, real_continuous.RealContinuousOnDef)
			radius := a.Have(
				"one radius keeps both parts of f(γ(x)) within ε of those of f(γ(c)) at the points x of s near c",
				Statement{
					Binders: "∀c ε:real.",
					Hypotheses: []string{
						"c ∈ s",
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    ∀x:real. " +
						"        x ∈ s ∧ |x - c| < δ ⇒ |re(f(γ(x))) - re(f(γ(c)))| < ε ∧ |im(f(γ(x))) - im(f(γ(c)))| < ε",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[Real]("c")
					ε := b.FixAs[Real]("ε")
					premises := b.Conjuncts(
						b.Assume(),
						"c lies in s",
						"and ε is positive")
					η, partwise := b.ObtainAs[Real](
						"f is continuous at γ(c), so part by part: parts within "+
							"some η of those of γ(c) keep the parts of f within ε",
						"∃η:real. "+
							"    &0 < η ∧ "+
							"    ∀z:complex. "+
							"        |re(z) - re(γ(c))| < η ∧ |im(z) - im(γ(c))| < η ⇒ "+
							"        |re(f(z)) - re(f(γ(c)))| < ε ∧ |im(f(z)) - im(f(γ(c)))| < ε",
						By(fContinuous.At(c), premises[0], premises[1], ContinuousAtPartwise.At(f, γ.Apply(c), ε)),
						Named("η"))
					control := b.Conjuncts(
						partwise,
						"η is positive",
						"and parts within η of those of γ(c) keep the parts of f within ε of those of f(γ(c))")
					δ1, reRadius := b.ObtainAs[Real](
						"the real part of γ answers η at c with a radius δ₁",
						"∃δ:real. &0 < δ ∧ ∀x:real. x ∈ s ∧ |x - c| < δ ⇒ |re(γ(x)) - re(γ(c))| < η",
						By(nearRe.At(c, η), premises[0], control[0]),
						Named("δ₁"))
					reHeld := b.Conjuncts(
						reRadius,
						"δ₁ is positive",
						"and inside δ₁ the real part of γ moves by less than η")
					δ2, imRadius := b.ObtainAs[Real](
						"and the imaginary part with a radius δ₂",
						"∃δ:real. &0 < δ ∧ ∀x:real. x ∈ s ∧ |x - c| < δ ⇒ |im(γ(x)) - im(γ(c))| < η",
						By(nearIm.At(c, η), premises[0], control[0]),
						Named("δ₂"))
					imHeld := b.Conjuncts(
						imRadius,
						"δ₂ is positive",
						"and inside δ₂ the imaginary part of γ moves by less than η")
					b.Take(b.TermAs[Real]("min(δ₁, δ₂)"))
					b.Do(SplitConj(
						Case(
							"the smaller of δ₁ and δ₂ is positive, both being positive",
							By(real_sup_inf.LessThanMin.At(δ1, δ2, b.TermAs[Real]("&0")), reHeld[0], imHeld[0])),
						Case(
							"and at a point x of s inside it both parts of f(γ(x)) are within ε of those of f(γ(c))",
							Derive(func(d *Argument) {
								x := d.FixAs[Real]("x")
								inside := d.Conjuncts(
									d.Assume(),
									"x lies in s",
									"and within min(δ₁, δ₂) of c")
								d.Show(
									"x is within δ₁ and δ₂ of c, so both parts of γ(x) are within η of those of γ(c)",
									By(
										control[1].At(γ.Apply(x)),
										reHeld[1].At(x),
										imHeld[1].At(x),
										inside[0],
										inside[1],
										real_sup_inf.LessThanMin.At(δ1, δ2, d.TermAs[Real]("|x - c|"))))
							})),
					))
				}))
			a.Show(
				"the one radius answers the continuity of each part on s",
				Unfold(real_continuous.RealContinuousOnDef),
				SplitConj(
					Case(
						"the real part of f along γ is continuous on s",
						By(radius)),
					Case(
						"and so is the imaginary part",
						By(radius))))
		}),
})}

// ContinuousAtAlongPath — a complex function continuous at the point γ(c)
// of a path whose parts are continuous at c is, read along the path,
// continuous at c part by part: f read part by part at γ(c) answers ε with
// an η, each part of γ answers η with a radius at c, and inside the smaller
// radius both parts of f(γ(x)) are within ε of those of f(γ(c)).
var ContinuousAtAlongPath = continuousAtAlongPathThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtAlongPath",
	Key:  "prop_976f192eb8885956",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀γ:(real → complex). ∀c:real.",
		Hypotheses: []string{
			"real_continuous_at(λt:real. re(γ(t)), c)",
			"real_continuous_at(λt:real. im(γ(t)), c)",
			"complex_continuous_at(f, γ(c))",
		},
		Conclusion: "real_continuous_at(λt:real. re(f(γ(t))), c) ∧ " +
			"real_continuous_at(λt:real. im(f(γ(t))), c)",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			γ *Arrow[Real, Complex],
			c *Expr[Real],
			reContinuous, imContinuous, fContinuous Fact,
		) {
			nearRe := a.Unfolded(reContinuous, real_continuous.RealContinuousAtDef)
			nearIm := a.Unfolded(imContinuous, real_continuous.RealContinuousAtDef)
			radius := a.Have(
				"one radius keeps both parts of f(γ(x)) within ε of those of f(γ(c)) for x near c",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    ∀x:real. |x - c| < δ ⇒ |re(f(γ(x))) - re(f(γ(c)))| < ε ∧ |im(f(γ(x))) - im(f(γ(c)))| < ε",
				},
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]("ε")
					pos := b.Assume()
					η, partwise := b.ObtainAs[Real](
						"f is continuous at γ(c), so part by part: parts within "+
							"some η of those of γ(c) keep the parts of f within ε",
						"∃η:real. "+
							"    &0 < η ∧ "+
							"    ∀z:complex. "+
							"        |re(z) - re(γ(c))| < η ∧ |im(z) - im(γ(c))| < η ⇒ "+
							"        |re(f(z)) - re(f(γ(c)))| < ε ∧ |im(f(z)) - im(f(γ(c)))| < ε",
						By(fContinuous, pos, ContinuousAtPartwise.At(f, γ.Apply(c), ε)),
						Named("η"))
					control := b.Conjuncts(
						partwise,
						"η is positive",
						"and parts within η of those of γ(c) keep the parts of f within ε of those of f(γ(c))")
					δ1, reRadius := b.ObtainAs[Real](
						"the real part of γ answers η at c with a radius δ₁",
						"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |re(γ(x)) - re(γ(c))| < η",
						By(nearRe.At(η), control[0]),
						Named("δ₁"))
					reHeld := b.Conjuncts(
						reRadius,
						"δ₁ is positive",
						"and inside δ₁ the real part of γ moves by less than η")
					δ2, imRadius := b.ObtainAs[Real](
						"and the imaginary part with a radius δ₂",
						"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |im(γ(x)) - im(γ(c))| < η",
						By(nearIm.At(η), control[0]),
						Named("δ₂"))
					imHeld := b.Conjuncts(
						imRadius,
						"δ₂ is positive",
						"and inside δ₂ the imaginary part of γ moves by less than η")
					b.Take(b.TermAs[Real]("min(δ₁, δ₂)"))
					b.Do(SplitConj(
						Case(
							"the smaller of δ₁ and δ₂ is positive, both being positive",
							By(real_sup_inf.LessThanMin.At(δ1, δ2, b.TermAs[Real]("&0")), reHeld[0], imHeld[0])),
						Case(
							"and at a point x inside it both parts of f(γ(x)) are within ε of those of f(γ(c))",
							Derive(func(d *Argument) {
								x := d.FixAs[Real]("x")
								near := d.Assume()
								d.Show(
									"x is within δ₁ and δ₂ of c, so both parts of γ(x) are within η of those of γ(c)",
									By(
										control[1].At(γ.Apply(x)),
										reHeld[1].At(x),
										imHeld[1].At(x),
										near,
										real_sup_inf.LessThanMin.At(δ1, δ2, d.TermAs[Real]("|x - c|"))))
							})),
					))
				}))
			a.Show(
				"the one radius answers the continuity of each part at c",
				Unfold(real_continuous.RealContinuousAtDef),
				SplitConj(
					Case(
						"the real part of f along γ is continuous at c",
						By(radius)),
					Case(
						"and so is the imaginary part",
						By(radius))))
		}),
})}

// PathDerivativeCompose — the chain rule along a path: where F has complex
// derivative l at γ(t) and γ has velocity d at t, F along γ has velocity
// l·d at t.
//
// By Carathéodory, F(z) − F(γ(t)) = φ(z)·(z − γ(t)) with φ continuous at
// γ(t) and φ(γ(t)) = l, and each part of γ factors through a real slope,
// ψ₁ for the real part and ψ₂ for the imaginary, continuous at t with
// values re(d) and im(d) there. So γ(s) − γ(t) is complex(ψ₁(s), ψ₂(s))
// times the real s − t, and F(γ(s)) − F(γ(t)) is φ(γ(s))·complex(ψ₁(s),
// ψ₂(s)) times s − t. Each part of that product is a real slope for the
// same part of F along γ: built from the parts of φ along γ, continuous at
// t as γ is, and from ψ₁ and ψ₂, it is continuous at t, and at t it is
// the part of l·d. Carathéodory's form on the line then gives each part's
// derivative.
var PathDerivativeCompose = pathDerivativeComposeThm{family.Add(registry.ProofEntry{
	Name: "PathDerivativeCompose",
	Key:  "prop_580f297e7d05276f",
	Build: family.Theorem(Statement{
		Binders: "∀F:(complex → complex). ∀γ:(real → complex). ∀t:real. ∀l d:complex.",
		Hypotheses: []string{
			"complex_derivative_at(F, γ(t), l)",
			"path_derivative_at(γ, t, d)",
		},
		Conclusion: "path_derivative_at(λs:real. F(γ(s)), t, l * d)",
	},
		func(
			a *Argument,
			F *Arrow[Complex, Complex],
			γ *Arrow[Real, Complex],
			t *Expr[Real],
			l, d *Expr[Complex],
			differentiable, velocity Fact,
		) {
			φ, factored := a.ObtainAs[Fun[Complex, Complex]](
				"by Carathéodory, F's increment from γ(t) factors "+
					"through a slope φ continuous at γ(t), with φ(γ(t)) = l",
				"∃φ:(complex → complex). "+
					"    (∀z:complex. F(z) - F(γ(t)) = φ(z) * (z - γ(t))) ∧ "+
					"    complex_continuous_at(φ, γ(t)) ∧ "+
					"    φ(γ(t)) = l",
				By(differentiable, complex_derivative.DerivativeCaratheodory.At(F, γ.Apply(t), l)),
				Named("φ"))
			slope := a.Conjuncts(
				factored,
				"F(z) − F(γ(t)) = φ(z)·(z − γ(t)) at every z",
				"φ is continuous at γ(t)",
				"φ(γ(t)) = l")
			rates := a.Conjuncts(
				a.Unfolded(velocity, complex_derivative.PathDerivativeAtDef),
				"the real part of γ has derivative re(d) at t",
				"and its imaginary part im(d)")
			_, reFactored := a.ObtainAs[Fun[Real, Real]](
				"by Carathéodory on the line, the real part of γ factors "+
					"through a slope ψ₁ continuous at t, with ψ₁(t) = re(d)",
				"∃ψ:(real → real). "+
					"    (∀s:real. re(γ(s)) - re(γ(t)) = ψ(s) * (s - t)) ∧ real_continuous_at(ψ, t) ∧ ψ(t) = re(d)",
				By(
					rates[0],
					real_derivative.DerivativeCaratheodory.At(
						a.TermAs[Fun[Real, Real]]("λs:real. re(γ(s))"), t, a.TermAs[Real]("re(d)"))),
				Named("ψ₁"))
			reSlope := a.Conjuncts(
				reFactored,
				"re(γ(s)) − re(γ(t)) = ψ₁(s)·(s − t) at every s",
				"ψ₁ is continuous at t",
				"ψ₁(t) = re(d)")
			_, imFactored := a.ObtainAs[Fun[Real, Real]](
				"and the imaginary part through a slope ψ₂ continuous at t, with ψ₂(t) = im(d)",
				"∃ψ:(real → real). "+
					"    (∀s:real. im(γ(s)) - im(γ(t)) = ψ(s) * (s - t)) ∧ real_continuous_at(ψ, t) ∧ ψ(t) = im(d)",
				By(
					rates[1],
					real_derivative.DerivativeCaratheodory.At(
						a.TermAs[Fun[Real, Real]]("λs:real. im(γ(s))"), t, a.TermAs[Real]("im(d)"))),
				Named("ψ₂"))
			imSlope := a.Conjuncts(
				imFactored,
				"im(γ(s)) − im(γ(t)) = ψ₂(s)·(s − t) at every s",
				"ψ₂ is continuous at t",
				"ψ₂(t) = im(d)")
			pathIncrement := a.Have(
				"so γ(s) − γ(t) is the number with parts ψ₁(s) and ψ₂(s) times the real s − t",
				"∀s:real. γ(s) - γ(t) = complex(ψ₁(s), ψ₂(s)) * &(s - t)",
				Derive(func(b *Argument) {
					s := b.FixAs[Real]("s")
					b.Show(
						"part by part, these are the two real factorizations",
						Simp(
							complex_field.Parts,
							Fwd(complex_field.PartsSub),
							Fwd(complex_field.PartsMul),
							Fwd(complex_field.PartsOfReal)),
						ByArith(reSlope[0].At(s), imSlope[0].At(s)))
				}))
			increment := a.Have(
				"and F(γ(s)) − F(γ(t)) = φ(γ(s))·(γ(s) − γ(t)) is φ(γ(s))·complex(ψ₁(s), ψ₂(s)) times s − t",
				"∀s:real. F(γ(s)) - F(γ(t)) = φ(γ(s)) * complex(ψ₁(s), ψ₂(s)) * &(s - t)",
				Derive(func(b *Argument) {
					s := b.FixAs[Real]("s")
					b.Show(
						"F's factorization at γ(s), with γ(s) − γ(t) multiplied through by φ(γ(s))",
						ByArith(slope[0].At(γ.Apply(s)), Scaled(b.TermAs[Complex]("φ(γ(s))"), pathIncrement.At(s))))
				}))
			parts := a.Have(
				"read part by part, each part of F(γ(s)) − F(γ(t)) is a real slope times s − t",
				"∀s:real. "+
					"    re(F(γ(s))) - re(F(γ(t))) = (re(φ(γ(s))) * ψ₁(s) - im(φ(γ(s))) * ψ₂(s)) * (s - t) ∧ "+
					"    im(F(γ(s))) - im(F(γ(t))) = (re(φ(γ(s))) * ψ₂(s) + im(φ(γ(s))) * ψ₁(s)) * (s - t)",
				Derive(func(b *Argument) {
					s := b.FixAs[Real]("s")
					components := b.Simplified(
						increment.At(s),
						complex_field.Parts,
						Fwd(complex_field.PartsSub),
						Fwd(complex_field.PartsMul),
						Fwd(complex_field.PartsOfReal))
					b.Show(
						"the parts of the product φ(γ(s))·complex(ψ₁(s), ψ₂(s)) times the real s − t",
						ByArith(components))
				}))
			along := a.Have(
				"γ's parts have derivatives at t, so are continuous there, and φ along γ has continuous parts at t",
				"real_continuous_at(λs:real. re(φ(γ(s))), t) ∧ real_continuous_at(λs:real. im(φ(γ(s))), t)",
				By(
					ContinuousAtAlongPath.At(φ, γ, t),
					rates[0],
					rates[1],
					slope[1],
					real_derivative.DerivativeContinuous))
			products := a.Have(
				"so are the products of those parts with ψ₁ and ψ₂",
				"real_continuous_at(λs:real. re(φ(γ(s))) * ψ₁(s), t) ∧ "+
					"real_continuous_at(λs:real. im(φ(γ(s))) * ψ₂(s), t) ∧ "+
					"real_continuous_at(λs:real. re(φ(γ(s))) * ψ₂(s), t) ∧ "+
					"real_continuous_at(λs:real. im(φ(γ(s))) * ψ₁(s), t)",
				By(along, reSlope[1], imSlope[1], real_continuous.ContinuousAtMul))
			reRe := a.TermAs[Fun[Real, Real]]("λs:real. re(φ(γ(s))) * ψ₁(s)")
			imIm := a.TermAs[Fun[Real, Real]]("λs:real. im(φ(γ(s))) * ψ₂(s)")
			reIm := a.TermAs[Fun[Real, Real]]("λs:real. re(φ(γ(s))) * ψ₂(s)")
			imRe := a.TermAs[Fun[Real, Real]]("λs:real. im(φ(γ(s))) * ψ₁(s)")
			realSlope := a.TermAs[Fun[Real, Real]]("λs:real. re(φ(γ(s))) * ψ₁(s) - im(φ(γ(s))) * ψ₂(s)")
			imaginarySlope := a.TermAs[Fun[Real, Real]]("λs:real. re(φ(γ(s))) * ψ₂(s) + im(φ(γ(s))) * ψ₁(s)")
			realSlopeContinuous := a.Have(
				"the real slope, a difference of two of them, is continuous at t: the limit of a difference",
				"real_continuous_at(λs:real. re(φ(γ(s))) * ψ₁(s) - im(φ(γ(s))) * ψ₂(s), t)",
				By(
					products,
					real_continuous.ContinuousAtIffLimit.At(reRe, t),
					real_continuous.ContinuousAtIffLimit.At(imIm, t),
					real_continuous.ContinuousAtIffLimit.At(realSlope, t),
					real_function_limits.LimitAtSub.At(
						reRe,
						imIm,
						t,
						a.TermAs[Real]("re(φ(γ(t))) * ψ₁(t)"),
						a.TermAs[Real]("im(φ(γ(t))) * ψ₂(t)"))))
			imaginarySlopeContinuous := a.Have(
				"and the imaginary slope, a sum of the other two: the limit of a sum",
				"real_continuous_at(λs:real. re(φ(γ(s))) * ψ₂(s) + im(φ(γ(s))) * ψ₁(s), t)",
				By(
					products,
					real_continuous.ContinuousAtIffLimit.At(reIm, t),
					real_continuous.ContinuousAtIffLimit.At(imRe, t),
					real_continuous.ContinuousAtIffLimit.At(imaginarySlope, t),
					real_function_limits.LimitAtAdd.At(
						reIm,
						imRe,
						t,
						a.TermAs[Real]("re(φ(γ(t))) * ψ₂(t)"),
						a.TermAs[Real]("im(φ(γ(t))) * ψ₁(t)"))))
			a.Show(
				"part by part, Carathéodory's form on the line with these slopes",
				Unfold(complex_derivative.PathDerivativeAtDef),
				SplitConj(
					Case(
						"the real part of F along γ has derivative re(l·d) at t",
						Derive(func(b *Argument) {
							factoredRe := b.Have(
								"the real slope factors the increment of re F(γ(s)), is continuous at t and is re(l·d) there",
								"∃ψ:(real → real). "+
									"    (∀s:real. re(F(γ(s))) - re(F(γ(t))) = ψ(s) * (s - t)) ∧ "+
									"    real_continuous_at(ψ, t) ∧ "+
									"    ψ(t) = re(l * d)",
								Derive(func(c *Argument) {
									c.Take(realSlope)
									c.Do(SplitConjAll(
										Case(
											"it factors the increment",
											By(parts)),
										Case(
											"it is continuous at t",
											By(realSlopeContinuous)),
										Case(
											"and at t it is re(l)·re(d) − im(l)·im(d), the real part of l·d",
											Simp(Fwd(slope[2]), Fwd(reSlope[2]), Fwd(imSlope[2]), Fwd(complex_field.PartsMul)),
											Refl())))
								}))
							b.Show(
								"so by Carathéodory's form on the line, re F(γ(s)) has derivative re(l·d) at t",
								By(
									factoredRe,
									real_derivative.DerivativeCaratheodory.At(
										b.TermAs[Fun[Real, Real]]("λs:real. re(F(γ(s)))"), t, b.TermAs[Real]("re(l * d)"))))
						})),
					Case(
						"the imaginary part of F along γ has derivative im(l·d) at t",
						Derive(func(b *Argument) {
							factoredIm := b.Have(
								"the imaginary slope factors the increment of im F(γ(s)), is continuous at t and is im(l·d) there",
								"∃ψ:(real → real). "+
									"    (∀s:real. im(F(γ(s))) - im(F(γ(t))) = ψ(s) * (s - t)) ∧ "+
									"    real_continuous_at(ψ, t) ∧ "+
									"    ψ(t) = im(l * d)",
								Derive(func(c *Argument) {
									c.Take(imaginarySlope)
									c.Do(SplitConjAll(
										Case(
											"it factors the increment",
											By(parts)),
										Case(
											"it is continuous at t",
											By(imaginarySlopeContinuous)),
										Case(
											"and at t it is re(l)·im(d) + im(l)·re(d), the imaginary part of l·d",
											Simp(Fwd(slope[2]), Fwd(reSlope[2]), Fwd(imSlope[2]), Fwd(complex_field.PartsMul)),
											Refl())))
								}))
							b.Show(
								"so by Carathéodory's form on the line, im F(γ(s)) has derivative im(l·d) at t",
								By(
									factoredIm,
									real_derivative.DerivativeCaratheodory.At(
										b.TermAs[Fun[Real, Real]]("λs:real. im(F(γ(s)))"), t, b.TermAs[Real]("im(l * d)"))))
						}))))
		}),
})}

// PathIntegrable — a function continuous at the points of a piecewise
// smooth path has an integral along it. The integrand t ↦ f(γ(t))·γ'(t) is
// read part by part. Along γ, f has continuous parts on ⟦a, b⟧, so each
// has an integral there, and an integrable function is bounded: by M₁ and
// by M₂. With |γ'| ≤ B the integrand has modulus at most (M₁ + M₂)·B, a
// complex number being no longer than the sum of its parts, and so has
// each of its parts. Those parts, sums and
// differences of products of the parts of f along γ and of γ', are
// continuous off the exceptional set k. A bounded function continuous off
// a finite set has an integral, so each part has one, and the number with
// those two integrals as its parts is the integral along γ.
var PathIntegrable = pathIntegrableThm{family.Add(registry.ProofEntry{
	Name: "PathIntegrable",
	Key:  "prop_1800b851c05a3269",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
		},
		Conclusion: "∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			smooth, fContinuous Fact,
		) {
			path := arg.Conjuncts(
				arg.Unfolded(smooth, PiecewiseSmoothPathDef),
				"the interval is ordered, a ≤ b",
				"the real part of γ is continuous on ⟦a, b⟧",
				"and so is its imaginary part",
				"off a finite set γ has velocity γ', which is bounded, with parts continuous off the set")
			k, offK := arg.UnpackAs[Set[Real]](path[3], "k")
			velocity := arg.Conjuncts(
				offK,
				"k is finite",
				"inside ⟦a, b⟧ and off k, γ has velocity γ'",
				"γ' is bounded on ⟦a, b⟧",
				"the real part of γ' is continuous on ⟦a, b⟧ off k",
				"and so is its imaginary part")
			_, speed := arg.UnpackAs[Real](velocity[2], "B")
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			onInterval := arg.Have(
				"f is continuous at γ(t) for every t in ⟦a, b⟧",
				"∀t:real. t ∈ ⟦a, b⟧ ⇒ complex_continuous_at(f, γ(t))",
				arg.ForEach(func(t *Expr[Real]) Action {
					return By(fContinuous.At(t), real_topology.ClosedIntervalMembership.At(t, a, b))
				}))
			along := arg.Have(
				"so f along γ has continuous parts on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λt:real. re(f(γ(t)))) ∧ "+
					"real_continuous_on(⟦a, b⟧, λt:real. im(f(γ(t))))",
				By(ContinuousAlongPath.At(f, γ, interval), path[1], path[2], onInterval))
			reFunction := arg.TermAs[Fun[Real, Real]]("λt:real. re(f(γ(t)))")
			imFunction := arg.TermAs[Fun[Real, Real]]("λt:real. im(f(γ(t)))")
			reArea, reIntegrable := arg.ObtainAs[Real](
				"continuous on ⟦a, b⟧, the real part of f along γ has an integral there",
				"∃I:real. real_has_integral(λt:real. re(f(γ(t))), a, b, I)",
				By(path[0], along, real_integral.ContinuousIntegrable.At(reFunction, a, b)),
				Named("I₁"))
			imArea, imIntegrable := arg.ObtainAs[Real](
				"and so has its imaginary part",
				"∃I:real. real_has_integral(λt:real. im(f(γ(t))), a, b, I)",
				By(path[0], along, real_integral.ContinuousIntegrable.At(imFunction, a, b)),
				Named("I₂"))
			_, reBounded := arg.ObtainAs[Real](
				"an integrable function is bounded: the real part by M₁",
				"∃M:real. ∀t:real. a ≤ t ∧ t ≤ b ⇒ |re(f(γ(t)))| ≤ M",
				By(reIntegrable, real_integral.IntegrableBounded.At(reFunction, a, b, reArea)),
				Named("M₁"))
			_, imBounded := arg.ObtainAs[Real](
				"and the imaginary part by M₂",
				"∃M:real. ∀t:real. a ≤ t ∧ t ≤ b ⇒ |im(f(γ(t)))| ≤ M",
				By(imIntegrable, real_integral.IntegrableBounded.At(imFunction, a, b, imArea)),
				Named("M₂"))
			modulus := arg.Have(
				"on ⟦a, b⟧ the integrand has modulus |f(γ(t))|·|γ'(t)| ≤ (M₁ + M₂)·B, as |f(γ(t))| ≤ |re| + |im|",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ |f(γ(t)) * γ'(t)| ≤ (M₁ + M₂) * B",
				Derive(func(c *Argument) {
					t := c.FixAs[Real]("t")
					inside := c.Assume()
					value := f.Apply(γ.Apply(t))
					rate := γPrime.Apply(t)
					c.Show(
						"a product of sizes below M₁ + M₂ and below B",
						ByArith(
							inside,
							reBounded.At(t),
							imBounded.At(t),
							speed.At(t),
							complex_abs.AbsMul.At(value, rate),
							complex_abs.AbsLeParts.At(value),
							complex_abs.AbsNonneg.At(value),
							complex_abs.AbsNonneg.At(rate)))
				}))
			parts := arg.Have(
				"so each part of the integrand is at most (M₁ + M₂)·B in size, a part being at most the modulus",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"a ≤ t ∧ t ≤ b",
					},
					Conclusion: "|re(f(γ(t)) * γ'(t))| ≤ (M₁ + M₂) * B ∧ |im(f(γ(t)) * γ'(t))| ≤ (M₁ + M₂) * B",
				},
				Derive(func(c *Argument) {
					t := c.FixAs[Real]("t")
					inside := c.Assume()
					integrand := c.TermAs[Complex]("f(γ(t)) * γ'(t)")
					c.Show(
						"a part is at most the modulus, which is at most (M₁ + M₂)·B",
						By(
							modulus.At(t),
							inside,
							complex_abs.ReLessEqAbs.At(integrand),
							complex_abs.ImLessEqAbs.At(integrand),
							real_construction.LessEqTrans))
				}))
			removed := arg.TermAs[Set[Real]]("⟦a, b⟧ ∖ k")
			inside := arg.Have(
				"⟦a, b⟧ less k lies inside ⟦a, b⟧",
				"⟦a, b⟧ ∖ k ⊆ ⟦a, b⟧",
				BySets())
			alongOff := arg.Have(
				"so f along γ has continuous parts on ⟦a, b⟧ off k",
				"real_continuous_on(⟦a, b⟧ ∖ k, λt:real. re(f(γ(t)))) ∧ "+
					"real_continuous_on(⟦a, b⟧ ∖ k, λt:real. im(f(γ(t))))",
				By(
					along,
					inside,
					real_continuous.ContinuousOnSubset.At(reFunction, interval, removed),
					real_continuous.ContinuousOnSubset.At(imFunction, interval, removed)))
			reContinuous := arg.Have(
				"off k the real part of the integrand, re f(γ)·re γ' − im f(γ)·im γ', is continuous",
				"real_continuous_on(⟦a, b⟧ ∖ k, λt:real. re(f(γ(t)) * γ'(t)))",
				Simp(Fwd(complex_field.PartsMul)),
				By(
					alongOff,
					velocity[3],
					velocity[4],
					real_continuous.ContinuousOnSub,
					real_continuous.ContinuousOnMul))
			imContinuous := arg.Have(
				"and so is the imaginary part, re f(γ)·im γ' + im f(γ)·re γ'",
				"real_continuous_on(⟦a, b⟧ ∖ k, λt:real. im(f(γ(t)) * γ'(t)))",
				Simp(Fwd(complex_field.PartsMul)),
				By(
					alongOff,
					velocity[3],
					velocity[4],
					real_continuous.ContinuousOnAdd,
					real_continuous.ContinuousOnMul))
			bound := arg.TermAs[Real]("(M₁ + M₂) * B")
			_, reIntegral := arg.ObtainAs[Real](
				"bounded on ⟦a, b⟧ and continuous off the finite k, the real part has an integral u",
				"∃u:real. real_has_integral(λt:real. re(f(γ(t)) * γ'(t)), a, b, u)",
				By(
					path[0],
					velocity[0],
					parts,
					reContinuous,
					real_integral.IntegrableOffFinite.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. re(f(γ(t)) * γ'(t))"), a, b, bound, k)),
				Named("u"))
			_, imIntegral := arg.ObtainAs[Real](
				"and the imaginary part an integral v",
				"∃v:real. real_has_integral(λt:real. im(f(γ(t)) * γ'(t)), a, b, v)",
				By(
					path[0],
					velocity[0],
					parts,
					imContinuous,
					real_integral.IntegrableOffFinite.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. im(f(γ(t)) * γ'(t))"), a, b, bound, k)),
				Named("v"))
			arg.Take(arg.TermAs[Complex]("complex(u, v)"))
			arg.Show(
				"the number with parts u and v is the integral along γ",
				Simp(Fwd(ComplexHasIntegralDef)),
				By(reIntegral, imIntegral))
		}),
})}

// PathIntegralPrimitive — the fundamental theorem along a path: where F is
// a primitive of f at the points of a piecewise smooth path, and f is
// continuous there, the integral of f along the path is the change of F
// between its ends. F along γ is continuous on ⟦a, b⟧, F having a
// derivative, so being continuous, at every point of γ; off the path's
// exceptional set it has velocity f(γ(t))·γ'(t) by the chain rule along a
// path; f has an integral along γ; and the Newton–Leibniz theorem, which
// allows finitely many exceptions, makes that integral F(γ(b)) − F(γ(a)).
var PathIntegralPrimitive = pathIntegralPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralPrimitive",
	Key:  "prop_c0672499b62a7262",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_derivative_at(F, γ(t), f(γ(t)))",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
		},
		Conclusion: "path_integral(f, γ, γ', a, b) = F(γ(b)) - F(γ(a))",
	},
		func(
			arg *Argument,
			F, f *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			smooth, primitive, fContinuous Fact,
		) {
			path := arg.Conjuncts(
				arg.Unfolded(smooth, PiecewiseSmoothPathDef),
				"the interval is ordered, a ≤ b",
				"the real part of γ is continuous on ⟦a, b⟧",
				"and so is its imaginary part",
				"off a finite set γ has velocity γ', which is bounded, with parts continuous off the set")
			k, offK := arg.UnpackAs[Set[Real]](path[3], "k")
			velocity := arg.Conjuncts(
				offK,
				"k is finite",
				"inside ⟦a, b⟧ and off k, γ has velocity γ'",
				"γ' is bounded on ⟦a, b⟧",
				"the real part of γ' is continuous on ⟦a, b⟧ off k",
				"and so is its imaginary part")
			onInterval := arg.Have(
				"F has a derivative, so is continuous, at γ(t) for every t in ⟦a, b⟧",
				"∀t:real. t ∈ ⟦a, b⟧ ⇒ complex_continuous_at(F, γ(t))",
				arg.ForEach(func(t *Expr[Real]) Action {
					return By(
						primitive.At(t),
						real_topology.ClosedIntervalMembership.At(t, a, b),
						complex_derivative.DerivativeContinuous.At(F, γ.Apply(t), f.Apply(γ.Apply(t))))
				}))
			along := arg.Have(
				"so F along γ has continuous parts on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λt:real. re(F(γ(t)))) ∧ "+
					"real_continuous_on(⟦a, b⟧, λt:real. im(F(γ(t))))",
				By(ContinuousAlongPath.At(F, γ, arg.TermAs[Set[Real]]("⟦a, b⟧")), path[1], path[2], onInterval))
			chain := arg.Have(
				"inside ⟦a, b⟧ and off k, F along γ has velocity f(γ(t))·γ'(t), by the chain rule along a path",
				"∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ path_derivative_at(λs:real. F(γ(s)), t, f(γ(t)) * γ'(t))",
				Derive(func(c *Argument) {
					t := c.FixAs[Real]("t")
					inside := c.Assume()
					c.Show(
						"F has derivative f(γ(t)) at γ(t), t lying in ⟦a, b⟧, and γ has velocity γ'(t) at t",
						ByArith(
							inside,
							velocity[1].At(t),
							primitive.At(t),
							PathDerivativeCompose.At(F, γ, t, f.Apply(γ.Apply(t)), γPrime.Apply(t))))
				}))
			integrand := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t)")
			I, integral := arg.ObtainAs[Complex](
				"f, continuous at the points of γ, has an integral I along it",
				"∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
				By(smooth, fContinuous, PathIntegrable.At(f, γ, γPrime, a, b)),
				Named("I"))
			increment := arg.Have(
				"by the Newton–Leibniz theorem off the finite k, I is the change of F along γ",
				"I = F(γ(b)) - F(γ(a))",
				By(
					velocity[0],
					along,
					chain,
					integral,
					ComplexNewtonLeibnizOffFinite.At(
						arg.TermAs[Fun[Real, Complex]]("λs:real. F(γ(s))"), integrand, a, b, I, k)))
			arg.Show(
				"the integral along γ is the integral of f(γ(t))·γ'(t), which is I",
				Unfold(PathIntegralDef),
				By(Normalized, increment, integral, ComplexHasIntegralValue.At(integrand, a, b, I)))
		}),
})}

// PathSpeedIntegrable — a piecewise smooth path has a length: its speed
// |γ'(t)| has an integral over ⟦a, b⟧. The speed is bounded by the bound of
// the velocity, being its own size. It is the real part of the continuous
// complex function z ↦ |z| read along γ', so it is continuous off the
// exceptional set, where the parts of γ' are; a bounded function
// continuous off a finite set has an integral.
var PathSpeedIntegrable = pathSpeedIntegrableThm{family.Add(registry.ProofEntry{
	Name: "PathSpeedIntegrable",
	Key:  "prop_36ec638fac5786e2",
	Build: family.Theorem(Statement{
		Binders: "∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
		},
		Conclusion: "∃L:real. real_has_integral(λt:real. |γ'(t)|, a, b, L)",
	},
		func(arg *Argument, γ, γPrime *Arrow[Real, Complex], a, b *Expr[Real], smooth Fact) {
			path := arg.Conjuncts(
				arg.Unfolded(smooth, PiecewiseSmoothPathDef),
				"the interval is ordered, a ≤ b",
				"the real part of γ is continuous on ⟦a, b⟧",
				"and so is its imaginary part",
				"off a finite set γ has velocity γ', which is bounded, with parts continuous off the set")
			k, offK := arg.UnpackAs[Set[Real]](path[3], "k")
			velocity := arg.Conjuncts(
				offK,
				"k is finite",
				"inside ⟦a, b⟧ and off k, γ has velocity γ'",
				"γ' is bounded on ⟦a, b⟧",
				"the real part of γ' is continuous on ⟦a, b⟧ off k",
				"and so is its imaginary part")
			B, bounded := arg.UnpackAs[Real](velocity[2], "B")
			speed := arg.TermAs[Fun[Real, Real]]("λt:real. |γ'(t)|")
			sizeAlong := arg.Simplified(
				ContinuousAlongPath.At(
					arg.TermAs[Fun[Complex, Complex]]("λz:complex. &|z|"),
					γPrime,
					arg.TermAs[Set[Real]]("⟦a, b⟧ ∖ k")),
				Fwd(complex_field.PartsOfReal))
			continuous := arg.Have(
				"off k the speed is continuous: it is the real part of the "+
					"continuous z ↦ &|z| read along γ', whose parts are continuous off k",
				"real_continuous_on(⟦a, b⟧ ∖ k, λt:real. |γ'(t)|)",
				By(sizeAlong, velocity[3], velocity[4], complex_topology.ContinuousAtParts))
			speedBound := arg.Have(
				"and bounded by B on ⟦a, b⟧, the speed being its own size",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ ||γ'(t)|| ≤ B",
				Derive(func(c *Argument) {
					t := c.FixAs[Real]("t")
					inside := c.Assume()
					c.Show(
						"a modulus is not negative, so it is its own size, and γ' is bounded by B",
						By(
							Normalized,
							inside,
							bounded.At(t),
							real_sgn_abs.AbsFixedIffNonneg.At(c.TermAs[Real]("|γ'(t)|")),
							complex_abs.AbsNonneg.At(γPrime.Apply(t))))
				}))
			arg.Show(
				"bounded on ⟦a, b⟧ and continuous off the finite k, the speed has an integral",
				By(
					path[0],
					velocity[0],
					speedBound,
					continuous,
					real_integral.IntegrableOffFinite.At(speed, a, b, B, k)))
		}),
})}

// PathIntegralBound — the ML estimate: if f is continuous at the points of
// a piecewise smooth path and bounded there by M, its integral along the
// path has modulus at most M times the path's length. The integrand
// f(γ(t))·γ'(t) has modulus |f(γ(t))|·|γ'(t)| ≤ M·|γ'(t)|, and M·|γ'|
// has integral M·L, L the integral of the speed; a dominated integral is
// at most the dominating one.
var PathIntegralBound = pathIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralBound",
	Key:  "prop_ea47b41f47484926",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀γ γ':(real → complex). ∀a b M:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t)) ∧ |f(γ(t))| ≤ M",
		},
		Conclusion: "|path_integral(f, γ, γ', a, b)| ≤ M * real_integral(λt:real. |γ'(t)|, a, b)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b, M *Expr[Real],
			smooth, bounded Fact,
		) {
			continuous := arg.Have(
				"f is continuous at the points of γ",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
				arg.ForEach(func(t *Expr[Real]) Action { return By(bounded.At(t)) }))
			integrand := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t)")
			speed := arg.TermAs[Fun[Real, Real]]("λt:real. |γ'(t)|")
			I, integral := arg.ObtainAs[Complex](
				"so f has an integral I along γ",
				"∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
				By(smooth, continuous, PathIntegrable.At(f, γ, γPrime, a, b)),
				Named("I"))
			L, length := arg.ObtainAs[Real](
				"and γ has a length L, the integral of its speed",
				"∃L:real. real_has_integral(λt:real. |γ'(t)|, a, b, L)",
				By(smooth, PathSpeedIntegrable.At(γ, γPrime, a, b)),
				Named("L"))
			dominated := arg.Have(
				"on ⟦a, b⟧ the integrand has modulus |f(γ(t))|·|γ'(t)| ≤ M·|γ'(t)|",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ |f(γ(t)) * γ'(t)| ≤ M * |γ'(t)|",
				Derive(func(c *Argument) {
					t := c.FixAs[Real]("t")
					inside := c.Assume()
					c.Show(
						"|f(γ(t))| ≤ M and |γ'(t)| ≥ 0",
						ByArith(
							inside,
							bounded.At(t),
							complex_abs.AbsMul.At(f.Apply(γ.Apply(t)), γPrime.Apply(t)),
							complex_abs.AbsNonneg.At(γPrime.Apply(t))))
				}))
			estimate := arg.Have(
				"M·|γ'| dominates the integrand and has integral M·L, so |I| ≤ M·L",
				"|I| ≤ M * L",
				By(
					integral,
					length,
					dominated,
					real_integral.HasIntegralScale.At(speed, a, b, L, M),
					ComplexHasIntegralDominated.At(
						integrand,
						arg.TermAs[Fun[Real, Real]]("λt:real. M * |γ'(t)|"),
						a,
						b,
						arg.TermAs[Real]("M * L"),
						I)))
			arg.Show(
				"the integral along γ is I, and the integral of the speed is L",
				Unfold(PathIntegralDef),
				By(
					Normalized,
					estimate,
					integral,
					length,
					ComplexHasIntegralValue.At(integrand, a, b, I),
					real_integral.HasIntegralValue.At(speed, a, b, L)))
		}),
})}

// PathIntegralAdd — the integral along a path of a sum of two functions
// continuous along it is the sum of their integrals: each has an integral
// along the path, the integrand of the sum is the sum of the integrands,
// and integrals add.
var PathIntegralAdd = pathIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralAdd",
	Key:  "prop_d3da7588c7387d62",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(g, γ(t))",
		},
		Conclusion: "path_integral(λz:complex. f(z) + g(z), γ, γ', a, b) = " +
			"path_integral(f, γ, γ', a, b) + path_integral(g, γ, γ', a, b)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			smooth, fContinuous, gContinuous Fact,
		) {
			ofF := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t)")
			ofG := arg.TermAs[Fun[Real, Complex]]("λt:real. g(γ(t)) * γ'(t)")
			ofSum := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t) + g(γ(t)) * γ'(t)")
			I, toI := arg.ObtainAs[Complex](
				"f has an integral I along γ",
				"∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
				By(smooth, fContinuous, PathIntegrable.At(f, γ, γPrime, a, b)),
				Named("I"))
			J, toJ := arg.ObtainAs[Complex](
				"and g an integral J",
				"∃J:complex. complex_has_integral(λt:real. g(γ(t)) * γ'(t), a, b, J)",
				By(smooth, gContinuous, PathIntegrable.At(g, γ, γPrime, a, b)),
				Named("J"))
			distributed := arg.Have(
				"the integrand of the sum is the sum of the integrands",
				"(λt:real. (f(γ(t)) + g(γ(t))) * γ'(t)) = (λt:real. f(γ(t)) * γ'(t) + g(γ(t)) * γ'(t))",
				Funext(),
				ByArith())
			arg.Show(
				"so the integral of the sum is I + J, integrals adding",
				Unfold(PathIntegralDef),
				distributed.Rw(),
				By(
					toI,
					toJ,
					ComplexHasIntegralAdd.At(ofF, ofG, a, b, I, J),
					ComplexHasIntegralValue.At(ofF, a, b, I),
					ComplexHasIntegralValue.At(ofG, a, b, J),
					ComplexHasIntegralValue.At(ofSum, a, b, arg.TermAs[Complex]("I + J"))))
		}),
})}

// PathIntegralSub — the integral along a path of a difference of two
// functions continuous along it is the difference of their integrals: each
// has an integral along the path, the integrand of the difference is the
// difference of the integrands, and integrals subtract.
var PathIntegralSub = pathIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralSub",
	Key:  "prop_398f7357688ba87a",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(g, γ(t))",
		},
		Conclusion: "path_integral(λz:complex. f(z) - g(z), γ, γ', a, b) = " +
			"path_integral(f, γ, γ', a, b) - path_integral(g, γ, γ', a, b)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			smooth, fContinuous, gContinuous Fact,
		) {
			ofF := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t)")
			ofG := arg.TermAs[Fun[Real, Complex]]("λt:real. g(γ(t)) * γ'(t)")
			ofDifference := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t) - g(γ(t)) * γ'(t)")
			I, toI := arg.ObtainAs[Complex](
				"f has an integral I along γ",
				"∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
				By(smooth, fContinuous, PathIntegrable.At(f, γ, γPrime, a, b)),
				Named("I"))
			J, toJ := arg.ObtainAs[Complex](
				"and g an integral J",
				"∃J:complex. complex_has_integral(λt:real. g(γ(t)) * γ'(t), a, b, J)",
				By(smooth, gContinuous, PathIntegrable.At(g, γ, γPrime, a, b)),
				Named("J"))
			distributed := arg.Have(
				"the integrand of the difference is the difference of the integrands",
				"(λt:real. (f(γ(t)) - g(γ(t))) * γ'(t)) = (λt:real. f(γ(t)) * γ'(t) - g(γ(t)) * γ'(t))",
				Funext(),
				ByArith())
			arg.Show(
				"so the integral of the difference is I − J, integrals subtracting",
				Unfold(PathIntegralDef),
				distributed.Rw(),
				By(
					toI,
					toJ,
					ComplexHasIntegralSub.At(ofF, ofG, a, b, I, J),
					ComplexHasIntegralValue.At(ofF, a, b, I),
					ComplexHasIntegralValue.At(ofG, a, b, J),
					ComplexHasIntegralValue.At(ofDifference, a, b, arg.TermAs[Complex]("I - J"))))
		}),
})}

// PathIntegralScale — the integral along a path of a constant multiple of a
// function continuous along it is that multiple of its integral: the
// integrand of k·f is k times the integrand of f, and integrals scale.
var PathIntegralScale = pathIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralScale",
	Key:  "prop_35cbd91261e75663",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀γ γ':(real → complex). ∀a b:real. ∀k:complex.",
		Hypotheses: []string{
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
		},
		Conclusion: "path_integral(λz:complex. k * f(z), γ, γ', a, b) = k * path_integral(f, γ, γ', a, b)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			k *Expr[Complex],
			smooth, fContinuous Fact,
		) {
			ofF := arg.TermAs[Fun[Real, Complex]]("λt:real. f(γ(t)) * γ'(t)")
			ofMultiple := arg.TermAs[Fun[Real, Complex]]("λt:real. k * (f(γ(t)) * γ'(t))")
			I, toI := arg.ObtainAs[Complex](
				"f has an integral I along γ",
				"∃I:complex. complex_has_integral(λt:real. f(γ(t)) * γ'(t), a, b, I)",
				By(smooth, fContinuous, PathIntegrable.At(f, γ, γPrime, a, b)),
				Named("I"))
			regrouped := arg.Have(
				"the integrand of k·f is k times the integrand of f",
				"(λt:real. k * f(γ(t)) * γ'(t)) = (λt:real. k * (f(γ(t)) * γ'(t)))",
				Funext(),
				ByArith())
			arg.Show(
				"so the integral of k·f is k·I, integrals scaling",
				Unfold(PathIntegralDef),
				regrouped.Rw(),
				By(
					toI,
					ComplexHasIntegralScale.At(ofF, a, b, k, I),
					ComplexHasIntegralValue.At(ofF, a, b, I),
					ComplexHasIntegralValue.At(ofMultiple, a, b, arg.TermAs[Complex]("k * I"))))
		}),
})}

// PathIntegralSum — the integral along a path of a finite sum of functions,
// each continuous along it, is the sum of their integrals. By induction on
// the index set, the partial sums staying continuous along the path: over ∅
// the sum is the function 0, which has the constant 0 as a primitive, so its
// integral is 0; one index x more adds F(x), continuous along the path, to
// the sum, and PathIntegralAdd adds its integral on.
var PathIntegralSum = pathIntegralSumThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralSum",
	Key:  "prop_adf9ca8709cea9a9",
	Build: family.Theorem(Statement{
		Binders: "∀I:set(A). ∀F:(A → complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"finite(I)",
			"piecewise_smooth_path(γ, γ', a, b)",
			"∀i:A. ∀t:real. i ∈ I ∧ a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(F(i), γ(t))",
		},
		Conclusion: "path_integral(λz:complex. Σ_{i∈I} F(i, z), γ, γ', a, b) = " +
			"Σ_{i∈I} path_integral(F(i), γ, γ', a, b)",
	},
		func(
			arg *Argument,
			I *Expr[Set[A]],
			F *Arrow2[A, Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			finite, smooth, continuous Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			carried := arg.TermAs[Set[Set[A]]](
				"λJ:set(A). " +
					"    (∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. Σ_{i∈J} F(i, z), γ(t))) ∧ " +
					"    path_integral(λz:complex. Σ_{i∈J} F(i, z), γ, γ', a, b) = " +
					"    Σ_{i∈J} path_integral(F(i), γ, γ', a, b)")
			alongPath := arg.TermAs[Set[A]]("λi:A. ∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(F(i), γ(t))")
			arg.Show(
				"the induction carries continuity along the path and the "+
					"equation from ∅ to I, each F(i) being continuous along it",
				ByInduction(finite_set.FiniteInductFreshOn.At(carried, alongPath, I), finite, continuous,
					Case(
						"over ∅ the sum is the function 0, which has the constant 0 as a primitive",
						Simp(Fwd(monoidal.Clauses.Read(addition)), Fwd(comm_ring.NeutralAdd.Read(complex_field.CommRing))),
						Derive(func(d *Argument) {
							zero := d.TermAs[Fun[Complex, Complex]]("λz:complex. &0")
							constant := d.Have(
								"the function 0 is continuous along the path",
								"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. &0, γ(t))",
								By(complex_topology.ContinuousAtConst))
							vanishes := d.Have(
								"so its integral is the change of the primitive 0 between the ends, which is 0",
								"path_integral(λz:complex. &0, γ, γ', a, b) = &0",
								ByArith(
									smooth,
									constant,
									complex_derivative.DerivativeConst,
									PathIntegralPrimitive.At(zero, zero, γ, γPrime, a, b)))
							d.Show(
								"both hold over ∅",
								By(constant, vanishes))
						})),
					Case(
						"one index x more adds F(x), continuous along the path, to the sum and to its integral",
						Derive(func(d *Argument) {
							x, J := d.FixAs[A]("x"), d.FixAs[Set[A]]("J")
							parts := d.Conjuncts(
								d.Assume(),
								"the sum over J is continuous along the path",
								"its integral is the sum of the integrals over J",
								"x is not in J",
								"J is finite",
								"F(x) is continuous along the path",
								"so is every F(i) for i in J")
							peel := d.Have(
								"x being new, the sum over J with x put in is F(x) plus the sum over J",
								"(λz:complex. Σ_{i∈insert(x, J)} F(i, z)) = (λz:complex. F(x, z) + Σ_{i∈J} F(i, z))",
								Funext(),
								Derive(func(e *Argument) {
									e.FixAs[Complex]("z")
									e.Show(
										"one turn of the sum takes x out",
										By(
											parts[3],
											parts[2],
											monoidal.OneTurn.Read(addition).At(J, x, e.TermAs[Fun[A, Complex]]("λi:A. F(i, z)"))))
								}))
							sumContinuous := d.Have(
								"F(x) plus the sum over J is continuous along the path",
								"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. F(x, z) + Σ_{i∈J} F(i, z), γ(t))",
								By(parts[4], parts[0], complex_topology.ContinuousAtAdd))
							integral := d.Have(
								"its integral is the integral of F(x) plus the sum of "+
									"the integrals over J, which one turn of that sum gives",
								"path_integral(λz:complex. F(x, z) + Σ_{i∈J} F(i, z), γ, γ', a, b) = "+
									"Σ_{i∈insert(x, J)} path_integral(F(i), γ, γ', a, b)",
								By(
									smooth,
									parts[4],
									parts[0],
									parts[1],
									parts[3],
									parts[2],
									PathIntegralAdd.At(
										d.TermAs[Fun[Complex, Complex]]("F(x)"),
										d.TermAs[Fun[Complex, Complex]]("λz:complex. Σ_{i∈J} F(i, z)"),
										γ,
										γPrime,
										a,
										b),
									monoidal.OneTurn.Read(addition).At(
										J, x, d.TermAs[Fun[A, Complex]]("λi:A. path_integral(F(i), γ, γ', a, b)"))))
							d.Show(
								"so both hold over J with x put in",
								peel.Rw(),
								By(sumContinuous, integral))
						}))))
		}),
})}

// PathIntegralCongruence — the integral along a path sees a function only
// at the points the path passes between a and b: two functions that agree
// at γ(t) for every t between a and b, whichever way round they stand, have
// integrands f(γ(t))·γ'(t) and g(γ(t))·γ'(t) that agree there, part by
// part, and the integral of each part from a to b sees only its values
// between a and b (real_integral.IntegralCongruence).
var PathIntegralCongruence = pathIntegralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "PathIntegralCongruence",
	Key:  "prop_d39b9fb47c0dda97",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"∀t:real. min(a, b) ≤ t ∧ t ≤ max(a, b) ⇒ f(γ(t)) = g(γ(t))",
		},
		Conclusion: "path_integral(f, γ, γ', a, b) = path_integral(g, γ, γ', a, b)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			agree Fact,
		) {
			arg.Show(
				"between a and b the integrands agree, so do their real and "+
					"imaginary parts, and so do the parts' integrals from a to b",
				Unfold(PathIntegralDef),
				Unfold(ComplexIntegralDef),
				By(
					agree,
					real_integral.IntegralCongruence.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. re(f(γ(t)) * γ'(t))"),
						arg.TermAs[Fun[Real, Real]]("λt:real. re(g(γ(t)) * γ'(t))"),
						a,
						b),
					real_integral.IntegralCongruence.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. im(f(γ(t)) * γ'(t))"),
						arg.TermAs[Fun[Real, Real]]("λt:real. im(g(γ(t)) * γ'(t))"),
						a,
						b)))
		}),
})}

// SegmentPathDerivative — the segment from z to w moves at the constant
// velocity w − z: its point at s has parts re(z) + (re(w) − re(z))·s and
// im(z) + (im(w) − im(z))·s, each a constant plus a multiple of s, whose
// derivatives are the parts of w − z.
var SegmentPathDerivative = segmentPathDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SegmentPathDerivative",
	Key:  "prop_28d1221bdb6e0a33",
	Build: family.Theorem("∀z w:complex. ∀t:real. path_derivative_at(segment_path(z, w), t, w - z)",
		func(a *Argument, z, w *Expr[Complex], t *Expr[Real]) {
			segment := a.Have(
				"the segment's point at s has parts re(z) + (re(w) − re(z))·s and im(z) + (im(w) − im(z))·s",
				"segment_path(z, w) = λs:real. complex(re(z) + (re(w) - re(z)) * s, im(z) + (im(w) - im(z)) * s)",
				Funext(),
				Simp(
					Fwd(SegmentPathDef),
					complex_field.Parts,
					Fwd(complex_field.PartsAdd),
					Fwd(complex_field.PartsSub),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal)),
				ByArith())
			velocity := a.Have(
				"and w − z has parts re(w) − re(z) and im(w) − im(z)",
				"w - z = complex(re(w) - re(z), im(w) - im(z))",
				Simp(complex_field.Parts, Fwd(complex_field.PartsSub)),
				ByArith())
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
			identity := a.TermAs[Fun[Real, Real]]("λs:real. s")
			a.Show(
				"read part by part, each part of the segment is to "+
					"have the matching part of w − z as its derivative",
				Simp(Fwd(segment), Fwd(velocity), Fwd(complex_derivative.PathDerivativeAtDef)),
				SplitConj(
					Case(
						"the real part re(z) + (re(w) − re(z))·s has derivative 0 + (re(w) − re(z))·1 = re(w) − re(z)",
						By(
							real_derivative.DerivativeAdd.At(
								a.TermAs[Fun[Real, Real]]("λs:real. re(z)"),
								a.TermAs[Fun[Real, Real]]("λs:real. (re(w) - re(z)) * s"),
								t,
								zero,
								a.TermAs[Real]("(re(w) - re(z)) * &1")),
							real_derivative.DerivativeConst.At(a.TermAs[Real]("re(z)"), t),
							real_derivative.DerivativeScale.At(identity, t, one, a.TermAs[Real]("re(w) - re(z)")),
							real_derivative.DerivativeId.At(t),
							real_construction.AddLeftId,
							real_ring.MulRightId)),
					Case(
						"the imaginary part im(z) + (im(w) − im(z))·s has derivative 0 + (im(w) − im(z))·1 = im(w) − im(z)",
						By(
							real_derivative.DerivativeAdd.At(
								a.TermAs[Fun[Real, Real]]("λs:real. im(z)"),
								a.TermAs[Fun[Real, Real]]("λs:real. (im(w) - im(z)) * s"),
								t,
								zero,
								a.TermAs[Real]("(im(w) - im(z)) * &1")),
							real_derivative.DerivativeConst.At(a.TermAs[Real]("im(z)"), t),
							real_derivative.DerivativeScale.At(identity, t, one, a.TermAs[Real]("im(w) - im(z)")),
							real_derivative.DerivativeId.At(t),
							real_construction.AddLeftId,
							real_ring.MulRightId))))
		}),
})}

// SegmentPiecewiseSmooth — the segment from z to w, run on ⟦0, 1⟧ at its
// velocity w − z, is a piecewise smooth path, with no exceptional point:
// it has that velocity everywhere, so its parts are continuous, and the
// velocity is a constant, bounded by its modulus, with constant parts.
var SegmentPiecewiseSmooth = segmentPiecewiseSmoothThm{family.Add(registry.ProofEntry{
	Name: "SegmentPiecewiseSmooth",
	Key:  "prop_af1899a84f87b4d9",
	Build: family.Theorem("∀z w:complex. "+
		"    piecewise_smooth_path(segment_path(z, w), λt:real. w - z, &0, &1)",
		func(a *Argument, z, w *Expr[Complex]) {
			parts := a.Have(
				"the segment has a velocity at every point, so its parts are continuous on ⟦0, 1⟧",
				"real_continuous_on(⟦&0, &1⟧, λt:real. re(segment_path(z, w, t))) ∧ "+
					"real_continuous_on(⟦&0, &1⟧, λt:real. im(segment_path(z, w, t)))",
				By(
					PathDerivativeContinuousOn.At(
						a.TermAs[Fun[Real, Complex]]("segment_path(z, w)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. w - z"),
						a.TermAs[Set[Real]]("⟦&0, &1⟧")),
					SegmentPathDerivative))
			a.Show(
				"each clause of piecewise smoothness on ⟦0, 1⟧",
				Simp(Fwd(PiecewiseSmoothPathDef)),
				SplitConjAll(
					Case(
						"the interval is ordered, 0 ≤ 1",
						ByArith()),
					Case(
						"the real part of the segment is continuous on ⟦0, 1⟧",
						By(parts)),
					Case(
						"and so is its imaginary part",
						By(parts)),
					Case(
						"no point need be set aside",
						Witness(a.TermAs[Set[Real]]("∅")),
						SplitConjAll(
							Case(
								"the empty set is finite",
								By(finite_set.FiniteRules)),
							Case(
								"inside ⟦0, 1⟧ the segment has velocity w − z",
								By(SegmentPathDerivative)),
							Case(
								"the velocity is bounded by its modulus |w − z|",
								Witness(a.TermAs[Real]("|w - z|")),
								ByArith()),
							Case(
								"its real part is a constant, so continuous",
								By(real_continuous.ContinuousOnConst)),
							Case(
								"and so is its imaginary part",
								By(real_continuous.ContinuousOnConst))))))
		}),
})}

// SegmentIntegrandContinuous — along a segment, a function continuous at
// its points gives an integrand with continuous parts: the segment has a
// velocity everywhere, so its parts are continuous on ⟦0, 1⟧, f read along
// it then has continuous parts there, and so has f times the constant
// velocity w − z.
var SegmentIntegrandContinuous = segmentIntegrandContinuousThm{family.Add(registry.ProofEntry{
	Name: "SegmentIntegrandContinuous",
	Key:  "prop_7544a69fbc8005a1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w:complex.",
		Hypotheses: []string{
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
		},
		Conclusion: "real_continuous_on(⟦&0, &1⟧, λu:real. re(f(segment_path(z, w, u)) * (w - z))) ∧ " +
			"real_continuous_on(⟦&0, &1⟧, λu:real. im(f(segment_path(z, w, u)) * (w - z)))",
	},
		func(arg *Argument, f *Arrow[Complex, Complex], z, w *Expr[Complex], continuous Fact) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			unit := arg.TermAs[Set[Real]]("⟦&0, &1⟧")
			segment := arg.TermAs[Fun[Real, Complex]]("segment_path(z, w)")
			pathParts := arg.Have(
				"the segment has a velocity everywhere, so its parts are continuous on ⟦0, 1⟧",
				"real_continuous_on(⟦&0, &1⟧, λt:real. re(segment_path(z, w, t))) ∧ "+
					"real_continuous_on(⟦&0, &1⟧, λt:real. im(segment_path(z, w, t)))",
				By(
					PathDerivativeContinuousOn.At(segment, arg.TermAs[Fun[Real, Complex]]("λt:real. w - z"), unit),
					SegmentPathDerivative))
			onUnit := arg.Have(
				"f is continuous at the segment's point for every t in ⟦0, 1⟧",
				"∀t:real. t ∈ ⟦&0, &1⟧ ⇒ complex_continuous_at(f, segment_path(z, w, t))",
				arg.ForEach(func(t *Expr[Real]) Action {
					return By(continuous.At(t), real_topology.ClosedIntervalMembership.At(t, zero, one))
				}))
			along := arg.Have(
				"so f along the segment has continuous parts on ⟦0, 1⟧",
				"real_continuous_on(⟦&0, &1⟧, λt:real. re(f(segment_path(z, w, t)))) ∧ "+
					"real_continuous_on(⟦&0, &1⟧, λt:real. im(f(segment_path(z, w, t))))",
				By(ContinuousAlongPath.At(f, segment, unit), pathParts, onUnit))
			arg.Show(
				"and so has f times the constant w − z, part by part sums and differences of products",
				Simp(Fwd(complex_field.PartsMul)),
				By(
					along,
					real_continuous.ContinuousOnSub,
					real_continuous.ContinuousOnAdd,
					real_continuous.ContinuousOnMul,
					real_continuous.ContinuousOnConst))
		}),
})}

// SegmentReverse — run backwards, a segment reverses the integral along it:
// for f continuous at the points of the segment from z to w, the integral
// along the segment from w to z is minus the integral along the segment
// from z to w. At time t the segment from w to z is at the point the
// segment from z to w reaches at time 1 − t, with the opposite velocity, so
// its integrand is the forward one read at 1 − t, times −1; the affine
// change of variable t ↦ 1 − t turns its integral into the forward
// integrand's integral from 1 to 0, which is minus its integral from 0 to 1.
var SegmentReverse = segmentReverseThm{family.Add(registry.ProofEntry{
	Name: "SegmentReverse",
	Key:  "prop_e340a80855793c42",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w:complex.",
		Hypotheses: []string{
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
		},
		Conclusion: "«segInt»(f, w, z) = -«segInt»(f, z, w)",
		Abbrev: Abbrev{
			{Name: "forward", Text: "λu:real. f(segment_path(z, w, u)) * (w - z)"},
		},
	},
		func(arg *Argument, f *Arrow[Complex, Complex], z, w *Expr[Complex], continuous Fact) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			integrand := arg.TermAs[Fun[Real, Complex]]("«forward»")
			integrandParts := arg.Have(
				"the forward integrand f(segment_path(z, w, u))·(w − z) has continuous parts on ⟦0, 1⟧",
				"real_continuous_on(⟦&0, &1⟧, λu:real. re(«forward»(u))) ∧ "+
					"real_continuous_on(⟦&0, &1⟧, λu:real. im(«forward»(u)))",
				By(continuous, SegmentIntegrandContinuous.At(f, z, w)))
			backwards := arg.Have(
				"the backward integrand at t is the forward one at 1 − t, times −1",
				"(λt:real. f(segment_path(w, z, t)) * (z - w)) = (λt:real. «forward»(&1 + -&1 * t) * &(-&1))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]("t")
					point := b.Have(
						"at time t the segment from w to z is where the segment from z to w is at time 1 − t",
						"segment_path(w, z, t) = segment_path(z, w, &1 + -&1 * t)",
						Simp(
							Fwd(SegmentPathDef),
							Fwd(complex_field.OfRealAdd),
							Fwd(complex_field.OfRealMul),
							Fwd(complex_field.OfRealNeg)),
						ByArith())
					b.Show(
						"and z − w is −(w − z)",
						point.Rw(),
						Simp(Fwd(complex_field.OfRealNeg)),
						ByArith())
				}))
			ends := arg.Have(
				"the ends 0, 1 and 1 − 1 lie in ⟦0, 1⟧",
				"&0 ≤ &0 ∧ &0 ≤ &1 ∧ &1 ≤ &1 ∧ &0 ≤ &1 + -&1 ∧ &1 + -&1 ≤ &1",
				ByArith())
			changed := arg.Have(
				"by the change of variable t ↦ 1 − t the backward "+
					"integrand's integral is the forward integrand's from 1 to 0",
				"complex_integral(λt:real. «forward»(&1 + -&1 * t) * &(-&1), &0, &1) = "+
					"complex_integral(«forward», &1, &0)",
				By(
					integrandParts,
					ends,
					ComplexIntegralAffine.At(integrand, zero, one, arg.TermAs[Real]("-&1"), one),
					real_ring.AddRightInv.At(one)))
			additive := arg.Have(
				"integrals add over ⟦0, 1⟧ and then back from 1 to 0, to the integral over ⟦0, 0⟧",
				"complex_integral(«forward», &0, &1) + complex_integral(«forward», &1, &0) = "+
					"complex_integral(«forward», &0, &0)",
				By(integrandParts, ends, ComplexIntegralAdditive.At(integrand, zero, one, zero, one, zero)))
			empty := arg.Have(
				"and the integral over ⟦0, 0⟧ is 0: added to itself, over ⟦0, 0⟧ and again ⟦0, 0⟧, it is unchanged",
				"complex_integral(«forward», &0, &0) = &0",
				ByArith(integrandParts, ends, ComplexIntegralAdditive.At(integrand, zero, one, zero, zero, zero)))
			arg.Show(
				"so the backward integral is the forward integrand's "+
					"integral from 1 to 0, minus its integral from 0 to 1",
				Simp(Fwd(PathIntegralDef)),
				backwards.Rw(),
				ByArith(changed, additive, empty))
		}),
})}

// SegmentSplit — a segment splits at any of its points: for p the point the
// segment from z to w reaches at time s in ⟦0, 1⟧, and f continuous at the
// points of the segment, the integral along the segment from z to w is the
// integral along the segment from z to p plus that along the segment from p
// to w. The segment from z to p is the first one run at pace s, at time t at
// its point s·t with velocity s·(w − z); the segment from p to w is it from
// time s at pace 1 − s. The affine changes of variable t ↦ s·t and
// t ↦ s + (1 − s)·t turn the two integrals into the integrals of the forward
// integrand over ⟦0, s⟧ and over ⟦s, 1⟧, which add up to its integral over
// ⟦0, 1⟧.
var SegmentSplit = segmentSplitThm{family.Add(registry.ProofEntry{
	Name: "SegmentSplit",
	Key:  "prop_6959a37d97b82166",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w:complex. ∀s:real.",
		Hypotheses: []string{
			"&0 ≤ s",
			"s ≤ &1",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
		},
		Conclusion: "«segInt»(f, z, w) = " +
			"«segInt»(f, z, segment_path(z, w, s)) + «segInt»(f, segment_path(z, w, s), w)",
		Abbrev: Abbrev{
			{Name: "forward", Text: "λu:real. f(segment_path(z, w, u)) * (w - z)"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			z, w *Expr[Complex],
			s *Expr[Real],
			low, high, continuous Fact,
		) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			integrand := arg.TermAs[Fun[Real, Complex]]("«forward»")
			integrandParts := arg.Have(
				"the forward integrand f(segment_path(z, w, u))·(w − z) has continuous parts on ⟦0, 1⟧",
				"real_continuous_on(⟦&0, &1⟧, λu:real. re(«forward»(u))) ∧ "+
					"real_continuous_on(⟦&0, &1⟧, λu:real. im(«forward»(u)))",
				By(continuous, SegmentIntegrandContinuous.At(f, z, w)))
			first := arg.Have(
				"the segment from z to p at time t is the first segment at time s·t, with velocity s·(w − z)",
				"(λt:real. f(segment_path(z, segment_path(z, w, s), t)) * (segment_path(z, w, s) - z)) = "+
					"(λt:real. «forward»(&0 + s * t) * &s)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]("t")
					point := b.Have(
						"z + t·(p − z) is z + (s·t)·(w − z)",
						"segment_path(z, segment_path(z, w, s), t) = segment_path(z, w, &0 + s * t)",
						Simp(Fwd(SegmentPathDef), Fwd(complex_field.OfRealAdd), Fwd(complex_field.OfRealMul)),
						ByArith())
					b.Show(
						"and p − z is s·(w − z)",
						point.Rw(),
						Simp(Fwd(SegmentPathDef)),
						ByArith())
				}))
			second := arg.Have(
				"the segment from p to w at time t is the first at "+
					"time s + (1 − s)·t, with velocity (1 − s)·(w − z)",
				"(λt:real. f(segment_path(segment_path(z, w, s), w, t)) * (w - segment_path(z, w, s))) = "+
					"(λt:real. «forward»(s + (&1 - s) * t) * &(&1 - s))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]("t")
					point := b.Have(
						"p + t·(w − p) is z + (s + (1 − s)·t)·(w − z)",
						"segment_path(segment_path(z, w, s), w, t) = segment_path(z, w, s + (&1 - s) * t)",
						Simp(
							Fwd(SegmentPathDef),
							Fwd(complex_field.OfRealSub),
							Fwd(complex_field.OfRealAdd),
							Fwd(complex_field.OfRealMul)),
						ByArith())
					b.Show(
						"and w − p is (1 − s)·(w − z)",
						point.Rw(),
						Simp(Fwd(SegmentPathDef), Fwd(complex_field.OfRealSub), Fwd(complex_field.OfRealAdd)),
						ByArith())
				}))
			ends := arg.Have(
				"the ends 0, s, 1 and their spellings lie in ⟦0, 1⟧",
				"&0 ≤ &0 ∧ "+
					"&0 ≤ &1 ∧ "+
					"&1 ≤ &1 ∧ "+
					"&0 ≤ &0 + s ∧ "+
					"&0 + s ≤ &1 ∧ "+
					"&0 ≤ s ∧ "+
					"s ≤ &1 ∧ "+
					"&0 ≤ s + (&1 - s) ∧ "+
					"s + (&1 - s) ≤ &1",
				ByArith(low, high))
			whole := arg.Have(
				"s + (1 − s) is 1",
				"s + (&1 - s) = &1",
				ByArith())
			firstChanged := arg.Have(
				"by the change of variable t ↦ s·t the first integral is the forward integrand's over ⟦0, s⟧",
				"complex_integral(λt:real. «forward»(&0 + s * t) * &s, &0, &1) = "+
					"complex_integral(«forward», &0, s)",
				By(
					integrandParts,
					ends,
					ComplexIntegralAffine.At(integrand, zero, one, s, zero),
					real_construction.AddLeftId.At(s)))
			secondChanged := arg.Have(
				"and by t ↦ s + (1 − s)·t the second is its integral over ⟦s, 1⟧",
				"complex_integral(λt:real. «forward»(s + (&1 - s) * t) * &(&1 - s), &0, &1) = "+
					"complex_integral(«forward», s, &1)",
				By(
					integrandParts,
					ends,
					whole,
					ComplexIntegralAffine.At(integrand, zero, one, arg.TermAs[Real]("&1 - s"), s)))
			additive := arg.Have(
				"integrals add over ⟦0, s⟧ and ⟦s, 1⟧",
				"complex_integral(«forward», &0, s) + complex_integral(«forward», s, &1) = "+
					"complex_integral(«forward», &0, &1)",
				By(integrandParts, ends, ComplexIntegralAdditive.At(integrand, zero, one, zero, s, one)))
			arg.Show(
				"so the integral along the segment is the sum of the integrals along its two pieces",
				Simp(Fwd(PathIntegralDef)),
				first.Rw(),
				second.Rw(),
				ByArith(firstChanged, secondChanged, additive))
		}),
})}
