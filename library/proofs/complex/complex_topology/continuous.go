// continuous.go — continuity of complex functions at a point (the limit at
// the point being the value there) and on a set (relative to the set, and
// as a map from the subspace), its laws, and its reading along sequences;
// and continuity of a map from any space into the plane, read through its
// real and imaginary parts; and the open rectangle, open through its parts,
// and convex.

package complex_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousAtIffLimit — f is continuous at c exactly when it tends to its
// value there.
//
// The punctured disc lies in the disc, so a radius continuity hands over
// serves the limit. Conversely a radius the limit hands over serves
// continuity: a point of the disc other than c lies in the punctured
// disc, and at c itself the value is f(c), at distance 0.
var ContinuousAtIffLimit = continuousAtIffLimitThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtIffLimit",
	Key:  "prop_7520c7401b04e60e",
	Build: family.Theorem("∀f:(complex → complex). ∀c:complex. "+
		"    complex_continuous_at(f, c) ⇔ f ⟶ f(c) (at c)",
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex]) {
			a.Iff()
			a.Forward(
				"a radius continuity hands over serves the punctured disc inside it",
				func(b *Argument, continuous Fact) {
					near := b.Unfolded(continuous, ComplexContinuousAtDef)
					b.Do(Unfold(ComplexLimitAtDef))
					eps := b.FixAs[Real]("ε")
					pos := b.Assume()
					δ, radius := b.ObtainAs[Real](
						"continuity at ε hands over a radius δ inside which f is within ε of f(c)",
						"∃δ:real. &0 < δ ∧ ∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(near.At(eps), pos),
						Named("δ"))
					within := b.Have(
						"on the disc of radius δ the values of f are within ε of f(c)",
						"∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(radius))
					b.Take(δ)
					b.Do(SplitConj(
						Case(
							"the radius δ is positive, as it was obtained",
							By(radius)),
						Case(
							"and a point of the punctured disc is a point of the disc",
							Derive(func(e *Argument) {
								z := e.FixAs[Complex]("z")
								disc := e.Assume()
								e.Show(
									"so f(z) is within ε of f(c)",
									By(within.At(z), disc))
							})),
					))
				})
			a.Backward(
				"a radius the limit hands over serves continuity, the value at c itself being f(c)",
				func(b *Argument, limit Fact) {
					near := b.Unfolded(limit, ComplexLimitAtDef)
					b.Do(Unfold(ComplexContinuousAtDef))
					eps := b.FixAs[Real]("ε")
					pos := b.Assume()
					δ, radius := b.ObtainAs[Real](
						"the limit at ε hands over a radius δ inside which f is within ε of f(c), c itself left out",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(near.At(eps), pos),
						Named("δ"))
					within := b.Have(
						"on the punctured disc of radius δ the values of f are within ε of f(c)",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(radius))
					b.Take(δ)
					b.Do(SplitConj(
						Case(
							"the radius δ is positive, as it was obtained",
							By(radius)),
						Case(
							"and at every point of the disc f is within ε of f(c)",
							Derive(func(e *Argument) {
								z := e.FixAs[Complex]("z")
								disc := e.Assume()
								e.Cases(e.Term("z = c"))
								e.When(
									"at c itself the value is f(c), at distance |f(c) − f(c)| = 0",
									func(g *Argument, same Fact) {
										g.Show(
											"f(c) − f(c) is zero, and only zero has modulus zero, below ε",
											same.Rw(),
											ByArith(complex_abs.AbsEqZero.At(g.TermAs[Complex]("f(c) - f(c)")), pos))
									})
								e.Otherwise(
									"any other point of the disc lies in the punctured disc",
									func(g *Argument, other Fact) {
										punctured := g.Have(
											"z ≠ c, so z lies a positive distance from c",
											"&0 < |z - c|",
											ByArith(other, complex_abs.AbsPosIffNonzero.At(g.TermAs[Complex]("z - c"))))
										g.Show(
											"so f(z) is within ε of f(c)",
											By(within.At(z), punctured, disc))
									})
							})),
					))
				})
		}),
})}

// ContinuousAtLocal — continuity at c is decided on a disc about c: where
// f agrees there with a function g continuous at c, the two have the same
// limits at c (LimitAtLocal), so f tends to g(c), which is f(c).
var ContinuousAtLocal = continuousAtLocalThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtLocal",
	Key:  "prop_c2cd969961c4344a",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex. ∀d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀z:complex. |z - c| < d ⇒ f(z) = g(z)",
			"complex_continuous_at(g, c)",
		},
		Conclusion: "complex_continuous_at(f, c)",
	}, func(
		a *Argument,
		f, g *Arrow[Complex, Complex],
		c *Expr[Complex],
		d *Expr[Real],
		radius, agree, continuous Fact,
	) {
		centre := a.Have(
			"the two agree at c itself",
			"f(c) = g(c)",
			ByArith(radius, agree.At(c), complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
		a.Show(
			"f tends to g(c) = f(c) at c, agreeing with g on the punctured disc",
			By(
				Normalized,
				radius,
				agree,
				centre,
				continuous,
				ContinuousAtIffLimit.At(f, c),
				ContinuousAtIffLimit.At(g, c),
				LimitAtLocal.At(f, g, c, d)))
	}),
})}

// ContinuousAtCompose — a composite of continuous functions is
// continuous: where g is continuous at c and f at g(c), f ∘ g is
// continuous at c.
//
// g tends to its value g(c), and f is continuous there, so f ∘ g tends to
// f(g(c)), which is its value at c.
var ContinuousAtCompose = continuousAtComposeThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtCompose",
	Key:  "prop_6acb5461b97ce648",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(g, c)",
			"complex_continuous_at(f, g(c))",
		},
		Conclusion: "complex_continuous_at(f ∘ g, c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c *Expr[Complex], inner, outer Fact) {
			composite := a.Have(
				"g tends to g(c) at c, and f is continuous at g(c), so f ∘ g tends to f(g(c))",
				"(f ∘ g) ⟶ f(g(c)) (at c)",
				By(At(LimitAtCompose, g, f, c, g.Apply(c)), At(ContinuousAtIffLimit, g, c), inner, outer))
			// `o` unfolded, so that the value of f ∘ g at c is f(g(c)).
			a.Do(Unfold(functions.ComposeApply))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. f(g(z))"), c), composite))
		}),
})}

// ContinuousAtRealCompose — a continuous real function of a real quantity
// that depends continuously on a complex point depends continuously on it:
// given ε, f moves by less than ε within some η of g(c), and g(w) lies
// within η of g(c) on a disc about c, two reals being as far apart in ℂ as
// in ℝ.
var ContinuousAtRealCompose = continuousAtRealComposeThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtRealCompose",
	Key:  "prop_47b5a2179d26cb9a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀g:(complex → real). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(λw:complex. &(g(w)), c)",
			"real_continuous_at(f, g(c))",
		},
		Conclusion: "complex_continuous_at(λw:complex. &(f(g(w))), c)",
	}, func(
		a *Argument,
		f *Arrow[Real, Real],
		g *Arrow[Complex, Real],
		c *Expr[Complex],
		inner, outer Fact,
	) {
		gNear := a.Unfolded(inner, ComplexContinuousAtDef)
		fNear := a.Unfolded(outer, real_continuous.RealContinuousAtDef)
		a.Do(Unfold(ComplexContinuousAtDef))
		a.Show(
			"given ε, f moves by less than ε within some η of g(c), and g(w) lies within η of g(c) near c",
			Derive(func(b *Argument) {
				eps := b.FixAs[Real]("ε")
				positive := b.Assume()
				eta, radius := b.ObtainAs[Real](
					"f moves by less than ε within some η of g(c)",
					"∃η:real. &0 < η ∧ ∀x:real. |x - g(c)| < η ⇒ |f(x) - f(g(c))| < ε",
					By(fNear.At(eps), positive),
					Named("η"))
				b.Show(
					"g's continuity at c, read at η, gives the radius",
					By(complex_abs.AbsOfRealSub, gNear.At(eta), radius))
			}))
	}),
})}

// ContinuousAtConst — a constant function is continuous.
var ContinuousAtConst = continuousAtConstThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtConst",
	Key:  "prop_d3f046ab74536dde",
	Build: family.Theorem("∀c k:complex. complex_continuous_at(λz:complex. k, c)",
		func(a *Argument, c, k *Expr[Complex]) {
			a.Show(
				"the constant tends to its value k",
				By(
					At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. k"), c),
					At(LimitAtConst, c, k)))
		}),
})}

// ContinuousAtId — the identity is continuous.
var ContinuousAtId = continuousAtIdThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtId",
	Key:  "prop_62bd4e33faa15bd6",
	Build: family.Theorem("∀c:complex. complex_continuous_at(λz:complex. z, c)",
		func(a *Argument, c *Expr[Complex]) {
			a.Show(
				"the identity tends to the point",
				By(At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. z"), c), At(LimitAtId, c)))
		}),
})}

// ContinuousAtNeg — the negative of a continuous function is continuous.
var ContinuousAtNeg = continuousAtNegThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtNeg",
	Key:  "prop_50d826ce8beb82a1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
		},
		Conclusion: "complex_continuous_at(λz:complex. -f(z), c)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], continuous Fact) {
			negated := a.Have(
				"f tends to f(c) at c, so −f tends to −f(c)",
				"(λz:complex. -f(z)) ⟶ -f(c) (at c)",
				By(LimitAtNeg, At(ContinuousAtIffLimit, f, c), continuous))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. -f(z)"), c), negated))
		}),
})}

// ContinuousAtAdd — the sum of continuous functions is continuous.
var ContinuousAtAdd = continuousAtAddThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtAdd",
	Key:  "prop_f151be5b28d1ab23",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
			"complex_continuous_at(g, c)",
		},
		Conclusion: "complex_continuous_at(λz:complex. f(z) + g(z), c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c *Expr[Complex], fContinuous, gContinuous Fact) {
			sum := a.Have(
				"f and g tend to their values at c, so f + g tends to f(c) + g(c)",
				"(λz:complex. f(z) + g(z)) ⟶ f(c) + g(c) (at c)",
				By(
					LimitAtAdd,
					At(ContinuousAtIffLimit, f, c),
					At(ContinuousAtIffLimit, g, c),
					fContinuous,
					gContinuous))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) + g(z)"), c), sum))
		}),
})}

// ContinuousAtSub — the difference of continuous functions is continuous.
var ContinuousAtSub = continuousAtSubThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtSub",
	Key:  "prop_f662fed94b84f1",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
			"complex_continuous_at(g, c)",
		},
		Conclusion: "complex_continuous_at(λz:complex. f(z) - g(z), c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c *Expr[Complex], fContinuous, gContinuous Fact) {
			difference := a.Have(
				"f and g tend to their values at c, so f − g tends to f(c) − g(c)",
				"(λz:complex. f(z) - g(z)) ⟶ f(c) - g(c) (at c)",
				By(
					LimitAtSub,
					At(ContinuousAtIffLimit, f, c),
					At(ContinuousAtIffLimit, g, c),
					fContinuous,
					gContinuous))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(
					At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) - g(z)"), c),
					difference))
		}),
})}

// ContinuousAtMul — the product of continuous functions is continuous.
var ContinuousAtMul = continuousAtMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtMul",
	Key:  "prop_b5b682fd9035ce7a",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
			"complex_continuous_at(g, c)",
		},
		Conclusion: "complex_continuous_at(λz:complex. f(z) * g(z), c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c *Expr[Complex], fContinuous, gContinuous Fact) {
			product := a.Have(
				"f and g tend to their values at c, so f·g tends to f(c)·g(c)",
				"(λz:complex. f(z) * g(z)) ⟶ f(c) * g(c) (at c)",
				By(
					LimitAtMul,
					At(ContinuousAtIffLimit, f, c),
					At(ContinuousAtIffLimit, g, c),
					fContinuous,
					gContinuous))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(
					At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) * g(z)"), c),
					product))
		}),
})}

// ContinuousAtInv — the inverse of a function continuous at a point where
// it is not zero is continuous there.
var ContinuousAtInv = continuousAtInvThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtInv",
	Key:  "prop_ae84f8746ac4736a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
			"f(c) ≠ &0",
		},
		Conclusion: "complex_continuous_at(λz:complex. complex_inv(f(z)), c)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], continuous, nonzero Fact) {
			inverse := a.Have(
				"f tends to its nonzero value f(c), so its inverse tends to the inverse of f(c)",
				"(λz:complex. complex_inv(f(z))) ⟶ complex_inv(f(c)) (at c)",
				By(LimitAtInv, At(ContinuousAtIffLimit, f, c), continuous, nonzero))
			a.Show(
				"a function tending to its value at c is continuous there",
				By(
					At(ContinuousAtIffLimit, a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(f(z))"), c),
					inverse))
		}),
})}

// ContinuousAtNonexpanding — a function that moves no point further from
// its value at c than the point lies from c is continuous at c.
//
// The radius is ε itself: a point within ε of c has its value within ε of
// the value at c.
var ContinuousAtNonexpanding = continuousAtNonexpandingThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtNonexpanding",
	Key:  "prop_42d52848b2e5d6fe",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex.",
		Hypotheses: []string{
			"∀z:complex. |f(z) - f(c)| ≤ |z - c|",
		},
		Conclusion: "complex_continuous_at(f, c)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], bound Fact) {
			a.Do(Unfold(ComplexContinuousAtDef))
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			a.Take(eps)
			a.Do(SplitConj(
				Case(
					"the radius is ε itself, which is positive",
					By(pos)),
				Case(
					"and a point within ε of c has its value within ε of f(c)",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						disc := b.Assume()
						b.Show(
							"|f(z) − f(c)| ≤ |z − c| < ε",
							ByArith(bound.At(z), disc))
					})),
			))
		}),
})}

// ContinuousAtConj — conjugation is continuous.
//
// The difference of two conjugates is the conjugate of the difference,
// and conjugation leaves the modulus alone: conjugation moves no two
// points closer or further apart.
var ContinuousAtConj = continuousAtConjThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtConj",
	Key:  "prop_c1ba828fea862d72",
	Build: family.Theorem("∀c:complex. complex_continuous_at(λz:complex. conj(z), c)",
		func(a *Argument, c *Expr[Complex]) {
			nonExpanding := a.Have(
				"conjugation moves no point farther from conj(c) than the point lies from c",
				"∀z:complex. |conj(z) - conj(c)| ≤ |z - c|",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					reflected := b.Have(
						"the difference of the conjugates is the conjugate of the difference",
						"conj(z) - conj(c) = conj(z - c)",
						Simp(
							complex_field.Parts,
							Fwd(complex_field.ComplexConjDef),
							Fwd(complex_field.ComplexSubDef),
							Fwd(complex_field.ComplexAddDef),
							Fwd(complex_field.ComplexNegDef)),
						ByArith())
					b.Show(
						"and conjugation leaves the modulus alone",
						reflected.Rw(),
						ByArith(complex_abs.AbsConj.At(b.TermAs[Complex]("z - c"))))
				}))
			a.Show(
				"so conjugation is continuous at c",
				By(
					At(ContinuousAtNonexpanding, a.TermAs[Fun[Complex, Complex]]("λz:complex. conj(z)"), c),
					nonExpanding))
		}),
})}

// ContinuousAtParts — the real part, the imaginary part and the modulus,
// each read as a complex number, are continuous.
//
// Each moves no point further than the point moves: the parts do
// (complex_abs.PartsNonexpanding), and the moduli of two numbers differ by
// at most the modulus of their difference.
var ContinuousAtParts = continuousAtPartsThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtParts",
	Key:  "prop_e779344df40554d6",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex.",
		Conclusion: "complex_continuous_at(λz:complex. &(re(z)), c) ∧ " +
			"complex_continuous_at(λz:complex. &(im(z)), c) ∧ " +
			"complex_continuous_at(λz:complex. &(|z|), c)",
	},
		func(a *Argument, c *Expr[Complex]) {
			realPart := a.Have(
				"the real part moves no point further than the point moves",
				"∀z:complex. |&(re(z)) - &(re(c))| ≤ |z - c|",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					b.Show(
						"read as complex numbers, the real parts are |re(z) − re(c)| apart, at most the modulus of z − c",
						ByArith(
							complex_abs.AbsOfRealSub.At(b.TermAs[Real]("re(z)"), b.TermAs[Real]("re(c)")),
							complex_abs.PartsNonexpanding.At(z, c)))
				}))
			imaginaryPart := a.Have(
				"so does the imaginary part",
				"∀z:complex. |&(im(z)) - &(im(c))| ≤ |z - c|",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					b.Show(
						"read as complex numbers, the imaginary parts are "+
							"|im(z) − im(c)| apart, at most the modulus of z − c",
						ByArith(
							complex_abs.AbsOfRealSub.At(b.TermAs[Real]("im(z)"), b.TermAs[Real]("im(c)")),
							complex_abs.PartsNonexpanding.At(z, c)))
				}))
			modulus := a.Have(
				"and so does the modulus",
				"∀z:complex. |&(|z|) - &(|c|)| ≤ |z - c|",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					b.Show(
						"read as complex numbers, the moduli are ||z| − |c|| "+
							"apart, at most |z − c| by the reverse triangle inequality",
						ByArith(
							complex_abs.AbsOfRealSub.At(b.TermAs[Real]("|z|"), b.TermAs[Real]("|c|")),
							complex_abs.AbsTriangleReverse.At(z, c)))
				}))
			a.Show(
				"each moves no point further than the point moves, so each is continuous at c",
				By(
					At(ContinuousAtNonexpanding, a.TermAs[Fun[Complex, Complex]]("λz:complex. &(re(z))"), c),
					realPart,
					At(ContinuousAtNonexpanding, a.TermAs[Fun[Complex, Complex]]("λz:complex. &(im(z))"), c),
					imaginaryPart,
					At(ContinuousAtNonexpanding, a.TermAs[Fun[Complex, Complex]]("λz:complex. &(|z|)"), c),
					modulus))
		}),
})}

// ContinuousAtOn — a function continuous at every point of s is
// continuous on s.
//
// The radius continuity at c hands over serves the points of s in it,
// those being points of the disc.
var ContinuousAtOn = continuousAtOnThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtOn",
	Key:  "prop_fd788675cdf9134e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"∀z:complex. z ∈ s ⇒ complex_continuous_at(f, z)",
		},
		Conclusion: "complex_continuous_on(s, f)",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], everywhere Fact) {
			a.Do(Unfold(ComplexContinuousOnDef))
			c := a.FixAs[Complex]("c")
			inS := a.Assume()
			near := a.Unfolded(GroupPremises(inS, everywhere.At(c)), ComplexContinuousAtDef)
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			δ, radius := a.ObtainAs[Real](
				"continuity at c, at ε, hands over a radius δ inside which f is within ε of f(c)",
				"∃δ:real. &0 < δ ∧ ∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
				By(near.At(eps), pos),
				Named("δ"))
			within := a.Have(
				"on the disc of radius δ the values of f are within ε of f(c)",
				"∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
				By(radius))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive, as it was obtained",
					By(radius)),
				Case(
					"and a point of s in the disc is a point of the disc",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						point := b.Assume()
						b.Show(
							"so f(z) is within ε of f(c)",
							By(within.At(z), point))
					})),
			))
		}),
})}

// ContinuousOnSubset — continuity on a set passes to its subsets.
//
// A point of t is a point of s, and the radius continuity on s hands over
// at it serves the points of t, which are points of s.
var ContinuousOnSubset = continuousOnSubsetThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnSubset",
	Key:  "prop_fe1d1e7c9265d557",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"complex_continuous_on(s, f)",
			"t ⊆ s",
		},
		Conclusion: "complex_continuous_on(t, f)",
	},
		func(a *Argument, s, t *Expr[Set[Complex]], f *Arrow[Complex, Complex], onS, subset Fact) {
			near := a.Unfolded(onS, ComplexContinuousOnDef)
			a.Do(Unfold(ComplexContinuousOnDef))
			c := a.FixAs[Complex]("c")
			inT := a.Assume()
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			inS := a.Have(
				"c lies in t, so in s",
				"c ∈ s",
				BySets(subset, inT))
			δ, radius := a.ObtainAs[Real](
				"continuity on s at c, at ε, hands over a radius δ "+
					"inside which f is within ε of f(c) at the points of s",
				"∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ s ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
				By(near.At(c, eps), inS, pos),
				Named("δ"))
			within := a.Have(
				"at the points of s in the disc of radius δ the values of f are within ε of f(c)",
				"∀z:complex. z ∈ s ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
				By(radius))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive, as it was obtained",
					By(radius)),
				Case(
					"and a point of t in the disc is a point of s in the disc",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						point := b.Assume()
						zInS := b.Have(
							"z lies in t, so in s",
							"z ∈ s",
							BySets(subset, point))
						b.Show(
							"so f(z) is within ε of f(c)",
							By(within.At(z), zInS, point))
					})),
			))
		}),
})}

// ContinuousOnOpenIff — on an open set, continuity on the set is
// continuity at each of its points.
//
// Continuity at each point gives continuity relative to any set. On an
// open set the converse holds: a disc about c lies in s (ComplexOpenIff),
// so on the smaller of its radius and the relative radius every point of
// the disc is a point of s, where f is within ε of f(c).
var ContinuousOnOpenIff = continuousOnOpenIffThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnOpenIff",
	Key:  "prop_de56484338e087d0",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"s ∈ complex_topology",
		},
		Conclusion: "complex_continuous_on(s, f) ⇔ ∀z:complex. z ∈ s ⇒ complex_continuous_at(f, z)",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], open Fact) {
			a.Iff()
			a.Backward(
				"continuity at each point of s is continuity on s",
				func(b *Argument, everywhere Fact) {
					b.Show(
						"a function continuous at every point of s is continuous on s",
						By(ContinuousAtOn, everywhere))
				})
			a.Forward(
				"on an open set, the relative radius cut down to a disc inside s is a radius",
				func(b *Argument, onS Fact) {
					near := b.Unfolded(onS, ComplexContinuousOnDef)
					c := b.FixAs[Complex]("c")
					inS := b.Assume()
					r, inside := b.ObtainAs[Real](
						"s is open, so it holds a disc of some radius r about c",
						"∃r:real. &0 < r ∧ ∀z:complex. |z - c| < r ⇒ z ∈ s",
						By(ComplexOpenIff.At(s), open, inS),
						Named("r"))
					discParts := b.Conjuncts(
						inside,
						"r is positive",
						"and every point within r of c lies in s")
					rPos, insideAll := discParts[0], discParts[1]
					b.Do(Unfold(ComplexContinuousAtDef))
					eps := b.FixAs[Real]("ε")
					pos := b.Assume()
					δ, radius := b.ObtainAs[Real](
						"continuity on s at c, at ε, hands over a radius δ "+
							"inside which f is within ε of f(c) at the points of s",
						"∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ s ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(near.At(c, eps), inS, pos),
						Named("δ"))
					within := b.Have(
						"at the points of s in the disc of radius δ the values of f are within ε of f(c)",
						"∀z:complex. z ∈ s ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
						By(radius))
					b.Take(b.TermAs[Real]("min(δ, r)"))
					b.Do(SplitConj(
						Case(
							"the smaller of δ and r is positive, both being positive",
							By(real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("&0")), radius, rPos)),
						Case(
							"and a point of the smaller disc is a point of s in the disc of radius δ",
							Derive(func(e *Argument) {
								z := e.FixAs[Complex]("z")
								point := e.Assume()
								inBoth := e.Have(
									"a distance below the smaller radius is below δ and below r",
									"|z - c| < δ ∧ |z - c| < r",
									By(real_sup_inf.LessThanMin.At(δ, r, e.TermAs[Real]("|z - c|")), point))
								e.Show(
									"z lies in s, within δ of c, so f(z) is within ε of f(c)",
									By(within.At(z), insideAll.At(z), inBoth))
							})),
					))
				})
		}),
})}

// ContinuousOnIffMap — a function is continuous on s exactly when it is a
// continuous map from the subspace s to the plane.
//
// The subspace of s is the metric topology of s under the same distance
// (ComplexTopologySubspace), and between two metric topologies continuity
// is the ε–δ sentence of the metric chapter. Read with the distance from z
// to w as |w − z|, that sentence is continuity on s.
var ContinuousOnIffMap = continuousOnIffMapThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnIffMap",
	Key:  "prop_307e9b60144f7a0a",
	Build: family.Theorem("∀s:set(complex). ∀f:(complex → complex). "+
		"    complex_continuous_on(s, f) ⇔ "+
		"    continuous_map(subtopology(complex_topology, s), complex_topology, f)",
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex]) {
			flipped := a.Have(
				"the distance from z to w is the modulus of w − z",
				"∀z w:complex. dist(z, w) = |w - z|",
				By(metric_space.DistSym.Read(ComplexMetric), ComplexDistDef, set_basic.InUniv))
			a.Show(
				"between metric topologies continuity is the ε–δ "+
					"sentence, which read with that distance is continuity on s",
				Simp(Rev(ComplexTopologySubspace)),
				Unfold(ComplexTopologyDef),
				By(
					flipped,
					metric_space.ContinuousMapIff.Read(ComplexMetric).At(
						s,
						a.TermAs[Fun2[Complex, Complex, Real]]("complex_dist"),
						f),
					ComplexContinuousOnDef,
					set_basic.InUniv))
		}),
})}

// ModulusContinuous — the modulus is a continuous map from the plane to
// the line.
//
// The modulus of z is its distance from 0, and in a metric space the
// distance from a fixed point is continuous.
var ModulusContinuous = modulusContinuousThm{family.Add(registry.ProofEntry{
	Name: "ModulusContinuous",
	Key:  "prop_15213ac6b7b09c2",
	Build: family.Theorem("continuous_map(complex_topology, real_topology, λz:complex. |z|)",
		func(a *Argument) {
			zero := a.TermAs[Complex]("&0")
			fromZero := a.Have(
				"the modulus of z is its distance from 0",
				"∀z:complex. dist(&0, z) = |z|",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					negated := b.Have(
						"0 − z is −z",
						"&0 - z = -z",
						ByArith())
					b.Show(
						"and negation leaves the modulus alone",
						By(Normalized, negated, ComplexDistDef, complex_abs.AbsNeg.At(z)))
				}))
			distance := a.Have(
				"the distance from 0 is continuous, as the distance from a fixed point of a metric space is",
				"continuous_map(complex_topology, real_topology, λz:complex. dist(&0, z))",
				Unfold(ComplexTopologyDef),
				By(real_valued.MetricDistanceContinuous.Read(ComplexMetric).At(
					a.MemberOf[on.Any](zero, set_basic.InUniv.At(zero)))))
			a.Show(
				"and that distance is the modulus",
				By(continuous.Eq.Read(distance).At(a.TermAs[Fun[Complex, Real]]("λz:complex. |z|")), fromZero))
		}),
})}

// PartsContinuous — the real and the imaginary part are continuous maps
// from the plane to the line.
//
// Neither part moves a point further than the point moves
// (complex_abs.PartsNonexpanding), so between the two metric topologies
// δ = ε serves.
var PartsContinuous = partsContinuousThm{family.Add(registry.ProofEntry{
	Name: "PartsContinuous",
	Key:  "prop_1256359b599e9339",
	Build: family.Theorem(
		"continuous_map(complex_topology, real_topology, λz:complex. re(z)) ∧ "+
			"continuous_map(complex_topology, real_topology, λz:complex. im(z))",
		func(a *Argument) {
			// The ε–δ sentence at a point x, answered by δ = ε, for either part.
			deltaIsEpsilon := func() Action {
				return Derive(func(b *Argument) {
					b.FixAs[Complex]("x")
					ε := b.FixAs[Real]("ε")
					given := b.Assume()
					b.Take(ε)
					b.Show(
						"a point within ε of x has its part within ε of the part of "+
							"x: neither part moves a point further than the point moves",
						ByArith(complex_abs.PartsNonexpanding, given, ComplexDistDef, real_sgn_abs.RealDistDef))
				})
			}
			// Both topologies are the topologies of their distances, and
			// continuity between two metric spaces is the ε–δ sentence.
			a.Do(
				Simp(Fwd(ComplexTopologyDef), Fwd(real_topology.RealTopologyMetric)),
				Simp(Fwd(real_topology.RealMetric), Fwd(metric_space.ContinuousMapIff)))
			a.Do(SplitConjAll(
				Case(
					"re(x) lies in 𝕌, the line's carrier, at every point x of the plane",
					BySets()),
				Case(
					"at every point x, δ = ε serves the real part",
					deltaIsEpsilon()),
				Case(
					"im(x) lies in 𝕌, the line's carrier, at every point x of the plane",
					BySets()),
				Case(
					"at every point x, δ = ε serves the imaginary part",
					deltaIsEpsilon()),
			))
		}),
})}

// ContinuousIffParts — a map into the plane is continuous exactly when its
// real and imaginary parts are.
//
// Forward, each part is the map followed by re or im, which are continuous
// (PartsContinuous). Backward, the preimage of an open v is open by the
// pointwise criterion in R: about a point x of it, v holds a disc of some
// radius r about h(x) (ComplexOpenIff), and the points whose parts lie
// within r/2 of those of h(x) form the meet of two open preimages under
// the parts. Each of them has its value within r of h(x), a modulus being
// at most the sum of the moduli of its parts, so in v.
var ContinuousIffParts = continuousIffPartsThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIffParts",
	Key:  "prop_7fc1912875344068",
	Build: family.Theorem(Statement{
		Binders:    "∀R:set(set(A)). ∀h:(A → complex).",
		Hypotheses: []string{"is_topology(R)"},
		Conclusion: "continuous_map(R, complex_topology, h) ⇔ " +
			"continuous_map(R, real_topology, λx:A. re(h(x))) ∧ " +
			"continuous_map(R, real_topology, λx:A. im(h(x)))",
	},
		func(
			a *Argument,
			R *Expr[Set[Set[A]]],
			h *Arrow[A, Complex],
			topology topological_space.IsTopologyFact[on.R],
		) {
			a.Iff()
			a.Forward(
				"the parts of a continuous map into the plane are the map followed by re and im",
				func(b *Argument, continuity Fact) {
					realPart := b.Have(
						"h followed by the real part is continuous",
						"continuous_map(R, real_topology, (λz:complex. re(z)) ∘ h)",
						By(continuous.Compose.Read(continuity), PartsContinuous))
					imaginaryPart := b.Have(
						"h followed by the imaginary part is continuous",
						"continuous_map(R, real_topology, (λz:complex. im(z)) ∘ h)",
						By(continuous.Compose.Read(continuity), PartsContinuous))
					b.Show(
						"and the two composites are the parts of h",
						By(realPart, imaginaryPart, functions.ComposeApply))
				})
			a.Backward(
				"a map with continuous parts is continuous into the plane",
				func(b *Argument, parts Fact) {
					continuousParts := b.Conjuncts(
						parts,
						"the real part of h is continuous",
						"the imaginary part of h is continuous")
					realPart, imaginaryPart := continuousParts[0], continuousParts[1]
					b.Show(
						"h is continuous into the plane",
						continuous.ContinuousMap.Intro(
							Case(
								"every complex number is a point of the plane",
								BySets(ComplexTopologySpace)),
							Case(
								"the preimage of an open set v is open, by the pointwise criterion in R",
								Derive(func(c *Argument) {
									v := c.FixAs[Set[Complex]]("v")
									open := c.Assume()
									c.Do(Simp(Fwd(topological_space.OpenPointwise)))
									x := c.FixAs[A]("x")
									position := c.Have(
										"x is a point of the space whose value lies in v",
										"x ∈ ⋃R ∧ h(x) ∈ v",
										BySets(c.Assume()))
									_, disc := c.ObtainAs[Real](
										"v holds a disc of some radius r about h(x)",
										"∃r:real. &0 < r ∧ ∀w:complex. |w - h(x)| < r ⇒ w ∈ v",
										By(open, position, ComplexOpenIff.At(v)),
										Named("r"))
									radius := c.Conjuncts(
										disc,
										"r is positive",
										"every point within r of h(x) lies in v")
									rPositive, insideV := radius[0], radius[1]
									half := c.TermAs[Real]("r / &2")
									_, UEq := c.LetAs[Set[A]](
										"U",
										"preimage_on(⋃R, λz:A. re(h(z)), {y:real | |y - re(h(x))| < r / &2})")
									_, VEq := c.LetAs[Set[A]](
										"V",
										"preimage_on(⋃R, λz:A. im(h(z)), {y:real | |y - im(h(x))| < r / &2})")
									UOpen := c.Have(
										"U is open, the preimage under the real part of an interval about re(h(x))",
										"U ∈ R",
										UEq.Rw(),
										By(
											continuous.PreimageOpen.Read(realPart),
											real_topology.BallOpen.At(c.TermAs[Real]("re(h(x))"), half)))
									VOpen := c.Have(
										"V is open, the preimage under the imaginary part of an interval about im(h(x))",
										"V ∈ R",
										VEq.Rw(),
										By(
											continuous.PreimageOpen.Read(imaginaryPart),
											real_topology.BallOpen.At(c.TermAs[Real]("im(h(x))"), half)))
									atCentre := c.Have(
										"the parts of h(x) lie within r/2 of themselves",
										"|re(h(x)) - re(h(x))| < r / &2 ∧ |im(h(x)) - im(h(x))| < r / &2",
										ByArith(rPositive))
									c.Take(c.TermAs[Set[A]]("U ∩ V"))
									c.Do(SplitConjAll(
										Case(
											"the meet of U and V is open",
											By(topological_space.InterOpen.Read(topology), UOpen, VOpen)),
										Case(
											"a point y of the meet has its value within r of h(x), hence in v",
											Simp(Fwd(set_basic.SubsetDef)),
											Derive(func(d *Argument) {
												y := d.FixAs[A]("y")
												near := d.Have(
													"y is a point of the space whose parts lie within r/2 of those of h(x)",
													"y ∈ ⋃R ∧ |re(h(y)) - re(h(x))| < r / &2 ∧ |im(h(y)) - im(h(x))| < r / &2",
													BySets(UEq, VEq, d.Assume()))
												within := d.Have(
													"so h(y) lies within r of h(x), a modulus being at most the sum of its parts' moduli",
													"|h(y) - h(x)| < r",
													ByArith(
														near,
														complex_abs.AbsLeParts.At(d.TermAs[Complex]("h(y) - h(x)")),
														complex_field.PartsSub.At(h.Apply(y), h.Apply(x))))
												d.Show(
													"which puts h(y) in v, and y in the preimage",
													BySets(insideV.At(h.Apply(y)), within, near))
											})),
										Case(
											"and x lies in the meet",
											BySets(UEq, VEq, atCentre, position))))
								})),
						))
				})
		}),
	Reading: "is_topology(R) is read only from right to left: there the preimage of " +
		"an open v is open by the pointwise criterion (OpenPointwise), each of its " +
		"points x lying in one meet U ∩ V of the preimages of two intervals under the " +
		"parts, open as R is closed under meets, which h carries into a disc about h(x) " +
		"inside v; left to right holds for any R, since both carriers are the whole type.",
})}

// RectangleOpenConvex — the open rectangle x₁ < Re z < x₂, y₁ < Im z < y₂
// is open, the meet of the preimages of two open intervals under the
// continuous real and imaginary parts, and convex: each coordinate of a
// point of the segment between two of its points lies between those of
// the ends.
var RectangleOpenConvex = rectangleOpenConvexThm{family.Add(registry.ProofEntry{
	Name: "RectangleOpenConvex",
	Key:  "prop_12d7e455f705b91f",
	Build: family.Theorem(Statement{
		Binders: "∀x₁ x₂ y₁ y₂:real.",
		Conclusion: "«rectangle» ∈ complex_topology ∧ " +
			"∀u v:complex. ∀t:real. " +
			"    u ∈ «rectangle» ∧ v ∈ «rectangle» ∧ &0 ≤ t ∧ t ≤ &1 ⇒ u + &t * (v - u) ∈ «rectangle»",
		Abbrev: Abbrev{
			{Name: "rectangle", Text: "{z:complex | x₁ < re(z) ∧ re(z) < x₂ ∧ y₁ < im(z) ∧ im(z) < y₂}"},
			{Name: "realBand", Text: "preimage_on(𝕌, λz:complex. re(z), ⟬x₁, x₂⟭)"},
			{Name: "imaginaryBand", Text: "preimage_on(𝕌, λz:complex. im(z), ⟬y₁, y₂⟭)"},
		},
	}, func(a *Argument, x1, x2, y1, y2 *Expr[Real]) {
		T := a.TermAs[Set[Set[Complex]]]("complex_topology")
		S := a.TermAs[Set[Set[Real]]]("real_topology")
		realBand := a.TermAs[Set[Complex]]("«realBand»")
		imaginaryBand := a.TermAs[Set[Complex]]("«imaginaryBand»")
		bands := a.Have(
			"both open coordinate intervals have open preimages",
			"«realBand» ∈ complex_topology ∧ «imaginaryBand» ∈ complex_topology",
			By(
				Normalized,
				ComplexTopologySpace,
				PartsContinuous,
				real_topology.OpenIntervalOpen.At(x1, x2),
				real_topology.OpenIntervalOpen.At(y1, y2),
				continuous.PreimageOpen.At(
					T, S, a.TermAs[Fun[Complex, Real]]("λz:complex. re(z)"), a.TermAs[Set[Real]]("⟬x₁, x₂⟭")),
				continuous.PreimageOpen.At(
					T, S, a.TermAs[Fun[Complex, Real]]("λz:complex. im(z)"), a.TermAs[Set[Real]]("⟬y₁, y₂⟭"))))
		shape := a.Have(
			"the rectangle is the intersection of the two bands",
			"«rectangle» = «realBand» ∩ «imaginaryBand»",
			Simp(
				Fwd(set_basic.Extension.Inst[Complex]()),
				Fwd(set_basic.InInter.Inst[Complex]()),
				Fwd(functions.PreimageOnDef),
				Fwd(set_basic.InUniv.Inst[Complex]()),
				Fwd(real_topology.OpenIntervalMembership)),
			BySets())
		open := a.Have(
			"an intersection of two open bands is open",
			"«rectangle» ∈ complex_topology",
			shape.Rw(),
			By(bands, ComplexTopology, topological_space.InterOpen.At(T, realBand, imaginaryBand)))
		affine := a.Have(
			"an affine combination lies between its endpoints",
			Statement{
				Binders: "∀x y l h t:real.",
				Hypotheses: []string{
					"l < x",
					"x < h",
					"l < y",
					"y < h",
					"&0 ≤ t",
					"t ≤ &1",
				},
				Conclusion: "l < x + t * (y - x) ∧ x + t * (y - x) < h",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				y := b.FixAs[Real]("y")
				b.FixAs[Real]("l")
				b.FixAs[Real]("h")
				t := b.FixAs[Real]("t")
				bounds := b.Assume()
				s := b.TermAs[Real]("&1 - t")
				b.Show(
					"use the smaller and larger endpoint in the two comparisons",
					ByArith(
						bounds,
						real_order_ring.LessEqMulLeft.At(t, x, y),
						real_order_ring.LessEqMulLeft.At(t, y, x),
						real_order_ring.LessEqMulLeft.At(s, x, y),
						real_order_ring.LessEqMulLeft.At(s, y, x)))
			}))
		convex := a.Have(
			"both coordinate intervals contain every point of the segment",
			Statement{
				Binders: "∀u v:complex. ∀t:real.",
				Hypotheses: []string{
					"u ∈ «rectangle»",
					"v ∈ «rectangle»",
					"&0 ≤ t",
					"t ≤ &1",
				},
				Conclusion: "u + &t * (v - u) ∈ «rectangle»",
			},
			Derive(func(b *Argument) {
				b.FixAs[Complex]("u")
				b.FixAs[Complex]("v")
				t := b.FixAs[Real]("t")
				inRect := b.Assume()
				ends := b.Have(
					"both endpoint coordinates lie in their open intervals",
					"(x₁ < re(u) ∧ re(u) < x₂ ∧ y₁ < im(u) ∧ im(u) < y₂) ∧ "+
						"(x₁ < re(v) ∧ re(v) < x₂ ∧ y₁ < im(v) ∧ im(v) < y₂)",
					BySets(inRect))
				inside := b.Have(
					"the coordinates of the segment point remain in the open intervals",
					"x₁ < re(u + &t * (v - u)) ∧ "+
						"re(u + &t * (v - u)) < x₂ ∧ "+
						"y₁ < im(u + &t * (v - u)) ∧ "+
						"im(u + &t * (v - u)) < y₂",
					Simp(
						Fwd(complex_field.PartsAdd),
						Fwd(complex_field.PartsMul),
						Fwd(complex_field.PartsSub),
						Fwd(complex_field.PartsOfReal)),
					ByArith(
						ends,
						inRect,
						affine.At(b.TermAs[Real]("re(u)"), b.TermAs[Real]("re(v)"), x1, x2, t),
						affine.At(b.TermAs[Real]("im(u)"), b.TermAs[Real]("im(v)"), y1, y2, t)))
				b.Show(
					"the two coordinates characterize the rectangle",
					BySets(inside))
			}))
		a.Show(
			"the rectangle is open and convex",
			By(open, convex))
	}),
})}

// ContinuousAtSequential — a function continuous at c carries every
// sequence tending to c to a sequence tending to its value there.
//
// Fix ε > 0. Continuity answers ε with a radius δ; the sequence, asked
// for δ, answers with an index N past which its terms lie within δ of
// c, and there f is within ε of f(c).
var ContinuousAtSequential = continuousAtSequentialThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtSequential",
	Key:  "prop_8b3c2102281e3562",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀a:(num → complex).",
		Hypotheses: []string{
			"complex_continuous_at(f, c)",
			"a ⟶ c",
		},
		Conclusion: "(λn:num. f(a(n))) ⟶ f(c)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			a *Arrow[Nat, Complex],
			isContinuous, toC Fact,
		) {
			near := arg.Unfolded(isContinuous, ComplexContinuousAtDef)
			approach := arg.Unfolded(toC, ComplexConvergesToDef)
			arg.Do(Unfold(ComplexConvergesToDef))
			eps := arg.FixAs[Real]("ε")
			pos := arg.Assume()
			δ, radius := arg.ObtainAs[Real](
				"continuity at c, at ε, hands over a radius δ inside which f is within ε of f(c)",
				"∃δ:real. &0 < δ ∧ ∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
				By(near.At(eps), pos),
				Named("δ"))
			N, tail := arg.ObtainAs[Nat](
				"a ⟶ c, asked for δ, hands over an index N past which the terms lie within δ of c",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - c| < δ",
				By(approach.At(δ), radius),
				Named("N"))
			arg.Take(N)
			n := arg.FixAs[Nat]("n")
			past := arg.Assume()
			arg.Show(
				"past N the term a(n) lies within δ of c, so f carries it within ε of f(c)",
				By(tail.At(n), past, radius))
		}),
})}
