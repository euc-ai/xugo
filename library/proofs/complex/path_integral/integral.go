// integral.go — the integral of a complex function of a real variable,
// part by part. Each law of the real integral holds for complex_has_integral
// because it holds for the real and the imaginary part: uniqueness and the
// value, the integral of a constant, the sum, the negative, the difference
// and the complex multiple, the joining and the restriction of intervals,
// the integrability of a continuous function, the additivity of the
// oriented integral and the affine change of variable, and the
// Newton–Leibniz theorem, which allows finitely many exceptional points.
// The estimate of the modulus by a dominating real integral mixes the
// parts; the integral of the modulus and a constant bound are its two
// cases.

package path_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexHasIntegralUnique — a complex function has at most one integral
// over an interval: each of its parts has at most one, and a complex
// number is its parts.
var ComplexHasIntegralUnique = complexHasIntegralUniqueThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralUnique",
	Key:  "prop_e3d8a77aa17b4b40",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b:real. ∀I J:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"complex_has_integral(g, a, b, J)",
		},
		Conclusion: "I = J",
	},
		func(arg *Argument, g *Arrow[Real, Complex], a, b *Expr[Real], I, J *Expr[Complex], toI, toJ Fact) {
			partsI := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			partsJ := arg.Conjuncts(
				arg.Unfolded(toJ, ComplexHasIntegralDef),
				"the real part of g has integral re(J)",
				"and its imaginary part im(J)")
			reEq := arg.Have(
				"the real part has only one integral",
				"re(I) = re(J)",
				By(partsI[0], partsJ[0], real_integral.HasIntegralUnique))
			imEq := arg.Have(
				"nor has the imaginary part",
				"im(I) = im(J)",
				By(partsI[1], partsJ[1], real_integral.HasIntegralUnique))
			arg.Show(
				"a complex number is its parts",
				By(reEq, imEq, complex_field.ComplexEq))
		}),
})}

// ComplexHasIntegralValue — the value complex_integral(g, a, b) is the
// integral g has: the value of each part is the part of the integral.
var ComplexHasIntegralValue = complexHasIntegralValueThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralValue",
	Key:  "prop_6c7850fd3f78fd21",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b:real. ∀I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "complex_integral(g, a, b) = I",
	},
		func(arg *Argument, g *Arrow[Real, Complex], a, b *Expr[Real], I *Expr[Complex], toI Fact) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			reValue := arg.Have(
				"so the integral of the real part is re(I)",
				"real_integral(λt:real. re(g(t)), a, b) = re(I)",
				By(parts[0], real_integral.HasIntegralValue))
			imValue := arg.Have(
				"and the integral of the imaginary part is im(I)",
				"real_integral(λt:real. im(g(t)), a, b) = im(I)",
				By(parts[1], real_integral.HasIntegralValue))
			arg.Show(
				"these are the parts of the complex integral",
				Simp(complex_field.Parts, Fwd(ComplexIntegralDef)),
				By(reValue, imValue))
		}),
})}

// ComplexIntegralConst — a complex constant k integrates over ⟦a, b⟧ to
// k·(b − a): its parts are the real constants re(k) and im(k), which
// integrate to re(k)·(b − a) and im(k)·(b − a), and these are the parts of
// k·(b − a), b − a being real.
var ComplexIntegralConst = complexIntegralConstThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralConst",
	Key:  "prop_912897f0a7374cc3",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀k:complex.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "complex_integral(λt:real. k, a, b) = k * &(b - a)",
	},
		func(arg *Argument, a, b *Expr[Real], k *Expr[Complex], ordered Fact) {
			re, im := arg.TermAs[Real]("re(k)"), arg.TermAs[Real]("im(k)")
			arg.Show(
				"the parts are the integrals of the constants re(k) "+
					"and im(k), which are re(k)·(b − a) and im(k)·(b − a)",
				Simp(
					Fwd(ComplexIntegralDef),
					complex_field.Parts,
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal)),
				ByArith(
					ordered,
					real_integral.HasIntegralConst.At(a, b, re),
					real_integral.HasIntegralConst.At(a, b, im),
					real_integral.HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. re(k)"), a, b, arg.TermAs[Real]("re(k) * (b - a)")),
					real_integral.HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. im(k)"), a, b, arg.TermAs[Real]("im(k) * (b - a)"))))
		}),
})}

// ComplexHasIntegralAdd — the sum of two complex functions has the sum of
// their integrals as its integral: the parts of a sum are the sums of the
// parts.
var ComplexHasIntegralAdd = complexHasIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralAdd",
	Key:  "prop_ed511364e328ae19",
	Build: family.Theorem(Statement{
		Binders: "∀g h:(real → complex). ∀a b:real. ∀I J:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"complex_has_integral(h, a, b, J)",
		},
		Conclusion: "complex_has_integral(λt:real. g(t) + h(t), a, b, I + J)",
	},
		func(
			arg *Argument,
			g, h *Arrow[Real, Complex],
			a, b *Expr[Real],
			I, J *Expr[Complex],
			toI, toJ Fact,
		) {
			ofG := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			ofH := arg.Conjuncts(
				arg.Unfolded(toJ, ComplexHasIntegralDef),
				"the real part of h has integral re(J)",
				"and its imaginary part im(J)")
			reSum := arg.Have(
				"the real parts add",
				"real_has_integral(λt:real. re(g(t)) + re(h(t)), a, b, re(I) + re(J))",
				By(ofG[0], ofH[0], real_integral.HasIntegralAdd))
			imSum := arg.Have(
				"and so do the imaginary parts",
				"real_has_integral(λt:real. im(g(t)) + im(h(t)), a, b, im(I) + im(J))",
				By(ofG[1], ofH[1], real_integral.HasIntegralAdd))
			arg.Show(
				"which are the parts of the sum, of the functions and of the integrals",
				Simp(Fwd(ComplexHasIntegralDef), Fwd(complex_field.PartsAdd)),
				By(reSum, imSum))
		}),
})}

// ComplexHasIntegralNeg — the negative of a complex function has the
// negative of its integral: the parts of a negative are the negatives of
// the parts.
var ComplexHasIntegralNeg = complexHasIntegralNegThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralNeg",
	Key:  "prop_5c079a892f2abe79",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b:real. ∀I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "complex_has_integral(λt:real. -g(t), a, b, -I)",
	},
		func(arg *Argument, g *Arrow[Real, Complex], a, b *Expr[Real], I *Expr[Complex], toI Fact) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			reNeg := arg.Have(
				"the negative of the real part has integral −re(I)",
				"real_has_integral(λt:real. -re(g(t)), a, b, -re(I))",
				By(parts[0], real_integral.HasIntegralNeg))
			imNeg := arg.Have(
				"and the negative of the imaginary part −im(I)",
				"real_has_integral(λt:real. -im(g(t)), a, b, -im(I))",
				By(parts[1], real_integral.HasIntegralNeg))
			arg.Show(
				"which are the parts of the negatives",
				Simp(Fwd(ComplexHasIntegralDef), Fwd(complex_field.PartsNeg)),
				By(reNeg, imNeg))
		}),
})}

// ComplexHasIntegralSub — the difference of two complex functions has the
// difference of their integrals: a difference is the sum with the
// negative.
var ComplexHasIntegralSub = complexHasIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralSub",
	Key:  "prop_fd672ecdea9cbd56",
	Build: family.Theorem(Statement{
		Binders: "∀g h:(real → complex). ∀a b:real. ∀I J:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"complex_has_integral(h, a, b, J)",
		},
		Conclusion: "complex_has_integral(λt:real. g(t) - h(t), a, b, I - J)",
	},
		func(
			arg *Argument,
			g, h *Arrow[Real, Complex],
			a, b *Expr[Real],
			I, J *Expr[Complex],
			toI, toJ Fact,
		) {
			arg.Show(
				"g − h is g plus the negative of h, whose integral is −J",
				Simp(Fwd(complex_field.ComplexSubDef)),
				By(toI, toJ, ComplexHasIntegralNeg.At(h, a, b, J), ComplexHasIntegralAdd))
		}),
})}

// ComplexHasIntegralScale — a complex multiple of a complex function has
// the multiple of its integral. The real part of c·g(t) is
// re(c)·re(g(t)) − im(c)·im(g(t)) and the imaginary part
// re(c)·im(g(t)) + im(c)·re(g(t)): each part of the product is a
// combination of the two parts of g with constant coefficients.
var ComplexHasIntegralScale = complexHasIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralScale",
	Key:  "prop_398818ad9fae3035",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b:real. ∀c I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "complex_has_integral(λt:real. c * g(t), a, b, c * I)",
	},
		func(arg *Argument, g *Arrow[Real, Complex], a, b *Expr[Real], c, I *Expr[Complex], toI Fact) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			reProduct := arg.Have(
				"re(c)·re(g(t)) − im(c)·im(g(t)) has integral re(c)·re(I) − im(c)·im(I)",
				"real_has_integral(λt:real. re(c) * re(g(t)) - im(c) * im(g(t)), "+
					"    a, "+
					"    b, "+
					"    re(c) * re(I) - im(c) * im(I))",
				By(parts[0], parts[1], real_integral.HasIntegralScale, real_integral.HasIntegralSub))
			imProduct := arg.Have(
				"and re(c)·im(g(t)) + im(c)·re(g(t)) has integral re(c)·im(I) + im(c)·re(I)",
				"real_has_integral(λt:real. re(c) * im(g(t)) + im(c) * re(g(t)), "+
					"    a, "+
					"    b, "+
					"    re(c) * im(I) + im(c) * re(I))",
				By(parts[1], parts[0], real_integral.HasIntegralScale, real_integral.HasIntegralAdd))
			arg.Show(
				"which are the parts of c·g(t) and of c·I",
				Simp(Fwd(ComplexHasIntegralDef), Fwd(complex_field.PartsMul)),
				By(reProduct, imProduct))
		}),
})}

// ComplexHasIntegralSplit — integrals over adjacent intervals add up to
// an integral over their union: each part's integrals do.
var ComplexHasIntegralSplit = complexHasIntegralSplitThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralSplit",
	Key:  "prop_138c35a5b262c245",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b c:real. ∀I J:complex.",
		Hypotheses: []string{
			"a ≤ c",
			"c ≤ b",
			"complex_has_integral(g, a, c, I)",
			"complex_has_integral(g, c, b, J)",
		},
		Conclusion: "complex_has_integral(g, a, b, I + J)",
	},
		func(
			arg *Argument,
			g *Arrow[Real, Complex],
			a, b, c *Expr[Real],
			I, J *Expr[Complex],
			ac, cb, left, right Fact,
		) {
			onLeft := arg.Conjuncts(
				arg.Unfolded(left, ComplexHasIntegralDef),
				"on ⟦a, c⟧ the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			onRight := arg.Conjuncts(
				arg.Unfolded(right, ComplexHasIntegralDef),
				"on ⟦c, b⟧ the real part of g has integral re(J)",
				"and its imaginary part im(J)")
			reJoined := arg.Have(
				"the real part has integral re(I) + re(J) over ⟦a, b⟧",
				"real_has_integral(λt:real. re(g(t)), a, b, re(I) + re(J))",
				By(ac, cb, onLeft[0], onRight[0], real_integral.HasIntegralSplit))
			imJoined := arg.Have(
				"and the imaginary part im(I) + im(J)",
				"real_has_integral(λt:real. im(g(t)), a, b, im(I) + im(J))",
				By(ac, cb, onLeft[1], onRight[1], real_integral.HasIntegralSplit))
			arg.Show(
				"which are the parts of I + J",
				Simp(Fwd(ComplexHasIntegralDef), Fwd(complex_field.PartsAdd)),
				By(reJoined, imJoined))
		}),
})}

// ComplexIntegrableSubinterval — a complex function with an integral over
// ⟦a, b⟧ has one over every subinterval ⟦c, d⟧: each part has one there,
// and the number with those two integrals as its parts is the integral of
// g.
var ComplexIntegrableSubinterval = complexIntegrableSubintervalThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegrableSubinterval",
	Key:  "prop_5831ddf56aae061e",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b c d:real. ∀I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"a ≤ c",
			"c ≤ d",
			"d ≤ b",
		},
		Conclusion: "∃J:complex. complex_has_integral(g, c, d, J)",
	},
		func(
			arg *Argument,
			g *Arrow[Real, Complex],
			a, b, c, d *Expr[Real],
			I *Expr[Complex],
			toI, ac, cd, db Fact,
		) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I) over ⟦a, b⟧",
				"and its imaginary part im(I)")
			_, reIntegral := arg.ObtainAs[Real](
				"the real part has an integral u over ⟦c, d⟧",
				"∃u:real. real_has_integral(λt:real. re(g(t)), c, d, u)",
				By(parts[0], ac, cd, db, real_integral.IntegrableSubinterval))
			_, imIntegral := arg.ObtainAs[Real](
				"and the imaginary part an integral v",
				"∃v:real. real_has_integral(λt:real. im(g(t)), c, d, v)",
				By(parts[1], ac, cd, db, real_integral.IntegrableSubinterval))
			arg.Take(arg.TermAs[Complex]("complex(u, v)"))
			arg.Show(
				"the number with parts u and v is an integral of g over ⟦c, d⟧",
				Simp(Fwd(ComplexHasIntegralDef)),
				By(reIntegral, imIntegral))
		}),
})}

// ComplexContinuousIntegrable — a complex function whose parts are
// continuous on ⟦a, b⟧ has an integral there: each part has one, and the
// number with those two integrals as its parts is the integral of g.
var ComplexContinuousIntegrable = complexContinuousIntegrableThm{family.Add(registry.ProofEntry{
	Name: "ComplexContinuousIntegrable",
	Key:  "prop_35b041b38b26bd17",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, λt:real. re(g(t)))",
			"real_continuous_on(⟦a, b⟧, λt:real. im(g(t)))",
		},
		Conclusion: "∃I:complex. complex_has_integral(g, a, b, I)",
	},
		func(
			arg *Argument,
			g *Arrow[Real, Complex],
			a, b *Expr[Real],
			ordered, reContinuous, imContinuous Fact,
		) {
			_, reIntegral := arg.ObtainAs[Real](
				"the real part, continuous on ⟦a, b⟧, has an integral u there",
				"∃u:real. real_has_integral(λt:real. re(g(t)), a, b, u)",
				By(ordered, reContinuous, real_integral.ContinuousIntegrable))
			_, imIntegral := arg.ObtainAs[Real](
				"and the imaginary part an integral v",
				"∃v:real. real_has_integral(λt:real. im(g(t)), a, b, v)",
				By(ordered, imContinuous, real_integral.ContinuousIntegrable))
			arg.Take(arg.TermAs[Complex]("complex(u, v)"))
			arg.Show(
				"the number with parts u and v is an integral of g",
				Simp(Fwd(ComplexHasIntegralDef)),
				By(reIntegral, imIntegral))
		}),
})}

// ComplexIntegralAdditive — integrals of a complex function with parts
// continuous on ⟦l, r⟧ add over adjacent stretches of ⟦l, r⟧, whatever
// their order: each part's integrals do.
var ComplexIntegralAdditive = complexIntegralAdditiveThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralAdditive",
	Key:  "prop_25889618b89155f1",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀l r a b c:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦l, r⟧, λt:real. re(g(t)))",
			"real_continuous_on(⟦l, r⟧, λt:real. im(g(t)))",
			"l ≤ a",
			"a ≤ r",
			"l ≤ b",
			"b ≤ r",
			"l ≤ c",
			"c ≤ r",
		},
		Conclusion: "complex_integral(g, a, b) + complex_integral(g, b, c) = complex_integral(g, a, c)",
	},
		func(arg *Argument, g *Arrow[Real, Complex], l, r, a, b, c *Expr[Real], within Fact) {
			arg.Show(
				"part by part, the real integrals add",
				Simp(Fwd(ComplexIntegralDef), complex_field.Parts, Fwd(complex_field.PartsAdd)),
				ByArith(
					within,
					real_integral.IntegralAdditive.At(arg.TermAs[Fun[Real, Real]]("λt:real. re(g(t))"), l, r, a, b, c),
					real_integral.IntegralAdditive.At(arg.TermAs[Fun[Real, Real]]("λt:real. im(g(t))"), l, r, a, b, c)))
		}),
})}

// ComplexIntegralAffine — an affine change of variable over ⟦0, 1⟧ for a
// complex function with parts continuous on an interval ⟦l, r⟧ holding β
// and β + α: the integral of g(β + α·t)·α over ⟦0, 1⟧ is the integral of g
// from β to β + α. Part by part it is the real change of variable.
var ComplexIntegralAffine = complexIntegralAffineThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralAffine",
	Key:  "prop_87cd1f9c9b96e44c",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀l r α β:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦l, r⟧, λt:real. re(g(t)))",
			"real_continuous_on(⟦l, r⟧, λt:real. im(g(t)))",
			"l ≤ β",
			"β ≤ r",
			"l ≤ β + α",
			"β + α ≤ r",
		},
		Conclusion: "complex_integral(λt:real. g(β + α * t) * &α, &0, &1) = complex_integral(g, β, β + α)",
	},
		func(arg *Argument, g *Arrow[Real, Complex], l, r, α, β *Expr[Real], within Fact) {
			arg.Show(
				"part by part, a real number α multiplies each part, and the real change of variable applies",
				Simp(
					Fwd(ComplexIntegralDef),
					complex_field.Parts,
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal)),
				Simp(Fwd(real_ring.MulRightZero), Fwd(real_ring.SubRightZero), Fwd(real_construction.AddLeftId)),
				By(
					within,
					real_integral.IntegralAffineSubstitution.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. re(g(t))"), l, r, α, β),
					real_integral.IntegralAffineSubstitution.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. im(g(t))"), l, r, α, β)))
		}),
})}

// ComplexHasIntegralDominated — a complex function whose modulus is
// dominated on ⟦a, b⟧ by a real function with integral J has an integral
// of modulus at most J. The component of g(t) along I, the real part of
// conj(I)·g(t), has integral re(I)² + im(I)² = |I|², and it is at most
// |conj(I)·g(t)| = |I|·|g(t)| ≤ |I|·h(t), whose integral is |I|·J; so
// |I|² ≤ |I|·J, and a positive |I| cancels. When I = 0, J is not
// negative: h dominates |g| ≥ 0.
var ComplexHasIntegralDominated = complexHasIntegralDominatedThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralDominated",
	Key:  "prop_c1f57d4f626c9299",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀h:(real → real). ∀a b J:real. ∀I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"real_has_integral(h, a, b, J)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ |g(t)| ≤ h(t)",
		},
		Conclusion: "|I| ≤ J",
	},
		func(
			arg *Argument,
			g *Arrow[Real, Complex],
			h *Arrow[Real, Real],
			a, b, J *Expr[Real],
			I *Expr[Complex],
			toI, toJ, dominated Fact,
		) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			along := arg.Have(
				"the component of g(t) along I has integral re(I)² + im(I)², by linearity on the parts",
				"real_has_integral(λt:real. re(I) * re(g(t)) + im(I) * im(g(t)), "+
					"    a, "+
					"    b, "+
					"    re(I) * re(I) + im(I) * im(I))",
				By(parts[0], parts[1], real_integral.HasIntegralScale, real_integral.HasIntegralAdd))
			schwarz := arg.Have(
				"a component along I is the real part of conj(I)·w, so at most |conj(I)·w| = |I|·|w|",
				"∀w:complex. re(I) * re(w) + im(I) * im(w) ≤ |I| * |w|",
				Derive(func(c *Argument) {
					w := c.FixAs[Complex]()
					component := c.Have(
						"the component of w along I is the real part of conj(I)·w",
						"re(conj(I) * w) = re(I) * re(w) + im(I) * im(w)",
						Simp(Fwd(complex_field.PartsMul), Fwd(complex_field.PartsConj)),
						ByArith())
					c.Show(
						"a real part is at most the modulus, and the modulus is multiplicative",
						ByArith(
							component,
							complex_abs.ReLessEqAbs.At(c.TermAs[Complex]("conj(I) * w")),
							complex_abs.AbsMul.At(c.TermAs[Complex]("conj(I)"), w),
							complex_abs.AbsConj.At(I)))
				}))
			below := arg.Have(
				"on ⟦a, b⟧ the component of g(t) along I is at most |I|·h(t)",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ re(I) * re(g(t)) + im(I) * im(g(t)) ≤ |I| * h(t)",
				arg.ForEach(func(t *Expr[Real]) Action {
					return ByArith(schwarz.At(g.Apply(t)), dominated.At(t), complex_abs.AbsNonneg.At(I))
				}))
			absI := arg.TermAs[Real]("|I|")
			compared := arg.Have(
				"so re(I)² + im(I)² is at most the integral |I|·J of |I|·h(t)",
				"re(I) * re(I) + im(I) * im(I) ≤ |I| * J",
				By(
					below,
					along,
					toJ,
					real_integral.HasIntegralScale.At(h, a, b, J, absI),
					real_integral.HasIntegralLessEq))
			arg.Cases(arg.Term("&0 < |I|"))
			arg.When(
				"when |I| is positive it cancels from |I|·|I| ≤ |I|·J",
				func(c *Argument, positive Fact) {
					c.Show(
						"|I|·|I| is re(I)² + im(I)²",
						ByArith(compared, positive, complex_abs.AbsSquare.At(I)))
				})
			arg.Otherwise(
				"when |I| is zero, J is not negative",
				func(c *Argument, zero Fact) {
					nonnegative := c.Have(
						"h dominates |g| ≥ 0 on ⟦a, b⟧",
						"∀t:real. a ≤ t ∧ t ≤ b ⇒ &0 ≤ h(t)",
						c.ForEach(func(t *Expr[Real]) Action {
							return ByArith(dominated.At(t), complex_abs.AbsNonneg.At(g.Apply(t)))
						}))
					zeroFunction := c.TermAs[Fun[Real, Real]]("λt:real. &0")
					beneath := c.Have(
						"so J is at least the integral 0·(b − a) of zero",
						"&0 * (b - a) ≤ J",
						By(
							nonnegative,
							toJ,
							real_integral.HasIntegralOrdered.At(h, a, b, J),
							real_integral.HasIntegralConst.At(a, b, c.TermAs[Real]("&0")),
							real_integral.HasIntegralLessEq.At(zeroFunction, h, a, b, c.TermAs[Real]("&0 * (b - a)"), J)))
					c.Show(
						"so |I| = 0 ≤ J",
						ByArith(zero, beneath, complex_abs.AbsNonneg.At(I)))
				})
		}),
})}

// ComplexHasIntegralAbsBound — the modulus of the integral is at most the
// integral of the modulus: |g| dominates itself.
var ComplexHasIntegralAbsBound = complexHasIntegralAbsBoundThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralAbsBound",
	Key:  "prop_e81861121f7e0b31",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b J:real. ∀I:complex.",
		Hypotheses: []string{
			"complex_has_integral(g, a, b, I)",
			"real_has_integral(λt:real. |g(t)|, a, b, J)",
		},
		Conclusion: "|I| ≤ J",
	},
		func(arg *Argument, g *Arrow[Real, Complex], a, b, J *Expr[Real], I *Expr[Complex], toI, toJ Fact) {
			arg.Show(
				"|g| dominates itself on ⟦a, b⟧",
				By(
					toI,
					toJ,
					real_order_ring.LessEqRefl,
					ComplexHasIntegralDominated.At(g, arg.TermAs[Fun[Real, Real]]("λt:real. |g(t)|"), a, b, J, I)))
		}),
})}

// ComplexHasIntegralBound — a complex function bounded by M on ⟦a, b⟧ has
// an integral of modulus at most M·(b − a): the constant M dominates |g|,
// and its integral over ⟦a, b⟧ is M·(b − a).
var ComplexHasIntegralBound = complexHasIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "ComplexHasIntegralBound",
	Key:  "prop_3629fbf1d0ca6a26",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → complex). ∀a b M:real. ∀I:complex.",
		Hypotheses: []string{
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ |g(t)| ≤ M",
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "|I| ≤ M * (b - a)",
	},
		func(
			arg *Argument,
			g *Arrow[Real, Complex],
			a, b, M *Expr[Real],
			I *Expr[Complex],
			bounded, toI Fact,
		) {
			arg.Show(
				"the constant M dominates |g| on ⟦a, b⟧ and has integral "+
					"M·(b − a) there, a ≤ b as g has an integral over ⟦a, b⟧",
				By(
					bounded,
					toI,
					arg.Unfolded(toI, ComplexHasIntegralDef),
					real_integral.HasIntegralOrdered,
					real_integral.HasIntegralConst.At(a, b, M),
					ComplexHasIntegralDominated.At(
						g,
						arg.TermAs[Fun[Real, Real]]("λt:real. M"),
						a,
						b,
						arg.TermAs[Real]("M * (b - a)"),
						I)))
		}),
})}

// ComplexNewtonLeibnizOffFinite — the Newton–Leibniz theorem for a path
// that may lack a velocity at finitely many points: when G is continuous
// on ⟦a, b⟧ with velocity g strictly inside off a finite set k, any
// integral g has over ⟦a, b⟧ is G(b) − G(a). Each part of G is continuous
// with the part of g as its derivative off k, so the real theorem, which
// allows the same finitely many exceptions, identifies each part of the
// integral as the increment of that part of G.
var ComplexNewtonLeibnizOffFinite = complexNewtonLeibnizOffFiniteThm{family.Add(registry.ProofEntry{
	Name: "ComplexNewtonLeibnizOffFinite",
	Key:  "prop_a3bc10b29b5cb2e3",
	Build: family.Theorem(Statement{
		Binders: "∀G g:(real → complex). ∀a b:real. ∀I:complex. ∀k:set(real).",
		Hypotheses: []string{
			"finite(k)",
			"real_continuous_on(⟦a, b⟧, λt:real. re(G(t)))",
			"real_continuous_on(⟦a, b⟧, λt:real. im(G(t)))",
			"∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ path_derivative_at(G, t, g(t))",
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "I = G(b) - G(a)",
	},
		func(
			arg *Argument,
			G, g *Arrow[Real, Complex],
			a, b *Expr[Real],
			I *Expr[Complex],
			k *Expr[Set[Real]],
			finite, reContinuous, imContinuous, velocity, toI Fact,
		) {
			parts := arg.Conjuncts(
				arg.Unfolded(toI, ComplexHasIntegralDef),
				"the real part of g has integral re(I)",
				"and its imaginary part im(I)")
			reDerivative := arg.Have(
				"inside ⟦a, b⟧ and off k the real part of G has the real part of g as its derivative",
				"∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ real_derivative_at(λs:real. re(G(s)), t, re(g(t)))",
				By(velocity, complex_derivative.PathDerivativeAtDef))
			imDerivative := arg.Have(
				"and the imaginary part of G the imaginary part of g",
				"∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ real_derivative_at(λs:real. im(G(s)), t, im(g(t)))",
				By(velocity, complex_derivative.PathDerivativeAtDef))
			reIncrement := arg.Have(
				"so re(I) is the increment of the real part of G",
				"re(I) = re(G(b)) - re(G(a))",
				By(
					finite,
					reContinuous,
					reDerivative,
					parts[0],
					real_integral.NewtonLeibnizOffFinite.At(
						arg.TermAs[Fun[Real, Real]]("λs:real. re(G(s))"),
						arg.TermAs[Fun[Real, Real]]("λt:real. re(g(t))"),
						a,
						b,
						arg.TermAs[Real]("re(I)"),
						k)))
			imIncrement := arg.Have(
				"and im(I) the increment of the imaginary part",
				"im(I) = im(G(b)) - im(G(a))",
				By(
					finite,
					imContinuous,
					imDerivative,
					parts[1],
					real_integral.NewtonLeibnizOffFinite.At(
						arg.TermAs[Fun[Real, Real]]("λs:real. im(G(s))"),
						arg.TermAs[Fun[Real, Real]]("λt:real. im(g(t))"),
						a,
						b,
						arg.TermAs[Real]("im(I)"),
						k)))
			arg.Show(
				"a complex number is its parts, and the parts of G(b) − G(a) are the increments",
				Simp(complex_field.Parts, Fwd(complex_field.PartsSub)),
				ByArith(reIncrement, imIncrement))
		}),
})}

// ComplexNewtonLeibniz — the Newton–Leibniz theorem for a path: when G is
// continuous on ⟦a, b⟧ with velocity g strictly inside, any integral g has
// over ⟦a, b⟧ is G(b) − G(a). It is the theorem off a finite set with no
// point set aside.
var ComplexNewtonLeibniz = complexNewtonLeibnizThm{family.Add(registry.ProofEntry{
	Name: "ComplexNewtonLeibniz",
	Key:  "prop_7d7e53401ec592f7",
	Build: family.Theorem(Statement{
		Binders: "∀G g:(real → complex). ∀a b:real. ∀I:complex.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, λt:real. re(G(t)))",
			"real_continuous_on(⟦a, b⟧, λt:real. im(G(t)))",
			"∀t:real. a < t ∧ t < b ⇒ path_derivative_at(G, t, g(t))",
			"complex_has_integral(g, a, b, I)",
		},
		Conclusion: "I = G(b) - G(a)",
	},
		func(
			arg *Argument,
			G, g *Arrow[Real, Complex],
			a, b *Expr[Real],
			I *Expr[Complex],
			reContinuous, imContinuous, velocity, toI Fact,
		) {
			arg.Show(
				"the theorem off a finite set, the finite set being empty",
				By(
					reContinuous,
					imContinuous,
					velocity,
					toI,
					finite_set.FiniteRules.Inst[Real](),
					ComplexNewtonLeibnizOffFinite.At(G, g, a, b, I, arg.TermAs[Set[Real]]("∅"))))
		}),
})}
