// exp.go — the exponential is its own derivative and the cosine and the
// sine are each other's up to sign; exp turns sums into products, its
// modulus is the real exponential of the real part, and a function whose
// derivative is itself times g′ is a multiple of exp(g).

package complex_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpDerivative — exp is its own derivative. exp(w) is the sum of the
// power series with coefficients 1/n! at every w, so term-by-term
// differentiation, inside the disc of radius |z| + 1, gives exp a
// derivative at z: the sum of the derived series. Its coefficients are
// (n + 1)·1/(n + 1)! = 1/n!, since (n + 1)! = (n + 1)·n!, so the derived
// series is the exponential series again, and its sum is exp(z).
var ExpDerivative = expDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ExpDerivative",
	Key:  "prop_261914d6b47fd6ba",
	Build: family.Theorem("∀z:complex. complex_derivative_at(exp, z, exp(z))",
		func(arg *Argument, z *Expr[Complex]) {
			coefficients := arg.TermAs[Fun[Nat, Complex]]("λn:num. complex_inv(complex_of_real(&factorial(n)))")
			exponential := arg.TermAs[Fun[Complex, Complex]]("exp")
			radius := arg.TermAs[Real]("|z| + &1")
			series := arg.Have(
				"at every w, exp(w) is the sum of the power series with coefficients 1/n!",
				"∀w:complex. complex_sums(λn:num. complex_inv(complex_of_real(&factorial(n))) * w ^ n, exp(w))",
				Derive(func(d *Argument) {
					w := d.FixAs[Complex]("w")
					terms := d.Have(
						"each term 1/n!·wⁿ is wⁿ/n!",
						"(λn:num. complex_inv(complex_of_real(&factorial(n))) * w ^ n) = "+
							"(λn:num. w ^ n / complex_of_real(&factorial(n)))",
						Funext(),
						Derive(func(e *Argument) {
							e.FixAs[Nat]()
							e.Show(
								"a quotient is a product with the inverse",
								ByArith())
						}))
					d.Show(
						"and the exponential series sums to exp(w)",
						By(terms, complex_exp.ExpSums.At(w)))
				}))
			inside := arg.Have(
				"z lies inside the disc of radius |z| + 1",
				"|z| < |z| + &1",
				ByArith())
			d, differentiated := arg.ObtainAs[Complex](
				"so term by term, exp has a derivative d at z, the sum of the derived series",
				"∃d:complex. "+
					"    complex_sums(λn:num. "+
					"            complex_of_real(&(n + 1)) * "+
					"            complex_inv(complex_of_real(&factorial(n + 1))) * "+
					"            z ^ n, "+
					"        d) ∧ "+
					"    complex_derivative_at(exp, z, d)",
				By(series, inside, PowerSeriesDerivative.At(coefficients, exponential, radius, z)))
			parts := arg.Conjuncts(
				differentiated,
				"the derived series sums to d",
				"d is the derivative of exp at z")
			derivedTerms := arg.Have(
				"the derived coefficients (n + 1)·1/(n + 1)! are 1/n!",
				"(λn:num. complex_of_real(&(n + 1)) * complex_inv(complex_of_real(&factorial(n + 1))) * z ^ n) = "+
					"(λn:num. z ^ n / complex_of_real(&factorial(n)))",
				Funext(),
				Derive(func(e *Argument) {
					e.FixAs[Nat]()
					e.Show(
						"(n + 1)! = (n + 1)·n!, and n + 1 cancels against its inverse",
						Simp(
							Rev(nat_arith.Add1),
							Fwd(nat_arith.Factorial),
							Fwd(real_construction.OfNumMul),
							Fwd(complex_field.OfRealMul),
							Fwd(field.InvMul.Read(complex_field.Field)),
							Fwd(complex_field.ComplexDivDef)),
						ByArith())
				}))
			same := arg.Have(
				"so the derived series is the exponential series, whose sum is exp(z): d = exp(z)",
				"d = exp(z)",
				By(
					derivedTerms,
					parts[0],
					complex_exp.ExpSums.At(z),
					complex_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. z ^ n / complex_of_real(&factorial(n))"),
						d,
						arg.TermAs[Complex]("exp(z)"))))
			arg.Show(
				"so exp(z) is the derivative of exp at z",
				By(Normalized, same, parts[1]))
		}),
})}

// ExpChainDerivative — where g has derivative d at s, z ↦ exp(g(z)) has
// derivative exp(g(s))·d there: the chain rule, exp being its own
// derivative.
var ExpChainDerivative = expChainDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ExpChainDerivative",
	Key:  "prop_eefb9b9fa970411e",
	Build: family.Theorem(Statement{
		Binders: "∀g:(complex → complex). ∀s d:complex.",
		Hypotheses: []string{
			"complex_derivative_at(g, s, d)",
		},
		Conclusion: "complex_derivative_at(λz:complex. exp(g(z)), s, exp(g(s)) * d)",
	},
		func(arg *Argument, g *Arrow[Complex, Complex], s, d *Expr[Complex], derivative Fact) {
			chained := arg.Have(
				"by the chain rule, exp after g has derivative exp(g(s))·d at s",
				"complex_derivative_at(complex_exp ∘ g, s, exp(g(s)) * d)",
				By(
					derivative,
					ExpDerivative.At(g.Apply(s)),
					complex_derivative.DerivativeChain.At(
						arg.TermAs[Fun[Complex, Complex]]("exp"),
						g,
						s,
						arg.TermAs[Complex]("exp(g(s))"),
						d)))
			arg.Show(
				"and exp after g is z ↦ exp(g(z))",
				By(arg.Simplified(chained, Fwd(functions.ComposeApply))))
		}),
})}

// ExpScaledDerivative — w ↦ exp(k·w) has derivative k·exp(k·c) at c: the
// chain rule after w ↦ k·w, whose derivative is k.
var ExpScaledDerivative = expScaledDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ExpScaledDerivative",
	Key:  "prop_9f25d9bbbc0dfd91",
	Build: family.Theorem("∀k c:complex. "+
		"    complex_derivative_at(λw:complex. exp(k * w), c, k * exp(k * c))",
		func(arg *Argument, k, c *Expr[Complex]) {
			value := arg.Have(
				"exp(k·c)·(k·1) is k·exp(k·c)",
				"exp(k * c) * (k * &1) = k * exp(k * c)",
				ByArith())
			arg.Show(
				"w ↦ k·w has derivative k·1 at c, so by the chain rule w ↦ "+
					"exp(k·w) has derivative exp(k·c)·(k·1) = k·exp(k·c) there",
				By(
					complex_derivative.DerivativeId.At(c),
					complex_derivative.DerivativeScale.At(
						arg.TermAs[Fun[Complex, Complex]]("λw:complex. w"),
						c,
						arg.TermAs[Complex]("&1"),
						k),
					value,
					ExpChainDerivative.At(
						arg.TermAs[Fun[Complex, Complex]]("λw:complex. k * w"), c, arg.TermAs[Complex]("k * &1"))))
		}),
})}

// SinDerivative — the derivative of the sine is the cosine. The sine is
// (exp(i·w) − exp(−(i·w)))/(2i), whose derivative at z is
// (i·exp(i·z) + i·exp(−(i·z)))/(2i) = (exp(i·z) + exp(−(i·z)))/2, the
// cosine.
var SinDerivative = sinDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SinDerivative",
	Key:  "prop_47043deddbebc17c",
	Build: family.Theorem("∀z:complex. complex_derivative_at(sin, z, cos(z))",
		func(arg *Argument, z *Expr[Complex]) {
			up := arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(complex_i * w)")
			down := arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(-(complex_i * w))")
			difference := arg.Have(
				"w ↦ exp(i·w) − exp(−(i·w)) has derivative i·exp(i·z) − (−i·exp(−(i·z))) at z",
				"complex_derivative_at(λw:complex. exp(complex_i * w) - exp(-(complex_i * w)), "+
					"    z, "+
					"    complex_i * exp(complex_i * z) - -(complex_i * exp(-(complex_i * z))))",
				By(
					ExpScaledDerivative.At(arg.TermAs[Complex]("complex_i"), z),
					// the derivative at −i, its −i·w read as −(i·w), the sine's own spelling
					arg.Simplified(
						ExpScaledDerivative.At(arg.TermAs[Complex]("-complex_i"), z),
						Fwd(comm_ring.MulLeftNeg.Read(complex_field.CommRing))),
					complex_derivative.DerivativeSub.At(
						up,
						down,
						z,
						arg.TermAs[Complex]("complex_i * exp(complex_i * z)"),
						arg.TermAs[Complex]("-(complex_i * exp(-(complex_i * z)))"))))
			scaled := arg.Have(
				"and its multiple by 1/(2i) has the multiple of that derivative",
				"complex_derivative_at(λw:complex. "+
					"        complex_inv(complex_of_real(&2) * complex_i) * "+
					"        (exp(complex_i * w) - exp(-(complex_i * w))), "+
					"    z, "+
					"    complex_inv(complex_of_real(&2) * complex_i) * "+
					"    (complex_i * exp(complex_i * z) - -(complex_i * exp(-(complex_i * z)))))",
				By(
					difference,
					complex_derivative.DerivativeScale.At(
						arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(complex_i * w) - exp(-(complex_i * w))"),
						z,
						arg.TermAs[Complex]("complex_i * exp(complex_i * z) - -(complex_i * exp(-(complex_i * z)))"),
						arg.TermAs[Complex]("complex_inv(complex_of_real(&2) * complex_i)"))))
			sine := arg.Have(
				"that multiple is the sine",
				"sin = "+
					"(λw:complex. "+
					"    complex_inv(complex_of_real(&2) * complex_i) * (exp(complex_i * w) - exp(-(complex_i * w))))",
				Funext(),
				arg.ForEach(func(w *Expr[Complex]) Action { return ByArith(complex_exp.SinExp.At(w)) }))
			value := arg.Have(
				"the derivative is i·(exp(i·z) + exp(−(i·z)))/(2i) = (exp(i·z) "+
					"+ exp(−(i·z)))/2, the cosine, as 1/i = −i and i² = −1",
				"complex_inv(complex_of_real(&2) * complex_i) * "+
					"(complex_i * exp(complex_i * z) - -(complex_i * exp(-(complex_i * z)))) = "+
					"cos(z)",
				Simp(
					Fwd(complex_exp.CosExp),
					Fwd(complex_field.ComplexDivDef),
					Fwd(field.InvMul.Read(complex_field.Field)),
					Fwd(complex_field.InvI)),
				ByArith(Scaled(
					arg.TermAs[Complex](
						"complex_inv(complex_of_real(&2)) * (exp(complex_i * z) + exp(-(complex_i * z)))"),
					complex_field.ISquared)))
			arg.Show(
				"so the sine has derivative cos(z) at z",
				By(sine, value, scaled))
		}),
})}

// CosDerivative — the derivative of the cosine is minus the sine. The
// cosine is (exp(i·w) + exp(−(i·w)))/2, whose derivative at z is
// (i·exp(i·z) − i·exp(−(i·z)))/2 = −(exp(i·z) − exp(−(i·z)))/(2i), as
// 1/i = −i: minus the sine.
var CosDerivative = cosDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CosDerivative",
	Key:  "prop_50ae58c44d1ce748",
	Build: family.Theorem("∀z:complex. complex_derivative_at(cos, z, -sin(z))",
		func(arg *Argument, z *Expr[Complex]) {
			up := arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(complex_i * w)")
			down := arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(-(complex_i * w))")
			sum := arg.Have(
				"w ↦ exp(i·w) + exp(−(i·w)) has derivative i·exp(i·z) + (−i·exp(−(i·z))) at z",
				"complex_derivative_at(λw:complex. exp(complex_i * w) + exp(-(complex_i * w)), "+
					"    z, "+
					"    complex_i * exp(complex_i * z) + -(complex_i * exp(-(complex_i * z))))",
				By(
					ExpScaledDerivative.At(arg.TermAs[Complex]("complex_i"), z),
					// the derivative at −i, its −i·w read as −(i·w), the cosine's own spelling
					arg.Simplified(
						ExpScaledDerivative.At(arg.TermAs[Complex]("-complex_i"), z),
						Fwd(comm_ring.MulLeftNeg.Read(complex_field.CommRing))),
					complex_derivative.DerivativeAdd.At(
						up,
						down,
						z,
						arg.TermAs[Complex]("complex_i * exp(complex_i * z)"),
						arg.TermAs[Complex]("-(complex_i * exp(-(complex_i * z)))"))))
			scaled := arg.Have(
				"and half of it has half that derivative",
				"complex_derivative_at(λw:complex. "+
					"        complex_inv(complex_of_real(&2)) * (exp(complex_i * w) + exp(-(complex_i * w))), "+
					"    z, "+
					"    complex_inv(complex_of_real(&2)) * "+
					"    (complex_i * exp(complex_i * z) + -(complex_i * exp(-(complex_i * z)))))",
				By(
					sum,
					complex_derivative.DerivativeScale.At(
						arg.TermAs[Fun[Complex, Complex]]("λw:complex. exp(complex_i * w) + exp(-(complex_i * w))"),
						z,
						arg.TermAs[Complex]("complex_i * exp(complex_i * z) + -(complex_i * exp(-(complex_i * z)))"),
						arg.TermAs[Complex]("complex_inv(complex_of_real(&2))"))))
			cosine := arg.Have(
				"half of it is the cosine",
				"cos = "+
					"(λw:complex. complex_inv(complex_of_real(&2)) * (exp(complex_i * w) + exp(-(complex_i * w))))",
				Funext(),
				arg.ForEach(func(w *Expr[Complex]) Action { return ByArith(complex_exp.CosExp.At(w)) }))
			value := arg.Have(
				"the derivative is i·(exp(i·z) − exp(−(i·z)))/2 = "+
					"−(exp(i·z) − exp(−(i·z)))/(2i), minus the sine, as 1/i = −i",
				"complex_inv(complex_of_real(&2)) * "+
					"(complex_i * exp(complex_i * z) + -(complex_i * exp(-(complex_i * z)))) = "+
					"-sin(z)",
				Simp(
					Fwd(complex_exp.SinExp),
					Fwd(complex_field.ComplexDivDef),
					Fwd(field.InvMul.Read(complex_field.Field)),
					Fwd(complex_field.InvI)),
				ByArith())
			arg.Show(
				"so the cosine has derivative −sin(z) at z",
				By(cosine, value, scaled))
		}),
})}

// ExpAdd — exp turns sums into products. With the sum z + w fixed,
// h(v) = exp(v)·exp(z + w − v) has derivative
// exp(u)·exp(z + w − u) + exp(u)·(exp(z + w − u)·(0 − 1)) = 0 at every u:
// the product rule, with v ↦ exp(z + w − v) differentiated by the chain
// rule through v ↦ z + w − v, whose derivative is 0 − 1. The plane is
// convex, and a function with derivative 0 on a convex set takes one value
// on it, so h takes at z its value at 0: exp(z)·exp(w) = exp(0)·exp(z + w),
// and exp(0) = 1.
var ExpAdd = expAddThm{family.Add(registry.ProofEntry{
	Name: "ExpAdd",
	Key:  "prop_b2f99f0ff882f42",
	Build: family.Theorem(Statement{
		Binders:    "∀z w:complex.",
		Conclusion: "exp(z + w) = exp(z) * exp(w)",
		Abbrev: Abbrev{
			{Name: "h", Text: "(λv:complex. exp(v) * exp(z + w - v))"},
			{Name: "minusOne", Text: "(complex_of_real(&0) - complex_of_real(&1))"},
		},
	},
		func(arg *Argument, z, w *Expr[Complex]) {
			flat := arg.Have(
				"h has derivative 0 at every point",
				"∀u:complex. complex_derivative_at(«h», u, &0)",
				Derive(func(b *Argument) {
					u := b.FixAs[Complex]("u")
					minusOne := b.TermAs[Complex]("«minusOne»")
					reflection := b.Have(
						"v ↦ z + w − v, a constant less the identity, has derivative 0 − 1 at u",
						"complex_derivative_at(λv:complex. z + w - v, u, «minusOne»)",
						By(
							complex_derivative.DerivativeConst.At(u, b.TermAs[Complex]("z + w")),
							complex_derivative.DerivativeId.At(u),
							complex_derivative.DerivativeSub.At(
								b.TermAs[Fun[Complex, Complex]]("λv:complex. z + w"),
								b.TermAs[Fun[Complex, Complex]]("λv:complex. v"),
								u,
								b.TermAs[Complex]("complex_of_real(&0)"),
								b.TermAs[Complex]("complex_of_real(&1)"))))
					product := b.Have(
						"so by the product rule and the chain rule, h has derivative "+
							"exp(u)·exp(z + w − u) + exp(u)·(exp(z + w − u)·(0 − 1)) at u",
						"complex_derivative_at(«h», u, exp(u) * exp(z + w - u) + exp(u) * (exp(z + w - u) * «minusOne»))",
						By(
							ExpDerivative.At(u),
							reflection,
							ExpChainDerivative.At(b.TermAs[Fun[Complex, Complex]]("λv:complex. z + w - v"), u, minusOne),
							complex_derivative.DerivativeMul.At(
								b.TermAs[Fun[Complex, Complex]]("exp"),
								b.TermAs[Fun[Complex, Complex]]("λv:complex. exp(z + w - v)"),
								u,
								b.TermAs[Complex]("exp(u)"),
								b.TermAs[Complex]("exp(z + w - u) * «minusOne»"))))
					cancel := b.Have(
						"the two terms cancel",
						"exp(u) * exp(z + w - u) + exp(u) * (exp(z + w - u) * «minusOne») = &0",
						ByArith())
					b.Show(
						"so h has derivative 0 at u",
						By(cancel, product))
				}))
			constant := arg.Have(
				"with derivative 0 on the plane, which is convex, h takes one value, so h(z) = h(0)",
				"«h»(z) = «h»(complex_of_real(&0))",
				By(
					flat,
					set_basic.InUniv,
					complex_derivative.DerivativeZeroConstantOnConvex.At(
						arg.TermAs[Fun[Complex, Complex]]("«h»"),
						arg.TermAs[Set[Complex]]("𝕌"),
						z,
						arg.TermAs[Complex]("&0"))))
			ends := arg.Have(
				"z + w − z is w, and z + w − 0 is z + w",
				"z + w - z = w ∧ z + w - &0 = z + w",
				ByArith())
			arg.Show(
				"so exp(z)·exp(w) = exp(0)·exp(z + w), and exp(0) = 1",
				ByArith(constant, ends, complex_exp.ExpZero))
		}),
})}

// ExpNonzero — exp never vanishes: exp(z)·exp(−z) = exp(z + (−z)) = exp(0)
// = 1, while 0 times anything is 0, which is not 1.
var ExpNonzero = expNonzeroThm{family.Add(registry.ProofEntry{
	Name: "ExpNonzero",
	Key:  "prop_675b237b708af5fe",
	Build: family.Theorem("∀z:complex. exp(z) ≠ &0",
		func(arg *Argument, z *Expr[Complex]) {
			opposite := arg.TermAs[Complex]("-z")
			cancel := arg.Have(
				"z + (−z) is 0",
				"z + -z = &0",
				ByArith())
			inverse := arg.Have(
				"exp(z)·exp(−z) = exp(z + (−z)) = exp(0) = 1",
				"exp(z) * exp(-z) = &1",
				By(cancel, ExpAdd.At(z, opposite), complex_exp.ExpZero))
			arg.Show(
				"were exp(z) zero, exp(z)·exp(−z) would be 0·exp(−z) = 0, and 0 is not 1",
				By(
					inverse,
					comm_ring.MulLeftZero.Read(complex_field.CommRing).At(arg.TermAs[Complex]("exp(-z)")),
					field.OneNotZero.Read(complex_field.Field)))
		}),
})}

// AbsExp — the modulus of exp(z) is the real exponential of the real part
// of z. Written z = re z + i·im z, exp(z) is exp(re z)·exp(i·im z), the
// real exponential of re z read in ℂ times a point of the unit circle, so
// its modulus is exp(re z)·1, the real exponential being positive.
var AbsExp = absExpThm{family.Add(registry.ProofEntry{
	Name: "AbsExp",
	Key:  "prop_6f1ba6585f288ad0",
	Build: family.Theorem("∀z:complex. |exp(z)| = exp(re(z))",
		func(arg *Argument, z *Expr[Complex]) {
			x, y := arg.TermAs[Real]("re(z)"), arg.TermAs[Real]("im(z)")
			decomposed := arg.Have(
				"z is its real part plus i times its imaginary part",
				"z = &(re(z)) + complex_i * &(im(z))",
				Simp(
					complex_field.Parts,
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexIDef)),
				ByArith())
			polar := arg.Have(
				"so exp(z) = exp(re z)·exp(i·im z), the real exponential of re z times a point of the unit circle",
				"exp(z) = &(exp(re(z))) * exp(complex_i * &(im(z)))",
				By(
					Normalized,
					decomposed,
					ExpAdd.At(arg.TermAs[Complex]("&(re(z))"), arg.TermAs[Complex]("complex_i * &(im(z))")),
					complex_exp.ExpOfReal.At(x)))
			arg.Show(
				"|exp(z)| = |exp(re z)|·|exp(i·im z)| = exp(re z)·1, the real exponential being positive",
				ByArith(
					polar,
					complex_abs.AbsMul.At(
						arg.TermAs[Complex]("&(exp(re(z)))"), arg.TermAs[Complex]("exp(complex_i * &(im(z)))")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("exp(re(z))")),
					complex_exp.AbsExpIOfReal.At(y),
					real_exp_log.ExpPositive.At(x)))
		}),
})}

// ExponentialOfPrimitive — on a right half-plane, a holomorphic f with
// f′ = f·g′ is a constant multiple of exp(g). The quotient h = f/exp(g) has
// derivative (f′·exp(g) − f·exp(g)·g′)/exp(g)² = 0 at every point of the
// half-plane c < re, by the quotient rule and the chain rule, exp never
// vanishing. The half-plane is convex, re being affine along a segment, so
// h takes one value on it: h(s) = h(c + 1), and f(s) is h(c + 1)·exp(g(s)).
var ExponentialOfPrimitive = exponentialOfPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "ExponentialOfPrimitive",
	Key:  "prop_8fc877a6dece51fc",
	Build: family.Theorem(Statement{
		Binders: "∀f g f' g':(complex → complex). ∀c:real.",
		Hypotheses: []string{
			"∀s:complex. c < re(s) ⇒ complex_derivative_at(f, s, f'(s))",
			"∀s:complex. c < re(s) ⇒ complex_derivative_at(g, s, g'(s))",
			"∀s:complex. c < re(s) ⇒ f'(s) = f(s) * g'(s)",
		},
		Conclusion: "∃C:complex. ∀s:complex. c < re(s) ⇒ f(s) = C * exp(g(s))",
		Abbrev: Abbrev{
			{Name: "h", Text: "(λz:complex. f(z) / exp(g(z)))"},
		},
	},
		func(
			arg *Argument,
			f, g, fPrime, gPrime *Arrow[Complex, Complex],
			c *Expr[Real],
			fDerivative, gDerivative, equation Fact,
		) {
			flat := arg.Have(
				"h = f/exp(g) has derivative 0 at every point of the half-plane",
				"∀s:complex. c < re(s) ⇒ complex_derivative_at(«h», s, &0)",
				Derive(func(b *Argument) {
					s := b.FixAs[Complex]("s")
					inside := b.Assume()
					differentiated := b.Have(
						"by the quotient rule and the chain rule, exp(g(s)) not being 0, h has "+
							"derivative (f′(s)·exp(g(s)) − f(s)·(exp(g(s))·g′(s)))/exp(g(s))² at s",
						"complex_derivative_at(«h», s, (f'(s) * exp(g(s)) - f(s) * (exp(g(s)) * g'(s))) / exp(g(s)) ^ 2)",
						By(
							fDerivative.At(s),
							gDerivative.At(s),
							inside,
							ExpChainDerivative.At(g, s, gPrime.Apply(s)),
							ExpNonzero.At(g.Apply(s)),
							complex_derivative.DerivativeDiv.At(
								f,
								b.TermAs[Fun[Complex, Complex]]("λz:complex. exp(g(z))"),
								s,
								fPrime.Apply(s),
								b.TermAs[Complex]("exp(g(s)) * g'(s)"))))
					vanishing := b.Have(
						"and as f′(s) = f(s)·g′(s) its numerator is 0",
						"(f'(s) * exp(g(s)) - f(s) * (exp(g(s)) * g'(s))) / exp(g(s)) ^ 2 = &0",
						ByArith(equation.At(s), inside))
					b.Show(
						"so h has derivative 0 at s",
						By(vanishing, differentiated))
				}))
			convex := arg.Have(
				"the half-plane is convex",
				"∀u v:complex. ∀t:real. c < re(u) ∧ c < re(v) ∧ &0 ≤ t ∧ t ≤ &1 ⇒ c < re(u + &t * (v - u))",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("u")
					b.FixAs[Complex]("v")
					t := b.FixAs[Real]("t")
					within := b.Assume()
					partU, partV := b.TermAs[Real]("re(u)"), b.TermAs[Real]("re(v)")
					b.Show(
						"re is affine along the segment: at t it is re(u) + t·(re(v) − "+
							"re(u)), at least the smaller of re(u) and re(v), both above c",
						Simp(
							Fwd(complex_field.PartsAdd),
							Fwd(complex_field.PartsMul),
							Fwd(complex_field.PartsSub),
							Fwd(complex_field.PartsOfReal)),
						ByArith(
							within,
							real_order_ring.LessEqMulLeft.At(t, partU, partV),
							real_order_ring.LessEqMulLeft.At(b.TermAs[Real]("&1 - t"), partV, partU)))
				}))
			base := arg.Have(
				"c + 1 lies in the half-plane",
				"c < re(&(c + &1))",
				ByArith(complex_field.PartsOfReal.At(arg.TermAs[Real]("c + &1"))))
			constant := arg.Have(
				"so at every point of the half-plane h takes its value at c + 1",
				"∀s:complex. c < re(s) ⇒ «h»(s) = «h»(&(c + &1))",
				Derive(func(b *Argument) {
					s := b.FixAs[Complex]("s")
					inside := b.Assume()
					b.Show(
						"h has derivative 0 on the half-plane, which is convex and holds s and c + 1, so h(s) = h(c + 1)",
						By(
							flat,
							convex,
							inside,
							base,
							complex_derivative.DerivativeZeroConstantOnConvex.At(
								b.TermAs[Fun[Complex, Complex]]("«h»"),
								b.TermAs[Set[Complex]]("{u:complex | c < re(u)}"),
								s,
								b.TermAs[Complex]("&(c + &1)"))))
				}))
			arg.Take(arg.TermAs[Complex]("«h»(&(c + &1))"))
			s := arg.FixAs[Complex]("s")
			inside := arg.Assume()
			arg.Show(
				"so C = h(c + 1) serves: f(s) = h(s)·exp(g(s)), exp(g(s)) not being 0",
				ByArith(constant.At(s), inside, ExpNonzero.At(g.Apply(s))))
		}),
	Reading: "The set must be connected for one constant to serve: a half-plane is, " +
		"being convex. The Dirichlet-series chapter reads it at f = D(a, ·) and g the " +
		"series of the logarithm, where the equation f′ = f·g′ is a convolution identity.",
})}
