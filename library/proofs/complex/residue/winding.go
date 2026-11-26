// winding.go — the winding index and the inverse powers of z − p round a
// path: the integral of 1/(z − p) as 2πi times the index (WindingIntegral);
// the index of a circle about a point inside and outside it
// (WindingCircleInside, WindingCircleOutside), of a closed path in a convex
// open set about a point outside the set (WindingOutsideConvex), and an
// index-weighted count round a circle (WindingCircleCount); a circle as a
// closed path in a set holding it (CircleClosedPathIn); the derivative
// and the holomorphy of the inverse powers (InversePowerDerivative,
// InversePowerHolomorphic); and the integrals round a closed path of
// 1/(z − p)ᵏ⁺² and of a principal part (InversePowerIntegralZero,
// PrincipalPartIntegral).

package residue

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// WindingIntegral — the integral of 1/(z − p) along a path is 2πi times the
// winding index of the path about p: the index is that integral over 2πi,
// and 2πi is not 0.
var WindingIntegral = windingIntegralThm{family.Add(registry.ProofEntry{
	Name: "WindingIntegral",
	Key:  "prop_a7968a0c098bb28",
	Build: family.Theorem(
		"∀γ γ':(real → complex). ∀a b:real. ∀p:complex. "+
			"    path_integral(λz:complex. complex_inv(z - p), γ, γ', a, b) = "+
			"    &(&2 * pi) * complex_i * winding_index(γ, γ', a, b, p)",
		func(arg *Argument, γ, γPrime *Arrow[Real, Complex], a, b *Expr[Real], p *Expr[Complex]) {
			arg.Show(
				"2πi times the integral over 2πi is the integral, 2πi being nonzero",
				ByArith(
					path_integral.TwoPiINonzero,
					Scaled(
						arg.TermAs[Complex]("&(&2 * pi) * complex_i"),
						WindingIndexDef.At(γ, γPrime, a, b, p))))
		}),
})}

// WindingCircleInside — once round a circle, the winding index about a
// point inside it is 1: the integral of 1/(z − w) round the circle is 2πi
// for every w inside, and the index is that integral over 2πi.
var WindingCircleInside = windingCircleInsideThm{family.Add(registry.ProofEntry{
	Name: "WindingCircleInside",
	Key:  "prop_1cf2ba804dd79193",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real.",
		Hypotheses: []string{
			"|w - c| < r",
		},
		Conclusion: "«circleIndex»(c, r, w) = &1",
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], inside Fact) {
			a.Show(
				"the integral round the circle is 2πi, and the index is that integral over 2πi, which is not 0",
				ByArith(
					inside,
					WindingIndexDef.At(
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"),
						w),
					cauchy_integral.CircleWindingInside.At(c, w, r),
					path_integral.TwoPiINonzero))
		}),
})}

// WindingCircleOutside — once round a circle, the winding index about a
// point outside it is 0: the circle is a closed path in the disc about c of
// radius |w − c|, which is open and convex and misses w
// (WindingOutsideConvex).
var WindingCircleOutside = windingCircleOutsideThm{family.Add(registry.ProofEntry{
	Name: "WindingCircleOutside",
	Key:  "prop_89fdca0994dbad7f",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real.",
		Hypotheses: []string{
			"|r| < |w - c|",
		},
		Conclusion: "«circleIndex»(c, r, w) = &0",
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], outside Fact) {
			radius := a.TermAs[Real]("|w - c|")
			inside := a.Have(
				"the circle stays at distance |r| < |w − c| from c, inside the disc about c of radius |w − c|",
				"∀t:real. circle_path(c, r, t) ∈ «disc»(c, |w - c|)",
				a.ForEach(func(t *Expr[Real]) Action {
					return ByArith(outside, path_integral.CirclePathRadius.At(c, r, t))
				}))
			a.Show(
				"that disc is open and convex and misses w, and the circle is a closed piecewise smooth path in it",
				By(
					inside,
					complex_topology.DiscOpen.At(c, radius),
					At(cauchy_integral.DiscConvex, c, radius),
					path_integral.CirclePiecewiseSmooth.At(c, r),
					path_integral.CirclePathClosed.At(c, r),
					real_order_ring.LessThanIrrefl.At(radius),
					WindingOutsideConvex.At(
						a.TermAs[Set[Complex]]("«disc»(c, |w - c|)"),
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"),
						w)))
		}),
})}

// WindingOutsideConvex — a closed piecewise smooth path in a convex open set
// does not wind about a point outside the set. 1/(z − w) is holomorphic on the
// set, which misses w, so by Cauchy's theorem it integrates to 0 round the
// path, and the index is that integral over 2πi.
var WindingOutsideConvex = windingOutsideConvexThm{family.Add(registry.ProofEntry{
	Name: "WindingOutsideConvex",
	Key:  "prop_288481a92afbf40a",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). ∀γ γ':(real → complex). ∀a b:real. ∀w:complex.",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"«convex»(S)",
			"«closedPathIn»(S, γ, γ', a, b)",
			"w ∉ S",
		},
		Conclusion: "winding_index(γ, γ', a, b, w) = &0",
	},
		func(
			arg *Argument,
			S *Expr[Set[Complex]],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			w *Expr[Complex],
			open, convex, path, outside Fact,
		) {
			reciprocal := arg.Simplified(
				GroupPremises(outside, InversePowerHolomorphic.At(S, w, arg.TermAs[Nat]("1"))),
				Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)))
			vanishes := arg.Have(
				"so by Cauchy's theorem 1/(z − w) integrates to 0 round the path",
				"path_integral(λz:complex. complex_inv(z - w), γ, γ', a, b) = &0",
				By(
					open,
					convex,
					reciprocal,
					path,
					cauchy_integral.CauchyConvex.At(
						S,
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(z - w)"),
						γ,
						γPrime,
						a,
						b)))
			arg.Show(
				"so the index, 0 over 2πi, is 0",
				ByArith(vanishes, WindingIndexDef.At(γ, γPrime, a, b, w)))
		}),
})}

// WindingCircleCount — the circle of radius r ≥ 0 about c winds once about
// each point inside it and not at all about a point outside, so over a
// finite set of points off the circle, a sum of whole numbers weighted by the
// winding index is the plain sum over the points inside.
var WindingCircleCount = windingCircleCountThm{family.Add(registry.ProofEntry{
	Name: "WindingCircleCount",
	Key:  "prop_52d900948620030d",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex. ∀r:real. ∀Z:set(complex). ∀k:(complex → num).",
		Hypotheses: []string{
			"&0 ≤ r",
			"finite(Z)",
			"∀z:complex. z ∈ Z ⇒ |z - c| ≠ r",
		},
		Conclusion: "Σ_{z∈Z} «circleIndex»(c, r, z) * &(&(k(z))) = &(&(Σ_{z∈Z ∩ «disc»(c, r)} k(z)))",
	},
		func(
			a *Argument,
			c *Expr[Complex],
			r *Expr[Real],
			Z *Expr[Set[Complex]],
			k *Arrow[Complex, Nat],
			nonneg, finite, offCircle Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			disc := a.TermAs[Set[Complex]]("«disc»(c, r)")
			inside := a.TermAs[Set[Complex]]("Z ∩ «disc»(c, r)")
			outside := a.Have(
				"about a point of Z outside the circle the index is 0, so it adds nothing",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ Z",
						"z ∉ Z ∩ «disc»(c, r)",
					},
					Conclusion: "«circleIndex»(c, r, z) * &(&(k(z))) = neutral_elem(complex_add)",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					given := d.Assume()
					member := d.Conjuncts(
						given,
						"z is in Z",
						"but not within r of c")
					notInside := d.Have(
						"z is not within r of c",
						"¬(|z - c| < r)",
						BySets(member[1], member[0]))
					far := d.Have(
						"so z is farther than |r| from c, lying off the circle",
						"|r| < |z - c|",
						ByArith(nonneg, notInside, offCircle.At(z), member[0]))
					d.Show(
						"the circle not winding about z",
						ByArith(far, WindingCircleOutside.At(c, z, r), comm_ring.NeutralAdd.Read(complex_field.CommRing)))
				}))
			widened := a.Have(
				"so the sum over Z is the sum over the points inside",
				"Σ_{z∈Z ∩ «disc»(c, r)} «circleIndex»(c, r, z) * &(&(k(z))) = "+
					"Σ_{z∈Z} «circleIndex»(c, r, z) * &(&(k(z)))",
				By(
					outside,
					set_order.InterSubset.At(Z, disc),
					monoidal.Superset.At(
						a.TermAs[Op[Complex]]("complex_add"),
						inside,
						Z,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. «circleIndex»(c, r, z) * &(&(k(z)))"))))
			insideTerms := a.Have(
				"about a point inside, the index is 1",
				"∀z:complex. z ∈ Z ∩ «disc»(c, r) ⇒ «circleIndex»(c, r, z) * &(&k(z)) = &(&k(z))",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					given := d.Assume()
					within := d.Have(
						"z is within r of c",
						"|z - c| < r",
						BySets(given))
					d.Show(
						"the circle winding once about z",
						ByArith(within, WindingCircleInside.At(c, z, r)))
				}))
			ones := a.Have(
				"so over the points inside the index drops out",
				"Σ_{z∈Z ∩ «disc»(c, r)} «circleIndex»(c, r, z) * &(&(k(z))) = Σ_{z∈Z ∩ «disc»(c, r)} &(&(k(z)))",
				By(insideTerms, addition, monoidal.Congruence))
			insideFinite := a.Have(
				"finitely many points lie inside",
				"finite(Z ∩ «disc»(c, r))",
				By(finite, finite_set.FiniteInter.At(Z, disc)))
			keepsZero := a.Have(
				"the cast of ℕ into ℂ keeps 0",
				"&(&(neutral_elem(λi:num. λj:num. i + j))) = neutral_elem(complex_add)",
				ByArith(nat_sum.NeutralNatAdd, comm_ring.NeutralAdd.Read(complex_field.CommRing)))
			keepsAddition := a.Have(
				"and carries addition to addition",
				"∀m n:num. &(&(m + n)) = &(&m) + &(&n)",
				By(Normalized, complex_field.OfRealAdd, real_construction.OfNumAdd))
			cast := a.Have(
				"so it carries the sum of k to the sum of its casts",
				"&(&(Σ_{z∈Z ∩ «disc»(c, r)} k(z))) = Σ_{z∈Z ∩ «disc»(c, r)} &(&(k(z)))",
				Unfold(nat_sum.NatSumDef),
				By(
					insideFinite,
					keepsZero,
					keepsAddition,
					nat_sum.MonoidalNatAdd,
					addition,
					Where(monoidal.Homomorphic, "h", a.TermAs[Fun[Nat, Complex]]("λn:num. &(&n)"))))
			a.Show(
				"so the weighted sum is the sum of k over the points inside",
				ByArith(widened, ones, cast))
		}),
})}

// CircleClosedPathIn — the circle of radius r ≥ 0 about c, run once round,
// is a closed piecewise smooth path in any set holding the points at
// distance r from c: each of its points lies at that distance.
var CircleClosedPathIn = circleClosedPathInThm{family.Add(registry.ProofEntry{
	Name: "CircleClosedPathIn",
	Key:  "prop_4d66df8d3eb6a13c",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex. ∀r:real. ∀X:set(complex).",
		Hypotheses: []string{
			"&0 ≤ r",
			"∀z:complex. |z - c| = r ⇒ z ∈ X",
		},
		Conclusion: "«closedPathIn»(X, " +
			"    circle_path(c, r), " +
			"    λt:real. complex_i * &r * exp(complex_i * &t), " +
			"    &0, " +
			"    &2 * pi)",
	},
		func(a *Argument, c *Expr[Complex], r *Expr[Real], X *Expr[Set[Complex]], nonneg, onCircle Fact) {
			along := a.Have(
				"each point of the circle lies at distance r from c, so in X",
				"∀t:real. &0 ≤ t ∧ t ≤ &2 * pi ⇒ circle_path(c, r, t) ∈ X",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					d.Assume()
					point := d.TermAs[Complex]("circle_path(c, r, t)")
					radius := d.Have(
						"circle_path(c, r, t) lies at distance |r| = r from c",
						"|circle_path(c, r, t) - c| = r",
						ByArith(nonneg, path_integral.CirclePathRadius.At(c, r, t)))
					d.Show(
						"so it lies in X",
						By(radius, onCircle.At(point)))
				}))
			a.Show(
				"the circle is piecewise smooth and closed",
				By(along, path_integral.CirclePiecewiseSmooth.At(c, r), path_integral.CirclePathClosed.At(c, r)))
		}),
})}

// InversePowerDerivative — off p, 1/(z − p)ⁿ⁺¹ has derivative
// −(n + 1)/(z − p)ⁿ⁺². By the chain rule through the power rule,
// (z − p)ⁿ⁺¹ has derivative (n + 1)(z − p)ⁿ, and it is not 0, so the
// reciprocal rule applies; (n + 1)(z − p)ⁿ over ((z − p)ⁿ⁺¹)² is
// (n + 1)/(z − p)ⁿ⁺², since no power of z − p is 0.
var InversePowerDerivative = inversePowerDerivativeThm{family.Add(registry.ProofEntry{
	Name: "InversePowerDerivative",
	Key:  "prop_e220516d3d74fd0",
	Build: family.Theorem(Statement{
		Binders: "∀p z:complex. ∀n:num.",
		Hypotheses: []string{
			"z ≠ p",
		},
		Conclusion: "complex_derivative_at(λu:complex. complex_inv((u - p) ^ (n + 1)), " +
			"    z, " +
			"    -(complex_of_real(&(n + 1)) * complex_inv((z - p) ^ (n + 2))))",
	},
		func(a *Argument, p, z *Expr[Complex], n *Expr[Nat], off Fact) {
			difference := a.TermAs[Complex]("z - p")
			shift := a.TermAs[Fun[Complex, Complex]]("λu:complex. u - p")
			slope := a.TermAs[Complex]("&(&(n + 1)) * (z - p) ^ n")
			apart := a.Have(
				"z − p is not 0",
				"z - p ≠ &0",
				ByArith(off))
			powers := a.Have(
				"so no power of z − p is 0",
				"∀k:num. (z - p) ^ k ≠ &0",
				a.ForEach(func(k *Expr[Nat]) Action {
					return ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(difference, k))
				}))
			unit := a.Have(
				"1 − 0 is 1",
				"&(&1) - &(&0) = &(&1)",
				ByArith())
			shifted := a.Have(
				"so u − p has derivative 1 − 0 = 1 at z",
				"complex_derivative_at(λu:complex. u - p, z, &1)",
				By(
					unit,
					complex_derivative.DerivativeId.At(z),
					complex_derivative.DerivativeConst.At(z, p),
					complex_derivative.DerivativeSub.At(
						a.TermAs[Fun[Complex, Complex]]("λu:complex. u"),
						a.TermAs[Fun[Complex, Complex]]("λu:complex. p"),
						z,
						a.TermAs[Complex]("&1"),
						a.TermAs[Complex]("&0"))))
			power := a.Unfolded(
				a.Have(
					"so (u − p)ⁿ⁺¹ has derivative (n + 1)(z − p)ⁿ, by the chain rule through the power rule at z − p",
					"complex_derivative_at((λy:complex. y ^ (n + 1)) ∘ (λu:complex. u - p), "+
						"    z, "+
						"    &(&(n + 1)) * (z - p) ^ n)",
					By(
						shifted,
						comm_monoid.RightIdentity.Read(complex_field.MulMonoid).At(slope),
						complex_derivative.DerivativePow.At(a.TermAs[Nat]("n + 1"), difference),
						nat_arith.Add1.At(n),
						nat_monus.SucSubOne.At(n),
						complex_derivative.DerivativeChain.At(
							a.TermAs[Fun[Complex, Complex]]("λy:complex. y ^ (n + 1)"),
							shift,
							z,
							slope,
							a.TermAs[Complex]("&1")))),
				functions.ComposeApply)
			value := a.Have(
				"(n + 1)(z − p)ⁿ over ((z − p)ⁿ⁺¹)² is (n + 1)/(z − p)ⁿ⁺², the factor (z − p)ⁿ cancelling",
				"-(&(&(n + 1)) * (z - p) ^ n / ((z - p) ^ (n + 1)) ^ 2) = "+
					"-(&(&(n + 1)) * complex_inv((z - p) ^ (n + 2)))",
				Simp(
					Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
					Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
					Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
					Fwd(field.DivMulInv.Read(complex_field.Field)),
					Fwd(field.InvMul.Read(complex_field.Field))),
				ByArith(powers.At(n)))
			a.Show(
				"so by the reciprocal rule, (z − p)ⁿ⁺¹ being nonzero, "+
					"its reciprocal has derivative −(n + 1)/(z − p)ⁿ⁺²",
				By(
					powers.At(a.TermAs[Nat]("n + 1")),
					value,
					power,
					complex_derivative.DerivativeInv.At(
						a.TermAs[Fun[Complex, Complex]]("λu:complex. (u - p) ^ (n + 1)"),
						z,
						slope)))
		}),
})}

// InversePowerHolomorphic — 1/(z − p)ⁿ is holomorphic on any set that misses
// p: z − p is holomorphic, so is its n-th power, and off p no power of z − p
// is 0, so its reciprocal is holomorphic too.
var InversePowerHolomorphic = inversePowerHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "InversePowerHolomorphic",
	Key:  "prop_1b701cebbbbb3c6c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀p:complex. ∀n:num.",
		Hypotheses: []string{
			"p ∉ s",
		},
		Conclusion: "holomorphic_on(s, λz:complex. complex_inv((z - p) ^ n))",
	},
		func(a *Argument, s *Expr[Set[Complex]], p *Expr[Complex], n *Expr[Nat], outside Fact) {
			shift := a.TermAs[Fun[Complex, Complex]]("λu:complex. u - p")
			translate := a.Have(
				"z − p is holomorphic on s, a difference of the identity and a constant",
				"holomorphic_on(s, λu:complex. u - p)",
				By(
					complex_derivative.HolomorphicOnId.At(s),
					complex_derivative.HolomorphicOnConst.At(s, p),
					complex_derivative.HolomorphicOnSub.At(
						s,
						a.TermAs[Fun[Complex, Complex]]("λu:complex. u"),
						a.TermAs[Fun[Complex, Complex]]("λu:complex. p"))))
			nonzero := a.Have(
				"off p no power of z − p is 0, z − p not being 0",
				"∀z:complex. z ∈ s ⇒ (z - p) ^ n ≠ &0",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					inside := b.Assume()
					apart := b.Have(
						"z is in s and p is not, so z is not p",
						"z ≠ p",
						By(Normalized, inside, outside))
					b.Show(
						"a power of a nonzero number is not 0",
						ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(b.TermAs[Complex]("z - p"), n)))
				}))
			a.Show(
				"so the reciprocal of the power is holomorphic on s",
				By(
					nonzero,
					translate,
					complex_derivative.HolomorphicOnPow.At(s, shift, n),
					complex_derivative.HolomorphicOnInv.At(
						s,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - p) ^ n"))))
		}),
})}

// InversePowerIntegralZero — round a closed piecewise smooth path that
// misses p, 1/(z − p)ᵏ⁺² integrates to 0. Off p it is the derivative of
// F(z) = −1/((k + 1)(z − p)ᵏ⁺¹), by InversePowerDerivative at k, and it is
// continuous there, being holomorphic off p; so the integral is the change of
// F between the ends of the path, which agree.
var InversePowerIntegralZero = inversePowerIntegralZeroThm{family.Add(registry.ProofEntry{
	Name: "InversePowerIntegralZero",
	Key:  "prop_f077614033eee4e1",
	Build: family.Theorem(Statement{
		Binders: "∀γ γ':(real → complex). ∀a b:real. ∀p:complex. ∀k:num.",
		Hypotheses: []string{
			"«closedPathIn»(𝕌 ∖ {p}, γ, γ', a, b)",
		},
		Conclusion: "path_integral(λz:complex. complex_inv((z - p) ^ (k + 2)), γ, γ', a, b) = &0",
		Abbrev: Abbrev{
			{Name: "F", Text: "λu:complex. " +
				"    -complex_inv(complex_of_real(&(k + 1))) * complex_inv((u - p) ^ (k + 1))"},
		},
	},
		func(
			arg *Argument,
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			p *Expr[Complex],
			k *Expr[Nat],
			path, closed, inside Fact,
		) {
			integrand := arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv((z - p) ^ (k + 2))")
			avoids := arg.Have(
				"the path, in ℂ ∖ {p}, misses p",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ≠ p",
				BySets(inside))
			slope := arg.Have(
				"at each point of the path, which is not p, F has derivative 1/(γ(t) − p)ᵏ⁺²",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_derivative_at(«F», γ(t), complex_inv((γ(t) - p) ^ (k + 2)))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					value := d.Have(
						"−1/(k + 1) times −(k + 1)/(γ(t) − p)ᵏ⁺² is 1/(γ(t) − p)ᵏ⁺²",
						"-complex_inv(complex_of_real(&(k + 1))) * "+
							"-(complex_of_real(&(k + 1)) * complex_inv((γ(t) - p) ^ (k + 2))) = "+
							"complex_inv((γ(t) - p) ^ (k + 2))",
						ByArith())
					d.Show(
						"F is −1/(k + 1) times 1/(u − p)ᵏ⁺¹, whose derivative at γ(t) is −(k + 1)/(γ(t) − p)ᵏ⁺²",
						By(
							within,
							value,
							avoids.At(t),
							At(InversePowerDerivative, p, γ.Apply(t), k),
							complex_derivative.DerivativeScale.At(
								d.TermAs[Fun[Complex, Complex]]("λu:complex. complex_inv((u - p) ^ (k + 1))"),
								γ.Apply(t),
								d.TermAs[Complex]("-(complex_of_real(&(k + 1)) * complex_inv((γ(t) - p) ^ (k + 2)))"),
								d.TermAs[Complex]("-complex_inv(complex_of_real(&(k + 1)))"))))
				}))
			offPole := arg.TermAs[Set[Complex]]("𝕌 ∖ {p}")
			holomorphic := arg.Have(
				"the integrand is holomorphic off p",
				"holomorphic_on(𝕌 ∖ {p}, λz:complex. complex_inv((z - p) ^ (k + 2)))",
				BySets(InversePowerHolomorphic.At(offPole, p, arg.TermAs[Nat]("k + 2"))))
			continuous := arg.Have(
				"and the integrand, holomorphic off p, is continuous at each point of the path",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. complex_inv((z - p) ^ (k + 2)), γ(t))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"γ(t) lies off p",
						By(
							within,
							inside.At(t),
							holomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(
								offPole,
								integrand,
								γ.Apply(t))))
				}))
			change := arg.Have(
				"so by the fundamental theorem the integral is the change of F between the ends of the path",
				"path_integral(λz:complex. complex_inv((z - p) ^ (k + 2)), γ, γ', a, b) = «F»(γ(b)) - «F»(γ(a))",
				By(
					path,
					slope,
					continuous,
					path_integral.PathIntegralPrimitive.At(
						arg.TermAs[Fun[Complex, Complex]]("«F»"),
						integrand,
						γ,
						γPrime,
						a,
						b)))
			arg.Show(
				"and the ends agree, so the change is 0",
				closed.Rw(),
				ByArith(change))
		}),
})}

// PrincipalPartIntegral — round a closed piecewise smooth path that misses p,
// the principal part Σ_{k ≤ m} c(k)/(z − p)ᵐ⁺¹⁻ᵏ integrates to 2πi times the
// winding index about p times c(m). Each term is continuous along the path,
// so the integral of the sum is the sum of the integrals; a term below the
// last has exponent m + 1 − k ≥ 2 and integrates to 0
// (InversePowerIntegralZero), and the last is c(m)/(z − p), whose integral is
// c(m) times 2πi times the index (WindingIntegral).
var PrincipalPartIntegral = principalPartIntegralThm{family.Add(registry.ProofEntry{
	Name: "PrincipalPartIntegral",
	Key:  "prop_6b9f6ea55fa6350e",
	Build: family.Theorem(Statement{
		Binders: "∀γ γ':(real → complex). ∀a b:real. ∀p:complex. ∀c:(num → complex). ∀m:num.",
		Hypotheses: []string{
			"«closedPathIn»(𝕌 ∖ {p}, γ, γ', a, b)",
		},
		Conclusion: "path_integral(λz:complex. Σ_{k∈0 .. m} c(k) * complex_inv((z - p) ^ (m + 1 - k)), " +
			"    γ, " +
			"    γ', " +
			"    a, " +
			"    b) = " +
			"&(&2 * pi) * complex_i * winding_index(γ, γ', a, b, p) * c(m)",
		Abbrev: Abbrev{
			{Name: "termIntegral", Text: "λk:num. " +
				"    path_integral(λz:complex. c(k) * complex_inv((z - p) ^ (m + 1 - k)), γ, γ', a, b)"},
		},
	},
		func(
			arg *Argument,
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			p *Expr[Complex],
			c *Arrow[Nat, Complex],
			m *Expr[Nat],
			path, closed, inside Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			offPole := arg.TermAs[Set[Complex]]("𝕌 ∖ {p}")
			holomorphic := arg.Have(
				"off p each inverse power of z − p is holomorphic",
				"∀n:num. holomorphic_on(𝕌 ∖ {p}, λz:complex. complex_inv((z - p) ^ n))",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return BySets(InversePowerHolomorphic.At(offPole, p, n))
				}))
			inverse := arg.Have(
				"so it is continuous along the path, which stays off p",
				Statement{
					Binders: "∀n:num. ∀t:real.",
					Hypotheses: []string{
						"a ≤ t",
						"t ≤ b",
					},
					Conclusion: "complex_continuous_at(λz:complex. complex_inv((z - p) ^ n), γ(t))",
				},
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]("n")
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"γ(t) lies off p",
						By(
							within,
							inside.At(t),
							holomorphic.At(n),
							complex_derivative.HolomorphicOnContinuousAt.At(
								offPole,
								d.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv((z - p) ^ n)"),
								γ.Apply(t))))
				}))
			terms := arg.Have(
				"so is each term c(k)/(z − p)ᵐ⁺¹⁻ᵏ",
				Statement{
					Binders: "∀k:num. ∀t:real.",
					Hypotheses: []string{
						"a ≤ t",
						"t ≤ b",
					},
					Conclusion: "complex_continuous_at(λz:complex. c(k) * complex_inv((z - p) ^ (m + 1 - k)), γ(t))",
				},
				By(inverse, complex_topology.ContinuousAtConst, complex_topology.ContinuousAtMul))
			indices := arg.TermAs[Set[Nat]]("0 .. m")
			split := arg.Have(
				"the integral of the finite sum is the sum of the integrals of its terms",
				"path_integral(λz:complex. Σ_{k∈0 .. m} c(k) * complex_inv((z - p) ^ (m + 1 - k)), "+
					"    γ, "+
					"    γ', "+
					"    a, "+
					"    b) = "+
					"Σ_{k∈0 .. m} «termIntegral»(k)",
				By(
					path,
					terms,
					num_segment.Finite.At(arg.TermAs[Nat]("0"), m),
					At(
						path_integral.PathIntegralSum,
						indices,
						arg.TermAs[Fun[Nat, Fun[Complex, Complex]]](
							"λk:num. λz:complex. c(k) * complex_inv((z - p) ^ (m + 1 - k))"),
						γ,
						γPrime,
						a,
						b)))
			below := arg.Have(
				"a term below the last has an exponent of at least 2, so it integrates to 0",
				"∀k:num. k ∈ 0 .. m ∧ k ∉ {m} ⇒ «termIntegral»(k) = &0",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					given := d.Assume()
					lower := d.TermAs[Nat]("m - 1 - k")
					exponent := d.Have(
						"k is below m, so m + 1 − k is (m − 1 − k) + 2",
						"m + 1 - k = m - 1 - k + 2",
						ByArith(given, num_segment.MembershipFromZero.At(k, m), set_basic.InSing.At(k, m)))
					d.Show(
						"c(k) comes out of the integral, and 1/(z − p)⁽ᵐ⁻¹⁻ᵏ⁾⁺² integrates to 0 round the closed path",
						exponent.Rw(),
						ByArith(
							inverse,
							path,
							closed,
							inside,
							path_integral.PathIntegralScale.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv((z - p) ^ (m - 1 - k + 2))"),
								γ,
								γPrime,
								a,
								b,
								c.Apply(k)),
							InversePowerIntegralZero.At(γ, γPrime, a, b, p, lower)))
				}))
			last := arg.Have(
				"the last term is c(m)/(z − p), whose integral is c(m) times 2πi times the index",
				"«termIntegral»(m) = &(&2 * pi) * complex_i * winding_index(γ, γ', a, b, p) * c(m)",
				Derive(func(d *Argument) {
					unity := comm_monoid.PowOne.Read(complex_field.MulMonoid)
					exponent := d.Have(
						"m + 1 − m is 1",
						"m + 1 - m = 1",
						ByArith())
					reciprocal := d.Simplified(inverse.At(d.TermAs[Nat]("1")), Fwd(unity))
					d.Show(
						"c(m) comes out of the integral of c(m)/(z − p)¹, and 1/(z − p) integrates to 2πi times the index",
						exponent.Rw(),
						Simp(Fwd(unity)),
						ByArith(
							reciprocal,
							path,
							path_integral.PathIntegralScale.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(z - p)"),
								γ,
								γPrime,
								a,
								b,
								c.Apply(m)),
							WindingIntegral.At(γ, γPrime, a, b, p)))
				}))
			alone := arg.Have(
				"the terms below the last add nothing, so the sum is the one over {m}",
				"Σ_{k∈{m}} «termIntegral»(k) = Σ_{k∈0 .. m} «termIntegral»(k)",
				By(
					below,
					comm_ring.NeutralAdd.Read(complex_field.CommRing),
					set_order.SingSubset.At(indices, m),
					num_segment.MembershipFromZero.At(m, m),
					nat_order.LessEqRefl.At(m),
					monoidal.Superset.At(
						arg.TermAs[Op[Complex]]("complex_add"),
						arg.TermAs[Set[Nat]]("{m}"),
						indices,
						arg.TermAs[Fun[Nat, Complex]]("«termIntegral»"))))
			arg.Show(
				"so the integral of the principal part is the last term's",
				By(split, alone, last, monoidal.Sing.Read(addition)))
		}),
})}
