// theorem.go — the residue theorem on a convex open set (ResidueTheorem).

package residue

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ResidueTheorem — the residue theorem: on a convex open set, a function
// holomorphic but for finitely many poles integrates round a closed piecewise
// smooth path that misses them to 2πi times the sum, over the poles, of the
// winding index times the residue. Less all its principal parts, f is
// holomorphic on the whole set, so it integrates to 0 by Cauchy's theorem, and
// each principal part integrates to 2πi times the index times its residue
// (PrincipalPartAtPole, PrincipalPartIntegral).
var ResidueTheorem = residueTheoremThm{family.Add(registry.ProofEntry{
	Name: "ResidueTheorem",
	Key:  "prop_7a9f3f23867927f1",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). " +
			"∀f:(complex → complex). " +
			"∀P:set(complex). " +
			"∀γ γ':(real → complex). " +
			"∀a b:real.",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"«convex»(S)",
			"finite(P)",
			"holomorphic_on(S ∖ P, f)",
			"∀p:complex. p ∈ P ⇒ «meromorphicAt»(f, p)",
			"«closedPathIn»(S ∖ P, γ, γ', a, b)",
		},
		Conclusion: "path_integral(f, γ, γ', a, b) = " +
			"&(&2 * pi) * complex_i * Σ_{p∈P} winding_index(γ, γ', a, b, p) * complex_residue(f, p)",
		Abbrev: Abbrev{
			{Name: "expansion", Text: "λp:complex. " +
				"λr:real. " +
				"λm:num. " +
				"λc:(num → complex). " +
				"λh:(complex → complex). " +
				"    &0 < r ∧ " +
				"    holomorphic_on(«disc»(p, r), h) ∧ " +
				"    (∀z:complex. " +
				"        z ∈ «punctured»(p, r) ⇒ " +
				"        f(z) = Σ_{k∈0 .. m} c(k) * complex_inv((z - p) ^ (m + 1 - k)) + h(z)) ∧ " +
				"    complex_residue(f, p) = c(m)"},
			{Name: "part", Text: "λq:complex. λz:complex. " +
				"    Σ_{k∈0 .. M(q)} C(q, k) * complex_inv((z - q) ^ (M(q) + 1 - k))"},
			{Name: "parts", Text: "λz:complex. Σ_{q∈P} «part»(q, z)"},
			{Name: "Q", Text: "λz:complex. " +
				"    COND(z ∈ P, H(z, z) - Σ_{q∈delete(P, z)} «part»(q, z), f(z) - «parts»(z))"},
		},
	},
		func(
			arg *Argument,
			S *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			P *Expr[Set[Complex]],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			open, convex, finite, holomorphic, poles, closedPath Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			loop := arg.Conjuncts(
				closedPath,
				"γ is a piecewise smooth path on ⟦a, b⟧",
				"it is closed",
				"it stays in S ∖ P")
			path, closed := loop[0], loop[1]
			avoids := arg.Have(
				"so it stays in S and misses the poles",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ S ∧ γ(t) ∉ P",
				BySets(loop[2]))
			local := arg.Have(
				"at each pole f is a principal part plus a function holomorphic "+
					"on a disc about it, the residue its coefficient of 1/(z − p)",
				Statement{
					Binders: "∀p:complex.",
					Hypotheses: []string{
						"p ∈ P",
					},
					Conclusion: "∃r:real. ∃m:num. ∃c:(num → complex). ∃h:(complex → complex). " +
						"    «expansion»(p, r, m, c, h)",
				},
				By(poles, PrincipalPartAtPole))
			_, _, _, chosen := arg.Obtain3As[Fun[Complex, Nat], Fun[Complex, Fun[Nat, Complex]], Fun[Complex, Fun[Complex, Complex]]](
				"choose them pole by pole: the order M(p), the coefficients C(p) and the regular part H(p)",
				"∃M:(complex → num). ∃C:(complex → num → complex). ∃H:(complex → complex → complex). ∀p:complex. "+
					"    p ∈ P ⇒ ∃r:real. «expansion»(p, r, M(p), C(p), H(p))",
				By(local))
			offPoles := arg.Have(
				"a sum of principal parts over some of the poles is holomorphic off them",
				"∀J:set(complex). J ⊆ P ⇒ holomorphic_on(𝕌 ∖ J, λz:complex. Σ_{q∈J} «part»(q, z))",
				Derive(func(d *Argument) {
					J := d.FixAs[Set[Complex]]("J")
					within := d.Assume()
					offJ := d.TermAs[Set[Complex]]("𝕌 ∖ J")
					each := d.Have(
						"each of them is holomorphic off its pole, so off J",
						"∀q:complex. q ∈ J ⇒ holomorphic_on(𝕌 ∖ J, «part»(q))",
						Derive(func(e *Argument) {
							q := e.FixAs[Complex]("q")
							among := e.Assume()
							e.Show(
								"a principal part is holomorphic off its pole, and q is not off J",
								BySets(
									among,
									PrincipalPartHolomorphic.At(
										offJ,
										q,
										e.TermAs[Fun[Nat, Complex]]("C(q)"),
										e.TermAs[Nat]("M(q)"))))
						}))
					d.Show(
						"so is their finite sum",
						By(
							each,
							finite,
							within,
							finite_set.FiniteSubset.At(J, P),
							complex_derivative.HolomorphicOnSum.At(
								offJ,
								J,
								d.TermAs[Fun[Complex, Fun[Complex, Complex]]]("λq:complex. λz:complex. «part»(q, z)"))))
				}))
			Q := arg.TermAs[Fun[Complex, Complex]]("«Q»")
			parts := arg.TermAs[Fun[Complex, Complex]]("«parts»")
			offAll := arg.TermAs[Set[Complex]]("𝕌 ∖ P")
			partsHolomorphic := arg.Have(
				"in particular the sum of all of them is holomorphic off the poles",
				"holomorphic_on(𝕌 ∖ P, «parts»)",
				By(offPoles.At(P), set_order.SubsetRefl.At(P)))
			regular := arg.Have(
				"Q is holomorphic on S",
				"holomorphic_on(S, «Q»)",
				Simp(Fwd(complex_derivative.HolomorphicOnDef)),
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					inside := d.Assume()
					δ, isolated := d.ObtainAs[Real](
						"no pole other than z lies within some distance δ of z",
						"∃δ:real. &0 < δ ∧ ∀q:complex. q ∈ P ∧ |q - z| < δ ⇒ q = z",
						By(finite, complex_topology.FinitePointsIsolated.At(P, z)),
						Named("δ"))
					apart := d.Conjuncts(
						isolated,
						"δ is positive",
						"no pole but z lies within δ of z")
					d.Cases(d.TermAs[Bool]("z ∈ P"))
					d.When(
						"at a pole, Q is near z the regular part H(z) less the other principal parts",
						func(e *Argument, pole Fact) {
							r, data := e.UnpackAs[Real](GroupPremises(pole, chosen.At(z)), "r")
							near := e.Conjuncts(
								data,
								"r is positive",
								"H(z) is holomorphic on the disc of radius r about z",
								"off z on that disc, f is the principal part at z plus H(z)",
								"the residue at z is C(z, M(z))")
							disc := e.TermAs[Set[Complex]]("«disc»(z, r)")
							centre := e.Have(
								"z lies in its own disc",
								"z ∈ «disc»(z, r)",
								ByArith(near[0], complex_abs.AbsEqZero.At(e.TermAs[Complex]("z - z"))))
							l1, regularSlope := e.ObtainAs[Complex](
								"H(z), holomorphic on the disc, has a derivative l₁ at z",
								"∃l:complex. complex_derivative_at(H(z), z, l)",
								By(
									near[1],
									centre,
									complex_derivative.HolomorphicOnDef.At(
										disc,
										e.TermAs[Fun[Complex, Complex]]("H(z)"))),
								Named("l₁"))
							others := e.TermAs[Set[Complex]]("delete(P, z)")
							aside := e.Have(
								"z is none of the other poles",
								"z ∈ 𝕌 ∖ delete(P, z)",
								BySets())
							l2, othersSlope := e.ObtainAs[Complex](
								"and the sum of the other principal parts, holomorphic "+
									"off the other poles, has a derivative l₂ at z",
								"∃l:complex. complex_derivative_at(λw:complex. Σ_{q∈delete(P, z)} «part»(q, w), z, l)",
								By(
									aside,
									set_order.DeleteSubset.At(P, z),
									offPoles.At(others),
									complex_derivative.HolomorphicOnDef.At(
										e.TermAs[Set[Complex]]("𝕌 ∖ delete(P, z)"),
										e.TermAs[Fun[Complex, Complex]]("λw:complex. Σ_{q∈delete(P, z)} «part»(q, w)"))),
								Named("l₂"))
							radius := e.TermAs[Real]("min(δ, r)")
							agree := e.Have(
								"within min(δ, r) of z, Q is H(z) less the other principal parts",
								"∀w:complex. |w - z| < min(δ, r) ⇒ «Q»(w) = H(z, w) - Σ_{q∈delete(P, z)} «part»(q, w)",
								Derive(func(g *Argument) {
									w := g.FixAs[Complex]("w")
									nearby := g.Assume()
									g.Cases(g.TermAs[Bool]("w = z"))
									g.When(
										"at z itself this is the value Q is given at a pole",
										func(k *Argument, same Fact) {
											k.Show(
												"z is a pole",
												same.Rw(),
												By(pole))
										})
									g.Otherwise(
										"elsewhere w is no pole, f(w) is the principal part at z plus H(z, "+
											"w), and the sum over P is that part plus the sum over the others",
										func(k *Argument, other Fact) {
											gap := k.TermAs[Real]("|w - z|")
											notPole := k.Have(
												"w is no pole, being within δ of z and not z",
												"w ∉ P",
												By(other, nearby, apart[1], real_sup_inf.LessThanMin.At(δ, r, gap)))
											value := k.Have(
												"w is off z within r of it, so f(w) is the principal part at z plus H(z, w)",
												"f(w) = «part»(z, w) + H(z, w)",
												ByArith(
													other,
													nearby,
													near[2].At(w),
													real_sup_inf.LessThanMin.At(δ, r, gap),
													complex_abs.AbsPosIffNonzero.At(
														k.TermAs[Complex]("w - z"))))
											k.Show(
												"so Q(w) = f(w) less all the parts is H(z, w) less the others",
												ByArith(
													finite,
													notPole,
													value,
													pole,
													monoidal.Delete.Read(addition).At(
														P,
														k.TermAs[Fun[Complex, Complex]]("λq:complex. «part»(q, w)"),
														z)))
										})
								}))
							e.Take(e.TermAs[Complex]("l₁ - l₂"))
							e.Show(
								"so Q, equal near z to H(z) less the other principal parts, has the derivative l₁ − l₂ at z",
								By(
									apart[0],
									near[0],
									agree,
									regularSlope,
									othersSlope,
									real_sup_inf.LessThanMin.At(δ, r, e.TermAs[Real]("&0")),
									complex_derivative.DerivativeSub.At(
										e.TermAs[Fun[Complex, Complex]]("H(z)"),
										e.TermAs[Fun[Complex, Complex]]("λw:complex. Σ_{q∈delete(P, z)} «part»(q, w)"),
										z,
										l1,
										l2),
									complex_derivative.DerivativeLocal.At(
										Q,
										e.TermAs[Fun[Complex, Complex]]("λw:complex. H(z, w) - Σ_{q∈delete(P, z)} «part»(q, w)"),
										z,
										e.TermAs[Complex]("l₁ - l₂"),
										radius)))
						})
					d.Otherwise(
						"off the poles, Q is near z f less all the principal parts",
						func(e *Argument, notPole Fact) {
							l1, fSlope := e.ObtainAs[Complex](
								"f, holomorphic off the poles, has a derivative l₁ at z",
								"∃l:complex. complex_derivative_at(f, z, l)",
								By(
									holomorphic,
									inside,
									notPole,
									complex_derivative.HolomorphicOnDef.At(
										e.TermAs[Set[Complex]]("S ∖ P"),
										f),
									set_basic.InDiff.At(S, P, z)),
								Named("l₁"))
							outside := e.Have(
								"z is off the poles",
								"z ∈ 𝕌 ∖ P",
								BySets(notPole))
							l2, partsSlope := e.ObtainAs[Complex](
								"and the sum of all the principal parts, holomorphic off the poles, has a derivative l₂ at z",
								"∃l:complex. complex_derivative_at(«parts», z, l)",
								By(outside, partsHolomorphic, complex_derivative.HolomorphicOnDef.At(offAll, parts)),
								Named("l₂"))
							agree := e.Have(
								"within δ of z there is no pole, so there Q is f less all the principal parts",
								"∀w:complex. |w - z| < δ ⇒ «Q»(w) = f(w) - «parts»(w)",
								By(notPole, apart[1]))
							e.Take(e.TermAs[Complex]("l₁ - l₂"))
							e.Show(
								"so Q has the derivative l₁ − l₂ at z",
								By(
									apart[0],
									agree,
									fSlope,
									partsSlope,
									complex_derivative.DerivativeSub.At(f, parts, z, l1, l2),
									complex_derivative.DerivativeLocal.At(
										Q,
										e.TermAs[Fun[Complex, Complex]]("λw:complex. f(w) - «parts»(w)"),
										z,
										e.TermAs[Complex]("l₁ - l₂"),
										δ)))
						})
				}))
			vanishes := arg.Have(
				"so by Cauchy's theorem Q integrates to 0 round the closed path, which stays in S",
				"path_integral(«Q», γ, γ', a, b) = &0",
				By(
					open,
					convex,
					regular,
					path,
					avoids,
					closed,
					cauchy_integral.CauchyConvex.At(S, Q, γ, γPrime, a, b)))
			QAlong := arg.Have(
				"so is Q, holomorphic on S, continuous at each point of the path",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(«Q», γ(t))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"γ(t) lies in S",
						By(
							within,
							avoids.At(t),
							regular,
							complex_derivative.HolomorphicOnContinuousAt.At(S, Q, γ.Apply(t))))
				}))
			offPath := arg.Have(
				"the path lies off the poles",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ 𝕌 ∖ P",
				BySets(loop[2]))
			partsAlong := arg.Have(
				"and so is the sum of the principal parts, holomorphic off the poles, which the path misses",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(«parts», γ(t))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"γ(t) is no pole",
						By(
							within,
							offPath.At(t),
							partsHolomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(
								offAll,
								parts,
								γ.Apply(t))))
				}))
			eachAlong := arg.Have(
				"and so is each principal part, holomorphic off its pole",
				"∀q:complex. ∀t:real. q ∈ P ∧ a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(«part»(q), γ(t))",
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					t := d.FixAs[Real]("t")
					given := d.Assume()
					offPole := d.TermAs[Set[Complex]]("𝕌 ∖ {q}")
					part := d.TermAs[Fun[Complex, Complex]]("«part»(q)")
					holomorphic := d.Have(
						"the principal part at q is holomorphic off q",
						"holomorphic_on(𝕌 ∖ {q}, «part»(q))",
						BySets(
							PrincipalPartHolomorphic.At(
								offPole,
								q,
								d.TermAs[Fun[Nat, Complex]]("C(q)"),
								d.TermAs[Nat]("M(q)"))))
					missed := d.Have(
						"γ(t), which is no pole, is not q",
						"γ(t) ∈ 𝕌 ∖ {q}",
						BySets(given, avoids.At(t)))
					d.Show(
						"so it is continuous at γ(t)",
						By(missed, holomorphic, complex_derivative.HolomorphicOnContinuousAt.At(offPole, part, γ.Apply(t))))
				}))
			ordered := arg.Have(
				"the path runs over ⟦a, b⟧, so a ≤ b",
				"a ≤ b",
				By(path, path_integral.PiecewiseSmoothPathDef.At(γ, γPrime, a, b)))
			split := arg.Have(
				"on the path, which misses the poles, f is Q plus the principal parts",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) = «Q»(γ(t)) + «parts»(γ(t))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"γ(t) is no pole, so there Q is f less the principal parts",
						ByArith(within, avoids.At(t)))
				}))
			each := arg.Have(
				"each principal part integrates to 2πi times the winding "+
					"index times its coefficient of 1/(z − q), the residue",
				Statement{
					Binders: "∀q:complex.",
					Hypotheses: []string{
						"q ∈ P",
					},
					Conclusion: "path_integral(«part»(q), γ, γ', a, b) = " +
						"&(&2 * pi) * complex_i * (winding_index(γ, γ', a, b, q) * complex_residue(f, q))",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					among := d.Assume()
					_, data := d.UnpackAs[Real](GroupPremises(among, chosen.At(q)), "r")
					residue := d.Conjuncts(
						data,
						"r is positive",
						"H(q) is holomorphic on the disc of radius r about q",
						"off q on that disc, f is the principal part at q plus H(q)",
						"the residue at q is C(q, M(q))")
					missed := d.Have(
						"the path misses q, a pole, so it runs in ℂ ∖ {q}",
						"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ 𝕌 ∖ {q}",
						BySets(among, avoids))
					d.Show(
						"by the integral of a principal part round a closed path",
						ByArith(
							residue[3],
							path,
							closed,
							missed,
							PrincipalPartIntegral.At(
								γ,
								γPrime,
								a,
								b,
								q,
								d.TermAs[Fun[Nat, Complex]]("C(q)"),
								d.TermAs[Nat]("M(q)"))))
				}))
			keepsZero := arg.Have(
				"multiplying by 2πi keeps 0",
				"&(&2 * pi) * complex_i * neutral_elem(complex_add) = neutral_elem(complex_add)",
				ByArith(comm_ring.NeutralAdd.Read(complex_field.CommRing)))
			keepsAddition := arg.Have(
				"and distributes over addition",
				"∀u v:complex. "+
					"    &(&2 * pi) * complex_i * (u + v) = &(&2 * pi) * complex_i * u + &(&2 * pi) * complex_i * v",
				ByArith())
			arg.Show(
				"so the integral of f is 2πi times the sum of index times residue",
				CalcEq(
					Leg(
						arg.TermAs[Complex]("path_integral(λz:complex. «Q»(z) + «parts»(z), γ, γ', a, b)"),
						"f agrees on the path with Q plus the principal "+
							"parts, the times between a and b being those of ⟦a, b⟧",
						By(
							ordered,
							split,
							real_sup_inf.RealMinDef.At(a, b),
							real_sup_inf.RealMaxDef.At(a, b),
							path_integral.PathIntegralCongruence.At(
								f,
								arg.TermAs[Fun[Complex, Complex]]("λz:complex. «Q»(z) + «parts»(z)"),
								γ,
								γPrime,
								a,
								b))),
					Leg(
						arg.TermAs[Complex]("path_integral(«Q», γ, γ', a, b) + path_integral(«parts», γ, γ', a, b)"),
						"integrals add",
						By(path, QAlong, partsAlong, path_integral.PathIntegralAdd.At(Q, parts, γ, γPrime, a, b))),
					Leg(
						arg.TermAs[Complex]("Σ_{q∈P} path_integral(«part»(q), γ, γ', a, b)"),
						"Q integrates to 0, and the integral of the finite sum "+
							"of the principal parts is the sum of their integrals",
						ByArith(
							vanishes,
							path,
							finite,
							eachAlong,
							path_integral.PathIntegralSum.At(
								P,
								arg.TermAs[Fun[Complex, Fun[Complex, Complex]]]("λq:complex. λz:complex. «part»(q, z)"),
								γ,
								γPrime,
								a,
								b))),
					Leg(
						arg.TermAs[Complex](
							"Σ_{q∈P} &(&2 * pi) * complex_i * (winding_index(γ, γ', a, b, q) * complex_residue(f, q))"),
						"each principal part integrates to 2πi times index times residue",
						By(each, addition, monoidal.Congruence)),
					FinalLeg(
						"and 2πi comes out of the finite sum",
						By(
							finite,
							keepsZero,
							keepsAddition,
							addition,
							Where(
								monoidal.Homomorphic,
								"h",
								arg.TermAs[Fun[Complex, Complex]]("λu:complex. &(&2 * pi) * complex_i * u"))))))
		}),
})}
