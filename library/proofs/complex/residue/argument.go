// argument.go — the argument principle on a convex open set, with poles and
// without (ArgumentPrinciple, ArgumentPrincipleHolomorphic), and Rouché's
// theorem (Rouche); both again on a circle, where the index-weighted counts
// are plain counts inside (RoucheCircle, ArgumentPrincipleCircle).

package residue

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ArgumentPrinciple — the argument principle on a convex open set: let f
// have a derivative f′ on S off the finite set P, each point of which is a
// pole of f, and let the zeros of f in S ∖ P be finitely many. Round a closed
// piecewise smooth path in S ∖ P on which f has no zero, f′/f integrates to
// 2πi times the orders of the zeros less the orders of the poles, each
// weighted by the winding index. f′/f is holomorphic on S off the zeros and
// the poles in S; at a zero it has at most a pole with residue the zero's
// order, at a pole one with residue minus the pole's order
// (LogDerivativeAtZero, LogDerivativeAtPole), so the residue theorem gives
// the weighted sum of these. A pole outside S counts nothing, the path not
// winding about it (WindingOutsideConvex).
var ArgumentPrinciple = argumentPrincipleThm{family.Add(registry.ProofEntry{
	Name: "ArgumentPrinciple",
	Key:  "prop_203ecba1f9201b96",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). " +
			"∀f f':(complex → complex). " +
			"∀P:set(complex). " +
			"∀γ γ':(real → complex). " +
			"∀a b:real.",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"«convex»(S)",
			"finite(P)",
			"∀z:complex. z ∈ S ∖ P ⇒ complex_derivative_at(f, z, f'(z))",
			"∀p:complex. p ∈ P ⇒ «properPole»(f, p)",
			"finite(«zeros»)",
			"«closedPathIn»(S ∖ P, γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) ≠ &0",
		},
		Conclusion: "path_integral(λz:complex. f'(z) / f(z), γ, γ', a, b) = " +
			"&(&2 * pi) * " +
			"complex_i * " +
			"(Σ_{z∈«zeros»} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z))) - " +
			"    Σ_{p∈P} winding_index(γ, γ', a, b, p) * &(&(complex_pole_order(f, p))))",
		Abbrev: Abbrev{
			{Name: "zeros", Text: "{z:complex | z ∈ S ∖ P ∧ f(z) = &0}"},
			{Name: "F", Text: "λz:complex. f'(z) / f(z)"},
			{Name: "weighted", Text: "λq:complex. winding_index(γ, γ', a, b, q) * complex_residue(«F», q)"},
		},
	},
		func(
			arg *Argument,
			S *Expr[Set[Complex]],
			f, fPrime *Arrow[Complex, Complex],
			P *Expr[Set[Complex]],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			open, convex, polesFinite, slope, poles, zerosFinite, closedPath, zeroFree Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			Z := arg.TermAs[Set[Complex]]("«zeros»")
			loop := arg.Conjuncts(
				closedPath,
				"γ is a piecewise smooth path on ⟦a, b⟧",
				"it is closed",
				"it stays in S ∖ P")
			path, closed := loop[0], loop[1]
			offPoles := arg.TermAs[Set[Complex]]("S ∖ P")
			nbhd := arg.Have(
				"about each point q of S a disc lies in S on which no zero or pole lies but q",
				Statement{
					Binders: "∀q:complex.",
					Hypotheses: []string{
						"q ∈ S",
					},
					Conclusion: "∃ρ:real. &0 < ρ ∧ ∀z:complex. |z - q| < ρ ⇒ z ∈ S ∧ (z ∈ «zeros» ∪ P ⇒ z = q)",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					inside := d.Assume()
					_, ball := d.ObtainAs[Real](
						"S being open, the disc of some radius r about q lies in S",
						"∃r:real. &0 < r ∧ ∀w:complex. |w - q| < r ⇒ w ∈ S",
						By(inside, open, complex_topology.ComplexOpenIff.At(S)),
						Named("r"))
					_, isolated := d.ObtainAs[Real](
						"the zeros and the poles being finitely many, none but q lies within some δ of q",
						"∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ «zeros» ∪ P ∧ |z - q| < δ ⇒ z = q",
						By(
							zerosFinite,
							polesFinite,
							finite_set.FiniteUnionImp.At(Z, P),
							complex_topology.FinitePointsIsolated.At(
								d.TermAs[Set[Complex]]("«zeros» ∪ P"),
								q)),
						Named("δ"))
					d.Take(d.TermAs[Real]("min(r, δ)"))
					d.Show(
						"the smaller of the two radii serves",
						By(ball, isolated, real_sup_inf.LessThanMin))
				}))
			punctured := arg.Have(
				"S ∖ P is open, an open set less finitely many points",
				"S ∖ P ∈ complex_topology",
				By(open, polesFinite, complex_topology.OpenDiffFinite.At(S, P)))
			holomorphic := arg.Have(
				"f is holomorphic on S ∖ P, having the derivative f′ there",
				"holomorphic_on(S ∖ P, f)",
				Unfold(complex_derivative.HolomorphicOnDef),
				arg.ForEach(func(z *Expr[Complex]) Action {
					return By(Normalized, slope.At(z))
				}))
			g, derived := arg.ObtainAs[Fun[Complex, Complex]](
				"so on the open set S ∖ P, f has a derivative g that is itself holomorphic",
				"∃g:(complex → complex). "+
					"    (∀z:complex. z ∈ S ∖ P ⇒ complex_derivative_at(f, z, g(z))) ∧ holomorphic_on(S ∖ P, g)",
				By(punctured, holomorphic, cauchy_integral.HolomorphicDerivative),
				Named("g"))
			derivative := arg.Conjuncts(
				derived,
				"g(z) is the derivative of f at each point z of S ∖ P",
				"g is holomorphic on S ∖ P")
			agree := arg.Have(
				"f′ is g on S ∖ P, a derivative being unique",
				"∀z:complex. z ∈ S ∖ P ⇒ f'(z) = g(z)",
				arg.ForEach(func(z *Expr[Complex]) Action {
					return By(slope.At(z), derivative[0].At(z), complex_derivative.DerivativeUnique)
				}))
			primeHolomorphic := arg.Have(
				"so f′ is holomorphic on S ∖ P",
				"holomorphic_on(S ∖ P, f')",
				By(punctured, derivative[1], agree, complex_derivative.HolomorphicOnAgree.At(offPoles, fPrime, g)))
			singular := arg.TermAs[Set[Complex]]("«zeros» ∪ (P ∩ S)")
			regularSet := arg.TermAs[Set[Complex]]("S ∖ («zeros» ∪ (P ∩ S))")
			smaller := arg.Have(
				"S less the zeros and the poles in S lies in S ∖ P",
				"S ∖ («zeros» ∪ (P ∩ S)) ⊆ S ∖ P",
				BySets())
			nonzero := arg.Have(
				"there f is not 0, no zero being left",
				"∀z:complex. z ∈ S ∖ («zeros» ∪ (P ∩ S)) ⇒ f(z) ≠ &0",
				BySets())
			logHolomorphic := arg.Have(
				"so f′/f is holomorphic on S off the zeros and the poles",
				"holomorphic_on(S ∖ («zeros» ∪ (P ∩ S)), «F»)",
				By(
					nonzero,
					primeHolomorphic,
					holomorphic,
					smaller,
					complex_derivative.HolomorphicOnSubset.At(offPoles, regularSet, f),
					complex_derivative.HolomorphicOnSubset.At(offPoles, regularSet, fPrime),
					complex_derivative.HolomorphicOnDiv.At(regularSet, fPrime, f)))
			atZeros := arg.Have(
				"at a zero z, f′/f has at most a pole, with residue the order of the zero",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ «zeros»",
					},
					Conclusion: "«meromorphicAt»(«F», z) ∧ complex_residue(«F», z) = &(&(complex_zero_order(f, z)))",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					zero := d.Assume()
					ρ, around := d.ObtainAs[Real](
						"a disc about z in S on which no zero or pole lies but z",
						"∃ρ:real. &0 < ρ ∧ ∀w:complex. |w - z| < ρ ⇒ w ∈ S ∧ (w ∈ «zeros» ∪ P ⇒ w = z)",
						By(nbhd.At(z), zero, set_basic.InDiff.At(S, P, z)),
						Named("ρ"))
					within := d.Have(
						"the disc lies in S ∖ P, z being no pole",
						"«disc»(z, ρ) ⊆ S ∖ P",
						BySets(around, zero))
					off := d.Have(
						"off z on the disc a point is in S ∖ P and no zero of f",
						"∀w:complex. w ∈ «punctured»(z, ρ) ⇒ w ∈ S ∖ P ∧ f(w) ≠ &0",
						Derive(func(e *Argument) {
							e.FixAs[Complex]("w")
							near := e.Assume()
							apart := e.Have(
								"w is not z",
								"w ≠ z",
								ByArith(near, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("w - z"))))
							e.Show(
								"so w is in S and neither a pole nor a zero",
								BySets(apart, around, near))
						}))
					differentiable := d.Have(
						"so off z on the disc f has the derivative f′",
						"∀w:complex. w ∈ «punctured»(z, ρ) ⇒ complex_derivative_at(f, w, f'(w))",
						By(slope, off))
					d.Show(
						"by the logarithmic derivative at a zero",
						By(
							off,
							differentiable,
							holomorphic,
							within,
							around,
							complex_derivative.HolomorphicOnSubset.At(
								offPoles,
								d.TermAs[Set[Complex]]("«disc»(z, ρ)"),
								f),
							LogDerivativeAtZero.At(f, fPrime, z, ρ)))
				}))
			atPoles := arg.Have(
				"at a pole p in S, f′/f has at most a pole, with residue minus the order of the pole",
				Statement{
					Binders: "∀p:complex.",
					Hypotheses: []string{
						"p ∈ P ∩ S",
					},
					Conclusion: "«meromorphicAt»(«F», p) ∧ complex_residue(«F», p) = -&(&(complex_pole_order(f, p)))",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Complex]("p")
					pole := d.Assume()
					inside := set_basic.InInter.At(P, S, p)
					ρ, around := d.ObtainAs[Real](
						"a disc about p in S on which no pole lies but p",
						"∃ρ:real. &0 < ρ ∧ ∀w:complex. |w - p| < ρ ⇒ w ∈ S ∧ (w ∈ «zeros» ∪ P ⇒ w = p)",
						By(nbhd.At(p), pole, inside),
						Named("ρ"))
					off := d.Have(
						"off p on the disc a point is in S ∖ P",
						"∀w:complex. w ∈ «punctured»(p, ρ) ⇒ w ∈ S ∖ P",
						Derive(func(e *Argument) {
							e.FixAs[Complex]("w")
							near := e.Assume()
							apart := e.Have(
								"w is not p",
								"w ≠ p",
								ByArith(near, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("w - p"))))
							e.Show(
								"so w is in S and no pole",
								BySets(apart, around, near))
						}))
					differentiable := d.Have(
						"so off p on the disc f has the derivative f′",
						"∀w:complex. w ∈ «punctured»(p, ρ) ⇒ complex_derivative_at(f, w, f'(w))",
						By(slope, off))
					d.Show(
						"by the logarithmic derivative at a pole",
						By(poles.At(p), pole, inside, differentiable, around, LogDerivativeAtPole.At(f, fPrime, p, ρ)))
				}))
			polesInS := arg.Have(
				"the poles in S are finitely many",
				"finite(P ∩ S)",
				By(polesFinite, finite_set.FiniteInter.At(P, S)))
			finiteSingular := arg.Have(
				"and so are the zeros with them",
				"finite(«zeros» ∪ (P ∩ S))",
				By(zerosFinite, polesInS, finite_set.FiniteUnionImp.At(Z, arg.TermAs[Set[Complex]]("P ∩ S"))))
			everyPole := arg.Have(
				"so f′/f has at most a pole at each of them",
				"∀q:complex. q ∈ «zeros» ∪ (P ∩ S) ⇒ «meromorphicAt»(«F», q)",
				By(atZeros, atPoles, set_basic.InUnion))
			missed := arg.Have(
				"the path stays in S and misses them, f having no zero on it",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ S ∖ («zeros» ∪ (P ∩ S))",
				BySets(loop[2], zeroFree))
			inS := arg.Have(
				"in particular it stays in S",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ S",
				BySets(loop[2]))
			residue := arg.Have(
				"so by the residue theorem f′/f integrates to 2πi times the sum over them of index times residue",
				"path_integral(«F», γ, γ', a, b) = &(&2 * pi) * complex_i * Σ_{q∈«zeros» ∪ (P ∩ S)} «weighted»(q)",
				By(
					open,
					convex,
					finiteSingular,
					logHolomorphic,
					everyPole,
					path,
					closed,
					missed,
					ResidueTheorem.At(
						S,
						arg.TermAs[Fun[Complex, Complex]]("«F»"),
						singular,
						γ,
						γPrime,
						a,
						b)))
			apart := arg.Have(
				"no zero is a pole",
				"disjoint(«zeros», P ∩ S)",
				BySets())
			split := arg.Have(
				"the sum splits into one over the zeros and one over the poles in S",
				"Σ_{q∈«zeros» ∪ (P ∩ S)} «weighted»(q) = Σ_{q∈«zeros»} «weighted»(q) + Σ_{q∈P ∩ S} «weighted»(q)",
				By(
					zerosFinite,
					polesInS,
					apart,
					monoidal.Union.Read(addition).At(
						Z,
						arg.TermAs[Set[Complex]]("P ∩ S"),
						arg.TermAs[Fun[Complex, Complex]]("«weighted»"))))
			zeroTerms := arg.Have(
				"at a zero the residue is the order",
				Statement{
					Binders: "∀q:complex.",
					Hypotheses: []string{
						"q ∈ «zeros»",
					},
					Conclusion: "«weighted»(q) = winding_index(γ, γ', a, b, q) * &(&(complex_zero_order(f, q)))",
				},
				arg.ForEach(func(q *Expr[Complex]) Action {
					return By(atZeros.At(q))
				}))
			zeroSum := arg.Have(
				"so the sum over the zeros is that of the orders, weighted by the index",
				"Σ_{q∈«zeros»} «weighted»(q) = "+
					"Σ_{q∈«zeros»} winding_index(γ, γ', a, b, q) * &(&(complex_zero_order(f, q)))",
				By(zeroTerms, addition, monoidal.Congruence))
			poleTerms := arg.Have(
				"at a pole in S the residue is minus the order",
				Statement{
					Binders: "∀q:complex.",
					Hypotheses: []string{
						"q ∈ P ∩ S",
					},
					Conclusion: "«weighted»(q) = -(winding_index(γ, γ', a, b, q) * &(&(complex_pole_order(f, q))))",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					pole := d.Assume()
					d.Show(
						"multiplying the residue by the index",
						ByArith(atPoles.At(q), pole))
				}))
			keepsZero := arg.Have(
				"negation keeps 0",
				"-neutral_elem(complex_add) = neutral_elem(complex_add)",
				ByArith(comm_ring.NeutralAdd.Read(complex_field.CommRing)))
			keepsAddition := arg.Have(
				"and distributes over addition",
				"∀u v:complex. -(u + v) = -u + -v",
				ByArith())
			outside := arg.Have(
				"a pole outside S adds nothing, the path not winding about it",
				Statement{
					Binders: "∀p:complex.",
					Hypotheses: []string{
						"p ∈ P",
						"p ∉ P ∩ S",
					},
					Conclusion: "winding_index(γ, γ', a, b, p) * &(&(complex_pole_order(f, p))) = " +
						"neutral_elem(complex_add)",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Complex]("p")
					given := d.Assume()
					away := d.Have(
						"p is not in S",
						"p ∉ S",
						BySets(given))
					d.Show(
						"the index about p is 0",
						ByArith(
							away,
							open,
							convex,
							path,
							closed,
							inS,
							WindingOutsideConvex.At(S, γ, γPrime, a, b, p),
							comm_ring.NeutralAdd.Read(complex_field.CommRing)))
				}))
			poleSum := arg.Have(
				"so the sum over the poles in S is minus that of "+
					"the orders over all the poles, weighted by the index",
				"Σ_{q∈P ∩ S} «weighted»(q) = "+
					"-Σ_{q∈P} winding_index(γ, γ', a, b, q) * &(&(complex_pole_order(f, q)))",
				CalcEq(
					Leg(
						arg.TermAs[Complex](
							"Σ_{q∈P ∩ S} -(winding_index(γ, γ', a, b, q) * &(&(complex_pole_order(f, q))))"),
						"each residue there is minus the order",
						By(poleTerms, addition, monoidal.Congruence)),
					Leg(
						arg.TermAs[Complex]("-Σ_{q∈P ∩ S} winding_index(γ, γ', a, b, q) * &(&(complex_pole_order(f, q)))"),
						"negation comes out of the finite sum",
						By(
							polesInS,
							keepsZero,
							keepsAddition,
							addition,
							Where(
								monoidal.Homomorphic,
								"h",
								arg.TermAs[Fun[Complex, Complex]]("λu:complex. -u")))),
					FinalLeg(
						"and the poles outside S add nothing",
						By(
							outside,
							set_order.InterSubset.At(P, S),
							monoidal.Superset.At(
								arg.TermAs[Op[Complex]]("complex_add"),
								arg.TermAs[Set[Complex]]("P ∩ S"),
								P,
								arg.TermAs[Fun[Complex, Complex]](
									"λq:complex. winding_index(γ, γ', a, b, q) * &(&(complex_pole_order(f, q)))"))))))
			twoPiI := arg.TermAs[Complex]("&(&2 * pi) * complex_i")
			arg.Show(
				"so the integral is 2πi times the zeros' orders less the poles' orders, weighted by the index",
				ByArith(residue, Scaled(twoPiI, split), Scaled(twoPiI, zeroSum), Scaled(twoPiI, poleSum)))
		}),
})}

// ArgumentPrincipleHolomorphic — the argument principle with no poles: where
// f has a derivative f′ on a convex open set S and its zeros there are
// finitely many, f′/f integrates round a closed piecewise smooth path in S on
// which f has no zero to 2πi times the orders of the zeros, weighted by the
// winding index. It is the argument principle with the empty set of poles,
// over which the sum is 0.
var ArgumentPrincipleHolomorphic = argumentPrincipleHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "ArgumentPrincipleHolomorphic",
	Key:  "prop_dd489e5634976265",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). ∀f f':(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"«convex»(S)",
			"∀z:complex. z ∈ S ⇒ complex_derivative_at(f, z, f'(z))",
			"finite(«zeros»)",
			"«closedPathIn»(S, γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) ≠ &0",
		},
		Conclusion: "path_integral(λz:complex. f'(z) / f(z), γ, γ', a, b) = " +
			"&(&2 * pi) * " +
			"complex_i * " +
			"Σ_{z∈«zeros»} winding_index(γ, γ', a, b, z) * " +
			"&(&(complex_zero_order(f, z)))",
		Abbrev: Abbrev{
			{Name: "zeros", Text: "{z:complex | z ∈ S ∧ f(z) = &0}"},
			{Name: "noPoles", Text: "Σ_{p∈∅⟨A:complex⟩} winding_index(γ, γ', a, b, p) * " +
				"&(&(complex_pole_order(f, p)))"},
		},
	},
		func(
			arg *Argument,
			S *Expr[Set[Complex]],
			f, fPrime *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			open, convex, slope, finite, path, zeroFree Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			none := arg.TermAs[Set[Complex]]("∅")
			same := arg.Have(
				"off no poles, the zeros are those in S",
				"{z:complex | z ∈ S ∖ ∅ ∧ f(z) = &0} = «zeros»",
				BySets())
			vacuous := arg.Have(
				"with no poles, the argument principle's hypotheses on them hold",
				"finite(∅⟨A:complex⟩) ∧ ∀p:complex. p ∈ ∅ ⇒ «properPole»(f, p)",
				BySets(finite_set.FiniteRules))
			offNone := arg.Have(
				"and S off no poles is S, where f has its derivative, finitely many zeros and the path",
				"(∀z:complex. z ∈ S ∖ ∅ ⇒ complex_derivative_at(f, z, f'(z))) ∧ "+
					"finite({z:complex | z ∈ S ∖ ∅ ∧ f(z) = &0}) ∧ "+
					"«closedPathIn»(S ∖ ∅, γ, γ', a, b)",
				same.Rw(),
				BySets(slope, finite, path))
			general := arg.Have(
				"so by the argument principle with no poles, f′/f integrates to "+
					"2πi times the weighted orders of the zeros less a sum over no poles",
				"path_integral(λz:complex. f'(z) / f(z), γ, γ', a, b) = "+
					"&(&2 * pi) * "+
					"complex_i * "+
					"(Σ_{z∈«zeros»} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z))) - «noPoles»)",
				same.RwRev(),
				By(
					vacuous,
					offNone,
					open,
					convex,
					zeroFree,
					ArgumentPrinciple.At(S, f, fPrime, none, γ, γPrime, a, b)))
			empty := arg.Have(
				"a sum over no poles is 0",
				"«noPoles» = &0",
				ByArith(monoidal.Clauses.Read(addition), comm_ring.NeutralAdd.Read(complex_field.CommRing)))
			arg.Show(
				"so the poles' part is 0",
				ByArith(general, empty))
		}),
})}

// Rouche — Rouché's theorem: where f and g are holomorphic on a convex open
// set S with finitely many zeros there, and |f − g| < |f| all along a closed
// piecewise smooth path in S, the zeros of f and of g counted by order and
// weighted by the winding index agree. On the path neither f
// nor g is 0, and g/f lies within 1 of 1, so in the plane slit along the
// negative reals, where the logarithm has derivative 1/w. So log(g/f) is a
// primitive of g′/g − f′/f at the points of the path, and the integral of
// g′/g − f′/f round the closed path is 0; by the argument principle it is
// 2πi times the difference of the two weighted sums.
var Rouche = roucheThm{family.Add(registry.ProofEntry{
	Name: "Rouche",
	Key:  "prop_244f38ad59bb8944",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). ∀f g:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"«convex»(S)",
			"holomorphic_on(S, f)",
			"holomorphic_on(S, g)",
			"finite(«fZeros»)",
			"finite(«gZeros»)",
			"«closedPathIn»(S, γ, γ', a, b)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ |f(γ(t)) - g(γ(t))| < |f(γ(t))|",
		},
		Conclusion: "Σ_{z∈«fZeros»} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z))) = " +
			"Σ_{z∈«gZeros»} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(g, z)))",
		Abbrev: Abbrev{
			{Name: "fZeros", Text: "{z:complex | z ∈ S ∧ f(z) = &0}"},
			{Name: "gZeros", Text: "{z:complex | z ∈ S ∧ g(z) = &0}"},
			{Name: "ratio", Text: "λz:complex. g(z) / f(z)"},
			{Name: "quotientSlope", Text: "λz:complex. (g'(z) * f(z) - g(z) * f'(z)) / f(z) ^ 2"},
			{Name: "slope", Text: "λz:complex. g'(z) / g(z) - f'(z) / f(z)"},
		},
	},
		func(
			arg *Argument,
			S *Expr[Set[Complex]],
			f, g *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			open, convex, fHolomorphic, gHolomorphic, fFinite, gFinite, closedPath, near Fact,
		) {
			loop := arg.Conjuncts(
				closedPath,
				"γ is a piecewise smooth path on ⟦a, b⟧",
				"it is closed",
				"it stays in S")
			path, closed := loop[0], loop[1]
			fPrime, fDerived := arg.ObtainAs[Fun[Complex, Complex]](
				"f has a derivative f′ on S, itself holomorphic there",
				"∃f':(complex → complex). "+
					"    (∀z:complex. z ∈ S ⇒ complex_derivative_at(f, z, f'(z))) ∧ holomorphic_on(S, f')",
				By(open, fHolomorphic, cauchy_integral.HolomorphicDerivative),
				Named("f'"))
			fSlope := arg.Conjuncts(
				fDerived,
				"f′(z) is the derivative of f at each point z of S",
				"f′ is holomorphic on S")
			gPrime, gDerived := arg.ObtainAs[Fun[Complex, Complex]](
				"and g a derivative g′, holomorphic there too",
				"∃g':(complex → complex). "+
					"    (∀z:complex. z ∈ S ⇒ complex_derivative_at(g, z, g'(z))) ∧ holomorphic_on(S, g')",
				By(open, gHolomorphic, cauchy_integral.HolomorphicDerivative),
				Named("g'"))
			gSlope := arg.Conjuncts(
				gDerived,
				"g′(z) is the derivative of g at each point z of S",
				"g′ is holomorphic on S")
			slit := arg.Have(
				"where |u − v| < |u|, neither u nor v is 0, and v/u lies within 1 of 1, so in the slit plane",
				"∀u v:complex. |u - v| < |u| ⇒ u ≠ &0 ∧ v ≠ &0 ∧ v / u ∈ slit_plane",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					v := d.FixAs[Complex]("v")
					bound := d.Assume()
					uNonzero := d.Have(
						"u is not 0, |u| exceeding |u − v| ≥ 0",
						"u ≠ &0",
						ByArith(
							bound,
							complex_abs.AbsNonneg.At(d.TermAs[Complex]("u - v")),
							complex_abs.AbsPosIffNonzero.At(u)))
					vNonzero := d.Have(
						"v is not 0, |u| − |v| being at most |u − v| < |u|",
						"v ≠ &0",
						ByArith(bound, complex_abs.AbsTriangleReverse.At(u, v), complex_abs.AbsPosIffNonzero.At(v)))
					shifted := d.Have(
						"v/u − 1 is (v − u)/u",
						"v / u - &1 = (v - u) / u",
						ByArith(uNonzero))
					ratio := d.Have(
						"so |v − u|/|u| < 1",
						"|v - u| / |u| < &1",
						ByArith(uNonzero, bound, complex_abs.AbsSubComm.At(u, v), complex_abs.AbsPosIffNonzero.At(u)))
					within := d.Have(
						"v/u lies within 1 of 1",
						"|v / u - &1| < &1",
						ByArith(shifted, ratio, complex_abs.AbsDiv.At(d.TermAs[Complex]("v - u"), u)))
					d.Show(
						"so neither u nor v is 0, and v/u, within 1 of 1, lies in the slit plane",
						By(uNonzero, vNonzero, within, complex_log.SlitPlaneNearOne.At(d.TermAs[Complex]("v / u"))))
				}))
			onPath := arg.Have(
				"on the path f and g are not 0, and g/f is in the slit plane",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ S ∧ f(γ(t)) ≠ &0 ∧ g(γ(t)) ≠ &0 ∧ g(γ(t)) / f(γ(t)) ∈ slit_plane",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					d.Show(
						"since the path stays in S and |f − g| < |f| there",
						By(within, loop[2].At(t), near.At(t), slit.At(f.Apply(γ.Apply(t)), g.Apply(γ.Apply(t)))))
				}))
			fMissed := arg.Have(
				"so f has no zero on the path",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) ≠ &0",
				By(onPath))
			gMissed := arg.Have(
				"nor has g",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ g(γ(t)) ≠ &0",
				By(onPath))
			fCount := arg.Have(
				"by the argument principle, f′/f integrates to 2πi times the weighted count of the zeros of f",
				"path_integral(λz:complex. f'(z) / f(z), γ, γ', a, b) = "+
					"&(&2 * pi) * "+
					"complex_i * "+
					"Σ_{z∈«fZeros»} winding_index(γ, γ', a, b, z) * "+
					"&(&(complex_zero_order(f, z)))",
				By(
					open,
					convex,
					fSlope[0],
					fFinite,
					closedPath,
					fMissed,
					ArgumentPrincipleHolomorphic.At(S, f, fPrime, γ, γPrime, a, b)))
			gCount := arg.Have(
				"and g′/g to 2πi times that of the zeros of g",
				"path_integral(λz:complex. g'(z) / g(z), γ, γ', a, b) = "+
					"&(&2 * pi) * "+
					"complex_i * "+
					"Σ_{z∈«gZeros»} winding_index(γ, γ', a, b, z) * "+
					"&(&(complex_zero_order(g, z)))",
				By(
					open,
					convex,
					gSlope[0],
					gFinite,
					closedPath,
					gMissed,
					ArgumentPrincipleHolomorphic.At(S, g, gPrime, γ, γPrime, a, b)))
			ratioAlong := arg.Have(
				"a function holomorphic on S, with its derivative, and not 0 on "+
					"the path has a logarithmic derivative continuous along the path",
				Statement{
					Binders: "∀F F':(complex → complex).",
					Hypotheses: []string{
						"holomorphic_on(S, F)",
						"holomorphic_on(S, F')",
						"∀t:real. a ≤ t ∧ t ≤ b ⇒ F(γ(t)) ≠ &0",
					},
					Conclusion: "∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. F'(z) / F(z), γ(t))",
				},
				Derive(func(d *Argument) {
					F := d.FixAs[Fun[Complex, Complex]]("F")
					FPrime := d.FixAs[Fun[Complex, Complex]]("F'")
					parts := d.Conjuncts(
						d.Assume(),
						"F is holomorphic on S",
						"so is F′",
						"F is not 0 on the path")
					zeroFree := d.TermAs[Set[Complex]]("{z:complex | z ∈ S ∧ F(z) ≠ &0}")
					quotient := d.TermAs[Fun[Complex, Complex]]("λz:complex. F'(z) / F(z)")
					inside := d.Have(
						"the points of S where F is not 0 lie in S",
						"{z:complex | z ∈ S ∧ F(z) ≠ &0} ⊆ S",
						BySets())
					holomorphic := d.Have(
						"so F′/F is holomorphic there",
						"holomorphic_on({z:complex | z ∈ S ∧ F(z) ≠ &0}, λz:complex. F'(z) / F(z))",
						By(
							parts[0],
							parts[1],
							inside,
							complex_derivative.HolomorphicOnSubset.At(S, zeroFree, F),
							complex_derivative.HolomorphicOnSubset.At(S, zeroFree, FPrime),
							complex_derivative.HolomorphicOnDiv.At(zeroFree, FPrime, F)))
					t := d.FixAs[Real]("t")
					within := d.Assume()
					onIt := d.Have(
						"γ(t) is such a point",
						"γ(t) ∈ {z:complex | z ∈ S ∧ F(z) ≠ &0}",
						BySets(within, loop[2].At(t), parts[2].At(t)))
					d.Show(
						"so F′/F is continuous at γ(t)",
						By(
							onIt,
							holomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(
								zeroFree,
								quotient,
								γ.Apply(t))))
				}))
			fRatioAlong := arg.Have(
				"so f′/f is continuous along the path",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. f'(z) / f(z), γ(t))",
				By(fHolomorphic, fSlope[1], fMissed, ratioAlong.At(f, fPrime)))
			gRatioAlong := arg.Have(
				"and so is g′/g",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(λz:complex. g'(z) / g(z), γ(t))",
				By(gHolomorphic, gSlope[1], gMissed, ratioAlong.At(g, gPrime)))
			primitive := arg.Have(
				"at the points of the path, log(g/f) has the derivative g′/g − f′/f",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"a ≤ t",
						"t ≤ b",
					},
					Conclusion: "complex_derivative_at(λz:complex. complex_log(«ratio»(z)), γ(t), «slope»(γ(t)))",
				},
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					within := d.Assume()
					point := γ.Apply(t)
					facts := d.Conjuncts(
						GroupPremises(within, onPath.At(t)),
						"γ(t) is in S",
						"f(γ(t)) is not 0",
						"g(γ(t)) is not 0",
						"g(γ(t))/f(γ(t)) is in the slit plane")
					w := d.TermAs[Complex]("«ratio»(γ(t))")
					quotient := d.Have(
						"g/f has a derivative at γ(t), by the quotient rule",
						"complex_derivative_at(«ratio», γ(t), «quotientSlope»(γ(t)))",
						By(
							facts[0],
							facts[1],
							fSlope[0].At(point),
							gSlope[0].At(point),
							complex_derivative.DerivativeDiv.At(
								g,
								f,
								point,
								d.TermAs[Complex]("g'(γ(t))"),
								d.TermAs[Complex]("f'(γ(t))"))))
					composed := d.Unfolded(
						d.Have(
							"so log(g/f) has derivative (g/f)′/(g/f) there, by the "+
								"chain rule, log having the derivative 1/w in the slit plane",
							"complex_derivative_at(complex_log ∘ «ratio», "+
								"    γ(t), "+
								"    complex_inv(«ratio»(γ(t))) * «quotientSlope»(γ(t)))",
							By(
								quotient,
								facts[3],
								complex_log.LogDerivative.At(w),
								complex_derivative.DerivativeChain.At(
									d.TermAs[Fun[Complex, Complex]]("complex_log"),
									d.TermAs[Fun[Complex, Complex]]("«ratio»"),
									point,
									d.TermAs[Complex]("complex_inv(«ratio»(γ(t)))"),
									d.TermAs[Complex]("«quotientSlope»(γ(t))")))),
						functions.ComposeApply)
					product := d.Have(
						"(g′/g − f′/f)·(g/f) is the derivative of g/f",
						"«slope»(γ(t)) * «ratio»(γ(t)) = «quotientSlope»(γ(t))",
						Simp(
							Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
							Fwd(field.DivMulInv.Read(complex_field.Field)),
							Fwd(field.InvMul.Read(complex_field.Field))),
						ByArith(facts[1], facts[2]))
					wNonzero := d.Have(
						"g/f is not 0, being in the slit plane",
						"«ratio»(γ(t)) ≠ &0",
						By(facts[3], complex_log.SlitPlaneAbsPos.At(w), complex_abs.AbsPosIffNonzero.At(w)))
					unit := d.Have(
						"so 1/(g/f) times g/f is 1",
						"complex_inv(«ratio»(γ(t))) * «ratio»(γ(t)) = &1",
						ByArith(wNonzero))
					value := d.Have(
						"so the derivative is g′/g − f′/f",
						"complex_inv(«ratio»(γ(t))) * «quotientSlope»(γ(t)) = «slope»(γ(t))",
						ByArith(
							Scaled(d.TermAs[Complex]("«slope»(γ(t))"), unit),
							Scaled(d.TermAs[Complex]("complex_inv(«ratio»(γ(t)))"), product)))
					d.Show(
						"so log(g/f) has the derivative g′/g − f′/f at γ(t)",
						By(composed, value))
				}))
			slopeAlong := arg.Have(
				"g′/g − f′/f is continuous at the points of the path",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(«slope», γ(t))",
				By(gRatioAlong, fRatioAlong, complex_topology.ContinuousAtSub))
			change := arg.Have(
				"so its integral round the path is the change of log(g/f) between the path's ends",
				"path_integral(«slope», γ, γ', a, b) = "+
					"complex_log(g(γ(b)) / f(γ(b))) - complex_log(g(γ(a)) / f(γ(a)))",
				By(
					path,
					primitive,
					slopeAlong,
					path_integral.PathIntegralPrimitive.At(
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_log(«ratio»(z))"),
						arg.TermAs[Fun[Complex, Complex]]("«slope»"),
						γ,
						γPrime,
						a,
						b)))
			ends := arg.Have(
				"the path being closed, log(g/f) takes one value at its two ends",
				"complex_log(g(γ(b)) / f(γ(b))) = complex_log(g(γ(a)) / f(γ(a)))",
				closed.Rw(),
				Basic())
			vanishes := arg.Have(
				"so the integral is 0",
				"path_integral(«slope», γ, γ', a, b) = &0",
				ByArith(change, ends))
			difference := arg.Have(
				"and it is the integral of g′/g less that of f′/f",
				"path_integral(«slope», γ, γ', a, b) = "+
					"path_integral(λz:complex. g'(z) / g(z), γ, γ', a, b) - "+
					"path_integral(λz:complex. f'(z) / f(z), γ, γ', a, b)",
				By(
					path,
					gRatioAlong,
					fRatioAlong,
					path_integral.PathIntegralSub.At(
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. g'(z) / g(z)"),
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. f'(z) / f(z)"),
						γ,
						γPrime,
						a,
						b)))
			arg.Show(
				"so 2πi times the two weighted counts agree, and 2πi is not 0",
				ByArith(
					path_integral.TwoPiINonzero,
					Scaled(arg.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)"), vanishes),
					Scaled(arg.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)"), difference),
					Scaled(arg.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)"), fCount),
					Scaled(arg.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)"), gCount)))
		}),
})}

// RoucheCircle — Rouché's theorem on a circle: where f and g are holomorphic
// on the disc of radius R about c, and |f − g| < |f| on the circle of radius
// r < R about c, f and g have as many zeros inside the circle, counted with
// their orders. Neither f nor g is 0 on the circle, so neither vanishes
// throughout the disc, and each has finitely many zeros in the closed disc
// of radius ρ = (r + R)/2 (ZerosFiniteInClosedDisc). Round the circle, a
// closed path in the open disc of radius ρ, Rouché's theorem equates the two
// index-weighted counts there; no zero lies on the circle, which winds once
// about each zero inside and not about one outside (WindingCircleCount). A
// circle of negative radius encloses nothing.
var RoucheCircle = roucheCircleThm{family.Add(registry.ProofEntry{
	Name: "RoucheCircle",
	Key:  "prop_2d4c90a6fa1c25cd",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"holomorphic_on(«disc»(c, R), g)",
			"r < R",
			"∀z:complex. |z - c| = r ⇒ |f(z) - g(z)| < |f(z)|",
		},
		Conclusion: "Σ_{z∈«zeros»(f, r)} complex_zero_order(f, z) = " +
			"Σ_{z∈«zeros»(g, r)} complex_zero_order(g, z)",
		Abbrev: Abbrev{
			{Name: "zeros", Text: "λh:(complex → complex). λs:real. " +
				"    {z:complex | z ∈ «disc»(c, s) ∧ h(z) = &0}"},
		},
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			fHolomorphic, gHolomorphic, smaller, near Fact,
		) {
			nonneg := arg.Assuming(
				arg.TermAs[Bool]("&0 ≤ r"),
				"a circle of negative radius encloses nothing, and both sums are over nothing",
				Given(func(b *Argument, negative Fact) {
					none := b.Have(
						"no point lies within r of c",
						"∀z:complex. ¬(|z - c| < r)",
						Derive(func(d *Argument) {
							d.FixAs[Complex]("z")
							d.Show(
								"a distance is never negative",
								ByArith(negative, complex_abs.AbsNonneg.At(d.TermAs[Complex]("z - c"))))
						}))
					empty := b.Conjuncts(
						b.Have(
							"so no zero of f or of g lies inside",
							"«zeros»(f, r) = ∅ ∧ «zeros»(g, r) = ∅",
							BySets(none)),
						"none of f",
						"none of g")
					b.Show(
						"and both sums, over the empty set, are 0",
						empty[0].Rw(),
						empty[1].Rw(),
						By(nat_sum.Clauses))
				}))
			ρ, ρDef := arg.LetAs[Real]("ρ", "(r + R) / &2")
			inner := arg.TermAs[Set[Complex]]("«disc»(c, ρ)")
			radii := arg.Conjuncts(
				arg.Have(
					"ρ lies between r and R",
					"(∀z:complex. |z - c| < r ⇒ |z - c| < ρ) ∧ "+
						"(∀z:complex. |z - c| = r ⇒ |z - c| < ρ) ∧ "+
						"(∀z:complex. |z - c| < ρ ⇒ |z - c| < R ∧ |z - c| ≤ ρ) ∧ "+
						"ρ < R",
					ByArith(ρDef, smaller)),
				"a point within r of c lies within ρ of it",
				"so does a point at distance r",
				"a point within ρ of c lies within R of it, and at most ρ from it",
				"ρ is below R")
			nonvanishing := arg.Have(
				"on the circle neither f nor g is 0: |f| exceeds |f − g| ≥ 0, and |g| ≥ |f| − |f − g| > 0",
				"∀z:complex. |z - c| = r ⇒ f(z) ≠ &0 ∧ g(z) ≠ &0",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					on := d.Assume()
					fz := d.TermAs[Complex]("f(z)")
					gz := d.TermAs[Complex]("g(z)")
					d.Show(
						"|f(z)| and |g(z)| are positive",
						ByArith(
							on,
							near.At(z),
							complex_abs.AbsNonneg.At(d.TermAs[Complex]("f(z) - g(z)")),
							complex_abs.AbsTriangleReverse.At(fz, gz),
							complex_abs.AbsPosIffNonzero.At(fz),
							complex_abs.AbsPosIffNonzero.At(gz)))
				}))
			w := arg.TermAs[Complex]("circle_path(c, r, &0)")
			onIt := arg.Conjuncts(
				arg.Have(
					"the point w = circle_path(c, r, 0) lies on the circle, within R of c",
					"|circle_path(c, r, &0) - c| = r ∧ |circle_path(c, r, &0) - c| < R",
					ByArith(nonneg, smaller, path_integral.CirclePathRadius.At(c, r, arg.TermAs[Real]("&0")))),
				"w lies on the circle",
				"and within R of c")
			restricted := arg.Have(
				"a function holomorphic on the disc of radius R and not 0 at w is "+
					"holomorphic on the disc of radius ρ, with finitely many zeros there",
				Statement{
					Binders: "∀h:(complex → complex).",
					Hypotheses: []string{
						"holomorphic_on(«disc»(c, R), h)",
						"h(circle_path(c, r, &0)) ≠ &0",
					},
					Conclusion: "holomorphic_on(«disc»(c, ρ), h) ∧ finite(«zeros»(h, ρ))",
				},
				Derive(func(d *Argument) {
					h := d.FixAs[Fun[Complex, Complex]]("h")
					given := d.Conjuncts(
						d.Assume(),
						"h is holomorphic on the disc of radius R",
						"h is not 0 at w")
					somewhere := d.Have(
						"h does not vanish throughout the disc, not being 0 at w",
						"¬(∀z:complex. |z - c| < R ⇒ h(z) = &0)",
						By(given[1], onIt[1]))
					closed := d.Have(
						"so it has finitely many zeros in the closed disc of radius ρ",
						"finite({z:complex | |z - c| ≤ ρ ∧ h(z) = &0})",
						By(given[0], radii[3], somewhere, cauchy_integral.ZerosFiniteInClosedDisc.At(h, c, R, ρ)))
					nested := d.Have(
						"the disc of radius ρ lies in that of radius R, and the zeros of h in it in the closed disc",
						"«disc»(c, ρ) ⊆ «disc»(c, R) ∧ «zeros»(h, ρ) ⊆ {z:complex | |z - c| ≤ ρ ∧ h(z) = &0}",
						BySets(radii[2]))
					d.Show(
						"so h is holomorphic on the smaller disc, and its zeros there are finitely many",
						By(
							given[0],
							closed,
							nested,
							complex_derivative.HolomorphicOnSubset.At(d.TermAs[Set[Complex]]("«disc»(c, R)"), inner, h),
							finite_set.FiniteSubset.At(
								d.TermAs[Set[Complex]]("«zeros»(h, ρ)"),
								d.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ ρ ∧ h(z) = &0}"))))
				}))
			atW := arg.Conjuncts(
				GroupPremises(onIt[0], nonvanishing.At(w)),
				"so f is not 0 at w",
				"nor is g")
			fInner := arg.Conjuncts(
				GroupPremises(fHolomorphic, atW[0], restricted.At(f)),
				"f is holomorphic on the disc of radius ρ",
				"with finitely many zeros there")
			gInner := arg.Conjuncts(
				GroupPremises(gHolomorphic, atW[1], restricted.At(g)),
				"g is holomorphic on the disc of radius ρ",
				"with finitely many zeros there")
			onDisc := arg.Have(
				"the circle lies in the disc of radius ρ",
				"∀z:complex. |z - c| = r ⇒ z ∈ «disc»(c, ρ)",
				BySets(radii[1]))
			loop := arg.Have(
				"so it is a closed path there",
				"«closedPathIn»(«disc»(c, ρ), "+
					"    circle_path(c, r), "+
					"    λt:real. complex_i * &r * exp(complex_i * &t), "+
					"    &0, "+
					"    &2 * pi)",
				By(nonneg, onDisc, CircleClosedPathIn.At(c, r, inner)))
			along := arg.Have(
				"and on it |f − g| < |f|",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &2 * pi",
					},
					Conclusion: "|f(circle_path(c, r, t)) - g(circle_path(c, r, t))| < |f(circle_path(c, r, t))|",
				},
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					d.Assume()
					radius := d.Have(
						"circle_path(c, r, t) lies at distance r from c",
						"|circle_path(c, r, t) - c| = r",
						ByArith(nonneg, path_integral.CirclePathRadius.At(c, r, t)))
					d.Show(
						"where |f − g| < |f|",
						By(radius, near.At(d.TermAs[Complex]("circle_path(c, r, t)"))))
				}))
			weighted := arg.Have(
				"by Rouché's theorem round the circle, the index-weighted "+
					"counts of the zeros in the disc of radius ρ agree",
				"Σ_{z∈«zeros»(f, ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(f, z))) = "+
					"Σ_{z∈«zeros»(g, ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(g, z)))",
				By(
					complex_topology.DiscOpen.At(c, ρ),
					At(cauchy_integral.DiscConvex, c, ρ),
					fInner[0],
					gInner[0],
					fInner[1],
					gInner[1],
					loop,
					along,
					Rouche.At(
						inner,
						f,
						g,
						arg.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						arg.TermAs[Real]("&0"),
						arg.TermAs[Real]("&2 * pi"))))
			off := arg.Conjuncts(
				arg.Have(
					"no zero of f or of g lies on the circle",
					"(∀z:complex. z ∈ «zeros»(f, ρ) ⇒ |z - c| ≠ r) ∧ (∀z:complex. z ∈ «zeros»(g, ρ) ⇒ |z - c| ≠ r)",
					BySets(nonvanishing)),
				"none of f",
				"none of g")
			inside := arg.Conjuncts(
				arg.Have(
					"the zeros in the disc of radius ρ within r of c are those inside the circle",
					"«zeros»(f, ρ) ∩ «disc»(c, r) = «zeros»(f, r) ∧ «zeros»(g, ρ) ∩ «disc»(c, r) = «zeros»(g, r)",
					BySets(radii[0])),
				"those of f",
				"those of g")
			fCount := arg.Have(
				"so the weighted count for f is the number of its zeros inside, with their orders",
				"Σ_{z∈«zeros»(f, ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(f, z))) = "+
					"&(&(Σ_{z∈«zeros»(f, r)} complex_zero_order(f, z)))",
				inside[0].RwRev(),
				By(
					nonneg,
					fInner[1],
					off[0],
					WindingCircleCount.At(
						c,
						r,
						arg.TermAs[Set[Complex]]("«zeros»(f, ρ)"),
						arg.TermAs[Fun[Complex, Nat]]("λz:complex. complex_zero_order(f, z)"))))
			gCount := arg.Have(
				"and likewise for g",
				"Σ_{z∈«zeros»(g, ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(g, z))) = "+
					"&(&(Σ_{z∈«zeros»(g, r)} complex_zero_order(g, z)))",
				inside[1].RwRev(),
				By(
					nonneg,
					gInner[1],
					off[1],
					WindingCircleCount.At(
						c,
						r,
						arg.TermAs[Set[Complex]]("«zeros»(g, ρ)"),
						arg.TermAs[Fun[Complex, Nat]]("λz:complex. complex_zero_order(g, z)"))))
			arg.Show(
				"so the two counts are equal, the cast of ℕ into ℂ being one to one",
				By(
					weighted,
					fCount,
					gCount,
					complex_field.OfRealInjective.At(
						arg.TermAs[Real]("&(Σ_{z∈«zeros»(f, r)} complex_zero_order(f, z))"),
						arg.TermAs[Real]("&(Σ_{z∈«zeros»(g, r)} complex_zero_order(g, z))")),
					real_construction.OfNumEq.At(
						arg.TermAs[Nat]("Σ_{z∈«zeros»(f, r)} complex_zero_order(f, z)"),
						arg.TermAs[Nat]("Σ_{z∈«zeros»(g, r)} complex_zero_order(g, z)"))))
		}),
})}

// ArgumentPrincipleCircle — the argument principle on a circle: where f has
// a derivative f′ on the disc of radius R about c off the set P of its
// poles, each a genuine pole, and no zero or pole lies on the circle of
// radius r about c, 0 ≤ r < R, f′/f integrates round the circle to 2πi
// times the number of zeros less the number of poles inside it, each counted
// with its order. f is not 0 on the circle, so not throughout the disc off
// the poles; in the closed disc of radius ρ = (r + R)/2 the poles are then
// finitely many (PolesFiniteInClosedDisc), and so are the zeros off them
// (ZerosFiniteOffPoles). The open disc of radius ρ is convex and holds the
// circle, so the argument principle applies there with the poles inside it;
// the circle winds once about each point inside and not about one outside
// (WindingCircleCount).
var ArgumentPrincipleCircle = argumentPrincipleCircleThm{family.Add(registry.ProofEntry{
	Name: "ArgumentPrincipleCircle",
	Key:  "prop_43951c7a558f7189",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(complex → complex). ∀c:complex. ∀R r:real. ∀P:set(complex).",
		Hypotheses: []string{
			"&0 ≤ r",
			"r < R",
			"∀z:complex. z ∈ «disc»(c, R) ∖ P ⇒ complex_derivative_at(f, z, f'(z))",
			"∀p:complex. p ∈ P ⇒ «properPole»(f, p)",
			"∀z:complex. |z - c| = r ⇒ z ∉ P ∧ f(z) ≠ &0",
		},
		Conclusion: "«circleInt»(λz:complex. f'(z) / f(z), c, r) = " +
			"&(&2 * pi) * " +
			"complex_i * " +
			"(&(&(Σ_{z∈«zeros»(r)} complex_zero_order(f, z))) - " +
			"    &(&(Σ_{p∈P ∩ «disc»(c, r)} complex_pole_order(f, p))))",
		Abbrev: Abbrev{
			{Name: "zeros", Text: "λs:real. {z:complex | z ∈ «disc»(c, s) ∖ P ∧ f(z) = &0}"},
			{Name: "zerosOff", Text: "λs:real. " +
				"    {z:complex | z ∈ «disc»(c, s) ∖ (P ∩ «disc»(c, s)) ∧ f(z) = &0}"},
		},
	},
		func(
			arg *Argument,
			f, fPrime *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			P *Expr[Set[Complex]],
			nonneg, smaller, slope, poles, offCircle Fact,
		) {
			ρ, ρDef := arg.LetAs[Real]("ρ", "(r + R) / &2")
			S := arg.TermAs[Set[Complex]]("«disc»(c, ρ)")
			inner := arg.TermAs[Set[Complex]]("P ∩ «disc»(c, ρ)")
			radii := arg.Conjuncts(
				arg.Have(
					"ρ lies between r and R",
					"(∀z:complex. |z - c| < r ⇒ |z - c| < ρ) ∧ "+
						"(∀z:complex. |z - c| = r ⇒ |z - c| < ρ) ∧ "+
						"(∀z:complex. |z - c| < ρ ⇒ |z - c| < R ∧ |z - c| ≤ ρ) ∧ "+
						"ρ < R",
					ByArith(ρDef, smaller)),
				"a point within r of c lies within ρ of it",
				"so does a point at distance r",
				"a point within ρ of c lies within R of it, and at most ρ from it",
				"ρ is below R")
			holomorphic := arg.Have(
				"f is holomorphic on the disc of radius R off the poles, having the derivative f′ there",
				"holomorphic_on(«disc»(c, R) ∖ P, f)",
				Unfold(complex_derivative.HolomorphicOnDef),
				arg.ForEach(func(z *Expr[Complex]) Action {
					return By(slope.At(z))
				}))
			w := arg.TermAs[Complex]("circle_path(c, r, &0)")
			onIt := arg.Have(
				"the point w = circle_path(c, r, 0) lies on the circle, within R of c",
				"|circle_path(c, r, &0) - c| = r ∧ |circle_path(c, r, &0) - c| < R",
				ByArith(nonneg, smaller, path_integral.CirclePathRadius.At(c, r, arg.TermAs[Real]("&0"))))
			somewhere := arg.Have(
				"f is not 0 throughout the disc off the poles, w lying there with f(w) ≠ 0",
				"¬(∀z:complex. z ∈ «disc»(c, R) ∖ P ⇒ f(z) = &0)",
				BySets(onIt, offCircle.At(w)))
			finitely := arg.Conjuncts(
				arg.Have(
					"in the closed disc of radius ρ the poles are finitely many, and so are the zeros off them",
					"finite({p:complex | p ∈ P ∧ |p - c| ≤ ρ}) ∧ finite({z:complex | |z - c| ≤ ρ ∧ z ∉ P ∧ f(z) = &0})",
					By(
						holomorphic,
						poles,
						radii[3],
						somewhere,
						PolesFiniteInClosedDisc.At(f, c, R, ρ, P),
						ZerosFiniteOffPoles.At(f, c, R, ρ, P))),
				"the poles",
				"the zeros")
			within := arg.Have(
				"the poles in the open disc of radius ρ lie in the closed one, and so do the zeros there off them",
				"P ∩ «disc»(c, ρ) ⊆ {p:complex | p ∈ P ∧ |p - c| ≤ ρ} ∧ "+
					"«zerosOff»(ρ) ⊆ {z:complex | |z - c| ≤ ρ ∧ z ∉ P ∧ f(z) = &0}",
				BySets(radii[2]))
			bothFinite := arg.Have(
				"so they are finitely many",
				"finite(P ∩ «disc»(c, ρ)) ∧ finite(«zerosOff»(ρ))",
				By(
					finitely[0],
					finitely[1],
					within,
					finite_set.FiniteSubset.At(inner, arg.TermAs[Set[Complex]]("{p:complex | p ∈ P ∧ |p - c| ≤ ρ}")),
					finite_set.FiniteSubset.At(
						arg.TermAs[Set[Complex]]("«zerosOff»(ρ)"),
						arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ ρ ∧ z ∉ P ∧ f(z) = &0}"))))
			restricted := arg.Have(
				"in the disc of radius ρ, off its poles, f has the derivative f′, and those poles are genuine",
				"(∀z:complex. z ∈ «disc»(c, ρ) ∖ (P ∩ «disc»(c, ρ)) ⇒ complex_derivative_at(f, z, f'(z))) ∧ "+
					"(∀p:complex. p ∈ P ∩ «disc»(c, ρ) ⇒ «properPole»(f, p))",
				BySets(radii[2], slope, poles))
			onDisc := arg.Have(
				"the circle lies in the disc of radius ρ off the poles",
				"∀z:complex. |z - c| = r ⇒ z ∈ «disc»(c, ρ) ∖ (P ∩ «disc»(c, ρ))",
				BySets(radii[1], offCircle))
			loop := arg.Have(
				"so it is a closed path there",
				"«closedPathIn»(«disc»(c, ρ) ∖ (P ∩ «disc»(c, ρ)), "+
					"    circle_path(c, r), "+
					"    λt:real. complex_i * &r * exp(complex_i * &t), "+
					"    &0, "+
					"    &2 * pi)",
				By(
					nonneg,
					onDisc,
					CircleClosedPathIn.At(c, r, arg.TermAs[Set[Complex]]("«disc»(c, ρ) ∖ (P ∩ «disc»(c, ρ))"))))
			along := arg.Have(
				"and f has no zero on it",
				"∀t:real. &0 ≤ t ∧ t ≤ &2 * pi ⇒ f(circle_path(c, r, t)) ≠ &0",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					d.Assume()
					radius := d.Have(
						"circle_path(c, r, t) lies at distance r from c",
						"|circle_path(c, r, t) - c| = r",
						ByArith(nonneg, path_integral.CirclePathRadius.At(c, r, t)))
					d.Show(
						"where f is not 0",
						By(radius, offCircle.At(d.TermAs[Complex]("circle_path(c, r, t)"))))
				}))
			weighted := arg.Have(
				"by the argument principle round the circle in the disc of radius ρ",
				"«circleInt»(λz:complex. f'(z) / f(z), c, r) = "+
					"&(&2 * pi) * "+
					"complex_i * "+
					"(Σ_{z∈«zerosOff»(ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(f, z))) - "+
					"    Σ_{p∈P ∩ «disc»(c, ρ)} «circleIndex»(c, r, p) * &(&(complex_pole_order(f, p))))",
				By(
					complex_topology.DiscOpen.At(c, ρ),
					At(cauchy_integral.DiscConvex, c, ρ),
					bothFinite,
					restricted,
					loop,
					along,
					ArgumentPrinciple.At(
						S,
						f,
						fPrime,
						inner,
						arg.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						arg.TermAs[Real]("&0"),
						arg.TermAs[Real]("&2 * pi"))))
			off := arg.Conjuncts(
				arg.Have(
					"no zero and no pole lies on the circle",
					"(∀z:complex. z ∈ «zerosOff»(ρ) ⇒ |z - c| ≠ r) ∧ (∀p:complex. p ∈ P ∩ «disc»(c, ρ) ⇒ |p - c| ≠ r)",
					BySets(offCircle)),
				"no zero",
				"no pole")
			inside := arg.Conjuncts(
				arg.Have(
					"those within r of c are the zeros and the poles inside the circle",
					"«zerosOff»(ρ) ∩ «disc»(c, r) = «zeros»(r) ∧ (P ∩ «disc»(c, ρ)) ∩ «disc»(c, r) = P ∩ «disc»(c, r)",
					BySets(radii[0])),
				"the zeros",
				"the poles")
			finiteParts := arg.Conjuncts(
				bothFinite,
				"the poles in the disc of radius ρ are finitely many",
				"and so are the zeros there off them")
			zeroCount := arg.Have(
				"so the weighted count of the zeros is the number inside, with their orders",
				"Σ_{z∈«zerosOff»(ρ)} «circleIndex»(c, r, z) * &(&(complex_zero_order(f, z))) = "+
					"&(&(Σ_{z∈«zeros»(r)} complex_zero_order(f, z)))",
				inside[0].RwRev(),
				By(
					nonneg,
					finiteParts[1],
					off[0],
					WindingCircleCount.At(
						c,
						r,
						arg.TermAs[Set[Complex]]("«zerosOff»(ρ)"),
						arg.TermAs[Fun[Complex, Nat]]("λz:complex. complex_zero_order(f, z)"))))
			poleCount := arg.Have(
				"and that of the poles the number inside, with their orders",
				"Σ_{p∈P ∩ «disc»(c, ρ)} «circleIndex»(c, r, p) * &(&(complex_pole_order(f, p))) = "+
					"&(&(Σ_{p∈P ∩ «disc»(c, r)} complex_pole_order(f, p)))",
				inside[1].RwRev(),
				By(
					nonneg,
					finiteParts[0],
					off[1],
					WindingCircleCount.At(
						c, r, inner, arg.TermAs[Fun[Complex, Nat]]("λp:complex. complex_pole_order(f, p)"))))
			twoPiI := arg.TermAs[Complex]("&(&2 * pi) * complex_i")
			arg.Show(
				"so the integral is 2πi times the zeros less the poles inside",
				ByArith(weighted, Scaled(twoPiI, zeroCount), Scaled(twoPiI, poleCount)))
		}),
})}
