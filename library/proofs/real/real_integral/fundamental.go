// fundamental.go — the fundamental theorem of calculus and what follows
// from it: the integral of a derivative over ⟦a, b⟧ is the increment of
// the function across it — finitely many points where the derivative
// fails change nothing — the integral of a continuous function has the
// function as the derivative in its upper bound, and so integrals change
// by parts and under a substitution.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// NewtonLeibniz — a function F continuous on ⟦a, b⟧ with derivative f
// strictly between a and b: when f has an integral over ⟦a, b⟧, that
// integral is F(b) − F(a). Were it some other I, take a partition of
// ⟦a, b⟧ finer than the mesh the integral hands over at
// ε = |I − (F(b) − F(a))|. The mean value theorem tags each piece at a
// point where f times the piece's length is the increment of F across
// it (a piece of length zero at its left end), and at these tags the
// Riemann sum telescopes to F(b) − F(a) while lying within ε of I.
var NewtonLeibniz = newtonLeibnizThm{family.Add(registry.ProofEntry{
	Name: "NewtonLeibniz",
	Key:  "prop_e23e058c95927e20",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, F)",
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(F, x, f(x))",
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "I = F(b) - F(a)",
	},
		func(
			arg *Argument,
			F, f *Arrow[Real, Real],
			a, b, I *Expr[Real],
			continuous, derivative, toI Fact,
		) {
			integral := arg.Conjuncts(
				arg.Unfolded(toI, RealHasIntegralDef),
				"the interval is ordered",
				"for every ε some mesh brings the Riemann sums of f within ε of I")
			apart := arg.SupposeNot()
			gap := arg.Have(
				"I and F(b) − F(a) lie a positive distance apart",
				"&0 < |I - (F(b) - F(a))|",
				ByArith(apart))
			δ, fine := arg.ObtainAs[Real](
				"at ε = |I − (F(b) − F(a))| the integral hands over a mesh δ",
				"∃δ:real. "+
					"    &0 < δ ∧ "+
					"    (∀n:num. ∀p t:(num → real). "+
					"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < |I - (F(b) - F(a))|)",
				By(integral[1].At(arg.TermAs[Real]("|I - (F(b) - F(a))|")), gap))
			mesh := arg.Conjuncts(
				fine,
				"δ is positive",
				"below δ every Riemann sum of f is within |I − (F(b) − F(a))| of I")
			n, p, t, partition := arg.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
				"⟦a, b⟧ has a tagged partition finer than δ",
				"∃n:num. ∃p t:(num → real). «finePartition»(a, b, δ, n, p, t)",
				By(FinePartitionExists, integral[0], mesh[0]))
			pieces := arg.Conjuncts(
				partition,
				"the points start at a",
				"and end at b",
				"each tag lies in its piece, and each piece is shorter than δ")
			meanValue := arg.Have(
				"on each piece some point ξ has f(ξ) times the "+
					"piece's length equal to the increment of F across it",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ≤ n",
					},
					Conclusion: "∃ξ:real. p(k) ≤ ξ ∧ ξ ≤ p(k + 1) ∧ F(p(k + 1)) - F(p(k)) = f(ξ) * (p(k + 1) - p(k))",
				},
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]()
					inside := c.Assume()
					ends := c.Have(
						"the piece lies in ⟦a, b⟧, p being a partition of ⟦a, b⟧",
						"a ≤ p(k) ∧ p(k) ≤ p(k + 1) ∧ p(k + 1) ≤ b",
						By(
							FinePartitionIsPartition.At(a, b, δ, n, p, t),
							PartitionPiecesInInterval.At(a, b, n, p, k),
							partition,
							inside))
					c.Cases(c.Term("p(k) < p(k + 1)"))
					c.When(
						"a piece of positive length: the mean value theorem on ⟦p(k), p(k + 1)⟧",
						func(d *Argument, longer Fact) {
							ξ, between := d.ObtainAs[Real](
								"the increment of F across the piece is f(ξ) times its length at some ξ strictly inside it",
								"∃ξ:real. p(k) < ξ ∧ ξ < p(k + 1) ∧ F(p(k + 1)) - F(p(k)) = f(ξ) * (p(k + 1) - p(k))",
								By(
									real_derivative.MeanValueBetween.At(F, f, a, b, d.TermAs[Real]("p(k)"), d.TermAs[Real]("p(k + 1)")),
									continuous,
									derivative,
									ends,
									longer))
							d.Take(ξ)
							d.Show(
								"ξ lies in the piece",
								ByArith(between))
						})
					c.Otherwise(
						"a piece of length zero: its left end serves",
						func(d *Argument, flat Fact) {
							same := d.Have(
								"the piece's two ends agree",
								"p(k + 1) = p(k)",
								ByArith(flat, ends))
							d.Take(d.TermAs[Real]("p(k)"))
							d.Show(
								"the increment of F across the piece and the piece's length are both zero",
								ByArith(same))
						})
				}))
			z, tags := arg.ObtainAs[Fun[Nat, Real]](
				"choosing such a point on every piece tags the partition at z",
				"∃z:(num → real). ∀k:num. "+
					"    k ≤ n ⇒ p(k) ≤ z(k) ∧ z(k) ≤ p(k + 1) ∧ F(p(k + 1)) - F(p(k)) = f(z(k)) * (p(k + 1) - p(k))",
				Derive(func(c *Argument) {
					c.Take(c.TermAs[Fun[Nat, Real]](
						"λk:num. εξ:real. p(k) ≤ ξ ∧ ξ ≤ p(k + 1) ∧ F(p(k + 1)) - F(p(k)) = f(ξ) * (p(k + 1) - p(k))"))
					c.Show(
						"the point chosen on each piece is one the mean value theorem gives",
						By(Normalized, meanValue))
				}))
			fineAtZ := arg.Have(
				"tagged at z, every piece is still shorter than δ",
				"∀k:num. k ≤ n ⇒ p(k) ≤ z(k) ∧ z(k) ≤ p(k + 1) ∧ p(k + 1) - p(k) < δ",
				arg.ForEach(func(k *Expr[Nat]) Action {
					return ByArith(tags.At(k), pieces[2].At(k))
				}))
			zero := arg.TermAs[Nat]("0")
			telescope := arg.Have(
				"at z the Riemann sum adds up the increments of F "+
					"across the pieces, which telescope to F(b) − F(a)",
				"«riemannSum»(f, n, p, z) = F(b) - F(a)",
				By(
					tags,
					pieces[0],
					pieces[1],
					real_sum.IntervalCongruence.At(
						zero,
						n,
						arg.TermAs[Fun[Nat, Real]]("λk:num. f(z(k)) * (p(k + 1) - p(k))"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. F(p(k + 1)) - F(p(k))")),
					real_sum.TelescopeUp.At(zero, n, arg.TermAs[Fun[Nat, Real]]("λk:num. F(p(k))")),
					nat_order.ZeroLessEq.At(n)))
			arg.Show(
				"so F(b) − F(a) lies within |I − (F(b) − F(a))| of I, closer than it is",
				ByArith(mesh[1].At(n, p, z), pieces[0], pieces[1], fineAtZ, telescope))
		}),
})}

// NewtonLeibnizOffFinite — the Newton–Leibniz theorem with finitely many
// exceptional points: F continuous on ⟦a, b⟧ with derivative f strictly
// between a and b off a finite set k, any integral f has over ⟦a, b⟧ is
// F(b) − F(a).
//
// By induction on k, for every interval at once. With no exceptional
// point it is the Newton–Leibniz theorem. With one more, c: when c lies
// inside the interval, split it at c — f has an integral on each side, the
// two adding up to the one over the whole, and on each side every
// exceptional point is one of the rest, so each integral is the increment
// of F across its side; when c lies outside, it is no exceptional point of
// the interval at all.
var NewtonLeibnizOffFinite = newtonLeibnizOffFiniteThm{family.Add(registry.ProofEntry{
	Name: "NewtonLeibnizOffFinite",
	Key:  "prop_98133312f18ae8a7",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(real → real). ∀a b I:real. ∀k:set(real).",
		Hypotheses: []string{
			"finite(k)",
			"real_continuous_on(⟦a, b⟧, F)",
			"∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ real_derivative_at(F, t, f(t))",
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "I = F(b) - F(a)",
	},
		func(
			arg *Argument,
			F, f *Arrow[Real, Real],
			a, b, I *Expr[Real],
			k *Expr[Set[Real]],
			finite, continuous, derivative, toI Fact,
		) {
			// The property the induction carries: on every interval where F
			// is continuous with derivative f off s strictly inside, an
			// integral of f is the increment of F.
			incrementOff := arg.TermAs[Set[Set[Real]]](
				"λs:set(real). ∀u v J:real. " +
					"    real_continuous_on(⟦u, v⟧, F) ∧ " +
					"    (∀t:real. u < t ∧ t < v ∧ t ∉ s ⇒ real_derivative_at(F, t, f(t))) ∧ " +
					"    real_has_integral(f, u, v, J) ⇒ " +
					"    J = F(v) - F(u)")
			arg.Show(
				"the induction carries the property to k, which is finite",
				ByInduction(finite_set.FiniteInduct.At(incrementOff, k), finite, continuous, derivative, toI,
					Case(
						"with no exceptional point it is the Newton–Leibniz theorem",
						Derive(func(h *Argument) {
							u := h.FixAs[Real]("u")
							v := h.FixAs[Real]("v")
							J := h.FixAs[Real]("J")
							given := h.Conjuncts(
								h.Assume(),
								"F is continuous on ⟦u, v⟧",
								"with derivative f strictly inside, off ∅",
								"and f has integral J over ⟦u, v⟧")
							inside := h.Have(
								"no point is exceptional, so f is the derivative of F everywhere strictly inside",
								"∀t:real. u < t ∧ t < v ⇒ real_derivative_at(F, t, f(t))",
								By(given[1], set_basic.NotInEmpty))
							h.Show(
								"so J is F(v) − F(u)",
								By(given[0], inside, given[2], NewtonLeibniz.At(F, f, u, v, J)))
						})),
					Case(
						"one more exceptional point c: split at c when it lies "+
							"inside, and otherwise it is none of the interval's",
						Derive(func(h *Argument) {
							c := h.FixAs[Real]("c")
							h.FixAs[Set[Real]]("s")
							carried := h.Assume()
							u := h.FixAs[Real]("u")
							v := h.FixAs[Real]("v")
							J := h.FixAs[Real]("J")
							given := h.Conjuncts(
								h.Assume(),
								"F is continuous on ⟦u, v⟧",
								"with derivative f strictly inside, off insert(c, s)",
								"and f has integral J over ⟦u, v⟧")
							offInsert := h.Have(
								"strictly inside ⟦u, v⟧, F has derivative f at every point that is neither c nor in s",
								"∀t:real. u < t ∧ t < v ∧ t ≠ c ∧ t ∉ s ⇒ real_derivative_at(F, t, f(t))",
								h.ForEach(func(t *Expr[Real]) Action {
									return By(set_basic.InInsert, given[1].At(t))
								}))
							h.Cases(h.Term("u < c ∧ c < v"))
							h.When(
								"c lies inside ⟬u, v⟭: split ⟦u, v⟧ at c",
								func(i *Argument, between Fact) {
									order := i.Have(
										"u ≤ c ≤ v, the ends each at most itself",
										"u ≤ u ∧ u ≤ c ∧ c ≤ v ∧ v ≤ v",
										ByArith(between))
									J1, left := i.ObtainAs[Real](
										"f has an integral J₁ over ⟦u, c⟧",
										"∃J₁:real. real_has_integral(f, u, c, J₁)",
										By(given[2], order, IntegrableSubinterval.At(f, u, v, u, c, J)))
									J2, right := i.ObtainAs[Real](
										"and an integral J₂ over ⟦c, v⟧",
										"∃J₂:real. real_has_integral(f, c, v, J₂)",
										By(given[2], order, IntegrableSubinterval.At(f, u, v, c, v, J)))
									sum := i.Have(
										"the two add up to the integral over ⟦u, v⟧, which is J",
										"J = J₁ + J₂",
										By(given[2], left, right, order, HasIntegralSplit.At(f, u, c, v, J1, J2), HasIntegralUnique))
									halves := i.Have(
										"each point of ⟦u, c⟧ or of ⟦c, v⟧ lies in ⟦u, v⟧",
										"∀z:real. (u ≤ z ∧ z ≤ c ∨ c ≤ z ∧ z ≤ v) ⇒ u ≤ z ∧ z ≤ v",
										ByArith(order))
									leftSide := i.Have(
										"so ⟦u, c⟧ lies in ⟦u, v⟧",
										"⟦u, c⟧ ⊆ ⟦u, v⟧",
										BySets(halves))
									rightSide := i.Have(
										"and so does ⟦c, v⟧",
										"⟦c, v⟧ ⊆ ⟦u, v⟧",
										BySets(halves))
									offLeft := i.Have(
										"strictly inside ⟦u, c⟧ the exceptional points are among s",
										"∀t:real. u < t ∧ t < c ∧ t ∉ s ⇒ real_derivative_at(F, t, f(t))",
										i.ForEach(func(t *Expr[Real]) Action {
											return ByArith(between, offInsert.At(t))
										}))
									offRight := i.Have(
										"and strictly inside ⟦c, v⟧ too",
										"∀t:real. c < t ∧ t < v ∧ t ∉ s ⇒ real_derivative_at(F, t, f(t))",
										i.ForEach(func(t *Expr[Real]) Action {
											return ByArith(between, offInsert.At(t))
										}))
									leftIncrement := i.Have(
										"by the induction hypothesis J₁ is the increment of F across ⟦u, c⟧",
										"J₁ = F(c) - F(u)",
										By(
											carried.At(u, c, J1),
											offLeft,
											left,
											real_continuous.ContinuousOnSubset.At(
												F, i.TermAs[Set[Real]]("⟦u, v⟧"), i.TermAs[Set[Real]]("⟦u, c⟧")),
											given[0],
											leftSide))
									rightIncrement := i.Have(
										"and J₂ across ⟦c, v⟧",
										"J₂ = F(v) - F(c)",
										By(
											carried.At(c, v, J2),
											offRight,
											right,
											real_continuous.ContinuousOnSubset.At(
												F, i.TermAs[Set[Real]]("⟦u, v⟧"), i.TermAs[Set[Real]]("⟦c, v⟧")),
											given[0],
											rightSide))
									i.Show(
										"the increments add up to F(v) − F(u)",
										ByArith(sum, leftIncrement, rightIncrement))
								})
							h.Otherwise(
								"c lies outside ⟬u, v⟭, so no point strictly inside is c",
								func(i *Argument, outside Fact) {
									off := i.Have(
										"strictly inside ⟦u, v⟧ the exceptional points are among s",
										"∀t:real. u < t ∧ t < v ∧ t ∉ s ⇒ real_derivative_at(F, t, f(t))",
										i.ForEach(func(t *Expr[Real]) Action {
											return ByArith(outside, offInsert.At(t))
										}))
									i.Show(
										"so the induction hypothesis applies to ⟦u, v⟧ itself",
										By(carried.At(u, v, J), given[0], off, given[2]))
								})
						}))))
		}),
})}

// NewtonLeibnizContinuous — a continuous f on ⟦a, b⟧ that is the
// derivative of F strictly between a and b, F continuous on ⟦a, b⟧, has
// integral F(b) − F(a) over ⟦a, b⟧: being continuous, f has an integral,
// and NewtonLeibniz identifies it.
var NewtonLeibnizContinuous = newtonLeibnizContinuousThm{family.Add(registry.ProofEntry{
	Name: "NewtonLeibnizContinuous",
	Key:  "prop_f3f999639641038f",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
			"real_continuous_on(⟦a, b⟧, F)",
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(F, x, f(x))",
		},
		Conclusion: "real_has_integral(f, a, b, F(b) - F(a))",
	},
		func(
			arg *Argument,
			F, f *Arrow[Real, Real],
			a, b *Expr[Real],
			ordered, fContinuous, FContinuous, derivative Fact,
		) {
			I, toI := arg.ObtainAs[Real](
				"f, continuous on ⟦a, b⟧, has an integral I over it",
				"∃I:real. real_has_integral(f, a, b, I)",
				By(ContinuousIntegrable, ordered, fContinuous))
			arg.Show(
				"and the Newton–Leibniz theorem identifies I as F(b) − F(a)",
				By(NewtonLeibniz.At(F, f, a, b, I), toI, FContinuous, derivative))
		}),
})}

// IntegrationByParts — for f and g with derivatives f' and g' at every
// point of ⟦a, b⟧, f' and g' continuous there, the integral of f·g' over
// ⟦a, b⟧ is f(b)·g(b) − f(a)·g(a) less the integral of f'·g. Both
// products are continuous, so both have integrals; their sum integrates
// f'·g + f·g', the derivative of f·g, and the Newton–Leibniz theorem
// makes it the increment of f·g across ⟦a, b⟧.
var IntegrationByParts = integrationByPartsThm{family.Add(registry.ProofEntry{
	Name: "IntegrationByParts",
	Key:  "prop_529cfc2b8000c4ae",
	Build: family.Theorem(Statement{
		Binders: "∀f f' g g':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x))",
			"real_continuous_on(⟦a, b⟧, f')",
			"real_continuous_on(⟦a, b⟧, g')",
		},
		Conclusion: "real_integral(λx:real. f(x) * g'(x), a, b) = " +
			"f(b) * g(b) - f(a) * g(a) - real_integral(λx:real. f'(x) * g(x), a, b)",
	},
		func(arg *Argument, f, fPrime, g, gPrime *Arrow[Real, Real], a, b *Expr[Real],
			ordered, derivatives, fPrimeContinuous, gPrimeContinuous Fact) {
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			fContinuous := arg.Have(
				"f is continuous on ⟦a, b⟧, having a derivative at each of its points",
				"real_continuous_on(⟦a, b⟧, f)",
				By(derivatives, real_derivative.DerivativeContinuousOn.At(f, fPrime, interval)))
			gContinuous := arg.Have(
				"and so is g",
				"real_continuous_on(⟦a, b⟧, g)",
				By(derivatives, real_derivative.DerivativeContinuousOn.At(g, gPrime, interval)))
			fgPrime := arg.TermAs[Fun[Real, Real]]("λx:real. f(x) * g'(x)")
			fPrimeG := arg.TermAs[Fun[Real, Real]]("λx:real. f'(x) * g(x)")
			I, toI := arg.ObtainAs[Real](
				"f·g', a product of functions continuous on ⟦a, b⟧, has an integral I over it",
				"∃I:real. real_has_integral(λx:real. f(x) * g'(x), a, b, I)",
				By(
					ordered,
					fContinuous,
					gPrimeContinuous,
					real_continuous.ContinuousOnMul.At(f, gPrime, interval),
					ContinuousIntegrable.At(fgPrime, a, b)))
			J, toJ := arg.ObtainAs[Real](
				"and f'·g an integral J",
				"∃J:real. real_has_integral(λx:real. f'(x) * g(x), a, b, J)",
				By(
					ordered,
					fPrimeContinuous,
					gContinuous,
					real_continuous.ContinuousOnMul.At(fPrime, g, interval),
					ContinuousIntegrable.At(fPrimeG, a, b)))
			productRule := arg.Have(
				"strictly inside ⟦a, b⟧ the product f·g has derivative f'·g + f·g'",
				"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(λy:real. f(y) * g(y), x, f'(x) * g(x) + f(x) * g'(x))",
				arg.ForEach(func(x *Expr[Real]) Action {
					return ByArith(
						derivatives.At(x),
						real_derivative.DerivativeMul.At(f, g, x, fPrime.Apply(x), gPrime.Apply(x)))
				}))
			increment := arg.Have(
				"J + I integrates f'·g + f·g', the derivative of f·g, so it is the increment of f·g across ⟦a, b⟧",
				"J + I = f(b) * g(b) - f(a) * g(a)",
				By(
					productRule,
					fContinuous,
					gContinuous,
					toJ,
					toI,
					real_continuous.ContinuousOnMul.At(f, g, interval),
					HasIntegralAdd.At(fPrimeG, fgPrime, a, b, J, I),
					NewtonLeibniz.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. f(x) * g(x)"),
						arg.TermAs[Fun[Real, Real]]("λx:real. f'(x) * g(x) + f(x) * g'(x)"),
						a,
						b,
						arg.TermAs[Real]("J + I"))))
			arg.Show(
				"the two integrals are I and J, and I = f(b)·g(b) − f(a)·g(a) − J",
				ByArith(
					increment,
					toI,
					toJ,
					HasIntegralValue.At(fgPrime, a, b, I),
					HasIntegralValue.At(fPrimeG, a, b, J)))
		}),
})}

// IntegralDerivative — the fundamental theorem of calculus, first part:
// for f continuous on ⟦a, b⟧, the integral of f from a to y, as a function
// of y, has derivative f(x) at every x strictly between a and b. Given ε,
// continuity keeps f within ε/2 of f(x) on ⟦a, b⟧ within some radius η
// of x. Across a span ⟦u, v⟧ of ⟦a, b⟧ within η of x the integral grows by
// the span's integral (IntegralAdditive), which lies within ε/2·(v − u) of
// f(x)·(v − u) (HasIntegralNearConstant). For y within η of x and inside
// ⟦a, b⟧, the increment from x to y is the span between them, read
// forwards or backwards, so it is within ε/2·|y − x| < ε·|y − x| of
// f(x)·(y − x): the increment criterion holds at ε.
var IntegralDerivative = integralDerivativeThm{family.Add(registry.ProofEntry{
	Name: "IntegralDerivative",
	Key:  "prop_3c668a424d5a4bd2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b x:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"a < x",
			"x < b",
		},
		Conclusion: "real_derivative_at(λy:real. real_integral(f, a, y), x, f(x))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, x *Expr[Real], continuous, above, below Fact) {
			I, toI := arg.ObtainAs[Real](
				"f, continuous on ⟦a, b⟧, has an integral I over it",
				"∃I:real. real_has_integral(f, a, b, I)",
				ByArith(ContinuousIntegrable.At(f, a, b), continuous, above, below))
			near := arg.Unfolded(continuous, real_continuous.RealContinuousOnDef)
			increments := arg.Have(
				"for every ε some radius about x brings the increment "+
					"of the integral within ε·|y − x| of f(x)·(y − x)",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀y:real. " +
						"        &0 < |y - x| ∧ |y - x| < δ ⇒ " +
						"        |real_integral(f, a, y) - real_integral(f, a, x) - f(x) * (y - x)| < ε * |y - x|)",
				},
				Derive(func(c *Argument) {
					c.FixAs[Real]()
					pos := c.Assume()
					_, radius := c.ObtainAs[Real](
						"f is continuous at x: within some radius η of x, f on ⟦a, b⟧ stays within ε/2 of f(x)",
						"∃η:real. &0 < η ∧ (∀t:real. a ≤ t ∧ t ≤ b ∧ |t - x| < η ⇒ |f(t) - f(x)| < ε / &2)",
						ByArith(near.At(x, c.TermAs[Real]("ε / &2")), above, below, pos))
					held := c.Conjuncts(
						radius,
						"η is positive",
						"within η of x the values of f on ⟦a, b⟧ are within ε/2 of f(x)")
					span := c.Have(
						"across a span ⟦u, v⟧ of ⟦a, b⟧ within η of x the "+
							"integral grows by f(x)·(v − u), up to ε/2·(v − u)",
						Statement{
							Binders: "∀u v:real.",
							Hypotheses: []string{
								"a ≤ u",
								"u ≤ v",
								"v ≤ b",
								"|u - x| < η",
								"|v - x| < η",
							},
							Conclusion: "|real_integral(f, a, v) - real_integral(f, a, u) - f(x) * (v - u)| ≤ ε / &2 * (v - u)",
						},
						Derive(func(d *Argument) {
							u := d.FixAs[Real]()
							v := d.FixAs[Real]()
							within := d.Assume()
							J, toJ := d.ObtainAs[Real](
								"f has an integral J over ⟦u, v⟧, a part of ⟦a, b⟧",
								"∃J:real. real_has_integral(f, u, v, J)",
								By(IntegrableSubinterval.At(f, a, b, u, v, I), toI, within))
							nearValue := d.Have(
								"on ⟦u, v⟧ the values of f are within ε/2 of f(x)",
								"∀t:real. u ≤ t ∧ t ≤ v ⇒ |f(t) - f(x)| ≤ ε / &2",
								d.ForEach(func(t *Expr[Real]) Action {
									return ByArith(held[1].At(t), within)
								}))
							d.Show(
								"the integral grows from u to v by J, which is within ε/2·(v − u) of f(x)·(v − u)",
								ByArith(
									nearValue,
									continuous,
									above,
									below,
									within,
									toJ,
									HasIntegralNearConstant.At(f, u, v, J, f.Apply(x), d.TermAs[Real]("ε / &2")),
									HasIntegralValue.At(f, u, v, J),
									IntegralAdditive.At(f, a, b, a, u, v)))
						}))
					c.Take(c.TermAs[Real]("min(η, min(x - a, b - x))"))
					c.Show(
						"within min(η, x − a, b − x) of x a point y lies in ⟦a, b⟧ and within η of x",
						SplitConj(
							Case(
								"the radius is positive",
								ByArith(above, below, held[0])),
							Case(
								"for such y the increment from x to y is the span between them, read forwards or backwards",
								Derive(func(d *Argument) {
									y := d.FixAs[Real]()
									apart := d.Assume()
									d.Cases(d.Term("x ≤ y"))
									d.When(
										"y right of x: the span is ⟦x, y⟧",
										func(e *Argument, right Fact) {
											length := e.Have(
												"|y − x| is y − x",
												"|y - x| = y - x",
												ByArith(right))
											e.Show(
												"the increment is within ε/2·(y − x) of f(x)·(y − x), and ε/2·(y − x) < ε·(y − x)",
												ByArith(span.At(x, y), length, right, above, below, pos, apart))
										})
									d.Otherwise(
										"y left of x: the span is ⟦y, x⟧, read backwards",
										func(e *Argument, left Fact) {
											length := e.Have(
												"|y − x| is x − y",
												"|y - x| = x - y",
												ByArith(left))
											backwards := e.Have(
												"the increment from x back to y is the span's, negated",
												"|real_integral(f, a, y) - real_integral(f, a, x) - f(x) * (y - x)| ≤ ε / &2 * (x - y)",
												ByArith(span.At(y, x), length, left, above, below, apart))
											e.Show(
												"and ε/2·(x − y) < ε·(x − y)",
												ByArith(backwards, length, left, pos))
										})
								}))))
				}))
			arg.Show(
				"which is the increment criterion for the derivative f(x) at x",
				By(
					increments,
					real_derivative.DerivativeIncrement.At(
						arg.TermAs[Fun[Real, Real]]("λy:real. real_integral(f, a, y)"),
						x,
						f.Apply(x))))
		}),
})}

// IntegralContinuousOn — the integral of a function continuous on ⟦a, b⟧,
// taken from a point c of ⟦a, b⟧, is continuous on ⟦a, b⟧ as a function of
// its upper limit, the ends included. f is bounded on ⟦a, b⟧, by M, so over
// a span ⟦u, v⟧ of ⟦a, b⟧ its integral is at most M·(v − u) in size; between
// two points x and y of ⟦a, b⟧ the integral from c moves by the integral
// between them, read forwards or backwards, so by at most M·|y − x|, which
// is below ε within ε/(M + 1) of x.
var IntegralContinuousOn = integralContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "IntegralContinuousOn",
	Key:  "prop_98b972a854df77d0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b c:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"a ≤ c",
			"c ≤ b",
		},
		Conclusion: "real_continuous_on(⟦a, b⟧, λy:real. real_integral(f, c, y))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, c *Expr[Real], continuous, lower, upper Fact) {
			I, toI := arg.ObtainAs[Real](
				"f, continuous on ⟦a, b⟧, has an integral I over it",
				"∃I:real. real_has_integral(f, a, b, I)",
				ByArith(ContinuousIntegrable.At(f, a, b), continuous, lower, upper),
				Named("I"))
			_, bounded := arg.ObtainAs[Real](
				"so f is bounded on ⟦a, b⟧, by M",
				"∃M:real. ∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ M",
				By(toI, IntegrableBounded.At(f, a, b, I)),
				Named("M"))
			span := arg.Have(
				"over a span ⟦u, v⟧ of ⟦a, b⟧ the integral of f is at most M·(v − u) in size",
				"∀u v:real. a ≤ u ∧ u ≤ v ∧ v ≤ b ⇒ |real_integral(f, u, v)| ≤ M * (v - u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Real]("u")
					v := d.FixAs[Real]("v")
					within := d.Assume()
					J, toJ := d.ObtainAs[Real](
						"f has an integral J over ⟦u, v⟧, a part of ⟦a, b⟧",
						"∃J:real. real_has_integral(f, u, v, J)",
						By(IntegrableSubinterval.At(f, a, b, u, v, I), toI, within),
						Named("J"))
					boundedSpan := d.Have(
						"M bounds f on ⟦u, v⟧",
						"∀t:real. u ≤ t ∧ t ≤ v ⇒ |f(t)| ≤ M",
						d.ForEach(func(t *Expr[Real]) Action {
							return ByArith(bounded.At(t), within)
						}))
					d.Show(
						"the integral over ⟦u, v⟧ is J, at most M·(v − u) in size",
						By(
							Normalized,
							toJ,
							boundedSpan,
							HasIntegralValue.At(f, u, v, J),
							HasIntegralBound.At(f, u, v, J, d.TermAs[Real]("M"))))
				}))
			moves := arg.Have(
				"between two points x and y of ⟦a, b⟧ the integral from c moves by at most M·|y − x|",
				Statement{
					Binders: "∀x y:real.",
					Hypotheses: []string{
						"a ≤ x",
						"x ≤ b",
						"a ≤ y",
						"y ≤ b",
					},
					Conclusion: "|real_integral(f, c, y) - real_integral(f, c, x)| ≤ M * |y - x|",
				},
				Derive(func(d *Argument) {
					x := d.FixAs[Real]("x")
					y := d.FixAs[Real]("y")
					within := d.Assume()
					additive := d.Have(
						"the integral from c to y is the integral to x and on to y",
						"real_integral(f, c, x) + real_integral(f, x, y) = real_integral(f, c, y)",
						By(continuous, lower, upper, within, IntegralAdditive.At(f, a, b, c, x, y)))
					d.Cases(d.Term("x ≤ y"))
					d.When(
						"forwards, the span from x to y",
						func(e *Argument, forwards Fact) {
							difference := e.Have(
								"the integral from c moves from x to y by the integral from x to y",
								"real_integral(f, c, y) - real_integral(f, c, x) = real_integral(f, x, y)",
								ByArith(additive))
							distance := e.Have(
								"y − x is its own size",
								"|y - x| = y - x",
								ByArith(forwards))
							e.Show(
								"and that integral is at most M·(y − x) in size",
								difference.Rw(),
								distance.Rw(),
								By(span.At(x, y), within, forwards))
						})
					d.Otherwise(
						"backwards, the span from y to x read in reverse",
						func(e *Argument, backwards Fact) {
							reverse := e.Have(
								"the integral from x to y is minus that from y to x, the integral from x to x being 0",
								"real_integral(f, x, y) = -real_integral(f, y, x)",
								ByArith(
									continuous,
									within,
									IntegralAdditive.At(f, a, b, x, y, x),
									IntegralAdditive.At(f, a, b, x, x, x)))
							difference := e.Have(
								"so the integral from c moves from x to y by minus the integral from y to x",
								"real_integral(f, c, y) - real_integral(f, c, x) = -real_integral(f, y, x)",
								ByArith(additive, reverse))
							distance := e.Have(
								"and |y − x| is x − y",
								"|y - x| = x - y",
								ByArith(backwards))
							e.Show(
								"a negative has the size of what it negates, at most M·(x − y)",
								difference.Rw(),
								distance.Rw(),
								ByArith(
									span.At(y, x),
									within,
									backwards,
									real_sgn_abs.AbsEven.At(e.TermAs[Real]("real_integral(f, y, x)"))))
						})
				}))
			nonnegative := arg.Have(
				"M is not negative, bounding |f(a)|",
				"&0 ≤ M",
				ByArith(bounded.At(a), lower, upper))
			arg.Do(Unfold(real_continuous.RealContinuousOnDef))
			x := arg.FixAs[Real]("x")
			inside := arg.Assume()
			arg.FixAs[Real]("ε")
			pos := arg.Assume()
			radius := arg.Have(
				"M·ε/(M + 1) is below ε",
				"M * (ε / (M + &1)) < ε",
				ByArith(nonnegative, pos))
			arg.Take(arg.TermAs[Real]("ε / (M + &1)"))
			arg.Do(SplitConj(
				Case(
					"the radius ε/(M + 1) is positive",
					ByArith(pos, nonnegative)),
				Case(
					"and within it, at a point y of ⟦a, b⟧, the integral from c moves by at most M·|y − x| < ε",
					Derive(func(d *Argument) {
						y := d.FixAs[Real]("y")
						near := d.Assume()
						scaled := d.Have(
							"M·|y − x| is at most M·ε/(M + 1), M not being negative",
							"M * |y - x| ≤ M * (ε / (M + &1))",
							ByArith(nonnegative, near))
						d.Show(
							"so the integral from c moves by at most M·|y − x| ≤ M·ε/(M + 1) < ε",
							ByArith(moves.At(x, y), inside, near, scaled, radius))
					})),
			))
		}),
})}

// DerivativeUnderIntegral — differentiation under the integral sign: when
// F(s, ·) has an integral over ⟦a, b⟧ for every s within d of t and G(t, ·)
// has one too, and on that ball F(t + h, x) − F(t, x) is G(t, x)·h to within
// K·h² at every point x of ⟦a, b⟧, then ∫ₐᵇ F(s, x) dx, as a function of s,
// has derivative ∫ₐᵇ G(t, x) dx at t. The integrals of F(t + h, ·), F(t, ·)
// and h·G(t, ·) combine into the integral of the pointwise remainder, which
// the uniform bound holds within K·h²·(b − a): a quadratic remainder for the
// integral, which DerivativeFromQuadraticRemainder turns into the derivative.
var DerivativeUnderIntegral = derivativeUnderIntegralThm{family.Add(registry.ProofEntry{
	Name: "DerivativeUnderIntegral",
	Key:  "prop_d660f35a693912f0",
	Build: family.Theorem(Statement{
		Binders: "∀F G:(real → real → real). ∀a b t K d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀s:real. |s - t| < d ⇒ real_has_integral(F(s), a, b, real_integral(F(s), a, b))",
			"real_has_integral(G(t), a, b, real_integral(G(t), a, b))",
			"∀h x:real. |h| < d ∧ a ≤ x ∧ x ≤ b ⇒ |F(t + h, x) - F(t, x) - G(t, x) * h| ≤ K * h ^ 2",
		},
		Conclusion: "real_derivative_at(λs:real. real_integral(F(s), a, b), t, real_integral(G(t), a, b))",
	},
		func(
			arg *Argument,
			F, G *Arrow2[Real, Real, Real],
			a, b, t, K, d *Expr[Real],
			radius, integrable, slopeIntegrable, remainder Fact,
		) {
			increments := arg.Have(
				"within d of t the integral moves by ∫ₐᵇ G(t, x) dx·h to within K·(b − a)·h²",
				Statement{
					Binders:    "∀h:real.",
					Hypotheses: []string{"|h| < d"},
					Conclusion: "|real_integral(F(t + h), a, b) - " +
						"real_integral(F(t), a, b) - " +
						"real_integral(G(t), a, b) * h| ≤ " +
						"K * (b - a) * h ^ 2",
				},
				Derive(func(e *Argument) {
					h := e.FixAs[Real]("h")
					small := e.Assume()
					shifted := e.TermAs[Fun[Real, Real]]("F(t + h)")
					unshifted := e.TermAs[Fun[Real, Real]]("F(t)")
					slope := e.TermAs[Fun[Real, Real]]("G(t)")
					shiftedValue := e.TermAs[Real]("real_integral(F(t + h), a, b)")
					unshiftedValue := e.TermAs[Real]("real_integral(F(t), a, b)")
					slopeValue := e.TermAs[Real]("real_integral(G(t), a, b)")
					both := e.Have(
						"t and t + h lie within d of t, so F(t, ·) and F(t + h, ·) have their integrals",
						"real_has_integral(F(t), a, b, real_integral(F(t), a, b)) ∧ "+
							"real_has_integral(F(t + h), a, b, real_integral(F(t + h), a, b))",
						ByArith(radius, small, integrable.At(t), integrable.At(e.TermAs[Real]("t + h"))))
					combined := e.Have(
						"so the pointwise remainder has the remainder of the integrals for its integral",
						"real_has_integral(λx:real. F(t + h, x) - F(t, x) - h * G(t, x), "+
							"    a, "+
							"    b, "+
							"    real_integral(F(t + h), a, b) - real_integral(F(t), a, b) - h * real_integral(G(t), a, b))",
						By(
							both,
							slopeIntegrable,
							HasIntegralSub.At(shifted, unshifted, a, b, shiftedValue, unshiftedValue),
							HasIntegralScale.At(slope, a, b, slopeValue, h),
							HasIntegralSub.At(
								e.TermAs[Fun[Real, Real]]("λx:real. F(t + h, x) - F(t, x)"),
								e.TermAs[Fun[Real, Real]]("λx:real. h * G(t, x)"),
								a,
								b,
								e.TermAs[Real]("real_integral(F(t + h), a, b) - real_integral(F(t), a, b)"),
								e.TermAs[Real]("h * real_integral(G(t), a, b)"))))
					pointwise := e.Have(
						"on ⟦a, b⟧ the pointwise remainder is at most K·h² in size",
						"∀x:real. a ≤ x ∧ x ≤ b ⇒ |F(t + h, x) - F(t, x) - h * G(t, x)| ≤ K * h ^ 2",
						e.ForEach(func(x *Expr[Real]) Action { return ByArith(small, remainder.At(h, x)) }))
					e.Show(
						"so its integral is at most K·h²·(b − a) in size",
						ByArith(
							HasIntegralBound.At(
								e.TermAs[Fun[Real, Real]]("λx:real. F(t + h, x) - F(t, x) - h * G(t, x)"),
								a,
								b,
								e.TermAs[Real](
									"real_integral(F(t + h), a, b) - real_integral(F(t), a, b) - h * real_integral(G(t), a, b)"),
								e.TermAs[Real]("K * h ^ 2")),
							pointwise,
							combined))
				}))
			arg.Show(
				"a quadratic remainder on a ball is a derivative",
				By(
					radius,
					increments,
					real_derivative.DerivativeFromQuadraticRemainder.At(
						arg.TermAs[Fun[Real, Real]]("λs:real. real_integral(F(s), a, b)"),
						t,
						arg.TermAs[Real]("real_integral(G(t), a, b)"),
						arg.TermAs[Real]("K * (b - a)"),
						d)))
		}),
})}

// IntegralAffineSubstitution — an affine change of variable over ⟦0, 1⟧:
// for f continuous on an interval ⟦l, r⟧ holding β and β + α, the integral
// of f(β + α·t)·α over ⟦0, 1⟧ is the integral of f from β to β + α,
// whatever the sign of α, and even where β or β + α is an end of ⟦l, r⟧.
// When α = 0 both are 0. Otherwise the integral of f from l, continuous on
// ⟦l, r⟧ (IntegralContinuousOn), read at β + α·t is continuous on ⟦0, 1⟧;
// strictly inside ⟬0, 1⟭ the point β + α·t lies strictly between β and
// β + α, so inside ⟬l, r⟭, where by the chain rule it has derivative
// f(β + α·t)·α; the Newton–Leibniz theorem makes the integral its
// increment, which additivity reads as the integral from β to β + α.
var IntegralAffineSubstitution = integralAffineSubstitutionThm{family.Add(registry.ProofEntry{
	Name: "IntegralAffineSubstitution",
	Key:  "prop_64d5d6a07e793e75",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀l r α β:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦l, r⟧, f)",
			"l ≤ β",
			"β ≤ r",
			"l ≤ β + α",
			"β + α ≤ r",
		},
		Conclusion: "real_integral(λt:real. f(β + α * t) * α, &0, &1) = real_integral(f, β, β + α)",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			l, r, α, β *Expr[Real],
			continuous, lowStart, highStart, lowEnd, highEnd Fact,
		) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			arg.Cases(arg.Term("α = &0"))
			arg.When(
				"a zero α makes both sides 0",
				func(b *Argument, vanishing Fact) {
					b.Show(
						"the integral of 0 over ⟦0, 1⟧ is 0, and so is the integral of f from β to β",
						vanishing.Rw(),
						Simp(Fwd(real_ring.MulRightZero), Fwd(real_ring.MulLeftZero), Fwd(real_ring.AddRightId)),
						ByArith(
							continuous,
							lowStart,
							highStart,
							HasIntegralConst.At(zero, one, zero),
							HasIntegralValue.At(
								b.TermAs[Fun[Real, Real]]("λt:real. &0"), zero, one, b.TermAs[Real]("&0 * (&1 - &0)")),
							IntegralAdditive.At(f, l, r, β, β, β)))
				})
			arg.Otherwise(
				"a nonzero α",
				func(b *Argument, nonzero Fact) {
					unit := b.TermAs[Set[Real]]("⟦&0, &1⟧")
					interval := b.TermAs[Set[Real]]("⟦l, r⟧")
					affine := b.TermAs[Fun[Real, Real]]("λt:real. β + α * t")
					integrand := b.TermAs[Fun[Real, Real]]("λt:real. f(β + α * t) * α")
					primitive := b.TermAs[Fun[Real, Real]]("λy:real. real_integral(f, l, y)")
					composite := b.TermAs[Fun[Real, Real]]("λt:real. real_integral(f, l, β + α * t)")
					ordered := b.Have(
						"l ≤ r",
						"l ≤ r",
						ByArith(lowStart, highStart))
					maps := b.Have(
						"the affine map carries ⟦0, 1⟧ into ⟦l, r⟧, β + α·t lying between β and β + α",
						"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ l ≤ β + α * t ∧ β + α * t ≤ r",
						b.ForEach(func(t *Expr[Real]) Action {
							return ByArith(lowStart, highStart, lowEnd, highEnd)
						}))
					interior := b.Have(
						"and (0, 1) into (l, r): for 0 < t < 1, β + α·t lies strictly between β and β + α",
						"∀t:real. &0 < t ∧ t < &1 ⇒ l < β + α * t ∧ β + α * t < r",
						Derive(func(c *Argument) {
							c.FixAs[Real]("t")
							inside := c.Assume()
							c.Cases(c.Term("&0 < α"))
							c.When(
								"for a positive α, β < β + α·t < β + α",
								func(d *Argument, positive Fact) {
									d.Show(
										"β + α·t climbs from β to β + α",
										ByArith(positive, lowStart, highEnd, inside))
								})
							c.Otherwise(
								"for a negative α, β + α < β + α·t < β",
								func(d *Argument, notPositive Fact) {
									d.Show(
										"β + α·t falls from β to β + α",
										ByArith(notPositive, nonzero, highStart, lowEnd, inside))
								})
						}))
					rate := b.Have(
						"the affine map has derivative α everywhere: 0 + α·1",
						"∀x:real. real_derivative_at(λt:real. β + α * t, x, α)",
						b.ForEach(func(x *Expr[Real]) Action {
							return By(
								real_derivative.DerivativeAdd.At(
									b.TermAs[Fun[Real, Real]]("λt:real. β"),
									b.TermAs[Fun[Real, Real]]("λt:real. α * t"),
									x,
									zero,
									b.TermAs[Real]("α * &1")),
								real_derivative.DerivativeConst.At(β, x),
								real_derivative.DerivativeScale.At(b.TermAs[Fun[Real, Real]]("λt:real. t"), x, one, α),
								real_derivative.DerivativeId.At(x),
								real_construction.AddLeftId,
								real_ring.MulRightId)
						}))
					affineContinuous := b.Have(
						"so it is continuous on ⟦0, 1⟧",
						"real_continuous_on(⟦&0, &1⟧, λt:real. β + α * t)",
						By(
							rate,
							real_derivative.DerivativeContinuousOn.At(affine, b.TermAs[Fun[Real, Real]]("λt:real. α"), unit)))
					primitiveContinuous := b.Have(
						"the integral of f from l is continuous on ⟦l, r⟧",
						"real_continuous_on(⟦l, r⟧, λy:real. real_integral(f, l, y))",
						ByArith(continuous, ordered, IntegralContinuousOn.At(f, l, r, l)))
					compositeContinuous := b.Have(
						"so, read at β + α·t, it is continuous on ⟦0, 1⟧",
						"real_continuous_on(⟦&0, &1⟧, λt:real. real_integral(f, l, β + α * t))",
						By(
							maps,
							affineContinuous,
							primitiveContinuous,
							real_continuous.ContinuousOnCompose.At(primitive, affine, unit, interval),
							functions.ComposeApply))
					integrandContinuous := b.Have(
						"and the integrand f(β + α·t)·α is continuous on ⟦0, 1⟧",
						"real_continuous_on(⟦&0, &1⟧, λt:real. f(β + α * t) * α)",
						By(
							maps,
							continuous,
							affineContinuous,
							real_continuous.ContinuousOnCompose.At(f, affine, unit, interval),
							real_continuous.ContinuousOnMul.At(
								b.TermAs[Fun[Real, Real]]("f ∘ (λt:real. β + α * t)"),
								b.TermAs[Fun[Real, Real]]("λt:real. α"),
								unit),
							real_continuous.ContinuousOnConst.At(α, unit),
							functions.ComposeApply))
					chain := b.Have(
						"strictly inside ⟬0, 1⟭ it has derivative f(β + α·t)·α, by the chain rule at a point inside ⟬l, r⟭",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"&0 < x",
								"x < &1",
							},
							Conclusion: "real_derivative_at(λt:real. real_integral(f, l, β + α * t), x, f(β + α * x) * α)",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[Real]("x")
							inside := c.Assume()
							point := c.TermAs[Real]("β + α * x")
							c.Show(
								"the integral of f from l has derivative f at β + α·x, and the affine map derivative α",
								By(
									interior.At(x),
									inside,
									continuous,
									rate.At(x),
									IntegralDerivative.At(f, l, r, point),
									real_derivative.DerivativeChain.At(primitive, affine, x, f.Apply(point), α),
									functions.ComposeApply))
						}))
					increment := b.Have(
						"so by the Newton–Leibniz theorem the integral over ⟦0, 1⟧ is the composite's increment",
						"real_has_integral(λt:real. f(β + α * t) * α, "+
							"    &0, "+
							"    &1, "+
							"    real_integral(f, l, β + α * &1) - real_integral(f, l, β + α * &0))",
						By(
							chain,
							integrandContinuous,
							compositeContinuous,
							NewtonLeibnizContinuous.At(composite, integrand, zero, one)))
					ends := b.Simplified(
						increment,
						Fwd(real_ring.MulRightId),
						Fwd(real_ring.MulRightZero),
						Fwd(real_ring.AddRightId))
					b.Show(
						"which additivity over l, β and β + α reads as the integral from β to β + α",
						ByArith(
							ends,
							continuous,
							ordered,
							lowStart,
							highStart,
							lowEnd,
							highEnd,
							HasIntegralValue.At(
								integrand,
								zero,
								one,
								b.TermAs[Real]("real_integral(f, l, β + α) - real_integral(f, l, β)")),
							IntegralAdditive.At(f, l, r, l, β, b.TermAs[Real]("β + α"))))
				})
		}),
})}

// RiemannIntegralAffineChange — an affine change of variable over a
// window ⟦l, u⟧: for f continuous on an interval ⟦c, d⟧ holding p + q·l and
// p + q·u, the integral of f(p + q·y)·q over ⟦l, u⟧ is the integral of f
// from p + q·l to p + q·u, whatever the sign of q. The point p + q·y lies
// between p + q·l and p + q·u, so in ⟦c, d⟧, and the integrand is
// continuous on ⟦l, u⟧. IntegralAffineSubstitution reads each integral
// over ⟦0, 1⟧, the one of f through p + q·l + q·(u − l)·t and the one of
// the integrand through l + (u − l)·t, and the two integrands there are
// one.
var RiemannIntegralAffineChange = riemannIntegralAffineChangeThm{family.Add(registry.ProofEntry{
	Name: "RiemannIntegralAffineChange",
	Key:  "prop_ec26763b500df04a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c d p q l u:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦c, d⟧, f)",
			"l ≤ u",
			"c ≤ p + q * l",
			"p + q * l ≤ d",
			"c ≤ p + q * u",
			"p + q * u ≤ d",
		},
		Conclusion: "real_integral(λy:real. f(p + q * y) * q, l, u) = " +
			"real_integral(f, p + q * l, p + q * u)",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			c, d, p, q, l, u *Expr[Real],
			continuous, ordered, lowStart, highStart, lowEnd, highEnd Fact,
		) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			window := arg.TermAs[Set[Real]]("⟦l, u⟧")
			interval := arg.TermAs[Set[Real]]("⟦c, d⟧")
			affine := arg.TermAs[Fun[Real, Real]]("λy:real. p + q * y")
			slope := arg.TermAs[Fun[Real, Real]]("λy:real. q")
			integrand := arg.TermAs[Fun[Real, Real]]("λy:real. f(p + q * y) * q")
			maps := arg.Have(
				"the affine map carries ⟦l, u⟧ into ⟦c, d⟧, p + q·y lying between p + q·l and p + q·u",
				"∀y:real. l ≤ y ∧ y ≤ u ⇒ c ≤ p + q * y ∧ p + q * y ≤ d",
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					inside := b.Assume()
					b.Cases(b.Term("&0 ≤ q"))
					b.When(
						"for q ≥ 0, p + q·y climbs from p + q·l to p + q·u",
						func(e *Argument, rising Fact) {
							e.Show(
								"q·(y − l) and q·(u − y) are nonnegative",
								ByArith(rising, inside, lowStart, highEnd))
						})
					b.Otherwise(
						"for q < 0, p + q·y falls from p + q·l to p + q·u",
						func(e *Argument, falling Fact) {
							e.Show(
								"q·(y − l) and q·(u − y) are nonpositive",
								ByArith(falling, inside, highStart, lowEnd))
						})
				}))
			rate := arg.Have(
				"the affine map has derivative q everywhere: 0 + q·1",
				"∀x:real. real_derivative_at(λy:real. p + q * y, x, q)",
				arg.ForEach(func(x *Expr[Real]) Action {
					return By(
						real_derivative.DerivativeAdd.At(
							arg.TermAs[Fun[Real, Real]]("λy:real. p"),
							arg.TermAs[Fun[Real, Real]]("λy:real. q * y"),
							x,
							zero,
							arg.TermAs[Real]("q * &1")),
						real_derivative.DerivativeConst.At(p, x),
						real_derivative.DerivativeScale.At(arg.TermAs[Fun[Real, Real]]("λy:real. y"), x, one, q),
						real_derivative.DerivativeId.At(x),
						real_construction.AddLeftId,
						real_ring.MulRightId)
				}))
			affineContinuous := arg.Have(
				"so it is continuous on ⟦l, u⟧",
				"real_continuous_on(⟦l, u⟧, λy:real. p + q * y)",
				By(rate, real_derivative.DerivativeContinuousOn.At(affine, slope, window)))
			integrandContinuous := arg.Have(
				"and the integrand f(p + q·y)·q is continuous on ⟦l, u⟧",
				"real_continuous_on(⟦l, u⟧, λy:real. f(p + q * y) * q)",
				By(
					maps,
					continuous,
					affineContinuous,
					real_continuous.ContinuousOnCompose.At(f, affine, window, interval),
					real_continuous.ContinuousOnMul.At(
						arg.TermAs[Fun[Real, Real]]("f ∘ (λy:real. p + q * y)"), slope, window),
					real_continuous.ContinuousOnConst.At(q, window),
					functions.ComposeApply))
			endpoints := arg.Have(
				"the parametrizations end where they should",
				"p + q * l + q * (u - l) = p + q * u ∧ l + (u - l) = u",
				ByArith())
			outer := arg.Have(
				"through p + q·l + q·(u − l)·t the integral of f from p + q·l to p + q·u is one over ⟦0, 1⟧",
				"real_integral(λt:real. f(p + q * l + q * (u - l) * t) * (q * (u - l)), &0, &1) = "+
					"real_integral(f, p + q * l, p + q * u)",
				ByArith(
					continuous,
					lowStart,
					highStart,
					lowEnd,
					highEnd,
					endpoints,
					IntegralAffineSubstitution.At(
						f, c, d, arg.TermAs[Real]("q * (u - l)"), arg.TermAs[Real]("p + q * l"))))
			inner := arg.Have(
				"through l + (u − l)·t the integral of the integrand over ⟦l, u⟧ is one over ⟦0, 1⟧",
				"real_integral(λt:real. f(p + q * (l + (u - l) * t)) * q * (u - l), &0, &1) = "+
					"real_integral(λy:real. f(p + q * y) * q, l, u)",
				ByArith(
					ordered,
					endpoints,
					integrandContinuous,
					IntegralAffineSubstitution.At(integrand, l, u, arg.TermAs[Real]("u - l"), l)))
			same := arg.Have(
				"the two integrands over ⟦0, 1⟧ are one",
				"(λt:real. f(p + q * l + q * (u - l) * t) * (q * (u - l))) = "+
					"(λt:real. f(p + q * (l + (u - l) * t)) * q * (u - l))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("t")
					point := b.Have(
						"the two points are one",
						"p + q * l + q * (u - l) * t = p + q * (l + (u - l) * t)",
						ByArith())
					b.Show(
						"and so are the two factors",
						ByArith(point))
				}))
			arg.Show(
				"so the two integrals are one",
				By(outer, inner, same))
		}),
})}

// IntegralSubstitution — change of variables: for g with derivative g' at
// every point of ⟦a, b⟧, g' continuous there, and g carrying ⟦a, b⟧ inside
// an interval ⟬l, r⟭ on whose closure f is continuous, the integral of
// f(g(t))·g'(t) over ⟦a, b⟧ is the integral of f from g(a) to g(b). The
// integral of f from l has derivative f inside ⟬l, r⟭ (IntegralDerivative),
// so by the chain rule its composite with g has derivative f(g(t))·g'(t)
// on ⟦a, b⟧; the Newton–Leibniz theorem makes the integral the composite's
// increment, which additivity reads as the integral from g(a) to g(b).
// g keeps strictly inside ⟬l, r⟭ so that the chain rule meets only points
// where the integral of f has a derivative.
var IntegralSubstitution = integralSubstitutionThm{family.Add(registry.ProofEntry{
	Name: "IntegralSubstitution",
	Key:  "prop_bf2cd4949dd769f9",
	Build: family.Theorem(Statement{
		Binders: "∀f g g':(real → real). ∀a b l r:real.",
		Hypotheses: []string{
			"a ≤ b",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ real_derivative_at(g, t, g'(t)) ∧ l < g(t) ∧ g(t) < r",
			"real_continuous_on(⟦a, b⟧, g')",
			"real_continuous_on(⟦l, r⟧, f)",
		},
		Conclusion: "real_integral(λt:real. f(g(t)) * g'(t), a, b) = real_integral(f, g(a), g(b))",
	},
		func(arg *Argument, f, g, gPrime *Arrow[Real, Real], a, b, l, r *Expr[Real],
			ordered, inside, gPrimeContinuous, fContinuous Fact) {
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			composite := arg.TermAs[Fun[Real, Real]]("λs:real. real_integral(f, l, g(s))")
			integrand := arg.TermAs[Fun[Real, Real]]("λt:real. f(g(t)) * g'(t)")
			chain := arg.Have(
				"on ⟦a, b⟧ the integral of f from l to g(t) has derivative "+
					"f(g(t))·g'(t): the chain rule at g(t), inside ⟬l, r⟭",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"a ≤ t",
						"t ≤ b",
					},
					Conclusion: "real_derivative_at(λs:real. real_integral(f, l, g(s)), t, f(g(t)) * g'(t))",
				},
				Derive(func(c *Argument) {
					t := c.FixAs[Real]()
					within := c.Assume()
					c.Show(
						"g has derivative g'(t) at t, and the integral of f from l has derivative f(g(t)) at g(t)",
						By(
							inside.At(t),
							within,
							fContinuous,
							IntegralDerivative.At(f, l, r, g.Apply(t)),
							real_derivative.DerivativeChain.At(
								c.TermAs[Fun[Real, Real]]("λy:real. real_integral(f, l, y)"),
								g,
								t,
								f.Apply(g.Apply(t)),
								gPrime.Apply(t)),
							functions.ComposeApply))
				}))
			maps := arg.Have(
				"g carries ⟦a, b⟧ into ⟦l, r⟧",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ l ≤ g(t) ∧ g(t) ≤ r",
				arg.ForEach(func(t *Expr[Real]) Action { return ByArith(inside.At(t)) }))
			gContinuous := arg.Have(
				"g is continuous on ⟦a, b⟧, having a derivative at each of its points",
				"real_continuous_on(⟦a, b⟧, g)",
				By(inside, real_derivative.DerivativeContinuousOn.At(g, gPrime, interval)))
			integrandContinuous := arg.Have(
				"f(g(t))·g'(t) is continuous on ⟦a, b⟧: so is f ∘ g, g carrying ⟦a, b⟧ into ⟦l, r⟧, and so is g'",
				"real_continuous_on(⟦a, b⟧, λt:real. f(g(t)) * g'(t))",
				By(
					maps,
					fContinuous,
					gPrimeContinuous,
					gContinuous,
					real_continuous.ContinuousOnCompose.At(f, g, interval, arg.TermAs[Set[Real]]("⟦l, r⟧")),
					real_continuous.ContinuousOnMul.At(arg.TermAs[Fun[Real, Real]]("f ∘ g"), gPrime, interval),
					functions.ComposeApply))
			compositeContinuous := arg.Have(
				"the integral of f from l to g(s) is continuous in s on ⟦a, b⟧, having a derivative there",
				"real_continuous_on(⟦a, b⟧, λs:real. real_integral(f, l, g(s)))",
				By(chain, real_derivative.DerivativeContinuousOn.At(composite, integrand, interval)))
			interior := arg.Have(
				"in particular it has derivative f(g(x))·g'(x) strictly between a and b",
				Statement{
					Binders: "∀x:real.",
					Hypotheses: []string{
						"a < x",
						"x < b",
					},
					Conclusion: "real_derivative_at(λs:real. real_integral(f, l, g(s)), x, f(g(x)) * g'(x))",
				},
				arg.ForEach(func(x *Expr[Real]) Action { return ByArith(chain.At(x)) }))
			integral := arg.Have(
				"so by the Newton–Leibniz theorem the integral of "+
					"f(g(t))·g'(t) over ⟦a, b⟧ is the composite's increment",
				"real_has_integral(λt:real. f(g(t)) * g'(t), "+
					"    a, "+
					"    b, "+
					"    real_integral(f, l, g(b)) - real_integral(f, l, g(a)))",
				By(
					interior,
					integrandContinuous,
					compositeContinuous,
					ordered,
					NewtonLeibnizContinuous.At(composite, integrand, a, b)))
			arg.Show(
				"which, the integral of f adding over l, g(a) and g(b), is the integral of f from g(a) to g(b)",
				ByArith(
					maps.At(a),
					maps.At(b),
					fContinuous,
					ordered,
					integral,
					HasIntegralValue.At(
						integrand,
						a,
						b,
						arg.TermAs[Real]("real_integral(f, l, g(b)) - real_integral(f, l, g(a))")),
					IntegralAdditive.At(f, l, r, l, g.Apply(a), g.Apply(b))))
		}),
})}
