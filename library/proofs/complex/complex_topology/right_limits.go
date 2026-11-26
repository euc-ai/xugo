// right_limits.go — complex functions of a real variable σ as σ decreases
// to a point a, read on the intervals (a, a + d): a limit of (σ − a)·f(σ)
// survives a bounded change of f, and a finite sum of functions each
// bounded on some such interval is bounded on one.

package complex_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ScaledLimitBoundedDifference — if (σ − a)·f(σ) tends to l as σ decreases
// to a, and g differs from f by at most M on an interval (a, a + e), then
// (σ − a)·g(σ) tends to l as well.
//
// Given ε, (σ − a)·f(σ) is within ε/2 of l below some radius d, and the
// change (σ − a)·(g(σ) − f(σ)) has modulus at most (σ − a)·M, below ε/2
// once σ − a < ε/(2(|M| + 1)); the smallest of d, e and that radius serves,
// by the triangle inequality.
var ScaledLimitBoundedDifference = scaledLimitBoundedDifferenceThm{family.Add(registry.ProofEntry{
	Name: "ScaledLimitBoundedDifference",
	Key:  "prop_ca347bb4a032c978",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → complex). ∀a e M:real. ∀l:complex. ∀ε:real.",
		Hypotheses: []string{
			"∀η:real. &0 < η ⇒ ∃d:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |&(σ - a) * f(σ) - l| < η)",
			"&0 < e",
			"∀σ:real. a < σ ∧ σ < a + e ⇒ |f(σ) - g(σ)| ≤ M",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀σ:real. a < σ ∧ σ < a + δ ⇒ |&(σ - a) * g(σ) - l| < ε)",
	}, func(
		arg *Argument,
		f, g *Arrow[Real, Complex],
		a, e, M *Expr[Real],
		l *Expr[Complex],
		ε *Expr[Real],
		toL, radiusPositive, bounded, positive Fact,
	) {
		d, density := arg.ObtainAs[Real](
			"below some radius d, (σ − a)·f(σ) is within half the tolerance of l",
			"∃d:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |&(σ - a) * f(σ) - l| < ε / &2)",
			ByArith(positive, toL.At(arg.TermAs[Real]("ε / &2"))),
			Named("d"))
		m, intersection := arg.LetAs[Real]("m", "min(d, e)")
		intersectionPositive := arg.Have(
			"the common interval has positive radius",
			"&0 < m",
			By(
				Normalized,
				density,
				radiusPositive,
				intersection,
				real_sup_inf.LessThanMin.At(d, e, arg.TermAs[Real]("&0"))))
		intersectionBounds := arg.Have(
			"the common interval lies in both original intervals",
			"m ≤ d ∧ m ≤ e",
			By(
				intersection,
				real_sup_inf.MinLessEq.At(d, e, d),
				real_sup_inf.MinLessEq.At(d, e, e),
				real_order_ring.LessEqRefl))

		denominator := arg.Have(
			"the denominator in the radius is positive",
			"&0 < &2 * (|M| + &1)",
			ByArith())
		den := arg.TermAs[Real]("&2 * (|M| + &1)")
		eta := arg.TermAs[Real]("ε / (&2 * (|M| + &1))")
		δ, radius := arg.LetAs[Real]("δ", "min(m, ε / (&2 * (|M| + &1)))")
		bothPositive := arg.Have(
			"both candidate radii are positive",
			"&0 < m ∧ &0 < ε / (&2 * (|M| + &1))",
			By(positive, intersectionPositive, denominator, real_order_field.DivPos.At(ε, den)))
		arg.Show(
			"the smaller radius controls both errors",
			Witness(δ),
			SplitConj(
				Case(
					"the smaller radius is positive",
					By(radius, bothPositive, real_sup_inf.LessThanMin.At(m, eta, arg.TermAs[Real]("&0")))),
				Case(
					"the two errors together are less than epsilon",
					Derive(func(b *Argument) {
						σ := b.FixAs[Real]("σ")
						interval := b.Assume()
						both := b.Have(
							"the radius is no larger than either candidate",
							"δ ≤ m ∧ δ ≤ ε / (&2 * (|M| + &1))",
							By(
								radius,
								real_sup_inf.MinLessEq.At(m, eta, m),
								real_sup_inf.MinLessEq.At(m, eta, eta),
								real_order_ring.LessEqRefl))
						near := b.Have(
							"(σ − a)·f(σ) stays within half the tolerance of l",
							"|&(σ - a) * f(σ) - l| < ε / &2",
							ByArith(interval, both, intersectionBounds, density))
						unscaled := b.Have(
							"the difference is bounded by M",
							"|f(σ) - g(σ)| ≤ M",
							ByArith(interval, both, intersectionBounds, bounded.At(σ)))
						short := b.Have(
							"the distance to a is less than the division radius",
							"σ - a < ε / (&2 * (|M| + &1))",
							ByArith(interval, both))
						excess := b.TermAs[Real]("σ - a")
						margin := b.Have(
							"multiplying by the denominator makes the distance less than epsilon",
							"(σ - a) * (&2 * (|M| + &1)) < ε",
							By(short, denominator, real_order_field.LessThanDivMulLeft.At(excess, ε, den)))
						scaled := b.Have(
							"the scaled difference is at most half the tolerance",
							"(σ - a) * |f(σ) - g(σ)| ≤ ε / &2",
							ByArith(interval, unscaled, margin))
						z, factor := b.LetAs[Complex]("z", "&(σ - a)")
						factored := b.Have(
							"factor the two scaled values",
							"z * g(σ) - z * f(σ) = z * (g(σ) - f(σ))",
							ByArith())
						perturbation := b.Have(
							"the modulus of the scaled difference is at most half the tolerance",
							"|z * g(σ) - z * f(σ)| ≤ ε / &2",
							ByArith(
								factored,
								factor,
								interval,
								scaled,
								complex_abs.AbsMul.At(z, b.TermAs[Complex]("g(σ) - f(σ)")),
								complex_abs.AbsOfReal.At(excess),
								complex_abs.AbsSubComm.At(g.Apply(σ), f.Apply(σ))))
						b.Show(
							"combine the estimates by the triangle inequality",
							ByArith(
								perturbation,
								near,
								complex_abs.AbsSubTriangle.At(b.TermAs[Complex]("z * g(σ)"),
									b.TermAs[Complex]("z * f(σ)"), l)))
					}))))
	}),
	Reading: "The factor σ − a is what lets a bounded change pass: without it a bounded change of " +
		"f moves its limit. The bound is read only on some interval (a, a + e), however short, so only " +
		"the behaviour near a matters: a simple pole's residue at a survives a bounded perturbation.",
})}

// FiniteSumBoundedNear — a finite sum of complex functions of a real
// variable, each bounded on some interval (a, a + d), is bounded on one
// such interval.
//
// By induction on the finite index set: the empty sum is 0, bounded by 0
// on (a, a + 1); inserting a fresh index takes the smaller of the two radii
// and the sum of the two bounds, by the triangle inequality.
var FiniteSumBoundedNear = finiteSumBoundedNearThm{family.Add(registry.ProofEntry{
	Name: "FiniteSumBoundedNear",
	Key:  "prop_c05aa1296ce6c644",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀F:(A → real → complex). ∀a:real.",
		Hypotheses: []string{
			"finite(S)",
			"∀x:A. x ∈ S ⇒ ∃d M:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |F(x, σ)| ≤ M)",
		},
		Conclusion: "∃d M:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |Σ_{x∈S} F(x, σ)| ≤ M)",
	}, func(arg *Argument, S *Expr[Set[A]], F *Arrow2[A, Real, Complex], a *Expr[Real], all Fact) {
		properties := arg.TermAs[Set[Set[A]]](
			"λS:set(A). ∃d M:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |Σ_{x∈S} F(x, σ)| ≤ M)")
		pointwise := arg.TermAs[Set[A]](
			"λx:A. ∃d M:real. &0 < d ∧ (∀σ:real. a < σ ∧ σ < a + d ⇒ |F(x, σ)| ≤ M)")
		addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		arg.Show(
			"start from the empty sum and insert one bounded summand at a time",
			ByInduction(At(finite_set.FiniteInductFreshOn.Inst[A](), properties, pointwise), all,
				Case(
					"the empty sum is zero",
					Witness(arg.TermAs[Real]("&1")),
					Witness(arg.TermAs[Real]("&0")),
					SplitConj(
						Case(
							"one is positive",
							ByArith()),
						Case(
							"the modulus of the empty sum is zero",
							Derive(func(b *Argument) {
								b.FixAs[Real]("σ")
								b.Assume()
								b.Show(
									"the empty fold is the additive identity",
									By(
										monoidal.Clauses.Read(addition),
										comm_ring.NeutralAdd.Read(complex_field.CommRing),
										complex_abs.AbsEqZero,
										real_order_ring.LessEqRefl))
							})))),
				Case(
					"insertion adds the new summand on the common interval",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						t := b.FixAs[Set[A]]("t")
						step := b.Assume()
						parts := b.Conjuncts(
							step,
							"the old sum has a bound",
							"x is fresh",
							"the old index set is finite",
							"the new summand has a bound",
							"every old summand has a bound")
						oldBounded, fresh, finite, newBounded := parts[0], parts[1], parts[2], parts[3]
						d0, _, old := b.Unpack2As[Real, Real](oldBounded, "d₀", "M₀")
						d1, _, added := b.Unpack2As[Real, Real](newBounded, "d₁", "M₁")
						b.Show(
							"use the smaller radius and add the bounds",
							Witness(b.TermAs[Real]("min(d₀,d₁)")),
							Witness(b.TermAs[Real]("M₀ + M₁")),
							SplitConj(Case(
								"both radii are positive",
								By(old, added, real_sup_inf.LessThanMin.At(d0, d1, b.TermAs[Real]("&0")))),
								Case(
									"bound the old sum and the new term separately",
									Derive(func(c *Argument) {
										c.FixAs[Real]("σ")
										near := c.Assume()
										both := c.Have(
											"the common radius is no larger than the original radii",
											"min(d₀,d₁) ≤ d₀ ∧ min(d₀,d₁) ≤ d₁",
											By(
												real_sup_inf.MinLessEq.At(d0, d1, d0),
												real_sup_inf.MinLessEq.At(d0, d1, d1),
												real_order_ring.LessEqRefl))
										oldBound := c.Have(
											"the old bound applies on this interval",
											"|Σ_{y∈t} F(y, σ)| ≤ M₀",
											ByArith(near, both, old))
										newBound := c.Have(
											"the new bound also applies",
											"|F(x, σ)| ≤ M₁",
											ByArith(near, both, added))
										insertion := c.Have(
											"inserting x adds its summand",
											"Σ_{y∈insert(x,t)} F(y, σ) = F(x, σ) + Σ_{y∈t} F(y, σ)",
											By(
												fresh,
												finite,
												monoidal.OneTurn.Read(addition).At(t, x, c.TermAs[Fun[A, Complex]]("λy:A. F(y, σ)"))))
										c.Show(
											"use the triangle inequality",
											ByArith(
												insertion,
												oldBound,
												newBound,
												complex_abs.AbsTriangle.At(c.TermAs[Complex]("F(x, σ)"), c.TermAs[Complex]("Σ_{y∈t} F(y, σ)"))))
									}))))
					}))))
	}),
	Reading: "Each summand may have an interval and a bound of its own; the finiteness of S is " +
		"what lets one interval serve them all. For S empty the sum is 0, bounded on every interval.",
})}
