// algebra.go — the algebra and order of integrals: a constant, sums of
// two functions and of finitely many, multiples, negatives and
// differences, the integral of a function nowhere above another and of a
// nonnegative one, and the bounds by the size of the integrand and by its
// distance from a constant.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// HasIntegralConst — a constant c has integral c·(b − a) over ⟦a, b⟧:
// each Riemann sum is c times the sum of the lengths of the pieces, which
// telescopes to p(n + 1) − p(0) = b − a, so any mesh serves.
var HasIntegralConst = hasIntegralConstThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralConst",
	Key:  "prop_d854f79a9be20bbe",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:real.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "real_has_integral(λx:real. c, a, b, c * (b - a))",
	},
		func(arg *Argument, a, b, c *Expr[Real], ordered Fact) {
			arg.Do(Unfold(RealHasIntegralDef))
			arg.Show(
				"every Riemann sum of c over ⟦a, b⟧ is c·(b − a)",
				SplitConj(
					Case(
						"the interval is ordered",
						By(ordered)),
					Case(
						"for every ε the mesh 1 serves",
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							pos := d.Assume()
							d.Take(d.TermAs[Real]("&1"))
							d.Show(
								"a partition of any mesh has Riemann sum exactly c·(b − a)",
								SplitConj(
									Case(
										"the mesh 1 is positive",
										ByArith()),
									Case(
										"Σ c·(p(k + 1) − p(k)) is c times a telescoping sum, c·(p(n + 1) − p(0))",
										Derive(func(e *Argument) {
											e.FixAs[Nat]()
											e.FixAs[Fun[Nat, Real]]()
											e.FixAs[Fun[Nat, Real]]()
											partition := e.Assume()
											e.Show(
												"and p(0) = a, p(n + 1) = b make it c·(b − a), within ε of itself",
												Simp(Rev(real_sum.ScalarLeft.Inst[Nat]()), Fwd(real_sum.TelescopeUp)),
												ByArith(pos, partition))
										}))))
						}))))
		}),
})}

// HasIntegralAdd — the integral of a sum is the sum of the integrals.
// Given ε, the two integrals share a mesh δ at ε/2; below it the Riemann
// sum of f + g is the sum of the Riemann sums of f and of g, each within
// ε/2 of its integral.
var HasIntegralAdd = hasIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralAdd",
	Key:  "prop_c0884fb4066cdfa2",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b I J:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"real_has_integral(g, a, b, J)",
		},
		Conclusion: "real_has_integral(λx:real. f(x) + g(x), a, b, I + J)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b, I, J *Expr[Real], toI, toJ Fact) {
			arg.Show(
				"the Riemann sums of f + g tend to I + J",
				Simp(Fwd(RealHasIntegralDef)),
				SplitConj(
					Case(
						"the interval is ordered",
						By(HasIntegralOrdered.At(f, a, b, I), toI)),
					Case(
						"for every ε the mesh the two integrals share at ε/2 serves",
						Derive(func(c *Argument) {
							c.FixAs[Real]()
							pos := c.Assume()
							halfPos := c.Have(
								"half of ε is positive",
								"&0 < ε / &2",
								ByArith(pos))
							δ, fine := c.ObtainAs[Real](
								"the mesh δ the two integrals share at ε/2",
								"∃δ:real. "+
									"    &0 < δ ∧ "+
									"    (∀n:num. ∀p t:(num → real). "+
									"        «finePartition»(a, b, δ, n, p, t) ⇒ "+
									"        |«riemannSum»(f, n, p, t) - I| < ε / &2 ∧ |«riemannSum»(g, n, p, t) - J| < ε / &2)",
								By(CommonMesh, toI, toJ, halfPos))
							mesh := c.Conjuncts(
								fine,
								"δ is positive",
								"below δ both Riemann sums are within ε/2 of their integrals")
							c.Take(δ)
							c.Show(
								"δ serves f + g",
								SplitConj(
									Case(
										"δ is positive",
										By(mesh[0])),
									Case(
										"below δ the Riemann sum of f + g is within ε/2 + ε/2 of I + J",
										Derive(func(d *Argument) {
											n := d.FixAs[Nat]()
											p := d.FixAs[Fun[Nat, Real]]()
											t := d.FixAs[Fun[Nat, Real]]()
											partition := d.Assume()
											near := d.Have(
												"the Riemann sum of f is within ε/2 of I, and that of g within ε/2 of J",
												"|«riemannSum»(f, n, p, t) - I| < ε / &2 ∧ |«riemannSum»(g, n, p, t) - J| < ε / &2",
												By(mesh[1].At(n, p, t), partition))
											d.Show(
												"the Riemann sum of f + g is the sum of the Riemann sums of f and of g",
												Simp(Fwd(real_ring.RightDistrib), Rev(real_sum.IntervalAdd)),
												ByArith(near))
										}))))
						}))))
		}),
})}

// HasIntegralSum — a finite sum of functions with integrals c(k) on
// ⟦a, b⟧ has the sum of the c(k) as its integral.
//
// By induction on the last index n: a sum of one term is that term, and
// the sum up to suc(n) is the sum up to n plus the term at suc(n), whose
// integral the sum rule for integrals adds on.
var HasIntegralSum = hasIntegralSumThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralSum",
	Key:  "prop_50919559085be451",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → real → real). ∀c:(num → real). ∀a b:real. ∀n:num.",
		Hypotheses: []string{
			"∀k:num. k ≤ n ⇒ real_has_integral(u(k), a, b, c(k))",
		},
		Conclusion: "real_has_integral(λx:real. Σ_{k∈0 .. n} u(k)(x), a, b, Σ_{k∈0 .. n} c(k))",
	},
		func(arg *Argument, u *Arrow2[Nat, Real, Real], c *Arrow[Nat, Real], a, b *Expr[Real]) {
			arg.Induct("n")
			arg.Base(
				"a sum of the one term at 0 is u(0), whose integral is c(0)",
				func(d *Argument) {
					integrals := d.Assume()
					zero := d.TermAs[Nat]("0")
					d.Show(
						"the sums over 0 .. 0 are the terms at 0",
						By(integrals.At(zero), nat_order.LessEqRefl.At(zero), real_sum.IntervalPoint))
				})
			arg.Step(
				"the sum up to suc(n) is the sum up to n plus the term at suc(n), and integrals add",
				func(d *Argument, ih Fact) {
					integrals := d.Assume()
					n := d.TermAs[Nat]("n")
					next := d.TermAs[Nat]("suc(n)")
					upToN := d.Have(
						"in particular the terms up to n have their integrals",
						"∀k:num. k ≤ n ⇒ real_has_integral(u(k), a, b, c(k))",
						d.ForEach(func(k *Expr[Nat]) Action {
							return By(integrals.At(k), nat_order.LessEqSucClause.At(k, n))
						}))
					extended := d.Have(
						"so the sum up to n has its integral, and adding the term at suc(n) adds c(suc(n))",
						"real_has_integral(λx:real. Σ_{k∈0 .. n} u(k)(x) + u(suc(n))(x), "+
							"    a, "+
							"    b, "+
							"    Σ_{k∈0 .. n} c(k) + c(suc(n)))",
						By(
							ih,
							upToN,
							integrals.At(next),
							nat_order.LessEqRefl.At(next),
							HasIntegralAdd.At(
								d.TermAs[Fun[Real, Real]]("λx:real. Σ_{k∈0 .. n} u(k)(x)"),
								d.TermAs[Fun[Real, Real]]("u(suc(n))"),
								a,
								b,
								d.TermAs[Real]("Σ_{k∈0 .. n} c(k)"),
								c.Apply(next))))
					d.Show(
						"the sums up to suc(n) are the sums up to n plus the terms at suc(n)",
						Simp(Fwd(real_sum.IntervalClauses), Fwd(nat_order.ZeroLessEq)),
						By(extended))
				})
		}),
})}

// HasIntegralScale — the integral of a multiple is the multiple of the
// integral. Given ε, take the mesh below which the Riemann sums of f are
// within ε/(|c| + 1) of I: the Riemann sum of c·f is c times that of f, so
// it lies within |c|·ε/(|c| + 1) < ε of c·I.
var HasIntegralScale = hasIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralScale",
	Key:  "prop_ced6f9a0d0d06cbf",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I c:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_has_integral(λx:real. c * f(x), a, b, c * I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I, c *Expr[Real], toI Fact) {
			integral := arg.Conjuncts(
				arg.Unfolded(toI, RealHasIntegralDef),
				"the interval is ordered",
				"for every ε some mesh brings the Riemann sums of f within ε of I")
			arg.Do(Unfold(RealHasIntegralDef))
			arg.Show(
				"the Riemann sums of c·f tend to c·I",
				SplitConj(
					Case(
						"the interval is ordered",
						By(integral[0])),
					Case(
						"for every ε the mesh the integral of f gives at ε/(|c| + 1) serves",
						Derive(func(d *Argument) {
							ε := d.FixAs[Real]()
							pos := d.Assume()
							shrunk := d.TermAs[Real]("ε / (|c| + &1)")
							shrunkPos := d.Have(
								"ε/(|c| + 1) is positive",
								"&0 < ε / (|c| + &1)",
								ByArith(pos, real_order_field.DivPos.At(ε, d.TermAs[Real]("|c| + &1"))))
							small := d.Have(
								"and |c| times it is below ε",
								"|c| * (ε / (|c| + &1)) < ε",
								ByArith(pos, shrunkPos, real_sgn_abs.AbsNonneg.At(c)))
							δ, fine := d.ObtainAs[Real](
								"the mesh δ the integral of f gives at ε/(|c| + 1)",
								"∃δ:real. "+
									"    &0 < δ ∧ "+
									"    (∀n:num. ∀p t:(num → real). "+
									"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε / (|c| + &1))",
								By(integral[1].At(shrunk), shrunkPos))
							mesh := d.Conjuncts(
								fine,
								"δ is positive",
								"below δ the Riemann sums of f are within ε/(|c| + 1) of I")
							d.Take(δ)
							d.Show(
								"δ serves c·f",
								SplitConj(
									Case(
										"δ is positive",
										By(mesh[0])),
									Case(
										"below δ the Riemann sum of c·f is within |c|·ε/(|c| + 1) of c·I",
										Derive(func(e *Argument) {
											n := e.FixAs[Nat]()
											p := e.FixAs[Fun[Nat, Real]]()
											t := e.FixAs[Fun[Nat, Real]]()
											partition := e.Assume()
											scaled := e.Have(
												"|c| times the distance of f's Riemann sum from I is at most |c|·ε/(|c| + 1)",
												"|c| * |«riemannSum»(f, n, p, t) - I| ≤ |c| * (ε / (|c| + &1))",
												ByArith(mesh[1].At(n, p, t), partition, real_sgn_abs.AbsNonneg.At(c)))
											e.Show(
												"the Riemann sum of c·f is c times that of f, so its distance from c·I is |c| times f's from I",
												Simp(
													Rev(real_construction.MulAssoc),
													Rev(real_sum.ScalarLeft.Inst[Nat]()),
													Rev(real_ring.SubLeftDistrib),
													Fwd(real_sgn_abs.AbsMul)),
												ByArith(scaled, small))
										}))))
						}))))
		}),
})}

// RiemannIntegralScale — the integral of a multiple is the multiple of the
// integral, as values: c·f has integral c·I (HasIntegralScale), and each
// integral is the value it has.
var RiemannIntegralScale = riemannIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "RiemannIntegralScale",
	Key:  "prop_f2d07508fb6b9d82",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I c:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_integral(λx:real. c * f(x), a, b) = c * real_integral(f, a, b)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I, c *Expr[Real], toI Fact) {
			arg.Show(
				"c·f has integral c·I, and each integral is the value it has",
				By(
					toI,
					HasIntegralScale.At(f, a, b, I, c),
					HasIntegralValue.At(f, a, b, I),
					HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. c * f(x)"), a, b, arg.TermAs[Real]("c * I"))))
		}),
})}

// HasIntegralNeg — the integral of the negative is the negative of the
// integral: −f is (−1)·f, and −I is (−1)·I.
var HasIntegralNeg = hasIntegralNegThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralNeg",
	Key:  "prop_984d4b5d85900b60",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_has_integral(λx:real. -f(x), a, b, -I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI Fact) {
			scaled := arg.Simplified(
				GroupPremises(toI, HasIntegralScale.At(f, a, b, I, arg.TermAs[Real]("-&1"))),
				Fwd(real_ring.NegMinusOne))
			arg.Show(
				"(−1)·f has integral (−1)·I, and multiplying by −1 negates",
				By(scaled))
		}),
})}

// HasIntegralSub — the integral of a difference is the difference of the
// integrals: f − g is f + (−g), whose integral is I + (−J).
var HasIntegralSub = hasIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralSub",
	Key:  "prop_4133a72ffc4d935c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b I J:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"real_has_integral(g, a, b, J)",
		},
		Conclusion: "real_has_integral(λx:real. f(x) - g(x), a, b, I - J)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b, I, J *Expr[Real], toI, toJ Fact) {
			arg.Show(
				"f − g is f + (−g), and −g has integral −J",
				Simp(Fwd(real_ring.RealSubDef)),
				By(HasIntegralAdd, HasIntegralNeg, toI, toJ))
		}),
})}

// HasIntegralLessEq — integrals keep order: a function nowhere above
// another on ⟦a, b⟧ has no larger integral. Were J < I, the two integrals
// would share a mesh at ε = (I − J)/2. On a partition finer than it every
// tag lies in ⟦a, b⟧, so the Riemann sum of f is at most that of g; yet the
// one lies above I − ε and the other below J + ε, the same number.
var HasIntegralLessEq = hasIntegralLessEqThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralLessEq",
	Key:  "prop_160a93b649159243",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b I J:real.",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ f(x) ≤ g(x)",
			"real_has_integral(f, a, b, I)",
			"real_has_integral(g, a, b, J)",
		},
		Conclusion: "I ≤ J",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b, I, J *Expr[Real], below, toI, toJ Fact) {
			reversed := arg.SupposeNot()
			pos := arg.Have(
				"half the gap from J up to I is positive",
				"&0 < (I - J) / &2",
				ByArith(reversed))
			_, shared := arg.Obtain(
				"the two integrals share a mesh δ at ε = (I − J)/2",
				"∃δ:real. "+
					"    &0 < δ ∧ "+
					"    (∀n:num. ∀p t:(num → real). "+
					"        «finePartition»(a, b, δ, n, p, t) ⇒ "+
					"        |«riemannSum»(f, n, p, t) - I| < (I - J) / &2 ∧ "+
					"        |«riemannSum»(g, n, p, t) - J| < (I - J) / &2)",
				By(CommonMesh, toI, toJ, pos))
			mesh := arg.Conjuncts(
				shared,
				"δ is positive",
				"below δ the Riemann sums of f and g are within (I − J)/2 of I and of J")
			n, p, t, fine := arg.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
				"⟦a, b⟧ has a tagged partition finer than δ",
				"∃n:num. ∃p t:(num → real). «finePartition»(a, b, δ, n, p, t)",
				By(FinePartitionExists, HasIntegralOrdered.At(f, a, b, I), toI, mesh[0]))
			partition := arg.Conjuncts(
				fine,
				"its points start at a",
				"and end at b",
				"each tag lies in its piece, and each piece is shorter than δ")
			termwise := arg.Have(
				"piece by piece the term of f is at most that of g",
				"∀i:num. 0 ≤ i ∧ i ≤ n ⇒ f(t(i)) * (p(i + 1) - p(i)) ≤ g(t(i)) * (p(i + 1) - p(i))",
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]()
					inRange := c.Assume()
					inside := c.Have(
						"the tag t(i) lies in ⟦a, b⟧",
						"a ≤ t(i) ∧ t(i) ≤ b",
						By(PartitionTagsInInterval, partition[0], partition[1], partition[2], inRange))
					c.Show(
						"f(t(i)) ≤ g(t(i)) there, and the piece has nonnegative length",
						ByArith(below.At(c.TermAs[Real]("t(i)")), partition[2].At(i), inside, inRange))
				}))
			sums := arg.Have(
				"so the Riemann sum of f is at most that of g",
				"«riemannSum»(f, n, p, t) ≤ «riemannSum»(g, n, p, t)",
				By(real_sum.IntervalMonotone, termwise))
			arg.Show(
				"yet f's lies above I − (I − J)/2 and g's below J + (I − J)/2, which is the same number",
				ByArith(mesh[1].At(n, p, t), fine, sums))
		}),
})}

// RiemannIntegralNonneg — a function nonnegative on ⟦a, b⟧ has a nonnegative
// integral there: it is nowhere below the constant 0, whose integral is
// 0·(b − a) = 0 (HasIntegralConst), and integrals keep order.
var RiemannIntegralNonneg = riemannIntegralNonnegThm{family.Add(registry.ProofEntry{
	Name: "RiemannIntegralNonneg",
	Key:  "prop_671455111c6b6108",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ &0 ≤ f(x)",
		},
		Conclusion: "&0 ≤ real_integral(f, a, b)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI, nonnegative Fact) {
			zero := arg.TermAs[Real]("&0")
			zeroIntegral := arg.Have(
				"the constant 0 has integral 0·(b − a) = 0",
				"real_has_integral(λx:real. &0, a, b, &0)",
				ByArith(HasIntegralOrdered.At(f, a, b, I), toI, HasIntegralConst.At(a, b, zero)))
			arg.Show(
				"f is nowhere below 0 on ⟦a, b⟧, so its integral is at least 0's, and it is the value it has",
				By(
					Normalized,
					nonnegative,
					toI,
					zeroIntegral,
					HasIntegralLessEq.At(arg.TermAs[Fun[Real, Real]]("λx:real. &0"), f, a, b, zero, I),
					HasIntegralValue.At(f, a, b, I)))
		}),
})}

// HasIntegralBound — a function of size at most M on ⟦a, b⟧ has an
// integral of size at most M·(b − a): there −M ≤ f ≤ M, and integrals keep
// order against the constants −M and M, whose integrals are ∓M·(b − a).
var HasIntegralBound = hasIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralBound",
	Key:  "prop_efba9a2d652fc7bc",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I M:real.",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ M",
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "|I| ≤ M * (b - a)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I, M *Expr[Real], bounded, toI Fact) {
			between := arg.Have(
				"on ⟦a, b⟧ the function lies between −M and M",
				"∀x:real. a ≤ x ∧ x ≤ b ⇒ -M ≤ f(x) ∧ f(x) ≤ M",
				arg.ForEach(func(x *Expr[Real]) Action { return ByArith(bounded.At(x)) }))
			above := arg.Have(
				"the integral is at most that of the constant M, which is M·(b − a)",
				"I ≤ M * (b - a)",
				By(
					HasIntegralLessEq.At(
						f, arg.TermAs[Fun[Real, Real]]("λx:real. M"), a, b, I, arg.TermAs[Real]("M * (b - a)")),
					between,
					toI,
					HasIntegralConst.At(a, b, M),
					HasIntegralOrdered.At(f, a, b, I)))
			beneath := arg.Have(
				"and at least that of the constant −M, which is −M·(b − a)",
				"-M * (b - a) ≤ I",
				By(
					HasIntegralLessEq.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. -M"), f, a, b, arg.TermAs[Real]("-M * (b - a)"), I),
					between,
					toI,
					HasIntegralConst.At(a, b, arg.TermAs[Real]("-M")),
					HasIntegralOrdered.At(f, a, b, I)))
			arg.Show(
				"so I lies within M·(b − a) of 0",
				ByArith(above, beneath))
		}),
})}

// HasIntegralNearConstant — a function within M of a constant c on
// ⟦a, b⟧ has its integral within M·(b − a) of c·(b − a): the constant
// has integral c·(b − a), so f − c has integral I − c·(b − a), which
// the bound M on |f − c| bounds by M·(b − a).
var HasIntegralNearConstant = hasIntegralNearConstantThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralNearConstant",
	Key:  "prop_4839130e21952671",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I c M:real.",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x) - c| ≤ M",
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "|I - c * (b - a)| ≤ M * (b - a)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I, c, M *Expr[Real], near, toI Fact) {
			arg.Show(
				"f − c has integral I − c·(b − a), and |f − c| ≤ M bounds it by M·(b − a)",
				By(
					near,
					HasIntegralOrdered.At(f, a, b, I),
					toI,
					HasIntegralConst.At(a, b, c),
					HasIntegralSub.At(
						f, arg.TermAs[Fun[Real, Real]]("λx:real. c"), a, b, I, arg.TermAs[Real]("c * (b - a)")),
					HasIntegralBound.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. f(x) - c"),
						a,
						b,
						arg.TermAs[Real]("I - c * (b - a)"),
						M)))
		}),
})}
