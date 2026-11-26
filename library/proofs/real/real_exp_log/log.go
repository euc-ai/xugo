// log.go — the logarithm, exp's inverse on the positive reals: its
// inverse laws, algebra, order, continuity and derivative, and its growth:
// 1/log(n + 1) tends to 0.

package real_exp_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// LogExp — log undoes exp. real_log(exp(x)) is the chosen u with
// exp(u) = exp(x); x itself is such a u, so the choice succeeds, and exp
// takes each value once, so the chosen u is x.
var LogExp = logExpThm{family.Add(registry.ProofEntry{
	Name: "LogExp",
	Key:  "prop_33cbc2c323601d65",
	Build: family.Theorem("∀x:real. log(exp(x)) = x",
		func(arg *Argument, x *Expr[Real]) {
			chosen := arg.Have(
				"the choice log(exp(x)) meets its condition",
				"exp(log(exp(x))) = exp(x)",
				Derive(func(d *Argument) {
					d.Do(Unfold(RealLogDef))
					preimage := d.Have(
						"exp(x) has a preimage, x itself",
						"∃u:real. exp(u) = exp(x)",
						Derive(func(e *Argument) {
							e.Take(x)
							e.Show(
								"exp maps x to exp(x)",
								Refl())
						}))
					d.Show(
						"so the chosen u is one",
						By(Normalized, preimage))
				}))
			arg.Show(
				"exp takes each value once, so log(exp(x)) is x",
				By(chosen, ExpInjective.At(arg.TermAs[Real]("log(exp(x))"), x)))
		}),
})}

// ExpLog — exp undoes log on the positive reals. real_log(y) is the
// chosen x with exp(x) = y, and for positive y there is one (exp takes
// every positive value), so the choice meets its condition.
var ExpLog = expLogThm{family.Add(registry.ProofEntry{
	Name: "ExpLog",
	Key:  "prop_e74082c3721378d5",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"&0 < y",
		},
		Conclusion: "exp(log(y)) = y",
	},
		func(arg *Argument, y *Expr[Real], positive Fact) {
			arg.Do(Unfold(RealLogDef))
			preimage := arg.Have(
				"a positive y is a value of exp",
				"∃x:real. exp(x) = y",
				By(positive, ExpSurjective.At(y)))
			arg.Show(
				"so the chosen x is one",
				By(Normalized, preimage))
		}),
})}

// LogOne — the logarithm of 1 is 0: 1 is exp(0), and log undoes exp.
var LogOne = logOneThm{family.Add(registry.ProofEntry{
	Name: "LogOne",
	Key:  "prop_be8ac74620075cd7",
	Build: family.Theorem("log(&1) = &0",
		func(arg *Argument) {
			arg.Show(
				"1 is exp(0), whose logarithm is 0",
				Simp(Rev(ExpZero)),
				Cite(LogExp, arg.TermAs[Real]("&0")))
		}),
})}

// LogMul — log turns products into sums: exp(log x + log y) is
// exp(log x)·exp(log y) = x·y, and log undoes exp.
var LogMul = logMulThm{family.Add(registry.ProofEntry{
	Name: "LogMul",
	Key:  "prop_9eb6f9fa01679261",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "log(x * y) = log(x) + log(y)",
	},
		func(arg *Argument, x, y *Expr[Real], positive Fact) {
			logX, logY := arg.TermAs[Real]("log(x)"), arg.TermAs[Real]("log(y)")
			product := arg.Have(
				"x·y is the exponential of log x + log y",
				"exp(log(x) + log(y)) = x * y",
				By(Normalized, positive, ExpAdd.At(logX, logY), ExpLog.At(x), ExpLog.At(y)))
			arg.Show(
				"so log(x·y) is log(exp(log x + log y)), which is log x + log y",
				product.RwRev(),
				Cite(LogExp, arg.TermAs[Real]("log(x) + log(y)")))
		}),
})}

// LogInv — the logarithm of a reciprocal is the negative of the
// logarithm: exp(−log x) is the inverse of exp(log x), which is x, so 1/x
// is exp(−log x), and log undoes exp.
var LogInv = logInvThm{family.Add(registry.ProofEntry{
	Name: "LogInv",
	Key:  "prop_3e23c1877f653339",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "log(real_inv(x)) = -log(x)",
	},
		func(arg *Argument, x *Expr[Real], positive Fact) {
			inverseAsExp := arg.Have(
				"exp(−log x) inverts exp(log x), which is x",
				"exp(-log(x)) = real_inv(x)",
				By(Normalized, positive, ExpNeg.At(arg.TermAs[Real]("log(x)")), ExpLog.At(x)))
			arg.Show(
				"so 1/x is exp(−log x), whose logarithm is −log x",
				inverseAsExp.RwRev(),
				Cite(LogExp, arg.TermAs[Real]("-log(x)")))
		}),
})}

// LogDiv — log turns quotients into differences: x/y is x·(1/y), and log
// turns the product into log x + log(1/y) = log x − log y.
var LogDiv = logDivThm{family.Add(registry.ProofEntry{
	Name: "LogDiv",
	Key:  "prop_d798482c4685df51",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "log(x / y) = log(x) - log(y)",
	},
		func(arg *Argument, x, y *Expr[Real], positive Fact) {
			parts := arg.Conjuncts(
				positive,
				"x is positive",
				"y is positive")
			xPositive, yPositive := parts[0], parts[1]
			reciprocal := arg.TermAs[Real]("real_inv(y)")
			reciprocalPositive := arg.Have(
				"1/y is positive as y is",
				"&0 < real_inv(y)",
				By(yPositive, real_order_field.InvPos.At(y)))
			split := arg.Have(
				"log(x·(1/y)) is log x + log(1/y)",
				"log(x * real_inv(y)) = log(x) + log(real_inv(y))",
				By(xPositive, reciprocalPositive, LogMul.At(x, reciprocal)))
			arg.Show(
				"x/y is x·(1/y), and log(1/y) is −log y",
				Simp(Fwd(real_field.RealDivDef)),
				ByArith(split, LogInv.At(y), yPositive))
		}),
})}

// LogPow — the logarithm turns a power into a multiple. exp turns the
// multiple n·log(x) into the power exp(log(x))ⁿ, which for positive x is
// xⁿ; so xⁿ is exp(n·log(x)), and log undoes exp.
var LogPow = logPowThm{family.Add(registry.ProofEntry{
	Name: "LogPow",
	Key:  "prop_15afa3b370995fef",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "log(real_pow(x, n)) = &n * log(x)",
	},
		func(arg *Argument, x *Expr[Real], n *Expr[Nat], positive Fact) {
			power := arg.Have(
				"xⁿ is exp(n·log(x)): exp makes the multiple a power of exp(log(x)), which is x",
				"exp(&n * log(x)) = real_pow(x, n)",
				By(Normalized, positive, ExpNatMul.At(n, arg.TermAs[Real]("log(x)")), ExpLog.At(x)))
			arg.Show(
				"so log(xⁿ) is log(exp(n·log(x))), which is n·log(x)",
				power.RwRev(),
				Cite(LogExp, arg.TermAs[Real]("&n * log(x)")))
		}),
})}

// LogProduct — a finite product of positive reals is positive, and its
// logarithm is the sum of the logarithms of its factors. By induction on
// the finite index set: the empty product is 1, whose logarithm is the
// empty sum 0, and adjoining a factor multiplies the product by it and
// adds its logarithm to the sum — the logarithm of a product of two
// positive reals being the sum of theirs.
var LogProduct = logProductThm{family.Add(registry.ProofEntry{
	Name: "LogProduct",
	Key:  "prop_796242eb532c89cb",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀x:A → real.",
		Hypotheses: []string{
			"finite(k)",
			"∀i:A. i ∈ k ⇒ &0 < x(i)",
		},
		Conclusion: "&0 < Π_{i∈k} x(i) ∧ log(Π_{i∈k} x(i)) = Σ_{i∈k} log(x(i))",
	}, func(a *Argument, k *Expr[Set[A]], finiteK Fact) {
		a.Show(
			"by induction on the finite index set, adjoining one fresh factor at a time",
			ByInduction(
				finite_set.FiniteInductFresh,
				finiteK,
				Case(
					"the empty product is 1, and its logarithm the empty sum 0",
					Simp(Fwd(real_product.ProductClauses), Fwd(real_sum.Clauses), Fwd(LogOne)),
					ByArith(),
				),
				Case(
					"adjoining a fresh factor at j to a finite set u",
					Derive(func(b *Argument) {
						b.FixAs[A]("j")
						b.FixAs[Set[A]]("u")
						step := b.Conjuncts(
							b.Assume(),
							"the claim holds over u",
							"j is not in u",
							"u is finite")
						x := b.FixAs[Fun[A, Real]]("x")
						positive := b.Assume()
						onU := b.Have(
							"the factors over u are positive",
							"∀i:A. i ∈ u ⇒ &0 < x(i)",
							BySets(positive))
						atJ := b.Have(
							"and so is x(j)",
							"&0 < x(j)",
							BySets(positive))
						peel := b.Have(
							"adjoining j multiplies the product by x(j) and adds log(x(j)) to the sum",
							"Π_{i∈insert(j, u)} x(i) = x(j) * Π_{i∈u} x(i) ∧ "+
								"Σ_{i∈insert(j, u)} log(x(i)) = log(x(j)) + Σ_{i∈u} log(x(i))",
							By(real_product.ProductClauses, real_sum.Clauses, step[2], step[1]),
						)
						overU := b.Have(
							"over u the product is positive and its logarithm is the sum",
							"&0 < Π_{i∈u} x(i) ∧ log(Π_{i∈u} x(i)) = Σ_{i∈u} log(x(i))",
							By(step[0].At(x), onU),
						)
						b.Show(
							"the logarithm of a product of two positive reals is the sum of theirs",
							ByArith(LogMul.At(b.TermAs[Real]("x(j)"), b.TermAs[Real]("Π_{i∈u} x(i)")), peel, overU, atJ),
						)
					}),
				),
			),
		)
	}),
})}

// LogLessIff — log is strictly increasing on the positive reals. exp is
// strictly increasing, so it orders log(x) and log(y) as they stand; and
// exp undoes log at the positive x and y, so the values it compares are
// x and y themselves.
var LogLessIff = logLessIffThm{family.Add(registry.ProofEntry{
	Name: "LogLessIff",
	Key:  "prop_517d9bfe305153ac",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "log(x) < log(y) ⇔ x < y",
	},
		func(arg *Argument, x, y *Expr[Real], positive Fact) {
			arg.Show(
				"exp orders log(x) and log(y) as it orders their "+
					"values, which exp undoes log to at the positive x and y",
				By(
					Normalized,
					positive,
					ExpLog.At(x),
					ExpLog.At(y),
					ExpLessIff.At(arg.TermAs[Real]("log(x)"), arg.TermAs[Real]("log(y)"))))
		}),
})}

// LogNonneg — the logarithm of a real at least 1 is nonnegative: log is
// increasing and vanishes at 1, so log x < 0 = log 1 would put x below 1.
var LogNonneg = logNonnegThm{family.Add(registry.ProofEntry{
	Name: "LogNonneg",
	Key:  "prop_ce27abe98d6aa1b5",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&1 ≤ x",
		},
		Conclusion: "&0 ≤ log(x)",
	},
		func(arg *Argument, x *Expr[Real], atLeastOne Fact) {
			arg.Show(
				"log x < log 1 = 0 would put x below 1, log being increasing",
				ByArith(atLeastOne, LogOne, LogLessIff.At(x, arg.TermAs[Real]("&1"))))
		}),
})}

// LogPowerLessEq — an inequality between powers of positive naturals survives
// taking logarithms: log is increasing, and it turns a power into a multiple
// of the logarithm of its base.
var LogPowerLessEq = logPowerLessEqThm{family.Add(registry.ProofEntry{
	Name: "LogPowerLessEq",
	Key:  "prop_af142d6662c1754a",
	Build: family.Theorem(Statement{
		Binders: "∀a b k l:num.",
		Hypotheses: []string{
			"1 ≤ a",
			"1 ≤ b",
			"a ^ k ≤ b ^ l",
		},
		Conclusion: "&k * log(&a) ≤ &l * log(&b)",
	},
		func(arg *Argument, a, b, k, l *Expr[Nat], positiveA, positiveB, ordered Fact) {
			baseA, baseB := arg.TermAs[Real]("&a"), arg.TermAs[Real]("&b")
			logs := arg.Have(
				"log is increasing, so log(aᵏ) ≤ log(bˡ)",
				"log(&a ^ k) ≤ log(&b ^ l)",
				ByArith(
					positiveA,
					ordered,
					real_pow.OfNumPow.At(a, k),
					real_pow.OfNumPow.At(b, l),
					real_pow.PowPos.At(baseA, k),
					LogLessIff.At(arg.TermAs[Real]("&b ^ l"), arg.TermAs[Real]("&a ^ k"))))
			arg.Show(
				"and log(aᵏ) = k·log a, log(bˡ) = l·log b",
				ByArith(positiveA, positiveB, logs, LogPow.At(baseA, k), LogPow.At(baseB, l)))
		}),
})}

// LogContinuous — log is continuous at every positive y, because exp is
// strictly increasing. Given ε, y = exp(log y) lies strictly between
// exp(log y − ε) and exp(log y + ε), and the radius is y's distance to
// the nearer of the two. A point x within it lies between them as well,
// so x is positive and x = exp(log x); exp orders log x against
// log y ∓ ε as it orders x against exp(log y ∓ ε), which puts log x
// within ε of log y.
var LogContinuous = logContinuousThm{family.Add(registry.ProofEntry{
	Name: "LogContinuous",
	Key:  "prop_3d979277091dd149",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"&0 < y",
		},
		Conclusion: "real_continuous_at(real_log, y)",
	},
		func(arg *Argument, y *Expr[Real], positive Fact) {
			logY := arg.TermAs[Real]("log(y)")

			arg.Do(Simp(Fwd(real_continuous.RealContinuousAtDef)))
			// ↦ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ (∀x. |x − y| < δ ⇒ |log x − log y| < ε)
			arg.FixAs[Real]("ε")
			epsilonPositive := arg.Assume()
			lower := arg.TermAs[Real]("log(y) - ε")
			upper := arg.TermAs[Real]("log(y) + ε")
			yBetween := arg.Have(
				"exp is increasing, so y = exp(log y) lies strictly between exp(log y − ε) and exp(log y + ε)",
				"exp(log(y) - ε) < y ∧ y < exp(log(y) + ε)",
				ByArith(
					positive,
					epsilonPositive,
					ExpLog.At(y),
					ExpLessIff.At(lower, logY),
					ExpLessIff.At(logY, upper)))

			gapBelow := arg.TermAs[Real]("y - exp(log(y) - ε)")
			gapAbove := arg.TermAs[Real]("exp(log(y) + ε) - y")
			arg.Take(arg.TermAs[Real]("min(y - exp(log(y) - ε), exp(log(y) + ε) - y)"))
			arg.Do(SplitConj(
				Case(
					"the radius, y's distance to the nearer of the two, is positive",
					ByArith(yBetween, real_sup_inf.LessThanMin.At(gapBelow, gapAbove, arg.TermAs[Real]("&0")))),
				Case(
					"and within it log moves by less than ε",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						near := b.Assume()
						xBetween := b.Have(
							"a distance below both gaps keeps x between exp(log y − ε) and exp(log y + ε) too",
							"exp(log(y) - ε) < x ∧ x < exp(log(y) + ε)",
							ByArith(near, real_sup_inf.LessThanMin.At(gapBelow, gapAbove, b.TermAs[Real]("|x - y|"))))
						xPositive := b.Have(
							"so x is positive, exp(log y − ε) being positive",
							"&0 < x",
							ByArith(xBetween, ExpPositive.At(lower)))
						logX := b.TermAs[Real]("log(x)")
						b.Show(
							"x = exp(log x), and exp orders log x against log y ∓ ε as it orders x against exp(log y ∓ ε)",
							ByArith(xPositive, xBetween, ExpLog.At(x), ExpLessIff.At(lower, logX), ExpLessIff.At(logX, upper)))
					})),
			))
		}),
})}

// LogDerivative — log′(y) = 1/y. exp has derivative exp(log y) = y at
// log y, which is not 0; log is continuous at y; and on the ball of
// radius y about y every point is positive, so exp undoes log there. The
// derivative of an inverse function is the reciprocal of the derivative.
var LogDerivative = logDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LogDerivative",
	Key:  "prop_d6d05e0d3779d4c9",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"&0 < y",
		},
		Conclusion: "real_derivative_at(real_log, y, real_inv(y))",
	},
		func(arg *Argument, y *Expr[Real], positive Fact) {
			logY := arg.TermAs[Real]("log(y)")
			radius := y
			undoes := arg.Have(
				"within the radius y of y every point is positive, so exp undoes log there",
				"∀x:real. |x - y| < y ⇒ exp(log(x)) = x",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					near := d.Assume()
					xPositive := d.Have(
						"x is positive",
						"&0 < x",
						ByArith(near))
					d.Show(
						"so exp undoes log at x",
						By(xPositive, ExpLog.At(x)))
				}))
			value := arg.Have(
				"the derivative of exp at log y is exp(log y), which is y",
				"exp(log(y)) = y",
				By(positive, ExpLog.At(y)))
			nonzero := arg.Have(
				"that derivative is not 0, exp being positive",
				"exp(log(y)) ≠ &0",
				ByArith(ExpPositive.At(logY)))
			inverse := arg.Have(
				"the inverse rule, read at exp and log on the ball of radius y — positive, as y is",
				"real_derivative_at(real_log, y, real_inv(exp(log(y))))",
				By(
					ExpDerivative.At(logY),
					nonzero,
					positive,
					LogContinuous.At(y),
					undoes,
					real_derivative.DerivativeInverse.At(arg.TermAs[Fun[Real, Real]]("real_exp"),
						arg.TermAs[Fun[Real, Real]]("real_log"), y, arg.TermAs[Real]("exp(log(y))"), radius)))
			arg.Show(
				"and exp(log y) is y",
				By(Normalized, inverse, value))
		}),
})}

// ReciprocalLogTendsToZero — 1/log(n + 1) tends to 0: past exp(1/ε) the
// logarithm exceeds 1/ε, so its reciprocal is positive and below ε.
var ReciprocalLogTendsToZero = reciprocalLogTendsToZeroThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalLogTendsToZero",
	Key:  "prop_e76a6c44d6416126",
	Build: family.Theorem("(λn:num. &1 / log(&(n + 1))) ⟶ &0", func(arg *Argument) {
		one := arg.TermAs[Real]("&1")
		arg.Do(Unfold(real_sequences.RealConvergesToDef))
		arg.FixAs[Real]("ε")
		positive := arg.Assume()
		L := arg.TermAs[Real]("&1 / ε")
		threshold := arg.TermAs[Real]("exp(&1 / ε)")
		J, above := arg.ObtainAs[Nat](
			"an integer above the exponential threshold",
			"∃J:num. exp(&1 / ε) ≤ &J",
			By(real_archimedean.ExistsNumAbove.At(threshold)),
			Named("J"))
		arg.Take(J)
		n := arg.FixAs[Nat]("n")
		large := arg.Assume()
		x := arg.TermAs[Real]("&(n + 1)")
		base := arg.Have(
			"the shifted index is strictly above the exponential threshold",
			"exp(&1 / ε) < &(n + 1)",
			ByArith(above, large, real_construction.OfNumLessEq.At(J, n)))
		logAbove := arg.Have(
			"take logarithms to get the required threshold",
			"&1 / ε < log(&(n + 1))",
			ByArith(base, ExpPositive.At(L), LogLessIff.At(threshold, x), LogExp.At(L)))
		ε := arg.TermAs[Real]("ε")
		logarithm := arg.TermAs[Real]("log(&(n + 1))")
		logPositive := arg.Have(
			"the logarithm is positive",
			"&0 < log(&(n + 1))",
			ByArith(logAbove, positive, real_order_field.DivPos.At(one, ε)))
		product := arg.Have(
			"multiply the threshold comparison by epsilon",
			"&1 < log(&(n + 1)) * ε",
			By(logAbove, positive, real_order_field.LessThanDivMulRight.At(one, logarithm, ε)))
		reciprocal := arg.Have(
			"the reciprocal is positive and smaller than epsilon",
			"&0 < &1 / log(&(n + 1)) ∧ &1 / log(&(n + 1)) < ε",
			ByArith(
				product,
				logPositive,
				real_order_field.DivPos.At(one, logarithm),
				real_order_field.LessThanDivMulRight.At(one, ε, logarithm)))
		arg.Show(
			"the modulus of the reciprocal is its positive value",
			Simp(Fwd(real_ring.SubRightZero)),
			ByArith(reciprocal, real_sgn_abs.AbsFixedIffNonneg.At(arg.TermAs[Real]("&1 / log(&(n + 1))"))))
	}),
})}
