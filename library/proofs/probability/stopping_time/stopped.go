// stopped.go — what a stopping time stops: the stopped sigma algebra is a
// sigma algebra inside the ambient one, the stopped process changes only
// before the stopping time and shows the stopped value once that time has
// passed, and the stopped value is measurable for the stopped sigma algebra
// while the stopped process stays adapted, both measurable for the ambient one.

package stopping_time

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// StoppedSigmaAlgebra — events observable at a stopping time form an ambient
// sub-sigma algebra: their restrictions commute with complements and countable unions.
var StoppedSigmaAlgebra = stoppedSigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "StoppedSigmaAlgebra",
	Key:  "prop_cea3ccf5b912af88",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀T:(A → option(num)).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. sigma_algebra_on(Ω, F(n))",
			"stopping_time_on(Ω, F, T)",
		},
		Conclusion: "sigma_algebra_on(Ω, stopped_sigma(Ω, S, F, T)) ∧ stopped_sigma(Ω, S, F, T) ⊆ S",
		Abbrev: Abbrev{
			{Name: "StoppedBy", Text: "λn:num. {x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))}"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		F *Arrow2[Nat, Set[A], Bool],
		T *Arrow[A, Option[Nat]],
		h Fact,
	) {
		algebras := a.Conjuncts(
			h,
			"the ambient family is a sigma algebra",
			"each observation family is a sigma algebra",
			"the time has observable finite stopping events")
		cutoffs := a.Have(
			"the finite stopping events are observable at their cutoffs",
			"∀n:num. «StoppedBy»(n) ∈ F(n)",
			By(algebras[2], StoppingTimeDef.At(Ω, F, T)))
		ambient := a.Have(
			"every stopped event is ambient measurable",
			"stopped_sigma(Ω, S, F, T) ⊆ S",
			BySets(StoppedSigmaDef.At(Ω, S, F, T)))
		carrier := a.Have(
			"the whole sample space is observable at the stopping time",
			"Ω ∈ stopped_sigma(Ω, S, F, T)",
			Simp(Fwd(StoppedSigmaDef)),
			Derive(func(a *Argument) {
				intersections := a.Have(
					"restricting the sample space retains each stopping event",
					"∀n:num. Ω ∩ «StoppedBy»(n) = «StoppedBy»(n)",
					BySets())
				a.Show(
					"the sample space is ambient measurable and has observable restrictions",
					By(intersections, cutoffs, algebras[0], sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		complements := a.Have(
			"relative complements remain observable at the stopping time",
			"∀E:set(A). E ∈ stopped_sigma(Ω, S, F, T) ⇒ Ω ∖ E ∈ stopped_sigma(Ω, S, F, T)",
			Derive(func(a *Argument) {
				a.FixAs[Set[A]]("E")
				event := a.Assume()
				properties := a.Conjuncts(
					a.Unfolded(event, StoppedSigmaDef),
					"the event is ambient measurable",
					"the event has observable finite restrictions")
				restrictions := a.Have(
					"each restricted complement is observable",
					"∀n:num. (Ω ∖ E) ∩ «StoppedBy»(n) ∈ F(n)",
					Derive(func(a *Argument) {
						n := a.FixAs[Nat]("n")
						difference := a.Have(
							"restriction turns a relative complement into a difference",
							"(Ω ∖ E) ∩ «StoppedBy»(n) = «StoppedBy»(n) ∖ (E ∩ «StoppedBy»(n))",
							BySets())
						a.Show(
							"the difference of the two observable events is observable",
							By(
								cutoffs.At(n),
								properties[1].At(n),
								algebras[1].At(n),
								difference,
								sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
					}))
				a.Show(
					"ambient complement closure and the finite restrictions give stopped measurability",
					Simp(Fwd(StoppedSigmaDef)),
					By(restrictions, properties[0], algebras[0], sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		unions := a.Have(
			"countable unions remain observable at the stopping time",
			Statement{
				Binders:    "∀q:(num → set(A)).",
				Hypotheses: []string{"∀j:num. q(j) ∈ stopped_sigma(Ω, S, F, T)"},
				Conclusion: "⋃image(q, 𝕌) ∈ stopped_sigma(Ω, S, F, T)",
			},
			Derive(func(a *Argument) {
				a.FixAs[Fun[Nat, Set[A]]]("q")
				events := a.Assume()
				restrictions := a.Have(
					"the countable union has observable finite restrictions",
					"∀n:num. ⋃image(q, 𝕌) ∩ «StoppedBy»(n) ∈ F(n)",
					Derive(func(a *Argument) {
						n := a.FixAs[Nat]("n")
						terms := a.Have(
							"each restricted term is observable at the fixed cutoff",
							"∀j:num. q(j) ∩ «StoppedBy»(n) ∈ F(n)",
							a.ForEach(func(j *Expr[Nat]) Action {
								return BySets(events.At(j), StoppedSigmaDef.At(Ω, S, F, T))
							}))
						distributes := a.Have(
							"restriction distributes over the countable union",
							"⋃image(q, 𝕌) ∩ «StoppedBy»(n) = ⋃image(λj:num. q(j) ∩ «StoppedBy»(n), 𝕌)",
							BySets())
						a.Show(
							"countable union closure in the observation sigma algebra applies",
							By(
								terms,
								algebras[1].At(n),
								distributes,
								sigma_algebra.SigmaAlgebraOnDef.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
					}))
				a.Show(
					"ambient union closure and the finite restrictions give stopped measurability",
					Simp(Fwd(StoppedSigmaDef)),
					BySets(events, restrictions, algebras[0], ambient, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		a.Show(
			"the stopped events form a sigma algebra contained in the ambient one",
			SplitConj(
				Case(
					"containment in the sample space and the three closure properties give a sigma algebra",
					Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)),
					BySets(
						complements,
						unions,
						carrier,
						algebras[0],
						ambient,
						sigma_algebra.SigmaAlgebraOnDef.At(Ω, S))),
				Case(
					"every stopped event belongs to the ambient sigma algebra",
					By(ambient))))
	}),
})}

// StoppedIncrement — stopping removes exactly the increments after the stopping time:
// the truncated index is fixed once reached, and advances with the cutoff beforehand.
var StoppedIncrement = stoppedIncrementThm{family.Add(registry.ProofEntry{
	Name: "StoppedIncrement",
	Reading: "It holds at every point with no hypotheses. " +
		"Where T is infinite the increment is never stopped.",
	Key: "prop_b4c69b776b51d602",
	Build: family.Sections(Statement{
		Binders: "∀M:(num → A → real). ∀T:(A → option(num)). ∀n:num. ∀x:A.",
		Conclusion: "stopped_process(M, T, n + 1, x) - stopped_process(M, T, n, x) = " +
			"COND(stopping_time_le(T(x), some(n)), &0, M(n + 1, x) - M(n, x))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			successorIndex := ctx.Lemma(
				"∀t:option(num). ∀n:num. "+
					"    stopping_time_min_nat(t, n + 1) = "+
					"    COND(stopping_time_le(t, some(n)), stopping_time_min_nat(t, n), n + 1)",
				func(a *Argument, t *Expr[Option[Nat]], n *Expr[Nat]) {
					nextBound := a.Have(
						"the next natural cutoff adds exactly its endpoint",
						"∀k:num. k ≤ n + 1 ⇔ k ≤ n ∨ k = n + 1",
						ByArith())
					nextCutoff := a.Have(
						"the next optional cutoff adds exactly the time n plus one",
						"stopping_time_le(t, some(n + 1)) ⇔ stopping_time_le(t, some(n)) ∨ t = some(n + 1)",
						By(nextBound, TimeLeSome.At(t, n), TimeLeSome.At(t, a.TermAs[Nat]("n + 1"))))
					a.Show(
						"the truncated index is fixed after stopping and advances beforehand",
						By(
							nextCutoff,
							TimeMinNatClauses.At(t, n),
							TimeMinNatClauses.At(t, a.TermAs[Nat]("n + 1")),
							option.SomeInjective.Inst[Nat]()))
				})
			return ctx.Theorem(headline,
				func(a *Argument, M *Arrow2[Nat, A, Real], T *Arrow[A, Option[Nat]], n *Expr[Nat], x *Expr[A]) {
					a.Cases(a.TermAs[Bool]("stopping_time_le(T(x), some(n))"))
					a.When(
						"the process has already stopped",
						func(a *Argument, stopped Fact) {
							a.Show(
								"equal truncated indices give zero increment",
								Simp(Fwd(StoppedProcessDef)),
								By(stopped, At(successorIndex, a.TermAs[Option[Nat]]("T(x)"), n), real_ring.SubRefl))
						})
					a.Otherwise(
						"the process has not yet stopped",
						func(a *Argument, running Fact) {
							a.Show(
								"the truncated indices are n and n plus one",
								Simp(Fwd(StoppedProcessDef)),
								By(
									Normalized,
									running,
									At(successorIndex, a.TermAs[Option[Nat]]("T(x)"), n),
									TimeMinNatClauses.At(a.TermAs[Option[Nat]]("T(x)"), n)))
						})
				})
		}),
})}

// StoppedValueSome — at a finite stopping value, evaluation selects the process
// at that index: constructor injectivity identifies the chosen witness.
var StoppedValueSome = stoppedValueSomeThm{family.Add(registry.ProofEntry{
	Name: "StoppedValueSome",
	Key:  "prop_f1a1d0b51ec1a281",
	Build: family.Theorem(Statement{
		Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀x:A. ∀k:num.",
		Hypotheses: []string{"T(x) = some(k)"},
		Conclusion: "stopped_value(M, T, x) = M(k, x)",
	}, func(a *Argument) {
		a.Show(
			"a finite stopping time selects its unique index",
			By(StoppedValueDef, option.NoneNotSome, option.SomeInjective))
	}),
})}

// StoppedProcessAtBound — once the stopping time has occurred by N, the process
// stopped and observed at N shows the stopped value: truncation at N keeps the
// finite time, and the stopped value reads the process there.
var StoppedProcessAtBound = stoppedProcessAtBoundThm{family.Add(registry.ProofEntry{
	Name: "StoppedProcessAtBound",
	Key:  "prop_308a83e3d41be52e",
	Build: family.Theorem(Statement{
		Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀N:num. ∀x:A.",
		Hypotheses: []string{"stopping_time_le(T(x), some(N))"},
		Conclusion: "stopped_process(M, T, N, x) = stopped_value(M, T, x)",
	}, func(
		a *Argument,
		M *Arrow2[Nat, A, Real],
		T *Arrow[A, Option[Nat]],
		N *Expr[Nat],
		x *Expr[A],
		reached Fact,
	) {
		a.Show(
			"the truncation at N is the finite stopping time, at which the stopped value reads the process",
			By(
				reached,
				TimeMinNatClauses.At(T.Apply(x), N),
				StoppedValueSome.At(M, T, x, a.TermAs[Nat]("stopping_time_min_nat(T(x), N)")),
				StoppedProcessDef.At(M, T, N, x)))
	}),
})}

// StoppedValueAtTruncation — the stopped value at the truncation of T at n is the
// process stopped at T and observed at n: both read M at the truncated index.
var StoppedValueAtTruncation = stoppedValueAtTruncationThm{family.Add(registry.ProofEntry{
	Name: "StoppedValueAtTruncation",
	Key:  "prop_83a439ca266bd130",
	Build: family.Theorem("∀M:(num → A → real). ∀T:(A → option(num)). ∀n:num. "+
		"    stopped_value(M, λx:A. some(stopping_time_min_nat(T(x), n))) = stopped_process(M, T, n)",
		func(a *Argument) {
			a.Show(
				"the finite truncation evaluates the stopped process at its cutoff",
				By(StoppedValueSome, StoppedProcessDef))
		}),
})}

// StoppedValueMeasurable — an adapted process evaluated at a stopping time is
// measurable at that time, and stopping preserves adaptation. Upper rays split
// into finite stopping levels and the zero-valued infinite level; truncation
// gives each observation of the stopped process.
var StoppedValueMeasurable = stoppedValueMeasurableThm{family.Add(registry.ProofEntry{
	Name: "StoppedValueMeasurable",
	Reading: "The points of Ω where T is infinite form Ω minus the union of the events " +
		"{T ≤ n}, which lies in S because every F(n) ⊆ S; the stopped value is zero there.",
	Key: "prop_88ac8eb289af915",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀F:(num → set(set(A))). " +
			"∀T:(A → option(num)). " +
			"∀M:(num → A → real).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"stopping_time_on(Ω, F, T)",
			"adapted_process(Ω, F, M)",
		},
		Conclusion: "real_measurable(Ω, «Stopped», stopped_value(M, T)) ∧ " +
			"adapted_process(Ω, F, stopped_process(M, T))",
		Abbrev: Abbrev{
			{Name: "Stopped", Text: "stopped_sigma(Ω, S, F, T)"},
			{Name: "Cut", Text: "λn:num. {x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))}"},
			{Name: "Level", Text: "λk:num. {x:A | x ∈ Ω ∧ T(x) = some(k)}"},
			{Name: "Infinite", Text: "{x:A | x ∈ Ω ∧ T(x) = none}"},
			{Name: "Piece", Text: "λc:real. λk:num. «Level»(k) ∩ {x:A | x ∈ Ω ∧ c < M(k, x)}"},
			{Name: "Ray", Text: "λc:real. {x:A | x ∈ Ω ∧ c < stopped_value(M, T, x)}"},
			{Name: "Trunc", Text: "λn:num. λx:A. some(stopping_time_min_nat(T(x), n))"},
			{Name: "CutU", Text: "λn:num. {x:A | x ∈ Ω ∧ stopping_time_le(U(x), some(n))}"},
			{Name: "StoppedU", Text: "stopped_sigma(Ω, S, F, U)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		infiniteValue := ctx.Lemma(Statement{
			Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀x:A.",
			Hypotheses: []string{"T(x) = none"},
			Conclusion: "stopped_value(M, T, x) = &0",
		}, func(a *Argument) {
			a.Show(
				"the infinite stopping value is zero",
				By(StoppedValueDef))
		})
		rayDecomposition := ctx.Lemma("∀Ω:set(A). ∀T:(A → option(num)). ∀M:(num → A → real). ∀c:real. "+
			"    «Ray»(c) = ⋃image(«Piece»(c), 𝕌) ∪ {x:A | x ∈ Ω ∧ T(x) = none ∧ c < &0}",
			func(
				a *Argument,
				Ω *Expr[Set[A]],
				T *Arrow[A, Option[Nat]],
				M *Arrow2[Nat, A, Real],
				c *Expr[Real],
			) {
				a.Show(
					"the ray splits over the finite levels and the infinite zero value",
					BySets(option.Cases.Inst[Nat](), StoppedValueSome.AsFact().At(M, T), At(infiniteValue, M, T)))
			})
		infiniteRestriction := ctx.Lemma("∀Ω:set(A). ∀T:(A → option(num)). ∀n:num. "+
			"    «Infinite» ∩ «Cut»(n) = ∅", func(a *Argument) {
			a.Show(
				"an infinite time misses every finite cutoff",
				BySets(TimeLeClauses))
		})
		levelRestrictions := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀F:(num → set(set(A))). " +
				"∀T:(A → option(num)). " +
				"∀k:num. " +
				"∀E:set(A).",
			Hypotheses: []string{"filtration_on(Ω, S, F)", "E ∈ F(k)", "E ⊆ «Level»(k)"},
			Conclusion: "∀n:num. E ∩ «Cut»(n) ∈ F(n)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			k *Expr[Nat],
			E *Expr[Set[A]],
			h Fact,
		) {
			n := a.FixAs[Nat]("n")
			a.Cases(a.TermAs[Bool]("k ≤ n"))
			a.When(
				"the level has occurred by the cutoff",
				func(a *Argument, within Fact) {
					same := a.Have(
						"restriction preserves the level event",
						"E ∩ «Cut»(n) = E",
						BySets(within, h, TimeLeClauses.At(k, n)))
					a.Show(
						"filtration monotonicity makes the event observable",
						same.Rw(),
						BySets(within, h, filtration.FiltrationMono.At(Ω, S, F, k, n)))
				})
			a.Otherwise(
				"the level lies beyond the cutoff",
				func(a *Argument, beyond Fact) {
					empty := a.Have(
						"no point of the level meets this cutoff",
						"E ∩ «Cut»(n) = ∅",
						BySets(beyond, h, TimeLeClauses.At(k, n)))
					a.Show(
						"the empty restriction is measurable",
						empty.Rw(),
						By(
							h,
							filtration.FiltrationDef.At(Ω, S, F),
							sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
				})
		})
		levelEvent := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀F:(num → set(set(A))). " +
				"∀T:(A → option(num)). " +
				"∀k:num. " +
				"∀E:set(A).",
			Hypotheses: []string{"filtration_on(Ω, S, F)", "E ∈ F(k)", "E ⊆ «Level»(k)"},
			Conclusion: "E ∈ «Stopped»",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			k *Expr[Nat],
			E *Expr[Set[A]],
			h Fact,
		) {
			properties := a.Conjuncts(
				h,
				"the observation sigma algebras form a filtration",
				"E is observable at the level's time",
				"E lies in the stopping level")
			a.Do(Unfold(StoppedSigmaDef))
			a.Show(
				"ambient measurability and observable restrictions give stopped measurability",
				BySets(
					properties[0],
					properties[1],
					properties[2],
					At(levelRestrictions, Ω, S, F, T, k, E),
					filtration.FiltrationDef.At(Ω, S, F)))
		})
		infiniteEvent := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀T:(A → option(num)).",
			Hypotheses: []string{"filtration_on(Ω, S, F)", "stopping_time_on(Ω, F, T)"},
			Conclusion: "«Infinite» ∈ «Stopped»",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			h Fact,
		) {
			cutoffs := a.Have(
				"the infinite level has measurable empty restrictions",
				"∀n:num. «Infinite» ∩ «Cut»(n) ∈ F(n)",
				Derive(func(a *Argument) {
					a.FixAs[Nat]("n")
					a.Show(
						"every restriction is the empty event",
						Simp(Fwd(infiniteRestriction)),
						By(
							h,
							filtration.FiltrationDef.At(Ω, S, F),
							sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
				}))
			ambient := a.Have(
				"the infinite level is an ambient event",
				"«Infinite» ∈ S",
				By(h, StoppingTimeLevelSets.At(Ω, S, F, T)))
			a.Do(Unfold(StoppedSigmaDef))
			a.Show(
				"the ambient infinite level is also observable at the stopping time",
				BySets(cutoffs, ambient))
		})
		infiniteRay := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀T:(A → option(num)). ∀c:real.",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, «Stopped»)",
				"filtration_on(Ω, S, F)",
				"stopping_time_on(Ω, F, T)",
			},
			Conclusion: "{x:A | x ∈ Ω ∧ T(x) = none ∧ c < &0} ∈ «Stopped»",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			c *Expr[Real],
			h Fact,
		) {
			premises := a.Conjuncts(
				h,
				"the stopped events form a sigma algebra",
				"the observation sigma algebras form a filtration",
				"T is a stopping time")
			a.Cases(a.TermAs[Bool]("c < &0"))
			a.When(
				"the ray contains zero",
				func(a *Argument, negative Fact) {
					whole := a.Have(
						"all of the infinite level contributes",
						"{x:A | x ∈ Ω ∧ T(x) = none ∧ c < &0} = «Infinite»",
						BySets(negative))
					a.Show(
						"the infinite level is stopped measurable",
						whole.Rw(),
						By(premises[1], premises[2], At(infiniteEvent, Ω, S, F, T)))
				})
			a.Otherwise(
				"the ray excludes zero",
				func(a *Argument, nonnegative Fact) {
					empty := a.Have(
						"no infinite-time value contributes",
						"{x:A | x ∈ Ω ∧ T(x) = none ∧ c < &0} = ∅",
						BySets(nonnegative))
					a.Show(
						"the empty portion is measurable",
						empty.Rw(),
						By(premises[0], sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("«Stopped»"))))
				})
		})
		finiteRay := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀F:(num → set(set(A))). " +
				"∀T:(A → option(num)). " +
				"∀M:(num → A → real). " +
				"∀c:real. " +
				"∀k:num.",
			Hypotheses: []string{
				"filtration_on(Ω, S, F)",
				"stopping_time_on(Ω, F, T)",
				"adapted_process(Ω, F, M)",
			},
			Conclusion: "«Piece»(c, k) ∈ «Stopped»",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			M *Arrow2[Nat, A, Real],
			c *Expr[Real],
			k *Expr[Nat],
			h Fact,
		) {
			observation := a.Have(
				"the kth observation is measurable in its sigma algebra",
				"sigma_algebra_on(Ω, F(k)) ∧ real_measurable(Ω, F(k), M(k))",
				By(h, filtration.FiltrationDef.At(Ω, S, F), filtration.AdaptedDef.At(Ω, F, M)))
			piece := a.Have(
				"intersect the measurable level with the observation's upper ray",
				"«Piece»(c, k) ∈ F(k)",
				By(
					observation,
					h,
					measurable_function.RealMeasurableIffRay.At(
						Ω, a.TermAs[Set[Set[A]]]("F(k)"), a.TermAs[Fun[A, Real]]("M(k)")),
					StoppingTimeLevelSets.At(Ω, S, F, T),
					sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(k)"))))
			a.Show(
				"a measurable event contained in this stopping level is stopped measurable",
				BySets(piece, h, At(levelEvent, Ω, S, F, T, k, a.TermAs[Set[A]]("«Piece»(c, k)"))))
		})
		stoppedValue := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀F:(num → set(set(A))). " +
				"∀T:(A → option(num)). " +
				"∀M:(num → A → real).",
			Hypotheses: []string{
				"filtration_on(Ω, S, F)",
				"stopping_time_on(Ω, F, T)",
				"adapted_process(Ω, F, M)",
			},
			Conclusion: "real_measurable(Ω, «Stopped», stopped_value(M, T))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			M *Arrow2[Nat, A, Real],
			h Fact,
		) {
			sigma := a.Have(
				"the stopped events form a sigma algebra",
				"sigma_algebra_on(Ω, «Stopped»)",
				By(h, filtration.FiltrationDef.At(Ω, S, F), StoppedSigmaAlgebra.At(Ω, S, F, T)))
			rays := a.Have(
				"every upper ray of the stopped value is measurable",
				"∀c:real. «Ray»(c) ∈ «Stopped»",
				Derive(func(a *Argument) {
					c := a.FixAs[Real]("c")
					finite := a.Have(
						"the countable union of finite ray pieces is measurable",
						"⋃image(«Piece»(c), 𝕌) ∈ «Stopped»",
						By(
							sigma,
							h,
							At(finiteRay, Ω, S, F, T, M, c),
							sigma_algebra.SigmaAlgebraOnDef.At(Ω, a.TermAs[Set[Set[A]]]("«Stopped»"))))
					a.Show(
						"the ray is the union of its finite and infinite portions",
						Simp(Fwd(rayDecomposition)),
						By(
							finite,
							h,
							At(infiniteRay, Ω, S, F, T, c),
							sigma,
							sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("«Stopped»"))))
				}))
			a.Show(
				"the upper-ray criterion proves real measurability",
				By(
					rays,
					sigma,
					measurable_function.RealMeasurableIffRay.At(
						Ω, a.TermAs[Set[Set[A]]]("«Stopped»"), a.TermAs[Fun[A, Real]]("stopped_value(M, T)"))))
		})
		boundedEvents := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀U:(A → option(num)). ∀n:num.",
			Hypotheses: []string{"sigma_algebra_on(Ω, S)", "∀x:A. x ∈ Ω ⇒ stopping_time_le(U(x), some(n))"},
			Conclusion: "«StoppedU» ⊆ F(n)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			U *Arrow[A, Option[Nat]],
			n *Expr[Nat],
			h Fact,
		) {
			unchanged := a.Have(
				"restriction at the bound preserves every ambient event",
				"∀E:set(A). E ∈ S ⇒ E ∩ «CutU»(n) = E",
				BySets(h, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			a.Do(Unfold(StoppedSigmaDef), Unfold(set_basic.SubsetDef))
			E := a.FixAs[Set[A]]("E")
			stopped := a.Assume()
			properties := a.Conjuncts(
				stopped,
				"the event is ambient measurable",
				"its cutoff restrictions are observable")
			a.Show(
				"at the bound its measurable restriction is the event itself",
				By(properties[0], unchanged.At(E), properties[1].At(n)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow2[Nat, Set[A], Bool],
			T *Arrow[A, Option[Nat]],
			M *Arrow2[Nat, A, Real],
			h Fact,
		) {
			a.Show(
				"stopped evaluation is measurable and the stopped process remains adapted",
				SplitConj(
					Case(
						"the stopping-time value is measurable",
						Cite(stoppedValue)),
					Case(
						"every finite observation of the stopped process is measurable",
						Simp(Fwd(filtration.AdaptedDef)),
						Derive(func(a *Argument) {
							n := a.FixAs[Nat]("n")
							U, uDef := a.LetAs[Fun[A, Option[Nat]]]("U", "«Trunc»(n)")
							bounded := a.Have(
								"the truncated time stops no later than n",
								"stopping_time_on(Ω, F, U) ∧ (∀x:A. x ∈ Ω ⇒ stopping_time_le(U(x), some(n)))",
								By(uDef, h, filtration.FiltrationDef.At(Ω, S, F), StoppingTruncation.At(Ω, F, T, n), TimeLeClauses))
							value := a.Have(
								"the truncated stopped value is measurable at its stopping time",
								"real_measurable(Ω, «StoppedU», stopped_value(M, U))",
								By(h, bounded, filtration.AdaptedDef.At(Ω, F, M), At(stoppedValue, Ω, S, F, U, M)))
							inclusion := a.Have(
								"all events at the truncated time are observable by n",
								"«StoppedU» ⊆ F(n)",
								By(bounded, h, filtration.FiltrationDef.At(Ω, S, F), At(boundedEvents, Ω, S, F, U, n)))
							a.Show(
								"transfer measurability to the observation sigma algebra",
								By(
									Normalized,
									uDef,
									inclusion,
									value,
									measurable_function.RealMeasurableSourceMono.At(
										Ω,
										a.TermAs[Set[Set[A]]]("«StoppedU»"),
										a.TermAs[Set[Set[A]]]("F(n)"),
										a.TermAs[Fun[A, Real]]("stopped_value(M, U)")),
									StoppedValueAtTruncation.At(M, T, n)))
						}))))
		})
	}),
})}

// StoppedAmbientMeasurable — the stopped value of an adapted process and each of
// its stopped observations are measurable for the ambient sigma algebra: the
// stopped sigma algebra and every time slice of the filtration lie inside it.
var StoppedAmbientMeasurable = stoppedAmbientMeasurableThm{family.Add(registry.ProofEntry{
	Name: "StoppedAmbientMeasurable",
	Key:  "prop_ed9d62d2aeee8c89",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀F:(num → set(set(A))). " +
			"∀T:(A → option(num)). " +
			"∀M:(num → A → real).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"stopping_time_on(Ω, F, T)",
			"adapted_process(Ω, F, M)",
		},
		Conclusion: "real_measurable(Ω, S, stopped_value(M, T)) ∧ " +
			"(∀n:num. real_measurable(Ω, S, stopped_process(M, T, n)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		F *Arrow2[Nat, Set[A], Bool],
		T *Arrow[A, Option[Nat]],
		M *Arrow2[Nat, A, Real],
		h Fact,
	) {
		inclusions := a.Have(
			"the stopped sigma algebra and all time slices lie in S",
			"stopped_sigma(Ω, S, F, T) ⊆ S ∧ (∀n:num. F(n) ⊆ S)",
			By(h, filtration.FiltrationDef.At(Ω, S, F), StoppedSigmaAlgebra.At(Ω, S, F, T)))
		a.Show(
			"measurability passes to the ambient sigma algebra",
			By(
				inclusions,
				h,
				StoppedValueMeasurable.At(Ω, S, F, T, M),
				filtration.AdaptedDef.At(Ω, F, a.TermAs[Fun2[Nat, A, Real]]("stopped_process(M, T)")),
				measurable_function.RealMeasurableSourceMono))
	}),
})}
