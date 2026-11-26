// times.go — stopping times and the operations on them. The order on optional
// times is the natural order on finite values with none greatest; constants,
// minima, maxima and truncations of stopping times are stopping times; the
// level sets of a stopping time are observable at their times; and its
// extended value is measurable.

package stopping_time

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// TimeLeClauses — the order on optional times at each pair of constructors:
// finite times compare as natural numbers, and none is the greatest time.
var TimeLeClauses = timeLeClausesThm{family.Add(registry.ProofEntry{
	Name: "TimeLeClauses",
	Key:  "prop_837c2003a866b8a2",
	Build: family.Theorem("∀m n:num. "+
		"    (stopping_time_le(some(m), some(n)) ⇔ m ≤ n) ∧ "+
		"    stopping_time_le(some(m), none) ∧ "+
		"    stopping_time_le(none, none) ∧ "+
		"    ¬stopping_time_le(none, some(n))",
		func(a *Argument) {
			a.Show(
				"finite values have the natural order and none is the greatest value",
				By(TimeLeDef, option.NoneNotSome.Inst[Nat](), option.SomeInjective.Inst[Nat]()))
		}),
})}

// TimeLeTrans — the order on optional times is transitive: finite comparisons
// compose as natural numbers, and a comparison ending at none holds outright.
var TimeLeTrans = timeLeTransThm{family.Add(registry.ProofEntry{
	Name: "TimeLeTrans",
	Key:  "prop_84ab5e69f3421fe7",
	Build: family.Theorem(Statement{
		Binders:    "∀r s t:option(num).",
		Hypotheses: []string{"stopping_time_le(r, s)", "stopping_time_le(s, t)"},
		Conclusion: "stopping_time_le(r, t)",
	}, func(a *Argument) {
		a.Show(
			"finite comparisons compose and infinity is the greatest time",
			By(
				TimeLeDef,
				option.NoneNotSome.Inst[Nat](),
				option.SomeInjective.Inst[Nat](),
				nat_order.LessEqTrans))
	}),
})}

// TimeLeSome — an optional time lies below a finite cutoff exactly when it has a
// finite value below that cutoff: unfold the order and identify the finite endpoint.
var TimeLeSome = timeLeSomeThm{family.Add(registry.ProofEntry{
	Name: "TimeLeSome",
	Key:  "prop_a522d732ce1e2f33",
	Build: family.Theorem("∀t:option(num). ∀n:num. "+
		"    stopping_time_le(t, some(n)) ⇔ ∃k:num. t = some(k) ∧ k ≤ n",
		func(a *Argument) {
			a.Show(
				"meeting a finite cutoff means having a finite value at most the cutoff",
				By(TimeLeDef, option.NoneNotSome.Inst[Nat](), option.SomeInjective.Inst[Nat]()))
		}),
})}

// TimeMinNatClauses — truncation at a cutoff n: a time that has reached n is
// its own truncation, and a time beyond n is truncated to n.
var TimeMinNatClauses = timeMinNatClausesThm{family.Add(registry.ProofEntry{
	Name: "TimeMinNatClauses",
	Key:  "prop_93b7fd688c019823",
	Build: family.Theorem("∀t:option(num). ∀n:num. "+
		"    (stopping_time_le(t, some(n)) ⇒ some(stopping_time_min_nat(t, n)) = t) ∧ "+
		"    (¬stopping_time_le(t, some(n)) ⇒ stopping_time_min_nat(t, n) = n)",
		func(a *Argument) {
			a.Show(
				"truncation retains a reached time and otherwise takes the cutoff",
				By(TimeMinNatDef, TimeLeSome))
		}),
})}

// StoppingConstants — constant finite times and the infinite time are stopping times:
// their finite stopping events are the whole carrier or the empty set.
var StoppingConstants = stoppingConstantsThm{family.Add(registry.ProofEntry{
	Name: "StoppingConstants",
	Reading: "stopping_time_le(none, some(n)) is false, so " +
		"every stopping event of the constant infinite time is empty.",
	Key: "prop_269dc33f5afaa6d7",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀F:(num → set(set(A))). ∀n:num.",
		Hypotheses: []string{"∀k:num. sigma_algebra_on(Ω, F(k))"},
		Conclusion: "stopping_time_on(Ω, F, λx:A. some(n)) ∧ stopping_time_on(Ω, F, λx:A. none)",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			F *Arrow2[Nat, Set[A], Bool],
			n *Expr[Nat],
			sigma Fact,
		) {
			trivialEvents := a.Have(
				"the carrier and empty event are measurable at every time",
				"∀k:num. Ω ∈ F(k) ∧ ∅ ∈ F(k)",
				By(sigma, sigma_algebra.SigmaFiniteOperations, sigma_algebra.SigmaAlgebraOnDef))
			a.Show(
				"both constant times have measurable finite stopping events",
				Unfold(StoppingTimeDef),
				SplitConj(
					Case(
						"the finite time has occurred exactly when n is at most the observation time",
						Derive(func(a *Argument) {
							k := a.FixAs[Nat]("k")
							a.Cases(a.TermAs[Bool]("n ≤ k"))
							a.When(
								"at and after n, the stopping event is the whole carrier",
								func(a *Argument, reached Fact) {
									event := a.Have(
										"every point has stopped",
										"{x:A | x ∈ Ω ∧ stopping_time_le(some(n), some(k))} = Ω",
										BySets(TimeLeClauses.At(n, k), reached))
									a.Show(
										"the carrier belongs to the observation sigma algebra",
										By(trivialEvents.At(k), event))
								})
							a.Otherwise(
								"before n, the stopping event is empty",
								func(a *Argument, before Fact) {
									event := a.Have(
										"no point has stopped",
										"{x:A | x ∈ Ω ∧ stopping_time_le(some(n), some(k))} = ∅",
										BySets(TimeLeClauses.At(n, k), before))
									a.Show(
										"the empty event belongs to the observation sigma algebra",
										By(trivialEvents.At(k), event))
								})
						})),
					Case(
						"the infinite time has never occurred by a finite observation time",
						Derive(func(a *Argument) {
							k := a.FixAs[Nat]("k")
							event := a.Have(
								"the infinite time has an empty stopping event",
								"{x:A | x ∈ Ω ∧ stopping_time_le(none, some(k))} = ∅",
								BySets(TimeLeClauses.At(n, k)))
							a.Show(
								"the empty event is measurable",
								By(trivialEvents.At(k), event))
						}))))
		}),
})}

// StoppingMinMax — minima and maxima of stopping times are stopping times:
// their finite stopping events are unions and intersections of the original events.
var StoppingMinMax = stoppingMinMaxThm{family.Add(registry.ProofEntry{
	Name: "StoppingMinMax",
	Key:  "prop_e9f051352a92997c",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀F:(num → set(set(A))). ∀T U:(A → option(num)).",
		Hypotheses: []string{
			"∀k:num. sigma_algebra_on(Ω, F(k))",
			"stopping_time_on(Ω, F, T)",
			"stopping_time_on(Ω, F, U)",
		},
		Conclusion: "stopping_time_on(Ω, F, λx:A. COND(stopping_time_le(T(x), U(x)), T(x), U(x))) ∧ " +
			"stopping_time_on(Ω, F, λx:A. COND(stopping_time_le(T(x), U(x)), U(x), T(x)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		cutoffs := ctx.Lemma("∀s t:option(num). ∀n:num. "+
			"    (stopping_time_le(COND(stopping_time_le(s, t), s, t), some(n)) ⇔ "+
			"        stopping_time_le(s, some(n)) ∨ stopping_time_le(t, some(n))) ∧ "+
			"    (stopping_time_le(COND(stopping_time_le(s, t), t, s), some(n)) ⇔ "+
			"        stopping_time_le(s, some(n)) ∧ stopping_time_le(t, some(n)))",
			func(a *Argument, s, t *Expr[Option[Nat]], n *Expr[Nat]) {
				a.Induct(s)
				a.Base(
					"when s is infinite, the minimum is t and the maximum is infinite",
					func(a *Argument) {
						a.Induct(t)
						a.Base(
							"two infinite times miss every finite cutoff",
							Simp(Fwd(TimeLeClauses)),
							TrivialNormalized())
						a.Step(
							"only the finite second time can meet the cutoff",
							Simp(Fwd(TimeLeClauses)),
							TrivialNormalized())
					})
				a.Step(
					"when s is finite, compare the second time with its value",
					func(a *Argument) {
						i := ext.As[Nat](a.StepArgs("i")[0])
						a.Induct(t)
						a.Base(
							"a finite first time precedes an infinite second time",
							Simp(Fwd(TimeLeClauses)),
							TrivialNormalized())
						a.Step(
							"two finite times are compared by their natural values",
							func(a *Argument) {
								j := ext.As[Nat](a.StepArgs("j")[0])
								a.Do(Simp(Fwd(TimeLeClauses)))
								a.Cases(a.TermAs[Bool]("i ≤ j"))
								a.When(
									"if i is at most j, the minimum is i and the maximum is j",
									func(a *Argument, ordered Fact) {
										a.Show(
											"a cutoff containing j also contains i",
											Simp(Fwd(TimeLeClauses), Fwd(ordered)),
											By(ordered, nat_order.LessEqTrans.At(i, j, n)))
									})
								a.Otherwise(
									"if i exceeds j, the minimum is j and the maximum is i",
									func(a *Argument, reversed Fact) {
										a.Show(
											"totality reverses the comparison and transfers the cutoff",
											Simp(Fwd(TimeLeClauses), Fwd(reversed)),
											By(reversed, nat_order.LessEqTotal.At(i, j), nat_order.LessEqTrans.At(j, i, n)))
									})
							})
					})
			})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				Ω *Expr[Set[A]],
				F *Arrow2[Nat, Set[A], Bool],
				T, U *Arrow[A, Option[Nat]],
				assumptions Fact,
			) {
				parts := a.Conjuncts(
					assumptions,
					"every observation family is a sigma algebra",
					"T is a stopping time",
					"U is a stopping time")
				tEvents := a.Unfolded(parts[1], StoppingTimeDef)
				uEvents := a.Unfolded(parts[2], StoppingTimeDef)
				a.Show(
					"the minimum and maximum have measurable stopping events",
					Simp(Fwd(StoppingTimeDef)),
					SplitConj(
						Case(
							"the minimum has stopped when either original time has stopped",
							Derive(func(a *Argument) {
								n := a.FixAs[Nat]("n")
								event := a.Have(
									"the minimum stopping event is the union",
									"{x:A | x ∈ Ω ∧ stopping_time_le(COND(stopping_time_le(T(x), U(x)), T(x), U(x)), some(n))} = "+
										"{x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))} ∪ {x:A | x ∈ Ω ∧ stopping_time_le(U(x), some(n))}",
									BySets(cutoffs))
								a.Show(
									"the union of the two measurable events is measurable",
									By(
										parts[0].At(n),
										tEvents.At(n),
										uEvents.At(n),
										event,
										sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
							})),
						Case(
							"the maximum has stopped when both original times have stopped",
							Derive(func(a *Argument) {
								n := a.FixAs[Nat]("n")
								event := a.Have(
									"the maximum stopping event is the intersection",
									"{x:A | x ∈ Ω ∧ stopping_time_le(COND(stopping_time_le(T(x), U(x)), U(x), T(x)), some(n))} = "+
										"{x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))} ∩ {x:A | x ∈ Ω ∧ stopping_time_le(U(x), some(n))}",
									BySets(cutoffs))
								a.Show(
									"the intersection of the two measurable events is measurable",
									By(
										parts[0].At(n),
										tEvents.At(n),
										uEvents.At(n),
										event,
										sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
							}))))
			})
	}),
})}

// StoppingTruncation — truncating a stopping time at a finite cutoff gives a
// stopping time bounded by that cutoff, by taking its minimum with a constant time.
var StoppingTruncation = stoppingTruncationThm{family.Add(registry.ProofEntry{
	Name: "StoppingTruncation",
	Key:  "prop_6fb6636adf60504f",
	Build: family.Sections(Statement{
		Binders:    "∀Ω:set(A). ∀F:(num → set(set(A))). ∀T:(A → option(num)). ∀n:num.",
		Hypotheses: []string{"∀k:num. sigma_algebra_on(Ω, F(k))", "stopping_time_on(Ω, F, T)"},
		Conclusion: "stopping_time_on(Ω, F, λx:A. some(stopping_time_min_nat(T(x), n))) ∧ " +
			"(∀x:A. stopping_time_min_nat(T(x), n) ≤ n)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		truncate := ctx.Lemma("∀t:option(num). ∀n:num. "+
			"    some(stopping_time_min_nat(t, n)) = COND(stopping_time_le(t, some(n)), t, some(n)) ∧ "+
			"    stopping_time_min_nat(t, n) ≤ n",
			func(a *Argument, t *Expr[Option[Nat]], n *Expr[Nat]) {
				a.Cases(a.TermAs[Bool]("stopping_time_le(t, some(n))"))
				a.When(
					"a time within the cutoff retains its finite value",
					func(a *Argument, within Fact) {
						a.Show(
							"the chosen finite witness is the minimum and lies below the cutoff",
							By(within, TimeMinNatClauses.At(t, n), TimeLeSome.At(t, n), option.SomeInjective.Inst[Nat]()))
					})
				a.Otherwise(
					"a time beyond the cutoff is replaced by the cutoff",
					func(a *Argument, beyond Fact) {
						a.Show(
							"the fallback value is the cutoff itself",
							By(beyond, TimeMinNatClauses.At(t, n), nat_order.LessEqRefl))
					})
			})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				Ω *Expr[Set[A]],
				F *Arrow2[Nat, Set[A], Bool],
				T *Arrow[A, Option[Nat]],
				n *Expr[Nat],
				assumptions Fact,
			) {
				a.Show(
					"truncation is a stopping time bounded by its cutoff",
					SplitConj(
						Case(
							"truncation is the minimum with a constant stopping time",
							Derive(func(a *Argument) {
								same := a.Have(
									"the truncated function is the minimum with the constant cutoff",
									"(λx:A. some(stopping_time_min_nat(T(x), n))) = "+
										"(λx:A. COND(stopping_time_le(T(x), some(n)), T(x), some(n)))",
									By(truncate))
								a.Show(
									"the minimum of two stopping times is a stopping time",
									same.Rw(),
									By(
										assumptions,
										StoppingConstants.At(Ω, F, n),
										StoppingMinMax.At(Ω, F, T, a.TermAs[Fun[A, Option[Nat]]]("λx:A. some(n)"))))
							})),
						Case(
							"every truncated value is at most the cutoff",
							By(truncate))))
			})
	}),
})}

// StoppingTimeLevelSets — a finite stopping level is measurable at its own time,
// and the infinite level is ambient measurable: successive cutoff differences
// give the finite levels, and their countable union has the infinite level as its complement.
var StoppingTimeLevelSets = stoppingTimeLevelSetsThm{family.Add(registry.ProofEntry{
	Name: "StoppingTimeLevelSets",
	Key:  "prop_937b3ef9d6ff897",
	Build: family.Sections(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀T:(A → option(num)).",
		Hypotheses: []string{"filtration_on(Ω, S, F)", "stopping_time_on(Ω, F, T)"},
		Conclusion: "(∀n:num. {x:A | x ∈ Ω ∧ T(x) = some(n)} ∈ F(n)) ∧ {x:A | x ∈ Ω ∧ T(x) = none} ∈ S",
		Abbrev:     Abbrev{{Name: "C", Text: "λn:num. {x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))}"}},
	}, func(ctx *Script, headline string) *GoalStackNode {
		zeroLevel := ctx.Lemma(
			"∀t:option(num). t = some(0) ⇔ stopping_time_le(t, some(0))",
			func(a *Argument) {
				a.Show(
					"only zero lies below the zero cutoff",
					By(TimeLeSome, nat_order.LessEqZeroClause))
			})
		successorLevel := ctx.Lemma(
			"∀t:option(num). ∀n:num. "+
				"    t = some(n + 1) ⇔ stopping_time_le(t, some(n + 1)) ∧ ¬stopping_time_le(t, some(n))",
			func(a *Argument, t *Expr[Option[Nat]], n *Expr[Nat]) {
				interval := a.Have(
					"passing to the next cutoff adds just its endpoint",
					"∀k:num. k ≤ n + 1 ⇔ k ≤ n ∨ k = n + 1",
					ByArith())
				strict := a.Have(
					"the next endpoint is beyond the preceding cutoff",
					"¬(n + 1 ≤ n)",
					ByArith())
				a.Iff()
				a.Forward(
					"the endpoint meets the next cutoff and misses the preceding one",
					func(a *Argument, endpoint Fact) {
						a.Show(
							"the two cutoff conditions hold",
							By(
								strict,
								endpoint,
								TimeLeSome.At(t, n),
								TimeLeSome.At(t, a.TermAs[Nat]("n + 1")),
								option.SomeInjective.Inst[Nat](),
								nat_order.LessEqRefl.At(a.TermAs[Nat]("n + 1"))))
					})
				a.Backward(
					"A value between consecutive cutoffs is their new endpoint",
					func(a *Argument, between Fact) {
						a.Show(
							"the finite value is n + 1",
							By(interval, between, TimeLeSome.At(t, n), TimeLeSome.At(t, a.TermAs[Nat]("n + 1"))))
					})
			})
		infiniteLevel := ctx.Lemma(
			"∀t:option(num). t = none ⇔ ¬(∃n:num. stopping_time_le(t, some(n)))",
			func(a *Argument) {
				a.Induct("t")
				a.Base(
					"infinity misses every finite cutoff",
					By(Normalized, TimeLeSome, option.NoneNotSome.Inst[Nat]()))
				a.Step(
					"a finite value meets its own cutoff",
					By(TimeLeSome, option.NoneNotSome.Inst[Nat](), nat_order.LessEqRefl))
			})
		return ctx.Theorem(headline,
			func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
				F *Arrow2[Nat, Set[A], Bool], T *Arrow[A, Option[Nat]], assumptions Fact) {
				data := a.Conjuncts(
					assumptions,
					"the sigma algebras form a filtration",
					"T is a stopping time")
				filtrationLaws := a.Conjuncts(
					a.Unfolded(data[0], filtration.FiltrationDef),
					"the ambient events form a sigma algebra",
					"each observation sigma algebra increases inside the ambient one")
				cutoffs := a.Unfolded(data[1], StoppingTimeDef)
				a.Show(
					"finite levels are observable at their times and the infinite level is ambient measurable",
					SplitConj(
						Case(
							"every finite level is observable at its own time",
							Derive(func(a *Argument) {
								a.Induct("n")
								a.Base(
									"stopping at zero is the zero cutoff",
									func(a *Argument) {
										event := a.Have(
											"the zero level equals the zero cutoff",
											"{x:A | x ∈ Ω ∧ T(x) = some(0)} = «C»(0)",
											BySets(zeroLevel))
										a.Show(
											"the zero cutoff is observable",
											event.Rw(),
											By(cutoffs.At(a.TermAs[Nat]("0"))))
									})
								a.Step(
									"a successor level is the difference of consecutive cutoffs",
									func(a *Argument) {
										n := ext.As[Nat](a.StepArgs("n")[0])
										a.Do(Simp(Fwd(nat_arith.Add1)))
										event := a.Have(
											"the new level is precisely the added part of the cutoff",
											"{x:A | x ∈ Ω ∧ T(x) = some(n + 1)} = «C»(n + 1) ∖ «C»(n)",
											BySets(successorLevel))
										a.Do(event.Rw())
										earlier := a.Have(
											"the preceding cutoff remains observable one time later",
											"«C»(n) ∈ F(n + 1)",
											BySets(cutoffs.At(n), filtrationLaws[1].At(n)))
										a.Show(
											"the observation sigma algebra is closed under this difference",
											By(
												cutoffs.At(a.TermAs[Nat]("n + 1")),
												filtrationLaws[1].At(a.TermAs[Nat]("n + 1")),
												earlier,
												sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n + 1)"))))
									})
							})),
						Case(
							"the infinite level is the complement of all finite cutoffs",
							Derive(func(a *Argument) {
								event := a.Have(
									"no finite cutoff contains an infinite value",
									"{x:A | x ∈ Ω ∧ T(x) = none} = Ω ∖ ⋃image(«C», 𝕌)",
									BySets(infiniteLevel))
								a.Do(event.Rw())
								ambientCutoffs := a.Have(
									"every finite cutoff is ambient measurable",
									"∀n:num. «C»(n) ∈ S",
									BySets(cutoffs, filtrationLaws[1]))
								finiteEvent := a.Have(
									"the union of finite cutoffs is ambient measurable",
									"⋃image(«C», 𝕌) ∈ S",
									By(ambientCutoffs, filtrationLaws[0], sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
								a.Show(
									"its relative complement is ambient measurable",
									By(finiteEvent, filtrationLaws[0], sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
							}))))
			})
	}),
})}

// StoppingTimeExtendedMeasurable — a stopping time for a constant sigma algebra
// is extended measurable. Each upper ray is the infinite level together with
// the countable union of the finite levels above its endpoint.
var StoppingTimeExtendedMeasurable = stoppingTimeExtendedMeasurableThm{family.Add(registry.ProofEntry{
	Name: "StoppingTimeExtendedMeasurable",
	Key:  "prop_b3bb0a3a26d5d551",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀T:(A → option(num)).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"stopping_time_on(Ω, λn:num. S, T)",
		},
		Conclusion: "extended_measurable(Ω, S, λx:A. stopping_time_extended(T(x)))",
		Abbrev: Abbrev{
			{Name: "Level", Text: "λk:num. {x:A | x ∈ Ω ∧ T(x) = some(k)}"},
			{Name: "Infinite", Text: "{x:A | x ∈ Ω ∧ T(x) = none}"},
			{Name: "Selected", Text: "λr:real. λk:num. " +
				"    COND(extended_of_real(r) < extended_of_real(&k), «Level»(k), ∅)"},
			{Name: "Ray", Text: "λr:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < stopping_time_extended(T(x))}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		values := ctx.Lemma(
			"∀k:num. stopping_time_extended(none) = extended_infinity ∧ stopping_time_extended(some(k)) = &k",
			func(a *Argument) {
				a.Show(
					"the constructors give infinity and the embedded finite value",
					By(Normalized, TimeToExtendedDef, option.NoneNotSome.Inst[Nat](), option.SomeInjective.Inst[Nat]()))
			})
		rayMembership := ctx.Lemma(
			"∀t:option(num). ∀r:real. "+
				"    extended_of_real(r) < stopping_time_extended(t) ⇔ "+
				"    t = none ∨ (∃k:num. t = some(k) ∧ extended_of_real(r) < &k)",
			func(a *Argument) {
				a.Induct("t")
				a.Base(
					"infinite time lies above every finite ray endpoint",
					By(
						Normalized,
						values,
						extended_nonneg_real.ExtendedLtDef,
						extended_nonneg_real.LeInfinity,
						extended_nonneg_real.OfRealNotInfinity))
				a.Step(
					"a finite time lies in the ray exactly when its value exceeds the endpoint",
					By(values, option.NoneNotSome.Inst[Nat](), option.SomeInjective.Inst[Nat]()))
			})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				T *Arrow[A, Option[Nat]],
				assumptions Fact,
			) {
				data := a.Conjuncts(
					assumptions,
					"S is a sigma algebra on Ω",
					"T is a stopping time for the constant filtration")
				constant := a.TermAs[Fun2[Nat, Set[A], Bool]]("λn:num. S")
				levels := a.Have(
					"every finite level and the infinite level are measurable",
					"(∀k:num. «Level»(k) ∈ S) ∧ «Infinite» ∈ S",
					BySets(
						data[0],
						data[1],
						filtration.FiltrationDef.At(Ω, S, constant),
						StoppingTimeLevelSets.At(Ω, S, constant, T)))
				selected := a.Have(
					"each selected finite level is measurable",
					"∀r:real. ∀k:num. «Selected»(r, k) ∈ S",
					By(data[0], levels, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
				rays := a.Have(
					"every upper ray is measurable",
					"∀r:real. «Ray»(r) ∈ S",
					Derive(func(a *Argument) {
						r := a.FixAs[Real]("r")
						decomposition := a.Have(
							"the upper ray consists of infinity and its selected finite levels",
							"«Ray»(r) = «Infinite» ∪ ⋃image(«Selected»(r), 𝕌)",
							Simp(Fwd(set_basic.Extension)),
							Derive(func(a *Argument) {
								x := a.FixAs[A]("x")
								a.Show(
									"ray membership selects precisely these levels",
									BySets(At(rayMembership, T.Apply(x), r)))
							}))
						a.Show(
							"countable union closure and the infinite level give ray measurability",
							decomposition.Rw(),
							By(
								selected.At(r),
								data[0],
								levels,
								sigma_algebra.SigmaAlgebraOnDef.At(Ω, S),
								sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					}))
				a.Show(
					"measurable upper rays give extended measurability",
					By(
						rays,
						data[0],
						measurable_function.ExtendedMeasurableIffRay.At(
							Ω,
							S,
							a.TermAs[Fun[A, extended_nonneg_real.ExtendedNonnegReal]]("λx:A. stopping_time_extended(T(x))"))))
			})
	}),
})}
