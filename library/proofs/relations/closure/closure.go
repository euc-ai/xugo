// closure.go — the transitive closure: the two rules that define it,
// the theorems they come with, and the laws that make it a closure
// operator; then the reflexive–transitive closure, which admits the
// empty stretch, with its transitivity, the property it carries, its
// monotonicity, and the equivalence it makes of a relation symmetric on
// a set. The README carries the chapter story.
//
// Two conventions the file keeps. A member's LEFT/RIGHT suffix names
// the side the CLOSURE stretch sits on, which is the side the member
// does not travel: `CasesLeft` keeps a stretch on the left and peels
// the last move off the right, `InductLeft` carries P along a stretch
// on the left and extends one step on the right, and the two `Right`
// members are their reflections. And every rule induction is the
// induction verb at the definition's own principle, cited bare: the
// property carried is the goal, read at the pair the closure fact names
// or off a claim that is the principle's conclusion, so a member's
// obligations are the principle's own cases and what the member writes
// is why each case holds.

package closure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

// transitiveClosure — the least transitive relation containing R: one
// step of R is a step of the closure, and two steps of the closure are
// one. The theorems those two rules come with follow it: the rule set,
// rule induction, its strengthened form and the case analysis.
var transitiveClosure = family.DefineInductive(registry.InductiveEntry{
	Name: "TransitiveClosure",
	Keys: registry.InductiveKeys{
		Rules:        "prop_680034345262ed53",
		Induct:       "prop_30167e3ba4acffcf",
		Cases:        "prop_4d74a65c83ec4cf",
		InductStrong: "prop_c7eff99a0c09b95a",
	},
	Const:  "transitive_closure",
	Type:   "(A → A → bool) → A → A → bool",
	Params: []string{"R"},
	Rules: []string{
		"∀x y:A. R(x, y) ⇒ transitive_closure(R, x, y)",
		"∀x y z:A. transitive_closure(R, x, y) ∧ transitive_closure(R, y, z) ⇒ transitive_closure(R, x, z)",
	},
	Deps: []registry.EntryLike{equivalence.TransitiveDef},
})

// TransitiveClosureRules — one step of R is a step of the closure, and
// two steps of the closure are one: the definition's rule set,
// registered verbatim as its Rules theorem.
var TransitiveClosureRules = transitiveClosureRulesThm{transitiveClosure.Rules}

// TransitiveClosureInduct — rule induction along the closure: a
// property that R's own steps have, and that survives composing two
// steps, holds of every step of the closure.
var TransitiveClosureInduct = transitiveClosureInductThm{transitiveClosure.Induct}

// TransitiveClosureInductStrong — the same induction with each step
// telling the proof that the two halves it composes are themselves
// steps of the closure.
var TransitiveClosureInductStrong = transitiveClosureInductStrongThm{transitiveClosure.InductStrong}

// TransitiveClosureCases — the two rules are exhaustive: a step of the
// closure is a step of R, or splits into two steps of the closure.
var TransitiveClosureCases = transitiveClosureCasesThm{transitiveClosure.Cases}

// Monotone — rule induction along R's closure, with "the pair is
// related by S's closure" as the property carried. What the induction
// asks of that property is exactly S's own two rules: the first one
// read through the containment, and the second one as it stands.
var Monotone = monotoneThm{family.Add(registry.ProofEntry{
	Name: "Monotone",
	Key:  "prop_b2249c107cc161f1",
	Build: family.Theorem(
		Statement{
			Binders: "∀R S:(A → A → bool). ∀x y:A.",
			Hypotheses: []string{
				"∀x y:A. R(x, y) ⇒ S(x, y)",
				"transitive_closure(R, x, y)",
			},
			Conclusion: "transitive_closure(S, x, y)",
		},
		func(a *Argument, R, S *Arrow2[A, A, Bool], x, y *Expr[A], containedInS, reachesInR Fact) {
			a.Show(
				"rule induction along R's closure carries the property to the "+
					"pair x, y, and what it asks of the property is S's own two rules",
				ByInduction(TransitiveClosureInduct, reachesInR,
					Case(
						"every R-step is an S-step, and S's first rule puts a single S-step in its closure",
						By(containedInS, TransitiveClosureRules.At(S))),
					Case(
						"S's second rule: two stretches of its closure, meeting at a point, make one",
						By(TransitiveClosureRules.At(S)))))
		}),
})}

// CasesLeft — rule induction along the closure, on the property that a
// pair splits at a LAST move. A single step of R is that split already;
// and a stretch of the closure laid in front of one that splits keeps
// the second one's last move, which is where the strengthened
// principle earns its keep — it hands the first stretch over as a
// closure step instead of making the proof rebuild it.
var CasesLeft = casesLeftThm{family.Add(registry.ProofEntry{
	Name: "CasesLeft",
	Key:  "prop_50cdf054d9c98507",
	Build: family.Theorem(
		"∀R:(A → A → bool). ∀x z:A. "+
			"    transitive_closure(R, x, z) ⇔ R(x, z) ∨ (∃y:A. transitive_closure(R, x, y) ∧ R(y, z))",
		func(a *Argument, R *Arrow2[A, A, Bool], x, z *Expr[A]) {
			a.Iff()

			a.Backward(
				"a single R-step enters the closure by the first rule, and a "+
					"closure step with an R-step after it composes by the second",
				func(b *Argument, split Fact) {
					b.Show(
						"either alternative is a step of the closure from x to z",
						By(split, TransitiveClosureRules.At(R)))
				})

			a.Forward(
				"rule induction along the closure, on the property that the pair splits at a last move",
				func(b *Argument, reaches Fact) {
					b.Show(
						"the strengthened induction carries that property to the pair x, z",
						ByInduction(TransitiveClosureInductStrong, reaches,
							Case(
								"a single step of R splits at a last move, being the left alternative outright",
								Derive(func(c *Argument) {
									c.Fix("p")
									c.Fix("q")
									step := c.Assume()
									c.Show(
										"the step is that alternative",
										By(step))
								})),
							Case(
								"and a stretch laid in front of a pair splitting at a last move "+
									"keeps that move last: the stretches compose up to the point it leaves",
								By(TransitiveClosureRules.At(R)))))
				})
		}),
})}

// CasesRight — rule induction along the closure, on the property that a
// pair splits at a FIRST move. A single step of R is that split already;
// and a stretch of the closure laid after one that splits keeps the
// first one's first move, which is where the strengthened principle
// earns its keep — it hands the second stretch over as a closure step
// instead of making the proof rebuild it.
var CasesRight = casesRightThm{family.Add(registry.ProofEntry{
	Name: "CasesRight",
	Key:  "prop_e14ec08d86019b16",
	Build: family.Theorem(
		"∀R:(A → A → bool). ∀x z:A. "+
			"    transitive_closure(R, x, z) ⇔ R(x, z) ∨ (∃y:A. R(x, y) ∧ transitive_closure(R, y, z))",
		func(a *Argument, R *Arrow2[A, A, Bool], x, z *Expr[A]) {
			a.Iff()

			a.Backward(
				"a single R-step enters the closure by the first rule, and "+
					"an R-step with a closure step after it composes by the second",
				func(b *Argument, split Fact) {
					b.Show(
						"either alternative is a step of the closure from x to z",
						By(split, TransitiveClosureRules.At(R)))
				})

			a.Forward(
				"rule induction along the closure, on the property that the pair splits at a first move",
				func(b *Argument, reaches Fact) {
					b.Show(
						"the strengthened induction carries that property to the pair x, z",
						ByInduction(TransitiveClosureInductStrong, reaches,
							Case(
								"a single step of R splits at a first move, being the left alternative outright",
								Derive(func(c *Argument) {
									c.Fix("p")
									c.Fix("q")
									step := c.Assume()
									c.Show(
										"the step is that alternative",
										By(step))
								})),
							Case(
								"and a stretch laid after a pair splitting at a first move keeps "+
									"that move first: the stretches compose on from the point it lands at",
								By(TransitiveClosureRules.At(R)))))
				})
		}),
})}

// Closed — forwards, the closure is transitive by its own second rule,
// and an R equal to it inherits that. Backwards, the relations are read
// pair by pair and the rule induction is run with R ITSELF as the
// property carried, which is what makes the induction cheap: it then
// asks that a single step of R be a step of R, which is nothing, and
// that two steps of R compose, which is the hypothesis.
var Closed = closedThm{family.Add(registry.ProofEntry{
	Name: "Closed",
	Key:  "prop_5db511fe034d3fd6",
	Build: family.Theorem(
		"∀R:(A → A → bool). transitive_closure(R) = R ⇔ transitive(R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Iff()

			a.Forward(
				"the closure is transitive by its second rule, and an R equal to it inherits that",
				func(b *Argument, closureIsR Fact) {
					b.Show(
						"two steps of R are two steps of the closure, whose composite is a step of R again",
						By(closureIsR, TransitiveClosureRules, equivalence.TransitiveDef))
				})

			a.Backward(
				"relations holding of the same pairs are equal, so the closure is read pair by pair",
				func(b *Argument, transitive Fact) {
					pointwise := b.Have(
						"at every pair the closure and R stand or fall together",
						"∀x y:A. transitive_closure(R, x, y) ⇔ R(x, y)",
						Derive(func(c *Argument) {
							c.FixAs[A]()
							c.FixAs[A]()
							c.Iff()

							c.Backward(
								"the first rule puts a single step of R into the closure",
								func(d *Argument, step Fact) {
									d.Show(
										"the step enters the closure as it stands",
										By(step, TransitiveClosureRules))
								})

							c.Forward(
								"rule induction along the closure, carrying R itself as the property",
								func(d *Argument, reaches Fact) {
									d.Show(
										"the induction carries R over every step of the closure, this pair among them",
										ByInduction(TransitiveClosureInduct, reaches,
											Case(
												"a single step of R is a step of R: nothing to prove",
												Basic()),
											Case(
												"and two steps of R are one — transitivity, as its definition spells it",
												By(transitive, equivalence.TransitiveDef))))
								})
						}))

					b.Do(Funext(), By(pointwise))
				})
		}),
})}

// Idempotent — the criterion above read at the closure itself: what it
// asks of transitive_closure(R) is that the closure be transitive, and
// that is the second of the two rules the closure is defined by, so one
// pass of the closing has already done all of it.
var Idempotent = idempotentThm{family.Add(registry.ProofEntry{
	Name: "Idempotent",
	Key:  "prop_aa7d15392c3ed7a",
	Build: family.Theorem(
		"∀R:(A → A → bool). transitive_closure(transitive_closure(R)) = transitive_closure(R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			closureIsTransitive := a.Have(
				"two steps of the closure compose into one — its "+
					"second rule is exactly what transitivity asks of it",
				"transitive(transitive_closure(R))",
				By(TransitiveClosureRules, equivalence.TransitiveDef))

			a.Show(
				"and a transitive relation is its own transitive closure",
				By(closureIsTransitive, Closed))
		}),
})}

// InductLeft — rule induction along the closure whose step extends by
// a single R-step on the RIGHT of what is already established, where
// the definition's own induction composes two arbitrary stretches:
// this is the principle an argument about a path wants. What runs
// through the definition's induction is not P itself but "P's second
// argument travels from u to v" — a property whose one-step
// obligation is the hypothesis's own right-extension rule and whose
// composing obligation is the composition of two such carriers.
// CasesRight then peels x's first move off the closure step, and the
// carrier takes P across the stretch that remains. The mirror
// principle extends on the left and turns on CasesLeft.
var InductLeft = inductLeftThm{family.Add(registry.ProofEntry{
	Name: "InductLeft",
	Key:  "prop_4f3bf7ad10ed5b3a",
	Build: family.Theorem(
		Statement{
			Binders: "∀R P:(A → A → bool). ∀x y:A.",
			Hypotheses: []string{
				"∀x y:A. R(x, y) ⇒ P(x, y)",
				"∀x y z:A. P(x, y) ∧ R(y, z) ⇒ P(x, z)",
				"transitive_closure(R, x, y)",
			},
			Conclusion: "P(x, y)",
		},
		func(a *Argument, R, P *Arrow2[A, A, Bool], rules Fact, x, y *Expr[A], reaches Fact) {
			carry := a.Have(
				"a closure step from u to v carries P's second argument across it",
				"∀u v:A. transitive_closure(R, u, v) ⇒ (∀t:A. P(t, u) ⇒ P(t, v))",
				Derive(func(b *Argument) {
					b.FixAs[A]("u")
					b.FixAs[A]("v")
					reachesV := b.Assume()
					b.Show(
						"rule induction along the closure carries that property to the pair u, v",
						ByInduction(TransitiveClosureInduct, reachesV,
							Case(
								"a single R-step carries it, which is the hypothesis's own right-extension rule",
								By(rules)),
							Case(
								"and two carriers meeting at a point compose into one",
								Derive(func(c *Argument) {
									c.Fix("p")
									c.Fix("q")
									c.Fix("r")
									carriers := c.Assume()
									c.Fix("t")
									atP := c.Assume()
									c.Show(
										"the first carrier takes P as far as q, the second the rest of the way to r",
										By(carriers, atP))
								}))))
				}))

			splits := a.Have(
				"the closure step out of x splits at a first move: x "+
					"steps to y outright, or steps to a point that reaches y",
				"R(x, y) ∨ (∃m:A. R(x, m) ∧ transitive_closure(R, m, y))",
				By(reaches, At(CasesRight, R, x, y)))

			a.Do(splits.SplitDisj(
				LeftHolds(
					"x steps to y outright, and the hypothesis's base rule is all that is needed",
					Given(func(b *Argument, direct Fact) {
						b.Show(
							"the base rule reads P off that single step",
							By(direct, rules))
					})),
				RightHolds(
					"x's first step lands short of y, and the carrier takes P from there to y",
					Given(func(b *Argument, beyond Fact) {
						m, legs := b.Unpack(beyond) // the point that first step lands at
						atM := b.Have(
							"the base rule reads P off the step into that point",
							"P(x, m)",
							By(legs, rules))
						b.Show(
							"and the carrier along the closure from there to y takes P on to y",
							By(atM, legs, carry.At(m, y)))
					})),
			))
		}),
})}

// InductRight — rule induction that never composes. The induction the
// definition comes with asks a property to survive joining two
// arbitrary stretches of the closure; this one only ever prefixes a
// single step of R, so the property's own occurrence stays on the
// RIGHT of that step and an argument walking a path one move at a time
// can use it. The proof strengthens the property to a CARRIER — a
// stretch of the closure from u to v moves P's first argument back
// from v to u — which is a property the definition's induction does
// establish. A carrier prepends, so it is CasesLeft, the split at the
// LAST move, that finishes: that move is a single step of R, the first
// rule puts it into P, and the carrier along everything before it
// brings the pair back to x.
var InductRight = inductRightThm{family.Add(registry.ProofEntry{
	Name: "InductRight",
	Key:  "prop_beeb336adf8e2175",
	Build: family.Theorem(
		Statement{
			Binders: "∀R P:(A → A → bool). ∀x y:A.",
			Hypotheses: []string{
				"∀x y:A. R(x, y) ⇒ P(x, y)",
				"∀x z:A. (∃y:A. R(x, y) ∧ P(y, z)) ⇒ P(x, z)",
				"transitive_closure(R, x, y)",
			},
			Conclusion: "P(x, y)",
		},
		func(a *Argument, R, P *Arrow2[A, A, Bool], rules Fact, x, y *Expr[A], reaches Fact) {
			carry := a.Have(
				"a stretch of the closure from u to v carries P's first argument back from v to u",
				"∀u v:A. transitive_closure(R, u, v) ⇒ ∀z:A. P(v, z) ⇒ P(u, z)",
				Derive(func(b *Argument) {
					b.FixAs[A]("u")
					b.FixAs[A]("v")
					reachesV := b.Assume()
					b.Show(
						"rule induction along the closure carries that property to the pair u, v",
						ByInduction(TransitiveClosureInduct, reachesV,
							Case(
								"a single step of R is a carrier, the hypothesis's "+
									"left-extension rule being exactly that P crosses such a step",
								By(rules)),
							Case(
								"and two carriers laid end to end are one",
								Derive(func(c *Argument) {
									c.Fix("p")
									c.Fix("q")
									c.Fix("r")
									carriers := c.Assume()
									c.Fix("w")
									atR := c.Assume()
									c.Show(
										"the second carrier brings P from r back to q, the first takes it on to p",
										By(carriers, atR))
								}))))
				}))

			split := a.Have(
				"x reaches y either in a single step of R, or through a point that steps to y",
				"R(x, y) ∨ (∃m:A. transitive_closure(R, x, m) ∧ R(m, y))",
				By(reaches, At(CasesLeft, R, x, y)))

			a.Do(split.SplitDisj(
				LeftHolds(
					"x steps to y in one move of R, which the hypothesis's base rule sends into P",
					Given(func(b *Argument, direct Fact) {
						b.Show(
							"the pair is in P outright",
							By(direct, rules))
					})),
				RightHolds(
					"x reaches a point that steps to y, and the carrier along that stretch brings P back",
					Given(func(b *Argument, beyond Fact) {
						m, legs := b.Unpack(beyond) // the point the last step leaves
						b.Show(
							"the hypothesis's base rule puts the last step into "+
								"P, and the carrier moves its first argument back to x",
							By(legs, rules, carry.At(x, m)))
					})),
			))
		}),
})}

// ReflexiveTransitiveClosureDef — `reflexive_transitive_closure(R, x, y)`:
// x reaches y in zero or more steps of R — the two points are equal, or
// a step of the transitive closure joins them.
var ReflexiveTransitiveClosureDef = reflexiveTransitiveClosureDefThm{family.Define(registry.DefEntry{
	Name:  "ReflexiveTransitiveClosureDef",
	Key:   "prop_39640205fdbed7e7",
	Const: "reflexive_transitive_closure",
	Type:  "(A → A → bool) → A → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀x y:A. " +
			"    reflexive_transitive_closure(R, x, y) ⇔ x = y ∨ transitive_closure(R, x, y)",
	},
	Deps: []registry.EntryLike{TransitiveClosureRules},
})}

// ReflexiveTransitiveClosureTransitive — two stretches of the
// reflexive–transitive closure meeting at a point make one: an empty
// stretch leaves the other as it is, and two steps of the transitive
// closure compose by its second rule.
var ReflexiveTransitiveClosureTransitive = reflexiveTransitiveClosureTransitiveThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveTransitiveClosureTransitive",
	Key:  "prop_5848439c1f74c6ea",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀x y z:A.",
		Hypotheses: []string{
			"reflexive_transitive_closure(R, x, y)",
			"reflexive_transitive_closure(R, y, z)",
		},
		Conclusion: "reflexive_transitive_closure(R, x, z)",
	}, func(a *Argument, R *Arrow2[A, A, Bool], x, y, z *Expr[A], first, second Fact) {
		firstStretch := a.Unfolded(first, ReflexiveTransitiveClosureDef)
		secondStretch := a.Unfolded(second, ReflexiveTransitiveClosureDef)
		a.Show(
			"an empty stretch leaves the other unchanged and two steps of the transitive closure compose",
			Simp(Fwd(ReflexiveTransitiveClosureDef)),
			By(firstStretch, secondStretch, TransitiveClosureRules.At(R)))
	}),
})}

// ReflexiveTransitiveClosurePreserves — a property that every step of R
// carries from its source to its target holds at the end of every
// stretch of the reflexive–transitive closure that starts where it
// holds: rule induction carries it along the transitive closure, and an
// empty stretch ends where it starts.
var ReflexiveTransitiveClosurePreserves = reflexiveTransitiveClosurePreservesThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveTransitiveClosurePreserves",
	Key:  "prop_e9024832d2c4b93",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀P:(A → bool). ∀u v:A.",
		Hypotheses: []string{
			"∀x y:A. R(x, y) ∧ P(x) ⇒ P(y)",
			"reflexive_transitive_closure(R, u, v)",
			"P(u)",
		},
		Conclusion: "P(v)",
	}, func(
		a *Argument,
		R *Arrow2[A, A, Bool],
		P *Expr[Set[A]],
		u, v *Expr[A],
		stepPreserves, reaches, start Fact,
	) {
		closureSteps := a.Have(
			"every step of the transitive closure preserves P",
			"∀x y:A. transitive_closure(R, x, y) ⇒ P(x) ⇒ P(y)",
			ByInduction(TransitiveClosureInduct,
				Case(
					"a single step of R preserves P by hypothesis",
					By(stepPreserves)),
				Case(
					"P passes along both stretches through their shared endpoint",
					Derive(func(b *Argument) {
						b.FixAs[A]()
						b.FixAs[A]()
						b.FixAs[A]()
						implications := b.Assume()
						holdsAtStart := b.Assume()
						b.Show(
							"the two implications carry P to the end",
							By(implications, holdsAtStart))
					}))))
		a.Show(
			"P holds at the end of an empty stretch and of a step of the transitive closure",
			By(Normalized, start, closureSteps.At(u, v), reaches, ReflexiveTransitiveClosureDef.At(R, u, v)))
	}),
})}

// ReflexiveTransitiveClosureMonotone — a relation contained in another
// has its reflexive–transitive closure contained in the other's: an
// empty stretch is one for either relation, and Monotone above carries
// a step of the transitive closure across.
var ReflexiveTransitiveClosureMonotone = reflexiveTransitiveClosureMonotoneThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveTransitiveClosureMonotone",
	Key:  "prop_576533463ed306b8",
	Build: family.Theorem(
		Statement{
			Binders: "∀R S:(A → A → bool). ∀x y:A.",
			Hypotheses: []string{
				"∀x y:A. R(x, y) ⇒ S(x, y)",
				"reflexive_transitive_closure(R, x, y)",
			},
			Conclusion: "reflexive_transitive_closure(S, x, y)",
		},
		func(a *Argument, R, S *Arrow2[A, A, Bool], x, y *Expr[A], containedInS, reachesInR Fact) {
			a.Show(
				"Monotone carries a step of the transitive closure across, and equality carries an empty stretch",
				By(
					Normalized,
					reachesInR,
					containedInS,
					Monotone.At(R, S, x, y),
					ReflexiveTransitiveClosureDef.At(R, x, y),
					ReflexiveTransitiveClosureDef.At(S, x, y)))
		}),
})}

// ReflexiveTransitiveClosureEquivalenceOn — the reflexive–transitive
// closure of a relation symmetric on c, restricted to c, is an
// equivalence on c. A point reaches itself in no steps; rule induction
// reverses every step of the transitive closure, composing the reversed
// steps in reverse order; and two stretches compose by
// ReflexiveTransitiveClosureTransitive above.
var ReflexiveTransitiveClosureEquivalenceOn = reflexiveTransitiveClosureEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveTransitiveClosureEquivalenceOn",
	Key:  "prop_5eb266cf9f4cd1ec",
	Build: family.Theorem(Statement{
		Binders:    "∀c:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"symmetric_on(c, R)"},
		Conclusion: "equivalence_on(c, reflexive_transitive_closure(relation_on(c, R)))",
	}, func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], symmetricOnC Fact) {
		symmetric := a.Unfolded(symmetricOnC, equivalence.SymmetricOnDef)
		restricted := a.TermAs[Fun2[A, A, Bool]]("relation_on(c, R)")
		closureReverses := a.Have(
			"every step of the transitive closure can be reversed",
			"∀u v:A. transitive_closure(relation_on(c, R), u, v) ⇒ transitive_closure(relation_on(c, R), v, u)",
			ByInduction(TransitiveClosureInduct,
				Case(
					"a single restricted step reverses by symmetry on c",
					Derive(func(b *Argument) {
						x := b.FixAs[A]()
						y := b.FixAs[A]()
						step := b.Assume()
						b.Show(
							"the reversed restricted step enters the closure",
							By(
								step,
								symmetric.At(x, y),
								equivalence.RelationOnDef.At(c, R, x, y),
								equivalence.RelationOnDef.At(c, R, y, x),
								TransitiveClosureRules.At(restricted)))
					})),
				Case(
					"the two reversed stretches compose in reverse order",
					By(TransitiveClosureRules.At(restricted)))))

		a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
			Case(
				"reflexive: a point reaches itself in no steps, the closure's x = y disjunct",
				By(ReflexiveTransitiveClosureDef)),
			Case(
				"symmetric: no steps reverse to none, and a step of the transitive closure reverses",
				By(closureReverses, ReflexiveTransitiveClosureDef)),
			Case(
				"transitive: two stretches of the closure meeting at a point make one",
				By(At(ReflexiveTransitiveClosureTransitive, restricted))),
		))
	}),
})}
