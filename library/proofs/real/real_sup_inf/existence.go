// existence.go — when an extremum exists, and what it is when it does.
//
// Three parts, marked by banners:
//
// - The attained-bound relations `real_has_sup` and `real_has_inf`
// - The structural equations: how sup and inf COMPUTE
// - Finite sets attain their bounds

package real_sup_inf

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The attained-bound relations `real_has_sup` and `real_has_inf`
// ---------------------------------------------------------------------------
//
// `real_has_sup(s, l)` is a definition that names no value and computes
// nothing:
//
// 	real_has_sup(s, l) ⇔ ∀c. ((∀x ∈ s. x ≤ c) ⇔ l ≤ c)
//
// — the caps of s are exactly the values from l up, and `real_has_inf` is
// the same with the order reversed. That is a statement about a whole
// half-line at once, and the file divides on how much of it a member
// spends.
//
// THE FIRST SIX read the relation at ONE value, chosen for what the
// member wants to say, and take a single consequence away:
//
// - At c := l the right side is reflexivity, so the left side comes
// free: l caps s. Taken at a member, that is the BOUND pair.
// - At a c BELOW l the right side FAILS, so the left side fails with
// it: c caps nothing, which is to say some member of s escapes c.
// That is the APPROACH pair, whose hypothesis hands the c over —
// and the NONEMPTY pair, which has to manufacture its own. An empty
// set is capped by every value whatsoever, so were s empty the
// equivalence would force `l ≤ c` for every c; `l - &1` denies
// that, and the member escaping it is what makes s inhabited.
//
// THE LAST SIX spend the relation whole, each saying the same thing in
// a different currency: an attained supremum IS the supremum
// (`HasSupIsSup`), it is the cap that is approached
// (`HasSupCharacterization`), it dominates whatever its set dominates
// (`HasSupDominated`), and it exists exactly when completeness asks
// (`HasSupExists`). Between the two characterizations the division is
// which side of the definition each translates. `HasSupIsSup`
// translates `real_sup`: it hands the relation to
// `real_sup_inf.go`'s `SupUniqueLeastBound`, whose hypothesis is verbatim what `real_has_sup`
// unfolds to, and gets `real_sup(s) = l` back for one citation.
// `HasSupCharacterization` translates the ORDER instead — a cap plus an
// approach clause — and rebuilding the relation out of those two needs
// nothing from this chapter, only `real_order_ring`'s order-negation
// law and transitivity, one per direction. `HasSupExists` is then
// bookkeeping over `HasSupIsSup`: forward it forgets the third
// conjunct, backward it supplies `real_sup(s) = real_sup(s)`.
//
// The relation is about a bound that is GIVEN, where `real_sup` and `real_inf`
// CHOOSE one; that seam is what separates this file from
// real_sup_inf.go, and it is why nothing here reaches an ε-term or
// unfolds either operator. Against real_sup_inf.go the seam is narrower
// and worth naming: `HasSupApproach` is `SupApproach`'s contraposition
// move exactly, with the leastness coming from the relation instead of
// from completeness.
//
// WHEN to unfold is the question every member of the second half
// answers first. `Unfold` reaches the relation wherever it stands,
// hypothesis or goal, and it is all-or-nothing: every occurrence goes
// at once. So a member that both cites one of the first six (which are
// stated OF `real_has_sup`) and reads the definition itself must cite first
// and unfold after — `HasSupIsSup` does exactly that, and a comment
// marks the seam. A member reading TWO relations, like
// `HasSupDominated`, cannot cite them at all: the one unfold spends
// both sets, so it takes the upper-bound reading from the relation in
// hand, which is why that member has no in-chapter dep.
//
// The unfold also SPLITS the conjunction it lands beside, so a ⇐ arm
// names the parts of its input with `a.Hyp` AFTER unfolding rather than
// receiving them whole through `Given`: the hypothesis the branch
// handed over no longer exists once the unfold has run. That is the
// same exception convention 5 grants the unfold sites below.
//
// THE WINGS PART COMPANY IN TWO PLACES, both forced by the mathematics
// and neither cosmetic. Both NONEMPTY members need a value on the far
// side of l from where the members lie; the inf wing takes `l + &1` and
// reads `¬(l + &1 ≤ l)` straight off `l < l + &1`, while the sup wing
// wants `l - &1 < l`, the same comparison carried across a subtraction
// (`real_order_ring.LessThanSubAddRight`) — one extra citation, visible
// as the premise `shortOfL` has that `overshootsL` does not. And a set
// dominated pointwise FROM BELOW has the smaller infimum, so
// `HasInfDominated` concludes `l ≤ m` where its twin concludes `m ≤ l`,
// with its hypothesis putting the member of s UNDER the member of t.
// That pair is mirror-symmetric, not position-symmetric; reading the
// statement is what tells the two apart.
//
// Two mechanics hold file-wide.
//
// Every dep whose statement quantifies over the SET is cited in its RAW
// surface and grounded there, real_sup_inf.go's header giving the reason
// in full. Here that is `HasSupNonempty` / `HasInfNonempty`,
// `SupUniqueLeastBound` / `InfUniqueGreatestBound`, `SupLessEqIff` /
// `LessEqInfIff`, `HasSupIsSup` / `HasInfIsInf`, and
// `set_basic.MemberNotEmpty`. The NONEMPTY pair belongs on that list
// even though neither states a `∀x ∈ s`: what expands pointwise ahead
// of the set binder is the CONCLUSION `s ≠ ∅`, an equation between
// sets. The BOUND and APPROACH pairs say nothing about a set as a whole
// and take ordinary typed cites.
//
// `Normalized` is written only where deleting it and replaying strict
// turns the leaf red, measured per site rather than inherited from a
// mirror. The measurement does NOT follow goal shape: two leaves that
// both prove `∀x ∈ s. x ≤ l` split on it, the one reading the relation
// at l closing without and the one handing that cap to a witness
// needing it. What the load-bearing sites have in common is that some
// premise's quantifier has to MOVE before the premises meet — an
// `a.Obtain` whose claim is a resident's own left side negated, a
// `∀x ∈ s` cap handed to an existential witness, two `∀x ∈ s` premises
// matched against each other through a relation. The sites where every
// premise is already a ground atom need none, and so does the
// `SupUniqueLeastBound` close, where the wide premise IS the cited
// law's antecedent verbatim. The wings agree site for site here, and that
// agreement was measured on each wing separately rather than carried
// across — elsewhere in this corpus seven of twenty-two such inherited
// shapings proved inert. With them the
// refuter is never reached: the fourteen entries here together mint
// no CNF key.

// A ⇒-arm member of either wing opens by expanding its relation in the
// goal — which discharges the statement's antecedent, leaving the
// relation and whatever else the antecedent held resident — and naming
// what the relation says about its set with a bare `a.Hyp`. One
// `Unfold` exposes every occurrence in the goal, so a member stating
// TWO relations unfolds once and names both.

// unitStepUp is `l < l + &1`, the strict step both NONEMPTY members
// start from — the sup wing carries it across a subtraction, the inf
// wing negates it where it stands. `LessThanAddOne` states
// `x ≤ y ⇒ x < y + &1`, so reflexivity at l supplies its premise.
// Both callers bind the bound as `l`, which the claim spells.
func unitStepUp(a *Argument, l Term) Fact {
	return a.Have(
		"the unit step up from l is strict, reflexivity supplying its premise",
		"l < l + &1",
		By(At(real_order_ring.LessThanAddOne, l, l), real_order_ring.LessEqRefl))
}

// showNonemptyFrom closes a `s ≠ ∅` goal from a member of s, which both
// NONEMPTY members reach by the same route and with the same shape of
// member — a value x and a fact saying it lies in s and escapes some
// bound.
//
// The BARE existence `∃x. x ∈ s` is stated in its own right rather than
// the escaping member being handed straight to `MemberNotEmpty`, and
// that is what keeps the close a simplification: the law's left side is
// literally that existence, so with it resident the equivalence rewrites
// it to the goal. Handing over the DECORATED existence instead — the
// member together with the bound it escapes — sends the leaf to the
// refuter and mints a recorded key for a step that needs no search.
// Measured both ways at this site.
//
// `MemberNotEmpty` quantifies over the SET, so it is cited in its RAW
// surface and grounded there — the reason real_sup_inf.go's header gives
// in full: the normalized install pointwise-expands and Skolemizes
// ahead of the set binder, so the typed cite cannot be handed s.
func showNonemptyFrom(a *Argument, s Term, x Term, member Fact) {
	holds := a.Have(
		"so s holds a member",
		"∃x:real. x ∈ s",
		Derive(func(a *Argument) {
			a.Take(x)
			a.Show(
				"the value just obtained is one",
				By(member))
		}))
	a.Show(
		"and a set with a member is not empty",
		By(holds, At(set_basic.MemberNotEmpty.Inst[Real](), s)))
}

// HasSupNonempty — a set with an attained supremum has a member. Its c
// is the one the relation does not supply and the member has to
// manufacture: `l - &1`, the nearest value the chapter's order laws
// place strictly below l.
//
// It exists because `HasSupIsSup`, `HasSupCharacterization` and
// `HasSupExists` each need `s ≠ ∅` out of the relation.
var HasSupNonempty = hasSupNonemptyThm{family.Add(registry.ProofEntry{
	Name: "HasSupNonempty",
	Key:  "prop_5cfdb833cc420990",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀l:real.",
		Hypotheses: []string{
			"real_has_sup(s, l)",
		},
		Conclusion: "s ≠ ∅",
	},
		func(a *Argument, s, l Term) {
			v := ops(a.Ctx())
			one := v.Lit(1)
			below := v.Sub.Apply(l, one) // l - &1, a value l is strictly above

			a.Do(Unfold(RealHasSupDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ l ≤ c")

			shortOfL := a.Have(
				"so l - &1 falls strictly short of l, the step read across the subtraction",
				"¬(l ≤ l - &1)",
				By(
					unitStepUp(a, l),
					// l - &1 < l ⇔ l < l + &1
					At(real_order_ring.LessThanSubAddRight, l, one, l),
					// ¬(l - &1 < l) ⇔ l ≤ l - &1
					At(real_order_ring.NotLessThan, below, l)))
			x, escapes := a.Obtain(
				"hence l - &1 caps nothing here — a cap there would put l at or below it",
				"∃x:real. x ∈ s ∧ ¬(x ≤ l - &1)",
				By(shortOfL, bounds.At(below)))

			showNonemptyFrom(a, s, x, escapes)
		}),
})}

// HasInfNonempty — the mirror, manufacturing `l + &1` where its twin
// manufactures `l - &1`. The step up to it IS the denial the argument
// needs, so this wing spends one citation fewer.
//
// The inf side's three members cite it, as the sup side's cite its
// twin.
var HasInfNonempty = hasInfNonemptyThm{family.Add(registry.ProofEntry{
	Name: "HasInfNonempty",
	Key:  "prop_2e4b0d0e01e73c5b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀l:real.",
		Hypotheses: []string{
			"real_has_inf(s, l)",
		},
		Conclusion: "s ≠ ∅",
	},
		func(a *Argument, s, l Term) {
			v := ops(a.Ctx())
			above := v.Add.Apply(l, v.Lit(1)) // l + &1, a value l is strictly below

			a.Do(Unfold(RealHasInfDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ l")

			overshootsL := a.Have(
				"so l + &1 overshoots l",
				"¬(l + &1 ≤ l)",
				// ¬(l < l + &1) ⇔ l + &1 ≤ l
				By(unitStepUp(a, l), At(real_order_ring.NotLessThan, l, above)))
			x, escapes := a.Obtain(
				"hence l + &1 floors nothing here — a floor there would put l at or above it",
				"∃x:real. x ∈ s ∧ ¬(l + &1 ≤ x)",
				By(overshootsL, bounds.At(above)))

			showNonemptyFrom(a, s, x, escapes)
		}),
})}

// HasSupUpperBound — an attained supremum is an upper bound: the
// relation read at the bound itself, the one value at which it costs
// nothing.
var HasSupUpperBound = hasSupUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "HasSupUpperBound",
	Key:  "prop_cda692d6c6edb4b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b x:real.",
		Hypotheses: []string{
			"real_has_sup(s, b)",
			"x ∈ s",
		},
		Conclusion: "x ≤ b",
	},
		func(a *Argument, s, b, x Term) {
			a.Do(Unfold(RealHasSupDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ b ≤ c")
			inS := a.Hyp("x ∈ s")

			caps := a.Have(
				"b caps s, reflexivity discharging the right side",
				"∀x:real. x ∈ s ⇒ x ≤ b",
				By(bounds.At(b), real_order_ring.LessEqRefl))
			a.Show(
				"and the member x lies under the cap",
				By(caps.At(x), inS))
		}),
})}

// HasInfLowerBound — the mirror: an attained infimum is a lower bound,
// the same reading on the other side.
var HasInfLowerBound = hasInfLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "HasInfLowerBound",
	Key:  "prop_c4c1c0339ff51824",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b x:real.",
		Hypotheses: []string{
			"real_has_inf(s, b)",
			"x ∈ s",
		},
		Conclusion: "b ≤ x",
	},
		func(a *Argument, s, b, x Term) {
			a.Do(Unfold(RealHasInfDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ b")
			inS := a.Hyp("x ∈ s")

			floors := a.Have(
				"b floors s, reflexivity discharging the right side",
				"∀x:real. x ∈ s ⇒ b ≤ x",
				By(bounds.At(b), real_order_ring.LessEqRefl))
			a.Show(
				"and the member x lies over the floor",
				By(floors.At(x), inS))
		}),
})}

// HasSupApproach — an attained supremum is approached from inside: no
// value strictly below it caps the set. This is the relation read at a
// c where it FAILS, and the hypothesis hands that c over — `l ≤ c` is
// exactly what `c < l` denies. The member is never constructed; it is
// read off the failure.
var HasSupApproach = hasSupApproachThm{family.Add(registry.ProofEntry{
	Name: "HasSupApproach",
	Key:  "prop_ef29a41d2755590e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀l c:real.",
		Hypotheses: []string{
			"real_has_sup(s, l)",
			"c < l",
		},
		Conclusion: "∃x:real. x ∈ s ∧ c < x",
	},
		func(a *Argument, s, l, c Term) {
			a.Do(Unfold(RealHasSupDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ l ≤ c")
			under := a.Hyp("c < l")

			x, escapes := a.Obtain(
				"c caps nothing here — a cap at c would put l at or below c",
				"∃x:real. x ∈ s ∧ ¬(x ≤ c)",
				By(
					Normalized,
					under,
					bounds.At(c),
					// ¬(c < l) ⇔ l ≤ c, the half the hypothesis denies
					At(real_order_ring.NotLessThan, c, l)))
			a.Take(x)
			a.Show(
				"and a member the cap misses lies above c", // ¬(x ≤ c) ⇔ c < x
				By(escapes, At(real_order_ring.NotLessThan, c, x)))
		}),
})}

// HasInfApproach — the mirror: no value strictly above an attained
// infimum floors the set, so each of them has a member beneath it.
var HasInfApproach = hasInfApproachThm{family.Add(registry.ProofEntry{
	Name: "HasInfApproach",
	Key:  "prop_68e8a0d6730101e7",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀l c:real.",
		Hypotheses: []string{
			"real_has_inf(s, l)",
			"l < c",
		},
		Conclusion: "∃x:real. x ∈ s ∧ x < c",
	},
		func(a *Argument, s, l, c Term) {
			a.Do(Unfold(RealHasInfDef)) // the antecedent discharges into the relation
			bounds := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ l")
			over := a.Hyp("l < c")

			x, escapes := a.Obtain(
				"c floors nothing here — a floor at c would put l at or above c",
				"∃x:real. x ∈ s ∧ ¬(c ≤ x)",
				By(
					Normalized,
					over,
					bounds.At(c),
					// ¬(l < c) ⇔ c ≤ l, the half the hypothesis denies
					At(real_order_ring.NotLessThan, l, c)))
			a.Take(x)
			a.Show(
				"and a member the floor misses lies below c", // ¬(c ≤ x) ⇔ x < c
				By(escapes, At(real_order_ring.NotLessThan, x, c)))
		}),
})}

// ---------------------------------------------------------------------
// The relation spent WHOLE: the four readings, each on both sides.
// ---------------------------------------------------------------------

// HasSupIsSup — a set has l as an attained supremum exactly when the
// completeness axiom applies to it and picks l out. It is the bridge
// between the relation and the operator, and each direction crosses it
// on one citation.
//
// Forward, the relation is read three times over, and this part has
// already spent two of them: `HasSupNonempty` reads it below l, and
// `HasSupUpperBound` reads it at l itself, handing back the cap that is
// at once the second conjunct's witness and the reason no bound has to
// be manufactured. Read whole it is `SupUniqueLeastBound`'s hypothesis
// word for word, so `real_sup(s) = l` costs a single cite. That is what
// spares this member the ε-layer entirely.
//
// Backward, `SupLessEqIff` says a value caps s exactly when it lies
// above `real_sup(s)`; the third conjunct puts l where `real_sup(s)` stands, and
// that is the relation.
var HasSupIsSup = hasSupIsSupThm{family.Add(registry.ProofEntry{
	Name: "HasSupIsSup",
	Key:  "prop_87eee985cb98b8ce",
	Build: family.Theorem("∀s:set(real). ∀l:real. "+
		"    real_has_sup(s, l) ⇔ s ≠ ∅ ∧ ((∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b) ∧ sup(s) = l)",
		func(a *Argument, s, l Term) {
			ctx := a.Ctx()

			a.Iff()
			a.Forward(
				"the relation names a member, a cap, and the least of the caps",
				func(a *Argument, hasSup Fact) {
					// The goal is the three conjuncts, and each fact below is
					// one of them; the last step closes it on the three.
					nonempty := a.Have(
						"s holds a member — nothing under l caps it",
						"s ≠ ∅",
						By(hasSup, At(HasSupNonempty, s, l)))
					caps := a.Have(
						"l caps s, being an attained bound",
						"∀x:real. x ∈ s ⇒ x ≤ l",
						Derive(func(a *Argument) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"the member x lies under the attained bound",
								By(hasSup, inS, At(HasSupUpperBound, s, l, x)))
						}))
					bounded := a.Have(
						"so s is bounded above, l itself being a bound",
						"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
						Derive(func(a *Argument) {
							a.Take(l)
							a.Show(
								"which is the cap just named",
								By(caps))
						}))

					// The relation read whole — and that is what pins the operator.
					bounds := a.Unfolded(hasSup, RealHasSupDef)
					isSup := a.Have(
						"and a value whose upper set is exactly the caps of s IS sup s",
						"sup(s) = l",
						By(bounds, ctx.Dep(SupUniqueLeastBound)))
					a.Show(
						"the member, the bound and the supremum are the three conjuncts",
						By(nonempty, bounded, isSup))
				})
			a.Backward(
				"l stands where sup s does, and sup s caps exactly the values above it",
				func(a *Argument) {
					a.Do(Unfold(RealHasSupDef)) // ↦ ∀c. (∀x ∈ s. x ≤ c) ⇔ l ≤ c
					nonempty := a.Hyp("s ≠ ∅")
					bounded := a.Hyp("∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b")
					isSup := a.Hyp("sup(s) = l")

					c := a.Fix()
					viaSup := a.Have(
						"c caps s exactly when sup s lies at or below c",
						"(∀x:real. x ∈ s ⇒ x ≤ c) ⇔ sup(s) ≤ c",
						By(nonempty, bounded, At(SupLessEqIff, s, c)))
					a.Show(
						"and l is that same value",
						By(viaSup, isSup))
				})
		}),
})}

// HasInfIsInf — a set has l as an attained infimum exactly when the
// completeness axiom applies to it and picks l out. It is the bridge
// between the relation and the operator, and each direction crosses it
// on one citation.
//
// Forward, the relation is read three times over, and this part has
// already spent two of them: `HasInfNonempty` reads it above l, and
// `HasInfLowerBound` reads it at l itself, handing back the floor that
// is at once the second conjunct's witness and the reason no bound has
// to be manufactured. Read whole it is `InfUniqueGreatestBound`'s
// hypothesis word for word, so `real_inf(s) = l` costs a single cite. That
// is what spares this member the ε-layer entirely.
//
// Backward, `LessEqInfIff` says a value floors s exactly when it lies
// below `real_inf(s)`; the third conjunct puts l where `real_inf(s)` stands, and
// that is the relation.
var HasInfIsInf = hasInfIsInfThm{family.Add(registry.ProofEntry{
	Name: "HasInfIsInf",
	Key:  "prop_15de74e2c0690439",
	Build: family.Theorem("∀s:set(real). ∀l:real. "+
		"    real_has_inf(s, l) ⇔ s ≠ ∅ ∧ ((∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x) ∧ inf(s) = l)",
		func(a *Argument, s, l Term) {
			ctx := a.Ctx()

			a.Iff()
			a.Forward(
				"the relation names a member, a floor, and the greatest of the floors",
				func(a *Argument, hasInf Fact) {
					// The goal is the three conjuncts, and each fact below is
					// one of them; the last step closes it on the three.
					nonempty := a.Have(
						"s holds a member — nothing above l floors it",
						"s ≠ ∅",
						By(hasInf, At(HasInfNonempty, s, l)))
					floors := a.Have(
						"l floors s, being an attained bound",
						"∀x:real. x ∈ s ⇒ l ≤ x",
						Derive(func(a *Argument) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"the member x lies over the attained bound",
								By(hasInf, inS, At(HasInfLowerBound, s, l, x)))
						}))
					bounded := a.Have(
						"so s is bounded below, l itself being a bound",
						"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
						Derive(func(a *Argument) {
							a.Take(l)
							a.Show(
								"which is the floor just named",
								By(floors))
						}))

					// The relation read whole — and that is what pins the operator.
					bounds := a.Unfolded(hasInf, RealHasInfDef)
					isInf := a.Have(
						"and a value whose lower set is exactly the floors of s IS inf s",
						"inf(s) = l",
						By(bounds, ctx.Dep(InfUniqueGreatestBound)))
					a.Show(
						"the member, the bound and the infimum are the three conjuncts",
						By(nonempty, bounded, isInf))
				})
			a.Backward(
				"l stands where inf s does, and inf s floors exactly the values below it",
				func(a *Argument) {
					a.Do(Unfold(RealHasInfDef)) // ↦ ∀c. (∀x ∈ s. c ≤ x) ⇔ c ≤ l
					nonempty := a.Hyp("s ≠ ∅")
					bounded := a.Hyp("∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x")
					isInf := a.Hyp("inf(s) = l")

					c := a.Fix()
					viaInf := a.Have(
						"c floors s exactly when it lies at or below inf s",
						"(∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ inf(s)",
						By(nonempty, bounded, At(LessEqInfIff, s, c)))
					a.Show(
						"and l is that same value",
						By(viaInf, isInf))
				})
		}),
})}

// HasSupCharacterization — the relation restated in the order alone: l
// is an attained supremum of s exactly when l caps s and nothing below l
// does. A two-way equivalence over ALL c is traded for two one-way
// clauses, and the trade is what makes the relation usable — a consumer
// holding a cap and an approaching member never has to produce the
// equivalence itself.
//
// Backward the equivalence is rebuilt at a fixed c, one direction each.
// `l ≤ c` makes c a cap, every member passing through l by transitivity.
// Conversely a cap at c cannot fall below l, since a c below l is
// escaped by a member of s — the approach clause produces one and the
// cap at c catches it. `real_order_ring.NotLessThan` is what turns each
// denial into a comparison, and with it the two directions need nothing
// else. Neither uses nonemptiness — the relation does not need it, which
// is this part's remark about the empty set seen from this side.
//
// Forward the three conjuncts are exactly the three readings this part
// publishes, one cite each.
var HasSupCharacterization = hasSupCharacterizationThm{family.Add(registry.ProofEntry{
	Name: "HasSupCharacterization",
	Key:  "prop_386346ada5636b92",
	Build: family.Theorem("∀s:set(real). ∀l:real. "+
		"    real_has_sup(s, l) ⇔ "+
		"    s ≠ ∅ ∧ ((∀x:real. x ∈ s ⇒ x ≤ l) ∧ (∀c:real. c < l ⇒ ∃x:real. x ∈ s ∧ c < x))",
		func(a *Argument, s, l Term) {
			a.Iff()
			a.Forward(
				"the three readings the relation publishes, one each",
				func(a *Argument, hasSup Fact) {
					nonempty := a.Have(
						"s holds a member — nothing under l caps it",
						"s ≠ ∅",
						By(hasSup, At(HasSupNonempty, s, l)))
					caps := a.Have(
						"l caps s, being an attained bound",
						"∀x:real. x ∈ s ⇒ x ≤ l",
						Derive(func(a *Argument) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"the member x lies under the attained bound",
								By(hasSup, inS, At(HasSupUpperBound, s, l, x)))
						}))
					approach := a.Have(
						"and s reaches above everything under l",
						"∀c:real. c < l ⇒ ∃x:real. x ∈ s ∧ c < x",
						Derive(func(a *Argument) {
							c := a.Fix()
							under := a.Assume()
							a.Show(
								"a c below the attained bound is escaped from inside s",
								By(hasSup, under, At(HasSupApproach, s, l, c)))
						}))

					a.Show(
						"nonempty, capped by l, approached from inside",
						By(nonempty, caps, approach))
				})
			a.Backward(
				"a cap that nothing below it matches bounds s from l up",
				func(a *Argument) {
					a.Do(Unfold(RealHasSupDef)) // ↦ ∀c. (∀x ∈ s. x ≤ c) ⇔ l ≤ c
					capsAtL := a.Hyp("∀x:real. x ∈ s ⇒ x ≤ l")
					approach := a.Hyp("∀c:real. c < l ⇒ ∃x:real. x ∈ s ∧ c < x")

					c := a.Fix()
					a.Iff()
					a.Forward(
						"a cap at c cannot fall below l, since s reaches above everything that does",
						func(a *Argument, capsAtC Fact) {
							short := a.SupposeNot() // ¬(l ≤ c)
							x, escapes := a.Obtain(
								"c falls short of l, so a member of s overshoots c",
								"∃x:real. x ∈ s ∧ c < x",
								By(
									short,
									approach.At(c),
									// ¬(c < l) ⇔ l ≤ c, the half `short` denies
									At(real_order_ring.NotLessThan, c, l)))
							a.Show(
								"but the cap at c catches that member", // ¬(c < x) ⇔ x ≤ c
								By(escapes, capsAtC.At(x), At(real_order_ring.NotLessThan, c, x)))
						})
					a.Backward(
						"c caps s once it lies at or above l, every member passing through l",
						func(a *Argument, lLeC Fact) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"x ≤ l ≤ c",
								By(capsAtL.At(x), inS, lLeC, At(real_construction.LessEqTrans, x, l, c)))
						})
				})
		}),
})}

// HasInfCharacterization — the relation restated in the order alone: l
// is an attained infimum of s exactly when l floors s and nothing above
// l does. A two-way equivalence over ALL c is traded for two one-way
// clauses, and the trade is what makes the relation usable — a consumer
// holding a floor and an approaching member never has to produce the
// equivalence itself.
//
// Backward the equivalence is rebuilt at a fixed c, one direction each.
// `c ≤ l` makes c a floor, every member passing through l by
// transitivity. Conversely a floor at c cannot rise above l, since a c
// above l is undercut by a member of s — the approach clause produces
// one and the floor at c catches it. `real_order_ring.NotLessThan` is
// what turns each denial into a comparison, and with it the two
// directions need nothing else. Neither uses nonemptiness — the relation
// does not need it, which is this part's remark about the empty set
// seen from this side.
//
// Forward the three conjuncts are exactly the three readings this part
// publishes, one cite each.
var HasInfCharacterization = hasInfCharacterizationThm{family.Add(registry.ProofEntry{
	Name: "HasInfCharacterization",
	Key:  "prop_57aa71127c165016",
	Build: family.Theorem("∀s:set(real). ∀l:real. "+
		"    real_has_inf(s, l) ⇔ "+
		"    s ≠ ∅ ∧ ((∀x:real. x ∈ s ⇒ l ≤ x) ∧ (∀c:real. l < c ⇒ ∃x:real. x ∈ s ∧ x < c))",
		func(a *Argument, s, l Term) {
			a.Iff()
			a.Forward(
				"the three readings the relation publishes, one each",
				func(a *Argument, hasInf Fact) {
					nonempty := a.Have(
						"s holds a member — nothing above l floors it",
						"s ≠ ∅",
						By(hasInf, At(HasInfNonempty, s, l)))
					floors := a.Have(
						"l floors s, being an attained bound",
						"∀x:real. x ∈ s ⇒ l ≤ x",
						Derive(func(a *Argument) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"the member x lies over the attained bound",
								By(hasInf, inS, At(HasInfLowerBound, s, l, x)))
						}))
					approach := a.Have(
						"and s reaches below everything above l",
						"∀c:real. l < c ⇒ ∃x:real. x ∈ s ∧ x < c",
						Derive(func(a *Argument) {
							c := a.Fix()
							over := a.Assume()
							a.Show(
								"a c above the attained bound is undercut from inside s",
								By(hasInf, over, At(HasInfApproach, s, l, c)))
						}))

					a.Show(
						"nonempty, floored by l, approached from inside",
						By(nonempty, floors, approach))
				})
			a.Backward(
				"a floor that nothing above it matches bounds s from l down",
				func(a *Argument) {
					a.Do(Unfold(RealHasInfDef)) // ↦ ∀c. (∀x ∈ s. c ≤ x) ⇔ c ≤ l
					floorsAtL := a.Hyp("∀x:real. x ∈ s ⇒ l ≤ x")
					approach := a.Hyp("∀c:real. l < c ⇒ ∃x:real. x ∈ s ∧ x < c")

					c := a.Fix()
					a.Iff()
					a.Forward(
						"a floor at c cannot rise above l, since s reaches below everything that does",
						func(a *Argument, floorsAtC Fact) {
							over := a.SupposeNot() // ¬(c ≤ l)
							x, escapes := a.Obtain(
								"c overshoots l, so a member of s undercuts c",
								"∃x:real. x ∈ s ∧ x < c",
								By(
									over,
									approach.At(c),
									// ¬(l < c) ⇔ c ≤ l, the half `over` denies
									At(real_order_ring.NotLessThan, l, c)))
							a.Show(
								"but the floor at c catches that member", // ¬(x < c) ⇔ c ≤ x
								By(escapes, floorsAtC.At(x), At(real_order_ring.NotLessThan, x, c)))
						})
					a.Backward(
						"c floors s once it lies at or below l, every member passing through l",
						func(a *Argument, cLeL Fact) {
							x := a.Fix()
							inS := a.Assume()
							a.Show(
								"c ≤ l ≤ x",
								By(floorsAtL.At(x), inS, cLeL, At(real_construction.LessEqTrans, c, l, x)))
						})
				})
		}),
})}

// HasSupDominated — a set dominated pointwise by another has the smaller
// attained supremum. Exactly one comparison is ever made: whether l caps
// t. Read at l, t's relation turns that into the conclusion, `m ≤ l`
// being precisely what it says a cap at l amounts to.
//
// That l caps t is where the domination is spent. A member y of t sits
// under some member x of s, and x sits under l, so y does — one use of
// transitivity per member of t.
//
// The member states two relations and so reaches none of this part's
// lemmas: one `Unfold` spends both sets at once, and after it there is no
// `real_has_sup` left for `HasSupUpperBound` to be cited against. The cap on s
// is therefore taken where that lemma takes it — from the relation at l,
// whose right side is reflexivity.
var HasSupDominated = hasSupDominatedThm{family.Add(registry.ProofEntry{
	Name: "HasSupDominated",
	Key:  "prop_91fd3919e4f34ca8",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real). ∀l m:real.",
		Hypotheses: []string{
			"real_has_sup(s, l)",
			"real_has_sup(t, m) ∧ (∀y:real. y ∈ t ⇒ ∃x:real. x ∈ s ∧ y ≤ x)",
		},
		Conclusion: "m ≤ l",
	},
		func(a *Argument, s, t, l, m Term) {
			// The one unfold. It discharges the statement's antecedent along
			// the way, leaving its three conjuncts standing separately.
			a.Do(Unfold(RealHasSupDef))
			boundsS := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ l ≤ c")
			boundsT := a.Hyp("∀c:real. (∀x:real. x ∈ t ⇒ x ≤ c) ⇔ m ≤ c")
			dominates := a.Hyp("∀y:real. y ∈ t ⇒ ∃x:real. x ∈ s ∧ y ≤ x")

			capsS := a.Have(
				"l caps s — the relation at l, reflexivity discharging its right side",
				"∀x:real. x ∈ s ⇒ x ≤ l",
				By(boundsS.At(l), real_order_ring.LessEqRefl))
			capsT := a.Have(
				"so l caps t as well, each member of t passing through the member of s above it",
				"∀y:real. y ∈ t ⇒ y ≤ l",
				Derive(func(a *Argument) {
					y := a.Fix()
					inT := a.Assume()
					x, above := a.Obtain(
						"a member of s at or above y",
						"∃x:real. x ∈ s ∧ y ≤ x",
						By(dominates.At(y), inT))
					a.Show(
						"y ≤ x ≤ l",
						By(above, capsS.At(x), At(real_construction.LessEqTrans, y, x, l)))
				}))
			a.Show(
				"and t's relation reads a cap at l as m ≤ l",
				By(capsT, boundsT.At(l)))
		}),
})}

// HasInfDominated — a set that undercuts another pointwise has the
// smaller attained infimum. Exactly one comparison is ever made: whether
// l floors t. Read at l, t's relation turns that into the conclusion,
// `l ≤ m` being precisely what it says a floor at l amounts to.
//
// That l floors t is where the domination is spent. A member y of t sits
// over some member x of s, and x sits over l, so y does — one use of
// transitivity per member of t.
//
// The member states two relations and so reaches none of this part's
// lemmas: one `Unfold` spends both sets at once, and after it there is no
// `real_has_inf` left for `HasInfLowerBound` to be cited against. The floor on
// s is therefore taken where that lemma takes it — from the relation at
// l, whose right side is reflexivity.
var HasInfDominated = hasInfDominatedThm{family.Add(registry.ProofEntry{
	Name: "HasInfDominated",
	Key:  "prop_23edee4482ef32",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real). ∀l m:real.",
		Hypotheses: []string{
			"real_has_inf(s, l)",
			"real_has_inf(t, m) ∧ (∀y:real. y ∈ t ⇒ ∃x:real. x ∈ s ∧ x ≤ y)",
		},
		Conclusion: "l ≤ m",
	},
		func(a *Argument, s, t, l, m Term) {
			// The one unfold. It discharges the statement's antecedent along
			// the way, leaving its three conjuncts standing separately.
			a.Do(Unfold(RealHasInfDef))
			boundsS := a.Hyp("∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ l")
			boundsT := a.Hyp("∀c:real. (∀x:real. x ∈ t ⇒ c ≤ x) ⇔ c ≤ m")
			dominates := a.Hyp("∀y:real. y ∈ t ⇒ ∃x:real. x ∈ s ∧ x ≤ y")

			floorsS := a.Have(
				"l floors s — the relation at l, reflexivity discharging its right side",
				"∀x:real. x ∈ s ⇒ l ≤ x",
				By(boundsS.At(l), real_order_ring.LessEqRefl))
			floorsT := a.Have(
				"so l floors t as well, each member of t passing through the member of s below it",
				"∀y:real. y ∈ t ⇒ l ≤ y",
				Derive(func(a *Argument) {
					y := a.Fix()
					inT := a.Assume()
					x, below := a.Obtain(
						"a member of s at or below y",
						"∃x:real. x ∈ s ∧ x ≤ y",
						By(dominates.At(y), inT))
					a.Show(
						"l ≤ x ≤ y",
						By(below, floorsS.At(x), At(real_construction.LessEqTrans, l, x, y)))
				}))
			a.Show(
				"and t's relation reads a floor at l as l ≤ m",
				By(floorsT, boundsT.At(l)))
		}),
})}

// HasSupExists — a set has an attained supremum exactly when it is
// nonempty and bounded above. That is the completeness axiom's own
// hypothesis pair read as the exact condition rather than as a
// sufficient one, and both directions are `HasSupIsSup` at a value.
//
// Backward the value is `real_sup(s)` itself, and the equation that
// characterization owes is then reflexive. Forward it is the bound the
// existential hands over, and the equation is simply forgotten.
var HasSupExists = hasSupExistsThm{family.Add(registry.ProofEntry{
	Name: "HasSupExists",
	Key:  "prop_b1fbb4c3eeb24214",
	Build: family.Theorem("∀s:set(real). "+
		"    (∃l:real. real_has_sup(s, l)) ⇔ s ≠ ∅ ∧ (∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b)",
		func(a *Argument, s Term) {
			ctx := a.Ctx()
			supS := ops(ctx).RealSup.Apply(s)

			a.Iff()
			a.Forward(
				"whichever bound is attained, s is nonempty and that bound caps it",
				func(a *Argument, someBound Fact) {
					// attained: real_has_sup(s, l) at the l just named.
					l, attained := a.Unpack(someBound)
					a.Show(
						"the characterization at l, its equation dropped",
						By(Normalized, attained, At(HasSupIsSup, s, l)))
				})
			a.Backward(
				"sup s is an attained bound, the equation it owes being reflexive",
				func(a *Argument, nonemptyBounded Fact) {
					a.Take(supS)
					a.Show(
						"the characterization at sup s",
						By(nonemptyBounded, At(HasSupIsSup, s, supS)))
				})
		}),
})}

// HasInfExists — a set has an attained infimum exactly when it is
// nonempty and bounded below. That is the completeness axiom's own
// hypothesis pair read as the exact condition rather than as a
// sufficient one, and both directions are `HasInfIsInf` at a value.
//
// Backward the value is `real_inf(s)` itself, and the equation that
// characterization owes is then reflexive. Forward it is the bound the
// existential hands over, and the equation is simply forgotten.
var HasInfExists = hasInfExistsThm{family.Add(registry.ProofEntry{
	Name: "HasInfExists",
	Key:  "prop_a0cc3e1184d0a0c",
	Build: family.Theorem("∀s:set(real). "+
		"    (∃l:real. real_has_inf(s, l)) ⇔ s ≠ ∅ ∧ (∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x)",
		func(a *Argument, s Term) {
			ctx := a.Ctx()
			infS := ops(ctx).RealInf.Apply(s)

			a.Iff()
			a.Forward(
				"whichever bound is attained, s is nonempty and that bound floors it",
				func(a *Argument, someBound Fact) {
					// attained: real_has_inf(s, l) at the l just named.
					l, attained := a.Unpack(someBound)
					a.Show(
						"the characterization at l, its equation dropped",
						By(Normalized, attained, At(HasInfIsInf, s, l)))
				})
			a.Backward(
				"inf s is an attained bound, the equation it owes being reflexive",
				func(a *Argument, nonemptyBounded Fact) {
					a.Take(infS)
					a.Show(
						"the characterization at inf s",
						By(nonemptyBounded, At(HasInfIsInf, s, infS)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The structural equations: how sup and inf COMPUTE
// ---------------------------------------------------------------------------
//
// Everywhere before this file the two operators are characterized and
// compared; here they are evaluated. A set given by its points has its
// extremum given by an expression in those points, and the expression
// is built out of the binary lattice of real_sup_inf.go — which is what
// makes movement 1 the engine room of the set-level wings rather than a
// preliminary to them.
//
// The equations come in two flavours, and the difference is whether the
// equation asks anything of the set at all.
//
// The one-point case and the two-point PEEL do not: `real_sup {a} = a`
// because a is a member that bounds, and
// `sup ({a, b} ∪ s) = sup ({max a b} ∪ s)` because the two sets have
// literally the same upper bounds, which SupInsertMax's own note works
// out. Neither statement asks anything of s at all, not even that it be
// nonempty or bounded: the first names a concrete set, and the second is
// an identity between two ε-descriptions that agree pointwise. That is
// why the peel is stated as a merge of two inserted points rather than
// as `sup ({a} ∪ s) = max a (sup s)`, which is the finite equation and
// does need hypotheses.
//
// The equations below the ruled seam do ask, and they ask different
// things. Peeling one point off a set down to a `max` against `real_sup s`
// needs s finite, so that `real_sup s` is a value the peeled equation may
// mention at all — and needs the ∅ case named separately, which is what
// the COND in those two statements is. The union law needs no
// finiteness, only what a supremum always needs: both sides nonempty and
// both bounded above.
//
// Two techniques above the seam, one per pair. The singletons go
// through the attainment law of real_sup_inf.go, which is the whole
// of their content: name the greatest element and the supremum is it,
// and in a one-point set the greatest element is the point. The peels go
// through SupSameUpperBounds, whose hypothesis is supplied by peeling
// each inserted point off the universal claim — bounding a set with a
// point laid on it is bounding the point and bounding the rest — so that
// the equivalence becomes propositional algebra over four atoms.
//
// Each wing states that peel once, at its own predicate, and hands it to
// the set driver. The peel is not a fact about the order at all —
// `x ≤ c` rides through it untouched — and what it actually claims is
// that a point of `insert(p, t)` is p or a point of t. That is what
// insert means, so the statement earns its place for the groundings it
// serves and its proof takes one call.
//
// The last three equations, below the second seam, run the other way.
// Everything above computes an extremum FROM a set; they read a set —
// or the failure of one to spread out — back off its extrema. Two of
// them evaluate the two-point set, which is the smallest case where
// `real_sup` has a choice to make and the first whose answer is written as a
// lattice term rather than read straight off the listing; the third says
// that when the two operators agree there was never any choice at all,
// because the set was a point.
//
// The file's mechanics follow the chapter's: a dep whose statement
// quantifies over the SET is cited in its RAW surface and grounded
// there, `Normalized` is written only where deleting it and replaying
// strict turns the leaf red, and the mirrors sit adjacent.

// SupSingleton — a one-point set is its own supremum. The point is a
// member, and it bounds the set because it is the only thing in it, so
// it is a greatest element and the attainment law names it.
var SupSingleton = supSingletonThm{family.Add(registry.ProofEntry{
	Name: "SupSingleton",
	Key:  "prop_e1d339da32f4476f",
	Build: family.Theorem("∀a:real. sup({a}) = a",
		func(arg *Argument, a Term) {
			ctx := arg.Ctx()

			// The order is consulted once, at a ≤ a; what the set driver
			// is left to decide is that {a} admits a and nothing else.
			greatest := arg.Have(
				"a is a member of {a}, and it caps {a} because a is all {a} has",
				"a ∈ insert(a, ∅) ∧ (∀x:real. x ∈ insert(a, ∅) ⇒ x ≤ a)",
				BySets(At(real_order_ring.LessEqRefl, a)))

			arg.Show(
				"and a greatest member IS the supremum",
				By(greatest, ctx.Dep(SupUniqueAttained)))
		}),
})}

// InfSingleton — the mirror: the one point is also the least element,
// so it is the infimum.
var InfSingleton = infSingletonThm{family.Add(registry.ProofEntry{
	Name: "InfSingleton",
	Key:  "prop_d1dbec70a7561763",
	Build: family.Theorem("∀a:real. inf({a}) = a",
		func(arg *Argument, a Term) {
			ctx := arg.Ctx()

			// The mirror: the same single order fact, and the same
			// question about {a} left to the set driver.
			least := arg.Have(
				"a is a member of {a}, and it floors {a} because a is all {a} has",
				"a ∈ insert(a, ∅) ∧ (∀x:real. x ∈ insert(a, ∅) ⇒ a ≤ x)",
				BySets(At(real_order_ring.LessEqRefl, a)))

			arg.Show(
				"and a least member IS the infimum",
				By(least, ctx.Dep(InfUniqueAttained)))
		}),
})}

// SupInsertMax — two points laid on a set may be merged into their
// maximum. No hypothesis at all: the two sets have the SAME upper
// bounds, and a supremum sees nothing else.
//
// The equivalence is where the mathematics is. Peeling an inserted
// point off a universal claim splits it into the claim at that point
// and the claim on the rest, so bounding the left set is three demands
// — c over b, c over a, c over s — and bounding the right is two, c
// over max(a, b) and c over s. MaxLessEq says the first two of those
// three ARE the one remaining, so the two conditions on c coincide.
var SupInsertMax = supInsertMaxThm{family.Add(registry.ProofEntry{
	Name: "SupInsertMax",
	Key:  "prop_735ff3be0952b17b",
	Build: family.Theorem("∀a b:real. ∀s:set(real). "+
		"    sup(insert(b, insert(a, s))) = sup(insert(max(a, b), s))",
		func(arg *Argument, a, b, s Term) {
			ctx := arg.Ctx()
			v := ops(ctx)

			sameBounds := arg.Have(
				"the two sets are bounded by exactly the same values",
				"∀c:real. "+
					"    (∀x:real. x ∈ insert(b, insert(a, s)) ⇒ x ≤ c) ⇔ (∀x:real. x ∈ insert(max(a, b), s) ⇒ x ≤ c)",
				Derive(func(arg *Argument) {
					c := arg.Fix()

					// The peel itself, read at the bounding predicate and stated
					// for an arbitrary point and rest, so that the three cites
					// below are three groundings of this one fact. The bound is
					// an atom the equivalence carries along, so what the set
					// driver is left to decide is who is in insert(p, t).
					peel := arg.Have(
						"bounding a set with one more point laid on it is bounding that point and bounding the rest",
						"∀t:set(real). ∀p:real. (∀x:real. x ∈ insert(p, t) ⇒ x ≤ c) ⇔ p ≤ c ∧ (∀x:real. x ∈ t ⇒ x ≤ c)",
						BySets())

					arg.Show(
						"c over b, over a and over s on the left; c over max(a, "+
							"b) and over s on the right; and those are the same demand",
						By(
							peel.At(v.Insert.Apply(a, s), b),
							peel.At(s, a),
							peel.At(s, v.Max.Apply(a, b)),
							At(MaxLessEq, a, b, c)))
				}))

			arg.Show(
				"and a supremum is determined by the upper bounds alone",
				By(sameBounds, ctx.Dep(SupSameUpperBounds)))
		}),
})}

// InfInsertMin — the mirror, merging through the minimum. The crossing
// is in which lattice law is cited: the sup wing wants the bound ABOVE
// a max, `MaxLessEq`, and this wing the bound BELOW a min, `LessEqMin`.
var InfInsertMin = infInsertMinThm{family.Add(registry.ProofEntry{
	Name: "InfInsertMin",
	Key:  "prop_a39271dad312c383",
	Build: family.Theorem("∀a b:real. ∀s:set(real). "+
		"    inf(insert(b, insert(a, s))) = inf(insert(min(a, b), s))",
		func(arg *Argument, a, b, s Term) {
			ctx := arg.Ctx()
			v := ops(ctx)

			sameBounds := arg.Have(
				"the two sets are bounded from below by exactly the same values",
				"∀c:real. "+
					"    (∀x:real. x ∈ insert(b, insert(a, s)) ⇒ c ≤ x) ⇔ (∀x:real. x ∈ insert(min(a, b), s) ⇒ c ≤ x)",
				Derive(func(arg *Argument) {
					c := arg.Fix()

					// The mirror peel, at the flooring predicate — a second
					// statement rather than a second reading of the sup wing's,
					// the predicate being the slot that changed. What the set
					// driver is left to decide is the same as above: who is in
					// insert(p, t).
					peel := arg.Have(
						"flooring a set with one more point laid on it is flooring that point and flooring the rest",
						"∀t:set(real). ∀p:real. (∀x:real. x ∈ insert(p, t) ⇒ c ≤ x) ⇔ c ≤ p ∧ (∀x:real. x ∈ t ⇒ c ≤ x)",
						BySets())

					arg.Show(
						"c under b, under a and under s on the left; c under min(a, "+
							"b) and under s on the right; and those are the same demand",
						By(
							peel.At(v.Insert.Apply(a, s), b),
							peel.At(s, a),
							peel.At(s, v.Min.Apply(a, b)),
							At(LessEqMin, a, b, c)))
				}))

			arg.Show(
				"and an infimum is determined by the lower bounds alone",
				By(sameBounds, ctx.Dep(InfSameLowerBounds)))
		}),
})}

// ---------------------------------------------------------------------
// The equations with hypotheses.
//
// The change of subject is real — these are the equations a consumer
// reaches for when it has a set in hand rather than a listing — but the
// technique is the one already in use, and the seam marks the change
// rather than proposing a split.
//
// Both pairs reduce to a characterization already landed and then argue
// about membership one point at a time, and the two characterizations
// are two of the three ways a supremum can be pinned. The insertion pair
// EXHIBITS one: `max(x, real_sup s)` is a member of the enlarged set and caps
// it, so it is a greatest member, and finiteness is what supplies the
// ingredient (`real_sup s ∈ s`) that makes the exhibition possible. The union
// pair exhibits nothing: it shows that the union and the pair of suprema
// have the same upper bounds, and leastness turns that into the equation
// without any point of the union ever being named.
//
// Where the membership question sits differs, and that is what decides
// how each pair meets it. The insertion pair asks it once, at the end,
// about a candidate it has already chosen — so it hands the whole
// question to the finite part's greatest-member packaging and never names a
// set law itself. The union pair asks it at the START of each direction
// and then keeps going: `x ∈ s ∪ t` is opened with `set_basic.InUnion`
// precisely so the two sides become two BRANCHES, and each branch is an
// argument about the order — through that side's supremum, and up to the
// max. The disjunction is the shape of the proof there, not a residue to
// be discharged.
// ---------------------------------------------------------------------

// SupInsertFinite — laying a point on a finite set lifts its supremum
// to the greater of the point and the supremum already there. The COND
// is not a case in the mathematics but a gap in it: ∅ has no supremum
// for `max` to be taken against, so the empty set gets the singleton
// answer and everything else the max.
//
// The nonempty branch is the whole content, and it is one sentence:
// `max(x, real_sup s)` IS a member of the enlarged set — being one of its two
// arguments, and both are in there — and it caps the enlarged set, so it
// is a greatest member and attainment names it the supremum. Finiteness
// enters exactly once, in the attainment cite that makes `real_sup s` both a
// member of s and the greatest one.
//
// The insertion helper assembles the candidate's membership and upper
// bound from its comparison with the new point and the old set.
var SupInsertFinite = supInsertFiniteThm{family.Add(registry.ProofEntry{
	Name: "SupInsertFinite",
	Key:  "prop_ca55f8ab8039a37d",
	Build: family.Sections(Statement{
		Binders: "∀x:real. ∀s:set(real).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "sup(insert(x, s)) = COND(s = ∅, x, max(x, sup(s)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		enlargedIsGreatest := enlargedIsGreatestAt(ctx)

		return ctx.Theorem(headline, func(arg *Argument, x, s Term, finite Fact) {
			v := ops(ctx)
			supS := v.RealSup.Apply(s)
			peak := v.Max.Apply(x, supS) // max(x, sup s)

			// The COND is split by its own guard rather than by a chosen
			// discriminant: CondRewrite turns the equation into the two
			// guarded equations it abbreviates, so each branch below arrives
			// with its answer already substituted and its guard to assume.
			arg.Do(CondRewrite(), SplitConj(
				Case(
					"s was empty, so the enlarged set is {x} and the answer is x",
					Derive(func(arg *Argument) {
						isEmpty := arg.Assume()
						arg.Do(isEmpty.Rw()) // ↦ real_sup({x}) = x
						arg.Show(
							"which is the singleton equation",
							By(SupSingleton))
					})),
				Case(
					"s was not empty, so the answer is max(x, sup s) — and that value is a greatest member",
					Derive(func(arg *Argument) {
						nonempty := arg.Assume()
						finiteNonempty := arg.Have(
							"s is finite and nonempty, so it attains its own supremum",
							"finite(s) ∧ s ≠ ∅",
							By(finite, nonempty))
						member, caps := supAttainedAt(arg, s, finiteNonempty)

						isPointOrMember := arg.Have(
							"so the max is the point just laid on, or a value s already held",
							"max(x, sup(s)) = x ∨ max(x, sup(s)) ∈ s",
							By(Normalized, At(MaxIsArgument, x, supS), member))

						capsS := arg.Have(
							"and the max caps s, lying over sup s which lies over every member",
							"∀y:real. y ∈ s ⇒ y ≤ max(x, sup(s))",
							Derive(func(arg *Argument) {
								y := arg.Fix()
								inS := arg.Assume()
								arg.Show(
									"y ≤ sup s ≤ max(x, sup s)",
									By(inS, caps.At(y), At(MaxUpperBound, x, supS), At(real_construction.LessEqTrans, y, supS, peak)))
							}))

						greatest := arg.Have(
							"so it is a greatest member of the enlarged set: over the "+
								"added point by construction, over the rest through sup s",
							"max(x, sup(s)) ∈ insert(x, s) ∧ (∀y:real. y ∈ insert(x, s) ⇒ y ≤ max(x, sup(s)))",
							By(isPointOrMember, At(MaxUpperBound, x, supS), capsS, enlargedIsGreatest))

						arg.Show(
							"and a greatest member IS the supremum",
							By(greatest, ctx.Dep(SupUniqueAttained)))
					})),
			))
		})
	}),
})}

// InfInsertFinite — the mirror: the infimum drops to the lesser of the
// point and the infimum already there. The crossing is in the guard's
// answer as much as in the lattice law — `min x y` is x when `x ≤ y`
// where `max x y` is y, so the two branches naming the chosen argument
// exchange places between the wings.
var InfInsertFinite = infInsertFiniteThm{family.Add(registry.ProofEntry{
	Name: "InfInsertFinite",
	Key:  "prop_286f438eac36b577",
	Build: family.Sections(Statement{
		Binders: "∀x:real. ∀s:set(real).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "inf(insert(x, s)) = COND(s = ∅, x, min(x, inf(s)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		enlargedIsLeast := enlargedIsLeastAt(ctx)

		return ctx.Theorem(headline, func(arg *Argument, x, s Term, finite Fact) {
			v := ops(ctx)
			infS := v.RealInf.Apply(s)
			trough := v.Min.Apply(x, infS) // min(x, inf s)

			// The COND is split by its own guard, as in the sup wing above.
			arg.Do(CondRewrite(), SplitConj(
				Case(
					"s was empty, so the enlarged set is {x} and the answer is x",
					Derive(func(arg *Argument) {
						isEmpty := arg.Assume()
						arg.Do(isEmpty.Rw()) // ↦ real_inf({x}) = x
						arg.Show(
							"which is the singleton equation",
							By(InfSingleton))
					})),
				Case(
					"s was not empty, so the answer is min(x, inf s) — and that value is a least member",
					Derive(func(arg *Argument) {
						nonempty := arg.Assume()
						finiteNonempty := arg.Have(
							"s is finite and nonempty, so it attains its own infimum",
							"finite(s) ∧ s ≠ ∅",
							By(finite, nonempty))
						member, floors := infAttainedAt(arg, s, finiteNonempty)

						isPointOrMember := arg.Have(
							"so the min is the point just laid on, or a value s already held",
							"min(x, inf(s)) = x ∨ min(x, inf(s)) ∈ s",
							By(Normalized, At(MinIsArgument, x, infS), member))

						floorsS := arg.Have(
							"and the min lies under s, lying under inf s which lies under every member",
							"∀y:real. y ∈ s ⇒ min(x, inf(s)) ≤ y",
							Derive(func(arg *Argument) {
								y := arg.Fix()
								inS := arg.Assume()
								arg.Show(
									"min(x, inf s) ≤ inf s ≤ y",
									By(
										inS,
										floors.At(y),
										At(MinLowerBound, x, infS),
										At(real_construction.LessEqTrans, trough, infS, y)))
							}))

						least := arg.Have(
							"so it is a least member of the enlarged set: under the "+
								"added point by construction, under the rest through inf s",
							"min(x, inf(s)) ∈ insert(x, s) ∧ (∀y:real. y ∈ insert(x, s) ⇒ min(x, inf(s)) ≤ y)",
							By(isPointOrMember, At(MinLowerBound, x, infS), floorsS, enlargedIsLeast))

						arg.Show(
							"and a least member IS the infimum",
							By(least, ctx.Dep(InfUniqueAttained)))
					})),
			))
		})
	}),
})}

// SupUnion — two sets side by side have the greater of the two suprema
// for their supremum. Nothing is ever exhibited: the claim is that the
// union and the pair have the same upper bounds, and leastness turns
// that into the equation.
//
// The equivalence is the whole proof, and each direction is one of the
// two lattice equivalences of movement 1 read at `real_sup s` and `real_sup t`.
// Upward, a cap on the union caps each side, so it caps each supremum,
// and MaxLessEq collects the two into a cap on the max. Downward, a
// point of the union lies under the supremum of whichever side it came
// from, and LessEqMax puts it under the max for that reason alone.
var SupUnion = supUnionThm{family.Add(registry.ProofEntry{
	Name: "SupUnion",
	Key:  "prop_4867a353365caf60",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real).",
		Hypotheses: []string{
			"s ≠ ∅",
			"t ≠ ∅ ∧ ((∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b) ∧ (∃c:real. ∀x:real. x ∈ t ⇒ x ≤ c))",
		},
		Conclusion: "sup(union(s, t)) = max(sup(s), sup(t))",
	},
		func(arg *Argument, s, t Term, nonemptyBounded Fact) {
			ctx := arg.Ctx()
			v := ops(ctx)
			supS, supT := v.RealSup.Apply(s), v.RealSup.Apply(t)
			join := v.Max.Apply(supS, supT) // max(sup s, sup t) — the join
			inUnion := set_basic.InUnion.Inst[Real]()

			sameBounds := arg.Have(
				"a value caps the union exactly when it caps the greater of the two suprema",
				"∀c:real. (∀x:real. x ∈ union(s, t) ⇒ x ≤ c) ⇔ max(sup(s), sup(t)) ≤ c",
				Derive(func(arg *Argument) {
					c := arg.Fix()
					arg.Iff()
					arg.Forward(
						"a cap on the union caps each side, hence each supremum, hence their max",
						func(arg *Argument, capsUnion Fact) {
							// One peel per side. A point of a side is a point of
							// the union, so the cap on the union is already the
							// cap on the side — read at that point.
							capsS := arg.Have(
								"c caps s",
								"∀y:real. y ∈ s ⇒ y ≤ c",
								Derive(func(arg *Argument) {
									y := arg.Fix()
									inSide := arg.Assume()
									arg.Show(
										"a point of the side is a point of the union",
										By(inSide, capsUnion.At(y), At(inUnion, s, t, y)))
								}))
							capsT := arg.Have(
								"c caps t",
								"∀y:real. y ∈ t ⇒ y ≤ c",
								Derive(func(arg *Argument) {
									y := arg.Fix()
									inSide := arg.Assume()
									arg.Show(
										"a point of the side is a point of the union",
										By(inSide, capsUnion.At(y), At(inUnion, s, t, y)))
								}))

							capsSupS := arg.Have(
								"so c is over the supremum of s",
								"sup(s) ≤ c",
								By(nonemptyBounded, capsS, ctx.Dep(SupLessEqBound)))
							capsSupT := arg.Have(
								"and over the supremum of t",
								"sup(t) ≤ c",
								By(nonemptyBounded, capsT, ctx.Dep(SupLessEqBound)))

							arg.Show(
								"and a cap over both is a cap over their max",
								By(capsSupS, capsSupT, At(MaxLessEq, supS, supT, c)))
						})
					arg.Backward(
						"a point of the union lies under the supremum of "+
							"its own side, and so under the max, and so under c",
						func(arg *Argument, capsJoin Fact) {
							x := arg.Fix()
							inEither := arg.Assume()
							which := arg.Have(
								"x came from s, or from t",
								"x ∈ s ∨ x ∈ t",
								By(inEither, inUnion))
							xUnderMax := arg.Have(
								"either way it lies under the max, being under one of the two",
								"x ≤ max(sup(s), sup(t))",
								Derive(func(arg *Argument) {
									arg.Do(which.SplitDisj(
										LeftHolds(
											"from s, so under sup s",
											Given(func(arg *Argument, inS Fact) {
												arg.Show(
													"a member is under the supremum, and sup s is one of the two the max is over",
													By(inS, nonemptyBounded, At(MemberLessEqSup, s, x), At(LessEqMax, supS, supT, x)))
											})),
										RightHolds(
											"from t, so under sup t",
											Given(func(arg *Argument, inT Fact) {
												arg.Show(
													"a member is under the supremum, and sup t is the other",
													By(inT, nonemptyBounded, At(MemberLessEqSup, t, x), At(LessEqMax, supS, supT, x)))
											})),
									))
								}))
							arg.Show(
								"and the max is under c by hypothesis",
								By(xUnderMax, capsJoin, At(real_construction.LessEqTrans, x, join, c)))
						})
				}))

			arg.Show(
				"and the upper bounds alone pin the supremum",
				By(sameBounds, ctx.Dep(SupUniqueLeastBound)))
		}),
})}

// InfUnion — the mirror, at the lesser of the two infima. The two
// lattice equivalences exchange as they do throughout the chapter: the
// arm that collects two bounds into one takes LessEqMin where the sup
// wing took MaxLessEq, and the arm that reads a single bound off the
// compound takes MinLessEq where the sup wing took LessEqMax.
var InfUnion = infUnionThm{family.Add(registry.ProofEntry{
	Name: "InfUnion",
	Key:  "prop_d0b064b47cf3a7b6",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real).",
		Hypotheses: []string{
			"s ≠ ∅",
			"t ≠ ∅ ∧ ((∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x) ∧ (∃c:real. ∀x:real. x ∈ t ⇒ c ≤ x))",
		},
		Conclusion: "inf(union(s, t)) = min(inf(s), inf(t))",
	},
		func(arg *Argument, s, t Term, nonemptyBounded Fact) {
			ctx := arg.Ctx()
			v := ops(ctx)
			infS, infT := v.RealInf.Apply(s), v.RealInf.Apply(t)
			meet := v.Min.Apply(infS, infT) // min(inf s, inf t) — the meet
			inUnion := set_basic.InUnion.Inst[Real]()

			sameBounds := arg.Have(
				"a value floors the union exactly when it floors the lesser of the two infima",
				"∀c:real. (∀x:real. x ∈ union(s, t) ⇒ c ≤ x) ⇔ c ≤ min(inf(s), inf(t))",
				Derive(func(arg *Argument) {
					c := arg.Fix()
					arg.Iff()
					arg.Forward(
						"a floor under the union floors each side, hence each infimum, hence their min",
						func(arg *Argument, floorsUnion Fact) {
							// One peel per side, as in the sup wing.
							floorsS := arg.Have(
								"c floors s",
								"∀y:real. y ∈ s ⇒ c ≤ y",
								Derive(func(arg *Argument) {
									y := arg.Fix()
									inSide := arg.Assume()
									arg.Show(
										"a point of the side is a point of the union",
										By(inSide, floorsUnion.At(y), At(inUnion, s, t, y)))
								}))
							floorsT := arg.Have(
								"c floors t",
								"∀y:real. y ∈ t ⇒ c ≤ y",
								Derive(func(arg *Argument) {
									y := arg.Fix()
									inSide := arg.Assume()
									arg.Show(
										"a point of the side is a point of the union",
										By(inSide, floorsUnion.At(y), At(inUnion, s, t, y)))
								}))

							floorsInfS := arg.Have(
								"so c is under the infimum of s",
								"c ≤ inf(s)",
								By(nonemptyBounded, floorsS, ctx.Dep(BoundLessEqInf)))
							floorsInfT := arg.Have(
								"and under the infimum of t",
								"c ≤ inf(t)",
								By(nonemptyBounded, floorsT, ctx.Dep(BoundLessEqInf)))

							arg.Show(
								"and a floor under both is a floor under their min",
								By(floorsInfS, floorsInfT, At(LessEqMin, infS, infT, c)))
						})
					arg.Backward(
						"a point of the union lies over the infimum of its own side, and so over the min, and so over c",
						func(arg *Argument, floorsMeet Fact) {
							x := arg.Fix()
							inEither := arg.Assume()
							which := arg.Have(
								"x came from s, or from t",
								"x ∈ s ∨ x ∈ t",
								By(inEither, inUnion))
							minUnderX := arg.Have(
								"either way the min lies under it, being under one of the two",
								"min(inf(s), inf(t)) ≤ x",
								Derive(func(arg *Argument) {
									arg.Do(which.SplitDisj(
										LeftHolds(
											"from s, so over inf s",
											Given(func(arg *Argument, inS Fact) {
												arg.Show(
													"the infimum is under a member, and inf s is one of the two the min is under",
													By(inS, nonemptyBounded, At(InfLessEqMember, s, x), At(MinLessEq, infS, infT, x)))
											})),
										RightHolds(
											"from t, so over inf t",
											Given(func(arg *Argument, inT Fact) {
												arg.Show(
													"the infimum is under a member, and inf t is the other",
													By(inT, nonemptyBounded, At(InfLessEqMember, t, x), At(MinLessEq, infS, infT, x)))
											})),
									))
								}))
							arg.Show(
								"and c is under the min by hypothesis",
								By(minUnderX, floorsMeet, At(real_construction.LessEqTrans, c, meet, x)))
						})
				}))

			arg.Show(
				"and the lower bounds alone pin the infimum",
				By(sameBounds, ctx.Dep(InfUniqueGreatestBound)))
		}),
})}

// ---------------------------------------------------------------------
// The equations read backwards.
//
// Above, a set is given and its extremum computed. Here the traffic
// reverses: the pair equations name a set by listing it and ask what
// `real_sup` makes of two points, and the last member asks what it means for
// the two operators to return the same value.
//
// The pair is the attainment law's cleanest instance. `max(x, y)` is
// one of x and y — that is the whole content of its case definition —
// so it lies IN `{x, y}`, and it lies over both, so it is a greatest
// member and `SupUniqueAttained` names it the supremum. No completeness,
// no finiteness, no bound hypothesis: a two-point set carries its own
// witness.
//
// The peel of the first half is not available for it, and the reason is
// worth recording because it looks available. `SupInsertMax` at s = ∅
// plus `SupSingleton` reaches `real_sup {x, y}` in two cites — but at
// `real_max(y, x)`, since the peel reads the max off the INNER
// insertion, and turning that around needs commutativity of `real_max`,
// which no member of this chapter states.
//
// The collapse member is the only one here that argues about a set it
// cannot list. Its ⇒ direction squeezes: a member lies under `real_sup s` and
// over `real_inf s`, the hypothesis identifies those two, and antisymmetry
// leaves the member with nowhere to be but that one value. The squeeze
// is the analysis and it ends there, having produced two plain facts —
// every member of s IS `real_sup s`, and `real_sup s` is one of them. Naming the
// singleton from those two is no longer analysis but bookkeeping about
// what a set is, so the last line hands both to the set driver and the
// equation `s = {real_sup s}` comes back.
// ---------------------------------------------------------------------

// SupPairIsMax — the supremum of a two-point set is the greater point.
// The max is a MEMBER of the set, being one of the two arguments it is
// defined to return, and it caps the set, being over both; so it is a
// greatest member and attainment names it.
//
// Those are the only two facts the argument uses, and both are facts
// about the operation rather than about the set — `MaxIsArgument` and
// `MaxUpperBound`, each read at (x, y). Which of the two points the max
// turns out to be is never asked, so the case split the operation is
// defined by does not reach this member at all.
var SupPairIsMax = supPairIsMaxThm{family.Add(registry.ProofEntry{
	Name: "SupPairIsMax",
	Key:  "prop_b98277f8c384b0ec",
	Build: family.Theorem("∀x y:real. sup({x, y}) = max(x, y)",
		func(arg *Argument, x, y Term) {
			ctx := arg.Ctx()

			// The set driver is left to decide that {x, y} admits x, y
			// and nothing else — so that being one of the two puts the
			// max in, and being over each puts it on top.
			greatest := arg.Have(
				"the max is a greatest member of {x, y}: it is one of the two points listed, and it lies over both",
				"max(x, y) ∈ insert(x, insert(y, ∅)) ∧ (∀z:real. z ∈ insert(x, insert(y, ∅)) ⇒ z ≤ max(x, y))",
				BySets(At(MaxIsArgument, x, y), At(MaxUpperBound, x, y)))

			arg.Show(
				"and a greatest member IS the supremum",
				By(greatest, ctx.Dep(SupUniqueAttained)))
		}),
})}

// InfPairIsMin — the mirror: the infimum of a two-point set is the
// lesser point. The crossing is in which pair of lattice laws is cited
// — `MinIsArgument` and `MinLowerBound` where the sup wing has
// `MaxIsArgument` and `MaxUpperBound`.
var InfPairIsMin = infPairIsMinThm{family.Add(registry.ProofEntry{
	Name: "InfPairIsMin",
	Key:  "prop_b6ba56c2b9cd2f67",
	Build: family.Theorem("∀x y:real. inf({x, y}) = min(x, y)",
		func(arg *Argument, x, y Term) {
			ctx := arg.Ctx()

			// The same two facts about the operation, at the other
			// extremum; the set driver's share is unchanged.
			least := arg.Have(
				"the min is a least member of {x, y}: it is one of the two points listed, and it lies under both",
				"min(x, y) ∈ insert(x, insert(y, ∅)) ∧ (∀z:real. z ∈ insert(x, insert(y, ∅)) ⇒ min(x, y) ≤ z)",
				BySets(At(MinIsArgument, x, y), At(MinLowerBound, x, y)))

			arg.Show(
				"and a least member IS the infimum",
				By(least, ctx.Dep(InfUniqueAttained)))
		}),
})}

// SupEqInfIffSingleton — a bounded nonempty set has its two extrema
// equal exactly when it is a single point. It is the chapter's one
// statement in which the two operators meet, and it meets them by
// measuring the gap between them: the gap is what a set opens by
// spreading out, so no gap means no spread.
//
// ⇐ is immediate: a one-point set offers one value, and both
// operators return it.
//
// ⇒ is the squeeze. A member lies under `real_sup s` and over `real_inf s`, the
// hypothesis makes those the same value, and antisymmetry leaves the
// member nowhere to be but there — so every member IS `real_sup s`. That
// value is also a member, s having one at all, and a set all of whose
// points are one point, which it holds, is that point's singleton.
//
// The two one-sided bounds are what the two comparison members ask
// for, and nothing else in the argument looks at them.
var SupEqInfIffSingleton = supEqInfIffSingletonThm{family.Add(registry.ProofEntry{
	Name: "SupEqInfIffSingleton",
	Key:  "prop_c8d4f09b850830c2",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "sup(s) = inf(s) ⇔ ∃a:real. s = {a}",
	},
		func(arg *Argument, s Term, given Fact) {
			ctx := arg.Ctx()
			v := ops(ctx)
			supS := v.RealSup.Apply(s)

			parts := arg.Conjuncts(
				given,
				"s is not empty",
				"s is bounded above",
				"s is bounded below")
			upper, lower := parts[1], parts[2]

			arg.Iff()
			arg.Forward(
				"with no gap between the two, every member is squeezed onto the single value they share",
				func(arg *Argument, agree Fact) {
					// ↦ s ≠ ∅ (the goal-rewrite direction; see
					// real_sup_inf.go's header).
					w, holds := arg.Obtain(
						"s is nonempty, so it holds a member",
						// The ∃-binder is spelled w, not x: three later steps
						// fix the statement's own x, and the member's name must
						// not collide with it.
						"∃w:real. w ∈ s",
						Cite(set_basic.MemberNotEmpty))

					collapse := arg.Have(
						"every member is trapped at sup s: under it as a member, over it because inf s is that same value",
						"∀x:real. x ∈ s ⇒ x = sup(s)",
						Derive(func(arg *Argument) {
							x := arg.Fix()
							inS := arg.Assume()
							underSup := arg.Have(
								"x lies under sup s, s being bounded above",
								"x ≤ sup(s)",
								By(inS, upper, ctx.Dep(MemberLessEqSup)))
							// The hypothesis is spent here and nowhere else, and it
							// is spent as a rewrite: the fact available is the
							// INFIMUM's comparison with a member, and what the
							// squeeze needs is that comparison read at sup s.
							overSup := arg.Have(
								"and over sup s as well, that being the value inf s is",
								"sup(s) ≤ x",
								Derive(func(arg *Argument) {
									arg.Do(agree.Rw()) // ↦ real_inf(s) ≤ x
									arg.Show(
										"s is bounded below, so its infimum lies under every member",
										By(inS, lower, ctx.Dep(InfLessEqMember)))
								}))
							arg.Show(
								"so x is at once at or below sup s and at or above it",
								By(underSup, overSup, At(real_construction.LessEqAntisym, x, supS)))
						}))

					member := arg.Have(
						"so sup s is itself a member: the point s holds IS sup s",
						"sup(s) ∈ s",
						Derive(func(arg *Argument) {
							isSup := arg.Have(
								"the point s holds is sup s",
								"w = sup(s)",
								By(holds, collapse.At(w)))
							arg.Do(isSup.RwRev()) // ↦ the claim read at that point
							arg.Show(
								"which is the point we have",
								By(holds))
						}))

					arg.Take(supS) // the one point s turns out to be
					arg.Show(
						"a set whose every member is one value, and which holds that value, IS that value's singleton",
						BySets(collapse, member))
				})
			arg.Backward(
				"a one-point set leaves both operators the same value to choose",
				func(arg *Argument, isSingleton Fact) {
					a, listed := arg.Unpack(isSingleton) // listed: s = {a}
					arg.Do(listed.Rw())                  // ↦ real_sup({a}) = real_inf({a})
					arg.Do(CalcEq(
						Leg(
							a,
							"the one point is the supremum",
							Cite(SupSingleton)),
						FinalLeg(
							"and equally the infimum",
							Cite(InfSingleton)),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Finite sets attain their bounds
// ---------------------------------------------------------------------------
//
// A finite nonempty set has a maximal point by finite order theory.
// Under a total order that point is greatest. Applying this to the
// usual real order gives an attained upper bound; applying it to the
// reversed order gives an attained lower bound. SupUniqueAttained and
// InfUniqueAttained identify these points with the chosen extrema.
//
// The comparison laws below use only this attainment: the extremum is
// a member and bounds every member, so existential comparisons use it
// as a witness and universal comparisons instantiate at it.

// enlargedIsGreatestAt opens the chapter's greatest-member packaging:
// a value that is the added point or an old member, lying above the
// added point and above everything old, is a member of the enlarged set
// and caps it.
//
// The three premises arrive as separate facts. The insertion equation
// picks max(x, sup(s)); MaxIsArgument and the supremum's membership
// put this candidate among the enlarged set's points.
//
// Nothing here is analysis. The order relation enters only as an atom
// carried along — c is over this or that, and which is never asked — so
// what is left once the three premises are on the table is a question
// about insert: who is in the enlarged set. That is the set driver's
// subject — `BySets`, which closes by membership — and it settles both
// halves at once.
func enlargedIsGreatestAt(ctx *Script) *GoalStackNode {
	return ctx.Lemma(
		"∀t:set(real). ∀x c:real. "+
			"    (c = x ∨ c ∈ t) ⇒ "+
			"    x ≤ c ⇒ "+
			"    (∀y:real. y ∈ t ⇒ y ≤ c) ⇒ "+
			"    c ∈ insert(x, t) ∧ (∀y:real. y ∈ insert(x, t) ⇒ y ≤ c)",
		func(a *Argument, t, x, c Term, isXOrInT, capsX, capsT Fact) {
			a.Show(
				"the enlarged set admits x and whatever t admitted, and c "+
					"answers for both: it is one of them, and it is over each",
				BySets(isXOrInT, capsX, capsT))
		})
}

// enlargedIsLeastAt is the mirror of enlargedIsGreatestAt: the same
// packaging at the other extremum, floors where that one has caps. The
// note above applies here unchanged.
func enlargedIsLeastAt(ctx *Script) *GoalStackNode {
	return ctx.Lemma(
		"∀t:set(real). ∀x c:real. "+
			"    (c = x ∨ c ∈ t) ⇒ "+
			"    c ≤ x ⇒ "+
			"    (∀y:real. y ∈ t ⇒ c ≤ y) ⇒ "+
			"    c ∈ insert(x, t) ∧ (∀y:real. y ∈ insert(x, t) ⇒ c ≤ y)",
		func(a *Argument, t, x, c Term, isXOrInT, underX, underT Fact) {
			a.Show(
				"the enlarged set admits x and whatever t admitted, and c "+
					"answers for both: it is one of them, and it is under each",
				BySets(isXOrInT, underX, underT))
		})
}

// SupFiniteAttained — a finite nonempty set contains its supremum.
// A maximal point exists by finite order theory, is greatest under the
// real total order, and therefore equals the chosen supremum.
var SupFiniteAttained = supFiniteAttainedThm{family.Add(registry.ProofEntry{
	Name: "SupFiniteAttained",
	Key:  "prop_59996f8da8701dc6",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "sup(s) ∈ s ∧ (∀x:real. x ∈ s ⇒ x ≤ sup(s))",
	},
		func(a *Argument, s *Expr[Set[Real]], finiteNonempty Fact) {
			total := a.Have(
				"the usual real order is a total order",
				"total_order(real_le)",
				Unfold(order.TotalOrder),
				Unfold(order.PartialOrder),
				Unfold(order.Preorder),
				Unfold(equivalence.ReflexiveDef),
				Unfold(equivalence.TransitiveDef),
				Unfold(order.AntisymmetricDef),
				SplitConjAll(
					Case(
						"every real is below itself",
						Cite(real_order_ring.LessEqRefl)),
					Case(
						"real comparisons compose",
						Cite(real_construction.LessEqTrans)),
					Case(
						"mutual comparison gives equality",
						Cite(real_construction.LessEqAntisym)),
					Case(
						"any two reals are comparable",
						Cite(real_construction.LessEqTotal))))
			pre := order.PartialOrderPreorder.Read(order.TotalOrderPartialOrder.Read(total))
			m, maximal := a.ObtainAs[Real](
				"the finite nonempty set has a maximal point m",
				"∃m:real. maximal(real_le, s, m)",
				By(finiteNonempty, order.FiniteMaximal.Read(pre)))
			le := a.TermAs[Fun2[Real, Real, Bool]]("real_le")
			greatest := a.Have(
				"a maximal point in the total order is a greatest member",
				"m₀ ∈ s ∧ (∀x:real. x ∈ s ⇒ x ≤ m₀)",
				By(
					maximal,
					order.MaximalGreatest.Read(total),
					order.GreatestDef.At(le, s, m),
					order.UpperBoundDef.At(le, s, m)))
			a.Show(
				"the attained greatest member is the supremum",
				By(Normalized, greatest, SupUniqueAttained.At(s, m)))
		}),
})}

// InfFiniteAttained — a finite nonempty set contains its infimum.
// A maximal point for the reversed real order is a least member of s,
// and an attained least member equals the chosen infimum.
var InfFiniteAttained = infFiniteAttainedThm{family.Add(registry.ProofEntry{
	Name: "InfFiniteAttained",
	Key:  "prop_5c7c82935b47acd6",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "inf(s) ∈ s ∧ (∀x:real. x ∈ s ⇒ inf(s) ≤ x)",
		Abbrev: Abbrev{
			{Name: "reverse", Text: "λx:real. λy:real. y ≤ x"},
		},
	},
		func(a *Argument, s *Expr[Set[Real]], finiteNonempty Fact) {
			total := a.Have(
				"the reversed real order is a total order",
				"total_order(«reverse»)",
				Unfold(order.TotalOrder),
				Unfold(order.PartialOrder),
				Unfold(order.Preorder),
				Unfold(equivalence.ReflexiveDef),
				Unfold(equivalence.TransitiveDef),
				Unfold(order.AntisymmetricDef),
				SplitConjAll(
					Case(
						"every real is below itself in the reversed order",
						Cite(real_order_ring.LessEqRefl)),
					Case(
						"reversed comparisons compose",
						By(real_construction.LessEqTrans)),
					Case(
						"mutual reversed comparison gives equality",
						By(real_construction.LessEqAntisym)),
					Case(
						"any two reals are comparable in the reversed order",
						Cite(real_construction.LessEqTotal))))
			pre := order.PartialOrderPreorder.Read(order.TotalOrderPartialOrder.Read(total))
			m, maximal := a.ObtainAs[Real](
				"the finite nonempty set has a maximal point for the reversed order",
				"∃m:real. maximal(«reverse», s, m)",
				By(finiteNonempty, order.FiniteMaximal.Read(pre)))
			reverse := a.TermAs[Fun2[Real, Real, Bool]]("«reverse»")
			least := a.Have(
				"a greatest member in the reversed order is a least member in the usual order",
				"m₀ ∈ s ∧ (∀x:real. x ∈ s ⇒ m₀ ≤ x)",
				By(
					maximal,
					order.MaximalGreatest.Read(total),
					order.GreatestDef.At(reverse, s, m),
					order.UpperBoundDef.At(reverse, s, m)))
			a.Show(
				"the attained least member is the infimum",
				By(Normalized, least, InfUniqueAttained.At(s, m)))
		}),
})}

// SupFiniteIffGreatest — on a finite nonempty set, `real_sup s = a` says
// exactly that a is a greatest member. The two directions are the two
// halves of the story this file tells: attainment says a greatest
// member is the supremum, and SupFiniteAttained says the supremum is a
// greatest member.
//
// Only the ⇒ direction spends finiteness. Attainment holds of any set
// whose bound is reached, so the ⇐ arm never asks whether s is finite —
// which is why it cites the characterization entry rather than this
// file's own.
var SupFiniteIffGreatest = supFiniteIffGreatestThm{family.Add(registry.ProofEntry{
	Name: "SupFiniteIffGreatest",
	Key:  "prop_a985ea3e3a9e8253",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "sup(s) = a ⇔ a ∈ s ∧ (∀y:real. y ∈ s ⇒ y ≤ a)",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			ctx := arg.Ctx()
			attainment := ctx.Dep(SupUniqueAttained)
			finiteAttains := ctx.Dep(SupFiniteAttained)

			arg.Iff()
			arg.Forward(
				"the supremum of a finite set is a greatest member, and here it is a",
				func(arg *Argument, isA Fact) {
					arg.Do(isA.RwRev()) // ↦ the claim read at real_sup(s)
					arg.Show(
						"which is what a finite set attains",
						By(finiteNonempty, finiteAttains))
				})
			arg.Backward(
				"a is a greatest member, and a greatest member IS the supremum",
				func(arg *Argument, greatest Fact) {
					arg.Show(
						"attainment",
						By(greatest, attainment))
				})
		}),
})}

// InfFiniteIffLeast — the mirror: on a finite nonempty set, `real_inf s = a`
// says exactly that a is a least member.
var InfFiniteIffLeast = infFiniteIffLeastThm{family.Add(registry.ProofEntry{
	Name: "InfFiniteIffLeast",
	Key:  "prop_a2c9a27e21c69fef",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "inf(s) = a ⇔ a ∈ s ∧ (∀y:real. y ∈ s ⇒ a ≤ y)",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			ctx := arg.Ctx()
			attainment := ctx.Dep(InfUniqueAttained)
			finiteAttains := ctx.Dep(InfFiniteAttained)

			arg.Iff()
			arg.Forward(
				"the infimum of a finite set is a least member, and here it is a",
				func(arg *Argument, isA Fact) {
					arg.Do(isA.RwRev()) // ↦ the claim read at real_inf(s)
					arg.Show(
						"which is what a finite set attains",
						By(finiteNonempty, finiteAttains))
				})
			arg.Backward(
				"a is a least member, and a least member IS the infimum",
				func(arg *Argument, least Fact) {
					arg.Show(
						"attainment",
						By(least, attainment))
				})
		}),
})}

// ---------------------------------------------------------------------
// The comparison laws.
//
// Everything below follows from attainment alone: once `real_sup s` is known
// to be a member, each comparison with it decomposes into the member it
// is, and one step of transitivity. FINITENESS never enters these eight
// proofs — it is spent entirely by the cite that supplies attainment, so
// the laws below are about attained extrema and inherit their finiteness
// hypothesis rather than using it.
//
// Each equivalence has one arm that uses the extremum's own membership —
// as the WITNESS where that arm is existential, as the INSTANTIATION
// POINT where it is universal — and one arm that is a single step of
// transitivity. Which transitivity law is forced by where the strict
// side sits: a strict leg below the extremum takes LessThanLessEqTrans,
// one above it takes LessEqLessThanTrans. One law suffices in each case.
//
// The pairs below are ordered by relation and then by arm shape —
// (∃, ≤), (∀, ≤), (∃, <), (∀, <) — and that ordering is what makes each
// adjacent two a mirror. It is worth stating because the pairing is not
// the one a reader guesses from the names alone: `LessEqSupFinite`
// mirrors `InfLessEqFinite`, not `LessEqInfFinite`.
// ---------------------------------------------------------------------

// supAttainedAt opens the attainment fact at s and names its two
// halves, which is where the four sup laws below begin. Its mirror
// follows, and the note here covers both.
//
// The cite delivers both halves as ONE conjunction and there is no
// combinator for projecting a conjunct out of a `Fact`, so each half
// is claimed separately and the same cite is made twice.
func supAttainedAt(a *Argument, s Term, finiteNonempty Fact) (member, caps Fact) {
	// The raw surface, grounded at s. Every caller binds its set as `s`,
	// which the claims spell.
	attained := At(SupFiniteAttained, s)
	member = a.Have(
		"sup s is itself a member of s",
		"sup(s) ∈ s",
		By(finiteNonempty, attained))
	caps = a.Have(
		"and it lies at or above every member",
		"∀x:real. x ∈ s ⇒ x ≤ sup(s)",
		By(finiteNonempty, attained))
	return member, caps
}

// infAttainedAt is the mirror of supAttainedAt: the same two halves at
// the other extremum, floors where the sup wing has caps. The note above
// applies here unchanged.
func infAttainedAt(a *Argument, s Term, finiteNonempty Fact) (member, floors Fact) {
	// The raw surface, grounded at s. Every caller binds its set as `s`,
	// which the claims spell.
	attained := At(InfFiniteAttained, s)
	member = a.Have(
		"inf s is itself a member of s",
		"inf(s) ∈ s",
		By(finiteNonempty, attained))
	floors = a.Have(
		"and it lies at or below every member",
		"∀x:real. x ∈ s ⇒ inf(s) ≤ x",
		By(finiteNonempty, attained))
	return member, floors
}

// LessEqSupFinite — to lie at or below the supremum of a finite set is
// to lie at or below one of its members. Reaching the supremum from
// below needs no approximation once it is attained: the member to
// produce is the supremum itself.
var LessEqSupFinite = lessEqSupFiniteThm{family.Add(registry.ProofEntry{
	Name: "LessEqSupFinite",
	Key:  "prop_dd14c5f16eaee259",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "a ≤ sup(s) ⇔ ∃x:real. x ∈ s ∧ a ≤ x",
	},
		// The statement binds `a`, so the context parameter is `arg`; the
		// same holds in each comparison law below.
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			supS := ops(arg.Ctx()).RealSup.Apply(s)
			member, caps := supAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"sup s is itself a member at or above a",
				func(arg *Argument, aLeSup Fact) {
					arg.Take(supS)
					arg.Show(
						"membership from attainment, the comparison from the hypothesis",
						By(member, aLeSup))
				})
			arg.Backward(
				"some member lies at or above a, and sup s lies over that member",
				func(arg *Argument, someMemberAbove Fact) {
					x, memberAbove := arg.Unpack(someMemberAbove)
					arg.Show(
						"transitivity through that member", // a ≤ x ≤ sup s
						By(caps.At(x), memberAbove, At(real_construction.LessEqTrans, a, x, supS)))
				})
		}),
})}

// InfLessEqFinite — `real_inf s` lies at or below a exactly when SOME member
// does. The existential is never searched for: the member that witnesses
// it is inf s itself.
var InfLessEqFinite = infLessEqFiniteThm{family.Add(registry.ProofEntry{
	Name: "InfLessEqFinite",
	Key:  "prop_c948dd9d387b23",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "inf(s) ≤ a ⇔ ∃x:real. x ∈ s ∧ x ≤ a",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			infS := ops(arg.Ctx()).RealInf.Apply(s)
			member, floors := infAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"inf s is itself a member at or below a",
				func(arg *Argument, infLeA Fact) {
					arg.Take(infS)
					arg.Show(
						"membership from attainment, the comparison from the hypothesis",
						By(member, infLeA))
				})
			arg.Backward(
				"some member lies at or below a, and inf s lies under that member",
				func(arg *Argument, someMemberBelow Fact) {
					x, memberBelow := arg.Unpack(someMemberBelow)
					arg.Show(
						"transitivity through that member", // inf s ≤ x ≤ a
						By(floors.At(x), memberBelow, At(real_construction.LessEqTrans, infS, x, a)))
				})
		}),
})}

// SupLessEqFinite — a bound on the members of a finite set is a bound
// on its supremum, and conversely. This is leastness with the
// existence side removed: `real_sup s` is not merely below every cap, it IS
// one of the values being capped, so the ⇐ direction is the hypothesis
// read at a single point.
var SupLessEqFinite = supLessEqFiniteThm{family.Add(registry.ProofEntry{
	Name: "SupLessEqFinite",
	Key:  "prop_5cbb6898a15d27bb",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "sup(s) ≤ a ⇔ ∀x:real. x ∈ s ⇒ x ≤ a",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			supS := ops(arg.Ctx()).RealSup.Apply(s)
			member, caps := supAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"every member is at or below sup s, which is at or below a",
				func(arg *Argument, supLeA Fact) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"transitivity through sup s", // x ≤ sup s ≤ a
						By(caps.At(x), inS, supLeA, At(real_construction.LessEqTrans, x, supS, a)))
				})
			arg.Backward(
				"a caps every member, and sup s is one of them",
				func(arg *Argument, aCaps Fact) {
					arg.Show(
						"the cap read at sup s itself", // sup s ≤ a
						By(aCaps.At(supS), member))
				})
		}),
})}

// LessEqInfFinite — a lies at or below `real_inf s` exactly when it lies at
// or below every member. One direction is the infimum's own membership:
// a statement about every member is in particular a statement about
// inf s. The other passes each member through inf s.
var LessEqInfFinite = lessEqInfFiniteThm{family.Add(registry.ProofEntry{
	Name: "LessEqInfFinite",
	Key:  "prop_6ec9b14ebdbe7e3b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "a ≤ inf(s) ⇔ ∀x:real. x ∈ s ⇒ a ≤ x",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			infS := ops(arg.Ctx()).RealInf.Apply(s)
			member, floors := infAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"every member is at or above inf s, which is at or above a",
				func(arg *Argument, aLeInf Fact) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"transitivity through inf s", // a ≤ inf s ≤ x
						By(floors.At(x), inS, aLeInf, At(real_construction.LessEqTrans, a, infS, x)))
				})
			arg.Backward(
				"a floors every member, and inf s is one of them",
				func(arg *Argument, aFloors Fact) {
					arg.Show(
						"the floor read at inf s itself", // a ≤ inf s
						By(aFloors.At(infS), member))
				})
		}),
})}

// LessThanSupFinite — the strict form of LessEqSupFinite: to lie
// strictly below the supremum of a finite set is to lie strictly below
// one of its members. On a general set this is the approximation
// property and costs a contraposition (real_sup_inf.go); attained, it is
// again the supremum exhibiting itself. Its strict leg sits below
// sup s, so the section's transitivity rule takes LessThanLessEqTrans.
var LessThanSupFinite = lessThanSupFiniteThm{family.Add(registry.ProofEntry{
	Name: "LessThanSupFinite",
	Key:  "prop_f3bea87291a3cc5",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "a < sup(s) ⇔ ∃x:real. x ∈ s ∧ a < x",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			supS := ops(arg.Ctx()).RealSup.Apply(s)
			member, caps := supAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"sup s is itself a member strictly above a",
				func(arg *Argument, aLtSup Fact) {
					arg.Take(supS)
					arg.Show(
						"membership from attainment, the comparison from the hypothesis",
						By(member, aLtSup))
				})
			arg.Backward(
				"some member lies strictly above a, and sup s lies over that member",
				func(arg *Argument, someMemberAbove Fact) {
					x, memberAbove := arg.Unpack(someMemberAbove)
					arg.Show(
						"mixed transitivity through that member", // a < x ≤ sup s
						By(caps.At(x), memberAbove, At(real_order_ring.LessThanLessEqTrans, a, x, supS)))
				})
		}),
})}

// InfLessThanFinite — the strict form of InfLessEqFinite. Its strict
// leg sits above inf s, so the section's transitivity rule takes
// LessEqLessThanTrans.
var InfLessThanFinite = infLessThanFiniteThm{family.Add(registry.ProofEntry{
	Name: "InfLessThanFinite",
	Key:  "prop_f29971b04da310ce",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "inf(s) < a ⇔ ∃x:real. x ∈ s ∧ x < a",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			infS := ops(arg.Ctx()).RealInf.Apply(s)
			member, floors := infAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"inf s is itself a member strictly below a",
				func(arg *Argument, infLtA Fact) {
					arg.Take(infS)
					arg.Show(
						"membership from attainment, the comparison from the hypothesis",
						By(member, infLtA))
				})
			arg.Backward(
				"some member lies strictly below a, and inf s lies under that member",
				func(arg *Argument, someMemberBelow Fact) {
					x, memberBelow := arg.Unpack(someMemberBelow)
					arg.Show(
						"mixed transitivity through that member", // inf s ≤ x < a
						By(floors.At(x), memberBelow, At(real_order_ring.LessEqLessThanTrans, infS, x, a)))
				})
		}),
})}

// SupLessThanFinite — the strict form of SupLessEqFinite: a strict
// bound on the members of a finite set is a strict bound on its
// supremum. Its strict leg sits above sup s, so the section's
// transitivity rule takes LessEqLessThanTrans.
var SupLessThanFinite = supLessThanFiniteThm{family.Add(registry.ProofEntry{
	Name: "SupLessThanFinite",
	Key:  "prop_817317722744d203",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "sup(s) < a ⇔ ∀x:real. x ∈ s ⇒ x < a",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			supS := ops(arg.Ctx()).RealSup.Apply(s)
			member, caps := supAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"every member is at or below sup s, which is strictly below a",
				func(arg *Argument, supLtA Fact) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"mixed transitivity through sup s", // x ≤ sup s < a
						By(caps.At(x), inS, supLtA, At(real_order_ring.LessEqLessThanTrans, x, supS, a)))
				})
			arg.Backward(
				"a strictly caps every member, and sup s is one of them",
				func(arg *Argument, aCapsStrictly Fact) {
					arg.Show(
						"the strict cap read at sup s itself", // sup s < a
						By(aCapsStrictly.At(supS), member))
				})
		}),
})}

// LessThanInfFinite — the strict form of LessEqInfFinite, and the same
// two moves. Its strict leg sits below inf s, so the section's
// transitivity rule takes LessThanLessEqTrans.
var LessThanInfFinite = lessThanInfFiniteThm{family.Add(registry.ProofEntry{
	Name: "LessThanInfFinite",
	Key:  "prop_b14455cd32298460",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "a < inf(s) ⇔ ∀x:real. x ∈ s ⇒ a < x",
	},
		func(arg *Argument, s, a Term, finiteNonempty Fact) {
			infS := ops(arg.Ctx()).RealInf.Apply(s)
			member, floors := infAttainedAt(arg, s, finiteNonempty)

			arg.Iff()
			arg.Forward(
				"every member is at or above inf s, which is strictly above a",
				func(arg *Argument, aLtInf Fact) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"mixed transitivity through inf s", // a < inf s ≤ x
						By(floors.At(x), inS, aLtInf, At(real_order_ring.LessThanLessEqTrans, a, infS, x)))
				})
			arg.Backward(
				"a strictly floors every member, and inf s is one of them",
				func(arg *Argument, aFloorsStrictly Fact) {
					arg.Show(
						"the strict floor read at inf s itself", // a < inf s
						By(aFloorsStrictly.At(infS), member))
				})
		}),
})}
