// apply_close_comprehension_test.go — the apply rung reads a membership
// in a set-builder as the predicate at the point: a guard
// `x ∈ {p | P(p)}` is supplied by a resident `P(x)`, and a guard `P(x)`
// by a resident `x ∈ {p | P(p)}`, the two being one condition — the
// spelling the set driver's unfolding reaches (set_member,
// set_comprehension and comprehension_spec unfolded, β, the ∃-one-point
// fusion). Measured before the reading: a guard restated as the
// membership in an index set (`i ∈ {i | i ≤ n}` for `i ≤ n`) fell to the
// refuter, and a structure law's guard at a comprehension carrier
// (`u ∈ {p | polynomial_over(c, p)}` with `polynomial_over(c, u)`
// resident, polynomial.PolynomialModuleOn) waited for an iff Have that
// bridged the two spellings.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// comprehensionScope is the vocabulary of the tests on a membership in
// a set-builder: two predicates of a number, a function, points, and
// the set-builder's constants with their definitions.
func comprehensionScope() *dsl.ParseScope {
	num := ext.NumType
	return &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"P": core.MakeFun(num, core.TypeBool()),
			"K": core.MakeFun(num, core.TypeBool()),
			"f": core.MakeFun(num, num),
			"a": num,
			"n": num,
			"Q": core.TypeBool(),
		},
		ConstMetas: setBuilderVocabulary(),
	}
}

// A resident law guarded by a membership in a set-builder applies to
// the goal with the predicate at the point resident, and a law guarded
// by the predicate applies with the membership resident: the guard and
// the fact are one condition in two spellings. A different predicate
// is not read as the same, and a conjunctive predicate is supplied
// conjunct by conjunct as a conjunctive guard is.
func TestApplyClose_MembershipInComprehensionIsThePredicate(t *testing.T) {
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, comprehensionScope())
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}

	closed, miss, sec := closes("P(a) ⇒ (∀x:num. x ∈ {p:num | P(p)} ⇒ f(x) = x) ⇒ f(a) = a", 2)
	require.True(t, closed, "a guard in a set-builder, the predicate at the point resident: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("a ∈ {p:num | P(p)} ⇒ (∀x:num. P(x) ⇒ f(x) = x) ⇒ f(a) = a", 2)
	require.True(t, closed, "a guard as the predicate, the membership resident: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("a ≤ n ⇒ (∀x:num. x ∈ {i:num | i ≤ n} ⇒ f(x) = x) ⇒ f(a) = a", 2)
	require.True(t, closed, "an index set: `x ∈ {i | i ≤ n}` is `x ≤ n`: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("P(a) ⇒ K(a) ⇒ (∀x:num. x ∈ {p:num | P(p) ∧ K(p)} ⇒ f(x) = x) ⇒ f(a) = a", 3)
	require.True(t, closed, "a conjunctive predicate, supplied conjunct by conjunct: %s", miss)
	require.True(t, sec.Proved())

	closed, _, _ = closes("P(a) ⇒ (∀x:num. x ∈ {p:num | K(p)} ⇒ f(x) = x) ⇒ f(a) = a", 2)
	require.False(t, closed, "a different predicate is not the guard")

	closed, _, _ = closes("P(n) ⇒ (∀x:num. x ∈ {p:num | P(p)} ⇒ f(x) = x) ⇒ f(a) = a", 2)
	require.False(t, closed, "the predicate at another point is not the guard")
}

// The By premise's guard reading is the same reading: a witnessed
// cite's guard `a ∈ {p | P(p)}` is supplied by a resident `P(a)`, and
// the guard `P(a)` by a resident membership.
func TestGuardSuppliedByContext_MembershipInComprehension(t *testing.T) {
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, comprehensionScope())
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	member := parse("a ∈ {p:num | P(p)}")
	point := parse("P(a)")

	byPredicate := core.MakeProp(parse("Q"), point)
	require.True(t, guardSuppliedByContext(byPredicate, member, rungOpts{}), "the membership guard from the predicate at the point")
	require.False(t, guardSuppliedByContext(byPredicate, parse("a ∈ {p:num | K(p)}"), rungOpts{}), "a different predicate")

	byMembership := core.MakeProp(parse("Q"), member)
	require.True(t, guardSuppliedByContext(byMembership, point, rungOpts{}), "the predicate guard from the membership")
	require.False(t, guardSuppliedByContext(byMembership, parse("K(a)"), rungOpts{}), "a different predicate")
}

// A structure law cited bare beside its instance at a comprehension
// carrier closes keyless: the law's carrier binder is pinned to the
// set-builder from the structure fact, and its membership guards are
// supplied by the resident memberships (the control — the folded
// spelling on both sides) or by the predicate at the points, the facts
// a proof over the set's members holds.
//
//	law:  ∀add c. S(add, c) ⇒ ∀x y. x ∈ c ∧ y ∈ c ⇒ add(x, y) = add(y, x)
//	S(vadd, {p | P(p)}),  u ∈ {p | P(p)},  v ∈ {p | P(p)}  ⊢  vadd(u, v) = vadd(v, u)
//	S(vadd, {p | P(p)}),  P(u),  P(v)                      ⊢  vadd(u, v) = vadd(v, u)
func TestByApply_StructureLawAtAComprehensionCarrier(t *testing.T) {
	num := ext.NumType
	add := ext.Var("add", core.MakeFun(num, core.MakeFun(num, num)))
	c := ext.Var("c", core.MakeFun(num, core.TypeBool()))
	// A constant, not a variable: a premise's normalized install closes
	// over its free variables, and a law over an arbitrary S would say
	// far more than the stated one.
	S := core.NewConstDef(add.To(c.To(c.Eq(c))), "zz_comprehension_s")
	scope := comprehensionScope()
	scope.Vars["u"] = num
	scope.Vars["v"] = num
	scope.Vars["vadd"] = add.Type()
	scope.Consts = map[string]core.ConstTerm{"zz_comprehension_s": S}
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	law := parse("∀add:(num → num → num). ∀c:set(num). zz_comprehension_s(add, c) ⇒ ∀x y:num. x ∈ c ∧ y ∈ c ⇒ add(x, y) = add(y, x)")
	instance := parse("zz_comprehension_s(vadd, {p:num | P(p)})")
	concl := parse("vadd(u, v) = vadd(v, u)")

	statedProp := prop.MakeProp(law)
	normalized, _ := prop.Normalize(statedProp)
	require.NotNil(t, normalized)
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: normalized, Reference: statedProp, Describe: "the commutativity law"},
		{Install: prop.MakeProp(instance), Resident: true, Describe: "the structure fact"},
	}}

	for name, facts := range map[string][]core.Term{
		"the memberships resident":             {parse("u ∈ {p:num | P(p)}"), parse("v ∈ {p:num | P(p)}")},
		"the predicate at the points resident": {parse("P(u)"), parse("P(v)")},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(concl, append([]core.Term{instance}, facts...)...)
			spec := spec
			for _, f := range facts {
				spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(f), Resident: true, Describe: ext.PrintTerm(f)})
			}
			st := newGroundByStore()
			live := groundTestEnv(t)
			st.wire(live, true)
			n := CreateGoalStack(goal)
			// A By whose closers all fail panics; reported as a failure here.
			require.NotPanics(t, func() { require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close") })
			assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it, not the refuter")
			assert.Empty(t, st.Plans(), "and before the grounding stage, so no plan entry")

			// Strict replay from an empty store: the move records nothing.
			strict := groundTestEnv(t)
			newGroundByStore().wire(strict, true)
			strict.RequireCNFCacheHit = true
			n2 := CreateGoalStack(goal)
			require.NotPanics(t, func() {
				require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay must close from an EMPTY store")
			})
		})
	}
}

// A head is matched as spelled first, and in the membership normal form
// only where no reading matches so: a law whose set is a binder, `y ∈ s`,
// meets a goal spelled with a set-builder at s := the set-builder, as it
// always has (num_segment.BelowStrictInjectiveOnto cites
// cardinality.SurjectiveIffInjective so, keyless), where a goal read
// first would have matched nothing; and a law concluding a membership in
// an explicit set-builder applies to the condition at the point.
func TestApplyClose_HeadMatchedAsSpelledThenRead(t *testing.T) {
	scope := comprehensionScope()
	scope.Vars["S"] = core.MakeFun(core.MakeFun(ext.NumType, core.TypeBool()), core.TypeBool())
	scope.Vars["R"] = core.MakeFun(ext.NumType, core.TypeBool())
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, scope)
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}

	closed, miss, sec := closes("S({i:num | i < n}) ⇒ (∀s:(num → bool). S(s) ⇒ a ∈ s) ⇒ a ∈ {i:num | i < n}", 2)
	require.True(t, closed, "the set a binder, the goal spelled with the set-builder: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("R(a) ⇒ (∀y:num. R(y) ⇒ y ∈ {p:num | P(p)}) ⇒ P(a)", 2)
	require.True(t, closed, "a law concluding a membership in a set-builder, at the condition: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("R(a) ⇒ (∀y:num. R(y) ⇒ y ∈ {p:num | P(p) ∧ K(p)}) ⇒ K(a)", 2)
	require.True(t, closed, "and at a conjunct of the condition: %s", miss)
	require.True(t, sec.Proved())
}

// A membership in a set-builder whose condition is a conjunction is ONE
// resident fact holding the conjunction at the point: a head whose
// antecedent is that conjunction is supplied by it as a whole, and the
// discharge reads the leaf's memberships before it splits the
// antecedent — split first, neither side alone is anything the context
// holds. The shape of the colon submodule's closure facts: the set
// `{x | x ∈ L ∧ ∀n. n ∈ N ⇒ x * n ∈ P}` with the facts stated pointwise.
func TestApplyClose_ConjunctiveConditionHeldAsOneMembership(t *testing.T) {
	res := dsl.ParsePropTextInScope("a ∈ {p:num | P(p) ∧ K(p)} ⇒ (∀x:num. P(x) ∧ K(x) ⇒ f(x) = x) ⇒ f(a) = a", comprehensionScope())
	require.Empty(t, res.Errors, "%v", res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	sec.Do(StripImp())
	sec.Do(StripImp())
	var claims []*GoalStackNode
	closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
	require.True(t, closed, "the conjunctive antecedent, held as one membership: %s", miss)
	require.True(t, sec.Proved())

	// The discharge alone, on what the closed reading accepts.
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, comprehensionScope())
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	for _, c := range []struct{ resident, concl string }{
		{"a ∈ {p:num | P(p) ∧ K(p)}", "P(a) ∧ K(a)"},
		{"a ∈ {p:num | P(p) ∧ K(p)}", "a ∈ {p:num | P(p)} ∧ K(a)"},
		{"P(a) ∧ K(a)", "a ∈ {p:num | P(p) ∧ K(p)}"},
	} {
		goal := prop.MakeProp(parse(c.concl), parse(c.resident))
		require.True(t, residentByAssumption(goal, goal.Conclusion(), rungOpts{}), "%s ⊢ %s is accepted", c.resident, c.concl)
		leaf := NewScript(makeStepTestEnv()).Section(goal)
		proveResident(leaf, false)
		require.True(t, leaf.Proved(), "%s ⊢ %s is discharged", c.resident, c.concl)
	}
}

// A membership in a three-part set-builder is read to its ∃: a goal
// spelled as that ∃ closes on the resident membership, and the
// membership closes on the resident ∃, keyless and under strict replay
// from an empty store — the shape of fractional_ideal's products, where
// each direction ran to the refuter's budget before the reading. The
// witnesses stay the author's: with only the members' memberships
// resident the membership is the set driver's, not the rung's.
func TestByApply_ThreePartMembershipIsItsExists(t *testing.T) {
	num := ext.NumType
	scope := comprehensionScope()
	scope.Vars["S"] = core.MakeFun(num, core.TypeBool())
	scope.Vars["M"] = core.MakeFun(num, core.TypeBool())
	scope.Vars["u"] = num
	scope.Vars["g"] = core.MakeFun(num, core.MakeFun(num, num))
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	member := parse("u ∈ {g(s, m):num | s:num, m:num | s ∈ S ∧ m ∈ M}")
	exists := parse("∃s m:num. (s ∈ S ∧ m ∈ M) ∧ u = g(s, m)")
	for name, c := range map[string]struct{ concl, resident core.Term }{
		"the ∃ from the membership": {exists, member},
		"the membership from the ∃": {member, exists},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(c.concl, c.resident)
			spec := BySpec{Premises: []ByPremiseSpec{{Install: prop.MakeProp(c.resident), Resident: true, Describe: ext.PrintTerm(c.resident)}}}
			st := newGroundByStore()
			live := groundTestEnv(t)
			st.wire(live, true)
			n := CreateGoalStack(goal)
			require.NotPanics(t, func() { require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close") })
			assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it, not the refuter")
			assert.Empty(t, st.Plans(), "and before the grounding stage, so no plan entry")

			strict := groundTestEnv(t)
			newGroundByStore().wire(strict, true)
			strict.RequireCNFCacheHit = true
			n2 := CreateGoalStack(goal)
			require.NotPanics(t, func() {
				require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay must close from an EMPTY store")
			})
		})
	}
}

// A goal membership in a set-builder whose condition is a conjunction
// closes conjunct by conjunct on the resident conjuncts, and one conjunct
// closes on a resident such membership — the goal closed as an
// antecedent of its shape is (closeGoal), keyless and under strict
// replay from an empty store. Before: both ran to the refuter's budget
// (fractional_ideal.FractionalMulSpan's `zero ∈ {y | y ∈ L ∧ y * n ∈ P}`,
// topology_category.TopologyIsomorphismIff's conjunct out of a membership).
func TestByApply_ConjunctiveConditionAsTheGoal(t *testing.T) {
	num := ext.NumType
	scope := comprehensionScope()
	scope.Vars["S"] = core.MakeFun(num, core.TypeBool())
	scope.Vars["M"] = core.MakeFun(num, core.TypeBool())
	scope.Vars["g"] = core.MakeFun(num, core.MakeFun(num, num))
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	member := parse("a ∈ {y:num | y ∈ S ∧ g(y, n) ∈ M}")
	for name, c := range map[string]struct {
		concl     core.Term
		residents []core.Term
	}{
		"the membership from its conjuncts":        {member, []core.Term{parse("a ∈ S"), parse("g(a, n) ∈ M")}},
		"one conjunct out of the membership":       {parse("g(a, n) ∈ M"), []core.Term{member}},
		"the first conjunct out of the membership": {parse("a ∈ S"), []core.Term{member}},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(c.concl, c.residents...)
			var spec BySpec
			for _, r := range c.residents {
				spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(r), Resident: true, Describe: ext.PrintTerm(r)})
			}
			st := newGroundByStore()
			live := groundTestEnv(t)
			st.wire(live, true)
			n := CreateGoalStack(goal)
			require.NotPanics(t, func() { require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close") })
			assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it, not the refuter")
			assert.Empty(t, st.Plans(), "and before the grounding stage, so no plan entry")

			strict := groundTestEnv(t)
			newGroundByStore().wire(strict, true)
			strict.RequireCNFCacheHit = true
			n2 := CreateGoalStack(goal)
			require.NotPanics(t, func() {
				require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay must close from an EMPTY store")
			})
		})
	}
}
