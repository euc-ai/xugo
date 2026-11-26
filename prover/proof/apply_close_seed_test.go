package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

func parseFor(t *testing.T, text string) core.Prop {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop
}

// A pinned binder's term type decides which candidate instances can
// pass the plan at all: the instance giving h a different type is
// dropped, the consistent one kept, and a candidate that does not bind
// the pinned name is unconstrained.
func TestConsistentWithPins(t *testing.T) {
	right := parseFor(t, "∀h:((num → A) → A). ∀x:(num → A). h(x) = h(x)")
	wrong := parseFor(t, "∀h:(A → (num → A)). ∀x:A. h(x) = h(x)")
	unbound := parseFor(t, "∀g:(num → num). g(0) = g(0)")
	pinned := ext.Var("pair", core.MakeFun(core.MakeFun(ext.NumType, core.TypeA()), core.TypeA())).Core()
	pins := pinnedBinderTypes([]NamedWitness{{Binder: "h", Witness: pinned}})

	kept := consistentWithPins([]core.Prop{wrong, right, unbound}, pins)
	require.Len(t, kept, 2)
	require.True(t, kept[0].AlphaEquals(right))
	require.True(t, kept[1].AlphaEquals(unbound))

	require.Empty(t, consistentWithPins([]core.Prop{wrong}, pins))
	require.Nil(t, pinnedBinderTypes(nil))
}

// An antecedent is resident up to βη, not only up to α: the big-operator
// sugar lowers `Σ_{i∈k} u(i)` to `real_sum(k, λi.u(i))` while a law binds the
// bare `u`, so the fact the context holds and the antecedent the head
// asks for differ by one η-expansion that Normalize identifies. The
// guard path already reads both the same way (residentModuloBetaEta);
// the dry run's antecedent check must too, or the leaf falls to the
// refuter and costs a key (convex.VanishingWeights).
func TestStructurallyResident_ModuloEta(t *testing.T) {
	numFn := core.MakeFun(ext.NumType, ext.NumType)
	scope := &dsl.ParseScope{Vars: map[string]core.HolType{
		"R": core.MakeFun(numFn, core.TypeBool()),
		"g": numFn,
		"P": core.TypeBool(),
		"Q": core.TypeBool(),
	}}
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	etaLong := parse("R(λi:num. g(i))")
	etaShort := parse("R(g)")
	other := parse("P")
	// MakeProp takes the conclusion first; the context is the two facts.
	goal := core.MakeProp(parse("Q"), etaLong, other)

	require.True(t, structurallyResident(goal, etaLong, rungOpts{}), "α-resident")
	require.True(t, structurallyResident(goal, etaShort, rungOpts{}), "resident up to η")
	require.True(t, structurallyResident(goal, ext.WrapTerm(etaShort).And(ext.WrapTerm(other)).Core(), rungOpts{}),
		"a conjunction whose conjuncts are resident, one of them up to η")
	require.False(t, structurallyResident(goal, parse("R(λi:num. i)"), rungOpts{}), "a different fact")
}

// A guard is supplied by the context as written or conjunct by conjunct,
// and "as written" holds for a conjunction too: a cite whose guard
// `A ∧ B ∧ C` is resident as ONE fact takes the stated form like one
// whose guard is resident as three. Read conjunct-wise only, the whole
// fact was missed and the witnessed cite fell to its clause form — the
// monotonicity criterion cited at a pair with its bounds stated as one
// Have (real_derivative.IncreasingIffDerivativeNonneg).
func TestGuardSuppliedByContext_WholeConjunctionAndItsParts(t *testing.T) {
	scope := &dsl.ParseScope{Vars: map[string]core.HolType{
		"A": core.TypeBool(), "B": core.TypeBool(), "C": core.TypeBool(),
		"D": core.TypeBool(), "Q": core.TypeBool(),
	}}
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	and := func(a, b core.Term) core.Term { return ext.WrapTerm(a).And(ext.WrapTerm(b)).Core() }
	A, B, C, D := parse("A"), parse("B"), parse("C"), parse("D")

	whole := core.MakeProp(parse("Q"), and(and(A, B), C))
	require.True(t, guardSuppliedByContext(whole, and(and(A, B), C), rungOpts{}), "resident as written")
	require.False(t, guardSuppliedByContext(whole, and(and(A, B), D), rungOpts{}), "a different conjunction")

	parts := core.MakeProp(parse("Q"), A, B, C)
	require.True(t, guardSuppliedByContext(parts, and(and(A, B), C), rungOpts{}), "resident conjunct by conjunct")
	require.False(t, guardSuppliedByContext(parts, and(A, D), rungOpts{}), "one conjunct missing")

	mixed := core.MakeProp(parse("Q"), and(A, B), C)
	require.True(t, guardSuppliedByContext(mixed, and(and(A, B), C), rungOpts{}), "one side as written, the other a conjunct")
}

// A witnessed cite that falls to its clause form says which guard the
// context was missing: the first part of the instance's guards that is
// neither resident nor a conjunction of resident parts — named after
// the witnesses are in, reduced, so the author reads the fact to supply.
func TestUnsuppliedStatedGuard_NamesTheMissingPart(t *testing.T) {
	num := ext.NumType
	scope := &dsl.ParseScope{Vars: map[string]core.HolType{
		"P": core.MakeFun(num, core.TypeBool()),
		"R": core.MakeFun(num, core.MakeFun(num, core.TypeBool())),
		"a": num, "b": num,
	}}
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	stated := core.MakeProp(parse("∀x y:num. P(x) ∧ P(y) ⇒ R(x, y)"))
	a, b := ext.Var("a", num).Core(), ext.Var("b", num).Core()

	both := core.MakeProp(parse("R(a, b)"), parse("P(a) ∧ P(b)"))
	require.True(t, statedGuardsSupplied(both, stated, []core.Term{a, b}, rungOpts{}))
	require.Nil(t, unsuppliedStatedGuard(both, stated, []core.Term{a, b}, rungOpts{}))

	one := core.MakeProp(parse("R(a, b)"), parse("P(a)"))
	require.False(t, statedGuardsSupplied(one, stated, []core.Term{a, b}, rungOpts{}))
	missing := unsuppliedStatedGuard(one, stated, []core.Term{a, b}, rungOpts{})
	require.NotNil(t, missing)
	require.True(t, missing.AlphaEquals(parse("P(b)")), "got %s", ext.PrintTerm(missing))

	// A partial tuple declines the stated form for another reason.
	require.Nil(t, unsuppliedStatedGuard(one, stated, []core.Term{a}, rungOpts{}))
}

// When no candidate fires, the miss reported is the one the author can
// act on. A two-carrier law read from the goal alone is a coin toss:
// the goal's own instances give the pinned binder the wrong type and
// miss on that, while the instance the pin completes (h at k's type)
// misses on the plan — here the law's guard, which the context lacks.
// The loop tries the pinned instance first; reporting the LAST miss
// would print the coin toss and tell the author to pin a term that is
// already pinned. (The corpus case: `Where(monoidal.Homomorphic, "h",
// pairWithY)` with `monoidal_op(vadd)` not resident.)
func TestApplyStatedHead_ReportsThePinnedInstancesMiss(t *testing.T) {
	lemma := parseFor(t, "∀op:(B → B → B). (∀b:B. op(b, b) = b) ⇒ ∀h:(B → C). ∀s z:A. ∀p:bool. COND(p, s, z) = s ⇒ h = h")
	goal := parseFor(t, "k:((num → X) → X), m:(X → num), t:num, w:num, q:bool ⊢ COND(q, t, w) = t ⇒ k = k")
	// The antecedent resident, the guard not: strip the implication so
	// COND(q, t, w) = t is a hypothesis and k = k the conclusion.
	root := CreateGoalStack(goal)
	require.True(t, root.runStep(StripImp()))
	leaf := root.Children()[0]
	require.Equal(t, 1, leaf.Goal.NumHyps())

	var k core.Term
	for _, v := range goal.Conclusion().Frees(nil) {
		if string(v.Name()) == "k" {
			k = v
		}
	}
	require.NotNil(t, k)
	hd := applyHead{stated: lemma, describe: "the law", named: []NamedWitness{{Binder: "h", Witness: k}}}
	var claims []*GoalStackNode
	ok, miss := applyStatedHead(root, &claims, leaf, hd, rungOpts{depth: antecedentApplies})
	require.False(t, ok)
	require.NotContains(t, miss, "at the type instance the goal offered",
		"the coin toss must not be what is reported: %s", miss)
	require.Contains(t, miss, "apply-close:", "a miss is reported: %q", miss)
	t.Log(miss)
}

// An ⇔-shaped conclusion is read as either of its Horn clauses: the
// goal matched against one side, the other side pinned from and
// discharged by the context — so a cancellation law closes `b = c`
// with `a + b = a + c` resident, and the reverse direction closes the
// sum with the equation resident. What stays open is the head's own
// claim obligation (the dependency's certificate closes it in a By).
// Without the other side in the context the reading is a named miss,
// not a refutation.
func TestApplyStatedHead_ReadsAnIffAsItsHornClauses(t *testing.T) {
	lemma := core.TestThm(parseFor(t, "∀x y z:num. x + y = x + z ⇔ y = z").Conclusion())
	try := func(goalText string) (bool, string, []*GoalStackNode) {
		t.Helper()
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the cancellation law"}, rungOpts{depth: antecedentApplies})
		return ok, miss, sec.UnsolvedLeaves()
	}
	onlyTheClaim := func(open []*GoalStackNode) bool {
		for _, l := range open {
			if l.Goal.NumHyps() != 0 || !l.Goal.Conclusion().AlphaEquals(lemma.Conclusion()) {
				return false
			}
		}
		return true
	}
	ok, miss, open := try("a:num, b:num, c:num ⊢ a + b = a + c ⇒ b = c")
	require.True(t, ok, "L ⇒ R: %s", miss)
	require.True(t, onlyTheClaim(open), "L ⇒ R left %d leaf(ves) open", len(open))

	ok, miss, open = try("a:num, b:num, c:num ⊢ b = c ⇒ a + b = a + c")
	require.True(t, ok, "R ⇒ L: %s", miss)
	require.True(t, onlyTheClaim(open), "R ⇒ L left %d leaf(ves) open", len(open))

	// The sum matches the ⇔'s left side with every binder pinned, and
	// the other side is not in the context: the named miss.
	ok, miss, _ = try("a:num, b:num, c:num, q:bool ⊢ q ⇒ a + b = a + c")
	require.False(t, ok)
	require.Contains(t, miss, "not in the context")
	// The equation matches the right side, and x is pinned by nothing.
	ok, miss, _ = try("a:num, b:num, c:num, q:bool ⊢ q ⇒ b = c")
	require.False(t, ok)
	require.Contains(t, miss, "pins every binder")
}

// An equation goal is matched against the head the other way round as
// well — `apply` up to the symmetry of =, finished by Symm: a law
// stating `x + 0 = x` closes `a = a + 0`, and the cancellation law's
// right side `y = z` closes `c = b` with `a + b = a + c` resident.
func TestApplyStatedHead_ReadsAnEquationGoalTheOtherWayRound(t *testing.T) {
	try := func(lemmaText, goalText string) (bool, string, *GoalStackNode, core.Prop) {
		t.Helper()
		lemma := core.TestThm(parseFor(t, lemmaText).Conclusion())
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the law"}, rungOpts{depth: antecedentApplies})
		return ok, miss, sec, lemma
	}
	onlyTheClaim := func(sec *GoalStackNode, lemma core.Prop) bool {
		for _, l := range sec.UnsolvedLeaves() {
			if l.Goal.NumHyps() != 0 || !l.Goal.Conclusion().AlphaEquals(lemma.Conclusion()) {
				return false
			}
		}
		return true
	}
	ok, miss, sec, lemma := try("∀x:num. x + 0 = x", "a:num, q:bool ⊢ q ⇒ a = a + 0")
	require.True(t, ok, "equation, flipped: %s", miss)
	require.True(t, onlyTheClaim(sec, lemma))

	ok, miss, sec, lemma = try("∀x y z:num. x + y = x + z ⇔ y = z", "a:num, b:num, c:num ⊢ a + b = a + c ⇒ c = b")
	require.True(t, ok, "iff side, flipped: %s", miss)
	require.True(t, onlyTheClaim(sec, lemma))
}

// An ⇔ whose one side is itself a law — a definition read as
// membership, `u(0) ⇔ ∀x. u(x) ⇒ ∃d. x < d ∧ u(d)` — is read THROUGH
// that side: the goal is an instance of the side's conclusion, the
// ⇔'s other side and the side's own antecedent are in the context.
// The head is grounded at its binders, the ⇔ eliminated toward the
// side, and the side applied at the point. Whole, the side is the old
// Horn reading; with nothing to supply the other side, or the point's
// own antecedent, the reading is a named miss.
func TestApplyStatedHead_ReadsThroughAnIffSide(t *testing.T) {
	const law = "∀u:(num → bool). u(0) ⇔ ∀x:num. u(x) ⇒ ∃d:num. x < d ∧ u(d)"
	lemma := core.TestThm(parseFor(t, law).Conclusion())
	try := func(goalText string, strips int, head applyHead) (bool, string, []*GoalStackNode) {
		t.Helper()
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		for range strips {
			sec.Do(StripImp())
		}
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], head, rungOpts{depth: antecedentApplies})
		return ok, miss, sec.UnsolvedLeaves()
	}
	onlyTheClaim := func(open []*GoalStackNode) bool {
		for _, l := range open {
			if l.Goal.NumHyps() != 0 || !l.Goal.Conclusion().AlphaEquals(lemma.Conclusion()) {
				return false
			}
		}
		return true
	}
	bare := applyHead{stated: lemma, describe: "the law"}

	const atAPoint = "v:(num → bool), c:num ⊢ v(0) ⇒ v(c) ⇒ ∃d:num. c < d ∧ v(d)"
	ok, miss, open := try(atAPoint, 2, bare)
	require.True(t, ok, "through the side, at a point: %s", miss)
	require.True(t, onlyTheClaim(open), "left %d leaf(ves) open", len(open))

	// The same head pinned at its tuple, as a witnessed premise offers it.
	v := parseFor(t, "v:(num → bool) ⊢ v(0)").Conclusion().(core.AppliedTerm).Fun()
	ok, miss, open = try(atAPoint, 2, applyHead{stated: lemma, describe: "the law at v", tuple: []core.Term{v}})
	require.True(t, ok, "through the side, the head pinned at its tuple: %s", miss)
	require.True(t, onlyTheClaim(open))

	ok, miss, open = try("v:(num → bool) ⊢ v(0) ⇒ ∀x:num. v(x) ⇒ ∃d:num. x < d ∧ v(d)", 1, bare)
	require.True(t, ok, "the side whole: %s", miss)
	require.True(t, onlyTheClaim(open))

	ok, miss, _ = try("v:(num → bool), c:num, q:bool ⊢ q ⇒ v(c) ⇒ ∃d:num. c < d ∧ v(d)", 2, bare)
	require.False(t, ok, "the ⇔'s other side is not in the context")
	require.Contains(t, miss, "the other side")

	ok, miss, _ = try("v:(num → bool), c:num, q:bool ⊢ v(0) ⇒ q ⇒ ∃d:num. c < d ∧ v(d)", 2, bare)
	require.False(t, ok, "the point's own antecedent is not in the context")
	require.Contains(t, miss, "not in the context")
}

// The side read through may be a CONJUNCTION one of whose conjuncts
// is the law — a metric topology read as membership, `u ∈ T ⇔ u ⊆ M ∧
// ∀x. x ∈ u ⇒ ∃r. …` — and the goal an instance of that conjunct's
// conclusion: the ⇔ is eliminated toward the side, the side split until
// the conjunct is resident, and the conjunct applied at the point. With
// nothing to supply the other side the reading is the same named miss.
func TestApplyStatedHead_ReadsThroughAConjunctOfAnIffSide(t *testing.T) {
	const law = "∀u:(num → bool). u(0) ⇔ u(1) ∧ ∀x:num. u(x) ⇒ ∃d:num. x < d ∧ u(d)"
	lemma := core.TestThm(parseFor(t, law).Conclusion())
	try := func(goalText string) (bool, string, []*GoalStackNode) {
		t.Helper()
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		sec.Do(StripImp())
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the law"}, rungOpts{depth: antecedentApplies})
		return ok, miss, sec.UnsolvedLeaves()
	}

	ok, miss, open := try("v:(num → bool), c:num ⊢ v(0) ⇒ v(c) ⇒ ∃d:num. c < d ∧ v(d)")
	require.True(t, ok, "through the side's second conjunct, at a point: %s", miss)
	for _, l := range open {
		require.Equal(t, 0, l.Goal.NumHyps(), "only the law's own claim is left open")
		require.True(t, l.Goal.Conclusion().AlphaEquals(lemma.Conclusion()))
	}

	ok, miss, _ = try("v:(num → bool), c:num, q:bool ⊢ q ⇒ v(c) ⇒ ∃d:num. c < d ∧ v(d)")
	require.False(t, ok, "the ⇔'s other side is not in the context")
	require.Contains(t, miss, "the other side")
}

// The same reading at a TYPE VARIABLE — the law over a letter A and the
// goal over the same letter, as a chapter's own laws meet its goals.
func TestApplyStatedHead_ReadsThroughAConjunctOfAnIffSideAtALetter(t *testing.T) {
	const law = "∀u:(A → bool). ∀a:A. u(a) ⇔ u(a) ∧ ∀x:A. u(x) ⇒ ∃d:A. u(d)"
	lemma := core.TestThm(parseFor(t, law).Conclusion())
	for _, goalText := range []string{
		"v:(A → bool), a:A, c:A ⊢ v(a) ⇒ v(c) ⇒ ∃d:A. v(d)",
		"v:(B → bool), a:B, c:B ⊢ v(a) ⇒ v(c) ⇒ ∃d:B. v(d)",
	} {
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		sec.Do(StripImp())
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the law"}, rungOpts{depth: antecedentApplies})
		require.True(t, ok, "%s: through the side's second conjunct at a point: %s", goalText, miss)
	}
}

// The plain side (no conjunction) read through at a type variable — the
// control for the letter test above.
func TestApplyStatedHead_ReadsThroughAnIffSideAtALetter(t *testing.T) {
	const law = "∀u:(A → bool). ∀a:A. u(a) ⇔ ∀x:A. u(x) ⇒ ∃d:A. u(d)"
	lemma := core.TestThm(parseFor(t, law).Conclusion())
	for _, goalText := range []string{
		"v:(A → bool), a:A, c:A ⊢ v(a) ⇒ v(c) ⇒ ∃d:A. v(d)",
		"v:(B → bool), a:B, c:B ⊢ v(a) ⇒ v(c) ⇒ ∃d:B. v(d)",
		"v:(num → bool), a:num, c:num ⊢ v(a) ⇒ v(c) ⇒ ∃d:num. v(d)",
	} {
		sec := NewScript(makeStepTestEnv()).Section(parseFor(t, goalText))
		sec.Do(StripImp())
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		var claims []*GoalStackNode
		ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the law"}, rungOpts{depth: antecedentApplies})
		require.True(t, ok, "%s: through the side at a point: %s", goalText, miss)
	}
}

// A law grounded at its witnesses is a fact with no binder left; where
// it is an ⇔ it still reads as its two Horn clauses, and through a side
// that is a law.
func TestPlanApply_ReadsAGroundIff(t *testing.T) {
	sec := NewScript(makeStepTestEnv()).Section(parseFor(t,
		"v:(num → bool), c:num ⊢ (v(0) ⇔ ∀x:num. v(x) ⇒ ∃d:num. x < d ∧ v(d)) ⇒ v(0) ⇒ v(c) ⇒ ∃d:num. c < d ∧ v(d)"))
	sec.Do(StripImp())
	sec.Do(StripImp())
	sec.Do(StripImp())
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	var claims []*GoalStackNode
	closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
	require.True(t, closed, "the resident ground ⇔, read through its side: %s", miss)
	require.True(t, sec.Proved())
}

// lawScope is the vocabulary of the tests on an antecedent that is
// itself a law: two predicates of an index, a set, a function.
func lawScope() *dsl.ParseScope {
	num := ext.NumType
	return &dsl.ParseScope{Vars: map[string]core.HolType{
		"P": core.MakeFun(num, core.TypeBool()),
		"K": core.MakeFun(num, core.TypeBool()),
		"H": core.MakeFun(num, core.TypeBool()),
		"s": core.MakeFun(num, core.TypeBool()),
		"f": core.MakeFun(num, num),
		"F": core.MakeFun(core.MakeFun(num, num), core.MakeFun(num, core.TypeBool())),
		"G": core.MakeFun(core.MakeFun(num, core.TypeBool()), core.TypeBool()),
		"Q": core.TypeBool(),
		"S": core.TypeBool(),
	}}
}

func lawTerm(t *testing.T, text string) core.Term {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, lawScope())
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// An antecedent that is itself a law is supplied the way a goal of its
// shape is closed: opened, and a resident hypothesis applied to what is
// left. A fact about every index supplies the law's reading of it from
// an index on; an injectivity over the whole type supplies the
// injectivity on a set; a guarded fact supplies a law that assumes its
// guard. What the context would have to search for is not supplied,
// and the apply inside reads its own antecedents with none: a
// hypothesis whose antecedent wants an apply of its own does not close
// it.
func TestStructurallyResident_AntecedentIsALaw(t *testing.T) {
	parse := func(text string) core.Term { return lawTerm(t, text) }
	everywhere := core.MakeProp(parse("Q"), parse("∀N:num. P(N)"), parse("S"))

	fromZero := parse("∀n:num. 0 ≤ n ⇒ P(n)")
	require.True(t, structurallyResident(everywhere, fromZero, rungOpts{}), "every index supplies every index from 0 on")
	require.False(t, residentByAssumption(everywhere, fromZero, rungOpts{}), "by assumption alone it is not in the context")
	require.True(t, structurallyResident(everywhere, ext.WrapTerm(fromZero).And(ext.WrapTerm(parse("S"))).Core(), rungOpts{}),
		"a conjunction of a law and a resident fact")
	require.True(t, guardSuppliedByContext(everywhere, fromZero, rungOpts{}), "the guard test reads the same way")
	require.False(t, structurallyResident(everywhere, parse("∀n:num. 0 ≤ n ⇒ K(n)"), rungOpts{}), "a law about another predicate")
	require.False(t, structurallyResident(everywhere, parse("P(0) ∧ K(0)"), rungOpts{}), "a part that is no law and not resident")

	injective := core.MakeProp(parse("Q"), parse("∀x y:num. f(x) = f(y) ⇒ x = y"))
	require.True(t, structurallyResident(injective, parse("∀x y:num. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y"), rungOpts{}),
		"injective everywhere, so injective on s: the resident law applies with its antecedent among those assumed")

	guarded := core.MakeProp(parse("Q"), parse("∀n:num. H(n) ⇒ P(n)"))
	require.True(t, structurallyResident(guarded, parse("∀n:num. H(n) ∧ K(n) ⇒ P(n)"), rungOpts{}), "the law assumes more than the fact asks")
	require.False(t, structurallyResident(guarded, parse("∀n:num. K(n) ⇒ P(n)"), rungOpts{}), "the fact's guard is not among those assumed")

	nested := core.MakeProp(parse("Q"), parse("∀n:num. (∀m:num. H(m) ⇒ K(m)) ⇒ P(n)"), parse("∀m:num. K(m)"))
	require.False(t, structurallyResident(nested, fromZero, rungOpts{}), "two applies deep: the hypothesis's own antecedent wants one")
}

// An antecedent is closed as a goal is, one apply deep, whatever its
// shape: an instance of a resident fact, the consequent of a resident
// law whose antecedent the context holds, a conjunction conjunct by
// conjunct, a law whose conclusion is a conjunction. A conjunct of a
// resident conjunction is held by assumption already: the datum
// gathered into one fact holds each clause, on the spine as inside a
// close. Two applies away is the closer's.
func TestStructurallyResident_OneApplyDeep(t *testing.T) {
	parse := func(text string) core.Term { return lawTerm(t, text) }
	context := func(hyps ...string) core.Prop {
		terms := make([]core.Term, len(hyps))
		for i, h := range hyps {
			terms[i] = parse(h)
		}
		return core.MakeProp(parse("Q"), terms...)
	}
	supplied := func(ctx core.Prop, text, why string) {
		t.Helper()
		require.True(t, structurallyResident(ctx, parse(text), rungOpts{}), why)
		require.True(t, guardSuppliedByContext(ctx, parse(text), rungOpts{}), "the guard test reads the same way: "+why)
		require.False(t, residentByAssumption(ctx, parse(text), rungOpts{}), "by assumption alone it is not held: "+why)
	}

	supplied(context("∀N:num. P(N)"), "P(0)", "an instance of a resident fact")
	supplied(context("∀n:num. H(n) ⇒ K(n)", "H(0)"), "K(0)", "the consequent of a law whose antecedent is held")
	supplied(context("∀N:num. P(N)", "S"), "P(0) ∧ S", "a conjunction, one side by an apply and one held")
	supplied(context("∀N:num. P(N) ∧ K(N)"), "∀n:num. 0 ≤ n ⇒ P(n) ∧ K(n)", "a law whose conclusion is a conjunction")
	supplied(context("∀N:num. P(N)", "∀N:num. K(N)"), "∀n:num. 0 ≤ n ⇒ P(n) ∧ K(n)", "the same from the two facts apart")

	conjunct := context("P(0) ∧ K(0)")
	require.True(t, structurallyResident(conjunct, parse("K(0)"), rungOpts{}), "a conjunct of a resident conjunction")
	require.True(t, guardSuppliedByContext(conjunct, parse("K(0)"), rungOpts{}), "the guard test reads it too")
	require.True(t, residentByAssumption(conjunct, parse("K(0)"), rungOpts{}), "and so does the reading by assumption: one resident fact holds each of its clauses")

	far := context("∀n:num. H(n) ⇒ K(n)", "∀n:num. P(n) ⇒ H(n)", "P(0)")
	require.False(t, structurallyResident(far, parse("K(0)"), rungOpts{}), "two applies away")
	require.False(t, structurallyResident(context("∀N:num. P(N)"), parse("K(0)"), rungOpts{}), "nothing the context holds yields it")
}

// An instance taken at a λ-witness states the law's pieces as redexes;
// the law is read in its reduced statement, which is the same fact.
func TestGuardSuppliedByContext_LawAtALambdaWitness(t *testing.T) {
	parse := func(text string) core.Term { return lawTerm(t, text) }
	num := ext.NumType
	stated := core.MakeProp(parse("∀g:(num → num). ∀N:num. (∀n:num. N ≤ n ⇒ F(g, n)) ⇒ F(g, N)"))
	atZero := parse("F(λk:num. f(k + 1), 0)").(core.AppliedTerm)
	shifted, zero := atZero.Fun().(core.AppliedTerm).Arg(), atZero.Arg()
	require.True(t, zero.Type().Equals(num))

	context := core.MakeProp(parse("Q"), parse("∀k:num. F(λk:num. f(k + 1), k)"))
	require.True(t, statedGuardsSupplied(context, stated, []core.Term{shifted, zero}, rungOpts{}))
	require.Nil(t, unsuppliedStatedGuard(context, stated, []core.Term{shifted, zero}, rungOpts{}))

	without := core.MakeProp(parse("Q"), parse("S"))
	require.False(t, statedGuardsSupplied(without, stated, []core.Term{shifted, zero}, rungOpts{}))
	require.NotNil(t, unsuppliedStatedGuard(without, stated, []core.Term{shifted, zero}, rungOpts{}))
}

// The rung commits what it validated: the law is asserted and proved
// by the apply that closes it, the head's antecedent is then resident,
// and the leaf closes with nothing left open. The law may be closed by
// the head itself, so it is made resident before the head is grounded.
func TestApplyClose_AntecedentIsALaw(t *testing.T) {
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, lawScope())
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}

	closed, miss, sec := closes("(∀N:num. P(N)) ⇒ S ⇒ ((∀n:num. 0 ≤ n ⇒ P(n)) ∧ S ⇒ Q) ⇒ Q", 3)
	require.True(t, closed, "a fact about every index, a law that reads it from 0 on: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("(∀x y:num. f(x) = f(y) ⇒ x = y) ⇒ "+
		"(∀u:(num → bool). (∀x y:num. x ∈ u ∧ y ∈ u ∧ f(x) = f(y) ⇒ x = y) ⇒ K(f(0))) ⇒ K(f(0))", 2)
	require.False(t, closed, "the set is pinned by nothing: %s", miss)

	closed, miss, sec = closes("(∀x y:num. f(x) = f(y) ⇒ x = y) ⇒ "+
		"((∀x y:num. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y) ⇒ Q) ⇒ Q", 2)
	require.True(t, closed, "injective everywhere, a law that asks it on s: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, _ = closes("(∀N:num. K(N)) ⇒ S ⇒ ((∀n:num. 0 ≤ n ⇒ P(n)) ∧ S ⇒ Q) ⇒ Q", 3)
	require.False(t, closed, "the context holds no fact the law follows from")
	require.Contains(t, miss, "not in the context")

	// A chain of two: the head's antecedent is the consequent of a law
	// whose own antecedent is held.
	closed, miss, sec = closes("(∀n:num. H(n) ⇒ K(n)) ⇒ H(0) ⇒ (K(0) ⇒ Q) ⇒ Q", 3)
	require.True(t, closed, "two applies: %s", miss)
	require.True(t, sec.Proved())

	// A chain of three is the closer's.
	closed, _, _ = closes("(∀n:num. H(n) ⇒ K(n)) ⇒ (∀n:num. P(n) ⇒ H(n)) ⇒ P(0) ⇒ (K(0) ⇒ Q) ⇒ Q", 4)
	require.False(t, closed, "three applies")

	// The head is pinned at a λ and its antecedent is a law that
	// concludes a conjunction: the rung reads the instance reduced, and
	// the fact about every index supplies it conjunct by conjunct.
	closed, miss, sec = closes("(∀N:num. P(N + 1) ∧ K(N)) ⇒ "+
		"(∀A:(num → bool). (∀n:num. 0 ≤ n ⇒ A(n) ∧ K(n)) ⇒ G(A)) ⇒ G(λm:num. P(m + 1))", 2)
	require.True(t, closed, "a conjunctive law at a λ-witness: %s", miss)
	require.True(t, sec.Proved())
}

// Inside a By, a grounded premise whose guard is a law the context
// closes is brought down to its consequent, as one whose guard is
// resident is — and the law stated for the modus ponens is gone again,
// so the closer's leaf holds what the author named and the consequent.
// On the spine the reading is closed: the fact a step names keeps the
// guard the context would have to prove.
func TestDischargeGuards_GuardIsALaw(t *testing.T) {
	grounded := func() (*GoalStackNode, *GoalStackNode, core.Term) {
		res := dsl.ParsePropTextInScope("(∀N:num. P(N)) ⇒ ((∀n:num. 0 ≤ n ⇒ P(n)) ⇒ K(0)) ⇒ Q", lawScope())
		require.Empty(t, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		sec.Do(StripImp())
		sec.Do(StripImp())
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		return sec, leaves[0], lawTerm(t, "(∀n:num. 0 ≤ n ⇒ P(n)) ⇒ K(0)")
	}
	guard := lawTerm(t, "∀n:num. 0 ≤ n ⇒ P(n)")

	sec, leaf, inst := grounded()
	after, named := dischargeGuards(leaf, inst, true, rungOpts{}, nil)
	require.True(t, named.AlphaEquals(lawTerm(t, "K(0)")), "the fact now names %s", ext.PrintTerm(named))
	require.True(t, after.Goal.AnyHyp(named.AlphaEquals), "and its consequent is in the context")
	require.False(t, after.Goal.AnyHyp(guard.AlphaEquals), "the law stated for the guard is cleared")
	require.Equal(t, 2, after.Goal.NumHyps(), "the fact about every index, and the consequent")
	open := sec.UnsolvedLeaves()
	require.Len(t, open, 1, "the law's own proof and the ¬guard branch are closed")
	require.True(t, open[0] == after)

	_, leaf, inst = grounded()
	after, named = dischargeGuards(leaf, inst, false, rungOpts{}, nil)
	require.True(t, named.AlphaEquals(inst), "on the spine the fact keeps its guard: %s", ext.PrintTerm(named))
	require.True(t, after == leaf)

	// The guard as an instance taken at a λ-witness states it — a redex
	// — while the context proves it reduced; with a conjunction for its
	// conclusion, a closer that normalizes reads the two as different
	// clause sets. The modus ponens does not normalize.
	for _, c := range []struct{ goal, inst, guard string }{
		{"(∀N:num. P(N) ∧ K(N)) ⇒ ((∀n:num. 0 ≤ n ⇒ (λm:num. P(m))(n) ∧ K(n)) ⇒ H(0)) ⇒ Q",
			"(∀n:num. 0 ≤ n ⇒ (λm:num. P(m))(n) ∧ K(n)) ⇒ H(0)",
			"∀n:num. 0 ≤ n ⇒ (λm:num. P(m))(n) ∧ K(n)"},
		{"(∀N:num. P(N) ∧ K(N)) ⇒ ((∀n:num. 0 ≤ n ⇒ P(n) ∧ K(n)) ⇒ H(0)) ⇒ Q",
			"(∀n:num. 0 ≤ n ⇒ P(n) ∧ K(n)) ⇒ H(0)",
			"∀n:num. 0 ≤ n ⇒ P(n) ∧ K(n)"},
		{"f(0) = 1 ⇒ P(1) ⇒ ((λm:num. P(m))(1) ∧ 1 = f(0) ⇒ H(0)) ⇒ Q",
			"(λm:num. P(m))(1) ∧ 1 = f(0) ⇒ H(0)",
			"(λm:num. P(m))(1) ∧ 1 = f(0)"},
	} {
		res := dsl.ParsePropTextInScope(c.goal, lawScope())
		require.Empty(t, res.Errors, "%s: %v", c.goal, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for sec.UnsolvedLeaves()[0].runStep(StripImp()) {
		}
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		hyps := leaves[0].Goal.NumHyps()
		inst := lawTerm(t, c.inst)
		require.True(t, leaves[0].Goal.AnyHyp(inst.AlphaEquals), "%s: the instance is stated as written", c.goal)
		after, named := dischargeGuards(leaves[0], inst, true, rungOpts{}, nil)
		require.True(t, named.AlphaEquals(lawTerm(t, "H(0)")), "%s: the fact now names %s", c.goal, ext.PrintTerm(named))
		require.Equal(t, hyps, after.Goal.NumHyps(), "%s: the consequent for the instance, nothing stated left behind", c.goal)
		require.False(t, after.Goal.AnyHyp(lawTerm(t, c.guard).AlphaEquals), "%s: the guard stated for the modus ponens is cleared", c.goal)
		open := sec.UnsolvedLeaves()
		require.Len(t, open, 1, "%s: the guard's proof and the ¬guard branch are closed", c.goal)
		require.True(t, open[0] == after)
	}

	// A guard that is an instance of a resident fact, and one that is
	// the consequent of a resident law: supplied in a By, kept on the
	// spine.
	for _, goalText := range []string{
		"(∀N:num. P(N)) ⇒ (P(0) ⇒ K(0)) ⇒ Q",
		"(∀n:num. H(n) ⇒ P(n)) ⇒ H(0) ⇒ (P(0) ⇒ K(0)) ⇒ Q",
	} {
		open := func() (*GoalStackNode, core.Term) {
			res := dsl.ParsePropTextInScope(goalText, lawScope())
			require.Empty(t, res.Errors)
			sec := NewScript(makeStepTestEnv()).Section(res.Prop)
			for sec.UnsolvedLeaves()[0].runStep(StripImp()) {
			}
			leaves := sec.UnsolvedLeaves()
			require.Len(t, leaves, 1)
			return leaves[0], lawTerm(t, "P(0) ⇒ K(0)")
		}
		leaf, inst := open()
		hyps := leaf.Goal.NumHyps()
		after, named := dischargeGuards(leaf, inst, true, rungOpts{}, nil)
		require.True(t, named.AlphaEquals(lawTerm(t, "K(0)")), "%s: the fact now names %s", goalText, ext.PrintTerm(named))
		require.Equal(t, hyps, after.Goal.NumHyps(), "%s: the consequent for the instance, nothing stated left behind", goalText)
		require.False(t, after.Goal.AnyHyp(lawTerm(t, "P(0)").AlphaEquals))

		leaf, inst = open()
		_, named = dischargeGuards(leaf, inst, false, rungOpts{}, nil)
		require.True(t, named.AlphaEquals(inst), "%s: on the spine the fact keeps its guard", goalText)
	}
}

// A guard is discharged into a consequent the context already holds:
// the same closure law read twice at one point in a By — a member's
// evidence carried by two cites — has its consequent resident the
// second time, and the modus ponens then has one branch, the
// kernel folding the ¬guard branch into it. The fact names the
// consequent, the implication is consumed, nothing is left behind, and
// the one leaf is the one the spine continues on.
func TestDischargeGuards_ConsequentAlreadyResident(t *testing.T) {
	for _, open := range []bool{true, false} {
		res := dsl.ParsePropTextInScope("P(f(0)) ⇒ K(f(0)) ⇒ (P(f(0)) ⇒ K(f(0))) ⇒ Q", lawScope())
		require.Empty(t, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for sec.UnsolvedLeaves()[0].runStep(StripImp()) {
		}
		leaves := sec.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		inst := lawTerm(t, "P(f(0)) ⇒ K(f(0))")
		require.True(t, leaves[0].Goal.AnyHyp(inst.AlphaEquals))
		after, named := dischargeGuards(leaves[0], inst, open, rungOpts{}, nil)
		require.True(t, named.AlphaEquals(lawTerm(t, "K(f(0))")), "open=%v: the fact now names %s", open, ext.PrintTerm(named))
		require.False(t, after.Goal.AnyHyp(inst.AlphaEquals), "open=%v: the implication is consumed", open)
		require.Equal(t, 2, after.Goal.NumHyps(), "open=%v: the guard and the consequent, nothing stated left behind", open)
		remaining := sec.UnsolvedLeaves()
		require.Len(t, remaining, 1, "open=%v: no ¬guard branch is left open", open)
		require.True(t, remaining[0] == after)
	}
}

// The guard's negation resident beside the guard: the kernel folds the
// consequent branch into the ¬guard branch, which closes on the two —
// and the leaf with it.
func TestDischargeGuards_GuardNegationResident(t *testing.T) {
	res := dsl.ParsePropTextInScope("P(f(0)) ⇒ ¬P(f(0)) ⇒ (P(f(0)) ⇒ K(f(0))) ⇒ Q", lawScope())
	require.Empty(t, res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	for sec.UnsolvedLeaves()[0].runStep(StripImp()) {
	}
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	inst := lawTerm(t, "P(f(0)) ⇒ K(f(0))")
	after, named := dischargeGuards(leaves[0], inst, true, rungOpts{}, nil)
	require.True(t, named.AlphaEquals(lawTerm(t, "K(f(0))")), "the fact now names %s", ext.PrintTerm(named))
	require.True(t, after.Proved(), "the one branch closed on the guard and its negation")
	require.True(t, sec.Proved())
}

// A law that concludes a conjunction is a law for each conjunct: the
// conditioning stage splits a conjunctive goal, so the goal such a law
// meets is one conjunct of what it concludes. The instance is brought
// down whole and split where it stands.
func TestApplyClose_HeadConcludesAConjunction(t *testing.T) {
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, lawScope())
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}
	for _, conjunct := range []string{"P(0)", "K(0)", "S"} {
		closed, miss, sec := closes("(∀n:num. H(n) ⇒ (P(n) ∧ K(n)) ∧ S) ⇒ H(0) ⇒ "+conjunct, 2)
		require.True(t, closed, "%s: %s", conjunct, miss)
		require.True(t, sec.Proved(), conjunct)
	}
	closed, _, _ := closes("(∀n:num. H(n) ⇒ P(n) ∧ K(n)) ⇒ H(0) ⇒ K(1)", 2)
	require.False(t, closed, "the conjunct at another point: the antecedent there is not held")

	// The same law as a NAMED premise: its stated form is installed on
	// the fire and the conjunct read off the instance.
	lemma := core.TestThm(parseForLaw(t, "∀n:num. H(n) ⇒ P(n) ∧ K(n)"))
	res := dsl.ParsePropTextInScope("H(0) ⇒ K(0)", lawScope())
	require.Empty(t, res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	sec.Do(StripImp())
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	var claims []*GoalStackNode
	ok, miss := applyStatedHead(sec, &claims, leaves[0], applyHead{stated: lemma, describe: "the law"}, rungOpts{depth: antecedentApplies})
	require.True(t, ok, "a named premise that concludes a conjunction: %s", miss)
	for _, l := range sec.UnsolvedLeaves() {
		require.True(t, l.Goal.NumHyps() == 0 && l.Goal.Conclusion().AlphaEquals(lemma.Conclusion()),
			"only the premise's own claim is left open")
	}
}

// parseForLaw parses a closed statement over lawScope's predicates,
// ∀-closed over them as a named premise's statement is.
func parseForLaw(t *testing.T, text string) core.Term {
	t.Helper()
	return lawTerm(t, text)
}

// TestApplyClose_ReflexiveAntecedent: an antecedent that is an equation
// between one term and itself is closed by reflexivity, as the same
// equation is closed as a goal — the one closing procedure (closeGoal).
// A law about a map read at an embedding asks `f(zero) = zero'`, which
// there is `f(0) = f(0)`.
func TestApplyClose_ReflexiveAntecedent(t *testing.T) {
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, lawScope())
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}
	closed, miss, sec := closes("(∀g:(num → num). g(0) = g(0) ⇒ F(g, 1)) ⇒ F(f, 1)", 1)
	require.True(t, closed, "a reflexive antecedent: %s", miss)
	require.True(t, sec.Proved())

	closed, miss, sec = closes("S ⇒ (∀g:(num → num). g(0) = g(0) ∧ S ⇒ F(g, 1)) ⇒ F(f, 1)", 2)
	require.True(t, closed, "a reflexive conjunct beside a resident one: %s", miss)
	require.True(t, sec.Proved())

	closed, _, _ = closes("(∀g:(num → num). g(0) = g(1) ⇒ F(g, 1)) ⇒ F(f, 1)", 1)
	require.False(t, closed, "an equation between two terms is not reflexivity")

	// Transitivity read at its middle point equal to its end asks for the
	// goal itself beside a reflexive piece; the goal is not supplied to
	// itself, and the head that does prove it is applied instead.
	closed, miss, sec = closes("(∀g:(num → num). g(0) = g(1) ∧ g(1) = g(1) ⇒ g(0) = g(1)) ⇒ S ⇒ "+
		"(S ⇒ f(0) = f(1)) ⇒ f(0) = f(1)", 3)
	require.True(t, closed, "a head asking for the goal itself is passed over: %s", miss)
	require.True(t, sec.Proved())

	// The same head before a resident goal: the goal is closed by
	// assumption, and no head is read. A strip closes a resident goal on
	// the spot, so the sequent is built with its hypotheses in place —
	// the conditioning stage leaves such a leaf.
	res := dsl.ParsePropTextInScope("(∀g:(num → num). g(0) = g(1) ∧ g(1) = g(1) ⇒ g(0) = g(1)) ⇒ f(0) = f(1)", lawScope())
	require.Empty(t, res.Errors)
	head, resident, ok := ext.MatchesIMPLY(res.Prop.Conclusion())
	require.True(t, ok)
	sec = NewScript(makeStepTestEnv()).Section(prop.MakeProp(resident, head, resident))
	var claims []*GoalStackNode
	closed, miss = applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
	require.True(t, closed, "a resident goal behind an applicable head: %s", miss)
	require.True(t, sec.Proved())
}
