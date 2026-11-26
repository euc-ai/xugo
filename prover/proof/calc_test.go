// calc_test.go — the Calc chain surfaces (calc.go).
//

package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// =======================================================================
// CalcOrder — the leg-tag fold
// =======================================================================

// The fold is pure over the leg TAGS — which lifts fire, which
// transitivity chains, what the running relation becomes — so it is
// testable without touching the kernel. These cases pin the table in
// CalcOrder's doc comment.

func legTags(kinds ...calcRelKind) []CalcLeg {
	legs := make([]CalcLeg, len(kinds))
	for i, k := range kinds {
		legs[i] = CalcLeg{to: nil, label: "leg", rel: k}
	}
	return legs
}

func TestCalcOrderPlanCompositions(t *testing.T) {
	for _, tc := range []struct {
		name              string
		tags              []calcRelKind
		wantLiftChain     []bool
		wantLiftLink      []bool
		wantRel           []calcRelKind
		wantFinalRelation calcRelKind
	}{
		{
			// ≤ ∘ ≤ → ≤, no lift: the CalcRel v1 shape.
			name:          "all order legs never lift",
			tags:          []calcRelKind{relLe, relLe, relLe},
			wantLiftChain: []bool{false, false},
			wantLiftLink:  []bool{false, false},
			wantRel:       []calcRelKind{relLe, relLe},
		},
		{
			// ≈ ∘ ≈ → ≈, no lift: an equivalence chain stays ≈.
			name:          "all equivalence legs stay equivalence",
			tags:          []calcRelKind{relEq, relEq, relEq},
			wantLiftChain: []bool{false, false},
			wantLiftLink:  []bool{false, false},
			wantRel:       []calcRelKind{relEq, relEq},
		},
		{
			// The pilot's shape: ≤ then ≈ then ≈ — each ≈ LINK is lifted,
			// the chain is already ≤ so it never is.
			name:          "order first then equivalences lift the link",
			tags:          []calcRelKind{relLe, relEq, relEq},
			wantLiftChain: []bool{false, false},
			wantLiftLink:  []bool{true, true},
			wantRel:       []calcRelKind{relLe, relLe},
		},
		{
			// ≈ then ≤: the running CHAIN is the ≈ fact, so it is what
			// gets lifted; the link is already ≤.
			name:          "equivalence first then order lifts the chain",
			tags:          []calcRelKind{relEq, relLe},
			wantLiftChain: []bool{true},
			wantLiftLink:  []bool{false},
			wantRel:       []calcRelKind{relLe},
		},
		{
			// Once ≤, always ≤ — a later ≈ cannot demote the chain, and
			// the chain is lifted at most once (step 1 only).
			name:          "order is absorbing",
			tags:          []calcRelKind{relEq, relLe, relEq},
			wantLiftChain: []bool{true, false},
			wantLiftLink:  []bool{false, true},
			wantRel:       []calcRelKind{relLe, relLe},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			steps := calcOrderPlan(legTags(tc.tags...))
			if len(steps) != len(tc.tags)-1 {
				t.Fatalf("got %d steps, want %d (one per chaining leg)", len(steps), len(tc.tags)-1)
			}
			for i, st := range steps {
				if st.liftChain != tc.wantLiftChain[i] {
					t.Errorf("step %d liftChain = %v, want %v", i, st.liftChain, tc.wantLiftChain[i])
				}
				if st.liftLink != tc.wantLiftLink[i] {
					t.Errorf("step %d liftLink = %v, want %v", i, st.liftLink, tc.wantLiftLink[i])
				}
				if st.rel != tc.wantRel[i] {
					t.Errorf("step %d rel = %v, want %v", i, st.rel, tc.wantRel[i])
				}
			}
		})
	}
}

// mustPanic runs fn and returns the panic text, failing if fn survived.
func mustPanic(t *testing.T, fn func()) string {
	t.Helper()
	var msg string
	func() {
		defer func() {
			if r := recover(); r != nil {
				msg, _ = r.(string)
			}
		}()
		fn()
		t.Fatal("expected a panic, got none")
	}()
	return msg
}

func TestCalcOrderRejectsUntaggedLeg(t *testing.T) {
	kit := CalcOrder{
		Le:      func(a, b Term) Prop { return nil },
		Eq:      func(a, b Term) Prop { return nil },
		LeTrans: depName("leTrans"),
		EqToLe:  depName("eqToLe"),
	}
	msg := mustPanic(t, func() {
		kit.Calc(nil, LeLeg(nil, "ordered"), Leg(nil, "untagged"))
	})
	// The leg has no target term either; the point is that the message
	// must be actionable, whichever check fires first.
	if !strings.Contains(msg, "untagged") && !strings.Contains(msg, "no target term") {
		t.Fatalf("panic did not name the offending leg: %q", msg)
	}
}

func TestSingleRelationChainsRejectTaggedLegs(t *testing.T) {
	kit := CalcRel{Rel: func(a, b Term) Prop { return nil }, Trans: depName("trans")}
	msg := mustPanic(t, func() {
		kit.Calc(nil, LeLeg(nil, "ordered"), LeLeg(nil, "ordered too"))
	})
	if !strings.Contains(msg, "CalcOrder") {
		t.Fatalf("panic should redirect a mixed chain to CalcOrder: %q", msg)
	}
}

func TestCalcOrderRequiresOnlyTheCertificatesItReaches(t *testing.T) {
	// An all-order chain must NOT demand Eq / EqTrans / EqToLe.
	allOrder := CalcOrder{
		Le:      func(a, b Term) Prop { return nil },
		LeTrans: depName("leTrans"),
	}
	allOrder.requireCerts(legTags(relLe, relLe))

	// Mixing ≈ in without a lift certificate must fail, naming EqToLe.
	msg := mustPanic(t, func() {
		allOrder.requireCerts(legTags(relLe, relEq))
	})
	if !strings.Contains(msg, "EqToLe") && !strings.Contains(msg, "Eq") {
		t.Fatalf("panic should name the missing certificate: %q", msg)
	}

	// A pure-≈ chain wants EqTrans, not LeTrans.
	pureEq := CalcOrder{Eq: func(a, b Term) Prop { return nil }}
	msg = mustPanic(t, func() {
		pureEq.requireCerts(legTags(relEq, relEq))
	})
	if !strings.Contains(msg, "EqTrans") {
		t.Fatalf("panic should name EqTrans: %q", msg)
	}
}

// =======================================================================
// CalcLeibniz — the ≈ side is the kernel's own =
// =======================================================================

// CalcLeibniz — the ≈ side is the kernel's own `=`.
//
// The fold TABLE is shared with .Calc (calcOrderPlan is untouched); what
// the Leibniz mode changes is which steps have to CITE a certificate.
// pureOrder is exactly that predicate, so these cases pin it against the
// same tag vectors this file's plan cases use. legTags and
// mustPanic come from there.

func TestPureOrderIsTheOnlyCitedComposition(t *testing.T) {
	for _, tc := range []struct {
		name string
		tags []calcRelKind
		want []bool // per chaining leg: does a Leibniz chain cite LeTrans?
	}{
		// ≤ ∘ ≤ is the one composition the kernel's `=` cannot discharge.
		{"order composes with order", []calcRelKind{relLe, relLe, relLe}, []bool{true, true}},
		// `=` ∘ `=` — transitive in the kernel, nothing cited.
		{"equality composes with equality", []calcRelKind{relEq, relEq, relEq}, []bool{false, false}},
		// ≤ then `=`: the link rewrites the running bound.
		{"order then equality rewrites the bound", []calcRelKind{relLe, relEq}, []bool{false}},
		// `=` then ≤: the running fact rewrites the link's left end.
		{"equality then order rewrites the link", []calcRelKind{relEq, relLe}, []bool{false}},
		// BoundsNotZero's shape: ≤ ≤ = — one cite, then none.
		{"two bounds then a refold", []calcRelKind{relLe, relLe, relEq}, []bool{true, false}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			steps := calcOrderPlan(legTags(tc.tags...))
			if len(steps) != len(tc.want) {
				t.Fatalf("got %d steps, want %d", len(steps), len(tc.want))
			}
			for i, st := range steps {
				if st.pureOrder() != tc.want[i] {
					t.Errorf("step %d pureOrder = %v, want %v", i, st.pureOrder(), tc.want[i])
				}
			}
		})
	}
}

func TestCalcLeibnizRejectsEquivalenceCertificates(t *testing.T) {
	base := func() CalcOrder {
		return CalcOrder{Le: func(a, b Term) Prop { return nil }, LeTrans: depName("leTrans")}
	}
	for _, tc := range []struct {
		field string
		set   func(*CalcOrder)
	}{
		{"Eq", func(k *CalcOrder) { k.Eq = func(a, b Term) Prop { return nil } }},
		{"EqTrans", func(k *CalcOrder) { k.EqTrans = depName("eqTrans") }},
		{"EqToLe", func(k *CalcOrder) { k.EqToLe = depName("eqToLe") }},
	} {
		t.Run(tc.field, func(t *testing.T) {
			kit := base()
			tc.set(&kit)
			msg := mustPanic(t, func() {
				kit.CalcLeibniz(nil, LeLeg(nil, "a"), EqLeg(nil, "b"))
			})
			if !strings.Contains(msg, tc.field) {
				t.Fatalf("panic should name the offending certificate %s: %q", tc.field, msg)
			}
			if !strings.Contains(msg, ".Calc") {
				t.Fatalf("panic should point a defined-relation chain at .Calc: %q", msg)
			}
		})
	}
}

func TestCalcLeibnizRequiresOnlyLeTransAndOnlyWhenReached(t *testing.T) {
	// ≤ then `=` never composes two order facts, so no certificate beyond
	// the Le builder is reached — LeTrans may stay nil.
	noTrans := CalcOrder{Le: func(a, b Term) Prop { return nil }}
	noTrans.requireLeibnizCerts(legTags(relLe, relEq))

	// An all-`=` chain reaches nothing at all: the empty kit is legal.
	CalcOrder{}.requireLeibnizCerts(legTags(relEq, relEq))

	// Two order legs do compose, and that wants LeTrans.
	msg := mustPanic(t, func() {
		noTrans.requireLeibnizCerts(legTags(relLe, relLe))
	})
	if !strings.Contains(msg, "LeTrans") {
		t.Fatalf("panic should name LeTrans: %q", msg)
	}

	// An order leg still wants the Le builder.
	msg = mustPanic(t, func() {
		CalcOrder{LeTrans: depName("leTrans")}.requireLeibnizCerts(legTags(relLe, relLe))
	})
	if !strings.Contains(msg, "Le") {
		t.Fatalf("panic should name Le: %q", msg)
	}
}

func TestCalcLeibnizRejectsUntaggedLeg(t *testing.T) {
	kit := CalcOrder{Le: func(a, b Term) Prop { return nil }, LeTrans: depName("leTrans")}
	msg := mustPanic(t, func() {
		kit.CalcLeibniz(nil, LeLeg(nil, "ordered"), Leg(nil, "untagged"))
	})
	if !strings.Contains(msg, "untagged") {
		t.Fatalf("panic did not name the offending leg: %q", msg)
	}
}

func TestCalcLeibnizNeedsTwoLegs(t *testing.T) {
	kit := CalcOrder{Le: func(a, b Term) Prop { return nil }, LeTrans: depName("leTrans")}
	msg := mustPanic(t, func() { kit.CalcLeibniz(nil, LeLeg(nil, "lonely")) })
	if !strings.Contains(msg, "Have") {
		t.Fatalf("panic should redirect a single link to Have: %q", msg)
	}
}

// The Leibniz mode must not leak into .Calc: a kit missing the ≈
// certificates still fails there exactly as it did before.
func TestCalcKeepsRequiringEquivalenceCertificates(t *testing.T) {
	kit := CalcOrder{
		Le:      func(a, b Term) Prop { return nil },
		Eq:      func(a, b Term) Prop { return nil },
		LeTrans: depName("leTrans"),
	}
	msg := mustPanic(t, func() { kit.requireCerts(legTags(relLe, relEq)) })
	if !strings.Contains(msg, "EqToLe") {
		t.Fatalf(".Calc must still demand EqToLe for a lifted link: %q", msg)
	}
}

// =======================================================================
// CalcRel — terminal chains
// =======================================================================

// CalcRel terminal chains.
//
// A chain whose endpoint IS the section goal cannot be asserted beside
// it — AssertTactic refuses a claim α-equal to the goal, and before the
// terminal branch existed such a chain died with "ministep Assert …
// failed", forcing the author to split it into a Calc over the interior
// waypoints plus a hand-grounded Show. These cases pin that the branch
// fires on α-equality and ONLY then, using a synthetic relation so no
// library certificate is needed.

// calcRelTestKit builds a CalcRel over an uninterpreted binary R.
func calcRelTestKit(R *ext.TermWrapper) CalcRel {
	return CalcRel{
		Rel: func(a, b Term) Prop {
			return MakeProp(R.Apply(a, b))
		},
		Trans: nil, // unreached: these chains arrive before any fold
	}
}

// When the leg's claim is α-equal to the goal, the leg's own proof runs
// AGAINST the goal: no AssertStep, no split, and the section closes.
func TestCalcRelTerminalChainProvesAgainstTheGoal(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)

	// Goal ⊢ R(x,y) with R(x,y) resident, so Assumption closes it.
	root := ctx.Section(MakeProp(R.Apply(x, y), R.Apply(x, y)))

	// The chain arrives at leg 1; leg 2 follows, which is the error the
	// terminal contract exists to name.
	msg := mustPanic(t, func() {
		calcRelTestKit(R).Calc(x,
			Leg(y, "arrive: R(x,y) is the goal", Assumption()),
			Leg(z, "after: nothing may follow the arrival", Assumption()),
		).applyAction(ctx, root)
	})

	if !strings.Contains(msg, "arrive") {
		t.Errorf("panic should name the leg the chain arrived at: %q", msg)
	}
	if !strings.Contains(msg, "must end there") {
		t.Errorf("panic should state the terminal contract: %q", msg)
	}
	// The point of the branch: the goal was PROVED, not asserted beside.
	assert.True(t, root.Proved(), "terminal leg should have closed the section")
	assert.Equal(t, 0, len(root.children), "terminal leg must not AssertStep-split the goal")
}

// Control: a claim that is NOT the goal still goes through AssertStep,
// exactly as before — the terminal branch must not capture ordinary
// links.
func TestCalcRelNonTerminalLinkStillAsserts(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())

	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)

	// Goal ⊢ R(x,z); the first link R(x,y) differs from it. (It must also
	// differ from every HYPOTHESIS — AssertTactic refuses an already
	// resident claim just as it refuses the goal, so a chain whose first
	// link is a given hypothesis is not spellable as a leg either.)
	root := ctx.Section(MakeProp(R.Apply(x, z)))

	// Leg 1's link is asserted — the split happens — and then its
	// non-closing body trips the eager-close contract.
	msg := mustPanic(t, func() {
		calcRelTestKit(R).Calc(x,
			Leg(y, "step: R(x,y) is a waypoint, not the goal",
				_RecordingAction{id: 1, trace: new([]int)}),
			Leg(z, "never reached", Assumption()),
		).applyAction(ctx, root)
	})

	if !strings.Contains(msg, "did not close") {
		t.Errorf("expected the eager-close panic from leg 2: %q", msg)
	}
	assert.Equal(t, 2, len(root.children), "a non-terminal link must AssertStep-split")
}
