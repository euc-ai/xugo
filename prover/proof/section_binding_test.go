package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	"github.com/stretchr/testify/require"
)

// A statement in the standard form, `∀xs. H₁ ∧ … ∧ Hₙ ⇒ C`, binds by its
// dependencies (section_binding.go): a fact parameter takes the
// hypotheses whose binders are bound before it, one fact all of them or
// one each, and what the parameters leave stays in the goal as a
// statement.

func contentOf(t *testing.T, f Fact) Term {
	t.Helper()
	content, ok := f.BoundContent()
	require.True(t, ok)
	return content
}

// transfer is a statement no tautology closes: the first hypothesis
// carries P to Q, the second puts x in P, the third is a bystander.
const transfer = "∀P Q:(num → bool). ∀x:num. (∀y:num. P(y) ⇒ Q(y)) ∧ P(x) ∧ x ≤ 3 ⇒ Q(x)"

func TestSection_OneFactEach(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem(transfer,
		func(a *Argument, P, Q, x Term, carry, px, small Fact) {
			require.Equal(t, 3, a.cur.Goal.NumHyps(), "%s", PrintProp(a.cur.Goal))
			require.True(t, contentOf(t, px).AlphaEquals(a.Term("P(x)").Core()))
			require.True(t, contentOf(t, small).AlphaEquals(a.Term("x ≤ 3").Core()))
			a.Show("carried over", By(carry, px))
		})
	require.True(t, sec.Proved())
}

func TestSection_OneFactSplitByConjuncts(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem(transfer,
		func(a *Argument, P, Q, x Term, given Fact) {
			held := a.Conjuncts(given, "P carries over to Q", "x is in P", "x is at most 3")
			a.Show("carried over", By(held[0], held[1]))
		})
	require.True(t, sec.Proved())
}

// A fact parameter between the binders takes the hypotheses available
// where it stands: after P and Q, the one about them alone; after x, the
// two that mention x.
func TestSection_FactsWhereTheirBindersAreBound(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem(transfer,
		func(a *Argument, P, Q Term, carry Fact, x Term, rest Fact) {
			require.True(t, contentOf(t, carry).AlphaEquals(a.Term("∀y:num. P(y) ⇒ Q(y)").Core()),
				"%s", ext.PrintTerm(contentOf(t, carry)))
			require.True(t, contentOf(t, rest).AlphaEquals(a.Term("P(x) ∧ x ≤ 3").Core()),
				"%s", ext.PrintTerm(contentOf(t, rest)))
			held := a.Conjuncts(rest, "x is in P", "x is at most 3")
			a.Show("carried over", By(carry, held[0]))
		})
	require.True(t, sec.Proved())
}

// Two facts where three hypotheses are available say nothing about which
// takes what: refused, and the author places them.
func TestSection_FactsRefusedWhereTheSplitIsAmbiguous(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, fmt.Sprint(r), "stand together where")
	}()
	ctx.Theorem(transfer,
		func(a *Argument, P, Q, x Term, both, small Fact) {
			a.Show("carried over", By(both, small))
		})
}

// Members take their memberships; the fact parameter takes what is left.
func TestSection_MembersAndAFact(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem("∀c:(num → bool). ∀f:(num → num). ∀x y:num. x ∈ c ∧ y ∈ c ∧ (∀z:num. z ∈ c ⇒ f(z) ∈ c) ⇒ f(y) ∈ c",
		func(a *Argument, c *ext.Expr[ext.Set[ext.Nat]], f Term, x, y *Member[ext.Nat, on.C], closed Fact) {
			require.True(t, contentOf(t, closed).AlphaEquals(a.Term("∀z:num. z ∈ c ⇒ f(z) ∈ c").Core()),
				"%s", ext.PrintTerm(contentOf(t, closed)))
			a.Show("c is closed under f", By(closed, y.AsFact()))
		})
	require.True(t, sec.Proved())
}

// What no parameter takes stays in the goal as a statement.
func TestSection_TheRestStaysInTheGoal(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem("∀c:(num → bool). ∀f:(num → num). ∀x:num. x ∈ c ∧ (∀z:num. z ∈ c ⇒ f(z) ∈ c) ⇒ f(x) ∈ c",
		func(a *Argument, c *ext.Expr[ext.Set[ext.Nat]], f Term, x *Member[ext.Nat, on.C]) {
			ante, _, ok := matchesImply(a.cur.Goal.Conclusion())
			require.True(t, ok, "%s", PrintProp(a.cur.Goal))
			require.True(t, ante.AlphaEquals(a.Term("∀z:num. z ∈ c ⇒ f(z) ∈ c").Core()))
			closed := a.Assume()
			a.Show("c is closed under f", By(closed, x.AsFact()))
		})
	require.True(t, sec.Proved())
}

// A closure that binds a prefix of the binders sees the rest of the
// statement as the statement says it: an induction on a binder left
// unbound generalizes over the binders left with it.
func TestSection_PrefixLeavesTheStatementGeneral(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem(transfer,
		func(a *Argument, P, Q Term) {
			require.True(t, a.cur.Goal.Conclusion().AlphaEquals(a.Term("∀x:num. (∀y:num. P(y) ⇒ Q(y)) ∧ P(x) ∧ x ≤ 3 ⇒ Q(x)").Core()),
				"%s", PrintProp(a.cur.Goal))
			a.Fix()
			held := a.Conjuncts(a.Assume(), "P carries over to Q", "x is in P", "x is at most 3")
			a.Show("carried over", By(held[0], held[1]))
		})
	require.True(t, sec.Proved())
}

// Facts standing together take one hypothesis each as long as they
// last; the one left over binds nothing, and is refused.
func TestSection_RefusesMoreFactsThanHypotheses(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, fmt.Sprint(r), "binding the binders left makes none available")
	}()
	ctx.Theorem(transfer,
		func(a *Argument, P, Q, x Term, carry, px, small, extra Fact) {
			a.Show("carried over", By(carry, px))
		})
}

// A Fact where nothing is available binds a bundle: the binders next in
// order up to the first hypothesis they make available, which mentions
// each of them.
func TestSection_FactBindsABundle(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Theorem("∀op:(A → A → A). ∀e x:A. readMon(op, e) ∧ op(x, e) = x ⇒ op(e, x) = x",
		func(a *Argument, mon Fact, x Term, right Fact) {
			require.True(t, contentOf(t, mon).AlphaEquals(a.Term("readMon(op, e)").Core()), "%s", ext.PrintTerm(contentOf(t, mon)))
			a.Show("the left identity", By(Read(depName("zz_read_law"), mon)))
		})
	require.True(t, sec.Proved())
}

// A closure that binds only the bundle leaves the rest of the statement
// in the goal, its binders general.
func TestSection_FactBundleLeavesTheRest(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Theorem("∀op:(A → A → A). ∀e x:A. readMon(op, e) ∧ op(x, e) = x ⇒ op(e, x) = x",
		func(a *Argument, mon Fact) {
			require.True(t, a.cur.Goal.Conclusion().AlphaEquals(a.Term("∀x:A. op(x, e) = x ⇒ op(e, x) = x").Core()),
				"%s", PrintProp(a.cur.Goal))
			a.Fix()
			a.Assume()
			a.Show("the left identity", By(Read(depName("zz_read_law"), mon)))
		})
	require.True(t, sec.Proved())
}

// A bundle is the structure fact at its binders, however early a
// hypothesis merely mentioning the first of them becomes available: the
// Fact binds op and e with readMon(op, e), and leaves `∀y. op(y, y) = y`,
// available at op alone, to the fact after it.
func TestSection_BundleIsTheStructureFactNotTheFirstMention(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Theorem("∀op:(A → A → A). ∀e:A. (∀y:A. op(y, y) = y) ∧ readMon(op, e) ⇒ op(e, e) = e",
		func(a *Argument, mon, idem Fact) {
			require.True(t, contentOf(t, mon).AlphaEquals(a.Term("readMon(op, e)").Core()), "%s", ext.PrintTerm(contentOf(t, mon)))
			require.True(t, contentOf(t, idem).AlphaEquals(a.Term("∀y:A. op(y, y) = y").Core()), "%s", ext.PrintTerm(contentOf(t, idem)))
			a.Show("e is idempotent like everything", By(idem))
		})
	require.True(t, sec.Proved())
}
