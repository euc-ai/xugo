// membership_hypothesis_test.go — the verbs that open one resident fact
// read a membership in a set-builder through its predicate where the
// fact is not already the shape they open: Conjuncts splits
// `a ∈ {y | P(y) ∧ K(y) ∧ y < n}` into P(a), K(a), a < n; Unpack
// Skolemizes `a ∈ {y | ∃k. …}` and the three-part `a ∈ {f(k) | k | …}`;
// SplitDisj splits `a ∈ {y | P(y) ∨ K(y)}`. Only the fact's top is
// read, and a fact that is the shape as written is opened as written.
package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// Each conjunct closes from the membership keyless: the store a
// refutation would record into stays empty.
func TestMembershipHypothesis_ConjunctsReadsThePredicate(t *testing.T) {
	ctx, sec := comprehensionSection(t, "a ∈ {y:num | P(y) ∧ K(y) ∧ y < n} ⇒ K(a) ∨ Q")
	store := NewMemoryCNFStore()
	ctx.Env.ProofService.CNFStore = store
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			in := a.Assume()
			parts := a.Conjuncts(in, "P at a", "K at a", "a is below n")
			require.Len(t, parts, 3)
			for i, want := range []string{"P(a)", "K(a)", "a < n"} {
				content, _ := parts[i].BoundContent()
				assert.Equal(t, want, ext.PrintTerm(content), "conjunct %d", i+1)
			}
			a.Show("K holds at a", By(Normalized, parts[1]))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
	require.Empty(t, store.Proofs(), "no conjunct needed a refutation")
	require.Empty(t, store.Plans())
}

// The negative control: a conjunction is split as written, its
// membership conjunct kept whole — only a membership at the fact's top
// is read.
func TestMembershipHypothesis_ConjunctsOfAConjunctionAsWritten(t *testing.T) {
	ctx, sec := comprehensionSection(t, "P(a) ∧ a ∈ {y:num | K(y) ∧ y < n} ⇒ K(a) ∨ Q")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			both := a.Assume()
			parts := a.Conjuncts(both, "P at a", "a is in the set")
			require.Len(t, parts, 2)
			for i, want := range []string{"P(a)", "a ∈ {y | K(y) ∧ (y < n)}"} {
				content, _ := parts[i].BoundContent()
				assert.Equal(t, want, ext.PrintTerm(content), "conjunct %d", i+1)
			}
			a.Show("K holds at a", By(parts[1]))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}

// A membership whose reading is no conjunction is refused with the
// reading named, and the three-part form — an ∃ — with Unpack named.
func TestMembershipHypothesis_ConjunctsRefusesAReadingThatIsNoConjunction(t *testing.T) {
	for _, c := range []struct{ text, want string }{
		{"a ∈ {y:num | P(y)} ⇒ P(a) ∨ Q", "Argument.Conjuncts: a ∈ {y | P(y)} is not a conjunction, nor is its reading P(a)"},
		{"a ∈ {f(k) | k:num | P(k)} ⇒ Q ∨ ¬Q",
			"Argument.Conjuncts: a ∈ {f(k) | k | P(k)} is not a conjunction, nor is its reading ∃k.(P(k) ∧ (a = f(k))) — an ∃, which Unpack opens"},
	} {
		ctx, sec := comprehensionSection(t, c.text)
		requirePanicContains(t, c.want, func() {
			Derive(func(a *Argument) {
				in := a.Assume()
				a.Conjuncts(in, "one", "two")
			}).applyAction(ctx, sec)
		})
	}
}

// Unpack Skolemizes the ∃ a membership reads as: the identity form's
// condition, and the three-part form's binders.
func TestMembershipHypothesis_UnpackReadsThePredicate(t *testing.T) {
	for _, c := range []struct{ text, instance string }{
		{"a ∈ {y:num | ∃k:num. P(k) ∧ y = f(k)} ⇒ (∀k:num. P(k) ⇒ K(f(k))) ⇒ K(a)", "P(k₀) ∧ (a = f(k₀))"},
		{"a ∈ {f(k) | k:num | P(k)} ⇒ (∀k:num. P(k) ⇒ K(f(k))) ⇒ K(a)", "P(k₀) ∧ (a = f(k₀))"},
	} {
		ctx, sec := comprehensionSection(t, c.text)
		ok := provesInHand(t, func() *GoalStackNode {
			Derive(func(a *Argument) {
				in := a.Assume()
				law := a.Assume()
				k, instance := a.Unpack(in)
				assert.Equal(t, "k₀", ext.PrintTerm(k.Core()))
				content, _ := instance.BoundContent()
				assert.Equal(t, c.instance, ext.PrintTerm(content))
				a.Show("K holds at a", By(law, instance))
			}).applyAction(ctx, sec)
			return sec
		})
		require.True(t, ok != nil && sec.Proved(), c.text)
	}
}

// A fact's SplitDisj splits the ∨ a membership reads as, each branch
// holding its disjunct at the point.
func TestMembershipHypothesis_SplitDisjReadsThePredicate(t *testing.T) {
	ctx, sec := comprehensionSection(t, "a ∈ {y:num | P(y) ∨ K(y)} ⇒ (∀y:num. P(y) ⇒ Q) ⇒ (∀y:num. K(y) ⇒ Q) ⇒ Q")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			in := a.Assume()
			fromP := a.Assume()
			fromK := a.Assume()
			a.Show("Q either way", in.SplitDisj(
				LeftHolds("Q from P", Given(func(b *Argument, pa Fact) {
					content, _ := pa.BoundContent()
					assert.Equal(t, "P(a)", ext.PrintTerm(content))
					b.Show("Q", By(fromP, pa))
				})),
				RightHolds("Q from K", Given(func(b *Argument, ka Fact) {
					content, _ := ka.BoundContent()
					assert.Equal(t, "K(a)", ext.PrintTerm(content))
					b.Show("Q", By(fromK, ka))
				}))))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}

// Funext leaves an equation between set-builders pointwise, each side
// the set-builder applied to the point. No verb reads that form, and
// the refusal of the verb that met it says what it is, which rewrite
// opens an equation between sets in its place, and how the content is
// taken where the Funext stays.
func TestMembershipHypothesis_ASetBuilderAtItsPointIsNamed(t *testing.T) {
	const form = "The fact is a set-builder applied to its point, the form Funext leaves of an equation between sets"
	const rule = "Simp(Fwd(set_basic.Extension)) in place of Funext()"
	const remedy = "BySets(fact)"
	for _, c := range []struct {
		name, text, refusal string
		open                func(a *Argument, source Fact)
	}{
		{"Unpack",
			"{y:num | ∃k:num. P(k) ∧ y = f(k)} = {y:num | ∃k:num. K(k) ∧ y = f(k)}",
			"Argument.Unpack: only 0 leading ∃-binder(s), need 1",
			func(a *Argument, source Fact) { a.Unpack(source) }},
		{"Conjuncts",
			"{y:num | P(y) ∧ K(y)} = {y:num | K(y) ∧ P(y)}",
			"is not a conjunction",
			func(a *Argument, source Fact) { a.Conjuncts(source, "P at the point", "K at the point") }},
	} {
		ctx, sec := comprehensionSection(t, c.text)
		var refusal string
		func() {
			defer func() { refusal = fmt.Sprint(recover()) }()
			Derive(func(a *Argument) {
				a.Do(Funext())
				a.FixAs[ext.Nat]("u")
				a.Iff()
				a.Forward("a point of the left set is one of the right", func(b *Argument, source Fact) {
					c.open(b, source)
				})
			}).applyAction(ctx, sec)
		}()
		require.Contains(t, refusal, c.refusal, c.name)
		require.Contains(t, refusal, form, c.name)
		require.Contains(t, refusal, rule, c.name)
		require.Contains(t, refusal, remedy, c.name)
	}
}

// A fact that is neither a membership nor a set-builder at its point is
// refused as it was, with no note of the form.
func TestMembershipHypothesis_NoNoteForAnotherFact(t *testing.T) {
	ctx, sec := comprehensionSection(t, "P(a) ⇒ Q ∨ ¬Q")
	var refusal string
	func() {
		defer func() { refusal = fmt.Sprint(recover()) }()
		Derive(func(a *Argument) {
			a.Unpack(a.Assume())
		}).applyAction(ctx, sec)
	}()
	require.Contains(t, refusal, "Argument.Unpack: only 0 leading ∃-binder(s), need 1")
	require.NotContains(t, refusal, "set-builder applied to its point")
}
