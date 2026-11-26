// branch_test.go — the statement form of a structural split
// (branch.go): the opener's fan-out, the branch verbs that claim it by
// name, and the contracts that make a forgotten or duplicated branch
// loud instead of silent.
//
// The first test is the one that matters most: the statement form and
// the Chain form must record the SAME TREE. Every recorded CNF key in
// the corpus depends on it, and the sweep that converted 329 sites
// rests on it being true rather than merely intended.

package proof

import (
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/require"
)

// dumpTree renders a proof tree as indented goals — the shape a
// recorded proof is keyed on, independent of the surface that built it.
func dumpTree(n *GoalStackNode, depth int) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s%s\n", strings.Repeat("  ", depth), prop.PrintProp(n.Goal))
	for _, c := range n.children {
		b.WriteString(dumpTree(c, depth+1))
	}
	return b.String()
}

// requirePanicMentions runs fn and requires it to panic with a message
// naming `want`. The contracts below are about what the panic SAYS —
// which branch was forgotten, which branches the open split has — so a
// bare "it panicked" would not test them.
func requirePanicMentions(t *testing.T, want string, fn func()) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a panic mentioning %q", want)
		require.Contains(t, fmt.Sprint(r), want)
	}()
	fn()
}

// caseSplitGoal is the fixture both spellings prove: a classical split
// with one law per branch.
type caseSplitGoal struct {
	e        *givenTestEnv
	R        *ext.TermWrapper
	pos, neg Term
	goal     Prop
}

func makeCaseSplitGoal() *caseSplitGoal {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	pos := e.P.Apply(e.x).Imply(R.Apply(e.x))
	neg := Not(e.P.Apply(e.x)).Imply(R.Apply(e.x))
	return &caseSplitGoal{
		e: e, R: R, pos: pos, neg: neg,
		goal: MakeProp(R.Apply(e.x), pos, neg),
	}
}

// TestBranch_StatementFormIsTreeIdentical: the statement form records
// exactly the tree the Chain form records. Nothing about the proof
// changes — only where the author's parentheses go.
func TestBranch_StatementFormIsTreeIdentical(t *testing.T) {
	chainForm := func() *GoalStackNode {
		g := makeCaseSplitGoal()
		sec := g.e.ctx.Section(g.goal)
		sec.Do(Derive(func(a *Argument) {
			a.Do(ByCaseStep(g.e.P.Apply(g.e.x).Core(),
				MakeCase("P(x)", Given(func(a *Argument, h Fact) {
					a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
				})),
				MakeCase("¬P(x)", Given(func(a *Argument, h Fact) {
					a.Show("modus ponens on the negative law", By(h, a.Hyp(g.neg.Core())))
				}))))
		}))
		require.True(t, sec.Proved())
		return sec
	}
	statementForm := func() *GoalStackNode {
		g := makeCaseSplitGoal()
		sec := g.e.ctx.Section(g.goal)
		sec.Do(Derive(func(a *Argument) {
			a.Cases(g.e.P.Apply(g.e.x))
			a.When("P(x)", func(a *Argument, h Fact) {
				a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
			})
			a.Otherwise("¬P(x)", func(a *Argument, h Fact) {
				a.Show("modus ponens on the negative law", By(h, a.Hyp(g.neg.Core())))
			})
		}))
		require.True(t, sec.Proved())
		return sec
	}
	require.Equal(t, dumpTree(chainForm(), 0), dumpTree(statementForm(), 0),
		"the statement form recorded a different tree than the Chain form — "+
			"every recorded CNF key in the corpus rests on these agreeing")
}

// TestBranch_OrderIsTheVerbNotThePosition: writing Otherwise before
// When proves the same theorem. Which branch a body proves is the verb;
// source order carries nothing.
func TestBranch_OrderIsTheVerbNotThePosition(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	sec.Do(Derive(func(a *Argument) {
		a.Cases(g.e.P.Apply(g.e.x))
		a.Otherwise("¬P(x) first — the verb says which branch this is", func(a *Argument, h Fact) {
			a.Show("modus ponens on the negative law", By(h, a.Hyp(g.neg.Core())))
		})
		a.When("P(x) second", func(a *Argument, h Fact) {
			a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
		})
	}))
	require.True(t, sec.Proved(), "branches written in the other order did not close the section")
}

// TestBranch_ActionListBody: a branch whose proof is a list of Actions
// needs no closure and no Chain — the slot already sequences.
func TestBranch_ActionListBody(t *testing.T) {
	e := makeGivenTestEnv()
	n := Var("n", numType)
	stepHyp := ForAll(n)(e.R.Apply(n).Imply(e.R.Apply(sucOf(n))))
	base := e.R.Apply(zeroTerm)

	sec := e.ctx.Section(MakeProp(e.R.Apply(e.k), base, stepHyp))
	sec.Do(Derive(func(a *Argument) {
		a.Induct(e.k)
		a.Base("the base hypothesis IS the goal", Assumption())
		a.Step("the step law at k carries R(k) to R(suc k)", func(a *Argument, ih Fact) {
			law := a.Hyp(stepHyp.Core())
			a.Show("modus ponens on the step law", By(ih, law.At(e.k)))
		})
	}))
	require.True(t, sec.Proved(), "an Action-list Base body did not close its branch")
}

// TestBranch_ReadInABranchArgumentList: Go evaluates a branch's
// argument list BEFORE the branch verb runs, so a read inside it — the
// `b.Term(…)` of a Calc leg is the corpus shape — is evaluated with the
// split already open. It must still work, and must read what it read
// before the split: an opener does not move the spine.
//
// This is the one contract the 329-site sweep broke on its first
// replay (vector/dot's AdjointLinear), which is why it is pinned here.
func TestBranch_ReadInABranchArgumentList(t *testing.T) {
	g := makeCaseSplitGoal()
	g.e.ctx.Var("x", TypeA)
	g.e.ctx.Var("P", MakeFun(TypeA, TypeBool))
	sec := g.e.ctx.Section(g.goal)

	var beforeSplit, whileOpen Term
	sec.Do(Derive(func(a *Argument) {
		beforeSplit = a.Term("P(x)")
		a.Cases(g.e.P.Apply(g.e.x))
		a.When("P(x)", readThenProve(&whileOpen, a, g.pos))
		a.Otherwise("¬P(x)", func(a *Argument, h Fact) {
			a.Show("modus ponens on the negative law", By(h, a.Hyp(g.neg.Core())))
		})
	}))
	require.True(t, sec.Proved())
	require.NotNil(t, whileOpen, "the read in the branch argument list never ran")
	require.True(t, beforeSplit.Core().Equals(whileOpen.Core()),
		"a read evaluated with the split open saw something else than the same read before it")
}

// readThenProve mirrors the corpus shape: an Action built for a branch's
// argument list whose CONSTRUCTION reads the block (`b.Term(…)` inside a
// Calc leg). Go runs it before the branch verb, so it runs with the
// split open.
func readThenProve(into *Term, a *Argument, law Term) Action {
	*into = a.Term("P(x)")
	return Given(func(b *Argument, h Fact) {
		b.Show("modus ponens on the positive law", By(h, b.Hyp(law.Core())))
	})
}

// TestBranch_ForgottenBranchPanicsNamingIt: a block that opens a split
// and proves only one branch names the one it forgot — not a generic
// "N open goals".
func TestBranch_ForgottenBranchPanicsNamingIt(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	requirePanicMentions(t, "Otherwise", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Cases(g.e.P.Apply(g.e.x))
			a.When("P(x)", func(a *Argument, h Fact) {
				a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
			})
		}))
	})
}

// TestBranch_BranchClaimedTwicePanics: the second claim of a branch is
// an authoring error, not a silent overwrite.
func TestBranch_BranchClaimedTwicePanics(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	requirePanicMentions(t, "already proved", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Cases(g.e.P.Apply(g.e.x))
			a.When("P(x)", func(a *Argument, h Fact) {
				a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
			})
			a.When("P(x) again", func(a *Argument, h Fact) {
				a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
			})
		}))
	})
}

// TestBranch_WrongBranchVerbPanics: a verb belonging to another split's
// branches names the branches the OPEN split actually has.
func TestBranch_WrongBranchVerbPanics(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	requirePanicMentions(t, "When and Otherwise", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Cases(g.e.P.Apply(g.e.x))
			a.Base("a Cases split has no Base", Assumption())
		}))
	})
}

// TestBranch_OrdinaryVerbWhileOpenPanics: the deduction has no single
// line to continue on until every branch is claimed, so an ordinary
// verb in between is refused rather than silently running on one of the
// branches.
func TestBranch_OrdinaryVerbWhileOpenPanics(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	requirePanicMentions(t, "still unproved", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Cases(g.e.P.Apply(g.e.x))
			a.When("P(x)", func(a *Argument, h Fact) {
				a.Show("modus ponens on the positive law", By(h, a.Hyp(g.pos.Core())))
			})
			a.Show("the split is not finished", By())
		}))
	})
}

// TestBranch_NoSplitOpenPanics: a branch verb with no opener before it
// says which openers produce it.
func TestBranch_NoSplitOpenPanics(t *testing.T) {
	g := makeCaseSplitGoal()
	sec := g.e.ctx.Section(g.goal)
	requirePanicMentions(t, "no split is open", func() {
		sec.Do(Derive(func(a *Argument) {
			a.When("nothing was opened", Assumption())
		}))
	})
}
