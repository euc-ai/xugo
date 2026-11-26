package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// A case split on t gives child 0 the term under one leading ¬ and
// child 1 its negation, so which child t HOLDS on is t's own polarity's
// to say. Every named branch reads it the same way: When / Otherwise,
// Assuming / Unless and the Argument verbs that bind the surviving
// hypothesis. The fixtures run one argument on p, ¬p and ¬¬p.

type casePolarityFixture struct {
	negations int
	e         *givenTestEnv
	term      Term // the case term
	holds     Term // the hypothesis of the branch on which term holds
	fails     Term // the hypothesis of the branch on which it fails
	holdsLaw  Term // holds ⇒ R
	failsLaw  Term // fails ⇒ R
	goal      Prop // holdsLaw, failsLaw ⊢ R
}

func casePolarityFixtures() []casePolarityFixture {
	var out []casePolarityFixture
	for negations := 0; negations <= 2; negations++ {
		e := makeGivenTestEnv()
		p := e.P.Apply(e.x).Core()
		term := p
		for range negations {
			term = Not(term).Core()
		}
		// The split contracts one leading ¬: the branch on which ¬p
		// fails holds p, the one on which ¬¬p fails holds ¬p.
		fails := Not(p).Core()
		if negations == 1 {
			fails = p
		}
		r := Var("R", MakeFun(TypeA, TypeBool)).Apply(e.x).Core()
		holdsLaw := ext.WrapTerm(term).Imply(r).Core()
		failsLaw := ext.WrapTerm(fails).Imply(r).Core()
		out = append(out, casePolarityFixture{
			negations: negations, e: e, term: term, holds: term, fails: fails,
			holdsLaw: holdsLaw, failsLaw: failsLaw, goal: MakeProp(r, holdsLaw, failsLaw),
		})
	}
	return out
}

// closeWith closes a branch from the hypothesis it received and the
// law that consumes it; a branch that received the other hypothesis
// has no such law and fails.
func closeWith(hyp, law Term) Action {
	return Derive(func(b *Argument) {
		b.Show("the matching law closes this branch", By(b.Hyp(hyp), b.Hyp(law)))
	})
}

// TestLinearizers_DischargeTheBranchNamed: Assuming(t) discharges the
// branch on which t fails and continues with t resident; Unless(t) the
// reverse — whatever t's polarity, in the Chain form and the Argument
// form alike, the Argument form binding the surviving hypothesis.
func TestLinearizers_DischargeTheBranchNamed(t *testing.T) {
	for _, f := range casePolarityFixtures() {
		for _, unless := range []bool{false, true} {
			for _, argument := range []bool{false, true} {
				verb, form := "Assuming", "chain"
				if unless {
					verb = "Unless"
				}
				if argument {
					form = "argument"
				}
				t.Run(fmt.Sprintf("%d negations/%s/%s", f.negations, verb, form), func(t *testing.T) {
					side, main, sideLaw, mainLaw := f.fails, f.holds, f.failsLaw, f.holdsLaw
					if unless {
						side, main, sideLaw, mainLaw = f.holds, f.fails, f.holdsLaw, f.failsLaw
					}
					sec := f.e.ctx.Section(f.goal)
					if argument {
						sec.Do(Derive(func(a *Argument) {
							var h Fact
							if unless {
								h = a.Unless(f.term, "the side law settles it", closeWith(side, sideLaw))
							} else {
								h = a.Assuming(f.term, "the side law settles it", closeWith(side, sideLaw))
							}
							a.Show("the surviving hypothesis feeds its law", By(h, a.Hyp(mainLaw)))
						}))
					} else {
						act := Assuming(f.term, "the side law settles it", closeWith(side, sideLaw))
						if unless {
							act = Unless(f.term, "the side law settles it", closeWith(side, sideLaw))
						}
						sec.Do(Chain(act, closeWith(main, mainLaw)))
					}
					require.True(t, sec.Proved())
				})
			}
		}
	}
}

// TestArgumentLinearizers_NameTheSurvivingHypothesis: the Fact
// a.Assuming and a.Unless return is named by the hypothesis the
// surviving branch received as the term prints — for a.Unless(¬p) that
// is p, the split having contracted the ¬.
func TestArgumentLinearizers_NameTheSurvivingHypothesis(t *testing.T) {
	for _, f := range casePolarityFixtures() {
		for _, unless := range []bool{false, true} {
			verb := "Assuming"
			if unless {
				verb = "Unless"
			}
			t.Run(fmt.Sprintf("%d negations/%s", f.negations, verb), func(t *testing.T) {
				sec := f.e.ctx.Section(f.goal)
				var h Fact
				sec.Do(Derive(func(a *Argument) {
					if unless {
						h = a.Unless(f.term, "the side law settles it", closeWith(f.holds, f.holdsLaw))
						a.Show("the surviving hypothesis feeds its law", By(h, a.Hyp(f.failsLaw)))
					} else {
						h = a.Assuming(f.term, "the side law settles it", closeWith(f.fails, f.failsLaw))
						a.Show("the surviving hypothesis feeds its law", By(h, a.Hyp(f.holdsLaw)))
					}
				}))
				require.True(t, sec.Proved())
				want := f.holds
				if unless {
					want = f.fails
				}
				require.Equal(t, ext.PrintTerm(want), h.handle.Name())
			})
		}
	}
}

// TestCases_WhenIsTheBranchOnWhichTheTermHolds: a.When claims the
// branch on which t holds and a.Otherwise the one on which it fails,
// whatever t's polarity; each binds the hypothesis its branch received.
func TestCases_WhenIsTheBranchOnWhichTheTermHolds(t *testing.T) {
	for _, f := range casePolarityFixtures() {
		t.Run(fmt.Sprintf("%d negations", f.negations), func(t *testing.T) {
			sec := f.e.ctx.Section(f.goal)
			sec.Do(Derive(func(a *Argument) {
				a.Cases(f.term)
				a.When("the term holds", func(b *Argument, h Fact) {
					b.Show("its law closes the branch", By(h, b.Hyp(f.holdsLaw)))
				})
				a.Otherwise("the term fails", func(b *Argument, h Fact) {
					b.Show("the other law closes the branch", By(h, b.Hyp(f.failsLaw)))
				})
			}))
			require.True(t, sec.Proved())
		})
	}
}
