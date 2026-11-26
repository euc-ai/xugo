package omega

import (
	"math/rand/v2"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Two applications of one head are equal where their arguments decide
// equal: under no hypothesis for an identity of the ring, and under the
// hypotheses for an equation they imply. A head the layers do not read is
// all the comparison asks of the applications.
func TestArgumentCongruence_AnEquationOfTwoApplications(t *testing.T) {
	installTestBundle(t)
	A := core.MakeVarType("A")
	f := ext.Var("f", core.MakeFun(numVar("n").Type(), A)).Core()
	app := func(x Term) Term { return ext.Apply(f, x) }
	n, q := numVar("n"), numVar("q")
	one, two := Numeral(1), Numeral(2)
	if !closesUnder(t, nil, eqT(app(plus(plus(n, one), one)), app(plus(n, two)))) {
		t.Error("f(n + 1 + 1) = f(n + 2) did not close")
	}
	// An equation with no variable side defines nothing, and the linear
	// layer reads n = q + 1 off it.
	shifted := eqT(plus(n, one), plus(q, two))
	goal := eqT(app(n), app(plus(q, one)))
	if !closesUnder(t, []Term{shifted}, goal) {
		t.Error("f(n) = f(q + 1) did not close from n + 1 = q + 2")
	}
	if closesUnder(t, []Term{eqT(plus(n, one), plus(q, one))}, goal) {
		t.Error("f(n) = f(q + 1) closed from n + 1 = q + 1")
	}
	if closesUnder(t, nil, eqT(app(plus(n, one)), app(plus(n, two)))) {
		t.Error("f(n + 1) = f(n + 2) closed")
	}
	g := ext.Var("g", core.MakeFun(numVar("n").Type(), A)).Core()
	if closesUnder(t, nil, eqT(app(plus(n, two)), ext.Apply(g, plus(n, two)))) {
		t.Error("two applications of different heads were compared")
	}
}

// A formula is read at a hypothesis that is the same application up to
// its arguments, and at the negation of one.
func TestArgumentCongruence_AFormulaAtAHypothesis(t *testing.T) {
	installTestBundle(t)
	P := ext.Var("P", core.MakeFun(numVar("n").Type(), core.TypeBool())).Core()
	n, q := numVar("n"), numVar("q")
	one, two := Numeral(1), Numeral(2)
	shifted := eqT(plus(n, one), plus(q, two))
	stated, goal := ext.Apply(P, n), ext.Apply(P, plus(q, one))
	if !closesUnder(t, []Term{shifted, stated}, goal) {
		t.Error("P(q + 1) did not close from P(n) and n + 1 = q + 2")
	}
	if !closesUnder(t, []Term{shifted, not(stated)}, not(goal)) {
		t.Error("¬P(q + 1) did not close from ¬P(n) and n + 1 = q + 2")
	}
	if closesUnder(t, []Term{stated}, goal) {
		t.Error("P(q + 1) closed from P(n) alone")
	}
}

// An equation is read at a hypothesis equation that states it up to the
// arguments of its two sides.
func TestArgumentCongruence_AnEquationAtAHypothesisEquation(t *testing.T) {
	installTestBundle(t)
	A := core.MakeVarType("A")
	f := ext.Var("f", core.MakeFun(numVar("n").Type(), A)).Core()
	g := ext.Var("g", core.MakeFun(numVar("n").Type(), A)).Core()
	n, m := numVar("n"), numVar("m")
	one := Numeral(1)
	stated := eqT(ext.Apply(f, plus(n, one)), ext.Apply(g, m))
	goal := eqT(ext.Apply(g, plus(m, Numeral(0))), ext.Apply(f, plus(one, n)))
	if !closesUnder(t, []Term{stated}, goal) {
		t.Error("g(m + 0) = f(1 + n) did not close from f(n + 1) = g(m)")
	}
}

// _QuestionScript works a table's questions out by a script: each question
// asks the ones listed for it, in order, and has a theorem where proves
// says so of the answers it got. It counts how often each is worked out.
type _QuestionScript struct {
	table  *_ArgumentQuestions
	asks   map[string][]string
	proves map[string]func(answers map[string]*prop.PropWrapper) bool
	worked map[string]int
}

func newQuestionScript(asks map[string][]string) *_QuestionScript {
	return &_QuestionScript{
		table:  newArgumentQuestions(),
		asks:   asks,
		proves: map[string]func(map[string]*prop.PropWrapper) bool{},
		worked: map[string]int{},
	}
}

func (s *_QuestionScript) ask(name string) *prop.PropWrapper {
	return s.table.ask(core.TermKey(name), func() *prop.PropWrapper {
		s.worked[name]++
		answers := map[string]*prop.PropWrapper{}
		for _, sub := range s.asks[name] {
			answers[sub] = s.ask(sub)
		}
		if proves := s.proves[name]; proves != nil && proves(answers) {
			return prop.WrapProp(core.Refl(numVar(name)))
		}
		return nil
	})
}

// Questions that all ask one another and have no theorem are each worked
// out once: the nil of one reached under the others' declines is the
// answer the others get when they ask it again.
func TestArgumentQuestions_ACycleIsWorkedOutOncePerQuestion(t *testing.T) {
	names := []string{"a", "b", "c", "d", "e", "f", "g", "h"}
	asks := map[string][]string{}
	for _, n := range names {
		for range 3 { // asked more than once at each level, as a rewrite to a fixpoint asks
			for _, m := range names {
				if m != n {
					asks[n] = append(asks[n], m)
				}
			}
		}
	}
	s := newQuestionScript(asks)
	for _, n := range names {
		if s.ask(n) != nil {
			t.Errorf("%s has a theorem", n)
		}
	}
	for _, n := range names {
		if s.worked[n] != 1 {
			t.Errorf("%s was worked out %d times", n, s.worked[n])
		}
	}
}

// A theorem found under a decline is kept: b asks a, which is open, and
// is proved all the same.
func TestArgumentQuestions_ATheoremUnderADeclineIsKept(t *testing.T) {
	s := newQuestionScript(map[string][]string{"a": {"b", "b"}, "b": {"a"}})
	s.proves["b"] = func(map[string]*prop.PropWrapper) bool { return true }
	if s.ask("a") != nil {
		t.Error("a has a theorem")
	}
	if s.ask("b") == nil {
		t.Error("b lost its theorem")
	}
	if s.worked["b"] != 1 {
		t.Errorf("b was worked out %d times", s.worked["b"])
	}
}

// A nil that rests on a decline is no answer once the declined question
// has a theorem: b needs a, is asked while a is open, and is worked out
// again after a is proved.
func TestArgumentQuestions_ANilUnderADeclineIsAskedAgainAfterATheorem(t *testing.T) {
	s := newQuestionScript(map[string][]string{"a": {"b"}, "b": {"a"}})
	s.proves["a"] = func(map[string]*prop.PropWrapper) bool { return true }
	s.proves["b"] = func(answers map[string]*prop.PropWrapper) bool { return answers["a"] != nil }
	if s.ask("a") == nil {
		t.Fatal("a has no theorem")
	}
	if s.ask("b") == nil {
		t.Error("b kept the nil it got while a was open")
	}
}

// A nil that rests on a decline is settled when the declined question
// closes with a settled nil, and is held meanwhile: c is asked by b and
// again by a, and worked out once.
func TestArgumentQuestions_AHeldNilFollowsWhatItRestsOn(t *testing.T) {
	s := newQuestionScript(map[string][]string{"a": {"b", "c", "b"}, "b": {"c", "c"}, "c": {"a", "b"}})
	if s.ask("a") != nil {
		t.Fatal("a has a theorem")
	}
	for _, n := range []string{"b", "c", "a"} {
		if s.ask(n) != nil {
			t.Errorf("%s has a theorem", n)
		}
	}
	for _, n := range []string{"a", "b", "c"} {
		if s.worked[n] != 1 {
			t.Errorf("%s was worked out %d times", n, s.worked[n])
		}
	}
}

// A nil a decline went into, reached with a theorem found on the way, is
// not kept: the theorem came after part of the work, which done again
// may go another way. b rests on the open a and finds c on the way; a
// rests on itself alone and does too.
func TestArgumentQuestions_ANilPastATheoremIsNotKept(t *testing.T) {
	s := newQuestionScript(map[string][]string{"a": {"b", "b"}, "b": {"a", "c"}})
	s.proves["c"] = func(map[string]*prop.PropWrapper) bool { return true }
	if s.ask("a") != nil {
		t.Fatal("a has a theorem")
	}
	if s.worked["b"] != 2 {
		t.Errorf("b was worked out %d times under a", s.worked["b"])
	}
	if s.worked["c"] != 1 {
		t.Errorf("c was worked out %d times", s.worked["c"])
	}
	// Asked again, a is worked out with c in hand, and b under it once:
	// no theorem is found this time, so both nils are kept.
	for range 2 {
		if s.ask("a") != nil {
			t.Fatal("a has a theorem")
		}
	}
	if s.worked["a"] != 2 || s.worked["b"] != 3 {
		t.Errorf("a was worked out %d times and b %d", s.worked["a"], s.worked["b"])
	}
}

// The table answers as the rules do. Each question has a few ways of
// being proved, each a list of questions that must all have theorems,
// which is what the comparison's own work comes to: an application's
// arguments, a hypothesis's two sides. Over random rules every question
// has a theorem exactly where forward chaining from the rules with no
// premise derives it, whatever order the questions are asked in and
// whatever the table kept from the ones before. A question is worked
// out again only after a theorem, once and once more per question open
// at the theorem, so no more often than the bound below.
func TestArgumentQuestions_AnswersAsTheRulesDo(t *testing.T) {
	rng := rand.New(rand.NewPCG(1, 2))
	for round := range 3000 {
		n := 2 + rng.IntN(7)
		names := make([]core.TermKey, n)
		for i := range names {
			names[i] = core.TermKey(string(rune('a' + i)))
		}
		// ways[i] is the ways of proving question i.
		ways := make([][][]int, n)
		for i := range ways {
			for range rng.IntN(4) {
				var premises []int
				for range rng.IntN(4) {
					premises = append(premises, rng.IntN(n))
				}
				ways[i] = append(ways[i], premises)
			}
		}
		derived := make([]bool, n)
		for changed := true; changed; {
			changed = false
			for i := range ways {
				if derived[i] {
					continue
				}
				for _, premises := range ways[i] {
					if !slices.ContainsFunc(premises, func(p int) bool { return !derived[p] }) {
						derived[i], changed = true, true
						break
					}
				}
			}
		}
		table := newArgumentQuestions()
		worked := make([]int, n)
		var ask func(i int) *prop.PropWrapper
		ask = func(i int) *prop.PropWrapper {
			return table.ask(names[i], func() *prop.PropWrapper {
				worked[i]++
				for _, premises := range ways[i] {
					if !slices.ContainsFunc(premises, func(p int) bool { return ask(p) == nil }) {
						return prop.WrapProp(core.Refl(numVar("x")))
					}
				}
				return nil
			})
		}
		theorems := 0
		for _, i := range rng.Perm(n) {
			if got := ask(i) != nil; got != derived[i] {
				t.Fatalf("round %d: question %d of %v answers %v, the rules %v", round, i, ways, got, derived[i])
			}
		}
		for i := range derived {
			if derived[i] {
				theorems++
			}
		}
		for i := range worked {
			if worked[i] > (theorems+1)*(n+1) {
				t.Fatalf("round %d: question %d of %v was worked out %d times with %d theorems", round, i, ways, worked[i], theorems)
			}
		}
	}
}

// A set-builder compared with a hypothesis's, whose body compares the
// first again at the bound variable, asks a chain of equations that
// closes on itself: one per application on the way down, at each of the
// names the bound variable takes. Each is asked more than once by the
// comparison above it, and the comparison works each out once.
func TestArgumentCongruence_AComparisonThatClosesOnItselfIsDecidedOnce(t *testing.T) {
	A := core.MakeVarType("A")
	pred := core.MakeFun(A, core.TypeBool())
	P := ext.Var("P", pred).Core()
	R := ext.Var("R", core.MakeFun(A, pred)).Core()
	wrap := ext.Var("g", core.MakeFun(core.TypeBool(), core.TypeBool())).Core()
	c, U := ext.Var("c", pred).Core(), ext.Var("U", pred).Core()
	u, v, x := core.Var("u", A), core.Var("v", A), core.Var("x", A)
	// A body sits under three applications, as a set-builder's does
	// under its quantifier and its specification.
	under := func(body Term) Term { return ext.Apply(wrap, ext.Apply(wrap, ext.Apply(wrap, body))) }
	// below(y) is {x | R(x, y)}.
	below := func(y Term) Term { return core.Abs(x, under(ext.Apply(R, x, y))) }
	defined := eqT(U, core.Abs(u, under(and(ext.Apply(P, u), not(eqT(below(u), c))))))
	hyps := []Term{defined}
	goal := eqT(below(v), c)

	const bound = 100
	asked := 0
	var whole prop.Rewrite
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	leaf := argumentCongruence(hyps, UnscopedArithPolicy(), nil, func() prop.Rewrite {
		if asked++; asked > bound {
			t.Fatalf("more than %d argument equations decided", bound)
		}
		return whole
	})
	whole = prop.BasicRewritesWithEnv(anyHyp, leaf)
	if w := whole(goal); w != nil {
		t.Errorf("the goal was rewritten to %v", prop.Rhs(w))
	}
	t.Logf("%d argument equations decided", asked)
}
