// induction_motive.go — the predicate of a cited induction, read from
// the goal.
//
// ByInduction cites a principle at its predicate. Where the cite stops
// before the predicate — the principle bare, or at its parameters —
// the predicate is not written: it is the goal, read at the index the
// induction runs on. "By induction on the derivation" names a fact and
// no predicate, and this is that reading.
//
// The index comes from one of two places, tried in this order:
//
//   - A PREMISE. An induction principle concludes `∀x̄. G(x̄) ⇒ P(x̄)`:
//     its predicate at every index its guard G holds of (finite(s),
//     transitive_closure(R, x, y), a derivation). A premise listed
//     beside the principle that states the guard at some terms fixes
//     the index — and the parameters the cite left open, and a binder
//     the principle states after its predicate where a guard applies
//     it (`∀y. y ∈ s ⇒ Q(y)`, read at `∀x. x ∈ s ⇒ F(x) ∈ c` as
//     `Q := λx. F(x) ∈ c`) — at them, and
//     the predicate is the goal abstracted over the index:
//     `λx̄. goal[index := x̄]`. Hypotheses the induction has to carry —
//     the predicate is then `λx̄. (h₁ ∧ … ∧ hₙ) ⇒ goal` — are named with
//     Generalizing; none is gathered.
//
//   - The GOAL's own binders. With no premise stating the guard, the
//     goal has to be the principle's conclusion itself, `∀x̄. G(x̄) ⇒
//     φ(x̄)` with the guard among its antecedents, conjoined or
//     curried, and the predicate is `λx̄. φ(x̄)`: the goal's body without
//     the guard.
//
// Either way the result is the tuple the cite would have spelled, and
// ByInduction runs at it as at a written one: the obligations, the
// terminal close and what is recorded are those of the written cite.

package proof

import (
	"fmt"
	"maps"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// Generalization is the ByInduction argument Generalizing builds: the
// hypotheses a predicate read from the goal carries.
type Generalization struct{ facts []Fact }

// Generalizing names the hypotheses a ByInduction carries into a
// predicate it reads from the goal: resident facts about the index that
// the induction hypothesis must assume at every index, as "for every
// finite s ⊆ c, …" carries `s ⊆ c`. The predicate becomes
// `λx̄. (h₁ ∧ … ∧ hₙ) ⇒ goal`, the facts conjoined in the order given,
// and the terminal close discharges them at the index from the facts
// themselves. It stands among the extras, before the Cases; beside a
// cite that states its predicate it panics — the predicate is written
// there, and so is what it assumes.
func Generalizing(facts ...CiteTarget) Generalization {
	if len(facts) == 0 {
		panic("Generalizing: no fact named — a predicate that carries nothing is the goal alone, which is ByInduction without it")
	}
	g := Generalization{}
	for _, f := range facts {
		g.facts = append(g.facts, targetFact("Generalizing", f))
	}
	return g
}

// PredicateSlot is where a principle's statement binds its predicate:
// the position, among the binders its statement states through its
// guards, of the variable its final consequent applies. A cite or a
// session table that grounds no more than slot binders stops before the
// predicate, and has it read from the goal. ok is false for a statement
// that is no induction principle's; ByInduction's own reading names
// that.
func PredicateSlot(stated core.Term) (slot int, ok bool) {
	binders, matrix := ematch.StripGuardedForalls(stated)
	for {
		_, rest, isImp := ext.MatchesIMPLY(matrix)
		if !isImp {
			break
		}
		matrix = rest
	}
	head, _ := ext.MatchesApply(matrix)
	hv, isVar := head.AsVar()
	if !isVar {
		return 0, false
	}
	for i, b := range binders {
		if b.Equals(hv) {
			return i, true
		}
	}
	return 0, false
}

// motiveFromGoal completes a principle cited before its predicate: the
// same fact at the tuple inductionMotive reads off the leaf. ok is
// false where the cite reaches its predicate, or is not a statement
// this reading takes — ByInduction's reading of the written tuple then
// runs, and names whatever is wrong with it.
func (act _ByInductionAction) motiveFromGoal(s *Script, leaf *GoalStackNode) (Fact, bool) {
	pr := act.principle
	if pr.handle != nil || pr.claim != nil || pr.residentContent != nil || len(pr.named) > 0 {
		return pr, false
	}
	ref := citeReferenceProp(s, pr.target)
	if ref == nil || ref.NumHyps() != 0 {
		return pr, false
	}
	slot, ok := PredicateSlot(ref.Conclusion())
	if !ok || len(pr.witnesses) > slot {
		return pr, false
	}
	var facts []Term
	conjuncts := ext.DecomposesBinaryOp(ext.MatchesAND)
	for _, x := range act.extras {
		target, isTarget := x.(CiteTarget)
		if !isTarget {
			continue
		}
		if content, resident := residentContentAt(target.AsFact(), leaf); resident {
			facts = append(facts, conjuncts(content)...)
		}
	}
	var carried []Term
	for _, f := range act.carried {
		content, resident := residentContentAt(f, leaf)
		if !resident {
			panic(fmt.Sprintf("ByInduction: Generalizing(%s) — a carried hypothesis is a resident fact, whose statement the "+
				"predicate assumes at every index; a cited law is a premise of the cases that use it", f.describe()))
		}
		carried = append(carried, content)
	}
	tuple, err := inductionMotive(ref, pr.witnesses, leaf.Goal, facts, carried, describeInductionTarget(pr))
	if err != nil {
		panic("ByInduction: " + err.Error())
	}
	completed := pr
	completed.witnesses = tuple
	return completed, true
}

// residentContentAt is the statement of a resident fact as leaf holds
// it; ok is false for a fact that is not resident as it stands (a law,
// a ground instance, a self-proving premise).
func residentContentAt(f Fact, leaf *GoalStackNode) (core.Term, bool) {
	if len(f.witnesses) > 0 || len(f.named) > 0 || f.claim != nil {
		return nil, false
	}
	switch {
	case f.handle != nil && f.handle.term != nil:
		return f.handle.contentAt(leaf), true
	case f.residentContent != nil:
		return contentHypTerm("ByInduction", f.residentContent), true
	}
	return nil, false
}

// InductionMotive completes the tuple of an induction principle named
// without its predicate, with no Script in hand — the session's reading
// of a `by_induction` whose table leaves the predicate out, and the
// emitter's test of whether a recorded predicate is the one the goal
// reads. stated is the principle's statement; given its leading
// binders' witnesses in stated order, none past the predicate; goal the
// leaf; facts the statements of the premises named beside the
// principle; carried those of the hypotheses the predicate assumes. The
// tuple comes back in stated order, as Go's At(principle, w…) writes
// it, with the statement typed as that tuple grounds it.
func InductionMotive(stated Prop, given []Term, goal Prop, facts, carried []Term, describe string) ([]Term, Prop, error) {
	if stated.NumHyps() != 0 {
		return nil, nil, fmt.Errorf("the principle carries hypotheses, so its predicate is not read off its statement:\n%s",
			prop.PrintProp(stated))
	}
	slot, ok := PredicateSlot(stated.Conclusion())
	if !ok {
		return nil, nil, fmt.Errorf("%s does not conclude a predicate applied to its index — is this an induction principle?\n  (principle: %s)",
			describe, prop.PrintProp(stated))
	}
	if len(given) > slot {
		return nil, nil, fmt.Errorf("%s is named at %d witness(es), which reaches its predicate (binder %d) — a tuple that states the predicate is read as written",
			describe, len(given), slot+1)
	}
	var split []Term
	conjuncts := ext.DecomposesBinaryOp(ext.MatchesAND)
	for _, f := range facts {
		split = append(split, conjuncts(f)...)
	}
	tuple, err := inductionMotive(stated, given, goal, split, carried, describe)
	if err != nil {
		return nil, nil, err
	}
	return tuple, witnessTypedForm(stated, tuple, goal), nil
}

// inductionMotive reads a principle's predicate from the goal (the file
// comment). given grounds the leading binders the cite named, all of
// them before the predicate; facts are the statements of the premises
// listed beside the principle, conjunct by conjunct; carried the
// statements Generalizing named. The tuple it returns is in stated
// order: given, the parameters a guard fixed, the predicate, and then,
// where a premise fixed the index, every binder after it, the index
// among them; where the goal's own binders are the index, the binders
// stated between the predicate and the index. A goal the reading does
// not fit is an error that says which of the two readings failed at
// what.
func inductionMotive(stated Prop, given []Term, goal Prop, facts, carried []Term, describe string) ([]Term, error) {
	statedBinders, _ := ematch.StripGuardedForalls(stated.Conclusion())
	avoid := utils.EmptySet[core.TermName]()
	note := func(t Term) {
		for _, v := range t.Frees(nil) {
			avoid.Add(v.Name())
		}
	}
	note(goal.Conclusion())
	for h := range goal.HypIter() {
		note(h)
	}
	for _, group := range [][]Term{given, facts, carried} {
		for _, t := range group {
			note(t)
		}
	}
	// The statement as a pattern: its binders as slots, every antecedent
	// (the cases and the guards alike), and the predicate applied.
	binders, antecedents, consequent, slots := ematch.Telescope(stated.Conclusion(), avoid)
	head, args := ext.MatchesApply(consequent)
	hv, _ := head.AsVar()
	slot := -1
	for i, b := range binders {
		if b.Equals(hv) {
			slot = i
		}
	}
	Assert(slot >= 0 && len(given) <= slot) // PredicateSlot read the same statement
	predicate := binders[slot].Name()
	nameOf := func(i int) string { return string(statedBinders[i].Name()) }

	// The index: the binders the predicate is applied to.
	position := map[core.TermName]int{}
	for i, b := range binders {
		position[b.Name()] = i
	}
	isIndex := map[core.TermName]bool{}
	indexArgs := make([]core.TermName, len(args))
	for j, a := range args {
		av, isVar := a.AsVar()
		i, bound := position[av.Name()]
		if !isVar || !bound || i == slot || isIndex[av.Name()] {
			return nil, fmt.Errorf("%s concludes its predicate at %s, which is not one of its binders for each argument — "+
				"the predicate of such a principle is written: At(principle, …, %s)\n  (principle: %s)",
				describe, ext.PrintTerm(consequent), nameOf(slot), prop.PrintProp(stated))
		}
		if i < slot {
			return nil, fmt.Errorf("%s binds its index %s before its predicate %s — the predicate of such a principle is "+
				"written: At(principle, …, %s)\n  (principle: %s)",
				describe, nameOf(i), nameOf(slot), nameOf(slot), prop.PrintProp(stated))
		}
		isIndex[av.Name()] = true
		indexArgs[j] = av.Name()
	}

	// The guards: the antecedents that do not mention the predicate. The
	// rest are the cases.
	conjuncts := ext.DecomposesBinaryOp(ext.MatchesAND)
	mentions := func(t Term, name core.TermName) bool { return t.HasFreeName(name) }
	var guards []Term
	for _, a := range antecedents {
		for _, c := range conjuncts(a) {
			if !mentions(c, predicate) {
				guards = append(guards, c)
			}
		}
	}

	// A polymorphic principle is typed as the reading goes: each match
	// instantiates the type letters it meets, in every guard still to be
	// read.
	types := make([]core.HolType, len(binders))
	for i, b := range binders {
		types[i] = b.Type()
	}
	instantiate := func(batch []core.TypeSubst) {
		if len(batch) == 0 {
			return
		}
		for i := range guards {
			guards[i] = guards[i].TypeSubstitute(batch...)
		}
		for i := range types {
			types[i] = types[i].Substitute(batch...)
		}
	}
	anyType := utils.FullPredicate[core.VarType]
	isSlot := func(v core.VarTerm) bool { return slots.Has(v.Name()) }

	bound := unify.MatchBindings{}
	for i, w := range given {
		var batch []core.TypeSubst
		if !core.MatchTypeInto(types[i], w.Type(), anyType, &batch) {
			return nil, fmt.Errorf("%s grounds binder %s (type %s) at %s (type %s) — the tuple is read in the stated binder order (%s)\n  (principle: %s)",
				describe, nameOf(i), ext.FormatType(types[i]), ext.PrintTerm(w), ext.FormatType(w.Type()),
				statedBinderNames(statedBinders), prop.PrintProp(stated))
		}
		instantiate(batch)
		bound[binders[i].Name()] = w.Core()
	}
	open := func(t Term) bool {
		for _, v := range t.Frees(nil) {
			if slots.Has(v.Name()) {
				if _, done := bound[v.Name()]; !done {
					return true
				}
			}
		}
		return false
	}
	// match reads one guard at one statement: the type letters first,
	// then the slots, consistently with what is bound. The letters are
	// read off the two aligned position by position; a guard that
	// applies a slot — `∀y. y ∈ s ⇒ Q(y)`, a condition on the members —
	// states it at a fact whose body no position aligns with (`F(y) ∈
	// c`), so there the letters are read off the guard's typing shape
	// and the application is left to the term match, which solves it.
	match := func(g int, target Term) bool {
		batch, typed := typematch.TypeOnlyMatch(guards[g], target, isSlot, anyType)
		if !typed {
			shape, stood := typingShape(guards[g], slots, avoid)
			if len(stood) == 0 {
				return false
			}
			standsIn := func(v core.VarTerm) bool { return isSlot(v) || stood.Has(v.Name()) }
			if batch, typed = typematch.TypeOnlyMatch(shape, target, standsIn, anyType); !typed {
				return false
			}
		}
		trial := maps.Clone(bound)
		if !unify.TermMatchWith(guards[g].TypeSubstitute(batch...), target, slots, trial, nil) {
			return false
		}
		bound = trial
		instantiate(batch)
		return true
	}
	indexBound := func() (all, none bool) {
		all, none = true, true
		for name := range isIndex {
			if _, done := bound[name]; done {
				none = false
			} else {
				all = false
			}
		}
		return all, none
	}
	guardText := func() string {
		var out []string
		for _, g := range guards {
			if open(g) || mentionsAny(g, isIndex) {
				out = append(out, ext.PrintTerm(restoreNames(g, binders, statedBinders)))
			}
		}
		if len(out) == 0 {
			return "none — its conclusion is its predicate at every index"
		}
		return strings.Join(out, " ∧ ")
	}

	// openBinder is the refusal for a binder no reading fixed. One stated
	// ahead of the predicate is cited (`At(principle, R)`); one stated
	// after it cannot be cited without the predicate, and is fixed by the
	// fact that states the guard it stands in.
	openBinder := func(i int, left string) error {
		if i < slot {
			return fmt.Errorf("%s: %s leave its parameter %s open — cite the principle at it: At(principle, %s…)\n  (principle: %s)",
				describe, left, nameOf(i), statedBinderNames(statedBinders[:i+1]), prop.PrintProp(stated))
		}
		var on []string
		for _, g := range guards {
			if g.HasFreeName(binders[i].Name()) {
				on = append(on, ext.PrintTerm(restoreNames(g, binders, statedBinders)))
			}
		}
		how := "no guard of the principle mentions it"
		if len(on) > 0 {
			how = "a fact that states its guard " + strings.Join(on, " ∧ ") + " fixes it"
		}
		return fmt.Errorf("%s: %s leave %s open, which the principle binds after its predicate — %s; otherwise cite "+
			"the principle at its predicate: At(principle, %s…)\n  (principle: %s)",
			describe, left, nameOf(i), how, statedBinderNames(statedBinders[:i+1]), prop.PrintProp(stated))
	}

	// First reading: a premise states the guard.
	for g := range guards {
		if !open(guards[g]) {
			continue
		}
		for _, f := range facts {
			if match(g, f) {
				break
			}
		}
	}
	all, none := indexBound()
	if len(args) > 0 && all {
		for i := len(given); i < len(binders); i++ {
			if _, done := bound[binders[i].Name()]; !done && i != slot {
				return nil, openBinder(i, "the premises fix its index, and")
			}
		}
		body := goal.Conclusion()
		if len(carried) > 0 {
			body = ext.Apply(ext.IMPLY, conjoinTerms(carried), body).Core()
		}
		motive, err := abstractOver(body, indexArgs, bound, describe)
		if err != nil {
			return nil, err
		}
		tuple := append([]Term{}, given...)
		for i := len(given); i < len(binders); i++ {
			if i == slot {
				tuple = append(tuple, motive)
				continue
			}
			tuple = append(tuple, bound[binders[i].Name()])
		}
		return tuple, nil
	}
	if !none {
		return nil, fmt.Errorf("%s: the premises listed beside it fix part of its index and not the rest — its guard is %s; "+
			"list the fact that states it, or cite the principle at its predicate: At(principle, …, %s)\n  (principle: %s)",
			describe, guardText(), nameOf(slot), prop.PrintProp(stated))
	}

	// Second reading: the goal is the principle's conclusion.
	if len(carried) > 0 {
		return nil, fmt.Errorf("%s: Generalizing carries hypotheses into a predicate abstracted over an index a premise "+
			"fixes, and no premise listed beside the principle states its guard (%s) — list that fact; a goal that is "+
			"the principle's conclusion already holds what its predicate assumes\n  (principle: %s)",
			describe, guardText(), prop.PrintProp(stated))
	}
	notConclusion := func(why string) error {
		return fmt.Errorf("%s is cited without its predicate, which is then read from the goal, and the goal fits neither "+
			"reading.\n  From a premise: none of the facts listed beside the principle states its guard (%s) — list the "+
			"fact the induction is on.\n  From the goal's binders: %s.\n  Otherwise cite the principle at its predicate: "+
			"At(principle, …, %s).\n  (principle: %s)\n  (goal: %s)",
			describe, guardText(), why, nameOf(slot), prop.PrintProp(stated), ext.PrintTerm(goal.Conclusion()))
	}
	var indexSlots []int
	for i := slot + 1; i < len(binders); i++ {
		if isIndex[binders[i].Name()] {
			indexSlots = append(indexSlots, i)
		}
	}
	body := goal.Conclusion()
	goalVar := map[core.TermName]core.VarTerm{}
	for _, i := range indexSlots {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			return nil, notConclusion(fmt.Sprintf("the goal binds fewer than the %d variable(s) of the index", len(indexSlots)))
		}
		var batch []core.TypeSubst
		if !core.MatchTypeInto(types[i], abs.Var().Type(), anyType, &batch) {
			return nil, notConclusion(fmt.Sprintf("the goal's binder %s (type %s) is not of the index %s's type (%s)",
				string(abs.Var().Name()), ext.FormatType(abs.Var().Type()), nameOf(i), ext.FormatType(types[i])))
		}
		instantiate(batch)
		bound[binders[i].Name()] = abs.Var()
		goalVar[binders[i].Name()] = abs.Var()
		body = abs.Body()
	}
	// The goal's antecedents, as it curries and conjoins them; the guards
	// are taken out of them and what is left is the predicate's body.
	var groups [][]Term
	for {
		ante, rest, isImp := ext.MatchesIMPLY(body)
		if !isImp {
			break
		}
		groups = append(groups, conjuncts(ante))
		body = rest
	}
	taken := make([][]bool, len(groups))
	for i := range groups {
		taken[i] = make([]bool, len(groups[i]))
	}
	for g := range guards {
		if !open(guards[g]) && !mentionsAny(guards[g], isIndex) {
			continue // a guard on the parameters alone: a premise's to discharge
		}
		found := false
	search:
		for i := range groups {
			for j := range groups[i] {
				if !taken[i][j] && match(g, groups[i][j]) {
					taken[i][j], found = true, true
					break search
				}
			}
		}
		if !found {
			return nil, notConclusion(fmt.Sprintf("the principle's guard %s is not among the goal's antecedents",
				ext.PrintTerm(restoreNames(guards[g], binders, statedBinders))))
		}
	}
	// The tuple runs to the predicate and on through the binders stated
	// between it and the index, which a guard among the goal's
	// antecedents fixed; the index stays the goal's own binders. A term
	// such a binder is fixed at stands outside those binders.
	last := slot
	for i := len(given); i < len(binders); i++ {
		name := binders[i].Name()
		if i == slot || isIndex[name] {
			continue
		}
		at, done := bound[name]
		if !done {
			return nil, openBinder(i, "the goal's antecedents")
		}
		if i > slot {
			if len(indexSlots) > 0 && i > indexSlots[0] {
				return nil, fmt.Errorf("%s binds %s after its index, so a tuple that leaves the index to the goal's "+
					"binders cannot reach it — the predicate of such a principle is written: At(principle, …, %s…)\n  (principle: %s)",
					describe, nameOf(i), nameOf(slot), prop.PrintProp(stated))
			}
			for _, v := range goalVar {
				if at.HasFreeName(v.Name()) {
					return nil, notConclusion(fmt.Sprintf("the goal states the principle's %s at %s, which mentions the goal's own binder %s",
						nameOf(i), ext.PrintTerm(at), string(v.Name())))
				}
			}
			last = i
		}
	}
	for i := len(groups) - 1; i >= 0; i-- {
		var kept []Term
		for j, c := range groups[i] {
			if !taken[i][j] {
				kept = append(kept, c)
			}
		}
		if len(kept) > 0 {
			body = ext.Apply(ext.IMPLY, conjoinTerms(kept), body).Core()
		}
	}
	motive := body
	for j := len(indexArgs) - 1; j >= 0; j-- {
		motive = core.Abs(goalVar[indexArgs[j]], motive)
	}
	tuple := append([]Term{}, given...)
	for i := len(given); i <= last; i++ {
		if i == slot {
			tuple = append(tuple, motive)
			continue
		}
		tuple = append(tuple, bound[binders[i].Name()])
	}
	return tuple, nil
}

// typingShape is t as a type match reads it where t applies a slot:
// every application headed by a slot is replaced by a variable of the
// application's type, a name of its own that stands for whatever term
// of that type the target holds there. What is left aligns with the
// target position by position, so its type letters are read as any
// first-order pattern's are; the applications themselves are the term
// match's, which binds the slot to an abstraction of the target. The
// names of the variables that stand in are returned, none where t
// applies no slot.
func typingShape(t Term, slots, avoid utils.Set[core.TermName]) (Term, utils.Set[core.TermName]) {
	stood := utils.EmptySet[core.TermName]()
	fresh := func() core.TermName {
		for i := len(stood); ; i++ {
			name := core.TermName(fmt.Sprintf("ǝapplied_%d", i))
			if !avoid.Has(name) && !slots.Has(name) && !stood.Has(name) && !t.HasFreeName(name) {
				stood.Add(name)
				return name
			}
		}
	}
	var walk func(t Term) Term
	walk = func(t Term) Term {
		if app, isApp := t.AsAppliedTerm(); isApp {
			head, _ := ext.MatchesApply(t)
			if hv, isVar := head.AsVar(); isVar && slots.Has(hv.Name()) {
				return core.Var(fresh(), t.Type())
			}
			return core.Apply(walk(app.Fun()), walk(app.Arg()))
		}
		if abs, isAbs := t.AsAbsTerm(); isAbs {
			return core.Abs(abs.Var(), walk(abs.Body()))
		}
		return t
	}
	return walk(t), stood
}

// abstractOver is the predicate `λx̄. body[index := x̄]` for an index of
// distinct variables: the terms bound to the principle's index binders,
// in the order its conclusion applies the predicate to them.
func abstractOver(body Term, indexArgs []core.TermName, bound unify.MatchBindings, describe string) (Term, error) {
	vars := make([]core.VarTerm, len(indexArgs))
	seen := map[core.TermName]bool{}
	for j, name := range indexArgs {
		v, isVar := bound[name].AsVar()
		if !isVar || seen[v.Name()] {
			var index []string
			for _, n := range indexArgs {
				index = append(index, ext.PrintTerm(bound[n]))
			}
			return nil, fmt.Errorf("%s: the induction is on (%s), which is not a tuple of distinct variables, so the goal "+
				"is not abstracted over it — the predicate of an induction on a compound term (a degree, a cardinality, "+
				"a difference of sets) says how the term enters, and is written: At(principle, …, P, …)",
				describe, strings.Join(index, ", "))
		}
		seen[v.Name()] = true
		vars[j] = v
	}
	// A goal that mentions none of the index is not a predicate of it:
	// the listed fact that fixed the index is about something else.
	mentioned := false
	for _, v := range vars {
		mentioned = mentioned || body.HasFreeName(v.Name())
	}
	if !mentioned {
		var index []string
		for _, v := range vars {
			index = append(index, string(v.Name()))
		}
		return nil, fmt.Errorf("%s: the facts listed beside it fix its index at (%s), which the goal does not mention — "+
			"the first listed fact that states a guard fixes the index, so list the fact the induction is on ahead of "+
			"the others, or cite the principle at its predicate: At(principle, …, P, …)",
			describe, strings.Join(index, ", "))
	}
	motive := body
	for j := len(vars) - 1; j >= 0; j-- {
		motive = core.Abs(vars[j], motive)
	}
	return motive, nil
}

// conjoinTerms is the conjunction of ts, associated to the left.
func conjoinTerms(ts []Term) Term {
	out := ts[0]
	for _, t := range ts[1:] {
		out = ext.Apply(ext.AND, out, t).Core()
	}
	return out
}

// mentionsAny reports whether a free variable of t is named in names.
func mentionsAny(t Term, names map[core.TermName]bool) bool {
	for _, v := range t.Frees(nil) {
		if names[v.Name()] {
			return true
		}
	}
	return false
}

// restoreNames spells a piece of the principle read as a pattern under
// the binder names its statement uses, for a message.
func restoreNames(t Term, slots, stated []core.VarTerm) Term {
	for i, s := range slots {
		for _, v := range t.Frees(nil) {
			if v.Name() == s.Name() {
				t = t.Substitute(core.MakeTermSubst(v, core.Var(stated[i].Name(), v.Type())))
			}
		}
	}
	return t
}
