// induction.go — ByInduction, the closer for induction by CITING a
// principle.
//
// There are two ways a proof runs an induction, and they are
// not variants of one another:
//
//   - `a.Induct(v, cases…)` (derive.go) drives the TACTIC. The
//     principle is the one the datatype comes with, the engine finds it
//     from the induction variable's type, and there is no predicate to
//     write down — the goal itself is the predicate. That is induction
//     over num, list, option.
//
//   - `ByInduction(At(principle, pred, x), …)` CITES a principle as a
//     theorem. The principle is an ordinary ∀-quantified fact — an
//     inductive definition's own induction rule (finite_set.FiniteInduct), a
//     strengthened variant (FiniteInductStrong), a wellfoundedness
//     principle (nat_order.StrongInduction) — at a predicate: the one
//     the cite states, or, where the cite stops before it, the goal
//     read at the index the induction is on (induction_motive.go).
//
// This file is the second one. The move it names is what a paper writes
// as "by induction on s" — and "with P(u) := …" where the predicate is
// not the goal: one predicate, one obligation per case of the
// principle, and a conclusion that follows by applying the principle to
// them.
//
// # What the verb removes
//
// The obligations of a cited induction are not free-standing claims —
// they are the principle's own case hypotheses read at the chosen
// predicate. Writing them by hand means performing the substitution and
// the β-reduction in Go source, which in practice means a Sprintf whose
// format string interpolates the predicate's body at two or three
// places:
//
//	joinsT := func(u string) string { return fmt.Sprintf("finite(%s ∪ %s)", u, t) }
//	joinsTPred := a.Ctx().TermText("λu:(A → bool). " + joinsT("u"))
//	base := a.Have("…", joinsT("∅"), By(…))
//	step := a.Have("…", fmt.Sprintf("∀x:A. ∀u:(A → bool). %s ⇒ %s",
//	    joinsT("u"), joinsT("insert(x, u)")), Derive(…))
//	a.Show("…", By(finite, base, step, At(FiniteInduct, joinsTPred, s)))
//
// Every one of those spellings is DERIVED from the principle and the
// predicate, and the derivation is mechanical — so the proof states the
// same mathematics three times and the reader has to check that the
// three agree. ByInduction computes them instead:
//
//	a.Show("…",
//	    ByInduction(At(FiniteInduct, joinsTPred, s), finite,
//	        Case("∅ contributes no element, so the join is t itself", By(…)),
//	        Case("one more element on the left is one more on the join", Derive(…))))
//
// The predicate is written ONCE, the case claims are the principle's,
// and what remains in the source is what the author actually decided:
// which principle, at which predicate, and why each case holds.
//
// # What it does not remove
//
// The Case LABELS. An obligation's statement is computable; what it
// means in this proof is not, and the labels are where that lives. A
// ByInduction whose labels are "base" and "step" has thrown away the
// only thing the verb could not compute for itself.

package proof

import (
	"context"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// ByInduction closes the current leaf by applying a cited induction
// principle: it proves one obligation per case of the principle, each
// under its own label, and then closes by By over those obligations,
// the principle itself, and whatever else the conclusion needs.
//
//	a.Show("so the induction carries the property to every finite set, and s is one of them",
//	    ByInduction(At(FiniteInduct, sendsToFinite, s), finiteS,
//	        Case("at ∅: the image is that empty set, which is finite outright",
//	            By(noPoints, FiniteRules)),
//	        Case("across insert: one more point in the source is one more in the image",
//	            Derive(func(b *Argument) { … }))))
//
// `principle` is the induction rule AT its predicate — and, where the
// principle carries parameters (an inductive definition minted with a
// parameter states its induction `∀R. ∀P. …`), at those parameters
// first, and where its conclusion quantifies the index, at the index
// the proof is about: an ordinary `At(dep, w…)` whose witnesses follow
// the dep's stated binder order like any other ground cite. The
// remaining arguments are the case bodies as `Case` values, in the
// principle's own case order, plus any extra premises the terminal
// needs: a principle whose conclusion is guarded (`∀a. finite(a) ⇒
// P(a)`) needs the guard discharged, and that hypothesis is an extra.
//
// A cite that stops BEFORE the predicate — the principle bare, or at
// its parameters — has its predicate read from the goal
// (induction_motive.go): the goal abstracted over the index, which the
// extra that states the principle's guard fixes,
//
//	ByInduction(DoDerivableInduct, derivation, Case(…), …)
//
// or, with no such extra, the body of a goal that is the principle's
// conclusion `∀x̄. guard ⇒ φ(x̄)`. Generalizing(h…) among the extras
// names the hypotheses such a predicate carries.
//
// The obligation each Case body must prove is COMPUTED from the
// principle — see inductionObligations — and a Case count that does not
// match panics with the computed obligations printed, which is also the
// fastest way to see what a principle actually asks for.
//
// The recorded proof is exactly what the hand-written spelling records:
// one AssertStep per obligation, then the terminal By. The verb is a
// spelling of that shape, not a new step, so converting a hand-written
// induction whose Haves state the obligations under the PRINCIPLE'S OWN
// binder names leaves the proof tree — and every recorded CNF key —
// alone; an obligation that normalizes to ⊤ (a motive that is the rule
// set's own parameter, whose one-step case reads `R(x, y) ⇒ R(x, y)`)
// is still asserted and still a Case, and costs no key (measured:
// `closure.Closed` replays at its keys and records +0). A Have spelled
// under OTHER binder names (`∀u v.` for a principle's `∀x y.`) is the
// same claim and a different leaf once a Case body Fixes it — the
// Skolem constants carry the binder names and the CNF keys hash them —
// so its keys re-record (measured: the hand-written `closure.Monotone`
// with only its binders renamed misses the same recorded plan).
//
// The principle reaches the terminal By in its STATED form — the form
// the obligations were read off — whatever spelling named it: an entry
// var, a typed instance (statedPrinciple). That is not what
// By makes of a named premise on its own (a partial tuple takes the
// closer's clause form), and a principle cited at its predicate with
// the index left universal is always a partial tuple.
func ByInduction(principle CiteTarget, rest ...any) Action {
	act := _ByInductionAction{principle: targetFact("ByInduction", principle), site: authorCallSite()}
	for _, r := range rest {
		if c, ok := r.(Case); ok {
			act.cases = append(act.cases, c)
			continue
		}
		if len(act.cases) > 0 {
			panic(fmt.Sprintf("ByInduction: extra premise (%T) after a Case — list the "+
				"extras the conclusion needs first, then one Case per obligation, so the "+
				"case order reads against the principle's", r))
		}
		if g, ok := r.(Generalization); ok {
			act.carried = append(act.carried, g.facts...)
			continue
		}
		act.extras = append(act.extras, r)
	}
	if len(act.cases) == 0 {
		panic("ByInduction: no Case bodies — an induction with no obligations to prove is " +
			"a plain cite of the principle, which is By(…, At(principle, w…))")
	}
	return act
}

type _ByInductionAction struct {
	principle Fact
	extras    []any
	// carried are the hypotheses Generalizing named: antecedents of a
	// predicate read from the goal, and premises of the terminal close.
	carried []Fact
	cases   []Case
	// site is the author's ByInduction call (authorCallSite); the By this
	// action builds carries it, so the economy audit names the author's line.
	site string
}

func (act _ByInductionAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("ByInduction: no unsolved leaves remaining (section already proved — extra step in chain?)" + closedLeafNote(root))
	}
	principle, read := act.motiveFromGoal(s, anchor)
	if !read && len(act.carried) > 0 {
		panic(fmt.Sprintf("ByInduction: Generalizing names hypotheses for a predicate read from the goal, and %s is "+
			"cited at its predicate — what the predicate assumes is written in it",
			describeInductionTarget(act.principle)))
	}
	obligations := inductionObligations(s, principle, len(act.cases), anchor.Goal)

	a := &Argument{s: s, cur: anchor, parent: s.curArg}
	defer s.enterArgument(a)()
	premises := make([]any, 0, len(act.extras)+len(act.carried)+len(act.cases)+1)
	premises = append(premises, act.extras...)
	for _, h := range act.carried {
		premises = append(premises, h)
	}
	for i, c := range act.cases {
		premises = append(premises, a.Have(c.Label, obligations[i], c.Body...))
	}
	premises = append(premises, statedPrinciple(s, principle))

	func() {
		defer func() {
			if r := recover(); r != nil {
				panic(fmt.Sprintf("ByInduction(%s): %v", describeInductionTarget(principle), r))
			}
		}()
		closeBy := By(premises...).(_ByAction)
		closeBy.site = act.site
		closeBy.applyAction(s, a.cur)
	}()
	requireBlockClosed("ByInduction", anchor)
}

// statedPrinciple is the principle as the terminal By installs it: the
// STATED form the obligations were read off, at the same tuple. A
// spelling that carries a clause form (premiseClauseForm: an entry
// var, a typed instance, a law read at an instance) is
// unwrapped to its reference form (citeReferenceProp) — the served
// certificate, a typed instance's stated half — which the cite dispatch
// installs verbatim. A certificate, a Prop or a proved section installs
// verbatim already.
//
// Left as a named premise, By would install the closer's CLAUSE form:
// a witnessed named premise takes its stated form only where the tuple
// grounds every guarded binder and every guard is resident (step_by.go,
// statedGuardsSupplied), and a principle cited at its predicate with
// the index left universal is always a partial tuple. The clause
// prefix is in Normalize's order, which the author never sees — where
// the index leads the predicate the tuple cannot ground it at all
// (nat_order.StrongInduction's clause form is `∀n.∀P.…`, and its one
// witness landed on n) — and the clause form has dissolved the ⇒ the
// close is the discharge of, which at a transparent predicate the
// refuter cannot recover. Neither is the verb's business: it computed
// the obligations from the stated antecedent, and the terminal is that
// antecedent's modus ponens.
func statedPrinciple(s *Script, principle Fact) Fact {
	if premiseClauseForm(s, principle.target) == nil {
		return principle
	}
	return Fact{target: citeReferenceProp(s, principle.target), witnesses: principle.witnesses}
}

// inductionObligations reads a cited induction principle's case
// obligations off its own statement, at the tuple the cite grounds it
// at.
//
// The shape it expects is the one every induction principle has:
//
//	∀params… ∀P … . H₁ ∧ … ∧ Hₙ ⇒ conclusion
//
// with the hypotheses conjoined or curried as an ⇒-chain — both are
// flattened. The obligations are the hypotheses that mention the
// predicate P: those are the principle's cases. A hypothesis that does
// not — `finite(s)`, a guard on the index, `presheaf(T, F, res)` on the
// parameters — is a premise of the principle, not a case of the
// induction, and the terminal By discharges it from the extras the
// author lists before the Cases, as it discharges a guard the
// conclusion states. Which binder is the predicate is read off
// the conclusion (principlePredicate); whether the conclusion is `P(x)`,
// `∀x. P(x)` or a guarded `∀x. finite(x) ⇒ P(x)` is the principle's
// business, and the terminal By closes against it.
//
// # Reading the tuple
//
// The obligations are the cases at the leading binders the tuple
// grounds — the predicate, and every parameter stated before it. A
// parameterized inductive definition states its rules over the
// parameter (`R(x, y) ⇒ P(x, y)` is transitive closure's first rule),
// so the parameter occurs in the obligations exactly as the predicate
// does, and an obligation read at the predicate alone would carry the
// principle's own bound `R` as a free name. So every leading binder the
// tuple reaches is substituted, and a leading binder the cases mention
// that the tuple does not reach is an error, not a wider obligation; a
// binder only a premise mentions (the index a guard is about) is the
// terminal's to ground.
//
// The tuple is read the way the terminal By will ground it, and by the
// same function (reorderWitnessesToInstall over the statement's guarded
// prefix): in the STATED binder order — parameters, predicate, indices
// — with a tuple whose positional reading is ill-typed permuted by type
// where the binder types settle it. That last lane is what lets peano
// write `At(Induction, point, pred)` against a principle stated
// `∀P. … ⇒ ∀n. P(n)`: `n` is bound twice there, so no slot is
// name-addressable and the grounding falls through to positional, and
// the type permutation reads the tuple right in both spellings. A
// parameter and a predicate of one type (`A → A → bool` both, for a
// relation's closure) are told apart by POSITION, which is exact because
// the statement names them, and the same reading the grounding makes —
// so the obligations are read at the instance the terminal applies.
//
// Every obligation is β-collapsed, because substituting a λ-predicate
// leaves redexes exactly where the author would otherwise have written
// the reduced form by hand: `(λu. finite(u ∪ t))(∅)` becomes
// `finite(∅ ∪ t)`, which is the claim as a person states it.
//
// The obligations carry the PRINCIPLE'S OWN binder names (finite_set.FiniteInduct
// states its step at `∀x. ∀s.`, so that is what the step case receives
// and what a `b.Fix()` in the body names its Skolem after). They are
// the principle's cases; naming them after the principle is what makes
// two members citing it produce the same obligation.
//
// goal is the leaf the induction closes: a polymorphic principle is
// typed by its tuple as the grounding types it (witnessTypedForm), and
// the goal decides only a type variable the tuple leaves open.
func inductionObligations(s *Script, principle Fact, want int, goal Prop) []Prop {
	ref := citeReferenceProp(s, principle.target)
	if principle.handle != nil {
		panic("ByInduction: the principle is a resident hypothesis — ByInduction reads the " +
			"obligations off a CITED principle's statement; a principle already assumed is an " +
			"ordinary premise, and its cases are ordinary Haves")
	}
	if ref == nil {
		panic(fmt.Sprintf("ByInduction: cannot read %s as a statement — an induction principle "+
			"must be a named dep, a registry entry, a certificate or a proved sibling section, "+
			"because the case obligations are computed from its own statement",
			describeInductionTarget(principle)))
	}
	if ref.NumHyps() != 0 {
		panic(fmt.Sprintf("ByInduction: the principle carries hypotheses, so its obligations are "+
			"not its statement's antecedent:\n%s", prop.PrintProp(ref)))
	}
	if len(principle.named) > 0 {
		panic(fmt.Sprintf("ByInduction: %s pins a binder by name (Where) — ByInduction reads its "+
			"obligations off the tuple a positional grounding supplies, in the principle's stated "+
			"binder order (parameters, then the predicate, then the indices), and its terminal By "+
			"grounds that same tuple; spell the cite At(principle, w…)",
			describeInductionTarget(principle)))
	}

	// The statement as the grounding installs it: a polymorphic
	// principle typed by its tuple, an explicit instance as it is.
	stated := ref
	if len(principle.witnesses) > 0 && !isExplicitInstance(principle.target) && ext.PropHasTypeVars(ref) {
		stated = witnessTypedForm(ref, principle.witnesses, goal)
	}
	obligations, err := obligationsOfPrinciple(ref, stated, principle.witnesses, describeInductionTarget(principle))
	if err != nil {
		panic("ByInduction: " + err.Error())
	}
	if len(obligations) != want {
		var b strings.Builder
		fmt.Fprintf(&b, "ByInduction: %d Case body(ies) provided, but %s asks for %d obligation(s)",
			want, describeInductionTarget(principle), len(obligations))
		for i, o := range obligations {
			fmt.Fprintf(&b, "\n  obligation %d: %s", i, prop.PrintProp(o))
		}
		fmt.Fprintf(&b, "\n  (principle: %s)", prop.PrintProp(stated))
		panic(b.String())
	}
	return obligations
}

// InductionObligations reads an induction principle's case obligations
// off its statement at a witness tuple, with no Script in hand — the
// session's reading of the principle its `by_induction` cites. stated
// is the principle as the grounding installs it, a polymorphic one
// already typed by its tuple; witnesses is the tuple in the STATED
// binder order, as Go's At(principle, w…) writes it; describe names the
// principle in the error. The obligations come back in the principle's
// own order, under its own binder names, β-collapsed — the claims Go's
// verb asserts one Have each.
func InductionObligations(stated Prop, witnesses []Term, describe string) ([]Prop, error) {
	if stated.NumHyps() != 0 {
		return nil, fmt.Errorf("the principle carries hypotheses, so its obligations are not its statement's antecedent:\n%s",
			prop.PrintProp(stated))
	}
	return obligationsOfPrinciple(stated, stated, witnesses, describe)
}

// obligationsOfPrinciple is the reading both doors share: ref is the
// statement whose binder order the tuple follows, stated the form the
// grounding installs (ref itself, or ref typed by the tuple).
func obligationsOfPrinciple(ref, stated Prop, witnesses []Term, describe string) ([]Prop, error) {
	// The leading ∀-prefix (parameters and predicate), the antecedent
	// the obligations come from, and the conclusion.
	body := stated.Conclusion()
	var leading []core.VarTerm
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			break
		}
		leading = append(leading, abs.Var())
		body = abs.Body()
	}
	var antecedents []Term
	for {
		ant, concl, ok := ext.MatchesIMPLY(body)
		if !ok {
			break
		}
		antecedents = append(antecedents, ant)
		body = concl
	}
	if len(antecedents) == 0 {
		return nil, fmt.Errorf("%s has no antecedent to read cases off — its statement's "+
			"conclusion is not an implication, so there are no obligations. Is this an induction "+
			"principle?\n  (principle: %s)",
			describe, prop.PrintProp(stated))
	}
	pred, err := principlePredicate(describe, stated, leading, body)
	if err != nil {
		return nil, err
	}
	decompose := ext.DecomposesBinaryOp(ext.MatchesAND)
	var cases []Term
	for _, ant := range antecedents {
		for _, h := range decompose(ant) {
			if mentionedIn(pred, []Term{h}) {
				cases = append(cases, h)
			}
		}
	}

	if len(witnesses) == 0 {
		return nil, fmt.Errorf("%s is cited bare — ByInduction computes its case "+
			"obligations from the principle AT a predicate, so ground the cite: "+
			"At(principle, %s…) where the predicate %s has type %s and every parameter stated "+
			"before it comes first",
			describe, statedBinderNames(leading), string(pred.Name()),
			ext.FormatType(pred.Type()))
	}

	// The tuple, read as the terminal grounds it: onto the statement's
	// guarded prefix, in stated order, permuted by type where the
	// positional reading is ill-typed and the types settle it.
	prefix, _ := ematch.StripGuardedForalls(stated.Conclusion())
	ordered := reorderWitnessesToInstall(ref, stated.Conclusion(), witnesses)
	if len(ordered) > len(prefix) {
		return nil, fmt.Errorf("%s grounds %d witnesses, but its statement binds %d "+
			"(%s) — the terminal By could not ground that tuple either\n  (principle: %s)",
			describe, len(ordered), len(prefix), statedBinderNames(prefix),
			prop.PrintProp(stated))
	}
	for i, w := range ordered {
		if !prefix[i].Type().Equals(w.Type()) {
			return nil, fmt.Errorf("%s grounds binder %s (type %s) at %s (type %s) — the "+
				"tuple is read in the stated binder order (%s); a principle cited across types "+
				"goes through AtTypes\n  (principle: %s)%s",
				describe, string(prefix[i].Name()), ext.FormatType(prefix[i].Type()),
				ext.PrintTerm(w), ext.FormatType(w.Type()), statedBinderNames(prefix), prop.PrintProp(stated),
				witnessOrderNote(ref, stated.Conclusion(), witnesses))
		}
	}
	grounded := len(ordered)
	if grounded > len(leading) {
		grounded = len(leading)
	}
	subst := make([]core.TermSubst, 0, grounded)
	for i := 0; i < grounded; i++ {
		subst = append(subst, core.MakeTermSubst(leading[i], ordered[i].Core()))
	}
	for i := grounded; i < len(leading); i++ {
		v := leading[i]
		if !mentionedIn(v, cases) {
			continue
		}
		what := "parameter"
		if v.Equals(pred) {
			what = "predicate"
		}
		return nil, fmt.Errorf("%s grounds %d witness(es), which stops before the "+
			"principle's %s %s (binder %d of its stated prefix %s) — the cases mention it, so the "+
			"obligations cannot be read until the cite reaches it: At(principle, %s…)",
			describe, len(ordered), what, string(v.Name()), i+1,
			statedBinderNames(leading), statedBinderNames(leading[:i+1]))
	}

	obligations := make([]Prop, 0, len(cases))
	for _, h := range cases {
		obligations = append(obligations, core.MakeProp(ext.BetaCollapse(context.Background(), h.Substitute(subst...))))
	}
	return obligations, nil
}

// principlePredicate identifies the principle's predicate among its
// leading binders: the one applied at the head of the statement's
// final consequent, past the conclusion's own binders and guards.
//
// That is what the predicate IS — the binder whose instances the
// principle concludes. A parameter never stands there: transitive
// closure's induction concludes `∀x0 x1. transitive_closure(R, x0, x1)
// ⇒ P(x0, x1)`, where the parameter `R` occurs only under the minted
// constant and the head is `P`. Reading the predicate off the CASES
// instead (the binder the cases apply) was right for every
// parameter-free principle and wrong for every parameterized one,
// whose first rule applies the parameter too.
func principlePredicate(describe string, stated Prop, leading []core.VarTerm, conclusion Term) (core.VarTerm, error) {
	body := conclusion
	for {
		if abs := ext.MatchesFORALL(body); !abs.IsZero() {
			body = abs.Body()
			continue
		}
		if _, rest, ok := ext.MatchesIMPLY(body); ok {
			body = rest
			continue
		}
		break
	}
	head, _ := ext.MatchesApply(body)
	hv, ok := head.AsVar()
	if !ok {
		return core.VarTerm{}, fmt.Errorf("%s concludes %s, whose head is not a variable — an "+
			"induction principle concludes its predicate applied to the index, P(x̄), and that "+
			"head is what the obligations are read at\n  (principle: %s)",
			describe, ext.PrintTerm(body), prop.PrintProp(stated))
	}
	for _, v := range leading {
		if v.Equals(hv) {
			return v, nil
		}
	}
	return core.VarTerm{}, fmt.Errorf("%s concludes %s, headed by %s, which is not one of its "+
		"leading binders (%s) — a variable the conclusion binds itself is an index, not the "+
		"predicate\n  (principle: %s)",
		describe, ext.PrintTerm(body), string(hv.Name()),
		statedBinderNames(leading), prop.PrintProp(stated))
}

// mentionedIn reports whether v occurs free in any of the terms.
func mentionedIn(v core.VarTerm, terms []Term) bool {
	for _, t := range terms {
		for _, fv := range t.Frees(nil) {
			if fv.Equals(v) {
				return true
			}
		}
	}
	return false
}

// statedBinderNames spells a binder list for a panic message.
func statedBinderNames(binders []core.VarTerm) string {
	names := make([]string, len(binders))
	for i, b := range binders {
		names[i] = string(b.Name())
	}
	return strings.Join(names, ", ")
}

// describeInductionTarget names the principle for a panic message,
// reusing the Fact's own description (which knows how to print a dep
// name, an entry, a certificate or a section).
func describeInductionTarget(f Fact) string { return f.describe() }
