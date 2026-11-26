/**
 * file: denote_tactics.go
 *
 * This file provides the following tactics:
 *
 * - denoteTactic: Simplifies complex expressions by introducing new variables for
 *    frequently occurring subterms. It analyzes goals to identify recurring complex
 *    expressions, introduces variables to represent them, and rewrites the goal
 *    accordingly. This reduces redundancy and makes proofs more manageable.
 *
 * - hilbertDenoteTactic: Handles Hilbert ε terms by introducing new variables
 *    and appropriate existential constraints. It transforms terms containing ε
 *    operators into equivalent forms with normal variables plus existential theorems,
 *    which are typically easier to work with in formal proofs.
 *
 * Supporting functions:
 * - hilbertDenoteTransform: Core transformation function for Hilbert ε terms
 */

package tactic

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

/**
 * DenoteTactic creates a tactic that simplifies expressions by introducing new variables
 * for frequently occurring complex subterms.
 *
 * This higher-order function:
 * 1. Takes a size threshold parameter to control which subterms are considered for replacement
 * 2. Returns a tactic function that analyzes goals and identifies frequent complex subterms
 * 3. The returned tactic introduces a new variable for the identified subterm and rewrites
 *    the goal to use this variable instead of the complex expression
 *
 * The tactic works through the following steps:
 * 1. Collects all hypotheses and (if applicable) the negated conclusion
 * 2. Records any beta-reductions applied to hypotheses for later reconstruction
 * 3. Combines hypotheses into a conjunction and analyzes for frequent subterms
 * 4. Skips simple abstractions; a λ-abstraction or set comprehension a hypothesis
 *    already names is folded into that name (foldNamed), any other named value left
 *    to the refuter
 * 5. Introduces a new variable x with equation x = s (where s is the identified subterm)
 * 6. Rewrites the conjunction using beta-equivalence and the introduced equation
 * 7. Decomposes the rewritten conjunction back into individual hypotheses
 * 8. Creates a new subgoal with the rewritten hypotheses plus the new equation
 *
 * The reconstruction function:
 * 1. Substitutes the original subterm s for the introduced variable x
 * 2. Applies beta-reduction and other necessary transformations
 * 3. Restores the original hypotheses through recorded beta-equivalences
 * 4. Handles negated conclusions appropriately if present
 *
 * This tactic is especially useful for simplifying large expressions with repeated
 * subterms, making proofs more manageable by reducing redundancy and complexity.
 *
 * Parameters:
 *   - sizeThreshold: Minimum size of subterms to consider for replacement
 *
 * Returns:
 *   - A Tactic function that performs denotation-based simplification
 */
func DenoteTactic(sizeThreshold int) Tactic {
	return DenoteTacticRecording(sizeThreshold, nil)
}

// DenoteSelection is what a denote firing actually DID: the subterm it
// named and the variable name it minted. The heuristic modes fill one
// through the *Recording entry points so the caller can record the
// choice instead of the recipe that produced it — see
// prover/proof/step.go's _AutoDenote.
type DenoteSelection struct {
	// Term is the named subterm (for the Hilbert mode, the ε-term the
	// step abstracts).
	Term Term
	// Name is the minted variable's name, AFTER collision avoidance —
	// the name an explicit replay must reuse verbatim.
	Name string
}

// DenoteTacticRecording is DenoteTactic with an output sink: when the
// heuristic fires, *sel records the subterm it selected and the variable
// it minted. Search behaviour is identical either way — sel only
// observes. Pass nil for the plain tactic.
func DenoteTacticRecording(sizeThreshold int, sel *DenoteSelection) Tactic {
	return func(goal Prop) *SubGoals {
		hyps, _ := denoteHyps(goal)
		// The heuristic reads values, not spellings: a fact spelled with a
		// redex, `e = «E»(f)` for a λ-abbreviation E, holds the value the
		// goal spells reduced.
		for i := range hyps {
			hyps[i] = betaNormal(hyps[i])
		}
		s := ext.FrequentSubTerms(sizeThreshold, hyps...)

		// If no suitable subterm found, or subterm is simple abstraction, don't apply this tactic
		if s == nil || ext.IsSimpleAbs(s) {
			return nil
		}
		return denoteTerm(goal, s, "", sel, denoteSearch)
	}
}

// DenoteComprehensionTactic is the conditioning stage's extended
// denote trigger: a set comprehension
// — a set_comprehension-headed application — is an opaque blob the refuter can
// only fail on ("cannot rewrite inside a set_comprehension", Wall #3), whatever
// its size, so it is denoted into an atom regardless of the size
// threshold. One candidate per firing; the caller loops to fixpoint.
//
// Candidate selection, deterministic: the LARGEST set_comprehension-headed
// application among the hyps and the negated conclusion (first found
// in hyp-order preorder wins a size tie) that
//   - carries no free occurrence of an enclosing binder's variable
//     (a comprehension under ∀ whose body mentions the bound var
//     cannot be named at the top level), and
//   - is not already denoted — it α-equals no var-equation hyp's RHS
//     (this also makes the firing loop self-terminating: each firing
//     adds exactly such an equation, and it covers the author's own
//     explicit denote, whose named term must not be re-named).
func DenoteComprehensionTactic() Tactic {
	return DenoteComprehensionTacticRecording(nil)
}

// DenoteComprehensionTacticRecording is DenoteComprehensionTactic with
// the DenoteSelection sink (see DenoteTacticRecording).
func DenoteComprehensionTacticRecording(sel *DenoteSelection) Tactic {
	return func(goal Prop) *SubGoals {
		hyps, _ := denoteHyps(goal)
		s := comprehensionCandidate(goal, hyps)
		if s == nil {
			return nil
		}
		return denoteTerm(goal, s, "", sel, denoteSearch)
	}
}

func comprehensionCandidate(goal Prop, hyps []Term) Term {
	// The already-denoted filter: RHSs of resident var-equations.
	var denoted []Term
	for i := range goal.NumHyps() {
		if l, r, ok := MatchesEQ(goal.Hyp(i)); ok {
			if _, isVar := l.AsVar(); isVar {
				denoted = append(denoted, r)
			}
		}
	}
	var best Term
	var visit func(t Term, env []VarTerm)
	visit = func(t Term, env []VarTerm) {
		if app, ok := t.AsAppliedTerm(); ok {
			if isComprehensionApp(t) && (best == nil || t.Size() > best.Size()) {
				capturing := false
				for _, v := range env {
					if t.HasFree(v) {
						capturing = true
						break
					}
				}
				if !capturing && !utils.Any(denoted, t.AlphaEquals) {
					best = t
				}
			}
			visit(app.Fun(), env)
			visit(app.Arg(), env)
			return
		}
		if abs, ok := t.AsAbsTerm(); ok {
			visit(abs.Body(), append(env, abs.Var()))
		}
	}
	for _, h := range hyps {
		visit(h, nil)
	}
	return best
}

// isComprehensionApp reports whether t is an application whose spine
// head is the set_comprehension constant — the set-builder constructor (comprehension_spec
// lives inside its body, so the set_comprehension application covers both heads
// the Wall #3 class names).
func isComprehensionApp(t Term) bool {
	head := t
	for {
		app, ok := head.AsAppliedTerm()
		if !ok {
			break
		}
		head = app.Fun()
	}
	c, ok := head.AsConst()
	return ok && c.Meta().Name() == "set_comprehension"
}

// denoteMode says what a denote firing does when the term it was asked
// to name turns out not to occur in the goal.
type denoteMode int

const (
	// denoteSearch — the heuristic picked the term off these very hyps,
	// so a miss can only be the DenoteRewrite unifier declining an
	// abstracted selection. Legacy behaviour: name it anyway (the
	// equation joins the hyps, nothing is rewritten). Recorded proofs
	// depend on this happening.
	denoteSearch denoteMode = iota
	// denoteExplicit — a caller named the term. A miss is a contract
	// violation: panic here, where the term is still on the page.
	denoteExplicit
	// denoteOptional — a caller named the term as a SHAPING preamble
	// that may legitimately meet leaves without it (By's Broadcast fan).
	// A miss declines the step; the By checks that the shaping applied
	// somewhere.
	denoteOptional
)

// DenoteTermTactic is the EXPLICIT form of DenoteTactic: it names the
// GIVEN subterm by the GIVEN variable name instead of re-deriving a
// choice from a size threshold. This is what a recorded denote replays
// as, and what a hand-written proof spells — "let name = term".
//
// Panics (loudly, at this step) when the goal's hypotheses / negated
// conclusion do not contain the term, or when the name collides with a
// variable already free in them. Both are the whole point: a denote
// whose term drifted out from under it must fail HERE, not surface a
// hundred steps later as a refuter cache miss.
//
// An empty name mints the default α₀ (collision-avoided), matching the
// heuristic's naming — the form the search stage uses when it has no
// mathematical name to offer.
func DenoteTermTactic(term Term, name string) Tactic {
	return denoteTermTactic(term, name, denoteExplicit)
}

// DenoteTermTacticOptional is DenoteTermTactic that DECLINES (returns
// nil) instead of panicking when the goal does not contain the term —
// the shaping-preamble flavor, for a caller that runs the same denote
// across a fan of leaves and checks elsewhere that it landed at all.
func DenoteTermTacticOptional(term Term, name string) Tactic {
	return denoteTermTactic(term, name, denoteOptional)
}

func denoteTermTactic(term Term, name string, mode denoteMode) Tactic {
	return func(goal Prop) *SubGoals {
		if term == nil {
			panic("DenoteTermTactic: nil term")
		}
		if ext.IsSimpleAbs(term) {
			panic(fmt.Sprintf("DenoteTermTactic: %s is a simple abstraction — "+
				"naming it buys nothing", ext.PrintTerm(term)))
		}
		return denoteTerm(goal, term, name, nil, mode)
	}
}

// LetTermTactic is the DEFINITIONAL denote — "let name := term" — the
// goal-preserving twin of DenoteTermTactic. The equation `name = term`
// joins the hypotheses, every occurrence of the term in the hypotheses
// and in the CONCLUSION becomes the name, and the goal keeps its form:
// the conclusion is not negated into the hypotheses. The term need not
// occur anywhere — a definition names what the argument is about to
// build with, and then the equation is all that is added. Panics when
// the name is already free in the goal.
//
// Soundness is instantiation: a proof of `Γ[x], x = s ⊢ C[x]` with x
// fresh is, at x := s, a proof of `Γ, s = s ⊢ C`, and s = s is
// reflexivity.
func LetTermTactic(term Term, name string) Tactic {
	return func(goal Prop) *SubGoals {
		if term == nil {
			panic("LetTermTactic: nil term")
		}
		if name == "" {
			panic("LetTermTactic: a name is required")
		}
		return letTerm(goal, term, name)
	}
}

func letTerm(goal Prop, s Term, name string) *SubGoals {
	hyps := goal.Hyps()
	concl := goal.Conclusion()

	// Already named by a resident equation: nothing to define. The
	// step declines, as a denote of a denoted term does.
	for _, h := range hyps {
		if l, r, ok := MatchesEQ(h); ok {
			if _, ok := l.AsVar(); ok && r.AlphaEquals(s) {
				return nil
			}
			if _, ok := r.AsVar(); ok && l.AlphaEquals(s) {
				return nil
			}
		}
	}

	// Record hypotheses after deepBeta, for the reconstruction.
	hBetas := make([]*PropWrapper, 0, len(hyps))
	for _, h := range hyps {
		if w := prop.DeepBeta(h); w != nil {
			hBetas = append(hBetas, w.LeftAssume())
		}
	}

	x := denoteVar(s, name, append(utils.Clone(hyps), concl), denoteExplicit)
	d, rewrite := Eq(x, s), prop.DenoteRewrite(x, s)
	newHyps := utils.Clone(hyps)
	for i, h := range hyps {
		if w := rewrite(h); w != nil {
			Assert(w.NumHyps() == 1 && w.Hyp(0).Equals(d))
			newHyps[i] = Rhs(w)
		}
	}
	newConcl := concl
	if w := rewrite(concl); w != nil {
		Assert(w.NumHyps() == 1 && w.Hyp(0).Equals(d))
		newConcl = Rhs(w)
	}
	goal0 := MakeProp(newConcl, append(utils.Clone(newHyps), d)...)

	reconstruct := func(thms ...Prop) Prop {
		// Instantiate the name at the term; the definition becomes s = s.
		p := core.PropTermInst(thms[0], ext.MakeTermSubst(x, s))
		p = prop.Refl(s).MaybeDeriveTrans(p)
		p = WrapProp(p).Rewrite(prop.DeepBeta)
		for _, h := range hBetas {
			p = h.MaybeDeriveTrans(p)
		}
		// DenoteRewrite may leave η-expanded forms; bridge each
		// hypothesis and the conclusion back to its original spelling.
		// A hypothesis the goal holds is no image to bridge (denoteTerm).
		for _, origHyp := range goal.Hyps() {
			if !p.HasHyp(origHyp) {
				for h := range p.HypIter() {
					if goal.HasHyp(h) {
						continue
					}
					if eq := prop.BetaEtaRefl(origHyp, h); eq != nil {
						p = eq.LeftAssume().DeriveTrans(p)
						break
					}
				}
			}
		}
		if !p.Conclusion().Equals(concl) {
			eq := prop.BetaEtaRefl(concl, p.Conclusion())
			switch {
			case eq != nil:
				p = eq.EqSym().EqMP(p)
			case p.Conclusion().Equals(F):
				// A child closed by contradiction concludes ⊥ where the
				// goal does not. Over the goal's hypotheses that theorem
				// is stronger than the goal as it stands, and it has no
				// conclusion to bridge.
			default:
				panic(fmt.Sprintf("let(%s): the reconstructed conclusion %s is not βη-equal to the goal's %s",
					name, ext.PrintTerm(p.Conclusion()), ext.PrintTerm(concl)))
			}
		}
		return p
	}
	// Each hypothesis descends from its own slot, rewritten through the
	// definition or not; the definition is new.
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, newHyps)}, goal0)
}

// denoteHyps is the denote stages' view of a goal: its hypotheses plus
// the negated conclusion (nil when the goal is already ⊥). The returned
// slice is safe to append to.
func denoteHyps(goal Prop) ([]Term, Term) {
	hyps := goal.Hyps()
	var negConcl Term
	if !goal.Conclusion().Equals(F) {
		negConcl = Not(goal.Conclusion())
		hyps = append(hyps, negConcl)
	}
	return hyps, negConcl
}

// denoteVar mints the denoting variable. An empty name takes the
// heuristic's α₀, renamed past every name the goal spells; a given name
// is used VERBATIM, and a collision is never silently renamed away —
// under an explicit denote the name is part of the record, so renaming
// it would move the very goal keys the explicit form exists to pin. A
// given name collides only with a variable FREE in the goal. A name the
// goal merely binds — the ∃ whose witness the author is naming, a λ in
// a resident equation — is the author's spelling to honour: where the
// denoted term occurs under such a binder, the rewrite renames the
// binder apart (prop.DenoteRewrite), so the name never meets it.
//
// What a collision MEANS depends on the mode. Under denoteExplicit the
// author named a variable the goal already has: a panic. Under
// denoteOptional the caller is a By shaping running across a FAN of
// leaves, and the name is free on this leaf precisely because the
// shaping already fired on the branch it was split from — "already
// done here", so the step declines (nil). The By's own end-of-close
// check is what catches a shaping that applied nowhere at all.
func denoteVar(s Term, name string, avoid []Term, mode denoteMode) core.VarTerm {
	if name == "" {
		return core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), s.Type()).
			RenameToAvoid(avoid...)
	}
	x := core.Var(TermName(name), s.Type())
	if utils.Any(avoid, utils.Curry(Term.HasFreeName, x.Name())) {
		if mode == denoteOptional {
			return core.VarTerm{}
		}
		panic(fmt.Sprintf("denote: the name %q is already free in the goal — "+
			"pick a name the argument does not already use", name))
	}
	return x
}

// denoteTerm is the shared body of every denote firing: name `s` by a
// fresh variable, rewrite the goal's hypotheses (and negated conclusion)
// through the resulting equation, and carry the reconstruction that
// undoes the naming. `name` empty ⇒ mint α₀; `sel` non-nil ⇒ record what
// was chosen; `mode` decides what a term the goal does not contain
// means (see denoteMode).
func denoteTerm(goal Prop, s Term, name string, sel *DenoteSelection, mode denoteMode) *SubGoals {
	hyps, negConcl := denoteHyps(goal)

	// Record hypotheses after applying deepBeta, used for later reconstruction of original proposition
	hBetas := make([]*PropWrapper, 0, len(hyps))
	for _, h := range hyps {
		if w := prop.DeepBeta(h); w != nil {
			hBetas = append(hBetas, w.LeftAssume())
		}
	}

	// A value the goal already names — a hypothesis `v = s` or `s = v`,
	// v a variable, its value read β-normal — takes no new variable. A
	// λ-abstraction or a set comprehension so named is denoted BY that
	// name: the clause pipeline reads the equation pointwise, and the
	// pointwise clauses — split further where the body is a COND or a
	// connective — reach none of the value's other occurrences, so they
	// are folded into v here and the equation stands as spelled
	// (foldNamed). Any other named value is left as it is: the refuter
	// folds a first-order equation itself, and recovers a λ-free
	// function equation from its pointwise form (ext/clause, FUNEXT).
	if v, naming := namedBy(hyps, s); !v.IsZero() {
		if _, isAbs := s.AsAbsTerm(); !isAbs && !isComprehensionApp(s) {
			return nil
		}
		return foldNamed(goal, s, v, naming, sel, mode)
	}

	// Introduce new variable x and create equation x = s
	x := denoteVar(s, name, hyps, mode)
	if x.IsZero() {
		return nil // optional mode, name already taken on this leaf
	}

	// Apply DenoteRewrite with denote equation x = s to the conjunction
	newHyps := utils.Clone(hyps)
	d, rewrite := Eq(x, s), prop.DenoteRewrite(x, s)
	hit := false
	for i, h := range hyps {
		if w := rewrite(h); w != nil {
			Assert(w.NumHyps() == 1 && w.Hyp(0).Equals(d))
			newHyps[i] = Rhs(w)
			hit = true
		}
	}
	if !hit {
		switch mode {
		case denoteExplicit:
			panic(fmt.Sprintf("denote(%s): the term does not occur in the goal's "+
				"hypotheses or negated conclusion — nothing to name\n(goal: %s)",
				ext.PrintTerm(s), prop.PrintProp(goal)))
		case denoteOptional:
			return nil
		}
		// denoteSearch. The heuristic can select an ABSTRACTED subterm (a
		// λ-closure over the binders it sits under) that DenoteRewrite's
		// unifier then fails to place back in any hypothesis. The firing
		// degenerates to "add the equation, rewrite nothing" — useless but
		// harmless, and recorded proofs in the corpus depend on it
		// happening, so it stays. It is NOT recorded as an explicit
		// choice: replaying it as one would hit the panic above.
		sel = nil
	}
	if sel != nil {
		*sel = DenoteSelection{Term: s, Name: string(x.Name())}
	}

	// Create new subgoal, adding expression equivalence constraint x = s
	goal0 := MakeProp(F, append(utils.Clone(newHyps), d)...)

	// Define reconstruction function to rebuild original goal proof from subgoal proof
	reconstruct := func(thms ...Prop) Prop {
		// Replace variable x with original subterm s
		p := core.PropTermInst(thms[0], ext.MakeTermSubst(x, s))
		// Handle potential beta-equivalence
		p = prop.Refl(s).MaybeDeriveTrans(p)
		p = WrapProp(p).Rewrite(prop.DeepBeta)
		// Apply previously recorded beta reductions
		for _, h := range hBetas {
			p = h.MaybeDeriveTrans(p)
		}
		// DenoteRewrite operates bottom-up and may rewrite inside
		// lambda bodies, producing eta-expanded forms like λẋ.f(ẋ)
		// instead of f. After PropTermInst + DeepBeta, hypotheses
		// may contain eta-expanded subterms and not match the
		// originals directly. Use BetaEtaRefl to bridge the gap: an
		// image the goal does not hold is carried back to a goal
		// hypothesis βη-equal to it. A hypothesis the goal holds is
		// no image — two of the goal's hypotheses can be η-variants
		// of each other, and bridging one away would leave the image
		// behind.
		for _, origHyp := range goal.Hyps() {
			if !p.HasHyp(origHyp) {
				for h := range p.HypIter() {
					if goal.HasHyp(h) {
						continue
					}
					if eq := prop.BetaEtaRefl(origHyp, h); eq != nil {
						p = eq.LeftAssume().DeriveTrans(p)
						break
					}
				}
			}
		}
		// If original goal is not ⊥, handle negated conclusion
		if negConcl != nil {
			if !p.HasHyp(negConcl) {
				for h := range p.HypIter() {
					if goal.HasHyp(h) {
						continue
					}
					if eq := prop.BetaEtaRefl(negConcl, h); eq != nil {
						p = eq.LeftAssume().DeriveTrans(p)
						break
					}
				}
			}
			if p.HasHyp(negConcl) {
				p = prop.DoubleNegRewrite(Not(negConcl)).
					EqMP(WrapProp(p).NegHyp(negConcl))
			}
		}
		return p
	}

	// Each hypothesis of the goal descends from its own slot, rewritten
	// through the abbreviation or not; the negated conclusion and the
	// defining equation are new.
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, newHyps[:goal.NumHyps()])}, goal0)
}

// namedBy is the variable a hypothesis of hyps names s by — `v = s'` or
// `s' = v` with s' β-normalizing to s — and that hypothesis; nil where
// none does.
func namedBy(hyps []Term, s Term) (core.VarTerm, Term) {
	for _, h := range hyps {
		l, r, ok := MatchesEQ(h)
		if !ok {
			continue
		}
		if v, ok := l.AsVar(); ok && betaNormal(r).AlphaEquals(s) {
			return v, h
		}
		if v, ok := r.AsVar(); ok && betaNormal(l).AlphaEquals(s) {
			return v, h
		}
	}
	return core.VarTerm{}, nil
}

// foldNamed is denoteTerm's firing for a value s the goal names by the
// variable v in the hypothesis naming: every other occurrence of s, in
// the hypotheses and the negated conclusion, is rewritten to v; naming
// stands as spelled; no equation is added. Nil where s occurs nowhere
// else (under denoteExplicit, the panic denoteTerm raises for a term the
// goal does not spell).
func foldNamed(goal Prop, s Term, v core.VarTerm, naming Term, sel *DenoteSelection, mode denoteMode) *SubGoals {
	hyps, negConcl := denoteHyps(goal)
	d, rewrite := Eq(v, s), prop.DenoteRewrite(v, s)
	newHyps := utils.Clone(hyps)
	rewritten := make([]*PropWrapper, len(hyps))
	hit := false
	for i, h := range hyps {
		if h.Equals(naming) {
			continue
		}
		if w := rewrite(h); w != nil {
			// The λ rewrite folds under binders and may leave an
			// η-expansion of the name, `λj. v(j)`; the name is v.
			w = w.RewriteConclRhs(prop.DeepBetaEta)
			Assert(w.NumHyps() == 1 && w.Hyp(0).Equals(d))
			newHyps[i], rewritten[i] = Rhs(w), w
			hit = true
		}
	}
	if !hit {
		if mode == denoteExplicit {
			panic(fmt.Sprintf("denote(%s): the term is named by %s and occurs nowhere else in the goal's "+
				"hypotheses or negated conclusion — nothing to fold\n(goal: %s)",
				ext.PrintTerm(s), ext.PrintTerm(v), prop.PrintProp(goal)))
		}
		return nil
	}
	if sel != nil {
		*sel = DenoteSelection{Term: s, Name: string(v.Name())}
	}
	// {naming} ⊢ v = s: the naming hypothesis read as the rewrite's
	// equation, its value spelled as the goal spells s — up to β, η and
	// the names of bound variables.
	bridge := prop.Assume(naming)
	if l, _, _ := MatchesEQ(naming); !l.Equals(v) {
		bridge = bridge.EqSym()
	}
	if spelled := Rhs(bridge); !spelled.Equals(s) {
		eq := prop.BetaEtaRefl(spelled, s)
		Assert(eq != nil)
		bridge = bridge.EqTrans(eq)
	}
	// MakeProp sorts the list it is handed in place; newHyps keeps the
	// order rewritten is indexed by.
	goal0 := MakeProp(F, utils.Clone(newHyps)...)
	reconstruct := func(thms ...Prop) Prop {
		p := WrapProp(thms[0])
		for i, w := range rewritten {
			if w != nil && p.HasHyp(newHyps[i]) {
				p = w.LeftAssume().DeriveTrans(p)
			}
		}
		if p.HasHyp(d) && !d.Equals(naming) {
			p = bridge.DeriveTrans(p)
		}
		if negConcl != nil && p.HasHyp(negConcl) {
			p = prop.DoubleNegRewrite(Not(negConcl)).EqMP(p.NegHyp(negConcl))
		}
		return p
	}
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, newHyps[:goal.NumHyps()])}, goal0)
}

/**
 * HilbertDenoteTactic simplifies goals containing Hilbert ε terms by introducing
 * new variables and appropriate existential constraints.
 *
 * This tactic:
 * 1. Searches for Hilbert ε operators in both hypotheses and conclusion
 * 2. Applies hilbertDenoteTransform to each term containing ε operators
 * 3. Creates a new subgoal where:
 *    - The ε term is replaced with a newly introduced variable
 *    - An equation relating the new variable to the ε term is added
 *    - An existential constraint capturing the semantics of the ε term is added
 *
 * A reconstruction function is provided that:
 * 1. Takes the proof of the simplified subgoal
 * 2. Uses the existential theorem to maintain semantic equivalence
 * 3. Uses the simplification theorem to restore the original form
 * 4. Eliminates the introduced variable equation (x = ε-term)
 *
 * Parameters:
 *   - goal: The goal proposition potentially containing ε terms
 *
 * Returns:
 *   - A SubGoals structure with simplified subgoals if applicable
 *   - nil if no ε terms are found
 */
func HilbertDenoteTactic(goal Prop) *SubGoals {
	return hilbertDenote(goal, nil, "", nil, false)
}

// HilbertDenoteTacticRecording is HilbertDenoteTactic with an output
// sink: when the search fires, *sel records the ε-term it abstracted and
// the variable it minted. Search behaviour is identical either way.
func HilbertDenoteTacticRecording(goal Prop, sel *DenoteSelection) *SubGoals {
	return hilbertDenote(goal, nil, "", sel, false)
}

// HilbertDenoteTermTactic is the EXPLICIT form of HilbertDenoteTactic:
// it abstracts the GIVEN ε-term under the GIVEN variable name instead of
// searching the goal for one. Panics when no hypothesis and not the
// conclusion contains the term — same contract, same reason, as
// DenoteTermTactic.
func HilbertDenoteTermTactic(term Term, name string) Tactic {
	return func(goal Prop) *SubGoals {
		if term == nil {
			panic("HilbertDenoteTermTactic: nil term")
		}
		sg := hilbertDenote(goal, term, name, nil, false)
		if sg == nil {
			panic(fmt.Sprintf("hilbert_denote(%s): the ε-term occurs in neither the "+
				"goal's hypotheses nor its conclusion — nothing to abstract\n(goal: %s)",
				ext.PrintTerm(term), prop.PrintProp(goal)))
		}
		return sg
	}
}

// HilbertDenoteTermTacticOptional is HilbertDenoteTermTactic that
// DECLINES instead of panicking when the ε-term is absent — the
// shaping-preamble flavor (see DenoteTermTacticOptional).
func HilbertDenoteTermTacticOptional(term Term, name string) Tactic {
	return func(goal Prop) *SubGoals {
		if term == nil {
			panic("HilbertDenoteTermTactic: nil term")
		}
		return hilbertDenote(goal, term, name, nil, true)
	}
}

// hilbertDenote is the shared body: scan the hypotheses, then the
// conclusion, for a term the ε-abstraction applies to. `pick` nil ⇒
// search (ext.HilbertSubTerm); `pick` non-nil ⇒ that ε-term, denoted by
// `name`. `sel` non-nil ⇒ record what the search chose.
func hilbertDenote(goal Prop, pick Term, name string, sel *DenoteSelection, optionalName bool) *SubGoals {
	avoidTerms := append(goal.Hyps(), goal.Conclusion())
	denote := func(t Term) (*PropWrapper, *PropWrapper, VarTerm) {
		if pick != nil {
			return prop.HilbertDenoteAt(t, pick, name, avoidTerms, optionalName)
		}
		simplify, existential, x, s := prop.HilbertDenoteSelect(t, avoidTerms)
		if !x.IsZero() && sel != nil {
			*sel = DenoteSelection{Term: s, Name: string(x.Name())}
		}
		return simplify, existential, x
	}
	for i := range goal.NumHyps() {
		if simplify, existential, x := denote(goal.Hyp(i)); !x.IsZero() {
			goal0 := MakeProp(
				goal.Conclusion(),
				append(restHyps(goal, i), Rhs(simplify), existential.Conclusion())...)
			reconstruct := func(thms ...Prop) Prop {
				if IsStronger(thms[0], goal) {
					return thms[0]
				}
				p := existential.MaybeDeriveTrans(thms[0])
				p = simplify.LeftAssume().MaybeDeriveTrans(p)
				p = WrapProp(p).RemoveVarHyp(x)
				return p
			}
			return MakeSubGoals(goal, reconstruct, goal0)
		}
	}
	if simplify, existential, x := denote(goal.Conclusion()); !x.IsZero() {
		goal0 := MakeProp(
			Rhs(simplify),
			append(goal.Hyps(), existential.Conclusion())...)
		reconstruct := func(thms ...Prop) Prop {
			if IsStronger(thms[0], goal) {
				return thms[0]
			}
			p := existential.MaybeDeriveTrans(thms[0])
			if !p.Conclusion().Equals(F) {
				p = simplify.EqSym().EqMP(p)
			}
			p = WrapProp(p).RemoveVarHyp(x)
			return p
		}
		return MakeSubGoals(goal, reconstruct, goal0)
	}
	return nil
}
