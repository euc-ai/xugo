package clause

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

// SelfContradict detects trivial self-contradictions in a single clause.
// It looks for clauses containing only one literal of the form (l ≠ r)
// where l and r can be unified.
// Example: ∀x.P(y) ≠ P(x) can be refuted by unifying x with y.
// Returns the refuted theorem if a contradiction is found, nil otherwise.
func (c *Clause) SelfContradict() *ClauseThm {
	if c.EffectiveNumLits() > 1 {
		return nil
	}
	if nci := MatchesNOT(c.EffectiveLit()); nci != nil {
		if l, r, ok := MatchesEQ(nci); ok {
			if substs := UnifyTerms(context.Background(), l, r,
				c.EffectiveTerm().HasFreeName); len(substs) > 0 {
				return selfContradictFromSubst(c, substs[0])
			}
		}
	}
	return nil
}

// selfContradictFromSubst builds the self-contradiction theorem from a recorded
// unifier (the deterministic tail of SelfContradict), and attaches a recipe so
// replay reproduces it without re-running the unification search.
func selfContradictFromSubst(c *Clause, subst TermSubstsGroup) *ClauseThm {
	thm := c.Specialize(subst).
		RewriteConcl(prop.DeepBetaEta).
		RewriteConcl(BasicRewrite).
		AsThmCert()
	Assert(thm.Conclusion().Equals(F))
	return MakeClauseThm(thm, FClause, c).withRecipe(&deduceRecipe{
		rule:   _RuleSelfContradict,
		inputs: []*Clause{c},
		substs: subst,
	})
}

// Factor performs all possible factoring operations on a clause.
// Factoring eliminates redundancy by unifying similar literals within the clause.
//
// It searches for:
// 1. Unifiable terms within the clause that can be factored
// 2. Boolean universal variables that can be instantiated to ⊤ or ⊥
//
// For each literal in the clause:
// - l ≠ r: tries to unify l or r with other terms
// - ¬t: tries to unify t with other terms (using t = ⊤)
// - t: tries to unify t with other terms (using t = ⊥)
//
// Results are delivered asynchronously through the deliverResults channel,
// which is closed on every exit. The unifications run on goroutines of
// their own; a panic in one is raised on the goroutine that called Factor
// (utils.Tasks).
func (c *Clause) Factor(
	ctx context.Context,
	deliverResults chan<- *ClauseThm) {
	defer close(deliverResults)

	// The original clause, before the simplification bridge below may replace c
	// with its simplified equivalent. Recorded in factor recipes so replay can
	// re-derive the bridge from the same starting clause (see factorReplay).
	origC := c

	var bridgeThm *ClauseThm
	if !c.simplificationThm.IsZero() {
		thm := WrapProp(c.simplificationThm).LeftAssume()
		conclClause := c.equivalentClause
		if conclClause.EquatesT() {
			return
		}
		clauseThm := MakeClauseThm(thm.AsThmCert(), conclClause, c).withRecipe(
			&deduceRecipe{rule: _RuleSimplifyBridge, inputs: []*Clause{c}})
		select {
		case <-ctx.Done():
		case deliverResults <- clauseThm:
		}

		if !thm.Conclusion().Equals(F) {
			// since simplificationThm doesn't reduce generality,
			// we can replace c with the new clause.
			c = conclClause
			bridgeThm = clauseThm
		}
	}

	c0SubTerms := ext.SubTerms(c.EffectiveLits()...)

	wg := utils.Tasks{}
	callback := func(t Term, i int) {
		keys := utils.EmptySet[core.TermKey]()
		for s := range c0SubTerms {
			if ctx.Err() != nil {
				return
			}
			if !t.Type().Equals(s.Type()) {
				continue
			}
			if keys.Has(s.AlphaKey()) {
				continue
			}
			keys.Add(s.AlphaKey())

			wg.Go(func() {
				for _, substs := range UnifyTerms(
					ctx, t, s, c.EffectiveTerm().HasFreeName) {
					if ctx.Err() != nil {
						return
					}
					for _, clauseThm := range factorClause(c, substs, i) {
						if bridgeThm != nil {
							// recover the input clause as the new hyp clause might not be in the record.
							clauseThm = clauseThm.DeriveHypFrom(bridgeThm)
						}
						clauseThm = clauseThm.withRecipe(&deduceRecipe{
							rule:     _RuleFactor,
							inputs:   []*Clause{origC},
							litIndex: i,
							substs:   substs,
						})
						select {
						case <-ctx.Done():
						case deliverResults <- clauseThm:
						}
					}
				}
			})
		}
	}

	// For bool universal bound vars, simply specialize them to ⊤ / ⊥.
	wg.Go(func() {
		for _, clauseThm := range boolSpecialize(c) {
			clauseThm = clauseThm.withRecipe(
				&deduceRecipe{rule: _RuleBoolSpecialize, inputs: []*Clause{c}})
			select {
			case <-ctx.Done():
				return
			case deliverResults <- clauseThm:
			}
		}
	})

	for i, t := range c.EffectiveLits() {
		if nt := MatchesNOT(t); nt != nil {
			// if ti is in the form of l ≠ r, use it as equality.
			if l, r, ok := MatchesEQ(nt); ok {
				callback(l, i)
				callback(r, i)
			} else {
				// if ti is in the form of ¬nti, use ¬ti ⊢ nti = ⊤
				callback(nt, i)
			}
		} else {
			// use ¬ti ⊢ ti = ⊥.
			callback(t, i)
		}
	}
	wg.Wait()
}

// Contradicts detects trivial contradictions between two unit clauses.
// It looks for complementary literals that can be unified:
// - c0 contains l and c1 contains ¬l', where l and l' unify
// - c0 contains ¬l and c1 contains l', where l and l' unify
// Example: ¬P(x) vs P(f(y)) can be refuted by unifying P(x) with P(f(y)).
// Returns the refuted theorem if a contradiction is found, nil otherwise.
// Note: Only works for unit clauses (clauses with exactly one literal).
func (c0 *Clause) Contradicts(c1 *Clause) *ClauseThm {
	if c0.EffectiveNumLits() > 1 || c1.EffectiveNumLits() > 1 {
		return nil
	}

	ground := utils.Disjunct(
		c0.EffectiveTerm().HasFreeName,
		c1.EffectiveTerm().HasFreeName)

	var subst TermSubstsGroup
	found, switchSide := false, false
	if ncj := MatchesNOT(c1.EffectiveLit()); ncj != nil {
		if substs := UnifyTerms(
			context.Background(), c0.EffectiveLit(), ncj, ground); len(substs) > 0 {
			subst, found = substs[0], true
		}
		if _, _, ok := MatchesEQ(ncj); ok {
			if li, ri, ok := MatchesEQ(c0.EffectiveLit()); ok {
				if substs := UnifyTerms(
					context.Background(), Eq(ri, li), ncj, ground); len(substs) > 0 {
					subst, found, switchSide = substs[0], true, true
				}
			}
		}
	}
	if !found {
		if nci := MatchesNOT(c0.EffectiveLit()); nci != nil {
			if substs := UnifyTerms(
				context.Background(), nci, c1.EffectiveLit(), ground); len(substs) > 0 {
				subst, found = substs[0], true
			}
			if _, _, ok := MatchesEQ(nci); ok {
				if lj, rj, ok := MatchesEQ(c1.EffectiveLit()); ok {
					if substs := UnifyTerms(
						context.Background(), nci, Eq(rj, lj), ground); len(substs) > 0 {
						subst, found, switchSide = substs[0], true, true
					}
				}
			}
		}
	}
	if !found {
		return nil
	}
	return contradictsFromSubst(c0, c1, subst, switchSide)
}

// contradictsFromSubst builds the contradiction theorem from a recorded unifier
// (the deterministic tail of Contradicts, shared by all four unify branches —
// they differ only in how the unifier is found, switchSide marks the commuted
// path). Attaches a recipe so replay reproduces it without re-searching.
func contradictsFromSubst(
	c0, c1 *Clause, subst TermSubstsGroup, switchSide bool) *ClauseThm {
	t0, t1 := c0.Specialize(subst), c1.Specialize(subst)
	if switchSide {
		if MatchesNOT(t0.Conclusion()) == nil {
			l, r, ok := MatchesEQ(t0.Conclusion())
			Assert(ok)
			t0 = prop.CommuteEQ(l, r).EqMP(t0)
		} else if MatchesNOT(t1.Conclusion()) == nil {
			l, r, ok := MatchesEQ(t1.Conclusion())
			Assert(ok)
			t1 = prop.CommuteEQ(l, r).EqMP(t1)
		} else {
			panic("should not happen")
		}
	}
	thm := prop.ConclAND(t0.Conclusion(), t1.Conclusion()).
		DeriveHypFrom(t0).
		DeriveHypFrom(t1).
		RewriteConcl(prop.DeepBetaEta).
		RewriteConcl(prop.BoolRewrite)
	Assert(thm.Conclusion().Equals(F))
	return MakeClauseThm(thm.AsThmCert(), FClause, c0, c1).withRecipe(&deduceRecipe{
		rule:       _RuleContradicts,
		inputs:     []*Clause{c0, c1},
		substs:     subst,
		switchSide: switchSide,
	})
}

// One clause simplifies another. Returns the resulting thm
// whose hyps are the 2 given clauses and the conclusion is the
// simplified clause.
// Simplification happens when c0 is a unit clause, and
// - when c0 is an equality, c1 can be simplified by eq rewriting.
// - when c0 is t, c1 can be simplified by rewriting t to ⊤.
// - when c0 is ¬t, c1 can be simplified by rewriting t to ⊥.
//
// GROUND CONGRUENCE CLOSURE rides this rule, in-search: a
// quantifier-free equality between compound non-bool terms may also
// rewrite at the SAME size, in whichever orientation strictly
// decreases the rewritten clause under the total (size, Term.Compare)
// order — the stored absEq orientation is tried first, then the
// commuted one. Pairwise, these order-gated demodulation steps are
// exactly ground Knuth–Bendix completion distributed over the
// saturation loop: equations interreduce each other, every clause's
// ground subterms normalize toward the order-least representative of
// their congruence class, and two spellings of one ground term (x*z
// vs z*x under a commutation premise) become literally the same atom
// — no paramodulation search, no direction guessed by anyone but the
// term order, termination by strict descent in a well-founded order.
// The clause-set identity is untouched (the FUNEXT lesson) and the
// recipe stays _RuleSimplifies: this function remains pure in
// (c0, c1), so recorded recipes replay bit-for-bit — the commuted
// orientation is only ever reached when the stored one declines,
// which is the same decision replay recomputes. Var=var equalities
// keep their own regime (fixed orientation, occurrence-count
// termination — alpha_merge.go) and are excluded from the commuted
// attempt.
func (c0 *Clause) Simplifies(c1 *Clause) *ClauseThm {
	// an equality can rewrite itself to be something trivial,
	// e.g. a = b rewrites a = b to b = b,
	// but this is pointless.
	if c0.Equivalent(c1) || c0.EffectiveNumLits() > 1 {
		return nil
	}
	Assert(c0.absEq != nil)
	if thm := c0.simplifiesWith(c0.absEq, c1, false); thm != nil {
		return thm
	}
	// The commuted orientation, ground compound equalities only. absEq
	// pre-swaps a strictly-smaller LHS (contextEqOpt), so for
	// different-size equations the stored orientation is already the
	// shrinking one and the commuted attempt can never pass the gate;
	// this is genuinely reachable only for same-size equations, whose
	// stored orientation is the as-written coin flip.
	if !c0.isGroundCompoundEq() {
		return nil
	}
	flipped := c0.flippedAbsEq()
	if flipped == nil {
		return nil
	}
	return c0.simplifiesWith(flipped, c1, true)
}

// RefutesByRewrite returns the refutation Simplifies finds when c0, a
// unit clause, rewrites c1 to ⊥, and nil otherwise. A clause rewrites to
// ⊥ only when every literal is rewritten, and a literal is rewritten only
// where a side of c0's equation matches, which needs that side's head
// symbol in the literal: a clause with a literal that carries neither
// side's head is declined before any proof is built. The refuter applies
// this to the clauses a search starts from (refuteStateFromCNF,
// divideConquer), which meet Contradicts but not cleanUpRecords.
func (c0 *Clause) RefutesByRewrite(c1 *Clause) *ClauseThm {
	if c0.Equivalent(c1) || c0.EffectiveNumLits() > 1 {
		return nil
	}
	Assert(c0.absEq != nil)
	l, r, ok := MatchesEQ(c0.absEq.Conclusion())
	if !ok {
		return nil
	}
	if heads := spineHeadNames(l, r); heads != nil {
		for _, lit := range c1.EffectiveLits() {
			if !slices.ContainsFunc(heads, lit.HasName) {
				return nil
			}
		}
	}
	if u := c0.Simplifies(c1); u != nil && u.IsRefuted() {
		return u
	}
	return nil
}

// spineHeadNames returns the head symbol of each term — the constant or
// free variable its application spine ends in, under its abstractions.
// nil when a spine ends in one of the term's own bound variables, which
// no symbol test stands for.
func spineHeadNames(terms ...Term) []TermName {
	names := make([]TermName, 0, len(terms))
	for _, t := range terms {
		vars, body := MatchesAbs(t)
		for {
			app, ok := body.AsAppliedTerm()
			if !ok {
				break
			}
			body = app.Fun()
		}
		if c, ok := body.AsConst(); ok {
			names = append(names, c.Name())
			continue
		}
		v, ok := body.AsVar()
		if !ok || slices.ContainsFunc(vars, func(b VarTerm) bool { return b.Equals(v) }) {
			return nil
		}
		names = append(names, v.Name())
	}
	return names
}

// simplifiesWith is Simplifies' body for one orientation of c0's
// equality. orderedOnly marks the commuted attempt: only the
// strictly-order-decreasing acceptances apply there — the bool-var and
// var=var same-size exceptions are licensed by fixed-orientation
// termination arguments and must not run reversed.
func (c0 *Clause) simplifiesWith(absEq *PropWrapper, c1 *Clause, orderedOnly bool) *ClauseThm {
	rewrite := prop.EqRewrite(absEq)
	if w := rewrite(c1.EffectiveTerm()); w != nil {
		w = w.RewriteConclRhs(BasicRewrite)
		// Normally we only simplify when the result is strictly smaller.
		// For boolean variable clauses (b₀ or ¬b₀), we also allow
		// same-size rewrites (b₀ → ⊤ or b₀ → ⊥) because they
		// substitute a ground variable with a constant, enabling
		// further contradiction finding. Ground var=var equality clauses
		// (α₀ = α₁, the ALPHA-MERGE derived equalities — alpha_merge.go)
		// get the same exception: the rewrite substitutes one ground symbol
		// by another (same size, and terminating — see isVarEqVarClause).
		// Ground compound equalities get the ORDER-gated same-size case
		// (congruence-closure demodulation — see Simplifies' doc): each
		// accepted step strictly decreases the clause term under
		// (size, Term.Compare), a well-founded order, so the saturation
		// cannot oscillate between the two spellings.
		accepted := Rhs(w).Size() < c1.EffectiveTerm().Size() ||
			c0.orientedGroundStep(Rhs(w), c1.EffectiveTerm())
		if !orderedOnly {
			accepted = accepted || isBoolVarClause(c0) || isVarEqVarClause(c0) ||
				isSymbolValuedBoolClause(c0)
		}
		if accepted {
			// The rule is a clause's equation, and its first pass shrank
			// c1. Each further pass rewrites occurrences the term already
			// holds, at most one per node of the term it started from
			// (the backstop of RewriteConclRhsRecurWhistled); a chain
			// longer than that is the rule making its own occurrences —
			// (λx. x) = set_comprehension reads every bound variable s as
			// set_comprehension(s), without end — and the rewrite stops
			// at its first pass.
			first, backstop := w, c1.EffectiveTerm().Size()
			for n, u := 0, rewrite(Rhs(w)); u != nil; n, u = n+1, rewrite(Rhs(w)) {
				if n == backstop {
					w = first
					break
				}
				w = w.EqTrans(u)
			}
			w = w.
				RewriteConclRhs(BasicRewrite).
				LeftAssume()

			// The rewrite was applied to c1.EffectiveTerm(), so LeftAssume
			// introduces c1's EFFECTIVE term as a hyp. MakeClauseThm aligns the
			// hyps against c1.Term() (the ORIGINAL), so when c1 has a non-trivial
			// equivalent clause (Term != EffectiveTerm) we must bridge that hyp
			// back via c1's simplificationThm (c1.Term() ⊢ c1.EffectiveTerm()) —
			// mirroring how Specialize keeps Contradicts' hyps in original-term
			// form. (c0's original-term hyp is already baked into c0.absEq.)
			if !c1.simplificationThm.IsZero() {
				w = w.DeriveHypFrom(WrapProp(c1.simplificationThm).LeftAssume())
			}

			w = prop.ForAllConclFreeVars(w)
			// A rewrite can open what an atom held inside an
			// abstraction — set_comprehension rewritten to λx. x reduces
			// set_comprehension(λz. ∃w. P(w), y) to ∃w. P(w) — and the
			// result is then no clause: no simplification.
			if !ext.IsDisjunctive(w.Conclusion()) {
				return nil
			}
			thm, conclClause := simplifyConclusion(w)
			return MakeClauseThm(thm.AsThmCert(), conclClause, c0, c1).withRecipe(
				&deduceRecipe{rule: _RuleSimplifies, inputs: []*Clause{c0, c1}})
		}
	}
	return nil
}

// orientedGroundStep is the congruence-closure same-size acceptance:
// c0 is a ground compound equality and the rewritten clause term is
// the SAME size but strictly Term.Compare-below the input. Combined
// with the strictly-smaller-size case this makes every accepted
// demodulation step a strict descent in the total well-founded
// (size, Compare) order — the termination measure, checked on the
// RESULT directly so no context-monotonicity assumption about Compare
// is needed.
func (c0 *Clause) orientedGroundStep(result, input Term) bool {
	if !c0.isGroundCompoundEq() {
		return false
	}
	return result.Size() == input.Size() && result.Compare(input) < 0
}

// isGroundCompoundEq reports whether the clause is a quantifier-free
// unit equality between non-bool terms, at least one side compound —
// the ground-congruence-closure demodulation license. Var=var
// equalities are excluded: they belong to the ALPHA-MERGE regime
// (fixed orientation; running them commuted would ping-pong against
// their own order-blind same-size exception). Bool equalities (iffs)
// are excluded: they carry disjunctive structure the clause layer
// handles through its own channels.
func (c *Clause) isGroundCompoundEq() bool {
	if c.effectiveUnivBoundVarCount() > 0 || isVarEqVarClause(c) {
		return false
	}
	if c.EffectiveNumLits() != 1 {
		return false
	}
	l, _, ok := MatchesEQ(c.EffectiveBody())
	return ok && !IsBool(l)
}

// flippedAbsEq is c's absEq with the equality commuted (hypothesis
// unchanged). nil when the absEq conclusion is not a plain equality —
// the caller then simply has no commuted orientation to try.
func (c *Clause) flippedAbsEq() *PropWrapper {
	if _, _, ok := MatchesEQ(c.absEq.Conclusion()); !ok {
		return nil
	}
	return c.absEq.EqSym()
}

// isVarEqVarClause checks if this clause's effective body is an equality
// between two variables (α₀ = α₁ — the derived form of an ALPHA-MERGE, see
// alpha_merge.go). Such a rewrite substitutes one ground symbol by another:
// it never grows the target, and it terminates — the absEq is oriented one
// way, each application strictly decreases the eliminated symbol's
// occurrence count, and no rule reintroduces the eliminated symbol.
func isVarEqVarClause(c *Clause) bool {
	l, r, ok := MatchesEQ(c.EffectiveBody())
	if !ok {
		return false
	}
	_, lok := l.AsVar()
	_, rok := r.AsVar()
	return lok && rok
}

// isSymbolValuedBoolClause checks if this clause is ∀x̄. A(x̄) or ∀x̄. ¬A(x̄)
// with A a variable applied to exactly the clause's binders — the
// ∀-generalization of isBoolVarClause: it fixes the ground symbol A to
// the constant predicate λx̄.⊤ / λx̄.⊥. The absEq of such a clause,
// λx̄.A(x̄) = λx̄.⊥, matches an occurrence of the bare symbol A in
// argument position (G(A)) modulo η, and the rewrite substitutes a
// ground symbol by a closed λ that does not mention it: same
// termination argument as the bool-var case (A is eliminated, nothing
// reintroduces it), and the size may grow by the binder count.
func isSymbolValuedBoolClause(c *Clause) bool {
	body := c.EffectiveBody()
	if n := MatchesNOT(body); n != nil {
		body = n
	}
	head, args := stripAppliedVar(body)
	bound := &c.univBoundVars
	if c.equivalentClause != nil {
		bound = &c.equivalentClause.univBoundVars
	}
	if head.IsZero() || len(args) != bound.Size() {
		return false
	}
	return boundVarArgs(args, bound) != nil
}

// isBoolVarClause checks if this clause's effective body is a boolean variable
// (b₀, meaning b₀ = ⊤) or the negation of a boolean variable (¬b₀, meaning b₀ = ⊥).
// Such clauses can be used to substitute the variable with ⊤/⊥ in other clauses.
func isBoolVarClause(c *Clause) bool {
	body := c.EffectiveBody()
	if _, ok := body.AsVar(); ok {
		return true
	}
	if n := MatchesNOT(body); n != nil {
		if _, ok := n.AsVar(); ok {
			return true
		}
	}
	return false
}

// Resolve performs all possible resolution operations between two clauses.
// Resolution eliminates complementary literals by unification.
//
// For each literal in c0, it searches for unifiable terms in c1:
// - If c0 has l = r: tries to unify l or r with subterms in c1
// - If c0 has t: tries to unify t with subterms in c1 (treats as t = ⊤)
// - If c0 has ¬t: tries to unify t with subterms in c1 (treats as t = ⊥)
//
// The resolution rule then:
// 1. Applies the unifying substitution to both clauses
// 2. Uses the literal from c0 to rewrite terms in c1
// 3. Combines the remaining literals
//
// Example: ¬P(x) and P(f(y)) ∨ Q(y) with x→f(y) produces Q(y)
//
// Results are delivered asynchronously through the deliverResults channel,
// which is closed on every exit. The unifications run on goroutines of
// their own; a panic in one is raised on the goroutine that called Resolve
// (utils.Tasks).
func (c0 *Clause) Resolve(
	ctx context.Context,
	c1 *Clause,
	deliverResults chan<- *ClauseThm) {
	defer close(deliverResults)

	// Both directions are needed: the first call renames c0's bound vars that
	// clash with any name in c1; the second renames c1's bound vars that clash
	// with any name in c0 (including c0's free vars). Without the second call,
	// relaxUnify can produce a substitution for a c1-bound var whose name also
	// appears free in c0. Specialize then applies TermInst to the entire thm
	// (hyps included), corrupting c0's hyp and breaking HasHyp/MakeClauseThm.
	// The order matters: c0 is renamed first so c1.AvoidVarsCollision sees the
	// already-renamed c0, avoiding unnecessary double-renames.
	c0 = c0.AvoidVarsCollision(c1)
	c1 = c1.AvoidVarsCollision(c0)
	ground := utils.Disjunct(
		c0.EffectiveTerm().HasFreeName,
		c1.EffectiveTerm().HasFreeName)

	c1SubTerms := ext.SubTerms(c1.EffectiveLits()...)

	wg := utils.Tasks{}
	callback := func(t Term, i int, rewriteType _EqRewriteType) {
		keys := utils.EmptySet[core.TermKey]()
		for s := range c1SubTerms {
			if ctx.Err() != nil {
				return
			}
			if !t.Type().Equals(s.Type()) {
				continue
			}
			if keys.Has(s.AlphaKey()) {
				continue
			}
			keys.Add(s.AlphaKey())
			wg.Go(func() {
				for _, substs := range UnifyTerms(ctx, t, s, ground) {
					if ctx.Err() != nil {
						return
					}
					for _, clauseThm := range resolveClause(
						c0, c1, substs, i, rewriteType) {
						clauseThm = clauseThm.withRecipe(&deduceRecipe{
							rule:        _RuleResolve,
							inputs:      []*Clause{c0, c1},
							litIndex:    i,
							rewriteType: rewriteType,
							substs:      substs,
						})
						select {
						case <-ctx.Done():
						case deliverResults <- clauseThm:
						}
					}
				}
			})
			// Only run diffResolveClause for simple clauses.
			if c0.EffectiveNumLits() > 1 ||
				c1.EffectiveNumLits() > 1 {
				continue
			}
			wg.Go(func() {
				for _, substs := range relaxUnify(ctx, c0, c1, t, s) {
					if ctx.Err() != nil {
						return
					}
					for _, clauseThm := range diffResolveClause(
						c0, c1, s, substs, i, rewriteType) {
						clauseThm = clauseThm.withRecipe(&deduceRecipe{
							rule:        _RuleDiffResolve,
							inputs:      []*Clause{c0, c1},
							litIndex:    i,
							rewriteType: rewriteType,
							substs:      substs,
							c1Subterm:   s,
						})
						select {
						case <-ctx.Done():
						case deliverResults <- clauseThm:
						}
					}
				}
			})
		}
	}

	for i, t := range c0.EffectiveLits() {
		if l, r, ok := MatchesEQ(t); ok {
			callback(l, i, rewriteEqLeft)
			callback(r, i, rewriteEqRight)
		} else if nt := MatchesNOT(t); nt != nil {
			callback(nt, i, rewriteNeg)
		} else {
			callback(t, i, rewriteWhole)
		}
	}

	wg.Wait()
}

// Specialize boolean universal vars to ⊤ / ⊥.
func boolSpecialize(c *Clause) []*ClauseThm {
	var validThms []*ClauseThm
	for v := range c.univBoundVars.Iter() {
		if IsBool(v) {
			for _, boolVar := range []Term{T, F} {
				thm := c.Specialize([]TermSubst{ext.MakeTermSubst(v, boolVar)})
				thm = thm.RewriteConcl(BasicRewrite)
				if !thm.Conclusion().Equals(T) {
					thm = prop.ForAllConclFreeVars(thm)
					clauseThm := MakeClauseThm(
						thm.AsThmCert(), MakeClause(thm.Conclusion()), c)
					if clauseThm.IsRefuted() {
						return []*ClauseThm{clauseThm}
					}
					if !clauseThm.ConclClause().EquatesT() {
						validThms = append(validThms, clauseThm)
					}
				}
			}
		}
	}
	return validThms
}

// factorClause performs factoring on a clause by unifying terms and applying substitutions.
// Given a clause with a literal at index 'ind' and a unifiable term elsewhere in the clause,
// it applies the substitution to eliminate redundancy.
//
// The literal at 'ind' determines the substitution:
// - If literal is l ≠ r: uses equality l = r (or r = l if rightSide=true)
// - If literal is ¬l: uses equality l = ⊤
// - If literal is l: uses equality l = ⊥
//
// Parameters:
// - c0: the clause to factor
// - subst: substitutions from unification
// - ind: index of the literal providing the equality
//
// Returns nil if factoring produces trivial or unchanged result.
func factorClause(
	c *Clause,
	subst TermSubstsGroup,
	ind int) []*ClauseThm {

	cSpecialized := c.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	components := DecomposesOR(cSpecialized.Conclusion())

	// specialization applies the substitution and confirms that specializing does
	// not change the number of effective literals. Some higher-order substitutions
	// can expand a single literal into a top-level disjunction (for example, by
	// instantiating H(a) with q ∨ r).
	if len(components) != c.EffectiveNumLits() {
		return nil
	}

	nti := Not(components[ind])
	equality := prop.Assume(nti).RewriteConcl(prop.DoubleNegRewrite)
	// turn it into an equality.
	equality = flexibleEq(equality, rewriteUnknown)
	Assert(equality.NumHyps() == 1 && equality.HasHyp(nti))

	// The rewriting may fail when the Lhs of the equality is a subterm of Rhs,
	// but the thm still might be useful, so we don't ctx early.
	thm := cSpecialized
	if u := prop.EqRewrite(equality)(thm.Conclusion()); u != nil {
		thm = u.EqMP(thm)
	}

	// c ⊢ ¬¬ti[subst] ∨ (rest[subst] after equality rewriting)
	thm = thm.MoveHypsToConcl(nti.Equals).
		RewriteConcl(ClauseDeduceFinalize)

	thm = prop.ForAllConclFreeVars(thm)
	Assert(thm.NumHyps() == 1)
	thms := makeConclDisjunct(thm)
	clauseThms := make([]*ClauseThm, 0, len(thms))
	for _, thm := range thms {
		thm, conclClause := simplifyConclusion(thm)
		if conclClause.EquatesT() || conclClause.Equivalent(c) {
			return nil
		}

		clauseThm := MakeClauseThm(thm.AsThmCert(), conclClause, c)
		Assert(clauseThm.ConclClause().EffectiveNumLits() <= c.EffectiveNumLits())
		clauseThms = append(clauseThms, clauseThm)
	}
	return clauseThms
}

// resolveClause performs resolution between two clauses using a literal from c0.
// The literal at index 'ind' in c0 is used to rewrite terms in c1.
//
// The literal at 'ind' determines the rewrite rule:
// - If literal is l = r: rewrites occurrences of l to r (or r to l if rightSide=true)
// - If literal is l: rewrites occurrences of l to ⊤
// - If literal is ¬l: rewrites occurrences of l to ⊥
//
// Parameters:
// - c0, c1: the clauses to resolve
// - subst: substitutions from unification
// - ind: index of the literal in c0 providing the rewrite rule
// - rightSide: if true, reverses equality direction for l = r literals
//
// Returns nil if resolution produces trivial or unchanged result.
func resolveClause(
	c0, c1 *Clause,
	subst TermSubstsGroup,
	ind int,
	rewriteType _EqRewriteType) []*ClauseThm {
	if c0.Equivalent(c1) {
		return nil
	}

	c0Specialized := c0.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	// specialization applies the substitution and confirms that specializing does
	// not change the number of effective literals. Some higher-order substitutions
	// can expand a single literal into a top-level disjunction (for example, by
	// instantiating H(a) with q ∨ r).
	if len(DecomposesOR(c0Specialized.Conclusion())) != c0.EffectiveNumLits() {
		return nil
	}

	equality, op := makeLitResolveEquality(c0Specialized, ind, rewriteType)

	thm := c1.Specialize(subst).RewriteConcl(prop.DeepBetaEta)

	if u := prop.EqRewrite(equality)(thm.Conclusion()); u != nil {
		thm = u.EqMP(thm).RewriteConcl(BasicRewrite)
	} else {
		// If the eq is not rewriting (because the Lhs is a subterm of Rhs),
		// thm is just a special case of c1, which is not useful.
		return nil
	}

	// c0, c1 ⊢ rest[subst] ∨ (ti[subst] after equality rewriting)
	thm = op(thm)

	thm = thm.RewriteConcl(ClauseDeduceFinalize)
	if thm.Conclusion().Equals(T) {
		return nil
	}

	thm = prop.ForAllConclFreeVars(thm)

	// It is possible that thm has only 1 hyp.
	// e.g. c0 := ∀x.(P(f(x)) ∨ f(x) = x), c1 := ¬P(ƒ(y))
	// we can have thm: ∀x.(P(f(x)) ∨ f(x) = x) ⊢ P(ƒ(y)) ∨ ¬P(y)
	// where c1 is overwridden by the specified c0.

	Assert(thm.NumHyps() <= 2)

	thms := makeConclDisjunct(thm)

	clauseThms := make([]*ClauseThm, 0, len(thms))
	for _, thm := range thms {
		thm, conclClause := simplifyConclusion(thm)
		if conclClause.EquatesT() ||
			conclClause.Equivalent(c0) ||
			conclClause.Equivalent(c1) {
			return nil
		}
		Assert(conclClause.Term().AlphaEquals(thm.Conclusion()))

		hypClauses := make([]*Clause, 0, 2)
		if thm.HasHyp(c0.Term()) {
			hypClauses = append(hypClauses, c0)
		}
		if thm.HasHyp(c1.Term()) && !c0.Equivalent(c1) {
			hypClauses = append(hypClauses, c1)
		}

		clauseThm := MakeClauseThm(thm.AsThmCert(), conclClause, hypClauses...)
		// A higher-order substitution can expand one of c1's literals into
		// a top-level disjunction, exactly as the c0-side check at the top
		// of this function describes for c0 (unifying a concrete
		// connective into c1's `op` slot does — op ↦ ∨ β-expands
		// `op(bit(k,x), bit(k,y))`, 2 literals → 3). Pure paramodulation
		// then deletes nothing, so a kernel-valid resolvent can reach
		// n0+n1 and the strict shrink bound fails. The candidate is
		// dropped, not asserted on: an Assert here fires inside a
		// Resolve worker goroutine, where the panic escapes the RPC
		// recover and kills the whole serve process. A grown resolvent
		// never leaves this function, and no stored recipe passes
		// through this state. The check sits HERE rather than as an
		// early c1-side specialize guard because expansion that is
		// subsequently deleted by the rewrite yields a shrinking,
		// recordable resolvent; an early guard would reject those and
		// could diverge existing replays.
		if clauseThm.ConclClause().EffectiveNumLits() >=
			c0.EffectiveNumLits()+c1.EffectiveNumLits() {
			return nil
		}
		clauseThms = append(clauseThms, clauseThm)
	}
	return clauseThms
}

// Resolve clauses that contain literals that are not directly unifiable
// but are similar, so they can be resolved by introduce a diff assumption.
// For example, in specialized c0 we have A = B,
// in specialized c1 we have C. Since A ≠ C, we cannot directly rewrite.
// So we first get assumption from TermDiff: l = r ⊢ C = A
// then we have l = r, c0 ⊢ C = B.
// This can be used to rewrite c1, so we have l = r, c0, c1 ⊢ B.
// Then move l = r to the conclusion side, we get c0, c1 ⊢ (l ≠ r) ∨ B.
func diffResolveClause(
	c0, c1 *Clause,
	c1SubTerm Term,
	subst TermSubstsGroup,
	ind int,
	rewriteType _EqRewriteType) []*ClauseThm {
	// c1's bound vars must not collide with names in c0 (and vice versa),
	// otherwise Specialize's TermInst leaks substitutions into the other
	// clause's hyp. Caller (Resolve) ensures this via AvoidVarsCollision.
	for v := range c0.univBoundVars.Iter() {
		Assert(!c1.Term().HasName(v.Name()))
	}
	for v := range c1.univBoundVars.Iter() {
		Assert(!c0.Term().HasName(v.Name()))
	}
	if c0.Equivalent(c1) {
		return nil
	}

	c1SubTerm = c1SubTerm.Substitute(subst...)
	c0Specialized := c0.Specialize(subst).RewriteConcl(prop.DeepBetaEta)

	// specialization applies the substitution and confirms that specializing does
	// not change the number of effective literals. Some higher-order substitutions
	// can expand a single literal into a top-level disjunction (for example, by
	// instantiating H(a) with q ∨ r).
	if len(DecomposesOR(c0Specialized.Conclusion())) != c0.EffectiveNumLits() {
		return nil
	}

	equality, removeEqHyp := makeLitResolveEquality(c0Specialized, ind, rewriteType)

	// We need to connect c1Subterm to the LHS of the equality (which is
	// the subterm in c0 to be used to rewrite c1.)
	equality, assumption, trivialDiff := diffAssumption(c0, c1, equality, c1SubTerm)
	if equality == nil {
		return nil
	}
	thm := c1.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	c1Specialized := thm

	if trivialDiff &&
		trivialDiffAssumption(c0Specialized, c1Specialized, assumption) {
		return nil
	}

	if u := prop.EqRewrite(equality)(thm.Conclusion()); u != nil {
		thm = u.EqMP(thm).RewriteConcl(BasicRewrite)
	} else {
		// If the eq is not rewriting (because the Lhs is a subterm of Rhs),
		// thm is just a special case of c1, which is not useful.
		return nil
	}
	c1Rewritten := thm.Conclusion()

	// It's possible that the assumption can be simplified by the specialized clauses.
	if u := prop.EqRewrite(
		flexibleEq(c1Specialized, rewriteUnknown))(assumption); u != nil {
		u = u.RewriteConclRhs(BasicRewrite)
		assumption = WrapTerm(Rhs(u))
		thm = u.RightAssume().DeriveTrans(thm)
	}
	if u := prop.EqRewrite(
		flexibleEq(c0Specialized, rewriteUnknown))(assumption); u != nil {
		u = u.RewriteConclRhs(BasicRewrite)
		// If the Rhs of u is not disjunctive and not a '⇔' term,
		// we don't simplify the assumtion as it may cause issues
		// in moveAssumptionToConcl.
		if _, _, ok := MatchesIFF(Rhs(u)); ok || ext.IsDisjunctive(Rhs(u)) {
			assumption = WrapTerm(Rhs(u))
			thm = u.RightAssume().DeriveTrans(thm)
		}
	}
	Assert(thm.HasHyp(assumption))

	var thms []*PropWrapper
	var clauseThms []*ClauseThm

	// Move assumption to the conclusion side.
	// Because assmption might contains IFF, this might lead to 2 thms.
	for _, thm := range moveAssumptionToConcl(thm, assumption, c1Rewritten) {
		// Each thm might be further split to multiple thms if the conclusion
		// is not disjunctive.
		thms = append(thms, makeConclDisjunct(thm)...)
	}

	for _, thm := range thms {
		thm = removeEqHyp(thm)
		thm = thm.RewriteConcl(ClauseDeduceFinalize)
		if thm.Conclusion().Equals(T) {
			continue
		}

		thm = prop.ForAllConclFreeVars(thm)

		// It is possible that thm has only 1 hyp.
		// e.g. c0 := ∀x.(P(f(x)) ∨ f(x) = x), c1 := ¬P(ƒ(y))
		// we can have thm: ∀x.(P(f(x)) ∨ f(x) = x) ⊢ P(ƒ(y)) ∨ ¬P(y)
		// where c1 is overwridden by the specified c0.

		Assert(thm.NumHyps() <= 2)
		thm, conclClause := simplifyConclusion(thm)
		if conclClause.EquatesT() ||
			conclClause.Equivalent(c0) ||
			conclClause.Equivalent(c1) {
			continue
		}
		if conclClause.EffectiveNumLits() > 1 {
			continue
		}
		Assert(conclClause.Term().AlphaEquals(thm.Conclusion()))

		hypClauses := make([]*Clause, 0, 2)
		if thm.HasHyp(c0.Term()) {
			hypClauses = append(hypClauses, c0)
		}
		if thm.HasHyp(c1.Term()) {
			hypClauses = append(hypClauses, c1)
		}

		clauseThm := MakeClauseThm(thm.AsThmCert(), conclClause, hypClauses...)
		clauseThms = append(clauseThms, clauseThm)
	}
	return clauseThms
}

// unify s0 and s1 without considering the ground vars,
// then filtered out the substitutions that contains the ground vars.
// In this way we can get substitutions that transfers the 2 terms
// to be close but not necessarily identical.
func relaxUnify(ctx context.Context, c0, c1 *Clause, s0, s1 Term) []TermSubstsGroup {
	var substsGroups []TermSubstsGroup
	if c0.univBoundVars.Size() > 0 {
		substsGroups = append(substsGroups,
			UnifyTerms(ctx, s0, s1, utils.EmptyPredicate)...)
	}
	if c1.univBoundVars.Size() > 0 {
		substsGroups = append(substsGroups,
			UnifyTerms(ctx, s1, s0, utils.EmptyPredicate)...)
	}
	filteredGroups := make([]TermSubstsGroup, 0, len(substsGroups))
	for _, substs := range substsGroups {
		group := make(TermSubstsGroup, 0, len(substs))
		for _, s := range substs {
			if c0.univBoundVars.Has(s.VarTerm) ||
				c1.univBoundVars.Has(s.VarTerm) {
				group = append(group, s)
			}
		}
		if len(group) > 0 {
			// deduplicate the groups
			if i, found := slices.BinarySearchFunc(filteredGroups, group,
				unify.CompareTermSubsts); !found {
				filteredGroups = slices.Insert(filteredGroups, i, group)
			}
		}
	}
	if len(filteredGroups) == 0 {
		return []TermSubstsGroup{{}}
	}
	return append(filteredGroups, TermSubstsGroup{})
}

// Move assumption to the conclusion side.
// If the assumption contains an IFF, it should be split into 2 thms.
func moveAssumptionToConcl(
	thm *PropWrapper,
	assumption, rest Term) []*PropWrapper {
	// At this point, assumption might not necessarily be an equality.
	thm = prop.WrapProp(thm).MoveHypsToConcl(assumption.Equals)
	if ext.IsDisjunctive(assumption) {
		return []*PropWrapper{thm}
	}

	// If assumption is not disjunctive
	// it must be an equality of 2 boolean terms,
	// the negAssumption should be convert to a conjunction of 2 disjunctions.
	// i.e.
	// p ⊕ q → (p ∨ q) ∧ (¬p ∨ ¬q)
	var conjunctConcl *PropWrapper
	var concl0, concl1 Term

	l, r, ok := MatchesIFF(assumption)
	Assert(ok)
	conjunctConcl = prop.BinaryThms["(p ⊕ q) ⇔ ((p ∨ q) ∧ (¬p ∨ ¬q))"](l, r)
	concl0, concl1, _ = MatchesAND(Rhs(conjunctConcl))

	// c0, c1, ¬rest[subst] ⊢ ¬(assumption)
	if rest.Equals(F) {
		thm = conjunctConcl.EqMP(thm)
		thm0 := thm.DeriveTrans(prop.HypAND0(concl0, concl1))
		thm1 := thm.DeriveTrans(prop.HypAND1(concl0, concl1))
		return []*PropWrapper{thm0, thm1}
	}

	// c0, c1, ¬rest[subst] ⊢ (ti[subst] after equality rewriting) ∨ ¬(assumption)
	distributivity := prop.TernaryThms["(p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))"]
	thm = conjunctConcl.LeftApply(Apply(OR, rest)).
		EqTrans(distributivity(rest, concl0, concl1)).
		EqMP(thm)

	concl0, concl1 = Or(rest, concl0), Or(rest, concl1)
	thm0 := thm.DeriveTrans(prop.HypAND0(concl0, concl1))
	thm1 := thm.DeriveTrans(prop.HypAND1(concl0, concl1))
	return []*PropWrapper{thm0, thm1}
}

// connect c1Subterm to the LHS of the equality (which is the subterm
// in c0 to be used to rewrite c1.)
// For example, the subterm equality in specialized c0 is A = B,
// in specialized c1 we have C. Since A ≠ C, we cannot directly rewrite.
// so we first get assumption from TermDiff: l = r ⊢ C = A
// then we have l = r, c0 ⊢ C = B. This is the new equality
// that can be used to rewrite c1.
// We return the new equality and the introduced assumption.
func diffAssumption(
	c0, c1 *Clause,
	equality *PropWrapper, c1SubTerm Term) (*PropWrapper, Term, bool) {
	trivialDiff := false // whether the term diff is trivial (just whole terms).
	rewriteLeft, rewriteRight := prop.TermDiff(c1SubTerm, Lhs(equality))
	var assumption Term
	if rewriteLeft != nil {
		l, r, _ := MatchesEQ(rewriteLeft.Hyp(0))
		if halfEq(l) || halfEq(r) {
			return nil, nil, false
		}
		if trivialAssumption(c0, c1, l, r) {
			return nil, nil, false
		}
		trivialDiff = l.AlphaEquals(c1SubTerm)
		assumption = rewriteLeft.Hyp(0)
		equality = rewriteLeft.EqTrans(equality)
	} else if rewriteRight != nil {
		l, r, _ := MatchesEQ(rewriteRight.Hyp(0))
		if halfEq(l) || halfEq(r) {
			return nil, nil, false
		}
		if trivialAssumption(c0, c1, l, r) {
			return nil, nil, false
		}
		trivialDiff = r.AlphaEquals(c1SubTerm)
		// make hyp always from subterm in c0 to subterm in c1.
		rewriteRight = prop.CommuteEQ(l, r).
			RightAssume().
			DeriveTrans(rewriteRight)
		assumption = rewriteRight.Hyp(0) // r = l
		equality = rewriteRight.
			EqSym().
			EqTrans(equality)
	} else {
		Assert(c1SubTerm.AlphaEquals(Lhs(equality)))
		return nil, nil, false
	}

	return equality, assumption, trivialDiff
}

// If either side of the assumption is from the whole
// specialized clause term, that side is known to be true or false,
// in which case it is not useful.
func trivialDiffAssumption(
	c0Specialized, c1Specialized *PropWrapper, assumption Term) bool {

	l, r, _ := MatchesEQ(assumption)
	if l.AlphaEquals(c1Specialized.Conclusion()) ||
		r.AlphaEquals(c0Specialized.Conclusion()) {
		return true
	}
	if n := MatchesNOT(c1Specialized.Conclusion()); n != nil &&
		l.AlphaEquals(n) {
		return true
	}
	if n := MatchesNOT(c0Specialized.Conclusion()); n != nil &&
		r.AlphaEquals(n) {
		return true
	}
	return false
}

// If one side of the assumption is a univeral quantifier,
// it is not useful, as the result could be also obtained by
// standard Resolve.
func trivialAssumption(c0, c1 *Clause, l, r Term) bool {
	if l, ok := l.AsVar(); ok &&
		(c0.univBoundVars.Has(l) || c1.univBoundVars.Has(l)) {
		return true
	}
	if r, ok := r.AsVar(); ok &&
		(c0.univBoundVars.Has(r) || c1.univBoundVars.Has(r)) {
		return true
	}
	return false
}

// Terms like "=x".
func halfEq(t Term) bool {
	if s, ok := t.AsAppliedTerm(); ok {
		if c, ok := s.Fun().AsConst(); ok {
			return c.Meta().Equals(core.MetaEq())
		}
	}
	return false
}

// Given a lit in specialized clause,
// returns an equality that based on that lit.
// For example, the clause is specialised to c ⊢ ... ∨ lit ∨ ...
// the equality would be lit ⊢ FlexibleEq(lit)
// where FlexibleEq transforms a lit term to equality.
// Since we have an extra lit hyp, we need to remove it.
// The returned operator helps to do this.
func makeLitResolveEquality(
	c0Specialized *PropWrapper,
	ind int,
	rewriteType _EqRewriteType) (*PropWrapper, utils.EndoFunc[*PropWrapper]) {

	ti := DecomposesOR(c0Specialized.Conclusion())[ind]
	var rest Term
	var equality *PropWrapper
	if ti.Equals(c0Specialized.Conclusion()) {
		equality = c0Specialized
	} else {
		c0Specialized = prop.ArrangeORChain(c0Specialized.Conclusion(), -1, ind).
			EqMP(c0Specialized)
		_, rest, _ = MatchesOR(c0Specialized.Conclusion())
		equality = prop.Assume(ti)
	}
	equality = flexibleEq(equality, rewriteType)

	var removeEqHyp utils.EndoFunc[*PropWrapper]
	if rest != nil {
		// removes ti hyp.
		removeEqHyp = func(thm *PropWrapper) *PropWrapper {
			return prop.TernaryThms["p ⇒ q, p ∨ r ⊢ q ∨ r"](ti, thm.Conclusion(), rest).
				DeriveHypFrom(thm.PromoteHyp(ti)).
				DeriveHypFrom(c0Specialized)
		}
	} else {
		removeEqHyp = utils.IdentityFunc
	}

	return equality, removeEqHyp
}

// Clause deduction can expose hidden boolean structure after rewriting.
// For example, a term that looked atomic at the clause layer may normalize to
// a conjunction such as ¬(p ⇒ q) ↦ p ∧ ¬q. ClauseThm, however, still expects
// each result theorem to conclude a single disjunctive clause. This helper
// normalizes the conclusion to CNF and splits a top-level conjunction into
// separate theorem results, so callers can return []*ClauseThm even when one
// deduction step produces multiple clause conclusions.
func makeConclDisjunct(thm *PropWrapper) []*PropWrapper {
	var thms []*PropWrapper
	if ext.IsDisjunctive(thm.Conclusion()) {
		thms = []*PropWrapper{thm}
	} else {
		w := cnfNormalizeWorkFlow(thm.Conclusion())
		if w == nil {
			// The workflow can decline (e.g. distribute-step timeout on a
			// pathological conclusion). No candidates then — same graceful
			// degrade as the non-disjunctive component skip below.
			return nil
		}
		thm = w.EqMP(thm)
		conclusions := ext.DecomposesAND(thm.Conclusion())
		for _, derivedConcl := range prop.HypANDRecursive(conclusions...) {
			if !ext.IsDisjunctive(derivedConcl.Conclusion()) {
				// Extremely rarely, a higher-order unifier can instantiate what
				// looked like an atomic clause literal with a logical binder. One
				// observed case was x' ↦ ∃: a clause containing x'(ẋ) normalized
				// after substitution to ∃ẋʹ.ẋ(ẋʹ), and Skolemization produced a
				// top-level ∃ƒ.∀... result rather than a disjunctive clause. Such a
				// candidate is outside ClauseThm's conclusion contract, so ignore
				// this derived component and keep any other valid CNF components.
				continue
			}
			thms = append(thms, thm.DeriveTrans(derivedConcl))
		}
	}
	return thms
}

// During proof search, Factor / Resolve discover an inference by running
// higher-order unification over many candidate subterms and delivering the
// results through channels. That search is concurrent and (because unification
// is wall-clock bounded) non-deterministic. Re-running that search at replay
// time would be both wasteful (the answer was already found once) and flaky (a
// loaded machine can time out before rediscovering the unifier).
//
// A deduceRecipe captures the one unifier that actually produced a clause thm,
// so replay can call the deterministic builder (factorClause / resolveClause /
// diffResolveClause) directly with the recorded substitution — no unification,
// no goroutines, no timeout. This is still sound: the builders re-derive the
// theorem through the kernel exactly as before; only the *search* for the
// unifier is skipped.

// _DeduceRule identifies which unification-based builder produced a clause thm.
type _DeduceRule int

const (
	_RuleFactor _DeduceRule = iota
	_RuleResolve
	_RuleDiffResolve
	_RuleContradicts
	_RuleSelfContradict
	_RuleSimplifies
	_RuleBoolSpecialize
	_RuleSimplifyBridge
	// _RuleFunext derives a function-typed equality clause from its
	// pointwise clause form(s): [c] = unit ∀-equality contraction,
	// [c0, c1] = complementary iff pair recombination. Search-free
	// deterministic builders (no unifier recorded). See funext.go.
	_RuleFunext
	// _RuleEqApply is the partial-application paramodulation of the nested
	// ALPHA-MERGE canonicalization: [eq, target] with substs pinning a
	// prefix of eq's λ-binders. Deterministic builder in alpha_bridge.go.
	_RuleEqApply
)

// deduceRecipe records the exact, deterministic inputs to one clause-inference
// builder, so replay reproduces it without re-searching for the unifier.
type deduceRecipe struct {
	rule _DeduceRule
	// The exact input clauses fed to the builder:
	//   _RuleFactor,
	//   _RuleSelfContradict: [c]   (factor: the original clause, before any
	//                              simplification bridge — factorReplay re-derives
	//                              the bridge);
	//   _RuleResolve,
	//   _RuleDiffResolve,
	//   _RuleContradicts:    [c0, c1] (already collision-renamed, as the builder
	//                              received them).
	inputs      []*Clause
	litIndex    int             // `ind` argument to the builder (factor/resolve)
	rewriteType _EqRewriteType  // resolve / diff-resolve only
	substs      TermSubstsGroup // the recorded unifier
	c1Subterm   Term            // diff-resolve only: the c1 subterm resolved against
	switchSide  bool            // contradicts only: the commuted-equality path
}

// reconstructFromRecipe rebuilds the base clause thm of a deduce step by
// replaying its recorded inference, then selecting the candidate that matches
// the recorded conclusion via conclMatch.
// Returns nil if the recorded inference does not reproduce the conclusion (a
// genuinely stale recipe), so the caller can surface a clear failure.
func reconstructFromRecipe(concl *Clause, r *deduceRecipe) *ClauseThm {
	var candidates []*ClauseThm
	switch r.rule {
	case _RuleFactor:
		Assert(len(r.inputs) == 1)
		candidates = factorReplay(r.inputs[0], r.substs, r.litIndex)
	case _RuleResolve:
		Assert(len(r.inputs) == 2)
		candidates = resolveClause(
			r.inputs[0], r.inputs[1], r.substs, r.litIndex, r.rewriteType)
	case _RuleDiffResolve:
		Assert(len(r.inputs) == 2)
		candidates = diffResolveClause(
			r.inputs[0], r.inputs[1], r.c1Subterm, r.substs, r.litIndex, r.rewriteType)
	case _RuleContradicts:
		Assert(len(r.inputs) == 2)
		candidates = []*ClauseThm{
			contradictsFromSubst(r.inputs[0], r.inputs[1], r.substs, r.switchSide)}
	case _RuleSelfContradict:
		Assert(len(r.inputs) == 1)
		candidates = []*ClauseThm{selfContradictFromSubst(r.inputs[0], r.substs)}
	case _RuleSimplifies:
		Assert(len(r.inputs) == 2)
		candidates = []*ClauseThm{r.inputs[0].Simplifies(r.inputs[1])}
	case _RuleBoolSpecialize:
		Assert(len(r.inputs) == 1)
		candidates = boolSpecialize(r.inputs[0])
	case _RuleSimplifyBridge:
		Assert(len(r.inputs) == 1)
		candidates = []*ClauseThm{simplifyBridgeReplay(r.inputs[0])}
	case _RuleFunext:
		Assert(len(r.inputs) == 1 || len(r.inputs) == 2)
		candidates = []*ClauseThm{funextReplay(r.inputs)}
	case _RuleEqApply:
		Assert(len(r.inputs) == 2)
		candidates = []*ClauseThm{eqApplyRewrite(r.inputs[0], r.inputs[1], r.substs)}
	default:
		panic("unknown deduce rule")
	}

	for _, clauseThm := range candidates {
		if clauseThm == nil {
			continue
		}
		if matched := conclMatch(clauseThm, concl); matched != nil {
			// The replay builders (factorClause/resolveClause/...) don't attach a
			// recipe — only the search-path delivery sites do. Stamp the known
			// recipe onto the result so the reconstructed thm stays self-describing
			// and re-serializes identically (DeserializeClauseThm now requires it).
			return matched.withRecipe(r)
		}
	}
	return nil
}

// simplifyBridgeReplay reproduces Factor's simplification-bridge step: the
// clause thm c.simplificationThm ⊢ c.equivalentClause (the first thing Factor
// delivers when the clause has a simplified equivalent). Search-free.
func simplifyBridgeReplay(c *Clause) *ClauseThm {
	if c.simplificationThm.IsZero() {
		return nil
	}
	conclClause := c.equivalentClause
	if conclClause == nil || conclClause.EquatesT() {
		return nil
	}
	return MakeClauseThm(
		WrapProp(c.simplificationThm).LeftAssume().AsThmCert(), conclClause, c)
}

// factorReplay deterministically reproduces Factor's factoring of a single
// clause for one recorded (subst, litIndex). It mirrors exactly the
// simplification-bridge prologue in Factor (deduce.go) — which can replace the
// clause with its simplified equivalent and post-compose a bridge theorem to
// restore the original hypothesis — and then calls factorClause directly with
// the recorded unifier instead of searching for it.
func factorReplay(c *Clause, subst TermSubstsGroup, ind int) []*ClauseThm {
	var bridgeThm *ClauseThm
	if !c.simplificationThm.IsZero() {
		thm := WrapProp(c.simplificationThm).LeftAssume()
		conclClause := c.equivalentClause
		if conclClause.EquatesT() {
			return nil
		}
		bridge := MakeClauseThm(thm.AsThmCert(), conclClause, c)
		if !thm.Conclusion().Equals(F) {
			c = conclClause
			bridgeThm = bridge
		}
	}

	results := factorClause(c, subst, ind)
	if bridgeThm != nil {
		for i, clauseThm := range results {
			results[i] = clauseThm.DeriveHypFrom(bridgeThm)
		}
	}
	return results
}
