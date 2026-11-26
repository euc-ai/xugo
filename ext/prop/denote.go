package prop

import (
	"context"
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Given a variable x and a term s, returns a rewrite that replaces all occurrences
// of s in the term with x.
// For example, the rewrite will transform P(s) to
// x = s ⊢ P(s) = P(x)
// The typical use case is when s is a subterm of t which we want
// to denote by an introduced variable x.
func DenoteRewrite(x VarTerm, s Term) Rewrite {
	return DenoteRewriteUnder(context.Background(), x, s)
}

// DenoteRewriteUnder is DenoteRewrite under a caller's context: the
// unifications that fold the instances of a denoted λ end with ctx
// (unifyEqRewriteAbsPermuted). A rewrite that ran past the end of ctx
// folded what it had reached and no more, so its result stands for
// nothing: the caller reads ctx before the result, and abandons.
func DenoteRewriteUnder(ctx context.Context, x VarTerm, s Term) Rewrite {
	if s, ok := s.AsAbsTerm(); ok {
		// Permuted-wrap mode: a denoted atom must fold EVERY instance
		// of its λ — a site under enclosing binders in a different
		// order than the λ's own would otherwise silently stay
		// unfolded, and the clause set then mixes the atom with raw
		// expansions the refuter cannot bridge.
		return unifyEqRewriteAbsPermuted(ctx, Assume(Eq(x, s)).EqSym())
	}
	return EqRewrite(Assume(Eq(x, s)).EqSym())
}

// Rewrites term with a given subterm by introducing new vars.
// E.g. s appears many times in t, then t can be rewritten as
// ⊢ t = ∀x.((x = s) ⇒ P)
// where P is a function of x such that P[x ↦ s] = t.
// If s is under abstraction of v in t, we cannot directly let x = s,
// rather we define x := λv.s(v), and rewrite t as
// ⊢ t = ∀x.((x = λv.s(v)) ⇒ P).
func ForAllDenoteRewrite(s Term) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if !IsBool(t) {
			return nil
		}
		// Create new variable x with same type as s,
		// ensuring its name doesn't conflict with s and t
		x := core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), s.Type()).
			RenameToAvoid(s, t)

		// We cannot use ForAllDenote theorem because
		// we don't know the exact form of λx.P(x)
		// which can not be easily obtained by s and t
		// (we want λx.P(x)(s) = t, i.e. we need to `extract` s from t.
		// So we use DenoteRewrite to do the unify matching.

		// Apply equation x = s to replace s in t with x.
		// Handle two cases:
		// 1. x = s  ⊢ t = P(x)  (direct replacement)
		// 2. x = λv.s(v) ⊢ t = P(x) (for abstract terms, preserve variable binding)
		w := DenoteRewrite(x, s)(t)
		if w == nil {
			return nil
		}
		Assert(w.NumHyps() == 1 && Lhs(w).AlphaEquals(t))

		xEq, _t := w.Hyp(0), Rhs(w)

		// Construct theorem: ∀x.((x = s) ⇒ P) ⊢ t
		// Apply equation x = s, instantiate universal quantifier, remove hypothesis
		u := w.
			EqSym().
			EqMP(ModusPonens(xEq, _t)).
			HypForAllInst(x, WrapTerm(xEq).Imply(_t)).
			RemoveVarHyp(x)

		// Construct theorem: t ⊢ ∀x.((x = s) ⇒ P)
		// Introduce hypothesis x = s, then abstract to universal quantifier
		v := w.
			LeftAssume().
			PromoteHyp(xEq).
			ConclForAll(x)

		// Combine theorems to get: ⊢ t = ∀x.((x = s) ⇒ P)
		return u.Deduct(v)
	}
	return verifyRewrite(rewrite)
}

// This is the reverse direction of ForAllDenoteRewrite.
// It rewrites ∀x.((x = s) ⇒ P) to P[x ↦ s].
func ForAllUndenoteRewrite(t Term) *PropWrapper {
	s := MatchesFORALL(t)
	if s.IsZero() {
		return nil
	}
	denoteEq, rest, ok := MatchesIMPLY(s.Body())
	if !ok {
		return nil
	}
	v, denote, ok := MatchesEQ(denoteEq)
	if !ok ||
		!v.Equals(s.Var()) ||
		denote.HasFree(s.Var()) {
		return nil
	}
	return ForAllDenote(s.Var(), denote, Abs(s.Var(), rest)).EqSym()
}

// Rewrites term with a given subterm by introducing new vars.
// E.g. s appears many times in t, then t can be rewritten as
// ⊢ t = ∃x.((x = s) ∧ P)
// where P is a function of x such that P[x ↦ s] = t.
// If s is under abstraction of v in t, we cannot directly let x = s,
// rather we define x := λv.s(v), and rewrite t as
// ⊢ t = ∃x.((x = λv.s(v)) ∧ P).
func ExistsDenoteRewrite(s Term) Rewrite {
	return ExistsDenoteRewriteUnder(context.Background(), s)
}

// ExistsDenoteRewriteUnder is ExistsDenoteRewrite under a caller's
// context (DenoteRewriteUnder).
func ExistsDenoteRewriteUnder(ctx context.Context, s Term) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if !IsBool(t) {
			return nil
		}
		// Create new variable x with same type as s,
		// ensuring its name doesn't conflict with s and t
		x := core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), s.Type()).
			RenameToAvoid(s, t)

		// We cannot use ExistsDenote theorem because
		// we don't know the exact form of λx.P(x)
		// which can not be easily obtained by s and t
		// (we want λx.P(x)(s) = t, i.e. we need to `extract` s from t.
		// So we use DenoteRewrite to do the unify matching.

		// Apply equation x = s to replace s in t with x.
		// Handle two cases:
		// 1. x = s  ⊢ t = P(x)  (direct replacement)
		// 2. x = λv.s(v) ⊢ t = P(x) (for abstract terms, preserve variable binding)
		w := DenoteRewriteUnder(ctx, x, s)(t)
		if w == nil {
			return nil
		}
		Assert(w.NumHyps() == 1 && Lhs(w).AlphaEquals(t))

		xEq, _t := w.Hyp(0), Rhs(w)

		// Construct theorem: (x = s) ∧ P ⊢ t
		// Apply equation through conjunction rules
		u := w.
			RightAssume().
			DeriveHypFrom(HypAND0(xEq, _t)).
			DeriveHypFrom(HypAND1(xEq, _t))

		// Introduce existential quantifier: ∃x.((x = s) ∧ P) ⊢ t
		u = u.HypExists(x, u.Hyp(0))

		// Construct theorem: t ⊢ ∃x.((x = s) ∧ P)
		// Derive conjunction (x = s) ∧ P from t,
		// then introduce existential quantifier
		v := w.
			LeftAssume().
			DeriveTrans(ConclAND(xEq, _t)).
			ConclExistsInst(x).
			RemoveVarHyp(x)

		// Combine theorems to get: ⊢ t = ∃x.((x = s) ∧ P)
		return u.Deduct(v)
	}
	return verifyRewrite(rewrite)
}

// This is the reverse direction of ExistsDenoteRewrite.
// It rewrites ∃x.((x = s) ∧ P) to P[x ↦ s].
func ExistsUndenoteRewrite(t Term) *PropWrapper {
	s := MatchesEXISTS(t)
	if s.IsZero() {
		return nil
	}
	denoteEq, rest, ok := MatchesAND(s.Body())
	if !ok {
		denoteEq = s.Body()
	}
	v, denote, ok := MatchesEQ(denoteEq)
	if !ok ||
		!v.Equals(s.Var()) ||
		denote.HasFree(s.Var()) {
		return nil
	}
	if rest == nil {
		// ⊢ ∃v.(v = s) = ⊤
		return QuantifierRewrite(t)
	}
	return ExistsDenote(s.Var(), denote, Abs(s.Var(), rest)).EqSym()
}

/**
 * HilbertDenote handles Hilbert ε terms by introducing new variables
 * and appropriate existential theorems to replace them.
 *
 * Given a term containing Hilbert (ε) operators, this function:
 * 1. Identifies a subterm containing an ε operator
 * 2. Introduces a new variable to replace this subterm
 * 3. Creates an equation relating the new variable to the ε term
 * 4. Generates two important theorems:
 *    - A simplification theorem that equates the original term with the new variable
 *    - An existential theorem that captures the semantic meaning of the ε term
 *
 * For example, given term ∀y.P(εx.f(x, y)):
 * - It introduces a new variable α₀
 * - Creates the simplification theorem: α₀ = (λy.(εx.f(x, y))) ⊢ (∀y.P(εx.f(x, y))) = (∀y.P(α₀(y)))
 * - Creates the existential theorem: α₀ = (λy.(εx.f(x, y))) ⊢ ∀y.((∃x.f(x, y)) ⇒ f(α₀(y), y))
 *
 * This transformation allows for elimination of ε terms from goals, replacing them
 * with normal variables plus appropriate existential constraints, which are often easier
 * to work with in formal proofs.
 *
 * Parameters:
 *   - t: The term containing ε operators to transform
 *   - avoid: A list of terms whose free variables should be avoided when naming the new variable
 *
 * Returns:
 *   - A simplification theorem
 *   - An existential theorem
 *   - The newly introduced variable
 *   - Or nil for all three if no ε term is found
 */
func HilbertDenote(t Term, avoid []Term) (*PropWrapper, *PropWrapper, VarTerm) {
	simplify, existential, x, _ := HilbertDenoteSelect(t, avoid)
	return simplify, existential, x
}

// HilbertDenoteSelect is HilbertDenote that also RETURNS the ε-subterm
// it selected. The selection is a search decision; a caller that records
// the step needs the decision itself, not the search that produced it
// (see prover/tactic's DenoteSelection).
func HilbertDenoteSelect(t Term, avoid []Term) (*PropWrapper, *PropWrapper, VarTerm, Term) {
	s := ext.HilbertSubTerm(t)
	if s == nil {
		return nil, nil, VarTerm{}, nil
	}
	simplify, existential, x := HilbertDenoteAt(t, s, "", avoid, false)
	Assert(simplify != nil)
	return simplify, existential, x, s
}

// HilbertDenoteAt is HilbertDenote with the ε-subterm GIVEN rather than
// searched for, and (optionally) with the denoting variable's name
// given too — the explicit form a recorded step replays as.
//
// Returns nil for all three when `s` does not occur in `t`, so a caller
// scanning a goal's hypotheses can try the next one. Panics when `s` is
// not an ε-term at all: unlike absence, that is a malformed request, not
// a miss.
//
// An empty name mints the default α₀, renamed past every name `avoid`
// spells; a given name is used verbatim and is never silently renamed
// — it is part of the record. A name already free in `avoid` panics,
// unless `optionalName`, which returns nil instead: that is the
// per-leaf shaping caller, for whom "the name is taken here" means the
// shaping already fired on the branch this leaf was split from. A name
// `avoid` merely binds is accepted: where the ε-term occurs under such
// a binder, the rewrite renames the binder apart from the name.
func HilbertDenoteAt(t Term, s Term, name string, avoid []Term, optionalName bool) (*PropWrapper, *PropWrapper, VarTerm) {
	vars, body := ext.MatchesAbs(s)
	app, ok := body.AsAppliedTerm()
	if !ok {
		panic(fmt.Sprintf("HilbertDenoteAt: %s is not an ε-term", ext.PrintTerm(s)))
	}
	if fun, ok := app.Fun().AsConst(); !ok || !fun.Meta().Equals(core.MetaHilbert()) {
		panic(fmt.Sprintf("HilbertDenoteAt: %s is not an ε-term", ext.PrintTerm(s)))
	}
	var x VarTerm
	if name == "" {
		x = core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), s.Type()).
			RenameToAvoid(avoid...)
	} else {
		x = core.Var(TermName(name), s.Type())
		if utils.Any(avoid, utils.Curry(Term.HasFreeName, x.Name())) {
			if optionalName {
				return nil, nil, VarTerm{}
			}
			panic(fmt.Sprintf("HilbertDenoteAt: the name %q is already free in the goal — "+
				"pick a name the argument does not already use", name))
		}
	}

	rewrite := DenoteRewrite(x, s)
	simplify := rewrite(t)
	if simplify == nil {
		return nil, nil, VarTerm{}
	}

	existential := SelectExists(app.Arg())
	existential = existential.PromoteHyp(existential.Hyp(0))
	for _, v := range slices.Backward(vars) {
		existential = existential.ConclForAll(v)
	}
	existential = existential.RewriteConcl(rewrite)
	return simplify, existential, x
}

// Rewrites ∀x.((x ≠ s) ∨ P) to P[x ↦ s].
// This is similar to ForAllUndenoteRewrite,
// but works for a general disjuntive clause, i.e.
// there can be multiple universal quantifiers,
// and the neq term (x ≠ s) can be in any literal position.
// This is useful to simplify disjunctive clauses.
func ClauseFactorRewrite(t Term) *PropWrapper {

	rewrite := func(t Term) *PropWrapper {
		vars, body := DecomposesFORALL(t)
		if vars.Empty() {
			return nil
		}
		lits := DecomposesOR(body)
		x, idx, varRight, transform, neq := locateNegVarEq(&vars, lits)
		if x.IsZero() {
			return nil
		}

		var w *PropWrapper
		if len(lits) == 1 {
			// ∀x.(x ≠ s) = ⊥
			w = BasicRewrite(ForAll(x)(lits[0]))
		} else {
			// Make the Rhs of w have the form of
			// ((x ≠ s) ∨ _) or ((s ≠ x) ∨ _).
			w = ArrangeORChain(body, -1, idx)
			_, rest, _ := MatchesOR(Rhs(w))
			if transform != nil {
				w = w.EqTrans(transform.LeftApply(OR).RightApply(rest))
			}

			denoteEq := MatchesNOT(neq)
			Assert(denoteEq != nil)
			denoteVar, denote, ok := MatchesEQ(denoteEq)
			if varRight {
				denoteVar, denote = denote, denoteVar
			}
			Assert(ok && denoteVar.Equals(x))

			// Make the Rhs of w have the form of
			// ((x = s) ⇒ _) or ((s = x) ⇒ _).
			w = w.EqTrans(BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](denoteEq, rest).EqSym())

			// Switch (s = x) to (x = s) if needed.
			if varRight {
				u := CommuteEQ(denote, x).
					LeftApply(IMPLY).
					RightApply(rest)
				w = w.EqTrans(u)
			}

			// Make the Rhs of w have the form of ∀x.((x = s) ⇒ _).
			w = w.Abs(x).LeftApply(makeQuantifierConst(FORALL, x.Type()))

			// This is where the real rewrite happens.
			// ⊢ ∀x.((x = s) ⇒ P) = P[x ↦ s]
			rewriteEq := ForAllDenote(x, denote, Abs(x, rest)).
				EqSym().
				RewriteConclRhs(BoolRewrite)
			w = w.EqTrans(rewriteEq)
		}
		return forallReorderHelper(t, &vars, x, w)
	}
	rewrite = verifyRewrite(rewrite)
	if w := rewrite(t); w != nil {
		return w.RewriteConclRhsRecur(rewrite)
	}
	return nil
}

// Find the first literal that has the form of (x ≠ s) or equivalent.
// Return the variable x, the index of the literal,
// whether x is on the right side of the equation,
// the transformation to make the literal into (x ≠ s),
// and the transformed term in the form of (x ≠ s).
func locateNegVarEq(vars *VarList, lits []Term) (
	VarTerm, int, bool, *PropWrapper, Term) {

	var x VarTerm
	var transform *PropWrapper
	var neq Term
	idx, varRight := -1, false
	for i, lit := range lits {
		if n := MatchesNOT(lit); n != nil {
			if l, r, ok := MatchesEQ(n); ok {
				if l, ok := l.AsVar(); ok &&
					vars.Has(l) &&
					!r.HasFree(l) {
					neq, idx, x = lit, i, l
					break
				}
				if r, ok := r.AsVar(); ok &&
					vars.Has(r) &&
					!l.HasFree(r) {
					neq, idx, x, varRight = lit, i, r, true
					break
				}
			}
			// ¬x can be seen as (x ≠ ⊤) if x is a boolean var.
			if n, ok := n.AsVar(); ok && IsBool(n) && vars.Has(n) {
				idx, x = i, n
				// ¬x ⇔ (x ≠ ⊤)
				transform = DeepBoolRewrite(Not(Eq(n, T))).EqSym()
				neq = Rhs(transform)
				break
			}
		}
		// x = r can be seen as (x ≠ ¬r) if x is a boolean var.
		if l, r, ok := MatchesEQ(lit); ok && IsBool(l) {
			if l, ok := l.AsVar(); ok &&
				vars.Has(l) &&
				!r.HasFree(l) {
				idx, x = i, l
				// (x = r) ⇔ (x ≠ ¬r)
				transform = PushNegRewrite(Not(Eq(l, Not(r)))).EqSym()
				neq = Rhs(transform)
				break
			}
			// ¬x = r can be seen as (x ≠ r) if x is a boolean var.
			if n := MatchesNOT(l); n != nil {
				if n, ok := n.AsVar(); ok &&
					vars.Has(n) &&
					!r.HasFree(n) {
					idx, x = i, n
					// (¬x = r) ⇔ (x ≠ r)
					transform = PushNegRewrite(Not(Eq(n, r))).EqSym()
					neq = Rhs(transform)
					break
				}
			}
			// l = x can be seen as (¬l ≠ x) if x is a boolean var.
			if r, ok := r.AsVar(); ok &&
				vars.Has(r) &&
				!l.HasFree(r) {
				idx, x, varRight = i, r, true
				// (l = x) ⇔ (¬l ≠ x)
				transform = DoubleNeg(lit).
					EqSym().
					EqTrans(PushNegRewrite(Not(lit)).LeftApply(NOT))
				neq = Rhs(transform)
				break
			}
			// l = ¬x can be seen as (l ≠ x) if x is a boolean var.
			if n := MatchesNOT(r); n != nil {
				if n, ok := n.AsVar(); ok &&
					vars.Has(n) &&
					!l.HasFree(n) {
					idx, x, varRight = i, n, true
					// (l = ¬x) ⇔ (l ≠ x)
					transform = DoubleNeg(lit).
						EqSym().
						EqTrans(PushNegRewrite(Not(lit)).LeftApply(NOT))
					neq = Rhs(transform)
					break
				}
			}
		}
		// x can be seen as (x ≠ ⊥) if x is a boolean var.
		if lit, ok := lit.AsVar(); ok && IsBool(lit) && vars.Has(lit) {
			neq, idx, x = Not(Eq(lit, F)), i, lit
			// x ⇔ (x ≠ ⊥)
			transform = DeepBoolRewrite(neq).
				RewriteConclRhs(DoubleNegRewrite).
				EqSym()
			break
		}
	}
	return x, idx, varRight, transform, neq
}
