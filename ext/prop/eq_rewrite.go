package prop

import (
	"context"
	"iter"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

// EqRewrite constructs a top-down, structure-aware rewrite from an equality theorem.
//
// Given an equality ⊢ l = r, it traverses a term top-down and replaces every
// occurrence of l with r, producing ⊢ t = t' where t' is the rewritten term.
// For example, given ⊢ l = r, rewriting f(l) produces ⊢ f(l) = f(r).
//
// Returns NilRewrite if l is a subterm of r (e.g. ⊢ l = l + 0), since
// applying this rewrite recursively would loop.
//
// The rewrite is non-recursive: it rewrites each match once without
// re-examining the result. For example, given ⊢ x + y = y, rewriting
// (x + y) + y produces ⊢ (x + y) + y = (x + y), not ⊢ (x + y) + y = y.
// Use RewriteConclRhsRecur to apply recursively.
//
// Abstraction-aware matching:
// The LHS l may be an abstraction like λx.P(x). In that case, the rewrite
// matches l structurally against abstracted subterms. Specifically, to rewrite
// inside ∃x.Q(P(x)), the LHS must be the abstracted form λx.P(x), not P(x).
//   - ⊢ λx.P(x) = ... WILL rewrite ∃x.Q(P(x)) (matches the abstracted body)
//   - ⊢ P(x) = ...     will NOT rewrite ∃x.Q(P(x)) (x is bound, no structural match)
//
// No β-matching is performed: ⊢ λx.P(x) = ... will NOT rewrite a bare P(x),
// because P(x) is not structurally identical to the abstraction λx.P(x).
// Use unifyEqRewrite for β-matching via unification.
//
// When the equality has hypotheses, bound variables that are free in any
// hypothesis are renamed to avoid capture (handled by RewriteSubTermsWithEnv).
func EqRewrite(eq Prop) Rewrite {
	return eqRewriteImpl(eq, "")
}

// eqRewriteCarrying is EqRewrite that does not enter a subterm without
// the constant name when both spellings of l the walk matches — l's body
// and its βη-contracted form — carry name: every occurrence then carries
// it, so the walk costs the part of the term that carries name (core
// memoizes HasName per node). The result is EqRewrite's.
func eqRewriteCarrying(eq Prop, name core.TermName) Rewrite {
	return eqRewriteImpl(eq, name)
}

// eqRewriteImpl enters only subterms carrying name; the empty name
// enters every subterm.
func eqRewriteImpl(eq Prop, name core.TermName) Rewrite {
	l, r, ok := MatchesEQ(eq.Conclusion())
	Assert(ok)
	if ext.IsSub(l, r) {
		return NilRewrite
	}

	// Collect the type at each abstraction level of l.
	// E.g. for l = λx:A.λy:B.body:C, types = [A→B→C, B→C, C].
	// A term can only match l at some level if its type is one of these.
	_l, types := l, []HolType{l.Type()}
	for abs, ok := _l.AsAbsTerm(); ok; abs, ok = _l.AsAbsTerm() {
		_l, types = abs.Body(), append(types, abs.Body().Type())
	}

	// Decompose l into its abstracted vars and body.
	// E.g. l = λx.λy.P(x,y) → lVars = [x, y], lBody = P(x,y).
	lVars, lBody := MatchesAbs(l)
	// An η-redex pattern λx̄.h(x̄) stands for h: an occurrence of h itself
	// is an instance of it, and ⊢ h = r follows by η (DeepBetaEta gives
	// the pattern's βη-normal form, which is h when the pattern is an
	// η-redex and l itself otherwise). This is what lets a clause's absEq
	// (λx̄.A(x̄) = λx̄.⊥, from ∀x̄.¬A(x̄)) reach an η-short occurrence of
	// the symbol A in argument position, G(A) — the spelling the
	// normalizer's η leaves there. The self-embedding guard above applies
	// to this spelling of the pattern too: a rule λẋ.E(x, ẋ) = λẋ.D(E(x),
	// ẋ) rewrites applications of E(x) once, but must not fold the bare
	// E(x) its own right side carries.
	var lContracted Term
	var eqContracted *PropWrapper
	if w := DeepBetaEta(l); w != nil && !ext.IsSub(Rhs(w), r) {
		lContracted, eqContracted = Rhs(w), w.EqSym().EqTrans(eq)
	}
	// A β-step can drop the argument that carried name; the walk then
	// enters every subterm.
	if name != "" && (!ext.TermContainsConstName(lBody, name) ||
		lContracted != nil && !ext.TermContainsConstName(lContracted, name)) {
		name = ""
	}
	// makeRewrite builds the recursive closure pair; cache == nil is the
	// plain zero-allocation path, non-nil the per-top-call shared-DAG memo
	// (see envScopeCache — results depend only on (term, binder env), so
	// pointer-shared subtrees under α-identical binder paths reuse both
	// nil and non-nil results, collapsing the naive O(2^depth) walk).
	makeRewrite := func(cache *envScopeCache) RewriteWithEnv {
		var rewrite, subTermsRewrite RewriteWithEnv
		rewrite = func(t Term, env ...VarTerm) *PropWrapper {
			if name != "" && !t.HasName(name) {
				return nil
			}
			if w, ok := cache.Load(env, t); ok {
				return w
			}
			var w *PropWrapper
			matched := false
			if utils.Any(types, t.Type().Equals) {
				// Type matches one of l's abstraction levels.
				// Try to reconstruct an abstraction from t using its free env vars
				// and check if it is α-equal to l.
				// E.g. if l = λx.P(x) and t = P(a) under env [a],
				// then ReverseAbsFreeVarsMatch rebuilds λa.P(a) ≡α λx.P(x).
				vars, match := ext.ReverseAbsFreeVarsMatch(lVars, lBody)(t, env...)
				if !match && lContracted != nil && lContracted.AlphaEquals(t) {
					matched = true
					if !Rhs(eqContracted).AlphaEquals(t) {
						w = eqContracted
					}
				} else if match {
					matched = true
					// Instantiate the equality by applying l to each matched var,
					// then β-reducing to expose the concrete subterm.
					// E.g. ⊢ λx.P(x) = r  →  ⊢ (λx.P(x))(a) = r(a)  →  ⊢ P(a) = r(a)
					_eq := WrapProp(eq)
					for _, v := range vars {
						rhs, rhsAbs := Rhs(_eq).AsAbsTerm()
						_eq = _eq.
							RightApply(v).
							RewriteConcl(DeepBetaAbs(Lhs(_eq).(AbsTerm)))
						if rhsAbs {
							_eq = _eq.RewriteConclRhs(DeepBetaAbs(rhs))
						}
					}
					Assert(Lhs(_eq).AlphaEquals(t))
					// Guard against trivial identity rewrites (e.g. after instantiation
					// both sides become the same term). On identity, w stays nil
					// WITHOUT descending into subterms.
					if !Rhs(_eq).AlphaEquals(t) {
						w = WrapProp(_eq)
					}
				}
			}
			if !matched {
				w = subTermsRewrite(t, env...)
			}
			cache.Store(env, t, w)
			return w
		}

		// Recurse into immediate subterms. Since rewrite is passed as the
		// callback, the traversal naturally goes top-down through the full term.
		// Uses RewriteSubTermsWithEnv (not rewriteSubTerms) to track bound
		// variables and avoid capture conflicts with the equality's hypotheses.
		subTermsRewrite = RewriteSubTermsWithEnv(rewrite, eq.AnyHyp)
		return rewrite
	}

	// Pre-allocate the plain closure pair so small-term calls allocate
	// nothing; the memoized pair is rebuilt per top-level call so the cache
	// never outlives (or races across) a call.
	plain := makeRewrite(nil)
	return func(t Term) *PropWrapper {
		if cache := ext.EnvMemoFor[*PropWrapper](t); cache != nil {
			return makeRewrite(cache)(t)
		}
		return plain(t)
	}
}

// EqReplacementRewrite constructs a simple find-and-replace rewrite from an equality.
//
// Given ⊢ l = r, it finds every α-equal occurrence of l in a term and replaces
// it with r, producing ⊢ t = t'. Returns NilRewrite if l and r are identical.
//
// Unlike EqRewrite, this function does NOT perform abstraction-aware matching.
// It treats bound variables as transparent and simply pattern-matches on the
// term structure. This means:
//   - ⊢ P(x) = Q(x) WILL rewrite ∃x.P(x) to ⊢ ∃x.P(x) = ∃x.Q(x),
//     even though x is bound by ∃. It simply finds P(x) and replaces it.
//
// However, when the equality has hypotheses with free variables that collide
// with bound variables, the rewrite is blocked. For example:
//   - R(x) ⊢ P(x) = Q(x) CANNOT rewrite ∃x.P(x), because x is free in
//     the hypothesis R(x) and bound by ∃, making the substitution unsound.
//     (This safety check is enforced by RewriteSubTermsWithEnv.)
//
// Safe with expansive equalities: unlike EqRewrite, this function does not
// check ext.IsSub(l, r), so it works with equalities like ⊢ l = l + 0.
// Since the match is exact (α-equality, not subterm matching), each occurrence
// is replaced at most once and there is no risk of infinite expansion.
func EqReplacementRewrite(eq Prop) Rewrite {
	l, r, ok := MatchesEQ(eq.Conclusion())
	Assert(ok)
	if l.Equals(r) {
		return NilRewrite
	}

	// makeRewrite builds the recursive closure pair; cache == nil is the
	// plain zero-allocation path. The walk ignores the binder env entirely
	// (both closures discard it), so the size-gated per-top-call memo is a
	// bare term-pointer PtrMemo, not an envScopeCache.
	makeRewrite := func(cache *ext.PtrMemo[*PropWrapper]) Rewrite {
		var rewrite Rewrite
		var subTermsRewrite RewriteWithEnv

		rewrite = func(t Term) *PropWrapper {
			if w, ok := cache.Load(t); ok {
				return w
			}
			var w *PropWrapper
			// Direct α-equality check — no abstraction decomposition.
			if t.AlphaEquals(l) {
				w = WrapProp(eq)
			} else {
				w = subTermsRewrite(t)
			}
			cache.Store(t, w)
			return w
		}

		// Uses RewriteSubTermsWithEnv (not rewriteSubTerms) to check eq's
		// hypotheses against bound variables, even though the rewrite itself
		// ignores the env. This prevents unsound rewrites when a hypothesis
		// has a free variable that collides with a binder.
		subTermsRewrite = RewriteSubTermsWithEnv(
			func(t Term, _ ...VarTerm) *PropWrapper { return rewrite(t) },
			eq.AnyHyp)

		return rewrite
	}

	plain := makeRewrite(nil)
	return func(t Term) *PropWrapper {
		if cache := ext.PtrMemoFor[*PropWrapper](t); cache != nil {
			return makeRewrite(cache)(t)
		}
		return plain(t)
	}
}

// EqReplacementRewriteWithPrune is EqReplacementRewrite that short-circuits
// on every subterm not mentioning any Const named `pruneConstName`.
// Semantically identical to EqReplacementRewrite when the input eq's
// LHS is a Const-headed term whose head name equals `pruneConstName` —
// the check merely elides the walk into subtrees that can't contain the
// LHS. Use this only when the extra const-name walk is cheaper than
// attempting the rewrite below that subtree.
//
// Empty `pruneConstName` disables pruning — degenerates to plain
// EqReplacementRewrite behavior.
func EqReplacementRewriteWithPrune(eq Prop, pruneConstName TermName) Rewrite {
	l, r, ok := MatchesEQ(eq.Conclusion())
	Assert(ok)
	if l.Equals(r) {
		return NilRewrite
	}

	// Same env-free walk as EqReplacementRewrite — bare term-pointer memo,
	// size-gated (see EqReplacementRewrite).
	makeRewrite := func(cache *ext.PtrMemo[*PropWrapper]) Rewrite {
		var rewrite Rewrite
		var subTermsRewrite RewriteWithEnv

		rewrite = func(t Term) *PropWrapper {
			if w, ok := cache.Load(t); ok {
				return w
			}
			var w *PropWrapper
			// Recursive short-circuit — because subTermsRewrite below calls
			// back into this closure at every descent, the prune applies at
			// every level, not just the outermost.
			if pruneConstName != "" && !ext.TermContainsConstName(t, pruneConstName) {
				// w stays nil
			} else if t.AlphaEquals(l) {
				w = WrapProp(eq)
			} else {
				w = subTermsRewrite(t)
			}
			cache.Store(t, w)
			return w
		}

		subTermsRewrite = RewriteSubTermsWithEnv(
			func(t Term, _ ...VarTerm) *PropWrapper { return rewrite(t) },
			eq.AnyHyp)

		return rewrite
	}

	plain := makeRewrite(nil)
	return func(t Term) *PropWrapper {
		if cache := ext.PtrMemoFor[*PropWrapper](t); cache != nil {
			return makeRewrite(cache)(t)
		}
		return plain(t)
	}
}

// contextEq converts a term into a conditional equality with that term as
// the sole hypothesis. The result always has the larger side on the LHS so
// that rewriting with it reduces term size.
//
// Conversion rules:
//   - Equality:  (l = r)  →  l = r ⊢ r = l   (swapped so that the bigger side is on the LHS)
//     or l = r ⊢ l = r (if l is already ≥ r in size)
//   - Negation:  ¬P      →  ¬P ⊢ P = ⊥       (via EqualsFalse)
//   - Truth:     ⊤       →  ⊤ ⊢ ⊤ = ⊤        (degenerate case)
//   - Other:     P       →  P ⊢ P = ⊤         (any true proposition equals ⊤)
func contextEq(t Term) *PropWrapper { return contextEqOpt(t, false) }

// noSwap controls whether the bigger-side-on-LHS swap disabled.
func contextEqOpt(t Term, noSwap bool) *PropWrapper {
	var eq *PropWrapper
	if l, r, ok := MatchesEQ(t); ok {
		eq = Assume(t)
		if !noSwap && contextEqSwaps(l, r) {
			eq = eq.EqSym()
		}
	} else if n := ext.MatchesNOT(t); n != nil {
		eq = EqualsFalse(n).RightAssume()
	} else {
		if t.Equals(T) {
			eq = DerivesTrue.Deduct(Refl(T)).LeftAssume()
		} else {
			eq = Assume(t).Deduct(DerivesTrue)
		}
	}
	Assert(eq.Hyp(0).Equals(t))
	return eq
}

// contextEqSwaps decides whether `l = r` is read right-to-left: the
// larger side goes on the LHS so the rewrite shrinks its target. One
// exception: a bare VARIABLE against a numeral literal always reads
// variable → numeral. By raw size a literal is the larger side (`1` is
// bit1(_0), two symbols) and `p = 1` would read `1 → p`, rewriting the
// literal — and the `1` inside `2`'s tower — into a variable the
// arithmetic closer cannot evaluate (measured: `2 ≤ p` became
// `bit0(p) ≤ p`). A variable's value is the literal, never the other
// way round. Compound terms keep the size rule, towers included: a
// datatype door's tag reasoning rewrites `1` into `suc(0)` inside a
// larger tag on purpose, and the value is the same.
func contextEqSwaps(l, r Term) bool {
	if isVarTerm(l) && isNumeralLiteral(r) {
		return false
	}
	if isNumeralLiteral(l) && isVarTerm(r) {
		return true
	}
	return l.Size() < r.Size()
}

// isVarTerm reports whether t is a (free) variable.
func isVarTerm(t Term) bool {
	_, ok := t.AsVar()
	return ok
}

// isNumeralLiteral reports whether t is a ground BIT tower — a numeral
// literal, canonical or not.
func isNumeralLiteral(t Term) bool {
	_, ok := ext.NumeralValue(t)
	return ok
}

// ContextAbsEq is the universally-quantified generalization of contextEq.
//
// It strips leading ∀-quantifiers from the input term, applies contextEq to the
// body, then re-abstracts over the quantified variables to produce an equality
// between lambda terms. The original (quantified) term becomes the sole hypothesis.
//
// Conversion examples:
//   - ∀x.(P(x) = Q(x))  →  ∀x.(P(x) = Q(x)) ⊢ λx.P(x) = λx.Q(x)
//     (sides swapped if needed so the bigger side is on the LHS)
//   - ∀x.¬P(x)           →  ∀x.¬P(x) ⊢ λx.P(x) = λx.⊥
//   - ∀x.P(x)            →  ∀x.P(x) ⊢ λx.P(x) = λx.⊤
//
// For a non-quantified term (no leading ∀), this behaves identically to contextEq.
func ContextAbsEq(t Term) *PropWrapper { return contextAbsEqOpt(t, false) }

func contextAbsEqOpt(t Term, noSwap bool) *PropWrapper {
	vars, body := DecomposesFORALL(t)
	absEq := contextEqOpt(body, noSwap)
	// Re-abstract: for each quantified variable (inner to outer),
	// instantiate the ∀ in the hypothesis and abstract the equality.
	// E.g. body_eq is  P(x) = Q(x) ⊢ P(x) = Q(x)
	//   → after HypForAllInst + Abs for x:
	//     ∀x.P(x) = Q(x) ⊢ λx.P(x) = λx.Q(x)
	for _, v := range vars.Backward() {
		absEq = absEq.HypForAllInst(v, absEq.Hyp(0)).Abs(v)
	}

	Assert(absEq.Hyp(0).Equals(t))
	return absEq
}

// unifyEq tries to instantiate an equality theorem to match a given term via unification.
//
// Given an equality ⊢ λx.λy...body = s and a target term t, it:
//  1. Determines how many abstraction layers to peel from the LHS so that the
//     body's type matches t's type.
//  2. Renames abstraction variables to avoid name clashes with t.
//  3. Unifies the peeled body with t to find substitutions {x ↦ p, y ↦ q, ...}.
//  4. Applies each substitution to the equality and β-reduces, producing
//     ⊢ t = s(p, q, ...).
//
// Returns an iterator of equalities because unification may yield multiple
// valid substitutions. Returns an empty iterator if no unification is possible.
//
// Example: given ⊢ λx.P(x) = Q and target P(R(y)),
// unification finds {x ↦ R(y)}, producing ⊢ P(R(y)) = Q(R(y)).
func unifyEq(ctx context.Context, eq Prop, t Term) iter.Seq[Prop] {
	s := Lhs(eq)
	if s.AlphaEquals(t) {
		return utils.SingleIter(eq)
	}

	// Peel abstraction layers from s until we reach a body whose type
	// matches t's type. The number of layers peeled is `level`.
	level := 0
	for _s := s; !_s.Type().Equals(t.Type()); level++ {
		if abs, ok := _s.AsAbsTerm(); ok {
			_s = abs.Body()
		} else {
			// no match, return empty result.
			return utils.EmptyIter[Prop]
		}
	}

	// Peel `level` layers from s, renaming bound vars to avoid names in t.
	vars, _s := matchesAbsToAvoid(s, t, level)
	Assert(_s.Type().Equals(t.Type()))

	// Variable-LHS rewrite-rule ban. If the peeled pattern body is itself
	// one of the peeled (flexible) vars, the "pattern" matches ANY target
	// of its type by absorbing the whole target into a single flexible
	// var — a vacuous match. Such rules are wrap-everything rewrites
	// (e.g. set_comprehension's identity def flipped: ⊢ λp.p = set_comprehension gives
	// t → set_comprehension(λx.t(x)) at every prod→bool node) and are inherently
	// non-terminating inside the merged-tactic fixpoint: the downstream
	// `!ext.IsSub(t, Rhs)` self-embed guard misses them because the
	// unifier's substitution value is a βη-VARIANT of t (η-expanded), not
	// t itself — the verified `def_expand(set_comprehension) on nested prod-type
	// binders` session wedge. Classical term-rewriting
	// rejects variable-LHS rules for
	// exactly this reason. The α-equality fast path above still handles
	// literal occurrences of the identity lambda, so definition-FOLDING
	// via an exact match keeps working.
	if v, ok := _s.AsVar(); ok && ext.NameInVars(vars, v.Name()) {
		return utils.EmptyIter[Prop]
	}
	// Projection-pattern ban — the level-0 sibling of the variable-LHS ban
	// above (the def_expand(set_comprehension) success-without-net-change
	// 2-cycle; engine.TestDefExpandSetComprehension_NoTreadmill). The check above only
	// fires when the type-driven peel reaches a bare var, i.e. when the
	// target is SMALLER-typed than the pattern. But the unifyEqRewrite walk
	// also builds tAbs candidates at the pattern's FULL type by wrapping an
	// application site with its binder-env vars: at a site s(x') inside
	// `∀s.∀x'. … s(x') …` it offers tAbs = λs.λx'.s(x'), the same type as
	// the un-peeled λp.p — so level = 0, vars = [], and _s is the identity
	// ABSTRACTION, not a var. λp.p then unifies with tAbs modulo η with an
	// EMPTY substitution, BetaEtaRefl bridges, and the rule folds
	// s(x') → set_comprehension(s)(x') — the same wrap-everything absorb, one η-step
	// removed (the syntactic `!ext.IsSub(t, Rhs)` guard misses it because
	// App(s,x') is not a subterm of App(App(set_comprehension,s),x')). More generally
	// any pattern that is a projection combinator (λp.p, λx.λy.x, …, or one
	// whose body is a peeled var) carries no rigid structure and matches
	// site-abstractions vacuously. Ban them all here, the same way — the
	// α-equality fast path above still folds LITERAL occurrences of the
	// identity lambda.
	if isProjectionPattern(_s, vars) {
		return utils.EmptyIter[Prop]
	}
	// Unify the peeled body with t. A name is considered rigid (not unifiable)
	// if it appears free in t, or if it appears free in _s but is NOT one of
	// the abstraction variables we peeled off.
	bounded, cancel := unify.WithWorkBudget(ctx)
	defer cancel()
	substs := unify.UnifyTerms(bounded, _s, t,
		func(n TermName) bool {
			return t.HasFreeName(n) ||
				(_s.HasFreeName(n) && !ext.NameInVars(vars, n))
		})

	if len(substs) == 0 {
		return utils.EmptyIter[Prop]
	}

	// Apply each peeled var to the equality and β-reduce the LHS,
	// transforming ⊢ λx.λy.body = s into ⊢ body = s(x)(y).
	_eq := WrapProp(eq)
	for _, v := range vars {
		_eq = _eq.
			RightApply(v).
			RewriteConcl(DeepBetaAbs(Lhs(_eq).(AbsTerm)))
	}
	Assert(_s.Equals(Lhs(_eq)))

	// For each unification result, apply the substitution to the equality.
	// If the LHS is not yet α-equal to t (due to β/η differences),
	// use BetaEtaRefl to bridge the gap.
	return utils.MapIter(
		slices.Values(substs),
		func(s ext.TermSubstsGroup) Prop {
			w := _eq.TermInst(s...)
			if !Lhs(w).AlphaEquals(t) {
				u := BetaEtaRefl(t, Lhs(w))
				Assert(u != nil)
				w = u.EqTrans(w)
			}
			return w
		})
}

// isProjectionPattern reports whether the peeled rewrite pattern `body`
// (with `peeled` the flexible vars peeled off the rule's LHS by unifyEq)
// is a projection combinator: an abstraction chain λv1…λvn.vi whose body
// is one of its own binders, or one of the peeled flexible vars. Such a
// pattern has no rigid structure — it matches any target of its type
// vacuously (modulo η via the unifier's empty-substitution success), so
// unifyEq refuses to build rewrite instances from it. See the two ban
// comments in unifyEq. The bare-var case (n = 0, body ∈ peeled) is the
// classical variable-LHS ban; callers keep the explicit AsVar check
// first for clarity, but this helper subsumes it.
func isProjectionPattern(body Term, peeled []VarTerm) bool {
	binders := peeled
	for {
		abs, ok := body.AsAbsTerm()
		if !ok {
			break
		}
		binders = append(binders[:len(binders):len(binders)], abs.Var())
		body = abs.Body()
	}
	v, ok := body.AsVar()
	return ok && ext.NameInVars(binders, v.Name())
}

// unifyEqRewrite constructs a bottom-up, unification-based rewrite from an equality.
//
// Like EqRewrite, it takes an equality ⊢ l = r and produces a Rewrite that
// transforms terms containing the pattern. The key differences are:
//
//  1. β-matching via unification: when the LHS is an abstraction λx.P(x),
//     EqRewrite requires the target to structurally contain λx.P(x). This
//     function instead uses unification to match P(x) directly against subterms.
//     For example, given ⊢ λx.P(x) = y and a term containing P(a):
//     - EqRewrite:      returns nil (P(a) ≠ λx.P(x) structurally)
//     - unifyEqRewrite: returns ⊢ P(a) = y(a) (unifies x ↦ a)
//
//  2. Bottom-up traversal: subterms are rewritten before their parents, so
//     the innermost matches are found first. EqRewrite uses top-down traversal.
//
//  3. Best-match selection: when unification yields multiple valid substitutions,
//     the result with the smallest RHS is chosen.
//
// Returns NilRewrite if l is a subterm of r (to prevent infinite expansion).
func unifyEqRewrite(eq Prop) Rewrite {
	return unifyEqRewriteImpl(context.Background(), eq, "", orderedOff, false)
}

// unifyEqRewriteAbsPermuted is unifyEqRewrite with the multi-var wrap
// attempted in EVERY type-compatible variable order, not only the
// binder (outside-in) order. The single-order wrap is incomplete
// exactly when a rigid-bodied multi-binder pattern sits under
// enclosing binders whose order differs from the λ's own — the wrap
// abstracts λy.λx where the pattern is λx.λy, the bodies fail α, and
// with no flexible head to absorb the swap the site silently never
// folds. DenoteRewrite is the caller that needs the complete search
// (a denoted atom must fold every instance of its λ or the clause set
// mixes spellings); the simp/def_expand channels keep the single-order
// wrap — their recorded corpora depend on which sites fire.
//
// ctx bounds the rewrite as it bounds every unifyEqRewriteImpl (see
// there): the caller reads ctx before it reads the result.
func unifyEqRewriteAbsPermuted(ctx context.Context, eq Prop) Rewrite {
	return unifyEqRewriteImpl(ctx, eq, "", orderedOff, true)
}

// wrapVarPermutations returns the non-binder-order orderings of a
// multi-var wrap whose positional type profile is unchanged (only
// equal-typed positions swap, so every returned order still fills the
// same lTypes gap the caller validated). Empty unless permute mode is
// on, at least two vars are in play, and no more than four (the
// factorial guard; a five-var wrap is tried in binder order alone).
// Generation order is fixed (index-lexicographic), so the
// caller's smallest-RHS pick stays deterministic.
func wrapVarPermutations(vars []VarTerm, permute bool) [][]VarTerm {
	if !permute || len(vars) < 2 || len(vars) > 4 {
		return nil
	}
	var out [][]VarTerm
	cur := make([]VarTerm, len(vars))
	used := make([]bool, len(vars))
	var build func(k int)
	build = func(k int) {
		if k == len(vars) {
			for i, v := range cur {
				if v != vars[i] {
					out = append(out, slices.Clone(cur))
					return
				}
			}
			return // the binder order itself — the caller already ran it
		}
		for i, v := range vars {
			if used[i] || !v.Type().Equals(vars[k].Type()) {
				continue
			}
			used[i] = true
			cur[k] = v
			build(k + 1)
			used[i] = false
		}
	}
	build(0)
	return out
}

// unifyEqRewriteImpl is the shared core of unifyEqRewrite and
// UnifyEqRewriteWithPrune. A non-empty pruneConstName short-circuits
// recursion on subterms not mentioning that Const (def_expand's channel
// — pruning merely elides walks into subtrees that CANNOT contain a
// match, so an empty name is behaviorally identical to the plain form).
//
// Rule-level ordered mode (orderPermutative): when the equality is a
// PERMUTATIVE rule — its two sides are variants, equal up to a
// bijective renaming of the rule's λ-peeled pattern vars
// (skeleton.PermutativeRulePattern: COMM and left-comm yes, ASSOC no) —
// every candidate instance must be strictly Compare-DECREASING (ordered
// rewriting). This is the constructor-
// level complement of the fire whistle's instance-level gate
// (skeleton.PermutationFireAllowed): the whistle classifies fires
// without rule identity and so cannot see left-commutativity (its
// instances are unordered-DISTINCT trees), while the pattern-level
// variants test catches it exactly.
//
// Ordered mode is CALLER-SCOPED, not unconditional: it is the
// discipline of the fixpoint simp-set drivers (simp_with clause rules,
// leanRwTacticMultiClause — the DeepRewriteWhistled compositions where
// a permutative rule self-feeds and storms), exactly where ordered
// rewriting belongs. One-shot explicit rewrite channels (lemma
// cites, eq tactics, def_expand) keep their written orientation: an
// agent-directed flip is a deliberate navigation choice, and the
// recorded corpus depends on those directions (retrofitting ordering
// onto every channel broke 69 stored replays across the REAL/HREAL/
// TREAL layers — commutativity-class lemmas cited directionally).
//
// ctx bounds the rewrite: its unifications run under ctx beside their
// own work budget (unify.WithWorkBudget), and its walk reads ctx at each
// node. Once ctx is done a unification in flight answers "no unifier"
// at its next poll and the walk enters no further node, so the rewrite
// answers nil or an equation short of the one it was building: no
// report of where the rule fires, and no normal form of anything. The
// caller reads ctx before it reads the result. A context that is never
// done leaves every result as it is.
func unifyEqRewriteImpl(
	ctx context.Context,
	eq Prop, pruneConstName TermName, orderMode orderedMode,
	permuteWrapVars bool) Rewrite {
	rewrite, selfEmbedding := unifyEqRewriteGuarded(ctx, eq, pruneConstName, orderMode, permuteWrapVars)
	if selfEmbedding {
		return NilRewrite
	}
	return rewrite
}

// unifyEqRewriteGuarded builds eq's rewrite and reports whether eq embeds
// itself. Such a rule rewrites its own output without end, so no fixpoint
// may run it (unifyEqRewriteImpl refuses it); the rewrite returned is one
// pass and terminates, which is what lets RewriteRefusedOn ask where the
// rule would have fired.
func unifyEqRewriteGuarded(
	ctx context.Context,
	eq Prop, pruneConstName TermName, orderMode orderedMode,
	permuteWrapVars bool) (Rewrite, bool) {
	l, r, ok := MatchesEQ(eq.Conclusion())
	Assert(ok)
	selfEmbedding := ext.IsSub(l, r)
	// Decompose l's type into its function chain.
	// E.g. for l : A → B → C, lTypes = [A, B, C].
	// This is used to quickly reject terms whose type cannot possibly match l.
	lTypes := ext.MatchesFun(l.Type())

	// Permutative (variants) rule → ordered rewriting for every
	// instance. Under orderedACGroup, a same-material rearrangement
	// (ASSOC-class rotation) is ordered too: rotations keep the fired
	// term's symbol multiset fixed, so gating their fires to the
	// strictly Compare-decreasing direction is exactly the
	// Martin–Nipkow termination discipline for an AC rule group —
	// leaving the rotation ungated lets a normal-form-oriented ASSOC
	// (stated toward left nesting = Compare-increasing) undo the
	// ordered COMM/left-comm sort in a 4-fire cycle around the AC
	// class (the int_add_th SimpWith storm, second layer). The AC mode
	// is chosen PER SIMP SET by the caller (SimpSetACGates): a lone
	// directional ASSOC keeps its written orientation.
	ordered := orderMode != orderedOff &&
		(skeleton.PermutativeRulePattern(l, r) ||
			(orderMode == orderedACGroup &&
				skeleton.RearrangementRulePattern(l, r)))

	// Rigid-head pre-filter (ext.MatchFilterFor): when l's λ-stripped
	// spine head is a Const, any target headed by a different const or
	// by a var cannot unify — skip the node-level attempt without paying
	// AbsFreeVars + UnifyTerms. Zero false negatives by construction
	// (see ext.MatchFilter), so results are unchanged, only cost. The
	// self-embed probe below runs through the same filtered step; that
	// is sound for the same reason — a filtered-out attempt is one the
	// unifier would have rejected anyway.
	headFilter := unify.MatchFilterFor(l)

	// makeRewrite builds the recursive closure pair; cache == nil is the
	// plain zero-allocation path, non-nil the per-top-call shared-DAG memo
	// (results depend only on (term, binder env) — see envScopeCache).
	makeRewrite := func(cache *envScopeCache) RewriteWithEnv {
		var rewrite, subTermsRewrite RewriteWithEnv
		// step is one uncached recursion level; defined once per closure
		// pair so the memo wrapper adds no per-visit allocation.
		step := func(t Term, env []VarTerm) *PropWrapper {
			// A done context ends the walk: no further node is entered
			// or tried.
			if ctx.Err() != nil {
				return nil
			}
			// PRUNE (def_expand channel): subtrees without the target
			// const cannot match. Recursive because subTermsRewrite calls
			// back into this closure.
			if pruneConstName != "" && !ext.TermContainsConstName(t, pruneConstName) {
				return nil
			}
			// Bottom-up: rewrite subterms first, then try this level.
			if w := subTermsRewrite(t, env...); w != nil {
				return w
			}

			if !headFilter.CouldMatch(t) {
				return nil
			}

			// Ordered mode fires only at fully-applied (atom-typed)
			// sites. A match at a partial-application/η level (t still
			// function-typed) rewrites `x∘Y → Y∘x` for a yet-unseen
			// argument, so no Compare verdict on the applied form exists;
			// the η-long comparison OrderedInstanceDecreasing would make
			// instead is degenerate — BetaEtaNormalize η-EXPANDS, and a
			// bound λ-var is Compare-MINIMAL, so the "λ-var first" flip
			// of a permutative rule is unconditionally "decreasing" at
			// the η level while the applied level orders the concrete
			// arguments. The two verdicts contradict on every sum whose
			// arguments are order-reversed, and the same COMM rule then
			// 2-cycles between its partial-level and applied-level fires
			// (the int_add_th SimpWith storm). Declining here is an
			// ordering decline, same contract as the
			// OrderedInstanceDecreasing skip below — not a whistle event.
			if ordered && ext.IsFunType(t.Type()) {
				return nil
			}

			// Type-level filter: decompose t's type and check that it matches
			// a suffix of lTypes. This is necessary because unification with l
			// requires t (after wrapping with env vars) to have the same type as l.
			// E.g. if l : A → B → C and t : B → C, then t matches at level 1
			// (needing one env var of type A).
			tTypes := ext.MatchesFun(t.Type())
			lTypesLen, tTypesLen := len(lTypes), len(tTypes)
			restLen := lTypesLen - tTypesLen
			if tTypesLen > lTypesLen ||
				!slices.EqualFunc(
					lTypes[restLen:],
					tTypes,
					HolType.Equals) {
				return nil
			}

			// Collect free env vars of t and check their types fill the gap
			// between t's type and l's type. E.g. if l : A → B → C, t : C,
			// and env vars have types [A, B], then we can wrap t as λa:A.λb:B.t
			// to attempt unification with l.
			vars := ext.AbsFreeVars(t, env...)
			varsTypes := utils.MapSlice(vars, (VarTerm).Type)
			if len(varsTypes) > restLen ||
				!slices.EqualFunc(
					lTypes[restLen-len(vars):restLen],
					varsTypes,
					HolType.Equals) {
				return nil
			}

			// Wrap t with its free env vars to form an abstraction, then
			// try unification against the equality. The binder-order
			// wrap runs first; permute mode then retries every other
			// type-compatible order (see unifyEqRewriteAbsPermuted) —
			// all candidates share one smallest-RHS pick, so the result
			// stays deterministic.
			var p *PropWrapper
			attempt := func(order []VarTerm) {
				tAbs := ext.ReverseAbsVars(t, order...)
				for e := range unifyEq(ctx, eq, tAbs) {
					Assert(Lhs(e).AlphaEquals(tAbs))
					// Peel the abstraction layers back off by applying each var
					// and β-reducing, recovering an equality at t's level.
					eq := WrapProp(e)
					for _, v := range order {
						eq = eq.
							RightApply(v).
							RewriteConcl(DeepBetaAbs(Lhs(eq).(AbsTerm)))
					}
					Assert(Lhs(eq).AlphaEquals(t))
					// Guard against infinite expansion: skip if t is a subterm of
					// the rewritten RHS. Among valid results, pick the smallest RHS.
					if !ext.IsSub(t, Rhs(eq)) {
						// Ordered mode (permutative rule): only strictly
						// Compare-decreasing instances may fire; an increasing
						// candidate is treated as no-match, like the IsSub guard.
						if ordered && !skeleton.OrderedInstanceDecreasing(t, Rhs(eq)) {
							continue
						}
						if p == nil || Rhs(eq).Size() < Rhs(p).Size() {
							p = WrapProp(eq)
						}
					}
				}
			}
			attempt(vars)
			for _, order := range wrapVarPermutations(vars, permuteWrapVars) {
				attempt(order)
			}
			return p
		}
		rewrite = func(t Term, env ...VarTerm) *PropWrapper {
			if w, ok := cache.Load(env, t); ok {
				return w
			}
			w := step(t, env)
			cache.Store(env, t, w)
			return w
		}

		// Recurse into immediate subterms. Since rewrite is the callback,
		// the traversal naturally goes bottom-up through the full term.
		subTermsRewrite = RewriteSubTermsWithEnv(rewrite, eq.AnyHyp)
		return rewrite
	}
	rewrite := makeRewrite(nil)

	// Unification-aware self-embedding guard. The syntactic ext.IsSub
	// check at the top of this function misses higher-order patterns:
	// e.g. l = λp.λx. p(x) is NOT a syntactic subterm of
	// r = λp.λx. set_comprehension(p)(x), but the rule's effect on a real target
	// q(a) is q(a) → set_comprehension(q)(a), and the unifier matches l against
	// that result too — so the rule fires on its own RHS and the
	// merged-tactic fixpoint expands without bound (the def_expand
	// set_comprehension hang).
	//
	// Mechanism: peel l's leading λ's into a body (with l's bound
	// vars now free), feed that body to the freshly-built rewrite —
	// this is exactly the shape a real target would have when the
	// rule first fires on it. If that step succeeds AND its normalized
	// RHS can be rewritten to a larger normalized result, the rule is
	// non-terminating: refuse it, the same way EqRewrite refuses
	// syntactic self-embed (eq_rewrite.go:43). Normalize the probe
	// results first because unification rewrites often leave β-redexes
	// such as `(λx.λy.y+x)(x,y)`; without normalization, harmless
	// involutive rules like commutativity look like growth.
	if !selfEmbedding {
		_, lBody := MatchesAbs(l)
		if w1 := rewrite(lBody); w1 != nil {
			rhs1 := Rhs(w1)
			if u := BasicRewrite(rhs1); u != nil {
				rhs1 = Rhs(u)
			}
			if w2 := rewrite(rhs1); w2 != nil {
				rhs2 := Rhs(w2)
				if u := BasicRewrite(rhs2); u != nil {
					rhs2 = Rhs(u)
				}
				selfEmbedding = rhs2.Size() > rhs1.Size()
			}
			if !selfEmbedding {
				anyRuleTerm := func(pred func(Term) bool) bool {
					return pred(eq.Conclusion()) || eq.AnyHyp(pred)
				}
				if w2 := rewriteNestedBinderBodiesOnce(rhs1, rewrite, anyRuleTerm); w2 != nil {
					rhs2 := Rhs(w2)
					if u := BasicRewrite(rhs2); u != nil {
						rhs2 = Rhs(u)
					}
					selfEmbedding = rhs2.Size() > rhs1.Size()
				}
			}
		}
	}

	return func(t Term) *PropWrapper {
		if cache := ext.EnvMemoFor[*PropWrapper](t); cache != nil {
			return makeRewrite(cache)(t)
		}
		return rewrite(t)
	}, selfEmbedding
}

// rewriteNestedBinderBodiesOnce probes a rule on each abstraction's body
// as a fresh target, as a surrounding fixpoint walk presents it to the
// rule. The rule's own binder-aware walk can miss such a target when the
// enclosing binder's type cannot fill its pattern's parameter slots.
// Inserted terms are not rescanned. Binders are renamed away from the
// rule's free variables before a body is entered, so treating the body as
// a fresh target cannot turn a bound variable into a fixed rule variable.
func rewriteNestedBinderBodiesOnce(t Term, rule RewriteWithEnv, anyRuleTerm func(func(Term) bool) bool) *PropWrapper {
	var walk, descend, enter RewriteWithEnv
	walk = func(t Term, env ...VarTerm) *PropWrapper {
		if _, ok := t.AsAbsTerm(); ok {
			return enter(t, env...)
		}
		return descend(t, env...)
	}
	body := func(t Term, env ...VarTerm) *PropWrapper {
		if w := rule(t); w != nil {
			return w
		}
		return walk(t, env...)
	}
	descend = RewriteSubTermsWithEnv(walk, anyRuleTerm)
	enter = RewriteSubTermsWithEnv(body, anyRuleTerm)
	return walk(t)
}

// orderedMode selects the rule-level ordered-rewriting discipline of
// unifyEqRewriteImpl (see the ordered-mode doc there). orderedOff is
// the one-shot explicit channels (written orientation); orderedVariants
// gates permutative (variants) rules Compare-decreasing — the fixpoint
// simp-set default; orderedACGroup additionally gates same-material
// rearrangements (ASSOC-class rotations) — chosen per clause by
// SimpSetACGates when the simp set pairs the rotation with a variants
// rule over the same operator (an AC group, the only combination whose
// ungated rotation cycles).
type orderedMode int

const (
	orderedOff orderedMode = iota
	orderedVariants
	orderedACGroup
)

// UnifyEqRewrite is the exported form of unifyEqRewrite, for callers outside
// `prop` that hold a PROVEN equality theorem (hyp-free) and want a unification-
// based (β-matching) deep rewrite from it — without ContextEqRewrite's
// lemma-as-hypothesis seam. The caller is responsible for shaping the proof into
// a bare `⊢ l = r` (or `⊢ λvars. l = λvars. r`) equality: strip the ∀-quantifiers
// (ConclForAllInst), orient as desired (EqSym for the reversed direction), and
// re-abstract the now-free vars (Abs) so unification can instantiate them.
// Because the input theorem carries no hypotheses, every rewrite it produces is
// hyp-free too. Used by omega.IntOfRealThm (omega/int_lemmas.go).
func UnifyEqRewrite(eq Prop) Rewrite { return unifyEqRewrite(eq) }

// UnifyEqRewriteWithPrune is unifyEqRewrite that short-circuits recursion
// on subterms not mentioning any Const named `pruneConstName`.
// Semantically identical to unifyEqRewrite when the LHS is a Const-headed
// term whose head name equals `pruneConstName` — pruning merely elides
// the walk into subtrees that CANNOT contain a match. Use this only when
// the extra const-name walk is cheaper than attempting unification
// below that subtree.
//
// Empty `pruneConstName` disables pruning — behaves as unifyEqRewrite.
// Both forms share unifyEqRewriteImpl; the prune check is the only
// behavioral difference between them.
func UnifyEqRewriteWithPrune(eq Prop, pruneConstName TermName) Rewrite {
	return unifyEqRewriteImpl(context.Background(), eq, pruneConstName, orderedOff, false)
}

// ContextEqRewrite converts a term (typically a hypothesis or known fact) into
// a conditional equality and uses it to build a rewrite.
//
// When unifyEq is false, it uses contextEq + EqRewrite (structural matching).
// When unifyEq is true, it uses ContextAbsEq + unifyEqRewrite (unification-based
// matching), which enables β-matching through ∀-quantified variables.
//
// Example with unifyEq=true: given the context ∀x.(P(x) = Q(x)),
// ContextAbsEq produces ∀x.(P(x) = Q(x)) ⊢ λx.P(x) = λx.Q(x).
// Then unifyEqRewrite can rewrite P(R(y)) to Q(R(y)) by unifying x with R(y).
//
// Falls back to plain EqRewrite when the resulting equality has no abstraction
// on either side and the hypothesis is not universally quantified (i.e.,
// unification would add no value over structural matching).
//
// Pre-CNF target fallback: when the primary rewrite fails on a Bool
// target, we retry against the target's pre-CNF normal form. This
// bridges "logically equal but syntactically different" misses where
// the lemma's pattern is canonical but the goal subterm uses ⇒ vs ¬∨, a
// different quantifier scope, etc. (e.g. two
// failure modes met in the canonical-form work).
// The composed equality is kernel-sound: ⊢ target = target_pre (from
// PreCNFNormalizeTerm) chained with the primary's ⊢ target_pre = result,
// giving ⊢ target = result. A rule is retried only where a normal form
// can hold an instance of its pattern (preCNFRetryOf): never when the
// pattern is an implication, and never on a target that lacks the
// pattern's head constant. The cache the parameterized forms take is
// shared across a rule set, so a node is normalized once per set (see
// preCNFFallbackRewrite).
func ContextEqRewrite(t Term, unifyEq bool) Rewrite {
	return ContextEqRewriteOpt(new(PreCNFCache), t, unifyEq, false)
}

// ContextEqRewriteOpt is the parameterized form of ContextEqRewrite.
// cache is the pre-CNF normalization cache the pre-CNF fallback
// reads: the rewrites of ONE rule set — a Simp's rules and its mined
// instances, a multi-clause LeanRw's clauses, the equalities one
// eqSimplify tactic call reads off a goal — are built over one cache;
// a one-shot caller passes a fresh one.
// allowExpand=true disables contextEq's bigger-side-on-LHS swap, so an
// equational lemma applied through this path preserves its written
// direction — required for explicit agent-driven rewrites (lean_rw,
// def_expand) where the lemma's RHS may legitimately be larger than
// the LHS (extensionality, COND distribution, definitional unfolding).
//
// The default form (allowExpand=false) keeps the swap so the
// fixpoint-bound BasicTactics path stays size-monotone.
func ContextEqRewriteOpt(cache *PreCNFCache, t Term, unifyEq, allowExpand bool) Rewrite {
	return ContextEqRewriteOptUnder(context.Background(), cache, t, unifyEq, allowExpand)
}

// ContextEqRewriteOptUnder is ContextEqRewriteOpt under a caller's
// context: ctx bounds the unifications and the walk of the rule's rewrite
// (unifyEqRewriteImpl) and the pre-CNF retry after it. Once ctx is done
// the rewrite answers nil at its next node, which is no report that the
// rule does not fire: the caller reads ctx before it reads the result.
func ContextEqRewriteOptUnder(ctx context.Context, cache *PreCNFCache, t Term, unifyEq, allowExpand bool) Rewrite {
	return preCNFFallbackRewrite(ctx,
		contextEqRewritePrimary(ctx, t, unifyEq, allowExpand, orderedOff),
		cache, preCNFRetryOf(t, allowExpand))
}

// ContextEqRewriteOrdered is ContextEqRewriteOpt for the fixpoint
// simp-set channels (simp_with clause rules, leanRwTacticMultiClause):
// a PERMUTATIVE rule (variants — skeleton.PermutativeRulePattern) is
// applied with ordered rewriting, each instance firing only in the
// strictly Compare-decreasing direction. Use ONLY for simp-set-driven
// rewriting where a permutative rule self-feeds to fixpoint; one-shot
// explicit rewrite channels must keep ContextEqRewriteOpt (written
// orientation — see unifyEqRewriteImpl's ordered-mode doc for why).
func ContextEqRewriteOrdered(cache *PreCNFCache, t Term, unifyEq, allowExpand bool) Rewrite {
	return preCNFFallbackRewrite(context.Background(),
		contextEqRewritePrimary(context.Background(), t, unifyEq, allowExpand, orderedVariants),
		cache, preCNFRetryOf(t, allowExpand))
}

// ContextEqRewriteOrderedAC is ContextEqRewriteOrdered with the
// AC-group extension: a same-material rearrangement rule (ASSOC-class
// rotation — skeleton.RearrangementRulePattern) is ALSO applied with
// ordered rewriting, not only the variants. Use it for exactly the
// clauses SimpSetACGates flags: a rotation sharing its operator with a
// variants clause in the same fixpoint simp set. A rotation cited
// alone stays on ContextEqRewriteOrdered (written orientation — a
// directional reassociation is a recorded navigation choice, e.g.
// int_add_th's `x+(y+z) = (x+y)+z` + cancellation set).
func ContextEqRewriteOrderedAC(cache *PreCNFCache, t Term, unifyEq, allowExpand bool) Rewrite {
	return preCNFFallbackRewrite(context.Background(),
		contextEqRewritePrimary(context.Background(), t, unifyEq, allowExpand, orderedACGroup),
		cache, preCNFRetryOf(t, allowExpand))
}

// contextEqRewritePrimary is the raw, fallback-free body of ContextEqRewrite —
// kept separate so the fallback wrapper composes cleanly and can be tested
// independently. orderPermutative reaches only the unify path (the
// EqRewrite fallbacks serve ground/non-∀ shapes, where the variants
// test is inapplicable and the fire whistle is the storm net). ctx
// bounds the unify path (unifyEqRewriteImpl); the structural channels
// run no unification and read no context.
func contextEqRewritePrimary(ctx context.Context, t Term, unifyEq, allowExpand bool, orderMode orderedMode) Rewrite {
	if !unifyEq {
		return EqRewrite(contextEqOpt(t, allowExpand))
	}
	absEq := contextAbsEqOpt(t, allowExpand)
	Assert(absEq != nil && absEq.NumHyps() == 1)
	if groundAbsEq(absEq) {
		return EqRewrite(absEq)
	}
	return unifyEqRewriteImpl(ctx, absEq, "", orderMode, false)
}

// groundAbsEq reports an absEq with no binder of the rule left in it: the
// structural channel serves it, there being nothing to unify.
func groundAbsEq(absEq *PropWrapper) bool {
	_, lAbs := Lhs(absEq).AsAbsTerm()
	_, rAbs := Rhs(absEq).AsAbsTerm()
	return !lAbs && !rAbs && MatchesFORALL(absEq.Hyp(0)).IsZero()
}

// RewriteRefusedOn reports that the rule t of a fixpoint simp set is
// refused as self-embedding (unifyEqRewriteImpl, eqRewriteImpl) while its
// left side matches within target: a fire the refusal took away, not a
// rule with nothing to rewrite. A failing simp step names such a rule,
// where "no rule fired" alone would read as a missing match.
func RewriteRefusedOn(t, target Term) bool {
	absEq := contextAbsEqOpt(t, true)
	if groundAbsEq(absEq) {
		l, r, ok := MatchesEQ(absEq.Conclusion())
		return ok && ext.IsSub(l, r) && ext.IsSub(l, target)
	}
	rewrite, selfEmbedding := unifyEqRewriteGuarded(context.Background(), absEq, "", orderedVariants, false)
	return selfEmbedding && rewrite(target) != nil
}

// SimpSetACGates decides, per clause of one fixpoint simp set, whether
// the ordered channel must use ContextEqRewriteOrderedAC instead of
// ContextEqRewriteOrdered. clauseConcls are the clause conclusions (the
// same ∀-quantified terms the caller feeds the constructors, in rule
// order). The gate flips on for exactly the same-material rearrangement
// clauses (ASSOC-class rotations — skeleton.RearrangementRulePattern)
// whose equation head constant also heads a variants clause (COMM/
// left-comm — skeleton.PermutativeRulePattern) in the SAME set:
//
//   - A rotation alone terminates in either written direction (the
//     one-sided nesting measure is monotone) and stored proofs cite it
//     directionally — it keeps its orientation.
//   - A rotation TOGETHER with ordered variants over the same operator
//     is an AC group: the variants fires sort Compare-decreasing, and a
//     rotation whose written direction is Compare-increasing (the
//     normal form's smaller-side-first orientation makes ASSOC point at
//     LEFT nesting, which is increasing under the leftmost-first
//     structural order) un-sorts what they just sorted — a 4-fire cycle
//     around the AC class (the int_add_th SimpWith storm). Ordered
//     rewriting terminates only if every material-preserving fire
//     decreases ONE common order, so exactly this combination gates the
//     rotation too.
//
// Deterministic — a pure function of the clause statements — so replay
// re-derives the same per-clause channel choice.
func SimpSetACGates(clauseConcls []Term) []bool {
	heads := make([]TermName, len(clauseConcls))
	rearr := make([]bool, len(clauseConcls))
	variantHeads := map[TermName]bool{}
	for i, t := range clauseConcls {
		varList, body := DecomposesFORALL(t)
		l, r, ok := MatchesEQ(body)
		if !ok || varList.Size() == 0 {
			continue
		}
		head, _ := ext.MatchesApply(l)
		hc, ok := head.AsConst()
		if !ok {
			continue
		}
		// Shape the sides exactly as contextAbsEq does: λ-abstract the
		// clause's ∀-vars.
		vars := varList.Section(0, varList.Size())
		lAbs := ext.ReverseAbsVars(l, vars...)
		rAbs := ext.ReverseAbsVars(r, vars...)
		if skeleton.PermutativeRulePattern(lAbs, rAbs) {
			variantHeads[hc.Name()] = true
		} else if skeleton.RearrangementRulePattern(lAbs, rAbs) {
			heads[i] = hc.Name()
			rearr[i] = true
		}
	}
	gates := make([]bool, len(clauseConcls))
	for i := range clauseConcls {
		gates[i] = rearr[i] && variantHeads[heads[i]]
	}
	return gates
}

// preCNFFallbackRewrite wraps a primary Rewrite with a pre-CNF target
// fallback: when primary fails on a Bool target whose pre-CNF normal form
// differs from the input, normalize the target and retry primary on the
// pre-form, then bridge back via PreCNFNormalizeTerm's witness.
//
// retry is preCNFRetryOf's verdict on the rule. A rule no normal form
// serves is returned unwrapped — never retried, normalizing nothing —
// and a target whose normal form cannot hold the rule's pattern
// (preCNFRetry.reaches) is answered nil with nothing normalized.
//
// Returns the primary's result unchanged when primary succeeds. Returns nil
// when primary fails and either (a) the target is not Bool-typed, (b) the
// target's normal form cannot hold the pattern, (c) the target is already
// in pre-CNF form (Rhs(preT) alpha-equals target), or (d) primary still
// fails on the pre-form.
//
// The wrapper is called wherever the rule is: a one-shot channel calls it
// once per hypothesis, but a fixpoint driver (DeepRewriteWhistled over a
// Simp's rule set) calls every rule at EVERY node of its walk, in every
// round — so every Bool node the rule does not fire on is a candidate
// for the normal form, and the goal changes each round. Two things bound
// that. The test of (b) leaves out the nodes that cannot hold the
// pattern, which for a rule about one constant is most of a goal. cache
// bounds the rest: the rule set's rewrites share one, so a node's normal
// form is computed once per set and per spelling, not once per rule (the
// ℂ-parts Simp of a ∀-stated two-variable identity normalized 579 times
// with a cache per rule and 114 times with one cache). Subterm traversal
// of either primary attempt continues to use raw matching on its
// argument, because pre-CNF normalization is deep — subterms of
// target_pre are themselves canonical, so primary's bottom-up traversal
// hits the same structural matches it would after any per-subterm
// normalization.
//
// ctx is the context primary runs under. A primary that answers nil
// once ctx is done was cut off and did not fail, so the target is
// neither normalized nor retried: the wrapper answers nil, and the
// caller reads ctx before it reads that.
func preCNFFallbackRewrite(ctx context.Context, primary Rewrite, cache *PreCNFCache, retry preCNFRetry) Rewrite {
	if !retry.serves {
		return primary
	}
	return func(target Term) *PropWrapper {
		if w := primary(target); w != nil {
			return w
		}
		if ctx.Err() != nil || !IsBool(target) || !retry.reaches(target) {
			return nil
		}
		preT := cache.NormalizeTerm(target)
		if Rhs(preT).AlphaEquals(target) {
			return nil
		}
		w := primary(Rhs(preT))
		if w == nil {
			return nil
		}
		return preT.EqTrans(w)
	}
}

// A preCNFRetry is what the pre-CNF fallback can serve of one rule
// (preCNFRetryOf).
type preCNFRetry struct {
	// serves is false for a rule whose pattern no normal form holds an
	// instance of.
	serves bool
	// head names the constant every instance of the pattern holds and
	// the normalizer never introduces; it is empty for a pattern with
	// no such constant.
	head TermName
}

// reaches reports whether target's pre-CNF normal form can hold an
// instance of the rule's pattern. The normalizer's rewrites are those of
// the logic — β, η, the connectives, the quantifiers, equality, choice,
// the conditional — so a normal form holds no constant its input lacks
// but a logical one: a target without the pattern's head has a normal
// form without it, and the retry would find nothing there. A false
// answer is never wrong; a true one decides nothing, and the retry
// does.
func (retry preCNFRetry) reaches(target Term) bool {
	return retry.head == "" || ext.TermContainsConstName(target, retry.head)
}

// preCNFRetryOf reads off the rule t what the pre-CNF fallback can serve
// of it, from its pattern: the side of its equation the primary matches
// (contextEqOpt's orientation: the left side, or the larger side when
// noSwap is false; a fact P stands for P ⇔ ⊤ and ¬P for P ⇔ ⊥).
//
// An implication pattern is not served. The normal form is
// implication-free (PreCNFNormalizeRewrite), so that pattern has no
// instance in any normal form and its retry could only cost. Every other
// pattern is served: a propositional pattern can BE the normal form's
// skeleton (⇒ as ¬∨, a quantifier's scope, a clause's order, an
// equation's orientation) — the bridge the fallback exists for — and a
// term pattern meets, through the normalizer's β, an instance a previous
// fire left inside a redex, which the recorded corpus depends on
// (cartesian/pairs' refutes replay only with it). A census of the corpus
// measured this, and it refutes a propositional-only criterion.
//
// The head is the pattern's rigid spine head (unify.SpineHeadConst: the
// constant every instance of the pattern is headed by, under any
// substitution of the rule's binders and up to βη) when that constant is
// not one of the logic's own. A pattern headed by a variable, or by a
// connective, a quantifier or equality — which the normalizer does
// introduce — has none, and is retried on every Bool target.
func preCNFRetryOf(t Term, noSwap bool) preCNFRetry {
	_, body := DecomposesFORALL(t)
	pattern := body
	if l, r, ok := MatchesEQ(body); ok {
		pattern = l
		if !noSwap && contextEqSwaps(l, r) {
			pattern = r
		}
	} else if n := ext.MatchesNOT(body); n != nil {
		pattern = n
	}
	if _, _, isImply := ext.MatchesIMPLY(pattern); isImply {
		return preCNFRetry{}
	}
	retry := preCNFRetry{serves: true}
	if head, ok := unify.SpineHeadConst(pattern); ok && !ext.IsLogicalConstName(head) {
		retry.head = head
	}
	return retry
}

// TermDiff computes the minimal single-replacement equality that transforms s into t.
//
// It can be viewed as the inverse of EqRewrite: if TermDiff(s, t) returns an
// equality l = r, then EqRewrite(l = r) applied to s will produce ⊢ s = t.
//
// Return values: two *PropWrapper pointers (rewriteLeft, rewriteRight).
//   - If only rewriteLeft is non-nil:  l = r ⊢ s = t  (rewriting s with l→r yields t)
//   - If only rewriteRight is non-nil: r = l ⊢ t = s  (rewriting t with r→l yields s)
//   - Both nil: s and t are α-equal, no replacement needed.
//
// The function tries both directions (s→t and t→s) and picks the smallest
// replacement across both. When multiple valid replacements exist at different
// granularities, it prefers the most fine-grained one.
//
// Algorithm:
//  1. Traverse s and t synchronously to collect all subterm differences (collectDiffs).
//  2. Deduplicate the candidate equalities (groupDiffs).
//  3. Sort by size (smallest first) and validate each by checking that
//     EqRewrite with the candidate actually transforms s into t.
//  4. If no fine-grained candidate works, fall back to the trivial whole-term
//     replacement ⊢ s = t.
//
// Examples:
//   - TermDiff(P(Q(x), Q(x)), P(R(x), R(x)))       → Q = R  (uniform replacement)
//   - TermDiff(P(Q(x), Q(x)), P(R(x), S(x)))        → P(Q(x),Q(x)) = P(R(x),S(x))
//     (no single subterm replacement works, falls back to whole term)
//   - TermDiff(∃a.P(a), ∃a.Q(a))                     → P = Q  (abstraction-aware)
//   - TermDiff(∃a.P(a), ∃a.(λb.(b=c))(a))            → P = λb.(b=c)
//   - TermDiff(∀a.P(a), ∀a.T(a,a))                   → λa.P(a) = λa.T(a,a)
//     (must abstract over bound var since P(a) and T(a,a) differ in arity)
func TermDiff(s, t Term) (*PropWrapper, *PropWrapper) {
	Assert(s.Type().Equals(t.Type()))

	// If terms are already equal, no replacement needed
	if s.AlphaEquals(t) {
		return nil, nil
	}

	// Collect all differences in a single traversal
	var diffs []Term
	collectDiffs(&diffs, s, t, nil)
	// now diffs contains all difference info
	Assert(len(diffs) > 0)

	// Group differences by their values to find candidates
	candidates := groupDiffs(diffs)

	// Sort candidates by size
	slices.SortFunc(candidates, func(a, b Term) int {
		return a.Size() - b.Size()
	})

	// Find the most minimal valid candidate
	var bestCandidate Term
	var rewriteLeft, rewriteRight *PropWrapper
	for _, cand := range candidates {
		l, r, _ := MatchesEQ(cand)
		// Skip trivial whole-term replacement unless it's the only option
		if l.AlphaEquals(s) && r.AlphaEquals(t) &&
			len(candidates) > 1 {
			continue
		}
		if l, r, ok := validateWithEqRewrite(s, t, cand); ok {
			if bestCandidate == nil ||
				cand.Size() < bestCandidate.Size() {
				bestCandidate = cand
				rewriteLeft, rewriteRight = l, r
			}
		}
	}

	if bestCandidate != nil {
		return rewriteLeft, rewriteRight
	}

	// If no other candidate worked, return the trivial whole-term replacement
	if ext.IsSub(s, t) {
		return nil, Assume(Eq(t, s))
	}
	return Assume(Eq(s, t)), nil
}

// validateWithEqRewrite checks whether a candidate equality eq can transform s into t
// (or t into s) via EqRewrite. It tries both directions:
//   - Forward:  EqRewrite(l = r) on s should produce ⊢ s = t
//   - Backward: EqRewrite(r = l) on t should produce ⊢ t = s
//
// When the RHS of the equality is a lambda, also tries β-reducing the result
// (since EqRewrite may produce unreduced lambda applications).
// Returns (left, right, ok) where at most one of left/right is non-nil.
func validateWithEqRewrite(s, t, eq Term) (*PropWrapper, *PropWrapper, bool) {
	l, r, _ := MatchesEQ(eq)
	if l.AlphaEquals(r) {
		return nil, nil, s.AlphaEquals(t)
	}

	validateOneSide := func(s, t, eq, r Term) *PropWrapper {
		result := EqRewrite(Assume(eq))(s)
		if result == nil {
			return nil
		}
		if Rhs(result).AlphaEquals(t) {
			return result
		}
		// If abs is a lambda abstraction, try with deep beta reduction
		// This handles cases where EqRewrite produces lambda applications that need reduction
		if abs, ok := r.AsAbsTerm(); ok {
			resultWithBeta := result.RewriteConclRhs(DeepBetaAbs(abs))
			if Rhs(resultWithBeta).AlphaEquals(t) {
				return resultWithBeta
			}
		}
		return nil
	}

	if result := validateOneSide(s, t, eq, r); result != nil {
		return result, nil, true
	}

	if result := validateOneSide(t, s, Eq(r, l), l); result != nil {
		return nil, result, true
	}

	return nil, nil, false
}

// Merged matcher for binary logical operators used by collectDiffs.
// MatchesEQ is excluded because two equalities can have different side types,
// making structural decomposition unreliable.
var binaryOpMatchers = ext.MergeBinaryOpMatchers(
	ext.MatchesAND,
	ext.MatchesOR,
	ext.MatchesIMPLY,
	ext.MatchesIFF,
)

// collectDiffs performs a single synchronized traversal of terms s and t,
// collecting candidate replacement equalities into dst.
//
// The traversal recurses into matching structure (both AppliedTerm, both AbsTerm)
// and records differences at each level. For abstractions, env tracks paired
// bound variables for α-equivalence checking. Candidates are stored as equality
// terms (l = r) where l and r are the differing subterms, possibly wrapped in
// lambda abstractions over bound variables from env.
//
// Optimization: if a candidate of minimal size 3 (a single variable on each side)
// is found and validated, the search terminates early since no smaller replacement
// is possible.
//
// For binary logical operators (∧, ∨, ⇒, ⇔), the function decomposes into
// operands before adding the whole term as a fallback, enabling finer-grained diffs.
func collectDiffs(dst *[]Term, s, t Term, env []core.VarPair) {
	if s.AlphaEqualsWithEnv(t, env) {
		return
	}
	// Early termination: an equality of size 3 means both sides are single
	// variables (the smallest possible replacement). No further search needed.
	if len(*dst) > 0 {
		if (*dst)[0].Size() == 3 {
			return
		}
	}

	// createDiff builds a candidate equality from two differing subterms.
	// If s and t appear under binders (tracked in env), it abstracts over
	// the bound variables that are actually free in s/t, so the candidate
	// equality lives at the right abstraction level for EqRewrite to use.
	createDiff := func(s, t Term, env []core.VarPair) {
		// Both sides must have the same type to form a valid equality.
		if !s.Type().Equals(t.Type()) {
			return
		}

		// Split env into per-side var lists (outer→inner order).
		sVars := make([]VarTerm, 0, len(env))
		tVars := make([]VarTerm, 0, len(env))
		for i := range env {
			sVars = append(sVars, env[i].V0)
			tVars = append(tVars, env[i].V1)
		}

		// Determine which env vars are actually free in each side.
		// Then check type compatibility before the expensive ReverseAbsVars:
		// the full type signature (free-var types ++ function-type chain) must
		// match between s and t for the equality to be well-typed.
		sFreeVars := ext.AbsFreeVars(s, sVars...)
		tFreeVars := ext.AbsFreeVars(t, tVars...)
		sTypes := append(
			utils.MapSlice(sFreeVars, (VarTerm).Type),
			ext.MatchesFun(s.Type())...)
		tTypes := append(
			utils.MapSlice(tFreeVars, (VarTerm).Type),
			ext.MatchesFun(t.Type())...)
		if !slices.EqualFunc(sTypes, tTypes, HolType.Equals) {
			return
		}

		// Wrap each side with its free env vars to form abstractions.
		// E.g. if s = P(a) with free env var a, sAbs = λa.P(a).
		sAbs := ext.ReverseAbsVars(s, sFreeVars...)
		tAbs := ext.ReverseAbsVars(t, tFreeVars...)

		d := Eq(sAbs, tAbs)
		// If both sides are single variables (minimal size), validate
		// immediately. If valid, this is optimal — clear dst and stop.
		if sAbs.Size() == 1 && tAbs.Size() == 1 {
			if _, _, ok := validateWithEqRewrite(s, t, d); ok {
				*dst = []Term{d}
			}
			return
		}
		*dst = append(*dst, d)
	}

	switch s := s.Core().(type) {
	case AppliedTerm:
		if t, ok := t.AsAppliedTerm(); ok {
			// Check if this is a binary operator
			// We don't do MatchesEQ here because 2 equalities might have
			// different side types.
			if sl, sr, ok := binaryOpMatchers(s); ok {
				if tl, tr, ok := binaryOpMatchers(t); ok {
					sOp := s.Fun().(AppliedTerm).Fun()
					tOp := t.Fun().(AppliedTerm).Fun()
					if !sOp.Equals(tOp) {
						createDiff(s, t, env)
						return
					}

					// Same binary operator - collect differences from operands first
					collectDiffs(dst, sl, tl, env)
					collectDiffs(dst, sr, tr, env)

					// Always add the full term as a fallback option
					createDiff(s, t, env)
					return
				}
			}

			// Regular application - recurse on both parts
			sFun, sArg := s.Fun(), s.Arg()
			tFun, tArg := t.Fun(), t.Arg()

			collectDiffs(dst, sFun, tFun, env)
			collectDiffs(dst, sArg, tArg, env)

			// Then add this level as a fallback candidate
			createDiff(s, t, env)
			return
		}
	case AbsTerm:
		if t, ok := t.AsAbsTerm(); ok {
			// Recurse into body with extended environment first
			newEnv := append(slices.Clone(env), core.VarPair{V0: s.Var(), V1: t.Var()})

			// Add body differences first
			collectDiffs(dst, s.Body(), t.Body(), newEnv)

			// Then add abstraction level difference as a fallback
			createDiff(s, t, env)
			return
		}
	}

	// Base case or structure mismatch
	createDiff(s, t, env)
}

// groupDiffs deduplicates a list of candidate equality terms by α-equivalence,
// returning one representative per unique (LHS, RHS) pair.
func groupDiffs(diffs []Term) []Term {
	if len(diffs) == 0 {
		return nil
	}
	if len(diffs) == 1 {
		return []Term{diffs[0]}
	}

	// Map to track unique pairs and their occurrence count
	uniquePairs := make(map[core.TermKey]Term)

	for _, diff := range diffs {
		lDiff, rDiff, _ := MatchesEQ(diff)

		// Create a key for this pair (using alpha-equal comparison)
		// For simplicity, we'll check against existing pairs
		found := false
		for key, entry := range uniquePairs {
			l, r, _ := MatchesEQ(entry)
			if l.AlphaEquals(lDiff) &&
				r.AlphaEquals(rDiff) {
				// Same replacement pattern
				uniquePairs[key] = entry
				found = true
				break
			}
		}

		if !found {
			// New unique pair
			uniquePairs[diff.AlphaKey()] = diff
		}
	}

	// Convert map to slice
	// Type compatibility is already checked.
	candidates := make([]Term, 0, len(uniquePairs))
	for _, entry := range uniquePairs {
		candidates = append(candidates, entry)
	}

	return candidates
}
