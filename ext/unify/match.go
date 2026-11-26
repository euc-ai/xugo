package unify

import (
	"context"
	"maps"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Term MATCHING — the deterministic, one-sided, search-free fragment of
// higher-order unification.
//
// Unlike Unify (two-sided: both sides may carry meta-variables, so it must
// branch through Huet's imitate/project and is bounded by a budget), TermMatch
// has a CLOSED/rigid target: only the pattern's variables (named in
// `instantiable`) are flexible. With one side rigid the procedure collapses to
// a single deterministic recursive descent — at every node exactly one rule
// applies; no branching, no backtracking, no budget. Only the two decidable
// higher-order shapes are admitted:
//
//   - Miller pattern: a flex var applied to pairwise-distinct in-scope bound
//     vars,  P(x̄) ≐ t  ⇒  P ↦ λx̄.t   (the unique MGU, Miller 1991). This is
//     the same witness ext/unify's tryMillerPattern builds — here without the
//     occurs / free-meta-var guards, which are vacuous against a rigid target.
//   - abstract-all: a flex var applied to closed args,  P(ā) ≐ t  ⇒
//     P ↦ λz̄. t[āᵢ↦zᵢ, all occurrences].  This is the unitary collapse of
//     Huet's `imitate` for the closed-target case (no fresh meta-vars, no
//     branch).
//
// Anything outside these shapes fails the match.
//
// Matching runs UNDER the pattern/target binders: descending through aligned
// ∀/λ adds the shared binder to `localBound` (rigid), and a witness may
// legitimately mention such an in-scope bound var — the caller (a rewrite
// driver) is responsible for keeping that var in scope at the substitution
// site (and re-generalizing it when carrying the result back out through the
// binders). For a top-level call (no binders descended) every witness is
// closed.
//
// Returns the binding σ (pattern var name → witness) with σ(pattern) α-equal to
// `target`, or ok=false. σ is a plain map so callers can both look a witness up
// by name (e.g. to instantiate a ∀-rule) and turn it into substitutions for
// Term.Substitute (see BindingSubsts).

// MatchBindings maps each matched pattern variable to its witness term.
type MatchBindings = map[TermName]Term

// MatchRecurse is the matcher-supplied continuation a MatchHook uses to dispatch
// sub-matches at the current binder depth — its `localBound` is captured, so a
// theory rule that splits or reorients a node (e.g. omega's `=`-commutativity)
// stays correct under ∀/λ descent.
type MatchRecurse = func(pat, t Term, b MatchBindings) bool

// MatchHook lets a caller inject a theory-specific rule at each node, fired
// after the type and flex-head checks and before the default structural switch.
// Return `handled=true` to short-circuit with `ok` as the matcher's verdict for
// this node; `handled=false` to fall through to the default rule. Recurse via
// `recurse` so the matcher's binder state propagates correctly. Used by omega
// to make `=` commutative at every nesting level.
type MatchHook = func(pat, t Term, b MatchBindings, recurse MatchRecurse) (handled, ok bool)

// TermMatch attempts to match `pattern` (vars named in `instantiable` flexible,
// all else rigid) against the closed `target`. See the file comment.
func TermMatch(pattern, target Term, instantiable TermNameSet) (MatchBindings, bool) {
	b := MatchBindings{}
	if !termMatch(pattern, target, instantiable, &VarList{}, b, matchOpts{}) {
		return nil, false
	}
	return b, true
}

// TermMatchApprox is TermMatch with FIRST-ORDER APPROXIMATION for a
// flexible head applied to arguments that are neither a Miller pattern
// nor closed (`P(iterated_op(op, s, f))` against `P₀(iterated_op(real_add, s₀,
// f₀))`): the head binds to the target's head applied to the leading
// arguments the pattern does not spell, and the pattern's arguments
// match the trailing ones pairwise — Lean's flex-rigid fallback
// (`?f ?x ?y` against `g a u v` at ?f := g a), and the reading `apply`
// needs of a law stated for an arbitrary predicate, relation or
// operation, whose instance is a variable (`add`) or a partial
// application (`vec_add(add)`) alike. A target with fewer arguments
// than the pattern is no match. Opt-in: only callers that verify the
// instance afterwards (the By executor's apply rung does, against the
// kernel's own instantiation) take it; the plain TermMatch and every
// consumer of it are untouched.
func TermMatchApprox(pattern, target Term, instantiable TermNameSet) (MatchBindings, bool) {
	b := MatchBindings{}
	if !termMatch(pattern, target, instantiable, &VarList{}, b, matchOpts{foApprox: true}) {
		return nil, false
	}
	return b, true
}

// TermMatchApproxWith is TermMatchApprox over caller-supplied bindings.
func TermMatchApproxWith(pattern, target Term, instantiable TermNameSet, b MatchBindings) bool {
	return termMatch(pattern, target, instantiable, &VarList{}, b, matchOpts{foApprox: true})
}

// TermMatchApproxEtaWith is TermMatchApproxWith reading a rigid
// abstraction against a term that is none up to η: where the pattern
// spells `λx. t(x)` and the target the function, or the other way
// round, the side without the abstraction is η-expanded one binder and
// the match descends, so `λT. ⋃T` matches `big_union` and `λr x. r * x`
// matches `mul`. A flexible head is bound as before — a bare slot takes
// the target as spelled. Opt-in as the approximation is: the caller
// verifies the instance (the apply rung's dry run reads it back through
// the kernel up to βη, the identity the rung's manual states).
func TermMatchApproxEtaWith(pattern, target Term, instantiable TermNameSet, b MatchBindings) bool {
	return termMatch(pattern, target, instantiable, &VarList{}, b, matchOpts{foApprox: true, eta: true})
}

// matchOpts carries a match's optional behaviors down the recursion.
type matchOpts struct {
	hook     MatchHook
	foApprox bool
	// eta reads a rigid abstraction against a non-abstraction of the
	// same type up to η (TermMatchApproxEtaWith).
	eta bool
}

// TermMatchWith is TermMatch with caller-supplied bindings (so multiple match
// calls can share metavar resolutions) and an optional theory hook. Pass
// hook=nil for plain matching; the unhooked path is byte-for-byte the original
// TermMatch behavior.
func TermMatchWith(pattern, target Term, instantiable TermNameSet,
	b MatchBindings, hook MatchHook) bool {
	return termMatch(pattern, target, instantiable, &VarList{}, b, matchOpts{hook: hook})
}

// BindingSubsts converts a MatchBindings into a substitution group ready for
// Term.Substitute.
func BindingSubsts(b MatchBindings) TermSubstsGroup {
	out := make(TermSubstsGroup, 0, len(b))
	for n, t := range b {
		out = append(out, MakeTermSubst(core.Var(n, t.Type()), t))
	}
	return out
}

func termMatch(pat, t Term, instantiable TermNameSet, localBound *VarList, b MatchBindings, o matchOpts) bool {
	if !pat.Type().Equals(t.Type()) {
		return false
	}

	// Flexible head? (a pattern var, not shadowed by a descended binder).
	head, args := ext.MatchesApply(pat)
	if hv, ok := head.AsVar(); ok && instantiable.Has(hv.Name()) && !localBound.Has(hv) {
		return matchFlexible(hv, args, t, instantiable, localBound, b, o)
	}

	if o.hook != nil {
		recurse := func(p, t Term, bb MatchBindings) bool {
			return termMatch(p, t, instantiable, localBound, bb, o)
		}
		if handled, ok := o.hook(pat, t, b, recurse); handled {
			return ok
		}
	}

	switch p := pat.Core().(type) {
	case VarTerm, ConstTerm:
		if o.eta && isAbs(t) {
			return termMatch(etaExpandOnce(pat, t), t, instantiable, localBound, b, o)
		}
		return pat.AlphaEquals(t)
	case AppliedTerm:
		ta, ok := t.Core().(AppliedTerm)
		if !ok {
			if o.eta && isAbs(t) {
				return termMatch(etaExpandOnce(pat, t), t, instantiable, localBound, b, o)
			}
			return false
		}
		return termMatch(p.Fun(), ta.Fun(), instantiable, localBound, b, o) &&
			termMatch(p.Arg(), ta.Arg(), instantiable, localBound, b, o)
	case AbsTerm:
		if _, ok := t.Core().(AbsTerm); !ok {
			if o.eta {
				return termMatch(pat, etaExpandOnce(t, pat), instantiable, localBound, b, o)
			}
			return false
		}
		// Align the two binders to a shared var, then descend with it rigid.
		ap, at := ext.AlignAbstractedVar(pat, t)
		localBound.Add(ap.Var())
		defer localBound.Remove(ap.Var())
		return termMatch(ap.Body(), at.Body(), instantiable, localBound, b, o)
	}
	return false
}

// matchFlexible resolves a flexible-head application P(a1..an) ≐ t.
func matchFlexible(hv VarTerm, args []Term, t Term,
	instantiable TermNameSet, localBound *VarList, b MatchBindings, o matchOpts) bool {

	// Bare flex var: bind directly.
	if len(args) == 0 {
		return bindMatch(b, hv, t)
	}

	// Miller pattern: every arg a pairwise-distinct in-scope bound var.
	if argVars, ok := distinctBoundArgs(args, localBound); ok {
		return bindMatch(b, hv, ext.ReverseAbsVars(t, argVars...))
	}

	// First-order approximation (opt-in, TermMatchApprox): read the
	// target as an application of at least the pattern's arity, bind
	// the head to the target's head applied to the leading arguments
	// the pattern does not spell, match the pattern's arguments against
	// the trailing ones pairwise — a candidate the caller verifies.
	// Tried on a copy so a failed attempt leaves the bindings as they
	// were. A target head that is a bound variable is not bound to: the
	// witness would escape its binder.
	if o.foApprox {
		thead, targs := ext.MatchesApply(t)
		if extra := len(targs) - len(args); extra >= 0 {
			headVar, isVar := thead.AsVar()
			if !isVar || !localBound.Has(headVar) {
				head := thead
				if extra > 0 {
					head = ext.Apply(thead, targs[:extra]...)
				}
				trial := maps.Clone(b)
				if bindMatch(trial, hv, head) {
					ok := true
					for i := range args {
						if !termMatch(args[i], targs[extra+i], instantiable, localBound, trial, o) {
							ok = false
							break
						}
					}
					if ok {
						maps.Copy(b, trial)
						return true
					}
				}
			}
		}
	}

	// abstract-all: args must be closed w.r.t. the rule vars (no nested flex),
	// and the abstraction must be NON-VACUOUS — every arg occurs in t (a vacuous
	// abstraction would match any term of the right type, a wildcard).
	for _, a := range args {
		if argMentionsFlex(a, instantiable, localBound, b, hv) {
			return false
		}
		if !ext.IsSub(a, t) {
			return false
		}
	}
	bound := t
	for i := len(args) - 1; i >= 0; i-- {
		z := freshMatchVar(i, bound, args[i].Type())
		bound = replaceAllSubterm(bound, args[i], z)
		bound = Abs(z, bound)
	}
	return bindMatch(b, hv, bound)
}

// bindMatch records hv ↦ t, enforcing consistency: a flex var bound more than
// once (it occurs at several pattern positions) must get the same witness.
func bindMatch(b MatchBindings, v VarTerm, t Term) bool {
	if prev, ok := b[v.Name()]; ok {
		if prev.AlphaEquals(t) {
			return true
		}
		// One witness, two spellings: a flex head applied to a bound
		// var binds through the Miller branch as an abstraction
		// (`λx. f(x)`), the same head bare binds the head itself (`f`).
		// They are η-equal, and a pattern that mentions its variable
		// both ways (`image(f, s)` beside `λy. … f(x) …`) must not
		// fail on the spelling. The first binding stays what it was;
		// only the consistency check reads modulo βη.
		ctx := context.Background()
		return ext.BetaEtaNormalize(ctx, prev).AlphaEquals(ext.BetaEtaNormalize(ctx, t))
	}
	if !v.Type().Equals(t.Type()) {
		return false
	}
	b[v.Name()] = t
	return true
}

// distinctBoundArgs returns the arg vars when every arg is a pairwise-distinct
// var currently in `localBound`; ok=false otherwise.
func distinctBoundArgs(args []Term, localBound *VarList) ([]VarTerm, bool) {
	seen := utils.Set[TermName]{}
	out := make([]VarTerm, 0, len(args))
	for _, a := range args {
		av, ok := a.AsVar()
		if !ok || !localBound.Has(av) || seen.Has(av.Name()) {
			return nil, false
		}
		seen.Add(av.Name())
		out = append(out, av)
	}
	return out, true
}

// argMentionsFlex conservatively rejects an abstract-all arg that still contains
// an unresolved rule var: the flex head hv, any instantiable rule var, or any
// already-bound flex name. We do not solve nested flex-flex shapes.
func argMentionsFlex(a Term, instantiable TermNameSet, localBound *VarList, b MatchBindings, hv VarTerm) bool {
	return len(a.Frees(func(v VarTerm) bool {
		if localBound.Has(v) {
			return false
		}
		if v.Equals(hv) || instantiable.Has(v.Name()) {
			return true
		}
		_, ok := b[v.Name()]
		return ok
	})) > 0
}

// isAbs reports whether t is an abstraction.
func isAbs(t Term) bool {
	_, ok := t.Core().(AbsTerm)
	return ok
}

// etaExpandOnce is `λx. t(x)` for a t of function type, x a variable
// free in neither t nor other — the match aligns it with the binder of
// the abstraction on the other side (termMatch's eta reading). The
// types were checked equal before the term shapes were compared, so t
// has the abstraction's type.
func etaExpandOnce(t, other Term) Term {
	domain := ext.MatchesFun(t.Type())[0]
	x := freshMatchVar(0, t, domain)
	for other.HasFreeName(x.Name()) {
		x = core.Var(utils.NextName(x.Name()), domain)
	}
	return Abs(x, ext.Apply(ext.WrapTerm(t), ext.WrapTerm(x)).Core())
}

// freshMatchVar picks a ƶ-named var (type ty) not free in `scope`.
func freshMatchVar(i int, scope Term, ty HolType) VarTerm {
	name := utils.Subscript(TermName(utils.Z_STROKE), i)
	for scope.HasFreeName(name) {
		name = utils.NextName(name)
	}
	return core.Var(name, ty)
}

// replaceAllSubterm replaces every subterm α-equal to `target` in t with `repl`
// (plain structural traversal; abstract-all calls it with closed target/repl).
func replaceAllSubterm(t, target, repl Term) Term {
	if t.Type().Equals(target.Type()) && t.AlphaEquals(target) {
		return repl
	}
	switch tt := t.Core().(type) {
	case AppliedTerm:
		f := replaceAllSubterm(tt.Fun(), target, repl)
		a := replaceAllSubterm(tt.Arg(), target, repl)
		if f.Equals(tt.Fun()) && a.Equals(tt.Arg()) {
			return t
		}
		return ext.Apply(ext.WrapTerm(f), ext.WrapTerm(a)).Core()
	case AbsTerm:
		body := replaceAllSubterm(tt.Body(), target, repl)
		if body.Equals(tt.Body()) {
			return t
		}
		return Abs(tt.Var(), body)
	}
	return t
}
