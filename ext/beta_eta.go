package ext

import (
	"context"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// All recursive helpers accept a context.Context so long-running normalizations
// (called from unify, which may recurse into pathologically large terms) can
// bail out when the caller's deadline fires.
//
// We *panic* with QuitSentinel rather than return a partially-normalized term,
// because downstream invariants in unify (e.g. makeBodyPair expects AbsTerm
// structure for function-typed terms after eta-expansion) assume full
// normalization. Returning partial would corrupt state; panicking unwinds the
// whole unify stack cleanly. Callers must install a matching recover — see
// RecoverQuit and the defers in ext/unify/unification.go.
//
// Pass context.Background() to opt out of cancellation; CheckCtx then
// short-circuits on the always-nil Err.

// betaEtaMemo is the per-call shared-DAG memo state for the β-η walkers
// — the exact walker class that burned in the `def_expand(set_comprehension) on
// nested prod-type binders` hang: each HO-unify
// attempt βη-normalizes set_comprehension/pattern_abstraction λ-terms and exhausted its whole work
// budget in this file.
//
// These walks REBUILD terms (β-substitution results are recursed into),
// so unlike the static walkers their total work is not bounded by the
// entry term's size. They therefore thread AdaptiveMemo[betaEtaMemo]
// (see subterm.go): entry size gate + fresh-term size gate + a
// cumulative visit budget as the sound backstop.
//
// Three result tables because the three recursions compute three
// distinct pure functions of the node pointer:
//   - collapse:  BetaCollapse(t)
//   - normalize: BetaEtaNormalize(t)
//   - spine:     betaEtaNormalizeAppliedTerm(t) (differs from normalize
//     on function-typed spine nodes, which normalize would η-expand)
//
// Purity: all three results depend only on the term's α-structure (no
// binder env is threaded — capture is handled inside Substitute), so a
// per-call pointer-keyed memo cannot change any observable result.
//
// Budget note (ext/unify's _BudgetCtx consumes one unit per CheckCtx):
// every helper still calls CheckCtx on node ARRIVAL before consulting
// the memo, so cancellation stays responsive; a memoized walk simply
// arrives at fewer nodes. Consumption remains a deterministic function
// of the inputs (AdaptiveMemo's arming points are too — see its doc),
// so the determinism contract unify's budget provides is preserved.
type betaEtaMemo struct {
	collapse  PtrMemo[Term]
	normalize PtrMemo[Term]
	spine     PtrMemo[Term]
}

// Nil-safe field accessors: a nil *betaEtaMemo (memo disarmed) yields
// nil *PtrMemo tables, whose Load/Store are no-ops.
func (m *betaEtaMemo) collapseTab() *PtrMemo[Term] {
	if m == nil {
		return nil
	}
	return &m.collapse
}

func (m *betaEtaMemo) normalizeTab() *PtrMemo[Term] {
	if m == nil {
		return nil
	}
	return &m.normalize
}

func (m *betaEtaMemo) spineTab() *PtrMemo[Term] {
	if m == nil {
		return nil
	}
	return &m.spine
}

// betaEtaWalk is the adaptive walk state threaded through the trio.
type betaEtaWalk = AdaptiveMemo[betaEtaMemo]

// β collapse recursively
// This is equivalent to prop.Rhs(prop.deepBeta(t)), but faster.
//
// Shared-DAG memoization, adaptive: see betaEtaMemo.
func BetaCollapse(ctx context.Context, t Term) Term {
	a := AdaptiveFor[betaEtaMemo](t)
	return betaCollapse(ctx, t, &a)
}

func betaCollapse(ctx context.Context, t Term, a *betaEtaWalk) Term {
	utils.CheckCtx(ctx)
	m := a.Arrive()
	switch t := t.Core().(type) {
	case VarTerm, ConstTerm:
		return t
	case AppliedTerm:
		if r, ok := m.collapseTab().Load(t); ok {
			return r
		}
		r := betaCollapseApplied(ctx, t, a)
		a.Memo().collapseTab().Store(t, r)
		return r
	case AbsTerm:
		if r, ok := m.collapseTab().Load(t); ok {
			return r
		}
		r := Term(t)
		if s := betaCollapse(ctx, t.Body(), a); !s.Equals(t.Body()) {
			r = Abs(t.Var(), s)
		}
		a.Memo().collapseTab().Store(t, r)
		return r
	default:
		panic("Wrong term type.")
	}
}

func betaCollapseApplied(ctx context.Context, t AppliedTerm, a *betaEtaWalk) Term {
	if tFun, ok := t.Fun().AsAbsTerm(); ok {
		tArg := betaCollapse(ctx, t.Arg(), a)
		// (λx.f(x))(x) = f(x)
		if tFun.Var().Equals(tArg) {
			return betaCollapse(ctx, tFun.Body(), a)
		}
		// (λx.f(x))(y) = f(y)
		sub := tFun.Body().Substitute(MakeTermSubst(tFun.Var(), tArg))
		// The substitution duplicates tArg (pointer-shared) at every
		// occurrence of the bound var; the result can cross the size
		// gate even when the top-level input didn't.
		a.ArmFor(sub)
		return betaCollapse(ctx, sub, a)
	}
	fun, arg := betaCollapse(ctx, t.Fun(), a), betaCollapse(ctx, t.Arg(), a)
	if !fun.Equals(t.Fun()) || !arg.Equals(t.Arg()) {
		rebuilt := Apply(fun, arg)
		a.ArmFor(rebuilt)
		return betaCollapse(ctx, rebuilt, a)
	}
	return t
}

// η-collapse
// λx.t(x) -> t (providing x not in t)
// This is equivalent to prop.Rhs(prop.deepRewrite(prop.etaRewrite)(t)), but faster.
func EtaCollapse(ctx context.Context, t Term) Term {
	utils.CheckCtx(ctx)
	switch t := t.Core().(type) {
	case VarTerm, ConstTerm:
		return t
	case AppliedTerm:
		fun, arg := EtaCollapse(ctx, t.Fun()), EtaCollapse(ctx, t.Arg())
		if !fun.Equals(t.Fun()) || !arg.Equals(t.Arg()) {
			return Apply(fun, arg)
		}
		return t
	case AbsTerm:
		body := EtaCollapse(ctx, t.Body())
		if body, ok := body.AsAppliedTerm(); ok &&
			body.Arg().Equals(t.Var()) &&
			!body.Fun().HasFree(t.Var()) {
			return body.Fun()
		}
		if !body.Equals(t.Body()) {
			return core.Abs(t.Var(), body)
		}
		return t
	default:
		panic("Wrong term type.")
	}
}

// for t with type (A0, A1, ..., An → B),
// t -> λx0:A0.λx1:A1....λxn:An.t(x0, x1, ..., xn)
// such that t(x0, x1, ..., xn) has an atomic type B.
//
// Non-recursive on term structure (bounded by type arity), so does not take
// quit — it always terminates quickly.
func etaExpand(t Term) Term {
	types := MatchesFun(t.Type())
	numArgs := getNumArgs(t)
	Assert(len(types) > 1)
	vars := make([]VarTerm, len(types)-1)
	s := t
	for i, ti := range utils.BeforeLast(types) {
		name := TermName(utils.Subscript(utils.X_DOT, i+numArgs))
		for t.HasName(name) ||
			utils.Any(vars[:i], utils.Curry((VarTerm).HasName, name)) {
			name = utils.NextName(name)
		}
		vars[i] = core.Var(name, ti)
		s = Apply(s, vars[i])
	}
	Assert(!IsFunType(s.Type()))
	s = ReverseAbsVars(s, vars...)
	Assert(s.Type().Equals(t.Type()))
	return s
}

// Returns the number of arguments that MatchesApply(t) would produce,
// without allocating the args slice.
func getNumArgs(t Term) int {
	if t, ok := t.AsAppliedTerm(); ok {
		return getNumArgs(t.Fun()) + 1
	}
	return 0
}

// β-η normalize
//   - β-collapse everywhere when applicable.
//   - η-expand t to λx0.λx1....λxn.t(x0, x1, ..., xn)
//     such that t(x0, x1, ..., xn) has an atom type.
//   - then recursively β-η normalize all arguments.
//
// this is different from the result of prop.DeepBetaEta,
// where η-collapse rather than η-expansion is used.
//
// Shared-DAG memoization, adaptive: see betaEtaMemo.
func BetaEtaNormalize(ctx context.Context, t Term) Term {
	a := AdaptiveFor[betaEtaMemo](t)
	return betaEtaNormalize(ctx, t, &a)
}

func betaEtaNormalize(ctx context.Context, t Term, a *betaEtaWalk) Term {
	utils.CheckCtx(ctx)
	m := a.Arrive()
	switch t := t.Core().(type) {
	case VarTerm, ConstTerm:
		if IsFunType(t.Type()) {
			expanded := etaExpand(t)
			a.ArmFor(expanded)
			return betaEtaNormalize(ctx, expanded, a)
		}
		return t

	case AppliedTerm:
		if r, ok := m.normalizeTab().Load(t); ok {
			return r
		}
		var r Term
		if IsFunType(t.Type()) {
			expanded := etaExpand(t)
			a.ArmFor(expanded)
			r = betaEtaNormalize(ctx, expanded, a)
		} else {
			r = betaEtaNormalizeAppliedTerm(ctx, t, a)
		}
		a.Memo().normalizeTab().Store(t, r)
		return r

	case AbsTerm:
		if r, ok := m.normalizeTab().Load(t); ok {
			return r
		}
		r := Term(t)
		if s := betaEtaNormalize(ctx, t.Body(), a); !s.Equals(t.Body()) {
			r = Abs(t.Var(), s)
		}
		a.Memo().normalizeTab().Store(t, r)
		return r
	default:
		panic("Wrong term type.")
	}
}

// Normalize an application term.
// It recursively normalizes along the left spine, normalizes the current
// argument, and beta-collapses after each application. The function part's
// head abstraction (if any) is normalized once.
func betaEtaNormalizeAppliedTerm(ctx context.Context, t AppliedTerm, a *betaEtaWalk) Term {
	utils.CheckCtx(ctx)
	if r, ok := a.Arrive().spineTab().Load(t); ok {
		return r
	}
	r := betaEtaNormalizeAppliedTermImpl(ctx, t, a)
	a.Memo().spineTab().Store(t, r)
	return r
}

func betaEtaNormalizeAppliedTermImpl(ctx context.Context, t AppliedTerm, a *betaEtaWalk) Term {
	// Normalize along the left spine first: if the function part is itself an
	// application, process it recursively to accumulate prior arguments; else
	// decide whether to normalize the head abstraction.
	fun := t.Fun()
	switch tFun := t.Fun().(type) {
	case AppliedTerm:
		fun = betaEtaNormalizeAppliedTerm(ctx, tFun, a)
	case AbsTerm:
		fun = betaEtaNormalize(ctx, tFun, a)
	}
	arg := betaEtaNormalize(ctx, t.Arg(), a)
	if !fun.Equals(t.Fun()) || !arg.Equals(t.Arg()) {
		rebuilt := Apply(fun, arg)
		a.ArmFor(rebuilt)
		return betaEtaNormalizeAppliedTerm(ctx, rebuilt, a)
	}
	// Both fun and arg are unchanged,
	// so we simply β-collapse it.
	return betaCollapse(ctx, t, a)
}

// Whether 2 terms are α-equal after β-η normalization.
func BetaEtaEquals(ctx context.Context, s, t Term) bool {
	return s.AlphaEquals(t) ||
		BetaEtaNormalize(ctx, s).AlphaEquals(BetaEtaNormalize(ctx, t))
}
