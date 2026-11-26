package core

import "github.com/euc-ai/xugo/utils"

// AppliedTerm is a function application. It is a handle over a node
// only this package can reach (see VarType).
type AppliedTerm struct{ *_AppliedTermNode }

type _AppliedTermNode struct {
	fun     Term
	arg     Term
	holType HolType
	size    int

	// memo is what the node remembers once asked (see _NodeMemo).
	memo _NodeMemoSlot
}

// _HasNameCell is one answer of AppliedTerm.HasName: a cell, once
// published, is never written again.
type _HasNameCell struct {
	name TermName
	has  bool
	next *_HasNameCell
}

func Apply(fun, arg Term) AppliedTerm { return apply(fun.kernel(), arg.kernel()) }

// apply is Apply over kernel values.
func apply(fun, arg Term) AppliedTerm {
	t, ok := fun.Type().(CompositeType)
	utils.Assert(ok &&
		t.meta.Equals(metaTypeFun) &&
		t.subTypes[0].Equals(arg.Type()))

	return AppliedTerm{&_AppliedTermNode{
		fun:     fun,
		arg:     arg,
		holType: t.subTypes[1],
		size:    fun.Size() + arg.Size()}}
}

// IsZero reports whether t is the zero handle.
func (t AppliedTerm) IsZero() bool { return t._AppliedTermNode == nil }

func (t AppliedTerm) Fun() Term { return t.fun }

func (t AppliedTerm) Arg() Term { return t.arg }

func (t AppliedTerm) Type() HolType { return t.holType }

func (t AppliedTerm) Size() int { return t.size }

func (t AppliedTerm) Equals(s Term) bool {
	if s, ok := s.AsAppliedTerm(); ok {
		return t == s ||
			(t.size == s.size && t.fun.Equals(s.fun) && t.arg.Equals(s.arg))
	}
	return false
}

func (t AppliedTerm) AlphaEquals(s Term) bool {
	return t.Equals(s) || (t.size == s.Size() && t.AlphaEqualsWithEnv(s, nil))
}

func (t AppliedTerm) Compare(s Term) int {
	if t.Equals(s) {
		return 0
	}
	return t.CompareWithEnv(s, nil)
}

func (t AppliedTerm) AlphaKey() TermKey {
	return t.memo.get().lazyAlphaKey.InitOrLoad(func() TermKey {
		return TermKey(_APPLIED_TERM_KEY_PREFIX +
			utils.GenerateHash(t.fun.AlphaKey(), t.arg.AlphaKey()))
	})
}

func (t AppliedTerm) key() TermKey {
	return t.memo.get().lazyKey.InitOrLoad(func() TermKey {
		// If the term contains no abstraction, the key and α-key are same.
		if !hasAbstraction(t) {
			return t.AlphaKey()
		}
		return TermKey(_APPLIED_TERM_KEY_PREFIX +
			utils.GenerateHash(t.fun.key(), t.arg.key()))
	})
}

// Whether the term contains abstraction. On AppliedTerm the result is
// memoized in the node's memo — the recursion is a pure structural
// fold whose per-node contribution is env-independent, so on shared
// DAGs pointer-shared subtrees are only walked once (see the
// _NodeMemo.lazyHasAbstraction for the depth-explosion rationale).
func hasAbstraction(t Term) bool {
	switch t := t.(type) {
	case VarTerm, ConstTerm:
		return false
	case AppliedTerm:
		return t.memo.get().lazyHasAbstraction.InitOrLoad(func() bool {
			return hasAbstraction(t.fun) || hasAbstraction(t.arg)
		})
	case AbsTerm:
		return true
	default:
		panic("Wrong term type.")
	}
}

func (t AppliedTerm) Frees(f VarPredicate) []VarTerm {
	if NaiveWalkNeedsMemo(t) {
		var out []VarTerm
		for _, v := range freeVarsIn(t, map[Term][]VarTerm{}) {
			if f == nil || f(v) {
				out = append(out, v)
			}
		}
		return out
	}
	freesInFun := t.fun.Frees(f)
	freesInArg := t.arg.Frees(func(v VarTerm) bool {
		return (f == nil || f(v)) && utils.None(freesInFun, v.EqualsVar)
	})
	return append(freesInFun, freesInArg...)
}

// HasFree answers whether v occurs free in t. Past the gate the term
// is walked as the DAG it is, each applied node once: the answer at a
// node depends on the node and v alone, and a node the walk has left
// behind lacked v, or the walk would have ended there. The
// higher-order unifier asks this of its pair terms at every search
// node, and imitation builds pair terms whose tree doubles per level
// over a DAG that grows by a few nodes.
func (t AppliedTerm) HasFree(v VarTerm) bool {
	if !NaiveWalkNeedsMemo(t) {
		return t.fun.HasFree(v) || t.arg.HasFree(v)
	}
	return hasFreeIn(t, v, map[AppliedTerm]struct{}{})
}

func (t AppliedTerm) AllFree(f VarPredicate) bool {
	if NaiveWalkNeedsMemo(t) {
		return utils.All(freeVarsIn(t, map[Term][]VarTerm{}), f)
	}
	return t.fun.AllFree(f) && t.arg.AllFree(f)
}

func (t AppliedTerm) HasFreeName(n TermName) bool {
	if NaiveWalkNeedsMemo(t) {
		return utils.Any(freeVarsIn(t, map[Term][]VarTerm{}),
			func(v VarTerm) bool { return v.name == n })
	}
	return t.fun.HasFreeName(n) || t.arg.HasFreeName(n)
}

func (t AppliedTerm) HasName(n TermName) bool {
	m := t.memo.get()
	head := m.hasNames.Load()
	for c := head; c != nil; c = c.next {
		if c.name == n {
			return c.has
		}
	}
	r := t.fun.HasName(n) || t.arg.HasName(n)
	// Two callers asking at once may both prepend the same answer; the
	// list then holds it twice, and either is the answer.
	cell := &_HasNameCell{name: n, has: r, next: head}
	for !m.hasNames.CompareAndSwap(cell.next, cell) {
		cell.next = m.hasNames.Load()
	}
	return r
}

func (t AppliedTerm) Substitute(substList ...TermSubst) Term {
	s, _ := t.substituteImpl(kernelTermSubsts(substList), nil)
	return s
}

func (t AppliedTerm) TypeSubstitute(substs ...TypeSubst) Term {
	if len(substs) == 0 {
		return t
	}
	s, clashed := t.typeSubstituteImpl(substs, nil, nil)
	utils.Assert(clashed.IsZero())
	return s
}

func (t AppliedTerm) DeBruijn(i int) Term { return t.deBruijnImpl(1, i, nil) }

func (t AppliedTerm) AlphaEqualsWithEnv(s Term, env []VarPair) bool {
	if s, ok := s.AsAppliedTerm(); ok && s.Type().Equals(t.Type()) {
		return t.fun.AlphaEqualsWithEnv(s.fun, env) &&
			t.arg.AlphaEqualsWithEnv(s.arg, env)
	}
	return false
}

func (t AppliedTerm) Core() Term { return t }

func (t AppliedTerm) kernel() Term {
	if t._AppliedTermNode == nil {
		panic("core: the zero AppliedTerm stands for no term")
	}
	return t
}

func (AppliedTerm) AsVar() (VarTerm, bool) { return VarTerm{}, false }

func (AppliedTerm) AsConst() (ConstTerm, bool) { return ConstTerm{}, false }

func (t AppliedTerm) AsAppliedTerm() (AppliedTerm, bool) { return t, true }

func (AppliedTerm) AsAbsTerm() (AbsTerm, bool) { return AbsTerm{}, false }

func (t AppliedTerm) typeVars() []VarType {
	if NaiveWalkNeedsMemo(t) {
		return typeVarsIn(t, map[Term][]VarType{})
	}
	return utils.OrderedSlicesUnion(
		t.fun.typeVars(), t.arg.typeVars(),
		(VarType).equalsVar, (VarType).CompareVar)
}

func (t AppliedTerm) CompareWithEnv(s Term, env []VarPair) int {
	switch s := s.kernel().(type) {
	case AppliedTerm:
		if c := t.fun.CompareWithEnv(s.fun, env); c != 0 {
			return c
		}
		return t.arg.CompareWithEnv(s.arg, env)
	case AbsTerm:
		return -1
	default:
		return 1
	}
}

// substituteImpl rewrites t under substs. Past the shared-DAG gate the
// term is walked as the DAG it is, each applied node once: the result
// at a node depends on the node and the list alone, and a shared node
// is rewritten once and its result shared again, so the result is a
// DAG of the input's shape and the walk is bounded by its nodes. The
// higher-order unifier substitutes into its pair terms at every search
// node, and imitation builds pair terms whose tree doubles per level
// over a DAG that grows by a few nodes; a walk per tree path there
// builds the whole tree, which neither ends nor fits.
func (t AppliedTerm) substituteImpl(substs []TermSubst, memo _SubstituteMemo) (Term, bool) {
	if len(substs) == 0 {
		return t, false
	}
	if memo == nil && NaiveWalkNeedsMemo(t) {
		memo = _SubstituteMemo{}
	}
	if r, ok := memo[t]; ok {
		return r.term, r.changed
	}
	fun, funChanged := t.fun.substituteImpl(substs, memo)
	arg, argChanged := t.arg.substituteImpl(substs, memo)
	r := _Substituted{term: t}
	if funChanged || argChanged {
		r = _Substituted{term: apply(fun, arg), changed: true}
	}
	if memo != nil {
		memo[t] = r
	}
	return r.term, r.changed
}

// typeSubstituteImpl rewrites the types in t under substs, below the
// binders env. Past the shared-DAG gate a shared node is rewritten
// once per binder environment it is reached under: the memo holds the
// results under this environment, and a binder opens one of its own
// for its body (see shared_dag.go).
func (t AppliedTerm) typeSubstituteImpl(
	substs []TypeSubst, env []VarPair, memo _TypeSubstituteMemo) (Term, VarTerm) {
	if memo == nil && NaiveWalkNeedsMemo(t) {
		memo = _TypeSubstituteMemo{}
	}
	if r, ok := memo[t]; ok {
		return r.term, r.clashed
	}
	term, clashed := t.typeSubstituteApplied(substs, env, memo)
	if memo != nil {
		memo[t] = _TypeSubstituted{term: term, clashed: clashed}
	}
	return term, clashed
}

// typeSubstituteApplied is typeSubstituteImpl's work at an application.
func (t AppliedTerm) typeSubstituteApplied(
	substs []TypeSubst, env []VarPair, memo _TypeSubstituteMemo) (Term, VarTerm) {
	fun, clashed := t.fun.typeSubstituteImpl(substs, env, memo)
	if !clashed.IsZero() {
		return nil, clashed
	}
	arg, clashed := t.arg.typeSubstituteImpl(substs, env, memo)
	if !clashed.IsZero() {
		return nil, clashed
	}
	if !fun.Equals(t.fun) || !arg.Equals(t.arg) {
		return apply(fun, arg), VarTerm{}
	}
	return t, VarTerm{}
}

// deBruijnImpl is deBruijnConvert at the application (see Term.deBruijnImpl).
func (t AppliedTerm) deBruijnImpl(nextFreeIndex, stopAtIndex int, memo _DeBruijnMemo) Term {
	return deBruijnConvert(t, nextFreeIndex, stopAtIndex, nil, memo)
}
