package core

import (
	"slices"

	"github.com/euc-ai/xugo/utils"
)

// AbsTerm is a lambda abstraction. It is a handle over a node only this
// package can reach (see VarType).
type AbsTerm struct{ *_AbsTermNode }

type _AbsTermNode struct {
	v       VarTerm
	body    Term
	holType HolType
	size    int

	// memo is what the node remembers once asked (see _NodeMemo).
	memo _NodeMemoSlot
}

func Abs(v VarTerm, body Term) AbsTerm { return abs(v, body.kernel()) }

// abs is Abs over a kernel value.
func abs(v VarTerm, body Term) AbsTerm {
	return AbsTerm{&_AbsTermNode{
		v:       v,
		body:    body,
		holType: MakeFun(v.holType, body.Type()),
		size:    1 + body.Size()}}
}

// IsZero reports whether t is the zero handle.
func (t AbsTerm) IsZero() bool { return t._AbsTermNode == nil }

// rebind is Abs(v, body) for a rewrite that keeps the binder's type and
// the body's — a substitution, a rename of the binder, the de Bruijn
// conversion: the abstraction's type is t's, not built again.
func (t AbsTerm) rebind(v VarTerm, body Term) AbsTerm {
	utils.Assert(v.holType.Equals(t.v.holType) && body.Type().Equals(t.body.Type()))
	return AbsTerm{&_AbsTermNode{
		v:       v,
		body:    body,
		holType: t.holType,
		size:    1 + body.Size()}}
}

func (t AbsTerm) Var() VarTerm { return t.v }

func (t AbsTerm) Body() Term { return t.body }

func (t AbsTerm) Type() HolType { return t.holType }

func (t AbsTerm) Size() int { return t.size }

func (t AbsTerm) Equals(s Term) bool {
	if s, ok := s.AsAbsTerm(); ok {
		return t == s ||
			(t.size == s.size && t.v.Equals(s.v) && t.body.Equals(s.body))
	}
	return false
}

func (t AbsTerm) AlphaEquals(s Term) bool {
	return t.Equals(s) || (t.size == s.Size() && t.AlphaEqualsWithEnv(s, nil))
}

func (t AbsTerm) Compare(s Term) int {
	if t.Equals(s) {
		return 0
	}
	return t.CompareWithEnv(s, nil)
}

func (t AbsTerm) AlphaKey() TermKey {
	return t.memo.get().lazyAlphaKey.InitOrLoad(func() TermKey {
		s := t.DeBruijn(0).(AbsTerm)
		// We use the key, not α-key, of the body in the calculation.
		// This is because the body of a de Bruijn normalized term
		// might not have legal de Bruijn so it has no α-key.
		// For example, the term is λx.(λy.x)
		// the de Bruijn normalized term is λ%1.(λ%2.%1),
		// the body is λ%2.%1, which cannot calculate de Bruijn again.
		return TermKey(_ABS_TERM_KEY_PREFIX +
			utils.GenerateHash(s.v.AlphaKey(), s.body.key()))
	})
}

func (t AbsTerm) key() TermKey {
	return t.memo.get().lazyKey.InitOrLoad(func() TermKey {
		return TermKey(_ABS_TERM_KEY_PREFIX +
			utils.GenerateHash(t.v.key(), t.body.key()))
	})
}

func (t AbsTerm) Frees(f VarPredicate) []VarTerm {
	if f != nil && !f(t.v) {
		return t.body.Frees(f)
	}
	return t.body.Frees(
		func(v VarTerm) bool { return (f == nil || f(v)) && !v.Equals(t.v) })
}

func (t AbsTerm) HasFree(v VarTerm) bool {
	return !t.v.Equals(v) && t.body.HasFree(v)
}

func (t AbsTerm) AllFree(f VarPredicate) bool {
	if f(t.v) {
		return t.body.AllFree(f)
	}
	return t.body.AllFree(
		func(v VarTerm) bool { return f(v) || v.Equals(t.v) })
}

func (t AbsTerm) HasFreeName(n TermName) bool {
	if t.v.name != n {
		return t.body.HasFreeName(n)
	}
	return !t.body.AllFree(
		func(v VarTerm) bool { return v.Equals(t.v) || v.name != n })
}

func (t AbsTerm) HasName(n TermName) bool {
	return t.v.name == n || t.body.HasName(n)
}

func (t AbsTerm) Substitute(substList ...TermSubst) Term {
	s, _ := t.substituteImpl(kernelTermSubsts(substList), nil)
	return s
}

func (t AbsTerm) TypeSubstitute(substs ...TypeSubst) Term {
	if len(substs) == 0 {
		return t
	}
	s, clashed := t.typeSubstituteImpl(substs, nil, nil)
	utils.Assert(clashed.IsZero())
	return s
}

func (t AbsTerm) DeBruijn(i int) Term { return t.deBruijnImpl(1, i, nil) }

func (t AbsTerm) AlphaEqualsWithEnv(s Term, env []VarPair) bool {
	if s, ok := s.AsAbsTerm(); ok && s.holType.Equals(t.holType) {
		return t.body.AlphaEqualsWithEnv(
			s.body,
			append(env, VarPair{t.v, s.v}))
	}
	return false
}

func (t AbsTerm) Core() Term { return t }

func (t AbsTerm) kernel() Term {
	if t._AbsTermNode == nil {
		panic("core: the zero AbsTerm stands for no term")
	}
	return t
}

func (AbsTerm) AsVar() (VarTerm, bool) { return VarTerm{}, false }

func (AbsTerm) AsConst() (ConstTerm, bool) { return ConstTerm{}, false }

func (AbsTerm) AsAppliedTerm() (AppliedTerm, bool) { return AppliedTerm{}, false }

func (t AbsTerm) AsAbsTerm() (AbsTerm, bool) { return t, true }

func (t AbsTerm) typeVars() []VarType {
	return utils.OrderedSlicesUnion(
		t.v.typeVars(), t.body.typeVars(),
		(VarType).equalsVar, (VarType).CompareVar)
}

func (t AbsTerm) CompareWithEnv(s Term, env []VarPair) int {
	if s, ok := s.AsAbsTerm(); ok {
		if c := t.v.holType.Compare(s.v.holType); c != 0 {
			return c
		}
		if c := t.body.Type().Compare(s.body.Type()); c != 0 {
			return c
		}
		return t.body.CompareWithEnv(
			s.body,
			append(env, VarPair{t.v, s.v}))
	}
	return 1
}

// substituteImpl rewrites the binder's body under substs. Past the
// shared-DAG gate the binder is remembered in the walk's memo under the
// outer list (see shared_dag.go).
func (t AbsTerm) substituteImpl(substs []TermSubst, memo _SubstituteMemo) (Term, bool) {
	if r, ok := memo[t]; ok {
		return r.term, r.changed
	}
	term, changed := t.substituteAbs(substs, memo)
	if memo != nil {
		memo[t] = _Substituted{term: term, changed: changed}
	}
	return term, changed
}

// substituteAbs is substituteImpl's work at the binder.
func (t AbsTerm) substituteAbs(substs []TermSubst, memo _SubstituteMemo) (Term, bool) {
	for i := range substs {
		// We only use the subst that is not regarding t.v,
		// but we don't want to allocate a new slice everytime,
		// so we select substs only when we know there exists some difference.
		if t.v.Equals(substs[i].VarTerm) {
			selected := append(make([]TermSubst, 0, len(substs)), substs[:i]...)
			for _, s := range substs[i+1:] {
				if !t.v.Equals(s.VarTerm) {
					selected = append(selected, s)
				}
			}
			substs = selected
			// The body is walked under another list, so with a memo of
			// its own; this one holds results under the outer list.
			memo = nil
			break
		}
	}

	if len(substs) == 0 {
		return t, false
	}

	body, changed := t.body.substituteImpl(substs, memo)
	if !changed {
		return t, false
	}

	for _, s := range substs {
		// The replacement is the smaller term and seldom mentions the
		// binder's name, so it is read first.
		if s.Term.HasFreeName(t.v.name) && t.body.HasFree(s.VarTerm) {
			// This means the subst contains var collision.
			// E.g. the original term is λx.F(x, y),
			// need to substitute y to something about x, say x+1,
			// we will rename x, get λxʹ.F(xʹ, x+1) or λy.F(y, x+1) or similar.
			// the exact new var will be determined by RenameToAvoid.
			avoidTerms := make([]Term, 0, len(substs)+2)
			avoidTerms = append(avoidTerms, t.body, body)
			for _, subst := range substs {
				avoidTerms = append(avoidTerms, subst.Term)
			}
			v := t.v.RenameToAvoid(avoidTerms...)
			body = t.body.Substitute(utils.CloneAppend(substs, MakeTermSubst(t.v, v))...)
			return t.rebind(v, body), true
		}
	}
	return t.rebind(t.v, body), true
}

// typeSubstituteImpl rewrites the binder and its body under substs,
// below the binders env. The binder is remembered in the walk's memo
// under env; its body is walked under env grown by the binder, so with
// a memo of its own (see shared_dag.go).
func (t AbsTerm) typeSubstituteImpl(
	substs []TypeSubst, env []VarPair, memo _TypeSubstituteMemo) (Term, VarTerm) {
	if r, ok := memo[t]; ok {
		return r.term, r.clashed
	}
	term, clashed := t.typeSubstituteAbs(substs, env)
	if memo != nil {
		memo[t] = _TypeSubstituted{term: term, clashed: clashed}
	}
	return term, clashed
}

// typeSubstituteAbs is typeSubstituteImpl's work at the binder.
func (t AbsTerm) typeSubstituteAbs(
	substs []TypeSubst, env []VarPair) (Term, VarTerm) {
	_v, _ := t.v.typeSubstituteImpl(substs, nil, nil)
	v := _v.(VarTerm)

	body, clashed := t.body.typeSubstituteImpl(
		substs, append(env, VarPair{v, t.v}), nil)

	if clashed.IsZero() { // no clash
		if v.Equals(t.v) && body.Equals(t.body) {
			return t, VarTerm{}
		}
		return abs(v, body), VarTerm{}
	}

	if !clashed.Equals(v) { // clash with a different var
		return nil, clashed
	}

	// clash with the current binder
	vars := utils.MapSlice(t.body.Frees(nil),
		func(v VarTerm) Term { return v.TypeSubstitute(substs...) })

	return t.
		ChangeAbsVar(v.RenameToAvoid(vars...).name).
		typeSubstituteAbs(substs, env)
}

// deBruijnImpl is deBruijnConvert at the binder (see Term.deBruijnImpl).
func (t AbsTerm) deBruijnImpl(nextFreeIndex, stopAtIndex int, memo _DeBruijnMemo) Term {
	return deBruijnConvert(t, nextFreeIndex, stopAtIndex, nil, memo)
}

// deBruijnConvert converts the abstractions of t to de Bruijn notation
// within an index window, in one pass over the term: bound pairs each
// binder above t with the de Bruijn variable it becomes, the innermost
// last, so an occurrence of a binder is renamed where it is met and no
// substitution runs over a body per binder. Past the shared-DAG gate
// memo holds the results under this window and these binders; a binder
// moves both for its body, which is converted with a memo of its own
// (see shared_dag.go). A term the conversion leaves as it is comes back
// as the same pointer.
//
// Parameters:
//   - nextFreeIndex: The next available De Bruijn index to assign (must be > 0)
//   - stopAtIndex: If > 0, defines the exclusive upper bound of the conversion window
//
// Window Adjustment Logic:
//
// 1. WINDOW DEFINITION:
//   - Window is [nextFreeIndex, stopAtIndex) when stopAtIndex > 0
//   - Window size = stopAtIndex - nextFreeIndex
//   - Conversion starts from the first abstraction, assigning indices from this window
//   - Stops when reaching stopAtIndex (only window-size abstractions are converted)
//   - Example: a window (1, 3) assigns %1 to the first abstraction, %2 to the second, then stops
//   - Example: a window (2, 5) assigns %2, %3, %4 to the first three abstractions
//
// 2. INDEX COLLISION AVOIDANCE:
//   - If the term already contains free De Bruijn variables (e.g., %2 as a free var),
//     we must avoid using those indices for our bound variables
//   - The algorithm scans for the minimum available index that doesn't conflict
//   - When a conflict is found, BOTH nextFreeIndex and stopAtIndex are incremented
//   - This preserves the window size while shifting it to avoid conflicts
//   - Example: If %2 is free and we want window [2,4), it becomes [3,5)
//
// 3. WINDOW BOUNDARY HANDLING:
//   - When nextFreeIndex >= stopAtIndex, we've exceeded the window
//   - Abstractions at or beyond the boundary are NOT converted
//   - Their bodies are still walked, to rename the occurrences of binders above
//   - Example: λx.λy.λz.M with window [1,3) converts x→%1, y→%2, but leaves z as is
//
// 4. INCREMENTAL CONVERSION:
//   - Each abstraction level increments the index by 1
//   - Nested abstractions get consecutive indices: %1, %2, %3, etc.
//   - The window can be used for partial/incremental conversion strategies
func deBruijnConvert(
	t Term, nextFreeIndex, stopAtIndex int, bound []VarPair, memo _DeBruijnMemo) Term {
	utils.Assert(nextFreeIndex > 0)
	switch t := t.(type) {
	case VarTerm:
		for _, pair := range slices.Backward(bound) {
			if t.Equals(pair.V1) {
				if pair.V0.Equals(t) {
					return t
				}
				return pair.V0
			}
		}
		return t
	case ConstTerm:
		return t
	case AppliedTerm:
		// Past the window no binder below is converted, and the binders
		// above are renamed by one substitution.
		if stopAtIndex > 0 && nextFreeIndex >= stopAtIndex {
			return t.Substitute(boundSubsts(bound)...)
		}
		if memo == nil && NaiveWalkNeedsMemo(t) {
			memo = _DeBruijnMemo{}
		}
		if r, ok := memo[t]; ok {
			return r
		}
		r := Term(t)
		fun := deBruijnConvert(t.fun, nextFreeIndex, stopAtIndex, bound, memo)
		arg := deBruijnConvert(t.arg, nextFreeIndex, stopAtIndex, bound, memo)
		if fun != t.fun || arg != t.arg {
			r = apply(fun, arg)
		}
		if memo != nil {
			memo[t] = r
		}
		return r
	case AbsTerm:
		if r, ok := memo[t]; ok {
			return r
		}
		r := deBruijnConvertAbs(t, nextFreeIndex, stopAtIndex, bound)
		if memo != nil {
			memo[t] = r
		}
		return r
	default:
		panic("Wrong term type.")
	}
}

// deBruijnConvertAbs is deBruijnConvert at a binder: the binder takes
// the window's next index, moved past any free de Bruijn variable of
// the term that holds it, and its body is converted under the window
// after that index with the binder among the bound. A variable bound
// above is the walk's to rename, so it is not a free de Bruijn variable
// here, whatever its name.
func deBruijnConvertAbs(t AbsTerm, nextFreeIndex, stopAtIndex int, bound []VarPair) Term {
	for !t.AllFree(func(v VarTerm) bool {
		return v.deBruijn == 0 || v.deBruijn != nextFreeIndex || boundAbove(bound, v)
	}) {
		nextFreeIndex++
		if stopAtIndex > 0 {
			stopAtIndex++
		}
	}
	if t.v.deBruijn == 0 && stopAtIndex > 0 && nextFreeIndex >= stopAtIndex {
		// A binder past the window stays; its body is walked for the
		// binders above alone.
		body := deBruijnConvert(t.body, nextFreeIndex, stopAtIndex, bound, nil)
		if body == t.body {
			return t
		}
		return t.rebind(t.v, body)
	}
	v := deBruijnVar(nextFreeIndex, t.v.holType)
	if v.Equals(t.v) {
		v = t.v
	} else if stopAtIndex > 0 {
		// A binder the window converts: no free de Bruijn variable of
		// the term lies past the window.
		utils.Assert(t.AllFree(func(v VarTerm) bool {
			return v.deBruijn == 0 || v.deBruijn <= stopAtIndex || boundAbove(bound, v)
		}))
	}
	body := deBruijnConvert(
		t.body, nextFreeIndex+1, stopAtIndex, append(bound, VarPair{v, t.v}), nil)
	if v == t.v && body == t.body {
		return t
	}
	return t.rebind(v, body)
}

// boundAbove reports whether v is a binder above the walk.
func boundAbove(bound []VarPair, v VarTerm) bool {
	for i := range bound {
		if bound[i].V1.Equals(v) {
			return true
		}
	}
	return false
}

// boundSubsts is the renaming of the binders above as one substitution:
// a variable is bound by the innermost binder of its name, which
// shadows the ones above, and a binder the conversion leaves as it is
// renames nothing.
func boundSubsts(bound []VarPair) []TermSubst {
	var substs []TermSubst
	var seen []VarTerm
	for _, pair := range slices.Backward(bound) {
		if utils.Any(seen, pair.V1.EqualsVar) {
			continue
		}
		seen = append(seen, pair.V1)
		if !pair.V0.Equals(pair.V1) {
			substs = append(substs, MakeTermSubst(pair.V1, pair.V0))
		}
	}
	return substs
}

// Changes the abstracted var to a new var of the same type.
// The new var cannot be free in the body — it would capture that occurrence —
// whether the current binder is an ordinary var or a de Bruijn var.
func (t AbsTerm) ChangeAbsVar(n TermName) AbsTerm {
	if t.v.deBruijn == 0 && t.v.name == n {
		return t
	}
	v := Var(n, t.v.holType)
	utils.Assert(!t.body.HasFree(v))
	return t.rebind(v, t.body.Substitute(MakeTermSubst(t.v, v)))
}
