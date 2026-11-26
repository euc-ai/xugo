package core

import (
	"cmp"
	"fmt"
	"slices"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/utils"
)

// VarTerm is a variable. It is a handle over a node only this package
// can reach (see VarType).
type VarTerm struct{ *_VarTermNode }

type _VarTermNode struct {
	name    TermName
	holType HolType

	// de Bruijn level, default to be 0.
	deBruijn int

	// Term key. Lazily calculated.
	lazyKey utils.Lazy[TermKey]
}

type VarPair struct{ V0, V1 VarTerm }

func Var[Name ~string](n Name, holType HolType) VarTerm {
	// PERCENT is reserved for deBruijn vars. Replaces it with MACRON.
	if _n, ok := strings.CutPrefix(string(n), utils.PercentStr); ok {
		n = Name(utils.MacronStr + _n)
	}
	return VarTerm{&_VarTermNode{name: TermName(n), holType: holType.core()}}
}

// IsZero reports whether t is the zero handle.
func (t VarTerm) IsZero() bool { return t._VarTermNode == nil }

// Creates a var for de Bruijn level, using the level itself as name.
// Only used internally.
func deBruijnVar(i int, holType HolType) VarTerm {
	utils.Assert(i > 0)
	return VarTerm{&_VarTermNode{
		name:     TermName(utils.PercentStr + strconv.Itoa(i)),
		holType:  holType,
		deBruijn: i}}
}

func (t VarTerm) Name() TermName { return t.name }

func (t VarTerm) Type() HolType { return t.holType }

func (VarTerm) Size() int { return 1 }

func (t VarTerm) Equals(s Term) bool {
	if s, ok := s.AsVar(); ok {
		return t == s ||
			(t.name == s.name && t.holType.Equals(s.holType) && t.deBruijn == s.deBruijn)
	}
	return false
}

func (t VarTerm) AlphaEquals(s Term) bool { return t.Equals(s) }

func (t VarTerm) Compare(s Term) int { return t.CompareWithEnv(s, nil) }

func (t VarTerm) AlphaKey() TermKey {
	return t.lazyKey.InitOrLoad(func() TermKey {
		return TermKey(fmt.Sprintf(
			"%s%s_%s", _VAR_TERM_KEY_PREFIX, t.name, t.holType.Key()))
	})
}

func (t VarTerm) AlphaEqualsWithEnv(s Term, env []VarPair) bool {
	if s, ok := s.AsVar(); ok && t.holType.Equals(s.holType) {
		for _, pair := range slices.Backward(env) {
			e0, e1 := pair.V0.Equals(t), pair.V1.Equals(s)
			if e0 && e1 {
				return true
			} else if e0 || e1 {
				return false
			}
		}
		return t.Equals(s)
	}
	return false
}

func (t VarTerm) key() TermKey { return t.AlphaKey() }

func (t VarTerm) Frees(f VarPredicate) []VarTerm {
	if f == nil || f(t) {
		return []VarTerm{t}
	}
	return nil
}

func (t VarTerm) HasFree(v VarTerm) bool { return t.Equals(v) }

func (t VarTerm) AllFree(f VarPredicate) bool { return f(t) }

func (t VarTerm) HasFreeName(n TermName) bool { return t.name == n }

func (t VarTerm) HasName(n TermName) bool { return t.name == n }

func (t VarTerm) Substitute(substList ...TermSubst) Term {
	s, _ := t.substituteImpl(kernelTermSubsts(substList), nil)
	return s
}

func (t VarTerm) TypeSubstitute(substs ...TypeSubst) Term {
	if len(substs) == 0 {
		return t
	}
	s, clashed := t.typeSubstituteImpl(substs, nil, nil)
	utils.Assert(clashed.IsZero())
	return s
}

func (t VarTerm) DeBruijn(int) Term { return t }

func (t VarTerm) Core() Term { return t }

func (t VarTerm) kernel() Term {
	if t._VarTermNode == nil {
		panic("core: the zero VarTerm stands for no term")
	}
	return t
}

func (t VarTerm) AsVar() (VarTerm, bool) { return t, true }

func (VarTerm) AsConst() (ConstTerm, bool) { return ConstTerm{}, false }

func (VarTerm) AsAppliedTerm() (AppliedTerm, bool) { return AppliedTerm{}, false }

func (VarTerm) AsAbsTerm() (AbsTerm, bool) { return AbsTerm{}, false }

func (t VarTerm) typeVars() []VarType { return t.holType.TypeVars() }

func (t VarTerm) CompareWithEnv(s Term, env []VarPair) int {
	if s, ok := s.AsVar(); ok {
		// if env exists, compare the vars based on their appearing positions.
		// the inner one is considered larger than the outer one.
		// the appearing one is considered larger than the non appearing one.
		for _, pair := range slices.Backward(env) {
			if pair.V0.Equals(t) && pair.V1.Equals(s) {
				return 0
			} else if pair.V0.Equals(t) {
				return 1
			} else if pair.V1.Equals(s) {
				return -1
			}
		}

		if c := t.holType.Compare(s.holType); c != 0 {
			return c
		}
		// We compare deBruijn before name because names are compared as
		// strings, so if we compare name first, "%10" will be smaller than "%9",
		// which will cause some issues.
		if c := cmp.Compare(t.deBruijn, s.deBruijn); c != 0 {
			return c
		}
		return cmp.Compare(t.name, s.name)
	}
	return -1
}

func (t VarTerm) substituteImpl(substs []TermSubst, _ _SubstituteMemo) (Term, bool) {
	for i := range substs {
		if t.Equals(substs[i].VarTerm) {
			if t.Equals(substs[i].Term) {
				return t, false
			}
			return substs[i].Term, true
		}
	}
	return t, false
}

// typeSubstituteImpl rewrites the variable's type under substs, below
// the binders env. A shared variable is rewritten once per region of
// the walk's memo, so the result keeps the term's sharing.
func (t VarTerm) typeSubstituteImpl(
	substs []TypeSubst, env []VarPair, memo _TypeSubstituteMemo) (Term, VarTerm) {
	if r, ok := memo[t]; ok {
		return r.term, r.clashed
	}
	term, clashed := t.typeSubstituteVar(substs, env)
	if memo != nil {
		memo[t] = _TypeSubstituted{term: term, clashed: clashed}
	}
	return term, clashed
}

// typeSubstituteVar is typeSubstituteImpl's work at the variable.
func (t VarTerm) typeSubstituteVar(
	substs []TypeSubst, env []VarPair) (Term, VarTerm) {
	newType := t.holType.Substitute(substs...)
	for i := range env {
		// Handle bound occurrences first: if this var equals the original binder, map to the new binder.
		if t.Equals(env[i].V1) {
			return env[i].V0, VarTerm{}
		}
		// Then detect potential capture after type substitution: same name and type as the new binder.
		if t.name == env[i].V0.name && newType.Equals(env[i].V0.holType) {
			return nil, env[i].V0
		}
	}
	if newType.Equals(t.holType) {
		return t, VarTerm{}
	}
	return Var(t.name, newType), VarTerm{}
}

func (t VarTerm) deBruijnImpl(int, int, _DeBruijnMemo) Term { return t }

// DeBruijnIndex returns the 1-based position assigned to this variable by
// the DeBruijn rename: %i corresponds to the i-th binder (outermost is %1)
// in the original abstraction chain. Returns 0 for non-DeBruijn vars.
func (t VarTerm) DeBruijnIndex() int { return t.deBruijn }

func (t VarTerm) EqualsVar(s VarTerm) bool { return t.Equals(s) }

// Renames the var to a different name.
// E.g. x -> y, a -> b, x_0 -> x_1, etc.
func (t VarTerm) Rename() VarTerm {
	utils.Assert(t.deBruijn == 0)
	return Var(utils.NextName(t.name), t.holType)
}

// Renames the var to avoid all names in the given terms.
func (t VarTerm) RenameToAvoid(terms ...Term) VarTerm {
	utils.Assert(t.deBruijn == 0)
	n := t.name
	for utils.Any(terms, utils.Curry(Term.HasName, n)) {
		n = utils.NextName(n)
	}
	if n != t.name {
		return Var(n, t.holType)
	}
	return t
}
