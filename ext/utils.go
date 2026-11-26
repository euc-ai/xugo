package ext

import (
	"fmt"
	"iter"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

type (
	HolType        = core.HolType
	VarType        = core.VarType
	CompositeType  = core.CompositeType
	TypeSubst      = core.TypeSubst
	Term           = core.Term
	VarTerm        = core.VarTerm
	ConstTerm      = core.ConstTerm
	AppliedTerm    = core.AppliedTerm
	AbsTerm        = core.AbsTerm
	TermName       = core.TermName
	TermSubst      = core.TermSubst
	Prop           = core.Prop
	Thm            = core.ThmCert
	ConstMetaMap   = utils.Map[TermName, core.ConstTermMeta]
	TermKeyPropMap = utils.Map[core.TermKey, Prop]
)

var (
	Assert      = utils.Assert
	TypeA       = core.TypeA()
	TypeB       = core.MakeVarType("B")
	TypeBool    = core.TypeBool()
	MakeFun     = core.MakeFun
	MakeVarType = core.MakeVarType[string]
	IsBool      = core.IsBool
	Abs         = core.Abs
	Eq          = core.Eq
	MatchesEQ   = core.MatchesEQ
)

// MakeType is the variadic-arity wrapper for the common
// `core.MakeCompositeType(core.MakeMetaType(name, n), subs...)`
// pattern: arity is inferred from the number of subtypes, so all
// composite types — 0-ary (`MakeType("int")`), 1-ary
// (`MakeType("list", NumType)`), 2-ary (`MakeType("prod", a, b)`), …
// — share one Go form.
//
// emit's printCompositeType uses this as the generic fallback when
// no per-type alias (TypeBool / NumType) applies: any new
// type the corpus encounters renders in a readable form without a
// hand-edited goprint case. Aliases stay as opt-in shortcuts for
// the very-high-frequency types where the saved characters are
// worth the extra global.
func MakeType(name string, subs ...HolType) HolType {
	return core.MakeCompositeType(core.MakeMetaType(TermName(name), len(subs)), subs...)
}

/**
 * p, q, r: Bool
 * x, y, z: A
 * w: B
 * P, Q: A → Bool
 * R: A → B → Bool
 * S: Bool → Bool
 * f, g: A → B
 * h: Bool → Bool → Bool
 */
var initVars = struct{ p, q, r, x, y, z, w, P, Q, R, S, f, g, h *TermWrapper }{
	p: Var("p", TypeBool),
	q: Var("q", TypeBool),
	r: Var("r", TypeBool),
	x: Var("x", TypeA),
	y: Var("y", TypeA),
	z: Var("z", TypeA),
	w: Var("w", TypeB),
	P: Var("P", MakeFun(TypeA, TypeBool)),
	Q: Var("Q", MakeFun(TypeA, TypeBool)),
	R: Var("R", MakeFun(TypeA, TypeB, TypeBool)),
	S: Var("S", MakeFun(TypeBool, TypeBool)),
	f: Var("f", MakeFun(TypeA, TypeB)),
	g: Var("g", MakeFun(TypeA, TypeB)),
	h: Var("h", MakeFun(TypeBool, TypeBool, TypeBool)),
}

func TestConst(n TermName, holType HolType) *TermWrapper {
	return Const(core.MakeConstMeta(n, holType), holType)
}

// TypeDefSourceThm forces the existence source recorded by NewTypeDef.
// The supplied Forcer retains the caller's builder scope and trust boundary.
// A constant that has no type-definition source is refused.
func TypeDefSourceThm(meta core.ConstTermMeta, f core.Forcer) core.ThmCert {
	source := meta.DefSource()
	Assert(source != nil)
	// A realized source needs no force or builder scope.
	thm := core.AsThm(source)
	if cert, ok := thm.(core.ThmCert); ok {
		return cert
	}
	return f.Force(thm)
}

// Returns whether the type contains →.
func IsFunType(t HolType) bool {
	s, ok := t.(CompositeType)
	return ok && s.Meta().Equals(core.MetaTypeFun())
}

// Decomposes function types.
// For type (A, B, ...) → C (which technically is A → (B → (... → C))),
// returns A, B, ..., C
func MatchesFun(t HolType) []HolType {
	var types []HolType
	for ; IsFunType(t); t = t.(CompositeType).SubType(1) {
		types = append(types, t.(CompositeType).SubType(0))
	}
	return append(types, t)
}

// the type has a certain var.
func TypeHasVar(t HolType, v VarType) bool {
	switch t := t.(type) {
	case core.VarType:
		return t.Equals(v)
	case core.CompositeType:
		for i := range t.Meta().Arity() {
			if TypeHasVar(t.SubType(i), v) {
				return true
			}
		}
		return false
	default:
		panic("Should not happen.")
	}
}

// Whether the type has any var that satisfies the given predicate.
func TypeAnyVar(t HolType, f core.VarTypePredicate) bool {
	switch t := t.(type) {
	case core.VarType:
		return f(t)
	case core.CompositeType:
		for i := range t.Meta().Arity() {
			if TypeAnyVar(t.SubType(i), f) {
				return true
			}
		}
		return false
	default:
		panic("Should not happen.")
	}
}

// Whether the term has any component with a relevant type var.
// Not same as whether the type of the term has the relevant type var.
// Past the shared-DAG gate the walk visits a shared node once: a node
// it has left behind lacked the var, or the walk would have ended
// there. The higher-order unifier asks this of every pair term for
// every type substitution of a search step.
func TermHasTypeVar(t Term, v VarType) bool {
	return TermAnyTypeVar(t, func(w VarType) bool { return w.Equals(v) })
}

// Whether the term has any relevant type var (not the vars of the type of this term)
// that satisfies the given predicate. Bounded over a shared DAG as
// TermHasTypeVar is.
func TermAnyTypeVar(t Term, f core.VarTypePredicate) bool {
	return termAnyTypeVar(t, f, SeenSetFor(t))
}

// termAnyTypeVar is TermAnyTypeVar over the nodes seen has not visited.
func termAnyTypeVar(t Term, f core.VarTypePredicate, seen *SeenSet) bool {
	switch t := t.Core().(type) {
	case VarTerm, ConstTerm:
		return TypeAnyVar(t.Type(), f)
	case AppliedTerm:
		return !seen.Visited(t) &&
			(termAnyTypeVar(t.Fun(), f, seen) || termAnyTypeVar(t.Arg(), f, seen))
	case AbsTerm:
		return !seen.Visited(t) &&
			(termAnyTypeVar(t.Var(), f, seen) || termAnyTypeVar(t.Body(), f, seen))
	default:
		panic("Should not happen.")
	}
}

// PropHasTypeVars returns true if the proposition contains any type variable.
func PropHasTypeVars(p core.Prop) bool {
	return TermAnyTypeVar(p.Conclusion(), utils.FullPredicate) ||
		p.AnyHyp(utils.Curry(TermAnyTypeVar, utils.FullPredicate))
}

// Decomposes multi-variable function.
// For term f(x, y, ...) (which technically is f(x)(y)(...))
// returns f and x, y, ...
//
// Capacity hint: the args slice holds one Term per applied argument
// in the leftmost spine, NOT one per subterm node. Using `t.Size()`
// as the capacity was catastrophic on pointer-shared DAG inputs —
// Size() sums naive subterm counts, which on a balanced diamond DAG
// grows as O(2^depth) while the actual argument-count is bounded by
// the term's function arity (typically ≤ 4). At depth 28 the pre-
// allocation alone was 500M×16B ≈ 8 GB per call and drove the
// documented def_expand(set_comprehension) session hang. Use a small constant
// capacity and let append() grow — amortized O(1), never wasteful.
func MatchesApply(t Term) (Term, []Term) {
	args := make([]Term, 0, 4)
	head := matchesApplyImpl(t, &args)
	return head, args
}

func matchesApplyImpl(t Term, args *[]Term) Term {
	if t, ok := t.AsAppliedTerm(); ok {
		head := matchesApplyImpl(t.Fun(), args)
		*args = append(*args, t.Arg())
		return head
	}
	return t
}

// Decomposes abstracted term.
// For term λx.λy....t,
// returns x, y, ... and t.
func MatchesAbs(t Term) ([]VarTerm, Term) {
	var vars []VarTerm
	for abs, ok := t.AsAbsTerm(); ok; abs, ok = t.AsAbsTerm() {
		vars, t = append(vars, abs.Var()), abs.Body()
	}
	return vars, t
}

// Add vars to the abstracted term in reverse order.
// The vars must be var terms.
func ReverseAbsVars[T Term](t Term, vars ...T) Term {
	return utils.Foldr(
		func(s Term, v T) Term { return Abs(Term(v).(VarTerm), s) }, t, vars)
}

// Given term t and vars,
// gradually add the vars in reverse order that are free to be added to t.
func ReverseAbsFreeVars(t Term, vars ...VarTerm) Term {
	for _, v := range slices.Backward(vars) {
		if t.HasFree(v) {
			t = Abs(v, t)
		}
	}
	return t
}

// returns the free vars of t that are in vars.
// the input vars and output vars are all from outside to inside.
func AbsFreeVars(t Term, vars ...VarTerm) []VarTerm {
	addVars := make([]VarTerm, 0, len(vars))
	// we goes from inside to outside to make sure
	// the edge cases when there are duplicated abstracted vars
	// are covered.
	for _, v := range slices.Backward(vars) {
		if t.HasFree(v) {
			addVars = append(addVars, v)
		}
	}
	slices.Reverse(addVars)
	return addVars
}

// Given abstracted vars and body of a given term s
// (we use this input because in many case the same input term
// are used repeatedly, so we don't want to decomposes it many times).
// returns a function that takes a term t and a var list
// outputs vars that are free in this term, such that
// ReverseAbsVars(t, vars) is α-equal to s.
// If this is not possible, returns nil, false.
// This is cheaper than directly checking ReverseAbsVars(t, vars) is α-equal to s,
// because usually this is not true and we can quit early without
// calculate the full abstracted term.
func ReverseAbsFreeVarsMatch(
	vars0 []VarTerm,
	body0 Term) func(Term, ...VarTerm) ([]VarTerm, bool) {
	return func(s1 Term, vars1 ...VarTerm) ([]VarTerm, bool) {
		vars, body := MatchesAbs(s1)

		if !body0.Type().Equals(body.Type()) {
			return nil, false
		}

		// num of extra vars that needed to match.
		numMissingVars := len(vars0) - len(vars)
		if numMissingVars < 0 || len(vars1) < numMissingVars {
			return nil, false
		}

		// the types of existing vars must match.
		for i := range vars {
			j := i + numMissingVars
			if !vars[i].Type().Equals(vars0[j].Type()) {
				return nil, false
			}
		}

		addVars := make([]VarTerm, 0, len(vars1))
		// We go from inside to outside to make sure
		// the edge cases when there are duplicated abstracted vars
		// are covered.
		for _, v := range slices.Backward(vars1) {
			if s1.HasFree(v) {
				// the edge cases of duplicated abstracted vars
				if utils.Any(addVars, v.EqualsVar) {
					continue
				}
				// if too many vars, quit early.
				if len(addVars)+1 > numMissingVars {
					return nil, false
				}
				// if the type doesn't match, quit early.
				if !v.Type().Equals(vars0[len(vars0)-len(addVars)-1].Type()) {
					return nil, false
				}
				// the edge cases of duplicated abstracted vars
				if utils.Any(addVars, v.EqualsVar) {
					continue
				}
				addVars = append(addVars, v)
			}
		}

		if len(addVars) != numMissingVars {
			return nil, false
		}

		// make addVars from outside to inside.
		slices.Reverse(addVars)

		// vars and vars0 and vars1 are from outside to inside.
		env := make([]core.VarPair, len(vars0))
		// fill V1 in env with addvars then vars.
		for i := range addVars {
			env[i] = core.VarPair{V0: vars0[i], V1: addVars[i]}
		}
		for i := range vars {
			j := i + len(addVars)
			env[j] = core.VarPair{V0: vars0[j], V1: vars[i]}
		}
		if body0.AlphaEqualsWithEnv(body, env) {
			return addVars, true
		}
		return nil, false
	}
}

// a term that looks like λa.λb....f(x, y, ...)
// where the fun and args of the abstracted term body
// are all var terms, and the abstracted vars are no less than the args.
// this kind of term may lead to infinite loop in denote rewriting.
func IsSimpleAbs(t Term) bool {
	vars, body := MatchesAbs(t)
	fun, args := MatchesApply(body)
	if len(vars) < len(args) {
		return false
	}
	if _, ok := fun.AsVar(); !ok {
		return false
	}
	for _, arg := range args {
		if _, ok := arg.AsVar(); !ok {
			return false
		}
	}
	return true
}

// Renames abstracted vars of the 2 abstracted Terms with the same type
// such that the 2 abstracted vars are exactly same.
func AlignAbstractedVar(t0, t1 Term) (AbsTerm, AbsTerm) {
	_t0, ok0 := t0.AsAbsTerm()
	_t1, ok1 := t1.AsAbsTerm()
	Assert(ok0 && ok1 && t0.Type().Equals(t1.Type()))
	if _t0.Var().Equals(_t1.Var()) {
		// do nothing
	} else if !_t1.HasName(_t0.Var().Name()) {
		_t1 = _t1.ChangeAbsVar(_t0.Var().Name())
	} else if !_t0.HasName(_t1.Var().Name()) {
		_t0 = _t0.ChangeAbsVar(_t1.Var().Name())
	} else {
		n := _t0.Var().Name()
		for _t0.Body().HasName(n) || _t1.Body().HasName(n) {
			n = utils.NextName(n)
		}
		_t0 = _t0.ChangeAbsVar(n)
		_t1 = _t1.ChangeAbsVar(n)
	}
	return _t0, _t1
}

// Calculates the length of the decomposition of a term.
func DecomposeLenBinaryOp(m BinaryOpMatcher) (decomposeLen func(Term) int) {
	return func(t Term) int {
		if l, r, ok := m(t); ok {
			return decomposeLen(l) + decomposeLen(r)
		}
		return 1
	}
}

func CollectVars(t Term, vars map[core.TermKey]VarTerm) {
	switch t := t.Core().(type) {
	case VarTerm:
		vars[t.AlphaKey()] = t
	case ConstTerm:
	case AppliedTerm:
		CollectVars(t.Fun(), vars)
		CollectVars(t.Arg(), vars)
	case AbsTerm:
		vars[t.Var().AlphaKey()] = t.Var()
		CollectVars(t.Body(), vars)
	default:
		panic("Wrong term type.")
	}
}

// Collects non-builtin constants in a term.
// Size-gated shared-DAG dedup (see subterm.go): the walk is a pure
// structural fold whose per-node contribution is env-independent, so on
// large terms pointer-shared subtrees are visited once.
func CollectConstTerms(t Term, consts map[core.TermKey]ConstTerm) {
	collectConstTerms(t, consts, SeenSetFor(t))
}

// CollectConstNames collects the names of the constants in t, the
// logic's own excluded as CollectConstTerms excludes them, and asks no
// term for its key: a constant's key is spelled on the first ask, and
// a scan over a corpus of statements that asked one of every constant
// would spell them all.
func CollectConstNames(t Term, names map[core.TermName]bool) {
	collectConstNames(t, names, SeenSetFor(t))
}

// CollectVarNames appends to names the names of the variables
// occurring in t that it does not hold yet, bound or free — a superset
// of the free ones, read without tracking binders and without a
// term's key, for a reader that asks only whether a name may occur
// free — in order of first occurrence.
func CollectVarNames(t Term, names []core.TermName) []core.TermName {
	return collectVarNames(t, names, SeenSetFor(t))
}

func collectVarNames(t Term, names []core.TermName, seen *SeenSet) []core.TermName {
	switch t := t.Core().(type) {
	case VarTerm:
		for _, n := range names {
			if n == t.Name() {
				return names
			}
		}
		return append(names, t.Name())
	case ConstTerm:
		return names
	case AppliedTerm:
		if seen.Visited(t) {
			return names
		}
		return collectVarNames(t.Arg(), collectVarNames(t.Fun(), names, seen), seen)
	case AbsTerm:
		if seen.Visited(t) {
			return names
		}
		return collectVarNames(t.Body(), names, seen)
	default:
		panic("Wrong term type.")
	}
}

// IsLogicalConstName reports a constant of the logic itself — a
// connective, a quantifier, equality, the choice operator, the
// conditional — which no collection of a statement's constants lists.
func IsLogicalConstName(name core.TermName) bool {
	return name == utils.EqStr || name == utils.HilbertStr ||
		name == utils.TrueStr || name == utils.FalseStr ||
		name == utils.NegStr || name == utils.AndStr ||
		name == utils.OrStr || name == utils.ImplyStr ||
		name == utils.ForAllStr || name == utils.ExistsStr ||
		name == utils.UniqueStr || name == CondStr
}

func collectConstNames(t Term, names map[core.TermName]bool, seen *SeenSet) {
	switch t := t.Core().(type) {
	case VarTerm:
	case ConstTerm:
		if !IsLogicalConstName(t.Name()) {
			names[t.Name()] = true
		}
	case AppliedTerm:
		if seen.Visited(t) {
			return
		}
		collectConstNames(t.Fun(), names, seen)
		collectConstNames(t.Arg(), names, seen)
	case AbsTerm:
		if seen.Visited(t) {
			return
		}
		collectConstNames(t.Body(), names, seen)
	default:
		panic("Wrong term type.")
	}
}

func collectConstTerms(
	t Term, consts map[core.TermKey]ConstTerm, seen *SeenSet) {
	switch t := t.Core().(type) {
	case VarTerm:
	case ConstTerm:
		if IsLogicalConstName(t.Name()) {
			return
		}
		consts[t.AlphaKey()] = t
	case AppliedTerm:
		if seen.Visited(t) {
			return
		}
		collectConstTerms(t.Fun(), consts, seen)
		collectConstTerms(t.Arg(), consts, seen)
	case AbsTerm:
		if seen.Visited(t) {
			return
		}
		collectConstTerms(t.Body(), consts, seen)
	default:
		panic("Wrong term type.")
	}
}

// TermContainsConstName reports whether any const named `name` occurs in t.
// Size-gated shared-DAG dedup (see subterm.go): misses ("not in this
// subtree") are env-independent, so on large terms pointer-shared
// subtrees are checked once. NOTE: a per-node caller (e.g. a
// prune-rewrite consulting this at every level of a memoized walk) still
// pays one walk per unique node — if that ever shows up hot, thread a
// cross-call cache at the call site.
func TermContainsConstName(t Term, name TermName) bool {
	return termContainsConstName(t, name, SeenSetFor(t))
}

func termContainsConstName(t Term, name TermName, seen *SeenSet) bool {
	switch t := t.Core().(type) {
	case VarTerm:
		return false
	case ConstTerm:
		return t.Name() == name
	case AppliedTerm:
		if seen.Visited(t) {
			return false
		}
		return termContainsConstName(t.Fun(), name, seen) ||
			termContainsConstName(t.Arg(), name, seen)
	case AbsTerm:
		if seen.Visited(t) {
			return false
		}
		return termContainsConstName(t.Body(), name, seen)
	default:
		panic("Wrong term type.")
	}
}

// CollectDefinableConsts returns all non-builtin constants in a prop that
// DefAction can actually unfold here:
//   - Type 1 (NewConstDef): meta has `.def` (a Thm) → unfold via def thm.
//   - Type 2 (NewTypeDef):  meta has `.defSource` (⊢ P(_)). Only include if
//     the defSource is Proved (i.e., we have a Thm under the Prop interface),
//     because DefAction's Type 2 path needs TypeDefExpand → Thm outputs to
//     feed into applyLemma. A meta whose defSource is not (yet) proved — an
//     unforced promise, or a restored Prop — isn't actionable via DefAction;
//     callers cite the type definition's abs/rep entry instead.
func CollectDefinableConsts(prop Prop) []ConstTerm {
	constMap := make(map[core.TermKey]ConstTerm)
	CollectConstTerms(prop.Conclusion(), constMap)
	for _, h := range prop.Hyps() {
		CollectConstTerms(h, constMap)
	}

	var result []ConstTerm
	for _, c := range constMap {
		if !c.DefThm().IsZero() {
			result = append(result, c)
			continue
		}
		if src := c.Meta().DefSource(); src != nil && src.Proved() {
			result = append(result, c)
		}
	}
	return result
}

func MergeBinaryOpMatchers(matchers ...BinaryOpMatcher) BinaryOpMatcher {
	return func(t Term) (Term, Term, bool) {
		for _, m := range matchers {
			if l, r, ok := m(t); ok {
				return l, r, true
			}
		}
		return nil, nil, false
	}
}

type TermSubstsGroup []TermSubst

func (substs TermSubstsGroup) String() string {
	if len(substs) == 0 {
		return "Empty substitution group."
	}
	s := make([]string, len(substs))
	for i, subst := range substs {
		s[i] = fmt.Sprintf(
			"%d: %s %s %s", i, PrintTerm(subst.VarTerm), utils.MapStr, PrintTerm(subst.Term))
	}
	return strings.Join(s, "\n")
}

func (substs TermSubstsGroup) Clone() TermSubstsGroup { return utils.Clone(substs) }

func (substs TermSubstsGroup) NonEmpty() bool { return len(substs) > 0 }

func (substs TermSubstsGroup) Size() int {
	totalSize := 0
	for i := range substs {
		totalSize += substs[i].Term.Size()
	}
	return totalSize
}

func NameInVars(vars []VarTerm, n TermName) bool {
	return utils.Any(vars, utils.Curry((VarTerm).HasName, n))
}

// Ordered var list. Dedup built in.
type VarList struct{ list []VarTerm }

func (s *VarList) Iter() iter.Seq[VarTerm] { return slices.Values(s.list) }

func (s *VarList) Section(i, j int) []VarTerm { return utils.Clone(s.list[i:j]) }

func (s *VarList) Empty() bool { return len(s.list) == 0 }

func (s *VarList) Size() int { return len(s.list) }

func (s *VarList) Has(v VarTerm) bool { return utils.Any(s.list, v.EqualsVar) }

func (s *VarList) HasNo(v VarTerm) bool { return !utils.Any(s.list, v.EqualsVar) }

func (s *VarList) Ind(i int) VarTerm { return s.list[i] }

func (s *VarList) Find(v VarTerm) int { return slices.IndexFunc(s.list, v.EqualsVar) }

func (s *VarList) HasName(n TermName) bool { return NameInVars(s.list, n) }

func (s *VarList) AllFreeIn(t Term) bool { return utils.All(s.list, t.HasFree) }

func (s *VarList) Clone() VarList { return VarList{utils.Clone(s.list)} }

func (s *VarList) Backward() iter.Seq2[int, VarTerm] {
	return slices.Backward(s.list)
}

// The lists contain the same elements, order doesn't matter.
func (s *VarList) ElementEquals(t *VarList) bool {
	return s.Size() == t.Size() &&
		utils.All(s.list, t.Has) &&
		utils.All(t.list, s.Has)
}

func (s *VarList) Add(v VarTerm) bool {
	if s.Has(v) {
		return false
	}
	s.list = append(s.list, v)
	return true
}

// Returns whether the element exists.
func (s *VarList) Remove(v VarTerm) bool {
	if !s.Has(v) {
		return false
	}
	for j, u := range s.list {
		if u.Compare(v) == 0 {
			s.list = slices.Delete(s.list, j, j+1)
			return true
		}
	}
	panic("Fail to remove element.")
}

// Keeps the position of the old v in the list.
// Returns whether the element to be replaced exists.
func (s *VarList) Replace(v0, v1 VarTerm) bool {
	Assert(s.HasNo(v1))

	if s.HasNo(v0) {
		return false
	}

	for j, v := range s.list {
		if v.Compare(v0) == 0 {
			s.list[j] = v1
			return true
		}
	}
	panic("Fail to replace element.")
}

// IsDisjunctive reports whether `t` is a well-formed disjunctive clause
// shape — the invariant the clause layer's `prepareClause` relies on:
//
//	∀x. L₁ ∨ L₂ ∨ … ∨ Lₙ
//
// where each Lᵢ is an atom or a negated atom, and no ∃, ∃!, ∧, ⇒, ⇔ or
// negation-of-quantifier/bool-op appears anywhere in the outer skeleton.
// (∨ nests freely; ∀ recurses into its body.) An equality between
// functions is an atom here whatever its codomain: clause normalization
// never extensionalizes one (prop.DisjunctNormalizeRewrite).
func IsDisjunctive(t Term) bool {
	Assert(IsBool(t))
	if _t := MatchesNOT(t); _t != nil {
		if !MatchesFORALL(_t).IsZero() {
			return false
		} else if !MatchesEXISTS(_t).IsZero() {
			return false
		} else if !MatchesUNIQUE(_t).IsZero() {
			return false
		} else if _, _, ok := BinaryBooleanOpMatchers(_t); ok {
			return false
		}
	} else if !MatchesEXISTS(t).IsZero() {
		return false
	} else if !MatchesUNIQUE(t).IsZero() {
		return false
	} else if _, _, ok := MatchesAND(t); ok {
		return false
	} else if _, _, ok := MatchesIMPLY(t); ok {
		return false
	} else if _, _, ok := MatchesIFF(t); ok {
		return false
	}
	if abs := MatchesFORALL(t); !abs.IsZero() {
		return IsDisjunctive(abs.Body())
	}
	if _, _, ok := MatchesOR(t); ok {
		return utils.All(DecomposesOR(t), IsDisjunctive)
	}
	return true
}
