package prop

import (
	"regexp"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

type (
	HolType           = core.HolType
	VarType           = core.VarType
	CompositeType     = core.CompositeType
	TypeSubst         = core.TypeSubst
	TermSubst         = core.TermSubst
	Term              = core.Term
	VarTerm           = core.VarTerm
	ConstTerm         = core.ConstTerm
	AppliedTerm       = core.AppliedTerm
	AbsTerm           = core.AbsTerm
	TermName          = core.TermName
	Prop              = core.Prop
	Thm               = core.ThmCert
	VarList           = ext.VarList
	TermNamePredicate = utils.Predicate[TermName]
)

var (
	Assert        = utils.Assert
	TypeA         = core.TypeA()
	TypeB         = ext.TypeB
	TypeBool      = core.TypeBool()
	MakeFun       = core.MakeFun
	IsBool        = core.IsBool
	MakeTypeSubst = core.MakeTypeSubst
	Abs           = core.Abs
	Eq            = core.Eq
	MatchesEQ     = core.MatchesEQ
	WrapTerm      = ext.WrapTerm
	Var           = ext.Var
	Const         = ext.Const
	Apply         = ext.Apply
	MakeTermSubst = ext.MakeTermSubst

	F                = ext.F
	T                = ext.T
	NOT              = ext.NOT
	AND              = ext.AND
	OR               = ext.OR
	IMPLY            = ext.IMPLY
	FORALL           = ext.FORALL
	EXISTS           = ext.EXISTS
	UNIQUE           = ext.UNIQUE
	Not              = ext.Not
	And              = ext.And
	Or               = ext.Or
	ForAll           = ext.ForAll
	Exists           = ext.Exists
	Unique           = ext.Unique
	MatchesAbs       = ext.MatchesAbs
	MatchesNOT       = ext.MatchesNOT
	MatchesAND       = ext.MatchesAND
	MatchesOR        = ext.MatchesOR
	MatchesIFF       = ext.MatchesIFF
	MatchesIMPLY     = ext.MatchesIMPLY
	MatchesFORALL    = ext.MatchesFORALL
	MatchesEXISTS    = ext.MatchesEXISTS
	MatchesUNIQUE    = ext.MatchesUNIQUE
	DecomposesAND    = ext.DecomposesAND
	DecomposesOR     = ext.DecomposesOR
	DecomposesFORALL = ext.DecomposesFORALL
	DecomposesEXISTS = ext.DecomposesEXISTS
)

/**
 * p, q, r: Bool
 * x, y: A
 * z: B
 * P, Q: A → Bool
 * R: A → B → Bool
 * S: Bool → Bool
 * f, g: A → B
 * h: Bool → Bool → Bool
 */
var initVars = struct{ p, q, r, x, y, z, P, Q, R, S, f, g, h *ext.TermWrapper }{
	p: Var("p", TypeBool),
	q: Var("q", TypeBool),
	r: Var("r", TypeBool),
	x: Var("x", TypeA),
	y: Var("y", TypeA),
	z: Var("z", TypeB),
	P: Var("P", MakeFun(TypeA, TypeBool)),
	Q: Var("Q", MakeFun(TypeA, TypeBool)),
	R: Var("R", MakeFun(TypeA, TypeB, TypeBool)),
	S: Var("S", MakeFun(TypeBool, TypeBool)),
	f: Var("f", MakeFun(TypeA, TypeB)),
	g: Var("g", MakeFun(TypeA, TypeB)),
	h: Var("h", MakeFun(TypeBool, TypeBool, TypeBool)),
}

func MakeProp(c Term, hyps ...Term) *PropWrapper {
	return WrapProp(core.MakeProp(c, hyps...))
}

// IsTypeMatchOf finds a substitution on p's type variables that makes its
// terms alpha-equal to q's, allowing only variables accepted by instantiable.
// Bound term variables may be renamed; free term variables keep their names.
// The hypotheses are paired in their stored canonical order, so a match that
// would reorder them may be missed. An identical pair returns an empty list.
// The result is a candidate substitution, applied by core.PropTypeInst.
func IsTypeMatchOf(p, q Prop, instantiable core.VarTypePredicate) ([]TypeSubst, bool) {
	p, q = p.Core(), q.Core()
	if p.NumHyps() != q.NumHyps() || p.Conclusion().Size() != q.Conclusion().Size() {
		return nil, false
	}
	var typeEnv []TypeSubst
	if !typeMatches(p.Conclusion(), q.Conclusion(), nil, instantiable, &typeEnv) {
		return nil, false
	}
	for i := range p.NumHyps() {
		if !typeMatches(p.Hyp(i), q.Hyp(i), nil, instantiable, &typeEnv) {
			return nil, false
		}
	}
	// Identity bindings constrain later positions during the walk, but need
	// not be included in the substitution handed to the caller.
	return slices.DeleteFunc(typeEnv, func(s TypeSubst) bool { return s.HolType.Equals(s.VarType) }), true
}

// IsTypeVariantOf restricts IsTypeMatchOf to bijective type-variable renamings.
func IsTypeVariantOf(p, q Prop) ([]TypeSubst, bool) {
	substs, ok := IsTypeMatchOf(p, q, utils.FullPredicate[VarType])
	if !ok || !isTypeVarBijection(substs) {
		return nil, false
	}
	return substs, true
}

func isTypeVarBijection(substs []TypeSubst) bool {
	for i, s := range substs {
		v, ok := s.HolType.(VarType)
		if !ok {
			return false
		}
		for _, prior := range substs[:i] {
			if prior.HolType.(VarType).Equals(v) {
				return false
			}
		}
	}
	return true
}

// typeMatches shares one type environment across all leaves and pairs bound
// variables from the innermost binder outward, respecting shadowing.
func typeMatches(t, s Term, env []core.VarPair, instantiable core.VarTypePredicate, typeEnv *[]TypeSubst) bool {
	t, s = t.Core(), s.Core()
	switch t := t.(type) {
	case VarTerm:
		sv, ok := s.AsVar()
		if !ok {
			return false
		}
		for _, pair := range slices.Backward(env) {
			e0, e1 := pair.V0.Equals(t), pair.V1.Equals(sv)
			if e0 && e1 {
				return true
			} else if e0 || e1 {
				return false
			}
		}
		return t.Name() == sv.Name() && t.DeBruijnIndex() == sv.DeBruijnIndex() &&
			core.MatchTypeInto(t.Type(), sv.Type(), instantiable, typeEnv)
	case ConstTerm:
		sc, ok := s.AsConst()
		return ok && t.Meta().Equals(sc.Meta()) && core.MatchTypeInto(t.Type(), sc.Type(), instantiable, typeEnv)
	case AppliedTerm:
		sa, ok := s.AsAppliedTerm()
		return ok && typeMatches(t.Fun(), sa.Fun(), env, instantiable, typeEnv) &&
			typeMatches(t.Arg(), sa.Arg(), env, instantiable, typeEnv)
	case AbsTerm:
		sa, ok := s.AsAbsTerm()
		if !ok || !core.MatchTypeInto(t.Var().Type(), sa.Var().Type(), instantiable, typeEnv) {
			return false
		}
		return typeMatches(t.Body(), sa.Body(), append(env, core.VarPair{V0: t.Var(), V1: sa.Var()}), instantiable, typeEnv)
	default:
		panic("typeMatches: unsupported term")
	}
}

// whether hyps0 ⊆ hyps1, both ORDERED and deduplicated.
// One merge — each slice is walked once, len(hyps0) + len(hyps1) comparisons,
// and a missing element ends it.
func hypsSubset(s0, s1 Prop) bool {
	j := 0
	for h := range s0.HypIter() {
		for {
			if j == s1.NumHyps() {
				return false
			}
			if c := s1.Hyp(j).Compare(h); c > 0 {
				return false
			} else {
				j++
				if c == 0 {
					break
				}
			}
		}
	}
	return true
}

// Proposition s is stronger than t, meaning that
// 1. the hyps of s are included in the hyps of t (modulo α-equal)
// 2. the conclusions are same, or the conlusion of s is ⊥.
func IsStronger(s, t Prop) bool {
	return (s.Conclusion().Equals(F) ||
		s.Conclusion().AlphaEquals(t.Conclusion())) && hypsSubset(s, t)
}

// A var is not free in a prop except the given hyps.
func NotFreeInHyps(t Prop, x VarTerm, except ...Term) bool {
	for h := range t.HypIter() {
		if utils.Any(except, h.AlphaEquals) {
			continue
		}
		if h.HasFree(x) {
			return false
		}
	}
	return true
}

// If prop s is weaker than t, weaken s to t. If s is proved, this returns a proved version of
// t whose conclusion is SYNTACTICALLY equal to t.Conclusion() — not merely α-equivalent.
//
// Bound-var name fidelity is load-bearing for record/replay determinism. When a cited
// lemma's stored Thm is α-equivalent to the recorded payload but uses different bound-var
// names (e.g. `∀kʹ.∃n.…` vs `∀n.∃kʹ.…`), a subsequent strip_quant in the consumer proof
// produces a Skolem constant whose name depends on which binder it peels — different bound
// names → different Skolem constants → different leaf AlphaKey → replay diverges from
// record. So WeakenTo's contract is "produce a Thm of t's SYNTACTIC form", not just t's
// α-class. The earlier `if s.AlphaEquals(t) { return s }` fast path returned s's syntactic
// form silently, violating this contract for α-equivalent-but-renamed cases.
//
// Implementation: when conclusions α-equal but differ syntactically, align via
// EqMP(Refl(t.Concl), s). Refl yields ⊢ t.Concl = t.Concl (syntactic RHS = t.Concl); EqMP
// requires only that the equation's LHS α-equal s's conclusion — which IsStronger already
// guarantees. The fast path (conclusions already syntactic-equal) skips the EqMP, so the
// common case carries zero extra kernel work.
func WeakenTo(s, t Prop) Prop {
	if !IsStronger(s, t) {
		return nil
	}
	_s := WrapProp(s)
	// Reify the conclusion to t.Conclusion()'s SYNTACTIC form. Skip when
	//   - conclusions are already syntactically equal: common fast path, no work needed.
	//   - s.Concl is F and t.Concl is not F: the FalseDerives branch below already
	//     produces t.Conclusion() syntactically.
	if !_s.Conclusion().Equals(t.Conclusion()) &&
		_s.Conclusion().AlphaEquals(t.Conclusion()) {
		_s = Refl(t.Conclusion()).EqMP(_s)
	}
	if _s.Conclusion().Equals(F) && !t.Conclusion().Equals(F) {
		_s = _s.DeriveTrans(FalseDerives(t.Conclusion()))
	}
	for h := range t.HypIter() {
		if !_s.HasHyp(h) {
			_h := Assume(h)
			_s = _h.Deduct(_s).EqMP(_h)
		}
	}
	return _s
}

// Left hand side of the conclusion of the prop.
// Panic if the conclusion is not an equality.
func Lhs(t Prop) Term {
	l, _, ok := MatchesEQ(t.Conclusion())
	Assert(ok)
	return l
}

// Right hand side of the conclusion of the prop.
// Panic if the conclusion is not an equality.
func Rhs(t Prop) Term {
	_, r, ok := MatchesEQ(t.Conclusion())
	Assert(ok)
	return r
}

// Given a const `c` with a def thm `⊢ c = body` and args `t1, ..., tN`,
// returns a kernel-verified proof of `c(t1, ..., tN) = body(t1, ..., tN)`
// with each β-redex collapsed.
// Used wherever a const's def thm is applied as a rewrite primitive
// (the bootstrap proofs, the ∃! bridges).
func ExpandDef(c ConstTerm, args ...Term) *PropWrapper {
	def := c.DefThm()
	Assert(!def.IsZero() && c.Equals(Lhs(def)))
	w := WrapProp(def)
	for _, arg := range args {
		w = w.RightApply(arg).RewriteConclRhs(betaRewrite)
	}
	return w
}

// ContainsConstName reports whether any term in `p` (conclusion or
// any hypothesis) contains a const occurrence whose name matches `name`.
func ContainsConstName(p Prop, name core.TermName) bool {
	return ext.TermContainsConstName(p.Conclusion(), name) ||
		p.AnyHyp(func(h Term) bool { return ext.TermContainsConstName(h, name) })
}

// Adds ∀ for all free vars in the conclusion except those free in the hyps.
func ForAllConclFreeVars(t *PropWrapper) *PropWrapper {
	for _, v := range t.Conclusion().Frees(
		func(v VarTerm) bool { return NotFreeInHyps(t, v) }) {
		t = t.ConclForAll(v)
	}
	return t
}

// s and t are alpha equivalent except for negations.
func negAlphaEquals(s, t Term) bool {
	if n := MatchesNOT(s); n != nil && n.AlphaEquals(t) {
		return true
	}
	if n := MatchesNOT(t); n != nil && n.AlphaEquals(s) {
		return true
	}
	return false
}

var subscriptDashRe = regexp.MustCompile(`^.+_\d+$`)
var subscriptNoDashRe = regexp.MustCompile(`([\p{L}'])(\d+)$`)

// Renames quantifier vars so they have number subscripts.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func subscriptVarsRewrite(
	m ext.QuantifierMatcher,
	avoid TermNamePredicate) Rewrite {

	rewrite := func(t Term) (w *PropWrapper) {
		defer func() {
			if w != nil {
				Assert(t.AlphaEquals(Lhs(w)) && w.NumHyps() == 0)
			}
		}()
		if abs := m(t); !abs.IsZero() {
			x, s := abs.Var(), abs.Body()
			name := x.Name()
			if !subscriptDashRe.MatchString(string(name)) {
				if subscriptNoDashRe.MatchString(string(name)) {
					// transform names like "x0" to "x_0"
					name = TermName(
						subscriptNoDashRe.ReplaceAllString(string(x.Name()), "${1}_$2"))
				} else {
					// transform names like "x" to "x_0"
					name = utils.Subscript(name, 0)
				}
				Assert(subscriptDashRe.MatchString(string(name)))
			}
			for s.HasName(name) && avoid(name) {
				name = utils.NextName(name)
			}
			if name != x.Name() {
				return BoundVarRewrite(x, core.Var(name, x.Type()))(t)
			}
		}
		return nil
	}
	return DeepRewrite(rewrite)
}

// Renames ∀ vars so they have number subscripts.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func SubscriptUnivVars(avoid TermNamePredicate) Rewrite {
	return subscriptVarsRewrite(MatchesFORALL, avoid)
}

// Renames ∃ vars so they have number subscripts.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func SubscriptExistsVars(avoid TermNamePredicate) Rewrite {
	return subscriptVarsRewrite(MatchesEXISTS, avoid)
}

// Adjusts the quantifier vars to avoid other names and remove primes as much as possible.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func adjustQuantifierVars(m ext.QuantifierMatcher, avoid TermNamePredicate) Rewrite {
	rewrite := func(t Term) (w *PropWrapper) {
		defer func() {
			if w != nil {
				Assert(t.AlphaEquals(Lhs(w)) && w.NumHyps() == 0)
			}
		}()

		if abs := m(t); !abs.IsZero() {
			x, s := abs.Var(), abs.Body()
			n := TermName(strings.TrimRight(string(x.Name()), utils.PrimeStr))
			if n != x.Name() || avoid(n) {
				for s.HasName(n) || avoid(n) {
					n = utils.NextName(n)
					if n == x.Name() {
						// some letter can only have prime as next letter,
						// which we cannot simplify.
						return nil
					}
				}
				return BoundVarRewrite(x, core.Var(n, x.Type()))(t)
			}
		}
		return nil
	}
	return DeepRewrite(rewrite)
}

// Adjusts the ∀ vars to avoid other names and remove primes as much as possible.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func AdjustUnivVars(avoid TermNamePredicate) Rewrite {
	return adjustQuantifierVars(MatchesFORALL, avoid)
}

// Adjusts the ∃ vars to avoid other names and remove primes as much as possible.
// avoid are names that to be avoided during renaming.
// Deep rewrite.
func AdjustExistsVars(avoid TermNamePredicate) Rewrite {
	return adjustQuantifierVars(MatchesEXISTS, avoid)
}

var BetaEtaRefl = EqualityFromRewrite(DeepBetaEta)
var NegRefl = EqualityFromRewrite(DeepNegRewrite)

// Given abs term s, replaces the abs vars in each level to avoid names
// appearing in term t, up to level i. Returns the new vars and the body at level i.
// For example, s is λx.λy.λz.P(x, y, z), if t = Q(x), i = 2,
// returns xʹ, y, and λz.P(xʹ, y, z).
func matchesAbsToAvoid(s, t Term, i int) ([]VarTerm, Term) {
	var vars []VarTerm
	for ; i > 0; i-- {
		abs, ok := s.AsAbsTerm()
		Assert(ok) // otherwise the input i is too large.
		n := abs.Var().Name()
		if t.HasName(n) {
			for t.HasName(n) || abs.Body().HasName(n) {
				n = utils.NextName(n)
			}
		}
		abs = abs.ChangeAbsVar(n)
		vars, s = append(vars, abs.Var()), abs.Body()
	}
	return vars, s
}

func makeQuantifierConst(c ConstTerm, t HolType) Term {
	return Const(c.Meta(), MakeFun(MakeFun(t, TypeBool), TypeBool))
}

var forallReorderHelper = quantifierReorderHelper(FORALL, ReorderForAll)
var existsReorderHelper = quantifierReorderHelper(EXISTS, ReorderExists)

func quantifierReorderHelper(
	c ConstTerm, reorder func(Term, Term) *PropWrapper) func(
	Term, *VarList, VarTerm, *PropWrapper) *PropWrapper {
	return func(t Term, vars *VarList, x VarTerm, w *PropWrapper) *PropWrapper {
		if vars.Size() == 1 {
			Assert(Lhs(w).AlphaEquals(t))
			return w
		}
		// Add the rest universal quantifiers to the Rhs of w.
		for _, v := range vars.Backward() {
			if x.Equals(v) {
				continue
			}
			w = w.
				Abs(v).
				LeftApply(makeQuantifierConst(c, v.Type())).
				RewriteConclRhs(BoolRewrite)
		}

		// If the denote var happens to be the most inside quantifier,
		// we don't need to reorder the universal quantifiers.
		if vars.Find(x) == vars.Size()-1 {
			return w
		}
		return reorder(t, Lhs(w)).EqTrans(w)
	}
}

// For a const term whose definition is one of:
//
//	(a) ⊢ c = εF.P(F)              — direct Hilbert (a basic definition)
//	(b) ⊢ c = (εF.P(F))(a1)...(aN) — applied Hilbert (a recursive definition,
//	                                  the generic recursion combinator)
//
// returns a thm  ∃F.P(F) ⊢ P′(c)  where P′(c) is P(εF.P(F)) with:
//
//   - first N ∀-binders ConclForAllInst'd with a1..aN (only in shape (b)),
//   - subterm occurrences of `(εF.P(F))(a1)...(aN)` rewritten to `c` via
//     `EqSym(def)`.
//
// Shape (a) is the N=0 special case: no ∀-binders consumed, and the
// rewrite replaces `εF.P(F)` directly. Result is  ∃F.P(F) ⊢ P(c)  —
// the original simple-case behavior.
//
// Shape (b) with one closed argument w: def=`c = (εF.∀_x.body)(w)`,
// args=[w]. After one ConclForAllInst(w) the conclusion contains
// `(εF.P(F))(w)` as a subterm (the partial application inside
// `F(_x, ...)` post-substitution), and EqSym(def) rewrites it to `c`,
// leaving c's characterizing equations.
//
// Beside the rewrite of c to its ε-term (the def-expand composite,
// whose tidy closes P(εF.P(F)) against a resident ∃F.P(F)), this bridge
// keeps c folded: its existence side is a theorem of its own (the
// recursion-existence obligation) and its P′(c) is the unfolded body
// as a hypothesis, c spelled as itself.
//
// Returns nil if c's def doesn't match either shape (e.g. plain
// `c = λx.body` ConstDef).
func ExistentialConstDef(c ConstTerm) Thm {
	def := c.DefThm()
	if def.IsZero() {
		return Thm{}
	}
	l, r, ok := MatchesEQ(def.Conclusion())
	if !ok || !l.Equals(c) {
		return Thm{}
	}

	// Walk down nested applications collecting args in application order
	// until we hit the innermost Hilbert (or fail).
	// IMPORTANT: check MatchesHilbert BEFORE the AppliedTerm peel, because
	// a Hilbert IS an AppliedTerm internally (ε(λx.body)) — peeling it
	// blindly would expose ε's λx.body as a spurious "arg".
	var args []Term
	cursor := r
	var abs core.AbsTerm
	for {
		if a := core.MatchesHilbert(cursor); !a.IsZero() {
			abs = a
			break
		}
		app, ok := cursor.(core.AppliedTerm)
		if !ok {
			return Thm{}
		}
		args = append([]Term{app.Arg()}, args...) // prepend → app order
		cursor = app.Fun()
	}

	// SelectExists: ∃F.P(F) ⊢ P(εF.P(F))
	w := SelectExists(abs)

	// One ConclForAllInst per arg, in application order. For the simple
	// direct-Hilbert case (N=0) this loop is empty.
	for _, arg := range args {
		w = w.ConclForAllInst(arg)
	}

	// Rewrite (εF.P(F))(args) → c via EqSym(def). For N>0, this finds
	// the partial-application subterm (εF.P(F))(args) introduced by
	// the post-Inst body and folds it back to c.
	return w.eqRewrite(core.EqSym(def)).AsThmCert()
}

// IsHilbertConstDef reports whether `c`'s definition has either the
// direct Hilbert shape `⊢ c = εF.P(F)` or the applied Hilbert shape
// `⊢ c = (εF.P(F))(args)` — i.e. whether ExistentialConstDef will
// succeed on `c`. The definition doors dispatch on it (the shape of a
// mint: a direct definition or a choice); the def-expand composite does
// not, since it opens a choice constant like any other definition.
//
// Returns false for constants without a DefThm and for shapes whose
// "head" after peeling applications isn't a Hilbert — a plain
// `c = λx.body` ConstDef, and a choice under a parameter,
// `c = λy. εx.P(x, y)`.
func IsHilbertConstDef(c ConstTerm) bool {
	def := c.DefThm()
	if def.IsZero() {
		return false
	}
	l, r, ok := MatchesEQ(def.Conclusion())
	if !ok || !l.Equals(c) {
		return false
	}
	// Mirror ExistentialConstDef's walk: peel applications down to the
	// head (checking Hilbert first at each level — see comment there).
	cursor := r
	for {
		if !core.MatchesHilbert(cursor).IsZero() {
			return true
		}
		app, ok := cursor.(core.AppliedTerm)
		if !ok {
			return false
		}
		cursor = app.Fun()
	}
}
