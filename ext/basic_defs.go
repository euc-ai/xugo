/**
 * File: basic_defs.go
 *
 * This file contains the definitions of the basic logic and math operators.
 *
 * ⊤ := (λp.p = λp.p)
 * ⊥ := (λp.p = λp.⊤)
 * ¬p := p ⇔ ⊥
 * p ∧ q := λh.h(p, q) = λh.h(⊤, ⊤)
 * p ⇒ q := (p ∧ q) ⇔ p
 * cond p x y := εz.((p ⇒ (z = x)) ∧ (¬p ⇒ (z = y))) (if p then x else y)
 * ∀P := P = λx.⊤
 * ∃P := P(εP) (see note below)
 * ∃!P := ∃x.∀y.(P(y) ⇔ (x = y)) (see note below)
 * injective f := ∀x.∀y.((f(x) = f(y)) ⇒ (x = y))
 * surjective f := ∀z.∃x.(z = f(x))
 *
 * Notes:
 *
 * The definitions largely follow HOL Light, with minor modifications.
 * They were introduced by L. Henkin in "A theory of propositional types", 1963.
 * See also W. Farmer "The Seven Virtues of Simple Type Theory", 2006.
 * and J. Harrison "HOL Light: an overview", 2009.

 * There are 2 ways to define the disjunct operator OR.
 * 1. Define OR such that proof by cases works automatically,
 *    i.e. p ∨ q is defined such that we have p ⇒ r, q ⇒ r ⊢ r for any r.
 *    Under this definition, the law of excluded middle ⊢ p ∨ ¬p is not trivial.
 *    It can be proved using the axiom of choice, as shown by Diaconescu.
 * 2. Define OR by the opposite of AND, i.e. p ∨ q := ¬(¬p ∧ ¬q).
 *    Under this definition, ⊢ p ∨ ¬p can be trivially proved,
 *    however p ∨ q, p ⇒ r, q ⇒ r ⊢ r becomes non-trivial.
 * These 2 appoaches are eventually equivalent.
 * We use the first definition and prove the other as a thm.

 * There are 2 ways to define ∃ and ∃! respectively.
 * ∃P := P(εP)
 * ∃P := ¬(∀x.(¬P(x)))
 * ∃!P := ∃x.∀y.(P(y) ⇔ (x = y))
 * ∃!P := ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
 * For each case, the 2 definitions are equivalent.
 * We use the first definition and prove the other as a thm
 * for both of them.
 *
 * Everything here is a definition: the logic states no axiom. The one
 * statement the corpus assumes outright, the axiom of infinity, is the
 * postulate of the chapter that constructs the naturals
 * (library/proofs/nat_num/peano).
 */

package ext

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

var (
	T      = defT()
	F      = defF()
	NOT    = defNot()
	AND    = defAnd()
	OR     = defOr()
	IMPLY  = defImply()
	COND   = defCond()
	FORALL = defForAll()
	EXISTS = defExists()
	UNIQUE = defUnique()

	And = binaryOpsFoldl((*TermWrapper).And)
	Or  = binaryOpsFoldl((*TermWrapper).Or)

	MatchesAND   = MatchesBinaryOp(AND)
	MatchesOR    = MatchesBinaryOp(OR)
	MatchesIMPLY = MatchesBinaryOp(IMPLY)
	MatchesIFF   = MatchesBinaryOp(core.IFF())

	DecomposesAND = DecomposesBinaryOp(MatchesAND)
	DecomposesOR  = DecomposesBinaryOp(MatchesOR)

	MatchesFORALL, ForAll = matchesQuantifier(FORALL), quantifierOp(FORALL)
	MatchesEXISTS, Exists = matchesQuantifier(EXISTS), quantifierOp(EXISTS)
	MatchesUNIQUE         = matchesQuantifier(UNIQUE)
	DecomposesFORALL      = decomposesQuantifier(MatchesFORALL)
	DecomposesEXISTS      = decomposesQuantifier(MatchesEXISTS)
)

type (
	BinaryOp           = func(*TermWrapper, TermLike) *TermWrapper
	BinaryOpMatcher    = func(Term) (Term, Term, bool)
	UnaryOpMatcher     = func(Term) (Term, bool)
	BinaryOpDecomposer = func(Term) []Term
	QuantifierOp       = func(...Term) func(Term) *TermWrapper
	QuantifierMatcher  = func(Term) AbsTerm
)

const CondStr = "COND"

func InitConstMetaMap() *ConstMetaMap {
	var m utils.Map[core.TermName, core.ConstTermMeta]
	storeConsts := func(consts ...core.ConstTerm) {
		for _, c := range consts {
			m.LoadOrStore(c.Name(), c.Meta())
		}
	}
	storeConsts(
		T,
		F,
		NOT,
		AND,
		OR,
		IMPLY,
		COND,
		FORALL,
		EXISTS,
		UNIQUE,
	)
	return &m
}

// ⊤ := (λp.p = λp.p)
func defT() ConstTerm {
	p := initVars.p
	return core.NewConstDef(
		p.To(p).Eq(p.To(p)),
		utils.TrueStr)
}

// ⊥ := (λp.p = λp.⊤)
func defF() ConstTerm {
	p := initVars.p
	return core.NewConstDef(
		p.To(p).Eq(p.To(T)),
		utils.FalseStr)
}

// ¬ := λp.(p ⇔ ⊥)
func defNot() ConstTerm {
	p := initVars.p
	return core.NewConstDef(
		p.To(p.Eq(F)),
		utils.NegStr)
}

func Not(t Term) *TermWrapper {
	Assert(IsBool(t))
	return WrapTerm(NOT).Apply(t)
}

// ∧ := λp.λq.(λh.h(p, q) = λh.h(⊤, ⊤))
func defAnd() ConstTerm {
	p, q, h := initVars.p, initVars.q, initVars.h
	return core.NewConstDef(
		p.To(q.To(h.To(h.Apply(p, q)).Eq(h.To(h.Apply(T, T))))),
		utils.AndStr)
}

func (t *_ExprCore) And(s TermLike) *TermWrapper {
	Assert(IsBool(t) && IsBool(s.Core()))
	return WrapTerm(Apply(AND, t, s.Core()))
}

// ∨ := λp.λq.∀r.(((p ⇒ r) ∧ (q ⇒ r)) ⇒ r)
func defOr() ConstTerm {
	p, q, r := initVars.p, initVars.q, initVars.r
	return core.NewConstDef(
		p.To(q.To(ForAll(r)(p.Imply(r).And(q.Imply(r)).Imply(r)))),
		utils.OrStr)
}

func (t *_ExprCore) Or(s TermLike) *TermWrapper {
	Assert(IsBool(t) && IsBool(s.Core()))
	return WrapTerm(Apply(OR, t, s.Core()))
}

// ⇒ := λp.λq.((p ∧ q) ⇔ p)
func defImply() ConstTerm {
	p, q := initVars.p, initVars.q
	return core.NewConstDef(
		p.To(q.To((p.And(q)).Eq(p))),
		utils.ImplyStr)
}

func (t *_ExprCore) Imply(s TermLike) *TermWrapper {
	Assert(IsBool(t) && IsBool(s.Core()))
	return WrapTerm(Apply(IMPLY, t, s.Core()))
}

// COND := λp.λx.λy.εz.((p ⇒ (z = x)) ∧ (¬p ⇒ (z = y)))
func defCond() ConstTerm {
	p, x, y, z := initVars.p, initVars.x, initVars.y, initVars.z
	return core.NewConstDef(
		p.To(x.To(y.To(z.SuchThat(p.Imply(z.Eq(x)).And(Not(p).Imply(z.Eq(y))))))),
		CondStr)
}

// If p then x else y.
func Cond(p, x, y Term) *TermWrapper {
	Assert(IsBool(p) && x.Type().Equals(y.Type()))
	return Const(COND.Meta(),
		MakeFun(TypeBool, x.Type(), x.Type(), x.Type())).
		Apply(p, x, y)
}

// ∀ := λP.(P = λx.⊤)
func defForAll() ConstTerm {
	x, P := initVars.x, initVars.P
	return core.NewConstDef(
		P.To(P.Eq(x.To(T))),
		utils.ForAllStr)
}

// ∃ := λP.(P(εP))
func defExists() ConstTerm {
	P := initVars.P
	return core.NewConstDef(
		P.To(P.Apply(Const(core.MetaHilbert(), core.MetaHilbert().AbsType()).Apply(P))),
		utils.ExistsStr)
}

// ∃! := λP.∃x.∀y.(P(y) ⇔ (x = y))
func defUnique() ConstTerm {
	x, y, P := initVars.x, initVars.y, initVars.P
	return core.NewConstDef(
		P.To(Exists(x)(ForAll(y)(P.Apply(y).Eq(x.Eq(y))))),
		utils.UniqueStr)
}

// returns a matcher that tells whether a term has form ¬x.
func MatchesNOT(t Term) Term {
	if t, ok := t.AsAppliedTerm(); ok && t.Fun().Equals(NOT) {
		return t.Arg()
	}
	return nil
}

// Connects terms using binary logic connectors.
func binaryOpsFoldl(m BinaryOp) func(...Term) *TermWrapper {
	return func(list ...Term) *TermWrapper {
		acc := WrapTerm(list[0])
		for _, t := range list[1:] {
			acc = m(acc, t)
		}
		return acc
	}
}

// Given a binary func const, e.g. ∧,
// returns a matcher that tells whether a term has form x ∧ y.
func MatchesBinaryOp(c ConstTerm) BinaryOpMatcher {
	return func(t Term) (Term, Term, bool) {
		if t, ok := t.AsAppliedTerm(); ok {
			if s, ok := t.Fun().AsAppliedTerm(); ok {
				if _, ok := s.Fun().AsConst(); ok {
					if s.Fun().Equals(c) {
						return s.Arg(), t.Arg(), true
					}
				}
			}
		}
		return nil, nil, false
	}
}

// MatchesUnaryOp returns a matcher for the unary application `c(x)`, yielding
// (x, true) when t = c(x). The unary analogue of MatchesBinaryOp and the
// declarative form of the hand-written `AsAppliedTerm + Fun().Equals(c)` shape
// (cf. MatchesNOT).
func MatchesUnaryOp(c ConstTerm) UnaryOpMatcher {
	return func(t Term) (Term, bool) {
		if t, ok := t.AsAppliedTerm(); ok && t.Fun().Equals(c) {
			return t.Arg(), true
		}
		return nil, false
	}
}

// Decomposes a term like p ∧ q ∧ r ∧ ... to {p, q, r, ...},
// returns a boolean telling whether the decomposition works.
func DecomposesBinaryOp(m BinaryOpMatcher) (decompose BinaryOpDecomposer) {
	return func(t Term) []Term {
		if l, r, ok := m(t); ok {
			return append(decompose(l), decompose(r)...)
		} else {
			return []Term{t.Core()}
		}
	}
}

func MatchesCond(t Term) (Term, Term, Term, bool) {
	if t, ok := t.AsAppliedTerm(); ok {
		f, args := MatchesApply(t)
		if f, ok := f.AsConst(); ok {
			if f.Meta().Equals(COND.Meta()) && len(args) == 3 {
				return args[0], args[1], args[2], true
			}
		}
	}
	return nil, nil, nil, false
}

// Wraps quantifier const (∀ / ∃) to a function.
func quantifierOp(quantifier ConstTerm) QuantifierOp {
	return func(vars ...Term) func(Term) *TermWrapper {
		return func(s Term) *TermWrapper {
			Assert(IsBool(s))
			for _, v := range slices.Backward(vars) {
				v, ok := v.AsVar()
				Assert(ok)
				abs := Abs(v, s)
				s = Const(quantifier.Meta(), MakeFun(abs.Type(), TypeBool)).Apply(abs)
			}
			return WrapTerm(s)
		}
	}
}

// Wraps ∃! to a function.
// ∃! does not take multiple bound variables because it would be ambiguous.
func Unique(v Term) func(Term) *TermWrapper {
	return func(s Term) *TermWrapper {
		v, ok := v.AsVar()
		Assert(ok && IsBool(s))
		abs := Abs(v, s)
		return Const(UNIQUE.Meta(), MakeFun(abs.Type(), TypeBool)).Apply(abs)
	}
}

// Given a Quantifier const, (∀ / ∃ / ∃!),
// returns a matcher that tells whether a term has form ∀x.P or ∃x.P or ∃!x.P.
func matchesQuantifier(quantifier ConstTerm) QuantifierMatcher {
	return func(t Term) AbsTerm {
		if t, ok := t.AsAppliedTerm(); ok {
			if tFun, ok := t.Fun().AsConst(); ok &&
				quantifier.Meta().Equals(tFun.Meta()) {
				if abs, ok := t.Arg().AsAbsTerm(); ok {
					return abs
				}
			}
		}
		return AbsTerm{}
	}
}

// Decomposes a term like ∀x.∀y....t to {x, y, ...} and term t,
// returns a var set (can be nil if no quantifiers) and the body term.
// Shadowed binders are renamed without capture so every binder stays in the list.
func decomposesQuantifier(m QuantifierMatcher) func(Term) (VarList, Term) {
	return func(t Term) (VarList, Term) {
		vars := VarList{}
		for abs := m(t); !abs.IsZero(); abs = m(t) {
			if vars.Has(abs.Var()) {
				avoid := make([]Term, 0, vars.Size()+1)
				avoid = append(avoid, abs.Body())
				for v := range vars.Iter() {
					avoid = append(avoid, v)
				}
				fresh := core.Var(abs.Var().Name(), abs.Var().Type()).RenameToAvoid(avoid...)
				abs = abs.ChangeAbsVar(fresh.Name())
			}
			vars.Add(abs.Var())
			t = abs.Body()
		}
		return vars, t
	}
}

// MetaTypeProd represents prod type constructor.
var MetaTypeProd = core.MakeMetaType(TermName("prod"), 2)
var CommaConstMeta = core.MakeConstMeta(
	TermName(","),
	MakeFun(TypeA, MakeFun(TypeB, MakeProdType(TypeA, TypeB))))

// MakeProdType constructs a product type prod(left, right).
func MakeProdType(left, right HolType) HolType {
	return core.MakeCompositeType(MetaTypeProd, left, right)
}
