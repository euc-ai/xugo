package tactic

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

type (
	Term            = core.Term
	VarTerm         = core.VarTerm
	ConstTerm       = core.ConstTerm
	AppliedTerm     = core.AppliedTerm
	AbsTerm         = core.AbsTerm
	TermName        = core.TermName
	TermSubst       = core.TermSubst
	Prop            = core.Prop
	PropKey         = core.PropKey
	Thm             = core.ThmCert
	PropWrapper     = prop.PropWrapper
	TermSubstsGroup = ext.TermSubstsGroup
	SubstsTuple     = unify.SubstsTuple
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
	MakeProp      = prop.MakeProp
	WrapProp      = prop.WrapProp
	IsStronger    = prop.IsStronger
	F             = ext.F
	T             = ext.T
	Not           = ext.Not
	And           = ext.And
	Or            = ext.Or
	ForAll        = ext.ForAll
	Exists        = ext.Exists
	Unique        = ext.Unique
	Rhs           = prop.Rhs
)

// Given prop s whose conclusion is ⊥, weaken the conclusion to t.
func weakenConcl(s Prop, t Term) *PropWrapper {
	_s := WrapProp(s)
	if s.Conclusion().Equals(F) && !t.Equals(F) {
		_s = _s.DeriveTrans(prop.FalseDerives(t))
	}
	return _s
}

// The hyps of a given prop except the i-th.
// It is the caller's responsibility to ensure bounds check.
func restHyps(p Prop, i int) []Term {
	Assert(i < p.NumHyps())
	hyps := make([]Term, 0, p.NumHyps()-1)
	for j := range p.NumHyps() {
		if j != i {
			hyps = append(hyps, p.Hyp(j))
		}
	}
	return hyps
}

func IsTrivial(p Prop) bool {
	w := TrivialSimplifyTactic(p)
	return w != nil && w.childrenGoals == nil
}

// normalizedTermKey computes a normalized prop-level key for a term by
// wrapping it as a hypothesis-free prop, normalizing via prop.Normalize,
// and taking the alpha key.
//
// Two terms whose only difference is in representation (⇒ vs ¬∨, ⇔
// orientation aside, NNF, prenex scope, disjunct/conjunct ordering,
// bound-variable names) collapse to the same key. The lemma layer can
// use this for applicability decisions without disturbing the original
// raw witness used for proof construction.
//
// Strictly a matcher-side helper: never feed a normalized term back into
// rewrite/eq construction — those still need the original equality/iff
// witness.
func normalizedTermKey(t Term) PropKey {
	n, _ := prop.Normalize(MakeProp(t))
	return n.AlphaKey()
}

// normalizedHypKeys computes the normalized comparison-key set for p's
// hypotheses. Callers should build this lazily after raw α-equality misses,
// because prop.Normalize is much more expensive than HasHyp.
func normalizedHypKeys(p Prop) map[PropKey]struct{} {
	keys := make(map[PropKey]struct{}, p.NumHyps())
	for h := range p.HypIter() {
		keys[normalizedTermKey(h)] = struct{}{}
	}
	return keys
}

// hasNormalizedHypKey reports whether keys contains t's normalized
// comparison key.
//
// Used by matcher applicability gates only — proof construction must
// continue to use the original raw witness.
func hasNormalizedHypKey(keys map[PropKey]struct{}, t Term) bool {
	_, ok := keys[normalizedTermKey(t)]
	return ok
}
