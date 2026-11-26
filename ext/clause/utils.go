package clause

import (
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

type (
	Term             = core.Term
	VarTerm          = core.VarTerm
	ConstTerm        = core.ConstTerm
	AppliedTerm      = core.AppliedTerm
	AbsTerm          = core.AbsTerm
	TermName         = core.TermName
	TermSubst        = core.TermSubst
	Prop             = core.Prop
	Thm              = core.ThmCert
	VarTypePredicate = core.VarTypePredicate
	VarPredicate     = core.VarPredicate
	TermSubstsGroup  = ext.TermSubstsGroup
	VarList          = ext.VarList
	PropWrapper      = prop.PropWrapper
)

var (
	Assert           = utils.Assert
	TypeA            = core.TypeA()
	TypeB            = ext.TypeB
	TypeBool         = core.TypeBool()
	MakeFun          = core.MakeFun
	IsBool           = core.IsBool
	MakeTypeSubst    = core.MakeTypeSubst
	Abs              = core.Abs
	Eq               = core.Eq
	MatchesEQ        = core.MatchesEQ
	WrapTerm         = ext.WrapTerm
	Var              = ext.Var
	Const            = ext.Const
	Apply            = ext.Apply
	F                = ext.F
	T                = ext.T
	AND              = ext.AND
	OR               = ext.OR
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

	MakeProp     = prop.MakeProp
	WrapProp     = prop.WrapProp
	IsStronger   = prop.IsStronger
	Lhs          = prop.Lhs
	Rhs          = prop.Rhs
	BasicRewrite = prop.BasicRewrite
	UnifyTerms   = unify.UnifyTerms

	decomposeANDlen = ext.DecomposeLenBinaryOp(MatchesAND)
)

const (
	_CNF_SIZE_THRES      = 64
	_CNF_REWRITE_TIMEOUT = 500 * time.Millisecond

	_DISJUNCTIVE_TERM_PREFIX = "disj_"
)

func disjunctiveComponentSize(s Term) int {
	_, body := DecomposesFORALL(s)
	return utils.Foldl(func(acc int, t Term) int {
		return acc + t.Size()
	}, 0, DecomposesOR(body))
}

func simplifyConclusion(thm *PropWrapper) (*PropWrapper, *Clause) {
	c := MakeClause(thm.Conclusion())
	if c.equivalentClause != nil {
		thm = WrapProp(c.simplificationThm).EqMP(thm)
		Assert(c.equivalentClause.Term().AlphaEquals(thm.Conclusion()))
		c = c.equivalentClause
	}
	return thm, c
}

type _EqRewriteType int

const (
	rewriteUnknown _EqRewriteType = iota
	rewriteEqLeft
	rewriteEqRight
	rewriteNeg
	rewriteWhole
)

// Given a theorem whose conclusion is not necessarily an equality,
// transform it to an equality so it can be used to EqRewrite.
// The way to transform is determined by the rewriteType.
// If rewriteType is unknown, we do the best effort.
func flexibleEq(eq *PropWrapper, rewriteType _EqRewriteType) *PropWrapper {
	var choosenType _EqRewriteType
	if rewriteType != rewriteUnknown {
		choosenType = rewriteType
	} else { // best effort.
		if l, r, ok := MatchesEQ(eq.Conclusion()); ok {
			if l.Size() >= r.Size() {
				choosenType = rewriteEqLeft
			} else {
				choosenType = rewriteEqRight
			}
		} else if ne := MatchesNOT(eq.Conclusion()); ne != nil {
			choosenType = rewriteNeg
		} else {
			choosenType = rewriteWhole
		}
	}
	switch choosenType {
	case rewriteEqLeft:
		_, _, ok := MatchesEQ(eq.Conclusion())
		Assert(ok)
		return eq
	case rewriteEqRight:
		_, _, ok := MatchesEQ(eq.Conclusion())
		Assert(ok)
		return eq.EqSym()
	case rewriteNeg:
		ne := MatchesNOT(eq.Conclusion())
		Assert(ne != nil)
		// make ¬t to t = ⊥
		return prop.EqualsFalse(ne).EqSym().EqMP(eq)
	case rewriteWhole:
		// make it t = ⊤
		return eq.Deduct(prop.DerivesTrue)
	default:
		panic("unknown rewrite type")
	}
}

// This works inside the universal quantifiers.
var ClauseDeduceFinalize = prop.ChainRewrites(
	BasicRewrite,
	prop.SimplifyDisjunct,
	prop.AssocORRewrite,
	univHilbertRewrite,
)
