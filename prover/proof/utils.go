package proof

import (
	"fmt"
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// The package's reading vocabulary: the kernel and prop-layer names
// this package writes often enough that the qualifier is noise rather
// than information (ext/utils.go re-exports core the same way). An
// alias never renames — the bare form is the original spelling, so a
// reader who knows `core.VarTerm` recognizes `VarTerm` on sight.
//
// Deliberately NOT aliased, because the bare name would be ambiguous
// here: MakeProp and Assume are DIFFERENT functions in core and prop
// (kernel Prop/ThmCert vs. *PropWrapper), and Refl is this package's
// own tactic step (script.go), not core.Refl. Those stay qualified.
type (
	Term          = core.Term
	TermLike      = ext.TermLike
	VarTerm       = core.VarTerm
	ConstTerm     = core.ConstTerm
	ConstTermMeta = core.ConstTermMeta
	TermName      = core.TermName
	TermSubst     = core.TermSubst
	HolType       = core.HolType
	VarType       = core.VarType
	CompositeType = core.CompositeType
	TypeName      = core.TypeName
	Prop          = core.Prop
	Thm           = core.Thm
	ThmCert       = core.ThmCert
	PropWrapper   = prop.PropWrapper
	SubGoals      = tactic.SubGoals
)

var (
	Assert   = utils.Assert
	TypeA    = core.TypeA()
	TypeB    = ext.TypeB
	TypeBool = core.TypeBool()
	NumType  = ext.NumType

	MakeFun           = core.MakeFun
	MakeVarType       = core.MakeVarType[string]
	MakeMetaType      = core.MakeMetaType[TypeName]
	MakeCompositeType = core.MakeCompositeType
	MakeProdType      = ext.MakeProdType
	MakeConstTerm     = core.MakeConstTerm
	MakeConstMeta     = core.MakeConstMeta[TermName]
	MakeTermSubst     = core.MakeTermSubst
	FormatType        = ext.FormatType

	// Term builders — the surface every statement in this package is
	// spelled in.
	F, T   = ext.F, ext.T
	Var    = ext.Var
	Abs    = core.Abs
	Apply  = ext.Apply
	Not    = ext.Not
	Cond   = ext.Cond
	ForAll = ext.ForAll
	Exists = ext.Exists
	Unique = ext.Unique

	// Shape probes — the readers that take a term apart again. The
	// whole family is aliased together: a half-aliased family reads
	// worse than either extreme, because the qualifier stops carrying
	// information and starts looking like a distinction.
	MatchesEQ          = core.MatchesEQ
	MatchesApply       = ext.MatchesApply
	MatchesFun         = ext.MatchesFun
	MatchesCond        = ext.MatchesCond
	MatchesNOT         = ext.MatchesNOT
	MatchesAND         = ext.MatchesAND
	MatchesIMPLY       = ext.MatchesIMPLY
	MatchesFORALL      = ext.MatchesFORALL
	MatchesEXISTS      = ext.MatchesEXISTS
	MatchesBinaryOp    = ext.MatchesBinaryOp
	DecomposesAND      = ext.DecomposesAND
	DecomposesFORALL   = ext.DecomposesFORALL
	DecomposesEXISTS   = ext.DecomposesEXISTS
	DecomposesBinaryOp = ext.DecomposesBinaryOp

	WrapTerm  = ext.WrapTerm
	WrapProp  = prop.WrapProp
	PrintTerm = ext.PrintTerm
	PrintProp = prop.PrintProp

	IsStronger        = prop.IsStronger
	Normalize         = prop.Normalize
	BridgeNormalize   = prop.BridgeNormalize
	DeepBeta          = prop.DeepBeta
	DeepBetaAbs       = prop.DeepBetaAbs
	EqRewrite         = prop.EqRewrite
	ConclANDRecursive = prop.ConclANDRecursive
	HypAND0           = prop.HypAND0
	HypAND1           = prop.HypAND1
	Lhs               = prop.Lhs
	Rhs               = prop.Rhs
)

const (
	_DENOTE_SIZE_THRES             = 8
	_STRONGER_GOALS_HYP_DIFF_THRES = 2
)

// Find stronger goals (including the original goal itself)
// whose num of hyps is no less than the num of hyps of the original goal minus _STRONGER_GOALS_HYP_DIFF_THRES.
// The larger the threshold is, the more stronger goals we have (the number of which is exponential).
func StrongerGoals(goal Prop) []Prop {
	var goals []Prop
	for _, s := range utils.SubIndices(goal.NumHyps(), goal.NumHyps()-_STRONGER_GOALS_HYP_DIFF_THRES) {
		if goal.Conclusion().Equals(F) && len(s) == 0 {
			continue
		}
		hyps := make([]Term, len(s))
		for j := range s {
			hyps[j] = goal.Hyp(s[j])
		}
		goals = append(goals, prop.MakeProp(goal.Conclusion(), hyps...))

		if !goal.Conclusion().Equals(F) && len(s) != 0 {
			goals = append(goals, prop.MakeProp(F, hyps...))
		}
	}
	return goals
}

// Equal is the equation l = r as a term, over any two term-like values
// — a typed wrapper beside a core term, or two of either; the typed
// wrapper yields its term and the phantoms are not compared.
func Equal(l, r TermLike) *ext.TermWrapper { return ext.WrapTerm(core.Eq(l.Core(), r.Core())) }

// Lambda is the abstraction λv. body as a term, over any two term-like
// values: the binder is a typed or untyped variable, the body whatever
// term the Go-built application of typed handles produced.
func Lambda(v, body TermLike) *ext.TermWrapper {
	x, ok := v.Core().(core.VarTerm)
	if !ok {
		panic(fmt.Sprintf("Lambda: the binder must be a variable, not %s", ext.PrintTerm(v)))
	}
	return ext.WrapTerm(core.Abs(x, body.Core()))
}
