package proof

import "github.com/euc-ai/xugo/core"

// mintedDefinition is the definition of a constant a test mints: the
// mint runs when the proof opens the constant.
type mintedDefinition func() core.ConstTerm

func (mint mintedDefinition) DefinedConstant() core.ConstTermMeta { return mint().Meta() }
