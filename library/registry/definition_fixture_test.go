package registry

import "github.com/euc-ai/xugo/core"

// mintedByName is a constant a test's definition door minted, read as
// the definition proof.Unfold takes; it is read when the proof opens it.
type mintedByName string

func (name mintedByName) DefinedConstant() core.ConstTermMeta {
	return mintedConstant("the test", string(name))
}
