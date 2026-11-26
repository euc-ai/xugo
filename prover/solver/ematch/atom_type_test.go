package ematch

import "github.com/euc-ai/xugo/core"

// TypeInd is an atomic type for this package's tests, spelled `ind`:
// any nullary type other than bool serves. The corpus's `ind` is the
// type the axiom of infinity introduces (library/proofs/nat_num/peano),
// and nothing below the chapters knows it.
var TypeInd = core.MakeCompositeType(core.MakeMetaType("ind", 0))
