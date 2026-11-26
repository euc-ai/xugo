package sobolev_section

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// SobolevLocalization packs the active chart count, charts and partition functions.
type SobolevLocalization[Point ext.TypePhantom] struct{}

func (SobolevLocalization[Point]) Reify() ext.HolType {
	return MakeType("sobolev_localization", ext.HolTypeOf[Point]())
}
