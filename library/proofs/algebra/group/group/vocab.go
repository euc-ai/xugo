// vocab.go — the group's record type on the typed term surface.

package group

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// GroupOps holds a group's product, identity, inverse and carrier.
type GroupOps[Element ext.TypePhantom] struct{}

func (GroupOps[Element]) Reify() ext.HolType {
	return MakeType(
		"group_ops", ext.HolTypeOf[Element]())
}
