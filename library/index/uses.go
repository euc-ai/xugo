package index

// The uses relation: the members whose statement stands on a definition
// they do not depend on.
//
// A member's dependencies are the entries its proof reads and the
// definitions it opens (Member.Deps), and the dependency graph is those
// edges. A definition is also stood on where a statement spells its
// constant, which reads no entry and opens nothing: a theorem about a
// constant needs the constant to be stated, and its proof may never
// touch the definition. That is no dependency, so a definition can
// show no dependent and still be used. Whether a definition may be
// deleted, moved or restated is asked of both relations: Dependents and
// UsedBy.

import (
	"slices"
	"sort"
)

// Use is a member whose statement spells constants of a definition it
// does not depend on: Statement are those constants.
type Use struct {
	Member    string   `json:"member"`
	Statement []string `json:"statement,omitempty"`
}

// UsedBy lists the members whose statement spells a constant m mints
// and that do not depend on m, in id order: nil for a member that mints
// no constant. A member that cites m or opens a constant of it is among
// m's Dependents and is left out here, whatever its statement spells.
func (c *Corpus) UsedBy(m *Member) []Use {
	var minted []string
	for _, d := range c.Definitions {
		if d.Member == m.ID {
			minted = append(minted, d.Const)
		}
	}
	if len(minted) == 0 {
		return nil
	}
	var uses []Use
	for _, x := range c.Members {
		if x == m || slices.Contains(m.Dependents, x.ID) {
			continue
		}
		var spelled []string
		for _, name := range minted {
			if slices.Contains(x.Constants, name) {
				spelled = append(spelled, name)
			}
		}
		if len(spelled) > 0 {
			uses = append(uses, Use{Member: x.ID, Statement: spelled})
		}
	}
	sort.Slice(uses, func(i, j int) bool { return uses[i].Member < uses[j].Member })
	return uses
}
