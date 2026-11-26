package serve

import (
	"fmt"

	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/tactic"
)

// InstallRecordNormal hands the instance normal form (prover/tactic,
// InstanceNormal) the corpus's record equations — every record's
// projection equations and the definitions a projection reads through
// (registry.RecordReductions). A proof reads each as it reads any
// library theorem. A caller that builds no proof (a session's step, a
// bundle's law) reads it here as a session cites any entry: the entry's
// promise in its stated form, unforced, so the theorem it derives is
// settled where that theorem is forced and nothing is built before.
// Idempotent.
func InstallRecordNormal() {
	equations, definitions, byName := recordEquations()
	tactic.InstallRecordNormal(equations, definitions, func(name string) *prop.PropWrapper {
		entry, ok := byName[name]
		if !ok {
			panic(fmt.Sprintf("InstallRecordNormal: %s is no record equation", name))
		}
		return fromEntryAsStated(entry)
	})
}

// recordEquations is the table InstallRecordNormal installs: the
// projection equations, the definitions a projection reads through, and
// each one's entry by its registered name.
func recordEquations() (equations, definitions []tactic.RecordEquation, byName map[string]*registry.ProofEntry) {
	projections, valued := registry.RecordReductions()
	byName = map[string]*registry.ProofEntry{}
	equations = make([]tactic.RecordEquation, 0, len(projections))
	for _, p := range projections {
		equations = append(equations, tactic.RecordEquation{
			Head:        p.Projection,
			Constructor: p.Constructor,
			Entry:       p.Entry.Name,
			Statement:   p.Entry.Statement().Prop,
		})
		byName[p.Entry.Name] = p.Entry
	}
	definitions = make([]tactic.RecordEquation, 0, len(valued))
	for _, e := range valued {
		definitions = append(definitions, tactic.RecordEquation{
			Head:      e.Defines()[0],
			Entry:     e.Name,
			Statement: e.Statement().Prop,
		})
		byName[e.Name] = e
	}
	return equations, definitions, byName
}
