package registry

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/tactic"
)

// RecordProjection is one projection equation of a record, `p(C(x̄)) =
// xᵢ`: the entry the record door registered it under, the projection p
// and the record's constructor C.
type RecordProjection struct {
	Entry       *ProofEntry
	Projection  string
	Constructor string
}

// RecordTermNormalizer computes record projections from their registered
// statements without installing a proof environment or reading theorems.
// It is used where vocabulary and generated types compare record fields.
func RecordTermNormalizer() func(core.Term) core.Term {
	projections, valued := RecordReductions()
	equations := make([]tactic.RecordEquation, 0, len(projections))
	definitions := make([]tactic.RecordEquation, 0, len(valued))
	for _, p := range projections {
		equations = append(equations, tactic.RecordEquation{Head: p.Projection, Constructor: p.Constructor, Entry: p.Entry.Name, Statement: p.Entry.Statement().Prop})
	}
	for _, e := range valued {
		definitions = append(definitions, tactic.RecordEquation{Head: e.Defines()[0], Entry: e.Name, Statement: e.Statement().Prop})
	}
	return tactic.NewRecordTermNormalizer(equations, definitions)
}

// RecordReductions lists the equations the instance normal form
// computes with (prover/tactic, InstanceNormal), in registration order:
// every record's projection equations (DataEntry.Fields), and every
// definition whose value is a structure — its one equation `∀ā. D(ā) =
// rhs` with rhs a structure record's constructor applied, or a
// definition already listed applied (`tor_module`, whose right side is
// `homology_module` applied).
//
// A structure record is a record over type parameters (`ring_ops(A)`):
// a value of it is a structure on its carrier types, and a projection
// of one picks a part out. A record without a type parameter is a type
// of elements (`complex`): a definition into it is arithmetic on those
// elements (`complex_mul`), and none is listed: the parts of `z * w`
// are a law of the record's chapter, cited where a proof wants them.
// The projection equations of such a record are listed like every
// record's, so `re(complex(a, b))` is `a`.
func RecordReductions() (projections []RecordProjection, valued []*ProofEntry) {
	recordOf := map[*ProofEntry]*DatatypeEntries{}
	for _, de := range datatypeByName {
		for _, f := range de.Fields {
			recordOf[f] = de
		}
	}
	values := map[string]bool{}
	for _, e := range all {
		de, isField := recordOf[e]
		if !isField {
			continue
		}
		projection, constructor, ok := projectionEquation(e)
		if !ok {
			panic("registry.RecordReductions: " + e.Name + " is no projection equation `p(C(x̄)) = xᵢ`")
		}
		projections = append(projections, RecordProjection{Entry: e, Projection: projection, Constructor: constructor})
		if len(de.md.Def.Params) > 0 {
			values[constructor] = true
		}
	}
	for _, e := range all {
		if recordOf[e] != nil || len(e.defines) != 1 || e.ServedAsAxiom() {
			continue
		}
		head, _, rhs, ok := equationSides(e)
		if !ok || head != e.defines[0] {
			continue
		}
		valueHead, _ := ext.MatchesApply(rhs)
		if c, isConst := valueHead.AsConst(); isConst && values[string(c.Name())] {
			valued = append(valued, e)
			values[head] = true
		}
	}
	return projections, valued
}

// projectionEquation reads a projection equation `∀x̄. p(C(x̄)) = xᵢ`.
func projectionEquation(e *ProofEntry) (projection, constructor string, ok bool) {
	head, args, _, ok := equationSides(e)
	if !ok || len(args) != 1 {
		return "", "", false
	}
	inner, _ := ext.MatchesApply(args[0])
	c, isConst := inner.AsConst()
	if !isConst {
		return "", "", false
	}
	return head, string(c.Name()), true
}

// equationSides reads an entry's statement `∀x̄. h(args) = rhs`: h's
// name, its arguments and the right side.
func equationSides(e *ProofEntry) (head string, args []core.Term, rhs core.Term, ok bool) {
	t := e.Statement().Prop.Conclusion()
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		t = abs.Body()
	}
	lhs, r, isEq := core.MatchesEQ(t)
	if !isEq {
		return "", nil, nil, false
	}
	h, a := ext.MatchesApply(lhs)
	c, isConst := h.AsConst()
	if !isConst {
		return "", nil, nil, false
	}
	return string(c.Name()), a, r, true
}
