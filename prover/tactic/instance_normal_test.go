package tactic

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// readCountedStatement is an equation's statement that counts the reads
// of its conclusion: the work the normal form does at the equations.
type readCountedStatement struct {
	core.Prop
	reads *int
}

func (s readCountedStatement) Conclusion() core.Term {
	*s.reads++
	return s.Prop.Conclusion()
}

// TestInstanceNormal_ProjectionComputesOnlyItsPart: a projection of a
// record value a definition builds computes the part it selects and
// none of the parts it drops. zz_dk(x) packs two projections of
// zz_d(k-1)(x), so computing every part of zz_dk(x) costs twice what
// every part of zz_d(k-1)(x) costs; its first part is
// zz_p1(zz_d(k-1)(x)) alone, so zz_p1(zz_dk(x)) costs one level more
// than zz_p1(zz_d(k-1)(x)), the same amount at every depth.
func TestInstanceNormal_ProjectionComputesOnlyItsPart(t *testing.T) {
	elem := core.TypeBool()
	rec := core.MakeFun(elem, elem)
	constant := func(name string, ty core.HolType) *ext.TermWrapper {
		return ext.Const(core.MakeConstMeta(name, ty), ty)
	}
	mk := constant("zz_mk", core.MakeFun(elem, elem, rec))
	p1 := constant("zz_p1", core.MakeFun(rec, elem))
	p2 := constant("zz_p2", core.MakeFun(rec, elem))
	a, b, x := ext.Var("a", elem), ext.Var("b", elem), ext.Var("x", elem)

	reads := 0
	counted := func(statement *ext.TermWrapper) core.Prop {
		return readCountedStatement{core.MakeProp(statement.Core()), &reads}
	}
	projections := []RecordEquation{
		{Head: "zz_p1", Constructor: "zz_mk", Entry: "zz.P1", Statement: counted(ext.ForAll(a, b)(p1.Apply(mk.Apply(a, b)).Eq(a)))},
		{Head: "zz_p2", Constructor: "zz_mk", Entry: "zz.P2", Statement: counted(ext.ForAll(a, b)(p2.Apply(mk.Apply(a, b)).Eq(b)))},
	}
	const depth = 12
	defs := make([]*ext.TermWrapper, depth+1)
	var valued []RecordEquation
	for k := range depth + 1 {
		name := fmt.Sprintf("zz_d%d", k)
		defs[k] = constant(name, core.MakeFun(elem, rec))
		value := mk.Apply(x, x)
		if k > 0 {
			value = mk.Apply(p1.Apply(defs[k-1].Apply(x)), p2.Apply(defs[k-1].Apply(x)))
		}
		valued = append(valued, RecordEquation{Head: name, Entry: "zz." + name, Statement: counted(ext.ForAll(x)(defs[k].Apply(x).Eq(value)))})
	}
	normal := NewRecordTermNormalizer(projections, valued)

	cost := make([]int, depth+1)
	for k := range depth + 1 {
		reads = 0
		require.True(t, normal(p1.Apply(defs[k].Apply(x)).Core()).Equals(x.Core()), "zz_p1(zz_d%d(x)) is x", k)
		cost[k] = reads
	}
	for k := 1; k <= depth; k++ {
		require.Equal(t, cost[1]-cost[0], cost[k]-cost[k-1], "the cost at each depth: %v", cost)
	}
}
