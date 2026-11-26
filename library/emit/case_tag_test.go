package emit

import (
	"regexp"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestEmit_ByCaseBranchTagsFollowTheTerm: a ByCaseStep on ¬t gives
// child 0 the hypothesis t and child 1 the hypothesis ¬t
// (proof.ByCaseBranch); the rendered tags say on which branch the CASE
// TERM holds, so child 0 is tagged `false` and child 1 `true`, while a
// split on t keeps `true` on child 0.
func TestEmit_ByCaseBranchTagsFollowTheTerm(t *testing.T) {
	env := makeTestEnv(t)
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	q := Q.Apply(x).Core()
	for _, tc := range []struct {
		name string
		term core.Term
		tags [2]string // the tags of child 0 and child 1
	}{
		{"plain", q, [2]string{"true", "false"}},
		{"negated", ext.Not(q).Core(), [2]string{"false", "true"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			goal := prop.MakeProp(P.Apply(x).Core())
			yes := prop.MakeProp(P.Apply(x).Core(), q)
			no := prop.MakeProp(P.Apply(x).Core(), ext.Not(q))
			pb := ext.NewPoolBuilder()
			steps := []*proof.StepProto{
				{
					Goal:     pb.PropRef(goal),
					SubGoals: []*ext.HolPropProto{pb.PropRef(yes), pb.PropRef(no)},
					Step:     &proof.StepProto_ByCase{ByCase: pb.TermRef(tc.term)},
				},
				{Goal: pb.PropRef(yes), Step: &proof.StepProto_TrivialSimplify{}},
				{Goal: pb.PropRef(no), Step: &proof.StepProto_CnfRefute{}},
			}
			src := emitMember(t, env, EmitOptions{FuncName: "Build_ByCaseTags"}, detailed(pb, steps...)).Source
			at := func(tag string) int {
				if loc := regexp.MustCompile(`Case\(\s*"` + regexp.QuoteMeta(tag+": ")).FindStringIndex(src); loc != nil {
					return loc[0]
				}
				return -1
			}
			first, second := at(tc.tags[0]), at(tc.tags[1])
			require.NotEqual(t, -1, first, "no %s branch:\n%s", tc.tags[0], src)
			require.NotEqual(t, -1, second, "no %s branch:\n%s", tc.tags[1], src)
			assert.Less(t, first, second, "child 0 is not tagged %s:\n%s", tc.tags[0], src)
		})
	}
}
