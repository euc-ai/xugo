package ext

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestDecomposesQuantifierShadowedBinder(t *testing.T) {
	for _, tc := range []struct {
		name      string
		quantify  QuantifierOp
		decompose func(Term) (VarList, Term)
		binders   int
	}{
		{"forall", ForAll, DecomposesFORALL, 2},
		{"exists", Exists, DecomposesEXISTS, 2},
		{"forall_unused_prior", ForAll, DecomposesFORALL, 3},
		{"exists_unused_prior", Exists, DecomposesEXISTS, 3},
	} {
		t.Run(tc.name, func(t *testing.T) {
			x := core.Var("x", core.TypeBool())
			free := x.Rename()
			term := tc.quantify(x)(tc.quantify(x)(WrapTerm(x).Eq(free))).Core()
			prior := free
			if tc.binders == 3 {
				free = prior.Rename()
				term = tc.quantify(x)(tc.quantify(prior)(tc.quantify(x)(WrapTerm(x).Eq(free)))).Core()
			}
			var vars VarList
			var body Term
			require.NotPanics(t, func() {
				vars, body = tc.decompose(term)
			})
			require.Equal(t, tc.binders, vars.Size())
			for i := 0; i < vars.Size(); i++ {
				for j := i + 1; j < vars.Size(); j++ {
					assert.False(t, vars.Ind(i).EqualsVar(vars.Ind(j)))
				}
				assert.Equal(t, i == vars.Size()-1, body.HasFree(vars.Ind(i)))
			}
			assert.True(t, body.HasFree(free))
			assert.True(t, vars.Ind(0).EqualsVar(x))
			if tc.binders == 3 {
				assert.True(t, vars.Ind(1).EqualsVar(prior))
			}
			rebuilt := body
			for _, v := range vars.Backward() {
				rebuilt = tc.quantify(v)(rebuilt).Core()
			}
			assert.True(t, rebuilt.AlphaEquals(term))
		})
	}
}
