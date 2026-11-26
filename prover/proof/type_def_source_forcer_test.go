package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

func TestTypeDefSourceUsesBuilderForcer(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	statement := core.MakeProp(core.Apply(core.Abs(x, core.Eq(x, x)), x))
	source := core.Promise(statement, func(core.Forcer) core.ThmCert {
		panic("the source must be settled at the caller's trust boundary")
	})
	_, abs, _ := core.NewTypeDef(source, "zz_forcer_type", "zz_forcer_abs", "zz_forcer_rep")
	meta := abs.Meta()
	goal := core.MakeProp(core.Eq(statement.Conclusion(), statement.Conclusion()))
	root := core.Promise(goal, func(f core.Forcer) core.ThmCert {
		env := &ProverEnv{
			Forcer: &f,
			ProofService: &ProofService{LoadConstMeta: func(name core.TermName) (core.ConstTermMeta, bool) {
				return meta, name == meta.Name()
			}},
		}
		cert := NewScript(env).TypeDefSource(string(meta.Name()))
		return core.Deduct(cert, cert).AsThmCert()
	})
	cert, _ := core.ForceWithBoundary(context.Background(), root, func(p core.Prop) bool {
		return p.AlphaEquals(statement)
	})
	require.True(t, cert.AlphaEquals(goal))
	assumptions := cert.Assumes()
	require.Len(t, assumptions, 1)
	require.Equal(t, core.BoundaryDoor, assumptions[0].Door)
	require.True(t, assumptions[0].Statement.AlphaEquals(statement))
}
