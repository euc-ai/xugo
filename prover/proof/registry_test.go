package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
)

// PromiseByKey hands out the statement without building; forcing it runs the
// builder once and memoizes the certificate into the ThmCache.
func TestTheoremRegistry_PromiseByKeyDoesNotForce(t *testing.T) {
	env := &ProverEnv{}
	l := core.Var("p", core.TypeBool())
	stmt := core.MakeProp(core.Eq(l, l)) // ⊢ p = p
	cert := core.TestThm(core.Eq(l, l))
	key := core.PropKey("prop_test_refl")

	calls := 0
	env.RegisterBuilder(key, func(core.Forcer) core.ThmCert {
		calls++
		return cert
	})

	p := env.PromiseByKey(key, stmt)
	assert.NotNil(t, p)
	assert.Equal(t, 0, calls, "PromiseByKey must not run the builder")
	assert.False(t, p.Proved())

	got := core.Force(context.Background(), core.AsThm(p))
	assert.True(t, got.AlphaEquals(stmt))
	assert.True(t, env.ThmCache.HasThm(got))

	a := env.Theorems().RequireThm(core.NewForcer(context.Background()), key)
	b := env.Theorems().RequireThm(core.NewForcer(context.Background()), key)
	assert.True(t, any(a) == any(b))
	assert.Equal(t, 1, calls, "builder runs once; later forces are cache hits")
}

func TestTheoremRegistry_UnregisteredKey(t *testing.T) {
	env := &ProverEnv{}
	l := core.Var("p", core.TypeBool())
	assert.Nil(t, env.PromiseByKey(core.PropKey("nope"), core.MakeProp(core.Eq(l, l))))
	assert.Panics(t, func() { env.Theorems().RequireThm(core.NewForcer(context.Background()), core.PropKey("nope")) })
}

// A by-key citation cycle (X's build forces Y, Y's build forces X) panics
// instead of deadlocking on the _BuilderEntry sync.Once. Requires the builders
// to retain the Forcer they are handed.
func TestTheoremRegistry_BuilderCyclePanics(t *testing.T) {
	env := &ProverEnv{}
	kA := core.PropKey("prop_cycle_A")
	kB := core.PropKey("prop_cycle_B")
	env.RegisterBuilder(kA, func(f core.Forcer) core.ThmCert {
		return env.Theorems().RequireThm(f, kB)
	})
	env.RegisterBuilder(kB, func(f core.Forcer) core.ThmCert {
		return env.Theorems().RequireThm(f, kA)
	})

	assert.Panics(t, func() { env.Theorems().RequireThm(core.NewForcer(context.Background()), kA) })
}
