package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Typed section citations retain declared binder names without forcing
// a promise; both positional and named witnesses then replay from it.
func TestSectionTypeInstance_StatedBindersAndPromise(t *testing.T) {
	for _, named := range []bool{false, true} {
		name := "positional"
		if named {
			name = "named"
		}
		t.Run(name, func(t *testing.T) {
			ctx := NewScript(makeStepTestEnv())
			lemma := ctx.Lemma("∀P:(B → bool). ∀f:(A → B). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))",
				func(a *Argument, P, f, x Term, all Fact) { a.Show("Specialize the premise", By(all)) })
			cert := lemma.PromisedThm()
			built := 0
			lemma.provedThm = core.Promise(cert, func(f core.Forcer) core.ThmCert { built++; return f.Force(cert) })
			aType, bType := core.MakeVarType("A"), core.MakeVarType("B")
			inst := ctx.AtTypeVars(lemma, TypeBinding{name: "A", to: bType}, TypeBinding{name: "B", to: aType})
			want := core.PropTypeInst(lemma.Goal, core.MakeTypeSubst(aType, bType), core.MakeTypeSubst(bType, aType))
			assert.True(t, inst.Reference().Conclusion().Equals(want.Conclusion()))
			assert.Zero(t, built)
			consumer := ctx.Theorem("∀Q:(A → bool). ∀g:(B → A). ∀b:B. (∀a:A. Q(a)) ⇒ Q(g(b))",
				func(a *Argument, Q, g, b Term, all Fact) {
					cite := At(inst, Q, g, b)
					if named {
						cite = Where(inst, "x", b)
					}
					a.Show("Use the section at its reverse type instance", By(all, cite))
				})
			require.True(t, consumer.Proved())
			assert.Zero(t, built)
			core.Force(t.Context(), consumer.PromisedThm())
			core.Force(t.Context(), inst.Reference())
			assert.Equal(t, 1, built)
			norm, _ := Normalize(lemma.Goal)
			vars := OrderedPropTypeVars(norm)
			at := make([]core.HolType, len(vars))
			for i, v := range vars {
				if v.Name() == "A" {
					at[i] = bType
				} else {
					at[i] = aType
				}
			}
			assert.True(t, ctx.AtTypes(lemma, at...).Reference().AlphaEquals(inst.Reference()))
			require.Panics(t, func() {
				ctx.AtTypeVars(CreateGoalStack(lemma.Goal), TypeBinding{name: "A", to: bType}, TypeBinding{name: "B", to: aType})
			})
		})
	}
}

func TestSectionTypeInstance_SoleType(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	lemma := ctx.Lemma("∀P:(A → bool). ∀x:A. (∀y:A. P(y)) ⇒ P(x)",
		func(a *Argument, P, x Term, all Fact) { a.Show("Specialize the premise", By(all)) })
	inst := ctx.AtSoleType(lemma, core.TypeBool())
	want := core.PropTypeInst(lemma.Goal, core.MakeTypeSubst(core.MakeVarType("A"), core.TypeBool()))
	require.True(t, inst.Reference().Conclusion().Equals(want.Conclusion()))
	core.Force(t.Context(), inst.Reference())
}
