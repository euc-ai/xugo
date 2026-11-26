package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// A reconstructed section certificate may rename bound variables. A named
// cite reads the section's stated names while retaining its kernel proof.
func TestSectionCite_WhereUsesStatedBinders(t *testing.T) {
	for _, promised := range []bool{false, true} {
		name := "eager"
		if promised {
			name = "promised"
		}
		t.Run(name, func(t *testing.T) {
			ctx := NewScript(makeStepTestEnv())
			lemma := ctx.Lemma("∀P:(num → bool). ∀c:num. (∀x:num. P(x)) ⇒ P(c)",
				func(a *Argument, P, c Term, all Fact) {
					a.Show("Specialize the universal premise", By(all))
				})
			cert := lemma.PromisedThm()
			require.False(t, cert.Conclusion().Equals(lemma.Goal.Conclusion()),
				"the fixture must reconstruct different binder names")
			built := 0
			if promised {
				lemma.provedThm = core.Promise(cert, func(f core.Forcer) core.ThmCert {
					built++
					return f.Force(cert)
				})
			}
			install := resolveLemmaTarget("By", ctx, lemma)
			positional := citeReferenceProp(ctx, lemma)
			ref := namedCiteReferenceProp(ctx, lemma)
			assert.True(t, install.Conclusion().Equals(cert.Conclusion()),
				"bare citations retain the reconstructed certificate spelling")
			assert.True(t, positional.Conclusion().Equals(cert.Conclusion()),
				"positional citations retain the reconstructed certificate spelling")
			assert.True(t, ref.Conclusion().Equals(lemma.Goal.Conclusion()))
			assert.Zero(t, built, "resolving a section cite must not force its certificate")
			consumer := ctx.Theorem("∀P:(num → bool). ∀Q:bool. ∀d:num. (∀x:num. P(x)) ∧ Q ⇒ P(d)",
				func(a *Argument, P, Q, d Term, h Fact) {
					a.Show("Read the sibling at its stated binder", By(h, Where(lemma, "c", d)))
				})
			require.True(t, consumer.Proved())
			assert.Zero(t, built, "using a section cite must preserve the promise")
			// The wire form must retain the named reference, even though
			// its certificate proves an alpha-equal statement.
			wire, err := proto.Marshal(consumer.DetailedProofProto())
			require.NoError(t, err)
			var decoded DetailedProofProto
			require.NoError(t, proto.Unmarshal(wire, &decoded))
			reader := ext.NewPoolReader(decoded.GetPool(), MockConstMetaService().LoadConstMeta)
			seen := false
			for _, record := range decoded.GetSteps() {
				bp := record.GetBy()
				if bp == nil {
					continue
				}
				hasNamed := false
				for _, p := range bp.GetPremises() {
					hasNamed = hasNamed || len(p.GetNamed()) > 0
				}
				if !hasNamed {
					continue
				}
				require.False(t, seen, "exactly one named By expected")
				seen = true
				spec := BySpec{}
				for _, p := range bp.GetPremises() {
					install, _ := reader.Prop(p.GetInstall())
					premise := ByPremiseSpec{Install: install, Resident: p.GetResident()}
					if len(p.GetNamed()) > 0 {
						require.NotNil(t, p.GetReference(), "the stated binder spelling must survive serialization")
					}
					if p.GetReference() != nil {
						premise.Reference, _ = reader.Prop(p.GetReference())
					}
					for _, nw := range p.GetNamed() {
						witness := reader.Term(nw.GetTerm())
						premise.Named = append(premise.Named, NamedWitness{Binder: nw.GetBinder(), Witness: witness})
					}
					spec.Premises = append(spec.Premises, premise)
				}
				goal, _ := reader.Prop(record.GetGoal())
				replayed := CreateGoalStack(goal)
				require.True(t, ApplyByStep(replayed, ctx.Env, t.Context(), spec))
				for _, claim := range replayed.UnsolvedLeaves() {
					require.True(t, claim.runStep(_KnownThmStep{strongerGoal: ref}))
				}
				require.True(t, replayed.Proved())
				assert.Zero(t, built, "recording and rebuilding the cite must preserve the promise")
				core.Force(t.Context(), replayed.PromisedThm())
			}
			require.True(t, seen)
			proved := core.Force(t.Context(), core.AsThm(ref))
			assert.True(t, proved.Conclusion().Equals(lemma.Goal.Conclusion()))
			if promised {
				assert.Equal(t, 1, built)
			}
		})
	}
}
