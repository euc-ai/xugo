package typedgen_test

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/typedgen"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

func TestRecordWholeViewsDoNotRefineStoredCarriers(t *testing.T) {
	for _, predicate := range []string{"group", "abelian_group", "comm_ring", "field"} {
		t.Run(predicate, func(t *testing.T) {
			whole, ok := registry.StructureByPredicate(predicate)
			require.True(t, ok)
			require.True(t, whole.IsWholeTypeView())
			_, _, _, ok = typedgen.StructureFactAlias(predicate, "record_fixture")
			require.False(t, ok, "a whole-type fact does not imply membership in the record's stored carrier")
			_, _, carriers, ok := typedgen.StructureFactAlias(predicate+"_on", "record_fixture")
			require.True(t, ok)
			require.Equal(t, []int{0}, carriers)
		})
	}
}

// A projection between records preserves the carrier phantom, including
// when the record map forgets operations or selects either endpoint.
func TestRender_RecordCarrierProjections(t *testing.T) {
	for _, tc := range []struct{ family, method, result string }{
		{"algebra/group/group_homomorphism", "sourceThm", "group.GroupFact[Car0]"},
		{"algebra/group/group_homomorphism", "targetThm", "group.GroupFact[Car1]"},
		{"algebra/module/module", "addGroupOnThm", "group.GroupFact[Car1]"},
		{"algebra/module/module", "ringOnThm", "comm_ring.CommRingFact[Car0]"},
		{"algebra/ring/comm_ring", "addGroupOnThm", "abelian_group.AbelianGroupFact[Car0]"},
		{"algebra/field/field", "ringOnThm", "comm_ring.CommRingFact[Car0]"},
	} {
		t.Run(tc.family+"/"+tc.method, func(t *testing.T) {
			var family *registry.Family
			for _, f := range registry.Families() {
				if f.Name == tc.family {
					family = f
					break
				}
			}
			require.NotNil(t, family)
			generated, err := typedgen.Render(family, "record_fixture", t.TempDir(), "record carrier projections")
			require.NoError(t, err)
			source := string(generated.Source)
			start := strings.Index(source, "func (th "+tc.method+") Read[")
			require.NotEqual(t, -1, start)
			// The interface constraint contains a brace too; the result is on
			// the final line of the generic signature.
			end := strings.Index(source[start:], "\n\treturn")
			require.Positive(t, end)
			signature := source[start : start+end]
			require.Contains(t, signature, ") "+tc.result+" {")
		})
	}
}

func TestRecordTermNormalizer_IsLocalAndFollowsForgetfulMaps(t *testing.T) {
	generation := tactic.RecordNormalGeneration()
	normalize := registry.RecordTermNormalizer()
	manager := registry.GetConstMetaManager()
	scope := &dsl.ParseScope{Syntax: manager, ConstResolver: func(name string) core.ConstTermMeta { m, _ := manager.LoadConstMeta(core.TermName(name)); return m }}
	for _, text := range []string{
		"R:ring_ops(A) ⊢ additive_group(R).carrier = R.carrier",
		"F:field_ops(A) ⊢ field_ring(F).carrier = F.carrier",
		"M:module_ops(A, B) ⊢ module_additive_group(M).carrier = M.carrier",
		"R:ring_ops(A), c:set(A) ⊢ restrict_ring(R, c).carrier = c",
	} {
		parsed := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, parsed.Errors)
		left, right, ok := core.MatchesEQ(parsed.Prop.Conclusion())
		require.True(t, ok)
		require.True(t, normalize(left).AlphaEquals(right), text)
	}
	require.Equal(t, generation, tactic.RecordNormalGeneration(), "local comparisons must not replace the proof environment's table")
}

func TestRecordInstanceVocabulary_UsesNormalizedFields(t *testing.T) {
	family := registry.NewFamily("zz_record_instance_vocabulary", nil).WithInstance(comm_ring.CommRing, real_ring.CommRing)
	bindings := family.ImplicitBindings()
	require.NotNil(t, bindings["R"])
	require.True(t, bindings["add"].AlphaEquals(dsl.RealPlusMeta.Term()))
	require.True(t, bindings["mul"].AlphaEquals(dsl.RealStarMeta.Term()))
	require.NotNil(t, bindings["carrier"])
}

func TestRecordInstanceVocabulary_QualifiesSharedFields(t *testing.T) {
	family := registry.NewFamily("zz_record_hom_vocabulary", nil).
		WithInstance(group_homomorphism.GroupHomomorphism, int_real_lift.RealOfIntHom)
	bindings := family.ImplicitBindings()
	require.NotNil(t, bindings["G"])
	require.NotNil(t, bindings["H"])
	require.NotNil(t, bindings["f"])
	for _, name := range []string{"mul", "one", "inv", "carrier"} {
		require.Nil(t, bindings[name], "shared fields require G.%s or H.%s", name, name)
	}
}
