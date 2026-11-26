package proof

import (
	"context"
	"reflect"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestCNFCaptureEnv_EveryFieldAccountedFor: CNFCaptureEnv builds the
// derived env by field, so every field of ProverEnv is one it either
// sets, leaves as the derived env's own, snapshots, or shares with the
// parent. The census below names each field's treatment and fails on a
// field it does not name — the decision a field added to ProverEnv
// then asks for. The parent is read and never written.
func TestCNFCaptureEnv_EveryFieldAccountedFor(t *testing.T) {
	parentStore := NewMemoryCNFStore()
	service := MockConstMetaService()
	service.CNFStore = parentStore
	var normalization ext.TermKeyPropMap
	f := core.NewForcer(context.Background())
	parent := &ProverEnv{
		ProofService:          service,
		Scope:                 NewProofScope("prop_capture_census"),
		Forcer:                &f,
		LibraryThms:           map[string]Thm{"num_induction": core.NewAxiom(ext.T)},
		LibraryResolver:       func(string) (Thm, bool) { return nil, false },
		ByAuditReport:         func(string) {},
		CnfRefuterTimeout:     7 * time.Second,
		CnfNormalizationCache: &normalization,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}
	require.NoError(t, parent.InstallLibraryThm("list_induction", core.NewAxiom(ext.T)))

	store := NewCapturingCNFStore(parentStore)
	derived := parent.CNFCaptureEnv(store)

	// The three the collection sets; the parent keeps its own.
	assert.True(t, derived.RequireCNFCacheHit)
	assert.True(t, derived.CNFCacheCaptureOnly)
	assert.Same(t, store, derived.ProofService.CNFStore)
	assert.False(t, parent.RequireCNFCacheHit)
	assert.False(t, parent.CNFCacheCaptureOnly)
	assert.Same(t, parentStore, parent.ProofService.CNFStore)
	// The service is the derived env's own value, every other slot the parent's.
	assert.NotSame(t, parent.ProofService, derived.ProofService)
	assert.Equal(t, reflect.ValueOf(parent.ProofService.LoadConstMeta).Pointer(),
		reflect.ValueOf(derived.ProofService.LoadConstMeta).Pointer())
	// The overlay is a snapshot: the same names in a map of its own.
	thm, ok := derived.LookupLibraryThm("list_induction")
	assert.True(t, ok && thm != nil, "the overlay's names are read through the derived env")

	pv := reflect.ValueOf(parent).Elem()
	dv := reflect.ValueOf(derived).Elem()
	for i := range pv.NumField() {
		field := pv.Type().Field(i)
		p, d := pv.Field(i), dv.Field(i)
		switch field.Name {
		case "ProofService", "RequireCNFCacheHit", "CNFCacheCaptureOnly":
			// Checked above.
		case "ThmCache", "cnfNormalizeCacheMu", "theoremsMu", "dynLibraryThmsMu":
			// The derived env's own: its locks, and a cache nothing the
			// collection runs reads.
		case "dynLibraryThms":
			assert.NotEqual(t, p.Pointer(), d.Pointer(), "the overlay is copied, not shared")
			assert.Equal(t, p.Len(), d.Len(), "the copy holds every installed name")
		default:
			switch field.Type.Kind() {
			case reflect.Pointer, reflect.Map, reflect.Func:
				assert.NotZero(t, p.Pointer(), "field %s: the census sets it on the parent", field.Name)
				assert.Equal(t, p.Pointer(), d.Pointer(), "field %s is shared with the parent", field.Name)
			case reflect.Int64:
				assert.Equal(t, p.Int(), d.Int(), "field %s is the parent's value", field.Name)
			default:
				t.Fatalf("field %s (%s) is not accounted for: decide what the derived env does with it", field.Name, field.Type)
			}
		}
	}
}
