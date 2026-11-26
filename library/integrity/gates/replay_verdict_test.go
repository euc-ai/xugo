// replay_verdict_test.go — what a replay's verdict is read from
// (forceMember, replay_test.go).

package gates

import (
	"context"
	"iter"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// _ForcesItself embeds a promise and declares forces of its own, each
// handing back a genuine certificate of another statement.
type _ForcesItself struct{ core.ThmPromise }

func (_ForcesItself) Force(context.Context) core.ThmCert {
	return core.Refl(core.Var("x", core.TypeBool()))
}

func (_ForcesItself) ForceWithBoundary(context.Context, core.PropPredicate) (core.ThmCert, []core.Prop) {
	return core.Refl(core.Var("x", core.TypeBool())), nil
}

// _RestatesItself embeds a promise of one statement and answers every
// question about what it states with another.
type _RestatesItself struct {
	core.ThmPromise
	as core.Prop
}

func (r _RestatesItself) Conclusion() core.Term            { return r.as.Conclusion() }
func (r _RestatesItself) Hyps() []core.Term                { return r.as.Hyps() }
func (r _RestatesItself) HypIter() iter.Seq[core.Term]     { return r.as.HypIter() }
func (r _RestatesItself) Hyp(i int) core.Term              { return r.as.Hyp(i) }
func (r _RestatesItself) NumHyps() int                     { return r.as.NumHyps() }
func (r _RestatesItself) AlphaKey() core.PropKey           { return r.as.AlphaKey() }
func (r _RestatesItself) AlphaEquals(p core.Prop) bool     { return r.as.AlphaEquals(p) }
func (r _RestatesItself) AsProp() core.Prop                { return r.as }
func (r _RestatesItself) Core() core.Prop                  { return r }
func (r _RestatesItself) String() string                   { return string(r.as.AlphaKey()) }
func (r _RestatesItself) HasFreeName(n core.TermName) bool { return r.as.HasFreeName(n) }

// TestForceMember_ReadsTheKernelValue: a member's Build is code the
// replay does not trust, and the theorem it hands back may be of a type
// that embeds a promise and answers for it. The replay asks the
// embedded promise and core forces it: a promise with no proof fails by
// its own builder whatever force its carrier declares, and a proved
// promise of another statement is refused whatever statement its
// carrier reports.
func TestForceMember_ReadsTheKernelValue(t *testing.T) {
	member, ok := registry.ByName("list.AppendAssoc")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	ctx := context.Background()
	stated := member.Statement().Prop
	trustNothing := func(core.Prop) bool { return false }
	none := &proof.Proof{}

	built := false
	unproved := core.Promise(stated, func(core.Forcer) core.ThmCert {
		built = true
		panic("no proof")
	})
	require.Panics(t, func() { forceMember(ctx, member, _ForcesItself{unproved}, none, trustNothing) },
		"a promise with no proof replayed")
	require.True(t, built, "the member's own builder never ran")
	require.False(t, unproved.Proved())

	x := core.Var("x", core.TypeBool())
	other := core.Promise(core.MakeProp(core.Eq(x, x)), func(core.Forcer) core.ThmCert { return core.Refl(x) })
	_, err := forceMember(ctx, member, _RestatesItself{other, stated}, none, trustNothing)
	if err == nil || !strings.Contains(err.Error(), "is not the entry's declared statement") {
		t.Fatalf("a proof of another statement reported as the member's: got %v, want the statement refused", err)
	}

	// A promise of the member's statement that settles is the member's:
	// the certificates come back, the top's last.
	proved := core.Promise(stated, func(core.Forcer) core.ThmCert { return core.NewAxiom(stated.Conclusion()) })
	certs, err := forceMember(ctx, member, proved, none, trustNothing)
	require.NoError(t, err)
	require.Len(t, certs, 1)
	require.True(t, certs[0].AlphaEquals(stated))
}
