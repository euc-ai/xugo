package gates

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestTermAs_ABarePolymorphicConstantTakesThePhantomsInstance: TermAs
// reads its text at the phantom's type, so `∅` written bare is ∅ at
// set(A) — the spelling a claim reads from its partner (`s = ∅`) — where
// the untyped Term adopted by ext.As leaves ∅'s letter free and the
// adoption refuses it. A text that cannot be read at the type is
// refused at the parse, naming both types.
func TestTermAs_ABarePolymorphicConstantTakesThePhantomsInstance(t *testing.T) {
	fam, ok := registry.FamilyByName("relations/order")
	require.True(t, ok)
	ctx := fam.ParseScript(serve.NewSeedEnv())
	sec := ctx.Section(ctx.MakePropText("∀s:set(A). s = s"))
	sec.Do(proof.Derive(func(a *proof.Argument) {
		a.Fix()

		empty := a.TermAs[ext.Set[ext.A]]("∅")
		require.True(t, empty.Core().Type().Equals(ext.HolTypeOf[ext.Set[ext.A]]()),
			"∅ read at %s", ext.FormatType(empty.Core().Type()))

		adopted := func() { ext.As[ext.Set[ext.A]](a.Term("∅")) }
		require.PanicsWithValue(t,
			"ext.As: ∅⟨A:var:?f1A⟩ has type (var:?f1A → bool), not (var:A → bool)", adopted,
			"the untyped Term carries no expectation: its ∅ keeps a free letter")

		func() {
			defer func() {
				r := recover()
				require.NotNil(t, r, "∅ is no number")
				msg, _ := r.(string)
				require.True(t, strings.Contains(msg, "Argument.TermAs") && strings.Contains(msg, "expected num"),
					"the refusal names the verb and the expected type: %v", r)
			}()
			a.TermAs[ext.Nat]("∅")
		}()

		a.Show("s = s", proof.Refl())
	}))
	require.True(t, sec.Proved())
}

// TestLetAs_ReadsTheTextAtThePhantomAndReturnsTheNameBesideItsDefinition:
// LetAs is Let with the text read at the phantom's type, as TermAs reads
// one — `∅` written bare is ∅ at set(A) — and the name comes back as the
// typed handle beside its equation: the handle is the variable `e` at
// set(A), the equation `e = ∅` is resident under the name a claim text
// now spells, and a text that cannot be read at the type is refused at
// the parse, naming the verb and the expected type, before any step.
func TestLetAs_ReadsTheTextAtThePhantomAndReturnsTheNameBesideItsDefinition(t *testing.T) {
	fam, ok := registry.FamilyByName("relations/order")
	require.True(t, ok)
	ctx := fam.ParseScript(serve.NewSeedEnv())
	sec := ctx.Section(ctx.MakePropText("∀s:set(A). s ∪ ∅ = s ∪ ∅"))
	sec.Do(proof.Derive(func(a *proof.Argument) {
		a.Fix()

		e, eDef := a.LetAs[ext.Set[ext.A]]("e", "∅")
		require.True(t, e.Core().Type().Equals(ext.HolTypeOf[ext.Set[ext.A]]()),
			"e read at %s", ext.FormatType(e.Core().Type()))
		v, isVar := e.Core().(core.VarTerm)
		require.True(t, isVar && string(v.Name()) == "e",
			"the handle is the name's own variable, got %s", ext.PrintTerm(e.Core()))
		content, bound := eDef.BoundContent()
		require.True(t, bound, "the Fact is the resident equation")
		require.True(t, content.AlphaEquals(ext.Eq(e.Core(), a.TermAs[ext.Set[ext.A]]("∅").Core())),
			"the equation is e = ∅ at set(A), got %s", ext.PrintTerm(content))
		require.NotPanics(t, func() { a.Hyp("e = ∅") },
			"the equation is resident under the name the claim text now spells")

		func() {
			defer func() {
				r := recover()
				require.NotNil(t, r, "∅ is no number")
				msg, _ := r.(string)
				require.True(t, strings.Contains(msg, "Argument.LetAs") && strings.Contains(msg, "expected num"),
					"the refusal names the verb and the expected type: %v", r)
			}()
			a.LetAs[ext.Nat]("n", "∅")
		}()

		a.Show("s ∪ e = s ∪ e", proof.Refl())
	}))
	require.True(t, sec.Proved())
}
