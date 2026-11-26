package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestReadingAtWitnessTypes_FreshLetterTakesTheBindersType: a reading
// `Q(c) ⊢ ∀S:set(A). P(c, S)`, its A fixed by the hypothesis, grounded
// at a bare `∅` — read with the constant's own fresh letter, which
// nothing in the text pinned: the witness takes the binder's A, and the
// tuple comes back so typed. A witness no reading of the binder takes
// is refused naming the binder's type, the witness's, and the tie.
func TestReadingAtWitnessTypes_FreshLetterTakesTheBindersType(t *testing.T) {
	A := core.MakeVarType("A")
	setA := core.MakeFun(A, core.TypeBool())
	c := ext.Var("c", A)
	Q := ext.Var("Q", core.MakeFun(A, core.TypeBool()))
	P := ext.Var("P", core.MakeFun(A, setA, core.TypeBool()))
	S := ext.Var("S", setA)
	reading := core.MakeProp(ext.ForAll(S)(P.Apply(c, S)).Core(), Q.Apply(c).Core())

	empty := dsl.ParseTermTextInScope("∅", nil, &dsl.ParseScope{FreshenMetaLetters: true}, nil)
	require.Empty(t, empty.Errors)
	fresh := func(v core.VarType) bool { return strings.HasPrefix(string(v.Name()), "?f") }
	require.True(t, ext.TypeAnyVar(empty.Term.Type(), fresh), "a bare ∅ is read with its own fresh letter: %s", ext.FormatType(empty.Term.Type()))

	_, fitted, err := ReadingAtWitnessTypes(reading, []Term{empty.Term})
	require.NoError(t, err)
	require.Len(t, fitted, 1)
	require.True(t, fitted[0].Type().Equals(setA), "the witness takes the binder's type; got %s", ext.FormatType(fitted[0].Type()))

	letter := core.MakeVarType("?f1A")
	idTy := core.MakeFun(letter, letter)
	id := core.MakeConstTerm(core.MakeConstMeta("zz_idm", idTy), idTy)
	_, _, err = ReadingAtWitnessTypes(reading, []Term{id})
	require.ErrorContains(t, err, "of type (var:?f1A → var:?f1A) does not fit the binder S:(var:A → bool)")
	require.ErrorContains(t, err, "write zz_idm⟨A:τ⟩")
}
