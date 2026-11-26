// ac_test.go — the premise surface (Deriver.Eq / Equation).

package ac

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// acTestCerts builds assoc/sym certificates for an uninterpreted
// binary op ⊕ on ind. TestThm is acceptable inside _test.go: the
// Deriver never looks the op up anywhere — it reads it off the assoc
// cert — so an uninterpreted const exercises exactly the any-AC-op
// contract.
func acTestCerts() (op *ext.TermWrapper, assoc, sym core.Thm) {
	opTy := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	op = ext.Const(core.MakeConstMeta("acplus", opTy), opTy)
	m, n, p := ext.Var("m", TypeInd), ext.Var("n", TypeInd), ext.Var("p", TypeInd)
	assoc = core.TestThm(ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(p)(
		op.Apply(op.Apply(m, n), p).Eq(op.Apply(m, op.Apply(n, p)))))))
	sym = core.TestThm(ext.ForAll(m)(ext.ForAll(n)(
		op.Apply(m, n).Eq(op.Apply(n, m)))))
	return op, assoc, sym
}

// TestDeriverEq_SelfProof: Eq's Equation carries the closed, kernel-
// derived ⊢ lhs = rhs — the certificate a consuming By closes the
// claim with.
func TestDeriverEq_SelfProof(t *testing.T) {
	op, assoc, sym := acTestCerts()
	a, b, c := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd)

	// a⊕(b⊕c) = b⊕(a⊕c) — the "carry the spare factor across" shape.
	lhs := op.Apply(a, op.Apply(b, c))
	rhs := op.Apply(b, op.Apply(a, c))

	cert := New(assoc, sym).Eq(lhs, rhs).SelfProof()
	require.NotNil(t, cert)
	require.True(t, cert.Proved(), "the self-proof must be a certificate")
	require.Equal(t, 0, cert.NumHyps(), "the self-proof must be closed")
	require.True(t, cert.Conclusion().AlphaEquals(core.Eq(lhs.Core(), rhs.Core())),
		"self-proof states %s, want %s", ext.PrintTerm(cert.Conclusion()),
		ext.PrintTerm(core.Eq(lhs.Core(), rhs.Core())))
}

// TestDeriverEq_ValidatesUpFront: the input contract is enforced at the
// authoring call site (Eq), not left to the consuming By — two terms
// that are not rearrangements of the same sum panic here.
func TestDeriverEq_ValidatesUpFront(t *testing.T) {
	op, assoc, sym := acTestCerts()
	a, b, c := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd)

	require.PanicsWithValue(t, "AC regroup: nil lhs/rhs term", func() {
		New(assoc, sym).Eq(nil, nil)
	})
	require.Panics(t, func() {
		// Different leaf multisets: a⊕b vs a⊕c.
		New(assoc, sym).Eq(op.Apply(a, b), op.Apply(a, c))
	})
	require.Panics(t, func() {
		// Nothing to regroup.
		New(assoc, sym).Eq(op.Apply(a, b), op.Apply(a, b))
	})
}
