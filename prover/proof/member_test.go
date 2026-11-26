package proof

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// The point-with-membership pairing (member.go): MemberOf pairs a term
// with the resident fact that it lies in a set, and refuses a fact about
// another term.

func TestMemberOf_PairsAPointWithItsMembership(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem("∀s:(num → bool). ∀x:num. x ∈ s ⇒ (∃y:num. y ∈ s)",
		func(a *Argument, s *ext.Expr[ext.Set[ext.Nat]], x *ext.Expr[ext.Nat], mem Fact) {
			m := MemberOf(x, mem)
			content, _ := m.AsFact().BoundContent()
			require.Contains(t, ext.PrintTerm(content), "∈", "%s", ext.PrintTerm(content))
			require.True(t, m.Core().Equals(x.Core()))
			a.Take(x)
			a.Show("the point itself", By(mem))
		})
	require.True(t, sec.Proved())
}

func TestMemberOf_RefusesAnotherPointsFact(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem("∀s:(num → bool). ∀x y:num. x ∈ s ⇒ y ∈ s ⇒ (∃z:num. z ∈ s)",
		func(a *Argument, s *ext.Expr[ext.Set[ext.Nat]], x, y *ext.Expr[ext.Nat], memX, memY Fact) {
			func() {
				defer func() {
					r := recover()
					require.NotNil(t, r)
					require.Contains(t, fmt.Sprint(r), "but the member is")
				}()
				MemberOf(y, memX) // the fact is about x
			}()
			a.Take(y)
			a.Show("the point itself", By(memY))
		})
	require.True(t, sec.Proved())
	_ = strings.HasPrefix
}
