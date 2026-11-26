package prop

// Differential contract test for ext.MatchFilter against unifyEq — the
// actual matcher the filter guards in unifyEqRewrite /
// UnifyEqRewriteWithPrune. The one-sided contract under test:
//
//	unifyEq(eq, t) yields a result  ⟹  CouldMatch(Lhs(eq))(t) == true
//
// A violation (a "false negative") would silently drop rewrites inside
// recorded tactics and diverge corpus replay, so this table
// deliberately concentrates on the shapes that defeat syntactic
// filters: η-variants, flexible (peeled-binder) heads, free-var heads,
// β-redex heads, and same-name/different-type-instance consts. Each
// case also pins the filter's expected verdict so effectiveness (the
// filter actually excluding head mismatches) is asserted, not just
// safety.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/stretchr/testify/assert"
)

func TestCouldMatchNeverBlocksUnifyEq(t *testing.T) {
	typeA := TypeA
	cMeta := core.MakeConstMeta("cm_c", MakeFun(typeA, TypeBool))
	c := core.MakeConstTerm(cMeta, MakeFun(typeA, TypeBool))
	dMeta := core.MakeConstMeta("cm_d", MakeFun(typeA, TypeBool))
	d := core.MakeConstTerm(dMeta, MakeFun(typeA, TypeBool))
	// Same meta at two type instances: polymorphic const over B.
	typeB := core.MakeVarType("B")
	polyMeta := core.MakeConstMeta("cm_poly", MakeFun(typeB, TypeBool))
	polyA := core.MakeConstTerm(polyMeta, MakeFun(typeA, TypeBool))
	polyBool := core.MakeConstTerm(polyMeta, MakeFun(TypeBool, TypeBool))

	a := Var("a", typeA)
	x := Var("x", typeA)
	xb := Var("xb", TypeBool)
	P := Var("P", MakeFun(typeA, TypeBool))
	g := Var("g", MakeFun(typeA, TypeBool))
	y := Var("y", MakeFun(typeA, TypeBool))

	cases := []struct {
		name string
		eq   Prop // ⊢ lhs = rhs, hyp-free
		t    Term
		// wantCould: the filter's expected verdict (effectiveness pin).
		wantCould bool
		// wantMatch: whether unifyEq must yield ≥1 result (safety-side
		// pin; nil-able cases use wantMatchAny=false + no assertion).
		wantMatch    bool
		assertNoHits bool // when true, assert unifyEq yields nothing
	}{
		{
			// A bare var at the rule's own type: the shape of a set
			// variable met by a resident ∀-hypothesis, read as
			// λx.P(x) = λx.⊤. The var is the target's, no substitution
			// of the rule reaches it, so the const head never meets it.
			name:         "const head, bare var target",
			eq:           testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:            y,
			wantCould:    false,
			assertNoHits: true,
		},
		{
			// A var-headed application, one peel level down.
			name:         "const head, var-headed application target",
			eq:           testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:            ext.Apply(P, a),
			wantCould:    false,
			assertNoHits: true,
		},
		{
			// The head a λ binds is the target's as well.
			name:         "const head, bound var head target",
			eq:           testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:            y.To(ext.Apply(y, a)),
			wantCould:    false,
			assertNoHits: true,
		},
		{
			// Plain const-headed rule on a matching target.
			name:      "const head, same head target",
			eq:        testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:         ext.Apply(c, a),
			wantCould: true,
			wantMatch: true,
		},
		{
			// Head mismatch: the filter must exclude, and the unifier
			// must agree there is nothing to find.
			name:         "const head, different head target",
			eq:           testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:            ext.Apply(d, a),
			wantCould:    false,
			assertNoHits: true,
		},
		{
			// η-short target: rule LHS λx.c(x), target bare c. The
			// unifier matches modulo η; the head filter must agree.
			name:      "eta-short target",
			eq:        testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:         c,
			wantCould: true,
			wantMatch: true,
		},
		{
			// Free-var-headed rule (the docstring example λx.P(x) = y):
			// P is rigid but a VAR — the filter must decline to filter
			// (var identity is unstable under eqSimplify's α-renaming),
			// and the unifier fires on P(a).
			name:      "free-var head rule",
			eq:        testProp(core.Eq(x.To(ext.Apply(P, x)), y)),
			t:         ext.Apply(P, a),
			wantCould: true,
			wantMatch: true,
		},
		{
			// Identity-lambda rule (the set_comprehension shape): peeled-binder
			// head. Non-filtering; unifyEq's variable-LHS ban rejects
			// it internally — contract holds with no hits either way.
			name:      "identity lambda rule",
			eq:        testProp(core.Eq(xb.To(xb), polyBool)),
			t:         ext.Apply(c, a),
			wantCould: true,
		},
		{
			// β-redex-headed target: filter must pass it through
			// (unknown head), unifier β-normalizes and fires.
			name:      "beta-redex target",
			eq:        testProp(core.Eq(x.To(ext.Apply(c, x)), g)),
			t:         ext.Apply(y.To(ext.Apply(y, a)), c),
			wantCould: true,
			wantMatch: true,
		},
		{
			// One const name at two type instances: unifyEq instantiates
			// no type, so the two heads are two constants and the filter
			// excludes the pair.
			name:         "same name different type instance",
			eq:           testProp(core.Eq(x.To(ext.Apply(polyA, x)), g)),
			t:            ext.Apply(polyBool, xb),
			wantCould:    false,
			assertNoHits: true,
		},
		{
			// The same polymorphic const at the rule's own instance.
			name:      "same name same type instance",
			eq:        testProp(core.Eq(x.To(ext.Apply(polyA, x)), g)),
			t:         ext.Apply(polyA, a),
			wantCould: true,
			wantMatch: true,
		},
		{
			// An injectivity law read left to right is headed by the
			// equation of the record's type: an equation between two of
			// the record's parts, at another type, is not its target.
			name:         "equation rule, equation at another type",
			eq:           testProp(core.Eq(core.Eq(ext.Apply(c, a), ext.Apply(c, x)), core.Eq(a, x))),
			t:            core.Eq(a, x),
			wantCould:    false,
			assertNoHits: true,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			filter := unify.MatchFilterFor(Lhs(tc.eq))
			could := filter.CouldMatch(tc.t)
			assert.Equal(t, tc.wantCould, could, "filter verdict")

			hits := 0
			for range unifyEq(context.Background(), tc.eq, tc.t) {
				hits++
			}
			if tc.wantMatch {
				assert.Greater(t, hits, 0, "unifyEq must fire on this case")
			}
			if tc.assertNoHits {
				assert.Equal(t, 0, hits, "filter excluded a pair the unifier matches — CONTRACT VIOLATION")
			}
			// The contract itself: a hit implies the filter said yes.
			if hits > 0 {
				assert.True(t, could,
					"CONTRACT VIOLATION: unifyEq matched but CouldMatch returned false")
			}
		})
	}
}
