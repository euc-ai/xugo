// Congruence surface for the text DSL: `x ≡ y (mod m)`.
//
// The domain is chosen by operand type, mirroring the `∣` divisibility
// dispatch, and both domains lower to the same shape: a three-place
// relation read in the order the mixfix spells it.
//
// At num the mixfix means ℕ's own `nat_cong(x, y, m)`, defined as
// `nat_mod(x, m) = nat_mod(y, m)`.
//
// At int it means ℤ's `int_cong(x, y, m)`, defined as `m ∣ (x - y)`.
//
// Real congruence is deliberately not dispatched, which buys a clean
// rule for `&` coercion operands: num is impossible for a coercion and
// real is not on the table, so `&x ≡ &y (mod &n)` always means int — no
// default-domain convention needed.

package dsl

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// Congruence const metas: the def-less surface meta each arm falls back
// to where the scope does not carry the chapter's mint.
var (
	// IntCongMeta: `int_cong` : int → int → int → bool — congruence
	// defined inside ℤ (proofs/int_num/int_congruence,
	// `int_cong(x, y, m) ⇔ m ∣ (x - y)`).
	IntCongMeta = core.MakeConstMeta("int_cong",
		core.MakeFun(IntType, IntType, IntType, core.TypeBool()))
	// NatCongMeta: `nat_cong` : num → num → num → bool — congruence
	// defined inside ℕ (proofs/nat_num/nat_congruence,
	// `nat_cong = λx y n. nat_mod(x, n) = nat_mod(y, n)`).
	NatCongMeta = core.MakeConstMeta("nat_cong",
		core.MakeFun(NumType, NumType, NumType, core.TypeBool()))
)

// buildCong lowers `x ≡ y (mod m)` to `nat_cong(x, y, m)` at num and to
// `int_cong(x, y, m)` at int.
//
// The three operands share one arithmetic domain. All-num dispatches
// `nat_cong`; otherwise every operand must land in int — num operands embed,
// a real-defaulted `&` coercion retargets (the type-directed `&`, as in
// reconcileNumericDomain), and a genuinely real or foreign-typed operand
// fails the rebuild and errors.
func buildCong(n *astCong, env *typeEnv) (core.Term, error) {
	// Build the operands in non-bool context, cross-propagating a
	// successfully-built type into the ones that need context — the
	// buildEqOperands discipline at three positions.
	nodes := [3]astNode{n.left, n.right, n.modulus}
	var terms [3]core.Term
	var errs [3]error
	for i, nd := range nodes {
		terms[i], errs[i] = buildTerm(nd, env, false)
	}
	var pinned core.HolType
	for i := range terms {
		if errs[i] == nil {
			if pinned == nil {
				pinned = NumType
			}
			// Congruence has only num and int instances. An integer or
			// a `&` selects int for operands needing context, even when
			// an earlier operand is natural (`-a ≡ k (mod &p)`).
			// A genuine real or foreign operand is refused below.
			if !terms[i].Type().Equals(NumType) {
				pinned = IntType
			}
		}
	}
	if pinned == nil {
		return nil, errs[0]
	}
	for i := range terms {
		if errs[i] != nil {
			t, err := buildExpected(nodes[i], env, pinned)
			if err != nil {
				return nil, err
			}
			terms[i] = t
		}
	}

	allNum := true
	for i := range terms {
		if !terms[i].Type().Equals(NumType) {
			allNum = false
			break
		}
	}
	if allNum {
		return buildAppViaMeta(env, scopeCongMeta(env, NatCongMeta), terms[:])
	}
	for i := range terms {
		if terms[i].Type().Equals(IntType) {
			continue
		}
		t, err := buildExpected(nodes[i], env, IntType)
		if err != nil || !t.Type().Equals(IntType) {
			return nil, fmt.Errorf(
				"≡ (mod) dispatches num and int congruence only; operand has type %s",
				ext.FormatType(terms[i].Type()))
		}
		terms[i] = t
	}
	return buildAppViaMeta(env, scopeCongMeta(env, IntCongMeta), terms[:])
}

// scopeCongMeta resolves a congruence meta scope-first, AbsType-guarded
// — the same rule as the arith/set operator paths, for the same reason:
// the congruence is def-carrying where its chapter is linked, and
// binding the def-less surface meta instead would leave it opaque to
// DefExpandStep.
func scopeCongMeta(env *typeEnv, surface core.ConstTermMeta) core.ConstTermMeta {
	if m, ok := env.scopeConstMetas[string(surface.Name())]; ok &&
		m.AbsType().Equals(surface.AbsType()) {
		return m
	}
	return surface
}
