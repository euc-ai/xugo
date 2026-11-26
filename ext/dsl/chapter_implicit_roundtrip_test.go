package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

type chapterRecordSyntax struct {
	SyntaxTable
	group *ConstSyntax
}

func (s chapterRecordSyntax) ConstSyntax(name string) *ConstSyntax {
	if name == "zz_group" {
		return s.group
	}
	return s.SyntaxTable.ConstSyntax(name)
}

func chapterImplicitRecordScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err)
		return ty
	}
	scope.ConstMetas["zz_derived"] = core.MakeConstMeta("zz_derived", typ("(A → A → A) → A → A → A"))
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", typ("(A → A → A) → (num → A) → (num → A) → num → A"))
	scope.ConstMetas["zz_default_op"] = core.MakeConstMeta("zz_default_op", typ("num → num → num"))
	scope.ConstMetas["zz_group"] = core.MakeConstMeta("zz_group", typ("zz_ops(A) → bool"))
	scope.Syntax = chapterRecordSyntax{SyntaxTable: implicitStructFieldsSyntax{scope.Syntax}, group: &ConstSyntax{
		StructurePredicate: true,
		Bundle: &BundleSyntax{Params: []BundleParam{{Name: "S", Type: typ("zz_ops(A)")}},
			Structure: true, Subject: 0, Layouts: []BundleLayout{{Structure: "zz_group", Slots: []int{0}}}},
	}}
	scope.ImplicitBindings = map[string]core.Term{
		"op": scope.ConstMetas["zz_default_op"].Term(), "add": scope.ConstMetas["zz_default_op"].Term(),
	}
	return scope
}

func TestChapterSpelling_InstancePrefixRoundTripUnderRecords(t *testing.T) {
	scope := chapterImplicitRecordScope(t)
	for _, tc := range []struct {
		name        string
		raw         string
		keepDefault bool
	}{
		{"instance", "∀x:num. zz_derived(zz_default_op, x, x) = x", false},
		{"record", "∀S:zz_ops(num). ∀x:num. zz_derived(zz_default_op, x, x) = x", true},
		{"two_records", "∀S T:zz_ops(num). ∀x:num. zz_derived(zz_default_op, x, x) = x", true},
		{"declared_record", "S:zz_ops(num), x:num ⊢ zz_derived(zz_default_op, x, x) = x", true},
		{"two_declared_records", "S:zz_ops(num), T:zz_ops(num), x:num ⊢ zz_derived(zz_default_op, x, x) = x", true},
		{"lambda_record", "∀x:num. (λS:zz_ops(num). zz_derived(zz_default_op, x, x)) = (λS:zz_ops(num). x)", true},
		{"shadowed_record", "∀S:zz_ops(num). ∀x:num. (∀S:num. zz_derived(zz_default_op, x, x) = x) ∧ zz_derived(zz_default_op, x, x) = x", true},
		{"explicit_record_fields", "∀S T:zz_ops(num). ∀x:num. zz_derived(zz_op(S), x, x) = zz_derived(zz_op(T), x, x)", false},
		{"constant_record_field", "zz_derived(zz_op(zz_record), 1, 2) = 1", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, err := ChapterSpelling(tc.raw, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, tc.keepDefault, strings.Contains(out, "zz_default_op"), out)
			assertSameProp(t, scope, out, tc.raw)
			again, err := ChapterSpelling(out, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, out, again)
		})
	}
}

func TestChapterSpelling_UniqueRecordPrefixRoundTrip(t *testing.T) {
	scope := chapterImplicitRecordScope(t)
	for _, tc := range []struct{ name, raw, want string }{
		{"record", "∀S:zz_ops(A). zz_group(S) ⇒ ∀x:A. zz_derived(zz_op(S), x, x) = x", "zz_derived(x, x)"},
		{"declared_record", "S:zz_ops(A), x:A, zz_group(S) ⊢ zz_derived(zz_op(S), x, x) = x", "zz_derived(x, x)"},
		{"instance_is_shadowed", "∀S:zz_ops(num). zz_group(S) ⇒ ∀x:num. zz_derived(zz_default_op, x, x) = x", "zz_derived(zz_default_op, x, x)"},
		{"other_record", "∀S:zz_ops(num). zz_group(S) ⇒ ∀x:num. zz_derived(zz_op(zz_record), x, x) = x", "zz_derived(zz_record.op, x, x)"},
		{"two_records", "∀S T:zz_ops(A). zz_group(S) ∧ zz_group(T) ⇒ ∀x:A. zz_derived(zz_op(S), x, x) = zz_derived(zz_op(T), x, x)", "zz_derived(S.op, x, x) = zz_derived(T.op, x, x)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, err := ChapterSpelling(tc.raw, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Contains(t, out, tc.want)
			assertSameProp(t, scope, out, tc.raw)
			again, err := ChapterSpelling(out, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, out, again)
		})
	}
}

// Beside a record on another carrier, a field is dropped where the
// application's types pick its record back, an operator's included; a
// bare head, whose types pick nothing, and a record beside one on its
// own carrier keep the field.
func TestChapterSpelling_RecordPickedByTypeRoundTrip(t *testing.T) {
	scope := chapterImplicitRecordScope(t)
	const two = "∀S:zz_ops(A). ∀T:zz_ops(B). zz_group(S) ∧ zz_group(T) ⇒ "
	for _, tc := range []struct{ name, raw, want string }{
		{"two_carriers", two + "∀x:A. ∀y:B. zz_derived(zz_op(S), x, x) = x ∧ zz_derived(zz_op(T), y, y) = y",
			"zz_derived(x, x) = x ∧ zz_derived(y, y) = y"},
		{"declared", "S:zz_ops(A), T:zz_ops(B), y:B, zz_group(S), zz_group(T) ⊢ zz_derived(zz_op(T), y, y) = y",
			"⊢ zz_derived(y, y) = y"},
		{"operator", two + "∀u v:(num → B). zz_pointwise(zz_op(T), u, v) = zz_pointwise(zz_op(T), v, u)",
			"u + v = v + u"},
		{"bare_head", two + "zz_derived(zz_op(S)) = zz_derived(zz_op(S))",
			"zz_derived(S.op) = zz_derived(S.op)"},
		{"one_carrier", "∀S T:zz_ops(A). zz_group(S) ∧ zz_group(T) ⇒ ∀x:A. zz_derived(zz_op(S), x, x) = x",
			"zz_derived(S.op, x, x) = x"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, err := ChapterSpelling(tc.raw, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Contains(t, out, tc.want)
			assertSameProp(t, scope, out, tc.raw)
			again, err := ChapterSpelling(out, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, out, again)
		})
	}
}

func TestChapterSpelling_RecordFoldRoundTrip(t *testing.T) {
	scope := chapterImplicitRecordScope(t)
	for _, tc := range []struct {
		name string
		raw  string
		sum  bool
	}{
		{"record", "∀S:zz_ops(A). zz_group(S) ⇒ ∀s:set(num). ∀f:(num → A). iterated_op(zz_op(S), s, λi:num. f(i)) = f(0)", true},
		{"declared_record", "S:zz_ops(A), s:set(num), f:(num → A), zz_group(S) ⊢ iterated_op(zz_op(S), s, λi:num. f(i)) = f(0)", true},
		{"two_records", "∀S T:zz_ops(A). ∀s:set(num). ∀f:(num → A). iterated_op(zz_op(S), s, λi:num. f(i)) = iterated_op(zz_op(T), s, λi:num. f(i))", false},
		{"intrinsic_sum_differs", "∀S:zz_ops(num). ∀s:set(num). ∀f:(num → num). iterated_op(zz_op(S), s, λi:num. f(i)) = f(0)", false},
		{"bare_function", "∀S:zz_ops(A). ∀s:set(num). ∀f:(num → A). iterated_op(zz_op(S), s, f) = f(0)", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, err := ChapterSpelling(tc.raw, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, tc.sum, strings.Contains(out, "Σ_{i∈s} f(i)"), out)
			assertSameProp(t, scope, out, tc.raw)
			again, err := ChapterSpelling(out, scope.Syntax, scope.ImplicitBindings)
			require.NoError(t, err)
			require.Equal(t, out, again)
		})
	}
	t.Run("unavailable_sum_prefix", func(t *testing.T) {
		unbound := *scope
		unbound.ImplicitBindings = map[string]core.Term{"op": scope.ImplicitBindings["op"]}
		raw := "∀S:zz_ops(A). ∀s:set(num). ∀f:(num → A). iterated_op(zz_op(S), s, λi:num. f(i)) = f(0)"
		out, err := ChapterSpelling(raw, unbound.Syntax, unbound.ImplicitBindings)
		require.NoError(t, err)
		require.NotContains(t, out, "Σ")
		assertSameProp(t, &unbound, out, raw)
	})
}
