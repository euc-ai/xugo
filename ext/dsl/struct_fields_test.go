package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

type structFieldsSyntax struct {
	SyntaxTable
	metas   map[string]core.ConstTermMeta
	structs map[string]*StructSyntax
}

type implicitStructFieldsSyntax struct{ SyntaxTable }

func (s implicitStructFieldsSyntax) ConstSyntax(name string) *ConstSyntax {
	switch name {
	case "zz_derived":
		return &ConstSyntax{Implicit: []string{"op"}}
	case "zz_coset":
		return &ConstSyntax{Implicit: []string{"op"}}
	case "zz_measure":
		return &ConstSyntax{Implicit: []string{"e"}}
	case "zz_delta":
		return &ConstSyntax{Implicit: []string{"e", "one"}}
	case "zz_pointwise":
		return &ConstSyntax{Implicit: []string{"op"}, Operator: &Operator{Symbol: "+", Args: []int{0, 1}}}
	case "zz_fadd":
		return &ConstSyntax{Implicit: []string{"op"}}
	case "zz_fzero":
		return &ConstSyntax{Implicit: []string{"e"}}
	}
	return s.SyntaxTable.ConstSyntax(name)
}

func (s implicitStructFieldsSyntax) OperatorConsts(symbol string, arity int) []string {
	names := s.SyntaxTable.OperatorConsts(symbol, arity)
	if symbol == "+" && arity == 2 {
		return append(append([]string{}, names...), "zz_pointwise")
	}
	return names
}

func TestStructFields_ImplicitComponent(t *testing.T) {
	scope := structFieldsTestScope(t)
	ty, err := ParseTypeText("(A → A → A) → A → A → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_derived"] = core.MakeConstMeta("zz_derived", ty)
	ty, err = ParseTypeText("(A → A → A) → (num → A) → (num → A) → num → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", ty)
	scope.Syntax = implicitStructFieldsSyntax{scope.Syntax}
	for _, tc := range []struct{ short, full string }{
		{"∀S:zz_ops(A). ∀x y:A. zz_derived(x, y) = S.e", "∀S:zz_ops(A). ∀x y:A. zz_derived(S.op, x, y) = S.e"},
		{"∀S:zz_ops(A). zz_derived = S.op", "∀S:zz_ops(A). zz_derived(S.op) = S.op"},
		{"S:zz_ops(A), x:A ⊢ zz_derived(x, x) = S.e", "S:zz_ops(A), x:A ⊢ zz_derived(S.op, x, x) = S.e"},
		{"∀S:zz_ops(A). ∀op:(A → A → A). ∀x:A. zz_derived(x, x) = x", "∀S:zz_ops(A). ∀op:(A → A → A). ∀x:A. zz_derived(op, x, x) = x"},
		{"∀S:zz_ops(A). ∀u v:(num → A). u + v = v + u", "∀S:zz_ops(A). ∀u v:(num → A). zz_pointwise(S.op, u, v) = zz_pointwise(S.op, v, u)"},
	} {
		assertSameProp(t, scope, tc.short, tc.full)
	}
	res := ParsePropTextInScope("∀S T:zz_ops(A). ∀x:A. zz_derived(x, x) = x", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "more than one record")
	res = ParsePropTextInScope("∀S T:zz_ops(A). ∀x:A. zz_derived(S.op, x, x) = x", scope)
	require.Empty(t, res.Errors)
}

// Records on different carriers are told apart by the application's
// types: a short application reads the fields of the one record its
// arguments fit, in the text and at an operator alike, and a name the
// prefix repeats is read from one record. Records on one carrier, or
// arguments whose types the text leaves open, leave several readings
// standing and the short form is refused.
func TestStructFields_ImplicitComponentPickedByType(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType { ty, err := ParseTypeText(text); require.NoError(t, err); return ty }
	scope.ConstMetas["zz_derived"] = core.MakeConstMeta("zz_derived", typ("(A → A → A) → A → A → A"))
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", typ("(A → A → A) → (num → A) → (num → A) → num → A"))
	scope.ConstMetas["zz_one"] = core.MakeConstMeta("zz_one", typ("zz_ops(A) → A"))
	scope.ConstMetas["zz_delta"] = core.MakeConstMeta("zz_delta", typ("A → A → D → D → A"))
	scope.ConstMetas["zz_eval"] = core.MakeConstMeta("zz_eval", typ("(A → A → A) → A → (A → A → A) → A → (num → A) → A → A"))
	syntax := scope.Syntax.(structFieldsSyntax)
	syntax.structs["zz_ops"].Fields = append(syntax.structs["zz_ops"].Fields, StructField{Name: "one", Const: "zz_one"})
	scope.Syntax = repeatedPrefixSyntax{implicitStructFieldsSyntax{syntax}}
	const two = "∀S:zz_ops(A). ∀T:zz_ops(B). "
	for _, tc := range []struct{ short, full string }{
		{two + "∀x:A. zz_derived(x, x) = S.e", two + "∀x:A. zz_derived(S.op, x, x) = S.e"},
		{two + "∀y:B. zz_derived(y, y) = T.e", two + "∀y:B. zz_derived(T.op, y, y) = T.e"},
		{two + "∀x:A. ∀y:B. zz_derived(x, x) = x ∧ zz_derived(y, y) = y",
			two + "∀x:A. ∀y:B. zz_derived(S.op, x, x) = x ∧ zz_derived(T.op, y, y) = y"},
		{"S:zz_ops(A), T:zz_ops(B), y:B ⊢ zz_derived(y, y) = y", "S:zz_ops(A), T:zz_ops(B), y:B ⊢ zz_derived(T.op, y, y) = y"},
		// The head's instance annotation is a type the text fixes.
		{two + "∀x:D. zz_delta⟨A:B⟩(x, x) = T.e", two + "∀x:D. zz_delta(T.e, T.one, x, x) = T.e"},
		{two + "∀P:(num → B). ∀y:B. zz_eval(P, y) = y", two + "∀P:(num → B). ∀y:B. zz_eval(T.op, T.e, T.op, T.e, P, y) = y"},
		{two + "∀u v:(num → A). u + v = v + u", two + "∀u v:(num → A). zz_pointwise(S.op, u, v) = zz_pointwise(S.op, v, u)"},
		{two + "∀u v:(num → B). u + v = v + u", two + "∀u v:(num → B). zz_pointwise(T.op, u, v) = zz_pointwise(T.op, v, u)"},
		// A big operator folds at the operation on its carrier.
		{two + "∀s:set(num). ∀f:(num → num → B). Σ_{i∈s} f(i) = f(0)",
			two + "∀s:set(num). ∀f:(num → num → B). iterated_op(zz_pointwise(T.op), s, λi:num. f(i)) = f(0)"},
	} {
		assertSameProp(t, scope, tc.short, tc.full)
	}
	for _, text := range []string{
		"∀S T:zz_ops(A). ∀x:A. zz_derived(x, x) = x",
		"∀S T:zz_ops(A). ∀u v:(num → A). u + v = v + u",
		two + "∀x:D. zz_delta(x, x) = T.e",
		two + "zz_derived = zz_derived",
	} {
		res := ParsePropTextInScope(text, scope)
		require.NotEmpty(t, res.Errors, text)
		require.Contains(t, res.Errors[0].Message, "more than one record", text)
	}
}

// repeatedPrefixSyntax declares zz_eval's prefix with each name twice,
// as polynomial_eval's add and mul read one record's fields.
type repeatedPrefixSyntax struct{ SyntaxTable }

func (s repeatedPrefixSyntax) ConstSyntax(name string) *ConstSyntax {
	if name == "zz_eval" {
		return &ConstSyntax{Implicit: []string{"op", "e", "op", "e"}}
	}
	return s.SyntaxTable.ConstSyntax(name)
}

// An operand that holds a record field is not the operation it holds:
// `zz_fadd(zz_fzero(S.e), u)` is the short pointwise sum of the zero
// function and u, since zz_fzero(S.e), a function of D, cannot be the
// operation on A the explicit reading would take it for. An operation
// built from a field still spells the prefix.
func TestStructFields_OperandHoldingAFieldIsNoOperation(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType { ty, err := ParseTypeText(text); require.NoError(t, err); return ty }
	scope.ConstMetas["zz_fadd"] = core.MakeConstMeta("zz_fadd", typ("(A → A → A) → (D → A) → (D → A) → D → A"))
	scope.ConstMetas["zz_fzero"] = core.MakeConstMeta("zz_fzero", typ("A → D → A"))
	scope.Syntax = implicitStructFieldsSyntax{scope.Syntax}
	// Every door freshens a constant's letters, so two occurrences of
	// zz_fadd read at two instances.
	scope.FreshenMetaLetters = true
	for _, tc := range []struct{ short, full string }{
		{"∀S:zz_ops(A). ∀u:(D → A). zz_fadd(zz_fzero(S.e), u) = u",
			"∀S:zz_ops(A). ∀u:(D → A). zz_fadd(S.op, zz_fzero(S.e), u) = u"},
		{"∀S:zz_ops(B). ∀R:zz_ops(A). ∀u:(D → B). zz_fadd(zz_fzero(S.e), u) = u",
			"∀S:zz_ops(B). ∀R:zz_ops(A). ∀u:(D → B). zz_fadd(S.op, zz_fzero(S.e), u) = u"},
		{"∀S:zz_ops(A). ∀u v:(D → A). zz_fadd(zz_fadd(u, v), u) = u",
			"∀S:zz_ops(A). ∀u v:(D → A). zz_fadd(S.op, zz_fadd(S.op, u, v), u) = u"},
	} {
		assertSameProp(t, scope, tc.short, tc.full)
	}
	// An operation built from a field is the prefix it spells: the sum
	// of functions of D at the pointwise sum of functions of num, which
	// a prefix put in front would leave one argument too many.
	res := ParsePropTextInScope("∀S:zz_ops(A). ∀u v:(D → num → A). zz_fadd(zz_fadd(S.op), u, v) = u", scope)
	require.Empty(t, res.Errors)
}

func TestStructFields_ExplicitPrefixAtOtherComponents(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType { ty, err := ParseTypeText(text); require.NoError(t, err); return ty }
	scope.ConstMetas["zz_one"] = core.MakeConstMeta("zz_one", typ("zz_ops(A) → A"))
	scope.ConstMetas["zz_delta"] = core.MakeConstMeta("zz_delta", typ("A → A → D → D → A"))
	syntax := scope.Syntax.(structFieldsSyntax)
	syntax.structs["zz_ops"].Fields = append(syntax.structs["zz_ops"].Fields, StructField{Name: "one", Const: "zz_one"})
	scope.Syntax = implicitStructFieldsSyntax{syntax}
	// The second component deliberately differs from the default. The
	// result type has already been pinned to rigid A, so a short reading
	// cannot apply it to an extra argument.
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀a:A. ∀x:D. zz_delta(S.e, a, x) = zz_delta(S.e, a, x)",
		"∀S:zz_ops(A). ∀a:A. ∀x:D. zz_delta(zz_e(S), a, x) = zz_delta(zz_e(S), a, x)")
	res := ParsePropTextInScope("∀S T:zz_ops(A). ∀x:D. zz_delta(S.e, S.one, x) = zz_delta(T.e, T.one, x)", scope)
	require.Empty(t, res.Errors)
	res = ParsePropTextInScope("∀S T:zz_ops(A). ∀a:A. ∀x:D. zz_delta(S.e, a, x) = zz_delta(T.e, a, x)", scope)
	require.Empty(t, res.Errors)
}

func TestStructFields_LocalRecordsShadowInstanceComponents(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType { ty, err := ParseTypeText(text); require.NoError(t, err); return ty }
	scope.ConstMetas["zz_derived"] = core.MakeConstMeta("zz_derived", typ("(A → A → A) → A → A → A"))
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", typ("(A → A → A) → (num → A) → (num → A) → num → A"))
	scope.ConstMetas["zz_default_op"] = core.MakeConstMeta("zz_default_op", typ("num → num → num"))
	scope.ImplicitBindings = map[string]core.Term{"op": scope.ConstMetas["zz_default_op"].Term()}
	scope.Syntax = implicitStructFieldsSyntax{scope.Syntax}
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀x:A. zz_derived(x, x) = S.e",
		"∀S:zz_ops(A). ∀x:A. zz_derived(S.op, x, x) = S.e")
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀u v:(num → A). u + v = v + u",
		"∀S:zz_ops(A). ∀u v:(num → A). zz_pointwise(S.op, u, v) = zz_pointwise(S.op, v, u)")
	res := ParsePropTextInScope("∀S T:zz_ops(A). ∀x:A. zz_derived(x, x) = x", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "more than one record")
	// A binder can shadow the projection's constant name. It then
	// denotes an ordinary operand, so the implicit operation is added.
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀zz_op:(zz_ops(A) → A). ∀x:A. zz_derived(zz_op(S), x) = x",
		"∀S:zz_ops(A). ∀f:(zz_ops(A) → A). ∀x:A. zz_derived(f(S), x) = x")
}

func TestStructFields_ExplicitPrefixWithDifferentFieldName(t *testing.T) {
	scope := structFieldsTestScope(t)
	ty, err := ParseTypeText("(A → A → A) → (num → A) → (num → A) → num → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", ty)
	syntax := scope.Syntax.(structFieldsSyntax)
	syntax.structs["zz_ops"].Fields = append(syntax.structs["zz_ops"].Fields, StructField{Name: "smul", Const: "zz_op"})
	scope.Syntax = implicitStructFieldsSyntax{syntax}
	// Explicit record operations may have another name, even when the
	// default implicit component is ambiguous among several records.
	res := ParsePropTextInScope("∀S T:zz_ops(A). zz_pointwise(S.smul) = zz_pointwise(T.smul)", scope)
	require.Empty(t, res.Errors)
	assertSameProp(t, scope,
		"∀S T:zz_ops(A). zz_pointwise(S.smul) = zz_pointwise(T.smul)",
		"∀S T:zz_ops(A). zz_pointwise(zz_op(S)) = zz_pointwise(zz_op(T))")
	ty, err = ParseTypeText("(A → A → A) → A → set(A) → set(A)")
	require.NoError(t, err)
	scope.ConstMetas["zz_coset"] = core.MakeConstMeta("zz_coset", ty)
	ty, err = ParseTypeText("(A → A → A) → (D → A) → (D → A) → D → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_lift"] = core.MakeConstMeta("zz_lift", ty)
	// A lifted operation explicitly chooses its component even when
	// the surrounding scope has several possible default operations.
	assertSameProp(t, scope,
		"∀S T:zz_ops(A). ∀u:(num → A). ∀s:set(num → A). zz_coset(zz_lift⟨D:num⟩(S.smul), u, s) = s",
		"∀S T:zz_ops(A). ∀u:(num → A). ∀s:set(num → A). zz_coset(zz_lift⟨D:num⟩(zz_op(S)), u, s) = s")
	ty, err = ParseTypeText("A → (num → A) → num")
	require.NoError(t, err)
	scope.ConstMetas["zz_measure"] = core.MakeConstMeta("zz_measure", ty)
	// An ordinary operand can contain fields too. This derived function
	// is the measured operand; the implicit identity still comes first.
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀u:(num → A). zz_measure(zz_lift⟨D:num⟩(S.op, u, u)) = 0",
		"∀S:zz_ops(A). ∀u:(num → A). zz_measure(S.e, zz_lift⟨D:num⟩(S.op, u, u)) = 0")
}

func (s structFieldsSyntax) ConstMeta(name string) core.ConstTermMeta { return s.metas[name] }
func (s structFieldsSyntax) StructSyntax(name string) *StructSyntax   { return s.structs[name] }

// structFieldsTestScope declares a toy structure type zz_ops(A) — an
// operation `op` carrying `+`, an identity `e`, an inverse `inv`
// carrying the prefix `-` — read off a value by the projections zz_op,
// zz_e and zz_inv.
func structFieldsTestScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := structureTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	scope.ConstMetas["zz_op"] = core.MakeConstMeta("zz_op", typ("zz_ops(A) → A → A → A"))
	scope.ConstMetas["zz_e"] = core.MakeConstMeta("zz_e", typ("zz_ops(A) → A"))
	scope.ConstMetas["zz_inv"] = core.MakeConstMeta("zz_inv", typ("zz_ops(A) → A → A"))
	scope.ConstMetas["zz_record"] = core.MakeConstMeta("zz_record", typ("zz_ops(num)"))
	scope.Syntax = structFieldsSyntax{SyntaxTable: scope.Syntax, metas: scope.ConstMetas, structs: map[string]*StructSyntax{"zz_ops": {Fields: []StructField{
		{Name: "op", Const: "zz_op", Symbol: "+", Arity: 2},
		{Name: "e", Const: "zz_e"},
		{Name: "inv", Const: "zz_inv", Symbol: "-", Arity: 1},
	}}}}
	return scope
}

// Under a binder of the type, a field reads as the projection applied
// to the variable and a symbol as the operation field applied to the
// operands; the same under a declared variable of a goal.
func TestStructFields_Parse(t *testing.T) {
	scope := structFieldsTestScope(t)
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀x y:A. x + y = S.e ∧ -x = S.inv(y)",
		"∀S:zz_ops(A). ∀x y:A. zz_op(S)(x, y) = zz_e(S) ∧ zz_inv(S)(x) = zz_inv(S)(y)")
	assertSameProp(t, scope,
		"S:zz_ops(A), x:A ⊢ x + x = S.e",
		"S:zz_ops(A), x:A ⊢ zz_op(S)(x, x) = zz_e(S)")
	// Two values at two carriers each take their own symbol, by the
	// operands' types.
	assertSameProp(t, scope,
		"∀S:zz_ops(A). ∀T:zz_ops(B). ∀x:A. ∀y:B. x + x = S.e ∧ y + y = T.e",
		"∀S:zz_ops(A). ∀T:zz_ops(B). ∀x:A. ∀y:B. zz_op(S)(x, x) = zz_e(S) ∧ zz_op(T)(y, y) = zz_e(T)")
	// A field the type does not declare is refused, naming the fields.
	res := ParsePropTextInScope("∀S:zz_ops(A). S.unit = S.unit", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "has no field unit; the fields of zz_ops are op, e, inv")
	// Two values at one carrier are two structures at one signature.
	res = ParsePropTextInScope("∀S T:zz_ops(A). ∀x:A. x + x = S.e", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "bound by two structures")
	// A text with no binder of the type sees no symbol.
	res = ParsePropTextInScope("∀x y:A. x + y = y + x", scope)
	require.NotEmpty(t, res.Errors)
}

// The chapter spelling writes a projection at a variable of the type
// back as the field, and an unambiguous operation field applied at its
// arity as the operator; the result reads back to the same statement.
func TestStructFields_ChapterSpelling(t *testing.T) {
	scope := structFieldsTestScope(t)
	for _, tc := range []struct{ raw, want string }{
		{"∀S:zz_ops(A). ∀x y:A. zz_op(S)(x, y) = zz_e(S) ∧ zz_inv(S)(x) = zz_inv(S)(y)",
			"∀S:zz_ops(A). ∀x y:A. x + y = S.e ∧ -x = -y"},
		{"∀S:zz_ops(A). ∀T:zz_ops(B). ∀x:A. ∀y:B. zz_op(S)(x, x) = zz_e(S) ∧ zz_op(T)(y, y) = zz_e(T)",
			"∀S:zz_ops(A). ∀T:zz_ops(B). ∀x:A. ∀y:B. x + x = S.e ∧ y + y = T.e"},
		{"S:zz_ops(A), x:A ⊢ zz_op(S)(x, x) = zz_e(S)",
			"S : zz_ops(A), x : A ⊢ x + x = S.e"},
		// The printers write a curried application flat.
		{"∀S:zz_ops(A). ∀x y:A. zz_op(S, x, y) = zz_e(S)",
			"∀S:zz_ops(A). ∀x y:A. x + y = S.e"},
		// Two records at the same carrier must retain their owners.
		{"∀S T:zz_ops(A). ∀x y:A. zz_op(S, x, y) = zz_op(T, y, x) ∧ zz_inv(S, x) = zz_inv(T, y)",
			"∀S T:zz_ops(A). ∀x y:A. S.op(x, y) = T.op(y, x) ∧ S.inv(x) = T.inv(y)"},
		{"S:zz_ops(A), T:zz_ops(A), x:A ⊢ zz_op(S, x, x) = zz_op(T, x, x)",
			"S : zz_ops(A), T : zz_ops(A), x : A ⊢ S.op(x, x) = T.op(x, x)"},
		// Intrinsic arithmetic retains its meaning beside record fields.
		{"∀S:zz_ops(num). ∀x y:num. zz_op(S, x, y) = x + y",
			"∀S:zz_ops(num). ∀x y:num. S.op(x, y) = x + y"},
		{"∀S:zz_ops(int). ∀x:int. zz_inv(S, x) = -x",
			"∀S:zz_ops(int). ∀x:int. S.inv(x) = -x"},
		{"∀S:zz_ops(real). ∀x y:real. zz_op(S, x, y) = x + y ∧ zz_inv(S, x) = -y",
			"∀S:zz_ops(real). ∀x y:real. S.op(x, y) = x + y ∧ S.inv(x) = -y"},
		// A nested binder shadows the outer record without disabling it
		// after leaving that binder.
		{"∀S:zz_ops(A). ∀x:A. (∀S:zz_ops(B). ∀y:B. zz_op(S, y, y) = zz_e(S)) ∧ zz_op(S, x, x) = zz_e(S)",
			"∀S:zz_ops(A). ∀x:A. (∀S:zz_ops(B). ∀y:B. y + y = S.e) ∧ x + x = S.e"},
		// A binder named like a projection stays a variable application.
		{"∀S:zz_ops(A). ∀zz_e:(zz_ops(A) → A). zz_e(S) = zz_e(S)",
			"∀S:zz_ops(A). ∀zz_e:(zz_ops(A) → A). zz_e(S) = zz_e(S)"},
		{"(∀S:zz_ops(A). ∀x:A. zz_op(S, x, x) = x) ∧ (∀S:(A → A → A). ∀x:A. S(x, x) = x)",
			"(∀S:zz_ops(A). ∀x:A. x + x = x) ∧ (∀S:(A → A → A). ∀x:A. S(x, x) = x)"},
		{"∀f:(A → zz_ops(A)). ∀x:A. zz_e(f(x)) = x",
			"∀f:(A → zz_ops(A)). ∀x:A. f(x).e = x"},
		{"∀P:(num → zz_ops(A)). ∀n:num. ∀x y:A. zz_op(P(n), x, y) = zz_e(P(n))",
			"∀P:(num → zz_ops(A)). ∀n:num. ∀x y:A. P(n).op(x, y) = P(n).e"},
		{"∀S:zz_ops(zz_ops(A)). zz_e(zz_e(S)) = zz_e(zz_e(S))",
			"∀S:zz_ops(zz_ops(A)). S.e.e = S.e.e"},
		{"∀S:zz_ops(zz_ops(A)). ∀x:zz_ops(A). zz_e(zz_inv(S, x)) = zz_e(x)",
			"∀S:zz_ops(zz_ops(A)). ∀x:zz_ops(A). (-x).e = x.e"},
		{"zz_op(zz_record, 1, 2) = zz_e(zz_record)",
			"zz_record.op(1, 2) = zz_record.e"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		assertSameProp(t, scope, out, tc.raw)
		again, err := ChapterSpelling(out, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, out, again)
	}
}

// A constant's polymorphic letter must not capture a declared carrier while
// probing whether a record field can be displayed as an operator.
func TestStructFields_OperatorProbeKeepsCarrierLettersRigid(t *testing.T) {
	scope := structFieldsTestScope(t)
	ty, err := ParseTypeText("(A → A → A) → (num → A) → (num → A) → num → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", ty)
	scope.Syntax = implicitStructFieldsSyntax{scope.Syntax}
	scope.FreshenMetaLetters = true
	const raw = "∀op:(A → A → A). ∀S:zz_ops(num → B). ∀u v:(num → B). zz_op(S, u, v) = zz_op(S, v, u)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "u + v")
	assertSameProp(t, scope, out, raw)
	again, err := ChapterSpelling(out, scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, out, again)
}

func TestStructFields_StructureOperatorProbeKeepsCarrierLettersRigid(t *testing.T) {
	scope := structFieldsTestScope(t)
	ty, err := ParseTypeText("(A → A → A) → (num → A) → (num → A) → num → A")
	require.NoError(t, err)
	scope.ConstMetas["zz_pointwise"] = core.MakeConstMeta("zz_pointwise", ty)
	declareStructure(t, scope, "zz_additive", "(A → A → A) → bool", []StructureComponent{{Symbol: "+", Arity: 2}})
	scope.Syntax = implicitStructFieldsSyntax{scope.Syntax}
	scope.FreshenMetaLetters = true
	const raw = "∀op:(A → A → A). ∀add:((num → B) → (num → B) → num → B). zz_additive(add) ⇒ ∀u v:(num → B). add(u, v) = add(v, u)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "u + v")
	assertSameProp(t, scope, out, raw)
	again, err := ChapterSpelling(out, scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, out, again)
}

// A structure fact over a record's fields, `zz_abel(S.op, S.e, S.inv)`,
// binds its symbol to the field, and the parser reads that symbol back
// through the record's own field only: `+` is op's own symbol and folds
// where the field fold cannot (under a set-builder's unannotated
// binder), and a group's `*` on S.op never folds, in a typed text or in
// a display whose record is an untyped Skolem.
func TestStructFields_StructureFactOnAField(t *testing.T) {
	scope := structFieldsTestScope(t)
	for name, symbol := range map[string]string{"zz_abel": "+", "zz_mgrp": "*"} {
		declareStructure(t, scope, name, "(A → A → A) → A → (A → A) → bool", []StructureComponent{
			{Symbol: symbol, Arity: 2}, {}, {Symbol: "-", Arity: 1},
		})
	}
	for _, tc := range []struct{ raw, want string }{
		{"∀S:zz_ops(A). ∀x:A. zz_abel(S.op, S.e, S.inv) ⇒ {S.op(x, a) | a:A | a = x} = {S.op(a, x) | a:A | a = x}",
			"∀S:zz_ops(A). ∀x:A. zz_abel(S.op, S.e, S.inv) ⇒ {x + a | a:A | a = x} = {a + x | a:A | a = x}"},
		{"∀S:zz_ops(A). ∀x:A. zz_mgrp(S.op, S.e, S.inv) ⇒ {S.op(x, a) | a:A | a = x} = {S.op(a, x) | a:A | a = x}",
			"∀S:zz_ops(A). ∀x:A. zz_mgrp(S.op, S.e, S.inv) ⇒ {S.op(x, a) | a:A | a = x} = {S.op(a, x) | a:A | a = x}"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		assertSameProp(t, scope, out, tc.raw)
	}
	display := "zz_mgrp(S_0.op, S_0.e, S_0.inv) ⊢ ∀x.∀y.(S_0.op(x, y) = S_0.op(y, x))"
	require.Equal(t, "zz_mgrp(S₀.op, S₀.e, S₀.inv) ⊢ ∀x y. S₀.op(x, y) = S₀.op(y, x)",
		DisplaySpelling(display, scope.Syntax, nil))
}

func TestStructFields_ExpressionReceiver(t *testing.T) {
	scope := structFieldsTestScope(t)
	for _, tc := range []struct{ short, full string }{
		{"∀P:(num → zz_ops(A)). ∀n:num. ∀x y:A. P(n).op(x, y) = P(n).e",
			"∀P:(num → zz_ops(A)). ∀n:num. ∀x y:A. zz_op(P(n))(x, y) = zz_e(P(n))"},
		{"∀P:(num → zz_ops(A)). ∀n:num. ∀x:A. P(n).op(x) = P(n).op(x)",
			"∀P:(num → zz_ops(A)). ∀n:num. ∀x:A. zz_op(P(n))(x) = zz_op(P(n))(x)"},
		{"∀P:(num → zz_ops(A)). ∀n:num. P(n).op = P(n).op",
			"∀P:(num → zz_ops(A)). ∀n:num. zz_op(P(n)) = zz_op(P(n))"},
		{"∀P:(num → zz_ops(A)). ∀n:num. (λi:num. P(i))(n).e = P(n).e",
			"∀P:(num → zz_ops(A)). ∀n:num. zz_e((λi:num. P(i))(n)) = zz_e(P(n))"},
		{"∀S:zz_ops(zz_ops(A)). S.e.e = S.e.e",
			"∀S:zz_ops(zz_ops(A)). zz_e(zz_e(S)) = zz_e(zz_e(S))"},
		{"∀S:zz_ops(zz_ops(A)). ∀f:(A → A). f S.e.e = S.e.e",
			"∀S:zz_ops(zz_ops(A)). ∀f:(A → A). f(zz_e(zz_e(S))) = zz_e(zz_e(S))"},
		{"∀P:(num → zz_ops(A)). ∀n:num. ∀f:(A → A). f(P(n).e) = P(n).e",
			"∀P:(num → zz_ops(A)). ∀n:num. ∀f:(A → A). f(zz_e(P(n))) = zz_e(P(n))"},
	} {
		assertSameProp(t, scope, tc.short, tc.full)
		out, err := ChapterSpelling(tc.full, scope.Syntax, nil)
		require.NoError(t, err)
		assertSameProp(t, scope, out, tc.full)
	}
	for _, tc := range []struct{ text, diagnostic string }{
		{"∀P:(num → zz_ops(A)). ∀n:num. P(n).unit = P(n).e", "has no field unit; the fields of zz_ops are op, e, inv"},
		{"∀P:(num → num). ∀n:num. P(n).e = n", "receiver type num declares no record fields"},
	} {
		res := ParsePropTextInScope(tc.text, scope)
		require.NotEmpty(t, res.Errors, tc.text)
		require.Contains(t, res.Errors[0].Message, tc.diagnostic)
	}
}

// A declared vector operator wins when its implicit component is in
// scope. When it is absent, the record field supplies the symbol.
func TestStructFields_DeclaredOperatorSpelling(t *testing.T) {
	scope := structFieldsTestScope(t)
	scope.ImplicitBindings = nil
	for _, tc := range []struct{ raw, want string }{
		{"∀S:zz_ops(num → A). ∀u v:(num → A). zz_op(S, u, v) = zz_op(S, v, u)",
			"∀S:zz_ops(num → A). ∀u v:(num → A). u + v = v + u"},
		{"∀add:(A → A → A). ∀S:zz_ops(num → A). ∀u v:(num → A). zz_op(S, u, v) = zz_op(S, v, u)",
			"∀add:(A → A → A). ∀S:zz_ops(num → A). ∀u v:(num → A). S.op(u, v) = S.op(v, u)"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		assertSameProp(t, scope, out, tc.raw)
	}
}

func TestStructFields_RecordResidentAliases(t *testing.T) {
	scope := chapterImplicitRecordScope(t)
	record, err := ParseTypeText("zz_ops(A)")
	require.NoError(t, err)
	scope.Vars = map[string]core.HolType{"S": record, "S_0": record}
	scope.ResidentNames = map[string]string{"S_0": "S"}
	assertSameProp(t, scope,
		"∀x:A. x + x = x",
		"∀x:A. zz_op(S, x, x) = x")
	assertSameProp(t, scope,
		"∀x:A. zz_derived(x, x) = x",
		"∀x:A. zz_derived(S.op, x, x) = x")
	assertSameProp(t, scope,
		"∀u v:(num → A). u + v = v + u",
		"∀u v:(num → A). zz_pointwise(S.op, u, v) = zz_pointwise(S.op, v, u)")
	for _, text := range []string{
		"∀S:zz_ops(A). ∀x:A. zz_derived(x, x) = x",
		"∀S:zz_ops(A). ∀u v:(num → A). u + v = v + u",
	} {
		res := ParsePropTextInScope(text, scope)
		require.NotEmpty(t, res.Errors, "a binder shadowing the surface alias is a second record: %s", text)
		require.Contains(t, res.Errors[0].Message, "more than one record")
	}
	shadowedScalar := ParsePropTextInScope("∀S:zz_ops(A). ∀x:A. x + x = x", scope)
	require.NotEmpty(t, shadowedScalar.Errors)
	require.Contains(t, shadowedScalar.Errors[0].Message, "two structures")
	vec, err := ParseTypeText("num → A")
	require.NoError(t, err)
	ctx := map[string]core.HolType{"u": vec, "v": vec}
	short := ParseTermTextInScope("u + v", ctx, scope, vec)
	full := ParseTermTextInScope("zz_pointwise(S.op, u, v)", ctx, scope, vec)
	require.Empty(t, short.Errors)
	require.Empty(t, full.Errors)
	require.True(t, short.Term.AlphaEquals(full.Term))
	scope.Vars["T"] = record
	res := ParsePropTextInScope("∀x:A. zz_derived(x, x) = x", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "more than one record")
}

// A field application types its arguments at the field's domains, as
// the projection applied to the record and the arguments does: under a
// declared record, binders nothing else types read at the carrier, an
// operator over binders the field application types reads as the
// record's field, and an argument applying an undeclared function
// takes its result type from the field.
func TestStructFields_FieldApplicationTypesItsArguments(t *testing.T) {
	scope := structFieldsTestScope(t)
	record, err := ParseTypeText("zz_ops(A)")
	require.NoError(t, err)
	scope.Vars = map[string]core.HolType{"S": record}
	for _, tc := range []struct{ short, full string }{
		{"∀x y. S.op(x, y) = S.op(y, x)", "∀x y:A. zz_op(S, x, y) = zz_op(S, y, x)"},
		{"∀x y. zz_op(S)(x, y) = zz_op(S)(y, x)", "∀x y:A. zz_op(S, x, y) = zz_op(S, y, x)"},
		{"∀x y. x + y = y ∧ S.op(x, y) = x", "∀x y:A. zz_op(S, x, y) = y ∧ zz_op(S, x, y) = x"},
		{"∀f x. S.op(f(x), x) = x", "∀f:(A → A). ∀x:A. zz_op(S, f(x), x) = x"},
		{"∀P:(num → zz_ops(A)). ∀n:num. ∀x y. P(n).op(x, y) = P(n).e",
			"∀P:(num → zz_ops(A)). ∀n:num. ∀x y:A. zz_op(P(n), x, y) = zz_e(P(n))"},
	} {
		assertSameProp(t, scope, tc.short, tc.full)
	}
}

// A display declares nothing. A record it shows — the receiver of a
// projection, the subject of a predicate on records — prints a field
// under its symbol where that field alone holds the symbol at its
// arity, and the display reads back where a session declares its free
// variables. A symbol two records hold, or a record's field and a
// structure fact's component, is printed for neither; a record an
// untyped binder binds, or a constant, keeps its field spelled. In a
// typed text a record left undeclared still holds its symbols: the
// declared record beside it is not folded either.
func TestStructFields_DisplayFoldsAFieldHeldAlone(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	scope.ConstMetas["zz_pred"] = core.MakeConstMeta("zz_pred", typ("zz_ops(A) → bool"))
	declareStructure(t, scope, "zz_abel", "(A → A → A) → A → (A → A) → bool", []StructureComponent{
		{Symbol: "+", Arity: 2}, {}, {Symbol: "-", Arity: 1},
	})
	for _, tc := range []struct{ raw, want string }{
		{"⊢ (zz_op(S, x, y) = zz_op(S, y, x)) ∧ (zz_inv(S, x) = zz_e(S))", "⊢ x + y = y + x ∧ -x = S.e"},
		{"⊢ zz_op(S, x, y) = zz_op(T, y, x)", "⊢ S.op(x, y) = T.op(y, x)"},
		{"zz_pred(T) ⊢ zz_op(S, x, y) = x", "zz_pred(T) ⊢ S.op(x, y) = x"},
		{"zz_abel(add, zero, neg) ⊢ add(x, x) = zz_op(S, x, x)", "zz_abel(add, zero, neg) ⊢ add(x, x) = S.op(x, x)"},
		{"⊢ ∀S.(zz_op(S, x, y) = x)", "⊢ ∀S. S.op(x, y) = x"},
		{"⊢ zz_op(zz_record, 1, 2) = zz_e(zz_record)", "⊢ zz_record.op(1, 2) = zz_record.e"},
	} {
		require.Equal(t, tc.want, DisplaySpelling(tc.raw, scope.Syntax, nil), tc.raw)
	}
	scope.Vars = map[string]core.HolType{"S": typ("zz_ops(A)"), "x": typ("A"), "y": typ("A")}
	assertSameProp(t, scope, "x + y = y + x ∧ -x = S.e", "zz_op(S, x, y) = zz_op(S, y, x) ∧ zz_inv(S, x) = zz_e(S)")
	out, err := ChapterSpelling("S:zz_ops(A), x:A ⊢ zz_op(S, x, x) = zz_op(T, x, x)", scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, "S : zz_ops(A), x : A ⊢ S.op(x, x) = T.op(x, x)", out)
}

// A registered constant of a record type keeps its fields under a
// structure fact whose subject it is — `comm_ring_on(int_ring) ⇒
// … int_ring.add …`, stated in the text or resident — where the
// fact makes the constant a bundle's component, not a variable; a
// binder of the constant's name shadows it, and the field is then the
// bundle's component, which the structure does not have.
func TestStructFields_ConstantSubjectOfAStructureFactKeepsItsFields(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	scope.ConstMetas["zz_struct"] = core.MakeConstMeta("zz_struct", typ("zz_ops(A) → bool"))
	testTable(scope)["zz_struct"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: []BundleParam{{Name: "R", Type: typ("zz_ops(A)")}}, Structure: true, Subject: 0,
			Layouts: []BundleLayout{{Structure: "zz_struct", Slots: []int{0}}}}}
	assertSameProp(t, scope,
		"zz_struct(zz_record) ⇒ zz_record.e = zz_record.e",
		"zz_struct(zz_record) ⇒ zz_e(zz_record) = zz_e(zz_record)")
	fact := ParsePropTextInScope("zz_struct(zz_record)", scope)
	require.Empty(t, fact.Errors)
	resident := *scope
	resident.ResidentFacts = []core.Term{fact.Prop.Conclusion()}
	assertSameProp(t, &resident, "zz_record.e = zz_record.e", "zz_e(zz_record) = zz_e(zz_record)")
	res := ParsePropTextInScope("∀zz_record. zz_struct(zz_record) ⇒ zz_record.e = zz_record.e", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "zz_record has no component e; the components of zz_struct are R")
}
