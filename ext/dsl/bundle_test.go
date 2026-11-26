package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// bundleTestScope declares a toy tower: a ring on a set zz_cring(add,
// zero, neg, mul, one, sub, c), a module over it zz_mod(…, add', zero',
// neg', smul, R, M) whose definition states the ring, a module
// homomorphism zz_hom(add', smul, add”, smul', R, M, M', f) declaring
// its two module layouts, a ring homomorphism zz_rhom(<ring>, <ring>', c,
// c', f) declaring its two ring layouts, and the tuple zz_lift(I) of the
// pointwise operations at the index type I.
func bundleTestScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := structureTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	ring := "(A → A → A) → A → (A → A) → (A → A → A) → A → (A → A → A) → "
	ringB := "(B → B → B) → B → (B → B) → (B → B → B) → B → (B → B → B) → "
	consts := map[string]string{
		"zz_cring":  ring + "(A → bool) → bool",
		"zz_mod":    ring + "(B → B → B) → B → (B → B) → (A → B → B) → (A → bool) → (B → bool) → bool",
		"zz_hom":    "(B → B → B) → (A → B → B) → (C → C → C) → (A → C → C) → (A → bool) → (B → bool) → (C → bool) → (B → C) → bool",
		"zz_rhom":   ring + ringB + "(A → bool) → (B → bool) → (A → B) → bool",
		"zz_fadd":   "(C → C → C) → (D → C) → (D → C) → D → C",
		"zz_fzero":  "C → D → C",
		"zz_fneg":   "(C → C) → (D → C) → D → C",
		"zz_fsmul":  "(A → C → C) → A → (D → C) → D → C",
		"zz_P":      "(B → C) → bool",
		"zz_grp":    "(B → B → B) → B → (B → B) → (B → bool) → bool",
		"zz_metric": "(A → bool) → (A → A → real) → bool",
		"zz_cmap":   "((A → bool) → bool) → ((B → bool) → bool) → (A → B) → bool",
		"zz_cxs":    "(B → B → B) → (num → B → bool) → (num → B → B) → bool",
		"zz_ch":     "(B → B → B) → (num → B → bool) → (num → B → B) → (num → B → bool) → (num → B → B) → num → B → B",
		"zz_tw":     ring + "(B → B → B) → (A → B → B) → (A → bool) → (B → bool) → B → bool",
		"zz_pair":   "(B → B → B) → (C → C → C) → (num → B → bool) → (num → B → B) → (num → C → bool) → (num → C → C) → bool",
	}
	for name, ty := range consts {
		scope.ConstMetas[name] = core.MakeConstMeta(name, typ(ty))
	}
	params := func(spec string) []BundleParam {
		var out []BundleParam
		for _, f := range strings.Split(spec, ";") {
			name, ty, _ := strings.Cut(strings.TrimSpace(f), ":")
			out = append(out, BundleParam{Name: name, Type: typ(ty)})
		}
		return out
	}
	ringParams := "add:A → A → A; zero:A; neg:A → A; mul:A → A → A; one:A; sub:A → A → A"
	ringParamsB := "add':B → B → B; zero':B; neg':B → B; mul':B → B → B; one':B; sub':B → B → B"
	syntax := testTable(scope)
	syntax["zz_cring"] = &ConstSyntax{StructurePredicate: true, Implicit: []string{"add", "zero", "neg", "mul", "one", "sub"},
		Bundle: &BundleSyntax{Params: params(ringParams + "; c:A → bool"), Structure: true, Subject: 6,
			Layouts: []BundleLayout{{Structure: "zz_cring", Slots: []int{0, 1, 2, 3, 4, 5, 6}}}}}
	syntax["zz_grp"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: params("mul:B → B → B; one:B; inv:B → B; c:B → bool"), Structure: true, Subject: 3,
			Layouts: []BundleLayout{{Structure: "zz_grp", Slots: []int{0, 1, 2, 3}}}}}
	// A metric space is named by its set, which comes first; a
	// continuous map by its map, which is no set.
	syntax["zz_metric"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: params("M:A → bool; d:A → A → real"), Structure: true, Subject: 0,
			Layouts: []BundleLayout{{Structure: "zz_metric", Slots: []int{0, 1}}}}}
	syntax["zz_cmap"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: params("T:(A → bool) → bool; S:(B → bool) → bool; f:A → B"), Structure: true, Subject: 2,
			Layouts: []BundleLayout{{Structure: "zz_cmap", Slots: []int{0, 1, 2}}}}}
	// A complex-like structure named by its modules P, and a map of
	// two complexes with the first's operation implicit.
	syntax["zz_cxs"] = &ConstSyntax{StructurePredicate: true, Implicit: []string{"op"},
		Bundle: &BundleSyntax{Params: params("op:B → B → B; P:num → B → bool; d:num → B → B"), Structure: true, Subject: 1,
			Layouts: []BundleLayout{{Structure: "zz_cxs", Slots: []int{0, 1, 2}}}}}
	syntax["zz_ch"] = &ConstSyntax{Implicit: []string{"op"},
		Bundle: &BundleSyntax{Params: params("op:B → B → B; P':num → B → bool; d':num → B → B; P:num → B → bool; d:num → B → B; n:num"), Subject: -1,
			Layouts: []BundleLayout{
				{Structure: "zz_cxs", Slots: []int{0, 1, 2}},
				{Structure: "zz_cxs", Slots: []int{-1, 3, 4}}}}}
	// The module's additive group sits on its carrier: the fact names
	// two bundles M, and the module is the one M stays.
	syntax["zz_mod"] = &ConstSyntax{StructurePredicate: true,
		Implicit: []string{"add", "zero", "neg", "mul", "one", "sub", "add'", "zero'", "neg'", "smul"},
		Bundle: &BundleSyntax{Params: params(ringParams + "; add':B → B → B; zero':B; neg':B → B; smul:A → B → B; R:A → bool; M:B → bool"),
			Structure: true, Subject: 11,
			Layouts: []BundleLayout{{Structure: "zz_mod", Slots: []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}},
				{Structure: "zz_cring", Slots: []int{0, 1, 2, 3, 4, 5, 10}},
				{Structure: "zz_grp", Slots: []int{6, 7, 8, 11}}}}}
	syntax["zz_hom"] = &ConstSyntax{Implicit: []string{"add'", "smul", "add''", "smul'"},
		Bundle: &BundleSyntax{Params: params("add':B → B → B; smul:A → B → B; add'':C → C → C; smul':A → C → C; R:A → bool; M:B → bool; M':C → bool; f:B → C"),
			Subject: -1,
			Layouts: []BundleLayout{
				{Structure: "zz_mod", Slots: []int{-1, -1, -1, -1, -1, -1, 0, -1, -1, 1, 4, 5}},
				{Structure: "zz_mod", Slots: []int{-1, -1, -1, -1, -1, -1, 2, -1, -1, 3, 4, 6}}}}}
	syntax["zz_rhom"] = &ConstSyntax{Implicit: []string{"add", "zero", "neg", "mul", "one", "sub", "add'", "zero'", "neg'", "mul'", "one'", "sub'"},
		Bundle: &BundleSyntax{Params: params(ringParams + "; " + ringParamsB + "; c:A → bool; c':B → bool; f:A → B"), Subject: -1,
			Layouts: []BundleLayout{
				{Structure: "zz_cring", Slots: []int{0, 1, 2, 3, 4, 5, 12}},
				{Structure: "zz_cring", Slots: []int{6, 7, 8, 9, 10, 11, 13}}}}}
	// zz_tw(<ring>, add', smul, R, M, u) takes a ring and a module over
	// it, the two layouts sharing the ring's components.
	syntax["zz_tw"] = &ConstSyntax{
		Bundle: &BundleSyntax{Params: params(ringParams + "; add':B → B → B; smul:A → B → B; R:A → bool; M:B → bool; u:B"), Subject: -1,
			Layouts: []BundleLayout{
				{Structure: "zz_cring", Slots: []int{0, 1, 2, 3, 4, 5, 8}},
				{Structure: "zz_mod", Slots: []int{0, 1, 2, 3, 4, 5, 6, -1, -1, 7, 8, 9}}}}}
	// Two complexes, a structure with no subject, folded under S.
	syntax["zz_pair"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: params("op:B → B → B; op':C → C → C; P:num → B → bool; d:num → B → B; Q:num → C → bool; e:num → C → C"),
			Structure: true, Subject: -1, Letter: "S",
			Layouts: []BundleLayout{{Structure: "zz_pair", Slots: []int{0, 1, 2, 3, 4, 5}},
				{Structure: "zz_cxs", Slots: []int{0, 2, 3}},
				{Structure: "zz_cxs", Slots: []int{1, 4, 5}}}}}
	syntax["zz_comp"] = &ConstSyntax{Tuple: &TupleSyntax{Params: []string{"h", "g"}, Terms: []string{"λu:B. h(g(u))"}}}
	syntax["zz_const"] = &ConstSyntax{Tuple: &TupleSyntax{Params: []string{"h", "y"}, Terms: []string{"λu:B. h(y)"}}}
	syntax["zz_lift"] = &ConstSyntax{Tuple: &TupleSyntax{Params: []string{"I"},
		Terms: []string{"zz_fadd⟨D:I⟩(add)", "zz_fzero⟨D:I⟩(zero)", "zz_fneg⟨D:I⟩(neg)", "zz_fsmul⟨D:I⟩(mul)"}}}
	// zz_lift with a subscripted parameter: its terms are normalized
	// before they are read, and so must its parameter be.
	syntax["zz_sublift"] = &ConstSyntax{Tuple: &TupleSyntax{Params: []string{"I₀"},
		Terms: []string{"zz_fadd⟨D:I₀⟩(add)", "zz_fzero⟨D:I₀⟩(zero)", "zz_fneg⟨D:I₀⟩(neg)", "zz_fsmul⟨D:I₀⟩(mul)"}}}
	syntax["zz_point"] = &ConstSyntax{Tuple: &TupleSyntax{Params: []string{"I", "X"},
		Terms: []string{"zz_fadd⟨D:I⟩(X.add')", "zz_fzero⟨D:I⟩(X.zero')", "zz_fneg⟨D:I⟩(X.neg')", "zz_fsmul⟨D:I⟩(X.smul)"}}}
	return scope
}

const zzRingModuleExplicit = "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). " +
	"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ " +
	"∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). ∀smul:(A → B → B). ∀M:(B → bool). " +
	"zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, M) ⇒ " +
	"∀N_add':(C → C → C). ∀N_zero':C. ∀N_neg':(C → C). ∀N_smul:(A → C → C). ∀N:(C → bool). " +
	"zz_mod(add, zero, neg, mul, one, sub, N_add', N_zero', N_neg', N_smul, R, N) ⇒ "

func sameBundleKey(t *testing.T, scope *ParseScope, bundled, explicit string) {
	t.Helper()
	a, b := parseImplicit(t, scope, bundled), parseImplicit(t, scope, explicit)
	require.Equal(t, b.AlphaKey(), a.AlphaKey(), "bundled ≠ explicit:\n  %s\n  %s", bundled, explicit)
}

// A bundle binder binds the components no bundle gives — named after
// the definition, primed until free, the carrier after the binder — and
// states the structure as the antecedent; a bundle argument lays its
// components out where the constant declares.
func TestBundle_BinderAndArgument(t *testing.T) {
	scope := bundleTestScope(t)
	sameBundleKey(t, scope,
		"∀R:zz_cring(A). ∀M:zz_mod(R, B). ∀N:zz_mod(R, C). ∀f:(B → C). zz_hom(M, N, f) ⇒ zz_P(f)",
		zzRingModuleExplicit+"∀f:(B → C). zz_hom(add', smul, N_add', N_smul, R, M, N, f) ⇒ zz_P(f)")
	// The module binder alone binds the ring's components too, the ring
	// carrier canonically R.
	sameBundleKey(t, scope,
		"∀M:zz_mod(A, B). ∀u:B. u ∈ M",
		"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). "+
			"∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). ∀smul:(A → B → B). ∀R:(A → bool). ∀M:(B → bool). "+
			"zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, M) ⇒ ∀u:B. u ∈ M")
	// ∃ states the conjunction.
	sameBundleKey(t, scope,
		"∀R:zz_cring(A). ∃M:zz_mod(R, B). ∀u:B. u ∈ M",
		"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). "+
			"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ "+
			"∃add':(B → B → B). ∃zero':B. ∃neg':(B → B). ∃smul:(A → B → B). ∃M:(B → bool). "+
			"zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, M) ∧ ∀u:B. u ∈ M")
	// A module given operation by operation fills the first layout, and
	// the bundle after it takes the second.
	sameBundleKey(t, scope,
		zzRingModuleExplicit+"∀S:(I → B) → bool. ∀g:((I → B) → C). zz_hom(zz_fadd⟨D:I⟩(add'), zz_fsmul⟨D:I⟩(smul), N, S, g) ⇒ ⊤",
		zzRingModuleExplicit+"∀S:(I → B) → bool. ∀g:((I → B) → C). zz_hom(zz_fadd⟨D:I⟩(add'), zz_fsmul⟨D:I⟩(smul), N_add', N_smul, R, S, N, g) ⇒ ⊤")
	// A bundle read off a spelled-out fact serves the same way.
	sameBundleKey(t, scope,
		zzRingModuleExplicit+"∀g:(C → B). zz_hom(N, M, g) ⇒ ⊤",
		zzRingModuleExplicit+"∀g:(C → B). zz_hom(N_add', N_smul, add', smul, R, N, M, g) ⇒ ⊤")
}

// The subject is the component the definition declares, at any
// position and of any type: the binder names it, the other components
// are minted after the definition, and the fold reads it back.
func TestBundle_SubjectAtAnyPosition(t *testing.T) {
	scope := bundleTestScope(t)
	metric := "∀M:(A → bool). ∀d:(A → A → real). zz_metric(M, d) ⇒ ∀x:A. x ∈ M"
	cmap := "∀T:((A → bool) → bool). ∀S:((B → bool) → bool). ∀f:(A → B). zz_cmap(T, S, f) ⇒ ∀u:(A → bool). u ∈ T"
	sameBundleKey(t, scope, "∀M:zz_metric(A). ∀x:A. x ∈ M", metric)
	sameBundleKey(t, scope, "∀f:zz_cmap(A, B). ∀u:(A → bool). u ∈ T", cmap)
	for _, tc := range []struct{ raw, want string }{
		{metric, "∀M:zz_metric(A). ∀x:A. x ∈ M"},
		{cmap, "∀f:zz_cmap(A, B). ∀u:(A → bool). u ∈ T"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		sameBundleKey(t, scope, out, tc.raw)
	}
	// A fact of a structure with a map for its subject states the
	// bundle under the map's name: its field is read.
	sameBundleKey(t, scope,
		"∀f:zz_cmap(A, B). ∀u:(A → bool). u ∈ f.T",
		cmap)
}

// A ∀-fact states a FAMILY, the module P(n) for every n: a fibre is
// named by applying the subject, fills a layout as the module would,
// and folds back; a structure applied to the components of a bundle in
// scope folds to the bundle.
func TestBundle_FamilyFromAForallFact(t *testing.T) {
	scope := bundleTestScope(t)
	ring := "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). " +
		"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ "
	complex := ring + "∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). ∀smul:(A → B → B). ∀P:(num → B → bool). ∀d:(num → B → B). " +
		"(∀n:num. zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, P(n))) ⇒ "
	explicit := complex + "∀n:num. zz_hom(add', smul, add', smul, R, P(n + 1), P(n), d(n + 1))"
	sameBundleKey(t, scope, complex+"∀n:num. zz_hom(P(n + 1), P(n), d(n + 1))", explicit)
	// A fibre's field is the component applied: P.add' is add'.
	sameBundleKey(t, scope, complex+"∀n:num. zz_hom(P(n + 1), P(n), d(n + 1)) ∧ P.add' = add'", explicit+" ∧ add' = add'")
	out, err := ChapterSpelling(explicit, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "∀R:zz_cring(A). ")
	require.Contains(t, out, "⇒ ∀n:num. zz_hom(P(n + 1), P(n), d(n + 1))")
	require.Contains(t, out, "(∀n:num. zz_mod(R, add', zero', neg', smul, P(n))) ⇒", "the fact stating the family, over terms, folds the ring it is given")
	sameBundleKey(t, scope, out, explicit)
	// The structure applied to the fibre's components is the fibre.
	sameBundleKey(t, scope, complex+"∀n:num. zz_mod(P(n))",
		complex+"∀n:num. zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, P(n))")
	out, err = ChapterSpelling(complex+"∀n:num. zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, P(n))", scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "⇒ ∀n:num. zz_mod(P(n))", "the bundle itself, not zz_mod(R, add', …, P(n)): the layouts leave operations loose")
	// A plain bundle too: the module M restated is zz_mod(M).
	sameBundleKey(t, scope, "∀M:zz_mod(A, B). zz_mod(M)", "∀M:zz_mod(A, B). zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, M)")
	// A tuple over a fibre reads its fields.
	sameBundleKey(t, scope, complex+"∀n:num. ∀S:(I → B) → bool. zz_mod(R, zz_point(I, P(n)), S)",
		complex+"∀n:num. ∀S:(I → B) → bool. zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add'), zz_fzero⟨D:I⟩(zero'), zz_fneg⟨D:I⟩(neg'), zz_fsmul⟨D:I⟩(smul), R, S)")
}

// An application over a bundle's name spelled as a variable — the
// complexes' components written out, the map's prefix left out, the
// map partially applied — keeps the implicit completion's reading: the
// bundles' would put a boundary where a complex goes, and a reading
// that places a variable at a parameter of another type is none.
func TestBundle_SpelledVariablesAreNoBundleReading(t *testing.T) {
	scope := bundleTestScope(t)
	two := "∀op:(B → B → B). ∀P':(num → B → bool). ∀d':(num → B → B). zz_cxs(op, P', d') ⇒ ∀P:(num → B → bool). ∀d:(num → B → B). zz_cxs(op, P, d) ⇒ ∀x:B. "
	explicit := two + "zz_ch(op, P', d', P, d, 0, x) = x"
	sameBundleKey(t, scope, two+"zz_ch(P', d', P, d, 0, x) = x", explicit)
	sameBundleKey(t, scope, two+"zz_ch(P', P, 0, x) = x", explicit)
	out, err := ChapterSpelling(explicit, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "zz_ch(P', P, 0, x) = x")
	sameBundleKey(t, scope, out, explicit)
}

// A sub-structure fact restating a bundle in scope — the module's
// additive group on M — leaves the richer bundle standing; two facts
// that read a name apart leave none.
func TestBundle_RicherFactStands(t *testing.T) {
	scope := bundleTestScope(t)
	sameBundleKey(t, scope,
		"∀M:zz_mod(A, B). ∀f:(B → B). zz_grp(add', zero', neg', M) ⇒ zz_hom(M, M, f)",
		"∀M:zz_mod(A, B). ∀f:(B → B). zz_grp(add', zero', neg', M) ⇒ zz_hom(add', smul, add', smul, R, M, M, f)")
	res := ParsePropTextInScope("∀M:zz_mod(A, B). ∀op:(B → B → B). ∀f:(B → B). zz_grp(op, zero', neg', M) ⇒ zz_hom(M, M, f)", scope)
	require.NotEmpty(t, res.Errors, "a group on M under another operation reads M apart, and M is no bundle")
}

// A field is the component of a bundle the definition names.
func TestBundle_Field(t *testing.T) {
	scope := bundleTestScope(t)
	sameBundleKey(t, scope,
		"∀R:zz_cring(A). ∀M:zz_mod(R, B). ∀N:zz_mod(R, C). ∀u:B. ∀v:C. M.add'(u, u) = M.zero' ∧ N.add'(v, v) = N.zero' ∧ M.smul(R.one, u) = u",
		zzRingModuleExplicit+"∀u:B. ∀v:C. add'(u, u) = zero' ∧ N_add'(v, v) = N_zero' ∧ smul(one, u) = u")
	res := ParsePropTextInScope("∀R:zz_cring(A). R.smul = R.smul", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "has no component smul")
}

// A tuple is spliced among the arguments where it stands, its
// parameter read as a type in the instance annotations.
func TestBundle_Tuple(t *testing.T) {
	scope := bundleTestScope(t)
	sameBundleKey(t, scope,
		"∀R:zz_cring(A). ∀S:(I → A) → bool. zz_mod(R, zz_lift(I), S)",
		"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). "+
			"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ ∀S:(I → A) → bool. "+
			"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add), zz_fzero⟨D:I⟩(zero), zz_fneg⟨D:I⟩(neg), zz_fsmul⟨D:I⟩(mul), R, S)")
	// A subscripted parameter is substituted like any other.
	sameBundleKey(t, scope,
		"∀R:zz_cring(A). ∀S:(I → A) → bool. zz_mod(R, zz_sublift(I), S)",
		"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). "+
			"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ ∀S:(I → A) → bool. "+
			"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add), zz_fzero⟨D:I⟩(zero), zz_fneg⟨D:I⟩(neg), zz_fsmul⟨D:I⟩(mul), R, S)")
	// A tuple over a bundle reads the bundle's fields.
	moduleExplicit := "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). " +
		"∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). ∀smul:(A → B → B). ∀R:(A → bool). ∀M:(B → bool). " +
		"zz_mod(add, zero, neg, mul, one, sub, add', zero', neg', smul, R, M) ⇒ ∀S:(I → B) → bool. "
	sameBundleKey(t, scope,
		"∀M:zz_mod(A, B). ∀S:(I → B) → bool. zz_mod(R, zz_point(I, M), S)",
		moduleExplicit+"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add'), zz_fzero⟨D:I⟩(zero'), zz_fneg⟨D:I⟩(neg'), zz_fsmul⟨D:I⟩(smul), R, S)")
	out, err := ChapterSpelling(moduleExplicit+"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add'), zz_fzero⟨D:I⟩(zero'), zz_fneg⟨D:I⟩(neg'), zz_fsmul⟨D:I⟩(smul), R, S)",
		scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, "∀M:zz_mod(A, B). ∀S:((I → B) → bool). zz_mod(R, zz_point(I, M), S)", out)
	// A type parameter may be a composite type, spelled as a term.
	pairExplicit := "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). " +
		"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ ∀S:(prod(B, C) → A) → bool. " +
		"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:prod(B, C)⟩(add), zz_fzero⟨D:prod(B, C)⟩(zero), zz_fneg⟨D:prod(B, C)⟩(neg), zz_fsmul⟨D:prod(B, C)⟩(mul), R, S)"
	sameBundleKey(t, scope, "∀R:zz_cring(A). ∀S:(prod(B, C) → A) → bool. zz_mod(R, zz_lift(prod(B, C)), S)", pairExplicit)
	pairOut, err := ChapterSpelling(pairExplicit, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, pairOut, "zz_mod(R, zz_lift(prod(B, C)), S)")
	res := ParsePropTextInScope("∀x:A. zz_lift(x) = zz_lift(x)", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "is a tuple")
	// A type parameter given a term that spells no type is refused, not
	// left standing as its own letter.
	res = ParsePropTextInScope("∀R:zz_cring(A). ∀S:((I → A) → A) → bool. zz_mod(R, zz_lift(I → A), S)", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "stands for a type")
}

// A tuple's term may bind: the fold matches under the binder, and a
// parameter binds nothing the binder captures.
func TestBundle_TupleUnderABinder(t *testing.T) {
	scope := bundleTestScope(t)
	raw := "∀h:(B → C). ∀g:(B → B). zz_P(λu:B. h(g(u)))"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, "∀h:(B → C). ∀g:(B → B). zz_P(zz_comp(h, g))", out)
	sameBundleKey(t, scope, out, raw)
	// y would bind the λ's own u: no fold.
	captured, err := ChapterSpelling("∀h:(B → C). zz_P(λu:B. h(u))", scope.Syntax, nil)
	require.NoError(t, err)
	require.NotContains(t, captured, "zz_const")
}

// Parentheses around a quantifier's whole body do not change the
// structure it states. Logical grouping outside that body and inside
// its residual proposition must survive the spelling roundtrip.
func TestBundle_ParenthesizedQuantifierBody(t *testing.T) {
	scope := bundleTestScope(t)
	forall := "∀M:(A → bool). ∀d:(A → A → real). "
	exists := "∃M:(A → bool). ∃d:(A → A → real). "
	fact := "zz_metric(M, d)"
	body := "∀x:A. x ∈ M"
	metric := forall + "(" + fact + " ⇒ (" + body + "))"
	for _, row := range []struct {
		name, raw, folded string
	}{
		{"forall", metric, "∀M:zz_metric(A)."},
		{"exists", exists + "(" + fact + " ∧ (∃x:A. x ∈ M))", "∃M:zz_metric(A)."},
		{"under negation", "¬(" + metric + ")", "∀M:zz_metric(A)."},
		{"in antecedent", "(" + metric + ") ⇒ ⊥", "∀M:zz_metric(A)."},
		{"nested implication", forall + "(" + fact + " ⇒ ((" + body + ") ⇒ ⊥))", "∀M:zz_metric(A)."},
		{"grouped antecedent", forall + "((" + fact + " ⇒ (" + body + ")) ⇒ ⊥)", ""},
		{"negated structure", forall + "(¬" + fact + " ⇒ (" + body + "))", ""},
		{"forall conjunction", forall + "(" + fact + " ∧ (" + body + "))", ""},
		{"exists implication", exists + "(" + fact + " ⇒ (" + body + "))", ""},
		{"mixed quantifiers", "∀M:(A → bool). ∃d:(A → A → real). (" + fact + " ∧ (" + body + "))", ""},
		{
			"sequence letter",
			"∀op:(B → B → B). ∀op':(C → C → C). ∀P:(num → B → bool). ∀d:(num → B → B). ∀Q:(num → C → bool). ∀e:(num → C → C). (zz_pair(op, op', P, d, Q, e) ⇒ P(0) = P(1))",
			"∀S:zz_pair(B, C).",
		},
	} {
		t.Run(row.name, func(t *testing.T) {
			original := parseImplicit(t, scope, row.raw)
			for _, form := range []struct{ name, text string }{
				{"authored", row.raw},
				{"parser print", prop.FormatPropForParser(original)},
			} {
				t.Run(form.name, func(t *testing.T) {
					out, err := ChapterSpelling(form.text, scope.Syntax, nil)
					require.NoError(t, err)
					if row.folded != "" {
						require.Contains(t, out, row.folded)
					} else {
						require.NotContains(t, out, ":zz_metric(")
					}
					back := parseImplicit(t, scope, out)
					require.Equal(t, original.AlphaKey(), back.AlphaKey(), "the spelling changed logical grouping or scope: %s", out)
				})
			}
		})
	}
}

// Two layouts may share components: the second bundle folds at the
// first of its slots the first left.
func TestBundle_SharedComponentsFold(t *testing.T) {
	scope := bundleTestScope(t)
	raw := zzRingModuleExplicit + "∀u:B. zz_tw(add, zero, neg, mul, one, sub, add', smul, R, M, u)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "zz_tw(R, M, u)")
	sameBundleKey(t, scope, out, raw)
}

// zzSimplicialScope is bundleTestScope with a record zz_sset(B) of a
// simplicial set, its n-simplices the field `simplices` read off by
// zz_simplices; a homomorphism zz_mhom named by its map; a map of
// simplicial sets zz_cxmap, which states a zz_mhom at the n-simplices
// for every n — the layout's templates are the kernel terms the
// registry reads off the definition's body; and zz_ses over two
// homomorphisms.
func zzSimplicialScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := bundleTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	param := func(name, ty string) BundleParam { return BundleParam{Name: name, Type: typ(ty)} }
	for name, ty := range map[string]string{
		"zz_simplices": "zz_sset(B) → num → B → bool",
		"zz_mhom":      "(B → B → B) → (B → bool) → (B → bool) → (B → B) → bool",
		"zz_cxmap":     "(B → B → B) → zz_sset(B) → zz_sset(B) → (num → B → B) → bool",
		"zz_ses":       "(B → B → B) → (B → bool) → (B → bool) → (B → bool) → (B → B) → (B → B) → bool",
	} {
		scope.ConstMetas[name] = core.MakeConstMeta(name, typ(ty))
	}
	scope.Syntax = structFieldsSyntax{SyntaxTable: scope.Syntax, metas: scope.ConstMetas,
		structs: map[string]*StructSyntax{"zz_sset": {Fields: []StructField{{Name: "simplices", Const: "zz_simplices"}}}}}
	syntax := testTable(scope)
	syntax["zz_mhom"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: []BundleParam{param("op", "B → B → B"), param("S", "B → bool"), param("T", "B → bool"), param("f", "B → B")},
			Structure: true, Subject: 3, Layouts: []BundleLayout{{Structure: "zz_mhom", Slots: []int{0, 1, 2, 3}}}}}
	family := parseImplicit(t, scope, "∀op:(B → B → B). ∀X Y:zz_sset(B). ∀F:(num → B → B). ∀n:num. zz_mhom(op, zz_simplices(X, n), zz_simplices(Y, n), F(n))")
	body := family.Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	_, templates := spineArgs(body)
	syntax["zz_cxmap"] = &ConstSyntax{StructurePredicate: true,
		Bundle: &BundleSyntax{Params: []BundleParam{param("op", "B → B → B"), param("X", "zz_sset(B)"), param("Y", "zz_sset(B)"), param("F", "num → B → B")},
			Structure: true, Subject: -1, Layouts: []BundleLayout{
				{Structure: "zz_cxmap", Slots: []int{0, 1, 2, 3}},
				{Structure: "zz_mhom", Slots: []int{0, -1, -1, -1}, Index: []BundleParam{param("n", "num")},
					Templates: []core.Term{nil, templates[1], templates[2], templates[3]}}}}}
	syntax["zz_ses"] = &ConstSyntax{
		Bundle: &BundleSyntax{Params: []BundleParam{param("op", "B → B → B"), param("S", "B → bool"), param("T", "B → bool"), param("U", "B → bool"), param("f", "B → B"), param("g", "B → B")},
			Subject: -1, Layouts: []BundleLayout{
				{Structure: "zz_mhom", Slots: []int{0, 1, 2, 4}},
				{Structure: "zz_mhom", Slots: []int{0, 2, 3, 5}}}}}
	return scope
}

// A layout's template is the kernel's spelling of a term over the
// components, `zz_simplices(X, n)`; a text writes the same term as a
// field of the record, `X.simplices(n)`. The two are one term to the
// fold: the short exact sequence at the n-simplices of three simplicial
// sets, for every n, folds to its two maps under either spelling.
func TestBundle_TemplateMeetsAFieldSpelling(t *testing.T) {
	scope := zzSimplicialScope(t)
	maps := "∀op:(B → B → B). ∀X Y Z:zz_sset(B). ∀i p:(num → B → B). zz_cxmap(op, X, Y, i) ⇒ zz_cxmap(op, Y, Z, p) ⇒ ∀n:num. "
	for _, raw := range []string{
		maps + "zz_ses(op, X.simplices(n), Y.simplices(n), Z.simplices(n), i(n), p(n))",
		maps + "zz_ses(op, zz_simplices(X, n), zz_simplices(Y, n), zz_simplices(Z, n), i(n), p(n))",
	} {
		out, err := ChapterSpelling(raw, scope.Syntax, nil)
		require.NoError(t, err, raw)
		require.Contains(t, out, "⇒ ∀n:num. zz_ses(i(n), p(n))", raw)
		sameBundleKey(t, scope, out, raw)
	}
}

// A definition's equation states its layouts (astApp.stated): the
// conjunct of zz_cxmap's body stating the zz_mhom at every n is spelled
// in full, where a theorem under a zz_cxmap restates the fibre by its
// name.
func TestBundle_DefinitionStatesItsLayoutsInFull(t *testing.T) {
	scope := zzSimplicialScope(t)
	binders := "∀op:(B → B → B). ∀X Y:zz_sset(B). ∀F:(num → B → B). "
	layout := "∀n:num. zz_mhom(op, X.simplices(n), Y.simplices(n), F(n))"
	definition := binders + "zz_cxmap(op, X, Y, F) ⇔ (" + layout + ") ∧ F(0) = F(0)"
	out, err := ChapterSpelling(definition, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "zz_cxmap(op, X, Y, F) ⇔ ("+layout+") ∧", "the body states the layout: spelled in full")
	sameBundleKey(t, scope, out, definition)
	theorem := binders + "zz_cxmap(op, X, Y, F) ⇒ " + layout
	out, err = ChapterSpelling(theorem, scope.Syntax, nil)
	require.NoError(t, err)
	require.Contains(t, out, "⇒ ∀n:num. zz_mhom(F(n))", "a theorem restates the fibre by its name")
	sameBundleKey(t, scope, out, theorem)
}

// A structure with no subject folds under the letter it declares; the
// letter is no component, and its complexes are bundles inside.
func TestBundle_LetterOfAStructureWithNoSubject(t *testing.T) {
	scope := bundleTestScope(t)
	raw := "∀op:(B → B → B). ∀op':(C → C → C). ∀P:(num → B → bool). ∀d:(num → B → B). ∀Q:(num → C → bool). ∀e:(num → C → C). " +
		"zz_pair(op, op', P, d, Q, e) ⇒ P(0) = P(1)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.Equal(t, "∀S:zz_pair(B, C). P(0) = P(1)", out)
	sameBundleKey(t, scope, out, raw)
}

// Two structures of one kind in scope: the second's components are
// minted under its bundle (S_add…S_sub), so no bound add'…sub' offers
// the implicit reading, and the bundles lay the constant out in the
// order written, either way round. Where the text itself binds the
// implicit names beside a bundle, the two readings exist and disagree:
// refused.
func TestBundle_ImplicitShortFormWins(t *testing.T) {
	scope := bundleTestScope(t)
	fwd := parseImplicit(t, scope, "∀R:zz_cring(A). ∀S:zz_cring(B). ∀f:(A → B). zz_rhom(R, S, f) ⇒ ⊤")
	require.Contains(t, prop.PrintProp(fwd), "zz_rhom(add, zero, neg, mul, one, sub, S_add, S_zero, S_neg, S_mul, S_one, S_sub, R, S, f)")
	rev := parseImplicit(t, scope, "∀R:zz_cring(A). ∀S:zz_cring(A). ∀f:(A → A). zz_rhom(S, R, f) ⇒ ⊤")
	require.Contains(t, prop.PrintProp(rev), "zz_rhom(S_add, S_zero, S_neg, S_mul, S_one, S_sub, add, zero, neg, mul, one, sub, S, R, f)")
	res := ParsePropTextInScope("∀R:zz_cring(A). ∀add':(A → A → A). ∀zero':A. ∀neg':(A → A). ∀mul':(A → A → A). ∀one':A. ∀sub':(A → A → A). ∀S:(A → bool). "+
		"zz_cring(add', zero', neg', mul', one', sub', S) ⇒ ∀f:(A → A). zz_rhom(S, R, f) ⇒ ⊤", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "reads two ways")
}

// The chapter spelling folds the spelled-out forms back: a binder run a
// structure fact closes, a constant's arguments a bundle fills, a run
// of arguments a tuple matches — and the fold reads back to the same
// statement.
func TestBundle_ChapterSpellingFolds(t *testing.T) {
	scope := bundleTestScope(t)
	for _, tc := range []struct{ raw, want string }{
		{zzRingModuleExplicit + "∀f:(B → C). zz_hom(add', smul, N_add', N_smul, R, M, N, f) ⇒ zz_P(f)",
			"∀R:zz_cring(A). ∀M:zz_mod(R, B). ∀N:zz_mod(R, C). ∀f:(B → C). zz_hom(M, N, f) ⇒ zz_P(f)"},
		{"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). " +
			"zz_cring(add, zero, neg, mul, one, sub, R) ⇒ ∀S:(I → A) → bool. " +
			"zz_mod(add, zero, neg, mul, one, sub, zz_fadd⟨D:I⟩(add), zz_fzero⟨D:I⟩(zero), zz_fneg⟨D:I⟩(neg), zz_fsmul⟨D:I⟩(mul), R, S)",
			"∀R:zz_cring(A). ∀S:((I → A) → bool). zz_mod(R, zz_lift(I), S)"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		sameBundleKey(t, scope, out, tc.raw)
	}
	// A binder whose names the expansion would not mint stays spelled.
	raw := "∀plus:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀R:(A → bool). " +
		"zz_cring(plus, zero, neg, mul, one, sub, R) ⇒ R = R"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	require.NoError(t, err)
	require.NotContains(t, out, "∀R:zz_cring")
}

// A resident structure fact whose component is an operator constant —
// `zz_cxs(+, P, d)` over num, as the printer spells the `+` of a
// resident `comm_monoid_on(𝕌, +, 0)` — is read into its bundle: the
// layout's template that is the operator alone reads back as the
// constant (templateOf), and the next text parses.
func TestBundle_ResidentFactOverABareOperator(t *testing.T) {
	scope := bundleTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	scope.ConstMetas["+"] = core.MakeConstMeta("+", typ("num → num → num"))
	scope.Vars = map[string]core.HolType{"P": typ("num → num → bool"), "d": typ("num → num → num"), "x": typ("num")}
	fact := ParsePropTextInScope("zz_cxs(+, P, d)", scope)
	require.Empty(t, fact.Errors, "%v", fact.Errors)
	plus := findConstOfName(fact.Prop.Conclusion(), "+")
	require.False(t, plus.IsZero())
	require.Equal(t, "+", printKey(templateOf(plus, map[string]astNode{}, 0)))
	resident := *scope
	resident.ResidentFacts = []core.Term{fact.Prop.Conclusion()}
	bundles := residentBundles(resident.Syntax, resident.ResidentFacts, nil)
	require.Len(t, bundles, 1)
	require.Equal(t, "+", printKey(bundles[0].comps[0]))
	assertSameProp(t, &resident, "P(0, x) ⇒ d(0, x) = x", "P(0, x) ⇒ d(0, x) = x")
}
