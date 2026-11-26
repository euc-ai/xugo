// Tests for ParseScope.FreshenMetaLetters — occurrence-local renaming
// of a polymorphic meta's internal letters at instantiation, so a meta
// letter can never capture (or be captured by) a same-named author
// letter. The acceptance criterion throughout: parse meaning must be
// invariant under renaming the AUTHOR's letters, and everything a
// structural anchor or a ⟨⟩ tie pins today stays byte-identical.
package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

func freshenScope() *ParseScope { return &ParseScope{FreshenMetaLetters: true} }

// constInstanceTyVars returns the type-variable names in the instance
// type of the named const's occurrences.
func constInstanceTyVars(t *testing.T, p core.Prop, constName string) map[string]bool {
	t.Helper()
	consts := map[core.TermKey]core.ConstTerm{}
	ext.CollectConstTerms(p.Conclusion(), consts)
	out := map[string]bool{}
	for _, c := range consts {
		if string(c.Name()) != constName {
			continue
		}
		for _, tv := range c.Type().TypeVars() {
			out[string(tv.Name())] = true
		}
	}
	return out
}

// The capture accident, killed: a bare ∅ (meta letter literally "A")
// inside a statement whose author letter is also "A". Verbatim
// instantiation ties them by name — the powers/words receipts;
// freshening keeps them apart.
func TestFreshenKillsNameCapture(t *testing.T) {
	text := "∀x:A. (x = x) ∧ subset(∅, ∅)"
	captured := ParsePropTextInScope(text, &ParseScope{})
	requireParses(t, captured)
	if !constInstanceTyVars(t, captured.Prop, "empty_set")["A"] {
		t.Fatal("precondition: the verbatim parse captures the author letter A")
	}
	freshened := ParsePropTextInScope(text, freshenScope())
	requireParses(t, freshened)
	if constInstanceTyVars(t, freshened.Prop, "empty_set")["A"] {
		t.Fatal("the freshened parse must not tie ∅ to the author's A")
	}
	if captured.Prop.AlphaKey() == freshened.Prop.AlphaKey() {
		t.Fatal("capture and no-capture are different statements — keys must differ")
	}
}

// Structural anchors deliver the same statement with or without the
// flag: the head's unify binds the occurrence-local letter to the
// author's, and the binding is substituted back into the built
// argument (without the flag `∅ ⊆ s` gets this by name collision).
func TestFreshenPreservesAnchoredParses(t *testing.T) {
	for _, text := range []string{
		"∀s:(A → bool). ∅ ⊆ s",
		"∀s:(num → bool). s = ∅",
		"∀m:num. m ∈ {m}",
		"∀n:num. subset(∅⟨A:num⟩, ∅⟨A:num⟩) ⇒ n = n",
	} {
		verbatim := ParsePropTextInScope(text, &ParseScope{})
		requireParses(t, verbatim)
		freshened := ParsePropTextInScope(text, freshenScope())
		requireParses(t, freshened)
		if verbatim.Prop.AlphaKey() != freshened.Prop.AlphaKey() {
			t.Errorf("%q: anchored parse must be identical under freshening\n  verbatim:  %s\n  freshened: %s",
				text, verbatim.Prop.AlphaKey(), freshened.Prop.AlphaKey())
		}
	}
}

// Deterministic: identical text parses to the identical statement.
func TestFreshenDeterministic(t *testing.T) {
	text := "∀x:A. (x = x) ∧ subset(∅, ∅)"
	a := ParsePropTextInScope(text, freshenScope())
	b := ParsePropTextInScope(text, freshenScope())
	requireParses(t, a)
	requireParses(t, b)
	if a.Prop.AlphaKey() != b.Prop.AlphaKey() {
		t.Fatal("freshening must be deterministic per text")
	}
}

// With StrictMint, freshening closes the name-collision hole: the
// capture shape that StrictMint alone waves through (the leaked letter
// looks binder-anchored) is now an orphan and is rejected with the tie
// spelled.
func TestFreshenClosesStrictMintCollisionHole(t *testing.T) {
	text := "∀x:A. (x = x) ∧ subset(∅, ∅)"
	// StrictMint alone: the hole — capture makes the leak look anchored.
	holed := ParsePropTextInScope(text, &ParseScope{StrictMint: true})
	requireParses(t, holed)
	// StrictMint + freshening: rejected, naming the repair.
	res := ParsePropTextInScope(text, &ParseScope{StrictMint: true, FreshenMetaLetters: true})
	if len(res.Errors) == 0 {
		t.Fatal("freshening + strict mint must reject the unanchored bare heads")
	}
	if msg := res.Errors[0].Message; !strings.Contains(msg, "strict mint") || !strings.Contains(msg, "⟨") {
		t.Fatalf("rejection must spell the tie, got: %s", msg)
	}
}

// The type collectors read a constant with the occurrence's own letters,
// as the build does: a set-builder's hidden binder is typed off its head
// before the build. Read verbatim beside an author's C, zz_pick's B and C
// would conflate — B := C makes its second slot zz_wrap(C, C), which
// zz_wrap(C, H) does not match — and zz_lift's own A, left open, would
// type the binder zz_box(A), which the head, at zz_box(H), cannot meet;
// spelled K, the author's letter collides with nothing. The statement
// does not depend on the spelling.
func TestFreshenTypesSetBuilderHeadApart(t *testing.T) {
	typ := func(text string) core.HolType {
		t.Helper()
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("%s: %v", text, err)
		}
		return ty
	}
	scope := func() *ParseScope {
		return &ParseScope{FreshenMetaLetters: true, ConstMetas: map[string]core.ConstTermMeta{
			"zz_pick": core.MakeConstMeta("zz_pick", typ("zz_box(B) → zz_wrap(B, C) → C")),
			"zz_lift": core.MakeConstMeta("zz_lift", typ("A → zz_box(A)")),
		}}
	}
	text := "∀b:zz_box(L). ∀w:zz_wrap(L, H). {zz_lift(zz_pick(b, w)) | u:H | ⊤} = {zz_lift(zz_pick(b, w)) | u:H | ⊤}"
	apart := ParsePropTextInScope(strings.ReplaceAll(text, "L", "K"), scope())
	requireParses(t, apart)
	colliding := ParsePropTextInScope(strings.ReplaceAll(text, "L", "C"), scope())
	requireParses(t, colliding)
	renamed := colliding.Prop.Conclusion().TypeSubstitute(core.MakeTypeSubst(core.MakeVarType("C"), core.MakeVarType("K")))
	if core.MakeProp(renamed).AlphaKey() != apart.Prop.AlphaKey() {
		t.Fatalf("renaming the author's letter must not change the statement\n  at C: %s\n  at K: %s",
			ext.FormatTerm(colliding.Prop.Conclusion(), false), ext.FormatTerm(apart.Prop.Conclusion(), false))
	}
}

// A binder whose only use is a membership takes the element type its
// partner set gives it, spelled in an author's letter as much as at
// num: under freshening only a constant's stand-ins are still open. The
// letter A is no exception: the set-builder's witness takes no type from
// comprehension_spec's own A, which an author's A would meet by name
// alone.
func TestFreshenMemberBinderTakesTheAuthorsLetter(t *testing.T) {
	for _, letter := range []string{"A", "K"} {
		for _, text := range []string{
			"∀s:set(L). {x | x ∈ s} = s",
			"∀s:set(L). ∃z. z ∈ s",
		} {
			text = strings.ReplaceAll(text, "L", letter)
			res := ParsePropTextInScope(text, freshenScope())
			if len(res.Errors) > 0 {
				t.Errorf("%s: %s", text, res.Errors[0].Message)
			}
		}
	}
}

// A stand-in that types a variable at one slot and meets a function
// over itself at another has no type. A corpus literal read outside the
// scope that types its variables — `k` at laurent_polynomial_coefficient's
// `A → A → A` and `t` at its `A`, then `k` at projective_line_duality_
// inverse's `B` and `t` at its `B → B` — asks for
// A = (A → A → A) → (A → A → A). The reverse match bound the letter to
// the type mentioning it, and closing the bindings then grew their
// targets slot after slot until the machine's memory was gone. The slot
// is refused as a mismatch; the constants have those two shapes.
func TestFreshenRefusesALetterBoundToItself(t *testing.T) {
	typ := func(text string) core.HolType {
		t.Helper()
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("%s: %v", text, err)
		}
		return ty
	}
	scope := &ParseScope{FreshenMetaLetters: true, StrictResolution: true, ConstMetas: map[string]core.ConstTermMeta{
		"zz_coefficient": core.MakeConstMeta("zz_coefficient",
			typ("(A → A → A) → A → (A → A → A) → A → (A → A) → set(A) → A → A → int → A")),
		"zz_inverse": core.MakeConstMeta("zz_inverse",
			typ("(A → A → A) → A → (A → A) → (A → A → A) → A → (A → A → A) → (A → A) → set(A) → "+
				"set(A) → A → zz_ops(A, B) → prod(set(B), set(B)) → (set(B) → A) → B → A")),
	}}
	res := ParseTermTextInScope("zz_coefficient(k, t, zz_inverse(L, k, t, V, M, u, y), -&1)", nil, scope, nil)
	if len(res.Errors) == 0 {
		t.Fatal("a letter bound to a type over itself must be refused")
	}
	if e := res.Errors[0]; e.Code != CodeTypeMismatch || !strings.Contains(e.Message, "does not match domain") {
		t.Fatalf("refused at the slot where the letter meets a function over itself, got [%s] %s", e.Code, e.Message)
	}
}
