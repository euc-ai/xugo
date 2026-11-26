package registry

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// An overloaded word and a constant's name refuse each other, and two
// constants the word could never tell apart refuse to share it — on a
// fresh manager, so the process registry stays untouched.
func TestOverloadRegistration(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := dsl.ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	word := func(ty string) *dsl.ConstSyntax {
		return &dsl.ConstSyntax{Overload: &dsl.Overload{Word: "zz_total", Arity: 2, Type: typ(ty)}}
	}
	var m ConstMetaManager
	m.RegisterConstSyntax("zz_real_total", word("(A → bool) → (A → real) → real"))
	m.RegisterConstSyntax("zz_nat_total", word("(A → bool) → (A → num) → num"))
	if got := strings.Join(m.OverloadConsts("zz_total"), ","); got != "zz_real_total,zz_nat_total" {
		t.Fatalf("OverloadConsts = %q", got)
	}

	mustPanic := func(what, want string, f func()) {
		t.Helper()
		defer func() {
			r := recover()
			if r == nil {
				t.Fatalf("%s must panic", what)
			}
			if !strings.Contains(r.(string), want) {
				t.Fatalf("%s: panic should say %q, got: %v", what, want, r)
			}
		}()
		f()
	}
	// A second constant at a type the first instantiates to.
	mustPanic("an indistinguishable constant", "indistinguishable", func() {
		m.RegisterConstSyntax("zz_other_total", word("(num → bool) → (num → real) → real"))
	})
	// The word cannot be minted, by either door.
	if err := m.ClaimName("zz_total"); err == nil || !strings.Contains(err.Error(), "overloaded word") {
		t.Fatalf("ClaimName(zz_total): %v", err)
	}
	mustPanic("minting the word", "overloaded word", func() {
		m.LoadOrStoreConstMeta(core.MakeConstMeta("zz_total", typ("num")))
	})
	// A minted name cannot become a word.
	m.LoadOrStoreConstMeta(core.MakeConstMeta("zz_minted", typ("num")))
	mustPanic("a constant's name as the word", "is a constant's name", func() {
		m.RegisterConstSyntax("zz_x", &dsl.ConstSyntax{Overload: &dsl.Overload{Word: "zz_minted", Arity: 1, Type: typ("num → num")}})
	})
}

// A pair of outfix delimiters is one constant's, or several constants'
// under one overloaded word with the holes placed alike; anything else
// sharing it is refused by name.
func TestOutfixSharedUnderOneWord(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := dsl.ParseTypeText(text)
		if err != nil {
			t.Fatal(err)
		}
		return ty
	}
	bars := func(word, ty string, sub int) *dsl.ConstSyntax {
		s := &dsl.ConstSyntax{Outfix: &dsl.Outfix{Open: "|", Close: "|", Body: []int{0}, Sub: sub}}
		if word != "" {
			s.Overload = &dsl.Overload{Word: word, Arity: 1, Type: typ(ty)}
		}
		return s
	}
	var m ConstMetaManager
	m.RegisterConstSyntax("zz_bars_real", bars("zz_bars", "real → real", -1))
	m.RegisterConstSyntax("zz_bars_int", bars("zz_bars", "int → int", -1))
	require.Equal(t, []string{"zz_bars_real", "zz_bars_int"}, m.OutfixConsts("|", "|"))
	require.PanicsWithValue(t,
		"constant \"zz_bars_alone\": the notation |…| is already zz_bars_real's — a second constant shares it only under an overloaded word both declare",
		func() { m.RegisterConstSyntax("zz_bars_alone", bars("", "", -1)) })
	require.PanicsWithValue(t,
		"constant \"zz_bars_other\": the notation |…| is zz_bars_real's under the word \"zz_bars\", not \"zz_other\"",
		func() { m.RegisterConstSyntax("zz_bars_other", bars("zz_other", "num → num", -1)) })
	require.PanicsWithValue(t,
		"constant \"zz_bars_sub\": the notation |…| places its holes differently from zz_bars_real's",
		func() { m.RegisterConstSyntax("zz_bars_sub", bars("zz_bars", "num → num → num", 1)) })
}

// A notation is its delimiter PAIR: two constants whose notations open
// alike and close differently share nothing — `⟦a, b⟧` and `⟦a, b⟭`
// are two notations, each its constant's alone.
func TestOutfixKeyedByThePair(t *testing.T) {
	interval := func(open, close string) *dsl.ConstSyntax {
		return &dsl.ConstSyntax{Outfix: &dsl.Outfix{Open: open, Close: close, Body: []int{0, 1}, Sub: -1}}
	}
	var m ConstMetaManager
	m.RegisterConstSyntax("zz_closed", interval("⟦", "⟧"))
	m.RegisterConstSyntax("zz_closed_open", interval("⟦", "⟭"))
	m.RegisterConstSyntax("zz_open", interval("⟬", "⟭"))
	m.RegisterConstSyntax("zz_open_closed", interval("⟬", "⟧"))
	require.Equal(t, []string{"zz_closed"}, m.OutfixConsts("⟦", "⟧"))
	require.Equal(t, []string{"zz_closed_open"}, m.OutfixConsts("⟦", "⟭"))
	require.Equal(t, []string{"zz_open"}, m.OutfixConsts("⟬", "⟭"))
	require.Equal(t, []string{"zz_open_closed"}, m.OutfixConsts("⟬", "⟧"))
	require.PanicsWithValue(t,
		"constant \"zz_closed_again\": the notation ⟦…⟭ is already zz_closed_open's — a second constant shares it only under an overloaded word both declare",
		func() { m.RegisterConstSyntax("zz_closed_again", interval("⟦", "⟭")) })
}
