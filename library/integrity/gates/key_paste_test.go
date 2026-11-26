// key_paste_test.go — the key-paste door's text surgery, on snippets:
// a Key inserted under the entry's Name line, a stale Key replaced, a
// Name line that is another entry's refused, both edits where the
// Name line carries the literal's other fields, and a stale Key that
// leads a line carrying other fields; and the same for the keys an
// inductive definition's literal spells for its entries in one Keys
// block.
package gates

import (
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/xugofmt"
)

const pasteFixture = `package fam

// Alpha — stated without a key.
var Alpha = family.Add(registry.ProofEntry{
	Name: "Alpha",
	Deps: []registry.EntryLike{Beta},
	Build: family.Card("∀n:num. n = n",
		"a note"),
})

// Beta — a key that moved.
var Beta = betaThm{family.Add(registry.ProofEntry{
	Name:  "Beta",
	Key:   "prop_0000000000000000",
	Build: family.Theorem("∀n:num. n + 0 = n", func(a *Argument) {}),
})}
`

func TestPasteKey_InsertsUnderName(t *testing.T) {
	out, err := pasteKey([]byte(pasteFixture), "Alpha", "prop_aaaaaaaaaaaaaaaa", 4)
	if err != nil {
		t.Fatal(err)
	}
	want := "\tName: \"Alpha\",\n\tKey: \"prop_aaaaaaaaaaaaaaaa\",\n\tDeps:"
	if !strings.Contains(string(out), want) {
		t.Fatalf("Key not inserted under Name:\n%s", out)
	}
	if strings.Count(string(out), "prop_0000000000000000") != 1 {
		t.Fatalf("the other entry's Key moved:\n%s", out)
	}
}

func TestPasteKey_ReplacesStaleKey(t *testing.T) {
	pasted, err := pasteKey([]byte(pasteFixture), "Beta", "prop_bbbbbbbbbbbbbbbb", 11)
	if err != nil {
		t.Fatal(err)
	}
	// The door formats after the paste (xugofmt); the literal's
	// alignment is the formatter's.
	out, err := xugofmt.Source(pasted)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(out), "prop_0000000000000000") || !strings.Contains(string(out), "\tKey:   \"prop_bbbbbbbbbbbbbbbb\",\n") {
		t.Fatalf("stale Key not replaced in place:\n%s", out)
	}
	if strings.Count(string(out), "Key:") != 1 {
		t.Fatalf("a second Key line appeared:\n%s", out)
	}
}

func TestPasteKey_RefusesAnotherEntry(t *testing.T) {
	// From Beta's line on, the first Name is Beta's — asking for Alpha
	// there names the wrong entry.
	if _, err := pasteKey([]byte(pasteFixture), "Alpha", "prop_aaaaaaaaaaaaaaaa", 11); err == nil {
		t.Fatal("pasting Alpha's key from Beta's line must be refused")
	}
	if _, err := pasteKey([]byte(pasteFixture), "Gamma", "prop_cccccccccccccccc", 1); err == nil {
		t.Fatal("an entry with no Name line must be refused")
	}
}

const pasteOneLineFixture = `package fam

// Gamma — its Name line carries the literal's other fields.
var Gamma = family.Define(registry.DefEntry{
	Name: "Gamma", Const: "gamma", Type: "num",
	Equations: []string{"gamma = 0"},
})

// Delta — a key that moved, beside its Name.
var Delta = family.Define(registry.DefEntry{
	Name: "Delta", Key: "prop_0000000000000000", Const: "delta", Type: "num",
	Equations: []string{"delta = 0"},
})
`

func TestPasteKey_InsertsUnderAOneLineName(t *testing.T) {
	pasted, err := pasteKey([]byte(pasteOneLineFixture), "Gamma", "prop_cccccccccccccccc", 4)
	if err != nil {
		t.Fatal(err)
	}
	out, err := xugofmt.Source(pasted)
	if err != nil {
		t.Fatal(err)
	}
	want := regexp.MustCompile(`\tName: "Gamma", Const: "gamma", Type: "num",\n\tKey:\s+"prop_cccccccccccccccc",\n\tEquations:`)
	if !want.Match(out) {
		t.Fatalf("Key not inserted under the one-line Name:\n%s", out)
	}
	if strings.Count(string(out), "prop_0000000000000000") != 1 {
		t.Fatalf("the other entry's Key moved:\n%s", out)
	}
}

func TestPasteKey_ReplacesAKeyBesideName(t *testing.T) {
	pasted, err := pasteKey([]byte(pasteOneLineFixture), "Delta", "prop_dddddddddddddddd", 10)
	if err != nil {
		t.Fatal(err)
	}
	out, err := xugofmt.Source(pasted)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(out), "\tName: \"Delta\", Key: \"prop_dddddddddddddddd\", Const: \"delta\", Type: \"num\",\n") {
		t.Fatalf("the Key beside Name not replaced in place:\n%s", out)
	}
	if strings.Contains(string(out), "prop_0000000000000000") || strings.Count(string(out), "Key:") != 1 {
		t.Fatalf("the stale Key survived or a second Key appeared:\n%s", out)
	}
}

const pasteKeyLeadFixture = `package fam

// Epsilon — its Key line carries the literal's other fields.
var Epsilon = family.Define(registry.DefEntry{
	Name: "Epsilon",
	Key:  "prop_0000000000000000", Const: "epsilon", Type: "num",
	Equations: []string{"epsilon = 0"},
})
`

func TestPasteKey_ReplacesAKeyLeadingOtherFields(t *testing.T) {
	pasted, err := pasteKey([]byte(pasteKeyLeadFixture), "Epsilon", "prop_eeeeeeeeeeeeeeee", 4)
	if err != nil {
		t.Fatal(err)
	}
	out, err := xugofmt.Source(pasted)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(out), "\tKey:  \"prop_eeeeeeeeeeeeeeee\", Const: \"epsilon\", Type: \"num\",\n") {
		t.Fatalf("the Key leading the line not replaced in place:\n%s", out)
	}
	if strings.Count(string(out), "Key:") != 1 {
		t.Fatalf("a second Key line appeared:\n%s", out)
	}
}

const pasteInductiveFixture = `package fam

// reach — the smallest relation its two rules close.
var reach = family.DefineInductive(registry.InductiveEntry{
	Name:   "Reach",
	Const:  "reach",
	Type:   "(A → A → bool) → A → A → bool",
	Params: []string{"R"},
	Rules: []string{
		"∀x:A. reach(R, x, x)",
	},
})

// Gamma — a member after the definition.
var Gamma = family.Add(registry.ProofEntry{
	Name:  "Gamma",
	Build: family.Card("∀n:num. n = n", "a note"),
})
`

// TestPasteInductiveKey_MakesTheBlockAndKeepsTheStructsOrder: a literal
// with no Keys gets the block under its Name line; the keys pasted
// after it, in any order, stand in the order InductiveKeys declares
// them, and a key pasted again is replaced where it stands.
func TestPasteInductiveKey_MakesTheBlockAndKeepsTheStructsOrder(t *testing.T) {
	src := []byte(pasteInductiveFixture)
	for _, paste := range [][2]string{
		{"Cases", "prop_cccccccccccccccc"},
		{"Rules", "prop_aaaaaaaaaaaaaaaa"},
		{"InductStrong", "prop_dddddddddddddddd"},
		{"Induct", "prop_0000000000000000"},
		{"Induct", "prop_bbbbbbbbbbbbbbbb"},
	} {
		var err error
		if src, err = pasteInductiveKey(src, "Reach", paste[0], paste[1], 4); err != nil {
			t.Fatal(err)
		}
	}
	out, err := xugofmt.Source(src)
	if err != nil {
		t.Fatal(err)
	}
	want := "\tName: \"Reach\",\n" +
		"\tKeys: registry.InductiveKeys{\n" +
		"\t\tRules:        \"prop_aaaaaaaaaaaaaaaa\",\n" +
		"\t\tInduct:       \"prop_bbbbbbbbbbbbbbbb\",\n" +
		"\t\tCases:        \"prop_cccccccccccccccc\",\n" +
		"\t\tInductStrong: \"prop_dddddddddddddddd\",\n" +
		"\t},\n" +
		"\tConst:  \"reach\",\n"
	if !strings.Contains(string(out), want) {
		t.Fatalf("the Keys block is not the four keys in the struct's order under Name:\n%s", out)
	}
	if strings.Contains(string(out), "prop_0000000000000000") {
		t.Fatalf("the key pasted over is still there:\n%s", out)
	}
	if !strings.Contains(string(out), "\tName:  \"Gamma\",\n\tBuild:") {
		t.Fatalf("the member after the definition moved:\n%s", out)
	}
}

// TestPasteInductiveKey_Refuses: a Name line that is another literal's,
// a field InductiveKeys does not have, and a Keys block whose line is
// not a key on a line of its own.
func TestPasteInductiveKey_Refuses(t *testing.T) {
	if _, err := pasteInductiveKey([]byte(pasteInductiveFixture), "Reach", "Rules", "prop_aaaaaaaaaaaaaaaa", 15); err == nil {
		t.Fatal("the first Name line from line 15 on is Gamma's: the paste must refuse")
	}
	if _, err := pasteInductiveKey([]byte(pasteInductiveFixture), "Reach", "Strong", "prop_aaaaaaaaaaaaaaaa", 4); err == nil {
		t.Fatal("Strong is no field of registry.InductiveKeys: the paste must refuse")
	}
	oneLine := strings.Replace(pasteInductiveFixture, "\tName:   \"Reach\",\n",
		"\tName:   \"Reach\",\n\tKeys: registry.InductiveKeys{\n\t\tRules: \"prop_aaaaaaaaaaaaaaaa\", Cases: \"prop_cccccccccccccccc\",\n\t},\n", 1)
	if _, err := pasteInductiveKey([]byte(oneLine), "Reach", "Induct", "prop_bbbbbbbbbbbbbbbb", 4); err == nil {
		t.Fatal("two keys on one line of the block: the paste must refuse")
	}
}

// TestKeySpelling_NamesAnInductiveEntrysField: the gate and the replay
// harness tell an author where a key goes. An entry of an inductive
// definition is told the field of its literal's Keys that its suffix
// names; an entry with a literal of its own is told Key.
func TestKeySpelling_NamesAnInductiveEntrysField(t *testing.T) {
	var inductive, alone *registry.ProofEntry
	for _, e := range registry.All() {
		door, shared := e.Door()
		switch {
		case inductive == nil && shared && door.Door == "DefineInductive":
			inductive = e
		case alone == nil && !shared:
			alone = e
		}
	}
	if inductive == nil || alone == nil {
		t.Fatal("the corpus has no inductive definition's entry, or no entry registered alone")
	}
	door, _ := inductive.Door()
	field, where := keySpelling(inductive)
	if !slices.Contains(inductiveKeyFields, field) || door.Name+field != inductive.BareName() {
		t.Fatalf("%s: field %q is not the Keys field its suffix names", inductive.Name, field)
	}
	if want := "the Keys of the DefineInductive literal " + door.Name; where != want {
		t.Fatalf("%s: told %q, want %q", inductive.Name, where, want)
	}
	if field, where := keySpelling(alone); field != "Key" || where != "the entry" {
		t.Fatalf("%s: told %q in %q, want Key in the entry", alone.Name, field, where)
	}
}
