// key_lint_test.go — every entry's Key is its statement's own
// normalized key (registry.ProofEntry.Key).
//
// The replay harness checks the same equation per member, at replay;
// this is the corpus-wide, hermetic, ~1 s form — the check that runs at
// every landing before anything is forced — and the minting assistant
// for an entry registered without a Key. A statement edit moves the
// key, and the replay of the member's citers is what checks the move.
//
// The maintenance door, as the recorder has one: XUGO_PASTE_KEYS names
// the entries whose keys the gate WRITES — a family by its name
// (`<domain>/<family>`), a member by its entry name (`<family>.<Name>`),
// as XUGO_REPLAY_SCOPE reads them — and each missing or moved key among
// them goes into its entry, the literal `Key: "…",` under the entry's
// `Name:` line, inserted or replaced, the file formatted (xugofmt);
// the gate reports what it wrote instead of failing on it. An entry
// outside the scope is never written: in a tree several provers edit
// at once, each pastes its own member and no sibling's file moves
// under it. Its missing or moved key is reported, and does not fail
// the door's run — the run's verdict is the paste's, ok once every
// named key is written, so a caller reading the exit code alone reads
// a completed paste; the gate's run, without the variable, fails on
// that entry as on any other. The registry linked into this binary
// still holds the old keys, so the next build reads the pasted ones; a
// skeleton of forty cards is one run over its family, not forty pastes.
//
// An inductive definition's entries share one literal, which spells
// their keys in its Keys field (registry.InductiveKeys), one field per
// entry: the gate reports such a key by its field, and the door writes
// it there — the `Keys: registry.InductiveKeys{…},` block under the
// literal's `Name:` line, made when the literal has none.
//
//	XUGO_PASTE_KEYS=simplicial_set.BaseSimplexSucc go test -count=1 -run TestEntryKeyIsOwnKey ./library/integrity/gates/
//	XUGO_PASTE_KEYS=simplicial/simplicial_set,simplicial/kan_complex go test -count=1 -run TestEntryKeyIsOwnKey ./library/integrity/gates/
package gates

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/xugofmt"
)

// envPasteKeys names the entries TestEntryKeyIsOwnKey writes keys into.
const envPasteKeys = "XUGO_PASTE_KEYS"

func TestEntryKeyIsOwnKey(t *testing.T) {
	var paste map[string]bool
	if spec := strings.TrimSpace(os.Getenv(envPasteKeys)); spec != "" {
		paste = scopeEntries(t, envPasteKeys, spec)
	}
	type fix struct {
		entry *registry.ProofEntry
		own   string
		line  int
	}
	byFile := map[string][]fix{}
	// outside: under the paste door, the entries outside its scope
	// whose keys are missing or moved — reported, never written, and
	// not the door's verdict.
	var outside []string
	checked := 0
	all := registry.All()
	owns := fanOut(all, func(e *registry.ProofEntry) string { return string(e.Statement().Key()) })
	for i, e := range all {
		own := owns[i]
		unminted := strings.HasPrefix(e.Key, registry.UnmintedKeyPrefix)
		if !unminted && e.Key == own {
			checked++
			continue
		}
		if paste[e.Name] {
			if file, line, ok := sourceFileLine(e.Source()); ok {
				byFile[file] = append(byFile[file], fix{e, own, line})
				continue
			}
		}
		field, where := keySpelling(e)
		var finding string
		if unminted {
			finding = fmt.Sprintf("%s has no Key — its statement's normalized key is %s; paste  %s: %q  into %s (%s=%s writes it)", e.Name, own, field, own, where, envPasteKeys, e.Name)
		} else {
			finding = fmt.Sprintf("%s: Key %s is not the statement's own normalized key — paste  %s: %q  into %s (%s=%s writes it)", e.Name, e.Key, field, own, where, envPasteKeys, e.Name)
		}
		if paste != nil {
			outside = append(outside, finding)
			continue
		}
		t.Error(finding)
	}
	t.Logf("%d of %d entries carry their statement's own key", checked, len(registry.All()))
	if len(outside) > 0 {
		t.Logf("%d entries outside the paste scope carry no key or a moved one — not written here; the gate's run (no %s) fails on them:\n  %s",
			len(outside), envPasteKeys, strings.Join(outside, "\n  "))
	}
	if len(byFile) == 0 {
		return
	}
	files := make([]string, 0, len(byFile))
	for file := range byFile {
		files = append(files, file)
	}
	sort.Strings(files)
	pasted := 0
	for _, file := range files {
		p := filepath.Join(corpusRoot, filepath.FromSlash(file))
		src, err := os.ReadFile(p)
		if err != nil {
			t.Fatalf("paste: %v", err)
		}
		// Bottom-up: an inserted Key line moves every line below it, so
		// the entries are pasted from the last declared to the first and
		// no unpasted entry's recorded line goes stale. (Registration
		// order is Go's init order, which follows the references between
		// entries and not the file.)
		sort.Slice(byFile[file], func(i, j int) bool { return byFile[file][i].line > byFile[file][j].line })
		var names []string
		for _, f := range byFile[file] {
			if literal, keysField, ok := inductiveKeyField(f.entry); ok {
				src, err = pasteInductiveKey(src, literal, keysField, f.own, f.line)
			} else {
				src, err = pasteKey(src, f.entry.BareName(), f.own, f.line)
			}
			if err != nil {
				t.Fatalf("paste %s: %v", f.entry.Name, err)
			}
			names = append(names, f.entry.BareName())
		}
		out, err := xugofmt.Source(src)
		if err != nil {
			t.Fatalf("paste %s: the file does not format after the paste: %v", file, err)
		}
		if err := os.WriteFile(p, out, 0o644); err != nil {
			t.Fatalf("paste: %v", err)
		}
		pasted += len(names)
		t.Logf("%s: wrote %d key(s) — %s", file, len(names), strings.Join(names, ", "))
	}
	t.Logf("pasted %d key(s) into %d file(s); the tree carries them and the next build reads them", pasted, len(files))
}

// inductiveKeyField is, for an entry an inductive definition
// registered, the Name of the definition's literal and the field of
// its Keys that spells the entry's key: the entry's suffix, as the
// door names its entries Name+"Rules", +"Induct", +"Cases",
// +"InductStrong" and registry.InductiveKeys its fields.
func inductiveKeyField(e *registry.ProofEntry) (literal, field string, ok bool) {
	door, shared := e.Door()
	if !shared || door.Door != "DefineInductive" {
		return "", "", false
	}
	return door.Name, strings.TrimPrefix(e.BareName(), door.Name), true
}

// keySpelling is where the source spells e's key: the field, and the
// literal it stands in.
func keySpelling(e *registry.ProofEntry) (field, where string) {
	if literal, keysField, ok := inductiveKeyField(e); ok {
		return keysField, "the Keys of the DefineInductive literal " + literal
	}
	return "Key", "the entry"
}

// inductiveKeyFields is registry.InductiveKeys' fields in the order the
// struct declares them, which is the order a Keys block lists them in.
var inductiveKeyFields = []string{"Rules", "Induct", "Cases", "InductStrong"}

var (
	keysBlockOpen  = regexp.MustCompile(`^(\s*)Keys:\s*registry\.InductiveKeys\{\s*$`)
	keysBlockClose = regexp.MustCompile(`^\s*\},\s*$`)
	keysFieldLine  = regexp.MustCompile(`^(\s*)(\w+):\s*"[^"]*",\s*$`)
)

// pasteInductiveKey writes key into the Keys block of the inductive
// definition literal named literal whose var is declared at fromLine
// (1-based) of src, under field. The block stands among the literal's
// fields, each key on a line of its own; a field already there is
// replaced, one that is not is inserted in the struct's order, and a
// literal with no block gets one under its Name line. The result is
// not yet formatted.
func pasteInductiveKey(src []byte, literal, field, key string, fromLine int) ([]byte, error) {
	order := slices.Index(inductiveKeyFields, field)
	if order < 0 {
		return nil, fmt.Errorf("%s: %q is no field of registry.InductiveKeys", literal, field)
	}
	lines := strings.Split(string(src), "\n")
	if fromLine > len(lines) {
		return nil, fmt.Errorf("%s: declared at line %d, past the file's %d lines", literal, fromLine, len(lines))
	}
	nameAt := -1
	for i := fromLine - 1; i < len(lines); i++ {
		m := nameLiteralLine.FindStringSubmatch(lines[i])
		if m == nil {
			continue
		}
		if m[2] != literal {
			return nil, fmt.Errorf("%s: the first Name line after line %d names %q", literal, fromLine, m[2])
		}
		nameAt = i
		break
	}
	if nameAt < 0 {
		return nil, fmt.Errorf("%s: no `Name: %q,` line from line %d on", literal, literal, fromLine)
	}
	indent := nameLiteralLine.FindStringSubmatch(lines[nameAt])[1]
	insert := func(at int, added ...string) []byte {
		lines = append(lines[:at], append(added, lines[at:]...)...)
		return []byte(strings.Join(lines, "\n"))
	}
	keyLine := func(in string) string { return in + field + ": " + strconv.Quote(key) + "," }
	for i := nameAt + 1; i < len(lines); i++ {
		if nameLiteralLine.MatchString(lines[i]) {
			break
		}
		open := keysBlockOpen.FindStringSubmatch(lines[i])
		if open == nil {
			continue
		}
		for j := i + 1; j < len(lines); j++ {
			if keysBlockClose.MatchString(lines[j]) {
				return insert(j, keyLine(open[1]+"\t")), nil
			}
			m := keysFieldLine.FindStringSubmatch(lines[j])
			if m == nil {
				return nil, fmt.Errorf("%s: line %d of its Keys block is not a key on a line of its own: %q", literal, j+1, strings.TrimSpace(lines[j]))
			}
			switch at := slices.Index(inductiveKeyFields, m[2]); {
			case at < 0:
				return nil, fmt.Errorf("%s: its Keys block spells %q, no field of registry.InductiveKeys", literal, m[2])
			case at == order:
				lines[j] = keyLine(m[1])
				return []byte(strings.Join(lines, "\n")), nil
			case at > order:
				return insert(j, keyLine(m[1])), nil
			}
		}
		return nil, fmt.Errorf("%s: its Keys block does not close", literal)
	}
	return insert(nameAt+1, indent+"Keys: registry.InductiveKeys{", keyLine(indent+"\t"), indent+"},"), nil
}

// sourceFileLine splits a registration source "<file>:<line>" (the
// chapter file relative to library/proofs, and the entry var's line).
func sourceFileLine(source string) (file string, line int, ok bool) {
	file, lineText, found := strings.Cut(source, ":")
	if !found {
		return "", 0, false
	}
	line, err := strconv.Atoi(lineText)
	if err != nil || line < 1 {
		return "", 0, false
	}
	return file, line, true
}

var (
	keyLiteralLine  = regexp.MustCompile(`^(\s*)Key:\s*"[^"]*",`)
	nameLiteralLine = regexp.MustCompile(`^(\s*)Name:\s*"([^"]*)",`)
	keyBesideName   = regexp.MustCompile(`Key:\s*"[^"]*",`)
)

// pasteKey writes key into the entry literal of the member named bare
// whose var is declared at fromLine (1-based) of src. The literal's
// `Name:` line may carry its other fields after Name (`Name: "X",
// Const: "x", Type: "num",`). Its Key is replaced where it stands —
// beside Name on that line, or on a line of its own among the
// literal's fields — or, when the entry has none, a `Key: "…",` line
// is inserted under the Name line at its indentation. The Name line is
// looked for from fromLine on, and must come before another entry's;
// the result is not yet formatted (the literal's alignment moves).
func pasteKey(src []byte, bare, key string, fromLine int) ([]byte, error) {
	lines := strings.Split(string(src), "\n")
	if fromLine > len(lines) {
		return nil, fmt.Errorf("%s: declared at line %d, past the file's %d lines", bare, fromLine, len(lines))
	}
	nameAt := -1
	for i := fromLine - 1; i < len(lines); i++ {
		m := nameLiteralLine.FindStringSubmatch(lines[i])
		if m == nil {
			continue
		}
		if m[2] != bare {
			return nil, fmt.Errorf("%s: the first Name line after line %d names %q", bare, fromLine, m[2])
		}
		nameAt = i
		break
	}
	if nameAt < 0 {
		return nil, fmt.Errorf("%s: no `Name: %q,` line from line %d on", bare, bare, fromLine)
	}
	indent := nameLiteralLine.FindStringSubmatch(lines[nameAt])[1]
	keyField := "Key: " + strconv.Quote(key) + ","
	keyLine := indent + keyField
	if keyBesideName.MatchString(lines[nameAt]) {
		lines[nameAt] = keyBesideName.ReplaceAllLiteralString(lines[nameAt], keyField)
		return []byte(strings.Join(lines, "\n")), nil
	}
	// An existing Key field leads a line among the literal's fields,
	// before the next entry's Name line — alone, or with the fields the
	// author put beside it.
	for i := nameAt + 1; i < len(lines); i++ {
		if nameLiteralLine.MatchString(lines[i]) {
			break
		}
		if keyLiteralLine.MatchString(lines[i]) {
			// The Key field leads the line; the fields after it stay.
			lines[i] = keyLiteralLine.ReplaceAllString(lines[i], "${1}"+keyField)
			return []byte(strings.Join(lines, "\n")), nil
		}
		if strings.HasPrefix(strings.TrimSpace(lines[i]), "Build:") {
			break
		}
	}
	lines = append(lines[:nameAt+1], append([]string{keyLine}, lines[nameAt+1:]...)...)
	return bytes.Join([][]byte{[]byte(strings.Join(lines, "\n"))}, nil), nil
}
