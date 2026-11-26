package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/xugofmt"
)

// pastTheWidth is a file the formatter changes: its one declaration
// runs past the width and has a list to break.
const pastTheWidth = "package p\n\n" +
	"var x = f(firstArgumentOfTheCall, secondArgumentOfTheCall, thirdArgumentOfTheCall, fourthArgumentOfTheCall, fifth)\n"

// newTree is a tree of its own in a temporary directory, entered as the
// working directory: a go.mod, a chapter file in its corpus, and a file
// in a package beside the corpus and in a directory whose name the
// corpus's opens, each of them pastTheWidth.
func newTree(t *testing.T) (root string, files []string) {
	t.Helper()
	root = t.TempDir()
	files = []string{
		"library/proofs/family/member.go",
		"library/registry/registry.go",
		"library/proofs_old/member.go",
	}
	texts := map[string]string{"go.mod": "module example.test/tree\n"}
	for _, file := range files {
		texts[file] = pastTheWidth
	}
	for file, text := range texts {
		path := filepath.Join(root, filepath.FromSlash(file))
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	t.Chdir(root)
	return root, files
}

// An argument is taken where it is the corpus of the tree holding it,
// or stands under it, and is refused anywhere else: above the corpus,
// beside it, in a directory whose name opens as the corpus's does, and
// in no tree at all. The verdict is the same of a path from the working
// directory and of the absolute one.
func TestInCorpus(t *testing.T) {
	root, _ := newTree(t)
	cases := []struct {
		path  string
		taken bool
	}{
		{"library/proofs", true},
		{"library/proofs/", true},
		{"library/proofs/family", true},
		{"library/proofs/family/member.go", true},
		{"library/proofs/family/not_written_yet.go", true},
		{"library/registry/../proofs/family", true},
		{".", false},
		{"library", false},
		{"library/", false},
		{"library/registry", false},
		{"library/registry/registry.go", false},
		{"library/proofs_old/member.go", false},
		{"library/proofs/../registry", false},
		{"library/proofs/..", false},
	}
	for _, c := range cases {
		for _, path := range []string{c.path, filepath.Join(root, filepath.FromSlash(c.path))} {
			err := inCorpus(path)
			if c.taken && err != nil {
				t.Errorf("%s: refused: %v", path, err)
			}
			if !c.taken && err == nil {
				t.Errorf("%s: taken, and it is outside library/proofs", path)
			}
			if err != nil && !strings.Contains(err.Error(), path) {
				t.Errorf("%s: the refusal does not name the argument: %v", path, err)
			}
		}
	}
	if err := inCorpus(filepath.Join(t.TempDir(), "library", "proofs", "family")); err == nil {
		t.Errorf("a library/proofs under no go.mod is taken")
	}
}

// The corpus of the tree this test runs in is taken, in the form the
// checks give it, and the library above it is refused.
func TestInCorpusOfThisTree(t *testing.T) {
	t.Chdir(filepath.Join("..", "..", ".."))
	if err := inCorpus("library/proofs"); err != nil {
		t.Errorf("library/proofs: refused: %v", err)
	}
	if err := inCorpus("library/"); err == nil {
		t.Errorf("library/: taken")
	}
}

// An argument outside the corpus is refused before any file is read:
// the status is 2, the refusal names the argument, nothing is listed,
// and -w leaves every file as it was, the chapter file of the argument
// beside the refused one among them.
func TestRunRefusesAnArgumentOutsideTheCorpus(t *testing.T) {
	for _, outside := range []string{"library", "library/registry/registry.go", "library/proofs_old", "."} {
		for _, flags := range [][]string{{"-l"}, {"-w"}, {"-l", "-w"}, {}} {
			_, files := newTree(t)
			var stdout, stderr bytes.Buffer
			status := run(append(flags, "library/proofs", outside), &stdout, &stderr)
			if status != 2 {
				t.Errorf("%v %s: status %d, want 2", flags, outside, status)
			}
			if stdout.Len() != 0 {
				t.Errorf("%v %s: printed\n%s", flags, outside, stdout.String())
			}
			if !strings.Contains(stderr.String(), outside+" is outside") {
				t.Errorf("%v %s: the refusal is\n%s", flags, outside, stderr.String())
			}
			for _, file := range files {
				if text, err := os.ReadFile(file); err != nil || string(text) != pastTheWidth {
					t.Errorf("%v %s: %s was written: %v\n%s", flags, outside, file, err, text)
				}
			}
		}
	}
}

// Inside the corpus the command lists the file it would change, writes
// it as Source lays it out, lists nothing after, and prints a file's
// layout where it is given neither flag.
func TestRunFormatsTheCorpus(t *testing.T) {
	_, files := newTree(t)
	member := files[0]
	want, err := xugofmt.Source([]byte(pastTheWidth))
	if err != nil || string(want) == pastTheWidth {
		t.Fatalf("the fixture is to be a file Source changes: %v", err)
	}
	steps := []struct {
		args           []string
		stdout, onDisk string
	}{
		{[]string{member}, string(want), pastTheWidth},
		{[]string{"-l", "library/proofs"}, member + "\n", pastTheWidth},
		{[]string{"-w", "library/proofs/"}, "", string(want)},
		{[]string{"-l", "library/proofs"}, "", string(want)},
	}
	for _, step := range steps {
		var stdout, stderr bytes.Buffer
		if status := run(step.args, &stdout, &stderr); status != 0 || stderr.Len() != 0 {
			t.Fatalf("%v: status %d\n%s", step.args, status, stderr.String())
		}
		if stdout.String() != step.stdout {
			t.Errorf("%v: printed\n%s\nwant\n%s", step.args, stdout.String(), step.stdout)
		}
		if text, err := os.ReadFile(member); err != nil || string(text) != step.onDisk {
			t.Errorf("%v: the chapter file is\n%s\nwant\n%s", step.args, text, step.onDisk)
		}
	}
	for _, file := range files[1:] {
		if text, err := os.ReadFile(file); err != nil || string(text) != pastTheWidth {
			t.Errorf("%s, outside the corpus, was written", file)
		}
	}
}
