// xugo_fmt formats a chapter's Go as package xugofmt does: gofmt's
// layout, with each argument of a narration verb (Have, Show, Case,
// When, Leg, …) on a line of its own, the arguments of a list verb (By,
// BySets, Simp, …) on one line within 100 columns of the line's
// indentation and one to a line past them, any other line of code past
// them broken at a call's arguments, a literal's elements or a
// function's parameters, and a text past them laid out as a chain of
// literals joined by `+`, one line each: a statement, claim or term
// text by its structure, a label, note or reading by its words. It is
// gofmt's counterpart for the corpus, and TestLintXugoFmt holds every
// chapter file to it. A
// generated file is left as its generator wrote it.
//
// Usage, from the tree's root:
//
//	go run ./library/cmd/xugo_fmt -l library/proofs                # the files it would change
//	go run ./library/cmd/xugo_fmt -w library/proofs/<family dir>   # rewrite them in place
//	go run ./library/cmd/xugo_fmt <file>                           # print the formatted file
//
// A directory is walked for its .go files. The corpus, library/proofs,
// is all the command formats: an argument that is not the corpus of the
// tree holding it, or a file or a directory under it, is refused, and
// with it the whole command, before a file is read.
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"github.com/euc-ai/xugo/library/xugofmt"
)

func main() {
	os.Exit(run(os.Args[1:], os.Stdout, os.Stderr))
}

// run is the command on args, and its exit status: 0, 1 where a file
// did not format or could not be read or written, and 2 where the
// arguments are not ones the command takes, in which case no file is
// read.
func run(args []string, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("xugo_fmt", flag.ContinueOnError)
	flags.SetOutput(stderr)
	list := flags.Bool("l", false, "list the files whose formatting differs")
	write := flags.Bool("w", false, "write the formatted source back to each file")
	if err := flags.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return 0
		}
		return 2
	}
	if flags.NArg() == 0 {
		fmt.Fprintln(stderr, "usage: xugo_fmt [-l] [-w] FILE_OR_DIR...")
		return 2
	}
	refused := false
	for _, arg := range flags.Args() {
		if err := inCorpus(arg); err != nil {
			fmt.Fprintln(stderr, err)
			refused = true
		}
	}
	if refused {
		return 2
	}
	failed := false
	for _, arg := range flags.Args() {
		err := filepath.WalkDir(arg, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() || !strings.HasSuffix(path, ".go") {
				return nil
			}
			if err := formatFile(path, *list, *write, stdout); err != nil {
				fmt.Fprintln(stderr, err)
				failed = true
			}
			return nil
		})
		if err != nil {
			fmt.Fprintln(stderr, err)
			failed = true
		}
	}
	if failed {
		return 1
	}
	return 0
}

// inCorpus is nil where path is the corpus of the tree holding it, the
// library/proofs under the nearest go.mod above path, or stands under
// that directory, and is otherwise the refusal. It reads path as it is
// spelled, from the working directory, and asks only for the go.mod:
// path itself need not exist.
func inCorpus(path string) error {
	abs, err := filepath.Abs(path)
	if err != nil {
		return fmt.Errorf("xugo_fmt: %s: %w", path, err)
	}
	for dir := abs; ; {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			corpus := filepath.Join(dir, "library", "proofs")
			if under, err := filepath.Rel(corpus, abs); err == nil && filepath.IsLocal(under) {
				return nil
			}
			return fmt.Errorf("xugo_fmt: %s is outside %s: the command formats chapter files only, and formatted nothing", path, corpus)
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return fmt.Errorf("xugo_fmt: %s is outside a tree's library/proofs, with no go.mod above it: the command formats chapter files only, and formatted nothing", path)
		}
		dir = parent
	}
}

// formatFile formats the file at path: it lists the path where list is
// set and the layout differs, writes the layout back where write is
// set, and prints it to stdout where neither is.
func formatFile(path string, list, write bool, stdout io.Writer) error {
	src, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	out, err := xugofmt.Source(src)
	if err != nil {
		return fmt.Errorf("%s: %w", path, err)
	}
	changed := !bytes.Equal(src, out)
	if list && changed {
		fmt.Fprintln(stdout, path)
	}
	if write && changed {
		return os.WriteFile(path, out, 0o644)
	}
	if !list && !write {
		_, err = stdout.Write(out)
	}
	return err
}
