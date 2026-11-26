// Package gates is the corpus-wide check suite: the properties that hold
// of the library as a whole rather than of any one chapter. A chapter's
// own correctness is its replay — the kernel re-runs its proof. What that
// cannot see is everything the chapters must agree on: that each member's
// key is its own statement's key, that claim texts parse under the
// vocabulary they are written against, that a headline says what the built
// theorem says, that recorded CNF blobs match what a fresh replay refutes,
// that generated surfaces are not stale, and that the corpus DAG stays
// acyclic.
//
// The suite lives here, beside the DAG and the capability manifest, because
// all three ask the same kind of question and all three read the whole
// corpus. It is a test-only package: the two non-test files carry the corpus
// anchor and the bare-name proof vocabulary the gates' own proof bodies use.
//
// The gates read the corpus TWICE — through registry.All(), populated by the
// blank import below, and through the filesystem, rooted at corpusRoot. Both
// reaches can silently go to zero, and a gate suite that iterates nothing
// passes everything, so TestCorpusIsReachable checks the two against each
// other before anything else runs.
//
// Registration roots must not import this package; the reverse edge would be
// an import cycle.
package gates

import (
	"path/filepath"

	"github.com/euc-ai/xugo/library/registry"

	// The chapter aggregator: its blank imports register every family.
	_ "github.com/euc-ai/xugo/library/proofs"
)

// corpusRoot is where the chapters live, relative to THIS package's
// directory (a `go test` binary runs with its own package dir as the
// working directory). Every gate that walks the chapters is rooted here.
//
// The gates do not live inside the corpus, so the anchor is explicit,
// and one that is wrong is caught by TestCorpusIsReachable, which
// counts what the walk finds against what the registry says exists.
const corpusRoot = "../../proofs"

// chapterRel is the corpus-relative spelling of a walked path — the form
// an allowlist row is written in, and the form an error message reads
// best in. Every path-keyed table in this package is keyed this way, so a
// row stays valid however the gate suite and the chapters are arranged
// relative to each other.
func chapterRel(path string) string {
	rel, err := filepath.Rel(corpusRoot, path)
	if err != nil {
		return filepath.ToSlash(path)
	}
	return filepath.ToSlash(rel)
}

// familyDir is a family's package directory, rooted at corpusRoot.
// Family.Dir is stated relative to the corpus root (empty means it
// equals Family.Name, the flat convention), so this is the one place
// that turns a Family into a path.
func familyDir(f *registry.Family) string {
	return filepath.Join(corpusRoot, filepath.FromSlash(familyRel(f)))
}

// familyRel is the family's directory relative to the corpus root,
// slash-separated, whose basename is the package name the generators
// render for.
func familyRel(f *registry.Family) string {
	if f.Dir != "" {
		return f.Dir
	}
	return f.Name
}
