// Package proofs is the library's mathematics: one Go package per
// chapter, grouped by domain, and nothing else. It carries no code of
// its own — the file below is a list of blank imports, and that list is
// the corpus.
//
// The imports do two jobs. Building or testing this package compiles the
// whole family DAG, so the compiler-checked acyclicity holds on every
// build: a cross-chapter cycle is an import cycle, and a same-chapter one
// is a package-level variable initialization cycle. And importing a
// chapter runs its init, which registers its members into
// library/registry — where the replay harness, the CNF recorder, the DAG
// and the capability manifest all read the corpus from. Any consumer that
// needs the whole corpus registered imports this package for that effect.
//
// One line per DOMAIN, not per chapter. The directory layout states each
// chapter's position in the tower: a chapter sits under the domain whose
// objects its DEFINITIONAL layer is closed in, never the one its subject
// matter merely evokes. A domain with more than one chapter carries its
// own aggregator package (nat_num, int_num, real); a domain still holding
// a single chapter is imported directly here and grows an aggregator when
// its second chapter lands.
//
// A chapter must NOT import this package: the reverse edge is an import
// cycle. library/integrity/gates has the gates that notice a chapter on
// disk that never reaches this list, and a package under this directory
// that no import reaches.
package proofs

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra"
	_ "github.com/euc-ai/xugo/library/proofs/analysis"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian"
	_ "github.com/euc-ai/xugo/library/proofs/category"
	_ "github.com/euc-ai/xugo/library/proofs/causal"
	_ "github.com/euc-ai/xugo/library/proofs/complex"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes"
	_ "github.com/euc-ai/xugo/library/proofs/int_num"
	_ "github.com/euc-ai/xugo/library/proofs/iterate"
	_ "github.com/euc-ai/xugo/library/proofs/manifold"
	_ "github.com/euc-ai/xugo/library/proofs/measure"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num"
	_ "github.com/euc-ai/xugo/library/proofs/probability"
	// ℝ — the domain aggregator fans out to the construction tower and
	// to the theory chapters built on it. It, rather than this file,
	// imports them: Go's internal/ rule keeps other domains from reaching
	// the tower's construction packages, and the domain's shared
	// statement alphabet, directly — which is the point of the layout.
	_ "github.com/euc-ai/xugo/library/proofs/real"
	_ "github.com/euc-ai/xugo/library/proofs/relations"
	_ "github.com/euc-ai/xugo/library/proofs/scheme"
	_ "github.com/euc-ai/xugo/library/proofs/sets"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial"
	_ "github.com/euc-ai/xugo/library/proofs/topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector"
	_ "github.com/euc-ai/xugo/library/proofs/words"
)

// go generate on this package regenerates every chapter's generated
// files — the typed wrappers, the vocabulary surface and the package's
// doc comment — in one process. The generator links the corpus, and
// linking it is what a run costs: one chapter costs about what all of
// them do.
//
//go:generate go run github.com/euc-ai/xugo/library/cmd/gen_family -all
