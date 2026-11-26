// Package on is the carrier phantom vocabulary: Go types standing for
// the SET a structure on a set is on, so that a structure fact and the
// points of its carrier agree in their Go types. `group_on(G)` at a proof's hypothesis is a value of
// `group.GroupFact[on.G]`, a group fact on G.carrier; a point x in it is a
// `*proof.Member[A, on.G]`, and a law read at that fact takes members
// of G.carrier alone: a point of another carrier is a compile error.
//
// A carrier letter names a BINDER, as a dimension letter does
// (ext/dimtypes): on.C is the binder c of the statement in scope, and
// the proof layer resolves it through the block's surface names, so it
// denotes the section's own variable after a rename. The binder is the
// carrier itself where it is a set, and the record's `carrier` field
// where it is a record — on.M under `module_on(R, M)` is M.carrier, the
// set the vectors lie in.
//
// This is a REFINEMENT vocabulary, like dimtypes and unlike
// ext.TypePhantom: two values that differ only in their carrier
// phantom hold terms of the same HOL type, and the kernel never sees
// the phantom. Dropping it is one explicit step (the Fact or the term
// a value holds).
//
// The letters are name-fixed, a Go type cannot capture a runtime name,
// and are the ones the corpus's structures bind as carriers and the
// ones its statements bind a bundle under, a primed binder under the
// letter's name and Prime (c' is CPrime). A carrier or bundle binder of
// another letter gets a letter here so a closure can bind its fact at
// it (`∀L:field_on(A).` is `L field.FieldFact[on.L]`).
//
// The package is named in proof files qualified, on.C, never through
// the dot import of library/authoring: its letters would collide with
// the statement letters A–E and the dimension letters N, M and K.
package on

import "reflect"

// Carrier is the constraint of the vocabulary: a zero-size Go type
// whose Binder names the statement binder the carrier is read off.
type Carrier interface{ Binder() string }

// letters is the vocabulary, every carrier phantom but Any.
var letters = []Carrier{C{}, R{}, M{}, N{}, CPrime{}, T{}, TPrime{}, S{}, P{}, V{}, L{}, G{}, H{}, K{}, F{}, Ob{}, Mor{}}

// Letter is the Go name of the carrier phantom naming binder (`c` is
// C, `c'` is CPrime), as a proof file spells it after `on.`; ok is
// false for a binder the vocabulary has no letter for, whose fact a
// closure binds untyped.
func Letter(binder string) (name string, ok bool) {
	for _, c := range letters {
		if c.Binder() == binder {
			return reflect.TypeOf(c).Name(), true
		}
	}
	return "", false
}

// C is the set binder c — the carrier a structure on a set states
// first.
type C struct{}

func (C) Binder() string { return "c" }

// R is the binder R — under `module_on(R, M)` the ring's record, whose
// carrier is the set of scalars.
type R struct{}

func (R) Binder() string { return "R" }

// M is the binder M — under `module_on(R, M)` the module's record,
// whose carrier is the set of vectors; under `metric_space(M, d)` the
// set of points.
type M struct{}

func (M) Binder() string { return "M" }

// N is the binder N — the second metric space of a map between two,
// `lipschitz_map(M, d, N, e, f)`.
type N struct{}

func (N) Binder() string { return "N" }

// CPrime is the binder c' — a second carrier set beside c, as a map
// between two subrings states it (`ring_transport.TransportHomAlong`).
type CPrime struct{}

func (CPrime) Binder() string { return "c'" }

// T is the binder T — a topology, the set of open sets a space and the
// sheaves over it are on.
type T struct{}

func (T) Binder() string { return "T" }

// TPrime is the binder T' — the second topology of a morphism of
// locally ringed spaces.
type TPrime struct{}

func (TPrime) Binder() string { return "T'" }

// S is the binder S — the target topology of a continuous map,
// `continuous_map(T, S, f)`, or the set a bundle binder names.
type S struct{}

func (S) Binder() string { return "S" }

// P is the binder P — the blocks of a partition, `set_partition(P)`.
type P struct{}

func (P) Binder() string { return "P" }

// V is the binder V — the module record of a double complex.
type V struct{}

func (V) Binder() string { return "V" }

// L is the binder L — the ambient field of the field chapters,
// `∀L:field_on(A).`, inside which the subfields are sets.
type L struct{}

func (L) Binder() string { return "L" }

// G, H and K name group records or subgroup carriers bound by a statement.
type (
	G struct{}
	H struct{}
	K struct{}
)

func (G) Binder() string { return "G" }
func (H) Binder() string { return "H" }
func (K) Binder() string { return "K" }

// F names a field record bound by a statement.
type F struct{}

func (F) Binder() string { return "F" }

// Ob and Mor are the binders Ob and Mor — a category's objects and
// morphisms.
type (
	Ob  struct{}
	Mor struct{}
)

func (Ob) Binder() string  { return "Ob" }
func (Mor) Binder() string { return "Mor" }

// Any is the carrier of a structure fact that carries no phantom of
// its own — an untyped Fact, an instance entry, a reading of a law
// whose structure has none. A law read there reads at Any, and takes
// members whose carrier is Any as well: what proof.MemberOf pairs.
// It names no binder.
type Any struct{}

func (Any) Binder() string { return "" }
