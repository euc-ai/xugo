// scheme.go — the chapter: schemes, the locally ringed spaces covered by
// open sets isomorphic to prime spectra, and the prime spectrum of a ring
// as one.
//
// An open set U is affine when it is isomorphic, as a locally ringed
// space, to the spectrum of the ring of its own sections F(U): if U is
// isomorphic to the spectrum of any ring, that ring is isomorphic to
// F(U), so asking for the spectrum of F(U) asks for no more, and it names
// the ring without quantifying over a type of rings. The spectrum of
// F(U) has points of the type set(B), the prime ideals of a ring on a
// set of sections, and sections of the type set(B) → set(prod(B, B)) —
// fixed by B, so the definition is a formula like any other.

package scheme

import (
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/scheme/spec_functor"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// Scheme — `scheme(T, F, res)`: a locally
// ringed space every point of which lies in an open U such that U, with
// the restriction of the structure, is isomorphic to the spectrum of the
// ring of sections over U with its structure sheaf.
var Scheme = schemeThm{family.DefineStructure(registry.DefEntry{
	Name:    "Scheme",
	Key:     "prop_ee6768f177a8299e",
	Const:   "scheme",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → ring_ops(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    scheme(T, F, res) ⇔ " +
			"    locally_ringed_space(T, F, res) ∧ " +
			"    (∀x:A. " +
			"        x ∈ ⋃T ⇒ " +
			"        ∃U:set(A). " +
			"            U ∈ T ∧ " +
			"            x ∈ U ∧ " +
			"            (∃φ:(A → set(B)). ∃ψ:(set(set(B)) → (set(B) → set(prod(B, B))) → B). " +
			"                lrs_isomorphism(sheaf_restriction(F, U), spec_sheaf(F(U)), φ, ψ)))",
	},
})}

// LocallyRinged — a scheme is a locally ringed space.
var LocallyRinged = locallyRingedThm{family.Add(registry.ProofEntry{
	Name:  "LocallyRinged",
	Key:   "prop_c59292c257df28d",
	Build: Scheme.Axiom("locally_ringed_space(T, F, res)"),
})}

// SpecScheme — the prime spectrum of a ring, with its structure sheaf, is
// a scheme.
var SpecScheme = specSchemeThm{family.Add(registry.ProofEntry{
	Name: "SpecScheme",
	Key:  "prop_b0142ec7ef2e79ec",
	Deps: []registry.EntryLike{
		Scheme,
		structure_sheaf.SpecLocallyRinged,
		structure_sheaf.GlobalSections,
		spec_functor.SpecIsomorphism,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement("scheme(spec_sheaf(R))"),
		"locally ringed by SpecLocallyRinged; take U the whole spectrum for every point: its ring "+
			"of sections is isomorphic to the ring (GlobalSections), and SpecIsomorphism carries this "+
			"ring isomorphism to an isomorphism of the spectra with their structure sheaves"),
})}
