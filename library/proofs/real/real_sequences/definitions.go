// definitions.go — the chapter's definitional layer: what it means for
// a sequence to converge to a number, to be Cauchy and to have a
// cluster point, and the upper and lower limits of a bounded sequence.
//
// The convergence definition is the ε-N one and nothing more: `a ⟶ l`
// says that for every positive ε there is an index past which every
// term is within ε of l. No limit operator is minted beside it —
// `lim a` would be a chosen value that means nothing when a diverges,
// and every theorem about it would carry a convergence hypothesis
// anyway; the relation carries that hypothesis as its own truth.
//
// Two more are ε-N sentences with no limit named: a cluster point is a
// number the sequence returns within any positive distance of past
// every index — infinitely often — the limit of a subsequence rather
// than of the whole (ClusterPointSubsequence); and a Cauchy sequence's
// terms end up within any positive distance of EACH OTHER.
//
// The upper and lower limits ARE minted, as values: `real_limsup(a)` is the
// infimum of the suprema of a's tails, `real_liminf(a)` the supremum of
// their infima. Where `lim` would be a choice, they are formulas built
// from sup and inf, which name a number wherever the sequence is
// bounded — and they are the named witnesses the chapter's theorems
// hand over: the cluster point of Bolzano–Weierstrass, the limit of a
// Cauchy sequence.
//
// Every member's Argument receiver is `arg`, because the statements
// bind the sequence as `a`; a section lemma about numbers (LimitMul's)
// keeps `s`.
//
// One engine fact shapes every ε-N body in the chapter. Unfolding the
// goal's `real_converges_to` (or `real_cauchy`, `real_cluster_point`)
// also unfolds every resident hypothesis that mentions it, and leaves
// the closure's hypothesis Fact without a successor, so whatever a
// proof needs from its hypothesis — its ε-N statement,
// `arg.Unfolded(h, RealConvergesToDef)`, a fact cited from it — is
// stated BEFORE the goal is unfolded (the manual's `Unfold`, "The goal
// and every hypothesis").

package real_sequences

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealConvergesToDef — `a ⟶ l`: every positive distance around l is met by
// all the terms past some index.
var RealConvergesToDef = realConvergesToDefThm{family.Define(registry.DefEntry{
	Name:     "RealConvergesToDef",
	Key:      "prop_21709dd90fbebd59",
	Const:    "real_converges_to",
	Type:     "(num → real) → real → bool",
	Notation: "a ⟶ l",
	Equations: []string{
		"∀a:(num → real). ∀l:real. " +
			"    real_converges_to(a, l) ⇔ ∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
	},
	// The mints of the four constants the definiens spells: `<`,
	// real_abs, `-` and the embedding `&`.
})}

// RealCauchyDef — `real_cauchy(a)`: every positive distance is met by all pairs
// of terms past some index.
var RealCauchyDef = realCauchyDefThm{family.Define(registry.DefEntry{
	Name:  "RealCauchyDef",
	Key:   "prop_ded964e545009392",
	Const: "real_cauchy",
	Type:  "(num → real) → bool",
	Equations: []string{
		"∀a:(num → real). " +
			"    real_cauchy(a) ⇔ ∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |a(m) - a(n)| < ε",
	},
	// The same four mints as the convergence definition.
})}

// RealClusterPointDef — `real_cluster_point(a, l)`: past every index some term
// lies within any positive distance of l.
var RealClusterPointDef = realClusterPointDefThm{family.Define(registry.DefEntry{
	Name:  "RealClusterPointDef",
	Key:   "prop_e9098c65b045a137",
	Const: "real_cluster_point",
	Type:  "(num → real) → real → bool",
	Equations: []string{
		"∀a:(num → real). ∀l:real. " +
			"    real_cluster_point(a, l) ⇔ ∀ε:real. &0 < ε ⇒ ∀N:num. ∃n:num. N ≤ n ∧ |a(n) - l| < ε",
	},
	// The same four mints as the convergence definition.
})}

// RealLimsupDef — `real_limsup(a)`: the upper limit, the infimum of the suprema
// of a's tails.
var RealLimsupDef = realLimsupDefThm{family.Define(registry.DefEntry{
	Name:  "RealLimsupDef",
	Key:   "prop_7c2e8e8f6686a2dd",
	Const: "real_limsup",
	Type:  "(num → real) → real",
	Equations: []string{
		"∀a:(num → real). real_limsup(a) = inf(image(λN:num. sup(image(a, {n:num | N ≤ n})), 𝕌))",
	},
	// The mints of the constants the definiens spells: inf and sup, the
	// image and the universe, the set-builder, and ℕ's ≤.
})}

// RealLiminfDef — `real_liminf(a)`: the lower limit, the supremum of the infima
// of a's tails.
var RealLiminfDef = realLiminfDefThm{family.Define(registry.DefEntry{
	Name:  "RealLiminfDef",
	Key:   "prop_f6668d27c1015e2d",
	Const: "real_liminf",
	Type:  "(num → real) → real",
	Equations: []string{
		"∀a:(num → real). real_liminf(a) = sup(image(λN:num. inf(image(a, {n:num | N ≤ n})), 𝕌))",
	},
	// The same mints as the upper limit's.
})}
