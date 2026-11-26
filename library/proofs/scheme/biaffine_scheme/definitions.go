// definitions.go — the chapter's definitional layer: the points of the
// scheme a biaffine datum glues from its two charts, its topology, its
// sections over an open set with their restriction and ring operations,
// and the sheaf, its section rings and its stalk rings, each named once.
//
// A point is a pair of chart ideals (P₀, P₁): each a prime of its chart
// ring or the chart ring itself, where the point lies off that chart, not
// both the chart rings, and the two generating one ideal of the overlap R,
// a proper one when the point lies on both charts. A section over U is a
// pair of sections of the two charts' structure sheaves, over the primes
// U projects to on each chart, whose fractions agree at every point of U
// on both charts when both are read in R localized at that point.

package biaffine_scheme

import (
	"github.com/euc-ai/xugo/library/registry"
)

// wa1PointType is the type of a point, a pair of chart ideals, and
// wa1SectionType the type of a section, a pair of sections of the charts'
// structure sheaves.
const (
	wa1PointType   = "prod(set(A), set(A))"
	wa1SectionType = "prod((set(A) → set(prod(A, A))), (set(A) → set(prod(A, A))))"
)

// wa1Trace0 and wa1Trace1 are the primes of A₀ and of A₁ the points of the
// set u project to.
func wa1Trace0(u string) string { return "biaffine_trace(A₀, fst, " + u + ")" }
func wa1Trace1(u string) string { return "biaffine_trace(A₁, snd, " + u + ")" }

// wa1OneSection binds a section, in the equations of the section
// operations.
const (
	wa1OneSection = "∀σ:" + wa1SectionType + ". "
)

// ---------------------------------------------------------------------------
// The space
// ---------------------------------------------------------------------------

// biaffinePointsDef — `biaffine_points(R, A₀, A₁)`: the pairs of chart
// ideals (P₀, P₁), each a prime of its chart ring or that ring itself,
// not both the rings, generating one ideal of R, and a proper one when
// both are primes. Over a biaffine datum a prime of A₀ holding t
// generates all of R, t being a unit there, and is paired with A₁; one
// missing t generates a prime of R and is paired with that prime's trace
// on A₁.
var biaffinePointsDef = biaffinePointsDefThm{family.Define(registry.DefEntry{
	Name:  "biaffinePointsDef",
	Key:   "prop_534e83b0ac2db2aa",
	Const: "biaffine_points",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ")",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). " +
			"    biaffine_points(R, A₀, A₁) = " +
			"    {P:prod(set(A), set(A)) | " +
			"        (fst(P) = A₀ ∨ fst(P) ∈ prime_spectrum(restrict_ring(R, A₀))) ∧ " +
			"        (snd(P) = A₁ ∨ snd(P) ∈ prime_spectrum(restrict_ring(R, A₁))) ∧ " +
			"        ¬(fst(P) = A₀ ∧ snd(P) = A₁) ∧ " +
			"        ideal_span(R, fst(P)) = ideal_span(R, snd(P)) ∧ " +
			"        (¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁) ⇒ ¬(R.one ∈ ideal_span(R, fst(P))))}",
	},
})}

// biaffineTraceDef — `biaffine_trace(S, projection, U)`: the ideals of the
// chart ring S that the points of U project to, the points lying off that
// chart, which project to S itself, left out. At (A₀, fst) it is the part
// of U on chart 0 read as primes of A₀, at (A₁, snd) the part on chart 1.
var biaffineTraceDef = biaffineTraceDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineTraceDef",
	Key:   "prop_eb72fcb4c0a5d4e9",
	Const: "biaffine_trace",
	Type:  "set(A) → (" + wa1PointType + " → set(A)) → set(" + wa1PointType + ") → set(set(A))",
	Equations: []string{
		"∀S:set(A). ∀projection:(" + wa1PointType + " → set(A)). ∀U:set(" + wa1PointType + "). biaffine_trace(S, projection, U) = " +
			"{projection(P) | P:" + wa1PointType + " | P ∈ U ∧ ¬(projection(P) = S)}",
	},
})}

// biaffineTopologyDef — `biaffine_topology(R, A₀, A₁)`: the sets of
// points whose parts on the two charts are Zariski open, read as primes
// of A₀ and of A₁.
var biaffineTopologyDef = biaffineTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineTopologyDef",
	Key:   "prop_eaddeb1395274d4b",
	Const: "biaffine_topology",
	Type:  "ring_ops(A) → set(A) → set(A) → set(set(" + wa1PointType + "))",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). " +
			"    biaffine_topology(R, A₀, A₁) = " +
			"    {U:set(prod(set(A), set(A))) | " +
			"        U ⊆ biaffine_points(R, A₀, A₁) ∧ " +
			"        biaffine_trace(A₀, fst, U) ∈ zariski_topology(restrict_ring(R, A₀)) ∧ " +
			"        biaffine_trace(A₁, snd, U) ∈ zariski_topology(restrict_ring(R, A₁))}",
	},
	Deps: []registry.EntryLike{biaffinePointsDef, biaffineTraceDef},
})}

// ---------------------------------------------------------------------------
// Sections, restriction and the ring operations
// ---------------------------------------------------------------------------

// biaffineSectionsDef — `biaffine_sections(R, A₀, A₁, U)`: the pairs
// (s₀, s₁), s₀ a section of the structure sheaf of A₀ over the part of U
// on chart 0 and s₁ one of A₁ over the part on chart 1, whose fractions at
// every point P of U on both charts agree in R localized at the prime P
// generates there.
var biaffineSectionsDef = biaffineSectionsDefThm{family.Define(registry.DefEntry{
	Name: "biaffineSectionsDef",
	Key:  "prop_891225f6c4bc5993",
	Reading: "The clause asks agreement for every pair of representatives, " +
		"which is no more than agreement of the canonical images: A₀ ∖ fst(P) lies " +
		"in R ∖ Q for the ideal Q the point generates, so two representatives of " +
		"one fraction of A₀ give one fraction of R at Q, and likewise on chart 1.",
	Const: "biaffine_sections",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → set(" + wa1SectionType + ")",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀U:set(prod(set(A), set(A))). " +
			"    biaffine_sections(R, A₀, A₁, U) = " +
			"    {(s₀, s₁) | " +
			"        s₀:(set(A) → set(prod(A, A))), " +
			"        s₁:(set(A) → set(prod(A, A))) | " +
			"        s₀ ∈ structure_sections(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U)) ∧ " +
			"        s₁ ∈ structure_sections(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U)) ∧ " +
			"        (∀P:prod(set(A), set(A)). ∀a₀ b₀ a₁ b₁:A. " +
			"            P ∈ U ∧ " +
			"            ¬(fst(P) = A₀) ∧ " +
			"            ¬(snd(P) = A₁) ∧ " +
			"            (a₀, b₀) ∈ s₀(fst(P)) ∧ " +
			"            (a₁, b₁) ∈ s₁(snd(P)) ⇒ " +
			"            fraction_class(R.mul, R.carrier, R.carrier ∖ ideal_span(R, fst(P)), a₀, b₀) = " +
			"            fraction_class(R.mul, R.carrier, R.carrier ∖ ideal_span(R, fst(P)), a₁, b₁))}",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineRestrictDef — `biaffine_restrict(A₀, A₁, U, V, σ)`: each chart's
// section restricted to the part of V on that chart.
var biaffineRestrictDef = biaffineRestrictDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineRestrictDef",
	Key:   "prop_b45365f768806b50",
	Const: "biaffine_restrict",
	Type:  "set(A) → set(A) → set(" + wa1PointType + ") → set(" + wa1PointType + ") → " + wa1SectionType + " → " + wa1SectionType,
	Equations: []string{
		"∀A₀ A₁:set(A). ∀U V:set(" + wa1PointType + "). " + wa1OneSection + "biaffine_restrict(A₀, A₁, U, V, σ) = " +
			"(structure_restrict(" + wa1Trace0("U") + ", " + wa1Trace0("V") + ", fst(σ)), " +
			"structure_restrict(" + wa1Trace1("U") + ", " + wa1Trace1("V") + ", snd(σ)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineAddDef — `biaffine_add(R, A₀, A₁, U, σ, τ)`: the sum of two
// sections over U, chart by chart.
var biaffineAddDef = biaffineAddDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineAddDef",
	Key:   "prop_4d055356e6f7eddd",
	Const: "biaffine_add",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType + " → " + wa1SectionType + " → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀U:set(prod(set(A), set(A))). " +
			"∀σ τ:prod((set(A) → set(prod(A, A))), (set(A) → set(prod(A, A)))). " +
			"    biaffine_add(R, A₀, A₁, U, σ, τ) = " +
			"    (structure_add(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U), fst(σ), fst(τ)), " +
			"        structure_add(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U), snd(σ), snd(τ)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineZeroDef — `biaffine_zero(R, A₀, A₁, U)`: the zero section over U.
var biaffineZeroDef = biaffineZeroDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineZeroDef",
	Key:   "prop_4bc5a8c7c4f3b9fa",
	Const: "biaffine_zero",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀U:set(prod(set(A), set(A))). " +
			"    biaffine_zero(R, A₀, A₁, U) = " +
			"    (structure_zero(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U)), " +
			"        structure_zero(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineNegDef — `biaffine_neg(R, A₀, A₁, U, σ)`: the negation of a
// section over U.
var biaffineNegDef = biaffineNegDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineNegDef",
	Key:   "prop_3f3ed37ac31111d2",
	Const: "biaffine_neg",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType + " → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀U:set(prod(set(A), set(A))). " +
			"∀σ:prod((set(A) → set(prod(A, A))), (set(A) → set(prod(A, A)))). " +
			"    biaffine_neg(R, A₀, A₁, U, σ) = " +
			"    (structure_neg(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U), fst(σ)), " +
			"        structure_neg(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U), snd(σ)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineMulDef — `biaffine_mul(R, A₀, A₁, U, σ, τ)`: the product of two
// sections over U.
var biaffineMulDef = biaffineMulDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineMulDef",
	Key:   "prop_257e6a8a1bd40190",
	Const: "biaffine_mul",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType + " → " + wa1SectionType + " → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀U:set(prod(set(A), set(A))). " +
			"∀σ τ:prod((set(A) → set(prod(A, A))), (set(A) → set(prod(A, A)))). " +
			"    biaffine_mul(R, A₀, A₁, U, σ, τ) = " +
			"    (structure_mul(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U), fst(σ), fst(τ)), " +
			"        structure_mul(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U), snd(σ), snd(τ)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineOneDef — `biaffine_one(R, A₀, A₁, U)`: the one section over U.
var biaffineOneDef = biaffineOneDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineOneDef",
	Key:   "prop_5ad2e7fb58f8ba4d",
	Const: "biaffine_one",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀U:set(prod(set(A), set(A))). " +
			"    biaffine_one(R, A₀, A₁, U) = " +
			"    (structure_one(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U)), " +
			"        structure_one(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// biaffineSubDef — `biaffine_sub(R, A₀, A₁, U, σ, τ)`: the difference of
// two sections over U.
var biaffineSubDef = biaffineSubDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineSubDef",
	Key:   "prop_4e1e6854b45175a4",
	Const: "biaffine_sub",
	Type:  "ring_ops(A) → set(A) → set(A) → set(" + wa1PointType + ") → " + wa1SectionType + " → " + wa1SectionType + " → " + wa1SectionType,
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀U:set(prod(set(A), set(A))). " +
			"∀σ τ:prod((set(A) → set(prod(A, A))), (set(A) → set(prod(A, A)))). " +
			"    biaffine_sub(R, A₀, A₁, U, σ, τ) = " +
			"    (structure_sub(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U), fst(σ), fst(τ)), " +
			"        structure_sub(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U), snd(σ), snd(τ)))",
	},
	Deps: []registry.EntryLike{biaffineTraceDef},
})}

// ---------------------------------------------------------------------------
// The sheaf, its section rings and its stalk rings, named once
// ---------------------------------------------------------------------------

// biaffineSectionOps — the ring record of sections over the open W.
var biaffineSectionOps = biaffineSectionOpsThm{family.Define(registry.DefEntry{
	Name: "biaffineSectionOps",
	Key:  "prop_5fd7004d49499010", Const: "biaffine_section_ops",
	Type: "ring_ops(A) → set(A) → set(A) → set(prod(set(A), set(A))) → ring_ops(" + wa1SectionType + ")",
	Equations: []string{
		"∀R:ring_ops(A). ∀X Y:set(A). ∀W:set(prod(set(A), set(A))). " +
			"    biaffine_section_ops(R, X, Y, W) = " +
			"    mk_ring(biaffine_add(R, X, Y, W), " +
			"        biaffine_zero(R, X, Y, W), " +
			"        biaffine_neg(R, X, Y, W), " +
			"        biaffine_mul(R, X, Y, W), " +
			"        biaffine_one(R, X, Y, W), " +
			"        biaffine_sub(R, X, Y, W), " +
			"        biaffine_sections(R, X, Y, W))",
	},
	Deps: []registry.EntryLike{
		biaffineAddDef,
		biaffineZeroDef,
		biaffineNegDef,
		biaffineMulDef,
		biaffineOneDef,
		biaffineSubDef,
		biaffineSectionsDef,
	},
})}

// BiaffineSheaf — the glued topology, section-ring family and restriction.
var BiaffineSheaf = family.Tuple("biaffine_sheaf", []string{"R", "X", "Y"},
	"biaffine_topology(R, X, Y)", "biaffine_section_ops(R, X, Y)", "biaffine_restrict(X, Y)")

// biaffineStalkOps — the ring record of germs at the point P.
var biaffineStalkOps = biaffineStalkOpsThm{family.Define(registry.DefEntry{
	Name: "biaffineStalkOps",
	Key:  "prop_2d5e30fecaf44966", Const: "biaffine_stalk_ops",
	Type: "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → ring_ops(set(prod(set(prod(set(A), set(A))), " + wa1SectionType + ")))",
	Equations: []string{
		"∀R:ring_ops(A). ∀X Y:set(A). ∀P:prod(set(A), set(A)). " +
			"    biaffine_stalk_ops(R, X, Y, P) = " +
			"    stalk_ring(biaffine_topology(R, X, Y), " +
			"        biaffine_section_ops(R, X, Y), " +
			"        biaffine_restrict(X, Y), " +
			"        P)",
	},
	Deps: []registry.EntryLike{biaffineTopologyDef, biaffineSectionOps, biaffineRestrictDef},
})}
