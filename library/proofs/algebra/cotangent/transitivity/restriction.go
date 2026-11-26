// restriction.go — the restriction of a cohomology class along a ring
// map ρ from S to S', with its coefficients carried by a map ν into a
// module over S': first composition with ν, a class of D^n(S/R, N'),
// then the preimage under the right map D^n(S'/R, N') → D^n(S/R, N') of
// the sequence of the tower R → S → S'. The cohomology is contravariant
// in the algebra, so this map, which runs from S to S', exists where the
// right map is a bijection, as it is for a localization.

package transitivity

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CotangentCohomologyRestrictionDef —
// `cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n, x)`: the
// class x of D^n(S/R, N) carried to D^n(S'/R, N') — its image under
// composition with ν, a class of D^n(S/R, N') with N' read over S through
// ρ, taken back along co_transitivity_right_map(R, S, f, S', ρ, N', n) by
// inverse_on on the classes of D^n(S'/R, N').
var CotangentCohomologyRestrictionDef = cotangentCohomologyRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentCohomologyRestrictionDef",
	Key:   "prop_9442c0866abb7ecc",
	Const: "cotangent_cohomology_restriction",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(F) → " +
		"(B → F) → " +
		"module_ops(F, G) → " +
		"(D → G) → " +
		"num → " +
		"set(U → D) → " +
		"set(U → G)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G). " +
			"∀n:num. " +
			"∀x:set(U → D). " +
			"    cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n, x) = " +
			"    inverse_on(cotangent_cohomology(R, S', λa:A. ρ(f(a)), S', λy:F. y, N', n).carrier, " +
			"        co_transitivity_right_map(R, S, f, S', ρ, N', n), " +
			"        cohomology_map(cotangent_cochain(R, S, f, S', ρ, N'), " +
			"            λk:num. λw:(U → D). λu:U. ν(w(u)), " +
			"            n, " +
			"            x))",
	},
	Reading: "The source module N is not an argument: its classes are sets of cochains on " +
		"the host with values in D, and only ν reads them. The map is the restriction of a class " +
		"on S to the localization S' when ρ is one, where the right map is a bijection on the " +
		"classes (LocalizationRightMapIsomorphism) and inverse_on picks the one preimage; for a " +
		"map ρ whose right map is not onto, the value off its image is a choice nothing reads. " +
		"With ν linear over S it is linear over S (CotangentCohomologyRestrictionHom). The " +
		"letter U is the host's, fixed by the universe hypotheses of the statements that read it.",
	Deps: []registry.EntryLike{CoTransitivityRightMapDef},
})}
