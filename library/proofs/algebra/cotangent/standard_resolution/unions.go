package standard_resolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var IncreasingAlgebraUnionDef = increasingAlgebraUnionDefThm{family.Define(registry.DefEntry{
	Name:  "IncreasingAlgebraUnionDef",
	Key:   "prop_74437191e5f9b21e",
	Const: "increasing_algebra_union",
	Type:  "ring_ops(A) → (num → ring_ops(B)) → ring_ops(B) → (A → B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:(num → ring_ops(B)). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    increasing_algebra_union(R, V, S, f) ⇔ " +
			"    ring_homomorphism(R, S, f) ∧ " +
			"    (∀k:num. " +
			"        ring_homomorphism(R, V(k), f) ∧ " +
			"        ring_homomorphism(V(k), V(k + 1), λy:B. y) ∧ " +
			"        ring_homomorphism(V(k), S, λy:B. y)) ∧ " +
			"    S.carrier = ⋃image(λk:num. V(k).carrier, 𝕌)",
	},
	Deps: []registry.EntryLike{},
	Reading: "An increasing sequence of R-subalgebras on one " +
		"host, with union S. Off-carrier operations may differ."})}

var StandardNameMapDef = standardNameMapDefThm{family.Define(registry.DefEntry{
	Name:  "StandardNameMapDef",
	Key:   "prop_dde9929962f45c49",
	Const: "standard_name_map",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → (B → C) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀g:(B → C). ∀n:num. ∀u:U. " +
			"    standard_name_map(R, S, T, g, n, u) = " +
			"    COND(n = 0, " +
			"        carrier_tag(T.carrier, g(inverse_on(S.carrier, carrier_tag(S.carrier), u))), " +
			"        standard_map(R, S, T, g, n - 1, u))",
	},
	Deps: []registry.EntryLike{StandardMapDef},
	Reading: "Names in degree zero are relabeled by carrier tags; successor " +
		"names are polynomials and use the preceding standard algebra map."})}

var StandardResolutionUnion = standardResolutionUnionThm{family.Add(registry.ProofEntry{
	Name: "StandardResolutionUnion",
	Key:  "prop_74c29c1c4be3ac6e",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀V:(num → ring_ops(B)). ∀S:ring_ops(B). ∀f:(A → B). ∀n:num.",
			Hypotheses: []string{
				"increasing_algebra_union(R, V, S, f)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
			},
			Conclusion: "standard_names⟨U:U⟩(R, S, n) = " +
				"⋃image(λk:num. " +
				"        image(standard_name_map⟨U:U⟩(R, V(k), S, λy:B. y, n), standard_names⟨U:U⟩(R, V(k), n)), " +
				"    𝕌) ∧ " +
				"(∀k:num. " +
				"    injective_on(standard_names⟨U:U⟩(R, V(k), n), " +
				"        standard_name_map⟨U:U⟩(R, V(k), S, λy:B. y, n)))",
		},
		"At degree zero relabel carrier injections. At each successor every polynomial has finite "+
			"support, which is contained in one stage; polynomial functoriality preserves injections."),
	Deps: []registry.EntryLike{IncreasingAlgebraUnionDef, StandardNameMapDef},
	Reading: "The equality is a union of images under induced " +
		"maps, not a literal union of independently chosen carrier tags.",
})}
