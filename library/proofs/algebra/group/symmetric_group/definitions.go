// definitions.go — the permutations of a type, and the operations the
// group is built from.

package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// PermutationInhabited — a type always has a bijection of itself: the
// identity. The permutation type is carved out of the maps by
// bijectivity, and a type may only be carved out by a predicate
// something satisfies.
var PermutationInhabited = permutationInhabitedThm{family.Add(registry.ProofEntry{
	Name: "PermutationInhabited",
	Key:  "prop_808aa59c70433266",
	Build: family.Theorem("∃f:(A → A). injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌",
		func(a *Argument) {
			a.Take(a.Term("identity_map⟨A:A⟩"))
			a.Show(
				"the identity separates points and sends the type onto itself",
				By(functions.IdentityInjective, set_image.ImageI))
		}),
})}

// PermutationDef — the permutations of A: the maps of A to itself that
// are bijective — injective on the whole type, and sending the whole
// type onto itself — made a type. `permutation_map(p)` is the map a
// permutation is, and `permutation_of_map(f)` the permutation a
// bijective map is. PermutationDef.Retraction
// (`permutation_of_map(permutation_map(p)) = p`) and
// PermutationDef.Membership (a map is bijective exactly when it survives
// the round trip) are the two facts the type comes with.
var PermutationDef = family.DefineType(registry.TypeEntry{
	Name:      "Permutation",
	Type:      "permutation",
	Abs:       "permutation_of_map",
	Rep:       "permutation_map",
	Pred:      "λf:(A → A). injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌",
	Existence: PermutationInhabited,
})

// The type's two facts, as typed citation surfaces: a permutation is the
// permutation of its own map, and a map is the map of the permutation
// made from it exactly when it is bijective.
var (
	PermutationRetraction = permutationRetractionThm{PermutationDef.Retraction}
	PermutationMembership = permutationMembershipThm{PermutationDef.Membership}
)

// PermutationComposeDef — the product of two permutations: run q, then
// p. It is the composite map, made a permutation, and it is written
// `p * q` — the group chapter's symbol, declared here as this constant's
// notation, so the parser reads it wherever no built-in `*` serves the
// operands.
var PermutationComposeDef = permutationComposeDefThm{family.Define(registry.DefEntry{
	Name:     "PermutationComposeDef",
	Key:      "prop_7ed59291bf34b1c4",
	Const:    "permutation_compose",
	Type:     "permutation(A) → permutation(A) → permutation(A)",
	Notation: "p * q",
	Equations: []string{"∀p q:permutation(A). " +
		"    permutation_compose(p, q) = permutation_of_map(permutation_map(p) ∘ permutation_map(q))"},
	Deps: []registry.EntryLike{PermutationDef.Retraction},
})}

// PermutationIdentityDef — the identity permutation: the identity map,
// made a permutation.
var PermutationIdentityDef = permutationIdentityDefThm{family.Define(registry.DefEntry{
	Name:      "PermutationIdentityDef",
	Key:       "prop_c7915cfd8a911000",
	Const:     "permutation_identity",
	Type:      "permutation(A)",
	Equations: []string{"permutation_identity = permutation_of_map(identity_map⟨A:A⟩)"},
	Deps:      []registry.EntryLike{PermutationDef.Retraction},
})}

// PermutationInverseDef — the inverse permutation: each point is sent to
// the point p sends to it, through the carrier inverse on the whole type.
var PermutationInverseDef = permutationInverseDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationInverseDef",
	Key:   "prop_4b101879c97a634a",
	Const: "permutation_inverse",
	Type:  "permutation(A) → permutation(A)",
	Equations: []string{"∀p:permutation(A). " +
		"    permutation_inverse(p) = permutation_of_map(inverse_on(𝕌, permutation_map(p)))"},
	Deps: []registry.EntryLike{PermutationDef.Retraction},
})}

// PermutationGroupDef — the group of permutations of A: composition, the
// identity and the inverse on the whole type. A group of permutations is
// this group restricted to its own carrier, `restrict_group(permutation_group,
// h)`; the symmetric group on a set s is the carrier symmetric_group(s).
var PermutationGroupDef = permutationGroupDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationGroupDef",
	Key:   "prop_dfebb087a5074498",
	Const: "permutation_group",
	Type:  "group_ops(permutation(A))",
	Equations: []string{"permutation_group = " +
		"mk_group(permutation_compose⟨A:A⟩, permutation_identity, permutation_inverse, 𝕌)"},
	Deps: []registry.EntryLike{PermutationComposeDef, PermutationIdentityDef, PermutationInverseDef},
})}

// TranspositionDef — the transposition of a and b: the permutation that
// swaps the two points and leaves every other point where it is. When a
// and b are the same point it is the identity.
var TranspositionDef = transpositionDefThm{family.Define(registry.DefEntry{
	Name:  "TranspositionDef",
	Key:   "prop_b5d677f273645f49",
	Const: "transposition",
	Type:  "A → A → permutation(A)",
	Equations: []string{"∀a b:A. " +
		"    transposition(a, b) = permutation_of_map(λx:A. COND(x = a, b, COND(x = b, a, x)))"},
	Deps: []registry.EntryLike{PermutationDef.Retraction},
})}

// SymmetricGroupDef — the symmetric group on a set s: the permutations of
// the whole type that move no point outside s. These are the
// permutations of s, each extended by the identity; the whole type's
// permutations are the symmetric group on 𝕌, and every symmetric group
// is a subgroup of that one.
var SymmetricGroupDef = symmetricGroupDefThm{family.Define(registry.DefEntry{
	Name:  "SymmetricGroupDef",
	Key:   "prop_44c017b16b3e20f0",
	Const: "symmetric_group",
	Type:  "set(A) → set(permutation(A))",
	Equations: []string{"∀s:set(A). " +
		"    symmetric_group(s) = {p:permutation(A) | ∀x:A. x ∉ s ⇒ permutation_map(p, x) = x}"},
	Deps: []registry.EntryLike{PermutationDef.Retraction},
})}

// PermutationOrderDef — the order of a permutation s: the least positive
// exponent e at which s^e is the identity, chosen. Where such an exponent
// exists the choice is it (PermutationOrderUnique); a permutation no
// positive power of which is the identity has an unspecified order.
var PermutationOrderDef = permutationOrderDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationOrderDef",
	Key:   "prop_f267d7e004f233df",
	Const: "permutation_order",
	Type:  "permutation(A) → num",
	Equations: []string{
		"∀s:permutation(A). " +
			"    permutation_order(s) = " +
			"    εe:num. " +
			"        0 < e ∧ " +
			"        monoid_pow⟨A:permutation(A)⟩( " +
			"            (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
			"            permutation_identity⟨A:A⟩, " +
			"            s, " +
			"            e) = " +
			"        permutation_identity ∧ " +
			"        (∀d:num. " +
			"            0 < d ∧ " +
			"            monoid_pow⟨A:permutation(A)⟩( " +
			"                (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
			"                permutation_identity⟨A:A⟩, " +
			"                s, " +
			"                d) = " +
			"            permutation_identity ⇒ " +
			"            e ≤ d)",
	},
	Deps: []registry.EntryLike{PermutationComposeDef, PermutationIdentityDef},
})}
