// derivation_localization.go — a derivation carried to a localization.
// For a localization ρ of S and a module N over the localization, a
// derivation d of S into N read over S through ρ extends to the
// localization by the quotient rule, D(a/s) = (s • d(a) − a • d(s))/s²,
// and uniquely: the Leibniz rule at y · ρ(s) = ρ(a) leaves D(y) no other
// value.

package partial_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivationLocalizationDef — `derivation_localization(S, S', ρ, N, d,
// y)`: the quotient rule along the ring map ρ from S to S' — at y, for a
// representation y · ρ(s) = ρ(a) chosen with a and s in S and ρ(s) a unit
// of S', the member m of N with ρ(s)² • m = ρ(s) • d(a) − ρ(a) • d(s).
var DerivationLocalizationDef = derivationLocalizationDefThm{family.Define(registry.DefEntry{
	Name:  "DerivationLocalizationDef",
	Key:   "prop_dbe7c575755d13b8",
	Const: "derivation_localization",
	Type:  "ring_ops(B) → ring_ops(F) → (B → F) → module_ops(F, G) → (B → G) → F → G",
	Equations: []string{
		"∀S:ring_ops(B). ∀S':ring_ops(F). ∀ρ:(B → F). ∀N:module_ops(F, G). ∀d:(B → G). ∀y:F. " +
			"    derivation_localization(S, S', ρ, N, d, y) = " +
			"    induced_map(λz:prod(B, B). " +
			"            inverse_on(N.carrier, " +
			"                λm:G. N.smul(S'.mul(ρ(snd(z)), ρ(snd(z))), m), " +
			"                N.add(N.smul(ρ(snd(z)), d(fst(z))), N.neg(N.smul(ρ(fst(z)), d(snd(z)))))), " +
			"        {z:prod(B, B) | " +
			"            fst(z) ∈ S.carrier ∧ " +
			"            snd(z) ∈ S.carrier ∧ " +
			"            ring_unit(S', ρ(snd(z))) ∧ " +
			"            S'.mul(y, ρ(snd(z))) = ρ(fst(z))})",
	},
	Reading: "No multiplicative set is an argument: any denominator whose image is a unit " +
		"serves, and every such representation gives the one value when ρ is a localization " +
		"(DerivationExtendsUniquely), since the extension D satisfies ρ(s) • D(y) + y • D(ρ(s)) " +
		"= D(ρ(a)) at each. d takes values in N read over S through ρ, so a derivation into a " +
		"module over S itself is first carried into N by a linear map. Off the localization's " +
		"carrier, or with no representation, the value is a choice nothing reads.",
})}

// DerivationExtendsUniquely — for a localization ρ of S at a
// multiplicative set and a module N over the localization, a derivation
// d of S over R into N read over S through ρ extends to a derivation of
// the localization over R into N, the quotient rule, which agrees with d
// on S and is the only such derivation on the localization's carrier.
var DerivationExtendsUniquely = derivationExtendsUniquelyThm{family.Add(registry.ProofEntry{
	Name: "DerivationExtendsUniquely",
	Key:  "prop_85121c00fbbae05f",
	Reading: "Any multiplicative set, the powers of one t among them, and any presentation " +
		"of the localization, the fraction model or a subring of a ring where t is a unit. The " +
		"kernel condition of is_localization_on is load-bearing for existence: two " +
		"representations (a, s), (a', s') of y have u(as' − a's) = 0 for a denominator u, and " +
		"the Leibniz rule there, ρ(u) a unit and ρ(as' − a's) = 0, gives d(as') = d(a's), which " +
		"makes the two quotients agree. A zero denominator makes the localization the zero ring " +
		"and N a single point, where both conclusions hold. With N a localization of a module M " +
		"over S through ν and d = ν ∘ d₀, this is d₀ : S → M extended to S[1/t] → M[1/t].",
	Deps: []registry.EntryLike{
		DerivationLocalizationDef,
		DerivationOn,
		ring_localization.IsLocalizationOnDef,
		ring_localization.MultiplicativeSetDef,
		ring_ideal.RingUnitDef,
		equivalence.InducedMapDef,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InverseOnUnique,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		module.ModuleOn,
		module.SmulAddLeft,
		module.SmulAddRight,
		module.SmulMul,
		module.SmulNeg,
		module.AddGroupOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀Q:set(B). " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N:module_ops(F, G). " +
			"∀d:(B → G).",
		Hypotheses: []string{
			"is_localization_on(S, Q, S', ρ)",
			"module_on(S', N)",
			"derivation_on(R, S, f, scalar_restriction(ρ, N), d)",
		},
		Conclusion: "derivation_on(R, S', λa:A. ρ(f(a)), N, derivation_localization(S, S', ρ, N, d)) ∧ " +
			"(∀b:B. b ∈ S.carrier ⇒ derivation_localization(S, S', ρ, N, d, ρ(b)) = d(b)) ∧ " +
			"(∀D:(F → G). " +
			"    derivation_on(R, S', λa:A. ρ(f(a)), N, D) ∧ (∀b:B. b ∈ S.carrier ⇒ D(ρ(b)) = d(b)) ⇒ " +
			"    ∀y:F. y ∈ S'.carrier ⇒ D(y) = derivation_localization(S, S', ρ, N, d, y))",
	},
		"every y of S' has y ρ(s) = ρ(a) with s in Q, ρ(s) a unit (IsLocalizationOnDef, "+
			"RingUnitDef). Uniqueness: a derivation D extending d has ρ(s) • D(y) + y • d(s) = d(a), "+
			"so ρ(s)² • D(y) = ρ(s) • d(a) − ρ(a) • d(s), and scaling by the unit ρ(s)² is injective "+
			"on N (ModuleOn, SmulMul), so D(y) is the quotient rule's value at any representation "+
			"(InducedMapDef, InverseOnUnique). Existence: two representations give one value, by the "+
			"kernel condition as the Reading says (MultiplicativeSetDef, MapMul, SmulAddLeft, "+
			"SmulNeg); the value lies in N (InverseOnIn, InverseOnRight). Representing y + y' and y y' "+
			"over s s' (MapAdd, MapMul) the quotient rule is additive and Leibniz, a computation in N "+
			"over S' (SmulAddRight, SmulMul, AddGroupOn); at ρ(b) the representation (b, one) gives "+
			"d(b), d(one) being zero (MapOne), and so ρ(f(a)) goes to d(f(a)) = N.zero (DerivationOn)"),
})}
