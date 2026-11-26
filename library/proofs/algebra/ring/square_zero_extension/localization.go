// localization.go — a square-zero extension localized at a lift. For an
// extension E of S by N over R and a lift t' of a member t of S, the
// ring of E with the powers of t' inverted is an extension of S[1/t] by
// N[1/t]: its members are fraction classes, since the ring of an
// extension has no ambient ring to compute in, while S[1/t] and N[1/t]
// are any localizations of S and of N at the powers of t, given with
// their maps ρ and ν — the fraction model, or a subring of a ring where
// t is a unit with the identity. Two lifts of t give isomorphic
// localizations, a unit plus a member of square zero staying a unit, and
// the split extension localizes to the split extension of the
// localizations.

package square_zero_extension

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the localization
// ---------------------------------------------------------------------------

// fractionRing spells the ring of fraction classes of the ring record r
// with denominators in s, as a ring record.
func fractionRing(r, s string) string {
	return "mk_ring(fraction_add(" + r + ".add, " + r + ".mul, " + r + ".carrier, " + s + "), fraction_zero(" + r + ".zero, " + r + ".mul, " + r + ".one, " + r + ".carrier, " + s + "), fraction_neg(" + r + ".neg, " + r + ".mul, " + r + ".carrier, " + s + "), fraction_mul(" + r + ".mul, " + r + ".carrier, " + s + "), fraction_one(" + r + ".mul, " + r + ".one, " + r + ".carrier, " + s + "), fraction_sub(" + r + ".add, " + r + ".neg, " + r + ".mul, " + r + ".carrier, " + s + "), ring_localization(" + r + ".mul, " + r + ".carrier, " + s + "))"
}

// liftPowers are the powers of the lift t' in the ring of E; fractionOf
// is the class of e over v among E's fractions at them.
const liftPowers = "monoid_powers(E.ring.mul, E.ring.one, t')"

func fractionOf(e, v string) string {
	return "fraction_class(E.ring.mul, E.ring.carrier, " + liftPowers + ", " + e + ", " + v + ")"
}

// ---------------------------------------------------------------------------
// The localized extension
// ---------------------------------------------------------------------------

// SquareZeroLocalizationDef — `square_zero_localization(N, S', ρ, N', ν,
// E, t')`: the extension E with the powers of t' inverted — the fraction
// classes of E's ring at the powers of t', with structure map
// a ↦ E.structure(a) / 1, inclusion m ↦ i(n) / v for a pair (n, v) of a
// member of N and a power of t' chosen with ρ(p(v)) • m = ν(n), and
// projection e / v ↦ ρ(p(e)) / ρ(p(v)) computed in S' at a chosen
// representative.
var SquareZeroLocalizationDef = squareZeroLocalizationDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroLocalizationDef",
	Key:   "prop_3ea252a45b409142",
	Const: "square_zero_localization",
	Type: "module_ops(B, D) → " +
		"ring_ops(F) → " +
		"(B → F) → " +
		"module_ops(F, G) → " +
		"(D → G) → " +
		"square_zero_ops(A, B, C, D) → " +
		"C → " +
		"square_zero_ops(A, F, set(prod(C, C)), G)",
	Equations: []string{
		"∀N:module_ops(B, D). ∀S':ring_ops(F). ∀ρ:(B → F). ∀N':module_ops(F, G). ∀ν:(D → G). ∀E:square_zero_ops(A, B, C, D). ∀t':C. square_zero_localization(N, S', ρ, N', ν, E, t') = mk_square_zero(" + fractionRing(
			"E.ring",
			liftPowers) + ", λa:A. " + fractionOf(
			"E.structure(a)",
			"E.ring.one") + ", λm:G. induced_map(λz:prod(D, C). " + fractionOf(
			"E.inclusion(fst(z))",
			"snd(z)") + ", {z:prod(D, C) | fst(z) ∈ N.carrier ∧ snd(z) ∈ " + liftPowers + " ∧ N'.smul(ρ(E.projection(snd(z))), m) = ν(fst(z))}), induced_map(λz:prod(C, C). inverse_on(S'.carrier, λy:F. S'.mul(y, ρ(E.projection(snd(z)))), ρ(E.projection(fst(z))))))",
	},
	Reading: "The ring is always fraction classes: an extension's ring sits in no " +
		"ambient ring where t' could be inverted. S' and N' are arguments, any localization " +
		"of S and of N at the powers of t = p(t') with their maps ρ and ν, so the fraction " +
		"model (ρ = to_fraction) and a subring of a ring where t is a unit (ρ the identity, " +
		"RingAwayIsLocalization with SpanIsModuleLocalization) are both instances. Of N only " +
		"the carrier is read, to keep the chosen representation of m inside N. The inclusion " +
		"and the projection read one chosen representative; the choice is immaterial exactly " +
		"under the localization hypotheses of SquareZeroLocalizationIsExtension, ρ(p(v)) " +
		"being a unit of S' there; elsewhere the values are junk nothing reads.",
})}

// ---------------------------------------------------------------------------
// The algebra of the localization
// ---------------------------------------------------------------------------

// SquareZeroLocalizationIsExtension — for an extension E of S by N over
// R, a lift t' of t, a localization S' of S and a localization N' of N at
// the powers of t, the localization of E at t' is a square-zero extension
// of S' by N' over R; its projection reads e / v as ρ(p(e)) / ρ(p(v)),
// and its inclusion reads m as i(n) / v whenever ρ(p(v)) • m = ν(n).
var SquareZeroLocalizationIsExtension = squareZeroLocalizationIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroLocalizationIsExtension",
	Key:  "prop_5f04276615d489e8",
	Reading: "The two kernel conditions are load-bearing for the kernel of the projection: e / v " +
		"projects to zero exactly when tᵏ p(e) = 0 for some k(is_localization_on), so t'ᵏ e lies in " +
		"i(N), and e / v = i(n) / (t'ᵏ v) is the inclusion's image; and the inclusion is injective " +
		"because i(n)/v = 0 forces i(tᵏ • n) = 0, so ν(n) = 0. At v = one the last conjunct says " +
		"i(n)/1 is the inclusion of ν(n), so e ↦ e/1 is a map of extensions over ρ that is ν on the " +
		"kernel. t nilpotent makes S' and N' zero and t' nilpotent (t'ᵏ = i(n) has square zero), the " +
		"localization the zero ring, and the statement holds there. The module kernel condition is " +
		"also what makes the inclusion independent of the representation (n, v) chosen for m.",
	Deps: []registry.EntryLike{
		SquareZeroLocalizationDef,
		SquareZeroExtension,
		ProjectionOnto,
		InclusionAction,
		InclusionSquareZero,
		InclusionInjective,
		ring_localization.LocalizationRing,
		ring_localization.ToFractionHomomorphism,
		ring_localization.FractionClassEq,
		ring_localization.FractionClassMember,
		ring_localization.FractionAddClass,
		ring_localization.FractionMulClass,
		ring_localization.FractionZeroIff,
		ring_localization.RingLocalizationDef,
		ring_localization.IsLocalizationOnDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_localization.MultiplicativeSetDef,
		comm_monoid.MonoidPowersDef,
		comm_monoid.MapPow,
		equivalence.InducedMapDef,
		functions.InverseOnIn,
		functions.InverseOnRight,
		ring_ideal.RingUnitDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomSmul,
		module.SmulMul,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapMul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀t:B. " +
			"∀t':C. " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"t' ∈ E.ring.carrier",
			"E.projection(t') = t",
			"«baseLocalization»",
			"«coefficientLocalization»",
		},
		Conclusion: "square_zero_extension(R, S', λa:A. ρ(f(a)), N', «localized») ∧ " +
			"(∀e v:C. " +
			"    e ∈ E.ring.carrier ∧ v ∈ monoid_powers(E.ring.mul, E.ring.one, t') ⇒ " +
			"    S'.mul(«localized».projection(«fractionOf»(e, v)), ρ(E.projection(v))) = " +
			"    ρ(E.projection(e))) ∧ " +
			"(∀n:D. ∀v:C. ∀m:G. " +
			"    n ∈ N.carrier ∧ " +
			"    v ∈ monoid_powers(E.ring.mul, E.ring.one, t') ∧ " +
			"    m ∈ N'.carrier ∧ " +
			"    N'.smul(ρ(E.projection(v)), m) = ν(n) ⇒ " +
			"    «localized».inclusion(m) = «fractionOf»(E.inclusion(n), v))",
		Abbrev: Abbrev{
			{Name: "fractionOf", Text: "fraction_class(E.ring.mul, " +
				"    E.ring.carrier, " +
				"    monoid_powers(E.ring.mul, E.ring.one, t'))"},
			{Name: "localized", Text: "square_zero_localization(N, S', ρ, N', ν, E, t')"},
		},
	},
		"the powers of t' are a multiplicative set of E's ring (MonoidPowersDef, "+
			"MultiplicativeSetDef), so the classes are a commutative ring and e ↦ e/1 a ring map "+
			"(LocalizationRing, ToFractionHomomorphism), which makes the structure map one over R. "+
			"p(t'ᵏ) = tᵏ (MapPow), whose image under ρ is a unit of S' (IsLocalizationOnDef), so the "+
			"projection is well defined: related pairs have equal quotients, the witness's image "+
			"cancelling (FractionClassEq, InducedMapDef, InverseOnIn, InverseOnRight); it is a ring "+
			"map (FractionAddClass, FractionMulClass), onto by the fraction representation of S' and p "+
			"onto (ProjectionOnto), and ρ(f(a)) after the structure map. The inclusion: a "+
			"representation (n, v) of m exists by the fraction condition of IsModuleLocalizationOnDef, "+
			"and two representations give one class, their difference ν(p(v')•n − p(v)•n') = 0 being "+
			"killed by a tᵏ (its kernel condition) and t'ᵏ i(x) = i(tᵏ • x) (InclusionAction); that is "+
			"the last conjunct. Additivity and the action e/v • i(n)/v' = i(p(e)•n)/(v v') follow at "+
			"representatives (FractionAddClass, FractionMulClass, HomSmul, SmulMul), square zero from "+
			"E's (InclusionSquareZero), injectivity from FractionZeroIff and the injectivity of i "+
			"(InclusionInjective), and the kernel of the projection is the image as the Reading says"),
})}

// SquareZeroLocalizationIndependent — two lifts t₁, t₂ of t give
// isomorphic localizations: e / t₁ᵏ ↦ e (2t₂ − t₁)ᵏ / t₂²ᵏ is an
// isomorphism of extensions, over R, the identity on N' and over S'.
var SquareZeroLocalizationIndependent = squareZeroLocalizationIndependentThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroLocalizationIndependent",
	Key:  "prop_55a000632846a7e3",
	Reading: "t₂ − t₁ lies in the kernel of the projection, so it is i(n) and squares to " +
		"zero; hence t₁(2t₂ − t₁) = t₂² − (t₂ − t₁)² = t₂², and t₁ is a unit among the fractions " +
		"at t₂ with inverse (2t₂ − t₁)/t₂². The map is written as a union over the " +
		"representations (e, t₁ᵏ) of a class, as the fraction operations are; every " +
		"representation gives one class, the image of e/t₁ᵏ under the ring map the universal " +
		"property gives, so no representative is chosen. At t₁ = t₂ it is the identity on classes.",
	Deps: []registry.EntryLike{
		SquareZeroLocalizationIsExtension,
		ring_ideal.UnitPlusSquareZeroIsUnit,
		SquareZeroIsomorphismDef,
		InclusionImage,
		InclusionSquareZero,
		ring_localization.IsModuleLocalizationOnDef,
		ring_localization.LocalizationUniversal,
		ring_localization.ToFractionIsLocalization,
		ring_localization.LocalizationHomomorphismExtensional,
		ring_localization.FractionClassEq,
		ring_localization.FractionMulClass,
		ring_localization.DenominatorUnit,
		ring_homomorphism.RingIsomorphismDef,
		comm_monoid.MonoidPowDef,
		comm_monoid.MulPowOn,
		comm_monoid.MapPow,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀t:B. " +
			"∀t₁ t₂:C. " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"t₁ ∈ E.ring.carrier",
			"t₂ ∈ E.ring.carrier",
			"E.projection(t₁) = t",
			"E.projection(t₂) = t",
			"«baseLocalization»",
			"«coefficientLocalization»",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N', " +
			"    square_zero_localization(N, S', ρ, N', ν, E, t₁), " +
			"    square_zero_localization(N, S', ρ, N', ν, E, t₂), " +
			"    λX:set(prod(C, C)). " +
			"        ⋃{fraction_class(E.ring.mul, " +
			"                E.ring.carrier, " +
			"                monoid_powers(E.ring.mul, E.ring.one, t₂), " +
			"                E.ring.mul(e, " +
			"                    monoid_pow(E.ring.mul, E.ring.one, E.ring.sub(E.ring.add(t₂, t₂), t₁), k)), " +
			"                monoid_pow(E.ring.mul, E.ring.one, t₂, k + k)) | " +
			"            e:C, " +
			"            k:num | " +
			"            (e, monoid_pow(E.ring.mul, E.ring.one, t₁, k)) ∈ X})",
	},
		"t₂ − t₁ has projection t − t = S.zero, so it is i(n) and (t₂ − t₁)² = 0 (InclusionImage, "+
			"InclusionSquareZero); UnitPlusSquareZeroIsUnit in the fractions at t₂ with u = t₂/1, w = "+
			"1/t₂, j = (t₁ − t₂)/1 makes t₁/1 a unit with inverse (2t₂ − t₁)/t₂² (DenominatorUnit, "+
			"FractionMulClass). LocalizationUniversal at ToFractionIsLocalization gives the ring map "+
			"from the fractions at t₁ extending e ↦ e/1, its value at e/t₁ᵏ the class written, every "+
			"representation giving it (FractionClassEq, MulPowOn); the map the other way is its inverse "+
			"(LocalizationHomomorphismExtensional), so a ring isomorphism (RingIsomorphismDef). Over R: "+
			"k(a)/1 ↦ k(a)/1. On N': the inclusion at t₁ reads m as i(n)/t₁ᵏ, sent to i(tᵏ • n)/t₂²ᵏ, "+
			"the inclusion at t₂ of the same m (SquareZeroLocalizationIsExtension's last conjunct, "+
			"MapPow). Over S': both projections read ρ(p(e))/ρ(tᵏ) (SquareZeroIsomorphismDef)"),
})}

// ---------------------------------------------------------------------------
// The coefficients in place, and the split extension
// ---------------------------------------------------------------------------

// SpanIsModuleLocalization — inside a ring R that is a subring A₀ with a
// unit t of A₀ inverted, the span over R of an A₀-submodule M₀ of a module
// V over R, with the identity, is the localization of M₀ at the powers of
// t.
var SpanIsModuleLocalization = spanIsModuleLocalizationThm{family.Add(registry.ProofEntry{
	Name: "SpanIsModuleLocalization",
	Key:  "prop_89788c412582abfc",
	Reading: "This is the localized module computed in place, the companion of " +
		"RingAwayIsLocalization for the ring: no fraction classes, N' a set of V's vectors. " +
		"The kernel condition holds with the denominator one, the identity killing nothing " +
		"but zero. R = ring_away(R, A₀, t) is load-bearing for the fraction condition: a " +
		"member of the span is Σ rᵢ mᵢ with tᵏ rᵢ ∈ A₀ for one k, so tᵏ times it lies in M₀.",
	Deps: []registry.EntryLike{
		submodule.ModuleSpanDef,
		submodule.SpanLeast,
		submodule.SubsetSpan,
		submodule.SpanSubmodule,
		submodule.SubmoduleModuleOn,
		submodule.SubmoduleDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_away.RingAwayDef,
		ring_away.RingAwaySubring,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
		module_homomorphism.ModuleHomomorphismDef,
		module.ModuleOn,
		module.SmulMul,
		module.SmulOne,
		comm_monoid.MonoidPowersDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀:set(A). ∀t:A. ∀V:module_ops(A, D). ∀M₀:set(D).",
		Hypotheses: []string{
			"subring(R, A₀)",
			"t ∈ A₀",
			"ring_unit(R, t)",
			"R.carrier = ring_away(R, A₀, t)",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
		},
		Conclusion: "is_module_localization_on(restrict_ring(R, A₀), " +
			"    monoid_powers(R.mul, R.one, t), " +
			"    R, " +
			"    λa:A. a, " +
			"    restrict_module(V, M₀), " +
			"    restrict_module(V, module_span(R, V, M₀)), " +
			"    λx:D. x)",
	},
		"unfold IsModuleLocalizationOnDef. The span is a submodule over R (SpanSubmodule), so a module "+
			"over R (SubmoduleModuleOn, RestrictModuleDef); M₀ lies in it (SubsetSpan) and the identity is "+
			"linear over A₀, both a module over A₀ ⊆ R's carrier (ModuleOn, SubmoduleDef, RestrictRingDef, "+
			"ModuleHomomorphismDef). The members x of V with tᵏ • x ∈ M₀ for some k are a submodule over R "+
			"containing M₀: sums at the larger power, and r • x with tʲ r ∈ A₀ (RingAwayDef) at the power "+
			"j + k, M₀ being closed under A₀ and t ∈ A₀ (SmulMul); so they hold the span (SpanLeast). The "+
			"kernel condition: x = V.zero is killed by one = t⁰ (SmulOne, MonoidPowersDef)"),
})}

// SplitSquareZeroLocalization — the split extension S ⋉ N localized at
// the lift (t, 0) of t is isomorphic to the split extension S' ⋉ N' of
// the localizations: the class of ((a, m), (s, 0)) goes to
// (ρ(a) / ρ(s), ν(m) / ρ(s)).
var SplitSquareZeroLocalization = splitSquareZeroLocalizationThm{family.Add(registry.ProofEntry{
	Name: "SplitSquareZeroLocalization",
	Key:  "prop_525c46e8b08cbee4",
	Reading: "(t, 0) lifts t, and its powers are the pairs (tᵏ, 0), so every class has a " +
		"representative whose denominator is such a pair; the map reads both quotients in S' and " +
		"N', ρ(tᵏ) being a unit. It is how a split extension on a chart restricts to the overlap: " +
		"(S ⋉ N)[1/t] ≅ S[1/t] ⋉ N[1/t], with the structure map, the inclusion and the projection " +
		"matched, so a shear of S' ⋉ N' by a derivation of S' acts on the localization through it.",
	Deps: []registry.EntryLike{
		SquareZeroLocalizationIsExtension,
		SplitSquareZeroRing,
		SplitSquareZeroDef,
		SquareZeroExtension,
		SquareZeroIsomorphismDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_localization.FractionClassEq,
		ring_localization.FractionZeroIff,
		ring_localization.IsLocalizationOnDef,
		ring_homomorphism.RingIsomorphismDef,
		equivalence.InducedMapDef,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀t:B. " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
			"«baseLocalization»",
			"«coefficientLocalization»",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N', " +
			"    square_zero_localization(N, S', ρ, N', ν, «split»(S, f, N), (t, N.zero)), " +
			"    «split»(S', λa:A. ρ(f(a)), N'), " +
			"    induced_map(λz:prod(prod(B, D), prod(B, D)). " +
			"            (inverse_on(S'.carrier, λy:F. S'.mul(y, ρ(fst(snd(z)))), ρ(fst(fst(z)))), " +
			"                inverse_on(N'.carrier, λm:G. N'.smul(ρ(fst(snd(z))), m), ν(snd(fst(z)))))))",
	},
		"S ⋉ N is an extension of S by N over R (SplitSquareZeroRing, SplitSquareZeroDef, "+
			"SquareZeroExtension) and (t, 0) lies over t, so its localization is an extension of S' "+
			"by N' (SquareZeroLocalizationIsExtension); the powers of (t, 0) are the pairs (tᵏ, 0) "+
			"(SplitSquareZeroDef). The map is well defined, related representatives giving equal "+
			"quotients after the unit ρ(tʲ) cancels (FractionClassEq, InducedMapDef, InverseOnIn, "+
			"InverseOnRight, HomSmul), and componentwise a ring map onto S' ⋉ N', every pair having "+
			"representations with one power of t as denominator; it is injective: ρ(a) = 0 and ν(m) "+
			"= 0 give tᵏ a = 0 and tʲ • m = 0 (IsLocalizationOnDef and IsModuleLocalizationOnDef), "+
			"so (tᵏ⁺ʲ, 0) kills ((a, m), (s, 0)) (FractionZeroIff, InjectiveOnDef). Over R: k(a)/1 "+
			"↦ (ρ(f(a)), ν(0)) = (ρ(f(a)), N'.zero) (HomZero); on N': the inclusion of m, the class "+
			"of ((0, n), v) with ρ(tᵏ) • m = ν(n), goes to (0, m); over S': both projections read "+
			"ρ(a)/ρ(s) (RingIsomorphismDef, SquareZeroIsomorphismDef, Fst, Snd, PairEq)"),
})}
