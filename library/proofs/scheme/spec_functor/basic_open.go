package spec_functor

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// BasicOpenAffine — a basic open is isomorphic to the spectrum of its localization.
var BasicOpenAffine = basicOpenAffineThm{family.Add(registry.ProofEntry{
	Name: "BasicOpenAffine",
	Key:  "prop_17ce2a89ed90b7d8",
	Reading: "The basic-open section rings are compared as localizations of R at the powers of " +
		"fg; the unique comparison commutes with coefficients. The localization ring and the " +
		"restricted spectrum use their section-ring records; no new structure constant is introduced.",
	Deps: []registry.EntryLike{
		ring_localization.LocalizationPrimeCorrespondence,
		ring_localization.LocalizationPrimeCorrespondenceInverse,
		ring_localization.ToFractionIsLocalization,
		ring_localization.LocalizationAtProduct,
		ring_localization.LocalizationIsomorphism,
		ring_localization.LocalizationHomomorphismExtensional,
		structure_sheaf.SectionsAtBasicOpen,
		structure_sheaf.StructureSheafOfRings,
		prime_spectrum.ZariskiOpenMul,
		locally_ringed_space.LrsIsomorphismDef,
		prime_spectrum.ZariskiOpenBase,
		presheaf.Gluing,
		presheaf.Locality,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). ∀f:A.",
		Hypotheses: []string{
			"f ∈ R.carrier",
		},
		Conclusion: "∃φ:(set(A) → set(set(prod(A, A)))). " +
			"∃ψ:(set(set(set(prod(A, A)))) → " +
			"        (set(set(prod(A, A))) → set(prod(set(prod(A, A)), set(prod(A, A))))) → " +
			"        set(A) → " +
			"        set(prod(A, A))). " +
			"    lrs_isomorphism(subtopology(zariski_topology(R), zariski_open(R, f)), " +
			"        spec_section_ops(R), " +
			"        structure_restrict, " +
			"        spec_sheaf(mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"                ring_localization(R.carrier, monoid_powers(R.mul, R.one, f)))), " +
			"        φ, " +
			"        ψ)",
	},
		"The prime correspondence identifies D(f) with Spec(R_f), and the pullback of D(g/one) is D(fg). "+
			"ToFractionIsLocalization and SectionsAtBasicOpen describe the section ring over D(g/one) as an "+
			"iterated localization; LocalizationAtProduct makes it a localization of R at the powers of fg. "+
			"SectionsAtBasicOpen gives the same interface for sections over D(fg). LocalizationIsomorphism "+
			"supplies the unique comparison commuting with coefficients. LocalizationHomomorphismExtensional "+
			"proves compatibility with restrictions by agreement on coefficients. These basic opens form a "+
			"basis, since denominators are units; glue the comparison maps and their inverses using Gluing "+
			"and Locality. The point map extends ideals and the section component is contravariant."),
})}
