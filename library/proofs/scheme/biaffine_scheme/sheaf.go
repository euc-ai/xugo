// sheaf.go — the sheaf of rings on the glued space: a presheaf, a sheaf
// and a sheaf of rings; its sections over an open set inside one chart
// are that chart's structure sections, its global sections the members of
// both chart rings, and its stalks local; each chart with the sheaf on it
// is the spectrum of its ring, so the glued space is a scheme, and the
// projective line inside a field is one.

package biaffine_scheme

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/scheme"
	"github.com/euc-ai/xugo/library/proofs/scheme/spec_functor"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The sheaf of rings
// ---------------------------------------------------------------------------

// BiaffineSheafPresheaf — the pairs of chart sections, restricted chart
// by chart, form a presheaf on the glued space.
var BiaffineSheafPresheaf = biaffineSheafPresheafThm{family.Add(registry.ProofEntry{
	Name: "BiaffineSheafPresheaf",
	Key:  "prop_7a9e72cca288863f",
	Reading: "Restriction acts on each chart's section through structure_restrict, which keeps it " +
		"on the smaller trace and makes it ∅ off it, so a restricted pair is again a pair of structure " +
		"sections, and agreement at the points of V on both charts is agreement at points of U. " +
		"Restricting to U itself changes nothing because a structure section is already ∅ off its trace.",
	Deps: []registry.EntryLike{
		biaffineSectionsDef,
		biaffineRestrictDef,
		biaffineTraceDef,
		BiaffineIsTopology,
		lattice_pair.BiaffineDef,
		structure_sheaf.StructureSheafOfRings,
		presheaf.Presheaf,
		presheaf.RestrictIn,
		presheaf.RestrictSelf,
		presheaf.RestrictTwice,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"«wa1Biaffine»",
		},
		Conclusion: "presheaf(biaffine_topology(R, A₀, A₁), " +
			"    biaffine_sections(R, A₀, A₁), " +
			"    biaffine_restrict(A₀, A₁))",
	},
		"is_topology by BiaffineIsTopology; for V ⊆ U open the traces of V lie in those of "+
			"U and are Zariski open, and structure_restrict lands in the structure sections "+
			"over the smaller one (StructureSheafOfRings at A₀ and at A₁, rings by BiaffineDef, "+
			"through its presheaf's RestrictIn); the agreement clause of biaffineSectionsDef at "+
			"V is that at U on fewer points; identity and composition hold on each component "+
			"(RestrictSelf, RestrictTwice), and a pair is its two components"),
})}

// BiaffineSheafIsSheaf — the presheaf is a sheaf: sections agreeing on a
// cover are equal, and compatible sections on a cover glue.
var BiaffineSheafIsSheaf = biaffineSheafIsSheafThm{family.Add(registry.ProofEntry{
	Name: "BiaffineSheafIsSheaf",
	Key:  "prop_c3568eee9c0f3c46",
	Reading: "A cover of U by open sets W gives covers of the two traces of U by the " +
		"traces of the W, and the agreement clause is pointwise, so locality and gluing " +
		"are those of the two structure sheaves: a glued pair agrees at a point of U on " +
		"both charts because the point lies in some W where the given pair does. The " +
		"empty cover of ∅ asks for exactly one section over ∅, the pair of empty sections.",
	Deps: []registry.EntryLike{
		BiaffineSheafPresheaf,
		biaffineSectionsDef,
		biaffineRestrictDef,
		biaffineTraceDef,
		BiaffinePointOverPrime,
		structure_sheaf.StructureSheafOfRings,
		presheaf.Sheaf,
		presheaf.Locality,
		presheaf.Gluing,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"«wa1Biaffine»",
		},
		Conclusion: "sheaf(biaffine_topology(R, A₀, A₁), " +
			"    biaffine_sections(R, A₀, A₁), " +
			"    biaffine_restrict(A₀, A₁))",
	},
		"presheaf by BiaffineSheafPresheaf; a cover V of U gives the cover of each trace of U "+
			"by the traces of the members (biaffineTraceDef); sections agreeing on every member "+
			"have equal components by Locality of each structure sheaf (StructureSheafOfRings); "+
			"compatible g(W) glue component by component by Gluing of each structure sheaf, the "+
			"chart-0 family indexed by the traces — two members with one trace meet in a member "+
			"of the same trace, fst being one-to-one on chart 0 (BiaffinePointOverPrime), so "+
			"compatibility makes their components agree there; the glued pair meets the agreement "+
			"clause at each point of U on both charts, which lies in some member"),
})}

// BiaffineSheafOfRings — with the chartwise ring operations the sheaf is
// a sheaf of rings.
var BiaffineSheafOfRings = biaffineSheafOfRingsThm{family.Add(registry.ProofEntry{
	Name: "BiaffineSheafOfRings",
	Key:  "prop_f1ab034492068172",
	Reading: "The operations are the two structure sheaves' chart by chart, so each ring law " +
		"holds on each component; what is asked beyond is that the sections over U are closed under " +
		"them, agreement in R localized at a point on both charts surviving sums and products — the " +
		"map from fractions of A₀ at fst(P) to fractions of R at the prime P generates is a ring " +
		"homomorphism. Over ∅ the ring is the one pair of empty sections, a zero ring.",
	Deps: []registry.EntryLike{
		BiaffineSheafIsSheaf,
		biaffineSectionsDef,
		biaffineAddDef,
		biaffineZeroDef,
		biaffineNegDef,
		biaffineMulDef,
		biaffineOneDef,
		biaffineSubDef,
		BiaffineOverlapPrime,
		structure_sheaf.StructureSheafOfRings,
		ring_localization.FractionClassEq,
		ring_localization.FractionAddClass,
		ring_localization.FractionMulClass,
		ring_localization.FractionNegClass,
		locally_ringed_space.SheafOfRings,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "sheaf_of_rings(biaffine_sheaf(R, A₀, A₁))",
	},
		"sheaf by BiaffineSheafIsSheaf; over each open U the six operations are those of "+
			"structure_sheaf on each component (StructureSheafOfRings: each section ring a ring, each "+
			"restriction a ring homomorphism), so comm_ring_on of the sections over U reduces to closure "+
			"of the agreement clause: at a point P on both charts with Q its prime of R "+
			"(BiaffineOverlapPrime), A₀ ∖ fst(P) lies in R ∖ Q as fst(P) = A₀ ∩ Q, so a class of A₀ at A₀ "+
			"∖ fst(P) has one class in R at R ∖ Q whatever its representative (FractionClassEq), and sums, "+
			"products and negations of classes go to sums, products and negations (FractionAddClass, "+
			"FractionMulClass, FractionNegClass); the restrictions are ring homomorphisms on each component"),
})}

// BiaffineChartSections — over an open set inside one chart, the
// sections are that chart's structure sections: the projection to the
// chart's component is a ring isomorphism.
var BiaffineChartSections = biaffineChartSectionsThm{family.Add(registry.ProofEntry{
	Name: "BiaffineChartSections",
	Key:  "prop_c3460fcb17cb47b8",
	Reading: "U inside the chart is load-bearing: every point of U on the other chart " +
		"then lies on both, where the agreement clause determines the other component " +
		"from this one, R localized at the point's prime being the other chart ring " +
		"localized at its own prime. Over an open set reaching the part of the other " +
		"chart off this one, the other component carries what the projection forgets.",
	Deps: []registry.EntryLike{
		biaffineSectionsDef,
		biaffineAddDef,
		biaffineZeroDef,
		biaffineNegDef,
		biaffineMulDef,
		biaffineOneDef,
		biaffineSubDef,
		BiaffineOverlapPrime,
		BiaffineChartOpen,
		BiaffineSheafOfRings,
		lattice_pair.BiaffineDef,
		lattice_pair.BiaffineSwap,
		ring_away.RingAwayDef,
		ring_localization.FractionClassEq,
		structure_sheaf.StructureSectionsDef,
		ring_homomorphism.RingIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "(∀U:set(prod(set(A), set(A))). " +
			"    U ∈ biaffine_topology(R, A₀, A₁) ∧ " +
			"    U ⊆ {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀)} ⇒ " +
			"    ring_isomorphism( " +
			"        restrict_ring(biaffine_section_ops(R, A₀, A₁, U), biaffine_sections(R, A₀, A₁, U)), " +
			"        spec_section_ops(restrict_ring(R, A₀), biaffine_trace(A₀, fst, U)), " +
			"        fst)) ∧ " +
			"(∀U:set(prod(set(A), set(A))). " +
			"    U ∈ biaffine_topology(R, A₀, A₁) ∧ " +
			"    U ⊆ {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(snd(P) = A₁)} ⇒ " +
			"    ring_isomorphism( " +
			"        restrict_ring(biaffine_section_ops(R, A₀, A₁, U), biaffine_sections(R, A₀, A₁, U)), " +
			"        spec_section_ops(restrict_ring(R, A₁), biaffine_trace(A₁, snd, U)), " +
			"        snd))",
	},
		"fst is a ring homomorphism, the operations being chartwise (biaffineAddDef, …); one-to-one: "+
			"two sections with one chart-0 component have chart-1 components agreeing at every point of "+
			"the chart-1 trace, each such point lying on both charts, since fractions of A₁ at snd(P) go "+
			"one-to-one to fractions of R at Q when s ∉ snd(P) (BiaffineOverlapPrime, FractionClassEq); "+
			"onto: for s₀ over the chart-0 trace let s₁ at snd(P) be the class whose image in R at Q is "+
			"that of s₀ at fst(P); where s₀ = a/b on V, s₁ = (sⁿ · a)/(sⁿ · b) on the image of V ∩ D(t) "+
			"in D(s) (BiaffineChartOpen), with sⁿ · a, sⁿ · b ∈ A₁ (R = ring_away(R, A₁, s), BiaffineDef, "+
			"RingAwayDef) and sⁿ · b ∉ snd(P) as b ∉ fst(P) = A₀ ∩ Q; chart 1 by BiaffineSwap"),
})}

// BiaffineGlobalSections — the global sections are the members of both
// chart rings: a ↦ (a / one, a / one) is a ring isomorphism from A₀ ∩ A₁.
var BiaffineGlobalSections = biaffineGlobalSectionsThm{family.Add(registry.ProofEntry{
	Name: "BiaffineGlobalSections",
	Key:  "prop_d46c36fb01a116e",
	Reading: "A global section is a global section of each chart's structure sheaf, a member a₀ " +
		"of A₀ and a₁ of A₁ (GlobalSections), whose images agree in R localized at every prime of R " +
		"— every prime of R is the prime of a point on both charts — so a₀ = a₁ in R, a member of a " +
		"ring zero at every prime being zero. Both chart rings lying in R is what makes the answer " +
		"A₀ ∩ A₁ rather than a fibre product. In the zero ring both sides are the zero ring.",
	Deps: []registry.EntryLike{
		biaffineSectionsDef,
		BiaffineSpace,
		BiaffinePointOverPrime,
		BiaffineOverlapPrime,
		BiaffineSheafOfRings,
		lattice_pair.BiaffineDef,
		structure_sheaf.GlobalSections,
		ring_localization.FractionClassEq,
		ring_localization.FractionZeroIff,
		ring_ideal.ExistsMaximalAbove,
		ring_homomorphism.RingIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "ring_isomorphism(restrict_ring(R, A₀ ∩ A₁), " +
			"    restrict_ring(biaffine_section_ops(R, A₀, A₁, biaffine_points(R, A₀, A₁)), " +
			"        biaffine_sections(R, A₀, A₁, biaffine_points(R, A₀, A₁))), " +
			"    λa:A. " +
			"        (λq:set(A). " +
			"            COND(q ∈ prime_spectrum(restrict_ring(R, A₀)), " +
			"                fraction_class(R.mul, A₀, A₀ ∖ q, a, R.one), " +
			"                ∅), " +
			"        λq:set(A). " +
			"            COND(q ∈ prime_spectrum(restrict_ring(R, A₁)), " +
			"                fraction_class(R.mul, A₁, A₁ ∖ q, a, R.one), " +
			"                ∅)))",
	},
		"the map is the pair of coefficient-section maps of structure_sheaf's GlobalSections at A₀ "+
			"and at A₁ on A₀ ∩ A₁, a subring of R (BiaffineDef), and both components of a/one are a/one "+
			"in R at every point on both charts, so the pair is a section (BiaffineSpace for the traces); "+
			"one-to-one already on chart 0 (GlobalSections at A₀); onto: a global section is (a₀/one, "+
			"a₁/one) with a₀ ∈ A₀ and a₁ ∈ A₁ (GlobalSections at each chart), every prime of R is the "+
			"prime of the point over its trace on A₀ (BiaffinePointOverPrime, BiaffineOverlapPrime), so "+
			"a₀ − a₁ is zero in R at every prime (FractionClassEq, FractionZeroIff) and its annihilator "+
			"lies in no maximal ideal (ExistsMaximalAbove), so a₀ = a₁"),
})}

// BiaffineStalkLocal — the ring of germs at each point is local.
var BiaffineStalkLocal = biaffineStalkLocalThm{family.Add(registry.ProofEntry{
	Name: "BiaffineStalkLocal",
	Key:  "prop_f9967881eb35cec3",
	Reading: "P a point is load-bearing: off the space the stalk is ∅, not a ring. " +
		"The stalk at a point of chart 0 is the stalk of the open chart, the spectrum " +
		"of A₀ (BiaffineChartIsSpec), at fst(P): the local ring of A₀ at that prime.",
	Deps: []registry.EntryLike{
		BiaffineChartOpen,
		BiaffineChartIsSpec,
		BiaffineSheafOfRings,
		structure_sheaf.SpecLocallyRinged,
		structure_sheaf.StalkAtPrime,
		presheaf.StalkDef,
		presheaf.SheafGermDef,
		local_ring.LocalRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"P ∈ biaffine_points(R, A₀, A₁)",
		},
		Conclusion: "local_ring_on(restrict_ring(biaffine_stalk_ops(R, A₀, A₁, P), " +
			"        stalk(biaffine_topology(R, A₀, A₁), " +
			"            biaffine_sections(R, A₀, A₁), " +
			"            biaffine_restrict(A₀, A₁), " +
			"            P)))",
	},
		"P lies on chart 0 or on chart 1, each open (BiaffineChartOpen), and germs at P are "+
			"represented over open sets inside that chart; the chart's isomorphism with the "+
			"spectrum of its ring (BiaffineChartIsSpec) carries them to germs of the structure "+
			"sheaf at fst(P) or snd(P), a ring isomorphism of stalks; that stalk is local "+
			"(SpecLocallyRinged), and a ring isomorphic to a local ring is local (LocalRingOn)"),
})}

// BiaffineLocallyRinged — the glued space with its sheaf is a locally
// ringed space.
var BiaffineLocallyRinged = biaffineLocallyRingedThm{family.Add(registry.ProofEntry{
	Name: "BiaffineLocallyRinged",
	Key:  "prop_1530167026ab21dc",
	Deps: []registry.EntryLike{
		BiaffineSheafOfRings,
		BiaffineStalkLocal,
		BiaffineSpace,
		locally_ringed_space.LocallyRingedSpace,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "locally_ringed_space(biaffine_sheaf(R, A₀, A₁))",
	},
		"unfold locally_ringed_space: BiaffineSheafOfRings, and "+
			"BiaffineStalkLocal at each x ∈ ⋃T, a point by BiaffineSpace"),
})}

// ---------------------------------------------------------------------------
// The charts as spectra, and the scheme
// ---------------------------------------------------------------------------

// BiaffineChartIsSpec — each chart, with the sheaf on it, is isomorphic to
// the spectrum of its ring through the projection.
var BiaffineChartIsSpec = biaffineChartIsSpecThm{family.Add(registry.ProofEntry{
	Name: "BiaffineChartIsSpec",
	Key:  "prop_a002f78c09fcd3fc",
	Reading: "On points the isomorphism is the projection to the chart's prime; on " +
		"the sections over a Zariski open set V of the chart it is the inverse of the " +
		"projection at the points over V (BiaffineChartSections), the other chart's " +
		"component rebuilt from this one by agreement. The two spaces' points have " +
		"different types — pairs of ideals and ideals — and nothing is transported.",
	Deps: []registry.EntryLike{
		BiaffineChartOpen,
		BiaffineChartSections,
		BiaffinePointOverPrime,
		biaffineRestrictDef,
		BiaffineSheafOfRings,
		locally_ringed_space.LrsIsomorphismDef,
		ring_homomorphism.IsomorphismInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "(∃ψ:(set(set(A)) → " +
			"        (set(A) → set(prod(A, A))) → " +
			"        prod(set(A) → set(prod(A, A)), set(A) → set(prod(A, A)))). " +
			"    lrs_isomorphism(subtopology(biaffine_topology(R, A₀, A₁), " +
			"            {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀)}), " +
			"        biaffine_section_ops(R, A₀, A₁), " +
			"        biaffine_restrict(A₀, A₁), " +
			"        zariski_topology(restrict_ring(R, A₀)), " +
			"        spec_section_ops(restrict_ring(R, A₀)), " +
			"        structure_restrict, " +
			"        fst, " +
			"        ψ)) ∧ " +
			"(∃ψ:(set(set(A)) → " +
			"        (set(A) → set(prod(A, A))) → " +
			"        prod(set(A) → set(prod(A, A)), set(A) → set(prod(A, A)))). " +
			"    lrs_isomorphism(subtopology(biaffine_topology(R, A₀, A₁), " +
			"            {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(snd(P) = A₁)}), " +
			"        biaffine_section_ops(R, A₀, A₁), " +
			"        biaffine_restrict(A₀, A₁), " +
			"        zariski_topology(restrict_ring(R, A₁)), " +
			"        spec_section_ops(restrict_ring(R, A₁)), " +
			"        structure_restrict, " +
			"        snd, " +
			"        ψ))",
	},
		"homeomorphic_map by BiaffineChartOpen; for V a Zariski open set of A₀ the points of chart 0 "+
			"over V form an open set inside chart 0 whose chart-0 trace is V (BiaffinePointOverPrime), so "+
			"BiaffineChartSections makes fst a ring isomorphism from its sections onto the structure "+
			"sections over V; ψ(V) is its inverse (IsomorphismInverse), and it commutes with restriction "+
			"because fst does (biaffineRestrictDef against structure_restrict); chart 1 by snd the same way"),
})}

// BiaffineScheme — the glued space with its sheaf is a scheme.
var BiaffineScheme = biaffineSchemeThm{family.Add(registry.ProofEntry{
	Name: "BiaffineScheme",
	Key:  "prop_8e4e4017fa249eed",
	Reading: "A scheme asks each point to lie in an open set isomorphic to " +
		"the spectrum of the ring of sections over that set itself; the two " +
		"charts are such sets, their rings of sections being the chart rings.",
	Deps: []registry.EntryLike{
		BiaffineLocallyRinged,
		BiaffineChartOpen,
		BiaffineChartIsSpec,
		BiaffineChartSections,
		BiaffineSpace,
		scheme.Scheme,
		structure_sheaf.GlobalSections,
		spec_functor.SpecIsomorphism,
		locally_ringed_space.IsomorphismMorphism,
		locally_ringed_space.MorphismCompose,
		locally_ringed_space.MorphismInverseIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "scheme(biaffine_sheaf(R, A₀, A₁))",
	},
		"locally ringed by BiaffineLocallyRinged; a point lies on chart 0 or chart 1, open "+
			"(BiaffineChartOpen); the chart is isomorphic to the spectrum of its ring (BiaffineChartIsSpec), "+
			"and its ring of sections is isomorphic to the chart ring (BiaffineChartSections over the whole "+
			"chart, whose trace is the whole spectrum by BiaffineSpace, then GlobalSections), so the "+
			"spectrum of the chart ring is isomorphic to that of the ring of sections (SpecIsomorphism); "+
			"compose the two isomorphisms (IsomorphismMorphism, MorphismCompose, MorphismInverseIsomorphism)"),
})}

// ProjectiveLineScheme — k[t] and k[1/t] inside a field, glued along
// k[t, 1/t], make a scheme: the projective line over k when t is
// transcendental.
var ProjectiveLineScheme = projectiveLineSchemeThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveLineScheme",
	Key:  "prop_a54997f7229bc6f7",
	Reading: "t ≠ zero is what makes (k[t], k[1/t]) a biaffine datum. For t " +
		"transcendental over k this is the projective line over k; for t algebraic " +
		"both charts and the overlap are the field k(t), and the scheme is one point.",
	Deps: []registry.EntryLike{projective_line.ProjectiveLineBiaffine, BiaffineScheme},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "scheme(biaffine_sheaf(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)), " +
			"        polynomial_image(field_ring(L), k, t), " +
			"        polynomial_image(field_ring(L), k, L.inv(t))))",
	},
		"ProjectiveLineBiaffine makes the datum biaffine at t and inv(t); BiaffineScheme"),
})}
