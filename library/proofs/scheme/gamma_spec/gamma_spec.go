// gamma_spec.go — maps to a spectrum and homomorphisms on global sections.

package gamma_spec

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/scheme/spec_functor"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// GlobalSectionHomDef — global_section_hom(R, ψ, a): the global fraction section of a, sent
// back to X by the morphism's section map over the whole spectrum.
var GlobalSectionHomDef = globalSectionHomDefThm{family.Define(registry.DefEntry{
	Name: "GlobalSectionHomDef", Const: "global_section_hom",
	Key:     "prop_8b31fb6210bd823c",
	Type:    "ring_ops(C) → (set(set(C)) → (set(C) → set(prod(C, C))) → B) → C → B",
	Bundles: []string{},
	Equations: []string{
		"∀R:ring_ops(C). ∀ψ:(set(set(C)) → (set(C) → set(prod(C, C))) → B). ∀a:C. " +
			"    global_section_hom(R, ψ, a) = " +
			"    ψ(prime_spectrum(R), fraction_section(R, prime_spectrum(R), a, R.one))",
	},
})}

// specAdjunctPointDef — spec_adjunct_point(X, R, α, x): the elements of R whose germ at x
// under α is a nonunit of the stalk — the point of Spec R assigned to x.
var specAdjunctPointDef = specAdjunctPointDefThm{family.Define(registry.DefEntry{
	Name: "specAdjunctPointDef", Const: "spec_adjunct_point",
	Key: "prop_d44d734f58fe219a",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"ring_ops(C) → " +
		"(C → B) → " +
		"A → " +
		"set(C)",
	Bundles: []string{"locally_ringed_space(T, F, res)", "comm_ring_on(R)"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀R:ring_ops(C). " +
			"∀α:(C → B). " +
			"∀x:A. " +
			"    spec_adjunct_point(T, F, res, R, α, x) = " +
			"    {a:C | " +
			"        a ∈ R.carrier ∧ " +
			"        ¬ring_unit(stalk_ring(T, F, res, x), " +
			"            sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, α(a)))}",
	},
})}

// specAdjunctSectionDef — spec_adjunct_section(X, R, α, V, s): the section over the preimage
// of V chosen to have, near each point, the germ α(a) · α(b)⁻¹ wherever s is locally a / b.
var specAdjunctSectionDef = specAdjunctSectionDefThm{family.Define(registry.DefEntry{
	Name: "specAdjunctSectionDef", Const: "spec_adjunct_section",
	Key: "prop_e8b01478bd6b9bbf",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"ring_ops(C) → " +
		"(C → B) → " +
		"set(set(C)) → " +
		"(set(C) → set(prod(C, C))) → " +
		"B",
	Bundles: []string{"locally_ringed_space(T, F, res)", "comm_ring_on(R)"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀R:ring_ops(C). " +
			"∀α:(C → B). " +
			"∀V:set(set(C)). " +
			"∀s:(set(C) → set(prod(C, C))). " +
			"    spec_adjunct_section(T, F, res, R, α, V, s) = " +
			"    εt:B. " +
			"        t ∈ F(preimage_on(⋃T, spec_adjunct_point(T, F, res, R, α), V)).carrier ∧ " +
			"        (∀x:A. ∀W:set(set(C)). ∀a b:C. " +
			"            x ∈ preimage_on(⋃T, spec_adjunct_point(T, F, res, R, α), V) ∧ " +
			"            W ∈ zariski_topology(R) ∧ " +
			"            spec_adjunct_point(T, F, res, R, α, x) ∈ W ∧ " +
			"            W ⊆ V ∧ " +
			"            a ∈ R.carrier ∧ " +
			"            b ∈ R.carrier ∧ " +
			"            (∀q:set(C). " +
			"                q ∈ W ⇒ b ∉ q ∧ s(q) = fraction_class(R.mul, R.carrier, R.carrier ∖ q, a, b)) ⇒ " +
			"            sheaf_germ(T, " +
			"                (λU:set(A). F(U).carrier), " +
			"                res, " +
			"                x, " +
			"                preimage_on(⋃T, spec_adjunct_point(T, F, res, R, α), V), " +
			"                t) = " +
			"            stalk_mul(T, " +
			"                F, " +
			"                res, " +
			"                x, " +
			"                sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, α(a)), " +
			"                (εh:set(prod(set(A), B)). " +
			"                    h ∈ stalk(T, (λU:set(A). F(U).carrier), res, x) ∧ " +
			"                    stalk_mul(T, " +
			"                        F, " +
			"                        res, " +
			"                        x, " +
			"                        sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, α(b)), " +
			"                        h) = " +
			"                    stalk_one(T, F, res, x))))",
	},
	Deps: []registry.EntryLike{specAdjunctPointDef},
})}

// GlobalSectionHom — a morphism of locally ringed spaces from X to Spec R
// gives a ring homomorphism from R to the global sections of X: a goes to
// the image of its global fraction section under the morphism's section
// map over the whole spectrum.
var GlobalSectionHom = globalSectionHomThm{family.Add(registry.ProofEntry{
	Name: "GlobalSectionHom",
	Key:  "prop_930ad03c6d1ffb72",
	Deps: []registry.EntryLike{
		GlobalSectionHomDef,
		locally_ringed_space.MorphismSections,
		locally_ringed_space.MorphismContinuous,
		structure_sheaf.GlobalSections,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀f:(A → set(C)). " +
			"∀ψ:(set(set(C)) → (set(C) → set(prod(C, C))) → B).",
		Hypotheses: []string{
			"lrs_morphism(X, spec_sheaf(R), f, ψ)",
		},
		Conclusion: "ring_homomorphism(R, X(⋃X.T), global_section_hom(R, ψ))",
	},
		"The preimage of the whole spectrum is the source space by continuity. "+
			"Compose GlobalSections with MorphismSections at that open."),
})}

// AdjunctPointPrime — the point assigned to x is the contraction of a
// prime ideal of the stalk at x. The nonunits of that local ring are its
// maximal ideal, hence prime; sending a to the germ of α(a) at x is a ring
// homomorphism from R to the stalk (locally_ringed_space.CoefficientGermHomomorphism); and an
// element of R lies in the point exactly when its image is a nonunit.
// PreimagePrime makes the contraction prime.
var AdjunctPointPrime = adjunctPointPrimeThm{family.Add(registry.ProofEntry{
	Name: "AdjunctPointPrime",
	Key:  "prop_f0bf8d6d0d231586",
	Build: family.Theorem(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"x ∈ ⋃X.T",
		},
		Conclusion: "prime_ideal(R, spec_adjunct_point(X, R, α, x))",
		Abbrev: Abbrev{
			{Name: "stalkNonunits", Text: "{g:set(prod(set(A), B)) | " +
				"    g ∈ stalk(X.T, (λU:set(A). X(U).carrier), X.res, x) ∧ " +
				"    ¬ring_unit(stalk_ring(X.T, X, X.res, x), g)}"},
			{Name: "germAfterAlpha", Text: "λa:C. " +
				"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, ⋃X.T, α(a))"},
		},
	},
		func(
			a *Argument,
			X locally_ringed_space.LocallyRingedSpaceFact[on.T],
			R comm_ring.CommRingFact[on.R],
			α *Arrow[C, B],
			x *Expr[A],
			hom, inSpace Fact,
		) {
			ringPresheaf := locally_ringed_space.SheafPresheafOfRings.Read(
				locally_ringed_space.RingedSheaf.Read(X))
			underlying := locally_ringed_space.Presheaf.Read(ringPresheaf)
			spaceOpen := topological_space.SpaceOpen.Read(presheaf.Topology.Read(underlying))
			globalSections := ring_homomorphism.MapIn.Read(hom)

			local := a.Have(
				"the stalk at x is a local ring",
				"local_ring_on(stalk_ring(X.T, X, X.res, x))",
				By(locally_ringed_space.StalkLocal.Read(X), inSpace))
			stalkRing := local_ring.Ring.Read(local)
			nonunitsPrime := a.Have(
				"its nonunits are its maximal ideal, so they form a prime ideal",
				"prime_ideal(stalk_ring(X.T, X, X.res, x), «stalkNonunits»)",
				By(ring_ideal.MaximalIsPrime.Read(stalkRing), local_ring.NonUnitsMaximal.Read(local)))
			germsInStalk := a.Have(
				"α(a) is a section over the whole space, so its germ at x lies in the stalk",
				"∀a:C. a ∈ R.carrier ⇒ «germAfterAlpha»(a) ∈ stalk(X.T, λU:set(A). X(U).carrier, X.res, x)",
				By(presheaf.GermInStalk.Read(underlying), spaceOpen, inSpace, globalSections))
			nonunitGerms := a.Have(
				"the germ of α(a) lies in the stalk, so it is among the nonunits exactly when it is not a unit",
				Statement{
					Binders: "∀a:C.",
					Hypotheses: []string{
						"a ∈ R.carrier",
					},
					Conclusion: "«germAfterAlpha»(a) ∈ «stalkNonunits» ⇔ " +
						"¬ring_unit(stalk_ring(X.T, X, X.res, x), «germAfterAlpha»(a))",
				},
				a.ForEach(func(r *Expr[C]) Action { return BySets(germsInStalk.At(r)) }))
			contraction := a.Have(
				"the point is the contraction of the nonunits along "+
					"that homomorphism: the two sets have the same elements",
				"spec_adjunct_point(X, R, α, x) = preimage_on(R.carrier, «germAfterAlpha», «stalkNonunits»)",
				Simp(Fwd(specAdjunctPointDef), Fwd(functions.PreimageOnDef)),
				Simp(Fwd(set_basic.Extension)),
				a.ForEach(func(r *Expr[C]) Action { return BySets(nonunitGerms.At(r)) }))
			a.Show(
				"a contraction of a prime ideal along a ring homomorphism is prime",
				contraction.Rw(),
				By(
					R,
					stalkRing,
					locally_ringed_space.CoefficientGermHomomorphism.Read(ringPresheaf),
					hom,
					inSpace,
					nonunitsPrime,
					spec_functor.PreimagePrime))
		}),
})}

// AdjunctPointInSpectrum — the point assigned to a point x of the space is
// a point of Spec R: it is a prime ideal of R by AdjunctPointPrime, and the
// spectrum is the set of the prime ideals.
var AdjunctPointInSpectrum = adjunctPointInSpectrumThm{family.Add(registry.ProofEntry{
	Name: "AdjunctPointInSpectrum",
	Key:  "prop_469cceee6a03b64b",
	Build: family.Theorem(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"x ∈ ⋃X.T",
		},
		Conclusion: "spec_adjunct_point(X, R, α, x) ∈ prime_spectrum(R)",
	},
		func(
			a *Argument,
			X locally_ringed_space.LocallyRingedSpaceFact[on.T],
			R comm_ring.CommRingFact[on.R],
			α *Arrow[C, B],
			x *Expr[A],
			hom, inSpace Fact,
		) {
			a.Show(
				"the point of x is a prime ideal of R, so it lies in the spectrum",
				Unfold(prime_spectrum.PrimeSpectrumDef),
				BySets(Read(AdjunctPointPrime, X), R, hom, inSpace))
		}),
})}

// AdjunctPointContinuous — the point map into Spec R is continuous, and the
// preimage of D(a) is the unit locus of α(a): a lies in the point of x
// exactly when the germ of α(a) at x is not a unit. Around the point of each
// x over an open W lies a basic open D(a) ⊆ W, and the unit locus of α(a),
// open by UnitLocusOpen, is then a neighbourhood of x inside the preimage
// of W.
var AdjunctPointContinuous = adjunctPointContinuousThm{family.Add(registry.ProofEntry{
	Name: "AdjunctPointContinuous",
	Key:  "prop_848c842fe994712b",
	Build: family.Theorem(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
		},
		Conclusion: "continuous_map(X.T, zariski_topology(R), spec_adjunct_point(X, R, α)) ∧ " +
			"(∀a:C. " +
			"    a ∈ R.carrier ⇒ " +
			"    preimage_on(⋃X.T, spec_adjunct_point(X, R, α), zariski_open(R, a)) = «unitLocus»(a))",
		Abbrev: Abbrev{
			{Name: "unitLocus", Text: "λa:C. " +
				"    {y:A | " +
				"        y ∈ ⋃X.T ∧ " +
				"        ring_unit(stalk_ring(X.T, X, X.res, y), " +
				"            sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, y, ⋃X.T, α(a)))}"},
		},
	},
		func(
			arg *Argument,
			X locally_ringed_space.LocallyRingedSpaceFact[on.T],
			R comm_ring.CommRingFact[on.R],
			α *Arrow[C, B],
			hom Fact,
		) {
			ringPresheaf := locally_ringed_space.SheafPresheafOfRings.Read(
				locally_ringed_space.RingedSheaf.Read(X))
			topology := presheaf.Topology.Read(locally_ringed_space.Presheaf.Read(ringPresheaf))
			spaceOpen := topological_space.SpaceOpen.Read(topology)
			globalSections := ring_homomorphism.MapIn.Read(hom)

			units := arg.Have(
				"for a in R, the point of x lies in D(a) exactly when the germ of α(a) at x is a unit",
				"∀a:C. "+
					"    a ∈ R.carrier ⇒ "+
					"    ∀x:A. "+
					"        x ∈ ⋃X.T ⇒ "+
					"        (spec_adjunct_point(X, R, α, x) ∈ zariski_open(R, a) ⇔ "+
					"            ring_unit(stalk_ring(X.T, X, X.res, x), "+
					"                sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, ⋃X.T, α(a))))",
				Derive(func(b *Argument) {
					b.FixAs[C]("a")
					inR := b.Assume()
					b.FixAs[A]("x")
					inSpace := b.Assume()
					holds := b.Have(
						"a lies in R, so it lies in the point of x exactly when the germ of α(a) at x is not a unit",
						"a ∈ spec_adjunct_point(X, R, α, x) ⇔ "+
							"¬ring_unit(stalk_ring(X.T, X, X.res, x), "+
							"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, ⋃X.T, α(a)))",
						Unfold(specAdjunctPointDef),
						BySets(inR))
					b.Show(
						"the point of x is a prime of R, and it lies in D(a) exactly when it misses a",
						Unfold(prime_spectrum.ZariskiOpenDef),
						BySets(Read(AdjunctPointInSpectrum, X), R, hom, inSpace, holds))
				}))
			preimage := arg.Have(
				"the preimage of D(a) is the unit locus of α(a)",
				Statement{
					Binders: "∀a:C.",
					Hypotheses: []string{
						"a ∈ R.carrier",
					},
					Conclusion: "preimage_on(⋃X.T, spec_adjunct_point(X, R, α), zariski_open(R, a)) = «unitLocus»(a)",
				},
				Derive(func(b *Argument) {
					a := b.FixAs[C]("a")
					inR := b.Assume()
					b.Show(
						"the two sets have the same points",
						Simp(Fwd(set_basic.Extension)),
						b.ForEach(func(x *Expr[A]) Action { return BySets(units.At(a, x), inR) }))
				}))
			opens := arg.Have(
				"the preimage of an open set is open",
				"∀W:set(set(C)). W ∈ zariski_topology(R) ⇒ preimage_on(⋃X.T, spec_adjunct_point(X, R, α), W) ∈ X.T",
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[C]]]("W")
					open := b.Assume()
					preimageW := b.Let("P", b.Term("preimage_on(⋃X.T, spec_adjunct_point(X, R, α), W)"))
					inP := b.Have(
						"the points of P are the points of the space lying over W",
						"∀x:A. x ∈ P ⇔ x ∈ ⋃X.T ∧ spec_adjunct_point(X, R, α, x) ∈ W",
						BySets(preimageW))
					near := b.Have(
						"each point of P has an open neighbourhood inside P",
						"∀x:A. x ∈ P ⇒ ∃v:set(A). v ∈ X.T ∧ v ⊆ P ∧ x ∈ v",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							member := d.Assume()
							inSpace := d.Have(
								"x lies in the space",
								"x ∈ ⋃X.T",
								By(inP.At(x), member))
							overW := d.Have(
								"the point of x lies in W",
								"spec_adjunct_point(X, R, α, x) ∈ W",
								By(inP.At(x), member))
							a, basic := d.ObtainAs[C](
								"W is open, so the point of x lies in a basic open set D(a) inside W",
								"∃a:C. "+
									"    a ∈ R.carrier ∧ spec_adjunct_point(X, R, α, x) ∈ zariski_open(R, a) ∧ zariski_open(R, a) ⊆ W",
								By(prime_spectrum.ZariskiOpenBase.Read(R), open, overW))
							parts := d.Conjuncts(
								basic,
								"a lies in R",
								"the point of x lies in D(a)",
								"D(a) lies inside W")
							inR, overD, insideW := parts[0], parts[1], parts[2]
							locusOpen := d.Have(
								"α(a) is a section over the whole space, so its unit locus is open",
								"«unitLocus»(a) ∈ X.T",
								By(locally_ringed_space.UnitLocusOpen.Read(ringPresheaf), spaceOpen, globalSections, inR))
							locusIsPreimage := d.Have(
								"a lies in R, so the unit locus of α(a) is the preimage of D(a)",
								"preimage_on(⋃X.T, spec_adjunct_point(X, R, α), zariski_open(R, a)) = «unitLocus»(a)",
								By(preimage.At(a), inR))
							d.Take(d.Term("«unitLocus»(a)"))
							d.Do(SplitConjAll(
								Case(
									"the unit locus of α(a) is open",
									By(locusOpen)),
								Case(
									"it is the preimage of D(a), and D(a) lies inside W, so it lies inside P",
									locusIsPreimage.RwRev(),
									BySets(preimageW, insideW)),
								Case(
									"it holds x, whose point lies in D(a)",
									BySets(units.At(a, x), inR, inSpace, overD)),
							))
						}))
					b.Show(
						"so P is open, by the pointwise criterion for openness",
						By(topological_space.OpenPointwise.Read(topology), near))
				}))
			continuous := arg.Have(
				"the points of a Zariski topology are its spectrum, so the point map is continuous",
				"continuous_map(X.T, zariski_topology(R), spec_adjunct_point(X, R, α))",
				Unfold(continuous.ContinuousMap),
				Simp(Fwd(prime_spectrum.ZariskiSpace.Read(R))),
				By(Read(AdjunctPointInSpectrum, X), R, hom, opens))
			arg.Show(
				"the point map is continuous, and the preimage of D(a) is the unit locus of α(a)",
				By(continuous, preimage))
		}),
})}

// AdjunctSectionExists — for a ring homomorphism α from R to the global
// sections of X, each section s over an open V of Spec R has a section
// over the preimage of V whose germ at a point is that of α(a) times the
// inverse of that of α(b), wherever s is a / b near the point assigned to it.
var AdjunctSectionExists = adjunctSectionExistsThm{family.Add(registry.ProofEntry{
	Name: "AdjunctSectionExists",
	Key:  "prop_bce2c89fc9ae4575",
	Deps: []registry.EntryLike{
		AdjunctPointContinuous,
		locally_ringed_space.UnitIffGermsUnit,
		locally_ringed_space.RestrictHomomorphism,
		locally_ringed_space.GermMul,
		locally_ringed_space.GermOne,
		ring_localization.FractionClassMember,
		presheaf.GermsDetermineSection,
		presheaf.Gluing,
		presheaf.GermRestrict,
		structure_sheaf.StructureSectionsDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀α:(C → B). " +
			"∀V:set(set(C)). " +
			"∀s:(set(C) → set(prod(C, C))).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"V ∈ zariski_topology(R)",
			"s ∈ structure_sections(R, V)",
		},
		Conclusion: "∃t:B. " +
			"    t ∈ X(preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V)).carrier ∧ " +
			"    (∀x:A. ∀W:set(set(C)). ∀a b:C. " +
			"        x ∈ preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V) ∧ " +
			"        W ∈ zariski_topology(R) ∧ " +
			"        spec_adjunct_point(X, R, α, x) ∈ W ∧ " +
			"        W ⊆ V ∧ " +
			"        a ∈ R.carrier ∧ " +
			"        b ∈ R.carrier ∧ " +
			"        (∀q:set(C). q ∈ W ⇒ b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b)) ⇒ " +
			"        sheaf_germ(X.T, " +
			"            λU:set(A). X(U).carrier, " +
			"            X.res, " +
			"            x, " +
			"            preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V), " +
			"            t) = " +
			"        stalk_mul(X.T, " +
			"            X, " +
			"            X.res, " +
			"            x, " +
			"            sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, ⋃X.T, α(a)), " +
			"            εh:set(prod(set(A), B)). " +
			"                h ∈ stalk(X.T, λU:set(A). X(U).carrier, X.res, x) ∧ " +
			"                stalk_mul(X.T, " +
			"                    X, " +
			"                    X.res, " +
			"                    x, " +
			"                    sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, ⋃X.T, α(b)), " +
			"                    h) = " +
			"                stalk_one(X.T, X, X.res, x)))",
	},
		"For each representation s = a/b on W, pull back W. On this open the restricted global "+
			"section α(b) has unit germs and is a unit by UnitIffGermsUnit. Form the local quotient "+
			"section there. FractionClassMember and the ring laws show agreement on overlaps, detected "+
			"by GermsDetermineSection. Select one representative for each resulting open and apply "+
			"Gluing. The cover uses W, where the representation holds, including the empty-cover case."),
})}

// AdjunctSectionGerm — the adjunct section of s is a section over the
// preimage of V whose germ at a point is that of α(a) times the inverse of
// that of α(b), wherever s is a / b near the point assigned to it.
var AdjunctSectionGerm = adjunctSectionGermThm{family.Add(registry.ProofEntry{
	Name: "AdjunctSectionGerm",
	Key:  "prop_1a49f85e3d762d70",
	Reading: "The inverse of the germ of α(b) is a choice read only through its stalk " +
		"membership and product equation; it is a true inverse because b lies outside the " +
		"point assigned to x, where that germ is a unit. Every point of the preimage of V " +
		"meets the germ equation's hypothesis, s being a fraction near each point of V.",
	Deps: []registry.EntryLike{specAdjunctSectionDef, AdjunctSectionExists},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀α:(C → B). " +
			"∀V:set(set(C)). " +
			"∀s:(set(C) → set(prod(C, C))).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"V ∈ zariski_topology(R)",
			"s ∈ structure_sections(R, V)",
		},
		Conclusion: "spec_adjunct_section(X, R, α, V, s) ∈ " +
			"X(preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V)).carrier ∧ " +
			"(∀x:A. ∀W:set(set(C)). ∀a b:C. " +
			"    x ∈ preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V) ∧ " +
			"    W ∈ zariski_topology(R) ∧ " +
			"    spec_adjunct_point(X, R, α, x) ∈ W ∧ " +
			"    W ⊆ V ∧ " +
			"    a ∈ R.carrier ∧ " +
			"    b ∈ R.carrier ∧ " +
			"    (∀q:set(C). q ∈ W ⇒ b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b)) ⇒ " +
			"    sheaf_germ(X.T, " +
			"        λU:set(A). X(U).carrier, " +
			"        X.res, " +
			"        x, " +
			"        preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V), " +
			"        spec_adjunct_section(X, R, α, V, s)) = " +
			"    stalk_mul(X.T, " +
			"        X, " +
			"        X.res, " +
			"        x, " +
			"        sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, ⋃X.T, α(a)), " +
			"        εh:set(prod(set(A), B)). " +
			"            h ∈ stalk(X.T, λU:set(A). X(U).carrier, X.res, x) ∧ " +
			"            stalk_mul(X.T, " +
			"                X, " +
			"                X.res, " +
			"                x, " +
			"                sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, ⋃X.T, α(b)), " +
			"                h) = " +
			"            stalk_one(X.T, X, X.res, x)))",
	},
		"Apply Hilbert choice to AdjunctSectionExists. For an arbitrary section this is the "+
			"read law for the chosen section: section membership and every local-fraction germ "+
			"equation. The inner inverse choice has stalk membership and its product equation."),
})}

// AdjunctSectionHomomorphism — over each open V of Spec R, the adjunct
// section map is a ring homomorphism from the sections over V to the
// sections of X over the preimage of V.
var AdjunctSectionHomomorphism = adjunctSectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AdjunctSectionHomomorphism",
	Key:  "prop_3721aa14d165cbae",
	Deps: []registry.EntryLike{
		AdjunctSectionGerm,
		AdjunctPointContinuous,
		locally_ringed_space.StalkRing,
		locally_ringed_space.GermAdd,
		locally_ringed_space.GermMul,
		locally_ringed_space.GermOne,
		presheaf.GermsDetermineSection,
		structure_sheaf.StructureSheafOfRings,
		ring_localization.FractionAddClass,
		ring_localization.FractionMulClass,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B). ∀V:set(set(C)).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"V ∈ zariski_topology(R)",
		},
		Conclusion: "ring_homomorphism(spec_section_ops(R, V), " +
			"    X(preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V)), " +
			"    spec_adjunct_section(X, R, α, V))",
	},
		"Use the section specification on common local-fraction neighbourhoods. The "+
			"germ laws reduce preservation of operations to fraction arithmetic and "+
			"uniqueness of inverse germs. GermsDetermineSection gives the section equations."),
})}

// AdjunctSectionRestrict — the adjunct section maps commute with
// restriction: the adjunct section of s, restricted from the preimage of V
// to that of W, is the adjunct section of s restricted to W.
var AdjunctSectionRestrict = adjunctSectionRestrictThm{family.Add(registry.ProofEntry{
	Name: "AdjunctSectionRestrict",
	Key:  "prop_c5356831bb9a276a",
	Deps: []registry.EntryLike{
		AdjunctSectionGerm,
		AdjunctPointContinuous,
		presheaf.GermRestrict,
		presheaf.GermsDetermineSection,
		structure_sheaf.StructureRestrictDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀α:(C → B). " +
			"∀V W:set(set(C)). " +
			"∀s:(set(C) → set(prod(C, C))).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"V ∈ zariski_topology(R)",
			"W ∈ zariski_topology(R)",
			"W ⊆ V",
			"s ∈ structure_sections(R, V)",
		},
		Conclusion: "X.res(preimage_on(⋃X.T, spec_adjunct_point(X, R, α), V), " +
			"    preimage_on(⋃X.T, spec_adjunct_point(X, R, α), W), " +
			"    spec_adjunct_section(X, R, α, V, s)) = " +
			"spec_adjunct_section(X, R, α, W, structure_restrict(V, W, s))",
	},
		"The local-fraction specification on W is inherited from that on V. GermRestrict "+
			"identifies the germs of the restricted section, and GermsDetermineSection gives equality."),
})}

// AdjunctStalkLocal — the localization representation and its numerator
// criterion make the induced stalk map local.
var AdjunctStalkLocal = adjunctStalkLocalThm{family.Add(registry.ProofEntry{
	Name: "AdjunctStalkLocal",
	Key:  "prop_77e32120170900d3",
	Deps: []registry.EntryLike{
		AdjunctSectionGerm,
		AdjunctSectionHomomorphism,
		AdjunctSectionRestrict,
		AdjunctPointContinuous,
		specAdjunctPointDef,
		presheaf.StalkMapGerm,
		locally_ringed_space.StalkMapHomomorphism,
		structure_sheaf.StalkAtPrime,
		local_ring.LocalizationAtPrimeUnit,
		ring_ideal.RingUnitDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀α:(C → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(set(C)), set(C) → set(prod(C, C)))).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"x ∈ ⋃X.T",
			"g ∈ " +
				"stalk(zariski_topology(R), " +
				"    structure_sections(R), " +
				"    structure_restrict, " +
				"    spec_adjunct_point(X, R, α, x))",
			"¬ring_unit(stalk_ring(zariski_topology(R), " +
				"        spec_section_ops(R), " +
				"        structure_restrict, " +
				"        spec_adjunct_point(X, R, α, x)), " +
				"    g)",
		},
		Conclusion: "¬ring_unit(stalk_ring(X.T, X, X.res, x), " +
			"    stalk_map(X.T, " +
			"        λU:set(A). X(U).carrier, " +
			"        X.res, " +
			"        spec_adjunct_point(X, R, α), " +
			"        spec_adjunct_section(X, R, α), " +
			"        x, " +
			"        g))",
	},
		"StalkAtPrime represents the input germ by g * ι(b) = ι(a). LocalizationAtPrimeUnit identifies "+
			"its being a nonunit with a lying in the source prime. The coefficient-germ calculation from "+
			"AdjunctSectionGerm and StalkMapGerm sends ι(a) to the germ of α(a), a nonunit by the point "+
			"definition, and ι(b) to a unit. Apply the stalk homomorphism to the representation; its image "+
			"of g cannot be a unit, since then its product with that denominator would be a unit."),
})}

// AdjunctMorphism — the assigned points and the adjunct section maps of a
// ring homomorphism α from R to the global sections of X form a morphism
// of locally ringed spaces from X to Spec R.
var AdjunctMorphism = adjunctMorphismThm{family.Add(registry.ProofEntry{
	Name: "AdjunctMorphism",
	Key:  "prop_27060940d61a641a",
	Deps: []registry.EntryLike{
		AdjunctPointContinuous,
		AdjunctSectionHomomorphism,
		AdjunctSectionRestrict,
		AdjunctStalkLocal,
		structure_sheaf.SpecLocallyRinged,
		locally_ringed_space.LrsMorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
		},
		Conclusion: "lrs_morphism(X, " +
			"    spec_sheaf(R), " +
			"    spec_adjunct_point(X, R, α), " +
			"    spec_adjunct_section(X, R, α))",
	},
		"Assemble continuity, the section homomorphisms and their "+
			"restriction law, and stalk locality, with SpecLocallyRinged."),
})}

// AdjunctionLeft — the global coefficient section of a is sent to α(a).
// Unfolded, its image is the section chosen by the specification of
// specAdjunctSectionDef over the whole spectrum, and α(a) meets that
// specification: its value a/one and any local fraction c/d have equal
// images in each stalk, since a denominator outside the assigned prime has
// unit image. Any two sections meeting it have equal germs, read at the
// global a/one representation, and hence are equal, so the choice is α(a).
var AdjunctionLeft = adjunctionLeftThm{family.Add(registry.ProofEntry{
	Name: "AdjunctionLeft",
	Key:  "prop_4eef2983faafb5e1",
	Build: family.Sections(Statement{
		Binders: "∀X:locally_ringed_space(A, B). ∀R:comm_ring_on(C). ∀α:(C → B). ∀a:C.",
		Hypotheses: []string{
			"ring_homomorphism(R, X(⋃X.T), α)",
			"a ∈ R.carrier",
		},
		Conclusion: "global_section_hom(R, spec_adjunct_section(X, R, α), a) = α(a)",
		Abbrev: Abbrev{
			{Name: "globalGerm", Text: "λx:A. λt:B. " +
				"    sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, ⋃X.T, t)"},
			{Name: "stalkAt", Text: "λx:A. stalk(X.T, λU:set(A). X(U).carrier, X.res, x)"},
			{Name: "stalkRingAt", Text: "λx:A. stalk_ring(X.T, X, X.res, x)"},
			{Name: "stalkMulAt", Text: "λx:A. stalk_mul(X.T, X, X.res, x)"},
			{Name: "stalkOneAt", Text: "λx:A. stalk_one(X.T, X, X.res, x)"},
			{Name: "inverseAt", Text: "λx:A. λg:set(prod(set(A), B)). εh:set(prod(set(A), B)). " +
				"    h ∈ «stalkAt»(x) ∧ «stalkMulAt»(x, g, h) = «stalkOneAt»(x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		fractionImages := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(C). ∀S:comm_ring_on(D). ∀φ:(C → D). ∀p:set(C). ∀a b c d:C. ∀h k:D.",
			Hypotheses: []string{
				"ring_homomorphism(R, S, φ)",
				"prime_ideal(R, p)",
				"∀u:C. u ∈ R.carrier ∖ p ⇒ ring_unit(S, φ(u))",
				"a ∈ R.carrier",
				"b ∈ R.carrier",
				"c ∈ R.carrier",
				"d ∈ R.carrier",
				"b ∉ p",
				"d ∉ p",
				"fraction_class(R.carrier, R.carrier ∖ p, a, b) = fraction_class(R.carrier, R.carrier ∖ p, c, d)",
				"h ∈ S.carrier",
				"k ∈ S.carrier",
				"S.mul(φ(b), h) = S.one",
				"S.mul(φ(d), k) = S.one",
			},
			Conclusion: "S.mul(φ(a), h) = S.mul(φ(c), k)",
		}, func(arg *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S],
			φ *Arrow[C, D], p *Expr[Set[C]], a, b, c, d *Expr[C], h, k *Expr[D], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"φ is a ring homomorphism",
				"p is prime",
				"the complement of p maps to units",
				"a lies in R",
				"b lies in R",
				"c lies in R",
				"d lies in R",
				"b avoids p",
				"d avoids p",
				"the two fractions are equal",
				"h lies in S",
				"k lies in S",
				"h inverts φ(b)",
				"k inverts φ(d)")
			hom, prime, units := parts[0], parts[1], parts[2]
			aIn, bIn, cIn, dIn := parts[3], parts[4], parts[5], parts[6]
			aMember := arg.MemberOf[on.R](a, aIn)
			cMember := arg.MemberOf[on.R](c, cIn)
			denominators := arg.Have(
				"the denominators lie in the multiplicative complement of p",
				"multiplicative_set(R.carrier, R.carrier ∖ p) ∧ b ∈ R.carrier ∖ p ∧ d ∈ R.carrier ∖ p",
				BySets(local_ring.PrimeComplementMultiplicative.Read(R), prime, parts[7], parts[8], bIn, dIn))
			t, clears := arg.ObtainAs[C](
				"equality of fractions gives a denominator clearing the cross products",
				"∃t:C. t ∈ R.carrier ∖ p ∧ R.mul(t, R.mul(a, d)) = R.mul(t, R.mul(c, b))",
				By(
					denominators,
					aIn,
					cIn,
					parts[9],
					ring_localization.FractionClassEq.Read(R).At(
						arg.TermAs[Set[C]]("R.carrier ∖ p"), aMember, b, cMember, d)))
			u, inverse := arg.ObtainAs[D](
				"the image of that denominator has an inverse u in S",
				"∃u:D. u ∈ S.carrier ∧ S.mul(φ(t), u) = S.one",
				By(units.At(t), clears, ring_ideal.RingUnitDef))
			tIn := arg.Have(
				"the clearing denominator lies in R",
				"t ∈ R.carrier",
				BySets(clears))
			crossImages := arg.Have(
				"φ carries the cleared cross-product equality to S",
				"S.mul(φ(t), S.mul(φ(a), φ(d))) = S.mul(φ(t), S.mul(φ(c), φ(b)))",
				By(ring_homomorphism.MapMul.Read(hom), comm_ring.MulIn.Read(R), aIn, bIn, cIn, dIn, tIn, clears))
			imagesIn := arg.Have(
				"all coefficients in the comparison have images in S",
				"φ(a) ∈ S.carrier ∧ φ(b) ∈ S.carrier ∧ φ(c) ∈ S.carrier ∧ φ(d) ∈ S.carrier ∧ φ(t) ∈ S.carrier",
				By(ring_homomorphism.MapIn.Read(hom), aIn, bIn, cIn, dIn, tIn))
			inverseParts := arg.Conjuncts(
				inverse,
				"u lies in S",
				"u inverts φ(t)")
			uMember := arg.MemberOf[on.S](u, inverseParts[0])
			arg.Show(
				"multiply the cleared equation by u·h·k and cancel φ(t)·u = 1; "+
					"as φ(d)·k = φ(b)·h = 1, the sides left are φ(a)·h and φ(c)·k",
				ByArith(
					S,
					parts[10],
					parts[11],
					uMember,
					imagesIn,
					Scaled(arg.TermAs[D]("S.mul(u, S.mul(h, k))"), crossImages),
					Scaled(
						arg.TermAs[D](
							"S.sub(S.mul(φ(a), S.mul(φ(d), S.mul(h, k))), S.mul(φ(c), S.mul(φ(b), S.mul(h, k))))"),
						inverseParts[1]),
					Scaled(arg.TermAs[D]("S.mul(φ(a), h)"), parts[13]),
					Scaled(arg.TermAs[D]("S.mul(φ(c), k)"), parts[12])))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			X locally_ringed_space.LocallyRingedSpaceFact[on.T],
			R comm_ring.CommRingFact[on.R],
			α *Arrow[C, B],
			a *Expr[C],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"α is a ring homomorphism on global sections",
				"a lies in R")
			hom, aIn := parts[0], parts[1]
			ringPresheaf := locally_ringed_space.SheafPresheafOfRings.Read(
				locally_ringed_space.RingedSheaf.Read(X))
			underlying := locally_ringed_space.Presheaf.Read(ringPresheaf)
			topology := presheaf.Topology.Read(underlying)
			sheaf := locally_ringed_space.Sheaf.Read(locally_ringed_space.RingedSheaf.Read(X))
			T := arg.TermAs[Set[Set[A]]]("X.T")
			F := arg.TermAs[Fun[Set[A], RingOps[B]]]("X")
			res := arg.TermAs[Fun3[Set[A], Set[A], B, B]]("X.res")
			Rops := arg.TermAs[RingOps[C]]("R")
			space := arg.TermAs[Set[A]]("⋃X.T")
			spectrum := arg.TermAs[Set[Set[C]]]("prime_spectrum(R)")
			one := arg.TermAs[C]("R.one")
			imageA := arg.TermAs[B]("α(a)")

			_, sDef := arg.LetAs[Fun[Set[C], Set[Prod[C, C]]]]("s",
				"fraction_section(R, prime_spectrum(R), a, R.one)")
			pullback := arg.Have(
				"the point map carries each source point into the spectrum, "+
					"so the preimage of the whole spectrum is the source space",
				"preimage_on(⋃X.T, spec_adjunct_point(X, R, α), prime_spectrum(R)) = ⋃X.T",
				Simp(Fwd(set_basic.Extension)),
				BySets(Read(AdjunctPointInSpectrum, X), R, hom))
			// Q is specAdjunctSectionDef's choice body at s as the unfolding
			// leaves it: the ∀q clause split in two.
			_, qDef := arg.LetAs[Fun[B, Bool]]("Q",
				"λt:B. "+
					"    t ∈ X(⋃X.T).carrier ∧ "+
					"    (∀x:A. ∀W:set(set(C)). ∀c d:C. "+
					"        x ∈ ⋃X.T ∧ "+
					"        W ∈ zariski_topology(R) ∧ "+
					"        spec_adjunct_point(X, R, α, x) ∈ W ∧ "+
					"        W ⊆ prime_spectrum(R) ∧ "+
					"        c ∈ R.carrier ∧ "+
					"        d ∈ R.carrier ∧ "+
					"        ((∀q:set(C). q ∈ W ⇒ d ∉ q) ∧ "+
					"            (∀q:set(C). q ∈ W ⇒ s(q) = fraction_class(R.carrier, R.carrier ∖ q, c, d))) ⇒ "+
					"        «globalGerm»(x, t) = "+
					"        «stalkMulAt»(x, «globalGerm»(x, α(c)), «inverseAt»(x, «globalGerm»(x, α(d)))))")
			chosen := arg.Have(
				"unfolded, the image of a is the adjunct section "+
					"of s over the whole spectrum: the section Q chooses",
				"global_section_hom(R, spec_adjunct_section(X, R, α), a) = εt:B. Q(t)",
				Simp(Fwd(GlobalSectionHomDef)),
				sDef.RwRev(),
				Simp(Fwd(specAdjunctSectionDef)),
				pullback.Rw(),
				qDef.Rw(),
				Basic())
			candidate := arg.Have(
				"α(a) satisfies the full section-choice specification",
				"Q(α(a))",
				Simp(Fwd(qDef)),
				SplitConj(
					Case(
						"α(a) is a global section",
						By(ring_homomorphism.MapIn.Read(hom), aIn)),
					Case(
						"every local fraction representation has the required image germ",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							b.FixAs[Set[Set[C]]]("W")
							c, d := b.FixAs[C]("c"), b.FixAs[C]("d")
							local := b.Assume()
							localParts := b.Conjuncts(
								local,
								"x lies in the source space",
								"W is open",
								"the point of x lies in W",
								"W lies inside the spectrum",
								"c lies in R",
								"d lies in R",
								"d avoids every prime in W",
								"s is c/d on W")
							p, pDef := b.LetAs[Set[C]]("p", "spec_adjunct_point(X, R, α, x)")
							φ, phiDef := b.LetAs[Fun[C, Set[Prod[Set[A], B]]]]("φ",
								"λr:C. «globalGerm»(x, α(r))")
							germHom := b.Have(
								"taking germs after α is a ring homomorphism to the stalk",
								"ring_homomorphism(R, «stalkRingAt»(x), φ)",
								phiDef.Rw(),
								By(locally_ringed_space.CoefficientGermHomomorphism.Read(ringPresheaf), hom, localParts[0]))
							pNonunits := b.Simplified(pDef, Fwd(specAdjunctPointDef))
							complementUnits := b.Have(
								"every element outside the assigned prime has a unit germ",
								"∀u:C. u ∈ R.carrier ∖ p ⇒ ring_unit(«stalkRingAt»(x), φ(u))",
								phiDef.Rw(),
								BySets(pNonunits))
							prime := b.Have(
								"p is a point of the spectrum, hence a prime ideal",
								"p ∈ prime_spectrum(R) ∧ prime_ideal(R, p)",
								BySets(localParts[2], localParts[3], prime_spectrum.PrimeSpectrumDef))
							value := b.Have(
								"the coefficient section has value a/one at p",
								"s(p) = fraction_class(R.carrier, R.carrier ∖ p, a, R.one)",
								sDef.Rw(),
								Simp(Fwd(structure_sheaf.FractionSectionDef)),
								By(prime))
							sourceFractions := b.Have(
								"a/one and c/d are equal fractions with denominators outside p",
								"R.one ∈ R.carrier ∧ "+
									"R.one ∉ p ∧ "+
									"d ∉ p ∧ "+
									"fraction_class(R.carrier, R.carrier ∖ p, a, R.one) = "+
									"fraction_class(R.carrier, R.carrier ∖ p, c, d)",
								By(
									comm_ring.OneIn.Read(R),
									localParts[2],
									prime,
									value,
									localParts[7].At(p),
									localParts[6].At(p),
									ring_ideal.PrimeIdealDef.At(Rops, p)))
							k, kDef := b.LetAs[Set[Prod[Set[A], B]]]("k",
								"«inverseAt»(x, φ(d))")
							stalkRing := b.TermAs[RingOps[Set[Prod[Set[A], B]]]]("«stalkRingAt»(x)")
							stalkOne := b.TermAs[Set[Prod[Set[A], B]]]("«stalkOneAt»(x)")
							stalkDefinition := locally_ringed_space.StalkRingDef.At(T, F, res, x)
							inverseExists := b.Have(
								"the germ of d has an inverse in the stalk",
								"∃h:set(prod(set(A), B)). h ∈ «stalkAt»(x) ∧ «stalkMulAt»(x, φ(d), h) = «stalkOneAt»(x)",
								BySets(
									complementUnits.At(d),
									localParts[5],
									sourceFractions,
									ring_ideal.RingUnitDef.At(stalkRing, b.TermAs[Set[Prod[Set[A], B]]]("φ(d)")),
									stalkDefinition))
							inverse := b.Have(
								"the selected inverse belongs to the stalk and inverts the germ of d",
								"k ∈ «stalkAt»(x) ∧ «stalkMulAt»(x, φ(d), k) = «stalkOneAt»(x)",
								kDef.Rw(),
								By(HilbertDenoted, inverseExists))
							oneFacts := b.Have(
								"one inverts the image of one and acts as the identity on the image of a",
								"«stalkOneAt»(x) ∈ «stalkAt»(x) ∧ "+
									"«stalkMulAt»(x, φ(R.one), «stalkOneAt»(x)) = «stalkOneAt»(x) ∧ "+
									"«stalkMulAt»(x, φ(a), «stalkOneAt»(x)) = φ(a)",
								By(
									ring_homomorphism.MapOne.Read(germHom),
									comm_ring.OneIn.Read(ring_homomorphism.Target.Read(germHom)),
									comm_monoid.RightIdentityOn.Read(
										comm_ring.MulMonoidOn.Read(ring_homomorphism.Target.Read(germHom))),
									aIn,
									ring_homomorphism.MapIn.Read(germHom).AsFact().At(a),
									stalkDefinition))
							evaluated := b.Have(
								"equal source fractions have equal images in the stalk",
								"«stalkRingAt»(x).mul(φ(a), «stalkOneAt»(x)) = «stalkRingAt»(x).mul(φ(c), k)",
								By(
									ring_homomorphism.Target.Read(germHom),
									R,
									complementUnits,
									aIn,
									localParts[4],
									localParts[5],
									prime,
									inverse,
									oneFacts,
									sourceFractions,
									stalkDefinition,
									At(fractionImages, Rops, stalkRing, φ, p, a, one, c, d, stalkOne, k)))
							products := b.Simplified(
								evaluated,
								Fwd(locally_ringed_space.StalkRingDef),
								Fwd(module_record.RingMulDef))
							b.Show(
								"so the local representation gives the germ of α(a)",
								By(products, oneFacts))
						}))))
			spectrumOpen := arg.Have(
				"the whole spectrum is open",
				"prime_spectrum(R) ∈ zariski_topology(R)",
				By(
					Normalized,
					topological_space.SpaceOpen.Read(prime_spectrum.ZariskiIsTopology.Read(R)),
					prime_spectrum.ZariskiSpace.Read(R)))
			coefficientRepresentation := arg.Have(
				"the coefficient section is a/one throughout the spectrum",
				Statement{
					Binders: "∀q:set(C).", Hypotheses: []string{"q ∈ prime_spectrum(R)"},
					Conclusion: "R.one ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, R.one)",
				},
				sDef.Rw(),
				Simp(Fwd(structure_sheaf.FractionSectionDef)),
				BySets(prime_spectrum.PrimeSpectrumDef, ring_ideal.PrimeIdealDef))
			unique := arg.Have(
				"any section satisfying the specification equals α(a)",
				"∀t:B. Q(t) ⇒ t = α(a)",
				Derive(func(b *Argument) {
					t := b.FixAs[B]("t")
					satisfies := b.Assume()
					tSpec := b.Simplified(satisfies, Fwd(qDef))
					aSpec := b.Simplified(candidate, Fwd(qDef))
					tParts := b.Conjuncts(
						tSpec,
						"t is a global section",
						"t has every prescribed local fraction germ")
					aParts := b.Conjuncts(
						aSpec,
						"α(a) is a global section",
						"α(a) has every prescribed local fraction germ")
					germs := b.Have(
						"the two specifications give the same germ at every source point",
						"∀x:A. x ∈ ⋃X.T ⇒ «globalGerm»(x, t) = «globalGerm»(x, α(a))",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inSpace := c.Assume()
							c.Show(
								"read both specifications at the global a/one representation",
								By(
									tParts[1].At(x, spectrum, a, one),
									aParts[1].At(x, spectrum, a, one),
									Read(AdjunctPointInSpectrum, X).At(Rops, α, x),
									R,
									hom,
									coefficientRepresentation,
									inSpace,
									aIn,
									comm_ring.OneIn.Read(R),
									spectrumOpen,
									set_order.SubsetRefl))
						}))
					b.Show(
						"the sheaf's germs determine its global sections",
						By(
							germs,
							tParts[0],
							aParts[0],
							topological_space.SpaceOpen.Read(topology),
							presheaf.GermsDetermineSection.Read(sheaf).AsFact().At(space, t, imageA)))
				}))
			arg.Show(
				"the section selected by its specification is α(a)",
				chosen.Rw(),
				By(HilbertDenoted, candidate, unique))
		})
	}),
})}

// AdjunctionRight — the numerator criterion recovers the point map,
// and localization extensionality recovers the section map.
var AdjunctionRight = adjunctionRightThm{family.Add(registry.ProofEntry{
	Name: "AdjunctionRight",
	Key:  "prop_4f9c034c17cc7bf7",
	Deps: []registry.EntryLike{
		GlobalSectionHom,
		GlobalSectionHomDef,
		specAdjunctPointDef,
		AdjunctSectionGerm,
		AdjunctMorphism,
		locally_ringed_space.MorphismLocal,
		locally_ringed_space.MorphismSections,
		locally_ringed_space.MorphismRestrict,
		locally_ringed_space.MorphismContinuous,
		presheaf.StalkMapGerm,
		locally_ringed_space.StalkMapHomomorphism,
		structure_sheaf.StalkAtPrime,
		local_ring.LocalizationAtPrimeUnit,
		ring_localization.LocalizationHomomorphismExtensional,
		presheaf.GermsDetermineSection,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀R:comm_ring_on(C). " +
			"∀f:(A → set(C)). " +
			"∀ψ:(set(set(C)) → (set(C) → set(prod(C, C))) → B).",
		Hypotheses: []string{
			"lrs_morphism(X, spec_sheaf(R), f, ψ)",
		},
		Conclusion: "(∀x:A. x ∈ ⋃X.T ⇒ spec_adjunct_point(X, R, global_section_hom(R, ψ), x) = f(x)) ∧ " +
			"(∀V:set(set(C)). ∀s:(set(C) → set(prod(C, C))). " +
			"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ " +
			"    spec_adjunct_section(X, R, global_section_hom(R, ψ), V, s) = ψ(V, s))",
	},
		"For points, StalkAtPrime and LocalizationAtPrimeUnit identify a coefficient germ being a "+
			"nonunit with its coefficient lying in f(x). The original stalk homomorphism preserves units "+
			"and MorphismLocal preserves nonunits, so they detect membership in that prime. After this "+
			"point equality identifies the guarded preimages, the original and adjunct stalk "+
			"homomorphisms have the same localization as source. StalkMapGerm and the global-section map "+
			"show agreement on coefficient germs. LocalizationHomomorphismExtensional gives equality on "+
			"all stalk elements; StalkMapGerm and GermsDetermineSection then give the section equation."),
})}

// AffineMorphisms — every morphism of locally ringed spaces from Spec S to
// Spec R comes from a ring homomorphism from R to S: sending a to the
// element of S whose global fraction section is the morphism's image of
// that of a is a ring homomorphism, and its point and section maps are the
// morphism's.
var AffineMorphisms = affineMorphismsThm{family.Add(registry.ProofEntry{
	Name: "AffineMorphisms",
	Key:  "prop_c071c5458ee2cc79",
	Deps: []registry.EntryLike{
		ring_homomorphism.IsomorphismInverse,
		GlobalSectionHom,
		AdjunctionRight,
		AdjunctSectionGerm,
		structure_sheaf.GlobalSections,
		spec_functor.SpecMorphism,
		spec_functor.SpecSectionMapDef,
		ring_localization.FractionMapClass,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:comm_ring_on(B). " +
			"∀f:(set(B) → set(A)). " +
			"∀ψ:(set(set(A)) → (set(A) → set(prod(A, A))) → set(B) → set(prod(B, B))).",
		Hypotheses: []string{
			"lrs_morphism(spec_sheaf(S), spec_sheaf(R), f, ψ)",
		},
		Conclusion: "ring_homomorphism(R, S, «recovery») ∧ " +
			"(∀q:set(B). q ∈ prime_spectrum(S) ⇒ preimage_on(R.carrier, «recovery», q) = f(q)) ∧ " +
			"(∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). " +
			"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ " +
			"    spec_section_map(R, S, «recovery», V, s) = ψ(V, s))",
		Abbrev: Abbrev{
			{Name: "recovery", Text: "λa:A. " +
				"    inverse_on(S.carrier, " +
				"        λb:B. fraction_section(S, prime_spectrum(S), b, S.one), " +
				"        global_section_hom(R, ψ, a))"},
		},
	},
		"GlobalSections and the inverse isomorphism law make the carrier inverse of the global "+
			"fraction map a ring homomorphism. AdjunctionRight and the local-fraction specification "+
			"identify its Spec point and section maps with the original morphism on their carriers."),
})}

// AffineMorphismsInverse — a ring homomorphism φ from R to S is recovered
// from its Spec morphism: the element of S whose global fraction section
// is the image of that of a under the section map of Spec φ is φ(a).
var AffineMorphismsInverse = affineMorphismsInverseThm{family.Add(registry.ProofEntry{
	Name: "AffineMorphismsInverse",
	Key:  "prop_e66501bbb3a9b80e",
	Deps: []registry.EntryLike{
		functions.InverseOnLeft,
		GlobalSectionHomDef,
		structure_sheaf.GlobalSections,
		spec_functor.SpecMorphism,
		spec_functor.SpecSectionMapDef,
		ring_localization.FractionMapToFraction,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B). ∀a:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"a ∈ R.carrier",
		},
		Conclusion: "inverse_on(S.carrier, " +
			"    λb:B. fraction_section(S, prime_spectrum(S), b, S.one), " +
			"    global_section_hom(R, spec_section_map(R, S, φ), a)) = " +
			"φ(a)",
	},
		"FractionMapToFraction computes the global fraction of φ(a). The left inverse law for "+
			"inverse_on, applied to the isomorphism in GlobalSections, recovers φ(a) on the ring carrier."),
})}
