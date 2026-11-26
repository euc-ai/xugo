package spec_functor

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// SpecIsomorphism — the inverse ring map induces the inverse on points and sections.
var SpecIsomorphism = specIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SpecIsomorphism",
	Key:  "prop_64fd9bdeac514878",
	Build: family.Sections(
		Statement{
			Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B).",
			Hypotheses: []string{
				"ring_isomorphism(R, S, φ)",
			},
			Conclusion: "lrs_isomorphism(spec_sheaf(S), " +
				"    spec_sheaf(R), " +
				"    preimage_on(R.carrier, φ), " +
				"    spec_section_map(R, S, φ))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			identityOnCarrierHom := ctx.Lemma(Statement{
				Binders: "∀R:comm_ring_on(A). ∀f:(A → A).",
				Hypotheses: []string{
					"∀a:A. a ∈ R.carrier ⇒ f(a) = a",
				},
				Conclusion: "ring_homomorphism(R, R, f)",
			},
				func(a *Argument, ring Fact, f *Arrow[A, A], fixesCarrier Fact) {
					one := a.TermAs[A]("R.one")
					a.Do(Simp(
						Fwd(ring_homomorphism.RingHomomorphism.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))),
						SplitConj(
							Case(
								"The map preserves the ring operations",
								SplitConj(
									Case(
										"The map preserves the carrier and addition",
										SplitConj(
											Case(
												"The source and target are rings and the carrier is preserved",
												By(Normalized, fixesCarrier, ring)),
											Case(
												"Addition is preserved",
												By(comm_ring.AddIn.Read(ring), fixesCarrier)),
										)),
									Case(
										"Multiplication is preserved",
										By(comm_ring.MulIn.Read(ring), fixesCarrier)),
								)),
							Case(
								"The unit is fixed",
								By(comm_ring.OneIn.Read(ring), fixesCarrier.At(one))),
						))
				})

			specCompositeIdentity := ctx.Lemma(
				Statement{
					Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀f:(A → B). ∀g:(B → A).",
					Hypotheses: []string{
						"ring_homomorphism(R, S, f)",
						"ring_homomorphism(S, R, g)",
						"∀a:A. a ∈ R.carrier ⇒ g(f(a)) = a",
					},
					Conclusion: "(∀p:set(A). " +
						"    p ∈ prime_spectrum(R) ⇒ preimage_on(R.carrier, f, preimage_on(S.carrier, g, p)) = p) ∧ " +
						"(∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). " +
						"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ " +
						"    spec_section_map(S, " +
						"        R, " +
						"        g, " +
						"        preimage_on(prime_spectrum(S), preimage_on(R.carrier, f), V), " +
						"        spec_section_map(R, S, f, V, s)) = " +
						"    s)",
				},
				func(a *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S],
					f *Arrow[A, B], g *Arrow[B, A], inverse Fact) {
					recordR, recordS := a.TermAs[module_record.RingOps[A]]("R"), a.TermAs[module_record.RingOps[B]]("S")
					endomorphisms := a.Have(
						"The identity and composite are ring endomorphisms",
						"ring_homomorphism(R, R, λa:A. a) ∧ ring_homomorphism(R, R, λa:A. g(f(a)))",
						By(inverse, R, identityOnCarrierHom))
					composite := a.TermAs[Fun[A, A]]("λa:A. g(f(a))")
					identity := a.TermAs[Fun[A, A]]("λa:A. a")
					a.Do(SplitConj(
						Case(
							"The composite fixes prime ideals",
							Derive(func(b *Argument) {
								b.FixAs[Set[A]]("p")
								prime := b.Assume()
								b.Show(
									"Functoriality and extensionality reduce the composite to the identity",
									CalcEq(
										Leg(
											b.TermAs[Set[A]]("preimage_on(R.carrier, λa:A. g(f(a)), p)"),
											"Composition on points",
											By(prime, inverse, R, S, SpecCompose.At(recordR, recordS, recordR, f, g))),
										Leg(
											b.TermAs[Set[A]]("preimage_on(R.carrier, λa:A. a, p)"),
											"Carrierwise equality determines the point map",
											By(
												prime,
												inverse,
												endomorphisms,
												R,
												Where(
													SpecPointMapExtensional.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()), "R", recordR).Where(
													"S", recordR).Where(
													"φ", composite).Where(
													"ψ", identity))),
										FinalLeg(
											"The identity fixes the prime ideal",
											By(SpecIdentity.Read(R), prime)),
									))
							})),
						Case(
							"The composite fixes sections",
							Derive(func(b *Argument) {
								b.FixAs[Set[Set[A]]]("V")
								b.FixAs[Fun[Set[A], Set[Prod[A, A]]]]("s")
								section := b.Assume()
								b.Show(
									"Functoriality and extensionality reduce the composite to the identity",
									CalcEq(
										Leg(
											b.TermAs[Fun[Set[A], Set[Prod[A, A]]]]("spec_section_map(R, R, λa:A. g(f(a)), V, s)"),
											"Composition on sections",
											By(section, inverse, R, S, SpecCompose.At(recordR, recordS, recordR, f, g))),
										Leg(
											b.TermAs[Fun[Set[A], Set[Prod[A, A]]]]("spec_section_map(R, R, λa:A. a, V, s)"),
											"Carrierwise equality determines the section map",
											By(
												section,
												inverse,
												endomorphisms,
												R,
												Where(
													SpecSectionMapExtensional.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()), "R", recordR).Where(
													"S", recordR).Where(
													"φ", composite).Where(
													"ψ", identity))),
										FinalLeg(
											"The identity fixes the section",
											By(SpecIdentity.Read(R), section)),
									))
							})),
					))
				})

			return ctx.Theorem(headline,
				func(a *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S],
					φ *Arrow[A, B], isomorphism Fact) {
					recordR, recordS := a.TermAs[module_record.RingOps[A]]("R"), a.TermAs[module_record.RingOps[B]]("S")
					carrierR := a.TermAs[Set[A]]("R.carrier")
					inverseIsomorphism := a.Have(
						"The inverse is a ring isomorphism",
						"ring_isomorphism(S, R, inverse_on(R.carrier, φ))",
						By(isomorphism, ring_homomorphism.IsomorphismInverse))
					ringMaps := a.Have(
						"Both maps are homomorphisms and the forward map is bijective",
						"ring_homomorphism(R, S, φ) ∧ "+
							"ring_homomorphism(S, R, inverse_on(R.carrier, φ)) ∧ "+
							"injective_on(R.carrier, φ) ∧ "+
							"image(φ, R.carrier) = S.carrier",
						By(
							a.Unfolded(isomorphism, ring_homomorphism.RingIsomorphismDef),
							a.Unfolded(inverseIsomorphism, ring_homomorphism.RingIsomorphismDef)))
					inverse := a.Have(
						"The two composites fix their ring carriers",
						"(∀a:A. a ∈ R.carrier ⇒ inverse_on(R.carrier, φ, φ(a)) = a) ∧ "+
							"(∀b:B. b ∈ S.carrier ⇒ φ(inverse_on(R.carrier, φ, b)) = b)",
						By(Normalized, ringMaps, functions.InverseOnLeft, At(functions.InverseOnRight, carrierR, φ)))
					inverseMap := a.TermAs[Fun[B, A]]("inverse_on(R.carrier, φ)")
					forward := a.Have(
						"The ring map induces a morphism of locally ringed spaces from Spec S to Spec R",
						"lrs_morphism(spec_sheaf(S), spec_sheaf(R), preimage_on(R.carrier, φ), spec_section_map(R, S, φ))",
						By(ringMaps, S, SpecMorphism.Read(R).At(recordS, φ)))
					backward := a.Have(
						"The inverse ring map induces the morphism back, from Spec R to Spec S",
						"lrs_morphism(spec_sheaf(R), "+
							"    spec_sheaf(S), "+
							"    preimage_on(S.carrier, inverse_on(R.carrier, φ)), "+
							"    spec_section_map(S, R, inverse_on(R.carrier, φ)))",
						By(ringMaps, R, SpecMorphism.Read(S).At(recordR, inverseMap)))
					spectrumCarrierR := a.Have(
						"The carrier of Spec R is the prime spectrum",
						"⋃zariski_topology(R) = prime_spectrum(R)",
						By(prime_spectrum.ZariskiSpace.Read(R)))
					spectrumCarrierS := a.Have(
						"The carrier of Spec S is the prime spectrum",
						"⋃zariski_topology(S) = prime_spectrum(S)",
						By(prime_spectrum.ZariskiSpace.Read(S)))
					compositeOnSpecR := a.Have(
						"The composite fixes points and sections of Spec R",
						"(∀p:set(A). "+
							"    p ∈ ⋃zariski_topology(R) ⇒ "+
							"    preimage_on(R.carrier, φ, preimage_on(S.carrier, inverse_on(R.carrier, φ), p)) = p) ∧ "+
							"(∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). "+
							"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ "+
							"    spec_section_map(S, "+
							"        R, "+
							"        inverse_on(R.carrier, φ), "+
							"        preimage_on(⋃zariski_topology(S), preimage_on(R.carrier, φ), V), "+
							"        spec_section_map(R, S, φ, V, s)) = "+
							"    s)",
						Derive(func(b *Argument) {
							b.Do(spectrumCarrierR.Rw(), spectrumCarrierS.Rw())
							b.Show(
								"Apply the composite identity on R",
								By(inverse, ringMaps, R, S, At(specCompositeIdentity, recordR, recordS, φ, inverseMap)))
						}))
					compositeOnSpecS := a.Have(
						"The composite fixes points and sections of Spec S",
						"(∀q:set(B). "+
							"    q ∈ ⋃zariski_topology(S) ⇒ "+
							"    preimage_on(S.carrier, inverse_on(R.carrier, φ), preimage_on(R.carrier, φ, q)) = q) ∧ "+
							"(∀U:set(set(B)). ∀t:(set(B) → set(prod(B, B))). "+
							"    U ∈ zariski_topology(S) ∧ t ∈ structure_sections(S, U) ⇒ "+
							"    spec_section_map(R, "+
							"        S, "+
							"        φ, "+
							"        preimage_on(⋃zariski_topology(R), preimage_on(S.carrier, inverse_on(R.carrier, φ)), U), "+
							"        spec_section_map(S, R, inverse_on(R.carrier, φ), U, t)) = "+
							"    t)",
						Derive(func(b *Argument) {
							b.Do(spectrumCarrierR.Rw(), spectrumCarrierS.Rw())
							b.Show(
								"Apply the composite identity on S",
								By(
									inverse,
									ringMaps,
									R,
									S,
									At(
										ctx.AtTypeVars(specCompositeIdentity, TypeBinder.BindA[B](), TypeBinder.BindB[A]()),
										recordS,
										recordR,
										inverseMap,
										φ)))
						}))
					locallyRingedSpectra := a.Have(
						"Both spectra are locally ringed spaces",
						"locally_ringed_space(spec_sheaf(R)) ∧ locally_ringed_space(spec_sheaf(S))",
						By(
							locally_ringed_space.MorphismTarget.Read(forward),
							locally_ringed_space.MorphismSource.Read(forward)))
					a.Show(
						"The induced morphisms are inverse on points and sections",
						By(
							compositeOnSpecR,
							compositeOnSpecS,
							locallyRingedSpectra,
							forward,
							backward,
							Where(
								locally_ringed_space.MorphismInverseIsomorphism.Inst(
									TypeBinder.BindA[Set[B]](),
									TypeBinder.BindB[Fun[Set[B], Set[Prod[B, B]]]](),
									TypeBinder.BindC[Set[A]](),
									TypeBinder.BindD[Fun[Set[A], Set[Prod[A, A]]]]()),
								"g",
								a.TermAs[Fun[Set[A], Set[B]]]("preimage_on(S.carrier, inverse_on(R.carrier, φ))")).Where(
								"g_ψ",
								a.TermAs[Fun[Set[Set[B]], Fun[Fun[Set[B], Set[Prod[B, B]]], Fun[Set[A], Set[Prod[A, A]]]]]](
									"spec_section_map(S, R, inverse_on(R.carrier, φ))"))))
				})
		}),
})}
