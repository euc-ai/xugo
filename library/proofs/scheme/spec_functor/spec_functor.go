// spec_functor.go — the contravariant maps on spectra and their structure sheaves.

package spec_functor

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// SpecSectionMapDef — map each local fraction and take the empty class off the preimage.
var SpecSectionMapDef = specSectionMapDefThm{family.Define(registry.DefEntry{
	Name: "SpecSectionMapDef", Const: "spec_section_map",
	Key: "prop_d0ccf61f456d2111",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"set(set(A)) → " +
		"(set(A) → set(prod(A, A))) → " +
		"set(B) → " +
		"set(prod(B, B))",
	Bundles: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀V:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))). " +
			"∀q:set(B). " +
			"    spec_section_map(R, S, φ, V, s, q) = " +
			"    COND(q ∈ prime_spectrum(S) ∧ preimage_on(R.carrier, φ, q) ∈ V, " +
			"        fraction_map(S.mul, " +
			"            S.carrier, " +
			"            φ, " +
			"            R.carrier ∖ preimage_on(R.carrier, φ, q), " +
			"            S.carrier ∖ q, " +
			"            s(preimage_on(R.carrier, φ, q))), " +
			"        ∅)",
	},
})}

// PreimagePrime — the contraction of a prime ideal of S along a ring
// homomorphism is a prime ideal of R. A prime ideal is an ideal, and the
// preimage of an ideal is an ideal; φ sends the one of R to the one of S,
// which q omits; and φ(x) * φ(y) = φ(x * y), so when x * y lies in the
// contraction one of φ(x), φ(y) lies in q by its primality.
var PreimagePrime = preimagePrimeThm{family.Add(registry.ProofEntry{
	Name: "PreimagePrime",
	Key:  "prop_9f4f16dc0af069f8",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B). ∀q:set(B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"prime_ideal(S, q)",
		},
		Conclusion: "prime_ideal(R, preimage_on(R.carrier, φ, q))",
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S], φ *Arrow[A, B],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.S], q *Expr[Set[B]], prime Fact) {
			ideal := a.Have(
				"q is an ideal of S",
				"ring_ideal(S, q)",
				By(ring_ideal.PrimeIdealIdeal.Read(prime)))
			contracted := a.Have(
				"so its contraction is an ideal of R",
				"ring_ideal(R, preimage_on(R.carrier, φ, q))",
				By(ring_homomorphism.PreimageIdeal.Read(hom).At(q), ideal))
			proper := a.Have(
				"φ sends the one of R to the one of S, which q omits",
				"R.one ∉ preimage_on(R.carrier, φ, q)",
				BySets(ring_homomorphism.MapOne.Read(hom), ring_ideal.PrimeIdealProper.Read(prime)))
			primality := a.Have(
				"φ(x) * φ(y) = φ(x * y) lies in q, so φ(x) or φ(y) does",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ R.carrier",
						"y ∈ R.carrier",
						"x * y ∈ preimage_on(R.carrier, φ, q)",
					},
					Conclusion: "x ∈ preimage_on(R.carrier, φ, q) ∨ y ∈ preimage_on(R.carrier, φ, q)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					b.Show(
						"q is prime and holds the product of the images",
						BySets(
							members,
							At(ring_homomorphism.MapMul.Read(hom), x, y),
							At(ring_homomorphism.MapIn.Read(hom), x),
							At(ring_homomorphism.MapIn.Read(hom), y),
							At(ring_ideal.PrimeIdealPrime.Read(prime), φ.Apply(x), φ.Apply(y))))
				}))
			a.Show(
				"these are the conditions defining a prime ideal of R",
				By(contracted, proper, primality, ring_ideal.PrimeIdealDef))
		}),
})}

// SpecMapContinuous — a prime of S contracts to a prime of R, so the point map carries Spec S
// into Spec R. For a in R the contraction of q holds a exactly when q holds φ(a), so the primes
// of S lying over D(a) are those missing φ(a). An open W of Spec R contains, around the
// contraction of each point q over it, a basic open D(a) ⊆ W; then q lies in D(φ(a)), whose
// points lie over D(a) and so over W. Every point of the preimage of W thus has a basic
// neighbourhood inside it, and the preimage is open. The points of a Zariski topology are its
// spectrum, so these two facts are the continuity of the point map.
var SpecMapContinuous = specMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "SpecMapContinuous",
	Key:  "prop_72330ad2515208e4",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
		},
		Conclusion: "continuous_map(zariski_topology(S), " +
			"    zariski_topology(R), " +
			"    preimage_on(R.carrier, φ)) ∧ " +
			"(∀a:A. " +
			"    a ∈ R.carrier ⇒ " +
			"    preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), zariski_open(R, a)) = " +
			"    zariski_open(S, φ(a)))",
	},
		func(arg *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S], φ *Arrow[A, B],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.S]) {
			contracts := PreimagePrime.Read(R)
			targetRing := arg.TermAs[RingOps[B]]("S")
			lands := arg.Have(
				"the point map carries Spec S into Spec R",
				"∀q:set(B). q ∈ prime_spectrum(S) ⇒ preimage_on(R.carrier, φ, q) ∈ prime_spectrum(R)",
				Unfold(prime_spectrum.PrimeSpectrumDef),
				Derive(func(b *Argument) {
					q := b.FixAs[Set[B]]("q")
					point := b.Assume()
					prime := b.Have(
						"q is a prime ideal of S",
						"prime_ideal(S, q)",
						BySets(point))
					b.Show(
						"so its contraction is a prime ideal of R",
						BySets(prime, S, hom, contracts.At(targetRing, φ, q)))
				}))
			preimage := arg.Have(
				"the preimage of D(a) is D(φ(a))",
				Statement{
					Binders: "∀a:A.",
					Hypotheses: []string{
						"a ∈ R.carrier",
					},
					Conclusion: "preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), zariski_open(R, a)) = " +
						"zariski_open(S, φ(a))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("a")
					inR := b.Assume()
					holds := b.Have(
						"a lies in R, so the contraction of q holds a exactly when q holds φ(a)",
						"∀q:set(B). a ∈ preimage_on(R.carrier, φ, q) ⇔ φ(a) ∈ q",
						b.ForEach(func(*Expr[Set[B]]) Action { return BySets(inR) }))
					b.Show(
						"a prime of S lies over D(a) exactly when it misses φ(a)",
						Unfold(prime_spectrum.ZariskiOpenDef),
						Simp(Fwd(set_basic.Extension)),
						b.ForEach(func(q *Expr[Set[B]]) Action {
							return BySets(lands.At(q), holds.At(q))
						}))
				}))
			opens := arg.Have(
				"the preimage of an open set is open",
				Statement{
					Binders: "∀W:set(set(A)).",
					Hypotheses: []string{
						"W ∈ zariski_topology(R)",
					},
					Conclusion: "preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), W) ∈ zariski_topology(S)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("W")
					open := b.Assume()
					preimageW := b.Let("P", b.Term("preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), W)"))
					inP := b.Have(
						"the points of P are the primes of S lying over W",
						"∀q:set(B). q ∈ P ⇔ q ∈ prime_spectrum(S) ∧ preimage_on(R.carrier, φ, q) ∈ W",
						BySets(preimageW))
					near := b.Have(
						"each point of P lies in a basic open set inside P",
						"∀q:set(B). q ∈ P ⇒ ∃f:B. f ∈ S.carrier ∧ q ∈ zariski_open(S, f) ∧ zariski_open(S, f) ⊆ P",
						Derive(func(d *Argument) {
							q := d.FixAs[Set[B]]("q")
							member := d.Assume()
							point := d.Have(
								"q is a prime of S",
								"q ∈ prime_spectrum(S)",
								By(inP.At(q), member))
							overW := d.Have(
								"q lies over W",
								"preimage_on(R.carrier, φ, q) ∈ W",
								By(inP.At(q), member))
							a, basic := d.ObtainAs[A](
								"W is open, so the contraction of q lies in a basic open set D(a) inside W",
								"∃a:A. a ∈ R.carrier ∧ preimage_on(R.carrier, φ, q) ∈ zariski_open(R, a) ∧ zariski_open(R, a) ⊆ W",
								By(prime_spectrum.ZariskiOpenBase.Read(R), open, overW))
							d.Take(φ.Apply(a))
							d.Do(SplitConjAll(
								Case(
									"φ(a) lies in S, as a lies in R",
									By(At(ring_homomorphism.MapIn.Read(hom), a), basic)),
								Case(
									"q, a prime of S over D(a), lies in D(φ(a))",
									BySets(preimage.At(a), point, basic)),
								Case(
									"the points of D(φ(a)) lie over D(a), so over W, and so in P",
									BySets(preimage.At(a), preimageW, basic)),
							))
						}))
					b.Show(
						"so P is open",
						By(prime_spectrum.OpenOfBasicNeighbourhoods.Read(S), near))
				}))
			continuous := arg.Have(
				"the points of each Zariski topology are its spectrum, so the point map is continuous",
				"continuous_map(zariski_topology(S), zariski_topology(R), preimage_on(R.carrier, φ))",
				Unfold(continuous.ContinuousMap),
				Simp(Fwd(prime_spectrum.ZariskiSpace.Read(S)), Fwd(prime_spectrum.ZariskiSpace.Read(R))),
				By(lands, opens))
			arg.Show(
				"the point map is continuous, and the preimage of D(a) is D(φ(a))",
				By(continuous, preimage))
		}),
})}

// SpecSectionIn — A local expression a/b on W pulls back to φ(a)/φ(b) on the preimage of W.
var SpecSectionIn = specSectionInThm{family.Add(registry.ProofEntry{
	Name: "SpecSectionIn",
	Key:  "prop_831063d11824b89a",
	Deps: []registry.EntryLike{
		SpecSectionMapDef,
		SpecMapContinuous,
		PreimagePrime,
		ring_localization.FractionMapClass,
		local_ring.PrimeComplementMultiplicative,
		structure_sheaf.StructureSectionsDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:comm_ring_on(B). " +
			"∀φ:(A → B). " +
			"∀V:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"V ∈ zariski_topology(R)",
			"s ∈ structure_sections(R, V)",
		},
		Conclusion: "spec_section_map(R, S, φ, V, s) ∈ " +
			"structure_sections(S, preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), V))",
	},
		"A local expression a/b on W pulls back to φ(a)/φ(b) on the preimage of W. "+
			"The denominators avoid the target prime by contraction, and FractionMapClass "+
			"identifies the value; SpecMapContinuous makes that neighbourhood open."),
})}

// SpecSectionHomomorphism — SpecSectionIn supplies the carrier condition.
var SpecSectionHomomorphism = specSectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "SpecSectionHomomorphism",
	Key:  "prop_31ab79c9c77265dd",
	Deps: []registry.EntryLike{
		SpecSectionIn,
		ring_localization.FractionMapHomomorphism,
		structure_sheaf.StructureSheafOfRings,
		locally_ringed_space.SectionRing,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B). ∀V:set(set(A)).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"V ∈ zariski_topology(R)",
		},
		Conclusion: "ring_homomorphism(restrict_ring(spec_section_ops(R, V), structure_sections(R, V)), " +
			"    restrict_ring( " +
			"        spec_section_ops(S, preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), V)), " +
			"        structure_sections(S, preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), V))), " +
			"    spec_section_map(R, S, φ, V))",
	},
		"SpecSectionIn supplies the carrier condition. The ring operations are "+
			"pointwise on the open, so FractionMapHomomorphism at each prime gives "+
			"addition, multiplication and one; all sections are empty off the preimage."),
})}

// SpecSectionRestrict — section maps commute with restriction: read pointwise, both sides are
// guarded fraction maps of s, and W ⊆ V makes their guards agree.
var SpecSectionRestrict = specSectionRestrictThm{family.Add(registry.ProofEntry{
	Name: "SpecSectionRestrict",
	Key:  "prop_291adaece51fa7f1",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:comm_ring_on(B). " +
			"∀φ:(A → B). " +
			"∀V W:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"W ⊆ V",
		},
		Conclusion: "structure_restrict(preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), V), " +
			"    preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), W), " +
			"    spec_section_map(R, S, φ, V, s)) = " +
			"spec_section_map(R, S, φ, W, structure_restrict(V, W, s))",
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R], S comm_ring.CommRingFact[on.S], φ *Arrow[A, B],
			V, W *Expr[Set[Set[A]]], s *Arrow[Set[A], Set[Prod[A, A]]], restriction Fact) {
			a.Do(Funext())
			a.FixAs[Set[B]]("q")
			a.FixAs[Prod[B, B]]("z")
			a.Do(Unfold(structure_sheaf.StructureRestrictDef), Unfold(SpecSectionMapDef))
			a.Show(
				"the preimage of W lies in the preimage of V, so at each "+
					"point q both sides hold the same representative pairs z",
				BySets(restriction))
		}),
})}

// SpecStalkLocal — the induced stalk map preserves nonunits because
// contraction preserves the numerator test for a localization at a prime.
var SpecStalkLocal = specStalkLocalThm{family.Add(registry.ProofEntry{
	Name: "SpecStalkLocal",
	Key:  "prop_87d9bf403d0e018a",
	Deps: []registry.EntryLike{
		PreimagePrime,
		SpecMapContinuous,
		SpecSectionHomomorphism,
		SpecSectionRestrict,
		presheaf.StalkMapGerm,
		locally_ringed_space.StalkMapHomomorphism,
		structure_sheaf.StalkAtPrime,
		local_ring.LocalizationAtPrimeUnit,
		ring_localization.FractionMapClass,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:comm_ring_on(B). " +
			"∀φ:(A → B). " +
			"∀q:set(B). " +
			"∀g:set(prod(set(set(A)), set(A) → set(prod(A, A)))).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"q ∈ prime_spectrum(S)",
			"g ∈ " +
				"stalk(zariski_topology(R), " +
				"    structure_sections(R), " +
				"    structure_restrict, " +
				"    preimage_on(R.carrier, φ, q))",
			"¬ring_unit(stalk_ring(zariski_topology(R), " +
				"        spec_section_ops(R), " +
				"        structure_restrict, " +
				"        preimage_on(R.carrier, φ, q)), " +
				"    g)",
		},
		Conclusion: "¬ring_unit( " +
			"    stalk_ring(zariski_topology(S), spec_section_ops(S), structure_restrict, q), " +
			"    stalk_map(zariski_topology(S), " +
			"        structure_sections(S), " +
			"        structure_restrict, " +
			"        preimage_on(R.carrier, φ), " +
			"        spec_section_map(R, S, φ), " +
			"        q, " +
			"        g))",
	},
		"StalkAtPrime gives a representation g * ι(u) = ι(a) with u outside the contracted prime. "+
			"StalkMapGerm and FractionMapClass identify the image of each coefficient germ with the "+
			"coefficient germ of its image under φ. The induced stalk homomorphism therefore carries "+
			"that representation to one with numerator φ(a) and denominator φ(u). "+
			"LocalizationAtPrimeUnit on both stalks identifies nonunits with numerators in their "+
			"primes; contraction gives a in the source prime exactly when φ(a) lies in the target prime."),
})}

// SpecMorphism — Assemble the two locally ringed spectra, continuity, section homomorphisms, restriction compatibility and stalk locality.
var SpecMorphism = specMorphismThm{family.Add(registry.ProofEntry{
	Name: "SpecMorphism",
	Key:  "prop_fb232081f7746bc9",
	Deps: []registry.EntryLike{
		structure_sheaf.SpecLocallyRinged,
		SpecMapContinuous,
		SpecSectionHomomorphism,
		SpecSectionRestrict,
		SpecStalkLocal,
		locally_ringed_space.LrsMorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
		},
		Conclusion: "lrs_morphism(spec_sheaf(S), " +
			"    spec_sheaf(R), " +
			"    preimage_on(R.carrier, φ), " +
			"    spec_section_map(R, S, φ))",
	},
		"Assemble the two locally ringed spectra, continuity, section "+
			"homomorphisms, restriction compatibility and stalk locality."),
})}

// SpecCompose — Contraction composes on prime ideals because φ maps into S.
var SpecCompose = specComposeThm{family.Add(registry.ProofEntry{
	Name: "SpecCompose",
	Key:  "prop_6bb98a4964eb9153",
	Deps: []registry.EntryLike{
		functions.PreimageOnDef,
		SpecSectionMapDef,
		PreimagePrime,
		SpecSectionIn,
		ring_localization.FractionMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀Q:comm_ring_on(C). ∀φ:(A → B). ∀χ:(B → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"ring_homomorphism(S, Q, χ)",
		},
		Conclusion: "(∀q:set(C). " +
			"    q ∈ prime_spectrum(Q) ⇒ " +
			"    preimage_on(R.carrier, λa:A. χ(φ(a)), q) = " +
			"    preimage_on(R.carrier, φ, preimage_on(S.carrier, χ, q))) ∧ " +
			"(∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). " +
			"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ " +
			"    spec_section_map(R, Q, λa:A. χ(φ(a)), V, s) = " +
			"    spec_section_map(S, " +
			"        Q, " +
			"        χ, " +
			"        preimage_on(prime_spectrum(S), preimage_on(R.carrier, φ), V), " +
			"        spec_section_map(R, S, φ, V, s)))",
	},
		"Contraction composes on prime ideals because φ maps into S. FractionMapCompose "+
			"gives equality of section values on the common preimage; both sides are empty off "+
			"it. These are the two carrier-restricted equations for the composite morphism."),
})}

// SpecIdentity — a prime ideal lies in R, so its contraction along the identity is itself.
// A section is compared with its image one point q at a time. At a point of V, q is prime,
// both guards of the section map hold and its value is the identity's fraction map applied
// to s(q), a fraction of R at the multiplicative set R ∖ q, which FractionMapIdentity
// fixes. Off V the guard fails, at its first conjunct when q is not prime and at its second
// when q is a prime, its own contraction, and s is empty there.
var SpecIdentity = specIdentityThm{family.Add(registry.ProofEntry{
	Name: "SpecIdentity",
	Key:  "prop_1f25ac6eb9327d64",
	Build: family.Theorem("∀R:comm_ring_on(A).( "+
		"    ∀p:set(A). p ∈ prime_spectrum(R) ⇒ preimage_on(R.carrier, λa:A. a, p) = p) ∧ "+
		"(∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). "+
		"    V ∈ zariski_topology(R) ∧ s ∈ structure_sections(R, V) ⇒ "+
		"    spec_section_map(R, R, λa:A. a, V, s) = s)",
		func(a *Argument, R comm_ring.CommRingFact[on.R]) {
			fixes := a.Have(
				"a prime ideal lies in R, so contraction along the identity fixes it",
				"∀p:set(A). p ∈ prime_spectrum(R) ⇒ preimage_on(R.carrier, λa:A. a, p) = p",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("p")
					point := b.Assume()
					prime := b.Have(
						"p is a prime ideal of R",
						"prime_ideal(R, p)",
						BySets(point, prime_spectrum.PrimeSpectrumDef))
					inR := b.Have(
						"an ideal lies in its ring",
						"p ⊆ R.carrier",
						By(ring_ideal.IdealSubset.Read(ring_ideal.PrimeIdealIdeal.Read(prime))))
					b.Show(
						"so the members of R lying in p are the members of p",
						BySets(inR))
				}))
			a.Do(SplitConj(
				Case(
					"the identity fixes the points of Spec R",
					By(fixes)),
				Case(
					"the identity fixes each section over an open set",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("V")
						b.FixAs[Fun[Set[A], Set[Prod[A, A]]]]("s")
						given := b.Conjuncts(
							b.Assume(),
							"V is open",
							"s is a section over V")
						open, section := given[0], given[1]
						regular := b.Unfolded(section, structure_sheaf.StructureSectionsDef)
						empty := b.Have(
							"a section is empty off V",
							"∀p:set(A). p ∉ V ⇒ s(p) = ∅",
							BySets(regular))
						pointwise := b.Have(
							"the image of s agrees with s at every point",
							"∀q:set(A). spec_section_map(R, R, λa:A. a, V, s, q) = s(q)",
							Derive(func(c *Argument) {
								q := c.FixAs[Set[A]]("q")
								c.Cases(c.Term("q ∈ V"))
								c.When(
									"at a point of V the guards hold and the identity fixes the fraction s(q)",
									func(d *Argument, inV Fact) {
										point := d.Have(
											"q is a prime of R, the points of the open set V being primes",
											"q ∈ prime_spectrum(R)",
											BySets(prime_spectrum.ZariskiSpace.Read(R), open, inV))
										prime := d.Have(
											"q is a prime ideal of R",
											"prime_ideal(R, q)",
											BySets(point, prime_spectrum.PrimeSpectrumDef))
										multiplicative := d.Have(
											"the complement of a prime is multiplicative",
											"multiplicative_set(R.carrier, R.carrier ∖ q)",
											By(local_ring.PrimeComplementMultiplicative.Read(R), prime))
										local := d.Have(
											"near q the section is locally a fraction",
											"locally_fraction(R, V, q, s)",
											BySets(regular, inV))
										r, u, value := d.Obtain2As[A, A](
											"so s(q) is the class of some r of R over some u of R outside q",
											"∃r u:A. "+
												"    r ∈ R.carrier ∧ u ∈ R.carrier ∧ u ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, r, u)",
											By(d.Unfolded(local, structure_sheaf.LocallyFractionDef)))
										parts := d.Conjuncts(
											value,
											"r lies in R",
											"u lies in R",
											"u lies outside q",
											"s(q) is the class of r over u")
										denominator := d.Have(
											"u lies in R outside q",
											"u ∈ R.carrier ∖ q",
											BySets(parts[1], parts[2]))
										fraction := d.Have(
											"s(q), the class of r ∈ R over u ∈ R ∖ q, is a fraction of R at R ∖ q",
											"s(q) ∈ ring_localization(R.carrier, R.carrier ∖ q)",
											parts[3].Rw(),
											Simp(Fwd(ring_localization.RingLocalizationMember)),
											Witness(r),
											Witness(u),
											By(parts[0], denominator))
										contraction := d.Have(
											"q is its own contraction",
											"preimage_on(R.carrier, λa:A. a, q) = q",
											By(fixes, point))
										// Read by its definition at the contraction q, the section map is guarded by
										// q being a prime in V, and its value is the identity's fraction map at R ∖ q
										// applied to s(q).
										d.Show(
											"both guards hold at q, and FractionMapIdentity fixes the fraction s(q)",
											Simp(Fwd(SpecSectionMapDef)),
											contraction.Rw(),
											By(
												ring_localization.FractionMapIdentity.Read(R).At(
													d.TermAs[Set[A]]("R.carrier ∖ q"), d.TermAs[Set[Prod[A, A]]]("s(q)")),
												multiplicative,
												fraction,
												point,
												inV))
									})
								c.Otherwise(
									"off V the guard fails and s is empty",
									func(d *Argument, offV Fact) {
										vanishes := d.Have(
											"s is empty at q",
											"s(q) = ∅",
											By(empty, offV))
										guardFails := d.Have(
											"a non-prime q fails the guard's first conjunct, and "+
												"a prime q is its own contraction, which lies off V",
											"¬(q ∈ prime_spectrum(R) ∧ preimage_on(R.carrier, λa:A. a, q) ∈ V)",
											By(Normalized, fixes.At(q), offV))
										d.Show(
											"so the section map takes the empty value at q",
											vanishes.Rw(),
											Unfold(SpecSectionMapDef),
											By(guardFails))
									})
							}))
						b.Show(
							"a function is determined by its values",
							By(Normalized, pointwise))
					})),
			))
		}),
})}
