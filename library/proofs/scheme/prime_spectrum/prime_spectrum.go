// prime_spectrum.go — the chapter: the prime spectrum of a ring on a
// set and its Zariski topology.
//
// A point of the spectrum is a prime ideal of the ring record R, a set of
// the type set(A); the spectrum is the set of them, of the type
// set(set(A)), and the Zariski topology a family of such sets. Two
// parts, marked by banners: the definitions; the topology and its basic
// open sets.

package prime_spectrum

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// PrimeSpectrumDef — the prime ideals of the ring record R.
var PrimeSpectrumDef = primeSpectrumDefThm{family.Define(registry.DefEntry{
	Name:      "PrimeSpectrumDef",
	Key:       "prop_e3c91781eae05b8b",
	Const:     "prime_spectrum",
	Type:      "ring_ops(A) → set(set(A))",
	Implicit:  []string{},
	Equations: []string{"∀R:ring_ops(A). prime_spectrum(R) = {p:set(A) | prime_ideal(R, p)}"},
})}

// ZariskiClosedDef — `zariski_closed(R, I)`: V(I),
// the primes holding the ideal I.
var ZariskiClosedDef = zariskiClosedDefThm{family.Define(registry.DefEntry{
	Name:     "ZariskiClosedDef",
	Key:      "prop_8d6930c5aed7b215",
	Const:    "zariski_closed",
	Type:     "ring_ops(A) → set(A) → set(set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). zariski_closed(R, I) = {p:set(A) | p ∈ prime_spectrum(R) ∧ I ⊆ p}",
	},
	Deps: []registry.EntryLike{PrimeSpectrumDef},
})}

// ZariskiOpenDef — `zariski_open(R, f)`: D(f), the
// primes missing f.
var ZariskiOpenDef = zariskiOpenDefThm{family.Define(registry.DefEntry{
	Name:     "ZariskiOpenDef",
	Key:      "prop_25c7e50479cef43b",
	Const:    "zariski_open",
	Type:     "ring_ops(A) → A → set(set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀f:A. zariski_open(R, f) = {p:set(A) | p ∈ prime_spectrum(R) ∧ f ∉ p}",
	},
	Deps: []registry.EntryLike{PrimeSpectrumDef},
})}

// ZariskiTopologyDef — `zariski_topology(R)`: the
// open sets of the spectrum, the complements of the V(I).
var ZariskiTopologyDef = zariskiTopologyDefThm{family.Define(registry.DefEntry{
	Name:     "ZariskiTopologyDef",
	Key:      "prop_ce2f8b1a4f3f2b0a",
	Const:    "zariski_topology",
	Type:     "ring_ops(A) → set(set(set(A)))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    zariski_topology(R) = " +
			"    {U:set(set(A)) | ∃I:set(A). ring_ideal(R, I) ∧ U = prime_spectrum(R) ∖ zariski_closed(R, I)}",
	},
	Deps: []registry.EntryLike{ZariskiClosedDef},
})}

// ---------------------------------------------------------------------------
// The topology and its basic open sets
// ---------------------------------------------------------------------------

// OpenOfBasicNeighbourhoods — a set W each of whose points lies in a basic
// open set inside it is open, the converse of ZariskiOpenBase. Let S be
// the members f of c with D(f) ⊆ W: a point of W misses some member of S,
// and a prime missing a member f of S lies in D(f) ⊆ W, so the points of W
// are the primes not holding S — those not holding the span of S, the
// least ideal holding S. W is then the complement of V of that span.
var OpenOfBasicNeighbourhoods = openOfBasicNeighbourhoodsThm{family.Add(registry.ProofEntry{
	Name: "OpenOfBasicNeighbourhoods",
	Key:  "prop_788c3348e155d780",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀W:set(set(A)).",
		Hypotheses: []string{
			"∀p:set(A). p ∈ W ⇒ ∃f:A. f ∈ R.carrier ∧ p ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ W",
		},
		Conclusion: "W ∈ zariski_topology(R)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], W *Expr[Set[Set[A]]], neighbourhoods Fact) {
			basicGenerators := a.Let("S", a.Term("{f:A | f ∈ R.carrier ∧ zariski_open(R, f) ⊆ W}"))
			generatorsInRing := a.Have(
				"S lies in c",
				"S ⊆ R.carrier",
				BySets(basicGenerators))
			spanIdeal := a.Have(
				"so its span is an ideal",
				"ring_ideal(R, ideal_span(R, S))",
				By(ring_ideal.SpanIdeal.Read(ring), generatorsInRing))
			spanContainedIff := a.Have(
				"a prime, an ideal, holds the span exactly when it holds S",
				"∀p:set(A). prime_ideal(R, p) ⇒ (ideal_span(R, S) ⊆ p ⇔ S ⊆ p)",
				BySets(ring_ideal.PrimeIdealIdeal, ring_ideal.SpanLeast, ring_ideal.SpanContains))
			openMembership := a.Have(
				"the points of W are the primes missing some member of S",
				"∀p:set(A). p ∈ W ⇔ prime_ideal(R, p) ∧ ¬(S ⊆ p)",
				BySets(ZariskiOpenMember.Read(ring), neighbourhoods, basicGenerators))
			openAsComplement := a.Have(
				"so W is the complement of V of the span of S",
				"W = prime_spectrum(R) ∖ zariski_closed(R, ideal_span(R, S))",
				Unfold(ZariskiClosedDef),
				Unfold(PrimeSpectrumDef),
				BySets(openMembership, spanContainedIff))
			a.Show(
				"and W is open, the span being an ideal",
				Unfold(ZariskiTopologyDef),
				BySets(openAsComplement, spanIdeal))
		}),
})}

// ZariskiIsTopology — the Zariski open sets form a topology, each axiom
// read through OpenOfBasicNeighbourhoods: a point of u ∩ v lies in a
// D(f) ⊆ u and a D(g) ⊆ v (ZariskiOpenBase), so in D(f * g) = D(f) ∩ D(g),
// inside u ∩ v; a point of a union of open sets lies in one of them, and
// in a D(f) inside that one.
var ZariskiIsTopology = zariskiIsTopologyThm{family.Add(registry.ProofEntry{
	Name: "ZariskiIsTopology",
	Key:  "prop_8504757340a9cce6",
	Build: comm_ring.CommRingOn.Law("is_topology(zariski_topology(R))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(topological_space.IsTopology), SplitConj(
				Case(
					"two open sets meet in an open set",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("u")
						b.FixAs[Set[Set[A]]]("v")
						open := b.Assume()
						near := b.Have(
							"each point of u ∩ v lies in a basic open set inside u ∩ v",
							"∀p:set(A). p ∈ u ∩ v ⇒ ∃h:A. h ∈ R.carrier ∧ p ∈ zariski_open(R, h) ∧ zariski_open(R, h) ⊆ u ∩ v",
							Derive(func(d *Argument) {
								d.FixAs[Set[A]]("p")
								member := d.Assume()
								_, nearF := d.ObtainAs[A](
									"p lies in a basic open set D(f) inside u",
									"∃f:A. f ∈ R.carrier ∧ p ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ u",
									BySets(ZariskiOpenBase.Read(ring), open, member))
								_, nearG := d.ObtainAs[A](
									"and in a basic open set D(g) inside v",
									"∃g:A. g ∈ R.carrier ∧ p ∈ zariski_open(R, g) ∧ zariski_open(R, g) ⊆ v",
									BySets(ZariskiOpenBase.Read(ring), open, member))
								meet := d.Have(
									"D(f) and D(g) meet in D(f * g)",
									"zariski_open(R, f) ∩ zariski_open(R, g) = zariski_open(R, f * g)",
									By(ZariskiOpenMul.Read(ring), nearF, nearG))
								d.Take(d.Term("f * g"))
								d.Do(SplitConjAll(
									Case(
										"f * g lies in c",
										By(comm_ring.MulIn.Read(ring), nearF, nearG)),
									Case(
										"p lies in D(f) ∩ D(g), which is D(f * g)",
										BySets(meet, nearF, nearG)),
									Case(
										"and D(f * g) lies in u ∩ v, as D(f) ⊆ u and D(g) ⊆ v",
										BySets(meet, nearF, nearG)),
								))
							}))
						b.Show(
							"so u ∩ v is open",
							By(OpenOfBasicNeighbourhoods.Read(ring), near))
					})),
				Case(
					"a union of open sets is open",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[Set[A]]]]("s")
						opens := b.Assume()
						near := b.Have(
							"each point of ⋃s lies in a basic open set inside ⋃s",
							"∀p:set(A). p ∈ ⋃s ⇒ ∃f:A. f ∈ R.carrier ∧ p ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ ⋃s",
							Derive(func(d *Argument) {
								d.FixAs[Set[A]]("p")
								member := d.Assume()
								_, inU := d.ObtainAs[Set[Set[A]]](
									"p lies in some member U of s",
									"∃U:set(set(A)). U ∈ s ∧ p ∈ U",
									BySets(member))
								f, nearF := d.ObtainAs[A](
									"U is open, so p lies in a basic open set D(f) inside U",
									"∃f:A. f ∈ R.carrier ∧ p ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ U",
									BySets(ZariskiOpenBase.Read(ring), opens, inU))
								d.Take(f)
								d.Show(
									"and U lies in ⋃s",
									BySets(inU, nearF))
							}))
						b.Show(
							"so ⋃s is open",
							By(OpenOfBasicNeighbourhoods.Read(ring), near))
					})),
			))
		}),
})}

// ZariskiSpace — the Zariski topology's points are the spectrum: every
// open set, a complement in the spectrum, lies in it, and the spectrum
// is itself open, the complement of V(c), which is empty since a prime
// holding R.carrier would hold one.
var ZariskiSpace = zariskiSpaceThm{family.Add(registry.ProofEntry{
	Name:    "ZariskiSpace",
	Key:     "prop_165ae6b167ebe0c3",
	Reading: "one ∈ c makes V(c) empty; in the zero ring the spectrum is ∅ and the topology is {∅}.",
	Build: comm_ring.CommRingOn.Law("⋃zariski_topology(R) = prime_spectrum(R)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			carrierVanishingEmpty := a.Have(
				"no prime holds c, which holds one",
				"zariski_closed(R, R.carrier) = ∅",
				Unfold(ZariskiClosedDef),
				Unfold(PrimeSpectrumDef),
				BySets(comm_ring.OneIn.Read(ring), ring_ideal.PrimeIdealProper))
			spectrumOpen := a.Have(
				"so the spectrum is open, the complement of V(c) for the ideal c",
				"prime_spectrum(R) ∈ zariski_topology(R)",
				Unfold(ZariskiTopologyDef),
				BySets(carrierVanishingEmpty, ring_ideal.CarrierIdeal.Read(ring)))
			opensInSpectrum := a.Have(
				"every open set, a complement in the spectrum, lies in it",
				"∀U:set(set(A)). U ∈ zariski_topology(R) ⇒ U ⊆ prime_spectrum(R)",
				Unfold(ZariskiTopologyDef),
				BySets())
			a.Show(
				"so the open sets unite to the spectrum",
				BySets(opensInSpectrum, spectrumOpen))
		}),
})}

// ZariskiOpenOpen — D(f) is open: each of its points lies in D(f) itself,
// a basic open set inside D(f), and OpenOfBasicNeighbourhoods applies.
var ZariskiOpenOpen = zariskiOpenOpenThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenOpen",
	Key:  "prop_d97b6a9a8650ad39",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ R.carrier",
		},
		Conclusion: "zariski_open(R, f) ∈ zariski_topology(R)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f *Member[A, on.R]) {
			itself := a.Have(
				"each point of D(f) lies in D(f) itself, a basic open set inside D(f)",
				Statement{
					Binders: "∀p:set(A).",
					Hypotheses: []string{
						"p ∈ zariski_open(R, f)",
					},
					Conclusion: "∃g:A. " +
						"    g ∈ R.carrier ∧ p ∈ zariski_open(R, g) ∧ zariski_open(R, g) ⊆ zariski_open(R, f)",
				},
				BySets(f))
			a.Show(
				"so D(f) is open",
				By(OpenOfBasicNeighbourhoods.Read(ring), itself))
		}),
})}

// ZariskiOpenMember — a prime lies in D(f) exactly when it misses f: D(f)
// is the set of the points of the spectrum missing f, and the points of
// the spectrum are the prime ideals.
var ZariskiOpenMember = zariskiOpenMemberThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenMember",
	Key:  "prop_407c05298ce31f68",
	Build: comm_ring.CommRingOn.Law("∀f:A. ∀p:set(A). "+
		"    p ∈ zariski_open(R, f) ⇔ prime_ideal(R, p) ∧ f ∉ p",
		func(a *Argument, _ comm_ring.CommRingFact[on.R]) {
			a.Show(
				"read D(f) and the spectrum by their definitions",
				Unfold(ZariskiOpenDef),
				Unfold(PrimeSpectrumDef),
				BySets())
		}),
})}

// ZariskiOpenMul — two basic open sets meet in the basic open set of the
// product: a prime holds f * g exactly when it holds f or g, primality
// one way and absorption the other, so it misses f * g exactly when it
// misses both.
var ZariskiOpenMul = zariskiOpenMulThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenMul",
	Key:  "prop_65958808fcbc3388",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"f ∈ R.carrier",
			"g ∈ R.carrier",
		},
		Conclusion: "zariski_open(R, f) ∩ zariski_open(R, g) = zariski_open(R, f * g)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f, g *Member[A, on.R]) {
			holds := a.Have(
				"a prime holds f * g exactly when it holds f or g",
				"∀p:set(A). prime_ideal(R, p) ⇒ (f * g ∈ p ⇔ f ∈ p ∨ g ∈ p)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					prime := b.Assume()
					ideal := b.Have(
						"p is an ideal",
						"ring_ideal(R, p)",
						By(ring_ideal.PrimeIdealIdeal, prime))
					b.Iff()
					b.Forward(
						"p is prime, so it holds one of the two factors",
						func(d *Argument, product Fact) {
							d.Show(
								"f or g lies in p",
								By(ring_ideal.PrimeIdealPrime, prime, f, g, product))
						})
					b.Backward(
						"p absorbs a product by a member of c",
						func(d *Argument, either Fact) {
							d.Show(
								"whichever factor lies in p, the product does",
								either.SplitDisj(
									LeftHolds(
										"f lies in p, so g * f does, and g * f is f * g",
										Given(func(e *Argument, fIn Fact) {
											swap := e.Have(
												"f * g is g * f",
												"f * g = g * f",
												By(comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)), f, g))
											e.Show(
												"absorption by g keeps g * f in p",
												swap.Rw(),
												By(ring_ideal.IdealMul, ideal, f, g, fIn))
										})),
									RightHolds(
										"g lies in p, so f * g does",
										Given(func(e *Argument, gIn Fact) {
											e.Show(
												"absorption by f keeps f * g in p",
												By(ring_ideal.IdealMul, ideal, f, g, gIn))
										})),
								))
						})
				}))
			a.Show(
				"so D(f) ∩ D(g) and D(f * g) hold the same primes",
				Unfold(ZariskiOpenDef),
				Unfold(PrimeSpectrumDef),
				BySets(holds))
		}),
})}

// ZariskiOpenBase — every open set is a union of basic open sets: each
// point of an open U lies in some D(f) ⊆ U. U is the complement of some
// V(I), and p, outside V(I), misses some f of I; a prime missing f does
// not hold I, so D(f) misses V(I).
var ZariskiOpenBase = zariskiOpenBaseThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenBase",
	Key:  "prop_58483f81607b1f1c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀U:set(set(A)). ∀p:set(A).",
		Hypotheses: []string{
			"U ∈ zariski_topology(R)",
			"p ∈ U",
		},
		Conclusion: "∃f:A. f ∈ R.carrier ∧ p ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ U",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			U *Expr[Set[Set[A]]],
			p *Expr[Set[A]],
			hypotheses Fact,
		) {
			pointInOpen := a.Conjuncts(
				hypotheses,
				"U is open",
				"p lies in U")
			_, complement := a.Obtain(
				"U is open, the complement of V(I) for an ideal I",
				"∃I:set(A). ring_ideal(R, I) ∧ U = prime_spectrum(R) ∖ zariski_closed(R, I)",
				BySets(a.Unfolded(pointInOpen[0], ZariskiTopologyDef)))
			idealAndComplement := a.Conjuncts(
				complement,
				"I is an ideal",
				"U is the complement of V(I)")
			outside := a.Unfolded(idealAndComplement[1], ZariskiClosedDef)
			f, missed := a.ObtainAs[A](
				"p lies in U, so outside V(I): some f of I lies outside p",
				"∃f:A. f ∈ I ∧ f ∉ p",
				BySets(pointInOpen[1], outside))
			generatorOutsidePrime := a.Conjuncts(
				missed,
				"f lies in I",
				"f lies outside p")
			idealInRing := a.Have(
				"I lies in c",
				"I ⊆ R.carrier",
				By(ring_ideal.IdealSubset, idealAndComplement[0]))
			a.Take(f)
			a.Do(Unfold(ZariskiOpenDef), SplitConjAll(
				Case(
					"f lies in c, as I does",
					BySets(idealInRing, generatorOutsidePrime[0])),
				Case(
					"p, a point of U, is a prime missing f",
					BySets(pointInOpen[1], outside, generatorOutsidePrime[1])),
				Case(
					"a prime missing f does not hold I, so lies outside V(I), in U",
					BySets(outside, generatorOutsidePrime[0])),
			))
		}),
})}

// ZariskiBase — the basic open sets D(f), f ∈ c, are a base of the Zariski
// topology: each is open (ZariskiOpenOpen), and each point of an open set
// lies in one of them inside that set (ZariskiOpenBase).
var ZariskiBase = zariskiBaseThm{family.Add(registry.ProofEntry{
	Name: "ZariskiBase",
	Key:  "prop_73fad8cc8a8aeb3c",
	Build: comm_ring.CommRingOn.Law("topology_base(zariski_topology(R), "+
		"    {zariski_open(R, f) | f:A | f ∈ R.carrier})",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(topological_space.TopologyBaseDef), SplitConj(
				Case(
					"each basic open set D(f) is open",
					BySets(ZariskiOpenOpen.Read(ring))),
				Case(
					"each point of an open set lies in a basic open set inside it",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("u")
						b.FixAs[Set[A]]("x")
						point := b.Assume()
						_, near := b.ObtainAs[A](
							"x lies in some D(f) inside u, f a member of c",
							"∃f:A. f ∈ R.carrier ∧ x ∈ zariski_open(R, f) ∧ zariski_open(R, f) ⊆ u",
							By(ZariskiOpenBase.Read(ring), point))
						b.Take(b.TermAs[Set[Set[A]]]("zariski_open(R, f)"))
						b.Show(
							"D(f), a basic open set, holds x and lies in u",
							BySets(near))
					})),
			))
		}),
})}

// ZariskiOpenCover — D(f) is covered by the D(h), h ∈ H, exactly when a
// power of f lies in the ideal H generates. When no power of f lies in the
// span, PrimeAvoidingPowers puts the span inside a prime p missing f, a
// point of D(f) that lies in no D(h), since H lies in the span and so in p.
// When f ^ n lies in the span, a prime holding the span would hold f ^ n,
// and so f (PrimeIdealPow): a prime missing f does not hold the span, nor
// H, the span being the least ideal holding H, and misses some h of H.
var ZariskiOpenCover = zariskiOpenCoverThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenCover",
	Key:  "prop_2d29a4a3788e68b7",
	Reading: "f ∈ c matters for ⇐: the multiplication is unconstrained off c, so for f ∉ c a " +
		"power could lie in the span of ∅ while D(f) is the whole spectrum. H ⊆ c is not load-bearing.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f:A. ∀H:set(A).",
		Hypotheses: []string{
			"f ∈ R.carrier",
			"H ⊆ R.carrier",
		},
		Conclusion: "zariski_open(R, f) ⊆ ⋃{zariski_open(R, h) | h:A | h ∈ H} ⇔ " +
			"∃n:num. monoid_pow(R.mul, R.one, f, n) ∈ ideal_span(R, H)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f *Expr[A], H *Expr[Set[A]], hypotheses Fact) {
			inRing := a.Conjuncts(
				hypotheses,
				"f lies in c",
				"H lies in c")
			fC, HIn := a.MemberOf[on.R](f, inRing[0]), inRing[1]
			a.Iff()
			a.Forward(
				"the cover gives a power: else a prime above the span lies in D(f) and in no D(h)",
				func(b *Argument, cover Fact) {
					noPowerExists := b.SupposeNot()
					noPower := b.Have(
						"that is, the span holds no power of f",
						"∀n:num. monoid_pow(R.mul, R.one, f, n) ∉ ideal_span(R, H)",
						By(Normalized, noPowerExists))
					spanIdeal := b.Have(
						"the span of H is an ideal",
						"ring_ideal(R, ideal_span(R, H))",
						By(ring_ideal.SpanIdeal.Read(ring), HIn))
					p, above := b.ObtainAs[Set[A]](
						"then the span lies in a prime p missing f",
						"∃p:set(A). prime_ideal(R, p) ∧ ideal_span(R, H) ⊆ p ∧ f ∉ p",
						By(ring_ideal.PrimeAvoidingPowers.Read(ring), spanIdeal, fC, noPower))
					primeAbove := b.Conjuncts(
						above,
						"p is prime",
						"p holds the span",
						"p misses f")
					prime, holdsSpan, missesF := primeAbove[0], primeAbove[1], primeAbove[2]
					inBasic := b.Have(
						"so p lies in D(f)",
						"p ∈ zariski_open(R, f)",
						By(ZariskiOpenMember.Read(ring).At(f, p), prime, missesF))
					outsideCover := b.Have(
						"but in no D(h), h ∈ H: H lies in the span, so in p",
						"p ∉ ⋃{zariski_open(R, h) | h:A | h ∈ H}",
						BySets(ZariskiOpenMember.Read(ring), ring_ideal.SpanContains, holdsSpan))
					b.Show(
						"which the cover of D(f) forbids",
						BySets(cover, inBasic, outsideCover))
				})
			a.Backward(
				"a power of f in the span gives the cover: no prime missing f holds H",
				func(b *Argument, power Fact) {
					n, inSpan := b.UnpackAs[Nat](power, "n")
					notHoldingH := b.Have(
						"a prime missing f does not hold H",
						"∀p:set(A). prime_ideal(R, p) ∧ f ∉ p ⇒ ¬(H ⊆ p)",
						Derive(func(d *Argument) {
							p := d.FixAs[Set[A]]("p")
							prime := d.Assume()
							notSpan := d.Have(
								"holding the span, p would hold f ^ n and so f, which it misses",
								"¬(ideal_span(R, H) ⊆ p)",
								BySets(ring_ideal.PrimeIdealPow.Read(ring).At(p, fC, n), inSpan, prime))
							d.Show(
								"nor H, the span lying in every ideal holding H",
								By(ring_ideal.SpanLeast, ring_ideal.PrimeIdealIdeal, prime, notSpan))
						}))
					b.Show(
						"so a point of D(f) misses some h of H, and lies in D(h)",
						BySets(ZariskiOpenMember.Read(ring), notHoldingH))
				})
		}),
})}

// ZariskiOpenCompact — D(f) is compact. D(f) is open, so it lies in the
// space. Given an open cover C of D(f), let H be the members h of c whose
// D(h) lies inside some member of C. The D(h), h ∈ H, cover D(f): a point
// of D(f) lies in a member of C, which is open, and so in a basic open set
// inside that member. So a power of f lies in the span of H, hence in the
// span of a finite T ⊆ H, and the D(h), h ∈ T, already cover D(f). Choose
// for each h of H a member g(h) of C holding D(h): the image of T under g
// is a finite subfamily of C covering D(f).
var ZariskiOpenCompact = zariskiOpenCompactThm{family.Add(registry.ProofEntry{
	Name: "ZariskiOpenCompact",
	Key:  "prop_9b812251e78f89c4",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ R.carrier",
		},
		Conclusion: "compact_in(zariski_topology(R), zariski_open(R, f))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f *Member[A, on.R]) {
			a.Do(Unfold(compact.CompactInDef), SplitConj(
				Case(
					"D(f) lies in the space, being one of its open sets",
					By(set_order.MemberSubsetUnions, ZariskiOpenOpen.Read(ring), f)),
				Case(
					"every open cover of D(f) has a finite subcover",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[Set[A]]]]("C")
						covering := b.Assume()
						coverParts := b.Conjuncts(
							covering,
							"the members of C are open",
							"and they cover D(f)")
						membersOpen, coversDf := coverParts[0], coverParts[1]
						H, generators := b.LetAs[Set[A]](
							"H", "{h:A | h ∈ R.carrier ∧ ∃U:set(set(A)). U ∈ C ∧ zariski_open(R, h) ⊆ U}")
						inH := b.Have(
							"a member h of c lies in H exactly when D(h) lies inside a member of the cover",
							"∀h:A. h ∈ H ⇔ h ∈ R.carrier ∧ ∃U:set(set(A)). U ∈ C ∧ zariski_open(R, h) ⊆ U",
							BySets(generators))
						HIn := b.Have(
							"H lies in c",
							"H ⊆ R.carrier",
							Simp(Fwd(set_basic.SubsetDef)),
							b.ForEach(func(h *Expr[A]) Action { return By(inH.At(h)) }))

						refined := b.Have(
							"each point of D(f) lies in some D(h), h ∈ H",
							"∀p:set(A). p ∈ zariski_open(R, f) ⇒ ∃h:A. h ∈ H ∧ p ∈ zariski_open(R, h)",
							Derive(func(d *Argument) {
								d.FixAs[Set[A]]("p")
								member := d.Assume()
								_, inU := d.ObtainAs[Set[Set[A]]](
									"p lies in some member U of the cover",
									"∃U:set(set(A)). U ∈ C ∧ p ∈ U",
									BySets(coversDf, member))
								h, near := d.ObtainAs[A](
									"U is open, so p lies in a basic open set D(h) inside U",
									"∃h:A. h ∈ R.carrier ∧ p ∈ zariski_open(R, h) ∧ zariski_open(R, h) ⊆ U",
									BySets(ZariskiOpenBase.Read(ring), membersOpen, inU))
								d.Take(h)
								d.Show(
									"h lies in H, D(h) lying inside the member U of the cover",
									By(inH.At(h), inU, near))
							}))
						basicCover := b.Have(
							"so the D(h), h ∈ H, cover D(f)",
							"zariski_open(R, f) ⊆ ⋃{zariski_open(R, h) | h:A | h ∈ H}",
							BySets(refined))

						_, power := b.ObtainAs[Nat](
							"a power of f lies in the span of H",
							"∃n:num. monoid_pow(R.mul, R.one, f, n) ∈ ideal_span(R, H)",
							By(ZariskiOpenCover.Read(ring).At(f, H), HIn, basicCover))
						T, fewGenerators := b.ObtainAs[Set[A]](
							"so in the span of a finite T ⊆ H",
							"∃T:set(A). finite(T) ∧ T ⊆ H ∧ monoid_pow(R.mul, R.one, f, n) ∈ ideal_span(R, T)",
							By(ring_ideal.SpanFinite.Read(ring), HIn, power))
						fewParts := b.Conjuncts(
							fewGenerators,
							"T is finite",
							"T lies in H",
							"the power of f lies in the span of T")
						finiteT, TWithinH, powerInSpanT := fewParts[0], fewParts[1], fewParts[2]
						TIn := b.Have(
							"T lies in c, as H does",
							"T ⊆ R.carrier",
							BySets(TWithinH, HIn))
						finiteCover := b.Have(
							"so the D(h), h ∈ T, already cover D(f)",
							"zariski_open(R, f) ⊆ ⋃{zariski_open(R, h) | h:A | h ∈ T}",
							By(ZariskiOpenCover.Read(ring).At(f, T), TIn, powerInSpanT))

						g, picks := b.ObtainAs[Fun[A, Set[Set[A]]]](
							"choosing for each h of H a member g(h) of the cover holding D(h)",
							"∃g:(A → set(set(A))). ∀h:A. h ∈ H ⇒ g(h) ∈ C ∧ zariski_open(R, h) ⊆ g(h)",
							By(inH))
						inCover := b.Have(
							"the members g(h), h ∈ T, belong to the cover, T lying in H",
							"image(g, T) ⊆ C",
							Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
							b.ForEach(func(h *Expr[A]) Action {
								return By(picks.At(h), TWithinH, set_basic.SubsetDef)
							}))
						covers := b.Have(
							"and they cover D(f), each D(h) lying inside g(h)",
							"zariski_open(R, f) ⊆ ⋃image(g, T)",
							Simp(Fwd(set_image.UnionsImage)),
							BySets(picks, finiteCover, TWithinH))
						b.Take(b.TermAs[Set[Set[Set[A]]]]("image(g, T)"))
						b.Show(
							"the image of the finite T under g is a finite subcover",
							By(inCover, finite_set.FiniteImage.At(g, T), finiteT, covers))
					})),
			))
		}),
})}
