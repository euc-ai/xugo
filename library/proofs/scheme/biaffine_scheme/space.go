// space.go — the glued space: the point over each prime of a chart ring,
// the prime of the overlap a point on both charts generates, the
// topology and its points, the two charts as open sets homeomorphic to
// the spectra of their rings, the overlap as the basic open set of t on
// chart 0 and of s on chart 1, and the rational points as closed points.

package biaffine_scheme

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The points
// ---------------------------------------------------------------------------

// BiaffinePointOverPrime — over each prime of a chart ring lies exactly
// one point: the projections are one-to-one from the points on a chart
// onto the spectrum of its ring.
var BiaffinePointOverPrime = biaffinePointOverPrimeThm{family.Add(registry.ProofEntry{
	Name: "BiaffinePointOverPrime",
	Key:  "prop_307a96b183a0145c",
	Reading: "A prime of A₀ is not A₀, which holds one, so every point over it lies on chart 0. " +
		"When t ∈ p, p generates all of R, t being a unit there with inverse s, as A₁ does; a prime " +
		"partner would need a proper generated ideal, so the partner is A₁. When t ∉ p, clearing a " +
		"power of t from one = Σ rᵢ · pᵢ shows that p generates a proper ideal Q, and the partner " +
		"must be A₁ ∩ Q. Uniqueness is what makes fst one-to-one on chart 0. There the partner A₁ " +
		"is excluded by the clause that both chart ideals generate one ideal of R, A₁ generating R.",
	Deps: []registry.EntryLike{
		biaffinePointsDef,
		lattice_pair.BiaffineDef,
		lattice_pair.BiaffineSwap,
		lattice_pair.BiaffineChartLocalization,
		ring_away.RingAwayDef,
		ring_localization.LocalizationPrimeCorrespondence,
		ring_localization.LocalizationPrimeCorrespondenceInverse,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanContains,
		ring_ideal.SpanLeast,
		ring_ideal.IdealOneIff,
		prime_spectrum.PrimeSpectrumDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "(∀p:set(A). " +
			"    p ∈ prime_spectrum(restrict_ring(R, A₀)) ⇒ " +
			"    (p, COND(t ∈ p, A₁, A₁ ∩ ideal_span(R, p))) ∈ biaffine_points(R, A₀, A₁) ∧ " +
			"    (∀P:prod(set(A), set(A)). " +
			"        P ∈ biaffine_points(R, A₀, A₁) ∧ fst(P) = p ⇒ " +
			"        P = (p, COND(t ∈ p, A₁, A₁ ∩ ideal_span(R, p))))) ∧ " +
			"(∀q:set(A). " +
			"    q ∈ prime_spectrum(restrict_ring(R, A₁)) ⇒ " +
			"    (COND(s ∈ q, A₀, A₀ ∩ ideal_span(R, q)), q) ∈ biaffine_points(R, A₀, A₁) ∧ " +
			"    (∀P:prod(set(A), set(A)). " +
			"        P ∈ biaffine_points(R, A₀, A₁) ∧ snd(P) = q ⇒ " +
			"        P = (COND(s ∈ q, A₀, A₀ ∩ ideal_span(R, q)), q)))",
	},
		"existence at t ∈ p: one = t · s lies in the ideal p generates (SpanContains), which is "+
			"then R.carrier, the ideal A₁ generates as A₁ holds one; at t ∉ p: R = ring_away(R, A₀, "+
			"t) (BiaffineDef, RingAwayDef) makes the ideal Q that p generates the extension of p "+
			"along the localization A₀ → R at the powers of t (BiaffineChartLocalization, "+
			"LocalizationPrimeCorrespondence), a prime of R with A₀ ∩ Q = p, and A₁ ∩ Q is a prime "+
			"of A₁ missing s that generates Q again: r ∈ Q has sⁿ · r ∈ A₁ ∩ Q and r = tⁿ · (sⁿ · "+
			"r). Uniqueness: a partner A₁ makes Q = R, and clearing denominators puts a power of t, "+
			"so t, into p; a prime partner P₁ generates Q and equals A₁ ∩ Q by the same clearing at "+
			"s. The chart-1 half is the chart-0 half at the exchanged datum (BiaffineSwap; "+
			"biaffine_points is symmetric under exchanging the charts and the pair's two ideals)"),
})}

// BiaffineOverlapPrime — a point on both charts generates a prime of the
// overlap R, misses t on chart 0 and s on chart 1, and each of its chart
// ideals is that prime met with its chart ring.
var BiaffineOverlapPrime = biaffineOverlapPrimeThm{family.Add(registry.ProofEntry{
	Name: "BiaffineOverlapPrime",
	Key:  "prop_fc312221b0966fa0",
	Reading: "On both charts the definition keeps one out of the ideal Q the point " +
		"generates, so Q holds no unit of R, neither t nor s. Q is the extension of the " +
		"prime fst(P) along A₀ → R = A₀[1/t] with t outside it, a prime contracting to " +
		"fst(P); Q is also the ideal snd(P) generates, so the same holds on chart 1.",
	Deps: []registry.EntryLike{
		biaffinePointsDef,
		lattice_pair.BiaffineDef,
		lattice_pair.BiaffineChartLocalization,
		ring_localization.LocalizationPrimeCorrespondence,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanContains,
		ring_ideal.UnitNotInProperIdeal,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"P ∈ biaffine_points(R, A₀, A₁)",
			"¬(fst(P) = A₀)",
			"¬(snd(P) = A₁)",
		},
		Conclusion: "t ∉ fst(P) ∧ " +
			"s ∉ snd(P) ∧ " +
			"ideal_span(R, fst(P)) ∈ prime_spectrum(R) ∧ " +
			"fst(P) = A₀ ∩ ideal_span(R, fst(P)) ∧ " +
			"snd(P) = A₁ ∩ ideal_span(R, fst(P))",
	},
		"t ∈ fst(P) or s ∈ snd(P) would put the unit t or s, so one = t · s, into Q (SpanContains, "+
			"UnitNotInProperIdeal), against the definition's last clause; Q is the extended prime of the "+
			"localization A₀ → R at the powers of t (BiaffineChartLocalization, "+
			"LocalizationPrimeCorrespondence) and contracts to fst(P); by the definition Q is also the "+
			"ideal snd(P) generates, and the localization A₁ → R at the powers of s gives the chart-1 half"),
})}

// ---------------------------------------------------------------------------
// The topology
// ---------------------------------------------------------------------------

// BiaffineIsTopology — the sets of points open on both charts form a
// topology.
var BiaffineIsTopology = biaffineIsTopologyThm{family.Add(registry.ProofEntry{
	Name: "BiaffineIsTopology",
	Key:  "prop_95f66adc0b71e272",
	Reading: "U ⊆ biaffine_points is load-bearing: fst is one-to-one on the points of chart " +
		"0 and snd on those of chart 1 (BiaffinePointOverPrime), so the trace of U ∩ V is the " +
		"meet of the traces; on arbitrary pairs of ideals two pairs over one prime could be " +
		"split by an intersection. The empty family unites to ∅, whose traces are empty and open.",
	Deps: []registry.EntryLike{
		biaffineTopologyDef,
		biaffineTraceDef,
		BiaffinePointOverPrime,
		lattice_pair.BiaffineDef,
		prime_spectrum.ZariskiIsTopology,
		topological_space.IsTopology,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"«wa1Biaffine»",
		},
		Conclusion: "is_topology(biaffine_topology(R, A₀, A₁))",
	},
		"for open U and V, biaffine_trace(A₀, fst, U ∩ V) is the meet of the traces "+
			"of U and V by the uniqueness in BiaffinePointOverPrime, and the trace of "+
			"⋃s is the union of the traces; both are Zariski open (ZariskiIsTopology at "+
			"A₀ and at A₁, rings by BiaffineDef), and the same at chart 1 by snd"),
})}

// BiaffineSpace — the topology's points are the points of the datum, and
// the points project onto the whole spectrum of each chart ring.
var BiaffineSpace = biaffineSpaceThm{family.Add(registry.ProofEntry{
	Name: "BiaffineSpace",
	Key:  "prop_8564263a1a25389",
	Reading: "Every prime of A₀ is the chart-0 ideal of a point, and a point's chart-0 ideal is " +
		"a prime of A₀ unless it is A₀ itself, so the points trace the whole spectrum on chart 0, " +
		"which is open; the same on chart 1, so the set of all points is open and every open set " +
		"lies in it. In the zero ring there are no primes and no points, and the topology is {∅}.",
	Deps: []registry.EntryLike{
		biaffinePointsDef,
		biaffineTopologyDef,
		biaffineTraceDef,
		BiaffinePointOverPrime,
		prime_spectrum.ZariskiSpace,
		prime_spectrum.ZariskiIsTopology,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "⋃biaffine_topology(R, A₀, A₁) = biaffine_points(R, A₀, A₁) ∧ " +
			"biaffine_trace(A₀, fst, biaffine_points(R, A₀, A₁)) = prime_spectrum(restrict_ring(R, A₀)) ∧ " +
			"biaffine_trace(A₁, snd, biaffine_points(R, A₀, A₁)) = prime_spectrum(restrict_ring(R, A₁))",
	},
		"the traces by biaffinePointsDef and the existence half of BiaffinePointOverPrime; each spectrum "+
			"is the union of its Zariski topology, hence open in it (ZariskiSpace, ZariskiIsTopology), so "+
			"biaffine_points is open, and every open set is a set of points (biaffineTopologyDef)"),
})}

// BiaffineChartOpen — each chart is open, and its projection is a
// homeomorphism onto the spectrum of the chart ring.
var BiaffineChartOpen = biaffineChartOpenThm{family.Add(registry.ProofEntry{
	Name: "BiaffineChartOpen",
	Key:  "prop_f70920b02309ad2d",
	Reading: "Chart 0 traces the whole spectrum of A₀ on chart 0 and the basic open D(s) on chart 1 " +
		"(BiaffineOverlapPrime), so it is open. A set of points inside chart 0 is open as soon as its " +
		"chart-0 trace is: its chart-1 trace is the image of an open set of D(t) under the homeomorphism " +
		"D(t) ≅ D(s) through the primes of R. The inverse of fst sends a prime to the point over it.",
	Deps: []registry.EntryLike{
		biaffineTopologyDef,
		biaffineTraceDef,
		BiaffineSpace,
		BiaffinePointOverPrime,
		BiaffineOverlapPrime,
		BiaffineIsTopology,
		lattice_pair.BiaffineDef,
		lattice_pair.BiaffineSwap,
		ring_away.RingAwayDef,
		prime_spectrum.ZariskiOpenOpen,
		prime_spectrum.ZariskiOpenBase,
		prime_spectrum.OpenOfBasicNeighbourhoods,
		continuous.HomeomorphicMap,
		continuous.ContinuousMap,
		topological_space.SubtopologyDef,
		topological_space.OpenInOpenSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "{P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀)} ∈ " +
			"biaffine_topology(R, A₀, A₁) ∧ " +
			"{P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(snd(P) = A₁)} ∈ " +
			"biaffine_topology(R, A₀, A₁) ∧ " +
			"homeomorphic_map(subtopology(biaffine_topology(R, A₀, A₁), " +
			"        {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀)}), " +
			"    zariski_topology(restrict_ring(R, A₀)), " +
			"    fst) ∧ " +
			"homeomorphic_map(subtopology(biaffine_topology(R, A₀, A₁), " +
			"        {P:prod(set(A), set(A)) | P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(snd(P) = A₁)}), " +
			"    zariski_topology(restrict_ring(R, A₁)), " +
			"    snd)",
	},
		"chart 0's traces are the spectrum of A₀ (BiaffineSpace) and D(s) "+
			"(BiaffineOverlapPrime), both open (ZariskiSpace, ZariskiOpenOpen); the inverse of fst "+
			"is the point over a prime (BiaffinePointOverPrime); the points of chart 0 over a "+
			"Zariski open W trace W on chart 0 and, on chart 1, the image of W ∩ D(t) under p ↦ A₁ ∩ "+
			"Q, which is open because D(a) ∩ D(t) for a ∈ A₀ goes to D(s · sⁿ · a) with sⁿ · a ∈ A₁ "+
			"(R = ring_away(R, A₁, s), BiaffineDef; ZariskiOpenBase, OpenOfBasicNeighbourhoods); the "+
			"opens of the subtopology are the opens inside the open chart (OpenInOpenSubtopology) "+
			"and the image of one is its chart-0 trace; chart 1 by BiaffineSwap"),
})}

// BiaffineOverlapBasicOpen — the points on both charts form an open set,
// the basic open set of t on chart 0 and of s on chart 1.
var BiaffineOverlapBasicOpen = biaffineOverlapBasicOpenThm{family.Add(registry.ProofEntry{
	Name: "BiaffineOverlapBasicOpen",
	Key:  "prop_59064a24fdb724e0",
	Reading: "A point over a prime p of A₀ lies on chart 1 exactly " +
		"when t ∉ p (BiaffinePointOverPrime pairs a prime holding t " +
		"with A₁), and over q of A₁ on chart 0 exactly when s ∉ q.",
	Deps: []registry.EntryLike{
		biaffineTraceDef,
		BiaffinePointOverPrime,
		BiaffineOverlapPrime,
		BiaffineChartOpen,
		BiaffineIsTopology,
		prime_spectrum.ZariskiOpenDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "{P:prod(set(A), set(A)) | " +
			"    P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁)} ∈ " +
			"biaffine_topology(R, A₀, A₁) ∧ " +
			"biaffine_trace(A₀, " +
			"    fst, " +
			"    {P:prod(set(A), set(A)) | " +
			"        P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁)}) = " +
			"zariski_open(restrict_ring(R, A₀), t) ∧ " +
			"biaffine_trace(A₁, " +
			"    snd, " +
			"    {P:prod(set(A), set(A)) | " +
			"        P ∈ biaffine_points(R, A₀, A₁) ∧ ¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁)}) = " +
			"zariski_open(restrict_ring(R, A₁), s)",
	},
		"⊆ by BiaffineOverlapPrime; ⊇: the point over a prime p of A₀ missing t is (p, A₁ ∩ Q) with "+
			"A₁ ∩ Q ≠ A₁, Q being proper (BiaffinePointOverPrime), and the same at s on chart 1; the "+
			"overlap is the meet of the two charts, open by BiaffineChartOpen and BiaffineIsTopology"),
})}

// ---------------------------------------------------------------------------
// Rational points
// ---------------------------------------------------------------------------

// RationalPointIsClosedPoint — a rational point over a subfield inside
// both charts is itself a point of the glued space, and a closed one.
var RationalPointIsClosedPoint = rationalPointIsClosedPointThm{family.Add(registry.ProofEntry{
	Name: "RationalPointIsClosedPoint",
	Key:  "prop_5ac40e202246e152",
	Reading: "The rational point is its own point of the space: a k-rational point is held by the " +
		"same pair of chart ideals. k a field inside both charts makes each proper chart ideal maximal " +
		"(RationalPointMaximal), hence prime. The complement of the point traces each spectrum minus " +
		"one maximal ideal m — the complement of V(m), open — or the whole spectrum where the point " +
		"lies off that chart; fst being one-to-one on chart 0 is what makes that trace miss only m.",
	Deps: []registry.EntryLike{
		biaffinePointsDef,
		biaffineTopologyDef,
		BiaffineSpace,
		BiaffinePointOverPrime,
		biaffine_rational_point.BiaffineRationalPointDef,
		biaffine_rational_point.RationalPointMaximal,
		ring_ideal.MaximalIsPrime,
		ring_ideal.MaximalIdealMaximal,
		prime_spectrum.ZariskiTopologyDef,
		prime_spectrum.ZariskiClosedDef,
		topological_space.ClosedInDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "P ∈ biaffine_points(R, A₀, A₁) ∧ closed_in(biaffine_topology(R, A₀, A₁), {P})",
	},
		"P is a point: its chart ideals are the chart or maximal (RationalPointMaximal), maximal "+
			"ideals are prime (MaximalIsPrime), and the other clauses of biaffine_points are those of "+
			"biaffine_rational_point (BiaffineRationalPointDef). {P} is closed (ClosedInDef, "+
			"BiaffineSpace): the other points trace prime_spectrum(A₀) minus fst(P) on chart 0 by the "+
			"uniqueness in BiaffinePointOverPrime, the complement of zariski_closed(A₀, fst(P)) since a "+
			"prime holding a maximal ideal is that ideal (MaximalIdealMaximal), and the same on chart 1"),
})}
