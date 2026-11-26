// universe.go — the one host type every free algebra of the cotangent
// domain lives in: a type U is a universe for a ring when it has room
// for the ring's carrier, for every polynomial over the ring in
// variables of U, and for num-many disjoint copies of itself. Under that
// hypothesis an injection of the ring's polynomials into U, the tags
// that put the copies of U side by side, and an injection of the
// carrier into U are chosen once, and every later construction reads
// them without naming them. The choices satisfy what they are chosen
// for; the subsets of prod(num, D) are a universe for every ring whose
// carrier injects into them, and the rings built from one — its
// polynomial ring, its quotients, its localizations, a free algebra in
// the host — have a universe there too, so a tower stays in the host
// chosen for its base.

package simplicial_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The capacity hypothesis
// ---------------------------------------------------------------------------

// CotangentUniverseDef — `cotangent_universe(R, V)`: the set V of the
// host type U has room for the ring R — its carrier, its polynomials in
// every variable of U, and the pairs of a natural number and a member of
// U each inject into V.
var CotangentUniverseDef = cotangentUniverseDefThm{family.Define(registry.DefEntry{
	Name:  "CotangentUniverseDef",
	Key:   "prop_d8e3b04dd7d9d8c",
	Const: "cotangent_universe",
	Type:  "ring_ops(A) → set(U) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:set(U). " +
			"    cotangent_universe(R, V) ⇔ " +
			"    card_le(R.carrier, V) ∧ " +
			"    card_le(polynomial_algebra(R, 𝕌⟨A:U⟩), V) ∧ " +
			"    card_le(𝕌⟨A:prod(num, U)⟩, V)",
	},
	Reading: "Statements take V to be the whole type, 𝕌⟨A:U⟩; a smaller V only strengthens " +
		"the hypothesis. The room is asked of the carrier, not of the ring's type: no type has room " +
		"for the type of its own subsets (Cantor), but a carrier on set(U) may have room in U, so a " +
		"quotient of a ring on U, or of a free algebra in U, has a universe in U, and a tower of " +
		"polynomial rings, quotients and localizations stays in the host chosen for its base. The " +
		"polynomial clause is the room the universe embedding needs (UniverseEmbeddingHost); the " +
		"first clause, the room the names of degree 0 need (CarrierTagInjective), follows from it " +
		"through the constant polynomials over a ring whose zero lies in its carrier and is kept so " +
		"that it is read off directly; the last clause reads no ring and is the room for the tags. " +
		"A tower of rings R, S, T in one host asks the hypothesis of each.",
})}

// ---------------------------------------------------------------------------
// The choices made under it
// ---------------------------------------------------------------------------

// UniverseEmbeddingDef — `universe_embedding(R)`: an injection of the
// polynomials over R in variables of U into U, chosen once for each ring
// — the host embedding every free algebra of the domain over R is read
// through.
var UniverseEmbeddingDef = universeEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseEmbeddingDef",
	Key:   "prop_774114b801ea27a8",
	Const: "universe_embedding",
	Type:  "ring_ops(A) → ((U → num) → A) → U",
	Equations: []string{
		"∀R:ring_ops(A). universe_embedding(R) = (εj:(((U → num) → A) → U). free_algebra_embedding(R, j))",
	},
	Reading: "The choice is arbitrary unless some embedding exists, which " +
		"cotangent_universe(R, V) provides; every statement reading the free algebras through " +
		"it carries that hypothesis. It is chosen per ring and reads no set of variables and " +
		"no degree, so the free algebras over R on every set of names are read through one " +
		"map; two rings with one zero and different carriers may be read through different " +
		"maps. One constant serves every coefficient type: the free algebras over a ring on A " +
		"and over a ring on B are read through its instances at A and at B, in the same host U.",
})}

// UniverseTagDef — `universe_tag(i, u)`: the member u of U carried into
// the i-th of num-many copies of U inside U — one map of two arguments,
// chosen once, injective in the pair (i, u). `universe_tag(0)` and
// `universe_tag(1)` are the two tags that keep two sets of names apart
// in one set of variables.
var UniverseTagDef = universeTagDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseTagDef",
	Key:   "prop_8aa281e4322f50a7",
	Const: "universe_tag",
	Type:  "num → U → U",
	Equations: []string{
		"universe_tag = (εt:(num → U → U). ∀i j:num. ∀u v:U. t(i, u) = t(j, v) ⇒ i = j ∧ u = v)",
	},
	Reading: "The choice is arbitrary unless an injection of prod(num, U) into " +
		"U exists, which the last clause of cotangent_universe provides: then each " +
		"universe_tag(i) is injective and two different tags have disjoint images.",
})}

// CarrierTagDef — `carrier_tag(C, b)`: the member b of a set C of B's
// carried into U by an injection on C chosen once for C — the name in U
// an element of a ring's carrier takes, so that the elements of a ring
// can be the variables of a free algebra in U.
var CarrierTagDef = carrierTagDefThm{family.Define(registry.DefEntry{
	Name:  "CarrierTagDef",
	Key:   "prop_9bb32ef4d225248d",
	Const: "carrier_tag",
	Type:  "set(B) → B → U",
	Equations: []string{
		"∀C:set(B). carrier_tag(C) = (εj:(B → U). injective_on(C, j))",
	},
	Reading: "The choice is arbitrary unless C injects into U, which cotangent_universe(S, V) " +
		"provides at C = S.carrier. One set, one naming: every statement that names S's elements " +
		"reads carrier_tag(S.carrier), so the names of degree 0 of the standard resolutions of S " +
		"over every base ring, and the relative names of degree 0 of every relative resolution of S, " +
		"are one set, image(carrier_tag(S.carrier), S.carrier); two different carriers, even on one " +
		"type, are named by choices of their own. Off C the values are unspecified and never read.",
})}

// ---------------------------------------------------------------------------
// What the choices satisfy
// ---------------------------------------------------------------------------

// UniverseEmbeddingHost — in a universe for R, the universe embedding of
// R is an embedding of R's polynomials: the room the universe has for
// those polynomials is some map injective on them, and the universe
// embedding is chosen among such maps.
var UniverseEmbeddingHost = universeEmbeddingHostThm{family.Add(registry.ProofEntry{
	Name: "UniverseEmbeddingHost",
	Key:  "prop_1342d0460b868245",
	Reading: "The hypothesis is on R itself: the embedding reads R's " +
		"carrier through its polynomials, so a universe for one ring " +
		"says nothing of the embedding of another ring with the same zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "free_algebra_embedding(R, universe_embedding⟨U:U⟩(R))",
	},
		func(a *Argument, R *Expr[RingOps[A]], universe Fact) {
			host := a.TermAs[Set[U]]("𝕌")
			polynomials := a.TermAs[Set[Fun[Fun[U, Nat], A]]]("polynomial_algebra(R, 𝕌)")
			a.Have(
				"the universe has room for the polynomials over R in every variable of U, so some map embeds them",
				"∃j:(((U → num) → A) → U). free_algebra_embedding(R, j)",
				By(
					universe,
					CotangentUniverseDef.At(R, host),
					cardinal.CardLeDef.At(polynomials, host),
					free_algebra.FreeAlgebraEmbeddingDef))
			a.Show(
				"and the universe embedding of R is chosen among the maps that embed them",
				Unfold(UniverseEmbeddingDef))
		}),
})}

// TagPairInjective — in a universe, two tagged members are equal only
// when they carry one index and one member: universe_tag is chosen
// among the maps injective in the pair, and there is one, since the
// room for prod(num, U) is an injection g of the pairs into U and
// t(i, u) = g((i, u)) is such a map.
var TagPairInjective = tagPairInjectiveThm{family.Add(registry.ProofEntry{
	Name: "TagPairInjective",
	Key:  "prop_dddb771f37fbd71f",
	Reading: "R is only a witness: the clause read, the room for prod(num, U), " +
		"reads no ring, so any ring on any type gives it. Without some such " +
		"hypothesis the tag is ε of an unsatisfiable property — at U = bool no map of " +
		"prod(num, bool) into bool is injective — and two tagged members may coincide.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀i j:num. ∀u v:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"universe_tag(i, u) = universe_tag(j, v)",
		},
		Conclusion: "i = j ∧ u = v",
	}, func(a *Argument, R *Expr[RingOps[A]], universe Fact) {
		a.Do(ExistentialConstDefStep(a.TermAs[Fun2[Nat, U, U]]("universe_tag").Core(),
			Case(
				"some map t of an index and a member is injective in the "+
					"pair: an injection g of the pairs, read as t(i, u) = g((i, u))",
				Derive(func(b *Argument) {
					_, injective := b.ObtainAs[Fun[Prod[Nat, U], U]](
						"the room for prod(num, U) is a map g of the pairs into U, injective on them",
						"∃g:(prod(num, U) → U). injective_on(𝕌⟨A:prod(num, U)⟩, g)",
						By(Normalized, universe, CotangentUniverseDef, cardinal.CardLeDef))
					b.Take(b.TermAs[Fun2[Nat, U, U]]("λi:num. λu:U. g((i, u))"))
					b.Show(
						"g identifies two pairs only when they are one pair, one index and one member",
						By(injective, functions.InjectiveOnDef, set_basic.InUniv, pairs.PairEq))
				})),
			Case(
				"universe_tag is chosen among the maps with that property",
				Given(func(b *Argument, chosen Fact) {
					b.Show(
						"so it has the property, which is the claim left general in i, j, u and v",
						By(chosen))
				})),
		))
	}),
})}

// TagInjective — in a universe, each tag universe_tag(i) is injective:
// it is the tag's injectivity in the pair at one index.
var TagInjective = tagInjectiveThm{family.Add(registry.ProofEntry{
	Name: "TagInjective",
	Key:  "prop_accbcaf95029120f",
	Reading: "R is only a witness: the clause read, the room for prod(num, U), " +
		"reads no ring, so any ring on any type gives it. Without some such " +
		"hypothesis the tag is ε of an unsatisfiable property — at U = bool no map " +
		"of prod(num, bool) into bool is injective — and the conclusion can fail.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "injective_on(𝕌⟨A:U⟩, universe_tag(i))",
	}, func(a *Argument, R *Expr[RingOps[A]], i *Expr[Nat], universe Fact) {
		a.Show(
			"two members tagged alike at i are one pair of index and member, so one member",
			By(universe, TagPairInjective, functions.InjectiveOnDef))
	}),
})}

// TagsDisjoint — in a universe, two different tags never meet: a value
// both took would give the two tags one index.
var TagsDisjoint = tagsDisjointThm{family.Add(registry.ProofEntry{
	Name: "TagsDisjoint",
	Key:  "prop_cd168ab6285296c6",
	Reading: "This is what keeps the names of a base algebra, tagged universe_tag(0), apart from an " +
		"algebra's own names, tagged universe_tag(1), in one set of variables. R is only a witness: any " +
		"ring on any type gives the last clause of cotangent_universe, the one read; without some such " +
		"hypothesis (U = bool) universe_tag is ε of an unsatisfiable property and two tags may meet.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀i j:num. ∀u v:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"¬(i = j)",
		},
		Conclusion: "¬(universe_tag(i, u) = universe_tag(j, v))",
	}, func(a *Argument, R *Expr[RingOps[A]], i, j *Expr[Nat], u, v *Expr[U], universe, distinct Fact) {
		a.Show(
			"a value both tags took would give them one index, and i and j differ",
			By(universe, distinct, TagPairInjective.At(R, i, j, u, v)))
	}),
})}

// CarrierTagInjective — the naming of a set that injects into U is
// injective on it: the room C has in U is some map injective on C, and
// the naming of C is chosen among such maps.
var CarrierTagInjective = carrierTagInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CarrierTagInjective",
	Key:  "prop_1682edf15c441a27",
	Reading: "No ring is read: at C = S.carrier the hypothesis is the first clause " +
		"of cotangent_universe(S, 𝕌⟨A:U⟩), and at C = 𝕌⟨A:num⟩ it follows from the last " +
		"clause of any universe, num injecting into prod(num, U). The naming is " +
		"injective on C only; a member of B outside C may take the name of a member of C.",
	Build: family.Theorem(Statement{
		Binders: "∀C:set(B).",
		Hypotheses: []string{
			"card_le(C, 𝕌⟨A:U⟩)",
		},
		Conclusion: "injective_on(C, carrier_tag⟨U:U⟩(C))",
	},
		func(a *Argument, C *Expr[Set[B]], room Fact) {
			host := a.TermAs[Set[U]]("𝕌")
			a.Have(
				"C has room in U, so some map is injective on C",
				"∃j:(B → U). injective_on(C, j)",
				By(Normalized, room, cardinal.CardLeDef.At(C, host)))
			a.Show(
				"and the naming of C is chosen among the maps injective on C",
				Unfold(CarrierTagDef))
		}),
})}

// CarrierTagDecode — the preimage chosen in C under C's naming reads a
// name of a member of C back as some member of C with that name, and,
// when C injects into U, as the member it names.
var CarrierTagDecode = carrierTagDecodeThm{family.Add(registry.ProofEntry{
	Name: "CarrierTagDecode",
	Key:  "prop_de4e1b133124936b",
	Reading: "This is how the augmentation of a standard resolution reads its names of degree " +
		"0 back, and how a map of resolutions carries them to the names of its target. The first " +
		"half asks nothing: the chosen preimage of a name lies in C and carries that name. The " +
		"second asks the room, the naming being then injective on C (CarrierTagInjective).",
	Deps: []registry.EntryLike{
		CarrierTagInjective,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InverseOnLeft,
	},
	Build: family.Card(
		"∀C:set(B).(∀z:U. "+
			"        z ∈ image(carrier_tag(C), C) ⇒ "+
			"        inverse_on(C, carrier_tag(C), z) ∈ C ∧ "+
			"        carrier_tag(C, inverse_on(C, carrier_tag(C), z)) = z) ∧ "+
			"(card_le(C, 𝕌⟨A:U⟩) ⇒ ∀y:B. y ∈ C ⇒ inverse_on(C, carrier_tag⟨U:U⟩(C), carrier_tag(C, y)) = y)",
		"the first conjunct is InverseOnIn and InverseOnRight at the naming of C; "+
			"the second is InverseOnLeft at the injectivity CarrierTagInjective gives"),
})}

// ---------------------------------------------------------------------------
// The powerset host
// ---------------------------------------------------------------------------

// PowerSetUniverse — the subsets of prod(num, D) are a universe for every
// ring whose carrier injects into them.
var PowerSetUniverse = powerSetUniverseThm{family.Add(registry.ProofEntry{
	Name: "PowerSetUniverse",
	Key:  "prop_38199ed2561b904a",
	Reading: "The hypothesis is the first clause of cotangent_universe verbatim; at a " +
		"powerset host the other two follow from it (PolynomialCarrierIntoPowerSet, " +
		"PowerSetTimesNum), so card_le(R.carrier, 𝕌) and cotangent_universe(R, 𝕌) say the " +
		"same. The room is the carrier's, not the type's: at a one-point D the host is 𝒫(ℕ) " +
		"up to that factor, a universe for every ring whose carrier has at most the size of " +
		"the continuum, and a ring on the host's own subsets qualifies when its carrier " +
		"does, as a quotient of a ring with a universe there does (QuotientCotangentUniverse).",
	Deps: []registry.EntryLike{
		CotangentUniverseDef,
		free_algebra.PolynomialCarrierIntoPowerSet,
		cardinal.PowerSetTimesNum,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"card_le(R.carrier, 𝕌⟨A:set(prod(num, D))⟩)",
		},
		Conclusion: "cotangent_universe(R, 𝕌⟨A:set(prod(num, D))⟩)",
	},
		"unfold cotangent_universe: the first clause is the hypothesis; the polynomial clause is "+
			"PolynomialCarrierIntoPowerSet under the same hypothesis; the last clause is PowerSetTimesNum"),
})}

// ConcreteUniverse — the subsets of prod(num, prod(A, prod(B, C))) are a
// universe for every ring of a tower of rings on A, B and C.
var ConcreteUniverse = concreteUniverseThm{family.Add(registry.ProofEntry{
	Name: "ConcreteUniverse",
	Key:  "prop_dbd467e692e1a52a",
	Reading: "No hypothesis, because every ring type is a factor of D = prod(A, prod(B, " +
		"C)), and a carrier is a set of its type: one cite discharges the capacity hypothesis " +
		"of every ring of a tower of three. It sizes the host to the types, which a tower " +
		"that goes on taking quotients cannot keep doing, each quotient on the subsets of the " +
		"last type; there the host is chosen for the base ring and the rings built from it " +
		"keep a universe in it (PolynomialRingCotangentUniverse, QuotientCotangentUniverse, " +
		"LocalizationCotangentUniverse, FreeAlgebraCotangentUniverse).",
	Deps: []registry.EntryLike{
		PowerSetUniverse,
		cardinal.LeftFactorIntoPowerSet,
		cardinal.RightFactorIntoPowerSet,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
		cardinal.CardLeCover,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). "+
			"    cotangent_universe(R, 𝕌⟨A:set(prod(num, prod(A, prod(B, C))))⟩) ∧ "+
			"    cotangent_universe(S, 𝕌⟨A:set(prod(num, prod(A, prod(B, C))))⟩) ∧ "+
			"    cotangent_universe(T, 𝕌⟨A:set(prod(num, prod(A, prod(B, C))))⟩)",
		"PowerSetUniverse at D = prod(A, prod(B, C)) for each ring, its carrier a subset of its type "+
			"(CardLeSubset). A injects by LeftFactorIntoPowerSet; prod(B, C) injects by "+
			"RightFactorIntoPowerSet, and B and C inject into prod(B, C), every b being fst((b, c)) and "+
			"every c being snd((b, c)) (CardLeCover with fst and snd, Fst, Snd), so CardLeTrans gives B and C"),
})}

// ---------------------------------------------------------------------------
// The rings built in a powerset host
// ---------------------------------------------------------------------------

// FreeAlgebraCotangentUniverse — every free algebra in the powerset host
// has a universe there: its carrier is a set of the host's members.
var FreeAlgebraCotangentUniverse = freeAlgebraCotangentUniverseThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraCotangentUniverse",
	Key:  "prop_c9a4abdf2583d82a",
	Reading: "No hypothesis, not even that R is a ring: the argument reads only that " +
		"the carrier is a set of the host's members, which holds of every ring on the host " +
		"type. So a free algebra of the host may serve as the coefficient ring of a further " +
		"algebra, and its quotients have a universe there too (QuotientCotangentUniverse).",
	Deps: []registry.EntryLike{
		UniverseAlgebraRingDef,
		free_algebra.FreeAlgebraRingDef,
		cardinal.CardLeSubset,
		PowerSetUniverse,
	},
	Build: family.Card(
		"∀R:ring_ops(A). ∀X:set(set(prod(num, D))). "+
			"    cotangent_universe(universe_algebra_ring(R, X), 𝕌⟨A:set(prod(num, D))⟩)",
		"the record's carrier is universe_algebra(R, X), a set of the "+
			"host's members (UniverseAlgebraRingDef, FreeAlgebraRingDef), "+
			"so no larger than the host (CardLeSubset); PowerSetUniverse"),
})}

// PolynomialRingCotangentUniverse — the polynomial ring over a ring with
// a universe in the powerset host has a universe there.
var PolynomialRingCotangentUniverse = polynomialRingCotangentUniverseThm{family.Add(registry.ProofEntry{
	Name: "PolynomialRingCotangentUniverse",
	Key:  "prop_548b63210e3477bf",
	Reading: "No ring law is read. The polynomial ring lives on num → A, which the host need " +
		"not fit: the room is that of the polynomials over R's carrier, which R's own room provides.",
	Deps: []registry.EntryLike{
		CotangentUniverseDef,
		free_algebra.UnivariatePolynomialCarrierCardLe,
		polynomial.PolynomialOverDef,
		PowerSetUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:set(prod(num, D))⟩)",
		},
		Conclusion: "cotangent_universe(polynomial_ring(R), 𝕌⟨A:set(prod(num, D))⟩)",
	},
		"the record's carrier is the polynomials over R's carrier, which "+
			"inject into the host by UnivariatePolynomialCarrierCardLe at the "+
			"first clause of R's universe (CotangentUniverseDef); PowerSetUniverse"),
})}

// QuotientCotangentUniverse — the quotient of a ring with a universe in
// the powerset host has a universe there.
var QuotientCotangentUniverse = quotientCotangentUniverseThm{family.Add(registry.ProofEntry{
	Name: "QuotientCotangentUniverse",
	Key:  "prop_a8bf40da667290c",
	Reading: "No ideal and no ring law is read: the cosets of any I are an image " +
		"of R's carrier. The quotient lives on set(A), so it never fits a host its " +
		"type must fit; it fits every host R's carrier fits. A koszul_quotient(R, g) " +
		"and a hypersurface_ring(R, g) are such quotients once unfolded.",
	Deps: []registry.EntryLike{
		CotangentUniverseDef,
		quotient_ring.QuotientCarrierCardLe,
		cardinal.CardLeTrans,
		PowerSetUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀I:set(A).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:set(prod(num, D))⟩)",
		},
		Conclusion: "cotangent_universe(ideal_quotient_ring(R, I), 𝕌⟨A:set(prod(num, D))⟩)",
	},
		"the quotient's carrier is no larger than R's (QuotientCarrierCardLe), which the first clause "+
			"of R's universe puts into the host (CotangentUniverseDef, CardLeTrans); PowerSetUniverse"),
})}

// LocalizationCotangentUniverse — a localization of a ring with a
// universe in the powerset host has a universe there.
var LocalizationCotangentUniverse = localizationCotangentUniverseThm{family.Add(registry.ProofEntry{
	Name: "LocalizationCotangentUniverse",
	Key:  "prop_b4bfee8c3898603",
	Reading: "Any localization, the fraction model on set(prod(A, A)) among them: the " +
		"room is read off the fraction representation every member of L has, not off L's type.",
	Deps: []registry.EntryLike{
		CotangentUniverseDef,
		ring_localization.LocalizationCarrierCardLe,
		ring_localization.MultiplicativeSetDef,
		cardinal.CardLeProduct,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
		cardinal.PairsIntoPowerSet,
		PowerSetUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:set(prod(num, D))⟩)",
			"is_localization_on(R, S, L, ι)",
		},
		Conclusion: "cotangent_universe(L, 𝕌⟨A:set(prod(num, D))⟩)",
	},
		"L's carrier is no larger than the pairs of R's carrier and S (LocalizationCarrierCardLe); S "+
			"lies in R's carrier (MultiplicativeSetDef), which injects into the host by the first clause "+
			"of R's universe, so the pairs are no larger than the pairs of host members (CardLeSubset, "+
			"CardLeTrans, CardLeProduct), which inject into the host (PairsIntoPowerSet); PowerSetUniverse"),
})}
