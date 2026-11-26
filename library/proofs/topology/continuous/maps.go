// maps.go — open maps, closed maps and quotient maps. A map is open when it
// carries open sets to open sets, closed when it carries closed sets to
// closed sets; neither is asked to be continuous. A quotient map carries
// the first space onto the second so that a set of the second is open
// exactly when its preimage is: the second topology is then the quotient
// topology of the map, the finest on the image for which the map is
// continuous, and a map out of the second space is continuous exactly
// when its composite with the quotient map is. A continuous surjection
// that is open or closed is a quotient map.

package continuous

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Quotient maps
// ---------------------------------------------------------------------------

// QuotientOnto — a quotient map carries the space onto the target's points.
var QuotientOnto = quotientOntoThm{family.Add(registry.ProofEntry{
	Name:  "QuotientOnto",
	Key:   "prop_3ab150083fdc3f44",
	Build: QuotientMap.Axiom("image(f, ⋃T) = ⋃S"),
})}

// QuotientOpenIff — under a quotient map a subset of the target is open
// exactly when its preimage is.
var QuotientOpenIff = quotientOpenIffThm{family.Add(registry.ProofEntry{
	Name: "QuotientOpenIff",
	Key:  "prop_ef323274a8867d06",
	Build: QuotientMap.Axiom(Statement{
		Binders: "∀v:set(B).",
		Hypotheses: []string{
			"v ⊆ ⋃S",
		},
		Conclusion: "preimage_on(⋃T, f, v) ∈ T ⇔ v ∈ S",
	}),
})}

// QuotientImpContinuous — a quotient map is continuous: it carries the
// first space onto the second, and an open set of the second space lies
// in that space, so the quotient property makes its preimage open.
var QuotientImpContinuous = quotientImpContinuousThm{family.Add(registry.ProofEntry{
	Name: "QuotientImpContinuous",
	Key:  "prop_2c2dac503a7f869",
	Build: QuotientMap.Law("continuous_map(T, S, f)",
		func(a *Argument, quotient QuotientMapFact[on.T, on.S]) {
			a.Show(
				"f is continuous",
				ContinuousMap.Intro(
					Case(
						"f carries the first space into the second, its image being the whole second space",
						By(QuotientOnto.Read(quotient), set_image.ImageSubsetIff, set_order.SubsetRefl)),
					Case(
						"an open set of the second space lies in that space, so its preimage is open",
						By(QuotientOpenIff.Read(quotient), set_order.MemberSubsetUnions)),
				))
		}),
})}

// OpenSurjectionQuotient — a continuous open map onto the second space
// is a quotient map. A subset v of the second space is the image of its
// preimage, f being onto; so v is open when its preimage is, the map
// being open, and its preimage is open when v is, the map being
// continuous. No axiom enters.
var OpenSurjectionQuotient = openSurjectionQuotientThm{family.Add(registry.ProofEntry{
	Name: "OpenSurjectionQuotient",
	Key:  "prop_2e49d8893e37a35f",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"open_map(T, S, f)",
			"image(f, ⋃T) = ⋃S",
		},
		Conclusion: "quotient_map(T, S, f)",
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			openMap OpenMapFact[on.T, on.S],
			onto Fact,
		) {
			a.Show(
				"f is a quotient map",
				QuotientMap.Intro(
					Case(
						"f is onto the second space",
						By(onto)),
					Case(
						"a subset v of the second space is open exactly when its preimage is",
						Derive(func(b *Argument) {
							b.FixAs[Set[B]]("v")
							vIn := b.Assume()
							b.Iff()
							b.Forward(
								"v is open when its preimage is",
								func(c *Argument, preimageOpen Fact) {
									onV := c.Have(
										"f carries the preimage of v onto v, every point of v being a value of f",
										"image(f, preimage_on(⋃T, f, v)) = v",
										BySets(onto, vIn))
									c.Show(
										"so v is the image of an open set under the open map f",
										By(onV, preimageOpen, openMap, OpenMap))
								})
							b.Backward(
								"the preimage of v is open when v is, f being continuous",
								func(c *Argument, vOpen Fact) {
									c.Show(
										"the preimage of an open set under a continuous map is open",
										By(PreimageOpen.Read(continuous), vOpen))
								})
						})),
				))
		}),
})}

// ClosedSurjectionQuotient — a continuous closed map onto the second
// space is a quotient map. For a subset v of the second space with an
// open preimage, the complement of the preimage in the first space is
// closed, and f carries it onto the complement of v in the second, every
// point there being a value; so that complement is closed, f being
// closed, and v is open. The preimage of an open set is open by
// continuity. No axiom enters.
var ClosedSurjectionQuotient = closedSurjectionQuotientThm{family.Add(registry.ProofEntry{
	Name: "ClosedSurjectionQuotient",
	Key:  "prop_425c551e945fdeb4",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"closed_map(T, S, f)",
			"image(f, ⋃T) = ⋃S",
		},
		Conclusion: "quotient_map(T, S, f)",
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			closedMap ClosedMapFact[on.T, on.S],
			onto Fact,
		) {
			a.Show(
				"f is a quotient map",
				QuotientMap.Intro(
					Case(
						"f is onto the second space",
						By(onto)),
					Case(
						"a subset v of the second space is open exactly when its preimage is",
						Derive(func(b *Argument) {
							b.FixAs[Set[B]]("v")
							vIn := b.Assume()
							b.Iff()
							b.Forward(
								"v is open when its preimage is",
								func(c *Argument, preimageOpen Fact) {
									complementClosed := c.Have(
										"the complement of the preimage in the first space is closed",
										"closed_in(T, ⋃T ∖ preimage_on(⋃T, f, v))",
										By(topological_space.OpenClosedComplement, preimageOpen))
									onComplement := c.Have(
										"f carries it onto the complement of v, every point of the second space being a value",
										"image(f, ⋃T ∖ preimage_on(⋃T, f, v)) = ⋃S ∖ v",
										onto.RwRev(),
										BySets())
									complementOfV := c.Have(
										"so the complement of v is closed, the image of a closed set under the closed map f",
										"closed_in(S, ⋃S ∖ v)",
										onComplement.RwRev(),
										By(closedMap, ClosedMap, complementClosed))
									c.Show(
										"v lies in the second space with a closed complement there, so it is open",
										By(topological_space.OpenClosedComplement, vIn, complementOfV))
								})
							b.Backward(
								"the preimage of v is open when v is, f being continuous",
								func(c *Argument, vOpen Fact) {
									c.Show(
										"the preimage of an open set under a continuous map is open",
										By(PreimageOpen.Read(continuous), vOpen))
								})
						})),
				))
		}),
})}

// QuotientUniversal — a map out of the target of a quotient map is
// continuous exactly when its composite with the quotient map is. Forward,
// a quotient map is continuous and continuous maps compose. Backward, a
// point of the second space is a value of f, so g carries it into the
// third space; and the preimage under g of an open set w, pulled back
// along f, is the preimage of w under the composite, open, so it is open
// in the second space by the quotient property. No axiom enters.
var QuotientUniversal = quotientUniversalThm{family.Add(registry.ProofEntry{
	Name: "QuotientUniversal",
	Key:  "prop_6cf2f32319957fe",
	Build: QuotientMap.Law("∀R:set(set(C)). ∀g:(B → C). "+
		"    (continuous_map(S, R, g) ⇔ continuous_map(T, R, g ∘ f))",
		func(a *Argument, quotient QuotientMapFact[on.T, on.S], R *Expr[Set[Set[C]]], g *Arrow[B, C]) {
			fContinuous := QuotientImpContinuous.Read(quotient)
			a.Iff()

			a.Forward(
				"g ∘ f is continuous, a composite of continuous maps",
				func(b *Argument, gContinuous Fact) {
					b.Show(
						"f is continuous, and so is g",
						By(Compose.Read(fContinuous), gContinuous))
				})

			a.Backward(
				"g is continuous when g ∘ f is",
				func(b *Argument, composite Fact) {
					onto := QuotientOnto.Read(quotient).AsFact()
					b.Show(
						"g is continuous",
						ContinuousMap.Intro(
							Case(
								"g carries the second space into the third: its points are the values of f, carried there by g ∘ f",
								onto.RwRev(),
								Simp(Fwd(set_image.ForallInImage)),
								By(MapsInto.Read(composite), functions.ComposeApply)),
							Case(
								"the preimage under g of an open set w is open: pulled back along f it is open",
								Derive(func(c *Argument) {
									c.FixAs[Set[C]]("w")
									wOpen := c.Assume()
									pulled := c.Have(
										"pulled back along f, the preimage of w under g is the preimage of w under g ∘ f",
										"preimage_on(⋃T, f, preimage_on(⋃S, g, w)) = preimage_on(⋃T, g ∘ f, w)",
										BySets(MapsInto.Read(fContinuous), functions.ComposeApply))
									pulledOpen := c.Have(
										"which is open, g ∘ f being continuous",
										"preimage_on(⋃T, f, preimage_on(⋃S, g, w)) ∈ T",
										pulled.Rw(),
										By(PreimageOpen.Read(composite), wOpen))
									c.Show(
										"so the preimage of w under g, a subset of the second space, is open there, f being a quotient map",
										BySets(QuotientOpenIff.Read(quotient), pulledOpen))
								})),
						))
				})
		}),
})}

// QuotientCompose — quotient maps compose. The composite is onto, its
// image the image under g of the image under f. Its preimage of a subset w
// of the third space is the preimage under f of the preimage of w under g,
// a subset of the second space: by the quotient property of f it is open
// exactly when that preimage under g is, and by the quotient property of g
// exactly when w is. No axiom enters.
var QuotientCompose = quotientComposeThm{family.Add(registry.ProofEntry{
	Name: "QuotientCompose",
	Key:  "prop_9af5594a19a694f4",
	Build: QuotientMap.Law(Statement{
		Binders: "∀R:set(set(C)). ∀g:(B → C).",
		Hypotheses: []string{
			"quotient_map(S, R, g)",
		},
		Conclusion: "quotient_map(T, R, g ∘ f)",
	},
		func(
			a *Argument,
			first QuotientMapFact[on.T, on.S],
			R *Expr[Set[Set[C]]],
			g *Arrow[B, C],
			second QuotientMapFact[on.S, on.R],
		) {
			fContinuous := QuotientImpContinuous.Read(first)
			a.Show(
				"g ∘ f is a quotient map",
				QuotientMap.Intro(
					Case(
						"g ∘ f is onto the third space, its image the image under g of the image under f",
						Simp(Fwd(set_image.ImageCompose)),
						By(Normalized, QuotientOnto.Read(first), QuotientOnto.Read(second))),
					Case(
						"a subset w of the third space is open exactly when its preimage under g ∘ f is",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[C]]("w")
							wIn := b.Assume()
							pulled := b.Have(
								"the preimage of w under g ∘ f is the preimage under f of its preimage under g",
								"preimage_on(⋃T, g ∘ f, w) = preimage_on(⋃T, f, preimage_on(⋃S, g, w))",
								BySets(MapsInto.Read(fContinuous), functions.ComposeApply))
							b.Show(
								"the quotient properties of f and of g",
								pulled.Rw(),
								BySets(QuotientOpenIff.Read(first), QuotientOpenIff.Read(second).At(w), wIn))
						})),
				))
		}),
})}

// QuotientTopologyCoinduced — the quotient topology is the coinduced
// topology on the image of the space: both have the same open sets.
var QuotientTopologyCoinduced = quotientTopologyCoinducedThm{family.Add(registry.ProofEntry{
	Name: "QuotientTopologyCoinduced",
	Key:  "prop_5f06f1d63d65f342",
	Build: family.Theorem("∀T:set(set(A)). ∀f:(A → B). "+
		"    quotient_topology(T, f) = coinduced_topology(image(f, ⋃T), T, f)",
		func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, B]) {
			a.Do(Simp(Fwd(QuotientTopologyDef), Fwd(topological_space.CoinducedTopologyDef)), Basic())
		}),
})}

// QuotientTopologyTopology — the quotient topology of a map is a
// topology, as the coinduced topology on the image of the space.
var QuotientTopologyTopology = quotientTopologyTopologyThm{family.Add(registry.ProofEntry{
	Name: "QuotientTopologyTopology",
	Key:  "prop_692de5e8e80bc5e6",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "is_topology(quotient_topology(T, f))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, B], topology Fact) {
			a.Do(Simp(Fwd(QuotientTopologyCoinduced)))
			a.Do(By(topology, topological_space.CoinducedTopology.At(T, a.TermAs[Set[B]]("image(f, ⋃T)"), f)))
		}),
})}

// QuotientMapIff — a map is a quotient map exactly when it is onto and
// the second topology is its quotient topology. Once the image is the
// second space, the two say the same of a set v: an open set lies in the
// second space, so it is open exactly when it lies in the image and has
// an open preimage, which is membership in the quotient topology. No
// axiom enters.
var QuotientMapIff = quotientMapIffThm{family.Add(registry.ProofEntry{
	Name: "QuotientMapIff",
	Key:  "prop_6e8bffff2e64e3e7",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
		"    quotient_map(T, S, f) ⇔ image(f, ⋃T) = ⋃S ∧ S = quotient_topology(T, f)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Iff()

			a.Forward(
				"a quotient map is onto, and the open sets of the second space are those of the quotient topology",
				func(b *Argument, quotient Fact) {
					onto := QuotientOnto.Read(quotient).AsFact()
					b.Do(SplitConj(
						Case(
							"f is onto the second space",
							By(onto)),
						Case(
							"a set is open in the second space exactly when it lies there, in the image, with an open preimage",
							Simp(Fwd(set_basic.Extension)),
							Simp(Fwd(QuotientTopologyDef)),
							onto.Rw(),
							By(QuotientOpenIff.Read(quotient), set_order.MemberSubsetUnions)),
					))
				})

			a.Backward(
				"an onto map whose second topology is its quotient topology is a quotient map",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"f is onto the second space",
						"and the second topology is the quotient topology")
					onto, topology := parts[0], parts[1]
					b.Show(
						"f is a quotient map",
						QuotientMap.Intro(
							Case(
								"f is onto the second space",
								By(onto)),
							Case(
								"a subset v of the second space is open exactly when it is in the quotient topology",
								Derive(func(c *Argument) {
									c.FixAs[Set[B]]("v")
									vIn := c.Assume()
									c.Show(
										"v lies in the image, so membership asks only an open preimage",
										topology.Rw(),
										Simp(Fwd(QuotientTopologyDef)),
										By(Normalized, onto, vIn))
								})),
						))
				})
		}),
})}

// QuotientTopologyQuotientMap — a map is a quotient map onto its
// quotient topology. The quotient topology is the topology coinduced on
// the image of the space, whose points are that image; so the map is onto
// them, and the quotient topology is its own quotient topology.
var QuotientTopologyQuotientMap = quotientTopologyQuotientMapThm{family.Add(registry.ProofEntry{
	Name: "QuotientTopologyQuotientMap",
	Key:  "prop_6f9a6e30f96ffde2",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "quotient_map(T, quotient_topology(T, f), f)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			f *Arrow[A, B],
			topology topological_space.IsTopologyFact[on.T],
		) {
			points := a.Have(
				"the points of the quotient topology are the image "+
					"of the space, as of the topology it coinduces there",
				"⋃quotient_topology(T, f) = image(f, ⋃T)",
				Simp(Fwd(QuotientTopologyCoinduced)),
				By(topological_space.CoinducedSpace, topology, set_order.SubsetRefl))
			a.Show(
				"f is onto those points, and the quotient topology is its own quotient topology",
				By(Normalized, points, QuotientMapIff.At(T, a.TermAs[Set[Set[B]]]("quotient_topology(T, f)"), f)))
		}),
})}
