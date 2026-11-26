// topology_category.go — topologies on subsets of one host type as a
// category assembled from its hom data, and that category seen from the
// category of sets: the forgetful functor, which keeps each space's points
// and each map, and the isomorphisms, which are the homeomorphisms.

package topology_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/category/set_category"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The category
// ---------------------------------------------------------------------------

// TopologyCategoryDef — topologies on subsets of one ambient type, with
// normalized continuous maps as morphisms, assembled from their hom sets.
var TopologyCategoryDef = topologyCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyCategoryDef",
	Key:   "prop_55cd413a35c9c5ca",
	Const: "topology_category",
	Type:  "category_ops(set(set(M)), morphism_triple(set(set(M)), M → M))",
	Equations: []string{
		"topology_category = " +
			"category_from_hom({T:set(set(M)) | is_topology(T)}, " +
			"    λT:set(set(M)). λS:set(set(M)). continuous_hom_set(T, S), " +
			"    λT:set(set(M)). normalize_on(⋃T, junk, identity_map), " +
			"    λT:set(set(M)). λS:set(set(M)). λR:set(set(M)). λg:(M → M). λf:(M → M). " +
			"        normalize_on(⋃T, junk, g ∘ f))",
	},
	Reading: "There is one category per ambient type M. Its objects are topologies on subsets " +
		"of M; a morphism from T to S is a continuous map with the fixed value junk outside ⋃T.",
})}

// TopologyCategory — topologies on subsets of a type form a category:
// continuous hom sets contain normalized identities and composites, and
// the unit and associative laws follow by equality on the source space.
var TopologyCategory = topologyCategoryThm{family.Add(registry.ProofEntry{
	Name: "TopologyCategory",
	Key:  "prop_98f644ef151b92a3",
	Build: family.Theorem("category(topology_category⟨M:A⟩)",
		func(a *Argument) {
			a.Do(Unfold(TopologyCategoryDef))
			junk := a.TermAs[A]("junk")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			inner := functions.NormalizeOnComposeInner.Inst(
				TypeBinder.BindA[A](), TypeBinder.BindB[A](), TypeBinder.BindC[A]())
			identities := a.Have(
				"normalized identities are continuous endomorphisms",
				"∀T:set(set(A)). normalize_on(⋃T, junk, identity_map) ∈ continuous_hom_set(T, T)",
				Cite(continuous.HomSetIdentity))
			composites := a.Have(
				"normalized composites belong to their continuous hom sets",
				Statement{
					Binders: "∀T S R:set(set(A)). ∀f g:(A → A).",
					Hypotheses: []string{
						"f ∈ continuous_hom_set(T, S)",
						"g ∈ continuous_hom_set(S, R)",
					},
					Conclusion: "normalize_on(⋃T, junk, g ∘ f) ∈ continuous_hom_set(T, R)",
				},
				Cite(
					continuous.HomSetCompose.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A](), TypeBinder.BindC[A]())))
			leftUnit := a.Have(
				"the target identity is a left unit",
				Statement{
					Binders: "∀T S:set(set(A)). ∀f:(A → A).",
					Hypotheses: []string{
						"f ∈ continuous_hom_set(T, S)",
					},
					Conclusion: "normalize_on(⋃T, junk, normalize_on(⋃S, junk, identity_map) ∘ f) = f",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("T")
					b.FixAs[Set[Set[A]]]("S")
					b.FixAs[Fun[A, A]]("f")
					morphism := b.Assume()
					membership := b.Unfolded(morphism, continuous.ContinuousHomSetDef)
					normalized := b.TermAs[Fun[A, A]]("normalize_on(⋃T, junk, f)")
					b.Show(
						"the composite agrees with the normalized representative",
						CalcEq(
							Leg(
								normalized.Core(),
								"compare the maps on their source space",
								Simp(Fwd(functions.NormalizeOnEqIff), Fwd(functions.ComposeApply), Fwd(functions.IdentityApply)),
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inSource := c.Assume()
									continuousMap := c.Have(
										"the representative is continuous",
										"continuous_map(T, S, f)",
										BySets(membership))
									imageIn := c.Have(
										"the image lies in the target space",
										"f(x) ∈ ⋃S",
										By(inSource, continuous.MapsInto.Read(continuousMap).At(x)))
									c.Show(
										"the normalized target identity fixes the image",
										By(
											imageIn,
											functions.NormalizeOnIn.At(c.TermAs[Set[A]]("⋃S"), junk, identity, c.TermAs[A]("f(x)"))))
								})),
							FinalLeg(
								"the representative is already normalized",
								BySets(membership))))
				}))
			rightUnit := a.Have(
				"the source identity is a right unit",
				Statement{
					Binders: "∀T S:set(set(A)). ∀f:(A → A).",
					Hypotheses: []string{
						"f ∈ continuous_hom_set(T, S)",
					},
					Conclusion: "normalize_on(⋃T, junk, f ∘ normalize_on(⋃T, junk, identity_map)) = f",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("T")
					b.FixAs[Set[Set[A]]]("S")
					b.FixAs[Fun[A, A]]("f")
					morphism := b.Assume()
					b.Do(Simp(Fwd(inner), Fwd(functions.ComposeApply), Fwd(functions.IdentityApply)))
					membership := b.Unfolded(morphism, continuous.ContinuousHomSetDef)
					b.Show(
						"inner normalization leaves the normalized representative unchanged",
						BySets(membership))
				}))
			associativity := a.Have(
				"normalized composition is associative",
				Statement{
					Binders: "∀T S R V:set(set(A)). ∀f g h:(A → A).",
					Hypotheses: []string{
						"f ∈ continuous_hom_set(T, S)",
						"g ∈ continuous_hom_set(S, R)",
						"h ∈ continuous_hom_set(R, V)",
					},
					Conclusion: "normalize_on(⋃T, junk, h ∘ normalize_on(⋃T, junk, g ∘ f)) = " +
						"normalize_on(⋃T, junk, normalize_on(⋃S, junk, h ∘ g) ∘ f)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("T")
					b.FixAs[Set[Set[A]]]("S")
					b.FixAs[Set[Set[A]]]("R")
					b.FixAs[Set[Set[A]]]("V")
					b.FixAs[Fun[A, A]]("f")
					b.FixAs[Fun[A, A]]("g")
					b.FixAs[Fun[A, A]]("h")
					morphisms := b.Assume()
					b.Do(Simp(Fwd(inner), Fwd(functions.NormalizeOnEqIff), Fwd(functions.ComposeApply)))
					x := b.FixAs[A]("x")
					inSource := b.Assume()
					membership := b.Unfolded(morphisms, continuous.ContinuousHomSetDef)
					continuousMap := b.Have(
						"the first representative is continuous",
						"continuous_map(T, S, f)",
						BySets(membership))
					imageIn := b.Have(
						"the first image lies in the middle space",
						"f(x) ∈ ⋃S",
						By(inSource, continuous.MapsInto.Read(continuousMap).At(x)))
					b.Show(
						"both parenthesizations have value h applied to g applied to f at x",
						By(
							imageIn,
							functions.NormalizeOnIn.At(b.TermAs[Set[A]]("⋃S"), junk,
								b.TermAs[Fun[A, A]]("λu:A. h(g(u))"), b.TermAs[A]("f(x)"))))
				}))
			objects := a.TermAs[Set[Set[Set[A]]]]("{T:set(set(A)) | is_topology(T)}")
			hom := a.TermAs[Fun[Set[Set[A]], Fun[Set[Set[A]], Set[Fun[A, A]]]]](
				"λT:set(set(A)). λS:set(set(A)). continuous_hom_set(T, S)")
			units := a.TermAs[Fun[Set[Set[A]], Fun[A, A]]](
				"λT:set(set(A)). normalize_on(⋃T, junk, identity_map)")
			compose := a.TermAs[Fun[Set[Set[A]], Fun[Set[Set[A]], Fun3[Set[Set[A]], Fun[A, A], Fun[A, A], Fun[A, A]]]]](
				"λT:set(set(A)). λS:set(set(A)). λR:set(set(A)). λg:(A → A). λf:(A → A). " +
					"    normalize_on(⋃T, junk, g ∘ f)")
			a.Show(
				"the five hom-data laws assemble the topology category",
				By(
					rightUnit,
					leftUnit,
					composites,
					associativity,
					identities,
					category.CategoryFromHom.At(objects, hom, units, compose)))
		}),
})}

// ---------------------------------------------------------------------------
// Underlying sets and isomorphisms
// ---------------------------------------------------------------------------

// TopologyForgetfulDef — forget the open sets and retain each topology's
// carrier and each continuous morphism's normalized underlying map.
var TopologyForgetfulDef = topologyForgetfulDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyForgetfulDef",
	Key:   "prop_45dfd737b39bd6eb",
	Const: "topology_forgetful",
	Type: "functor_ops(set(set(M)), " +
		"    morphism_triple(set(set(M)), M → M), " +
		"    set(M), " +
		"    morphism_triple(set(M), M → M))",
	Equations: []string{
		"topology_forgetful = " +
			"mk_functor(λT:set(set(M)). ⋃T, " +
			"    λt:morphism_triple(set(set(M)), M → M). mk_morphism(⋃t.source, ⋃t.target, t.map))",
	},
})}

// TopologyForgetful — taking underlying carriers and maps is a functor
// from the topology category to the set category: by the hom-data
// criterion, every carrier is a set; a continuous map carries its source
// carrier into its target carrier and is normalized on the source, so
// framed by the two carriers it is a map of sets; and the two categories
// normalize identities and composites on the source carrier alike.
var TopologyForgetful = topologyForgetfulThm{family.Add(registry.ProofEntry{
	Name: "TopologyForgetful",
	Key:  "prop_76d592eaca2c5b16",
	Build: family.Theorem("functor(topology_category⟨M:A⟩, set_category⟨M:A⟩, topology_forgetful⟨M:A⟩)",
		func(a *Argument) {
			arrows := a.Have(
				"a continuous map framed by the two carriers is a map of sets",
				Statement{
					Binders: "∀T S:set(set(A)). ∀f:(A → A).",
					Hypotheses: []string{
						"f ∈ continuous_hom_set(T, S)",
					},
					Conclusion: "mk_morphism(⋃T, ⋃S, f) ∈ category_hom(set_category⟨M:A⟩, ⋃T, ⋃S)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("T")
					b.FixAs[Set[Set[A]]]("S")
					b.FixAs[Fun[A, A]]("f")
					morphism := b.Assume()
					membership := b.Unfolded(morphism, continuous.ContinuousHomSetDef)
					continuousMap := b.Have(
						"the representative is continuous",
						"continuous_map(T, S, f)",
						BySets(membership))
					b.Show(
						"the carriers are sets, and f carries the first into the second and is normalized on it",
						Simp(Fwd(set_category.SetCategoryDef), Fwd(category.CategoryFromHomHomIff)),
						BySets(membership, continuous.MapsInto.Read(continuousMap)))
				}))
			// IdentityApply reads identity_map as λx. x, the set category's
			// spelling of the identity. The two categories then normalize an
			// identity and a composite on the source carrier by the same term,
			// so the criterion's identity and composition clauses hold as they
			// are computed, with no premise.
			topologyIsCategory := a.Simplified(
				TopologyCategory.Inst[A](),
				Fwd(TopologyCategoryDef),
				Fwd(functions.IdentityApply))
			a.Do(Simp(Fwd(TopologyForgetfulDef), Fwd(TopologyCategoryDef), Fwd(functions.IdentityApply)))
			objects := a.TermAs[Set[Set[Set[A]]]]("{T:set(set(A)) | is_topology(T)}")
			hom := a.TermAs[Fun[Set[Set[A]], Fun[Set[Set[A]], Set[Fun[A, A]]]]](
				"λT:set(set(A)). λS:set(set(A)). continuous_hom_set(T, S)")
			units := a.TermAs[Fun[Set[Set[A]], Fun[A, A]]]("λT:set(set(A)). normalize_on(⋃T, junk, λx:A. x)")
			compose := a.TermAs[Fun[Set[Set[A]], Fun[Set[Set[A]], Fun3[Set[Set[A]], Fun[A, A], Fun[A, A], Fun[A, A]]]]](
				"λT:set(set(A)). λS:set(set(A)). λR:set(set(A)). λg:(A → A). λf:(A → A). " +
					"    normalize_on(⋃T, junk, g ∘ f)")
			setCategory := a.TermAs[category.CategoryOps[Set[A], category.MorphismTriple[Set[A], Fun[A, A]]]](
				"set_category⟨M:A⟩")
			carrier := a.TermAs[Fun[Set[Set[A]], Set[A]]]("λT:set(set(A)). ⋃T")
			framing := a.TermAs[Fun3[Set[Set[A]], Set[Set[A]], Fun[A, A], category.MorphismTriple[Set[A], Fun[A, A]]]](
				"λT:set(set(A)). λS:set(set(A)). λf:(A → A). mk_morphism(⋃T, ⋃S, f)")
			a.Show(
				"carriers are sets, continuous maps frame maps of sets, and identities and composites agree",
				By(
					topologyIsCategory,
					set_category.SetCategory.Inst[A](),
					set_basic.InUniv,
					arrows,
					category.FunctorFromHomIff.At(objects, hom, units, compose, setCategory, carrier, framing)))
		}),
})}

// TopologyIsomorphismIff — a framed map mk_morphism(T, S, f) is an
// isomorphism of the topology category exactly when T and S are
// topologies, f is normalized on the source space and f is a
// homeomorphism: the two composite equations of inverse data are the
// inverse laws on the two spaces, and the continuous inverse of a
// homeomorphism, normalized on the target space, supplies inverse data.
var TopologyIsomorphismIff = topologyIsomorphismIffThm{family.Add(registry.ProofEntry{
	Name: "TopologyIsomorphismIff",
	Key:  "prop_8b4206443386cbef",
	Build: family.Theorem("∀T S:set(set(A)). ∀f:(A → A). "+
		"    category_isomorphism(topology_category⟨M:A⟩, mk_morphism(T, S, f)) ⇔ "+
		"    is_topology(T) ∧ is_topology(S) ∧ normalize_on(⋃T, junk, f) = f ∧ homeomorphic_map(T, S, f)",
		func(a *Argument, T, S *Expr[Set[Set[A]]], f *Arrow[A, A]) {
			a.Do(Simp(Fwd(TopologyCategoryDef), Fwd(category.CategoryFromHomIsomorphismIff)))
			a.Iff()
			a.Forward(
				"inverse data make f a normalized homeomorphism between topologies",
				func(b *Argument, isomorphism Fact) {
					parts := b.Conjuncts(
						isomorphism,
						"the source is a topology",
						"the target is a topology",
						"f belongs to its continuous hom set",
						"inverse data exist")
					g, inverse := b.UnpackAs[Fun[A, A]](parts[3], "g")
					inverseOnSpaces := b.Simplified(
						inverse,
						Fwd(functions.NormalizeOnEqIff),
						Fwd(functions.ComposeApply),
						Fwd(functions.IdentityApply))
					laws := b.Conjuncts(
						inverseOnSpaces,
						"g belongs to the continuous hom set back",
						"g undoes f on the source space",
						"f undoes g on the target space")
					fMorphism := b.Unfolded(parts[2], continuous.ContinuousHomSetDef)
					gMorphism := b.Unfolded(laws[0], continuous.ContinuousHomSetDef)
					gContinuous := b.Have(
						"g is continuous",
						"continuous_map(S, T, g)",
						BySets(gMorphism))
					homeomorphism := b.Have(
						"g is a continuous inverse of f, so f is a homeomorphism",
						"homeomorphic_map(T, S, f)",
						Unfold(continuous.HomeomorphicMap),
						SplitConj(
							Case(
								"f is continuous",
								BySets(fMorphism)),
							Case(
								"g is continuous and undoes f on both spaces",
								Witness(g),
								By(gContinuous, laws[1], laws[2])),
						))
					b.Show(
						"the ends are topologies, the representative f is normalized, and f is a homeomorphism",
						BySets(parts[0], parts[1], fMorphism, homeomorphism))
				})
			a.Backward(
				"normalize the continuous inverse of the homeomorphism",
				func(b *Argument, normalizedHomeomorphism Fact) {
					parts := b.Conjuncts(
						normalizedHomeomorphism,
						"the source is a topology",
						"the target is a topology",
						"f is normalized on the source space",
						"f is a homeomorphism")
					fContinuous := continuous.HomeomorphismContinuous.Read(parts[3])
					g, inverse := b.UnpackAs[Fun[A, A]](continuous.HomeomorphismInverseMaps.Read(parts[3]), "g")
					laws := b.Conjuncts(
						inverse,
						"g is continuous",
						"g undoes f on the source space",
						"f undoes g on the target space")
					b.Do(SplitConj(
						Case(
							"the ends are objects and f is a continuous hom-set representative",
							By(
								Normalized,
								parts[0],
								parts[1],
								parts[2],
								fContinuous,
								continuous.NormalizeHomSetIff.At(T, S, f))),
						Case(
							"the normalized inverse supplies inverse data",
							Derive(func(c *Argument) {
								junk := c.TermAs[A]("junk")
								target := c.TermAs[Set[A]]("⋃S")
								c.Take(c.TermAs[Fun[A, A]]("normalize_on(⋃S, junk, g)"))
								c.Do(SplitConjAll(
									Case(
										"the normalized inverse is a continuous hom-set representative from S to T",
										By(laws[0], continuous.NormalizeHomSetIff.At(S, T, g))),
									Case(
										"the normalized inverse after f gives the source identity",
										Derive(func(d *Argument) {
											d.Do(Simp(
												Fwd(functions.NormalizeOnEqIff),
												Fwd(functions.ComposeApply),
												Fwd(functions.IdentityApply)))
											x := d.FixAs[A]("x")
											inSource := d.Assume()
											d.Show(
												"f carries x into the target space, where normalization keeps g",
												By(
													Normalized,
													inSource,
													laws[1].At(x),
													continuous.MapsInto.Read(fContinuous).At(x),
													functions.NormalizeOnIn.At(target, junk, g, f.Apply(x))))
										})),
									Case(
										"f after the normalized inverse gives the target identity",
										Derive(func(d *Argument) {
											d.Do(Simp(
												Fwd(functions.NormalizeOnEqIff),
												Fwd(functions.ComposeApply),
												Fwd(functions.IdentityApply)))
											y := d.FixAs[A]("y")
											inTarget := d.Assume()
											d.Show(
												"normalization keeps g at a point of the target space",
												By(Normalized, inTarget, laws[2].At(y), functions.NormalizeOnIn.At(target, junk, g, y)))
										})),
								))
							})),
					))
				})
		}),
})}

// TopologyIsomorphicIff — T and S are isomorphic in the topology
// category exactly when both are topologies and their spaces are
// homeomorphic: an isomorphism from T to S is its own map framed by T and
// S, and that map is a homeomorphism; conversely the representative of a
// homeomorphism normalized on the source space agrees with it there, so it
// is a homeomorphism too, and framed by T and S it is an isomorphism
// between them.
var TopologyIsomorphicIff = topologyIsomorphicIffThm{family.Add(registry.ProofEntry{
	Name: "TopologyIsomorphicIff",
	Key:  "prop_846e58611ad75b1a",
	Build: family.Theorem("∀T S:set(set(A)). "+
		"    category_isomorphic(topology_category⟨M:A⟩, T, S) ⇔ "+
		"    is_topology(T) ∧ is_topology(S) ∧ homeomorphic(T, S)",
		func(a *Argument, T, S *Expr[Set[Set[A]]]) {
			a.Do(Unfold(category.CategoryIsomorphicDef))
			a.Iff()
			a.Forward(
				"the map of an isomorphism from T to S is a homeomorphism",
				func(b *Argument, isomorphic Fact) {
					_, isomorphism := b.UnpackAs[category.MorphismTriple[Set[Set[A]], Fun[A, A]]](isomorphic, "m")
					parts := b.Conjuncts(
						isomorphism,
						"m is a morphism from T to S",
						"m is an isomorphism")
					frame := b.Have(
						"m runs from T to S",
						"m.source = T ∧ m.target = S",
						BySets(b.Unfolded(parts[0], category.CategoryHomDef)))
					framedByEnds := b.Have(
						"so m is its map framed by T and S",
						"m = mk_morphism(T, S, m.map)",
						Simp(category.MorphismTripleData.Parts),
						By(Normalized, frame))
					mMap := b.TermAs[Fun[A, A]]("m.map")
					characterized := b.Have(
						"the framed map of an isomorphism is a homeomorphism between topologies",
						"is_topology(T) ∧ is_topology(S) ∧ homeomorphic_map(T, S, m.map)",
						By(Normalized, framedByEnds, parts[1], TopologyIsomorphismIff.At(T, S, mMap)))
					homeomorphic := b.Have(
						"the map of m makes T and S homeomorphic",
						"homeomorphic(T, S)",
						Simp(Fwd(continuous.HomeomorphicDef)),
						Witness(mMap),
						By(characterized))
					b.Show(
						"T and S are homeomorphic topologies",
						By(characterized, homeomorphic))
				})
			a.Backward(
				"frame the normalized representative of a homeomorphism",
				func(b *Argument, homeomorphicTopologies Fact) {
					parts := b.Conjuncts(
						homeomorphicTopologies,
						"T is a topology",
						"S is a topology",
						"T and S are homeomorphic")
					f, homeomorphism := b.UnpackAs[Fun[A, A]](b.Unfolded(parts[2], continuous.HomeomorphicDef), "f")
					junk := b.TermAs[A]("junk")
					source := b.TermAs[Set[A]]("⋃T")
					representative := b.TermAs[Fun[A, A]]("normalize_on(⋃T, junk, f)")
					agree := b.Have(
						"the representative agrees with f on the source space",
						"∀x:A. x ∈ ⋃T ⇒ f(x) = normalize_on(⋃T, junk, f, x)",
						By(functions.NormalizeOnIn))
					representativeHomeomorphism := b.Have(
						"so the representative is a homeomorphism",
						"homeomorphic_map(T, S, normalize_on(⋃T, junk, f))",
						By(agree, continuous.HomeomorphismEq.Read(homeomorphism).At(representative)))
					b.Take(b.TermAs[category.MorphismTriple[Set[Set[A]], Fun[A, A]]](
						"mk_morphism(T, S, normalize_on(⋃T, junk, f))"))
					b.Do(SplitConj(
						Case(
							"the framed representative is a morphism from T to S",
							Simp(Fwd(TopologyCategoryDef), Fwd(category.CategoryFromHomHomIff)),
							BySets(
								parts[0],
								parts[1],
								continuous.HomeomorphismContinuous.Read(homeomorphism),
								continuous.NormalizeHomSetIff.At(T, S, f))),
						Case(
							"the framed representative is an isomorphism",
							By(
								parts[0],
								parts[1],
								representativeHomeomorphism,
								functions.NormalizeOnIdempotent.At(source, junk, f),
								TopologyIsomorphismIff.At(T, S, representative))),
					))
				})
		}),
})}
