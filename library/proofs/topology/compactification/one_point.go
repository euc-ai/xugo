// one_point.go — the one-point compactification of a space, carried on the
// optional values with none the new point. Its open sets are of two kinds,
// the images of open sets of the space and the new point with the image of
// the space less a closed compact set, and its space is the space with the
// new point added. A set v of optional values is read through its trace on
// the space, {x | some(x) ∈ v}, the points the space carries into it: v is
// open exactly when its trace is open and, when v holds the new point, the
// complement of the trace is compact — so the trace of an open set is
// open. Through that reading the open sets form a topology, some is
// continuous, and the compactification is compact; the space sits in it as
// an open subspace; it is Hausdorff exactly when the space is Hausdorff
// and locally compact; and the space is dense in it exactly when the space
// is not compact.

package compactification

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OnePointImageOpen — the image under some of an open set of the space is
// open in the one-point compactification: the first kind of open set.
var OnePointImageOpen = onePointImageOpenThm{family.Add(registry.ProofEntry{
	Name: "OnePointImageOpen",
	Key:  "prop_a914e61242860405",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀u:set(A).",
		Hypotheses: []string{
			"u ∈ T",
		},
		Conclusion: "image(some, u) ∈ one_point_compactification(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], u *Expr[Set[A]], open Fact) {
			a.Show(
				"the image of an open set is the first kind of open set",
				Simp(Fwd(OnePointCompactificationDef)),
				By(open))
		}),
})}

// OnePointComplementOpen — the new point with the image of the space less
// a closed compact set k is open in the one-point compactification: the
// second kind of open set, a neighbourhood of the new point.
var OnePointComplementOpen = onePointComplementOpenThm{family.Add(registry.ProofEntry{
	Name: "OnePointComplementOpen",
	Key:  "prop_87a0c00b0c1961cc",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k:set(A).",
		Hypotheses: []string{
			"closed_in(T, k)",
			"compact_in(T, k)",
		},
		Conclusion: "insert(none, image(some, ⋃T ∖ k)) ∈ one_point_compactification(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k *Expr[Set[A]], closed, compactK Fact) {
			a.Show(
				"the complement of a closed compact set, with the new point, is the second kind of open set",
				Simp(Fwd(OnePointCompactificationDef)),
				By(closed, compactK))
		}),
})}

// OnePointSpace — the one-point compactification lives on the space with
// the new point added. Every open set lies there: the image of an open set
// of T lies in the image of the space, and so does the image of the space
// less a closed set; and the whole of it is open, being the complement of
// the empty set, which is closed and compact.
var OnePointSpace = onePointSpaceThm{family.Add(registry.ProofEntry{
	Name: "OnePointSpace",
	Key:  "prop_36e4694fd248ecca",
	Build: topological_space.IsTopology.Law(
		"⋃one_point_compactification(T) = insert(none, image(some, ⋃T))",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			within := a.Have(
				"every open set lies in the space with the new point added",
				"∀v:set(option(A)). v ∈ one_point_compactification(T) ⇒ v ⊆ insert(none, image(some, ⋃T))",
				Derive(func(b *Argument) {
					b.FixAs[Set[option.Option[A]]]("v")
					kinds := b.Unfolded(b.Assume(), OnePointCompactificationDef)
					b.Show(
						"v is of one of the two kinds of open set",
						kinds.SplitDisj(
							LeftHolds(
								"the image of an open set lies in the image of the space",
								Given(func(c *Argument, image Fact) {
									c.Show(
										"so v lies in the space with the new point",
										BySets(image))
								})),
							RightHolds(
								"the new point with the image of the space less a closed set lies there too",
								Given(func(c *Argument, complement Fact) {
									c.Show(
										"so v lies in the space with the new point",
										BySets(complement))
								}))))
				}))
			whole := a.Have(
				"the space with the new point added is open, the complement of the closed compact empty set",
				"insert(none, image(some, ⋃T)) ∈ one_point_compactification(T)",
				By(
					Normalized,
					topological_space.EmptyClosed.Read(topology),
					compact.EmptyCompact,
					set_algebra.DiffEmpty,
					OnePointComplementOpen))
			a.Show(
				"the open sets unite to exactly that set",
				By(within, whole, set_order.SubsetAntisym, set_order.UnionsSubset, set_order.MemberSubsetUnions))
		}),
})}

// OnePointPreimageOpen — an open set of the one-point compactification
// pulls back along some to an open set of the space. The image of an open
// set u pulls back to u, some being one-to-one; the new point with the
// image of the space less a closed set k pulls back to the space less k,
// the new point being no value of some, and that is open as k is closed.
// Neither kind asks anything of the topology's axioms.
var OnePointPreimageOpen = onePointPreimageOpenThm{family.Add(registry.ProofEntry{
	Name: "OnePointPreimageOpen",
	Key:  "prop_618e401f523fcf4c",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀v:set(option(A)).",
		Hypotheses: []string{
			"v ∈ one_point_compactification(T)",
		},
		Conclusion: "{x:A | some(x) ∈ v} ∈ T",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], v *Expr[Set[option.Option[A]]], open Fact) {
			kinds := a.Unfolded(open, OnePointCompactificationDef)
			a.Show(
				"v is of one of the two kinds of open set",
				kinds.SplitDisj(
					LeftHolds(
						"v is the image of an open set u",
						Given(func(b *Argument, image Fact) {
							_, at := b.UnpackAs[Set[A]](image, "u")
							parts := b.Conjuncts(
								at,
								"u is open",
								"v is the image of u")
							same := b.Have(
								"some is one-to-one, so v pulls back to u",
								"{x:A | some(x) ∈ v} = u",
								BySets(parts[1], option.SomeInjective))
							b.Show(
								"which is open",
								By(same, parts[0]))
						})),
					RightHolds(
						"v is the new point with the image of the space less a closed compact set k",
						Given(func(b *Argument, complement Fact) {
							_, at := b.UnpackAs[Set[A]](complement, "k")
							parts := b.Conjuncts(
								at,
								"k is closed",
								"k is compact",
								"v is the new point with the image of the space less k")
							same := b.Have(
								"the new point is no value of some, so v pulls back to the space less k",
								"{x:A | some(x) ∈ v} = ⋃T ∖ k",
								parts[2].Rw(),
								BySets(option.SomeInjective, option.NoneNotSome))
							b.Show(
								"which is open, k being closed",
								By(same, parts[0], topological_space.ClosedInDef))
						}))))
		}),
})}

// OnePointOpenIff — the open sets of the one-point compactification read
// through their traces on the space: a set v of optional values is open
// exactly when the points the space carries into it form an open set,
// whose complement in the space is compact when v holds the new point.
// Forward, the trace is open (OnePointPreimageOpen); when v holds the new
// point it is the new point with the image of the space less a closed
// compact k, and the complement of its trace, closed as the complement of
// an open set, lies in k and so is compact. Backward, every optional value
// is none or some value, so v is the image of its trace or the new point
// with that image; the trace is the space less its complement, which is
// closed, and compact when v holds the new point.
var OnePointOpenIff = onePointOpenIffThm{family.Add(registry.ProofEntry{
	Name: "OnePointOpenIff",
	Key:  "prop_5c8df89e8193fa03",
	Build: family.Theorem(
		"∀T:set(set(A)). ∀v:set(option(A)). "+
			"    v ∈ one_point_compactification(T) ⇔ "+
			"    {x:A | some(x) ∈ v} ∈ T ∧ (none ∈ v ⇒ compact_in(T, ⋃T ∖ {x:A | some(x) ∈ v}))",
		func(a *Argument, T *Expr[Set[Set[A]]], v *Expr[Set[option.Option[A]]]) {
			trace := a.TermAs[Set[A]]("{x:A | some(x) ∈ v}")
			a.Iff()
			a.Forward(
				"an open set has an open trace, whose complement is compact when the set holds the new point",
				func(b *Argument, open Fact) {
					traceOpen := b.Have(
						"the trace of v is open",
						"{x:A | some(x) ∈ v} ∈ T",
						By(open, OnePointPreimageOpen))
					compactness := b.Have(
						"when v holds the new point, the complement of its trace is compact",
						"none ∈ v ⇒ compact_in(T, ⋃T ∖ {x:A | some(x) ∈ v})",
						Derive(func(c *Argument) {
							noneIn := c.Assume()
							kinds := c.Unfolded(open, OnePointCompactificationDef)
							c.Show(
								"v is of one of the two kinds of open set",
								kinds.SplitDisj(
									LeftHolds(
										"an image under some does not hold the new point",
										Given(func(d *Argument, image Fact) {
											d.Show(
												"so v is not of this kind",
												BySets(image, noneIn, option.NoneNotSome))
										})),
									RightHolds(
										"v is the new point with the image of the space less a closed compact set k",
										Given(func(d *Argument, complement Fact) {
											_, at := d.UnpackAs[Set[A]](complement, "k")
											parts := d.Conjuncts(
												at,
												"k is closed",
												"k is compact",
												"v is the new point with the image of the space less k")
											within := d.Have(
												"a point of the space outside k is carried into v, so the complement of the trace lies in k",
												"⋃T ∖ {x:A | some(x) ∈ v} ⊆ k",
												BySets(parts[2]))
											closed := d.Have(
												"the complement of the open trace is closed",
												"closed_in(T, ⋃T ∖ {x:A | some(x) ∈ v})",
												By(traceOpen, topological_space.OpenClosedComplement.At(T, trace)))
											d.Show(
												"a closed part of the compact k is compact",
												By(closed, parts[1], within, compact.ClosedSubsetCompact))
										}))))
						}))
					b.Show(
						"so v has both properties",
						By(traceOpen, compactness))
				})
			a.Backward(
				"a set with an open trace, whose complement is compact when the set holds the new point, is open",
				func(b *Argument, traced Fact) {
					parts := b.Conjuncts(
						traced,
						"the trace of v is open",
						"its complement is compact when v holds the new point")
					cases := b.Have(
						"every optional value is none or some value",
						"∀z:option(A). z = none ∨ (∃x:A. z = some(x))",
						By(option.Cases.Inst[A]()))
					b.Cases(b.Term("none ∈ v"))
					b.When(
						"v holds the new point",
						func(c *Argument, noneIn Fact) {
							_, kDef := c.LetAs[Set[A]]("k", "⋃T ∖ {x:A | some(x) ∈ v}")
							closed := c.Have(
								"k is closed, the complement of the open trace",
								"closed_in(T, k)",
								By(kDef, parts[0], topological_space.OpenClosedComplement.At(T, trace)))
							whole := c.Have(
								"v is the new point with the image of the space less k, its trace",
								"v = insert(none, image(some, ⋃T ∖ k))",
								BySets(cases, kDef, parts[0], noneIn))
							c.Show(
								"so v is open, k being closed and compact",
								By(Normalized, whole, closed, noneIn, parts[1], OnePointComplementOpen))
						})
					b.Otherwise(
						"v does not hold the new point",
						func(c *Argument, noneOut Fact) {
							image := c.Have(
								"v is the image of its trace",
								"v = image(some, {x:A | some(x) ∈ v})",
								BySets(noneOut, cases))
							c.Show(
								"so v is open, its trace being open",
								By(image, parts[0], OnePointImageOpen))
						})
				})
		}),
})}

// OnePointTopology — the one-point compactification of a space is a
// space. Read through OnePointOpenIff, both axioms are statements about
// traces. The trace of a meet is the meet of the traces, open, and its
// complement is the union of the two complements, compact when the meet
// holds the new point. The trace of a union is open, each of its points
// lying in the open trace of a member; and when the union holds the new
// point, some member holds it, and the complement of the union's trace —
// closed, the trace being open — lies in the compact complement of that
// member's trace.
var OnePointTopology = onePointTopologyThm{family.Add(registry.ProofEntry{
	Name: "OnePointTopology",
	Key:  "prop_8c348483e826bcc4",
	Build: topological_space.IsTopology.Law(
		"is_topology(one_point_compactification(T))",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			a.Show(
				"the open sets meet and unite to open sets",
				topological_space.IsTopology.Intro(
					Case(
						"two open sets meet in an open set",
						Derive(func(b *Argument) {
							b.FixAs[Set[option.Option[A]]]("u")
							b.FixAs[Set[option.Option[A]]]("v")
							both := b.Conjuncts(
								b.Assume(),
								"u is open",
								"v is open")
							uTrace := b.Conjuncts(
								b.Simplified(both[0], Fwd(OnePointOpenIff)),
								"u has an open trace",
								"whose complement is compact when u holds the new point")
							vTrace := b.Conjuncts(
								b.Simplified(both[1], Fwd(OnePointOpenIff)),
								"v has an open trace",
								"whose complement is compact when v holds the new point")
							meet := b.Have(
								"the trace of the meet is the meet of the traces",
								"{x:A | some(x) ∈ u ∩ v} = {x:A | some(x) ∈ u} ∩ {x:A | some(x) ∈ v}",
								BySets())
							complement := b.Have(
								"its complement is the union of the two complements",
								"⋃T ∖ {x:A | some(x) ∈ u ∩ v} = (⋃T ∖ {x:A | some(x) ∈ u}) ∪ (⋃T ∖ {x:A | some(x) ∈ v})",
								BySets())
							b.Show(
								"so the meet is open",
								Simp(Fwd(OnePointOpenIff)),
								SplitConj(
									Case(
										"its trace is open, a meet of two open sets",
										meet.Rw(),
										By(topological_space.InterOpen.Read(topology), uTrace[0], vTrace[0])),
									Case(
										"its complement is compact when the meet holds the new point, a union of two compact sets",
										Derive(func(c *Argument) {
											noneIn := c.Assume()
											c.Show(
												"both complements are compact",
												complement.Rw(),
												By(noneIn, uTrace[1], vTrace[1], set_basic.InInter, compact.CompactUnion))
										}))))
						})),
					Case(
						"a family of open sets unites to an open set",
						Derive(func(b *Argument) {
							b.FixAs[Set[Set[option.Option[A]]]]("s")
							opens := b.Assume()
							neighbourhoods := b.Have(
								"each point of the trace of the union lies in the open trace of a member, inside it",
								"∀x:A. x ∈ {y:A | some(y) ∈ ⋃s} ⇒ ∃w:set(A). w ∈ T ∧ w ⊆ {y:A | some(y) ∈ ⋃s} ∧ x ∈ w",
								Derive(func(c *Argument) {
									c.FixAs[A]("x")
									xIn := c.Assume()
									_, at := c.ObtainAs[Set[option.Option[A]]](
										"some(x) lies in a member v of s",
										"∃v:set(option(A)). v ∈ s ∧ some(x) ∈ v",
										BySets(xIn))
									c.Take(c.TermAs[Set[A]]("{y:A | some(y) ∈ v}"))
									c.Show(
										"the trace of v is open, holds x and lies in the trace of the union",
										BySets(at, opens, OnePointPreimageOpen))
								}))
							traceOpen := b.Have(
								"so the trace of the union is open",
								"{x:A | some(x) ∈ ⋃s} ∈ T",
								By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
							b.Show(
								"so the union is open",
								Simp(Fwd(OnePointOpenIff)),
								SplitConj(
									Case(
										"its trace is open",
										By(traceOpen)),
									Case(
										"its complement is compact when the union holds the new point",
										Derive(func(c *Argument) {
											noneIn := c.Assume()
											_, at := c.ObtainAs[Set[option.Option[A]]](
												"the new point lies in a member v of s",
												"∃v:set(option(A)). v ∈ s ∧ none ∈ v",
												BySets(noneIn))
											parts := c.Conjuncts(
												at,
												"v is a member of s",
												"v holds the new point")
											vOpen := c.Have(
												"v is open",
												"v ∈ one_point_compactification(T)",
												By(parts[0], opens, set_basic.SubsetDef))
											vCompact := c.Have(
												"the complement of the trace of v is compact",
												"compact_in(T, ⋃T ∖ {x:A | some(x) ∈ v})",
												By(vOpen, parts[1], OnePointOpenIff))
											within := c.Have(
												"the complement of the trace of the union lies in it",
												"⋃T ∖ {x:A | some(x) ∈ ⋃s} ⊆ ⋃T ∖ {x:A | some(x) ∈ v}",
												BySets(parts[0]))
											c.Show(
												"a closed part of a compact set, the complement of an open trace",
												By(
													vCompact,
													traceOpen,
													within,
													compact.ClosedSubsetCompact,
													topological_space.OpenClosedComplement))
										}))))
						})),
				))
		}),
})}

// OnePointSomeContinuous — some carries a space continuously into its
// one-point compactification. A point x of the space lies in an open set
// u, and some(x) in the image of u, which is open; and the preimage of an
// open set, cut to the space, is its trace, which is open
// (OnePointPreimageOpen) and so lies in the space already. The topology's
// axioms are not read.
var OnePointSomeContinuous = onePointSomeContinuousThm{family.Add(registry.ProofEntry{
	Name: "OnePointSomeContinuous",
	Key:  "prop_6e7166d845ccd35b",
	Build: family.Theorem(
		"∀T:set(set(A)). continuous_map(T, one_point_compactification(T), some)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"some is continuous",
				continuous.ContinuousMap.Intro(
					Case(
						"some carries each point of the space into an open set, the image of an open set holding it",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							xIn := b.Assume()
							_, at := b.ObtainAs[Set[A]](
								"x lies in an open set u",
								"∃u:set(A). u ∈ T ∧ x ∈ u",
								BySets(xIn))
							parts := b.Conjuncts(
								at,
								"u is open",
								"x lies in u")
							imageOpen := b.Have(
								"the image of u is open",
								"image(some, u) ∈ one_point_compactification(T)",
								By(parts[0], OnePointImageOpen))
							b.Show(
								"and holds some(x)",
								BySets(parts[1], imageOpen))
						})),
					Case(
						"the preimage of an open set, cut to the space, is its trace, which is open",
						Derive(func(b *Argument) {
							b.FixAs[Set[option.Option[A]]]("v")
							open := b.Assume()
							traceOpen := b.Have(
								"the trace of v is open",
								"{x:A | some(x) ∈ v} ∈ T",
								By(open, OnePointPreimageOpen))
							same := b.Have(
								"so the trace lies in the space, and the preimage cut to the space is the trace",
								"preimage_on(⋃T, some, v) = {x:A | some(x) ∈ v}",
								BySets(traceOpen))
							b.Show(
								"which is open",
								same.Rw(),
								By(traceOpen))
						})),
				))
		}),
})}

// OnePointCompact — the one-point compactification is compact. An open
// cover of its space has a member w holding the new point; the complement
// k of the trace of w is compact (OnePointOpenIff), and so is its image
// under some, some being continuous, so finitely many members of the
// cover cover that image. Those members with w cover the space: the new
// point lies in w, and a point some(x) of the space lies in w unless x is
// in k, when it lies in the image of k.
var OnePointCompact = onePointCompactThm{family.Add(registry.ProofEntry{
	Name: "OnePointCompact",
	Key:  "prop_13434712f9ee9f5b",
	Build: topological_space.IsTopology.Law(
		"compact_in(one_point_compactification(T), ⋃one_point_compactification(T))",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			T := a.TermAs[Set[Set[A]]]("T")
			space := OnePointSpace.Read(topology)
			a.Show(
				"the space lies in itself, and every open cover of it has a finite subcover",
				Simp(Fwd(compact.CompactInDef)),
				SplitConj(
					Case(
						"the space lies in itself",
						By(set_order.SubsetRefl)),
					Case(
						"an open cover of the space has a finite subcover",
						Derive(func(b *Argument) {
							b.FixAs[Set[Set[option.Option[A]]]]("c")
							cover := b.Conjuncts(
								b.Assume(),
								"c consists of open sets",
								"c covers the space")
							w, at := b.ObtainAs[Set[option.Option[A]]](
								"the new point lies in a member w of c",
								"∃w:set(option(A)). w ∈ c ∧ none ∈ w",
								BySets(space, cover[1]))
							member := b.Conjuncts(
								at,
								"w is a member of c",
								"w holds the new point")
							wOpen := b.Have(
								"w is open",
								"w ∈ one_point_compactification(T)",
								By(member[0], cover[0], set_basic.SubsetDef))
							_, kDef := b.LetAs[Set[A]]("k", "⋃T ∖ {x:A | some(x) ∈ w}")
							kCompact := b.Have(
								"k, the complement of the trace of w, is compact",
								"compact_in(T, k)",
								By(kDef, wOpen, member[1], OnePointOpenIff.At(T, w)))
							imageCompact := b.Have(
								"so is its image under the continuous some",
								"compact_in(one_point_compactification(T), image(some, k))",
								By(kCompact, OnePointSomeContinuous, continuous.ImageCompact))
							_, finitely := b.ObtainAs[Set[Set[option.Option[A]]]](
								"finitely many members d of c cover that image, which lies in the space",
								"∃d:set(set(option(A))). d ⊆ c ∧ finite(d) ∧ image(some, k) ⊆ ⋃d",
								By(imageCompact, cover[0], cover[1], compact.CompactInDef, set_order.SubsetTrans))
							subcover := b.Conjuncts(
								finitely,
								"d is part of c",
								"d is finite",
								"d covers the image of k")
							b.Take(b.TermAs[Set[Set[option.Option[A]]]]("insert(w, d)"))
							b.Show(
								"w with d is a finite part of c covering the space",
								SplitConj(
									Case(
										"w with d is a finite part of c",
										By(subcover[1], member[0], subcover[0], set_order.InsertSubset, finite_set.FiniteInsert)),
									Case(
										"the new point lies in w, and some(x) lies in w unless x is in k, when d covers it",
										Simp(Fwd(space), Fwd(set_algebra.UnionsInsert)),
										BySets(kDef, member[1], subcover[2]))))
						}))))
		}),
})}

// OnePointOpenEmbedding — a space sits in its one-point compactification
// as an open subspace. The image of the space under some is open, the
// image of an open set; and some is a homeomorphism onto the subspace on
// that image, being a continuous open injection onto it
// (continuous.HomeomorphismIffOpenBijection): continuous, its values
// lying in the image; open, the image of an open set u being open and its
// own trace on the image of the space; onto, the subspace's points being
// the image, which lies in the space; and one-to-one.
var OnePointOpenEmbedding = onePointOpenEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "OnePointOpenEmbedding",
	Key:  "prop_c24d9a21ca71ad63",
	Build: topological_space.IsTopology.Law(
		"image(some, ⋃T) ∈ one_point_compactification(T) ∧ "+
			"embedding_map(T, one_point_compactification(T), some)",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			imageOpen := a.Have(
				"the image of the space is open, the image of an open set",
				"image(some, ⋃T) ∈ one_point_compactification(T)",
				By(topological_space.SpaceOpen.Read(topology), OnePointImageOpen))
			into := a.Have(
				"some is continuous into the subspace on its image, where its values lie",
				"continuous_map(T, subtopology(one_point_compactification(T), image(some, ⋃T)), some)",
				By(continuous.IntoSubtopology, OnePointSomeContinuous, set_image.FunInImage))
			open := a.Have(
				"some is open into that subspace",
				"open_map(T, subtopology(one_point_compactification(T), image(some, ⋃T)), some)",
				continuous.OpenMap.Intro(Derive(func(b *Argument) {
					b.FixAs[Set[A]]("u")
					uOpen := b.Assume()
					image := b.Have(
						"the image of u is open",
						"image(some, u) ∈ one_point_compactification(T)",
						By(uOpen, OnePointImageOpen))
					trace := b.Have(
						"u lies in the space, so its image is its own trace on the image of the space",
						"image(some, u) = image(some, u) ∩ image(some, ⋃T)",
						BySets(uOpen))
					b.Show(
						"so it is open in the subspace",
						By(trace, image, topological_space.TraceOpen))
				})))
			onto := a.Have(
				"the subspace's points are the image, which lies in the space",
				"image(some, ⋃T) = ⋃subtopology(one_point_compactification(T), image(some, ⋃T))",
				Simp(Fwd(topological_space.SubtopologySpace), Fwd(OnePointSpace.Read(topology))),
				BySets())
			injective := a.Have(
				"some is one-to-one",
				"injective_on(⋃T, some)",
				By(functions.InjectiveOnDef, option.SomeInjective))
			embedding := a.Have(
				"so some is a homeomorphism onto the subspace on its image",
				"embedding_map(T, one_point_compactification(T), some)",
				continuous.EmbeddingMap.Intro(
					By(continuous.HomeomorphismIffOpenBijection, into, open, onto, injective)))
			a.Show(
				"the image is open and some an embedding",
				By(imageOpen, embedding))
		}),
})}

// OnePointHausdorffIff — the one-point compactification of a space is
// Hausdorff exactly when the space is Hausdorff and locally compact.
// Forward, some is a continuous injection into a Hausdorff space, so the
// space is Hausdorff (continuous.HausdorffInjectivePreimage); and for a
// point x of the space, open sets u ∋ some(x) and v ∋ none that are
// disjoint give x the open neighbourhood the trace of u, which misses the
// trace of v and so lies in its complement, compact by OnePointOpenIff.
// Backward, every point of the compactification is the new point or
// some(x) for a point x of the space. A point some(x) is separated from
// the new point by the image of an open u ∋ x inside a compact k and the
// new point with the image of the space less k, open as k is closed in the
// Hausdorff space; two points some(x), some(y) are separated by the images
// of open sets separating x from y, some being one-to-one.
var OnePointHausdorffIff = onePointHausdorffIffThm{family.Add(registry.ProofEntry{
	Name: "OnePointHausdorffIff",
	Key:  "prop_6356e3eda7596232",
	Build: topological_space.IsTopology.Law(
		"hausdorff(one_point_compactification(T)) ⇔ hausdorff(T) ∧ locally_compact_space(T)",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			space := OnePointSpace.Read(topology)
			a.Iff()
			a.Forward(
				"a Hausdorff compactification makes the space Hausdorff and locally compact",
				func(b *Argument, separated Fact) {
					injective := b.Have(
						"some is one-to-one",
						"injective_on(⋃T, some)",
						By(functions.InjectiveOnDef, option.SomeInjective))
					hausdorff := b.Have(
						"the space is Hausdorff, some being a continuous injection into a Hausdorff space",
						"hausdorff(T)",
						By(separated, injective, OnePointSomeContinuous, continuous.HausdorffInjectivePreimage))
					local := b.Have(
						"the space is locally compact",
						"locally_compact_space(T)",
						Simp(Fwd(compact.LocallyCompactSpaceDef)),
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							xIn := c.Assume()
							points := c.Have(
								"some(x) and the new point are points of the compactification",
								"some(x) ∈ ⋃one_point_compactification(T) ∧ none ∈ ⋃one_point_compactification(T)",
								BySets(space, xIn))
							_, _, at := c.Obtain2As[Set[option.Option[A]], Set[option.Option[A]]](
								"they lie in disjoint open sets u and v",
								"∃u v:set(option(A)). "+
									"    u ∈ one_point_compactification(T) ∧ "+
									"    v ∈ one_point_compactification(T) ∧ "+
									"    some(x) ∈ u ∧ "+
									"    none ∈ v ∧ "+
									"    u ∩ v = ∅",
								By(separated, points, topological_space.HausdorffDef, option.NoneNotSome))
							sep := c.Conjuncts(
								at,
								"u is open",
								"v is open",
								"u holds some(x)",
								"v holds the new point",
								"u and v are disjoint")
							uTrace := c.Have(
								"the trace of u is open",
								"{y:A | some(y) ∈ u} ∈ T",
								By(sep[0], OnePointPreimageOpen))
							kCompact := c.Have(
								"the complement of the trace of v is compact",
								"compact_in(T, ⋃T ∖ {y:A | some(y) ∈ v})",
								By(sep[1], sep[3], OnePointOpenIff))
							c.Take(c.TermAs[Set[A]]("{y:A | some(y) ∈ u}"))
							c.Take(c.TermAs[Set[A]]("⋃T ∖ {y:A | some(y) ∈ v}"))
							c.Show(
								"x lies in the open trace of u, which misses the trace of v and so lies in that compact set",
								BySets(sep[4], kCompact, uTrace, sep[2]))
						}))
					b.Show(
						"so the space is Hausdorff and locally compact",
						By(hausdorff, local))
				})
			a.Backward(
				"a Hausdorff, locally compact space has a Hausdorff compactification",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"the space is Hausdorff",
						"the space is locally compact")
					fromInfinity := b.Have(
						"a point some(x) and the new point lie in disjoint open sets",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"x ∈ ⋃T",
							},
							Conclusion: "∃u v:set(option(A)). " +
								"    u ∈ one_point_compactification(T) ∧ " +
								"    v ∈ one_point_compactification(T) ∧ " +
								"    some(x) ∈ u ∧ " +
								"    none ∈ v ∧ " +
								"    u ∩ v = ∅",
						},
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							xIn := c.Assume()
							_, _, at := c.Obtain2As[Set[A], Set[A]](
								"x has an open neighbourhood u inside a compact set k",
								"∃u k:set(A). u ∈ T ∧ compact_in(T, k) ∧ x ∈ u ∧ u ⊆ k",
								By(parts[1], xIn, compact.LocallyCompactSpaceDef))
							nbhd := c.Conjuncts(
								at,
								"u is open",
								"k is compact",
								"u holds x",
								"u lies in k")
							closed := c.Have(
								"k is closed, a compact set of a Hausdorff space",
								"closed_in(T, k)",
								By(parts[0], nbhd[1], compact.CompactClosed.Read(topology)))
							uImage := c.Have(
								"the image of u is open",
								"image(some, u) ∈ one_point_compactification(T)",
								By(nbhd[0], OnePointImageOpen))
							complement := c.Have(
								"the new point with the image of the space less k is open",
								"insert(none, image(some, ⋃T ∖ k)) ∈ one_point_compactification(T)",
								By(closed, nbhd[1], OnePointComplementOpen))
							disjoint := c.Have(
								"the two are disjoint, u lying in k",
								"image(some, u) ∩ insert(none, image(some, ⋃T ∖ k)) = ∅",
								BySets(nbhd[3], option.SomeInjective, option.NoneNotSome))
							c.Take(c.TermAs[Set[option.Option[A]]]("image(some, u)"))
							c.Take(c.TermAs[Set[option.Option[A]]]("insert(none, image(some, ⋃T ∖ k))"))
							c.Show(
								"they separate some(x) from the new point",
								BySets(disjoint, nbhd[2], uImage, complement))
						}))
					twoPoints := b.Have(
						"two distinct points some(x) and some(y) lie in disjoint open sets",
						Statement{
							Binders: "∀x y:A.",
							Hypotheses: []string{
								"x ∈ ⋃T",
								"y ∈ ⋃T",
								"x ≠ y",
							},
							Conclusion: "∃u v:set(option(A)). " +
								"    u ∈ one_point_compactification(T) ∧ " +
								"    v ∈ one_point_compactification(T) ∧ " +
								"    some(x) ∈ u ∧ " +
								"    some(y) ∈ v ∧ " +
								"    u ∩ v = ∅",
						},
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							c.FixAs[A]("y")
							distinct := c.Assume()
							_, _, at := c.Obtain2As[Set[A], Set[A]](
								"x and y lie in disjoint open sets u and v",
								"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅",
								By(parts[0], distinct, topological_space.HausdorffDef))
							sep := c.Conjuncts(
								at,
								"u is open",
								"v is open",
								"u holds x",
								"v holds y",
								"u and v are disjoint")
							uImage := c.Have(
								"the image of u is open",
								"image(some, u) ∈ one_point_compactification(T)",
								By(sep[0], OnePointImageOpen))
							vImage := c.Have(
								"the image of v is open",
								"image(some, v) ∈ one_point_compactification(T)",
								By(sep[1], OnePointImageOpen))
							disjoint := c.Have(
								"the images are disjoint, some being one-to-one",
								"image(some, u) ∩ image(some, v) = ∅",
								BySets(sep[4], option.SomeInjective))
							c.Take(c.TermAs[Set[option.Option[A]]]("image(some, u)"))
							c.Take(c.TermAs[Set[option.Option[A]]]("image(some, v)"))
							c.Show(
								"they separate some(x) from some(y)",
								BySets(disjoint, sep[2], sep[3], uImage, vImage))
						}))
					b.Show(
						"so the compactification is Hausdorff",
						Simp(Fwd(topological_space.HausdorffDef)),
						Derive(func(c *Argument) {
							c.FixAs[option.Option[A]]("p")
							c.FixAs[option.Option[A]]("q")
							distinct := c.Assume()
							c.Cases(c.Term("q = none"))
							c.When(
								"q is the new point",
								func(d *Argument, qNone Fact) {
									x, at := d.ObtainAs[A](
										"p, another point, is some(x) for a point x of the space",
										"∃x:A. x ∈ ⋃T ∧ p = some(x)",
										BySets(space, qNone, distinct))
									d.Show(
										"some(x) and the new point lie in disjoint open sets",
										By(fromInfinity.At(x), qNone, at))
								})
							c.Otherwise(
								"q is some(y) for a point y of the space",
								func(d *Argument, qSome Fact) {
									y, atY := d.ObtainAs[A](
										"q is some(y) for a point y of the space",
										"∃y:A. y ∈ ⋃T ∧ q = some(y)",
										BySets(space, qSome, distinct))
									d.Cases(d.Term("p = none"))
									d.When(
										"p is the new point",
										func(e *Argument, pNone Fact) {
											e.Show(
												"the new point and some(y) lie in disjoint open sets, taken the other way round",
												By(fromInfinity.At(y), pNone, atY, set_algebra.InterComm))
										})
									d.Otherwise(
										"p is some(x) as well",
										func(e *Argument, pSome Fact) {
											x, atX := e.ObtainAs[A](
												"p is some(x) for a point x of the space, distinct from y",
												"∃x:A. x ∈ ⋃T ∧ p = some(x)",
												BySets(space, pSome, distinct))
											e.Show(
												"some(x) and some(y) lie in disjoint open sets",
												By(twoPoints.At(x, y), atX, atY, distinct))
										})
								})
						}))
				})
		}),
})}

// OnePointDenseIff — a space is dense in its one-point compactification
// exactly when it is not compact. The compactification is a space
// (OnePointTopology), so by the density criterion
// (topological_space.DenseMeetsOpen) the image of the space is dense when
// every non-empty open set meets it. When the space is compact, the new
// point alone is open, the complement of the closed compact space, and it
// misses the image. When it is not, an open set u holding no new point
// holds some(x) for a point x of the space; and when u holds the new
// point, the complement of its trace is compact, so not the whole space,
// and the trace has a point x of the space, some(x) lying in u and in the
// image.
var OnePointDenseIff = onePointDenseIffThm{family.Add(registry.ProofEntry{
	Name: "OnePointDenseIff",
	Key:  "prop_341d683cea276b9f",
	Build: topological_space.IsTopology.Law(
		"closure(one_point_compactification(T), image(some, ⋃T)) = ⋃one_point_compactification(T) ⇔ "+
			"¬compact_in(T, ⋃T)",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			space := OnePointSpace.Read(topology)
			compactification := a.Have(
				"the compactification is a space",
				"is_topology(one_point_compactification(T))",
				By(OnePointTopology.Read(topology)))
			within := a.Have(
				"the image of the space lies in its space",
				"image(some, ⋃T) ⊆ ⋃one_point_compactification(T)",
				BySets(space))
			a.Do(Simp(Fwd(GroupPremises(within, Read(topological_space.DenseMeetsOpen, compactification)))))
			a.Iff()
			a.Forward(
				"if every non-empty open set meets the image, the space is not compact",
				func(b *Argument, meets Fact) {
					compactSpace := b.SupposeNot()
					isolated := b.Have(
						"the new point alone is open, the complement of the closed compact space",
						"insert(none, image(some, ⋃T ∖ ⋃T)) ∈ one_point_compactification(T)",
						By(compactSpace, topological_space.SpaceClosed.Read(topology), OnePointComplementOpen))
					misses := b.Have(
						"and it misses the image of the space",
						"insert(none, image(some, ⋃T ∖ ⋃T)) ∩ image(some, ⋃T) = ∅",
						BySets(option.NoneNotSome))
					b.Show(
						"a non-empty open set missing the image",
						BySets(
							meets.At(b.TermAs[Set[option.Option[A]]]("insert(none, image(some, ⋃T ∖ ⋃T))")),
							isolated,
							misses))
				})
			a.Backward(
				"if the space is not compact, every non-empty open set meets the image",
				func(b *Argument, notCompact Fact) {
					b.FixAs[Set[option.Option[A]]]("u")
					given := b.Conjuncts(
						b.Assume(),
						"u is open",
						"u is not empty")
					compactness := b.Have(
						"the complement of the trace of u is compact when u holds the new point",
						"none ∈ u ⇒ compact_in(T, ⋃T ∖ {x:A | some(x) ∈ u})",
						By(given[0], OnePointOpenIff))
					b.Cases(b.Term("none ∈ u"))
					b.When(
						"u holds the new point",
						func(c *Argument, noneIn Fact) {
							proper := c.Have(
								"the complement of the trace of u is compact, so not the whole space",
								"⋃T ∖ {x:A | some(x) ∈ u} ≠ ⋃T",
								By(notCompact, noneIn, compactness))
							c.Show(
								"so the trace has a point x of the space, and some(x) lies in u and in the image",
								BySets(proper))
						})
					b.Otherwise(
						"u does not hold the new point",
						func(c *Argument, noneOut Fact) {
							c.Show(
								"so a point of u, a point of the compactification other than the new point, lies in the image",
								BySets(given[1], noneOut, given[0], space))
						})
				})
		}),
})}
