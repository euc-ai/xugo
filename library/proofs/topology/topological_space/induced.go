// induced.go — induced and coinduced topologies along a map on specified carriers.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// InducedTopologyDef — the induced open sets are the restricted preimages
// of the source open sets.
var InducedTopologyDef = inducedTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "InducedTopologyDef",
	Key:   "prop_18b96e63432b0f6b",
	Const: "induced_topology",
	Type:  "set(A) → set(set(B)) → (A → B) → set(set(A))",
	Equations: []string{
		"∀X:set(A). ∀S:set(set(B)). ∀f:(A → B). " +
			"    induced_topology(X, S, f) = image(λv:set(B). preimage_on(X, f, v), S)",
	},
})}

// InducedSpace — the induced family covers exactly the points of X mapped
// into the union of the source family. No topology axiom is needed.
var InducedSpace = inducedSpaceThm{family.Add(registry.ProofEntry{
	Name: "InducedSpace",
	Key:  "prop_99d3da7652afff23",
	Build: family.Theorem("∀X:set(A). ∀S:set(set(B)). ∀f:(A → B). "+
		"    ⋃induced_topology(X, S, f) = preimage_on(X, f, ⋃S)",
		func(a *Argument, X *Expr[Set[A]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Show(
				"a point lies in the induced union exactly when it lies in X and its image lies in a member of S",
				Unfold(InducedTopologyDef),
				Unfold(functions.PreimageOnDef),
				BySets())
		}),
})}

// InducedTopology — restricted preimages of the opens of a topology form
// a topology. They preserve intersections; a family of them unites to the
// preimage of the union of all source opens whose preimages lie inside that union.
var InducedTopology = inducedTopologyThm{family.Add(registry.ProofEntry{
	Name: "InducedTopology",
	Key:  "prop_d348b1d72c937f98",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(set(B)). ∀X:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(S)",
		},
		Conclusion: "is_topology(induced_topology(X, S, f))",
	},
		func(
			a *Argument,
			S *Expr[Set[Set[B]]],
			X *Expr[Set[A]],
			f *Arrow[A, B],
			topology IsTopologyFact[on.S],
		) {
			pullback := a.TermAs[Fun[Set[B], Set[A]]]("preimage_on(X, f)")
			a.Do(Simp(Fwd(IsTopology)), Unfold(InducedTopologyDef), SplitConj(
				Case(
					"two restricted preimages meet in the preimage of an open intersection",
					Simp(Fwd(set_image.ForallInImagePair.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[A]]()))),
					Derive(func(b *Argument) {
						b.FixAs[Set[B]]("u")
						b.FixAs[Set[B]]("v")
						bothOpen := b.Assume()
						meetOpen := b.Have(
							"the source intersection is open",
							"u ∩ v ∈ S",
							By(InterOpen.Read(topology), bothOpen))
						meet := b.Have(
							"restricted preimages preserve intersections",
							"preimage_on(X, f, u) ∩ preimage_on(X, f, v) = preimage_on(X, f, u ∩ v)",
							Unfold(functions.PreimageOnDef),
							BySets())
						b.Show(
							"the intersection is the preimage of a source open",
							meet.Rw(),
							By(meetOpen, set_image.FunInImage.At(pullback, S, b.TermAs[Set[B]]("u ∩ v"))))
					})),
				Case(
					"a family of restricted preimages unites to the preimage of an open union",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("F")
						covered := b.Assume()
						C, selected := b.LetAs[Set[Set[B]]]("C", "{v:set(B) | v ∈ S ∧ preimage_on(X, f, v) ⊆ ⋃F}")
						subfamily := b.Have(
							"the selected opens form a subfamily of S",
							"C ⊆ S",
							BySets(selected))
						unionOpen := b.Have(
							"their union is open",
							"⋃C ∈ S",
							By(subfamily, UnionsOpen.Read(topology).At(C)))
						selectedPoints := b.Unfolded(selected, functions.PreimageOnDef)
						coveredPoints := b.Unfolded(covered, functions.PreimageOnDef)
						reached := b.Have(
							"each member of F lies in the preimage of the selected union",
							"⋃F ⊆ preimage_on(X, f, ⋃C)",
							Unfold(functions.PreimageOnDef),
							Simp(Fwd(set_order.UnionsSubset)),
							BySets(selectedPoints, coveredPoints))
						within := b.Have(
							"each selected preimage lies inside the union of F",
							"preimage_on(X, f, ⋃C) ⊆ ⋃F",
							Unfold(functions.PreimageOnDef),
							BySets(selectedPoints))
						unites := b.Have(
							"the two unions agree under restricted preimage",
							"⋃F = preimage_on(X, f, ⋃C)",
							By(reached, within, set_order.SubsetAntisym))
						b.Show(
							"the union of F is the preimage of a source open",
							unites.Rw(),
							By(unionOpen, set_image.FunInImage.At(pullback, S, b.TermAs[Set[B]]("⋃C"))))
					})),
			))
		}),
})}

// CoinducedTopologyDef — the coinduced opens are the subsets of the target
// carrier whose restricted preimages are open in the source.
var CoinducedTopologyDef = coinducedTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "CoinducedTopologyDef",
	Key:   "prop_f105c07d2431f81c",
	Const: "coinduced_topology",
	Type:  "set(B) → set(set(A)) → (A → B) → set(set(B))",
	Equations: []string{
		"∀Y:set(B). ∀T:set(set(A)). ∀f:(A → B). " +
			"    coinduced_topology(Y, T, f) = {v:set(B) | v ⊆ Y ∧ preimage_on(⋃T, f, v) ∈ T}",
	},
})}

// CoinducedTopology — subsets with open restricted preimages form a topology:
// preimages preserve intersections and arbitrary unions, and both remain in Y.
var CoinducedTopology = coinducedTopologyThm{family.Add(registry.ProofEntry{
	Name: "CoinducedTopology",
	Key:  "prop_a198d0547a1337eb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀Y:set(B). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "is_topology(coinduced_topology(Y, T, f))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			Y *Expr[Set[B]],
			f *Arrow[A, B],
			topology IsTopologyFact[on.T],
		) {
			a.Do(Simp(Fwd(IsTopology)), Unfold(CoinducedTopologyDef), SplitConj(
				Case(
					"two target opens meet with an open restricted preimage",
					Derive(func(b *Argument) {
						b.FixAs[Set[B]]("u")
						b.FixAs[Set[B]]("v")
						bothOpen := b.Assume()
						preimagesOpen := b.Have(
							"both restricted preimages are open",
							"preimage_on(⋃T, f, u) ∈ T ∧ preimage_on(⋃T, f, v) ∈ T",
							BySets(bothOpen))
						meet := b.Have(
							"restricted preimages preserve intersections",
							"preimage_on(⋃T, f, u ∩ v) = preimage_on(⋃T, f, u) ∩ preimage_on(⋃T, f, v)",
							Unfold(functions.PreimageOnDef),
							BySets())
						meetOpen := b.Have(
							"the intersection has an open restricted preimage",
							"preimage_on(⋃T, f, u ∩ v) ∈ T",
							meet.Rw(),
							By(preimagesOpen, InterOpen.Read(topology)))
						b.Show(
							"the intersection lies in Y and has open preimage",
							BySets(meetOpen, bothOpen))
					})),
				Case(
					"a family of target opens unites with an open restricted preimage",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[B]]]("F")
						covered := b.Assume()
						subfamily := b.Have(
							"the restricted preimages form a subfamily of T",
							"image(preimage_on(⋃T, f), F) ⊆ T",
							Simp(Fwd(set_basic.SubsetDef.Inst[Set[A]]())),
							Simp(Fwd(set_image.ForallInImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[A]]()))),
							BySets(covered))
						unites := b.Have(
							"restricted preimages preserve the union",
							"preimage_on(⋃T, f, ⋃F) = ⋃image(preimage_on(⋃T, f), F)",
							Unfold(functions.PreimageOnDef),
							BySets())
						unionOpen := b.Have(
							"the union has an open restricted preimage",
							"preimage_on(⋃T, f, ⋃F) ∈ T",
							unites.Rw(),
							By(subfamily, UnionsOpen.Read(topology).At(b.TermAs[Set[Set[A]]]("image(preimage_on(⋃T, f), F)"))))
						within := b.Have(
							"the union stays inside Y",
							"⋃F ⊆ Y",
							Simp(Fwd(set_order.UnionsSubset)),
							BySets(covered))
						b.Show(
							"the union lies in Y and has open preimage",
							BySets(unionOpen, within))
					})),
			))
		}),
})}

// CoinducedSpace — when the source carrier maps into Y, the coinduced
// topology has carrier Y: Y itself has the whole source as its preimage.
var CoinducedSpace = coinducedSpaceThm{family.Add(registry.ProofEntry{
	Name: "CoinducedSpace",
	Key:  "prop_7836d256edf88986",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀Y:set(B). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"image(f, ⋃T) ⊆ Y",
		},
		Conclusion: "⋃coinduced_topology(Y, T, f) = Y",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], Y *Expr[Set[B]], f *Arrow[A, B], mapsInto Fact) {
			parts := a.Conjuncts(
				mapsInto,
				"the source is a topology",
				"the source carrier maps into Y")
			wholePreimage := a.Have(
				"the target carrier pulls back to the whole source",
				"preimage_on(⋃T, f, Y) = ⋃T",
				Unfold(functions.PreimageOnDef),
				BySets(parts[1]))
			preimageOpen := a.Have(
				"the preimage of Y is open",
				"preimage_on(⋃T, f, Y) ∈ T",
				wholePreimage.Rw(),
				By(SpaceOpen.Read(parts[0])))
			carrierOpen := a.Have(
				"Y is coinduced open",
				"Y ∈ coinduced_topology(Y, T, f)",
				Simp(Fwd(CoinducedTopologyDef)),
				BySets(preimageOpen))
			within := a.Have(
				"every coinduced open lies in Y",
				"⋃coinduced_topology(Y, T, f) ⊆ Y",
				Unfold(CoinducedTopologyDef),
				Simp(Fwd(set_order.UnionsSubset)),
				BySets())
			covers := a.Have(
				"the coinduced opens cover Y",
				"Y ⊆ ⋃coinduced_topology(Y, T, f)",
				By(
					carrierOpen,
					set_order.MemberSubsetUnions.At(a.TermAs[Set[Set[B]]]("coinduced_topology(Y, T, f)"), Y)))
			a.Show(
				"the coinduced carrier is Y",
				By(within, covers, set_order.SubsetAntisym))
		}),
})}

// InducedCoinducedAdjunction — inclusion of the induced family in T is
// equivalent to inclusion in the coinduced family: both say that every
// member of S has its restricted preimage in T.
var InducedCoinducedAdjunction = inducedCoinducedAdjunctionThm{family.Add(registry.ProofEntry{
	Name: "InducedCoinducedAdjunction",
	Key:  "prop_39f6453068793757",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
		"    induced_topology(⋃T, S, f) ⊆ T ⇔ S ⊆ coinduced_topology(⋃S, T, f)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Show(
				"both inclusions express openness of every restricted preimage",
				Unfold(InducedTopologyDef),
				Unfold(CoinducedTopologyDef),
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_image.ForallInImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[A]]()))),
				BySets())
		}),
})}
