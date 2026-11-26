// lifting.go — lifting through a covering map: two lifts of one map from
// a connected space that agree at a point agree everywhere; a path lifts
// from any point over its start, and so does a map of the unit square;
// so homotopic paths lift, from one point, to homotopic paths, and the
// covering map induces an injective map of fundamental groups.

package covering_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LiftsLocallyAgreeOrDiffer — two lifts of one map from a space agree
// throughout, or differ throughout, an open neighbourhood of each point of
// it. About q take an evenly covered u holding p(f(q)) = p(g(q)), and the
// sheets w and w' over u holding f(q) and g(q); on the open set N of points
// f carries into w and g into w', the lifts agree if the two sheets are one,
// p having an inverse on a sheet, and differ if they are two, distinct
// sheets being disjoint.
var LiftsLocallyAgreeOrDiffer = liftsLocallyAgreeOrDifferThm{family.Add(registry.ProofEntry{
	Name: "LiftsLocallyAgreeOrDiffer",
	Key:  "prop_ed295e497a5fd04f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀R:set(set(C)). ∀f g:(C → A). ∀q:C.",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"is_topology(R)",
			"continuous_map(R, T, f)",
			"continuous_map(R, T, g)",
			"∀x:C. x ∈ ⋃R ⇒ p(f(x)) = p(g(x))",
			"q ∈ ⋃R",
		},
		Conclusion: "∃N:set(C). " +
			"    N ∈ R ∧ q ∈ N ∧ ((∀x:C. x ∈ N ⇒ f(x) = g(x)) ∨ (∀x:C. x ∈ N ⇒ f(x) ≠ g(x)))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			p *Arrow[A, B],
			R *Expr[Set[Set[C]]],
			f, g *Arrow[C, A],
			q *Expr[C],
			covering Fact,
			topology topological_space.IsTopologyFact[on.R],
			fContinuous, gContinuous continuous.ContinuousMapFact[on.R, on.T],
			overP Fact,
			inSpace Fact,
		) {
			covered := a.Conjuncts(
				a.Unfolded(covering, CoveringMapDef),
				"p is continuous",
				"each point of the base lies in an evenly covered open set")
			values := a.Have(
				"f and g carry q into the covering space",
				"f(q) ∈ ⋃T ∧ g(q) ∈ ⋃T",
				By(
					inSpace,
					continuous.MapsInto.Read(fContinuous).At(q),
					continuous.MapsInto.Read(gContinuous).At(q)))
			_, around := a.ObtainAs[Set[B]](
				"p carries f(q) into the base, where it lies in an evenly covered open set u",
				"∃u:set(B). p(f(q)) ∈ u ∧ evenly_covered(T, S, p, u)",
				By(values, covered[1].At(p.Apply(f.Apply(q))), continuous.MapsInto.Read(covered[0]).At(f.Apply(q))))
			overU := a.Conjuncts(
				around,
				"u holds p(f(q))",
				"u is evenly covered")
			evenly := a.Conjuncts(
				a.Unfolded(overU[1], EvenlyCoveredDef),
				"u is open in the base",
				"the part of the space over u is a union of sheets")
			_, sheetsFact := a.UnpackAs[Set[Set[A]]](evenly[1], "v")
			sheets := a.Conjuncts(
				sheetsFact,
				"the sheets are open",
				"they make up the part of the space over u",
				"two distinct sheets are disjoint",
				"p carries each sheet homeomorphically onto u")
			w, wPrime, onSheets := a.Obtain2As[Set[A], Set[A]](
				"f(q) lies over u, and so does g(q), as p(g(q)) = p(f(q)): each lies in a sheet, w and w'",
				"∃w w':set(A). w ∈ v ∧ w' ∈ v ∧ f(q) ∈ w ∧ g(q) ∈ w'",
				BySets(sheets[1], values, overU[0], inSpace, overP.At(q)))
			placed := a.Conjuncts(
				onSheets,
				"w is a sheet",
				"w' is a sheet",
				"w holds f(q)",
				"w' holds g(q)")
			sheetsOpen := a.Have(
				"the sheets w and w' are open",
				"w ∈ T ∧ w' ∈ T",
				BySets(sheets[0], placed[0], placed[1]))
			N, NDef := a.LetAs[Set[C]]("N", "preimage_on(⋃R, f, w) ∩ preimage_on(⋃R, g, w')")
			fPreimage := a.TermAs[Set[C]]("preimage_on(⋃R, f, w)")
			gPreimage := a.TermAs[Set[C]]("preimage_on(⋃R, g, w')")
			open := a.Have(
				"N, the meet of the preimages of two open sets, is open",
				"N ∈ R",
				By(
					Normalized,
					NDef,
					sheetsOpen,
					continuous.PreimageOpen.Read(fContinuous).AsFact().At(w),
					continuous.PreimageOpen.Read(gContinuous).AsFact().At(wPrime),
					topological_space.InterOpen.Read(topology).AsFact().At(fPreimage, gPreimage)))
			holdsQ := a.Have(
				"N holds q",
				"q ∈ N",
				BySets(NDef, inSpace, placed[2], placed[3]))
			agreeOrDiffer := a.Have(
				"on N, f and g agree throughout or differ throughout",
				"(∀x:C. x ∈ N ⇒ f(x) = g(x)) ∨ (∀x:C. x ∈ N ⇒ f(x) ≠ g(x))",
				Derive(func(b *Argument) {
					b.Cases(b.Term("w = w'"))
					b.When(
						"on one sheet, where p has an inverse, f and g agree throughout N",
						func(c *Argument, same Fact) {
							_, undoes := c.ObtainAs[Fun[B, A]](
								"p carries the sheet w homeomorphically onto u, so has an inverse h on w",
								"∃h:(B → A). ∀a:A. a ∈ ⋃T ∧ a ∈ w ⇒ h(p(a)) = a",
								BySets(
									placed[0],
									sheets[3].At(w),
									continuous.HomeomorphismInverseMaps,
									topological_space.SubtopologySpace.At(T, w)))
							c.Show(
								"at each point x of N, h takes p(f(x)) = p(g(x)) back to f(x) and to g(x)",
								Left(),
								Derive(func(d *Argument) {
									x := d.FixAs[C]("x")
									inN := d.Assume()
									onW := d.Have(
										"x is a point of the space that f and g both carry into w",
										"x ∈ ⋃R ∧ f(x) ∈ w ∧ g(x) ∈ w",
										BySets(NDef, inN, same))
									d.Show(
										"f(x) = h(p(f(x))) = h(p(g(x))) = g(x)",
										By(
											onW,
											overP.At(x),
											undoes.At(f.Apply(x)),
											undoes.At(g.Apply(x)),
											continuous.MapsInto.Read(fContinuous).At(x),
											continuous.MapsInto.Read(gContinuous).At(x)))
								}))
						})
					b.Otherwise(
						"on two sheets, which are disjoint, f and g differ throughout N",
						func(c *Argument, distinct Fact) {
							c.Show(
								"a point of N where they agreed would lie in both sheets",
								BySets(NDef, placed[0], placed[1], distinct, sheets[2].At(w, wPrime)))
						})
				}))
			a.Take(N)
			a.Show(
				"N is an open set about q on which f and g agree throughout or differ throughout",
				By(open, holdsQ, agreeOrDiffer))
		}),
})}

// LiftUnique — two lifts of one map from a connected space that agree at
// one point agree everywhere: the points where they agree form a set E
// both open and closed, since about each point of the space they agree
// throughout, or differ throughout, an open set (LiftsLocallyAgreeOrDiffer);
// the connected space lies in E or misses it, and it meets E at z.
var LiftUnique = liftUniqueThm{family.Add(registry.ProofEntry{
	Name: "LiftUnique",
	Key:  "prop_f34adf302a5ee51",
	Reading: "Connectedness and is_topology(R) carry it: the agree set and the disagree " +
		"set are unions of the open sets where f goes into one sheet and g into another. Here " +
		"R is read for its unions (OpenPointwise), and LiftsLocallyAgreeOrDiffer reads its " +
		"meets, which make those sets open. Without connectedness two lifts on a two-point " +
		"discrete space agree at one point and differ at the other. T and S need no axiom.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀R:set(set(C)). ∀f g:(C → A). ∀z y:C.",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"is_topology(R)",
			"connected_in(R, ⋃R)",
			"continuous_map(R, T, f)",
			"continuous_map(R, T, g)",
			"∀x:C. x ∈ ⋃R ⇒ p(f(x)) = p(g(x))",
			"z ∈ ⋃R",
			"f(z) = g(z)",
			"y ∈ ⋃R",
		},
		Conclusion: "f(y) = g(y)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			p *Arrow[A, B],
			R *Expr[Set[Set[C]]],
			f, g *Arrow[C, A],
			z, y *Expr[C],
			covering Fact,
			topology topological_space.IsTopologyFact[on.R],
			connectedSpace Fact,
			fContinuous, gContinuous continuous.ContinuousMapFact[on.R, on.T],
			overP Fact,
			zIn Fact,
			agreeAtZ Fact,
			yIn Fact,
		) {
			local := a.Have(
				"about each point of the space, f and g agree throughout or differ throughout an open set",
				Statement{
					Binders: "∀q:C.",
					Hypotheses: []string{
						"q ∈ ⋃R",
					},
					Conclusion: "∃N:set(C). " +
						"    N ∈ R ∧ q ∈ N ∧ ((∀x:C. x ∈ N ⇒ f(x) = g(x)) ∨ (∀x:C. x ∈ N ⇒ f(x) ≠ g(x)))",
				},
				By(
					covering,
					topology,
					fContinuous,
					gContinuous,
					overP,
					At(LiftsLocallyAgreeOrDiffer, T, S, p, R, f, g)))
			E, EDef := a.LetAs[Set[C]]("E", "{x:C | x ∈ ⋃R ∧ f(x) = g(x)}")
			agreeNear := a.Have(
				"each point of E lies in an open set inside E",
				"∀x:C. x ∈ E ⇒ ∃v:set(C). v ∈ R ∧ v ⊆ E ∧ x ∈ v",
				Derive(func(b *Argument) {
					x := b.FixAs[C]("x")
					inE := b.Assume()
					agreeAt := b.Have(
						"x is a point of the space where f and g agree",
						"x ∈ ⋃R ∧ f(x) = g(x)",
						BySets(EDef, inE))
					b.Show(
						"about x they agree throughout an open set, since they agree at x, and it lies in E",
						BySets(EDef, agreeAt, local.At(x)))
				}))
			differNear := a.Have(
				"each point of the space outside E lies in an open set outside E",
				"∀x:C. x ∈ ⋃R ∖ E ⇒ ∃v:set(C). v ∈ R ∧ v ⊆ ⋃R ∖ E ∧ x ∈ v",
				Derive(func(b *Argument) {
					x := b.FixAs[C]("x")
					outside := b.Assume()
					b.Show(
						"about x they differ throughout an open set, since they differ at x, and it misses E",
						BySets(EDef, outside, local.At(x)))
				}))
			open := a.Have(
				"so E is open, by the pointwise criterion",
				"E ∈ R",
				By(agreeNear, topological_space.OpenPointwise.Read(topology)))
			restOpen := a.Have(
				"and so is the rest of the space",
				"⋃R ∖ E ∈ R",
				By(differNear, topological_space.OpenPointwise.Read(topology)))
			closed := a.Have(
				"so E, a set of points of the space, is closed",
				"closed_in(R, E)",
				BySets(restOpen, EDef, topological_space.ClosedInDef))
			split := a.Have(
				"the connected space lies in the open and closed set E or misses it",
				"⋃R ⊆ E ∨ ⋃R ∩ E = ∅",
				By(connectedSpace, open, closed, connected.ConnectedClopen.At(R, a.TermAs[Set[C]]("⋃R"), E)))
			a.Show(
				"it meets E at z, so it lies in E, and y is a point of E",
				BySets(split, EDef, zIn, agreeAtZ, yIn))
		}),
})}

// PathLifting — a path in the base lifts to a path from any point over its
// start.
var PathLifting = pathLiftingThm{family.Add(registry.ProofEntry{
	Name: "PathLifting",
	Key:  "prop_f967750b54a0a8d2",
	Reading: "p(e) = g(0) is load-bearing: the lift starts over the path's start. " +
		"p need not be onto: each evenly covered set met holds a point p reaches, so " +
		"it has a sheet. No axiom on T or S; the pasting is on the interval.",
	Deps: []registry.EntryLike{
		CoveringMapDef,
		EvenlyCoveredDef,
		complete_metric.LebesgueNumber,
		continuous.ClosedPasting,
		continuous.HomeomorphismInverseMaps,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀g:(real → B). ∀e:A.",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"path_in(S, g)",
			"e ∈ ⋃T",
			"p(e) = g(&0)",
		},
		Conclusion: "∃h:(real → A). path_in(T, h) ∧ h(&0) = e ∧ ∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ p(h(t)) = g(t)",
	},
		"cut ⟦0, 1⟧ by a Lebesgue number of the cover by the preimages under g of evenly covered "+
			"sets (LebesgueNumber) into finitely many intervals each carried into one evenly covered "+
			"u; on each in turn lift by the inverse of p on the sheet over u holding the lift's "+
			"value at the interval's left end (HomeomorphismInverseMaps), and paste (ClosedPasting)"),
})}

// SquareLifting — a map of the unit square into the base lifts to a map of
// the square from any point over the image of its corner.
var SquareLifting = squareLiftingThm{family.Add(registry.ProofEntry{
	Name: "SquareLifting",
	Key:  "prop_924f88698133ab90",
	Reading: "p(e) = H((0, 0)) is load-bearing, as in PathLifting; " +
		"neighbouring small squares' lifts agree on the edges they share by " +
		"LiftUnique, the edges being connected and holding a common corner.",
	Deps: []registry.EntryLike{
		PathLifting,
		LiftUnique,
		CoveringMapDef,
		EvenlyCoveredDef,
		complete_metric.LebesgueNumber,
		continuous.ClosedPasting,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀H:(prod(real, real) → B). ∀e:A.",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"continuous_map(product_topology(«I», «I»), S, H)",
			"e ∈ ⋃T",
			"p(e) = H((&0, &0))",
		},
		Conclusion: "∃K:(prod(real, real) → A). " +
			"    continuous_map(product_topology(«I», «I»), T, K) ∧ " +
			"    K((&0, &0)) = e ∧ " +
			"    ∀s t:real. &0 ≤ s ∧ s ≤ &1 ∧ &0 ≤ t ∧ t ≤ &1 ⇒ p(K((s, t))) = H((s, t))",
	},
		"cut the square by a Lebesgue number (LebesgueNumber) into a grid of small squares "+
			"each carried into one evenly covered set; lift the left edge by PathLifting, then "+
			"the small squares one at a time in rows from the bottom and left, each by the "+
			"inverse of p on the sheet holding the lift of its lower left corner: what of its "+
			"lower and left edges is already lifted is connected and holds that corner, so the "+
			"new lift agrees with it there (LiftUnique), and the pieces paste (ClosedPasting)"),
})}

// PathHomotopyLifting — the monodromy theorem: lifts from one point of two
// homotopic paths are homotopic, and in particular end at one point.
var PathHomotopyLifting = pathHomotopyLiftingThm{family.Add(registry.ProofEntry{
	Name: "PathHomotopyLifting",
	Key:  "prop_8f12de25b72ee0d2",
	Reading: "g'(0) = h'(0) is load-bearing: on the circle the lifts of " +
		"one loop from s and from s + 1 end at different points. The lifted " +
		"homotopy holds its ends because its two sides lift constant paths.",
	Deps: []registry.EntryLike{
		SquareLifting,
		LiftUnique,
		homotopy.PathHomotopicDef,
		homotopy.HomotopicRelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀g h:(real → B). ∀g' h':(real → A).",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"path_homotopic(S, g, h)",
			"path_in(T, g')",
			"path_in(T, h')",
			"g'(&0) = h'(&0)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ p(g'(t)) = g(t) ∧ p(h'(t)) = h(t)",
		},
		Conclusion: "path_homotopic(T, g', h')",
	},
		"lift the homotopy of g to h from g'(0) (SquareLifting); its two sides lift "+
			"constant paths, so are constant (LiftUnique on the connected interval), and "+
			"its bottom and top edges are lifts of g and h from g'(0), so are g' and h' "+
			"(LiftUnique): the lifted square is a homotopy of g' to h' with the ends held"),
})}

// CoveringFundamentalMapInjective — a covering map induces an injective map
// of fundamental groups.
var CoveringFundamentalMapInjective = coveringFundamentalMapInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CoveringFundamentalMapInjective",
	Key:  "prop_a28f77c1afc2889f",
	Reading: "At a point outside the space the carrier is empty and injectivity " +
		"is trivial; the content is PathHomotopyLifting at two loops at e.",
	Deps: []registry.EntryLike{
		PathHomotopyLifting,
		fundamental_group.FundamentalMapClass,
		fundamental_group.FundamentalGroupMember,
		fundamental_group.PathClassEq,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀p:(A → B). ∀e:A.",
		Hypotheses: []string{
			"covering_map(T, S, p)",
			"e ∈ ⋃T",
		},
		Conclusion: "injective_on(fundamental_group(T, e).carrier, fundamental_map(S, p))",
	},
		"if p ∘ g and p ∘ h are homotopic for two loops g and h at e, then g and h, which "+
			"are lifts of them from e, are homotopic (PathHomotopyLifting); the classes are "+
			"read through FundamentalGroupMember, FundamentalMapClass and PathClassEq"),
})}
