// paths.go — the homotopy of paths with their ends held: an equivalence
// on the paths of a space that keeps both ends; a path read along two
// maps of the interval with the same ends gives homotopic paths; and
// joining is associative, unital and inverted by reversal, up to
// homotopy, and both operations respect homotopy. These are the laws the
// classes of paths are a groupoid by.

package homotopy

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PathHomotopicEnds — homotopic paths share their two ends.
var PathHomotopicEnds = pathHomotopicEndsThm{family.Add(registry.ProofEntry{
	Name: "PathHomotopicEnds",
	Key:  "prop_3e5e29b3447555a6",
	Reading: "No continuity is read: 0 and 1 are held points " +
		"of ⟦0, 1⟧, so h(0) = H((0, 1)) = g(0), and likewise at 1.",
	Deps: []registry.EntryLike{PathHomotopicDef, HomotopicRelDef},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_homotopic(T, g, h)",
		},
		Conclusion: "g(&0) = h(&0) ∧ g(&1) = h(&1)",
	},
		"the homotopy holds 0 and 1, points of the interval, "+
			"at g(0) and g(1) at every time, and at time 1 it is h"),
})}

// PathHomotopicPaths — homotopic paths are paths.
var PathHomotopicPaths = pathHomotopicPathsThm{family.Add(registry.ProofEntry{
	Name: "PathHomotopicPaths",
	Key:  "prop_3a5726fc7f16bdd5",
	Reading: "g and h are the homotopy along the bottom and top edges " +
		"of the square on ⟦0, 1⟧, so continuous (Eq). T needs no axiom.",
	Deps: []registry.EntryLike{
		PathHomotopicDef,
		HomotopicRelDef,
		path_connected.PathInDef,
		continuous.Compose,
		continuous.Eq,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_homotopic(T, g, h)",
		},
		Conclusion: "path_in(T, g) ∧ path_in(T, h)",
	},
		"on the interval g is the homotopy after t ↦ (t, 0) and h the homotopy "+
			"after t ↦ (t, 1), both continuous into the square (Compose), and a "+
			"map agreeing on the interval with a continuous one is continuous (Eq)"),
})}

// PathHomotopicEquivalence — homotopy with ends held is an equivalence on
// the paths of a space.
var PathHomotopicEquivalence = pathHomotopicEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "PathHomotopicEquivalence",
	Key:  "prop_fb98557936cd8cbe",
	Reading: "Holds for any family T: transitivity pastes on the square, " +
		"a topology because «I» is, and nothing is claimed off the paths.",
	Deps: []registry.EntryLike{
		PathHomotopicDef,
		HomotopicRelRefl,
		HomotopicRelSym,
		HomotopicRelTrans,
		equivalence.EquivalenceOn,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Conclusion: "equivalence_on({g:(real → A) | path_in(T, g)}, path_homotopic(T))",
	},
		"HomotopicRelRefl, HomotopicRelSym and HomotopicRelTrans at the interval, which is a topology; "+
			"the target needs no axiom, since the pasting in the transitivity is done on the square"),
})}

// PathReparametriseHomotopic — a path run after two maps of the interval
// into itself that agree at 0 and at 1 gives two homotopic paths: the
// straight line (t, s) ↦ (1 − s)·a(t) + s·b(t) between the two maps is a
// continuous map of the square into the interval, a sum of products of
// continuous functions whose values are convex combinations of points of
// ⟦0, 1⟧; it is a at time 0 and b at time 1 and does not move at the two
// ends, where a and b agree, so g after it is the homotopy.
var PathReparametriseHomotopic = pathReparametriseHomotopicThm{family.Add(registry.ProofEntry{
	Name: "PathReparametriseHomotopic",
	Key:  "prop_e8d0e9fd64559a0f",
	Reading: "a(0) = b(0) and a(1) = b(1) are load-bearing: they keep the convex combination " +
		"still at the two held ends. Continuity into «I» keeps the combination in ⟦0, 1⟧.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A). ∀a b:(real → real).",
		Hypotheses: []string{
			"path_in(T, g)",
			"continuous_map(«I», «I», a)",
			"continuous_map(«I», «I», b)",
			"a(&0) = b(&0)",
			"a(&1) = b(&1)",
		},
		Conclusion: "path_homotopic(T, g ∘ a, g ∘ b)",
		Abbrev: Abbrev{
			{Name: "line", Text: "λp:prod(real, real). (&1 - snd(p)) * a(fst(p)) + snd(p) * b(fst(p))"},
		},
	}, func(
		arg *Argument,
		T *Expr[Set[Set[A]]],
		g *Arrow[Real, A],
		a, b *Arrow[Real, Real],
		path, aMap, bMap, start, end Fact,
	) {
		interval := arg.TermAs[Set[Set[Real]]]("«I»")
		zeroOne := arg.TermAs[Set[Real]]("⟦&0, &1⟧")
		reals := arg.TermAs[Set[Set[Real]]]("real_topology")
		square := arg.TermAs[Set[Set[Prod[Real, Real]]]]("product_topology(«I», «I»)")
		first := arg.TermAs[Fun[Prod[Real, Real], Real]]("fst")
		second := arg.TermAs[Fun[Prod[Real, Real], Real]]("snd")

		straight := arg.Have(
			"the straight line from a to b is a continuous map of the square into the interval",
			"continuous_map(product_topology(«I», «I»), «I», «line»)",
			Derive(func(d *Argument) {
				topology := d.Have(
					"the square is a topology, the interval being one",
					"is_topology(product_topology(«I», «I»))",
					By(
						product_topology.ProductTopology,
						topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
				along := d.Have(
					"a map of the interval into itself, read at the first "+
						"coordinate, is a continuous function on the square",
					Statement{
						Binders: "∀f:(real → real).",
						Hypotheses: []string{
							"continuous_map(«I», «I», f)",
						},
						Conclusion: "continuous_map(product_topology(«I», «I»), " +
							"    real_topology, " +
							"    λp:prod(real, real). f(fst(p)))",
					},
					Derive(func(e *Argument) {
						f := e.FixAs[Fun[Real, Real]]("f")
						fMap := e.Assume()
						e.Show(
							"f after the first projection is continuous into the interval, so into the reals",
							By(
								fMap,
								product_topology.FstContinuous.At(interval, interval),
								continuous.Compose.At(square, interval, first, interval, f),
								continuous.IntoSubtopology.At(
									square, reals, e.TermAs[Fun[Prod[Real, Real], Real]]("f ∘ fst"), zeroOne),
								functions.ComposeApply.At(f, first)))
					}))
				time := d.Have(
					"so is the second coordinate",
					"continuous_map(product_topology(«I», «I»), real_topology, snd)",
					By(
						product_topology.SndContinuous.At(interval, interval),
						continuous.IntoSubtopology.At(square, reals, second, zeroOne)))
				weight := d.Have(
					"and so is one less the second coordinate",
					"continuous_map(product_topology(«I», «I»), real_topology, λp:prod(real, real). &1 - snd(p))",
					By(
						topology,
						time,
						real_valued.ContinuousRealSub.At(
							square, d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). &1"), second),
						continuous.Constant.At(square, reals, d.TermAs[Real]("&1")),
						real_topology.RealSpace,
						set_basic.InUniv))
				continuousOnSquare := d.Have(
					"so the straight line, a sum of products of these, is a continuous function on the square",
					"continuous_map(product_topology(«I», «I»), real_topology, «line»)",
					By(
						topology,
						weight,
						time,
						aMap,
						bMap,
						along.At(a),
						along.At(b),
						real_valued.ContinuousRealAdd.At(
							square,
							d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). (&1 - snd(p)) * a(fst(p))"),
							d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). snd(p) * b(fst(p))")),
						real_valued.ContinuousRealMul.At(
							square,
							d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). &1 - snd(p)"),
							d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). a(fst(p))")),
						real_valued.ContinuousRealMul.At(
							square,
							second,
							d.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). b(fst(p))"))))
				inside := d.Have(
					"it takes the square into ⟦0, 1⟧",
					"∀p:prod(real, real). p ∈ ⋃product_topology(«I», «I») ⇒ «line»(p) ∈ ⟦&0, &1⟧",
					Derive(func(e *Argument) {
						p := e.FixAs[Prod[Real, Real]]("p")
						pIn := e.Assume()
						t := e.TermAs[Real]("fst(p)")
						intervalPoints := e.TermAs[Set[Real]]("⋃«I»")
						bounds := e.Have(
							"the second coordinate of p and the values of a and b at its first lie in ⟦0, 1⟧",
							"&0 ≤ snd(p) ∧ snd(p) ≤ &1 ∧ &0 ≤ a(fst(p)) ∧ a(fst(p)) ≤ &1 ∧ &0 ≤ b(fst(p)) ∧ b(fst(p)) ≤ &1",
							By(
								pIn,
								product_topology.ProductSpace.At(interval, interval),
								set_product.InCrossProjections.At(intervalPoints, intervalPoints, p),
								continuous.MapsInto.Read(aMap).At(t),
								continuous.MapsInto.Read(bMap).At(t),
								path_connected.UnitIntervalPoints.At(e.TermAs[Real]("snd(p)")),
								path_connected.UnitIntervalPoints.At(a.Apply(t)),
								path_connected.UnitIntervalPoints.At(b.Apply(t))))
						e.Show(
							"a convex combination of two points of ⟦0, 1⟧ lies in ⟦0, 1⟧",
							ByArith(bounds))
					}))
				d.Show(
					"a continuous function on the square with values in ⟦0, 1⟧ is a map into the interval",
					By(continuousOnSquare, inside, continuous.IntoSubtopology))
			}))
		edges := arg.Have(
			"the straight line is a along the bottom edge of the square and b along the top",
			"∀t:real. «line»((t, &0)) = a(t) ∧ «line»((t, &1)) = b(t)",
			Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
			ByArith())
		held := arg.Have(
			"at the ends 0 and 1 it stays at a's value, a and b agreeing there",
			"∀x t:real. x ∈ {&0, &1} ⇒ «line»((x, t)) = a(x)",
			Derive(func(d *Argument) {
				x := d.FixAs[Real]("x")
				d.FixAs[Real]("t")
				xEnd := d.Assume()
				agree := d.Have(
					"x is 0 or 1, where a and b agree",
					"a(x) = b(x)",
					By(
						start,
						end,
						xEnd,
						set_basic.InInsert.At(d.TermAs[Set[Real]]("{&1}"), d.TermAs[Real]("&0"), x),
						set_basic.InSing.At(x, d.TermAs[Real]("&1"))))
				d.Show(
					"so the convex combination of a(x) and b(x) is a(x)",
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
					ByArith(agree))
			}))

		arg.Do(Unfold(PathHomotopicDef), Unfold(HomotopicRelDef))
		arg.Take(arg.TermAs[Fun[Prod[Real, Real], A]]("g ∘ «line»"))
		arg.Do(SplitConjAll(
			Case(
				"g after the straight line is continuous on the square, g being a path",
				By(path, path_connected.PathInDef, continuous.Compose.Read(straight))),
			Case(
				"at time 0 it is g after a, and at time 1 g after b",
				Simp(Fwd(functions.ComposeApply)),
				arg.ForEach(func(x *Expr[Real]) Action { return By(edges.At(x)) })),
			Case(
				"at the ends 0 and 1 it stays at g(a(0)) and g(a(1)) for all time",
				Simp(Fwd(functions.ComposeApply)),
				arg.ForEach(func(x *Expr[Real]) Action {
					return arg.ForEach(func(t *Expr[Real]) Action { return By(held.At(x, t)) })
				})),
		))
	}),
})}

// PathJoinHomotopic — joining respects homotopy.
var PathJoinHomotopic = pathJoinHomotopicThm{family.Add(registry.ProofEntry{
	Name: "PathJoinHomotopic",
	Key:  "prop_6c2f5dd619079b5e",
	Reading: "g(1) = h(0) is load-bearing: on the line t = 1/2 the two " +
		"homotopies hold g(1) and h(0), and the pasting needs them equal.",
	Deps: []registry.EntryLike{
		PathHomotopicDef,
		PathHomotopicEnds,
		path_connected.PathJoinDef,
		continuous.ClosedPasting,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g g' h h':(real → A).",
		Hypotheses: []string{
			"path_homotopic(T, g, g')",
			"path_homotopic(T, h, h')",
			"g(&1) = h(&0)",
		},
		Conclusion: "path_homotopic(T, path_join(g, h), path_join(g', h'))",
	},
		"the two homotopies side by side, the first on ⟦0, 1/2⟧ × ⟦0, 1⟧ at double speed "+
			"in t and the second on ⟦1/2, 1⟧ × ⟦0, 1⟧; on the line t = 1/2 both hold the "+
			"common point g(1) = h(0), and ClosedPasting joins the two halves of the square"),
})}

// PathReverseHomotopic — reversing respects homotopy.
var PathReverseHomotopic = pathReverseHomotopicThm{family.Add(registry.ProofEntry{
	Name:    "PathReverseHomotopic",
	Key:     "prop_c449ca3f7318a7b6",
	Reading: "The homotopy is H((1 − t, s)), which swaps the two held ends; nothing more is needed.",
	Deps:    []registry.EntryLike{PathHomotopicDef, path_connected.PathReverseDef},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_homotopic(T, g, h)",
		},
		Conclusion: "path_homotopic(T, path_reverse(g), path_reverse(h))",
	},
		"the homotopy read at (1 − t, s)"),
})}

// PathJoinAssoc — joining is associative up to homotopy.
var PathJoinAssoc = pathJoinAssocThm{family.Add(registry.ProofEntry{
	Name: "PathJoinAssoc",
	Key:  "prop_df07d58789ad5089",
	Reading: "The two end-matching equations make the joins paths. On ⟦0, 1⟧ the left side is " +
		"the right side after the piecewise linear map sending 0, 1/4, 1/2, 1 to 0, 1/2, 3/4, 1.",
	Deps: []registry.EntryLike{
		PathReparametriseHomotopic,
		path_connected.PathJoin,
		path_connected.PathJoinDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h k:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
			"path_in(T, h)",
			"path_in(T, k)",
			"g(&1) = h(&0)",
			"h(&1) = k(&0)",
		},
		Conclusion: "path_homotopic(T, path_join(path_join(g, h), k), path_join(g, path_join(h, k)))",
	},
		"on the interval the left side is the right side after the piecewise linear map sending 0, "+
			"1/4, 1/2, 1 to 0, 1/2, 3/4, 1; PathReparametriseHomotopic compares it with the identity"),
})}

// PathJoinConstantLeft — a constant path joined before a path changes it
// only up to homotopy.
var PathJoinConstantLeft = pathJoinConstantLeftThm{family.Add(registry.ProofEntry{
	Name: "PathJoinConstantLeft",
	Key:  "prop_67d7b179b11aca7f",
	Reading: "Needs only that g is a path: the left side is " +
		"g after COND(t ≤ 1/2, 0, 2t − 1), which fixes 0 and 1.",
	Deps: []registry.EntryLike{PathReparametriseHomotopic, path_connected.PathJoinDef},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_homotopic(T, path_join(λt:real. g(&0), g), g)",
	},
		"the left side is g after t ↦ COND(t ≤ 1/2, 0, 2t − 1); "+
			"PathReparametriseHomotopic compares it with the identity"),
})}

// PathJoinConstantRight — a constant path joined after a path changes it
// only up to homotopy.
var PathJoinConstantRight = pathJoinConstantRightThm{family.Add(registry.ProofEntry{
	Name: "PathJoinConstantRight",
	Key:  "prop_68c4e4b8a203fc20",
	Reading: "Needs only that g is a path: the left side " +
		"is g after COND(t ≤ 1/2, 2t, 1), which fixes 0 and 1.",
	Deps: []registry.EntryLike{PathReparametriseHomotopic, path_connected.PathJoinDef},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_homotopic(T, path_join(g, λt:real. g(&1)), g)",
	},
		"the left side is g after t ↦ COND(t ≤ 1/2, 2t, 1); "+
			"PathReparametriseHomotopic compares it with the identity"),
})}

// PathJoinReverseRight — a path followed by its reverse is homotopic to
// the constant path at its start.
var PathJoinReverseRight = pathJoinReverseRightThm{family.Add(registry.ProofEntry{
	Name: "PathJoinReverseRight",
	Key:  "prop_ab30104d1f2cd65a",
	Reading: "Both sides are g after a map of ⟦0, 1⟧ sending 0 " +
		"and 1 to 0: COND(t ≤ 1/2, 2t, 2 − 2t) and the constant 0.",
	Deps: []registry.EntryLike{
		PathReparametriseHomotopic,
		path_connected.PathJoinDef,
		path_connected.PathReverseDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_homotopic(T, path_join(g, path_reverse(g)), λt:real. g(&0))",
	},
		"the left side is g after t ↦ COND(t ≤ 1/2, 2t, 2 − 2t) and the right side g after the "+
			"constant 0, two maps of the interval agreeing at 0 and at 1 (PathReparametriseHomotopic)"),
})}

// PathJoinReverseLeft — the reverse of a path followed by the path is
// homotopic to the constant path at its end.
var PathJoinReverseLeft = pathJoinReverseLeftThm{family.Add(registry.ProofEntry{
	Name: "PathJoinReverseLeft",
	Key:  "prop_c1b5852eafd998a3",
	Reading: "Both sides are g after a map of ⟦0, 1⟧ sending 0 " +
		"and 1 to 1: COND(t ≤ 1/2, 1 − 2t, 2t − 1) and the constant 1.",
	Deps: []registry.EntryLike{
		PathReparametriseHomotopic,
		path_connected.PathJoinDef,
		path_connected.PathReverseDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_homotopic(T, path_join(path_reverse(g), g), λt:real. g(&1))",
	},
		"the left side is g after t ↦ COND(t ≤ 1/2, 1 − 2t, 2t − 1) and the right side g after the "+
			"constant 1, two maps of the interval agreeing at 0 and at 1 (PathReparametriseHomotopic)"),
})}
