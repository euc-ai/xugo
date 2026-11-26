// instances.go — the line among the spaces of the topology chapters: its
// topology has a countable base, the open intervals with rational ends;
// every real has a compact neighbourhood and a base of connected ones; and
// the line itself is not compact.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The line's place among the spaces
// ---------------------------------------------------------------------------

// RealSecondCountable — the line has a countable base: the open intervals
// with rational ends. They are the image of the pairs of rationals, a
// countable set, so there are countably many of them, and each is open. A
// point x of an open u lies in an open interval with rational ends inside
// u (RationalIntervalInside), and that interval is one of them.
var RealSecondCountable = realSecondCountableThm{family.Add(registry.ProofEntry{
	Name: "RealSecondCountable",
	Key:  "prop_4b559254d60bd20d",
	Build: family.Theorem("second_countable_space(real_topology)",
		func(a *Argument) {
			a.Do(Unfold(countability.SecondCountableSpaceDef))
			rationals := a.TermAs[Set[Real]]("{x:real | rational(x)}")
			between := a.TermAs[Fun[Prod[Real, Real], Set[Real]]]("λp:prod(real, real). ⟬fst(p), snd(p)⟭")
			rationalPairs := a.TermAs[Set[Prod[Real, Real]]](
				"set_cross({x:real | rational(x)}, {x:real | rational(x)})")
			base, baseDef := a.LetAs[Set[Set[Real]]](
				"B",
				"image(λp:prod(real, real). ⟬fst(p), snd(p)⟭, "+
					"    set_cross({x:real | rational(x)}, {x:real | rational(x)}))")
			a.Take(base)
			countable := a.Have(
				"the intervals with rational ends are the image of the pairs of rationals, so countably many",
				"countable(B)",
				By(
					baseDef,
					cardinal.CountableImage.At(between, rationalPairs),
					cardinal.CountableProduct.At(rationals, rationals),
					real_cardinality.CountableRational))
			open := a.Have(
				"each of them is open",
				"B ⊆ real_topology",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					v := b.FixAs[Set[Real]]("v")
					inBase := b.Assume()
					_, isInterval := b.ObtainAs[Prod[Real, Real]](
						"v is the interval between the two ends of a pair",
						"∃p:prod(real, real). v = ⟬fst(p), snd(p)⟭",
						By(baseDef, inBase, set_basic.InImage.At(between, rationalPairs, v)))
					b.Show(
						"an open interval is open",
						By(isInterval, OpenIntervalOpen.At(b.TermAs[Real]("fst(p)"), b.TermAs[Real]("snd(p)"))))
				}))
			near := a.Have(
				"a point of an open set lies in one of them inside it",
				"∀u:set(real). ∀x:real. u ∈ real_topology ∧ x ∈ u ⇒ ∃v:set(real). v ∈ B ∧ x ∈ v ∧ v ⊆ u",
				Derive(func(b *Argument) {
					u := b.FixAs[Set[Real]]("u")
					x := b.FixAs[Real]("x")
					point := b.Assume() // u open, x ∈ u
					p, q, around := b.Obtain2As[Real, Real](
						"x lies in an open interval with rational ends inside u",
						"∃p q:real. rational(p) ∧ rational(q) ∧ p < x ∧ x < q ∧ ⟬p, q⟭ ⊆ u",
						By(point, RationalIntervalInside.At(u, x)))
					b.Take(b.TermAs[Set[Real]]("⟬p, q⟭"))
					member := b.Have(
						"(p, q) is a pair of rationals, so the interval between them is one of B",
						"⟬p, q⟭ ∈ B",
						Simp(Fwd(baseDef), Fwd(set_basic.InImage)),
						Witness(b.TermAs[Prod[Real, Real]]("(p, q)")),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						By(around, set_product.InCross.At(rationals, rationals, p, q)))
					b.Show(
						"it is one of B, holds x and lies in u",
						By(member, around))
				}))
			a.Show(
				"so they are a countable base of the line",
				Unfold(topological_space.TopologyBaseDef),
				By(countable, open, near))
		}),
})}

// RealLocallyCompact — the line is locally compact: a real x lies in the
// open interval ⟬x − 1, x + 1⟭, which lies in the closed interval
// ⟦x − 1, x + 1⟧, and a closed interval is compact.
var RealLocallyCompact = realLocallyCompactThm{family.Add(registry.ProofEntry{
	Name: "RealLocallyCompact",
	Key:  "prop_830d21f993f3833c",
	Build: family.Theorem("locally_compact_space(real_topology)",
		func(a *Argument) {
			a.Do(Unfold(compact.LocallyCompactSpaceDef))
			a.FixAs[Real]("x")
			a.Assume() // x is a point of the line, as every real is
			below, above := a.TermAs[Real]("x - &1"), a.TermAs[Real]("x + &1")
			a.Take(a.TermAs[Set[Real]]("⟬x - &1, x + &1⟭"))
			a.Take(a.TermAs[Set[Real]]("⟦x - &1, x + &1⟧"))
			inside := a.Have(
				"the open interval about x lies in the closed one",
				"⟬x - &1, x + &1⟭ ⊆ ⟦x - &1, x + &1⟧",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(y *Expr[Real]) Action { return ByArith() }))
			a.Show(
				"the open interval is open and holds x, and the closed one is compact",
				ByArith(OpenIntervalOpen.At(below, above), ClosedIntervalCompact.At(below, above), inside))
		}),
})}

// RealLocallyConnected — the line is locally connected: a point x of an
// open u keeps a radius δ inside u, and the open interval ⟬x − δ, x + δ⟭
// is open, holds x and lies in u; an interval, it is connected.
var RealLocallyConnected = realLocallyConnectedThm{family.Add(registry.ProofEntry{
	Name: "RealLocallyConnected",
	Key:  "prop_4d206cf82e975ac7",
	Build: family.Theorem("locally_connected_space(real_topology)",
		func(a *Argument) {
			a.Do(Unfold(connected.LocallyConnectedSpaceDef))
			u := a.FixAs[Set[Real]]("u")
			a.FixAs[Real]("x")
			point := a.Assume() // u open, x ∈ u
			_, radius := a.ObtainAs[Real](
				"x keeps a radius δ inside the open u",
				"∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u",
				By(point, OpenIff.At(u)))
			parts := a.Conjuncts(
				radius,
				"the radius is positive",
				"the reals within δ of x lie in u")
			positive, within := parts[0], parts[1]
			below, above := a.TermAs[Real]("x - δ"), a.TermAs[Real]("x + δ")
			interval := a.TermAs[Set[Real]]("⟬x - δ, x + δ⟭")
			a.Take(interval)
			isInterval := a.Have(
				"the open interval of radius δ about x holds every real between two of its points",
				"real_interval(⟬x - δ, x + δ⟭)",
				Unfold(RealIntervalDef),
				ByArith())
			inside := a.Have(
				"its points are within δ of x, so it lies in u",
				"⟬x - δ, x + δ⟭ ⊆ u",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(y *Expr[Real]) Action { return ByArith(within.At(y)) }))
			a.Show(
				"the open interval is open and holds x, and an interval is connected",
				ByArith(
					positive,
					isInterval,
					inside,
					OpenIntervalOpen.At(below, above),
					IntervalConnected.At(interval)))
		}),
})}

// RealNotCompact — the line is not compact: a compact set of reals is
// bounded, and no bound B holds the real B + 1.
var RealNotCompact = realNotCompactThm{family.Add(registry.ProofEntry{
	Name: "RealNotCompact",
	Key:  "prop_789e83ff930150b0",
	Build: family.Theorem("¬compact_in(real_topology, 𝕌)",
		func(a *Argument) {
			compact := a.SupposeNot()
			_, bound := a.ObtainAs[Real](
				"a compact set of reals is bounded",
				"∃B:real. ∀x:real. x ∈ 𝕌 ⇒ |x| ≤ B",
				By(Normalized, compact, CompactBounded.At(a.TermAs[Set[Real]]("𝕌"))))
			beyond := a.TermAs[Real]("B + &1")
			a.Show(
				"B + 1 is a real, and its magnitude exceeds B",
				ByArith(bound.At(beyond), set_basic.InUniv.At(beyond)))
		}),
})}
