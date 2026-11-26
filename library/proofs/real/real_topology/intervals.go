// intervals.go — the open sets of the line built from open intervals: a
// point of an open set lies in an open interval with rational ends
// inside it, and so an open set is the union of countably many open
// intervals.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Open sets as unions of intervals
// ---------------------------------------------------------------------------

// RationalIntervalInside — a point of an open set of reals lies in an open
// interval with rational ends that lies inside the set. The point keeps a
// radius δ inside the set; the rationals are dense, so one end lies between
// x − δ and x and the other between x and x + δ, and every real between
// the two ends is within δ of x.
var RationalIntervalInside = rationalIntervalInsideThm{family.Add(registry.ProofEntry{
	Name: "RationalIntervalInside",
	Key:  "prop_2a5c8c213fb838ed",
	Build: family.Theorem(Statement{
		Binders: "∀u:set(real). ∀x:real.",
		Hypotheses: []string{
			"u ∈ real_topology",
			"x ∈ u",
		},
		Conclusion: "∃p q:real. rational(p) ∧ rational(q) ∧ p < x ∧ x < q ∧ ⟬p, q⟭ ⊆ u",
	},
		func(a *Argument, u *Expr[Set[Real]], x *Expr[Real], open, member Fact) {
			_, radius := a.ObtainAs[Real](
				"x keeps a radius δ inside the open u",
				"∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u",
				By(open, member, OpenIff.At(u)))
			parts := a.Conjuncts(
				radius,
				"the radius is positive",
				"the reals within δ of x lie in u")
			positive, within := parts[0], parts[1]
			p, below := a.ObtainAs[Real](
				"a rational p lies between x − δ and x",
				"∃p:real. rational(p) ∧ x - δ < p ∧ p < x",
				ByArith(positive, rational.RationalBetween.At(a.TermAs[Real]("x - δ"), x)))
			q, above := a.ObtainAs[Real](
				"and a rational q between x and x + δ",
				"∃q:real. rational(q) ∧ x < q ∧ q < x + δ",
				ByArith(positive, rational.RationalBetween.At(x, a.TermAs[Real]("x + δ"))))
			a.Take(p)
			a.Take(q)
			inside := a.Have(
				"a real between p and q is within δ of x, so it lies in u",
				"⟬p, q⟭ ⊆ u",
				Simp(Fwd(set_basic.SubsetDef)),
				a.ForEach(func(y *Expr[Real]) Action {
					return ByArith(within.At(y), below, above)
				}))
			a.Show(
				"so (p, q) is an interval with rational ends about x inside u",
				By(below, above, inside))
		}),
})}

// OpenCountableIntervalUnion — an open set of reals is the union of
// countably many open intervals ⟬a(n), b(n)⟭. The pairs of rationals are
// countable, so a sequence e runs through all of them. Keep the interval
// e(n) bounds where it lies inside u, and put the empty interval ⟬0, 0⟭ in
// its place elsewhere: every interval kept lies in u and the empty one holds
// nothing, so the union lies in u. A point of u lies in an interval with
// rational ends inside u (RationalIntervalInside); its pair of ends is some
// e(n), whose interval is kept.
var OpenCountableIntervalUnion = openCountableIntervalUnionThm{family.Add(registry.ProofEntry{
	Name: "OpenCountableIntervalUnion",
	Key:  "prop_f918bf8b725a4dcb",
	Build: family.Theorem(Statement{
		Binders: "∀u:set(real).",
		Hypotheses: []string{
			"u ∈ real_topology",
		},
		Conclusion: "∃a b:num → real. ∀x:real. x ∈ u ⇔ ∃n:num. a(n) < x ∧ x < b(n)",
		Abbrev: Abbrev{
			{Name: "rationalPairs", Text: "set_cross({x:real | rational(x)}, {x:real | rational(x)})"},
		},
	},
		func(arg *Argument, u *Expr[Set[Real]], open Fact) {
			rationals := arg.TermAs[Set[Real]]("{x:real | rational(x)}")
			rationalPairs := arg.TermAs[Set[Prod[Real, Real]]]("«rationalPairs»")
			_, covers := arg.ObtainAs[Fun[Nat, Prod[Real, Real]]](
				"the pairs of rationals are countable, so a sequence e runs through all of them",
				"∃e:num → prod(real, real). «rationalPairs» ⊆ image(e, 𝕌)",
				By(
					cardinal.CountableProduct.At(rationals, rationals),
					real_cardinality.CountableRational,
					cardinal.CountableCover.At(rationalPairs)))
			a, aDef := arg.LetAs[Fun[Nat, Real]](
				"a",
				"λn:num. COND(⟬fst(e(n)), snd(e(n))⟭ ⊆ u, fst(e(n)), &0)")
			b, bDef := arg.LetAs[Fun[Nat, Real]](
				"b",
				"λn:num. COND(⟬fst(e(n)), snd(e(n))⟭ ⊆ u, snd(e(n)), &0)")
			arg.Take(a)
			arg.Take(b)
			x := arg.FixAs[Real]("x")
			arg.Iff()
			arg.Forward(
				"a point of u lies in one of the intervals kept",
				func(c *Argument, member Fact) {
					p, q, around := c.Obtain2As[Real, Real](
						"x lies in an open interval with rational ends inside u",
						"∃p q:real. rational(p) ∧ rational(q) ∧ p < x ∧ x < q ∧ ⟬p, q⟭ ⊆ u",
						By(open, member, RationalIntervalInside.At(u, x)))
					parts := c.Conjuncts(
						around,
						"p is rational",
						"q is rational",
						"p lies below x",
						"x lies below q",
						"the interval from p to q lies inside u")
					n, pair := c.ObtainAs[Nat](
						"(p, q) is a pair of rationals, so a value of e",
						"∃n:num. e(n) = (p, q)",
						BySets(covers, parts[0], parts[1], set_product.InCross.At(rationals, rationals, p, q)))
					c.Take(n)
					c.Show(
						"the interval e(n) bounds is the one from p to q, inside u, so it is kept and holds x",
						Simp(Fwd(aDef), Fwd(bDef), Fwd(pair), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						By(Normalized, parts[2], parts[3], parts[4]))
				})
			arg.Backward(
				"a point of one of the intervals lies in u",
				func(c *Argument, some Fact) {
					_, between := c.UnpackAs[Nat](some)
					c.Cases(c.Term("⟬fst(e(n)), snd(e(n))⟭ ⊆ u"))
					c.When(
						"where the interval e(n) bounds lies inside u, it is ⟬a(n), b(n)⟭ and x is in it",
						func(d *Argument, inside Fact) {
							ends := d.Simplified(between, Fwd(aDef), Fwd(bDef))
							d.Show(
								"so x lies in u",
								BySets(inside, ends))
						})
					c.Otherwise(
						"elsewhere ⟬a(n), b(n)⟭ is the empty interval ⟬0, 0⟭, which holds no x",
						func(d *Argument, outside Fact) {
							empty := d.Simplified(between, Fwd(aDef), Fwd(bDef))
							d.Show(
								"and no x lies between 0 and 0",
								ByArith(empty))
						})
				})
		}),
})}
