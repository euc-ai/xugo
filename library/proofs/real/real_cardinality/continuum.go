// continuum.go — the continuum: there are strictly more reals than
// naturals, so ℝ is not countable, nor are the irrationals; and there are
// exactly as many reals as sets of naturals.

package real_cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// NumLessReal — there are strictly more reals than naturals. By
// Cantor's theorem the sets of naturals outnumber the naturals, and the
// sets of naturals inject into ℝ; a set strictly below one that is no
// larger than a third is strictly below the third.
var NumLessReal = numLessRealThm{family.Add(registry.ProofEntry{
	Name: "NumLessReal",
	Key:  "prop_bea9410b5ec2447",
	Build: family.Theorem("card_lt(𝕌⟨A:num⟩, 𝕌⟨A:real⟩)",
		func(a *Argument) {
			naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
			setsOfNaturals := a.TermAs[Set[Set[Nat]]]("𝕌⟨A:set(num)⟩")
			reals := a.TermAs[Set[Real]]("𝕌⟨A:real⟩")
			a.Show(
				"ℕ < P(ℕ) ≤ ℝ",
				By(
					cardinal.CantorUniv.Inst[Nat](),
					PowersetNumLeReal,
					cardinal.CardLtLeTrans.At(naturals, setsOfNaturals, reals)))
		}),
})}

// RealUncountable — ℝ is not countable: were it no larger than ℕ, the
// naturals would not be strictly fewer.
var RealUncountable = realUncountableThm{family.Add(registry.ProofEntry{
	Name: "RealUncountable",
	Key:  "prop_4ef5e85fb44a1819",
	Build: family.Theorem("¬countable(𝕌⟨A:real⟩)",
		Opening(Unfold(cardinal.CountableDef), func(a *Argument) {
			a.Show(
				"ℕ < ℝ says ℝ is not no larger than ℕ",
				By(
					NumLessReal,
					cardinal.CardLtDef.At(a.TermAs[Set[Nat]]("𝕌⟨A:num⟩"), a.TermAs[Set[Real]]("𝕌⟨A:real⟩"))))
		})),
})}

// IrrationalUncountable — the irrationals are not countable: every real
// is rational or not, so were the irrationals countable, ℝ would be the
// union of two countable sets.
var IrrationalUncountable = irrationalUncountableThm{family.Add(registry.ProofEntry{
	Name: "IrrationalUncountable",
	Key:  "prop_12379eaf253cb4b2",
	Build: family.Theorem("¬countable({x:real | ¬rational(x)})",
		func(a *Argument) {
			irrationalsCountable := a.SupposeNot()
			reals := a.TermAs[Set[Real]]("𝕌⟨A:real⟩")
			rationals := a.TermAs[Set[Real]]("{x:real | rational(x)}")
			irrationals := a.TermAs[Set[Real]]("{x:real | ¬rational(x)}")
			rationalOrNot := a.TermAs[Set[Real]]("{x:real | rational(x)} ∪ {x:real | ¬rational(x)}")
			covered := a.Have(
				"every real is rational or not",
				"𝕌⟨A:real⟩ ⊆ {x:real | rational(x)} ∪ {x:real | ¬rational(x)}",
				BySets())
			a.Show(
				"then ℝ, inside the union of two countable sets, would be countable",
				By(
					irrationalsCountable,
					covered,
					RealUncountable,
					CountableRational,
					cardinal.CountableUnion.At(rationals, irrationals),
					cardinal.CountableSubset.At(reals, rationalOrNot)))
		}),
})}

// RealLePowersetNum — Dedekind: a real is determined by the rationals
// below it. The rationals being countable, a map q tags them by
// naturals, no two alike; send each real x to its cut, the set of tags
// of the rationals below x. Of two different reals one lies below the
// other, say x < y, and a rational p lies strictly between them. Its tag
// is the tag of a rational below y, and of none below x — a rational
// with p's tag is p itself, which lies above x. So different reals have
// different cuts, and every cut is a set of naturals.
var RealLePowersetNum = realLePowersetNumThm{family.Add(registry.ProofEntry{
	Name: "RealLePowersetNum",
	Key:  "prop_9e2e096a87bc9772",
	Build: family.Theorem("card_le(𝕌⟨A:real⟩, 𝕌⟨A:set(num)⟩)",
		Opening(Chain(Unfold(cardinal.CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			rationalsCountable := a.Have(
				"the rationals are countable",
				"countable({x:real | rational(x)})",
				Cite(CountableRational))
			_, tagging := a.UnpackAs[Fun[Real, Nat]](
				a.Unfolded(a.Unfolded(rationalsCountable, cardinal.CountableDef), cardinal.CardLeDef), "q")
			distinctTags := a.Unfolded(a.Conjuncts(
				tagging,
				"q tags every rational by a natural",
				"no two rationals share a tag")[1], functions.InjectiveOnDef)

			differ := a.Have(
				"the cuts of different reals differ",
				Statement{
					Binders: "∀x y:real.",
					Hypotheses: []string{
						"x < y",
					},
					Conclusion: "image(q, {r:real | rational(r) ∧ r < x}) ≠ image(q, {r:real | rational(r) ∧ r < y})",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[Real](), b.FixAs[Real]()
					below := b.Assume()
					p, between := b.ObtainAs[Real](
						"a rational p lies strictly between x and y",
						"∃p:real. rational(p) ∧ x < p ∧ p < y",
						By(below, rational.RationalBetween.At(x, y)))
					belowY := b.Have(
						"p is a rational below y",
						"p ∈ {r:real | rational(r) ∧ r < y}",
						BySets(between))
					inCutY := b.Have(
						"so q(p) is the tag of a rational below y",
						"q(p) ∈ image(q, {r:real | rational(r) ∧ r < y})",
						By(belowY, set_image.FunInImage))
					notInCutX := b.Have(
						"and of none below x: a rational with p's tag is p, which lies above x",
						"q(p) ∉ image(q, {r:real | rational(r) ∧ r < x})",
						BySets(distinctTags, between, real_order_ring.LessThanAsym.At(x, p)))
					b.Show(
						"so q(p) tells the two cuts apart",
						By(inCutY, notInCutX))
				}))

			a.Take(a.TermAs[Fun[Real, Set[Nat]]]("λx:real. image(q, {r:real | rational(r) ∧ r < x})"))
			oneToOne := a.Have(
				"two reals with one cut are one real",
				Statement{
					Binders: "∀x y:real.",
					Hypotheses: []string{
						"image(q, {r:real | rational(r) ∧ r < x}) = image(q, {r:real | rational(r) ∧ r < y})",
					},
					Conclusion: "x = y",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[Real](), b.FixAs[Real]()
					b.Show(
						"x = y, or x < y, or y < x, and in the last two the cuts differ",
						By(differ.At(x, y), differ.At(y, x), real_order_ring.LessThanTrichotomy.At(x, y)))
				}))
			a.Show(
				"every cut is a set of naturals, and no two reals share one",
				Simp(Fwd(set_basic.InUniv.Inst[Real]()), Fwd(set_basic.InUniv.Inst[Set[Nat]]())),
				By(oneToOne))
		})),
})}

// RealCardEqPowersetNum — there are exactly as many reals as sets of
// naturals: each injects into the other (RealLePowersetNum,
// PowersetNumLeReal), and Schröder–Bernstein joins them.
var RealCardEqPowersetNum = realCardEqPowersetNumThm{family.Add(registry.ProofEntry{
	Name: "RealCardEqPowersetNum",
	Key:  "prop_a2d7e6e3943a23a4",
	Build: family.Theorem("card_eq(𝕌⟨A:real⟩, 𝕌⟨A:set(num)⟩)",
		func(a *Argument) {
			reals := a.TermAs[Set[Real]]("𝕌⟨A:real⟩")
			setsOfNaturals := a.TermAs[Set[Set[Nat]]]("𝕌⟨A:set(num)⟩")
			a.Show(
				"ℝ ≤ P(ℕ) by the cuts, P(ℕ) ≤ ℝ by the ternary expansion; Schröder–Bernstein joins them",
				By(RealLePowersetNum, PowersetNumLeReal, cardinal.SchroederBernstein.At(reals, setsOfNaturals)))
		}),
})}
